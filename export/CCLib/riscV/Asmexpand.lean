/-
  Expansion of built-ins and pseudo-instructions for RISC-V — port of
  `riscV/Asmexpand.ml`.

  `Asmexpand` runs after the verified compiler, on the generated `Asm`
  program: it replaces the pseudo-instructions (`Pallocframe`,
  `Pfreeframe`, `Pcsel`, `Pseqw`, `Psnew`, `Pseql`, `Psnel`, `Pcvtl2w`,
  `Pcvtw2l`) by machine instructions, expands the built-in functions that
  are inlined (`memcpy`, volatile loads and stores, `va_start`, byte swaps,
  bit counting, fused multiply-add, 64-bit arithmetic on split integers, …)
  and moves the floating-point arguments of variadic calls that are passed
  in integer registers.  Like the OCaml code, it is not verified.

  Differences from OCaml:
  * `Clflags.option_ffpu` is the field of `Options`.
  * The global reference `vararg_start_ofs` is the state of the monad `RM`,
    on top of the expansion monad `Asmexpandaux.M`; the loop of
    `Asmexpandaux.expand` (without `-g`) is re-done in `RM`
    (`expandCode`).
  * `raise (Error s)`, `assert false` and `invalid_arg` become errors of the
    monad.
  * Offsets: OCaml uses the same type (`Z.t`) for the immediates of type
    `int`, `int64` and `ptrofs`; here they are converted through their
    unsigned value.  `offset_in_range` compares the value as an integer
    (`Z.to_int64` raises an exception in OCaml for values that do not fit
    in 64 bits; here such values are out of range).
  * Not ported: the DWARF register numbering (`int_reg_to_dwarf`,
    `float_reg_to_dwarf`, `preg_to_dwarf`), which only serves `-g` (see
    `CCLib.backend.Asmexpandaux`).
-/
import CCLib.riscV.Asmgen
import CCLib.backend.Asmexpandaux

namespace CC
namespace RiscV
namespace Asmexpand

open Asm Asmexpandaux

instance : AsmInstr Instruction where
  labelOf | .Plabel l => some l | _ => none
  mkLabel := .Plabel
  annotKind | .Pbuiltin (.EF_annot kind _ _) _ _ => some kind | _ => none
  isDebug | .Pbuiltin (.EF_debug _ _ _) _ _ => true | _ => false
  mkBuiltin ef := .Pbuiltin ef [] .BR_none

/-- The expansion monad for RISC-V code. -/
abbrev EM := Asmexpandaux.M Instruction

/-- The configuration used by the expansion. -/
structure Options where
  /-- `Clflags.option_ffpu` -/
  ffpu : Bool := true

/-- `Int.repr` -/
abbrev I32 (n : Int) : Integers.Int := Integers.Int.repr n
/-- `Ptrofs.repr` -/
abbrev P (n : Int) : Integers.Ptrofs := Integers.Ptrofs.repr n

/-- `wordsize` -/
def wordsize : Int := if Archi.ptr64 then 8 else 4

/-- `align n a` (for `a` a power of 2 and `n ≥ 0`) -/
def align (n a : Int) : Int := (n + a - 1) / a * a

/-! ## Setting or offsetting a register by a constant -/

/-- `expand_loadimm32` -/
def expandLoadimm32 (dst : Ireg) (n : Integers.Int) : EM Unit :=
  for i in Asmgen.loadimm32 dst n [] do emit i

/-- `expand_addptrofs` -/
def expandAddptrofs (dst src : Ireg) (n : Integers.Ptrofs) : EM Unit :=
  for i in Asmgen.addptrofs dst src n [] do emit i

/-- `expand_storeind_ptr` -/
def expandStoreindPtr (src base : Ireg) (ofs : Integers.Ptrofs) : EM Unit :=
  for i in Asmgen.storeindPtr src base ofs [] do emit i

/-! ## Fix-up code around function calls and function entry

Some floating-point arguments residing in FP registers need to be moved to
integer registers or register pairs, and symmetrically for parameters. -/

/-- `int_param_regs` -/
def intParamReg : Nat → Ireg
  | 0 => .X10 | 1 => .X11 | 2 => .X12 | 3 => .X13
  | 4 => .X14 | 5 => .X15 | 6 => .X16 | _ => .X17

/-- `move_single_arg` -/
def moveSingleArg (fr : Freg) (i : Nat) : EM Unit := emit (.Pfmvxs (intParamReg i) fr)

/-- `move_double_arg` -/
def moveDoubleArg (fr : Freg) (i : Nat) : EM Unit :=
  if Archi.ptr64 then emit (.Pfmvxd (intParamReg i) fr)
  else do
    emit (.Paddiw .X2 (.X .X2) (Integers.Int.neg (I32 16)))
    emit (.Pfsd fr .X2 (.Ofsimm (P 0)))
    emit (.Plw (intParamReg i) .X2 (.Ofsimm (P 0)))
    if i < 7 then
      emit (.Plw (intParamReg (i + 1)) .X2 (.Ofsimm (P 4)))
    else
      emit (.Plw .X31 .X2 (.Ofsimm (P 4)))
      emit (.Psw .X31 .X2 (.Ofsimm (P 16)))
    emit (.Paddiw .X2 (.X .X2) (I32 16))

/-- `move_single_param` -/
def moveSingleParam (fr : Freg) (i : Nat) : EM Unit := emit (.Pfmvsx fr (intParamReg i))

/-- `move_double_param` -/
def moveDoubleParam (fr : Freg) (i : Nat) : EM Unit :=
  if Archi.ptr64 then emit (.Pfmvdx fr (intParamReg i))
  else do
    emit (.Paddiw .X2 (.X .X2) (Integers.Int.neg (I32 16)))
    emit (.Psw (intParamReg i) .X2 (.Ofsimm (P 0)))
    if i < 7 then
      emit (.Psw (intParamReg (i + 1)) .X2 (.Ofsimm (P 4)))
    else
      emit (.Plw .X31 .X2 (.Ofsimm (P 16)))
      emit (.Psw .X31 .X2 (.Ofsimm (P 4)))
    emit (.Pfld fr .X2 (.Ofsimm (P 0)))
    emit (.Paddiw .X2 (.X .X2) (I32 16))

/-- `float_extra_index` -/
def floatExtraIndex : Mreg → Option (Freg × Nat)
  | .F0 => some (.F0, 0) | .F1 => some (.F1, 1)
  | .F2 => some (.F2, 2) | .F3 => some (.F3, 3)
  | .F4 => some (.F4, 4) | .F5 => some (.F5, 5)
  | .F6 => some (.F6, 6) | .F7 => some (.F7, 7)
  | _ => none

/-- `fixup_gen` -/
def fixupGen (single double : Freg → Nat → EM Unit) (sg : Signature) : EM Unit :=
  for (ty, loc) in (Conventions1.projSigArgs sg).zip (Conventions1.locArguments sg) do
    match ty, loc with
    | .Tsingle, .One (.R r) =>
      match floatExtraIndex r with
      | some (r, i) => single r i
      | none => pure ()
    | .Tfloat, .One (.R r) | .Tany64, .One (.R r) =>
      match floatExtraIndex r with
      | some (r, i) => double r i
      | none => pure ()
    | _, _ => pure ()

/-- `fixup_call` -/
def fixupCall (sg : Signature) : EM Unit := fixupGen moveSingleArg moveDoubleArg sg

/-- `fixup_function_entry` -/
def fixupFunctionEntry (sg : Signature) : EM Unit :=
  fixupGen moveSingleParam moveDoubleParam sg

/-! ## Annotations -/

/-- `expand_annot_val` -/
def expandAnnotVal (kind : Positive) (txt : String) (targ : ATyp)
    (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg) : EM Unit := do
  emit (.Pbuiltin (.EF_annot kind txt [targ]) args .BR_none)
  match args, res with
  | [.BA (.IR src)], .BR (.IR dst) => if dst ≠ src then emit (.Pmv dst src)
  | [.BA (.FR src)], .BR (.FR dst) => if dst ≠ src then emit (.Pfmv dst src)
  | _, _ => error "ill-formed __builtin_annot_val"

/-! ## Handling of `memcpy`

Unaligned accesses are slow on RISC-V, so they are not used. -/

/-- `offset_in_range` -/
def offsetInRange (ofs : Int) : Bool := -2048 ≤ ofs && ofs < 2048

/-- `memcpy_small_arg` -/
def memcpySmallArg (sz : Int) (arg : BuiltinArg Preg) (tmp : Ireg) :
    EM (Ireg × Integers.Ptrofs) :=
  match arg with
  | .BA (.IR r) => pure (r, P 0)
  | .BA_addrstack ofs =>
    if offsetInRange (Integers.Ptrofs.unsigned ofs)
        && offsetInRange (Integers.Ptrofs.unsigned (Integers.Ptrofs.add ofs (P sz))) then
      pure (.X2, ofs)
    else do
      expandAddptrofs tmp .X2 ofs
      pure (tmp, P 0)
  | _ => error "memcpy_small_arg"

/-- The loop `copy` of `expand_builtin_memcpy_small`. -/
def memcpySmallCopy (o : Options) (al : Int) (rsrc rdst : Ireg) :
    Nat → Integers.Ptrofs → Integers.Ptrofs → EM Unit
  | sz, osrc, odst =>
    let next (n : Nat) (h : n > 0) (ld st : Instruction) (hle : n ≤ sz) : EM Unit := do
      emit ld
      emit st
      memcpySmallCopy o al rsrc rdst (sz - n) (Integers.Ptrofs.add osrc (P n))
        (Integers.Ptrofs.add odst (P n))
    if h8 : Archi.ptr64 && sz ≥ 8 && al ≥ 8 then
      next 8 (by decide) (.Pld .X31 rsrc (.Ofsimm osrc)) (.Psd .X31 rdst (.Ofsimm odst))
        (by simp at h8; omega)
    else if h8' : o.ffpu && sz ≥ 8 && al ≥ 8 then
      next 8 (by decide) (.Pfld .F0 rsrc (.Ofsimm osrc)) (.Pfsd .F0 rdst (.Ofsimm odst))
        (by simp at h8'; omega)
    else if h4 : sz ≥ 4 && al ≥ 4 then
      next 4 (by decide) (.Plw .X31 rsrc (.Ofsimm osrc)) (.Psw .X31 rdst (.Ofsimm odst))
        (by simp at h4; omega)
    else if h2 : sz ≥ 2 && al ≥ 2 then
      next 2 (by decide) (.Plh .X31 rsrc (.Ofsimm osrc)) (.Psh .X31 rdst (.Ofsimm odst))
        (by simp at h2; omega)
    else if h1 : sz ≥ 1 then
      next 1 (by decide) (.Plb .X31 rsrc (.Ofsimm osrc)) (.Psb .X31 rdst (.Ofsimm odst)) h1
    else pure ()
termination_by sz => sz

/-- `expand_builtin_memcpy_small` -/
def expandBuiltinMemcpySmall (o : Options) (sz al : Int) (src dst : BuiltinArg Preg) :
    EM Unit := do
  let tsrc : Ireg := if dst ≠ .BA (.IR .X5) then .X5 else .X6
  let tdst : Ireg := if src ≠ .BA (.IR .X6) then .X6 else .X5
  let (rsrc, osrc) ← memcpySmallArg sz src tsrc
  let (rdst, odst) ← memcpySmallArg sz dst tdst
  memcpySmallCopy o al rsrc rdst sz.toNat osrc odst

/-- `memcpy_big_arg` -/
def memcpyBigArg (arg : BuiltinArg Preg) (tmp : Ireg) : EM Unit :=
  match arg with
  | .BA (.IR r) => if r ≠ tmp then emit (.Pmv tmp r) else pure ()
  | .BA_addrstack ofs => expandAddptrofs tmp .X2 ofs
  | _ => error "memcpy_big_arg"

/-- `expand_builtin_memcpy_big` -/
def expandBuiltinMemcpyBig (o : Options) (sz al : Int) (src dst : BuiltinArg Preg) :
    EM Unit := do
  if !(sz ≥ al) || al = 0 || sz % al ≠ 0 then error "expand_builtin_memcpy_big"
  let (s, d) : Ireg × Ireg := if dst ≠ .BA (.IR .X5) then (.X5, .X6) else (.X6, .X5)
  memcpyBigArg src s
  memcpyBigArg dst d
  -- Use X7 as loop count, X31 and F0 as ld/st temporaries.
  let (load, store, chunksize) : Instruction × Instruction × Int :=
    if Archi.ptr64 && al ≥ 8 then
      (.Pld .X31 s (.Ofsimm (P 0)), .Psd .X31 d (.Ofsimm (P 0)), 8)
    else if o.ffpu && al ≥ 8 then
      (.Pfld .F0 s (.Ofsimm (P 0)), .Pfsd .F0 d (.Ofsimm (P 0)), 8)
    else if al ≥ 4 then
      (.Plw .X31 s (.Ofsimm (P 0)), .Psw .X31 d (.Ofsimm (P 0)), 4)
    else if al = 2 then
      (.Plh .X31 s (.Ofsimm (P 0)), .Psh .X31 d (.Ofsimm (P 0)), 2)
    else
      (.Plb .X31 s (.Ofsimm (P 0)), .Psb .X31 d (.Ofsimm (P 0)), 1)
  expandLoadimm32 .X7 (I32 (sz / chunksize))
  let delta := P chunksize
  let lbl ← newLabel
  emit (.Plabel lbl)
  emit load
  expandAddptrofs s s delta
  emit (.Paddiw .X7 (.X .X7) (I32 (-1)))
  emit store
  expandAddptrofs d d delta
  emit (.Pbnew (.X .X7) .X0 lbl)

/-- `expand_builtin_memcpy` -/
def expandBuiltinMemcpy (o : Options) (sz al : Int) (args : List (BuiltinArg Preg)) :
    EM Unit :=
  match args with
  | [dst, src] =>
    if sz ≤ 32 then expandBuiltinMemcpySmall o sz al src dst
    else expandBuiltinMemcpyBig o sz al src dst
  | _ => error "expand_builtin_memcpy"

/-! ## Handling of volatile reads and writes -/

/-- `expand_builtin_vload_common` -/
def expandBuiltinVloadCommon (chunk : Chunk) (base : Ireg) (ofs : Integers.Ptrofs)
    (res : BuiltinRes Preg) : EM Unit :=
  match chunk, res with
  | .Mbool, .BR (.IR res) | .Mint8unsigned, .BR (.IR res) => emit (.Plbu res base (.Ofsimm ofs))
  | .Mint8signed, .BR (.IR res) => emit (.Plb res base (.Ofsimm ofs))
  | .Mint16unsigned, .BR (.IR res) => emit (.Plhu res base (.Ofsimm ofs))
  | .Mint16signed, .BR (.IR res) => emit (.Plh res base (.Ofsimm ofs))
  | .Mint32, .BR (.IR res) => emit (.Plw res base (.Ofsimm ofs))
  | .Mint64, .BR (.IR res) => emit (.Pld res base (.Ofsimm ofs))
  | .Mint64, .BR_splitlong (.BR (.IR res1)) (.BR (.IR res2)) => do
    let ofs' := Integers.Ptrofs.add ofs (P 4)
    if base ≠ res2 then
      emit (.Plw res2 base (.Ofsimm ofs))
      emit (.Plw res1 base (.Ofsimm ofs'))
    else
      emit (.Plw res1 base (.Ofsimm ofs'))
      emit (.Plw res2 base (.Ofsimm ofs))
  | .Mfloat32, .BR (.FR res) => emit (.Pfls res base (.Ofsimm ofs))
  | .Mfloat64, .BR (.FR res) => emit (.Pfld res base (.Ofsimm ofs))
  | _, _ => error "expand_builtin_vload_common"

/-- The offset of `BA_addptr (BA (IR addr)) (BA_int ofs | BA_long ofs)`. -/
def addptrOffset : BuiltinArg Preg → Option Int
  | .BA_int ofs => some (Integers.Int.unsigned ofs)
  | .BA_long ofs => some (Integers.Int64.unsigned ofs)
  | _ => none

/-- `expand_builtin_vload` -/
def expandBuiltinVload (chunk : Chunk) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit :=
  match args with
  | [.BA (.IR addr)] => expandBuiltinVloadCommon chunk addr (P 0) res
  | [.BA_addrstack ofs] =>
    if offsetInRange (Integers.Ptrofs.unsigned ofs + sizeChunk chunk) then
      expandBuiltinVloadCommon chunk .X2 ofs res
    else do
      expandAddptrofs .X31 .X2 ofs
      expandBuiltinVloadCommon chunk .X31 (P 0) res
  | [.BA_addptr (.BA (.IR addr)) a] =>
    match addptrOffset a with
    | some ofs =>
      if offsetInRange (ofs + sizeChunk chunk) then
        expandBuiltinVloadCommon chunk addr (P ofs) res
      else do
        expandAddptrofs .X31 addr (P ofs)
        expandBuiltinVloadCommon chunk .X31 (P 0) res
    | none => error "expand_builtin_vload"
  | _ => error "expand_builtin_vload"

/-- `expand_builtin_vstore_common` -/
def expandBuiltinVstoreCommon (chunk : Chunk) (base : Ireg) (ofs : Integers.Ptrofs)
    (src : BuiltinArg Preg) : EM Unit :=
  match chunk, src with
  | .Mbool, .BA (.IR src) | .Mint8signed, .BA (.IR src) | .Mint8unsigned, .BA (.IR src) =>
    emit (.Psb src base (.Ofsimm ofs))
  | .Mint16signed, .BA (.IR src) | .Mint16unsigned, .BA (.IR src) =>
    emit (.Psh src base (.Ofsimm ofs))
  | .Mint32, .BA (.IR src) => emit (.Psw src base (.Ofsimm ofs))
  | .Mint64, .BA (.IR src) => emit (.Psd src base (.Ofsimm ofs))
  | .Mint64, .BA_splitlong (.BA (.IR src1)) (.BA (.IR src2)) => do
    let ofs' := Integers.Ptrofs.add ofs (P 4)
    emit (.Psw src2 base (.Ofsimm ofs))
    emit (.Psw src1 base (.Ofsimm ofs'))
  | .Mfloat32, .BA (.FR src) => emit (.Pfss src base (.Ofsimm ofs))
  | .Mfloat64, .BA (.FR src) => emit (.Pfsd src base (.Ofsimm ofs))
  | _, _ => error "expand_builtin_vstore_common"

/-- `expand_builtin_vstore` -/
def expandBuiltinVstore (chunk : Chunk) (args : List (BuiltinArg Preg)) : EM Unit :=
  match args with
  | [.BA (.IR addr), src] => expandBuiltinVstoreCommon chunk addr (P 0) src
  | [.BA_addrstack ofs, src] =>
    if offsetInRange (Integers.Ptrofs.unsigned ofs + sizeChunk chunk) then
      expandBuiltinVstoreCommon chunk .X2 ofs src
    else do
      expandAddptrofs .X31 .X2 ofs
      expandBuiltinVstoreCommon chunk .X31 (P 0) src
  | [.BA_addptr (.BA (.IR addr)) a, src] =>
    match addptrOffset a with
    | some ofs =>
      if offsetInRange (ofs + sizeChunk chunk) then
        expandBuiltinVstoreCommon chunk addr (P ofs) src
      else do
        expandAddptrofs .X31 addr (P ofs)
        expandBuiltinVstoreCommon chunk .X31 (P 0) src
    | none => error "expand_builtin_vstore"
  | _ => error "expand_builtin_vstore"

/-! ## Handling of varargs

The number of integer registers, FP registers, and stack words used to pass
the (fixed) arguments to a function. -/

/-- `arg_int_size` -/
def argIntSize (ri rf ofs : Int) : Int × Int × Int :=
  if ri < 8 then (ri + 1, rf, ofs) else (ri, rf, ofs + 1)

/-- `arg_single_size` -/
def argSingleSize (ri rf ofs : Int) : Int × Int × Int :=
  if rf < 8 then (ri, rf + 1, ofs) else argIntSize ri rf ofs

/-- `arg_long_size` -/
def argLongSize (ri rf ofs : Int) : Int × Int × Int :=
  if Archi.ptr64 then
    if ri < 8 then (ri + 1, rf, ofs) else (ri, rf, ofs + 1)
  else if ri < 7 then (ri + 2, rf, ofs)
  else if ri = 7 then (ri + 1, rf, ofs + 1)
  else (ri, rf, align ofs 2 + 2)

/-- `arg_double_size` -/
def argDoubleSize (ri rf ofs : Int) : Int × Int × Int :=
  if rf < 8 then (ri, rf + 1, ofs) else argLongSize ri rf ofs

/-- `args_size` (the continuation-passing style of OCaml is unfolded) -/
def argsSize : List ATyp → Int → Int → Int → Int × Int × Int
  | [], ri, rf, ofs => (ri, rf, ofs)
  | ty :: l, ri, rf, ofs =>
    let (ri, rf, ofs) := match ty with
      | .Tint | .Tany32 => argIntSize ri rf ofs
      | .Tsingle => argSingleSize ri rf ofs
      | .Tlong => argLongSize ri rf ofs
      | .Tfloat | .Tany64 => argDoubleSize ri rf ofs
    argsSize l ri rf ofs

/-- `arguments_size`: the size in words of the arguments passed in integer
    registers or on the stack. -/
def argumentsSize (sg : Signature) : Int :=
  let (ri, _, ofs) := argsSize (Conventions1.projSigArgs sg) 0 0 0
  ri + ofs

/-- `save_arguments first_reg base_ofs` -/
def saveArguments (firstReg : Nat) (baseOfs : Int) : EM Unit :=
  for i in List.range' firstReg (8 - firstReg) do
    expandStoreindPtr (intParamReg i) .X2 (P (baseOfs + (i - firstReg : Int) * wordsize))

/-- `expand_builtin_va_start r`, given `vararg_start_ofs`. -/
def expandBuiltinVaStart (varargStartOfs : Option Int) (r : Ireg) : EM Unit :=
  match varargStartOfs with
  | none => error "Fatal error: va_start used in non-vararg function"
  | some ofs => do
    expandAddptrofs .X31 .X2 (P ofs)
    expandStoreindPtr .X31 r Integers.Ptrofs.zero

/-! ## 64-bit integer arithmetic, byte swaps, bit counting -/

/-- `expand_int64_arith`: when the first instruction would overwrite
    arguments of the second, the low half goes through `X31`. -/
def expandInt64Arith (conflict : Bool) (rl : Ireg) (fn : Ireg → EM Unit) : EM Unit :=
  if conflict then do
    fn .X31
    emit (.Pmv rl .X31)
  else fn rl

/-- `expand_bswap16`: `d = (s & 0xFF) << 8 | (s >> 8) & 0xFF` -/
def expandBswap16 (d s : Ireg) : EM Unit := do
  emit (.Pandiw .X31 (.X s) (I32 0xFF))
  emit (.Pslliw .X31 (.X .X31) (I32 8))
  emit (.Psrliw d (.X s) (I32 8))
  emit (.Pandiw d (.X d) (I32 0xFF))
  emit (.Porw d (.X .X31) (.X d))

/-- `expand_bswap32` -/
def expandBswap32 (d s : Ireg) : EM Unit := do
  emit (.Pslliw .X1 (.X s) (I32 24))
  emit (.Psrliw .X31 (.X s) (I32 8))
  emit (.Pandiw .X31 (.X .X31) (I32 0xFF))
  emit (.Pslliw .X31 (.X .X31) (I32 16))
  emit (.Porw .X1 (.X .X1) (.X .X31))
  emit (.Psrliw .X31 (.X s) (I32 16))
  emit (.Pandiw .X31 (.X .X31) (I32 0xFF))
  emit (.Pslliw .X31 (.X .X31) (I32 8))
  emit (.Porw .X1 (.X .X1) (.X .X31))
  emit (.Psrliw .X31 (.X s) (I32 24))
  emit (.Porw d (.X .X1) (.X .X31))

/-- `expand_bswap64` -/
def expandBswap64 (d s : Ireg) : EM Unit := do
  emit (.Psllil .X1 (.X s) (I32 56))
  for (n1, n2) in [((8 : Int), (48 : Int)), (16, 40), (24, 32), (32, 24), (40, 16), (48, 8)] do
    emit (.Psrlil .X31 (.X s) (I32 n1))
    emit (.Pandil .X31 (.X .X31) (Integers.Int64.repr 0xFF))
    emit (.Psllil .X31 (.X .X31) (I32 n2))
    emit (.Porl .X1 (.X .X1) (.X .X31))
  emit (.Psrlil .X31 (.X s) (I32 56))
  emit (.Porl d (.X .X1) (.X .X31))

/-- `expand_clz ~sixtyfour ~splitlong` (Hacker's Delight, algorithm 5-7):
    input in `X5` (or `X5`, `X6`), result in `X7`, temporaries `X8`, `X9`. -/
def expandClz (sixtyfour splitlong : Bool) : EM Unit := do
  let lbl1 ← newLabel
  let lbl2 ← newLabel
  expandLoadimm32 .X7 (I32 (if sixtyfour || splitlong then 64 else 32))
  expandLoadimm32 .X8 (I32 (if sixtyfour then 32 else 16))
  if splitlong then
    emit (.Pbeqw (.X .X6) .X0 lbl1)
    expandLoadimm32 .X7 (I32 32)
    emit (.Pmv .X5 .X6)
  emit (.Plabel lbl1)
  emit (if sixtyfour then .Psrll .X9 (.X .X5) (.X .X8) else .Psrlw .X9 (.X .X5) (.X .X8))
  emit (if sixtyfour then .Pbeql (.X .X9) .X0 lbl2 else .Pbeqw (.X .X9) .X0 lbl2)
  emit (.Psubw .X7 (.X .X7) (.X .X8))
  emit (.Pmv .X5 .X9)
  emit (.Plabel lbl2)
  emit (.Psrliw .X8 (.X .X8) (I32 1))
  emit (.Pbnew (.X .X8) .X0 lbl1)
  emit (.Psubw .X7 (.X .X7) (.X .X5))

/-- `expand_ctz ~sixtyfour ~splitlong` (Hacker's Delight, algorithm 5-14):
    input in `X6` (or `X5`, `X6`), result in `X7`, temporaries `X8`, `X9`. -/
def expandCtz (sixtyfour splitlong : Bool) : EM Unit := do
  let lbl1 ← newLabel
  let lbl2 ← newLabel
  expandLoadimm32 .X7 (I32 (if sixtyfour || splitlong then 64 else 32))
  expandLoadimm32 .X8 (I32 (if sixtyfour then 32 else 16))
  if splitlong then
    emit (.Pbeqw (.X .X5) .X0 lbl1)
    expandLoadimm32 .X7 (I32 32)
    emit (.Pmv .X6 .X5)
  emit (.Plabel lbl1)
  emit (if sixtyfour then .Pslll .X9 (.X .X6) (.X .X8) else .Psllw .X9 (.X .X6) (.X .X8))
  emit (if sixtyfour then .Pbeql (.X .X9) .X0 lbl2 else .Pbeqw (.X .X9) .X0 lbl2)
  emit (.Psubw .X7 (.X .X7) (.X .X8))
  emit (.Pmv .X6 .X9)
  emit (.Plabel lbl2)
  emit (.Psrliw .X8 (.X .X8) (I32 1))
  emit (.Pbnew (.X .X8) .X0 lbl1)
  emit (if sixtyfour then .Psrlil .X6 (.X .X6) (I32 63) else .Psrliw .X6 (.X .X6) (I32 31))
  emit (.Psubw .X7 (.X .X7) (.X .X6))

/-- Full register width `and` -/
def pand (r : Ireg) (a1 a2 : Ireg0) : Instruction :=
  if Archi.ptr64 then .Pandl r a1 a2 else .Pandw r a1 a2

/-- Full register width `xor` -/
def pxor (r : Ireg) (a1 a2 : Ireg0) : Instruction :=
  if Archi.ptr64 then .Pxorl r a1 a2 else .Pxorw r a1 a2

/-- `expand_csel res cond arg1 arg2`: `res := cond ? arg1 : arg2`, for
    `cond` equal to 0 or 1. -/
def expandCsel (res : Ireg) (cond arg1 arg2 : Ireg0) : EM Unit := do
  emit (.Psubw .X31 .X0 cond)
  emit (pxor .X1 arg1 arg2)
  emit (pand .X1 (.X .X1) (.X .X31))
  emit (pxor res arg2 (.X .X1))

/-! ## Compiler-inlined built-ins -/

/-- `expand_builtin_inline` (`varargStartOfs` is `vararg_start_ofs`) -/
def expandBuiltinInline (varargStartOfs : Option Int) (name : String)
    (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg) : EM Unit :=
  let check (b : Bool) (k : EM Unit) : EM Unit :=
    if b then k else error s!"{name}: unexpected registers"
  match name, args, res with
  -- Synchronization
  | "__builtin_membar", [], _ => pure ()
  | "__builtin_fence", [], _ => emit .Pfence
  -- Vararg stuff
  | "__builtin_va_start", [.BA (.IR a)], _ => expandBuiltinVaStart varargStartOfs a
  -- Byte swaps
  | "__builtin_bswap16", [.BA (.IR a1)], .BR (.IR res) => expandBswap16 res a1
  | "__builtin_bswap", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_bswap32", [.BA (.IR a1)], .BR (.IR res) => expandBswap32 res a1
  | "__builtin_bswap64", [.BA (.IR a1)], .BR (.IR res) => expandBswap64 res a1
  | "__builtin_bswap64", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    check (ah = .X6 && al = .X5 && rh = .X5 && rl = .X6) do
      expandBswap32 .X5 .X5
      expandBswap32 .X6 .X6
  -- Count zeros
  | "__builtin_clz", [.BA (.IR a)], .BR (.IR res) =>
    check (a = .X5 && res = .X7) (expandClz false false)
  | "__builtin_clzl", [.BA (.IR a)], .BR (.IR res) =>
    check (a = .X5 && res = .X7) (expandClz Archi.ptr64 false)
  | "__builtin_clzll", [.BA (.IR a)], .BR (.IR res) =>
    check (a = .X5 && res = .X7) (expandClz true false)
  | "__builtin_clzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) =>
    check (al = .X5 && ah = .X6 && res = .X7) (expandClz false true)
  | "__builtin_ctz", [.BA (.IR a)], .BR (.IR res) =>
    check (a = .X6 && res = .X7) (expandCtz false false)
  | "__builtin_ctzl", [.BA (.IR a)], .BR (.IR res) =>
    check (a = .X6 && res = .X7) (expandCtz Archi.ptr64 false)
  | "__builtin_ctzll", [.BA (.IR a)], .BR (.IR res) =>
    check (a = .X6 && res = .X7) (expandCtz true false)
  | "__builtin_ctzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) =>
    check (al = .X5 && ah = .X6 && res = .X7) (expandCtz false true)
  -- Float arithmetic
  | "__builtin_fsqrt", [.BA (.FR a1)], .BR (.FR res)
  | "__builtin_sqrt", [.BA (.FR a1)], .BR (.FR res) => emit (.Pfsqrtd res a1)
  | "__builtin_fmadd", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfmaddd res a1 a2 a3)
  | "__builtin_fmsub", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfmsubd res a1 a2 a3)
  | "__builtin_fnmadd", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfnmaddd res a1 a2 a3)
  | "__builtin_fnmsub", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfnmsubd res a1 a2 a3)
  | "__builtin_fmin", [.BA (.FR a1), .BA (.FR a2)], .BR (.FR res) => emit (.Pfmind res a1 a2)
  | "__builtin_fmax", [.BA (.FR a1), .BA (.FR a2)], .BR (.FR res) => emit (.Pfmaxd res a1 a2)
  -- 64-bit integer arithmetic for a 32-bit platform
  | "__builtin_negl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl = ah) rl fun rl => do
      emit (.Psltuw .X1 .X0 (.X al))
      emit (.Psubw rl .X0 (.X al))
      emit (.Psubw rh .X0 (.X ah))
      emit (.Psubw rh (.X rh) (.X .X1))
  | "__builtin_addl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl = bl || rl = ah || rl = bh) rl fun rl => do
      emit (.Paddw rl (.X al) (.X bl))
      emit (.Psltuw .X1 (.X rl) (.X bl))
      emit (.Paddw rh (.X ah) (.X bh))
      emit (.Paddw rh (.X rh) (.X .X1))
  | "__builtin_subl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl = ah || rl = bh) rl fun rl => do
      emit (.Psltuw .X1 (.X al) (.X bl))
      emit (.Psubw rl (.X al) (.X bl))
      emit (.Psubw rh (.X ah) (.X bh))
      emit (.Psubw rh (.X rh) (.X .X1))
  | "__builtin_mull", [.BA (.IR a), .BA (.IR b)], .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl = a || rl = b) rl fun rl => do
      emit (.Pmulw rl (.X a) (.X b))
      emit (.Pmulhuw rh (.X a) (.X b))
  -- No operation
  | "__builtin_nop", [], _ => emit .Pnop
  -- Optimization hint
  | "__builtin_unreachable", [], _ => pure ()
  -- Catch-all
  | _, _, _ => error ("unrecognized builtin " ++ name)

/-! ## Expansion of instructions -/

/-- The RISC-V expansion monad: `vararg_start_ofs` on top of `EM`. -/
abbrev RM := StateT (Option Int) EM

/-- The size of the extra area where a variadic function saves its
    integer parameter registers. -/
def extraSize (sg : Signature) : Int :=
  if sg.sig_cc.cc_vararg.isSome then
    let n := argumentsSize sg
    if n ≥ 8 then 0 else align ((8 - n) * wordsize) 16
  else 0

/-- `expand_instruction` -/
def expandInstruction (o : Options) (instr : Instruction) : RM Unit :=
  match instr with
  | .Pallocframe sz ofs => do
    let sg ← (getCurrentFunctionSig : EM Signature)
    (emit (.Pmv .X30 .X2) : EM Unit)
    if sg.sig_cc.cc_vararg.isSome then
      let n := argumentsSize sg
      let fullSz := sz + extraSize sg
      (expandAddptrofs .X2 .X2 (P (-fullSz)) : EM Unit)
      (emit (.Pcfi_adjust (I32 sz)) : EM Unit)
      (expandStoreindPtr .X30 .X2 ofs : EM Unit)
      let vaOfs := fullSz + (n - 8) * wordsize
      set (some vaOfs)
      (saveArguments n.toNat vaOfs : EM Unit)
    else
      (expandAddptrofs .X2 .X2 (P (-sz)) : EM Unit)
      (emit (.Pcfi_adjust (I32 sz)) : EM Unit)
      (expandStoreindPtr .X30 .X2 ofs : EM Unit)
      set (none : Option Int)
  | .Pfreeframe sz _ => do
    let sg ← (getCurrentFunctionSig : EM Signature)
    (expandAddptrofs .X2 .X2 (P (sz + extraSize sg)) : EM Unit)
  | .Pcsel rd rcond rs1 rs2 => (expandCsel rd (.X rcond) (.X rs1) (.X rs2) : EM Unit)
  | .Pseqw rd rs1 rs2 =>
    -- x == 0 iff x <u 1 (unsigned comparison)
    if rs2 = .X0 then (emit (.Psltiuw rd rs1 Integers.Int.one) : EM Unit)
    else do
      (emit (.Pxorw rd rs1 rs2) : EM Unit)
      (emit (.Psltiuw rd (.X rd) Integers.Int.one) : EM Unit)
  | .Psnew rd rs1 rs2 =>
    -- x != 0 iff 0 <u x (unsigned comparison)
    if rs2 = .X0 then (emit (.Psltuw rd .X0 rs1) : EM Unit)
    else do
      (emit (.Pxorw rd rs1 rs2) : EM Unit)
      (emit (.Psltuw rd .X0 (.X rd)) : EM Unit)
  | .Pseql rd rs1 rs2 =>
    if rs2 = .X0 then (emit (.Psltiul rd rs1 Integers.Int64.one) : EM Unit)
    else do
      (emit (.Pxorl rd rs1 rs2) : EM Unit)
      (emit (.Psltiul rd (.X rd) Integers.Int64.one) : EM Unit)
  | .Psnel rd rs1 rs2 =>
    if rs2 = .X0 then (emit (.Psltul rd .X0 rs1) : EM Unit)
    else do
      (emit (.Pxorl rd rs1 rs2) : EM Unit)
      (emit (.Psltul rd .X0 (.X rd)) : EM Unit)
  | .Pcvtl2w rd rs =>
    if !Archi.ptr64 then (error "Pcvtl2w: not a 64-bit target" : EM Unit)
    else (emit (.Paddiw rd rs Integers.Int.zero) : EM Unit)  -- 32-bit sign extension
  | .Pcvtw2l _ =>
    -- no-operation because the 32-bit integer was kept sign extended already
    if !Archi.ptr64 then (error "Pcvtw2l: not a 64-bit target" : EM Unit) else pure ()
  | .Pjal_r _ sg | .Pjal_s _ sg | .Pj_s _ sg => do
    (fixupCall sg : EM Unit)
    (emit instr : EM Unit)
  | .Pj_r r sg => do
    if r ≠ .X1 then (fixupCall sg : EM Unit)
    (emit instr : EM Unit)
  | .Pbuiltin ef args res => do
    let vofs ← get
    match ef with
    | .EF_builtin name _ => (expandBuiltinInline vofs name args res : EM Unit)
    | .EF_vload chunk => (expandBuiltinVload chunk args res : EM Unit)
    | .EF_vstore chunk => (expandBuiltinVstore chunk args : EM Unit)
    | .EF_annot_val kind txt targ => (expandAnnotVal kind txt targ args res : EM Unit)
    | .EF_memcpy sz al => (expandBuiltinMemcpy o sz al args : EM Unit)
    | .EF_annot _ _ _ | .EF_debug _ _ _ | .EF_inline_asm _ _ _ => (emit instr : EM Unit)
    | _ => (error "expand_instruction: unexpected builtin" : EM Unit)
  | _ => (emit instr : EM Unit)

/-- `Asmexpandaux.expand` (without `-g`), in the monad `RM`. -/
def expandCode (o : Options) : List Instruction → RM Unit
  | [] => pure ()
  | i :: rest => do
    expandInstruction o i
    match AsmInstr.annotKind i with
    | some kind => if kind.toNat = 2 && lblFollows rest then expandInstruction o builtinNop
    | none => pure ()
    expandCode o rest

/-- `expand_function` -/
def expandFunction (o : Options) (fn : Asm.Function) : Res Asm.Function :=
  let run : EM (List Instruction) := do
    setCurrentFunction fn.fn_sig fn.fn_code
    fixupFunctionEntry fn.fn_sig
    (expandCode o fn.fn_code).run' none
    getCurrentFunction
  match run.run' {} with
  | .ok c => .OK { fn with fn_code := c }
  | .error s => .Error s

/-- `expand_fundef` -/
def expandFundef (o : Options) : Asm.Fundef → Res Asm.Fundef
  | .Internal f =>
    match expandFunction o f with
    | .OK tf => .OK (.Internal tf)
    | .Error msg => .Error msg
  | .External ef => .OK (.External ef)

/-- `expand_program` -/
def expandProgram (o : Options) (p : Asm.Program) : Res Asm.Program :=
  transformPartialProgram2 (fun _ f => expandFundef o f) (fun _ v => .OK v) p

/-! ## Tests -/

private def testSig : Signature := { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }

/-- The code of a function after expansion. -/
private def expandedCode (sg : Signature) (code : List Instruction) :
    Option (List Instruction) :=
  match expandFunction {} { fn_sig := sg, fn_code := code } with
  | .OK f => some f.fn_code
  | .Error _ => none

-- `Pseqw` against `x0` is one `sltiu`.
#guard match expandedCode testSig [.Pseqw .X5 (.X .X6) .X0] with
  | some [.Psltiuw .X5 (.X .X6) _] => true
  | _ => false

-- `Pcsel` takes four instructions.
#guard (expandedCode testSig [.Pcsel .X5 .X6 .X7 .X8]).map List.length == some 4

-- A frame of 16 bytes for a non-variadic function: save the old `sp` in
-- `X30`, decrement `sp`, CFI, store the back link.
#guard match expandedCode testSig
    [.Pallocframe 16 (Integers.Ptrofs.repr 0), .Pfreeframe 16 (Integers.Ptrofs.repr 0)] with
  | some (.Pmv .X30 .X2 :: _) => true
  | _ => false

-- `va_start` outside a variadic function is an error.
#guard (expandedCode testSig
    [.Pallocframe 16 (Integers.Ptrofs.repr 0),
     .Pbuiltin (.EF_builtin "__builtin_va_start" testSig) [.BA (.IR .X10)] .BR_none]).isNone

-- In a variadic function it is accepted.
#guard (expandedCode { testSig with sig_cc := { cc_default with cc_vararg := some 0 } }
    [.Pallocframe 16 (Integers.Ptrofs.repr 0),
     .Pbuiltin (.EF_builtin "__builtin_va_start" testSig) [.BA (.IR .X10)] .BR_none]).isSome

-- `memcpy` of 16 bytes aligned on 8: two `ld`/`sd` pairs.
#guard (expandedCode testSig
    [.Pbuiltin (.EF_memcpy 16 8) [.BA (.IR .X10), .BA (.IR .X11)] .BR_none]).map List.length
  == some 4

end Asmexpand
end RiscV
end CC
