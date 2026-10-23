/-
  Expansion of built-ins and pseudo-instructions for ARM — port of
  `arm/Asmexpand.ml`.

  `Asmexpand` runs after the verified compiler, on the generated `Asm`
  program: it replaces `Pallocframe`/`Pfreeframe` by explicit stack-pointer
  arithmetic, expands the built-in functions that are inlined (`memcpy`,
  volatile loads and stores, `va_start`, byte swaps, `clz`/`ctz`, 64-bit
  arithmetic on register pairs, …), inserts the moves required by the
  calling conventions (EABI soft-float or hard-float), and finally calls
  `Constantexpand.expandConstants` to emit the literal pools.  Like the OCaml
  code, it is not verified.

  Differences from OCaml:
  * The configuration (`Compopts.thumb`, `Archi.thumb2_support`,
    `Archi.abi` through `Asmgen.Options`; `Archi.big_endian`;
    `Clflags.option_ffpu`; the options of `Constantexpand`) is the argument
    `Asmexpand.Options`.
  * The state of `Asmexpandaux` (code being emitted, fresh labels, current
    function, `current_function_stacksize`) is threaded by the monad
    `Asmexpandaux.M`; `raise (Error s)`, `assert false` and `invalid_arg`
    become errors of this monad.
  * The mutable array `used` of `FixupHF` is a `List Bool` threaded through
    `findSingle`/`findDouble`.
  * Not ported: the DWARF register numbering (`int_reg_to_dwarf`,
    `float_reg_to_dwarf`, `preg_to_dwarf`), which only serves `-g`.
-/
import CCLib.arm.Asmgen
import CCLib.arm.Constantexpand

namespace CC
namespace Arm
namespace Asmexpand

open Asm Asmexpandaux Constantexpand

/-- The configuration used by the expansion. -/
structure Options where
  /-- `Compopts.thumb`, `Archi.thumb2_support`, `Archi.abi`, … -/
  asmgen : Asmgen.Options
  /-- `Archi.big_endian` -/
  bigEndian : Bool := false
  /-- `Clflags.option_ffpu` -/
  ffpu : Bool := true
  /-- the options of `Constantexpand` -/
  constants : Constantexpand.Options := {}

/-- `Compopts.thumb ()` (`Clflags.option_mthumb`) -/
def Options.thumb (o : Options) : Bool := o.asmgen.thumb ()

/-- A stack offset as a 32-bit integer. -/
def ofsInt (n : Integers.Ptrofs) : Integers.Int := Integers.Int.repr (Integers.Ptrofs.signed n)

/-- `Int.repr` -/
abbrev I (n : Int) : Integers.Int := Integers.Int.repr n

/-! ## Constants -/

/-- `Asmexpand.expand_movimm` -/
def expandMovimm (o : Options) (dst : Ireg) (n : Integers.Int) : EM Unit :=
  for i in Asmgen.loadimm o.asmgen dst n [] do emit i

/-- `Asmexpand.expand_subimm` -/
def expandSubimm (o : Options) (dst src : Ireg) (n : Integers.Int) : EM Unit :=
  if dst ≠ src || n ≠ Integers.Int.zero then
    for i in Asmgen.addimm o.asmgen dst src (Integers.Int.neg n) [] do emit i
  else pure ()

/-- `Asmexpand.expand_addimm` -/
def expandAddimm (o : Options) (dst src : Ireg) (n : Integers.Int) : EM Unit :=
  if dst ≠ src || n ≠ Integers.Int.zero then
    for i in Asmgen.addimm o.asmgen dst src n [] do emit i
  else pure ()

/-- `Asmexpand.expand_int64_arith`: compute the low word in `IR14` first if
    it would overwrite an argument still needed. -/
def expandInt64Arith (conflict : Bool) (rl : Ireg) (fn : Ireg → EM Unit) : EM Unit :=
  if conflict then do
    fn .IR14
    emit (.Pmov rl (.SOreg .IR14))
  else fn rl

/-! ## Annotations -/

/-- `Asmexpand.expand_annot_val` -/
def expandAnnotVal (kind : Positive) (txt : String) (targ : ATyp) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit := do
  emit (.Pbuiltin (.EF_annot kind txt [targ]) args .BR_none)
  match args, res with
  | [.BA (.IR src)], .BR (.IR dst) => if dst ≠ src then emit (.Pmov dst (.SOreg src))
  | [.BA (.FR src)], .BR (.FR dst) => if dst ≠ src then emit (.Pfcpyd dst src)
  | _, _ => error "ill-formed __builtin_annot_intval"

/-! ## `memcpy`

The ARM has strict alignment constraints for 2- and 4-byte accesses; 8-byte
accesses must be 4-aligned. -/

/-- `Asmexpand.memcpy_small_arg` -/
def memcpySmallArg (o : Options) (sz : Int) (arg : BuiltinArg Preg) (tmp : Ireg) :
    EM (Ireg × Integers.Int) :=
  let offsetInRange (ofs : Integers.Int) : Bool :=
    let n := Integers.Int.signed ofs
    n ≤ 128 && n ≥ -128
  match arg with
  | .BA (.IR r) => return (r, Integers.Int.zero)
  | .BA_addrstack ofs =>
    let ofs := ofsInt ofs
    if offsetInRange ofs && offsetInRange (Integers.Int.add ofs (I sz)) then
      return (.IR13, ofs)
    else do
      expandAddimm o tmp .IR13 ofs
      return (tmp, Integers.Int.zero)
  | _ => error "memcpy_small_arg"

/-- `Asmexpand.expand_builtin_memcpy_small` -/
def expandBuiltinMemcpySmall (o : Options) (sz al : Int) (src dst : BuiltinArg Preg) :
    EM Unit := do
  let tsrc : Ireg := if dst ≠ .BA (.IR .IR2) then .IR2 else .IR3
  let tdst : Ireg := if src ≠ .BA (.IR .IR3) then .IR3 else .IR2
  let (rsrc, osrc) ← memcpySmallArg o sz src tsrc
  let (rdst, odst) ← memcpySmallArg o sz dst tdst
  let add := fun (x : Integers.Int) (k : Int) => Integers.Int.add x (I k)
  let rec copy (fuel : Nat) (osrc odst : Integers.Int) (sz : Int) : EM Unit :=
    match fuel with
    | 0 => pure ()
    | fuel + 1 =>
      if sz ≥ 8 && al ≥ 4 && o.ffpu then do
        emit (.Pfldd .FR7 rsrc osrc); emit (.Pfstd .FR7 rdst odst)
        copy fuel (add osrc 8) (add odst 8) (sz - 8)
      else if sz ≥ 4 && al ≥ 4 then do
        emit (.Pldr .IR14 rsrc (.SOimm osrc)); emit (.Pstr .IR14 rdst (.SOimm odst))
        copy fuel (add osrc 4) (add odst 4) (sz - 4)
      else if sz ≥ 2 && al ≥ 2 then do
        emit (.Pldrh .IR14 rsrc (.SOimm osrc)); emit (.Pstrh .IR14 rdst (.SOimm odst))
        copy fuel (add osrc 2) (add odst 2) (sz - 2)
      else if sz ≥ 1 then do
        emit (.Pldrb .IR14 rsrc (.SOimm osrc)); emit (.Pstrb .IR14 rdst (.SOimm odst))
        copy fuel (add osrc 1) (add odst 1) (sz - 1)
      else pure ()
  copy (sz.toNat + 1) osrc odst sz

/-- `Asmexpand.memcpy_big_arg` -/
def memcpyBigArg (o : Options) (arg : BuiltinArg Preg) (tmp : Ireg) : EM Unit :=
  match arg with
  | .BA (.IR r) => if r ≠ tmp then emit (.Pmov tmp (.SOreg r)) else pure ()
  | .BA_addrstack ofs => expandAddimm o tmp .IR13 (ofsInt ofs)
  | _ => error "memcpy_big_arg"

/-- `Asmexpand.expand_builtin_memcpy_big`: a loop copying `al` bytes (at
    most 4) at a time. -/
def expandBuiltinMemcpyBig (o : Options) (sz al : Int) (src dst : BuiltinArg Preg) :
    EM Unit := do
  if !(sz ≥ al) || al = 0 || sz % al ≠ 0 then error "expand_builtin_memcpy_big"
  let (s, d) : Ireg × Ireg := if dst ≠ .BA (.IR .IR2) then (.IR2, .IR3) else (.IR3, .IR2)
  memcpyBigArg o src s
  memcpyBigArg o dst d
  let (load, store, chunksize) : Instruction × Instruction × Int :=
    if al ≥ 4 then (.Pldr_p .IR12 s (.SOimm (I 4)), .Pstr_p .IR12 d (.SOimm (I 4)), 4)
    else if al = 2 then (.Pldrh_p .IR12 s (.SOimm (I 2)), .Pstrh_p .IR12 d (.SOimm (I 2)), 2)
    else (.Pldrb_p .IR12 s (.SOimm (I 1)), .Pstrb_p .IR12 d (.SOimm (I 1)), 1)
  expandMovimm o .IR14 (I (sz / chunksize))
  let lbl ← newLabel
  emit (.Plabel lbl)
  emit load
  emit (.Psubs .IR14 .IR14 (.SOimm (I 1)))
  emit store
  emit (.Pbne lbl)

/-- `Asmexpand.expand_builtin_memcpy` -/
def expandBuiltinMemcpy (o : Options) (sz al : Int) (args : List (BuiltinArg Preg)) : EM Unit :=
  match args with
  | [dst, src] =>
    if sz ≤ 32 then expandBuiltinMemcpySmall o sz al src dst
    else expandBuiltinMemcpyBig o sz al src dst
  | _ => error "expand_builtin_memcpy"

/-! ## Volatile reads and writes -/

/-- `Asmexpand.offset_in_range` -/
def offsetInRange (o : Options) (chunk : Chunk) (ofs : Integers.Int) : EM Bool :=
  let word := Asmgen.mkImmedMemWord o.asmgen
  match chunk with
  | .Mint8signed | .Mint16signed | .Mint16unsigned =>
    return Asmgen.mkImmedMemSmall ofs == ofs
  | .Mint8unsigned | .Mint32 => return word ofs == ofs
  | .Mfloat32 | .Mfloat64 => return Asmgen.mkImmedMemFloat ofs == ofs
  | .Mint64 =>
    let ofs4 := Integers.Int.add ofs (I 4)
    return word ofs == ofs && word ofs4 == ofs4
  | _ => error "offset_in_range"

/-- `Asmexpand.expand_builtin_vload_common` -/
def expandBuiltinVloadCommon (o : Options) (chunk : Chunk) (base : Ireg) (ofs : Integers.Int)
    (res : BuiltinRes Preg) : EM Unit :=
  match chunk, res with
  | .Mbool, .BR (.IR res) | .Mint8unsigned, .BR (.IR res) => emit (.Pldrb res base (.SOimm ofs))
  | .Mint8signed, .BR (.IR res) => emit (.Pldrsb res base (.SOimm ofs))
  | .Mint16unsigned, .BR (.IR res) => emit (.Pldrh res base (.SOimm ofs))
  | .Mint16signed, .BR (.IR res) => emit (.Pldrsh res base (.SOimm ofs))
  | .Mint32, .BR (.IR res) => emit (.Pldr res base (.SOimm ofs))
  | .Mint64, .BR_splitlong (.BR (.IR res1)) (.BR (.IR res2)) => do
    let ofs4 := Integers.Int.add ofs (I 4)
    let ofsHi := if o.bigEndian then ofs else ofs4
    let ofsLo := if o.bigEndian then ofs4 else ofs
    if base ≠ res2 then
      emit (.Pldr res2 base (.SOimm ofsLo))
      emit (.Pldr res1 base (.SOimm ofsHi))
    else
      emit (.Pldr res1 base (.SOimm ofsHi))
      emit (.Pldr res2 base (.SOimm ofsLo))
  | .Mfloat32, .BR (.FR res) => emit (.Pflds res base ofs)
  | .Mfloat64, .BR (.FR res) => emit (.Pfldd res base ofs)
  | _, _ => error "expand_builtin_vload_common"

/-- `Asmexpand.expand_builtin_vload` -/
def expandBuiltinVload (o : Options) (chunk : Chunk) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit :=
  match args with
  | [.BA (.IR addr)] => expandBuiltinVloadCommon o chunk addr Integers.Int.zero res
  | [.BA_addrstack ofs] => do
    let ofs := ofsInt ofs
    if ← offsetInRange o chunk ofs then
      expandBuiltinVloadCommon o chunk .IR13 ofs res
    else
      expandAddimm o .IR14 .IR13 ofs
      expandBuiltinVloadCommon o chunk .IR14 Integers.Int.zero res
  | [.BA_addrglobal id ofs] => do
    emit (.Ploadsymbol .IR14 id ofs)
    expandBuiltinVloadCommon o chunk .IR14 Integers.Int.zero res
  | [.BA_addptr (.BA (.IR addr)) (.BA_int ofs)] => do
    if ← offsetInRange o chunk ofs then
      expandBuiltinVloadCommon o chunk addr ofs res
    else
      expandAddimm o .IR14 addr ofs
      expandBuiltinVloadCommon o chunk .IR14 Integers.Int.zero res
  | _ => error "expand_builtin_vload"

/-- `Asmexpand.expand_builtin_vstore_common` -/
def expandBuiltinVstoreCommon (o : Options) (chunk : Chunk) (base : Ireg) (ofs : Integers.Int)
    (src : BuiltinArg Preg) : EM Unit :=
  match chunk, src with
  | .Mbool, .BA (.IR src) | .Mint8signed, .BA (.IR src) | .Mint8unsigned, .BA (.IR src) =>
    emit (.Pstrb src base (.SOimm ofs))
  | .Mint16signed, .BA (.IR src) | .Mint16unsigned, .BA (.IR src) =>
    emit (.Pstrh src base (.SOimm ofs))
  | .Mint32, .BA (.IR src) => emit (.Pstr src base (.SOimm ofs))
  | .Mint64, .BA_splitlong (.BA (.IR src1)) (.BA (.IR src2)) => do
    let ofs4 := Integers.Int.add ofs (I 4)
    let ofsHi := if o.bigEndian then ofs else ofs4
    let ofsLo := if o.bigEndian then ofs4 else ofs
    emit (.Pstr src2 base (.SOimm ofsLo))
    emit (.Pstr src1 base (.SOimm ofsHi))
  | .Mfloat32, .BA (.FR src) => emit (.Pfsts src base ofs)
  | .Mfloat64, .BA (.FR src) => emit (.Pfstd src base ofs)
  | _, _ => error "expand_builtin_vstore_common"

/-- `Asmexpand.expand_builtin_vstore` -/
def expandBuiltinVstore (o : Options) (chunk : Chunk) (args : List (BuiltinArg Preg)) : EM Unit :=
  match args with
  | [.BA (.IR addr), src] => expandBuiltinVstoreCommon o chunk addr Integers.Int.zero src
  | [.BA_addrstack ofs, src] => do
    let ofs := ofsInt ofs
    if ← offsetInRange o chunk ofs then
      expandBuiltinVstoreCommon o chunk .IR13 ofs src
    else
      expandAddimm o .IR14 .IR13 ofs
      expandBuiltinVstoreCommon o chunk .IR14 Integers.Int.zero src
  | [.BA_addrglobal id ofs, src] => do
    emit (.Ploadsymbol .IR14 id ofs)
    expandBuiltinVstoreCommon o chunk .IR14 Integers.Int.zero src
  | [.BA_addptr (.BA (.IR addr)) (.BA_int ofs), src] => do
    if ← offsetInRange o chunk ofs then
      expandBuiltinVstoreCommon o chunk addr ofs src
    else
      expandAddimm o .IR14 addr ofs
      expandBuiltinVstoreCommon o chunk .IR14 Integers.Int.zero src
  | _ => error "expand_builtin_vstore"

/-! ## Variable arguments -/

/-- `Asmexpand.align` (for `a` a power of 2 and `n ≥ 0`) -/
def align (n a : Int) : Int := (n + a - 1) / a * a

/-- `Asmexpand.next_arg_location`: the stack offset of the first variadic
    argument. -/
def nextArgLocation (ir ofs : Int) : List ATyp → Int
  | [] => ir * 4 + ofs
  | ty :: l =>
    match ty with
    | .Tint | .Tsingle | .Tany32 =>
      if ir < 4 then nextArgLocation (ir + 1) ofs l else nextArgLocation ir (ofs + 4) l
    | .Tfloat | .Tlong | .Tany64 =>
      if ir < 3 then nextArgLocation (align ir 2 + 2) ofs l
      else nextArgLocation 4 (align ofs 8 + 8) l

/-- `Asmexpand.expand_builtin_va_start` -/
def expandBuiltinVaStart (o : Options) (r : Ireg) : EM Unit := do
  if !(← isCurrentFunctionVariadic) then
    error "Fatal error: va_start used in non-vararg function"
  let ofs := nextArgLocation 0 0 (← getCurrentFunctionArgs) + (← get).stacksize
  expandAddimm o .IR14 .IR13 (I ofs)
  emit (.Pstr .IR14 r (.SOimm Integers.Int.zero))

/-! ## Built-ins inlined by the compiler -/

/-- `Asmexpand.expand_builtin_inline` -/
def expandBuiltinInline (o : Options) (name : String) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit :=
  let z := Integers.Int.zero
  match name, args, res with
  -- Integer arithmetic
  | "__builtin_bswap64", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == al) rl fun rl => do
      emit (.Prev rl ah)
      emit (.Prev rh al)
  | "__builtin_bswap", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_bswap32", [.BA (.IR a1)], .BR (.IR res) => emit (.Prev res a1)
  | "__builtin_bswap16", [.BA (.IR a1)], .BR (.IR res) => emit (.Prev16 res a1)
  | "__builtin_clz", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_clzl", [.BA (.IR a1)], .BR (.IR res) => emit (.Pclz res a1)
  | "__builtin_clzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) => do
    emit (.Pclz .IR14 al)
    emit (.Pcmp ah (.SOimm z))
    emit (.Pmovite .TCeq .IR14 (.SOreg .IR14) (.SOimm z))
    emit (.Pclz res ah)
    emit (.Padd res res (.SOreg .IR14))
  | "__builtin_ctz", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_ctzl", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Psub .IR14 a1 (.SOimm (I 1)))     -- tmp := x-1
    emit (.Pmvn res (.SOreg a1))             -- res := ~(x)
    emit (.Pand res .IR14 (.SOreg res))      -- res := tmp & ~(x)
    emit (.Pclz res res)                     -- res := #leading zeros
    emit (.Prsb res res (.SOimm (I 32)))     -- res := 32 - #leading zeros
  | "__builtin_ctzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) => do
    let lbl1 ← newLabel
    let lbl2 ← newLabel
    -- low word equal to zero?
    emit (.Pcmp al (.SOimm z))
    emit (.Pbne lbl1)
    -- low word is zero: count trailing zeros in high word and add 32
    emit (.Psub .IR14 ah (.SOimm (I 1)))
    emit (.Pmvn res (.SOreg ah))
    emit (.Pand res .IR14 (.SOreg res))
    emit (.Pclz res res)
    emit (.Prsb res res (.SOimm (I 64)))
    emit (.Pb lbl2)
    -- count trailing zeros in low word
    emit (.Plabel lbl1)
    emit (.Psub .IR14 al (.SOimm (I 1)))
    emit (.Pmvn res (.SOreg al))
    emit (.Pand res .IR14 (.SOreg res))
    emit (.Pclz res res)
    emit (.Prsb res res (.SOimm (I 32)))
    emit (.Plabel lbl2)
  -- Float arithmetic
  | "__builtin_fsqrt", [.BA (.FR a1)], .BR (.FR res)
  | "__builtin_sqrt", [.BA (.FR a1)], .BR (.FR res) => emit (.Pfsqrt res a1)
  -- 64-bit integer arithmetic
  | "__builtin_negl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == ah) rl fun rl => do
      emit (.Prsbs rl al (.SOimm z))
      -- No `rsc` instruction in Thumb2: `rsc a, b, #0` is `mvn a, b; adc a, a, #0`.
      if o.thumb then
        emit (.Pmvn rh (.SOreg ah))
        emit (.Padc rh rh (.SOimm z))
      else
        emit (.Prsc rh ah (.SOimm z))
  | "__builtin_addl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == ah || rl == bh) rl fun rl => do
      emit (.Padds rl al (.SOreg bl))
      emit (.Padc rh ah (.SOreg bh))
  | "__builtin_subl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == ah || rl == bh) rl fun rl => do
      emit (.Psubs rl al (.SOreg bl))
      emit (.Psbc rh ah (.SOreg bh))
  | "__builtin_mull", [.BA (.IR a), .BA (.IR b)], .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    emit (.Pumull rl rh a b)
  -- Memory accesses
  | "__builtin_read16_reversed", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Pldrh res a1 (.SOimm z))
    emit (.Prev16 res res)
  | "__builtin_read32_reversed", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Pldr res a1 (.SOimm z))
    emit (.Prev res res)
  | "__builtin_write16_reversed", [.BA (.IR a1), .BA (.IR a2)], _ => do
    emit (.Prev16 .IR14 a2)
    emit (.Pstrh .IR14 a1 (.SOimm z))
  | "__builtin_write32_reversed", [.BA (.IR a1), .BA (.IR a2)], _ => do
    emit (.Prev .IR14 a2)
    emit (.Pstr .IR14 a1 (.SOimm z))
  -- Synchronization
  | "__builtin_membar", [], _ => pure ()
  | "__builtin_dmb", [], _ => emit .Pdmb
  | "__builtin_dsb", [], _ => emit .Pdsb
  | "__builtin_isb", [], _ => emit .Pisb
  -- Vararg stuff
  | "__builtin_va_start", [.BA (.IR a)], _ => expandBuiltinVaStart o a
  -- No operation
  | "__builtin_nop", [], _ => emit .Pnop
  -- Optimization hint
  | "__builtin_unreachable", [], _ => pure ()
  -- Catch-all
  | _, _, _ => error ("unrecognized builtin " ++ name)

/-! ## Calling conventions -/

/-- `Asmexpand.direction` -/
inductive Direction where
  | Incoming
  | Outgoing
  deriving DecidableEq

namespace FixupEABI

/-- `FixupEABI.ireg_param` -/
def iregParam : Nat → EM Ireg
  | 0 => pure .IR0 | 1 => pure .IR1 | 2 => pure .IR2 | 3 => pure .IR3
  | _ => error "FixupEABI.ireg_param"

/-- `FixupEABI.freg_param` -/
def fregParam : Nat → EM Freg
  | 0 => pure .FR0 | 1 => pure .FR1 | 2 => pure .FR2 | 3 => pure .FR3
  | _ => error "FixupEABI.freg_param"

/-- `FixupEABI.fixup_double` -/
def fixupDouble (dir : Direction) (f : Freg) (i1 i2 : Ireg) : EM Unit :=
  match dir with
  | .Incoming => emit (.Pfcpy_fii f i1 i2)   -- f <- (i1, i2)
  | .Outgoing => emit (.Pfcpy_iif i1 i2 f)   -- (i1, i2) <- f

/-- `FixupEABI.fixup_single` -/
def fixupSingle (dir : Direction) (f : Freg) (i : Ireg) : EM Unit :=
  match dir with
  | .Incoming => emit (.Pfcpy_fi f i)        -- f <- i
  | .Outgoing => emit (.Pfcpy_if i f)        -- i <- f

/-- `FixupEABI.fixup_conventions`: under the soft-float EABI, float
    arguments are passed in pairs of integer registers. -/
def fixupConventions (bigEndian : Bool) (dir : Direction) (tyl : List ATyp) : EM Unit :=
  fixup 0 tyl
where
  fixup (i : Nat) : List ATyp → EM Unit
    | [] => pure ()
    | ty :: tyl' =>
      if i < 4 then
        match ty with
        | .Tint | .Tany32 => fixup (i + 1) tyl'
        | .Tlong => fixup ((i + 1) / 2 * 2 + 2) tyl'
        | .Tfloat | .Tany64 => do
          let i := (i + 1) / 2 * 2
          if i < 4 then
            let f ← fregParam i
            let r0 ← iregParam i
            let r1 ← iregParam (i + 1)
            if bigEndian then fixupDouble dir f r1 r0 else fixupDouble dir f r0 r1
            fixup (i + 2) tyl'
        | .Tsingle => do
          fixupSingle dir (← fregParam i) (← iregParam i)
          fixup (i + 1) tyl'
      else pure ()
  termination_by tyl => tyl.length

/-- `FixupEABI.fixup_arguments` -/
def fixupArguments (bigEndian : Bool) (dir : Direction) (sg : Signature) : EM Unit :=
  fixupConventions bigEndian dir (sg.sig_args.map XType.proj)

/-- `FixupEABI.fixup_result` -/
def fixupResult (bigEndian : Bool) (dir : Direction) (sg : Signature) : EM Unit :=
  fixupConventions bigEndian dir [sg.sig_res.proj]

end FixupEABI

namespace FixupHF

/-- `FixupHF.fsize` -/
inductive Fsize where
  | Single
  | Double

/-- `FixupHF.find_single` (the array `used` of 16 booleans is threaded). -/
def findSingle (used : List Bool) (pos : Nat) : Nat × List Bool :=
  if h : pos ≥ used.length then (pos, used)
  else if used.getD pos false then findSingle used (pos + 1)
  else (pos, used.set pos true)
termination_by used.length - pos

/-- `FixupHF.find_double` -/
def findDouble (used : List Bool) (pos : Nat) : Nat × List Bool :=
  if h : pos + 1 ≥ used.length then (pos, used)
  else if used.getD pos false || used.getD (pos + 1) false then findDouble used (pos + 2)
  else (pos / 2, (used.set pos true).set (pos + 1) true)
termination_by used.length - pos

/-- `FixupHF.freg_param` -/
def fregParam : Nat → EM Freg
  | 0 => pure .FR0 | 1 => pure .FR1 | 2 => pure .FR2 | 3 => pure .FR3
  | 4 => pure .FR4 | 5 => pure .FR5 | 6 => pure .FR6 | 7 => pure .FR7
  | _ => error "FixupHF.freg_param"

/-- `FixupHF.sreg_param` -/
def sregParam : Nat → EM Sreg
  | 0 => pure .SR0 | 1 => pure .SR1 | 2 => pure .SR2 | 3 => pure .SR3
  | 4 => pure .SR4 | 5 => pure .SR5 | 6 => pure .SR6 | 7 => pure .SR7
  | 8 => pure .SR8 | 9 => pure .SR9 | 10 => pure .SR10 | 11 => pure .SR11
  | 12 => pure .SR12 | 13 => pure .SR13 | 14 => pure .SR14 | 15 => pure .SR15
  | _ => error "FixupHF.sreg_param"

/-- `FixupHF.fixup_actions`: for each float argument, the register in which
    CompCert expects it (`fr`) and the one in which the hard-float ABI passes
    it (a double register or a single register). -/
def fixupActions (used : List Bool) (fr : Nat) : List ATyp → EM (List (Nat × Fsize × Nat))
  | [] => pure []
  | ty :: tyl' =>
    match ty with
    | .Tint | .Tlong | .Tany32 => fixupActions used fr tyl'
    | .Tfloat | .Tany64 =>
      if fr ≥ 8 then pure [] else do
        let (dr, used) := findDouble used 0
        if !(dr < 8) then error "FixupHF.fixup_actions"
        return (fr, .Double, dr) :: (← fixupActions used (fr + 1) tyl')
    | .Tsingle =>
      if fr ≥ 8 then pure [] else do
        let (sr, used) := findSingle used 0
        if !(sr < 16) then error "FixupHF.fixup_actions"
        return (fr, .Single, sr) :: (← fixupActions used (fr + 1) tyl')

/-- `FixupHF.fixup_outgoing` -/
def fixupOutgoing : List (Nat × Fsize × Nat) → EM Unit
  | [] => pure ()
  | (fr, .Double, dr) :: act => do
    if fr ≠ dr then emit (.Pfcpyd (← fregParam dr) (← fregParam fr))
    fixupOutgoing act
  | (fr, .Single, sr) :: act => do
    if 2 * fr ≠ sr then emit (.Pfcpy_sf (← sregParam sr) (← fregParam fr))
    fixupOutgoing act

/-- `FixupHF.fixup_incoming` -/
def fixupIncoming : List (Nat × Fsize × Nat) → EM Unit
  | [] => pure ()
  | (fr, .Double, dr) :: act => do
    fixupIncoming act
    if fr ≠ dr then emit (.Pfcpyd (← fregParam fr) (← fregParam dr))
  | (fr, .Single, sr) :: act => do
    fixupIncoming act
    if 2 * fr ≠ sr then emit (.Pfcpy_fs (← fregParam fr) (← sregParam sr))

/-- `FixupHF.fixup_arguments` -/
def fixupArguments (bigEndian : Bool) (dir : Direction) (sg : Signature) : EM Unit :=
  if sg.sig_cc.cc_vararg.isSome then FixupEABI.fixupArguments bigEndian dir sg
  else do
    let act ← fixupActions (List.replicate 16 false) 0 (sg.sig_args.map XType.proj)
    match dir with
    | .Outgoing => fixupOutgoing act
    | .Incoming => fixupIncoming act

/-- `FixupHF.fixup_result` -/
def fixupResult (bigEndian : Bool) (dir : Direction) (sg : Signature) : EM Unit :=
  if sg.sig_cc.cc_vararg.isSome then FixupEABI.fixupResult bigEndian dir sg
  else pure ()

end FixupHF

/-- `Asmexpand.fixup_arguments` (chosen by `Configuration.abi`) -/
def fixupArguments (o : Options) (dir : Direction) (sg : Signature) : EM Unit :=
  match o.asmgen.params.abi with
  | .Softfloat => FixupEABI.fixupArguments o.bigEndian dir sg
  | .Hardfloat => FixupHF.fixupArguments o.bigEndian dir sg

/-- `Asmexpand.fixup_result` (chosen by `Configuration.abi`) -/
def fixupResult (o : Options) (dir : Direction) (sg : Signature) : EM Unit :=
  match o.asmgen.params.abi with
  | .Softfloat => FixupEABI.fixupResult o.bigEndian dir sg
  | .Hardfloat => FixupHF.fixupResult o.bigEndian dir sg

/-! ## Expansion of instructions -/

/-- `Asmexpand.expand_instruction` -/
def expandInstruction (o : Options) (instr : Instruction) : EM Unit :=
  match instr with
  | .Pallocframe sz ofs => do
    emit (.Pmov .IR12 (.SOreg .IR13))
    if ← isCurrentFunctionVariadic then
      emit (.Ppush [.IR0, .IR1, .IR2, .IR3])
      emit (.Pcfi_adjust (I 16))
    let ofs' := Integers.Ptrofs.signed ofs
    if ofs' ≥ 4096 && sz ≥ ofs' then
      expandSubimm o .IR13 .IR13 (I (sz - (ofs' + 4)))
      emit (.Ppush [.IR12])
      expandSubimm o .IR13 .IR13 (I ofs')
      emit (.Pcfi_adjust (I sz))
    else
      if !(ofs' < 4096) then error "Pallocframe: offset out of range"
      expandSubimm o .IR13 .IR13 (I sz)
      emit (.Pcfi_adjust (I sz))
      emit (.Pstr .IR12 .IR13 (.SOimm (I ofs')))
    modify fun s => { s with stacksize := sz }
  | .Pfreeframe sz ofs => do
    let sz := if ← isCurrentFunctionVariadic then 16 + sz else sz
    let ofs' := Integers.Ptrofs.signed ofs
    if Asmgen.isImmedArith o.asmgen (I sz) then
      expandAddimm o .IR13 .IR13 (I sz)
    else if ofs' ≥ 4096 then
      expandAddimm o .IR13 .IR13 (I ofs')
      emit (.Pldr .IR13 .IR13 (.SOimm Integers.Int.zero))
    else
      emit (.Pldr .IR13 .IR13 (.SOimm (I ofs')))
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_builtin name _ => expandBuiltinInline o name args res
    | .EF_vload chunk => expandBuiltinVload o chunk args res
    | .EF_vstore chunk => expandBuiltinVstore o chunk args
    | .EF_annot_val kind txt targ => expandAnnotVal kind txt targ args res
    | .EF_memcpy sz al => expandBuiltinMemcpy o sz al args
    | .EF_annot _ _ _ | .EF_debug _ _ _ | .EF_inline_asm _ _ _ => emit instr
    | _ => error "expand_instruction: unexpected builtin"
  -- Fixup for calling conventions
  | .Pbsymb _ sg => do
    fixupArguments o .Outgoing sg
    emit instr
  | .Pbreg r sg => do
    if r == .IR14 then fixupResult o .Outgoing sg else fixupArguments o .Outgoing sg
    emit instr
  | .Pblsymb _ sg | .Pblreg _ sg => do
    fixupArguments o .Outgoing sg
    emit instr
    fixupResult o .Incoming sg
  | _ => emit instr

/-- `Asmexpand.expand_function`: calling-convention fixup of the incoming
    arguments, expansion, then the literal pools of `Constantexpand`. -/
def expandFunction (o : Options) (fn : Asm.Function) : Res Asm.Function :=
  let run : EM Asm.Function := do
    setCurrentFunction fn.fn_sig fn.fn_code
    fixupArguments o .Incoming fn.fn_sig
    expand (expandInstruction o) fn.fn_code
    let code ← getCurrentFunction
    Constantexpand.expandConstants o.constants { fn with fn_code := code }
  match run.run' {} with
  | .ok f => .OK f
  | .error s => .Error s

/-- `Asmexpand.expand_fundef` -/
def expandFundef (o : Options) : Asm.Fundef → Res Asm.Fundef
  | .Internal f =>
    match expandFunction o f with
    | .OK tf => .OK (.Internal tf)
    | .Error msg => .Error msg
  | .External ef => .OK (.External ef)

/-- `Asmexpand.expand_program` -/
def expandProgram (o : Options) (p : Asm.Program) : Res Asm.Program :=
  transformPartialProgram2 (fun _ f => expandFundef o f) (fun _ v => .OK v) p

end Asmexpand
end Arm
end CC
