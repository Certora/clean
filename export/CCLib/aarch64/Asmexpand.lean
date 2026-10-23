/-
  Expansion of built-ins and pseudo-instructions for AArch64 — port of
  `aarch64/Asmexpand.ml`.

  `Asmexpand` runs after the verified compiler, on the generated `Asm`
  program: it replaces the pseudo-instructions `Pallocframe`, `Pfreeframe`
  and `Pcvtx2w` by machine instructions, expands the built-in functions
  that are inlined (`memcpy`, volatile loads and stores, `va_start`, byte
  swaps, bit counting, fused multiply-add, …) and relaxes the conditional
  branches whose target is out of range.  Like the OCaml code, it is not
  verified.

  Differences from OCaml:
  * `Archi.abi` is the argument `abi` of the functions that depend on it.
  * The global reference `current_function_stacksize` is the field
    `stacksize` of the state of the expansion monad `Asmexpandaux.M`.
  * `raise (Error s)`, `assert false` and `invalid_arg` become errors of the
    monad.
  * Offsets of type `Ptrofs` are converted to `Int64` (they are the same
    type in OCaml, AArch64 being a 64-bit target).
  * Not ported: the DWARF register numbering (`int_reg_to_dwarf`,
    `float_reg_to_dwarf`, `preg_to_dwarf`), which only serves `-g` (see
    `CCLib.backend.Asmexpandaux`).
-/
import CCLib.aarch64.Asmgen
import CCLib.backend.Asmexpandaux

namespace CC
namespace Asmexpand

open Asm Asmexpandaux Conventions1

instance : AsmInstr Instruction where
  labelOf | .Plabel l => some l | _ => none
  mkLabel := .Plabel
  annotKind | .Pbuiltin (.EF_annot kind _ _) _ _ => some kind | _ => none
  isDebug | .Pbuiltin (.EF_debug _ _ _) _ _ => true | _ => false
  mkBuiltin ef := .Pbuiltin ef [] .BR_none

/-- The expansion monad for AArch64 code. -/
abbrev EM := Asmexpandaux.M Instruction

/-- `Int.repr` -/
abbrev I32 (n : Int) : Integers.Int := Integers.Int.repr n
/-- `Int64.repr` -/
abbrev L (n : Int) : Integers.Int64 := Integers.Int64.repr n

/-- A pointer offset as a 64-bit integer. -/
def ofs64 (n : Integers.Ptrofs) : Integers.Int64 := Integers.Ptrofs.to_int64 n

/-! ## Setting or offsetting a register by a constant -/

/-- `expand_loadimm32` -/
def expandLoadimm32 (dst : Ireg) (n : Integers.Int) : EM Unit :=
  for i in Asmgen.loadimm32 dst n [] do emit i

/-- `expand_addimm64` -/
def expandAddimm64 (dst src : Iregsp) (n : Integers.Int64) : EM Unit :=
  for i in Asmgen.addimm64 dst src n [] do emit i

/-! ## Handling of varargs -/

/-- `align n a` (for `a` a power of 2) -/
def align (n a : Int) : Int := (n + a - 1) / a * a

/-- `typesize` -/
def typesize : ATyp → Int
  | .Tint | .Tany32 | .Tsingle => 4
  | .Tlong | .Tany64 | .Tfloat => 8

/-- `reserve_stack` -/
def reserveStack (abi : AbiKind) (stk : Int) (ty : ATyp) : Int :=
  match abi with
  | .AAPCS64 => stk + 8
  | .Apple => align stk (typesize ty) + typesize ty

/-- `next_arg_locations`: the number of integer registers, FP registers
    and stack bytes used to pass the fixed parameters. -/
def nextArgLocations (abi : AbiKind) (ir fr stk : Int) : List ATyp → Int × Int × Int
  | [] => (ir, fr, stk)
  | ty :: l =>
    match ty with
    | .Tint | .Tlong | .Tany32 | .Tany64 =>
      if ir < 8 then nextArgLocations abi (ir + 1) fr stk l
      else nextArgLocations abi ir fr (reserveStack abi stk ty) l
    | .Tfloat | .Tsingle =>
      if fr < 8 then nextArgLocations abi ir (fr + 1) stk l
      else nextArgLocations abi ir fr (reserveStack abi stk ty) l

/-- `int_param_regs` -/
def intParamReg : Nat → Ireg
  | 0 => .X0 | 1 => .X1 | 2 => .X2 | 3 => .X3
  | 4 => .X4 | 5 => .X5 | 6 => .X6 | _ => .X7

/-- `float_param_regs` -/
def floatParamReg : Nat → Freg
  | 0 => .D0 | 1 => .D1 | 2 => .D2 | 3 => .D3
  | 4 => .D4 | 5 => .D5 | 6 => .D6 | _ => .D7

/-- `size_save_register_area` -/
def sizeSaveRegisterArea : Int := 8 * 8 + 8 * 16

/-- The integer-register part of `save_parameter_registers` (the `while`
    loop): save `X_i … X_7`, by pairs from an even register. -/
def saveIntRegs (i : Nat) : EM Unit :=
  if h : i < 8 then do
    let pos : Int := 8 * 16 + i * 8
    if i % 2 = 0 then
      emit (.Pstp (intParamReg i) (intParamReg (i + 1)) (.ADimm .XSP (L pos)))
      saveIntRegs (i + 2)
    else
      emit (.Pstrx (intParamReg i) (.ADimm .XSP (L pos)))
      saveIntRegs (i + 1)
  else pure ()
termination_by 8 - i

/-- `save_parameter_registers ir fr`: allocate memory on the stack and save
    the registers used for parameter passing, except those used to pass
    the fixed parameters. -/
def saveParameterRegisters (ir fr : Nat) : EM Unit := do
  emit (.Psubimm .X .XSP .XSP sizeSaveRegisterArea)
  saveIntRegs ir
  for i in List.range' fr (8 - fr) do
    emit (.Pstrd (floatParamReg i) (.ADimm .XSP (L (i * 16))))

/-- `expand_builtin_va_start_aapcs64`: initialize the `va_list` pointed to
    by `r` (the structure `__stack`, `__gr_top`, `__vr_top`, `__gr_offs`,
    `__vr_offs`). -/
def expandBuiltinVaStartAapcs64 (r : Ireg) : EM Unit := do
  let (ir, fr, stk) := nextArgLocations .AAPCS64 0 0 0 (← getCurrentFunctionArgs)
  let cs := (← get).stacksize
  let stackOfs := cs + stk
  let grTopOfs := cs
  let vrTopOfs := cs - 64
  let grOffs := -((8 - ir) * 8)
  let vrOffs := -((8 - fr) * 16)
  -- va->__stack = sp + stack_ofs
  expandAddimm64 (.RR1 .X16) .XSP (L stackOfs)
  emit (.Pstrx .X16 (.ADimm (.RR1 r) (L 0)))
  -- va->__gr_top = sp + gr_top_ofs
  if grTopOfs ≠ stackOfs then
    expandAddimm64 (.RR1 .X16) .XSP (L grTopOfs)
  emit (.Pstrx .X16 (.ADimm (.RR1 r) (L 8)))
  -- va->__vr_top = sp + vr_top_ofs
  expandAddimm64 (.RR1 .X16) .XSP (L vrTopOfs)
  emit (.Pstrx .X16 (.ADimm (.RR1 r) (L 16)))
  -- va->__gr_offs = gr_offs
  expandLoadimm32 .X16 (I32 grOffs)
  emit (.Pstrw .X16 (.ADimm (.RR1 r) (L 24)))
  -- va->__vr_offs = vr_offs
  expandLoadimm32 .X16 (I32 vrOffs)
  emit (.Pstrw .X16 (.ADimm (.RR1 r) (L 28)))

/-- `expand_builtin_va_start_apple`: on macOS, `va_list` is a pointer and
    all variadic arguments are passed on the stack. -/
def expandBuiltinVaStartApple (r : Ireg) : EM Unit := do
  let (_, _, stk) := nextArgLocations .Apple 0 0 0 (← getCurrentFunctionArgs)
  let stk := align stk 8
  let stackOfs := (← get).stacksize + stk
  -- *va = sp + stack_ofs
  expandAddimm64 (.RR1 .X16) .XSP (L stackOfs)
  emit (.Pstrx .X16 (.ADimm (.RR1 r) (L 0)))

/-- `expand_builtin_va_start` -/
def expandBuiltinVaStart (abi : AbiKind) (r : Ireg) : EM Unit := do
  if !(← isCurrentFunctionVariadic) then
    error "Fatal error: va_start used in non-vararg function"
  match abi with
  | .AAPCS64 => expandBuiltinVaStartAapcs64 r
  | .Apple => expandBuiltinVaStartApple r

/-! ## Handling of annotations -/

/-- `expand_annot_val` -/
def expandAnnotVal (kind : Positive) (txt : String) (targ : ATyp)
    (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg) : EM Unit := do
  emit (.Pbuiltin (.EF_annot kind txt [targ]) args .BR_none)
  match args, res with
  | [.BA (.IR src)], .BR (.IR dst) => if dst ≠ src then emit (.Pmov (.RR1 dst) (.RR1 src))
  | [.BA (.FR src)], .BR (.FR dst) => if dst ≠ src then emit (.Pfmov dst src)
  | _, _ => error "ill-formed __builtin_annot_val"

/-! ## Handling of `memcpy`

Unaligned memory accesses are assumed to be efficient, so the accesses are
as wide as possible, up to 16 bytes.  Temporary registers: x15, x16, x17,
x29, x30. -/

/-- `offset_in_range` (the bound 512 comes from `ldp`/`stp`) -/
def offsetInRange (ofs : Integers.Int64) : Bool :=
  let o := Integers.Int64.signed ofs
  0 ≤ o && o < 512

/-- `memcpy_small_arg` -/
def memcpySmallArg (sz : Int) (arg : BuiltinArg Preg) (tmp : Ireg) :
    EM (Iregsp × Integers.Int64) :=
  match arg with
  | .BA (.IR r) => pure (.RR1 r, L 0)
  | .BA_addrstack ofs =>
    let ofs := ofs64 ofs
    if offsetInRange ofs && offsetInRange (Integers.Int64.add ofs (L sz))
        && Integers.Int64.signed ofs % 8 = 0 then
      pure (.XSP, ofs)
    else do
      expandAddimm64 (.RR1 tmp) .XSP ofs
      pure (.RR1 tmp, L 0)
  | _ => error "memcpy_small_arg"

/-- The loop `copy` of `expand_builtin_memcpy_small`. -/
def memcpySmallCopy (rsrc rdst : Iregsp) : Nat → Integers.Int64 → Integers.Int64 → EM Unit
  | sz, osrc, odst =>
    if h16 : sz ≥ 16 then do
      emit (.Pldp .X16 .X30 (.ADimm rsrc osrc))
      emit (.Pstp .X16 .X30 (.ADimm rdst odst))
      memcpySmallCopy rsrc rdst (sz - 16) (Integers.Int64.add osrc (L 16))
        (Integers.Int64.add odst (L 16))
    else if h8 : sz ≥ 8 then do
      emit (.Pldrx .X16 (.ADimm rsrc osrc))
      emit (.Pstrx .X16 (.ADimm rdst odst))
      memcpySmallCopy rsrc rdst (sz - 8) (Integers.Int64.add osrc (L 8))
        (Integers.Int64.add odst (L 8))
    else if h4 : sz ≥ 4 then do
      emit (.Pldrw .X16 (.ADimm rsrc osrc))
      emit (.Pstrw .X16 (.ADimm rdst odst))
      memcpySmallCopy rsrc rdst (sz - 4) (Integers.Int64.add osrc (L 4))
        (Integers.Int64.add odst (L 4))
    else if h2 : sz ≥ 2 then do
      emit (.Pldrh .W .X16 (.ADimm rsrc osrc))
      emit (.Pstrh .X16 (.ADimm rdst odst))
      memcpySmallCopy rsrc rdst (sz - 2) (Integers.Int64.add osrc (L 2))
        (Integers.Int64.add odst (L 2))
    else if h1 : sz ≥ 1 then do
      emit (.Pldrb .W .X16 (.ADimm rsrc osrc))
      emit (.Pstrb .X16 (.ADimm rdst odst))
      memcpySmallCopy rsrc rdst (sz - 1) (Integers.Int64.add osrc (L 1))
        (Integers.Int64.add odst (L 1))
    else pure ()
termination_by sz => sz

/-- `expand_builtin_memcpy_small` -/
def expandBuiltinMemcpySmall (sz : Nat) (src dst : BuiltinArg Preg) : EM Unit := do
  let tsrc : Ireg := if dst ≠ .BA (.IR .X17) then .X17 else .X15
  let tdst : Ireg := if src ≠ .BA (.IR .X15) then .X15 else .X17
  let (rsrc, osrc) ← memcpySmallArg sz src tsrc
  let (rdst, odst) ← memcpySmallArg sz dst tdst
  memcpySmallCopy rsrc rdst sz osrc odst

/-- `memcpy_big_arg` -/
def memcpyBigArg (arg : BuiltinArg Preg) (tmp : Ireg) : EM Unit :=
  match arg with
  | .BA (.IR r) => emit (.Pmov (.RR1 tmp) (.RR1 r))
  | .BA_addrstack ofs => expandAddimm64 (.RR1 tmp) .XSP (ofs64 ofs)
  | _ => error "memcpy_big_arg"

/-- `expand_builtin_memcpy_big` -/
def expandBuiltinMemcpyBig (sz : Nat) (src dst : BuiltinArg Preg) : EM Unit := do
  if sz < 16 then error "expand_builtin_memcpy_big"
  memcpyBigArg src .X30
  memcpyBigArg dst .X14
  let lbl ← newLabel
  expandLoadimm32 .X15 (I32 (sz / 16))
  emit (.Plabel lbl)
  emit (.Pldp .X16 .X17 (.ADpostincr (.RR1 .X30) (L 16)))
  emit (.Pstp .X16 .X17 (.ADpostincr (.RR1 .X14) (L 16)))
  emit (.Psubimm .W (.RR1 .X15) (.RR1 .X15) 1)
  emit (.Pcbnz .W .X15 lbl)
  if sz % 16 ≥ 8 then
    emit (.Pldrx .X16 (.ADpostincr (.RR1 .X30) (L 8)))
    emit (.Pstrx .X16 (.ADpostincr (.RR1 .X14) (L 8)))
  if sz % 8 ≥ 4 then
    emit (.Pldrw .X16 (.ADpostincr (.RR1 .X30) (L 4)))
    emit (.Pstrw .X16 (.ADpostincr (.RR1 .X14) (L 4)))
  if sz % 4 ≥ 2 then
    emit (.Pldrh .W .X16 (.ADpostincr (.RR1 .X30) (L 2)))
    emit (.Pstrh .X16 (.ADpostincr (.RR1 .X14) (L 2)))
  if sz % 2 ≥ 1 then
    emit (.Pldrb .W .X16 (.ADpostincr (.RR1 .X30) (L 1)))
    emit (.Pstrb .X16 (.ADpostincr (.RR1 .X14) (L 1)))

/-- `expand_builtin_memcpy` -/
def expandBuiltinMemcpy (sz : Int) (args : List (BuiltinArg Preg)) : EM Unit :=
  match args with
  | [dst, src] =>
    if sz < 64 then expandBuiltinMemcpySmall sz.toNat src dst
    else expandBuiltinMemcpyBig sz.toNat src dst
  | _ => error "expand_builtin_memcpy"

/-! ## Handling of volatile reads and writes -/

/-- `expand_builtin_vload_common` -/
def expandBuiltinVloadCommon (chunk : Chunk) (base : Iregsp) (ofs : Integers.Int64)
    (res : BuiltinRes Preg) : EM Unit :=
  let addr := Addressing.ADimm base ofs
  match chunk, res with
  | .Mbool, .BR (.IR res) | .Mint8unsigned, .BR (.IR res) => emit (.Pldrb .W res addr)
  | .Mint8signed, .BR (.IR res) => emit (.Pldrsb .W res addr)
  | .Mint16unsigned, .BR (.IR res) => emit (.Pldrh .W res addr)
  | .Mint16signed, .BR (.IR res) => emit (.Pldrsh .W res addr)
  | .Mint32, .BR (.IR res) => emit (.Pldrw res addr)
  | .Mint64, .BR (.IR res) => emit (.Pldrx res addr)
  | .Mfloat32, .BR (.FR res) => emit (.Pldrs res addr)
  | .Mfloat64, .BR (.FR res) => emit (.Pldrd res addr)
  | _, _ => error "expand_builtin_vload_common"

/-- `expand_builtin_vload` -/
def expandBuiltinVload (chunk : Chunk) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit :=
  match args with
  | [.BA (.IR addr)] => expandBuiltinVloadCommon chunk (.RR1 addr) (L 0) res
  | [.BA_addrstack ofs] =>
    let ofs := ofs64 ofs
    if Asmgen.offsetRepresentable (sizeChunk chunk) ofs then
      expandBuiltinVloadCommon chunk .XSP ofs res
    else do
      expandAddimm64 (.RR1 .X16) .XSP ofs
      expandBuiltinVloadCommon chunk (.RR1 .X16) (L 0) res
  | [.BA_addptr (.BA (.IR addr)) (.BA_long ofs)] =>
    if Asmgen.offsetRepresentable (sizeChunk chunk) ofs then
      expandBuiltinVloadCommon chunk (.RR1 addr) ofs res
    else do
      expandAddimm64 (.RR1 .X16) (.RR1 addr) ofs
      expandBuiltinVloadCommon chunk (.RR1 .X16) (L 0) res
  | _ => error "expand_builtin_vload"

/-- `expand_builtin_vstore_common` -/
def expandBuiltinVstoreCommon (chunk : Chunk) (base : Iregsp) (ofs : Integers.Int64)
    (src : BuiltinArg Preg) : EM Unit :=
  let addr := Addressing.ADimm base ofs
  match chunk, src with
  | .Mbool, .BA (.IR src) | .Mint8signed, .BA (.IR src) | .Mint8unsigned, .BA (.IR src) =>
    emit (.Pstrb src addr)
  | .Mint16signed, .BA (.IR src) | .Mint16unsigned, .BA (.IR src) => emit (.Pstrh src addr)
  | .Mint32, .BA (.IR src) => emit (.Pstrw src addr)
  | .Mint64, .BA (.IR src) => emit (.Pstrx src addr)
  | .Mfloat32, .BA (.FR src) => emit (.Pstrs src addr)
  | .Mfloat64, .BA (.FR src) => emit (.Pstrd src addr)
  | _, _ => error "expand_builtin_vstore_common"

/-- `expand_builtin_vstore` -/
def expandBuiltinVstore (chunk : Chunk) (args : List (BuiltinArg Preg)) : EM Unit :=
  match args with
  | [.BA (.IR addr), src] => expandBuiltinVstoreCommon chunk (.RR1 addr) (L 0) src
  | [.BA_addrstack ofs, src] =>
    let ofs := ofs64 ofs
    if Asmgen.offsetRepresentable (sizeChunk chunk) ofs then
      expandBuiltinVstoreCommon chunk .XSP ofs src
    else do
      expandAddimm64 (.RR1 .X16) .XSP ofs
      expandBuiltinVstoreCommon chunk (.RR1 .X16) (L 0) src
  | [.BA_addptr (.BA (.IR addr)) (.BA_long ofs), src] =>
    if Asmgen.offsetRepresentable (sizeChunk chunk) ofs then
      expandBuiltinVstoreCommon chunk (.RR1 addr) ofs src
    else do
      expandAddimm64 (.RR1 .X16) (.RR1 addr) ofs
      expandBuiltinVstoreCommon chunk (.RR1 .X16) (L 0) src
  | _ => error "expand_builtin_vstore"

/-! ## Compiler-inlined built-ins -/

/-- `expand_builtin_inline` -/
def expandBuiltinInline (abi : AbiKind) (name : String) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit :=
  match name, args, res with
  -- Synchronization
  | "__builtin_membar", [], _ => pure ()
  -- No operation
  | "__builtin_nop", [], _ => emit .Pnop
  -- Optimization hint
  | "__builtin_unreachable", [], _ => pure ()
  -- Byte swap
  | "__builtin_bswap", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_bswap32", [.BA (.IR a1)], .BR (.IR res) => emit (.Prev .W res a1)
  | "__builtin_bswap64", [.BA (.IR a1)], .BR (.IR res) => emit (.Prev .X res a1)
  | "__builtin_bswap16", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Prev16 .W res a1)
    emit (.Pandimm .W res (.RR0 res) 0xFFFF)
  -- Count leading zeros, leading sign bits, trailing zeros
  | "__builtin_clz", [.BA (.IR a1)], .BR (.IR res) => emit (.Pclz .W res a1)
  | "__builtin_clzl", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_clzll", [.BA (.IR a1)], .BR (.IR res) => emit (.Pclz .X res a1)
  | "__builtin_cls", [.BA (.IR a1)], .BR (.IR res) => emit (.Pcls .W res a1)
  | "__builtin_clsl", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_clsll", [.BA (.IR a1)], .BR (.IR res) => emit (.Pcls .X res a1)
  | "__builtin_ctz", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Prbit .W res a1)
    emit (.Pclz .W res res)
  | "__builtin_ctzl", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_ctzll", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Prbit .X res a1)
    emit (.Pclz .X res res)
  -- Float arithmetic
  | "__builtin_fsqrt", [.BA (.FR a1)], .BR (.FR res)
  | "__builtin_sqrt", [.BA (.FR a1)], .BR (.FR res) => emit (.Pfsqrt .D res a1)
  | "__builtin_fmadd", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfmadd .D res a1 a2 a3)
  | "__builtin_fmsub", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfmsub .D res a1 a2 a3)
  | "__builtin_fnmadd", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfnmadd .D res a1 a2 a3)
  | "__builtin_fnmsub", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    emit (.Pfnmsub .D res a1 a2 a3)
  | "__builtin_fmax", [.BA (.FR a1), .BA (.FR a2)], .BR (.FR res) =>
    emit (.Pfmax .D res a1 a2)
  | "__builtin_fmin", [.BA (.FR a1), .BA (.FR a2)], .BR (.FR res) =>
    emit (.Pfmin .D res a1 a2)
  -- Vararg
  | "__builtin_va_start", [.BA (.IR a)], _ => expandBuiltinVaStart abi a
  -- Catch-all
  | _, _, _ => error ("unrecognized builtin " ++ name)

/-! ## Branch relaxation -/

/-- Remove the comments of a piece of inline assembly (OCaml:
    `Str.global_replace re_asm_comment ""` with `re_asm_comment` matching
    `//` anywhere or `#` at the beginning of a line, up to the end of the
    line). -/
def removeAsmComments (txt : String) : List String :=
  (txt.splitOn "\n").map fun l =>
    if l.startsWith "#" then ""
    else (l.splitOn "//").headD ""

/-- `num_statements_inline_asm`: an upper bound on the number of machine
    instructions of a piece of inline assembly (comments and blank lines
    removed, then split at newlines and `;`). -/
def numStatementsInlineAsm (txt : String) : Nat :=
  let lines := removeAsmComments txt
  -- `Str.global_replace re_blank_line ""`: a blank line followed by a newline
  let n := lines.length
  let lines := (lines.zipIdx).filterMap fun (l, i) =>
    if i + 1 < n && l.toList.all (fun c => c == ' ' || c == '\t') then none else some (l, i)
  let txt := "\n".intercalate (lines.map (·.1))
  let txt :=
    if lines.getLast?.map (·.2) == some (n - 1) || lines.isEmpty then txt else txt ++ "\n"
  -- `Str.split re_asm_stmt_separator`: the non-empty fields
  let fields := ((txt.splitOn "\n").flatMap (·.splitOn ";"))
  let fields := fields.dropWhile (· == "")
  let fields := if fields.getLast? == some "" then fields.dropLast else fields
  fields.length

#guard numStatementsInlineAsm "mov x0, x1 // comment\n\n  \nnop; nop" = 3
#guard numStatementsInlineAsm "# directive\nnop" = 1
#guard numStatementsInlineAsm "" = 0

/-- `BInfo.builtin_size` -/
def builtinSize : ExtFun → Nat
  | .EF_annot _ _ _ => 0
  | .EF_debug _ _ _ => 0
  | .EF_inline_asm txt _ _ => 4 * numStatementsInlineAsm txt
  | _ => 0

/-- `BInfo.instr_size` -/
def instrSize : Instruction → Nat
  | .Pfmovimmd _ _ | .Pfmovimms _ _ => 8
  | .Ploadsymbol _ _ => 2
  | .Pbtbl _ tbl => 12 + 4 * tbl.length
  | .Plabel _ | .Pcfi_adjust _ | .Pcfi_rel_offset _ => 0
  | .Pbuiltin ef _ _ => builtinSize ef
  | _ => 4

/-- `BInfo.branch_overflow` -/
def branchOverflow (map : Positive → Except String Int) (pc : Int) (lbl : Positive)
    (range : Int) : Except String Bool := do
  let displ := (← map lbl) - pc
  return displ < -range || displ ≥ range

/-- `BInfo.need_relaxation` -/
def needRelaxation (map : Positive → Except String Int) (pc : Int) :
    Instruction → Except String Bool
  -- +/- 1 MB
  | .Pbc _ lbl | .Pcbnz _ _ lbl | .Pcbz _ _ lbl => branchOverflow map pc lbl 0x100000
  -- +/- 32 KB
  | .Ptbnz _ _ _ lbl | .Ptbz _ _ _ lbl => branchOverflow map pc lbl 0x8000
  | _ => .ok false

/-- `BInfo.negate_testcond` -/
def negateTestcond : Testcond → Testcond
  | .TCeq => .TCne | .TCne => .TCeq
  | .TChs => .TClo | .TClo => .TChs
  | .TCmi => .TCpl | .TCpl => .TCmi
  | .TChi => .TCls | .TCls => .TChi
  | .TCge => .TClt | .TClt => .TCge
  | .TCgt => .TCle | .TCle => .TCgt

theorem negateTestcond_involutive (c : Testcond) : negateTestcond (negateTestcond c) = c := by
  cases c <;> rfl

/-- `BInfo.relax_instruction`: a conditional branch to a far label becomes
    the opposite branch over an unconditional branch to it. -/
def relaxInstruction : Instruction → EM (List Instruction)
  | .Pbc c lbl => do
    let lbl' ← newLabel
    return [.Pbc (negateTestcond c) lbl', .Pb lbl, .Plabel lbl']
  | .Pcbnz sz r lbl => do
    let lbl' ← newLabel
    return [.Pcbz sz r lbl', .Pb lbl, .Plabel lbl']
  | .Pcbz sz r lbl => do
    let lbl' ← newLabel
    return [.Pcbnz sz r lbl', .Pb lbl, .Plabel lbl']
  | .Ptbnz sz r n lbl => do
    let lbl' ← newLabel
    return [.Ptbz sz r n lbl', .Pb lbl, .Plabel lbl']
  | .Ptbz sz r n lbl => do
    let lbl' ← newLabel
    return [.Ptbnz sz r n lbl', .Pb lbl, .Plabel lbl']
  | _ => error "relax_instruction"

/-- `Asmexpand.BInfo` -/
def bInfo : BranchInformation Instruction where
  instrSize := instrSize
  needRelaxation := needRelaxation
  relaxInstruction := relaxInstruction

/-! ## Expansion of instructions -/

/-- `expand_instruction` -/
def expandInstruction (abi : AbiKind) (instr : Instruction) : EM Unit :=
  match instr with
  | .Pallocframe sz linkofs retaddrofs => do
    emit (.Pmov (.RR1 .X15) .XSP)
    if (← isCurrentFunctionVariadic) && abi == .AAPCS64 then
      let (ir, fr, _) := nextArgLocations abi 0 0 0 (← getCurrentFunctionArgs)
      saveParameterRegisters ir.toNat fr.toNat
      modify fun s => { s with stacksize := sz + sizeSaveRegisterArea }
    else
      modify fun s => { s with stacksize := sz }
    if Integers.Ptrofs.unsigned retaddrofs ≠ Integers.Ptrofs.unsigned linkofs + 8 then
      error "Pallocframe: return address not next to the back link"
    let sz1 := sz - Integers.Ptrofs.unsigned linkofs
    if sz1 ≤ 512 then
      emit (.Pstp .X15 .X30 (.ADpreincr .XSP (L (-sz1))))
      emit (.Pcfi_adjust (I32 sz1))
    else
      expandAddimm64 .XSP .XSP (L (-sz1))
      emit (.Pcfi_adjust (I32 sz1))
      emit (.Pstp .X15 .X30 (.ADimm .XSP (L 0)))
    let sz2 := sz - sz1
    if sz2 > 0 then
      expandAddimm64 .XSP .XSP (L (-sz2))
      emit (.Pcfi_adjust (I32 sz2))
  | .Pfreeframe _ _ => do
    expandAddimm64 .XSP .XSP (L (← get).stacksize)
  | .Pcvtx2w _ =>
    -- no code generated, the upper 32 bits of rd will be ignored
    pure ()
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_builtin name _ => expandBuiltinInline abi name args res
    | .EF_vload chunk => expandBuiltinVload chunk args res
    | .EF_vstore chunk => expandBuiltinVstore chunk args
    | .EF_annot_val kind txt targ => expandAnnotVal kind txt targ args res
    | .EF_memcpy sz _ => expandBuiltinMemcpy sz args
    | .EF_annot _ _ _ | .EF_debug _ _ _ | .EF_inline_asm _ _ _ => emit instr
    | _ => error "expand_instruction: unexpected builtin"
  | _ => emit instr

/-- `expand_function`: expansion, then branch relaxation. -/
def expandFunction (abi : AbiKind) (fn : Asm.Function) : Res Asm.Function :=
  let run : EM (List Instruction) := do
    setCurrentFunction fn.fn_sig fn.fn_code
    expand (expandInstruction abi) fn.fn_code
    BranchRelaxation.relaxation bInfo (← getCurrentFunction)
  match run.run' {} with
  | .ok c => .OK { fn with fn_code := c }
  | .error s => .Error s

/-- `expand_fundef` -/
def expandFundef (abi : AbiKind) : Asm.Fundef → Res Asm.Fundef
  | .Internal f =>
    match expandFunction abi f with
    | .OK tf => .OK (.Internal tf)
    | .Error msg => .Error msg
  | .External ef => .OK (.External ef)

/-- `expand_program` -/
def expandProgram (abi : AbiKind) (p : Asm.Program) : Res Asm.Program :=
  transformPartialProgram2 (fun _ f => expandFundef abi f) (fun _ v => .OK v) p

/-! ## Tests -/

private def testSig : Signature := { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }

/-- The code of a function after expansion. -/
private def expandedCode (code : List Instruction) : Option (List Instruction) :=
  match expandFunction .AAPCS64 { fn_sig := testSig, fn_code := code } with
  | .OK f => some f.fn_code
  | .Error _ => none


-- A small frame: one `stp` with pre-increment, the frame is freed by
-- adding the frame size back to `sp`.
#guard (expandedCode [.Pallocframe 32 (Integers.Ptrofs.repr 0) (Integers.Ptrofs.repr 8),
    .Pfreeframe 32 (Integers.Ptrofs.repr 0), .Pret .X30]).map List.length == some 5

-- A far conditional branch is relaxed into the opposite branch over `b`.
#guard match expandedCode
    ([.Pbc .TCeq (.xO .xH)] ++ List.replicate 300000 .Pnop ++ [.Plabel (.xO .xH)]) with
  | some (.Pbc .TCne _ :: .Pb _ :: .Plabel _ :: _) => true
  | _ => false

-- A near one is not.
#guard match expandedCode ([.Pbc .TCeq (.xO .xH), .Pnop, .Plabel (.xO .xH)]) with
  | some [.Pbc .TCeq _, .Pnop, .Plabel _] => true
  | _ => false

-- `memcpy` of 20 bytes between two registers: one 16-byte pair, one word.
#guard (expandedCode [.Pbuiltin (.EF_memcpy 20 4) [.BA (.IR .X0), .BA (.IR .X1)] .BR_none]).map
    List.length == some 4

-- An unknown built-in is an error.
#guard (expandedCode [.Pbuiltin (.EF_builtin "__builtin_foo" testSig) [] .BR_none]).isNone

end Asmexpand
end CC
