/-
  Expansion of built-ins and pseudo-instructions for x86 — port of
  `x86/Asmexpand.ml`.

  `Asmexpand` runs after the verified compiler, on the generated `Asm`
  program: it replaces the pseudo-instructions `Pallocframe` and
  `Pfreeframe` by stack-pointer adjustments, expands the built-in functions
  that are inlined (`memcpy`, volatile loads and stores, `va_start`, byte
  swaps, bit scans, fused multiply-add, …) and adds the register set-up that
  calls to variadic functions need.  Like the OCaml code, it is not verified.

  Differences from OCaml:
  * The port's x86 target is x86-64 (`Archi.ptr64 = true`), so only the
    64-bit paths are ported: the IA32 versions of `Pallocframe`,
    `Pfreeframe` and `va_start` (`sp_adjustment_32`,
    `expand_builtin_va_start_32`, which read
    `PrintAsmaux.current_function_stacksize`) are not, and the `memcpy`
    expansion always uses 8-byte integer moves (on x86-64 the
    `Clflags.option_ffpu` alternative is unreachable).  The expansions of the
    built-ins on split 64-bit integers (`__builtin_negl`, `__builtin_addl`,
    …), which only arise on IA32, are ported nevertheless.
  * `Archi.win64` and the atom `intern_string "__compcert_va_saveregs"` are
    the fields of `Options`.
  * The global reference `current_function_stacksize` is the field
    `stacksize` of the state of the expansion monad `Asmexpandaux.M`.
  * `raise (Error s)`, `assert false` and `invalid_arg` become errors of the
    monad.
  * Not ported: the DWARF register numbering (`int_reg_to_dwarf`,
    `float_reg_to_dwarf`, `preg_to_dwarf`), which only serves `-g` (see
    `CCLib.backend.Asmexpandaux`).
-/
import CCLib.x86.Asmgen
import CCLib.backend.Asmexpandaux

namespace CC
namespace X86
namespace Asmexpand

open Asm Asmexpandaux

instance : AsmInstr Instruction where
  labelOf | .Plabel l => some l | _ => none
  mkLabel := .Plabel
  annotKind | .Pbuiltin (.EF_annot kind _ _) _ _ => some kind | _ => none
  isDebug | .Pbuiltin (.EF_debug _ _ _) _ _ => true | _ => false
  mkBuiltin ef := .Pbuiltin ef [] .BR_none

/-- The expansion monad for x86 code. -/
abbrev EM := Asmexpandaux.M Instruction

/-- The configuration used by the expansion. -/
structure Options where
  /-- `Archi.win64` (Windows x86-64 calling conventions) -/
  win64 : Bool := false
  /-- `intern_string "__compcert_va_saveregs"` -/
  vaSaveregs : Ident := identOfString "__compcert_va_saveregs"

/-- `Int.repr` -/
abbrev I32 (n : Int) : Integers.Int := Integers.Int.repr n
/-- `Int64.repr` -/
abbrev L (n : Int) : Integers.Int64 := Integers.Int64.repr n

/-! ## Stack-pointer adjustment -/

/-- `align n a` (for `a` a power of 2): round `n` up to a multiple of `a`
    if `n ≥ 0`, down otherwise. -/
def align (n a : Int) : Int :=
  if n ≥ 0 then (n + a - 1) / a * a else n / a * a

/-- `sp_adjustment_elf64 sz`: the adjustment of `RSP` that allocates a frame
    of size `sz`, and the offset of the register save area of a variadic
    function (`-1` if not variadic). -/
def spAdjustmentElf64 (sz : Int) : EM (Int × Int) := do
  if ← isCurrentFunctionVariadic then
    -- If variadic, add room for register save area, which must be 16-aligned
    let ofs := align (sz - 8) 16
    let sz := ofs + 176 + 8
    -- Preserve proper alignment of the stack
    let sz := align sz 16
    -- The top 8 bytes have already been allocated by the "call" instruction.
    return (sz - 8, ofs)
  else
    let sz := align sz 16
    return (sz - 8, -1)

/-- `sp_adjustment_win64` -/
def spAdjustmentWin64 (sz : Int) : Int := align sz 16 - 8

/-! ## Annotations -/

/-- `expand_annot_val` -/
def expandAnnotVal (kind : Positive) (txt : String) (targ : ATyp)
    (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg) : EM Unit := do
  emit (.Pbuiltin (.EF_annot kind txt [targ]) args .BR_none)
  match args, res with
  | [.BA (.IR src)], .BR (.IR dst) => if dst ≠ src then emit (.Pmov_rr dst src)
  | [.BA (.FR src)], .BR (.FR dst) => if dst ≠ src then emit (.Pmovsd_ff dst src)
  | _, _ => error "ill-formed __builtin_annot_intval"

/-! ## Operations on addressing modes -/

/-- `offset_addressing` -/
def offsetAddressing : Addrmode → Int → Addrmode
  | .Addrmode base ofs cst, delta =>
    .Addrmode base ofs
      (match cst with
       | .inl n => .inl (n + delta)
       | .inr (id, n) => .inr (id, Integers.Ptrofs.add n (Integers.Ptrofs.repr delta)))

/-- `linear_addr` -/
def linearAddr (reg : Ireg) (ofs : Int) : Addrmode := .Addrmode (some reg) none (.inl ofs)

/-- `global_addr` -/
def globalAddr (id : Ident) (ofs : Integers.Ptrofs) : Addrmode :=
  .Addrmode none none (.inr (id, ofs))

/-- `emit_leaq`: a `leaq` instruction that does not overflow. -/
def emitLeaq (r : Ireg) (addr : Addrmode) : EM Unit :=
  match Asmgen.normalizeAddrmode64 addr with
  | (addr, none) => emit (.Pleaq r addr)
  | (addr, some delta) => do
    emit (.Pleaq r addr)
    emit (.Paddq_ri r delta)

/-- `addressing_of_builtin_arg` -/
def addressingOfBuiltinArg : BuiltinArg Preg → EM Addrmode
  | .BA (.IR r) => pure (linearAddr r 0)
  | .BA_addrstack ofs => pure (linearAddr .RSP (Integers.Ptrofs.unsigned ofs))
  | .BA_addrglobal id ofs => pure (globalAddr id ofs)
  | .BA_addptr (.BA (.IR r)) (.BA_int n) => pure (linearAddr r (Integers.Int.signed n))
  | .BA_addptr (.BA (.IR r)) (.BA_long n) => pure (linearAddr r (Integers.Int64.signed n))
  | _ => error "addressing_of_builtin_arg"

/-! ## Handling of `memcpy`

Unaligned memory accesses are fast on x86, so large accesses are used
regardless of alignment. -/

/-- The loop `copy` of `expand_builtin_memcpy_small`. -/
def memcpySmallCopy : Nat → Addrmode → Addrmode → EM Unit
  | sz, src, dst =>
    if h8 : sz ≥ 8 then do
      emit (.Pmovq_rm .RCX src)
      emit (.Pmovq_mr dst .RCX)
      memcpySmallCopy (sz - 8) (offsetAddressing src 8) (offsetAddressing dst 8)
    else if h4 : sz ≥ 4 then do
      emit (.Pmovl_rm .RCX src)
      emit (.Pmovl_mr dst .RCX)
      memcpySmallCopy (sz - 4) (offsetAddressing src 4) (offsetAddressing dst 4)
    else if h2 : sz ≥ 2 then do
      emit (.Pmovw_rm .RCX src)
      emit (.Pmovw_mr dst .RCX)
      memcpySmallCopy (sz - 2) (offsetAddressing src 2) (offsetAddressing dst 2)
    else if h1 : sz ≥ 1 then do
      emit (.Pmovb_rm .RCX src)
      emit (.Pmovb_mr dst .RCX)
      memcpySmallCopy (sz - 1) (offsetAddressing src 1) (offsetAddressing dst 1)
    else pure ()
termination_by sz => sz

/-- `expand_builtin_memcpy_small` -/
def expandBuiltinMemcpySmall (sz : Nat) (src dst : BuiltinArg Preg) : EM Unit := do
  memcpySmallCopy sz (← addressingOfBuiltinArg src) (← addressingOfBuiltinArg dst)

/-- `expand_builtin_memcpy_big` -/
def expandBuiltinMemcpyBig (sz : Nat) (src dst : BuiltinArg Preg) : EM Unit := do
  if src ≠ .BA (.IR .RSI) then emitLeaq .RSI (← addressingOfBuiltinArg src)
  if dst ≠ .BA (.IR .RDI) then emitLeaq .RDI (← addressingOfBuiltinArg dst)
  emit (.Pmovl_ri .RCX (I32 (sz / 4)))
  emit .Prep_movsl
  if sz % 4 ≥ 2 then emit .Pmovsw
  if sz % 2 ≥ 1 then emit .Pmovsb

/-- `expand_builtin_memcpy` -/
def expandBuiltinMemcpy (sz : Int) (args : List (BuiltinArg Preg)) : EM Unit :=
  match args with
  | [dst, src] =>
    if sz ≤ 32 then expandBuiltinMemcpySmall sz.toNat src dst
    else expandBuiltinMemcpyBig sz.toNat src dst
  | _ => error "expand_builtin_memcpy"

/-! ## Handling of volatile reads and writes -/

/-- `expand_builtin_vload_common` -/
def expandBuiltinVloadCommon (chunk : Chunk) (addr : Addrmode) (res : BuiltinRes Preg) :
    EM Unit :=
  match chunk, res with
  | .Mbool, .BR (.IR res) | .Mint8unsigned, .BR (.IR res) => emit (.Pmovzb_rm res addr)
  | .Mint8signed, .BR (.IR res) => emit (.Pmovsb_rm res addr)
  | .Mint16unsigned, .BR (.IR res) => emit (.Pmovzw_rm res addr)
  | .Mint16signed, .BR (.IR res) => emit (.Pmovsw_rm res addr)
  | .Mint32, .BR (.IR res) => emit (.Pmovl_rm res addr)
  | .Mint64, .BR (.IR res) => emit (.Pmovq_rm res addr)
  | .Mint64, .BR_splitlong (.BR (.IR res1)) (.BR (.IR res2)) => do
    let addr' := offsetAddressing addr 4
    if !Asmgen.addressingMentions addr res2 then
      emit (.Pmovl_rm res2 addr)
      emit (.Pmovl_rm res1 addr')
    else
      emit (.Pmovl_rm res1 addr')
      emit (.Pmovl_rm res2 addr)
  | .Mfloat32, .BR (.FR res) => emit (.Pmovss_fm res addr)
  | .Mfloat64, .BR (.FR res) => emit (.Pmovsd_fm res addr)
  | _, _ => error "expand_builtin_vload_common"

/-- `expand_builtin_vload` -/
def expandBuiltinVload (chunk : Chunk) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit :=
  match args with
  | [addr] => do expandBuiltinVloadCommon chunk (← addressingOfBuiltinArg addr) res
  | _ => error "expand_builtin_vload"

/-- `expand_builtin_vstore_common` -/
def expandBuiltinVstoreCommon (chunk : Chunk) (addr : Addrmode) (src : BuiltinArg Preg)
    (tmp : Ireg) : EM Unit :=
  match chunk, src with
  | .Mbool, .BA (.IR src) | .Mint8signed, .BA (.IR src) | .Mint8unsigned, .BA (.IR src) =>
    if Archi.ptr64 || Asmgen.lowIreg src then emit (.Pmovb_mr addr src)
    else do
      emit (.Pmov_rr tmp src)
      emit (.Pmovb_mr addr tmp)
  | .Mint16signed, .BA (.IR src) | .Mint16unsigned, .BA (.IR src) => emit (.Pmovw_mr addr src)
  | .Mint32, .BA (.IR src) => emit (.Pmovl_mr addr src)
  | .Mint64, .BA (.IR src) => emit (.Pmovq_mr addr src)
  | .Mint64, .BA_splitlong (.BA (.IR src1)) (.BA (.IR src2)) => do
    let addr' := offsetAddressing addr 4
    emit (.Pmovl_mr addr src2)
    emit (.Pmovl_mr addr' src1)
  | .Mfloat32, .BA (.FR src) => emit (.Pmovss_mf addr src)
  | .Mfloat64, .BA (.FR src) => emit (.Pmovsd_mf addr src)
  | _, _ => error "expand_builtin_vstore_common"

/-- `expand_builtin_vstore` -/
def expandBuiltinVstore (chunk : Chunk) (args : List (BuiltinArg Preg)) : EM Unit :=
  match args with
  | [addr, src] => do
    let addr ← addressingOfBuiltinArg addr
    expandBuiltinVstoreCommon chunk addr src
      (if Asmgen.addressingMentions addr .RAX then .RCX else .RAX)
  | _ => error "expand_builtin_vstore"

/-! ## Handling of varargs -/

/-- `next_arg_locations`: the number of integer registers, FP registers
    and stack bytes used to pass the fixed parameters (x86-64 ELF). -/
def nextArgLocations (ir fr ofs : Int) : List ATyp → Int × Int × Int
  | [] => (ir, fr, ofs)
  | ty :: l =>
    match ty with
    | .Tint | .Tlong | .Tany32 | .Tany64 =>
      if ir < 6 then nextArgLocations (ir + 1) fr ofs l
      else nextArgLocations ir fr (ofs + 8) l
    | .Tfloat | .Tsingle =>
      if fr < 8 then nextArgLocations ir (fr + 1) ofs l
      else nextArgLocations ir fr (ofs + 8) l

/-- `expand_builtin_va_start_elf64`: `r` points to the structure
    `{ unsigned gp_offset; unsigned fp_offset; void *overflow_arg_area;
       void *reg_save_area; }`. -/
def expandBuiltinVaStartElf64 (r : Ireg) : EM Unit := do
  if !(← isCurrentFunctionVariadic) then
    error "Fatal error: va_start used in non-vararg function"
  let (ir, fr, ofs) := nextArgLocations 0 0 0 (← getCurrentFunctionArgs)
  let cs := (← get).stacksize
  let gpOffset := ir * 8
  let fpOffset := 6 * 8 + fr * 16
  let overflowArgArea := cs + ofs
  let regSaveArea := cs - 192
  if r = .RAX then error "expand_builtin_va_start_elf64"
  emit (.Pmovl_ri .RAX (I32 gpOffset))
  emit (.Pmovl_mr (linearAddr r 0) .RAX)
  emit (.Pmovl_ri .RAX (I32 fpOffset))
  emit (.Pmovl_mr (linearAddr r 4) .RAX)
  emitLeaq .RAX (linearAddr .RSP overflowArgArea)
  emit (.Pmovq_mr (linearAddr r 8) .RAX)
  emitLeaq .RAX (linearAddr .RSP regSaveArea)
  emit (.Pmovq_mr (linearAddr r 16) .RAX)

/-- `expand_builtin_va_start_win64` -/
def expandBuiltinVaStartWin64 (r : Ireg) : EM Unit := do
  if !(← isCurrentFunctionVariadic) then
    error "Fatal error: va_start used in non-vararg function"
  let numArgs := (← getCurrentFunctionArgs).length
  let ofs := (← get).stacksize + 8 * numArgs
  emitLeaq .RAX (linearAddr .RSP ofs)
  emit (.Pmovq_mr (linearAddr r 0) .RAX)

/-! ## FMA operations

`vfmadd<i><j><k> r1, r2, r3` performs `r1 := ri * rj + rk`. -/

/-- `expand_fma` -/
def expandFma (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg)
    (i132 i213 i231 : Freg → Freg → Freg → Instruction) : EM Unit :=
  match args, res with
  | [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    if res = a1 then emit (i132 a1 a3 a2)
    else if res = a2 then emit (i213 a2 a1 a3)
    else if res = a3 then emit (i231 a3 a1 a2)
    else do
      emit (.Pmovsd_ff res a3)
      emit (i231 res a1 a2)
  | _, _ => error "ill-formed fma builtin"

/-! ## Compiler-inlined built-ins -/

/-- `expand_builtin_inline` -/
def expandBuiltinInline (o : Options) (name : String) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : EM Unit :=
  match name, args, res with
  -- Integer arithmetic
  | "__builtin_bswap", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_bswap32", [.BA (.IR a1)], .BR (.IR res) => do
    if a1 ≠ res then emit (.Pmov_rr res a1)
    emit (.Pbswap32 res)
  | "__builtin_bswap64", [.BA (.IR a1)], .BR (.IR res) => do
    if a1 ≠ res then emit (.Pmov_rr res a1)
    emit (.Pbswap64 res)
  | "__builtin_bswap64", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) => do
    if !(ah = .RAX && al = .RDX && rh = .RDX && rl = .RAX) then
      error "__builtin_bswap64: unexpected registers"
    emit (.Pbswap32 .RAX)
    emit (.Pbswap32 .RDX)
  | "__builtin_bswap16", [.BA (.IR a1)], .BR (.IR res) => do
    if a1 ≠ res then emit (.Pmov_rr res a1)
    emit (.Pbswap16 res)
  | "__builtin_clz", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Pbsrl res a1)
    emit (.Pxorl_ri res (I32 31))
  | "__builtin_clzl", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_clzll", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Pbsrq res a1)
    emit (.Pxorl_ri res (I32 63))
  | "__builtin_clzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) => do
    let lbl1 ← newLabel
    let lbl2 ← newLabel
    emit (.Ptestl_rr ah ah)
    emit (.Pjcc .Cond_e lbl1)
    emit (.Pbsrl res ah)
    emit (.Pxorl_ri res (I32 31))
    emit (.Pjmp_l lbl2)
    emit (.Plabel lbl1)
    emit (.Pbsrl res al)
    emit (.Pxorl_ri res (I32 63))
    emit (.Plabel lbl2)
  | "__builtin_ctz", [.BA (.IR a1)], .BR (.IR res) => emit (.Pbsfl res a1)
  | "__builtin_ctzl", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_ctzll", [.BA (.IR a1)], .BR (.IR res) => emit (.Pbsfq res a1)
  | "__builtin_ctzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) => do
    let lbl1 ← newLabel
    let lbl2 ← newLabel
    emit (.Ptestl_rr al al)
    emit (.Pjcc .Cond_e lbl1)
    emit (.Pbsfl res al)
    emit (.Pjmp_l lbl2)
    emit (.Plabel lbl1)
    emit (.Pbsfl res ah)
    emit (.Paddl_ri res (I32 32))
    emit (.Plabel lbl2)
  -- Float arithmetic
  | "__builtin_fsqrt", [.BA (.FR a1)], .BR (.FR res)
  | "__builtin_sqrt", [.BA (.FR a1)], .BR (.FR res) => emit (.Psqrtsd res a1)
  | "__builtin_fmadd", _, _ => expandFma args res .Pfmadd132 .Pfmadd213 .Pfmadd231
  | "__builtin_fmsub", _, _ => expandFma args res .Pfmsub132 .Pfmsub213 .Pfmsub231
  | "__builtin_fnmadd", _, _ => expandFma args res .Pfnmadd132 .Pfnmadd213 .Pfnmadd231
  | "__builtin_fnmsub", _, _ => expandFma args res .Pfnmsub132 .Pfnmsub213 .Pfnmsub231
  -- 64-bit integer arithmetic (IA32)
  | "__builtin_negl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) => do
    if !(ah = .RDX && al = .RAX && rh = .RDX && rl = .RAX) then
      error "__builtin_negl: unexpected registers"
    emit (.Pnegl .RAX)
    emit (.Padcl_ri .RDX (I32 0))
    emit (.Pnegl .RDX)
  | "__builtin_addl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) => do
    if !(ah = .RDX && al = .RAX && bh = .RCX && bl = .RBX && rh = .RDX && rl = .RAX) then
      error "__builtin_addl: unexpected registers"
    emit (.Paddl_rr .RAX .RBX)
    emit (.Padcl_rr .RDX .RCX)
  | "__builtin_subl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) => do
    if !(ah = .RDX && al = .RAX && bh = .RCX && bl = .RBX && rh = .RDX && rl = .RAX) then
      error "__builtin_subl: unexpected registers"
    emit (.Psubl_rr .RAX .RBX)
    emit (.Psbbl_rr .RDX .RCX)
  | "__builtin_mull", [.BA (.IR a), .BA (.IR b)], .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) => do
    if !(a = .RAX && b = .RDX && rh = .RDX && rl = .RAX) then
      error "__builtin_mull: unexpected registers"
    emit (.Pmull_r .RDX)
  -- Memory accesses
  | "__builtin_read16_reversed", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Pmovzw_rm res (linearAddr a1 0))
    emit (.Pbswap16 res)
  | "__builtin_read32_reversed", [.BA (.IR a1)], .BR (.IR res) => do
    emit (.Pmovl_rm res (linearAddr a1 0))
    emit (.Pbswap32 res)
  | "__builtin_write16_reversed", [.BA (.IR a1), .BA (.IR a2)], _ => do
    let tmp : Ireg := if a1 = .RCX then .RDX else .RCX
    if a2 ≠ tmp then emit (.Pmov_rr tmp a2)
    emit (.Pbswap16 tmp)
    emit (.Pmovw_mr (linearAddr a1 0) tmp)
  | "__builtin_write32_reversed", [.BA (.IR a1), .BA (.IR a2)], _ => do
    let tmp : Ireg := if a1 = .RCX then .RDX else .RCX
    if a2 ≠ tmp then emit (.Pmov_rr tmp a2)
    emit (.Pbswap32 tmp)
    emit (.Pmovl_mr (linearAddr a1 0) tmp)
  -- Vararg stuff
  | "__builtin_va_start", [.BA (.IR a)], _ => do
    if a ≠ .RDX then error "__builtin_va_start: unexpected register"
    if o.win64 then expandBuiltinVaStartWin64 a else expandBuiltinVaStartElf64 a
  -- Synchronization
  | "__builtin_membar", [], _ => pure ()
  -- No operation
  | "__builtin_nop", [], _ => emit .Pnop
  -- Optimization hint
  | "__builtin_unreachable", [], _ => pure ()
  -- Catch-all
  | _, _, _ => error ("unrecognized builtin " ++ name)

/-! ## Calls to variadic functions -/

/-- `fixup_funcall_elf64`: for x86-64 ELF, register `AL` must contain the
    number of XMM registers used for parameter passing when calling a
    variadic (or unprototyped) function. -/
def fixupFuncallElf64 (sg : Signature) : EM Unit :=
  if sg.sig_cc.cc_vararg.isSome || sg.sig_cc.cc_unproto then
    let (_, fr, _) := nextArgLocations 0 0 0 sg.projArgs
    emit (.Pmovl_ri .RAX (I32 fr))
  else pure ()

/-- `copy_fregs_to_iregs` -/
def copyFregsToIregs : List ATyp → List Freg → List Ireg → EM Unit
  | ty :: args, f1 :: fr, i1 :: ir => do
    match ty with
    | .Tfloat | .Tsingle => emit (.Pmovq_rf i1 f1)
    | _ => pure ()
    copyFregsToIregs args fr ir
  | _, _, _ => pure ()

/-- `fixup_funcall_win64`: for x86-64 Windows, floating-point arguments
    passed in FP registers must also be passed in integer registers when
    calling a variadic function. -/
def fixupFuncallWin64 (sg : Signature) : EM Unit :=
  if sg.sig_cc.cc_vararg.isSome then
    copyFregsToIregs sg.projArgs [.XMM0, .XMM1, .XMM2, .XMM3] [.RCX, .RDX, .R8, .R9]
  else pure ()

/-- `fixup_funcall` -/
def fixupFuncall (o : Options) (sg : Signature) : EM Unit :=
  if o.win64 then fixupFuncallWin64 sg else fixupFuncallElf64 sg

/-! ## Expansion of instructions -/

/-- The signature of `__compcert_va_saveregs`. -/
def vaSaveregsSig : Signature := { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }

/-- `expand_instruction` -/
def expandInstruction (o : Options) (instr : Instruction) : EM Unit :=
  match instr with
  | .Pallocframe sz _ ofsLink =>
    if o.win64 then do
      let sz := spAdjustmentWin64 sz
      if ← isCurrentFunctionVariadic then
        -- Save parameters passed in registers in reserved stack area
        emit (.Pcall_s o.vaSaveregs vaSaveregsSig)
      -- Allocate frame
      emit (.Psubq_ri .RSP (L sz))
      emit (.Pcfi_adjust (I32 sz))
      -- Stack chaining
      emitLeaq .RAX (linearAddr .RSP (sz + 8))
      emit (.Pmovq_mr (linearAddr .RSP (Integers.Ptrofs.unsigned ofsLink)) .RAX)
      modify fun s => { s with stacksize := sz + 8 }
    else do
      let (sz, saveRegs) ← spAdjustmentElf64 sz
      -- Allocate frame
      emit (.Psubq_ri .RSP (L sz))
      emit (.Pcfi_adjust (I32 sz))
      if saveRegs ≥ 0 then
        -- Save the registers
        emitLeaq .R10 (linearAddr .RSP saveRegs)
        emit (.Pcall_s o.vaSaveregs vaSaveregsSig)
      -- Stack chaining
      let fullsz := sz + 8
      emitLeaq .RAX (linearAddr .RSP fullsz)
      emit (.Pmovq_mr (linearAddr .RSP (Integers.Ptrofs.unsigned ofsLink)) .RAX)
      modify fun s => { s with stacksize := fullsz }
  | .Pfreeframe sz _ _ =>
    if o.win64 then emit (.Paddq_ri .RSP (L (spAdjustmentWin64 sz)))
    else do
      let (sz, _) ← spAdjustmentElf64 sz
      emit (.Paddq_ri .RSP (L sz))
  | .Pjmp_s _ sg | .Pjmp_r _ sg | .Pcall_s _ sg | .Pcall_r _ sg => do
    fixupFuncall o sg
    emit instr
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_builtin name _ => expandBuiltinInline o name args res
    | .EF_vload chunk => expandBuiltinVload chunk args res
    | .EF_vstore chunk => expandBuiltinVstore chunk args
    | .EF_memcpy sz _ => expandBuiltinMemcpy sz args
    | .EF_annot_val kind txt targ => expandAnnotVal kind txt targ args res
    | .EF_annot _ _ _ | .EF_debug _ _ _ | .EF_inline_asm _ _ _ => emit instr
    | _ => error "expand_instruction: unexpected builtin"
  | _ => emit instr

/-- `expand_function` -/
def expandFunction (o : Options) (fn : Asm.Function) : Res Asm.Function :=
  let run : EM (List Instruction) := do
    setCurrentFunction fn.fn_sig fn.fn_code
    expand (expandInstruction o) fn.fn_code
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
private def varSig : Signature :=
  { sig_args := [.Xint], sig_res := .Xvoid, sig_cc := { cc_default with cc_vararg := some 1 } }

/-- The code of a function after expansion. -/
private def expandedCode (o : Options) (sg : Signature) (code : List Instruction) :
    Option (List Instruction) :=
  match expandFunction o { fn_sig := sg, fn_code := code } with
  | .OK f => some f.fn_code
  | .Error _ => none

-- A frame of 24 bytes: `subq $24` (32 - 8), CFI, stack chaining; freed by
-- `addq $24`.
#guard match expandedCode {} testSig
    [.Pallocframe 24 (Integers.Ptrofs.repr 16) (Integers.Ptrofs.repr 0),
     .Pfreeframe 24 (Integers.Ptrofs.repr 16) (Integers.Ptrofs.repr 0), .Pret] with
  | some [.Psubq_ri .RSP n, .Pcfi_adjust _, .Pleaq .RAX _, .Pmovq_mr _ .RAX,
          .Paddq_ri .RSP m, .Pret] => n == L 24 && m == L 24
  | _ => false

-- A call to a variadic function sets `AL` (here: no FP argument).
#guard match expandedCode {} testSig [.Pcall_s (.xO .xH) varSig] with
  | some [.Pmovl_ri .RAX n, .Pcall_s _ _] => n == I32 0
  | _ => false

-- `memcpy` of 12 bytes: one 8-byte move, one 4-byte move.
#guard (expandedCode {} testSig
    [.Pbuiltin (.EF_memcpy 12 4) [.BA (.IR .RDI), .BA (.IR .RSI)] .BR_none]).map List.length
  == some 4

-- `memcpy` of 100 bytes uses `rep movsl`.
#guard match expandedCode {} testSig
    [.Pbuiltin (.EF_memcpy 100 4) [.BA (.IR .RDI), .BA (.IR .RSI)] .BR_none] with
  | some [.Pmovl_ri .RCX _, .Prep_movsl] => true
  | _ => false

-- `va_start` outside a variadic function is an error.
#guard (expandedCode {} testSig
    [.Pbuiltin (.EF_builtin "__builtin_va_start" testSig) [.BA (.IR .RDX)] .BR_none]).isNone

end Asmexpand
end X86
end CC
