/-
  Translation from Mach to PowerPC assembly — port of `powerpc/Asmgen.v`
  (whole file).

  Ported: `ireg_of`, `freg_of`, `low_u`, `high_u`, `low_s`, `high_s`,
  `loadimm`, `addimm`, `andimm_base`, `andimm`, `orimm`, `xorimm`, `rolm`,
  `low64_u`, `low64_s`, `loadimm64_32s`, `loadimm64`, `loadimm64_notemp`,
  `opimm64`, `addimm64`, `orimm64`, `xorimm64`, `andimm64_base`, `andimm64`,
  `rolm64`, `accessind`, `loadind`, `storeind`, `floatcomp`, `transl_cond`,
  `crbit_for_icmp`, `crbit_for_fcmp`, `crbit_for_cond`, `condition_class`,
  `classify_condition`, `transl_cond_op`, `transl_select_op`,
  `transl_fselect_op`, `transl_op`, `int_temp_for`,
  `symbol_ofs_word_aligned`, `aindexed`, `aindexed2`, `aglobal`, `abased`,
  `ainstack`, `transl_memory_access`, `transl_load`, `transl_store`,
  `transl_epilogue`, `transl_instr`, `it1_is_parent`, `transl_code`,
  `transl_code_rec`, `transl_code'`, `transl_function`, `transf_function`,
  `transf_fundef`, `transf_program`.
  Also proved: `transl_code'_transl_code` (from `powerpc/Asmgenproof.v`).

  Differences from Rocq:
  * The linker parameters of `powerpc/Asm.v` (`symbol_is_small_data`,
    `symbol_is_rel_data`, `symbol_is_aligned`) are the explicit argument
    `lp : Asm.LinkerParams` of the functions that use them.
  * `condition_class`, a dependent type indexed by the condition and its
    arguments in Rocq, is the plain inductive `CondClass` (the register of
    the comparison with zero, or `default`); `classify_condition` returns it.
  * `assertion b; k` is `assert b k`; error messages are plain strings.
  * The source language is `CC.PowerPC.Mach`: the target-generic Mach syntax
    `CCLib.backend.MachSyntax` instantiated with the PowerPC operators
    (`CC.PowerPC.Op`) and machine registers (`CC.PowerPC.Mreg`).
-/
import CCLib.powerpc.Asm
import CCLib.backend.MachSyntax

namespace CC
namespace PowerPC

/-! ## Mach syntax over the PowerPC operators -/

namespace Mach

/-- `Mach.instruction` (instantiated for PowerPC) -/
abbrev Instruction :=
  MachSyntax.Instruction Op.Operation Op.Addressing Op.Condition Mreg
/-- `Mach.code` -/
abbrev Code := List Instruction
/-- `Mach.function` -/
abbrev Function :=
  MachSyntax.Function Op.Operation Op.Addressing Op.Condition Mreg
/-- `Mach.fundef` -/
abbrev Fundef := ASTFundef Function
/-- `Mach.program` -/
abbrev Program := ASTProgram Fundef Unit

end Mach

namespace Asmgen

open Asm Op

/-- `assertion b; k` of Rocq's error monad. -/
def assert {A : Type} (b : Bool) (k : Res A) : Res A :=
  if b then k else .Error "Assertion failed"

local notation "I" => Integers.Int.repr
local notation "L" => Integers.Int64.repr

/-! ## Extracting integer or float registers -/

/-- `Asmgen.ireg_of` -/
def iregOf (r : Mreg) : Res Ireg :=
  match pregOf r with
  | .IR mr => .OK mr
  | _ => .Error "Asmgen.ireg_of"

/-- `Asmgen.freg_of` -/
def fregOf (r : Mreg) : Res Freg :=
  match pregOf r with
  | .FR mr => .OK mr
  | _ => .Error "Asmgen.freg_of"

/-! ## Decomposition of 32-bit integer constants into 16-bit halves -/

/-- `Asmgen.low_u`: an unsigned 16-bit integer -/
def lowU (n : Integers.Int) : Integers.Int := Integers.Int.and n (I 65535)
/-- `Asmgen.high_u`: `(high_u n) << 16 | low_u n = n` -/
def highU (n : Integers.Int) : Integers.Int := Integers.Int.shru n (I 16)
/-- `Asmgen.low_s`: a signed 16-bit integer -/
def lowS (n : Integers.Int) : Integers.Int := Integers.Int.sign_ext 16 n
/-- `Asmgen.high_s`: `(high_s n) << 16 + low_s n = n` -/
def highS (n : Integers.Int) : Integers.Int :=
  Integers.Int.shru (Integers.Int.sub n (lowS n)) (I 16)

/-! ## Smart constructors for 32-bit integer constants -/

/-- `Asmgen.loadimm` -/
def loadimm (r : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq (highS n) Integers.Int.zero then .Paddi r .GPR0 (.Cint n) :: k
  else if Integers.Int.eq (lowS n) Integers.Int.zero then .Paddis r .GPR0 (.Cint (highS n)) :: k
  else .Paddis r .GPR0 (.Cint (highU n)) :: .Pori r r (.Cint (lowU n)) :: k

/-- `Asmgen.addimm` -/
def addimm (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq (highS n) Integers.Int.zero then .Paddi r1 r2 (.Cint n) :: k
  else if Integers.Int.eq (lowS n) Integers.Int.zero then .Paddis r1 r2 (.Cint (highS n)) :: k
  else .Paddis r1 r2 (.Cint (highS n)) :: .Paddi r1 r1 (.Cint (lowS n)) :: k

/-- `Asmgen.andimm_base` -/
def andimmBase (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq (highU n) Integers.Int.zero then .Pandi_ r1 r2 (.Cint n) :: k
  else if Integers.Int.eq (lowU n) Integers.Int.zero then .Pandis_ r1 r2 (.Cint (highU n)) :: k
  else loadimm .GPR0 n (.Pand_ r1 r2 .GPR0 :: k)

/-- `Asmgen.andimm` -/
def andimm (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if isRlwMask n then .Prlwinm r1 r2 Integers.Int.zero n :: k
  else andimmBase r1 r2 n k

/-- `Asmgen.orimm` -/
def orimm (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq (highU n) Integers.Int.zero then .Pori r1 r2 (.Cint n) :: k
  else if Integers.Int.eq (lowU n) Integers.Int.zero then .Poris r1 r2 (.Cint (highU n)) :: k
  else .Poris r1 r2 (.Cint (highU n)) :: .Pori r1 r1 (.Cint (lowU n)) :: k

/-- `Asmgen.xorimm` -/
def xorimm (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq (highU n) Integers.Int.zero then .Pxori r1 r2 (.Cint n) :: k
  else if Integers.Int.eq (lowU n) Integers.Int.zero then .Pxoris r1 r2 (.Cint (highU n)) :: k
  else .Pxoris r1 r2 (.Cint (highU n)) :: .Pxori r1 r1 (.Cint (lowU n)) :: k

/-- `Asmgen.rolm` -/
def rolm (r1 r2 : Ireg) (amount mask : Integers.Int) (k : Code) : Code :=
  if isRlwMask mask then .Prlwinm r1 r2 amount mask :: k
  else .Prlwinm r1 r2 amount Integers.Int.mone :: andimmBase r1 r1 mask k

/-! ## Smart constructors for 64-bit integer constants -/

/-- `Asmgen.low64_u` -/
def low64U (n : Integers.Int64) : Integers.Int64 := Integers.Int64.zero_ext 16 n
/-- `Asmgen.low64_s` -/
def low64S (n : Integers.Int64) : Integers.Int64 := Integers.Int64.sign_ext 16 n

/-- `Asmgen.loadimm64_32s` -/
def loadimm64_32s (r : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  let loU := low64U n
  let loS := low64S n
  let hiS := low64S (Integers.Int64.shr n (L 16))
  if Integers.Int64.eq n loS then .Paddi64 r .GPR0 n :: k
  else .Paddis64 r .GPR0 hiS :: .Pori64 r r loU :: k

/-- `Asmgen.loadimm64` -/
def loadimm64 (r : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  if Integers.Int64.eq n (Integers.Int64.sign_ext 32 n) then loadimm64_32s r n k
  else .Pldi r n :: k

/-- `Asmgen.loadimm64_notemp`: a variant of `loadimm64` that uses no
temporary register. -/
def loadimm64Notemp (r : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  if Integers.Int64.eq n (Integers.Int64.sign_ext 32 n) then loadimm64_32s r n k
  else
    loadimm64_32s r (Integers.Int64.shru n (L 32))
      (.Prldinm r r (I 32) (Integers.Int64.shl Integers.Int64.mone (L 32)) ::
       .Poris64 r r (low64U (Integers.Int64.shru n (L 16))) ::
       .Pori64 r r (low64U n) :: k)

/-- `Asmgen.opimm64` -/
def opimm64 (insn2 : Ireg → Ireg → Ireg → Instruction)
    (insn1 : Ireg → Ireg → Integers.Int64 → Instruction) (r1 r2 : Ireg) (n : Integers.Int64)
    (ok : Bool) (k : Code) : Code :=
  if ok then insn1 r1 r2 n :: k
  else if r2 = .GPR12 then .Pmr .GPR0 .GPR12 :: loadimm64 .GPR12 n (insn2 r1 .GPR0 .GPR12 :: k)
  else loadimm64 .GPR0 n (insn2 r1 r2 .GPR0 :: k)

/-- `Asmgen.addimm64` -/
def addimm64 (r1 r2 : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  opimm64 .Padd64 .Paddi64 r1 r2 n (Integers.Int64.eq n (low64S n)) k

/-- `Asmgen.orimm64` -/
def orimm64 (r1 r2 : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  opimm64 .Por64 .Pori64 r1 r2 n (Integers.Int64.eq n (low64U n)) k

/-- `Asmgen.xorimm64` -/
def xorimm64 (r1 r2 : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  opimm64 .Pxor64 .Pxori64 r1 r2 n (Integers.Int64.eq n (low64U n)) k

/-- `Asmgen.andimm64_base` -/
def andimm64Base (r1 r2 : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  opimm64 .Pand_64 .Pandi_64 r1 r2 n (Integers.Int64.eq n (low64U n)) k

/-- `Asmgen.andimm64` -/
def andimm64 (r1 r2 : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  if isRldlMask n || isRldrMask n then .Prldinm r1 r2 Integers.Int.zero n :: k
  else andimm64Base r1 r2 n k

/-- `Asmgen.rolm64` -/
def rolm64 (r1 r2 : Ireg) (amount : Integers.Int) (mask : Integers.Int64) (k : Code) : Code :=
  if isRldlMask mask || isRldrMask mask ||
      (let mask' := Integers.Int64.shru' mask amount
       Integers.Int64.eq mask (Integers.Int64.shl' mask' amount) && isRldlMask mask') then
    .Prldinm r1 r2 amount mask :: k
  else .Prldinm r1 r2 amount Integers.Int64.mone :: andimm64Base r1 r1 mask k

/-! ## Accessing slots in the stack frame -/

/-- `Asmgen.accessind`: for 64-bit accesses (`unaligned = false`) the
offset must be a multiple of the word size. -/
def accessind {A : Type} (instr1 : A → Constant → Ireg → Instruction)
    (instr2 : A → Ireg → Ireg → Instruction) (unaligned : Bool) (base : Ireg)
    (ofs : Integers.Ptrofs) (r : A) (k : Code) : Code :=
  let ofs := Integers.Ptrofs.to_int ofs
  if Integers.Int.eq (highS ofs) Integers.Int.zero &&
      (unaligned || Integers.Int.eq (Integers.Int.mods ofs (I 4)) Integers.Int.zero) then
    instr1 r (.Cint ofs) base :: k
  else loadimm .GPR0 ofs (instr2 r base .GPR0 :: k)

/-- `Asmgen.loadind` -/
def loadind (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg) (k : Code) :
    Res Code :=
  match ty, pregOf dst with
  | .Tint, .IR r => .OK (accessind .Plwz .Plwzx true base ofs r k)
  | .Tany32, .IR r => .OK (accessind .Plwz_a .Plwzx_a true base ofs r k)
  | .Tsingle, .FR r => .OK (accessind .Plfs .Plfsx true base ofs r k)
  | .Tlong, .IR r => .OK (accessind .Pld .Pldx false base ofs r k)
  | .Tfloat, .FR r => .OK (accessind .Plfd .Plfdx true base ofs r k)
  | .Tany64, .IR r => .OK (accessind .Pld_a .Pldx_a false base ofs r k)
  | .Tany64, .FR r => .OK (accessind .Plfd_a .Plfdx_a true base ofs r k)
  | _, _ => .Error "Asmgen.loadind"

/-- `Asmgen.storeind` -/
def storeind (src : Mreg) (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (k : Code) :
    Res Code :=
  match ty, pregOf src with
  | .Tint, .IR r => .OK (accessind .Pstw .Pstwx true base ofs r k)
  | .Tany32, .IR r => .OK (accessind .Pstw_a .Pstwx_a true base ofs r k)
  | .Tsingle, .FR r => .OK (accessind .Pstfs .Pstfsx true base ofs r k)
  | .Tlong, .IR r => .OK (accessind .Pstd .Pstdx false base ofs r k)
  | .Tfloat, .FR r => .OK (accessind .Pstfd .Pstfdx true base ofs r k)
  | .Tany64, .IR r => .OK (accessind .Pstd_a .Pstdx_a false base ofs r k)
  | .Tany64, .FR r => .OK (accessind .Pstfd_a .Pstfdx_a true base ofs r k)
  | _, _ => .Error "Asmgen.storeind"

/-! ## Conditions -/

/-- `Asmgen.floatcomp`: `fcmpu` sets the bits 0, 1, 2 of the condition
register (less, greater, equal); `<=` and `>=` are synthesized by `cror`
into bit 3. -/
def floatcomp (cmp : Comparison) (r1 r2 : Freg) (k : Code) : Code :=
  .Pfcmpu r1 r2 ::
    match cmp with
    | .Cle => .Pcror .CRbit_3 .CRbit_2 .CRbit_0 :: k
    | .Cge => .Pcror .CRbit_3 .CRbit_2 .CRbit_1 :: k
    | _ => k

/-- `Asmgen.transl_cond`: prepends to `k` the instructions that leave the
truth value of `cond` in the bit `crbit_for_cond cond` of the condition
register. -/
def translCond (cond : Condition) (args : List Mreg) (k : Code) : Res Code :=
  match cond, args with
  | .Ccomp _, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmpw r1 r2 :: k)
  | .Ccompu _, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmplw r1 r2 :: k)
  | .Ccompimm _ n, [a1] => do
    let r1 ← iregOf a1
    if Integers.Int.eq (highS n) Integers.Int.zero then pure (.Pcmpwi r1 (.Cint n) :: k)
    else pure (loadimm .GPR0 n (.Pcmpw r1 .GPR0 :: k))
  | .Ccompuimm _ n, [a1] => do
    let r1 ← iregOf a1
    if Integers.Int.eq (highU n) Integers.Int.zero then pure (.Pcmplwi r1 (.Cint n) :: k)
    else pure (loadimm .GPR0 n (.Pcmplw r1 .GPR0 :: k))
  | .Ccompf cmp, [a1, a2] | .Cnotcompf cmp, [a1, a2] => do
    let r1 ← fregOf a1; let r2 ← fregOf a2; pure (floatcomp cmp r1 r2 k)
  | .Cmaskzero n, [a1] | .Cmasknotzero n, [a1] => do
    let r1 ← iregOf a1; pure (andimmBase .GPR0 r1 n k)
  | .Ccompl _, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmpd r1 r2 :: k)
  | .Ccomplu _, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmpld r1 r2 :: k)
  | .Ccomplimm _ n, [a1] => do
    let r1 ← iregOf a1
    if Integers.Int64.eq n (low64S n) then pure (.Pcmpdi r1 n :: k)
    else pure (loadimm64Notemp .GPR0 n (.Pcmpd r1 .GPR0 :: k))
  | .Ccompluimm _ n, [a1] => do
    let r1 ← iregOf a1
    if Integers.Int64.eq n (low64U n) then pure (.Pcmpldi r1 n :: k)
    else pure (loadimm64Notemp .GPR0 n (.Pcmpld r1 .GPR0 :: k))
  | _, _ => .Error "Asmgen.transl_cond"

/-- `Asmgen.crbit_for_icmp` (`CRbit_0` = less, `CRbit_1` = greater,
`CRbit_2` = equal) -/
def crbitForIcmp : Comparison → Crbit × Bool
  | .Ceq => (.CRbit_2, true) | .Cne => (.CRbit_2, false) | .Clt => (.CRbit_0, true)
  | .Cle => (.CRbit_1, false) | .Cgt => (.CRbit_1, true) | .Cge => (.CRbit_0, false)

/-- `Asmgen.crbit_for_fcmp` -/
def crbitForFcmp : Comparison → Crbit × Bool
  | .Ceq => (.CRbit_2, true) | .Cne => (.CRbit_2, false) | .Clt => (.CRbit_0, true)
  | .Cle => (.CRbit_3, true) | .Cgt => (.CRbit_1, true) | .Cge => (.CRbit_3, true)

/-- `Asmgen.crbit_for_cond` -/
def crbitForCond : Condition → Crbit × Bool
  | .Ccomp c | .Ccompu c | .Ccompimm c _ | .Ccompuimm c _ => crbitForIcmp c
  | .Ccompl c | .Ccomplu c | .Ccomplimm c _ | .Ccompluimm c _ => crbitForIcmp c
  | .Ccompf c => crbitForFcmp c
  | .Cnotcompf c => let p := crbitForFcmp c; (p.1, !p.2)
  | .Cmaskzero _ => (.CRbit_2, true)
  | .Cmasknotzero _ => (.CRbit_2, false)

/-- `Asmgen.condition_class`: comparisons of a register with `0`. -/
inductive CondClass where
  | eq0 (r : Mreg)
  | ne0 (r : Mreg)
  | ge0 (r : Mreg)
  | lt0 (r : Mreg)
  | default

/-- `Asmgen.classify_condition` -/
def classifyCondition (c : Condition) (args : List Mreg) : CondClass :=
  match c, args with
  | .Ccompimm .Ceq n, [r] => if n = Integers.Int.zero then .eq0 r else .default
  | .Ccompimm .Cne n, [r] => if n = Integers.Int.zero then .ne0 r else .default
  | .Ccompimm .Cge n, [r] => if n = Integers.Int.zero then .ge0 r else .default
  | .Ccompimm .Clt n, [r] => if n = Integers.Int.zero then .lt0 r else .default
  | _, _ => .default

/-- `Asmgen.transl_cond_op`: sets `r` to `0` or `1` according to the truth
value of the condition. -/
def translCondOp (cond : Condition) (args : List Mreg) (r : Mreg) (k : Code) : Res Code := do
  let r' ← iregOf r
  match classifyCondition cond args with
  | .eq0 a => do
    let a' ← iregOf a
    pure (.Psubfic .GPR0 a' (.Cint Integers.Int.zero) :: .Padde r' .GPR0 a' :: k)
  | .ne0 a => do
    let a' ← iregOf a
    pure (.Paddic .GPR0 a' (.Cint Integers.Int.mone) :: .Psubfe r' .GPR0 a' :: k)
  | .ge0 a => do
    let a' ← iregOf a
    pure (.Prlwinm r' a' Integers.Int.one Integers.Int.one ::
          .Pxori r' r' (.Cint Integers.Int.one) :: k)
  | .lt0 a => do
    let a' ← iregOf a
    pure (.Prlwinm r' a' Integers.Int.one Integers.Int.one :: k)
  | .default =>
    let p := crbitForCond cond
    translCond cond args
      (.Pmfcrbit r' p.1 :: if p.2 then k else .Pxori r' r' (.Cint Integers.Int.one) :: k)

/-- `Asmgen.transl_select_op` -/
def translSelectOp (cond : Condition) (args : List Mreg) (r1 r2 rd : Ireg) (k : Code) :
    Res Code :=
  if r1 = r2 then .OK (.Pmr rd r1 :: k)
  else
    let p := crbitForCond cond
    let r1' := if p.2 then r1 else r2
    let r2' := if p.2 then r2 else r1
    translCond cond args (.Pisel rd r1' r2' p.1 :: k)

/-- `Asmgen.transl_fselect_op` -/
def translFselectOp (cond : Condition) (args : List Mreg) (r1 r2 rd : Freg) (k : Code) :
    Res Code :=
  if r1 = r2 then .OK (.Pfmr rd r1 :: k)
  else
    let p := crbitForCond cond
    let r1' := if p.2 then r1 else r2
    let r2' := if p.2 then r2 else r1
    translCond cond args (.Pfsel_gen rd r1' r2' p.1 :: k)

/-! ## Arithmetic operations -/

/-- A binary integer operation `r <- mk r1 r2` (helper of `transl_op`). -/
def binInt (mk : Ireg → Ireg → Ireg → Instruction) (res a1 a2 : Mreg) (k : Code) : Res Code := do
  let r1 ← iregOf a1; let r2 ← iregOf a2; let r ← iregOf res
  pure (mk r r1 r2 :: k)

/-- A unary integer operation, as a code transformer (helper of `transl_op`). -/
def unInt (mk : Ireg → Ireg → Code → Code) (res a1 : Mreg) (k : Code) : Res Code := do
  let r1 ← iregOf a1; let r ← iregOf res
  pure (mk r r1 k)

/-- A unary float operation (helper of `transl_op`). -/
def unFloat (mk : Freg → Freg → Instruction) (res a1 : Mreg) (k : Code) : Res Code := do
  let r1 ← fregOf a1; let r ← fregOf res
  pure (mk r r1 :: k)

/-- A binary float operation (helper of `transl_op`). -/
def binFloat (mk : Freg → Freg → Freg → Instruction) (res a1 a2 : Mreg) (k : Code) :
    Res Code := do
  let r1 ← fregOf a1; let r2 ← fregOf a2; let r ← fregOf res
  pure (mk r r1 r2 :: k)

/-- `Asmgen.transl_op`: the instructions computing `res <- op(args)`,
prepended to `k`. -/
def translOp (lp : LinkerParams) (op : Operation) (args : List Mreg) (res : Mreg) (k : Code) :
    Res Code :=
  match op, args with
  | .Omove, [a1] =>
    match pregOf res, pregOf a1 with
    | .IR r, .IR a => .OK (.Pmr r a :: k)
    | .FR r, .FR a => .OK (.Pfmr r a :: k)
    | _, _ => .Error "Asmgen.Omove"
  | .Ointconst n, [] => do let r ← iregOf res; pure (loadimm r n k)
  | .Ofloatconst f, [] => do let r ← fregOf res; pure (.Plfi r f :: k)
  | .Osingleconst f, [] => do let r ← fregOf res; pure (.Plfis r f :: k)
  | .Oaddrsymbol s ofs, [] => do
    let r ← iregOf res
    pure (if lp.symbol_is_small_data s ofs then .Paddi r .GPR0 (.Csymbol_sda s ofs) :: k
          else if lp.symbol_is_rel_data s ofs then
            .Paddis r .GPR0 (.Csymbol_rel_high s ofs) :: .Paddi r r (.Csymbol_rel_low s ofs) :: k
          else .Paddis r .GPR0 (.Csymbol_high s ofs) :: .Paddi r r (.Csymbol_low s ofs) :: k)
  | .Oaddrstack n, [] => do
    let r ← iregOf res; pure (addimm r .GPR1 (Integers.Ptrofs.to_int n) k)
  | .Ocast8signed, [a1] => unInt (fun r r1 k => .Pextsb r r1 :: k) res a1 k
  | .Ocast16signed, [a1] => unInt (fun r r1 k => .Pextsh r r1 :: k) res a1 k
  | .Oadd, [a1, a2] => binInt .Padd res a1 a2 k
  | .Oaddimm n, [a1] => unInt (fun r r1 => addimm r r1 n) res a1 k
  | .Oaddsymbol s ofs, [a1] => do
    let r1 ← iregOf a1; let r ← iregOf res
    pure (if lp.symbol_is_small_data s ofs then
            .Paddi .GPR0 .GPR0 (.Csymbol_sda s ofs) :: .Padd r r1 .GPR0 :: k
          else if lp.symbol_is_rel_data s ofs then
            .Pmr .GPR0 r1 :: .Paddis r .GPR0 (.Csymbol_rel_high s ofs) ::
              .Paddi r r (.Csymbol_rel_low s ofs) :: .Padd r r .GPR0 :: k
          else .Paddis r r1 (.Csymbol_high s ofs) :: .Paddi r r (.Csymbol_low s ofs) :: k)
  | .Osub, [a1, a2] => binInt (fun r r1 r2 => .Psubfc r r2 r1) res a1 a2 k
  | .Osubimm n, [a1] =>
    unInt (fun r r1 k =>
      if Integers.Int.eq (highS n) Integers.Int.zero then .Psubfic r r1 (.Cint n) :: k
      else loadimm .GPR0 n (.Psubfc r r1 .GPR0 :: k)) res a1 k
  | .Omul, [a1, a2] => binInt .Pmullw res a1 a2 k
  | .Omulimm n, [a1] =>
    unInt (fun r r1 k =>
      if Integers.Int.eq (highS n) Integers.Int.zero then .Pmulli r r1 (.Cint n) :: k
      else loadimm .GPR0 n (.Pmullw r r1 .GPR0 :: k)) res a1 k
  | .Omulhs, [a1, a2] => binInt .Pmulhw res a1 a2 k
  | .Omulhu, [a1, a2] => binInt .Pmulhwu res a1 a2 k
  | .Odiv, [a1, a2] => binInt .Pdivw res a1 a2 k
  | .Odivu, [a1, a2] => binInt .Pdivwu res a1 a2 k
  | .Oand, [a1, a2] => binInt .Pand_ res a1 a2 k
  | .Oandimm n, [a1] => unInt (fun r r1 => andimm r r1 n) res a1 k
  | .Oor, [a1, a2] => binInt .Por res a1 a2 k
  | .Oorimm n, [a1] => unInt (fun r r1 => orimm r r1 n) res a1 k
  | .Oxor, [a1, a2] => binInt .Pxor res a1 a2 k
  | .Oxorimm n, [a1] => unInt (fun r r1 => xorimm r r1 n) res a1 k
  | .Onot, [a1] => unInt (fun r r1 k => .Pnor r r1 r1 :: k) res a1 k
  | .Onand, [a1, a2] => binInt .Pnand res a1 a2 k
  | .Onor, [a1, a2] => binInt .Pnor res a1 a2 k
  | .Onxor, [a1, a2] => binInt .Peqv res a1 a2 k
  | .Oandc, [a1, a2] => binInt .Pandc res a1 a2 k
  | .Oorc, [a1, a2] => binInt .Porc res a1 a2 k
  | .Oshl, [a1, a2] => binInt .Pslw res a1 a2 k
  | .Oshr, [a1, a2] => binInt .Psraw res a1 a2 k
  | .Oshrimm n, [a1] => unInt (fun r r1 k => .Psrawi r r1 n :: k) res a1 k
  | .Oshrximm n, [a1] => unInt (fun r r1 k => .Psrawi r r1 n :: .Paddze r r :: k) res a1 k
  | .Oshru, [a1, a2] => binInt .Psrw res a1 a2 k
  | .Orolm amount mask, [a1] => unInt (fun r r1 => rolm r r1 amount mask) res a1 k
  | .Oroli amount mask, [a1, a2] =>
    assert (decide (a1 = res)) do
      let r2 ← iregOf a2; let r ← iregOf res
      pure (.Prlwimi r r2 amount mask :: k)
  | .Onegf, [a1] => unFloat .Pfneg res a1 k
  | .Oabsf, [a1] => unFloat .Pfabs res a1 k
  | .Oaddf, [a1, a2] => binFloat .Pfadd res a1 a2 k
  | .Osubf, [a1, a2] => binFloat .Pfsub res a1 a2 k
  | .Omulf, [a1, a2] => binFloat .Pfmul res a1 a2 k
  | .Odivf, [a1, a2] => binFloat .Pfdiv res a1 a2 k
  | .Onegfs, [a1] => unFloat .Pfnegs res a1 k
  | .Oabsfs, [a1] => unFloat .Pfabss res a1 k
  | .Oaddfs, [a1, a2] => binFloat .Pfadds res a1 a2 k
  | .Osubfs, [a1, a2] => binFloat .Pfsubs res a1 a2 k
  | .Omulfs, [a1, a2] => binFloat .Pfmuls res a1 a2 k
  | .Odivfs, [a1, a2] => binFloat .Pfdivs res a1 a2 k
  | .Osingleoffloat, [a1] => unFloat .Pfrsp res a1 k
  | .Ofloatofsingle, [a1] => unFloat .Pfxdp res a1 k
  | .Ointoffloat, [a1] => do
    let r1 ← fregOf a1; let r ← iregOf res; pure (.Pfcti r r1 :: k)
  | .Ofloatofwords, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2; let r ← fregOf res; pure (.Pfmake r r1 r2 :: k)
  | .Omakelong, [a1, a2] => binInt .Plmake res a1 a2 k
  | .Olowlong, [a1] =>
    assert (decide (a1 = res)) do let r ← iregOf res; pure (.Pllo r :: k)
  | .Ohighlong, [a1] => unInt (fun r r1 k => .Plhi r r1 :: k) res a1 k
  | .Ocmp cmp, _ => translCondOp cmp args res k
  | .Osel cmp _, a1 :: a2 :: args =>
    match pregOf res with
    | .IR _ => do
      let r1 ← iregOf a1; let r2 ← iregOf a2; let r ← iregOf res
      translSelectOp cmp args r1 r2 r k
    | .FR _ => do
      let r1 ← fregOf a1; let r2 ← fregOf a2; let r ← fregOf res
      translFselectOp cmp args r1 r2 r k
    | _ => .Error "Asmgen.Osel"
  -- PPC64 operations
  | .Olongconst n, [] => do let r ← iregOf res; pure (loadimm64 r n k)
  | .Ocast32signed, [a1] => unInt (fun r r1 k => .Pextsw r r1 :: k) res a1 k
  | .Ocast32unsigned, [a1] => unInt (fun r r1 k => .Pextzw r r1 :: k) res a1 k
  | .Oaddl, [a1, a2] => binInt .Padd64 res a1 a2 k
  | .Oaddlimm n, [a1] => unInt (fun r r1 => addimm64 r r1 n) res a1 k
  | .Osubl, [a1, a2] => binInt (fun r r1 r2 => .Psubfc64 r r2 r1) res a1 a2 k
  | .Onegl, [a1] => unInt (fun r r1 k => .Psubfic64 r r1 Integers.Int64.zero :: k) res a1 k
  | .Omull, [a1, a2] => binInt .Pmulld res a1 a2 k
  | .Omullhs, [a1, a2] => binInt .Pmulhd res a1 a2 k
  | .Omullhu, [a1, a2] => binInt .Pmulhdu res a1 a2 k
  | .Odivl, [a1, a2] => binInt .Pdivd res a1 a2 k
  | .Odivlu, [a1, a2] => binInt .Pdivdu res a1 a2 k
  | .Oandl, [a1, a2] => binInt .Pand_64 res a1 a2 k
  | .Oandlimm n, [a1] => unInt (fun r r1 => andimm64 r r1 n) res a1 k
  | .Oorl, [a1, a2] => binInt .Por64 res a1 a2 k
  | .Oorlimm n, [a1] => unInt (fun r r1 => orimm64 r r1 n) res a1 k
  | .Oxorl, [a1, a2] => binInt .Pxor64 res a1 a2 k
  | .Oxorlimm n, [a1] => unInt (fun r r1 => xorimm64 r r1 n) res a1 k
  | .Onotl, [a1] => unInt (fun r r1 k => .Pnor64 r r1 r1 :: k) res a1 k
  | .Oshll, [a1, a2] => binInt .Psld res a1 a2 k
  | .Oshrl, [a1, a2] => binInt .Psrad res a1 a2 k
  | .Oshrlimm n, [a1] => unInt (fun r r1 k => .Psradi r r1 n :: k) res a1 k
  | .Oshrlu, [a1, a2] => binInt .Psrd res a1 a2 k
  | .Orolml amount mask, [a1] => unInt (fun r r1 => rolm64 r r1 amount mask) res a1 k
  | .Oshrxlimm n, [a1] => unInt (fun r r1 k => .Psradi r r1 n :: .Paddze64 r r :: k) res a1 k
  | .Olongoffloat, [a1] => do
    let r1 ← fregOf a1; let r ← iregOf res; pure (.Pfctid r r1 :: k)
  | .Ofloatoflong, [a1] => do
    let r1 ← iregOf a1; let r ← fregOf res; pure (.Pfcfl r r1 :: k)
  | _, _ => .Error "Asmgen.transl_op"

/-! ## Memory accesses -/

/-- `Asmgen.int_temp_for` -/
def intTempFor (r : Mreg) : Ireg := if r = .R12 then .GPR11 else .GPR12

/-- `Asmgen.symbol_ofs_word_aligned` -/
def symbolOfsWordAligned (lp : LinkerParams) (symb : Ident) (ofs : Integers.Ptrofs) : Bool :=
  let ofs := Integers.Ptrofs.to_int ofs
  lp.symbol_is_aligned symb 4 && Integers.Int.eq (Integers.Int.mods ofs (I 4)) Integers.Int.zero

/-- `Asmgen.aindexed` -/
def aindexed (mk1 : Constant → Ireg → Code → Code) (mk2 : Ireg → Ireg → Code → Code)
    (unaligned : Bool) (r1 temp : Ireg) (ofs : Integers.Int) (k : Code) : Code :=
  if unaligned || Integers.Int.eq (Integers.Int.mods ofs (I 4)) Integers.Int.zero then
    if Integers.Int.eq (highS ofs) Integers.Int.zero then mk1 (.Cint ofs) r1 k
    else .Paddis temp r1 (.Cint (highS ofs)) :: mk1 (.Cint (lowS ofs)) temp k
  else loadimm .GPR0 ofs (mk2 r1 .GPR0 k)

/-- `Asmgen.aindexed2` -/
def aindexed2 (mk : Ireg → Ireg → Code → Code) (r1 r2 : Ireg) (k : Code) : Code := mk r1 r2 k

/-- `Asmgen.aglobal` -/
def aglobal (lp : LinkerParams) (mk1 : Constant → Ireg → Code → Code)
    (_mk2 : Ireg → Ireg → Code → Code) (unaligned : Bool) (temp : Ireg) (symb : Ident)
    (ofs : Integers.Ptrofs) (k : Code) : Code :=
  if lp.symbol_is_small_data symb ofs then
    if unaligned || symbolOfsWordAligned lp symb ofs then mk1 (.Csymbol_sda symb ofs) .GPR0 k
    else .Paddi temp .GPR0 (.Csymbol_sda symb ofs) :: mk1 (.Cint Integers.Int.zero) temp k
  else if lp.symbol_is_rel_data symb ofs then
    .Paddis temp .GPR0 (.Csymbol_rel_high symb ofs) ::
      .Paddi temp temp (.Csymbol_rel_low symb ofs) :: mk1 (.Cint Integers.Int.zero) temp k
  else if unaligned || symbolOfsWordAligned lp symb ofs then
    .Paddis temp .GPR0 (.Csymbol_high symb ofs) :: mk1 (.Csymbol_low symb ofs) temp k
  else
    .Paddis temp .GPR0 (.Csymbol_high symb ofs) ::
      .Paddi temp temp (.Csymbol_low symb ofs) :: mk1 (.Cint Integers.Int.zero) temp k

/-- `Asmgen.abased` -/
def abased (lp : LinkerParams) (mk1 : Constant → Ireg → Code → Code)
    (mk2 : Ireg → Ireg → Code → Code) (unaligned : Bool) (r1 temp : Ireg) (symb : Ident)
    (ofs : Integers.Ptrofs) (k : Code) : Code :=
  if lp.symbol_is_small_data symb ofs then
    .Paddi .GPR0 .GPR0 (.Csymbol_sda symb ofs) :: mk2 r1 .GPR0 k
  else if lp.symbol_is_rel_data symb ofs then
    .Pmr .GPR0 r1 :: .Paddis temp .GPR0 (.Csymbol_rel_high symb ofs) ::
      .Paddi temp temp (.Csymbol_rel_low symb ofs) :: mk2 temp .GPR0 k
  else if unaligned || symbolOfsWordAligned lp symb ofs then
    .Paddis temp r1 (.Csymbol_high symb ofs) :: mk1 (.Csymbol_low symb ofs) temp k
  else
    .Pmr .GPR0 r1 :: .Paddis temp .GPR0 (.Csymbol_high symb ofs) ::
      .Paddi temp temp (.Csymbol_low symb ofs) :: mk2 temp .GPR0 k

/-- `Asmgen.ainstack` -/
def ainstack (mk1 : Constant → Ireg → Code → Code) (_mk2 : Ireg → Ireg → Code → Code)
    (unaligned : Bool) (temp : Ireg) (ofs : Integers.Int) (k : Code) : Code :=
  if unaligned || Integers.Int.eq (Integers.Int.mods ofs (I 4)) Integers.Int.zero then
    if Integers.Int.eq (highS ofs) Integers.Int.zero then mk1 (.Cint ofs) .GPR1 k
    else .Paddis temp .GPR1 (.Cint (highS ofs)) :: mk1 (.Cint (lowS ofs)) temp k
  else addimm temp .GPR1 ofs (mk1 (.Cint Integers.Int.zero) temp k)

/-- `Asmgen.transl_memory_access` -/
def translMemoryAccess (lp : LinkerParams) (mk1 : Constant → Ireg → Instruction)
    (mk2 : Ireg → Ireg → Instruction) (unaligned : Bool) (addr : Addressing) (args : List Mreg)
    (temp : Ireg) (k : Code) : Res Code :=
  let m1 := fun c r k => mk1 c r :: k
  let m2 := fun r1 r2 k => mk2 r1 r2 :: k
  match addr, args with
  | .Aindexed ofs, [a1] => do
    let r1 ← iregOf a1; pure (aindexed m1 m2 unaligned r1 temp ofs k)
  | .Aindexed2, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2; pure (aindexed2 m2 r1 r2 k)
  | .Aglobal symb ofs, [] => .OK (aglobal lp m1 m2 unaligned temp symb ofs k)
  | .Abased symb ofs, [a1] => do
    let r1 ← iregOf a1; pure (abased lp m1 m2 unaligned r1 temp symb ofs k)
  | .Ainstack ofs, [] => .OK (ainstack m1 m2 unaligned temp (Integers.Ptrofs.to_int ofs) k)
  | _, _ => .Error "Asmgen.transl_memory_access"

/-- `Asmgen.transl_load` -/
def translLoad (lp : LinkerParams) (chunk : Chunk) (addr : Addressing) (args : List Mreg)
    (dst : Mreg) (k : Code) : Res Code :=
  let tma := translMemoryAccess lp
  match chunk with
  | .Mint8signed => do
    let r ← iregOf dst; tma (.Plbz r) (.Plbzx r) true addr args .GPR12 (.Pextsb r r :: k)
  | .Mint8unsigned => do let r ← iregOf dst; tma (.Plbz r) (.Plbzx r) true addr args .GPR12 k
  | .Mint16signed => do let r ← iregOf dst; tma (.Plha r) (.Plhax r) true addr args .GPR12 k
  | .Mint16unsigned => do let r ← iregOf dst; tma (.Plhz r) (.Plhzx r) true addr args .GPR12 k
  | .Mint32 => do let r ← iregOf dst; tma (.Plwz r) (.Plwzx r) true addr args .GPR12 k
  | .Mint64 => do let r ← iregOf dst; tma (.Pld r) (.Pldx r) false addr args .GPR12 k
  | .Mfloat32 => do let r ← fregOf dst; tma (.Plfs r) (.Plfsx r) true addr args .GPR12 k
  | .Mfloat64 => do let r ← fregOf dst; tma (.Plfd r) (.Plfdx r) true addr args .GPR12 k
  | _ => .Error "Asmgen.transl_load"

/-- `Asmgen.transl_store` -/
def translStore (lp : LinkerParams) (chunk : Chunk) (addr : Addressing) (args : List Mreg)
    (src : Mreg) (k : Code) : Res Code :=
  let temp := intTempFor src
  let tma := translMemoryAccess lp
  match chunk with
  | .Mint8unsigned => do let r ← iregOf src; tma (.Pstb r) (.Pstbx r) true addr args temp k
  | .Mint16unsigned => do let r ← iregOf src; tma (.Psth r) (.Psthx r) true addr args temp k
  | .Mint32 => do let r ← iregOf src; tma (.Pstw r) (.Pstwx r) true addr args temp k
  | .Mint64 => do let r ← iregOf src; tma (.Pstd r) (.Pstdx r) false addr args temp k
  | .Mfloat32 => do let r ← fregOf src; tma (.Pstfs r) (.Pstfsx r) true addr args temp k
  | .Mfloat64 => do let r ← fregOf src; tma (.Pstfd r) (.Pstfdx r) true addr args temp k
  | _ => .Error "Asmgen.transl_store"

/-! ## Instructions, code and functions -/

/-- `Asmgen.transl_epilogue`: reloads the return address into `LR` (unless
the function is a leaf) and frees the stack frame. -/
def translEpilogue (f : Mach.Function) (k : Code) : Code :=
  if MachSyntax.isLeafFunction f then .Pfreeframe f.fn_stacksize f.fn_link_ofs :: k
  else
    .Plwz .GPR0 (.Cint (Integers.Ptrofs.to_int f.fn_retaddr_ofs)) .GPR1 :: .Pmtlr .GPR0 ::
      .Pfreeframe f.fn_stacksize f.fn_link_ofs :: k

/-- `Asmgen.transl_instr`; `r11IsParent` tells whether `R11` holds the
parent frame (the back link) on entry. -/
def translInstr (lp : LinkerParams) (f : Mach.Function) (i : Mach.Instruction)
    (r11IsParent : Bool) (k : Code) : Res Code :=
  match i with
  | .Mgetstack ofs ty dst => loadind .GPR1 ofs ty dst k
  | .Msetstack src ofs ty => storeind src .GPR1 ofs ty k
  | .Mgetparam ofs ty dst =>
    if r11IsParent then loadind .GPR11 ofs ty dst k
    else do
      let k1 ← loadind .GPR11 ofs ty dst k
      loadind .GPR1 f.fn_link_ofs .Tint .R11 k1
  | .Mop op args res => translOp lp op args res k
  | .Mload chunk addr args dst => translLoad lp chunk addr args dst k
  | .Mstore chunk addr args src => translStore lp chunk addr args src k
  | .Mcall sig (.inl r) => do let r1 ← iregOf r; pure (.Pmtctr r1 :: .Pbctrl sig :: k)
  | .Mcall sig (.inr symb) => .OK (.Pbl symb sig :: k)
  | .Mtailcall sig (.inl r) => do
    let r1 ← iregOf r
    pure (.Pmtctr r1 :: translEpilogue f (.Pbctr sig :: k))
  | .Mtailcall sig (.inr symb) => .OK (translEpilogue f (.Pbs symb sig :: k))
  | .Mbuiltin ef args res =>
    .OK (.Pbuiltin ef (args.map (BuiltinArg.map pregOf)) (BuiltinRes.map pregOf res) :: k)
  | .Mlabel lbl => .OK (.Plabel lbl :: k)
  | .Mgoto lbl => .OK (.Pb lbl :: k)
  | .Mcond cond args lbl =>
    let p := crbitForCond cond
    translCond cond args (if p.2 then .Pbt p.1 lbl :: k else .Pbf p.1 lbl :: k)
  | .Mjumptable arg tbl => do let r ← iregOf arg; pure (.Pbtbl r tbl :: k)
  | .Mreturn => .OK (translEpilogue f (.Pblr :: k))

/-- `Asmgen.it1_is_parent` -/
def it1IsParent (before : Bool) (i : Mach.Instruction) : Bool :=
  match i with
  | .Msetstack .. => before
  | .Mgetparam _ _ dst => !(decide (dst = .R11))
  | .Mop .Omove _ res => before && !(decide (res = .R11))
  | _ => false

/-- `Asmgen.transl_code` (the specification; not tail-recursive) -/
def translCode (lp : LinkerParams) (f : Mach.Function) :
    List Mach.Instruction → Bool → Res Code
  | [], _ => .OK []
  | i1 :: il', it1p => do
    let k ← translCode lp f il' (it1IsParent it1p i1)
    translInstr lp f i1 it1p k

/-- `Asmgen.transl_code_rec`: the same in continuation-passing style. -/
def translCodeRec (lp : LinkerParams) (f : Mach.Function) :
    List Mach.Instruction → Bool → (Code → Res Code) → Res Code
  | [], _, k => k []
  | i1 :: il', it1p, k =>
    translCodeRec lp f il' (it1IsParent it1p i1)
      (fun c1 => do let c2 ← translInstr lp f i1 it1p c1; k c2)

/-- `Asmgen.transl_code'` -/
def translCode' (lp : LinkerParams) (f : Mach.Function) (il : List Mach.Instruction)
    (it1p : Bool) : Res Code :=
  translCodeRec lp f il it1p (fun c => .OK c)

/-- `Asmgen.transl_function` -/
def translFunction (lp : LinkerParams) (f : Mach.Function) : Res Asm.Function := do
  let c ← translCode' lp f f.fn_code false
  pure { fn_sig := f.fn_sig,
         fn_code := .Pallocframe f.fn_stacksize f.fn_link_ofs f.fn_retaddr_ofs ::
           .Pmflr .GPR0 ::
           .Pstw .GPR0 (.Cint (Integers.Ptrofs.to_int f.fn_retaddr_ofs)) .GPR1 ::
           .Pcfi_rel_offset (Integers.Ptrofs.to_int f.fn_retaddr_ofs) :: c }

/-- `Asmgen.transf_function`: the code must have fewer than `2^32`
instructions. -/
def transfFunction (lp : LinkerParams) (f : Mach.Function) : Res Asm.Function := do
  let tf ← translFunction lp f
  if Integers.Ptrofs.max_unsigned < (tf.fn_code.length : Z) then .Error "code size exceeded"
  else pure tf

/-- `Asmgen.transf_fundef` -/
def transfFundef (lp : LinkerParams) (f : Mach.Fundef) : Res Asm.Fundef :=
  ASTFundef.transfPartial (transfFunction lp) f

/-- `Asmgen.transf_program` -/
def transfProgram (lp : LinkerParams) (p : Mach.Program) : Res Asm.Program :=
  transformPartialProgram (transfFundef lp) p

/-! ## Equivalence of the two code translations (`Asmgenproof.v`) -/

private theorem translCodeRec_spec (lp : LinkerParams) (f : Mach.Function) :
    ∀ (il : List Mach.Instruction) (it1p : Bool) (k : Code → Res Code),
      translCodeRec lp f il it1p k = Res.bind (translCode lp f il it1p) k
  | [], _, _ => rfl
  | i1 :: il', it1p, k => by
    rw [translCodeRec, translCodeRec_spec lp f il']
    simp only [translCode]
    show _ = Res.bind (Res.bind _ _) _
    cases translCode lp f il' (it1IsParent it1p i1) with
    | OK a => rfl
    | Error m => rfl

/-- `Asmgenproof.transl_code'_transl_code` -/
theorem translCode'_translCode (lp : LinkerParams) (f : Mach.Function)
    (il : List Mach.Instruction) (it1p : Bool) :
    translCode' lp f il it1p = translCode lp f il it1p := by
  rw [translCode', translCodeRec_spec]
  cases translCode lp f il it1p <;> rfl

end Asmgen
end PowerPC
end CC
