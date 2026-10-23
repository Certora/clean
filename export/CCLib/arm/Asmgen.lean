/-
  Translation from Mach to ARM assembly — port of `arm/Asmgen.v` (whole
  file).

  Ported: `ireg_of`, `freg_of`, `is_immed_arith_arm`,
  `is_immed_arith_thumb`, `is_immed_arith_thumb_special`, `is_immed_arith`,
  `mk_immed_mem_word`, `mk_immed_mem_small`, `mk_immed_mem_float`,
  `decompose_int_arm`, `decompose_int_thumb`, `decompose_int_base`,
  `decompose_int`, `iterate_op`, `loadimm_word`, `loadimm`, `addimm`,
  `rsubimm`, `andimm`, `orimm`, `xorimm`, `transl_shift`, `transl_cond`,
  `cond_for_signed_cmp`, `cond_for_unsigned_cmp`, `cond_for_float_cmp`,
  `cond_for_float_not_cmp`, `cond_for_cond`, `transl_op`,
  `indexed_memory_access`, `loadind_int`, `loadind`, `storeind`, `save_lr`,
  `save_lr_preserves_R12`, `transl_memory_access`,
  `transl_memory_access_int`, `transl_memory_access_float`, `transl_load`,
  `transl_store`, `transl_instr`, `it1_is_parent`, `transl_code`,
  `transl_code_rec`, `transl_code'`, `transl_function`, `transf_function`,
  `transf_fundef`, `transf_program`.
  Also proved: `transl_code'_transl_code` (from `arm/Asmgenproof.v`).

  Differences from Rocq:
  * The `Parameter`s of `arm/Archi.v` (`abi`, `thumb2_support`,
    `hardware_idiv`) and of `driver/Compopts.v` (`thumb`) are the fields of
    an explicit argument `Options` (`Options.params` for the `Archi` ones).
  * `assertion b; k` is `assert b k`; error messages are plain strings.
  * The source language is `CC.Arm.Mach`: the target-generic Mach syntax
    `CCLib.backend.MachSyntax` instantiated with the ARM operators
    (`CC.Arm.Op`) and machine registers (`CC.Arm.Mreg`).  The `backend/`
    modules of the port, with the Mach semantics, are instantiated for
    AArch64 (see `MODULE_AUDIT.md` §4); the translation needs the syntax only.
-/
import CCLib.arm.Asm
import CCLib.backend.MachSyntax

namespace CC
namespace Arm

/-! ## Mach syntax over the ARM operators -/

namespace Mach

/-- `Mach.instruction` (instantiated for ARM) -/
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

/-- `Archi.abi_kind` (`arm/Archi.v`) -/
inductive AbiKind where
  | Softfloat
  | Hardfloat
  deriving DecidableEq, Repr

/-- The `Parameter`s of `arm/Archi.v` used by the ARM back end. -/
structure Params where
  /-- `Archi.abi` -/
  abi : AbiKind := .Hardfloat
  /-- `Archi.thumb2_support` -/
  thumb2Support : Bool := true
  /-- `Archi.hardware_idiv ()` -/
  hardwareIdiv : Bool := true

/-- The OCaml parameters used by Asmgen. -/
structure Options where
  /-- the `Parameter`s of `arm/Archi.v` -/
  params : Params := {}
  /-- `Compopts.thumb` (flag `-mthumb`) -/
  thumb : Unit → Bool := fun _ => false

/-- `assertion b; k` of Rocq's error monad. -/
def assert {A : Type} (b : Bool) (k : Res A) : Res A :=
  if b then k else .Error "Assertion failed"

local notation "I" => Integers.Int.repr

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

/-! ## Immediate arguments -/

/-- `Asmgen.is_immed_arith_arm`: `x` is an 8-bit constant rotated right by an
even amount. -/
def isImmedArithArm : Nat → Integers.Int → Bool
  | 0, _ => false
  | n + 1, x =>
    Integers.Int.eq x (Integers.Int.and x (I 255)) ||
    isImmedArithArm n (Integers.Int.rol x (I 2))

/-- `Asmgen.is_immed_arith_thumb`: `x` is an 8-bit constant shifted left. -/
def isImmedArithThumb : Nat → Integers.Int → Bool
  | 0, _ => true
  | n + 1, x =>
    Integers.Int.eq x (Integers.Int.and x (I 255)) ||
    (Integers.Int.eq (Integers.Int.and x Integers.Int.one) Integers.Int.zero &&
     isImmedArithThumb n (Integers.Int.shru x Integers.Int.one))

/-- `Asmgen.is_immed_arith_thumb_special`: `00XY00XY`, `XY00XY00` or
`XYXYXYXY`. -/
def isImmedArithThumbSpecial (x : Integers.Int) : Bool :=
  let l1 := Integers.Int.and x (I 255)
  let l2 := Integers.Int.shl l1 (I 8)
  let l3 := Integers.Int.shl l2 (I 8)
  let l4 := Integers.Int.shl l3 (I 8)
  let l13 := Integers.Int.or l1 l3
  let l24 := Integers.Int.or l2 l4
  Integers.Int.eq x l13 || Integers.Int.eq x l24 || Integers.Int.eq x (Integers.Int.or l13 l24)

/-- `Asmgen.is_immed_arith` -/
def isImmedArith (o : Options) (x : Integers.Int) : Bool :=
  if o.thumb () then isImmedArithThumb 24 x || isImmedArithThumbSpecial x
  else isImmedArithArm 16 x

/-- `Asmgen.mk_immed_mem_word` -/
def mkImmedMemWord (o : Options) (x : Integers.Int) : Integers.Int :=
  if Integers.Int.lt x Integers.Int.zero then
    Integers.Int.neg (Integers.Int.zero_ext (if o.thumb () then 8 else 12) (Integers.Int.neg x))
  else Integers.Int.zero_ext 12 x

/-- `Asmgen.mk_immed_mem_small` -/
def mkImmedMemSmall (x : Integers.Int) : Integers.Int :=
  if Integers.Int.lt x Integers.Int.zero then
    Integers.Int.neg (Integers.Int.zero_ext 8 (Integers.Int.neg x))
  else Integers.Int.zero_ext 8 x

/-- `Asmgen.mk_immed_mem_float` (the low two bits are masked off) -/
def mkImmedMemFloat (x : Integers.Int) : Integers.Int :=
  let x := Integers.Int.and x (I (-4))
  if Integers.Int.lt x Integers.Int.zero then
    Integers.Int.neg (Integers.Int.zero_ext 10 (Integers.Int.neg x))
  else Integers.Int.zero_ext 10 x

/-! ## Decomposition of a 32-bit integer into immediates -/

/-- `Asmgen.decompose_int_arm` -/
def decomposeIntArm : Nat → Integers.Int → Integers.Int → List Integers.Int
  | 0, n, _ => if Integers.Int.eq n Integers.Int.zero then [] else [n]
  | m + 1, n, p =>
    if Integers.Int.eq (Integers.Int.and n (Integers.Int.shl (I 3) p)) Integers.Int.zero then
      decomposeIntArm m n (Integers.Int.add p (I 2))
    else
      let msk := Integers.Int.shl (I 255) p
      Integers.Int.and n msk ::
        decomposeIntArm m (Integers.Int.and n (Integers.Int.not msk)) (Integers.Int.add p (I 2))

/-- `Asmgen.decompose_int_thumb` -/
def decomposeIntThumb : Nat → Integers.Int → Integers.Int → List Integers.Int
  | 0, n, _ => if Integers.Int.eq n Integers.Int.zero then [] else [n]
  | m + 1, n, p =>
    if Integers.Int.eq (Integers.Int.and n (Integers.Int.shl Integers.Int.one p))
        Integers.Int.zero then
      decomposeIntThumb m n (Integers.Int.add p Integers.Int.one)
    else
      let msk := Integers.Int.shl (I 255) p
      Integers.Int.and n msk ::
        decomposeIntThumb m (Integers.Int.and n (Integers.Int.not msk))
          (Integers.Int.add p Integers.Int.one)

/-- `Asmgen.decompose_int_base` -/
def decomposeIntBase (o : Options) (n : Integers.Int) : List Integers.Int :=
  if o.thumb () then
    if isImmedArithThumbSpecial n then [n] else decomposeIntThumb 24 n Integers.Int.zero
  else decomposeIntArm 12 n Integers.Int.zero

/-- `Asmgen.decompose_int`: never empty. -/
def decomposeInt (o : Options) (n : Integers.Int) : List Integers.Int :=
  match decomposeIntBase o n with
  | [] => [Integers.Int.zero]
  | l => l

/-- `Asmgen.iterate_op` -/
def iterateOp (op1 op2 : ShiftOp → Instruction) (l : List Integers.Int) (k : Code) : Code :=
  match l with
  | [] => op1 (.SOimm Integers.Int.zero) :: k
  | i :: l' => op1 (.SOimm i) :: l'.map (fun i => op2 (.SOimm i)) ++ k

/-! ## Smart constructors for integer immediate arguments -/

/-- `Asmgen.loadimm_word` -/
def loadimmWord (r : Ireg) (n : Integers.Int) (k : Code) : Code :=
  let hi := Integers.Int.shru n (I 16)
  if Integers.Int.eq hi Integers.Int.zero then .Pmovw r n :: k
  else .Pmovw r (Integers.Int.zero_ext 16 n) :: .Pmovt r hi :: k

/-- `Asmgen.loadimm` -/
def loadimm (o : Options) (r : Ireg) (n : Integers.Int) (k : Code) : Code :=
  let d1 := decomposeInt o n
  let d2 := decomposeInt o (Integers.Int.not n)
  if d1.length ≤ 1 then .Pmov r (.SOimm n) :: k
  else if d2.length ≤ 1 then .Pmvn r (.SOimm (Integers.Int.not n)) :: k
  else if o.params.thumb2Support then loadimmWord r n k
  else if d1.length ≤ d2.length then iterateOp (.Pmov r) (.Porr r r) d1 k
  else iterateOp (.Pmvn r) (.Pbic r r) d2 k

/-- `Asmgen.addimm` -/
def addimm (o : Options) (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.ltu (I (-256)) n then .Psub r1 r2 (.SOimm (Integers.Int.neg n)) :: k
  else
    let d1 := decomposeInt o n
    let d2 := decomposeInt o (Integers.Int.neg n)
    if d1.length ≤ d2.length then iterateOp (.Padd r1 r2) (.Padd r1 r1) d1 k
    else iterateOp (.Psub r1 r2) (.Psub r1 r1) d2 k

/-- `Asmgen.rsubimm` -/
def rsubimm (o : Options) (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  iterateOp (.Prsb r1 r2) (.Padd r1 r1) (decomposeInt o n) k

/-- `Asmgen.andimm` -/
def andimm (o : Options) (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if isImmedArith o n then .Pand r1 r2 (.SOimm n) :: k
  else iterateOp (.Pbic r1 r2) (.Pbic r1 r1) (decomposeInt o (Integers.Int.not n)) k

/-- `Asmgen.orimm` -/
def orimm (o : Options) (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  iterateOp (.Porr r1 r2) (.Porr r1 r1) (decomposeInt o n) k

/-- `Asmgen.xorimm` -/
def xorimm (o : Options) (r1 r2 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  iterateOp (.Peor r1 r2) (.Peor r1 r1) (decomposeInt o n) k

/-! ## Shifts and conditions -/

/-- `Asmgen.transl_shift` -/
def translShift (s : Shift) (r : Ireg) : ShiftOp :=
  match s with
  | .Slsl n => .SOlsl r n.s_amount
  | .Slsr n => .SOlsr r n.s_amount
  | .Sasr n => .SOasr r n.s_amount
  | .Sror n => .SOror r n.s_amount

/-- Comparison with an integer immediate (shared by `Ccompimm` and
`Ccompuimm` in `transl_cond`). -/
def translCmpImm (o : Options) (r1 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if isImmedArith o n then .Pcmp r1 (.SOimm n) :: k
  else if isImmedArith o (Integers.Int.neg n) then .Pcmn r1 (.SOimm (Integers.Int.neg n)) :: k
  else loadimm o .IR14 n (.Pcmp r1 (.SOreg .IR14) :: k)

/-- `Asmgen.transl_cond`: prepends to `k` the instructions that set the
condition flags according to `cond`. -/
def translCond (o : Options) (cond : Condition) (args : List Mreg) (k : Code) : Res Code :=
  match cond, args with
  | .Ccomp _, [a1, a2] | .Ccompu _, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2
    pure (.Pcmp r1 (.SOreg r2) :: k)
  | .Ccompshift _ s, [a1, a2] | .Ccompushift _ s, [a1, a2] => do
    let r1 ← iregOf a1; let r2 ← iregOf a2
    pure (.Pcmp r1 (translShift s r2) :: k)
  | .Ccompimm _ n, [a1] | .Ccompuimm _ n, [a1] => do
    let r1 ← iregOf a1
    pure (translCmpImm o r1 n k)
  | .Ccompf _, [a1, a2] | .Cnotcompf _, [a1, a2] => do
    let r1 ← fregOf a1; let r2 ← fregOf a2
    pure (.Pfcmpd r1 r2 :: k)
  | .Ccompfzero _, [a1] | .Cnotcompfzero _, [a1] => do
    let r1 ← fregOf a1
    pure (.Pfcmpzd r1 :: k)
  | .Ccompfs _, [a1, a2] | .Cnotcompfs _, [a1, a2] => do
    let r1 ← fregOf a1; let r2 ← fregOf a2
    pure (.Pfcmps r1 r2 :: k)
  | .Ccompfszero _, [a1] | .Cnotcompfszero _, [a1] => do
    let r1 ← fregOf a1
    pure (.Pfcmpzs r1 :: k)
  | _, _ => .Error "Asmgen.transl_cond"

/-- `Asmgen.cond_for_signed_cmp` -/
def condForSignedCmp : Comparison → Testcond
  | .Ceq => .TCeq | .Cne => .TCne | .Clt => .TClt
  | .Cle => .TCle | .Cgt => .TCgt | .Cge => .TCge

/-- `Asmgen.cond_for_unsigned_cmp` -/
def condForUnsignedCmp : Comparison → Testcond
  | .Ceq => .TCeq | .Cne => .TCne | .Clt => .TClo
  | .Cle => .TCls | .Cgt => .TChi | .Cge => .TChs

/-- `Asmgen.cond_for_float_cmp` -/
def condForFloatCmp : Comparison → Testcond
  | .Ceq => .TCeq | .Cne => .TCne | .Clt => .TCmi
  | .Cle => .TCls | .Cgt => .TCgt | .Cge => .TCge

/-- `Asmgen.cond_for_float_not_cmp` -/
def condForFloatNotCmp : Comparison → Testcond
  | .Ceq => .TCne | .Cne => .TCeq | .Clt => .TCpl
  | .Cle => .TChi | .Cgt => .TCle | .Cge => .TClt

/-- `Asmgen.cond_for_cond` -/
def condForCond : Condition → Testcond
  | .Ccomp c | .Ccompshift c _ | .Ccompimm c _ => condForSignedCmp c
  | .Ccompu c | .Ccompushift c _ | .Ccompuimm c _ => condForUnsignedCmp c
  | .Ccompf c | .Ccompfzero c | .Ccompfs c | .Ccompfszero c => condForFloatCmp c
  | .Cnotcompf c | .Cnotcompfzero c | .Cnotcompfs c | .Cnotcompfszero c =>
    condForFloatNotCmp c

/-! ## Arithmetic operations -/

/-- A binary integer operation `r <- mk r1 r2` (helper of `transl_op`). -/
def binInt (mk : Ireg → Ireg → Ireg → Instruction) (res a1 a2 : Mreg) (k : Code) : Res Code := do
  let r ← iregOf res; let r1 ← iregOf a1; let r2 ← iregOf a2
  pure (mk r r1 r2 :: k)

/-- A unary float operation `r <- mk r1` (helper of `transl_op`). -/
def unFloat (mk : Freg → Freg → Instruction) (res a1 : Mreg) (k : Code) : Res Code := do
  let r ← fregOf res; let r1 ← fregOf a1
  pure (mk r r1 :: k)

/-- A binary float operation `r <- mk r1 r2` (helper of `transl_op`). -/
def binFloat (mk : Freg → Freg → Freg → Instruction) (res a1 a2 : Mreg) (k : Code) :
    Res Code := do
  let r ← fregOf res; let r1 ← fregOf a1; let r2 ← fregOf a2
  pure (mk r r1 r2 :: k)

/-- A float-to-integer conversion (helper of `transl_op`). -/
def convFI (mk : Ireg → Freg → Instruction) (res a1 : Mreg) (k : Code) : Res Code := do
  let r ← iregOf res; let r1 ← fregOf a1
  pure (mk r r1 :: k)

/-- An integer-to-float conversion (helper of `transl_op`). -/
def convIF (mk : Freg → Ireg → Instruction) (res a1 : Mreg) (k : Code) : Res Code := do
  let r ← fregOf res; let r1 ← iregOf a1
  pure (mk r r1 :: k)

/-- An integer operation with an immediate argument (helper of `transl_op`). -/
def immInt (mk : Ireg → Ireg → Code → Code) (res a1 : Mreg) (k : Code) : Res Code := do
  let r ← iregOf res; let r1 ← iregOf a1
  pure (mk r r1 k)

/-- Division, signed or unsigned: without hardware division, the arguments
and the result must be in the registers expected by the run-time library. -/
def translDiv (o : Options) (mk : Ireg → Ireg → Ireg → Instruction) (res a1 a2 : Mreg)
    (k : Code) : Res Code := do
  let r ← iregOf res; let r1 ← iregOf a1; let r2 ← iregOf a2
  if o.params.hardwareIdiv then pure (mk r r1 r2 :: k)
  else
    assert (decide (res = .R0)) <| assert (decide (a1 = .R0)) <| assert (decide (a2 = .R1)) <|
      pure (mk r r1 r2 :: k)

/-- `Asmgen.transl_op`: the instructions computing `res <- op(args)`,
prepended to `k`. -/
def translOp (o : Options) (op : Operation) (args : List Mreg) (res : Mreg) (k : Code) :
    Res Code :=
  match op, args with
  | .Omove, [a1] =>
    match pregOf res, pregOf a1 with
    | .IR r, .IR a => .OK (.Pmov r (.SOreg a) :: k)
    | .FR r, .FR a => .OK (.Pfcpyd r a :: k)
    | _, _ => .Error "Asmgen.Omove"
  | .Ointconst n, [] => do let r ← iregOf res; pure (loadimm o r n k)
  | .Ofloatconst f, [] => do let r ← fregOf res; pure (.Pflid r f :: k)
  | .Osingleconst f, [] => do let r ← fregOf res; pure (.Pflis r f :: k)
  | .Oaddrsymbol s ofs, [] => do let r ← iregOf res; pure (.Ploadsymbol r s ofs :: k)
  | .Oaddrstack n, [] => do
    let r ← iregOf res
    pure (addimm o r .IR13 (Integers.Ptrofs.to_int n) k)
  | .Ocast8signed, [a1] => do
    let r ← iregOf res; let r1 ← iregOf a1
    pure (if o.params.thumb2Support then .Psbfx r r1 Integers.Int.zero (I 8) :: k
          else .Pmov r (.SOlsl r1 (I 24)) :: .Pmov r (.SOasr r (I 24)) :: k)
  | .Ocast16signed, [a1] => do
    let r ← iregOf res; let r1 ← iregOf a1
    pure (if o.params.thumb2Support then .Psbfx r r1 Integers.Int.zero (I 16) :: k
          else .Pmov r (.SOlsl r1 (I 16)) :: .Pmov r (.SOasr r (I 16)) :: k)
  | .Oadd, [a1, a2] => binInt (fun r r1 r2 => .Padd r r1 (.SOreg r2)) res a1 a2 k
  | .Oaddshift s, [a1, a2] => binInt (fun r r1 r2 => .Padd r r1 (translShift s r2)) res a1 a2 k
  | .Oaddimm n, [a1] => immInt (fun r r1 => addimm o r r1 n) res a1 k
  | .Osub, [a1, a2] => binInt (fun r r1 r2 => .Psub r r1 (.SOreg r2)) res a1 a2 k
  | .Osubshift s, [a1, a2] => binInt (fun r r1 r2 => .Psub r r1 (translShift s r2)) res a1 a2 k
  | .Orsubshift s, [a1, a2] => binInt (fun r r1 r2 => .Prsb r r1 (translShift s r2)) res a1 a2 k
  | .Orsubimm n, [a1] => immInt (fun r r1 => rsubimm o r r1 n) res a1 k
  | .Omul, [a1, a2] => binInt .Pmul res a1 a2 k
  | .Omla, [a1, a2, a3] => do
    let r ← iregOf res; let r1 ← iregOf a1; let r2 ← iregOf a2; let r3 ← iregOf a3
    pure (.Pmla r r1 r2 r3 :: k)
  | .Omulhs, [a1, a2] => binInt (fun r r1 r2 => .Psmull .IR14 r r1 r2) res a1 a2 k
  | .Omulhu, [a1, a2] => binInt (fun r r1 r2 => .Pumull .IR14 r r1 r2) res a1 a2 k
  | .Odiv, [a1, a2] => translDiv o .Psdiv res a1 a2 k
  | .Odivu, [a1, a2] => translDiv o .Pudiv res a1 a2 k
  | .Oand, [a1, a2] => binInt (fun r r1 r2 => .Pand r r1 (.SOreg r2)) res a1 a2 k
  | .Oandshift s, [a1, a2] => binInt (fun r r1 r2 => .Pand r r1 (translShift s r2)) res a1 a2 k
  | .Oandimm n, [a1] => immInt (fun r r1 => andimm o r r1 n) res a1 k
  | .Oor, [a1, a2] => binInt (fun r r1 r2 => .Porr r r1 (.SOreg r2)) res a1 a2 k
  | .Oorshift s, [a1, a2] => binInt (fun r r1 r2 => .Porr r r1 (translShift s r2)) res a1 a2 k
  | .Oorimm n, [a1] => immInt (fun r r1 => orimm o r r1 n) res a1 k
  | .Oxor, [a1, a2] => binInt (fun r r1 r2 => .Peor r r1 (.SOreg r2)) res a1 a2 k
  | .Oxorshift s, [a1, a2] => binInt (fun r r1 r2 => .Peor r r1 (translShift s r2)) res a1 a2 k
  | .Oxorimm n, [a1] => immInt (fun r r1 => xorimm o r r1 n) res a1 k
  | .Obic, [a1, a2] => binInt (fun r r1 r2 => .Pbic r r1 (.SOreg r2)) res a1 a2 k
  | .Obicshift s, [a1, a2] => binInt (fun r r1 r2 => .Pbic r r1 (translShift s r2)) res a1 a2 k
  | .Onot, [a1] => immInt (fun r r1 k => .Pmvn r (.SOreg r1) :: k) res a1 k
  | .Onotshift s, [a1] => immInt (fun r r1 k => .Pmvn r (translShift s r1) :: k) res a1 k
  | .Oshl, [a1, a2] => binInt .Plsl res a1 a2 k
  | .Oshr, [a1, a2] => binInt .Pasr res a1 a2 k
  | .Oshru, [a1, a2] => binInt .Plsr res a1 a2 k
  | .Oshift s, [a1] => immInt (fun r r1 k => .Pmov r (translShift s r1) :: k) res a1 k
  | .Oshrximm n, [a1] => do
    let r ← iregOf res; let r1 ← iregOf a1
    if Integers.Int.eq n Integers.Int.zero then pure (.Pmov r (.SOreg r1) :: k)
    else
      pure (.Pmov .IR14 (.SOasr r1 (I 31)) ::
            .Padd .IR14 r1 (.SOlsr .IR14 (Integers.Int.sub Integers.Int.iwordsize n)) ::
            .Pmov r (.SOasr .IR14 n) :: k)
  | .Onegf, [a1] => unFloat .Pfnegd res a1 k
  | .Oabsf, [a1] => unFloat .Pfabsd res a1 k
  | .Oaddf, [a1, a2] => binFloat .Pfaddd res a1 a2 k
  | .Osubf, [a1, a2] => binFloat .Pfsubd res a1 a2 k
  | .Omulf, [a1, a2] => binFloat .Pfmuld res a1 a2 k
  | .Odivf, [a1, a2] => binFloat .Pfdivd res a1 a2 k
  | .Onegfs, [a1] => unFloat .Pfnegs res a1 k
  | .Oabsfs, [a1] => unFloat .Pfabss res a1 k
  | .Oaddfs, [a1, a2] => binFloat .Pfadds res a1 a2 k
  | .Osubfs, [a1, a2] => binFloat .Pfsubs res a1 a2 k
  | .Omulfs, [a1, a2] => binFloat .Pfmuls res a1 a2 k
  | .Odivfs, [a1, a2] => binFloat .Pfdivs res a1 a2 k
  | .Osingleoffloat, [a1] => unFloat .Pfcvtsd res a1 k
  | .Ofloatofsingle, [a1] => unFloat .Pfcvtds res a1 k
  | .Ointoffloat, [a1] => convFI .Pftosizd res a1 k
  | .Ointuoffloat, [a1] => convFI .Pftouizd res a1 k
  | .Ofloatofint, [a1] => convIF .Pfsitod res a1 k
  | .Ofloatofintu, [a1] => convIF .Pfuitod res a1 k
  | .Ointofsingle, [a1] => convFI .Pftosizs res a1 k
  | .Ointuofsingle, [a1] => convFI .Pftouizs res a1 k
  | .Osingleofint, [a1] => convIF .Pfsitos res a1 k
  | .Osingleofintu, [a1] => convIF .Pfuitos res a1 k
  | .Ocmp cmp, _ => do
    let r ← iregOf res
    translCond o cmp args
      (.Pmovite (condForCond cmp) r (.SOimm Integers.Int.one) (.SOimm Integers.Int.zero) :: k)
  | .Osel cmp _, a1 :: a2 :: args =>
    match pregOf res with
    | .IR r => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      if r1 = r2 then pure (.Pmov r (.SOreg r1) :: k)
      else translCond o cmp args (.Pmovite (condForCond cmp) r (.SOreg r1) (.SOreg r2) :: k)
    | .FR r => do
      let r1 ← fregOf a1; let r2 ← fregOf a2
      if r1 = r2 then pure (.Pfcpyd r r1 :: k)
      else translCond o cmp args (.Pfmovite (condForCond cmp) r r1 r2 :: k)
    | _ => .Error "Asmgen.Osel"
  | _, _ => .Error "Asmgen.transl_op"

/-! ## Accessing data in the stack frame -/

/-- `Asmgen.indexed_memory_access` -/
def indexedMemoryAccess (o : Options) (mkInstr : Ireg → Integers.Int → Instruction)
    (mkImmed : Integers.Int → Integers.Int) (base : Ireg) (n : Integers.Int) (k : Code) : Code :=
  let n1 := mkImmed n
  if Integers.Int.eq n n1 then mkInstr base n :: k
  else addimm o .IR14 base (Integers.Int.sub n n1) (mkInstr .IR14 n1 :: k)

/-- `Asmgen.loadind_int` -/
def loadindInt (o : Options) (base : Ireg) (ofs : Integers.Ptrofs) (dst : Ireg) (k : Code) :
    Code :=
  indexedMemoryAccess o (fun base n => .Pldr dst base (.SOimm n)) (mkImmedMemWord o) base
    (Integers.Ptrofs.to_int ofs) k

/-- `Asmgen.loadind` -/
def loadind (o : Options) (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg)
    (k : Code) : Res Code :=
  let ofs := Integers.Ptrofs.to_int ofs
  match ty, pregOf dst with
  | .Tint, .IR r =>
    .OK (indexedMemoryAccess o (fun base n => .Pldr r base (.SOimm n)) (mkImmedMemWord o) base ofs k)
  | .Tany32, .IR r =>
    .OK (indexedMemoryAccess o (fun base n => .Pldr_a r base (.SOimm n)) (mkImmedMemWord o)
      base ofs k)
  | .Tsingle, .FR r => .OK (indexedMemoryAccess o (.Pflds r) mkImmedMemFloat base ofs k)
  | .Tfloat, .FR r => .OK (indexedMemoryAccess o (.Pfldd r) mkImmedMemFloat base ofs k)
  | .Tany64, .FR r => .OK (indexedMemoryAccess o (.Pfldd_a r) mkImmedMemFloat base ofs k)
  | _, _ => .Error "Asmgen.loadind"

/-- `Asmgen.storeind` -/
def storeind (o : Options) (src : Mreg) (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp)
    (k : Code) : Res Code :=
  let ofs := Integers.Ptrofs.to_int ofs
  match ty, pregOf src with
  | .Tint, .IR r =>
    .OK (indexedMemoryAccess o (fun base n => .Pstr r base (.SOimm n)) (mkImmedMemWord o) base ofs k)
  | .Tany32, .IR r =>
    .OK (indexedMemoryAccess o (fun base n => .Pstr_a r base (.SOimm n)) (mkImmedMemWord o)
      base ofs k)
  | .Tsingle, .FR r => .OK (indexedMemoryAccess o (.Pfsts r) mkImmedMemFloat base ofs k)
  | .Tfloat, .FR r => .OK (indexedMemoryAccess o (.Pfstd r) mkImmedMemFloat base ofs k)
  | .Tany64, .FR r => .OK (indexedMemoryAccess o (.Pfstd_a r) mkImmedMemFloat base ofs k)
  | _, _ => .Error "Asmgen.storeind"

/-- `Asmgen.save_lr`: saves the return address at the beginning of a
function, using `R12` (not `R14`) as temporary. -/
def saveLr (o : Options) (ofs : Integers.Ptrofs) (k : Code) : Code :=
  let n := Integers.Ptrofs.to_int ofs
  let n1 := mkImmedMemWord o n
  if Integers.Int.eq n n1 then .Pstr .IR14 .IR13 (.SOimm n) :: k
  else addimm o .IR12 .IR13 (Integers.Int.sub n n1) (.Pstr .IR14 .IR12 (.SOimm n1) :: k)

/-- `Asmgen.save_lr_preserves_R12` -/
def saveLrPreservesR12 (o : Options) (ofs : Integers.Ptrofs) : Bool :=
  let n := Integers.Ptrofs.to_int ofs
  Integers.Int.eq n (mkImmedMemWord o n)

/-! ## Memory accesses -/

/-- `Asmgen.transl_memory_access` -/
def translMemoryAccess (o : Options) (mkInstrImm : Ireg → Integers.Int → Instruction)
    (mkInstrGen : Option (Ireg → ShiftOp → Instruction)) (mkImmed : Integers.Int → Integers.Int)
    (addr : Addressing) (args : List Mreg) (k : Code) : Res Code :=
  match addr, args with
  | .Aindexed n, [a1] => do
    let r1 ← iregOf a1
    pure (indexedMemoryAccess o mkInstrImm mkImmed r1 n k)
  | .Aindexed2, [a1, a2] =>
    match mkInstrGen with
    | some f => do let r1 ← iregOf a1; let r2 ← iregOf a2; pure (f r1 (.SOreg r2) :: k)
    | none => .Error "Asmgen.Aindexed2"
  | .Aindexed2shift s, [a1, a2] =>
    match mkInstrGen with
    | some f => do let r1 ← iregOf a1; let r2 ← iregOf a2; pure (f r1 (translShift s r2) :: k)
    | none => .Error "Asmgen.Aindexed2shift"
  | .Ainstack n, [] =>
    .OK (indexedMemoryAccess o mkInstrImm mkImmed .IR13 (Integers.Ptrofs.to_int n) k)
  | _, _ => .Error "Asmgen.transl_memory_access"

/-- `Asmgen.transl_memory_access_int` -/
def translMemoryAccessInt (o : Options) (mkInstr : Ireg → Ireg → ShiftOp → Instruction)
    (mkImmed : Integers.Int → Integers.Int) (dst : Mreg) (addr : Addressing) (args : List Mreg)
    (k : Code) : Res Code := do
  let rd ← iregOf dst
  translMemoryAccess o (fun r n => mkInstr rd r (.SOimm n)) (some (mkInstr rd)) mkImmed addr args k

/-- `Asmgen.transl_memory_access_float` -/
def translMemoryAccessFloat (o : Options) (mkInstr : Freg → Ireg → Integers.Int → Instruction)
    (mkImmed : Integers.Int → Integers.Int) (dst : Mreg) (addr : Addressing) (args : List Mreg)
    (k : Code) : Res Code := do
  let rd ← fregOf dst
  translMemoryAccess o (mkInstr rd) none mkImmed addr args k

/-- `Asmgen.transl_load` -/
def translLoad (o : Options) (chunk : Chunk) (addr : Addressing) (args : List Mreg) (dst : Mreg)
    (k : Code) : Res Code :=
  match chunk with
  | .Mint8signed => translMemoryAccessInt o .Pldrsb mkImmedMemSmall dst addr args k
  | .Mint8unsigned => translMemoryAccessInt o .Pldrb (mkImmedMemWord o) dst addr args k
  | .Mint16signed => translMemoryAccessInt o .Pldrsh mkImmedMemSmall dst addr args k
  | .Mint16unsigned => translMemoryAccessInt o .Pldrh mkImmedMemSmall dst addr args k
  | .Mint32 => translMemoryAccessInt o .Pldr (mkImmedMemWord o) dst addr args k
  | .Mfloat32 => translMemoryAccessFloat o .Pflds mkImmedMemFloat dst addr args k
  | .Mfloat64 => translMemoryAccessFloat o .Pfldd mkImmedMemFloat dst addr args k
  | _ => .Error "Asmgen.transl_load"

/-- `Asmgen.transl_store` -/
def translStore (o : Options) (chunk : Chunk) (addr : Addressing) (args : List Mreg) (src : Mreg)
    (k : Code) : Res Code :=
  match chunk with
  | .Mint8unsigned => translMemoryAccessInt o .Pstrb (mkImmedMemWord o) src addr args k
  | .Mint16unsigned => translMemoryAccessInt o .Pstrh mkImmedMemSmall src addr args k
  | .Mint32 => translMemoryAccessInt o .Pstr (mkImmedMemWord o) src addr args k
  | .Mfloat32 => translMemoryAccessFloat o .Pfsts mkImmedMemFloat src addr args k
  | .Mfloat64 => translMemoryAccessFloat o .Pfstd mkImmedMemFloat src addr args k
  | _ => .Error "Asmgen.transl_store"

/-! ## Instructions, code and functions -/

/-- `Asmgen.transl_instr`; `r12IsParent` tells whether `R12` holds the
parent frame (the back link) on entry. -/
def translInstr (o : Options) (f : Mach.Function) (i : Mach.Instruction) (r12IsParent : Bool)
    (k : Code) : Res Code :=
  match i with
  | .Mgetstack ofs ty dst => loadind o .IR13 ofs ty dst k
  | .Msetstack src ofs ty => storeind o src .IR13 ofs ty k
  | .Mgetparam ofs ty dst => do
    let c ← loadind o .IR12 ofs ty dst k
    pure (if r12IsParent then c else loadindInt o .IR13 f.fn_link_ofs .IR12 c)
  | .Mop op args res => translOp o op args res k
  | .Mload chunk addr args dst => translLoad o chunk addr args dst k
  | .Mstore chunk addr args src => translStore o chunk addr args src k
  | .Mcall sig (.inl arg) => do let r ← iregOf arg; pure (.Pblreg r sig :: k)
  | .Mcall sig (.inr symb) => .OK (.Pblsymb symb sig :: k)
  | .Mtailcall sig (.inl arg) => do
    let r ← iregOf arg
    pure (loadindInt o .IR13 f.fn_retaddr_ofs .IR14
      (.Pfreeframe f.fn_stacksize f.fn_link_ofs :: .Pbreg r sig :: k))
  | .Mtailcall sig (.inr symb) =>
    .OK (loadindInt o .IR13 f.fn_retaddr_ofs .IR14
      (.Pfreeframe f.fn_stacksize f.fn_link_ofs :: .Pbsymb symb sig :: k))
  | .Mbuiltin ef args res =>
    .OK (.Pbuiltin ef (args.map (BuiltinArg.map pregOf)) (BuiltinRes.map pregOf res) :: k)
  | .Mlabel lbl => .OK (.Plabel lbl :: k)
  | .Mgoto lbl => .OK (.Pb lbl :: k)
  | .Mcond cond args lbl => translCond o cond args (.Pbc (condForCond cond) lbl :: k)
  | .Mjumptable arg tbl => do let r ← iregOf arg; pure (.Pbtbl r tbl :: k)
  | .Mreturn =>
    .OK (loadindInt o .IR13 f.fn_retaddr_ofs .IR14
      (.Pfreeframe f.fn_stacksize f.fn_link_ofs :: .Pbreg .IR14 f.fn_sig :: k))

/-- `Asmgen.it1_is_parent` -/
def it1IsParent (before : Bool) (i : Mach.Instruction) : Bool :=
  match i with
  | .Msetstack .. => before
  | .Mgetparam _ _ dst => !(decide (dst = .R12))
  | .Mop .Omove _ res => before && !(decide (res = .R12))
  | _ => false

/-- `Asmgen.transl_code` (the specification; not tail-recursive) -/
def translCode (o : Options) (f : Mach.Function) : List Mach.Instruction → Bool → Res Code
  | [], _ => .OK []
  | i1 :: il', it1p => do
    let k ← translCode o f il' (it1IsParent it1p i1)
    translInstr o f i1 it1p k

/-- `Asmgen.transl_code_rec`: the same in continuation-passing style. -/
def translCodeRec (o : Options) (f : Mach.Function) :
    List Mach.Instruction → Bool → (Code → Res Code) → Res Code
  | [], _, k => k []
  | i1 :: il', it1p, k =>
    translCodeRec o f il' (it1IsParent it1p i1)
      (fun c1 => do let c2 ← translInstr o f i1 it1p c1; k c2)

/-- `Asmgen.transl_code'` -/
def translCode' (o : Options) (f : Mach.Function) (il : List Mach.Instruction) (it1p : Bool) :
    Res Code :=
  translCodeRec o f il it1p (fun c => .OK c)

/-- `Asmgen.transl_function` -/
def translFunction (o : Options) (f : Mach.Function) : Res Asm.Function := do
  let c ← translCode o f f.fn_code (saveLrPreservesR12 o f.fn_retaddr_ofs)
  pure { fn_sig := f.fn_sig,
         fn_code := .Pallocframe f.fn_stacksize f.fn_link_ofs ::
           saveLr o f.fn_retaddr_ofs
             (.Pcfi_rel_offset (Integers.Ptrofs.to_int f.fn_retaddr_ofs) :: c) }

/-- `Asmgen.transf_function`: the code must have fewer than `2^32`
instructions, so that the offset part of `PC` cannot wrap around. -/
def transfFunction (o : Options) (f : Mach.Function) : Res Asm.Function := do
  let tf ← translFunction o f
  if Integers.Ptrofs.max_unsigned < (tf.fn_code.length : Z) then .Error "code size exceeded"
  else pure tf

/-- `Asmgen.transf_fundef` -/
def transfFundef (o : Options) (f : Mach.Fundef) : Res Asm.Fundef :=
  ASTFundef.transfPartial (transfFunction o) f

/-- `Asmgen.transf_program` -/
def transfProgram (o : Options) (p : Mach.Program) : Res Asm.Program :=
  transformPartialProgram (transfFundef o) p

/-! ## Equivalence of the two code translations (`Asmgenproof.v`) -/

private theorem translCodeRec_spec (o : Options) (f : Mach.Function) :
    ∀ (il : List Mach.Instruction) (it1p : Bool) (k : Code → Res Code),
      translCodeRec o f il it1p k = Res.bind (translCode o f il it1p) k
  | [], _, _ => rfl
  | i1 :: il', it1p, k => by
    rw [translCodeRec, translCodeRec_spec o f il']
    simp only [translCode]
    show _ = Res.bind (Res.bind _ _) _
    cases translCode o f il' (it1IsParent it1p i1) with
    | OK a => rfl
    | Error m => rfl

/-- `Asmgenproof.transl_code'_transl_code` -/
theorem translCode'_translCode (o : Options) (f : Mach.Function) (il : List Mach.Instruction)
    (it1p : Bool) : translCode' o f il it1p = translCode o f il it1p := by
  rw [translCode', translCodeRec_spec]
  cases translCode o f il it1p <;> rfl

end Asmgen
end Arm
end CC
