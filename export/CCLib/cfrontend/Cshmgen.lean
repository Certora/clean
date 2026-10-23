/-
  Translation from Clight to Csharpminor — port of `cfrontend/Cshmgen.v`
  (the whole file).

  This is the third pass of CompCert's compiler.  It resolves every
  type-dependent behaviour (overloaded operators, address computations for
  array and struct accesses, …) and turns Clight's loops and `switch`
  statements into Csharpminor's simpler `block`/`loop`/`exit` structure.

  Differences from Rocq:
  * `Conventions1.return_value_needs_normalization` is target-dependent (and,
    on aarch64, depends on the OCaml parameter `Archi.abi`); the translation
    of statements, functions and programs takes this function as an explicit
    argument `rvNorm : XType → Bool`.  The aarch64 driver passes
    `Conventions1.returnValueNeedsNormalization abi`, the x86-64 driver
    `X86.Conventions1.returnValueNeedsNormalization`.
  * Error messages are plain strings (the port's `Res`).
-/
import CCLib.cfrontend.Csharpminor
import CCLib.cfrontend.Clight
import CCLib.aarch64.Conventions1

namespace CC
namespace Cshmgen

open Cminor (UnaryOperation BinaryOperation)
open Cminor.UnaryOperation Cminor.BinaryOperation

local notation "CExpr" => Csharpminor.Expr
local notation "CStmt" => Csharpminor.Stmt

/-! ## Operations over expressions -/

/-- `Cshmgen.make_intconst` -/
def makeIntconst (n : Integers.Int) : CExpr := .Econst (.Ointconst n)
/-- `Cshmgen.make_longconst` -/
def makeLongconst (f : Integers.Int64) : CExpr := .Econst (.Olongconst f)
/-- `Cshmgen.make_floatconst` -/
def makeFloatconst (f : Floats.Float) : CExpr := .Econst (.Ofloatconst f)
/-- `Cshmgen.make_singleconst` -/
def makeSingleconst (f : Floats.Float32) : CExpr := .Econst (.Osingleconst f)

/-- `Cshmgen.make_ptrofsconst` -/
def makePtrofsconst (n : Z) : CExpr :=
  if Archi.ptr64 then makeLongconst (Integers.Int64.repr n) else makeIntconst (Integers.Int.repr n)

/-- `Cshmgen.make_singleoffloat` -/
def makeSingleoffloat (e : CExpr) : CExpr := .Eunop Osingleoffloat e
/-- `Cshmgen.make_floatofsingle` -/
def makeFloatofsingle (e : CExpr) : CExpr := .Eunop Ofloatofsingle e

/-- `Cshmgen.make_floatofint` -/
def makeFloatofint (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Ofloatofint e
  | .Unsigned => .Eunop Ofloatofintu e
/-- `Cshmgen.make_singleofint` -/
def makeSingleofint (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Osingleofint e
  | .Unsigned => .Eunop Osingleofintu e
/-- `Cshmgen.make_intoffloat` -/
def makeIntoffloat (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Ointoffloat e
  | .Unsigned => .Eunop Ointuoffloat e
/-- `Cshmgen.make_intofsingle` -/
def makeIntofsingle (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Ointofsingle e
  | .Unsigned => .Eunop Ointuofsingle e
/-- `Cshmgen.make_longofint` -/
def makeLongofint (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Olongofint e
  | .Unsigned => .Eunop Olongofintu e
/-- `Cshmgen.make_floatoflong` -/
def makeFloatoflong (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Ofloatoflong e
  | .Unsigned => .Eunop Ofloatoflongu e
/-- `Cshmgen.make_singleoflong` -/
def makeSingleoflong (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Osingleoflong e
  | .Unsigned => .Eunop Osingleoflongu e
/-- `Cshmgen.make_longoffloat` -/
def makeLongoffloat (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Olongoffloat e
  | .Unsigned => .Eunop Olonguoffloat e
/-- `Cshmgen.make_longofsingle` -/
def makeLongofsingle (e : CExpr) : Signedness → CExpr
  | .Signed => .Eunop Olongofsingle e
  | .Unsigned => .Eunop Olonguofsingle e

/-- `Cshmgen.make_cmpu_ne_zero` -/
def makeCmpuNeZero (e : CExpr) : CExpr :=
  match e with
  | .Ebinop (.Ocmp _) _ _ => e
  | .Ebinop (.Ocmpu _) _ _ => e
  | .Ebinop (.Ocmpf _) _ _ => e
  | .Ebinop (.Ocmpfs _) _ _ => e
  | .Ebinop (.Ocmpl _) _ _ => e
  | .Ebinop (.Ocmplu _) _ _ => e
  | _ => .Ebinop (.Ocmpu .Cne) e (makeIntconst Integers.Int.zero)

/-- `Cshmgen.sizeof`: the size of a complete type. -/
def sizeof (ce : CompositeEnv) (t : Ty) : Res Z :=
  if completeType ce t then .OK (CC.sizeof ce t) else .Error "incomplete type"

/-- `Cshmgen.alignof`: the alignment of a complete type. -/
def alignof (ce : CompositeEnv) (t : Ty) : Res Z :=
  if completeType ce t then .OK (CC.alignof ce t) else .Error "incomplete type"

/-- `Cshmgen.make_cast_int` -/
def makeCastInt (e : CExpr) (sz : IntSize) (si : Signedness) : CExpr :=
  match sz, si with
  | .I8, .Signed => .Eunop Ocast8signed e
  | .I8, .Unsigned => .Eunop Ocast8unsigned e
  | .I16, .Signed => .Eunop Ocast16signed e
  | .I16, .Unsigned => .Eunop Ocast16unsigned e
  | .I32, _ => e
  | .IBool, _ => makeCmpuNeZero e

/-- `Cshmgen.make_cast`: convert a value of type `from` to type `to`. -/
def makeCast (tfrom tto : Ty) (e : CExpr) : Res CExpr :=
  match Cop.classifyCast tfrom tto with
  | .pointer => .OK e
  | .i2i sz2 si2 => .OK (makeCastInt e sz2 si2)
  | .f2f => .OK e
  | .s2s => .OK e
  | .f2s => .OK (makeSingleoffloat e)
  | .s2f => .OK (makeFloatofsingle e)
  | .i2f si1 => .OK (makeFloatofint e si1)
  | .i2s si1 => .OK (makeSingleofint e si1)
  | .f2i sz2 si2 => .OK (makeCastInt (makeIntoffloat e si2) sz2 si2)
  | .s2i sz2 si2 => .OK (makeCastInt (makeIntofsingle e si2) sz2 si2)
  | .l2l => .OK e
  | .i2l si1 => .OK (makeLongofint e si1)
  | .l2i sz2 si2 => .OK (makeCastInt (.Eunop Ointoflong e) sz2 si2)
  | .l2f si1 => .OK (makeFloatoflong e si1)
  | .l2s si1 => .OK (makeSingleoflong e si1)
  | .f2l si2 => .OK (makeLongoffloat e si2)
  | .s2l si2 => .OK (makeLongofsingle e si2)
  | .i2bool => .OK (makeCmpuNeZero e)
  | .f2bool => .OK (.Ebinop (.Ocmpf .Cne) e (makeFloatconst Floats.Float.zero))
  | .s2bool => .OK (.Ebinop (.Ocmpfs .Cne) e (makeSingleconst Floats.Float32.zero))
  | .l2bool => .OK (.Ebinop (.Ocmplu .Cne) e (makeLongconst Integers.Int64.zero))
  | .struct _ _ => .OK e
  | .union _ _ => .OK e
  | .void => .OK e
  | .default => .Error "Cshmgen.make_cast"

/-- `Cshmgen.make_boolean` -/
def makeBoolean (e : CExpr) (ty : Ty) : CExpr :=
  match Cop.classifyBool ty with
  | .i => makeCmpuNeZero e
  | .f => .Ebinop (.Ocmpf .Cne) e (makeFloatconst Floats.Float.zero)
  | .s => .Ebinop (.Ocmpfs .Cne) e (makeSingleconst Floats.Float32.zero)
  | .l => .Ebinop (.Ocmplu .Cne) e (makeLongconst Integers.Int64.zero)
  | .default => e

/-- `Cshmgen.make_notbool` -/
def makeNotbool (e : CExpr) (ty : Ty) : Res CExpr :=
  match Cop.classifyBool ty with
  | .i => .OK (.Ebinop (.Ocmpu .Ceq) e (makeIntconst Integers.Int.zero))
  | .f => .OK (.Ebinop (.Ocmpf .Ceq) e (makeFloatconst Floats.Float.zero))
  | .s => .OK (.Ebinop (.Ocmpfs .Ceq) e (makeSingleconst Floats.Float32.zero))
  | .l => .OK (.Ebinop (.Ocmplu .Ceq) e (makeLongconst Integers.Int64.zero))
  | .default => .Error "Cshmgen.make_notbool"

/-- `Cshmgen.make_neg` -/
def makeNeg (e : CExpr) (ty : Ty) : Res CExpr :=
  match Cop.classifyNeg ty with
  | .i _ => .OK (.Eunop Onegint e)
  | .f => .OK (.Eunop Onegf e)
  | .s => .OK (.Eunop Onegfs e)
  | .l _ => .OK (.Eunop Onegl e)
  | .default => .Error "Cshmgen.make_neg"

/-- `Cshmgen.make_absfloat` -/
def makeAbsfloat (e : CExpr) (ty : Ty) : Res CExpr :=
  match Cop.classifyNeg ty with
  | .i sg => .OK (.Eunop Oabsf (makeFloatofint e sg))
  | .f => .OK (.Eunop Oabsf e)
  | .s => .OK (.Eunop Oabsf (makeFloatofsingle e))
  | .l sg => .OK (.Eunop Oabsf (makeFloatoflong e sg))
  | .default => .Error "Cshmgen.make_absfloat"

/-- `Cshmgen.make_notint` -/
def makeNotint (e : CExpr) (ty : Ty) : Res CExpr :=
  match Cop.classifyNotint ty with
  | .i _ => .OK (.Eunop Onotint e)
  | .l _ => .OK (.Eunop Onotl e)
  | .default => .Error "Cshmgen.make_notint"

/-- `Cshmgen.make_binarith` -/
def makeBinarith (iop iopu fop sop lop lopu : BinaryOperation)
    (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr := do
  let c := Cop.classifyBinarith ty1 ty2
  let ty := Cop.binarithType c
  let e1' ← makeCast ty1 ty e1
  let e2' ← makeCast ty2 ty e2
  match c with
  | .i .Signed => .OK (.Ebinop iop e1' e2')
  | .i .Unsigned => .OK (.Ebinop iopu e1' e2')
  | .f => .OK (.Ebinop fop e1' e2')
  | .s => .OK (.Ebinop sop e1' e2')
  | .l .Signed => .OK (.Ebinop lop e1' e2')
  | .l .Unsigned => .OK (.Ebinop lopu e1' e2')
  | .default => .Error "Cshmgen.make_binarith"

/-- `Cshmgen.make_add_ptr_int` -/
def makeAddPtrInt (ce : CompositeEnv) (ty : Ty) (si : Signedness) (e1 e2 : CExpr) :
    Res CExpr := do
  let sz ← sizeof ce ty
  if Archi.ptr64 then
    let n := makeLongconst (Integers.Int64.repr sz)
    .OK (.Ebinop Oaddl e1 (.Ebinop Omull n (makeLongofint e2 si)))
  else
    let n := makeIntconst (Integers.Int.repr sz)
    .OK (.Ebinop Oadd e1 (.Ebinop Omul n e2))

/-- `Cshmgen.make_add_ptr_long` -/
def makeAddPtrLong (ce : CompositeEnv) (ty : Ty) (e1 e2 : CExpr) : Res CExpr := do
  let sz ← sizeof ce ty
  if Archi.ptr64 then
    let n := makeLongconst (Integers.Int64.repr sz)
    .OK (.Ebinop Oaddl e1 (.Ebinop Omull n e2))
  else
    let n := makeIntconst (Integers.Int.repr sz)
    .OK (.Ebinop Oadd e1 (.Ebinop Omul n (.Eunop Ointoflong e2)))

/-- `Cshmgen.make_add` -/
def makeAdd (ce : CompositeEnv) (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  match Cop.classifyAdd ty1 ty2 with
  | .pi ty si => makeAddPtrInt ce ty si e1 e2
  | .pl ty => makeAddPtrLong ce ty e1 e2
  | .ip si ty => makeAddPtrInt ce ty si e2 e1
  | .lp ty => makeAddPtrLong ce ty e2 e1
  | .default => makeBinarith Oadd Oadd Oaddf Oaddfs Oaddl Oaddl e1 ty1 e2 ty2

/-- `Cshmgen.make_sub` -/
def makeSub (ce : CompositeEnv) (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  match Cop.classifySub ty1 ty2 with
  | .pi ty si => do
    let sz ← sizeof ce ty
    if Archi.ptr64 then
      let n := makeLongconst (Integers.Int64.repr sz)
      .OK (.Ebinop Osubl e1 (.Ebinop Omull n (makeLongofint e2 si)))
    else
      let n := makeIntconst (Integers.Int.repr sz)
      .OK (.Ebinop Osub e1 (.Ebinop Omul n e2))
  | .pp ty => do
    let sz ← sizeof ce ty
    if Archi.ptr64 then
      let n := makeLongconst (Integers.Int64.repr sz)
      .OK (.Ebinop Odivl (.Ebinop Osubl e1 e2) n)
    else
      let n := makeIntconst (Integers.Int.repr sz)
      .OK (.Ebinop Odiv (.Ebinop Osub e1 e2) n)
  | .pl ty => do
    let sz ← sizeof ce ty
    if Archi.ptr64 then
      let n := makeLongconst (Integers.Int64.repr sz)
      .OK (.Ebinop Osubl e1 (.Ebinop Omull n e2))
    else
      let n := makeIntconst (Integers.Int.repr sz)
      .OK (.Ebinop Osub e1 (.Ebinop Omul n (.Eunop Ointoflong e2)))
  | .default => makeBinarith Osub Osub Osubf Osubfs Osubl Osubl e1 ty1 e2 ty2

/-- `Cshmgen.make_mul` -/
def makeMul (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  makeBinarith Omul Omul Omulf Omulfs Omull Omull e1 ty1 e2 ty2

/-- `Cshmgen.make_div` -/
def makeDiv (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  makeBinarith Odiv Odivu Odivf Odivfs Odivl Odivlu e1 ty1 e2 ty2

/-- `Cshmgen.make_binarith_int` -/
def makeBinarithInt (iop iopu lop lopu : BinaryOperation)
    (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr := do
  let c := Cop.classifyBinarith ty1 ty2
  let ty := Cop.binarithType c
  let e1' ← makeCast ty1 ty e1
  let e2' ← makeCast ty2 ty e2
  match c with
  | .i .Signed => .OK (.Ebinop iop e1' e2')
  | .i .Unsigned => .OK (.Ebinop iopu e1' e2')
  | .l .Signed => .OK (.Ebinop lop e1' e2')
  | .l .Unsigned => .OK (.Ebinop lopu e1' e2')
  | .f | .s | .default => .Error "Cshmgen.make_binarith_int"

/-- `Cshmgen.make_mod` -/
def makeMod (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  makeBinarithInt Omod Omodu Omodl Omodlu e1 ty1 e2 ty2
/-- `Cshmgen.make_and` -/
def makeAnd (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  makeBinarithInt Oand Oand Oandl Oandl e1 ty1 e2 ty2
/-- `Cshmgen.make_or` -/
def makeOr (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  makeBinarithInt Oor Oor Oorl Oorl e1 ty1 e2 ty2
/-- `Cshmgen.make_xor` -/
def makeXor (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  makeBinarithInt Oxor Oxor Oxorl Oxorl e1 ty1 e2 ty2

/-- `Cshmgen.make_shl` -/
def makeShl (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  match Cop.classifyShift ty1 ty2 with
  | .ii _ => .OK (.Ebinop Oshl e1 e2)
  | .li _ => .OK (.Ebinop Oshll e1 e2)
  | .il _ => .OK (.Ebinop Oshl e1 (.Eunop Ointoflong e2))
  | .ll _ => .OK (.Ebinop Oshll e1 (.Eunop Ointoflong e2))
  | .default => .Error "Cshmgen.make_shl"

/-- `Cshmgen.make_shr` -/
def makeShr (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  match Cop.classifyShift ty1 ty2 with
  | .ii .Signed => .OK (.Ebinop Oshr e1 e2)
  | .ii .Unsigned => .OK (.Ebinop Oshru e1 e2)
  | .li .Signed => .OK (.Ebinop Oshrl e1 e2)
  | .li .Unsigned => .OK (.Ebinop Oshrlu e1 e2)
  | .il .Signed => .OK (.Ebinop Oshr e1 (.Eunop Ointoflong e2))
  | .il .Unsigned => .OK (.Ebinop Oshru e1 (.Eunop Ointoflong e2))
  | .ll .Signed => .OK (.Ebinop Oshrl e1 (.Eunop Ointoflong e2))
  | .ll .Unsigned => .OK (.Ebinop Oshrlu e1 (.Eunop Ointoflong e2))
  | .default => .Error "Cshmgen.make_shr"

/-- `Cshmgen.make_cmp_ptr` -/
def makeCmpPtr (c : Comparison) (e1 e2 : CExpr) : CExpr :=
  .Ebinop (if Archi.ptr64 then .Ocmplu c else .Ocmpu c) e1 e2

/-- `Cshmgen.make_cmp` -/
def makeCmp (c : Comparison) (e1 : CExpr) (ty1 : Ty) (e2 : CExpr) (ty2 : Ty) : Res CExpr :=
  match Cop.classifyCmp ty1 ty2 with
  | .pp => .OK (makeCmpPtr c e1 e2)
  | .pi si => .OK (makeCmpPtr c e1 (if Archi.ptr64 then makeLongofint e2 si else e2))
  | .ip si => .OK (makeCmpPtr c (if Archi.ptr64 then makeLongofint e1 si else e1) e2)
  | .pl => .OK (makeCmpPtr c e1 (if Archi.ptr64 then e2 else .Eunop Ointoflong e2))
  | .lp => .OK (makeCmpPtr c (if Archi.ptr64 then e1 else .Eunop Ointoflong e1) e2)
  | .default =>
    makeBinarith (.Ocmp c) (.Ocmpu c) (.Ocmpf c) (.Ocmpfs c) (.Ocmpl c) (.Ocmplu c)
      e1 ty1 e2 ty2

/-- `Coqlib.two_p` -/
def twoP (x : Z) : Z := if 0 ≤ x then (2 : Z) ^ x.toNat else 0

/-- `Cshmgen.make_extract_bitfield` -/
def makeExtractBitfield (sz : IntSize) (sg : Signedness) (pos width : Z) (addr : CExpr) :
    Res CExpr :=
  if 0 ≤ pos ∧ 0 < width ∧ pos + width ≤ Cop.bitsizeCarrier sz then
    let amount1 := Integers.Int.repr (Integers.Int.zwordsize - Cop.firstBit sz pos width - width)
    let amount2 := Integers.Int.repr (Integers.Int.zwordsize - width)
    let e1 := Csharpminor.Expr.Eload (Cop.chunkForCarrier sz) addr
    let e2 := Csharpminor.Expr.Ebinop Oshl e1 (makeIntconst amount1)
    let e3 := Csharpminor.Expr.Ebinop (if decide (sz = .IBool) || decide (sg = .Unsigned) then Oshru else Oshr)
      e2 (makeIntconst amount2)
    .OK e3
  else .Error "Cshmgen.extract_bitfield"

/-- `Cshmgen.make_load` -/
def makeLoad (addr : CExpr) (tyRes : Ty) : Bitfield → Res CExpr
  | .Full =>
    match accessMode tyRes with
    | .By_value chunk => .OK (.Eload chunk addr)
    | .By_reference => .OK addr
    | .By_copy => .OK addr
    | .By_nothing => .Error "Cshmgen.make_load"
  | .Bits sz sg pos width => makeExtractBitfield sz sg pos width addr

/-- `Cshmgen.make_store_bitfield` -/
def makeStoreBitfield (sz : IntSize) (_sg : Signedness) (pos width : Z) (addr val : CExpr) :
    Res CStmt :=
  if 0 ≤ pos ∧ 0 < width ∧ pos + width ≤ Cop.bitsizeCarrier sz then
    let amount := Cop.firstBit sz pos width
    let mask := Integers.Int.shl (Integers.Int.repr (twoP width - 1)) (Integers.Int.repr amount)
    let e1 := Csharpminor.Expr.Eload (Cop.chunkForCarrier sz) addr
    let e2 := Csharpminor.Expr.Ebinop Oshl val (makeIntconst (Integers.Int.repr amount))
    let e3 := Csharpminor.Expr.Ebinop Oor (.Ebinop Oand e2 (makeIntconst mask))
      (.Ebinop Oand e1 (makeIntconst (Integers.Int.not mask)))
    .OK (.Sstore (Cop.chunkForCarrier sz) addr e3)
  else .Error "Cshmgen.make_store_bitfield"

/-- `Cshmgen.make_memcpy` -/
def makeMemcpy (ce : CompositeEnv) (dst src : CExpr) (ty : Ty) : Res CStmt := do
  let sz ← sizeof ce ty
  .OK (.Sbuiltin none (.EF_memcpy sz (alignofBlockcopy ce ty)) [dst, src])

/-- `Cshmgen.make_store` -/
def makeStore (ce : CompositeEnv) (addr : CExpr) (ty : Ty) (bf : Bitfield) (rhs : CExpr) :
    Res CStmt :=
  match bf with
  | .Full =>
    match accessMode ty with
    | .By_value chunk => .OK (.Sstore chunk addr rhs)
    | .By_copy => makeMemcpy ce addr rhs ty
    | _ => .Error "Cshmgen.make_store"
  | .Bits sz sg pos width => makeStoreBitfield sz sg pos width addr rhs

/-! ## Translation of operators -/

/-- `Cshmgen.transl_unop` -/
def translUnop (op : Unop) (a : CExpr) (ta : Ty) : Res CExpr :=
  match op with
  | .Onotbool => makeNotbool a ta
  | .Onotint => makeNotint a ta
  | .Oneg => makeNeg a ta
  | .Oabsfloat => makeAbsfloat a ta

/-- `Cshmgen.transl_binop` -/
def translBinop (ce : CompositeEnv) (op : Binop) (a : CExpr) (ta : Ty) (b : CExpr) (tb : Ty) :
    Res CExpr :=
  match op with
  | .Oadd => makeAdd ce a ta b tb
  | .Osub => makeSub ce a ta b tb
  | .Omul => makeMul a ta b tb
  | .Odiv => makeDiv a ta b tb
  | .Omod => makeMod a ta b tb
  | .Oand => makeAnd a ta b tb
  | .Oor => makeOr a ta b tb
  | .Oxor => makeXor a ta b tb
  | .Oshl => makeShl a ta b tb
  | .Oshr => makeShr a ta b tb
  | .Oeq => makeCmp .Ceq a ta b tb
  | .One => makeCmp .Cne a ta b tb
  | .Olt => makeCmp .Clt a ta b tb
  | .Ogt => makeCmp .Cgt a ta b tb
  | .Ole => makeCmp .Cle a ta b tb
  | .Oge => makeCmp .Cge a ta b tb

/-! ## Translation of field accesses -/

/-- `Cshmgen.make_field_access` -/
def makeFieldAccess (ce : CompositeEnv) (ty : Ty) (f : Ident) (a : CExpr) :
    Res (CExpr × Bitfield) := do
  let (ofs, bf) ←
    match ty with
    | .Tstruct id _ =>
      match PTree.get id ce with
      | none => Res.Error "Undefined struct"
      | some co => fieldOffset ce f co.co_members
    | .Tunion id _ =>
      match PTree.get id ce with
      | none => Res.Error "Undefined union"
      | some co => unionFieldOffset ce f co.co_members
    | _ => Res.Error "Cshmgen.make_field_access"
  let a' :=
    if Archi.ptr64 then Csharpminor.Expr.Ebinop Oaddl a (makeLongconst (Integers.Int64.repr ofs))
    else Csharpminor.Expr.Ebinop Oadd a (makeIntconst (Integers.Int.repr ofs))
  .OK (a', bf)

/-! ## Translation of expressions -/

mutual
/-- `Cshmgen.transl_expr`: the Csharpminor code computing the value of a
    Clight expression. -/
def translExpr (ce : CompositeEnv) : Expr → Res CExpr
  | .Econst_int n _ => .OK (makeIntconst n)
  | .Econst_float n _ => .OK (makeFloatconst n)
  | .Econst_single n _ => .OK (makeSingleconst n)
  | .Econst_long n _ => .OK (makeLongconst n)
  | .Evar id ty => makeLoad (.Eaddrof id) ty .Full
  | .Etempvar id _ => .OK (.Evar id)
  | .Ederef b ty => do
    let tb ← translExpr ce b
    makeLoad tb ty .Full
  | .Eaddrof b _ => do
    let (tb, bf) ← translLvalue ce b
    match bf with
    | .Full => .OK tb
    | .Bits _ _ _ _ => .Error "Cshmgen.transl_expr: addrof bitfield"
  | .Eunop op b _ => do
    let tb ← translExpr ce b
    translUnop op tb (typeof b)
  | .Ebinop op b c _ => do
    let tb ← translExpr ce b
    let tc ← translExpr ce c
    translBinop ce op tb (typeof b) tc (typeof c)
  | .Ecast b ty => do
    let tb ← translExpr ce b
    makeCast (typeof b) ty tb
  | .Efield b i ty => do
    let tb ← translExpr ce b
    let (addr, bf) ← makeFieldAccess ce (typeof b) i tb
    makeLoad addr ty bf
  | .Esizeof ty' _ => do
    let sz ← sizeof ce ty'
    .OK (makePtrofsconst sz)
  | .Ealignof ty' _ => do
    let al ← alignof ce ty'
    .OK (makePtrofsconst al)

/-- `Cshmgen.transl_lvalue`: the Csharpminor code computing the address of
    a Clight l-value, and the bitfield accessed at that address. -/
def translLvalue (ce : CompositeEnv) : Expr → Res (CExpr × Bitfield)
  | .Evar id _ => .OK (.Eaddrof id, .Full)
  | .Ederef b _ => do
    let tb ← translExpr ce b
    .OK (tb, .Full)
  | .Efield b i _ => do
    let tb ← translExpr ce b
    makeFieldAccess ce (typeof b) i tb
  | _ => .Error "Cshmgen.transl_lvalue"
end

/-- `Ctypes.default_argument_conversion` -/
def defaultArgumentConversion (ty : Ty) : Ty :=
  match ty with
  | .Tint .I8 _ _ | .Tint .I16 _ _ | .Tint .IBool _ _ => .Tint .I32 .Signed noattr
  | .Tfloat _ _ => .Tfloat .F64 noattr
  | .Tarray t _ _ => .Tpointer t noattr
  | .Tfunction _ _ _ => .Tpointer ty noattr
  | _ => removeAttributes ty

/-- `Cshmgen.transl_arglist`: translate the arguments of a call, casting
    them to the parameter types. -/
def translArglist (ce : CompositeEnv) : List Expr → List Ty → Res (List CExpr)
  | [], [] => .OK []
  | a1 :: a2, ty1 :: ty2 => do
    let ta1 ← translExpr ce a1
    let ta1' ← makeCast (typeof a1) ty1 ta1
    let ta2 ← translArglist ce a2 ty2
    .OK (ta1' :: ta2)
  | a1 :: a2, [] => do
    let ta1 ← translExpr ce a1
    let ta1' ← makeCast (typeof a1) (defaultArgumentConversion (typeof a1)) ta1
    let ta2 ← translArglist ce a2 []
    .OK (ta1' :: ta2)
  | _, _ => .Error "Cshmgen.transl_arglist: arity mismatch"

/-- `Cshmgen.typlist_of_arglist` -/
def typlistOfArglist : List Expr → List Ty → List XType
  | [], _ => []
  | _ :: a2, ty1 :: ty2 => argtypeOfType ty1 :: typlistOfArglist a2 ty2
  | a1 :: a2, [] =>
    argtypeOfType (defaultArgumentConversion (typeof a1)) :: typlistOfArglist a2 []

/-- `Cshmgen.make_normalization` -/
def makeNormalization (t : Ty) (a : CExpr) : CExpr :=
  match t with
  | .Tint .IBool _ _ => .Eunop Ocast8unsigned a
  | .Tint .I8 .Signed _ => .Eunop Ocast8signed a
  | .Tint .I8 .Unsigned _ => .Eunop Ocast8unsigned a
  | .Tint .I16 .Signed _ => .Eunop Ocast16signed a
  | .Tint .I16 .Unsigned _ => .Eunop Ocast16unsigned a
  | _ => a

section ABI
variable (rvNorm : XType → Bool)

/-- `Cshmgen.make_funcall` -/
def makeFuncall (x : Option Ident) (tres : Ty) (sg : Signature) (fn : CExpr) (args : List CExpr) :
    CStmt :=
  match x, rvNorm sg.sig_res with
  | some id, true => .Sseq (.Scall x sg fn args) (.Sset id (makeNormalization tres (.Evar id)))
  | _, _ => .Scall x sg fn args

/-! ## Translation of statements -/

mutual
/-- `Cshmgen.transl_statement`: `break` becomes `exit nbrk` and `continue`
    becomes `exit ncnt`. -/
def translStatement (ce : CompositeEnv) (tyret : Ty) (nbrk ncnt : Nat) : Stmt → Res CStmt
  | .Sskip => .OK .Sskip
  | .Sassign b c => do
    let (tb, bf) ← translLvalue ce b
    let tc ← translExpr ce c
    let tc' ← makeCast (typeof c) (typeof b) tc
    makeStore ce tb (typeof b) bf tc'
  | .Sset x b => do
    let tb ← translExpr ce b
    .OK (.Sset x tb)
  | .Scall x b cl =>
    match Cop.classifyFun (typeof b) with
    | .f args res cconv => do
      let tb ← translExpr ce b
      let tcl ← translArglist ce cl args
      let sg : Signature :=
        { sig_args := typlistOfArglist cl args, sig_res := rettypeOfType res, sig_cc := cconv }
      .OK (makeFuncall rvNorm x res sg tb tcl)
    | _ => .Error "Cshmgen.transl_stmt(call)"
  | .Sbuiltin x ef tyargs bl => do
    let tbl ← translArglist ce bl tyargs
    .OK (.Sbuiltin x ef tbl)
  | .Ssequence s1 s2 => do
    let ts1 ← translStatement ce tyret nbrk ncnt s1
    let ts2 ← translStatement ce tyret nbrk ncnt s2
    .OK (.Sseq ts1 ts2)
  | .Sifthenelse e s1 s2 => do
    let te ← translExpr ce e
    let ts1 ← translStatement ce tyret nbrk ncnt s1
    let ts2 ← translStatement ce tyret nbrk ncnt s2
    .OK (.Sifthenelse (makeBoolean te (typeof e)) ts1 ts2)
  | .Sloop s1 s2 => do
    let ts1 ← translStatement ce tyret 1 0 s1
    let ts2 ← translStatement ce tyret 0 (ncnt + 1) s2
    .OK (.Sblock (.Sloop (.Sseq (.Sblock ts1) ts2)))
  | .Sbreak => .OK (.Sexit nbrk)
  | .Scontinue => .OK (.Sexit ncnt)
  | .Sreturn (some e) => do
    let te ← translExpr ce e
    let te' ← makeCast (typeof e) tyret te
    .OK (.Sreturn (some te'))
  | .Sreturn none => .OK (.Sreturn none)
  | .Sswitch a sl => do
    let ta ← translExpr ce a
    let tsl ← translLblStmt ce tyret 0 (ncnt + 1) sl
    match Cop.classifySwitch (typeof a) with
    | .i => .OK (.Sblock (.Sswitch false ta tsl))
    | .l => .OK (.Sblock (.Sswitch true ta tsl))
    | .default => .Error "Cshmgen.transl_stmt(switch)"
  | .Slabel lbl s => do
    let ts ← translStatement ce tyret nbrk ncnt s
    .OK (.Slabel lbl ts)
  | .Sgoto lbl => .OK (.Sgoto lbl)

/-- `Cshmgen.transl_lbl_stmt` -/
def translLblStmt (ce : CompositeEnv) (tyret : Ty) (nbrk ncnt : Nat) :
    LStmts → Res Csharpminor.LblStmt
  | .LSnil => .OK .LSnil
  | .LScons n s sl' => do
    let ts ← translStatement ce tyret nbrk ncnt s
    let tsl' ← translLblStmt ce tyret nbrk ncnt sl'
    .OK (.LScons n ts tsl')
end

end ABI

/-! ## Translation of functions and programs -/

/-- `Errors.mmap` -/
def mmap {A B : Type} (f : A → Res B) : List A → Res (List B)
  | [] => .OK []
  | x :: xs => do
    let y ← f x
    let ys ← mmap f xs
    .OK (y :: ys)

/-- `Cshmgen.transl_var` -/
def translVar (ce : CompositeEnv) (v : Ident × Ty) : Res (Ident × Z) := do
  let sz ← sizeof ce v.2
  .OK (v.1, sz)

/-- `Cshmgen.signature_of_function` -/
def signatureOfFunction (f : Function) : Signature :=
  { sig_args := (f.fn_params.map (·.2)).map argtypeOfType,
    sig_res := rettypeOfType f.fn_return,
    sig_cc := f.fn_callconv }

/-- `Cshmgen.transl_function` -/
def translFunction (rvNorm : XType → Bool) (ce : CompositeEnv) (f : Function) :
    Res Csharpminor.Function := do
  let tbody ← translStatement rvNorm ce f.fn_return 1 0 f.fn_body
  let tvars ← mmap (translVar ce) f.fn_vars
  .OK { fn_sig := signatureOfFunction f,
        fn_params := f.fn_params.map (·.1),
        fn_vars := tvars,
        fn_temps := f.fn_temps.map (·.1),
        fn_body := tbody }

/-- `Cshmgen.transl_fundef` -/
def translFundef (rvNorm : XType → Bool) (ce : CompositeEnv) (_id : Ident) :
    FunDef → Res Csharpminor.Fundef
  | .Internal g => do
    let tg ← translFunction rvNorm ce g
    .OK (.Internal tg)
  | .External ef args res cconv =>
    if ef.sig = signatureOfType args res cconv then .OK (.External ef)
    else .Error "Cshmgen.transl_fundef: wrong external signature"

/-- `Cshmgen.transl_globvar` -/
def translGlobvar (_id : Ident) (_ty : Ty) : Res Unit := .OK ()

/-- `Cshmgen.transl_program` -/
def translProgram (rvNorm : XType → Bool) (p : Program) : Res Csharpminor.Program :=
  transformPartialProgram2 (translFundef rvNorm p.prog_comp_env) translGlobvar
    { prog_defs := p.prog_defs, prog_public := p.prog_public, prog_main := p.prog_main }

end Cshmgen
end CC
