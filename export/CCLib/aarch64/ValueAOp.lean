/-
  Value analysis for AArch64 operators — port of `aarch64/ValueAOp.v`
  (definitions).

  Ported: `eval_static_shift`, `eval_static_shiftl`, `eval_static_extend`,
  `eval_static_condition`, `eval_static_addressing`,
  `eval_static_operation`.
  Not ported: the soundness lemmas (`eval_static_condition_sound`,
  `eval_static_addressing_sound`, `eval_static_operation_sound`).

  Differences from Rocq: the OCaml parameters `Compopts.va_strict` and
  `Compopts.propagate_float_constants` are the fields of an explicit
  `ValueAOp.Options` argument.
-/
import CCLib.backend.ValueDomain
import CCLib.aarch64.Op

namespace CC
namespace ValueAOp

open ValueDomain

/-- The compiler options used by the value analysis. -/
structure Options where
  /-- `Compopts.va_strict` -/
  strict : Bool := false
  /-- `Compopts.propagate_float_constants` -/
  propagateFloatConstants : Bool := true

/-- `ValueAOp.eval_static_shift` -/
def evalStaticShift (s : Op.Shift) (v : Aval) (n : Op.Amount32) : Aval :=
  match s with
  | .Slsl => shl v (.I n.a32_amount)
  | .Slsr => shru v (.I n.a32_amount)
  | .Sasr => shr v (.I n.a32_amount)
  | .Sror => ror v (.I n.a32_amount)

/-- `ValueAOp.eval_static_shiftl` -/
def evalStaticShiftl (s : Op.Shift) (v : Aval) (n : Op.Amount64) : Aval :=
  match s with
  | .Slsl => shll v (.I n.a64_amount)
  | .Slsr => shrlu v (.I n.a64_amount)
  | .Sasr => shrl v (.I n.a64_amount)
  | .Sror => rorl v (.I n.a64_amount)

/-- `ValueAOp.eval_static_extend` -/
def evalStaticExtend (x : Op.Extension) (v : Aval) (n : Op.Amount64) : Aval :=
  shll (match x with | .Xsgn32 => longofint v | .Xuns32 => longofintu v) (.I n.a64_amount)

section
variable (o : Options)

/-- `ValueAOp.eval_static_condition` -/
def evalStaticCondition (cond : Op.Condition) (vl : List Aval) : Abool :=
  match cond, vl with
  | .Ccomp c, [v1, v2] => cmpBool c v1 v2
  | .Ccompu c, [v1, v2] => cmpuBool o.strict c v1 v2
  | .Ccompimm c n, [v1] => cmpBool c v1 (.I n)
  | .Ccompuimm c n, [v1] => cmpuBool o.strict c v1 (.I n)
  | .Ccompshift c s a, [v1, v2] => cmpBool c v1 (evalStaticShift s v2 a)
  | .Ccompushift c s a, [v1, v2] => cmpuBool o.strict c v1 (evalStaticShift s v2 a)
  | .Cmaskzero m, [v1] => maskzero v1 m
  | .Cmasknotzero m, [v1] => cnot (maskzero v1 m)
  | .Ccompl c, [v1, v2] => cmplBool c v1 v2
  | .Ccomplu c, [v1, v2] => cmpluBool o.strict c v1 v2
  | .Ccomplimm c n, [v1] => cmplBool c v1 (.L n)
  | .Ccompluimm c n, [v1] => cmpluBool o.strict c v1 (.L n)
  | .Ccomplshift c s a, [v1, v2] => cmplBool c v1 (evalStaticShiftl s v2 a)
  | .Ccomplushift c s a, [v1, v2] => cmpluBool o.strict c v1 (evalStaticShiftl s v2 a)
  | .Cmasklzero m, [v1] => cmplBool .Ceq (andl v1 (.L m)) (.L Integers.Int64.zero)
  | .Cmasklnotzero m, [v1] => cmplBool .Cne (andl v1 (.L m)) (.L Integers.Int64.zero)
  | .Ccompf c, [v1, v2] => cmpfBool c v1 v2
  | .Cnotcompf c, [v1, v2] => cnot (cmpfBool c v1 v2)
  | .Ccompfzero c, [v1] => cmpfBool c v1 (.F Floats.Float.zero)
  | .Cnotcompfzero c, [v1] => cnot (cmpfBool c v1 (.F Floats.Float.zero))
  | .Ccompfs c, [v1, v2] => cmpfsBool c v1 v2
  | .Cnotcompfs c, [v1, v2] => cnot (cmpfsBool c v1 v2)
  | .Ccompfszero c, [v1] => cmpfsBool c v1 (.FS Floats.Float32.zero)
  | .Cnotcompfszero c, [v1] => cnot (cmpfsBool c v1 (.FS Floats.Float32.zero))
  | _, _ => .Bnone

end

/-- `ValueAOp.eval_static_addressing` -/
def evalStaticAddressing (addr : Op.Addressing) (vl : List Aval) : Aval :=
  match addr, vl with
  | .Aindexed n, [v1] => addl v1 (.L n)
  | .Aindexed2, [v1, v2] => addl v1 v2
  | .Aindexed2shift a, [v1, v2] => addl v1 (shll v2 (.I a.a64_amount))
  | .Aindexed2ext x a, [v1, v2] => addl v1 (evalStaticExtend x v2 a)
  | .Aglobal s ofs, [] => .Ptr (.Gl s ofs)
  | .Ainstack ofs, [] => .Ptr (.Stk ofs)
  | _, _ => .Vbot

section
variable (o : Options)

/-- `ValueAOp.eval_static_operation` -/
def evalStaticOperation (op : Op.Operation) (vl : List Aval) : Aval :=
  match op, vl with
  | .Omove, [v1] => v1
  | .Ointconst n, [] => .I n
  | .Olongconst n, [] => .L n
  | .Ofloatconst n, [] => if o.propagateFloatConstants then .F n else ntop
  | .Osingleconst n, [] => if o.propagateFloatConstants then .FS n else ntop
  | .Oaddrsymbol id ofs, [] => .Ptr (.Gl id ofs)
  | .Oaddrstack ofs, [] => .Ptr (.Stk ofs)
  | .Oshift s a, [v1] => evalStaticShift s v1 a
  | .Oadd, [v1, v2] => add v1 v2
  | .Oaddshift s a, [v1, v2] => add v1 (evalStaticShift s v2 a)
  | .Oaddimm n, [v1] => add v1 (.I n)
  | .Oneg, [v1] => neg v1
  | .Onegshift s a, [v1] => neg (evalStaticShift s v1 a)
  | .Osub, [v1, v2] => sub v1 v2
  | .Osubshift s a, [v1, v2] => sub v1 (evalStaticShift s v2 a)
  | .Omul, [v1, v2] => mul v1 v2
  | .Omuladd, [v1, v2, v3] => add v1 (mul v2 v3)
  | .Omulsub, [v1, v2, v3] => sub v1 (mul v2 v3)
  | .Odiv, [v1, v2] => divs o.strict v1 v2
  | .Odivu, [v1, v2] => divu o.strict v1 v2
  | .Oand, [v1, v2] => and v1 v2
  | .Oandshift s a, [v1, v2] => and v1 (evalStaticShift s v2 a)
  | .Oandimm n, [v1] => and v1 (.I n)
  | .Oor, [v1, v2] => or v1 v2
  | .Oorshift s a, [v1, v2] => or v1 (evalStaticShift s v2 a)
  | .Oorimm n, [v1] => or v1 (.I n)
  | .Oxor, [v1, v2] => xor v1 v2
  | .Oxorshift s a, [v1, v2] => xor v1 (evalStaticShift s v2 a)
  | .Oxorimm n, [v1] => xor v1 (.I n)
  | .Onot, [v1] => notint v1
  | .Onotshift s a, [v1] => notint (evalStaticShift s v1 a)
  | .Obic, [v1, v2] => and v1 (notint v2)
  | .Obicshift s a, [v1, v2] => and v1 (notint (evalStaticShift s v2 a))
  | .Oorn, [v1, v2] => or v1 (notint v2)
  | .Oornshift s a, [v1, v2] => or v1 (notint (evalStaticShift s v2 a))
  | .Oeqv, [v1, v2] => xor v1 (notint v2)
  | .Oeqvshift s a, [v1, v2] => xor v1 (notint (evalStaticShift s v2 a))
  | .Oshl, [v1, v2] => shl v1 v2
  | .Oshr, [v1, v2] => shr v1 v2
  | .Oshru, [v1, v2] => shru v1 v2
  | .Oshrximm n, [v1] => shrx v1 (.I n)
  | .Ozext s, [v1] => zeroExt s v1
  | .Osext s, [v1] => signExt s v1
  | .Oshlzext s a, [v1] => shl (zeroExt s v1) (.I a.a32_amount)
  | .Oshlsext s a, [v1] => shl (signExt s v1) (.I a.a32_amount)
  | .Ozextshr a s, [v1] => zeroExt s (shru v1 (.I a.a32_amount))
  | .Osextshr a s, [v1] => signExt s (shr v1 (.I a.a32_amount))
  | .Oshiftl s a, [v1] => evalStaticShiftl s v1 a
  | .Oextend x a, [v1] => evalStaticExtend x v1 a
  | .Omakelong, [v1, v2] => longofwords v1 v2
  | .Olowlong, [v1] => loword v1
  | .Ohighlong, [v1] => hiword v1
  | .Oaddl, [v1, v2] => addl v1 v2
  | .Oaddlshift s a, [v1, v2] => addl v1 (evalStaticShiftl s v2 a)
  | .Oaddlext x a, [v1, v2] => addl v1 (evalStaticExtend x v2 a)
  | .Oaddlimm n, [v1] => addl v1 (.L n)
  | .Onegl, [v1] => negl v1
  | .Oneglshift s a, [v1] => negl (evalStaticShiftl s v1 a)
  | .Osubl, [v1, v2] => subl v1 v2
  | .Osublshift s a, [v1, v2] => subl v1 (evalStaticShiftl s v2 a)
  | .Osublext x a, [v1, v2] => subl v1 (evalStaticExtend x v2 a)
  | .Omull, [v1, v2] => mull v1 v2
  | .Omulladd, [v1, v2, v3] => addl v1 (mull v2 v3)
  | .Omullsub, [v1, v2, v3] => subl v1 (mull v2 v3)
  | .Omullhs, [v1, v2] => mullhs v1 v2
  | .Omullhu, [v1, v2] => mullhu v1 v2
  | .Odivl, [v1, v2] => divls o.strict v1 v2
  | .Odivlu, [v1, v2] => divlu o.strict v1 v2
  | .Oandl, [v1, v2] => andl v1 v2
  | .Oandlshift s a, [v1, v2] => andl v1 (evalStaticShiftl s v2 a)
  | .Oandlimm n, [v1] => andl v1 (.L n)
  | .Oorl, [v1, v2] => orl v1 v2
  | .Oorlshift s a, [v1, v2] => orl v1 (evalStaticShiftl s v2 a)
  | .Oorlimm n, [v1] => orl v1 (.L n)
  | .Oxorl, [v1, v2] => xorl v1 v2
  | .Oxorlshift s a, [v1, v2] => xorl v1 (evalStaticShiftl s v2 a)
  | .Oxorlimm n, [v1] => xorl v1 (.L n)
  | .Onotl, [v1] => notl v1
  | .Onotlshift s a, [v1] => notl (evalStaticShiftl s v1 a)
  | .Obicl, [v1, v2] => andl v1 (notl v2)
  | .Obiclshift s a, [v1, v2] => andl v1 (notl (evalStaticShiftl s v2 a))
  | .Oornl, [v1, v2] => orl v1 (notl v2)
  | .Oornlshift s a, [v1, v2] => orl v1 (notl (evalStaticShiftl s v2 a))
  | .Oeqvl, [v1, v2] => xorl v1 (notl v2)
  | .Oeqvlshift s a, [v1, v2] => xorl v1 (notl (evalStaticShiftl s v2 a))
  | .Oshll, [v1, v2] => shll v1 v2
  | .Oshrl, [v1, v2] => shrl v1 v2
  | .Oshrlu, [v1, v2] => shrlu v1 v2
  | .Oshrlximm n, [v1] => shrxl v1 (.I n)
  | .Ozextl s, [v1] => zeroExtL s v1
  | .Osextl s, [v1] => signExtL s v1
  | .Oshllzext s a, [v1] => shll (zeroExtL s v1) (.I a.a64_amount)
  | .Oshllsext s a, [v1] => shll (signExtL s v1) (.I a.a64_amount)
  | .Ozextshrl a s, [v1] => zeroExtL s (shrlu v1 (.I a.a64_amount))
  | .Osextshrl a s, [v1] => signExtL s (shrl v1 (.I a.a64_amount))
  | .Onegf, [v1] => negf v1
  | .Oabsf, [v1] => absf v1
  | .Oaddf, [v1, v2] => addf v1 v2
  | .Osubf, [v1, v2] => subf v1 v2
  | .Omulf, [v1, v2] => mulf v1 v2
  | .Odivf, [v1, v2] => divf v1 v2
  | .Onegfs, [v1] => negfs v1
  | .Oabsfs, [v1] => absfs v1
  | .Oaddfs, [v1, v2] => addfs v1 v2
  | .Osubfs, [v1, v2] => subfs v1 v2
  | .Omulfs, [v1, v2] => mulfs v1 v2
  | .Odivfs, [v1, v2] => divfs v1 v2
  | .Osingleoffloat, [v1] => singleoffloat v1
  | .Ofloatofsingle, [v1] => floatofsingle v1
  | .Ointoffloat, [v1] => intoffloat o.strict v1
  | .Ointuoffloat, [v1] => intuoffloat o.strict v1
  | .Ofloatofint, [v1] => floatofint v1
  | .Ofloatofintu, [v1] => floatofintu v1
  | .Ointofsingle, [v1] => intofsingle o.strict v1
  | .Ointuofsingle, [v1] => intuofsingle o.strict v1
  | .Osingleofint, [v1] => singleofint v1
  | .Osingleofintu, [v1] => singleofintu v1
  | .Olongoffloat, [v1] => longoffloat o.strict v1
  | .Olonguoffloat, [v1] => longuoffloat o.strict v1
  | .Ofloatoflong, [v1] => floatoflong v1
  | .Ofloatoflongu, [v1] => floatoflongu v1
  | .Olongofsingle, [v1] => longofsingle o.strict v1
  | .Olonguofsingle, [v1] => longuofsingle o.strict v1
  | .Osingleoflong, [v1] => singleoflong v1
  | .Osingleoflongu, [v1] => singleoflongu v1
  | .Ocmp c, _ => ofOptbool (evalStaticCondition o c vl)
  | .Osel c ty, v1 :: v2 :: vl => select o.strict (evalStaticCondition o c vl) v1 v2 ty
  | _, _ => .Vbot

end

end ValueAOp
end CC
