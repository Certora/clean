/-
  Operators and addressing modes of the aarch64 back end — port of
  `aarch64/Op.v` (syntax, `eval_condition`, `eval_operation`,
  `eval_addressing`, static typing, `negate_condition`, the stack-shifting
  functions, `offset_addressing`, `is_trivial_op`, the memory-dependence
  tests, `globals_operation`/`globals_addressing` and `builtin_arg_ok`).

  Differences from Rocq:
  * `amount32`/`amount64` are structures whose second field is the range
    proof, as in Rocq.
  * `Val.zero_ext`/`Val.sign_ext` take a `Nat` width in this port, so the
    `Z` widths of `Ozext`, `Osext`, … are converted with `Int.toNat`
    (only non-negative widths are ever generated).
-/
import CCLib.common.Globalenvs
import CCLib.common.ValuesOps
import CCLib.common.ASTTheory

namespace CC
namespace Op

/-- `Op.amount32`: a shift amount in `[0, 32)`. -/
structure Amount32 where
  a32_amount : Integers.Int
  a32_range : Integers.Int.ltu a32_amount Integers.Int.iwordsize = true
  deriving DecidableEq

/-- `Op.amount64`: a shift amount in `[0, 64)`. -/
structure Amount64 where
  a64_amount : Integers.Int
  a64_range : Integers.Int.ltu a64_amount Integers.Int64.iwordsize' = true
  deriving DecidableEq

instance : Coe Amount32 Integers.Int := ⟨Amount32.a32_amount⟩
instance : Coe Amount64 Integers.Int := ⟨Amount64.a64_amount⟩

/-- `Op.shift` -/
inductive Shift where
  | Slsl | Slsr | Sasr | Sror
  deriving DecidableEq, Repr

/-- `Op.extension` -/
inductive Extension where
  | Xsgn32 | Xuns32
  deriving DecidableEq, Repr

/-- `Op.condition` -/
inductive Condition where
  | Ccomp (c : Comparison)
  | Ccompu (c : Comparison)
  | Ccompimm (c : Comparison) (n : Integers.Int)
  | Ccompuimm (c : Comparison) (n : Integers.Int)
  | Ccompshift (c : Comparison) (s : Shift) (a : Amount32)
  | Ccompushift (c : Comparison) (s : Shift) (a : Amount32)
  | Cmaskzero (n : Integers.Int)
  | Cmasknotzero (n : Integers.Int)
  | Ccompl (c : Comparison)
  | Ccomplu (c : Comparison)
  | Ccomplimm (c : Comparison) (n : Integers.Int64)
  | Ccompluimm (c : Comparison) (n : Integers.Int64)
  | Ccomplshift (c : Comparison) (s : Shift) (a : Amount64)
  | Ccomplushift (c : Comparison) (s : Shift) (a : Amount64)
  | Cmasklzero (n : Integers.Int64)
  | Cmasklnotzero (n : Integers.Int64)
  | Ccompf (c : Comparison)
  | Cnotcompf (c : Comparison)
  | Ccompfzero (c : Comparison)
  | Cnotcompfzero (c : Comparison)
  | Ccompfs (c : Comparison)
  | Cnotcompfs (c : Comparison)
  | Ccompfszero (c : Comparison)
  | Cnotcompfszero (c : Comparison)
  deriving DecidableEq

/-- `Op.operation` -/
inductive Operation where
  | Omove
  | Ointconst (n : Integers.Int)
  | Olongconst (n : Integers.Int64)
  | Ofloatconst (n : Floats.Float)
  | Osingleconst (n : Floats.Float32)
  | Oaddrsymbol (id : Ident) (ofs : Integers.Ptrofs)
  | Oaddrstack (ofs : Integers.Ptrofs)
  | Oshift (s : Shift) (a : Amount32)
  | Oadd
  | Oaddshift (s : Shift) (a : Amount32)
  | Oaddimm (n : Integers.Int)
  | Oneg
  | Onegshift (s : Shift) (a : Amount32)
  | Osub
  | Osubshift (s : Shift) (a : Amount32)
  | Omul
  | Omuladd
  | Omulsub
  | Odiv
  | Odivu
  | Oand
  | Oandshift (s : Shift) (a : Amount32)
  | Oandimm (n : Integers.Int)
  | Oor
  | Oorshift (s : Shift) (a : Amount32)
  | Oorimm (n : Integers.Int)
  | Oxor
  | Oxorshift (s : Shift) (a : Amount32)
  | Oxorimm (n : Integers.Int)
  | Onot
  | Onotshift (s : Shift) (a : Amount32)
  | Obic
  | Obicshift (s : Shift) (a : Amount32)
  | Oorn
  | Oornshift (s : Shift) (a : Amount32)
  | Oeqv
  | Oeqvshift (s : Shift) (a : Amount32)
  | Oshl
  | Oshr
  | Oshru
  | Oshrximm (n : Integers.Int)
  | Ozext (s : Z)
  | Osext (s : Z)
  | Oshlzext (s : Z) (a : Amount32)
  | Oshlsext (s : Z) (a : Amount32)
  | Ozextshr (a : Amount32) (s : Z)
  | Osextshr (a : Amount32) (s : Z)
  | Oshiftl (s : Shift) (a : Amount64)
  | Oextend (x : Extension) (a : Amount64)
  | Omakelong
  | Olowlong
  | Ohighlong
  | Oaddl
  | Oaddlshift (s : Shift) (a : Amount64)
  | Oaddlext (x : Extension) (a : Amount64)
  | Oaddlimm (n : Integers.Int64)
  | Onegl
  | Oneglshift (s : Shift) (a : Amount64)
  | Osubl
  | Osublshift (s : Shift) (a : Amount64)
  | Osublext (x : Extension) (a : Amount64)
  | Omull
  | Omulladd
  | Omullsub
  | Omullhs
  | Omullhu
  | Odivl
  | Odivlu
  | Oandl
  | Oandlshift (s : Shift) (a : Amount64)
  | Oandlimm (n : Integers.Int64)
  | Oorl
  | Oorlshift (s : Shift) (a : Amount64)
  | Oorlimm (n : Integers.Int64)
  | Oxorl
  | Oxorlshift (s : Shift) (a : Amount64)
  | Oxorlimm (n : Integers.Int64)
  | Onotl
  | Onotlshift (s : Shift) (a : Amount64)
  | Obicl
  | Obiclshift (s : Shift) (a : Amount64)
  | Oornl
  | Oornlshift (s : Shift) (a : Amount64)
  | Oeqvl
  | Oeqvlshift (s : Shift) (a : Amount64)
  | Oshll
  | Oshrl
  | Oshrlu
  | Oshrlximm (n : Integers.Int)
  | Ozextl (s : Z)
  | Osextl (s : Z)
  | Oshllzext (s : Z) (a : Amount64)
  | Oshllsext (s : Z) (a : Amount64)
  | Ozextshrl (a : Amount64) (s : Z)
  | Osextshrl (a : Amount64) (s : Z)
  | Onegf
  | Oabsf
  | Oaddf
  | Osubf
  | Omulf
  | Odivf
  | Onegfs
  | Oabsfs
  | Oaddfs
  | Osubfs
  | Omulfs
  | Odivfs
  | Osingleoffloat
  | Ofloatofsingle
  | Ointoffloat
  | Ointuoffloat
  | Ofloatofint
  | Ofloatofintu
  | Ointofsingle
  | Ointuofsingle
  | Osingleofint
  | Osingleofintu
  | Olongoffloat
  | Olonguoffloat
  | Ofloatoflong
  | Ofloatoflongu
  | Olongofsingle
  | Olonguofsingle
  | Osingleoflong
  | Osingleoflongu
  | Ocmp (cond : Condition)
  | Osel (cond : Condition) (ty : ATyp)
  deriving DecidableEq

/-- `Op.addressing` -/
inductive Addressing where
  | Aindexed (ofs : Integers.Int64)
  | Aindexed2
  | Aindexed2shift (a : Amount64)
  | Aindexed2ext (x : Extension) (a : Amount64)
  | Aglobal (id : Ident) (ofs : Integers.Ptrofs)
  | Ainstack (ofs : Integers.Ptrofs)
  deriving DecidableEq

/-! ## Evaluation functions -/

/-- `Op.eval_shift` -/
def evalShift (s : Shift) (v : Val) (n : Amount32) : Val :=
  match s with
  | .Slsl => Val.shl v (.Vint n.a32_amount)
  | .Slsr => Val.shru v (.Vint n.a32_amount)
  | .Sasr => Val.shr v (.Vint n.a32_amount)
  | .Sror => Val.ror v (.Vint n.a32_amount)

/-- `Op.eval_shiftl` -/
def evalShiftl (s : Shift) (v : Val) (n : Amount64) : Val :=
  match s with
  | .Slsl => Val.shll v (.Vint n.a64_amount)
  | .Slsr => Val.shrlu v (.Vint n.a64_amount)
  | .Sasr => Val.shrl v (.Vint n.a64_amount)
  | .Sror => Val.rorl v (.Vint n.a64_amount)

/-- `Op.eval_extend` -/
def evalExtend (x : Extension) (v : Val) (n : Amount64) : Val :=
  Val.shll
    (match x with
     | .Xsgn32 => Val.longofint v
     | .Xuns32 => Val.longofintu v)
    (.Vint n.a64_amount)

/-- `Op.eval_condition` -/
def evalCondition (cond : Condition) (vl : List Val) (m : Mem) : Option Bool :=
  match cond, vl with
  | .Ccomp c, [v1, v2] => Val.cmp_bool c v1 v2
  | .Ccompu c, [v1, v2] => Val.cmpu_bool (Mem.validPointer m) c v1 v2
  | .Ccompimm c n, [v1] => Val.cmp_bool c v1 (.Vint n)
  | .Ccompuimm c n, [v1] => Val.cmpu_bool (Mem.validPointer m) c v1 (.Vint n)
  | .Ccompshift c s a, [v1, v2] => Val.cmp_bool c v1 (evalShift s v2 a)
  | .Ccompushift c s a, [v1, v2] => Val.cmpu_bool (Mem.validPointer m) c v1 (evalShift s v2 a)
  | .Cmaskzero n, [v1] => Val.cmp_bool .Ceq (Val.and v1 (.Vint n)) (.Vint Integers.Int.zero)
  | .Cmasknotzero n, [v1] => Val.cmp_bool .Cne (Val.and v1 (.Vint n)) (.Vint Integers.Int.zero)

  | .Ccompl c, [v1, v2] => Val.cmpl_bool c v1 v2
  | .Ccomplu c, [v1, v2] => Val.cmplu_bool (Mem.validPointer m) c v1 v2
  | .Ccomplimm c n, [v1] => Val.cmpl_bool c v1 (.Vlong n)
  | .Ccompluimm c n, [v1] => Val.cmplu_bool (Mem.validPointer m) c v1 (.Vlong n)
  | .Ccomplshift c s a, [v1, v2] => Val.cmpl_bool c v1 (evalShiftl s v2 a)
  | .Ccomplushift c s a, [v1, v2] => Val.cmplu_bool (Mem.validPointer m) c v1 (evalShiftl s v2 a)
  | .Cmasklzero n, [v1] => Val.cmpl_bool .Ceq (Val.andl v1 (.Vlong n)) (.Vlong Integers.Int64.zero)
  | .Cmasklnotzero n, [v1] => Val.cmpl_bool .Cne (Val.andl v1 (.Vlong n)) (.Vlong Integers.Int64.zero)

  | .Ccompf c, [v1, v2] => Val.cmpf_bool c v1 v2
  | .Cnotcompf c, [v1, v2] => Option.map not (Val.cmpf_bool c v1 v2)
  | .Ccompfzero c, [v1] => Val.cmpf_bool c v1 (.Vfloat Floats.Float.zero)
  | .Cnotcompfzero c, [v1] => Option.map not (Val.cmpf_bool c v1 (.Vfloat Floats.Float.zero))

  | .Ccompfs c, [v1, v2] => Val.cmpfs_bool c v1 v2
  | .Cnotcompfs c, [v1, v2] => Option.map not (Val.cmpfs_bool c v1 v2)
  | .Ccompfszero c, [v1] => Val.cmpfs_bool c v1 (.Vsingle Floats.Float32.zero)
  | .Cnotcompfszero c, [v1] => Option.map not (Val.cmpfs_bool c v1 (.Vsingle Floats.Float32.zero))

  | _, _ => none

/-- `Op.eval_operation` -/
def evalOperation {F V : Type} (genv : Genv F V) (sp : Val)
    (op : Operation) (vl : List Val) (m : Mem) : Option Val :=
  match op, vl with
  | .Omove, [v1] => some v1
  | .Ointconst n, [] => some (.Vint n)
  | .Olongconst n, [] => some (.Vlong n)
  | .Ofloatconst n, [] => some (.Vfloat n)
  | .Osingleconst n, [] => some (.Vsingle n)
  | .Oaddrsymbol s ofs, [] => some (Genv.symbolAddress genv s ofs)
  | .Oaddrstack ofs, [] => some (Val.offsetPtr sp ofs)

  | .Oshift s a, [v1] => some (evalShift s v1 a)
  | .Oadd, [v1, v2] => some (Val.add v1 v2)
  | .Oaddshift s a, [v1, v2] => some (Val.add v1 (evalShift s v2 a))
  | .Oaddimm n, [v1] => some (Val.add v1 (.Vint n))
  | .Oneg, [v1] => some (Val.neg v1)
  | .Onegshift s a, [v1] => some (Val.neg (evalShift s v1 a))
  | .Osub, [v1, v2] => some (Val.sub v1 v2)
  | .Osubshift s a, [v1, v2] => some (Val.sub v1 (evalShift s v2 a))
  | .Omul, [v1, v2] => some (Val.mul v1 v2)
  | .Omuladd, [v1, v2, v3] => some (Val.add v1 (Val.mul v2 v3))
  | .Omulsub, [v1, v2, v3] => some (Val.sub v1 (Val.mul v2 v3))
  | .Odiv, [v1, v2] => Val.divs v1 v2
  | .Odivu, [v1, v2] => Val.divu v1 v2
  | .Oand, [v1, v2] => some (Val.and v1 v2)
  | .Oandshift s a, [v1, v2] => some (Val.and v1 (evalShift s v2 a))
  | .Oandimm n, [v1] => some (Val.and v1 (.Vint n))
  | .Oor, [v1, v2] => some (Val.or v1 v2)
  | .Oorshift s a, [v1, v2] => some (Val.or v1 (evalShift s v2 a))
  | .Oorimm n, [v1] => some (Val.or v1 (.Vint n))
  | .Oxor, [v1, v2] => some (Val.xor v1 v2)
  | .Oxorshift s a, [v1, v2] => some (Val.xor v1 (evalShift s v2 a))
  | .Oxorimm n, [v1] => some (Val.xor v1 (.Vint n))
  | .Onot, [v1] => some (Val.notint v1)
  | .Onotshift s a, [v1] => some (Val.notint (evalShift s v1 a))
  | .Obic, [v1, v2] => some (Val.and v1 (Val.notint v2))
  | .Obicshift s a, [v1, v2] => some (Val.and v1 (Val.notint (evalShift s v2 a)))
  | .Oorn, [v1, v2] => some (Val.or v1 (Val.notint v2))
  | .Oornshift s a, [v1, v2] => some (Val.or v1 (Val.notint (evalShift s v2 a)))
  | .Oeqv, [v1, v2] => some (Val.xor v1 (Val.notint v2))
  | .Oeqvshift s a, [v1, v2] => some (Val.xor v1 (Val.notint (evalShift s v2 a)))
  | .Oshl, [v1, v2] => some (Val.shl v1 v2)
  | .Oshr, [v1, v2] => some (Val.shr v1 v2)
  | .Oshru, [v1, v2] => some (Val.shru v1 v2)
  | .Oshrximm n, [v1] => Val.shrx v1 (.Vint n)
  | .Ozext s, [v1] => some (Val.zeroExt s.toNat v1)
  | .Osext s, [v1] => some (Val.signExt s.toNat v1)
  | .Oshlzext s a, [v1] => some (Val.shl (Val.zeroExt s.toNat v1) (.Vint a))
  | .Oshlsext s a, [v1] => some (Val.shl (Val.signExt s.toNat v1) (.Vint a))
  | .Ozextshr a s, [v1] => some (Val.zeroExt s.toNat (Val.shru v1 (.Vint a)))
  | .Osextshr a s, [v1] => some (Val.signExt s.toNat (Val.shr v1 (.Vint a)))

  | .Oshiftl s a, [v1] => some (evalShiftl s v1 a)
  | .Oextend x a, [v1] => some (evalExtend x v1 a)
  | .Omakelong, [v1, v2] => some (Val.longofwords v1 v2)
  | .Olowlong, [v1] => some (Val.loword v1)
  | .Ohighlong, [v1] => some (Val.hiword v1)
  | .Oaddl, [v1, v2] => some (Val.addl v1 v2)
  | .Oaddlshift s a, [v1, v2] => some (Val.addl v1 (evalShiftl s v2 a))
  | .Oaddlext x a, [v1, v2] => some (Val.addl v1 (evalExtend x v2 a))
  | .Oaddlimm n, [v1] => some (Val.addl v1 (.Vlong n))
  | .Onegl, [v1] => some (Val.negl v1)
  | .Oneglshift s a, [v1] => some (Val.negl (evalShiftl s v1 a))
  | .Osubl, [v1, v2] => some (Val.subl v1 v2)
  | .Osublshift s a, [v1, v2] => some (Val.subl v1 (evalShiftl s v2 a))
  | .Osublext x a, [v1, v2] => some (Val.subl v1 (evalExtend x v2 a))
  | .Omull, [v1, v2] => some (Val.mull v1 v2)
  | .Omulladd, [v1, v2, v3] => some (Val.addl v1 (Val.mull v2 v3))
  | .Omullsub, [v1, v2, v3] => some (Val.subl v1 (Val.mull v2 v3))
  | .Omullhs, [v1, v2] => some (Val.mullhs v1 v2)
  | .Omullhu, [v1, v2] => some (Val.mullhu v1 v2)
  | .Odivl, [v1, v2] => Val.divls v1 v2
  | .Odivlu, [v1, v2] => Val.divlu v1 v2
  | .Oandl, [v1, v2] => some (Val.andl v1 v2)
  | .Oandlshift s a, [v1, v2] => some (Val.andl v1 (evalShiftl s v2 a))
  | .Oandlimm n, [v1] => some (Val.andl v1 (.Vlong n))
  | .Oorl, [v1, v2] => some (Val.orl v1 v2)
  | .Oorlshift s a, [v1, v2] => some (Val.orl v1 (evalShiftl s v2 a))
  | .Oorlimm n, [v1] => some (Val.orl v1 (.Vlong n))
  | .Oxorl, [v1, v2] => some (Val.xorl v1 v2)
  | .Oxorlshift s a, [v1, v2] => some (Val.xorl v1 (evalShiftl s v2 a))
  | .Oxorlimm n, [v1] => some (Val.xorl v1 (.Vlong n))
  | .Onotl, [v1] => some (Val.notl v1)
  | .Onotlshift s a, [v1] => some (Val.notl (evalShiftl s v1 a))
  | .Obicl, [v1, v2] => some (Val.andl v1 (Val.notl v2))
  | .Obiclshift s a, [v1, v2] => some (Val.andl v1 (Val.notl (evalShiftl s v2 a)))
  | .Oornl, [v1, v2] => some (Val.orl v1 (Val.notl v2))
  | .Oornlshift s a, [v1, v2] => some (Val.orl v1 (Val.notl (evalShiftl s v2 a)))
  | .Oeqvl, [v1, v2] => some (Val.xorl v1 (Val.notl v2))
  | .Oeqvlshift s a, [v1, v2] => some (Val.xorl v1 (Val.notl (evalShiftl s v2 a)))
  | .Oshll, [v1, v2] => some (Val.shll v1 v2)
  | .Oshrl, [v1, v2] => some (Val.shrl v1 v2)
  | .Oshrlu, [v1, v2] => some (Val.shrlu v1 v2)
  | .Oshrlximm n, [v1] => Val.shrxl v1 (.Vint n)
  | .Ozextl s, [v1] => some (Val.zero_ext_l s.toNat v1)
  | .Osextl s, [v1] => some (Val.sign_ext_l s.toNat v1)
  | .Oshllzext s a, [v1] => some (Val.shll (Val.zero_ext_l s.toNat v1) (.Vint a))
  | .Oshllsext s a, [v1] => some (Val.shll (Val.sign_ext_l s.toNat v1) (.Vint a))
  | .Ozextshrl a s, [v1] => some (Val.zero_ext_l s.toNat (Val.shrlu v1 (.Vint a)))
  | .Osextshrl a s, [v1] => some (Val.sign_ext_l s.toNat (Val.shrl v1 (.Vint a)))

  | .Onegf, [v1] => some (Val.negf v1)
  | .Oabsf, [v1] => some (Val.absf v1)
  | .Oaddf, [v1, v2] => some (Val.addf v1 v2)
  | .Osubf, [v1, v2] => some (Val.subf v1 v2)
  | .Omulf, [v1, v2] => some (Val.mulf v1 v2)
  | .Odivf, [v1, v2] => some (Val.divf v1 v2)

  | .Onegfs, [v1] => some (Val.negfs v1)
  | .Oabsfs, [v1] => some (Val.absfs v1)
  | .Oaddfs, [v1, v2] => some (Val.addfs v1 v2)
  | .Osubfs, [v1, v2] => some (Val.subfs v1 v2)
  | .Omulfs, [v1, v2] => some (Val.mulfs v1 v2)
  | .Odivfs, [v1, v2] => some (Val.divfs v1 v2)

  | .Osingleoffloat, [v1] => some (Val.singleoffloat v1)
  | .Ofloatofsingle, [v1] => some (Val.floatofsingle v1)
  | .Ointoffloat, [v1] => Val.intoffloat v1
  | .Ointuoffloat, [v1] => Val.intuoffloat v1
  | .Ofloatofint, [v1] => Val.floatofint v1
  | .Ofloatofintu, [v1] => Val.floatofintu v1
  | .Ointofsingle, [v1] => Val.intofsingle v1
  | .Ointuofsingle, [v1] => Val.intuofsingle v1
  | .Osingleofint, [v1] => Val.singleofint v1
  | .Osingleofintu, [v1] => Val.singleofintu v1
  | .Olongoffloat, [v1] => Val.longoffloat v1
  | .Olonguoffloat, [v1] => Val.longuoffloat v1
  | .Ofloatoflong, [v1] => Val.floatoflong v1
  | .Ofloatoflongu, [v1] => Val.floatoflongu v1
  | .Olongofsingle, [v1] => Val.longofsingle v1
  | .Olonguofsingle, [v1] => Val.longuofsingle v1
  | .Osingleoflong, [v1] => Val.singleoflong v1
  | .Osingleoflongu, [v1] => Val.singleoflongu v1

  | .Ocmp c, _ => some (Val.ofOptbool (evalCondition c vl m))
  | .Osel c ty, v1 :: v2 :: vl => some (Val.select (evalCondition c vl m) v1 v2 ty)
  | _, _ => none

/-- `Op.eval_addressing` -/
def evalAddressing {F V : Type} (genv : Genv F V) (sp : Val)
    (addr : Addressing) (vl : List Val) : Option Val :=
  match addr, vl with
  | .Aindexed n, [v1] => some (Val.addl v1 (.Vlong n))
  | .Aindexed2, [v1, v2] => some (Val.addl v1 v2)
  | .Aindexed2shift a, [v1, v2] => some (Val.addl v1 (Val.shll v2 (.Vint a)))
  | .Aindexed2ext x a, [v1, v2] => some (Val.addl v1 (evalExtend x v2 a))
  | .Aglobal s ofs, [] => some (Genv.symbolAddress genv s ofs)
  | .Ainstack n, [] => some (Val.offsetPtr sp n)
  | _, _ => none

/-! ## Static typing -/

/-- `Op.type_of_condition` -/
def typeOfCondition (c : Condition) : List ATyp :=
  match c with
  | .Ccomp _ => [.Tint, .Tint]
  | .Ccompu _ => [.Tint, .Tint]
  | .Ccompimm _ _ => [.Tint]
  | .Ccompuimm _ _ => [.Tint]
  | .Ccompshift _ _ _ => [.Tint, .Tint]
  | .Ccompushift _ _ _ => [.Tint, .Tint]
  | .Cmaskzero _ => [.Tint]
  | .Cmasknotzero _ => [.Tint]
  | .Ccompl _ => [.Tlong, .Tlong]
  | .Ccomplu _ => [.Tlong, .Tlong]
  | .Ccomplimm _ _ => [.Tlong]
  | .Ccompluimm _ _ => [.Tlong]
  | .Ccomplshift _ _ _ => [.Tlong, .Tlong]
  | .Ccomplushift _ _ _ => [.Tlong, .Tlong]
  | .Cmasklzero _ => [.Tlong]
  | .Cmasklnotzero _ => [.Tlong]
  | .Ccompf _ => [.Tfloat, .Tfloat]
  | .Cnotcompf _ => [.Tfloat, .Tfloat]
  | .Ccompfzero _ => [.Tfloat]
  | .Cnotcompfzero _ => [.Tfloat]
  | .Ccompfs _ => [.Tsingle, .Tsingle]
  | .Cnotcompfs _ => [.Tsingle, .Tsingle]
  | .Ccompfszero _ => [.Tsingle]
  | .Cnotcompfszero _ => [.Tsingle]

/-- `Op.type_of_operation` -/
def typeOfOperation (op : Operation) : List ATyp × ATyp :=
  match op with
  | .Omove => ([], .Tint)  -- treated specially
  | .Ointconst _ => ([], .Tint)
  | .Olongconst _ => ([], .Tlong)
  | .Ofloatconst _ => ([], .Tfloat)
  | .Osingleconst _ => ([], .Tsingle)
  | .Oaddrsymbol _ _ => ([], Tptr)
  | .Oaddrstack _ => ([], Tptr)

  | .Oshift _ _ => ([.Tint], .Tint)
  | .Oadd => ([.Tint, .Tint], .Tint)
  | .Oaddshift _ _ => ([.Tint, .Tint], .Tint)
  | .Oaddimm _ => ([.Tint], .Tint)
  | .Oneg => ([.Tint], .Tint)
  | .Onegshift _ _ => ([.Tint], .Tint)
  | .Osub => ([.Tint, .Tint], .Tint)
  | .Osubshift _ _ => ([.Tint, .Tint], .Tint)
  | .Omul => ([.Tint, .Tint], .Tint)
  | .Omuladd => ([.Tint, .Tint, .Tint], .Tint)
  | .Omulsub => ([.Tint, .Tint, .Tint], .Tint)
  | .Odiv => ([.Tint, .Tint], .Tint)
  | .Odivu => ([.Tint, .Tint], .Tint)
  | .Oand => ([.Tint, .Tint], .Tint)
  | .Oandshift _ _ => ([.Tint, .Tint], .Tint)
  | .Oandimm _ => ([.Tint], .Tint)
  | .Oor => ([.Tint, .Tint], .Tint)
  | .Oorshift _ _ => ([.Tint, .Tint], .Tint)
  | .Oorimm _ => ([.Tint], .Tint)
  | .Oxor => ([.Tint, .Tint], .Tint)
  | .Oxorshift _ _ => ([.Tint, .Tint], .Tint)
  | .Oxorimm _ => ([.Tint], .Tint)
  | .Onot => ([.Tint], .Tint)
  | .Onotshift _ _ => ([.Tint], .Tint)
  | .Obic => ([.Tint, .Tint], .Tint)
  | .Obicshift _ _ => ([.Tint, .Tint], .Tint)
  | .Oorn => ([.Tint, .Tint], .Tint)
  | .Oornshift _ _ => ([.Tint, .Tint], .Tint)
  | .Oeqv => ([.Tint, .Tint], .Tint)
  | .Oeqvshift _ _ => ([.Tint, .Tint], .Tint)
  | .Oshl => ([.Tint, .Tint], .Tint)
  | .Oshr => ([.Tint, .Tint], .Tint)
  | .Oshru => ([.Tint, .Tint], .Tint)
  | .Oshrximm _ => ([.Tint], .Tint)
  | .Ozext _ => ([.Tint], .Tint)
  | .Osext _ => ([.Tint], .Tint)
  | .Oshlzext _ _ => ([.Tint], .Tint)
  | .Oshlsext _ _ => ([.Tint], .Tint)
  | .Ozextshr _ _ => ([.Tint], .Tint)
  | .Osextshr _ _ => ([.Tint], .Tint)

  | .Oshiftl _ _ => ([.Tlong], .Tlong)
  | .Oextend _ _ => ([.Tint], .Tlong)
  | .Omakelong => ([.Tint, .Tint], .Tlong)
  | .Olowlong => ([.Tlong], .Tint)
  | .Ohighlong => ([.Tlong], .Tint)
  | .Oaddl => ([.Tlong, .Tlong], .Tlong)
  | .Oaddlshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Oaddlext _ _ => ([.Tlong, .Tint], .Tlong)
  | .Oaddlimm _ => ([.Tlong], .Tlong)
  | .Onegl => ([.Tlong], .Tlong)
  | .Oneglshift _ _ => ([.Tlong], .Tlong)
  | .Osubl => ([.Tlong, .Tlong], .Tlong)
  | .Osublshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Osublext _ _ => ([.Tlong, .Tint], .Tlong)
  | .Omull => ([.Tlong, .Tlong], .Tlong)
  | .Omulladd => ([.Tlong, .Tlong, .Tlong], .Tlong)
  | .Omullsub => ([.Tlong, .Tlong, .Tlong], .Tlong)
  | .Omullhs => ([.Tlong, .Tlong], .Tlong)
  | .Omullhu => ([.Tlong, .Tlong], .Tlong)
  | .Odivl => ([.Tlong, .Tlong], .Tlong)
  | .Odivlu => ([.Tlong, .Tlong], .Tlong)
  | .Oandl => ([.Tlong, .Tlong], .Tlong)
  | .Oandlshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Oandlimm _ => ([.Tlong], .Tlong)
  | .Oorl => ([.Tlong, .Tlong], .Tlong)
  | .Oorlshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Oorlimm _ => ([.Tlong], .Tlong)
  | .Oxorl => ([.Tlong, .Tlong], .Tlong)
  | .Oxorlshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Oxorlimm _ => ([.Tlong], .Tlong)
  | .Onotl => ([.Tlong], .Tlong)
  | .Onotlshift _ _ => ([.Tlong], .Tlong)
  | .Obicl => ([.Tlong, .Tlong], .Tlong)
  | .Obiclshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Oornl => ([.Tlong, .Tlong], .Tlong)
  | .Oornlshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Oeqvl => ([.Tlong, .Tlong], .Tlong)
  | .Oeqvlshift _ _ => ([.Tlong, .Tlong], .Tlong)
  | .Oshll => ([.Tlong, .Tint], .Tlong)
  | .Oshrl => ([.Tlong, .Tint], .Tlong)
  | .Oshrlu => ([.Tlong, .Tint], .Tlong)
  | .Oshrlximm _ => ([.Tlong], .Tlong)
  | .Ozextl _ => ([.Tlong], .Tlong)
  | .Osextl _ => ([.Tlong], .Tlong)
  | .Oshllzext _ _ => ([.Tlong], .Tlong)
  | .Oshllsext _ _ => ([.Tlong], .Tlong)
  | .Ozextshrl _ _ => ([.Tlong], .Tlong)
  | .Osextshrl _ _ => ([.Tlong], .Tlong)

  | .Onegf => ([.Tfloat], .Tfloat)
  | .Oabsf => ([.Tfloat], .Tfloat)
  | .Oaddf => ([.Tfloat, .Tfloat], .Tfloat)
  | .Osubf => ([.Tfloat, .Tfloat], .Tfloat)
  | .Omulf => ([.Tfloat, .Tfloat], .Tfloat)
  | .Odivf => ([.Tfloat, .Tfloat], .Tfloat)

  | .Onegfs => ([.Tsingle], .Tsingle)
  | .Oabsfs => ([.Tsingle], .Tsingle)
  | .Oaddfs => ([.Tsingle, .Tsingle], .Tsingle)
  | .Osubfs => ([.Tsingle, .Tsingle], .Tsingle)
  | .Omulfs => ([.Tsingle, .Tsingle], .Tsingle)
  | .Odivfs => ([.Tsingle, .Tsingle], .Tsingle)
  | .Osingleoffloat => ([.Tfloat], .Tsingle)
  | .Ofloatofsingle => ([.Tsingle], .Tfloat)

  | .Ointoffloat => ([.Tfloat], .Tint)
  | .Ointuoffloat => ([.Tfloat], .Tint)
  | .Ofloatofint => ([.Tint], .Tfloat)
  | .Ofloatofintu => ([.Tint], .Tfloat)
  | .Ointofsingle => ([.Tsingle], .Tint)
  | .Ointuofsingle => ([.Tsingle], .Tint)
  | .Osingleofint => ([.Tint], .Tsingle)
  | .Osingleofintu => ([.Tint], .Tsingle)
  | .Olongoffloat => ([.Tfloat], .Tlong)
  | .Olonguoffloat => ([.Tfloat], .Tlong)
  | .Ofloatoflong => ([.Tlong], .Tfloat)
  | .Ofloatoflongu => ([.Tlong], .Tfloat)
  | .Olongofsingle => ([.Tsingle], .Tlong)
  | .Olonguofsingle => ([.Tsingle], .Tlong)
  | .Osingleoflong => ([.Tlong], .Tsingle)
  | .Osingleoflongu => ([.Tlong], .Tsingle)

  | .Ocmp c => (typeOfCondition c, .Tint)
  | .Osel c ty => (ty :: ty :: typeOfCondition c, ty)

/-- `Op.type_of_addressing` -/
def typeOfAddressing (addr : Addressing) : List ATyp :=
  match addr with
  | .Aindexed _ => [Tptr]
  | .Aindexed2 => [Tptr, .Tlong]
  | .Aindexed2shift _ => [Tptr, .Tlong]
  | .Aindexed2ext _ _ => [Tptr, .Tint]
  | .Aglobal _ _ => []
  | .Ainstack _ => []

/-! ## Manipulating and transforming operations -/

/-- `Op.is_move_operation` -/
def isMoveOperation {A : Type} (op : Operation) (args : List A) : Option A :=
  match op, args with
  | .Omove, [arg] => some arg
  | _, _ => none

/-- `Op.negate_condition` -/
def negateCondition (cond : Condition) : Condition :=
  match cond with
  | .Ccomp c => .Ccomp (c.negate)
  | .Ccompu c => .Ccompu (c.negate)
  | .Ccompimm c n => .Ccompimm (c.negate) n
  | .Ccompuimm c n => .Ccompuimm (c.negate) n
  | .Ccompshift c s a => .Ccompshift (c.negate) s a
  | .Ccompushift c s a => .Ccompushift (c.negate) s a
  | .Cmaskzero n => .Cmasknotzero n
  | .Cmasknotzero n => .Cmaskzero n
  | .Ccompl c => .Ccompl (c.negate)
  | .Ccomplu c => .Ccomplu (c.negate)
  | .Ccomplimm c n => .Ccomplimm (c.negate) n
  | .Ccompluimm c n => .Ccompluimm (c.negate) n
  | .Ccomplshift c s a => .Ccomplshift (c.negate) s a
  | .Ccomplushift c s a => .Ccomplushift (c.negate) s a
  | .Cmasklzero n => .Cmasklnotzero n
  | .Cmasklnotzero n => .Cmasklzero n
  | .Ccompf c => .Cnotcompf c
  | .Cnotcompf c => .Ccompf c
  | .Ccompfzero c => .Cnotcompfzero c
  | .Cnotcompfzero c => .Ccompfzero c
  | .Ccompfs c => .Cnotcompfs c
  | .Cnotcompfs c => .Ccompfs c
  | .Ccompfszero c => .Cnotcompfszero c
  | .Cnotcompfszero c => .Ccompfszero c

/-- `Op.shift_stack_addressing` -/
def shiftStackAddressing (delta : Z) (addr : Addressing) : Addressing :=
  match addr with
  | .Ainstack ofs => .Ainstack (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta))
  | _ => addr

/-- `Op.shift_stack_operation` -/
def shiftStackOperation (delta : Z) (op : Operation) : Operation :=
  match op with
  | .Oaddrstack ofs => .Oaddrstack (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta))
  | _ => op

/-- `Op.offset_addressing` -/
def offsetAddressing (addr : Addressing) (delta : Z) : Option Addressing :=
  match addr with
  | .Aindexed n => some (.Aindexed (Integers.Int64.add n (Integers.Int64.repr delta)))
  | .Aindexed2 => none
  | .Aindexed2shift _ => none
  | .Aindexed2ext _ _ => none
  | .Aglobal id n => some (.Aglobal id (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta)))
  | .Ainstack n => some (.Ainstack (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta)))

/-- `Op.is_trivial_op` -/
def isTrivialOp (op : Operation) : Bool :=
  match op with
  | .Omove => true
  | .Ointconst n => Integers.Int.eq (Integers.Int.sign_ext 16 n) n
  | .Olongconst n => Integers.Int64.eq (Integers.Int64.sign_ext 16 n) n
  | .Oaddrstack _ => true
  | _ => false

/-- `Op.cond_depends_on_memory` -/
def condDependsOnMemory (c : Condition) : Bool :=
  match c with
  | .Ccomplu _ | .Ccompluimm _ _ | .Ccomplushift _ _ _ => true
  | _ => false

/-- `Op.op_depends_on_memory` -/
def opDependsOnMemory (op : Operation) : Bool :=
  match op with
  | .Ocmp c => condDependsOnMemory c
  | .Osel c _ => condDependsOnMemory c
  | _ => false

/-- `Op.globals_addressing` -/
def globalsAddressing (addr : Addressing) : List Ident :=
  match addr with
  | .Aglobal s _ => [s]
  | _ => []

/-- `Op.globals_operation` -/
def globalsOperation (op : Operation) : List Ident :=
  match op with
  | .Oaddrsymbol s _ => [s]
  | _ => []

/-- `Op.builtin_arg_ok_1` -/
def builtinArgOk1 {A : Type} (ba : BuiltinArg A) (c : BuiltinArgConstraint) : Bool :=
  match c, ba with
  | .OK_all, _ => true
  | .OK_const, .BA_int _ | .OK_const, .BA_long _
  | .OK_const, .BA_float _ | .OK_const, .BA_single _ => true
  | .OK_addrstack, .BA_addrstack _ => true
  | .OK_addressing, .BA_addrstack _ => true
  | .OK_addressing, .BA_addptr (.BA _) (.BA_int _) => true
  | .OK_addressing, .BA_addptr (.BA _) (.BA_long _) => true
  | _, _ => false

/-- `Op.builtin_arg_ok` -/
def builtinArgOk {A : Type} (ba : BuiltinArg A) (c : BuiltinArgConstraint) : Bool :=
  match ba with
  | .BA _ | .BA_splitlong (.BA _) (.BA _) => true
  | _ => builtinArgOk1 ba c

/-- `Op.eval_negate_condition` -/
theorem eval_negateCondition (cond : Condition) (vl : List Val) (m : Mem) :
    evalCondition (negateCondition cond) vl m = (evalCondition cond vl m).map (!·) := by
  cases cond <;> rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp only [negateCondition, evalCondition, Option.map_none, Option.map_map] <;>
    first
    | rfl
    | exact Val.negate_cmp_bool _ _ _
    | exact Val.negate_cmpu_bool _ _ _ _
    | exact Val.negate_cmpl_bool _ _ _
    | exact Val.negate_cmplu_bool _ _ _ _
    | (rw [← Val.negate_cmp_bool]; rfl)
    | (rw [← Val.negate_cmpl_bool]; rfl)
    | (cases Val.cmpf_bool _ _ _ <;> simp)
    | (cases Val.cmpfs_bool _ _ _ <;> simp)

end Op
end CC
