/-
  Operators and addressing modes of the x86 back end — port of `x86/Op.v`
  (syntax, `eval_condition`, `eval_addressing32/64`, `eval_operation`,
  static typing, `negate_condition`, the stack-shifting functions,
  `offset_addressing`, `addressing_valid`, `is_trivial_op`, the
  memory-dependence tests, `globals_operation`/`globals_addressing` and
  `builtin_arg_ok`), with the target-independent lemmas about them.

  As in Rocq, the 32- and 64-bit variants are selected by `Archi.ptr64`.
  The port's `Archi.ptr64` is `true` (see `CCLib/targets/Archi.lean`), so
  this is the x86-64 configuration; the `ptr64 = false` branches are kept
  for fidelity but are dead code here.

  Differences from Rocq: `Val.zero_ext`/`Val.sign_ext` take a `Nat` width.
-/
import CCLib.common.Globalenvs
import CCLib.common.ValuesOps
import CCLib.common.ASTTheory

namespace CC
namespace X86
namespace Op


/-- `Op.condition` (x86) -/
inductive Condition where
  | Ccomp (c : Comparison)
  | Ccompu (c : Comparison)
  | Ccompimm (c : Comparison) (n : Integers.Int)
  | Ccompuimm (c : Comparison) (n : Integers.Int)
  | Ccompl (c : Comparison)
  | Ccomplu (c : Comparison)
  | Ccomplimm (c : Comparison) (n : Integers.Int64)
  | Ccompluimm (c : Comparison) (n : Integers.Int64)
  | Ccompf (c : Comparison)
  | Cnotcompf (c : Comparison)
  | Ccompfs (c : Comparison)
  | Cnotcompfs (c : Comparison)
  | Cmaskzero (n : Integers.Int)
  | Cmasknotzero (n : Integers.Int)
  deriving DecidableEq

/-- `Op.addressing` (x86) -/
inductive Addressing where
  /-- `r1 + offset` -/
  | Aindexed (ofs : Z)
  /-- `r1 + r2 + offset` -/
  | Aindexed2 (ofs : Z)
  /-- `r1 * scale + offset` -/
  | Ascaled (sc : Z) (ofs : Z)
  /-- `r1 + r2 * scale + offset` -/
  | Aindexed2scaled (sc : Z) (ofs : Z)
  /-- `symbol + offset` -/
  | Aglobal (id : Ident) (ofs : Integers.Ptrofs)
  /-- `symbol + offset + r1` -/
  | Abased (id : Ident) (ofs : Integers.Ptrofs)
  /-- `symbol + offset + r1 * scale` -/
  | Abasedscaled (sc : Z) (id : Ident) (ofs : Integers.Ptrofs)
  /-- `stack_pointer + offset` -/
  | Ainstack (ofs : Integers.Ptrofs)
  deriving DecidableEq

/-- `Op.operation` (x86) -/
inductive Operation where
  | Omove
  | Ointconst (n : Integers.Int)
  | Olongconst (n : Integers.Int64)
  | Ofloatconst (n : Floats.Float)
  | Osingleconst (n : Floats.Float32)
  | Oindirectsymbol (id : Ident)
  | Ocast8signed
  | Ocast8unsigned
  | Ocast16signed
  | Ocast16unsigned
  | Oneg
  | Osub
  | Omul
  | Omulimm (n : Integers.Int)
  | Omulhs
  | Omulhu
  | Odiv
  | Odivu
  | Omod
  | Omodu
  | Oand
  | Oandimm (n : Integers.Int)
  | Oor
  | Oorimm (n : Integers.Int)
  | Oxor
  | Oxorimm (n : Integers.Int)
  | Onot
  | Oshl
  | Oshlimm (n : Integers.Int)
  | Oshr
  | Oshrimm (n : Integers.Int)
  | Oshrximm (n : Integers.Int)
  | Oshru
  | Oshruimm (n : Integers.Int)
  | Ororimm (n : Integers.Int)
  | Oshldimm (n : Integers.Int)
  | Olea (a : Addressing)
  | Omakelong
  | Olowlong
  | Ohighlong
  | Ocast32signed
  | Ocast32unsigned
  | Onegl
  | Oaddlimm (n : Integers.Int64)
  | Osubl
  | Omull
  | Omullimm (n : Integers.Int64)
  | Omullhs
  | Omullhu
  | Odivl
  | Odivlu
  | Omodl
  | Omodlu
  | Oandl
  | Oandlimm (n : Integers.Int64)
  | Oorl
  | Oorlimm (n : Integers.Int64)
  | Oxorl
  | Oxorlimm (n : Integers.Int64)
  | Onotl
  | Oshll
  | Oshllimm (n : Integers.Int)
  | Oshrl
  | Oshrlimm (n : Integers.Int)
  | Oshrxlimm (n : Integers.Int)
  | Oshrlu
  | Oshrluimm (n : Integers.Int)
  | Ororlimm (n : Integers.Int)
  | Oleal (a : Addressing)
  | Onegf
  | Oabsf
  | Oaddf
  | Osubf
  | Omulf
  | Odivf
  | Omaxf
  | Ominf
  | Onegfs
  | Oabsfs
  | Oaddfs
  | Osubfs
  | Omulfs
  | Odivfs
  | Osingleoffloat
  | Ofloatofsingle
  | Ointoffloat
  | Ofloatofint
  | Ointofsingle
  | Osingleofint
  | Olongoffloat
  | Ofloatoflong
  | Olongofsingle
  | Osingleoflong
  | Ocmp (cond : Condition)
  | Osel (cond : Condition) (ty : ATyp)
  deriving DecidableEq

/-! ## Floating-point maximum and minimum -/

/-- `Op.float_max` -/
def floatMax (f1 f2 : Floats.Float) : Floats.Float :=
  match Floats.Float.compare f1 f2 with
  | some .gt => f1
  | _ => f2

/-- `Op.maxf` -/
def maxf (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (floatMax f1 f2)
  | _, _ => .Vundef

/-- `Op.float_min` -/
def floatMin (f1 f2 : Floats.Float) : Floats.Float :=
  match Floats.Float.compare f1 f2 with
  | some .lt => f1
  | _ => f2

/-- `Op.minf` -/
def minf (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (floatMin f1 f2)
  | _, _ => .Vundef

/-! ## Valid addressing modes -/

/-- `Op.offset_in_range`: fits in a signed 32-bit displacement. -/
def offsetInRange (n : Z) : Bool :=
  decide (Integers.Int.min_signed ≤ n) && decide (n ≤ Integers.Int.max_signed)

/-- `Op.ptroffset_min` = `-2^24` -/
def ptroffsetMin : Z := -16777216
/-- `Op.ptroffset_max` = `2^24 - 1` -/
def ptroffsetMax : Z := 16777215

/-- `Op.ptroffset_in_range` (small code model, RIP-relative addressing) -/
def ptroffsetInRange (n : Integers.Ptrofs) : Bool :=
  let n := Integers.Ptrofs.signed n
  decide (ptroffsetMin ≤ n) && decide (n ≤ ptroffsetMax)

/-- `Op.addressing_valid` -/
def addressingValid (a : Addressing) : Bool :=
  if Archi.ptr64 then
    match a with
    | .Aindexed n => offsetInRange n
    | .Aindexed2 n => offsetInRange n
    | .Ascaled _ ofs => offsetInRange ofs
    | .Aindexed2scaled _ ofs => offsetInRange ofs
    | .Aglobal _ ofs => ptroffsetInRange ofs
    | .Abased _ ofs => ptroffsetInRange ofs
    | .Abasedscaled _ _ ofs => ptroffsetInRange ofs
    | .Ainstack ofs => offsetInRange (Integers.Ptrofs.signed ofs)
  else true

/-! ## Evaluation functions -/

/-- `Op.eval_condition` -/
def evalCondition (cond : Condition) (vl : List Val) (m : Mem) : Option Bool :=
  match cond, vl with
  | .Ccomp c, [v1, v2] => Val.cmp_bool c v1 v2
  | .Ccompu c, [v1, v2] => Val.cmpu_bool (Mem.validPointer m) c v1 v2
  | .Ccompimm c n, [v1] => Val.cmp_bool c v1 (.Vint n)
  | .Ccompuimm c n, [v1] => Val.cmpu_bool (Mem.validPointer m) c v1 (.Vint n)
  | .Ccompl c, [v1, v2] => Val.cmpl_bool c v1 v2
  | .Ccomplu c, [v1, v2] => Val.cmplu_bool (Mem.validPointer m) c v1 v2
  | .Ccomplimm c n, [v1] => Val.cmpl_bool c v1 (.Vlong n)
  | .Ccompluimm c n, [v1] => Val.cmplu_bool (Mem.validPointer m) c v1 (.Vlong n)
  | .Ccompf c, [v1, v2] => Val.cmpf_bool c v1 v2
  | .Cnotcompf c, [v1, v2] => Option.map not (Val.cmpf_bool c v1 v2)
  | .Ccompfs c, [v1, v2] => Val.cmpfs_bool c v1 v2
  | .Cnotcompfs c, [v1, v2] => Option.map not (Val.cmpfs_bool c v1 v2)
  | .Cmaskzero n, [v1] => Val.maskzero_bool v1 n
  | .Cmasknotzero n, [v1] => Option.map not (Val.maskzero_bool v1 n)
  | _, _ => none

/-- `Op.eval_addressing32` -/
def evalAddressing32 {F V : Type} (genv : Genv F V) (sp : Val)
    (addr : Addressing) (vl : List Val) : Option Val :=
  match addr, vl with
  | .Aindexed n, [v1] => some (Val.add v1 (.Vint (Integers.Int.repr n)))
  | .Aindexed2 n, [v1, v2] => some (Val.add (Val.add v1 v2) (.Vint (Integers.Int.repr n)))
  | .Ascaled sc ofs, [v1] =>
      some (Val.add (Val.mul v1 (.Vint (Integers.Int.repr sc))) (.Vint (Integers.Int.repr ofs)))
  | .Aindexed2scaled sc ofs, [v1, v2] =>
      some (Val.add v1 (Val.add (Val.mul v2 (.Vint (Integers.Int.repr sc))) (.Vint (Integers.Int.repr ofs))))
  | .Aglobal s ofs, [] =>
      if Archi.ptr64 then none else some (Genv.symbolAddress genv s ofs)
  | .Abased s ofs, [v1] =>
      if Archi.ptr64 then none else some (Val.add (Genv.symbolAddress genv s ofs) v1)
  | .Abasedscaled sc s ofs, [v1] =>
      if Archi.ptr64 then none
      else some (Val.add (Genv.symbolAddress genv s ofs) (Val.mul v1 (.Vint (Integers.Int.repr sc))))
  | .Ainstack ofs, [] =>
      if Archi.ptr64 then none else some (Val.offsetPtr sp ofs)
  | _, _ => none

/-- `Op.eval_addressing64` -/
def evalAddressing64 {F V : Type} (genv : Genv F V) (sp : Val)
    (addr : Addressing) (vl : List Val) : Option Val :=
  match addr, vl with
  | .Aindexed n, [v1] => some (Val.addl v1 (.Vlong (Integers.Int64.repr n)))
  | .Aindexed2 n, [v1, v2] => some (Val.addl (Val.addl v1 v2) (.Vlong (Integers.Int64.repr n)))
  | .Ascaled sc ofs, [v1] =>
      some (Val.addl (Val.mull v1 (.Vlong (Integers.Int64.repr sc))) (.Vlong (Integers.Int64.repr ofs)))
  | .Aindexed2scaled sc ofs, [v1, v2] =>
      some (Val.addl v1 (Val.addl (Val.mull v2 (.Vlong (Integers.Int64.repr sc))) (.Vlong (Integers.Int64.repr ofs))))
  | .Aglobal s ofs, [] =>
      if Archi.ptr64 then some (Genv.symbolAddress genv s ofs) else none
  | .Ainstack ofs, [] =>
      if Archi.ptr64 then some (Val.offsetPtr sp ofs) else none
  | _, _ => none

/-- `Op.eval_addressing` -/
def evalAddressing {F V : Type} (genv : Genv F V) (sp : Val)
    (addr : Addressing) (vl : List Val) : Option Val :=
  if Archi.ptr64 then evalAddressing64 genv sp addr vl
  else evalAddressing32 genv sp addr vl

/-- `Op.eval_operation` -/
def evalOperation {F V : Type} (genv : Genv F V) (sp : Val)
    (op : Operation) (vl : List Val) (m : Mem) : Option Val :=
  match op, vl with
  | .Omove, [v1] => some v1
  | .Ointconst n, [] => some (.Vint n)
  | .Olongconst n, [] => some (.Vlong n)
  | .Ofloatconst n, [] => some (.Vfloat n)
  | .Osingleconst n, [] => some (.Vsingle n)
  | .Oindirectsymbol id, [] => some (Genv.symbolAddress genv id Integers.Ptrofs.zero)
  | .Ocast8signed, [v1] => some (Val.signExt 8 v1)
  | .Ocast8unsigned, [v1] => some (Val.zeroExt 8 v1)
  | .Ocast16signed, [v1] => some (Val.signExt 16 v1)
  | .Ocast16unsigned, [v1] => some (Val.zeroExt 16 v1)
  | .Oneg, [v1] => some (Val.neg v1)
  | .Osub, [v1, v2] => some (Val.sub v1 v2)
  | .Omul, [v1, v2] => some (Val.mul v1 v2)
  | .Omulimm n, [v1] => some (Val.mul v1 (.Vint n))
  | .Omulhs, [v1, v2] => some (Val.mulhs v1 v2)
  | .Omulhu, [v1, v2] => some (Val.mulhu v1 v2)
  | .Odiv, [v1, v2] => Val.divs v1 v2
  | .Odivu, [v1, v2] => Val.divu v1 v2
  | .Omod, [v1, v2] => Val.mods v1 v2
  | .Omodu, [v1, v2] => Val.modu v1 v2
  | .Oand, [v1, v2] => some (Val.and v1 v2)
  | .Oandimm n, [v1] => some (Val.and v1 (.Vint n))
  | .Oor, [v1, v2] => some (Val.or v1 v2)
  | .Oorimm n, [v1] => some (Val.or v1 (.Vint n))
  | .Oxor, [v1, v2] => some (Val.xor v1 v2)
  | .Oxorimm n, [v1] => some (Val.xor v1 (.Vint n))
  | .Onot, [v1] => some (Val.notint v1)
  | .Oshl, [v1, v2] => some (Val.shl v1 v2)
  | .Oshlimm n, [v1] => some (Val.shl v1 (.Vint n))
  | .Oshr, [v1, v2] => some (Val.shr v1 v2)
  | .Oshrimm n, [v1] => some (Val.shr v1 (.Vint n))
  | .Oshrximm n, [v1] => Val.shrx v1 (.Vint n)
  | .Oshru, [v1, v2] => some (Val.shru v1 v2)
  | .Oshruimm n, [v1] => some (Val.shru v1 (.Vint n))
  | .Ororimm n, [v1] => some (Val.ror v1 (.Vint n))
  | .Oshldimm n, [v1, v2] =>
      some (Val.or (Val.shl v1 (.Vint n)) (Val.shru v2 (.Vint (Integers.Int.sub Integers.Int.iwordsize n))))
  | .Olea addr, _ => evalAddressing32 genv sp addr vl
  | .Omakelong, [v1, v2] => some (Val.longofwords v1 v2)
  | .Olowlong, [v1] => some (Val.loword v1)
  | .Ohighlong, [v1] => some (Val.hiword v1)
  | .Ocast32signed, [v1] => some (Val.longofint v1)
  | .Ocast32unsigned, [v1] => some (Val.longofintu v1)
  | .Onegl, [v1] => some (Val.negl v1)
  | .Oaddlimm n, [v1] => some (Val.addl v1 (.Vlong n))
  | .Osubl, [v1, v2] => some (Val.subl v1 v2)
  | .Omull, [v1, v2] => some (Val.mull v1 v2)
  | .Omullimm n, [v1] => some (Val.mull v1 (.Vlong n))
  | .Omullhs, [v1, v2] => some (Val.mullhs v1 v2)
  | .Omullhu, [v1, v2] => some (Val.mullhu v1 v2)
  | .Odivl, [v1, v2] => Val.divls v1 v2
  | .Odivlu, [v1, v2] => Val.divlu v1 v2
  | .Omodl, [v1, v2] => Val.modls v1 v2
  | .Omodlu, [v1, v2] => Val.modlu v1 v2
  | .Oandl, [v1, v2] => some (Val.andl v1 v2)
  | .Oandlimm n, [v1] => some (Val.andl v1 (.Vlong n))
  | .Oorl, [v1, v2] => some (Val.orl v1 v2)
  | .Oorlimm n, [v1] => some (Val.orl v1 (.Vlong n))
  | .Oxorl, [v1, v2] => some (Val.xorl v1 v2)
  | .Oxorlimm n, [v1] => some (Val.xorl v1 (.Vlong n))
  | .Onotl, [v1] => some (Val.notl v1)
  | .Oshll, [v1, v2] => some (Val.shll v1 v2)
  | .Oshllimm n, [v1] => some (Val.shll v1 (.Vint n))
  | .Oshrl, [v1, v2] => some (Val.shrl v1 v2)
  | .Oshrlimm n, [v1] => some (Val.shrl v1 (.Vint n))
  | .Oshrxlimm n, [v1] => Val.shrxl v1 (.Vint n)
  | .Oshrlu, [v1, v2] => some (Val.shrlu v1 v2)
  | .Oshrluimm n, [v1] => some (Val.shrlu v1 (.Vint n))
  | .Ororlimm n, [v1] => some (Val.rorl v1 (.Vint n))
  | .Oleal addr, _ => evalAddressing64 genv sp addr vl
  | .Onegf, [v1] => some (Val.negf v1)
  | .Oabsf, [v1] => some (Val.absf v1)
  | .Oaddf, [v1, v2] => some (Val.addf v1 v2)
  | .Osubf, [v1, v2] => some (Val.subf v1 v2)
  | .Omulf, [v1, v2] => some (Val.mulf v1 v2)
  | .Odivf, [v1, v2] => some (Val.divf v1 v2)
  | .Omaxf, [v1, v2] => some (maxf v1 v2)
  | .Ominf, [v1, v2] => some (minf v1 v2)
  | .Onegfs, [v1] => some (Val.negfs v1)
  | .Oabsfs, [v1] => some (Val.absfs v1)
  | .Oaddfs, [v1, v2] => some (Val.addfs v1 v2)
  | .Osubfs, [v1, v2] => some (Val.subfs v1 v2)
  | .Omulfs, [v1, v2] => some (Val.mulfs v1 v2)
  | .Odivfs, [v1, v2] => some (Val.divfs v1 v2)
  | .Osingleoffloat, [v1] => some (Val.singleoffloat v1)
  | .Ofloatofsingle, [v1] => some (Val.floatofsingle v1)
  | .Ointoffloat, [v1] => Val.intoffloat v1
  | .Ofloatofint, [v1] => Val.floatofint v1
  | .Ointofsingle, [v1] => Val.intofsingle v1
  | .Osingleofint, [v1] => Val.singleofint v1
  | .Olongoffloat, [v1] => Val.longoffloat v1
  | .Ofloatoflong, [v1] => Val.floatoflong v1
  | .Olongofsingle, [v1] => Val.longofsingle v1
  | .Osingleoflong, [v1] => Val.singleoflong v1
  | .Ocmp c, _ => some (Val.ofOptbool (evalCondition c vl m))
  | .Osel c ty, v1 :: v2 :: vl => some (Val.select (evalCondition c vl m) v1 v2 ty)
  | _, _ => none

/-! ## Static typing -/

/-- `Op.type_of_condition` -/
def typeOfCondition (c : Condition) : List ATyp :=
  match c with
  | .Ccomp _ | .Ccompu _ => [.Tint, .Tint]
  | .Ccompimm _ _ | .Ccompuimm _ _ => [.Tint]
  | .Ccompl _ | .Ccomplu _ => [.Tlong, .Tlong]
  | .Ccomplimm _ _ | .Ccompluimm _ _ => [.Tlong]
  | .Ccompf _ | .Cnotcompf _ => [.Tfloat, .Tfloat]
  | .Ccompfs _ | .Cnotcompfs _ => [.Tsingle, .Tsingle]
  | .Cmaskzero _ | .Cmasknotzero _ => [.Tint]

/-- `Op.type_of_addressing_gen` -/
def typeOfAddressingGen (tyA : ATyp) (addr : Addressing) : List ATyp :=
  match addr with
  | .Aindexed _ => [tyA]
  | .Aindexed2 _ => [tyA, tyA]
  | .Ascaled _ _ => [tyA]
  | .Aindexed2scaled _ _ => [tyA, tyA]
  | .Aglobal _ _ => []
  | .Abased _ _ => [tyA]
  | .Abasedscaled _ _ _ => [tyA]
  | .Ainstack _ => []

/-- `Op.type_of_addressing` -/
def typeOfAddressing : Addressing → List ATyp := typeOfAddressingGen Tptr
/-- `Op.type_of_addressing32` -/
def typeOfAddressing32 : Addressing → List ATyp := typeOfAddressingGen .Tint
/-- `Op.type_of_addressing64` -/
def typeOfAddressing64 : Addressing → List ATyp := typeOfAddressingGen .Tlong

/-- `Op.type_of_operation` -/
def typeOfOperation (op : Operation) : List ATyp × ATyp :=
  match op with
  | .Omove => ([], .Tint)  -- treated specially
  | .Ointconst _ => ([], .Tint)
  | .Olongconst _ => ([], .Tlong)
  | .Ofloatconst _ => ([], .Tfloat)
  | .Osingleconst _ => ([], .Tsingle)
  | .Oindirectsymbol _ => ([], Tptr)
  | .Ocast8signed | .Ocast8unsigned | .Ocast16signed | .Ocast16unsigned => ([.Tint], .Tint)
  | .Oneg => ([.Tint], .Tint)
  | .Osub | .Omul => ([.Tint, .Tint], .Tint)
  | .Omulimm _ => ([.Tint], .Tint)
  | .Omulhs | .Omulhu | .Odiv | .Odivu | .Omod | .Omodu => ([.Tint, .Tint], .Tint)
  | .Oand => ([.Tint, .Tint], .Tint)
  | .Oandimm _ => ([.Tint], .Tint)
  | .Oor => ([.Tint, .Tint], .Tint)
  | .Oorimm _ => ([.Tint], .Tint)
  | .Oxor => ([.Tint, .Tint], .Tint)
  | .Oxorimm _ => ([.Tint], .Tint)
  | .Onot => ([.Tint], .Tint)
  | .Oshl => ([.Tint, .Tint], .Tint)
  | .Oshlimm _ => ([.Tint], .Tint)
  | .Oshr => ([.Tint, .Tint], .Tint)
  | .Oshrimm _ | .Oshrximm _ => ([.Tint], .Tint)
  | .Oshru => ([.Tint, .Tint], .Tint)
  | .Oshruimm _ | .Ororimm _ => ([.Tint], .Tint)
  | .Oshldimm _ => ([.Tint, .Tint], .Tint)
  | .Olea addr => (typeOfAddressing32 addr, .Tint)
  | .Omakelong => ([.Tint, .Tint], .Tlong)
  | .Olowlong | .Ohighlong => ([.Tlong], .Tint)
  | .Ocast32signed | .Ocast32unsigned => ([.Tint], .Tlong)
  | .Onegl | .Oaddlimm _ => ([.Tlong], .Tlong)
  | .Osubl | .Omull => ([.Tlong, .Tlong], .Tlong)
  | .Omullimm _ => ([.Tlong], .Tlong)
  | .Omullhs | .Omullhu | .Odivl | .Odivlu | .Omodl | .Omodlu => ([.Tlong, .Tlong], .Tlong)
  | .Oandl => ([.Tlong, .Tlong], .Tlong)
  | .Oandlimm _ => ([.Tlong], .Tlong)
  | .Oorl => ([.Tlong, .Tlong], .Tlong)
  | .Oorlimm _ => ([.Tlong], .Tlong)
  | .Oxorl => ([.Tlong, .Tlong], .Tlong)
  | .Oxorlimm _ => ([.Tlong], .Tlong)
  | .Onotl => ([.Tlong], .Tlong)
  | .Oshll => ([.Tlong, .Tint], .Tlong)
  | .Oshllimm _ => ([.Tlong], .Tlong)
  | .Oshrl => ([.Tlong, .Tint], .Tlong)
  | .Oshrlimm _ | .Oshrxlimm _ => ([.Tlong], .Tlong)
  | .Oshrlu => ([.Tlong, .Tint], .Tlong)
  | .Oshrluimm _ | .Ororlimm _ => ([.Tlong], .Tlong)
  | .Oleal addr => (typeOfAddressing64 addr, .Tlong)
  | .Onegf | .Oabsf => ([.Tfloat], .Tfloat)
  | .Oaddf | .Osubf | .Omulf | .Odivf | .Omaxf | .Ominf => ([.Tfloat, .Tfloat], .Tfloat)
  | .Onegfs | .Oabsfs => ([.Tsingle], .Tsingle)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => ([.Tsingle, .Tsingle], .Tsingle)
  | .Osingleoffloat => ([.Tfloat], .Tsingle)
  | .Ofloatofsingle => ([.Tsingle], .Tfloat)
  | .Ointoffloat => ([.Tfloat], .Tint)
  | .Ofloatofint => ([.Tint], .Tfloat)
  | .Ointofsingle => ([.Tsingle], .Tint)
  | .Osingleofint => ([.Tint], .Tsingle)
  | .Olongoffloat => ([.Tfloat], .Tlong)
  | .Ofloatoflong => ([.Tlong], .Tfloat)
  | .Olongofsingle => ([.Tsingle], .Tlong)
  | .Osingleoflong => ([.Tlong], .Tsingle)
  | .Ocmp c => (typeOfCondition c, .Tint)
  | .Osel c ty => (ty :: ty :: typeOfCondition c, ty)

/-! ## Manipulating and transforming operations -/

/-- `Op.is_move_operation` -/
def isMoveOperation {A : Type} (op : Operation) (args : List A) : Option A :=
  match op, args with
  | .Omove, [arg] => some arg
  | _, _ => none

/-- `Op.negate_condition` -/
def negateCondition (cond : Condition) : Condition :=
  match cond with
  | .Ccomp c => .Ccomp c.negate
  | .Ccompu c => .Ccompu c.negate
  | .Ccompimm c n => .Ccompimm c.negate n
  | .Ccompuimm c n => .Ccompuimm c.negate n
  | .Ccompl c => .Ccompl c.negate
  | .Ccomplu c => .Ccomplu c.negate
  | .Ccomplimm c n => .Ccomplimm c.negate n
  | .Ccompluimm c n => .Ccompluimm c.negate n
  | .Ccompf c => .Cnotcompf c
  | .Cnotcompf c => .Ccompf c
  | .Ccompfs c => .Cnotcompfs c
  | .Cnotcompfs c => .Ccompfs c
  | .Cmaskzero n => .Cmasknotzero n
  | .Cmasknotzero n => .Cmaskzero n

/-- `Op.shift_stack_addressing` -/
def shiftStackAddressing (delta : Z) (addr : Addressing) : Addressing :=
  match addr with
  | .Ainstack ofs => .Ainstack (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta))
  | _ => addr

/-- `Op.shift_stack_operation` -/
def shiftStackOperation (delta : Z) (op : Operation) : Operation :=
  match op with
  | .Olea addr => .Olea (shiftStackAddressing delta addr)
  | .Oleal addr => .Oleal (shiftStackAddressing delta addr)
  | _ => op

/-- `Op.offset_addressing_total` -/
def offsetAddressingTotal (addr : Addressing) (delta : Z) : Addressing :=
  match addr with
  | .Aindexed n => .Aindexed (n + delta)
  | .Aindexed2 n => .Aindexed2 (n + delta)
  | .Ascaled sc n => .Ascaled sc (n + delta)
  | .Aindexed2scaled sc n => .Aindexed2scaled sc (n + delta)
  | .Aglobal s n => .Aglobal s (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta))
  | .Abased s n => .Abased s (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta))
  | .Abasedscaled sc s n => .Abasedscaled sc s (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta))
  | .Ainstack n => .Ainstack (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta))

/-- `Op.offset_addressing` -/
def offsetAddressing (addr : Addressing) (delta : Z) : Option Addressing :=
  let addr' := offsetAddressingTotal addr delta
  if addressingValid addr' then some addr' else none

/-- `Op.is_trivial_op` -/
def isTrivialOp (op : Operation) : Bool :=
  match op with
  | .Omove => true
  | .Ointconst _ => true
  | .Olongconst _ => true
  | .Olea (.Aglobal _ _) => true
  | .Olea (.Ainstack _) => true
  | .Oleal (.Aglobal _ _) => true
  | .Oleal (.Ainstack _) => true
  | _ => false

/-- `Op.condition_depends_on_memory` -/
def conditionDependsOnMemory (c : Condition) : Bool :=
  match c with
  | .Ccompu _ => !Archi.ptr64
  | .Ccompuimm _ _ => !Archi.ptr64
  | .Ccomplu _ => Archi.ptr64
  | .Ccompluimm _ _ => Archi.ptr64
  | _ => false

/-- `Op.op_depends_on_memory` -/
def opDependsOnMemory (op : Operation) : Bool :=
  match op with
  | .Ocmp c => conditionDependsOnMemory c
  | .Osel c _ => conditionDependsOnMemory c
  | _ => false

/-- `Op.globals_addressing` -/
def globalsAddressing (addr : Addressing) : List Ident :=
  match addr with
  | .Aglobal s _ => [s]
  | .Abased s _ => [s]
  | .Abasedscaled _ s _ => [s]
  | _ => []

/-- `Op.globals_operation` -/
def globalsOperation (op : Operation) : List Ident :=
  match op with
  | .Oindirectsymbol s => [s]
  | .Olea addr => globalsAddressing addr
  | .Oleal addr => globalsAddressing addr
  | _ => []

/-- `Op.builtin_arg_ok_1` -/
def builtinArgOk1 {A : Type} (ba : BuiltinArg A) (c : BuiltinArgConstraint) : Bool :=
  match c, ba with
  | .OK_all, _ => true
  | .OK_const, .BA_int _ | .OK_const, .BA_long _
  | .OK_const, .BA_float _ | .OK_const, .BA_single _ => true
  | .OK_addrstack, .BA_addrstack _ => true
  | .OK_addressing, .BA_addrstack _ => true
  | .OK_addressing, .BA_addrglobal _ _ => true
  | .OK_addressing, .BA_addptr (.BA _) (.BA_int _) => true
  | .OK_addressing, .BA_addptr (.BA _) (.BA_long _) => true
  | _, _ => false

/-- `Op.builtin_arg_ok` -/
def builtinArgOk {A : Type} (ba : BuiltinArg A) (c : BuiltinArgConstraint) : Bool :=
  match ba with
  | .BA _ | .BA_splitlong (.BA _) (.BA _) => true
  | _ => builtinArgOk1 ba c

end Op
end X86
end CC
