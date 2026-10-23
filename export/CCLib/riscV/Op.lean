/-
  Operators and addressing modes of the RISC-V back end — port of
  `riscV/Op.v` (syntax, `eval_condition`, `eval_operation`,
  `eval_addressing`, static typing, `is_move_operation`,
  `negate_condition`, the stack-shifting functions, `offset_addressing`,
  `is_trivial_op`, the memory-dependence tests, `globals_operation` /
  `globals_addressing` and `builtin_arg_ok`).

  The port's `Archi.ptr64` is `true`, which is the RV64 configuration
  (see `CCLib/targets/Archi.lean`, `ArchiConfig.riscV true`).

  Differences from Rocq: `Val.sign_ext` takes a `Nat` width.
-/
import CCLib.common.Globalenvs
import CCLib.common.ValuesOps
import CCLib.common.ASTTheory

namespace CC
namespace RiscV
namespace Op

/-- `Op.condition` (RISC-V) -/
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
  deriving DecidableEq

/-- `Op.operation` (RISC-V) -/
inductive Operation where
  | Omove
  | Ointconst (n : Integers.Int)
  | Olongconst (n : Integers.Int64)
  | Ofloatconst (n : Floats.Float)
  | Osingleconst (n : Floats.Float32)
  | Oaddrsymbol (id : Ident) (ofs : Integers.Ptrofs)
  | Oaddrstack (ofs : Integers.Ptrofs)
  | Ocast8signed
  | Ocast16signed
  | Oadd
  | Oaddimm (n : Integers.Int)
  | Oneg
  | Osub
  | Omul
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
  | Oshl
  | Oshlimm (n : Integers.Int)
  | Oshr
  | Oshrimm (n : Integers.Int)
  | Oshru
  | Oshruimm (n : Integers.Int)
  | Oshrximm (n : Integers.Int)
  | Omakelong
  | Olowlong
  | Ohighlong
  | Ocast32signed
  | Ocast32unsigned
  | Oaddl
  | Oaddlimm (n : Integers.Int64)
  | Onegl
  | Osubl
  | Omull
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
  | Oshll
  | Oshllimm (n : Integers.Int)
  | Oshrl
  | Oshrlimm (n : Integers.Int)
  | Oshrlu
  | Oshrluimm (n : Integers.Int)
  | Oshrxlimm (n : Integers.Int)
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

/-- `Op.addressing` (RISC-V) -/
inductive Addressing where
  /-- `r1 + offset` -/
  | Aindexed (ofs : Integers.Ptrofs)
  /-- global plus offset -/
  | Aglobal (id : Ident) (ofs : Integers.Ptrofs)
  /-- `stack_pointer + offset` -/
  | Ainstack (ofs : Integers.Ptrofs)
  deriving DecidableEq

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
  | .Ocast8signed, [v1] => some (Val.signExt 8 v1)
  | .Ocast16signed, [v1] => some (Val.signExt 16 v1)
  | .Oadd, [v1, v2] => some (Val.add v1 v2)
  | .Oaddimm n, [v1] => some (Val.add v1 (.Vint n))
  | .Oneg, [v1] => some (Val.neg v1)
  | .Osub, [v1, v2] => some (Val.sub v1 v2)
  | .Omul, [v1, v2] => some (Val.mul v1 v2)
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
  | .Oshl, [v1, v2] => some (Val.shl v1 v2)
  | .Oshlimm n, [v1] => some (Val.shl v1 (.Vint n))
  | .Oshr, [v1, v2] => some (Val.shr v1 v2)
  | .Oshrimm n, [v1] => some (Val.shr v1 (.Vint n))
  | .Oshru, [v1, v2] => some (Val.shru v1 v2)
  | .Oshruimm n, [v1] => some (Val.shru v1 (.Vint n))
  | .Oshrximm n, [v1] => Val.shrx v1 (.Vint n)
  | .Omakelong, [v1, v2] => some (Val.longofwords v1 v2)
  | .Olowlong, [v1] => some (Val.loword v1)
  | .Ohighlong, [v1] => some (Val.hiword v1)
  | .Ocast32signed, [v1] => some (Val.longofint v1)
  | .Ocast32unsigned, [v1] => some (Val.longofintu v1)
  | .Oaddl, [v1, v2] => some (Val.addl v1 v2)
  | .Oaddlimm n, [v1] => some (Val.addl v1 (.Vlong n))
  | .Onegl, [v1] => some (Val.negl v1)
  | .Osubl, [v1, v2] => some (Val.subl v1 v2)
  | .Omull, [v1, v2] => some (Val.mull v1 v2)
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
  | .Oshll, [v1, v2] => some (Val.shll v1 v2)
  | .Oshllimm n, [v1] => some (Val.shll v1 (.Vint n))
  | .Oshrl, [v1, v2] => some (Val.shrl v1 v2)
  | .Oshrlimm n, [v1] => some (Val.shrl v1 (.Vint n))
  | .Oshrlu, [v1, v2] => some (Val.shrlu v1 v2)
  | .Oshrluimm n, [v1] => some (Val.shrlu v1 (.Vint n))
  | .Oshrxlimm n, [v1] => Val.shrxl v1 (.Vint n)
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
  | .Aindexed n, [v1] => some (Val.offsetPtr v1 n)
  | .Aglobal s ofs, [] => some (Genv.symbolAddress genv s ofs)
  | .Ainstack n, [] => some (Val.offsetPtr sp n)
  | _, _ => none

/-- `Op.eval_addressing_Ainstack` -/
theorem evalAddressing_Ainstack {F V : Type} (genv : Genv F V) (sp : Val)
    (ofs : Integers.Ptrofs) :
    evalAddressing genv sp (.Ainstack ofs) [] = some (Val.offsetPtr sp ofs) := rfl

/-- `Op.eval_addressing_Ainstack_inv` -/
theorem evalAddressing_Ainstack_inv {F V : Type} (genv : Genv F V) (sp : Val)
    (ofs : Integers.Ptrofs) (vl : List Val) (v : Val)
    (h : evalAddressing genv sp (.Ainstack ofs) vl = some v) :
    vl = [] ∧ v = Val.offsetPtr sp ofs := by
  cases vl with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons _ _ => cases h

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

/-- `Op.type_of_operation` (`Omove` is treated specially) -/
def typeOfOperation (op : Operation) : List ATyp × ATyp :=
  match op with
  | .Omove => ([], .Tint)
  | .Ointconst _ => ([], .Tint)
  | .Olongconst _ => ([], .Tlong)
  | .Ofloatconst _ => ([], .Tfloat)
  | .Osingleconst _ => ([], .Tsingle)
  | .Oaddrsymbol _ _ => ([], Tptr)
  | .Oaddrstack _ => ([], Tptr)
  | .Ocast8signed => ([.Tint], .Tint)
  | .Ocast16signed => ([.Tint], .Tint)
  | .Oadd => ([.Tint, .Tint], .Tint)
  | .Oaddimm _ => ([.Tint], .Tint)
  | .Oneg => ([.Tint], .Tint)
  | .Osub => ([.Tint, .Tint], .Tint)
  | .Omul => ([.Tint, .Tint], .Tint)
  | .Omulhs => ([.Tint, .Tint], .Tint)
  | .Omulhu => ([.Tint, .Tint], .Tint)
  | .Odiv => ([.Tint, .Tint], .Tint)
  | .Odivu => ([.Tint, .Tint], .Tint)
  | .Omod => ([.Tint, .Tint], .Tint)
  | .Omodu => ([.Tint, .Tint], .Tint)
  | .Oand => ([.Tint, .Tint], .Tint)
  | .Oandimm _ => ([.Tint], .Tint)
  | .Oor => ([.Tint, .Tint], .Tint)
  | .Oorimm _ => ([.Tint], .Tint)
  | .Oxor => ([.Tint, .Tint], .Tint)
  | .Oxorimm _ => ([.Tint], .Tint)
  | .Oshl => ([.Tint, .Tint], .Tint)
  | .Oshlimm _ => ([.Tint], .Tint)
  | .Oshr => ([.Tint, .Tint], .Tint)
  | .Oshrimm _ => ([.Tint], .Tint)
  | .Oshru => ([.Tint, .Tint], .Tint)
  | .Oshruimm _ => ([.Tint], .Tint)
  | .Oshrximm _ => ([.Tint], .Tint)
  | .Omakelong => ([.Tint, .Tint], .Tlong)
  | .Olowlong => ([.Tlong], .Tint)
  | .Ohighlong => ([.Tlong], .Tint)
  | .Ocast32signed => ([.Tint], .Tlong)
  | .Ocast32unsigned => ([.Tint], .Tlong)
  | .Oaddl => ([.Tlong, .Tlong], .Tlong)
  | .Oaddlimm _ => ([.Tlong], .Tlong)
  | .Onegl => ([.Tlong], .Tlong)
  | .Osubl => ([.Tlong, .Tlong], .Tlong)
  | .Omull => ([.Tlong, .Tlong], .Tlong)
  | .Omullhs => ([.Tlong, .Tlong], .Tlong)
  | .Omullhu => ([.Tlong, .Tlong], .Tlong)
  | .Odivl => ([.Tlong, .Tlong], .Tlong)
  | .Odivlu => ([.Tlong, .Tlong], .Tlong)
  | .Omodl => ([.Tlong, .Tlong], .Tlong)
  | .Omodlu => ([.Tlong, .Tlong], .Tlong)
  | .Oandl => ([.Tlong, .Tlong], .Tlong)
  | .Oandlimm _ => ([.Tlong], .Tlong)
  | .Oorl => ([.Tlong, .Tlong], .Tlong)
  | .Oorlimm _ => ([.Tlong], .Tlong)
  | .Oxorl => ([.Tlong, .Tlong], .Tlong)
  | .Oxorlimm _ => ([.Tlong], .Tlong)
  | .Oshll => ([.Tlong, .Tint], .Tlong)
  | .Oshllimm _ => ([.Tlong], .Tlong)
  | .Oshrl => ([.Tlong, .Tint], .Tlong)
  | .Oshrlimm _ => ([.Tlong], .Tlong)
  | .Oshrlu => ([.Tlong, .Tint], .Tlong)
  | .Oshrluimm _ => ([.Tlong], .Tlong)
  | .Oshrxlimm _ => ([.Tlong], .Tlong)
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

/-- `Op.offset_addressing` (always succeeds on RISC-V) -/
def offsetAddressing (addr : Addressing) (delta : Z) : Option Addressing :=
  match addr with
  | .Aindexed n => some (.Aindexed (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta)))
  | .Aglobal id n => some (.Aglobal id (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta)))
  | .Ainstack n => some (.Ainstack (Integers.Ptrofs.add n (Integers.Ptrofs.repr delta)))

/-- `Op.is_trivial_op`: cheap enough that CSE should not factor them out
(12-bit immediates fit in one `addi`). -/
def isTrivialOp (op : Operation) : Bool :=
  match op with
  | .Omove => true
  | .Ointconst n => Integers.Int.eq (Integers.Int.sign_ext 12 n) n
  | .Olongconst n => Integers.Int64.eq (Integers.Int64.sign_ext 12 n) n
  | .Oaddrstack _ => true
  | _ => false

/-- `Op.cond_depends_on_memory` -/
def condDependsOnMemory (c : Condition) : Bool :=
  match c with
  | .Ccompu _ | .Ccompuimm _ _ => !Archi.ptr64
  | .Ccomplu _ | .Ccompluimm _ _ => Archi.ptr64
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

end Op
end RiscV
end CC
