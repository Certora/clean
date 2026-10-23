/-
  Abstract syntax and operators of Cminor — port of the first part of
  `backend/Cminor.v` (syntax, environments, continuations, states,
  `eval_constant`, `eval_unop`, `eval_binop`).

  Cminor is the low-level imperative language that `Cminorgen` targets;
  its operators are shared with Csharpminor.

  This file also provides `ASTFundef` (`AST.fundef`, the generic
  internal/external function definition used by every language after
  Clight) and `ASTFundef.transfPartial` (`AST.transf_partial_fundef`).
-/
import CCLib.common.Globalenvs
import CCLib.common.ValuesOps

namespace CC

/-- `AST.fundef`: a function definition, internal (of type `F`) or
    external. -/
inductive ASTFundef (F : Type) where
  | Internal (f : F)
  | External (ef : ExtFun)

/-- `AST.transf_partial_fundef` -/
def ASTFundef.transfPartial {A B : Type} (transf : A → Res B) : ASTFundef A → Res (ASTFundef B)
  | .Internal f =>
    match transf f with
    | .OK tf => .OK (.Internal tf)
    | .Error msg => .Error msg
  | .External ef => .OK (.External ef)

namespace Cminor

/-! ## Abstract syntax -/

/-- `Cminor.constant` -/
inductive Constant where
  | Ointconst (n : Integers.Int)
  | Ofloatconst (f : Floats.Float)
  | Osingleconst (f : Floats.Float32)
  | Olongconst (n : Integers.Int64)
  | Oaddrsymbol (id : Ident) (ofs : Integers.Ptrofs)
  | Oaddrstack (ofs : Integers.Ptrofs)

/-- `Cminor.unary_operation` -/
inductive UnaryOperation where
  | Ocast8unsigned | Ocast8signed | Ocast16unsigned | Ocast16signed
  | Onegint | Onotint
  | Onegf | Oabsf | Onegfs | Oabsfs
  | Osingleoffloat | Ofloatofsingle
  | Ointoffloat | Ointuoffloat | Ofloatofint | Ofloatofintu
  | Ointofsingle | Ointuofsingle | Osingleofint | Osingleofintu
  | Onegl | Onotl | Ointoflong | Olongofint | Olongofintu
  | Olongoffloat | Olonguoffloat | Ofloatoflong | Ofloatoflongu
  | Olongofsingle | Olonguofsingle | Osingleoflong | Osingleoflongu
  deriving DecidableEq, Repr

/-- `Cminor.binary_operation` -/
inductive BinaryOperation where
  | Oadd | Osub | Omul | Odiv | Odivu | Omod | Omodu
  | Oand | Oor | Oxor | Oshl | Oshr | Oshru
  | Oaddf | Osubf | Omulf | Odivf
  | Oaddfs | Osubfs | Omulfs | Odivfs
  | Oaddl | Osubl | Omull | Odivl | Odivlu | Omodl | Omodlu
  | Oandl | Oorl | Oxorl | Oshll | Oshrl | Oshrlu
  | Ocmp (c : Comparison) | Ocmpu (c : Comparison)
  | Ocmpf (c : Comparison) | Ocmpfs (c : Comparison)
  | Ocmpl (c : Comparison) | Ocmplu (c : Comparison)
  deriving DecidableEq, Repr

/-- `Cminor.expr` -/
inductive Expr where
  | Evar (id : Ident)
  | Econst (c : Constant)
  | Eunop (op : UnaryOperation) (a : Expr)
  | Ebinop (op : BinaryOperation) (a1 a2 : Expr)
  | Eload (chunk : Chunk) (a : Expr)

/-- `Cminor.label` -/
abbrev Label := Ident

/-- `Cminor.stmt` -/
inductive Stmt where
  | Sskip
  | Sassign (id : Ident) (a : Expr)
  | Sstore (chunk : Chunk) (addr a : Expr)
  | Scall (optid : Option Ident) (sg : Signature) (fn : Expr) (args : List Expr)
  | Stailcall (sg : Signature) (fn : Expr) (args : List Expr)
  | Sbuiltin (optid : Option Ident) (ef : ExtFun) (args : List Expr)
  | Sseq (s1 s2 : Stmt)
  | Sifthenelse (a : Expr) (s1 s2 : Stmt)
  | Sloop (s : Stmt)
  | Sblock (s : Stmt)
  | Sexit (n : Nat)
  | Sswitch (islong : Bool) (a : Expr) (cases : List (Z × Nat)) (dfl : Nat)
  | Sreturn (a : Option Expr)
  | Slabel (lbl : Label) (s : Stmt)
  | Sgoto (lbl : Label)

/-- `Cminor.function` -/
structure Function where
  fn_sig : Signature
  fn_params : List Ident
  fn_vars : List Ident
  fn_stackspace : Z
  fn_body : Stmt

/-- `Cminor.fundef` -/
abbrev Fundef := ASTFundef Function

/-- `Cminor.program` -/
abbrev Program := ASTProgram Fundef Unit

/-- `Cminor.funsig` -/
def funsig : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External ef => ef.sig

/-! ## Environments, continuations and states -/

/-- `Cminor.genv` -/
abbrev CGenv := Genv Fundef Unit

/-- `Cminor.env`: values of the local variables. -/
abbrev Env := PTree Val

/-- `Cminor.set_params` -/
def setParams : List Val → List Ident → Env
  | v1 :: vl, i1 :: il => PTree.set i1 v1 (setParams vl il)
  | [], i1 :: il => PTree.set i1 .Vundef (setParams [] il)
  | _, [] => PTree.empty

/-- `Cminor.set_locals` -/
def setLocals : List Ident → Env → Env
  | [], e => e
  | i1 :: il, e => PTree.set i1 .Vundef (setLocals il e)

/-- `Cminor.set_optvar` -/
def setOptvar : Option Ident → Val → Env → Env
  | none, _, e => e
  | some id, v, e => PTree.set id v e

/-- `Cminor.cont` -/
inductive Cont where
  | Kstop
  | Kseq (s : Stmt) (k : Cont)
  | Kblock (k : Cont)
  | Kcall (optid : Option Ident) (f : Function) (sp : Val) (e : Env) (k : Cont)

/-- `Cminor.state` -/
inductive State where
  | State (f : Function) (s : Stmt) (k : Cont) (sp : Val) (e : Env) (m : Mem)
  | Callstate (f : Fundef) (args : List Val) (k : Cont) (m : Mem)
  | Returnstate (v : Val) (k : Cont) (m : Mem)

/-! ## Evaluation of constants and operators -/

/-- `Cminor.eval_constant` -/
def evalConstant (ge : CGenv) (sp : Val) : Constant → Option Val
  | .Ointconst n => some (.Vint n)
  | .Ofloatconst n => some (.Vfloat n)
  | .Osingleconst n => some (.Vsingle n)
  | .Olongconst n => some (.Vlong n)
  | .Oaddrsymbol s ofs => some (Genv.symbolAddress ge s ofs)
  | .Oaddrstack ofs => some (Val.offsetPtr sp ofs)

/-- `Cminor.eval_unop` -/
def evalUnop (op : UnaryOperation) (arg : Val) : Option Val :=
  match op with
  | .Ocast8unsigned => some (Val.zeroExt 8 arg)
  | .Ocast8signed => some (Val.signExt 8 arg)
  | .Ocast16unsigned => some (Val.zeroExt 16 arg)
  | .Ocast16signed => some (Val.signExt 16 arg)
  | .Onegint => some (Val.negint arg)
  | .Onotint => some (Val.notint arg)
  | .Onegf => some (Val.negf arg)
  | .Oabsf => some (Val.absf arg)
  | .Onegfs => some (Val.negfs arg)
  | .Oabsfs => some (Val.absfs arg)
  | .Osingleoffloat => some (Val.singleoffloat arg)
  | .Ofloatofsingle => some (Val.floatofsingle arg)
  | .Ointoffloat => Val.intoffloat arg
  | .Ointuoffloat => Val.intuoffloat arg
  | .Ofloatofint => Val.floatofint arg
  | .Ofloatofintu => Val.floatofintu arg
  | .Ointofsingle => Val.intofsingle arg
  | .Ointuofsingle => Val.intuofsingle arg
  | .Osingleofint => Val.singleofint arg
  | .Osingleofintu => Val.singleofintu arg
  | .Onegl => some (Val.negl arg)
  | .Onotl => some (Val.notl arg)
  | .Ointoflong => some (Val.loword arg)
  | .Olongofint => some (Val.longofint arg)
  | .Olongofintu => some (Val.longofintu arg)
  | .Olongoffloat => Val.longoffloat arg
  | .Olonguoffloat => Val.longuoffloat arg
  | .Ofloatoflong => Val.floatoflong arg
  | .Ofloatoflongu => Val.floatoflongu arg
  | .Olongofsingle => Val.longofsingle arg
  | .Olonguofsingle => Val.longuofsingle arg
  | .Osingleoflong => Val.singleoflong arg
  | .Osingleoflongu => Val.singleoflongu arg

/-- `Cminor.eval_binop` -/
def evalBinop (op : BinaryOperation) (arg1 arg2 : Val) (m : Mem) : Option Val :=
  match op with
  | .Oadd => some (Val.add arg1 arg2)
  | .Osub => some (Val.sub arg1 arg2)
  | .Omul => some (Val.mul arg1 arg2)
  | .Odiv => Val.divs arg1 arg2
  | .Odivu => Val.divu arg1 arg2
  | .Omod => Val.mods arg1 arg2
  | .Omodu => Val.modu arg1 arg2
  | .Oand => some (Val.and arg1 arg2)
  | .Oor => some (Val.or arg1 arg2)
  | .Oxor => some (Val.xor arg1 arg2)
  | .Oshl => some (Val.shl arg1 arg2)
  | .Oshr => some (Val.shr arg1 arg2)
  | .Oshru => some (Val.shru arg1 arg2)
  | .Oaddf => some (Val.addf arg1 arg2)
  | .Osubf => some (Val.subf arg1 arg2)
  | .Omulf => some (Val.mulf arg1 arg2)
  | .Odivf => some (Val.divf arg1 arg2)
  | .Oaddfs => some (Val.addfs arg1 arg2)
  | .Osubfs => some (Val.subfs arg1 arg2)
  | .Omulfs => some (Val.mulfs arg1 arg2)
  | .Odivfs => some (Val.divfs arg1 arg2)
  | .Oaddl => some (Val.addl arg1 arg2)
  | .Osubl => some (Val.subl arg1 arg2)
  | .Omull => some (Val.mull arg1 arg2)
  | .Odivl => Val.divls arg1 arg2
  | .Odivlu => Val.divlu arg1 arg2
  | .Omodl => Val.modls arg1 arg2
  | .Omodlu => Val.modlu arg1 arg2
  | .Oandl => some (Val.andl arg1 arg2)
  | .Oorl => some (Val.orl arg1 arg2)
  | .Oxorl => some (Val.xorl arg1 arg2)
  | .Oshll => some (Val.shll arg1 arg2)
  | .Oshrl => some (Val.shrl arg1 arg2)
  | .Oshrlu => some (Val.shrlu arg1 arg2)
  | .Ocmp c => some (Val.cmp c arg1 arg2)
  | .Ocmpu c => some (Val.cmpu (Mem.validPointer m) c arg1 arg2)
  | .Ocmpf c => some (Val.cmpf c arg1 arg2)
  | .Ocmpfs c => some (Val.cmpfs c arg1 arg2)
  | .Ocmpl c => Val.cmpl c arg1 arg2
  | .Ocmplu c => Val.cmplu (Mem.validPointer m) c arg1 arg2

end Cminor
end CC
