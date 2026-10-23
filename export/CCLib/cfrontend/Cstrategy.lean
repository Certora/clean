/-
  The deterministic reduction strategy of CompCert C — port of the first part
  of `cfrontend/Cstrategy.v` (definitions and basic properties, lines 1–495,
  and the strategy's `semantics`).

  CompCert's compiler evaluates effectful subexpressions first, in
  leftmost-innermost order, and then the remaining *simple* expression in one
  big step.  This file defines:

  * `simple`/`simplelist`, the big-step evaluation of simple expressions
    (`eval_simple_lvalue`/`eval_simple_rvalue`/`eval_simple_list`);
  * left reduction contexts `leftcontext`/`leftcontextlist`, with
    `leftcontext_context`;
  * the strategy's transitions `estep` (18 rules) and `step`, and
    `Cstrategy.semantics`;
  * `context_compose`; safe states (`safe`, `safe_steps`, `star_safe`,
    `plus_safe`, `safe_imm_safe`); the l-value/r-value classification
    `expr_kind` with `lred_kind`, `rred_kind`, `callred_kind`, `context_kind`,
    `imm_safe_kind` and `safe_expr_kind`;
  * `eval_simple_rvalue_steps`/`eval_simple_lvalue_steps`: the big-step
    evaluation of a simple expression is matched by silent steps of the
    nondeterministic semantics (and the `_safe` corollaries).

  The rest of the file is ported in `CCLib.cfrontend.CstrategyInversion`,
  `CCLib.cfrontend.CstrategyDecompose`, `CCLib.cfrontend.CstrategySimulation`,
  `CCLib.cfrontend.CstrategyBackward` (simulation), `CCLib.cfrontend.CstrategyReceptive` (strong
  receptiveness), `CCLib.cfrontend.CstrategyBigstep` and `CCLib.cfrontend.CstrategyBigstepSound`
  (the big-step semantics and its soundness).
-/
import CCLib.cfrontend.Csem

namespace CC
namespace Cstrategy

open Csem

/-! ## Simple expressions -/

/-- `Cstrategy.simple`: expressions without side effects (and without
    volatile reads), whose evaluation always terminates. -/
def simple : Csyntax.Expr → Bool
  | .Eloc _ _ _ _ => true
  | .Evar _ _ => true
  | .Ederef r _ => simple r
  | .Efield r _ _ => simple r
  | .Eval _ _ => true
  | .Evalof l _ => simple l && !(typeIsVolatile (Csyntax.typeof l))
  | .Eaddrof l _ => simple l
  | .Eunop _ r1 _ => simple r1
  | .Ebinop _ r1 r2 _ => simple r1 && simple r2
  | .Ecast r1 _ => simple r1
  | .Eseqand _ _ _ => false
  | .Eseqor _ _ _ => false
  | .Econdition _ _ _ _ => false
  | .Esizeof _ _ => true
  | .Ealignof _ _ => true
  | .Eassign _ _ _ => false
  | .Eassignop _ _ _ _ _ => false
  | .Epostincr _ _ _ => false
  | .Ecomma _ _ _ => false
  | .Ecall _ _ _ => false
  | .Ebuiltin _ _ _ _ => false
  | .Eparen _ _ _ => false

/-- `Cstrategy.simplelist` -/
def simplelist : Csyntax.ExprList → Bool
  | .Enil => true
  | .Econs r rl' => simple r && simplelist rl'

section SIMPLE_EXPRS

variable (ge : Csem.CGenv) (e : Env) (m : Mem)

mutual
/-- `Cstrategy.eval_simple_lvalue` -/
inductive EvalSimpleLvalue : Csyntax.Expr → Block → Integers.Ptrofs → Bitfield → Prop where
  | loc (b ofs ty bf) : EvalSimpleLvalue (.Eloc b ofs bf ty) b ofs bf
  | var_local (x ty b) :
      e.get x = some (b, ty) →
      EvalSimpleLvalue (.Evar x ty) b Integers.Ptrofs.zero .Full
  | var_global (x ty b) :
      e.get x = none →
      Genv.findSymbol ge.genv_genv x = some b →
      EvalSimpleLvalue (.Evar x ty) b Integers.Ptrofs.zero .Full
  | deref (r ty b ofs) :
      EvalSimpleRvalue r (.Vptr b ofs) →
      EvalSimpleLvalue (.Ederef r ty) b ofs .Full
  | field_struct (r f ty b ofs id co a delta bf) :
      EvalSimpleRvalue r (.Vptr b ofs) →
      Csyntax.typeof r = .Tstruct id a →
      ge.genv_cenv.get id = some co →
      fieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      EvalSimpleLvalue (.Efield r f ty) b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf
  | field_union (r f ty b ofs id co a delta bf) :
      EvalSimpleRvalue r (.Vptr b ofs) →
      Csyntax.typeof r = .Tunion id a →
      unionFieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      ge.genv_cenv.get id = some co →
      EvalSimpleLvalue (.Efield r f ty) b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf

/-- `Cstrategy.eval_simple_rvalue` -/
inductive EvalSimpleRvalue : Csyntax.Expr → Val → Prop where
  | val (v ty) : EvalSimpleRvalue (.Eval v ty) v
  | rvalof (b ofs bf l ty v) :
      EvalSimpleLvalue l b ofs bf →
      ty = Csyntax.typeof l → typeIsVolatile ty = false →
      Csem.DerefLoc ge ty m b ofs bf E0 v →
      EvalSimpleRvalue (.Evalof l ty) v
  | addrof (b ofs l ty) :
      EvalSimpleLvalue l b ofs .Full →
      EvalSimpleRvalue (.Eaddrof l ty) (.Vptr b ofs)
  | unop (op r1 ty v1 v) :
      EvalSimpleRvalue r1 v1 →
      Cop.semUnaryOperation op v1 (Csyntax.typeof r1) m = some v →
      EvalSimpleRvalue (.Eunop op r1 ty) v
  | binop (op r1 r2 ty v1 v2 v) :
      EvalSimpleRvalue r1 v1 → EvalSimpleRvalue r2 v2 →
      Cop.semBinaryOperation ge.genv_cenv op v1 (Csyntax.typeof r1) v2 (Csyntax.typeof r2) m =
        some v →
      EvalSimpleRvalue (.Ebinop op r1 r2 ty) v
  | cast (ty r1 v1 v) :
      EvalSimpleRvalue r1 v1 →
      Cop.semCast v1 (Csyntax.typeof r1) ty m = some v →
      EvalSimpleRvalue (.Ecast r1 ty) v
  | sizeof (ty1 ty) :
      EvalSimpleRvalue (.Esizeof ty1 ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (sizeof ge.genv_cenv ty1)))
  | alignof (ty1 ty) :
      EvalSimpleRvalue (.Ealignof ty1 ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (alignof ge.genv_cenv ty1)))
end

/-- `Cstrategy.eval_simple_list` -/
inductive EvalSimpleList : Csyntax.ExprList → List Ty → List Val → Prop where
  | nil : EvalSimpleList .Enil [] []
  | cons (r rl ty tyl v vl v') :
      EvalSimpleRvalue ge e m r v' →
      Cop.semCast v' (Csyntax.typeof r) ty m = some v →
      EvalSimpleList rl tyl vl →
      EvalSimpleList (.Econs r rl) (ty :: tyl) (v :: vl)

end SIMPLE_EXPRS

/-! ## Left reduction contexts -/

mutual
/-- `Cstrategy.leftcontext`: reduction may take place to the right of an
    operator only if everything to its left is simple. -/
inductive LeftContext : Csem.Kind → Csem.Kind → (Csyntax.Expr → Csyntax.Expr) → Prop where
  | top (k) : LeftContext k k (fun x => x)
  | deref (k C ty) : LeftContext k .RV C → LeftContext k .LV (fun x => .Ederef (C x) ty)
  | field (k C f ty) : LeftContext k .RV C → LeftContext k .LV (fun x => .Efield (C x) f ty)
  | rvalof (k C ty) : LeftContext k .LV C → LeftContext k .RV (fun x => .Evalof (C x) ty)
  | addrof (k C ty) : LeftContext k .LV C → LeftContext k .RV (fun x => .Eaddrof (C x) ty)
  | unop (k C op ty) : LeftContext k .RV C → LeftContext k .RV (fun x => .Eunop op (C x) ty)
  | binop_left (k C op e2 ty) :
      LeftContext k .RV C → LeftContext k .RV (fun x => .Ebinop op (C x) e2 ty)
  | binop_right (k C op e1 ty) :
      simple e1 = true → LeftContext k .RV C →
      LeftContext k .RV (fun x => .Ebinop op e1 (C x) ty)
  | cast (k C ty) : LeftContext k .RV C → LeftContext k .RV (fun x => .Ecast (C x) ty)
  | seqand (k C r2 ty) :
      LeftContext k .RV C → LeftContext k .RV (fun x => .Eseqand (C x) r2 ty)
  | seqor (k C r2 ty) :
      LeftContext k .RV C → LeftContext k .RV (fun x => .Eseqor (C x) r2 ty)
  | condition (k C r2 r3 ty) :
      LeftContext k .RV C → LeftContext k .RV (fun x => .Econdition (C x) r2 r3 ty)
  | assign_left (k C e2 ty) :
      LeftContext k .LV C → LeftContext k .RV (fun x => .Eassign (C x) e2 ty)
  | assign_right (k C e1 ty) :
      simple e1 = true → LeftContext k .RV C →
      LeftContext k .RV (fun x => .Eassign e1 (C x) ty)
  | assignop_left (k C op e2 tyres ty) :
      LeftContext k .LV C → LeftContext k .RV (fun x => .Eassignop op (C x) e2 tyres ty)
  | assignop_right (k C op e1 tyres ty) :
      simple e1 = true → LeftContext k .RV C →
      LeftContext k .RV (fun x => .Eassignop op e1 (C x) tyres ty)
  | postincr (k C id ty) :
      LeftContext k .LV C → LeftContext k .RV (fun x => .Epostincr id (C x) ty)
  | call_left (k C el ty) :
      LeftContext k .RV C → LeftContext k .RV (fun x => .Ecall (C x) el ty)
  | call_right (k C e1 ty) :
      simple e1 = true → LeftContextList k C →
      LeftContext k .RV (fun x => .Ecall e1 (C x) ty)
  | builtin (k C ef tyargs ty) :
      LeftContextList k C → LeftContext k .RV (fun x => .Ebuiltin ef tyargs (C x) ty)
  | comma (k C e2 ty) :
      LeftContext k .RV C → LeftContext k .RV (fun x => .Ecomma (C x) e2 ty)
  | paren (k C tycast ty) :
      LeftContext k .RV C → LeftContext k .RV (fun x => .Eparen (C x) tycast ty)

/-- `Cstrategy.leftcontextlist` -/
inductive LeftContextList : Csem.Kind → (Csyntax.Expr → Csyntax.ExprList) → Prop where
  | head (k C el) : LeftContext k .RV C → LeftContextList k (fun x => .Econs (C x) el)
  | tail (k C e1) :
      simple e1 = true → LeftContextList k C → LeftContextList k (fun x => .Econs e1 (C x))
end

mutual
/-- `Cstrategy.leftcontext_context`: left contexts are reduction contexts. -/
theorem leftcontext_context {k1} : ∀ {k2 C}, LeftContext k1 k2 C → Csem.Context k1 k2 C
  | _, _, .top _ => .top _
  | _, _, .deref _ _ _ h => .deref _ _ _ (leftcontext_context h)
  | _, _, .field _ _ _ _ h => .field _ _ _ _ (leftcontext_context h)
  | _, _, .rvalof _ _ _ h => .rvalof _ _ _ (leftcontext_context h)
  | _, _, .addrof _ _ _ h => .addrof _ _ _ (leftcontext_context h)
  | _, _, .unop _ _ _ _ h => .unop _ _ _ _ (leftcontext_context h)
  | _, _, .binop_left _ _ _ _ _ h => .binop_left _ _ _ _ _ (leftcontext_context h)
  | _, _, .binop_right _ _ _ _ _ _ h => .binop_right _ _ _ _ _ (leftcontext_context h)
  | _, _, .cast _ _ _ h => .cast _ _ _ (leftcontext_context h)
  | _, _, .seqand _ _ _ _ h => .seqand _ _ _ _ (leftcontext_context h)
  | _, _, .seqor _ _ _ _ h => .seqor _ _ _ _ (leftcontext_context h)
  | _, _, .condition _ _ _ _ _ h => .condition _ _ _ _ _ (leftcontext_context h)
  | _, _, .assign_left _ _ _ _ h => .assign_left _ _ _ _ (leftcontext_context h)
  | _, _, .assign_right _ _ _ _ _ h => .assign_right _ _ _ _ (leftcontext_context h)
  | _, _, .assignop_left _ _ _ _ _ _ h => .assignop_left _ _ _ _ _ _ (leftcontext_context h)
  | _, _, .assignop_right _ _ _ _ _ _ _ h =>
      .assignop_right _ _ _ _ _ _ (leftcontext_context h)
  | _, _, .postincr _ _ _ _ h => .postincr _ _ _ _ (leftcontext_context h)
  | _, _, .call_left _ _ _ _ h => .call_left _ _ _ _ (leftcontext_context h)
  | _, _, .call_right _ _ _ _ _ h => .call_right _ _ _ _ (leftcontextlist_contextlist h)
  | _, _, .builtin _ _ _ _ _ h => .builtin _ _ _ _ _ (leftcontextlist_contextlist h)
  | _, _, .comma _ _ _ _ h => .comma _ _ _ _ (leftcontext_context h)
  | _, _, .paren _ _ _ _ h => .paren _ _ _ _ (leftcontext_context h)

/-- `Cstrategy.leftcontextlist_contextlist` -/
theorem leftcontextlist_contextlist {k} : ∀ {C}, LeftContextList k C → Csem.ContextList k C
  | _, .head _ _ _ h => .head _ _ _ (leftcontext_context h)
  | _, .tail _ _ _ _ h => .tail _ _ _ (leftcontextlist_contextlist h)
end

/-! ## The strategy -/

section STRATEGY

variable (ge : Csem.CGenv)

/-- `Cstrategy.estep`: reduce the leftmost-innermost non-simple subexpression,
    evaluating its (simple) arguments in one big step; if the whole expression
    is simple, evaluate it in one big step. -/
inductive Estep : Csem.State → Trace → Csem.State → Prop where
  | expr (f r k e m v ty) :
      EvalSimpleRvalue ge e m r v →
      (match r with | .Eval _ _ => False | _ => True) →
      ty = Csyntax.typeof r →
      Estep (.ExprState f r k e m) E0 (.ExprState f (.Eval v ty) k e m)
  | rvalof_volatile (f C l ty k e m b ofs bf t v) :
      LeftContext .RV .RV C →
      EvalSimpleLvalue ge e m l b ofs bf →
      Csem.DerefLoc ge ty m b ofs bf t v →
      ty = Csyntax.typeof l → typeIsVolatile ty = true →
      Estep (.ExprState f (C (.Evalof l ty)) k e m) t (.ExprState f (C (.Eval v ty)) k e m)
  | seqand_true (f C r1 r2 ty k e m v) :
      LeftContext .RV .RV C →
      EvalSimpleRvalue ge e m r1 v →
      Cop.boolVal v (Csyntax.typeof r1) m = some true →
      Estep (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eparen r2 type_bool ty)) k e m)
  | seqand_false (f C r1 r2 ty k e m v) :
      LeftContext .RV .RV C →
      EvalSimpleRvalue ge e m r1 v →
      Cop.boolVal v (Csyntax.typeof r1) m = some false →
      Estep (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eval (.Vint Integers.Int.zero) ty)) k e m)
  | seqor_true (f C r1 r2 ty k e m v) :
      LeftContext .RV .RV C →
      EvalSimpleRvalue ge e m r1 v →
      Cop.boolVal v (Csyntax.typeof r1) m = some true →
      Estep (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eval (.Vint Integers.Int.one) ty)) k e m)
  | seqor_false (f C r1 r2 ty k e m v) :
      LeftContext .RV .RV C →
      EvalSimpleRvalue ge e m r1 v →
      Cop.boolVal v (Csyntax.typeof r1) m = some false →
      Estep (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
        (.ExprState f (C (.Eparen r2 type_bool ty)) k e m)
  | condition (f C r1 r2 r3 ty k e m v b) :
      LeftContext .RV .RV C →
      EvalSimpleRvalue ge e m r1 v →
      Cop.boolVal v (Csyntax.typeof r1) m = some b →
      Estep (.ExprState f (C (.Econdition r1 r2 r3 ty)) k e m) E0
        (.ExprState f (C (.Eparen (if b then r2 else r3) ty ty)) k e m)
  | assign (f C l r ty k e m b ofs bf v v1 t m' v') :
      LeftContext .RV .RV C →
      EvalSimpleLvalue ge e m l b ofs bf →
      EvalSimpleRvalue ge e m r v →
      Cop.semCast v (Csyntax.typeof r) (Csyntax.typeof l) m = some v1 →
      Csem.AssignLoc ge (Csyntax.typeof l) m b ofs bf v1 t m' v' →
      ty = Csyntax.typeof l →
      Estep (.ExprState f (C (.Eassign l r ty)) k e m) t (.ExprState f (C (.Eval v' ty)) k e m')
  | assignop (f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1 t2 m' v' t) :
      LeftContext .RV .RV C →
      EvalSimpleLvalue ge e m l b ofs bf →
      Csem.DerefLoc ge (Csyntax.typeof l) m b ofs bf t1 v1 →
      EvalSimpleRvalue ge e m r v2 →
      Cop.semBinaryOperation ge.genv_cenv op v1 (Csyntax.typeof l) v2 (Csyntax.typeof r) m =
        some v3 →
      Cop.semCast v3 tyres (Csyntax.typeof l) m = some v4 →
      Csem.AssignLoc ge (Csyntax.typeof l) m b ofs bf v4 t2 m' v' →
      ty = Csyntax.typeof l →
      t = Eapp t1 t2 →
      Estep (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t
        (.ExprState f (C (.Eval v' ty)) k e m')
  | assignop_stuck (f C op l r tyres ty k e m b ofs bf v1 v2 t) :
      LeftContext .RV .RV C →
      EvalSimpleLvalue ge e m l b ofs bf →
      Csem.DerefLoc ge (Csyntax.typeof l) m b ofs bf t v1 →
      EvalSimpleRvalue ge e m r v2 →
      (match Cop.semBinaryOperation ge.genv_cenv op v1 (Csyntax.typeof l) v2
          (Csyntax.typeof r) m with
       | none => True
       | some v3 =>
          match Cop.semCast v3 tyres (Csyntax.typeof l) m with
          | none => True
          | some v4 => ∀ t2 m' v', ¬ Csem.AssignLoc ge (Csyntax.typeof l) m b ofs bf v4 t2 m' v') →
      ty = Csyntax.typeof l →
      Estep (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t .Stuckstate
  | postincr (f C id l ty k e m b ofs bf v1 v2 v3 t1 t2 m' v' t) :
      LeftContext .RV .RV C →
      EvalSimpleLvalue ge e m l b ofs bf →
      Csem.DerefLoc ge ty m b ofs bf t1 v1 →
      Cop.semIncrdecr ge.genv_cenv id v1 ty m = some v2 →
      Cop.semCast v2 (Cop.incrdecrType ty) ty m = some v3 →
      Csem.AssignLoc ge ty m b ofs bf v3 t2 m' v' →
      ty = Csyntax.typeof l →
      t = Eapp t1 t2 →
      Estep (.ExprState f (C (.Epostincr id l ty)) k e m) t
        (.ExprState f (C (.Eval v1 ty)) k e m')
  | postincr_stuck (f C id l ty k e m b ofs bf v1 t) :
      LeftContext .RV .RV C →
      EvalSimpleLvalue ge e m l b ofs bf →
      Csem.DerefLoc ge ty m b ofs bf t v1 →
      (match Cop.semIncrdecr ge.genv_cenv id v1 ty m with
       | none => True
       | some v2 =>
          match Cop.semCast v2 (Cop.incrdecrType ty) ty m with
          | none => True
          | some v3 => ∀ t2 m' v', ¬ Csem.AssignLoc ge (Csyntax.typeof l) m b ofs bf v3 t2 m' v') →
      ty = Csyntax.typeof l →
      Estep (.ExprState f (C (.Epostincr id l ty)) k e m) t .Stuckstate
  | comma (f C r1 r2 ty k e m v) :
      LeftContext .RV .RV C →
      EvalSimpleRvalue ge e m r1 v →
      ty = Csyntax.typeof r2 →
      Estep (.ExprState f (C (.Ecomma r1 r2 ty)) k e m) E0 (.ExprState f (C r2) k e m)
  | paren (f C r tycast ty k e m v1 v) :
      LeftContext .RV .RV C →
      EvalSimpleRvalue ge e m r v1 →
      Cop.semCast v1 (Csyntax.typeof r) tycast m = some v →
      Estep (.ExprState f (C (.Eparen r tycast ty)) k e m) E0
        (.ExprState f (C (.Eval v ty)) k e m)
  | call (f C rf rargs ty k e m targs tres cconv vf vargs fd) :
      LeftContext .RV .RV C →
      Cop.classifyFun (Csyntax.typeof rf) = .f targs tres cconv →
      EvalSimpleRvalue ge e m rf vf →
      EvalSimpleList ge e m rargs targs vargs →
      Genv.findFunct ge.genv_genv vf = some fd →
      Csyntax.typeOfFundef fd = .Tfunction targs tres cconv →
      Estep (.ExprState f (C (.Ecall rf rargs ty)) k e m) E0
        (.Callstate fd vargs (.Kcall f e C ty k) m)
  | builtin (f C ef tyargs rargs ty k e m vargs t vres m') :
      LeftContext .RV .RV C →
      EvalSimpleList ge e m rargs tyargs vargs →
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      Estep (.ExprState f (C (.Ebuiltin ef tyargs rargs ty)) k e m) t
        (.ExprState f (C (.Eval vres ty)) k e m')

/-- `Cstrategy.step` -/
def Step (S : Csem.State) (t : Trace) (S' : Csem.State) : Prop :=
  Estep ge S t S' ∨ Csem.Sstep ge S t S'

end STRATEGY

/-! ## Properties of contexts -/

mutual
/-- `Cstrategy.context_compose` (with the inner context `C1` as first argument). -/
theorem context_compose {k1 k2 C1} (h1 : Csem.Context k1 k2 C1) :
    ∀ {k3 C2}, Csem.Context k2 k3 C2 → Csem.Context k1 k3 (fun x => C2 (C1 x))
  | _, _, .top _ => h1
  | _, _, .deref _ _ _ h => .deref _ _ _ (context_compose h1 h)
  | _, _, .field _ _ _ _ h => .field _ _ _ _ (context_compose h1 h)
  | _, _, .rvalof _ _ _ h => .rvalof _ _ _ (context_compose h1 h)
  | _, _, .addrof _ _ _ h => .addrof _ _ _ (context_compose h1 h)
  | _, _, .unop _ _ _ _ h => .unop _ _ _ _ (context_compose h1 h)
  | _, _, .binop_left _ _ _ _ _ h => .binop_left _ _ _ _ _ (context_compose h1 h)
  | _, _, .binop_right _ _ _ _ _ h => .binop_right _ _ _ _ _ (context_compose h1 h)
  | _, _, .cast _ _ _ h => .cast _ _ _ (context_compose h1 h)
  | _, _, .seqand _ _ _ _ h => .seqand _ _ _ _ (context_compose h1 h)
  | _, _, .seqor _ _ _ _ h => .seqor _ _ _ _ (context_compose h1 h)
  | _, _, .condition _ _ _ _ _ h => .condition _ _ _ _ _ (context_compose h1 h)
  | _, _, .assign_left _ _ _ _ h => .assign_left _ _ _ _ (context_compose h1 h)
  | _, _, .assign_right _ _ _ _ h => .assign_right _ _ _ _ (context_compose h1 h)
  | _, _, .assignop_left _ _ _ _ _ _ h => .assignop_left _ _ _ _ _ _ (context_compose h1 h)
  | _, _, .assignop_right _ _ _ _ _ _ h => .assignop_right _ _ _ _ _ _ (context_compose h1 h)
  | _, _, .postincr _ _ _ _ h => .postincr _ _ _ _ (context_compose h1 h)
  | _, _, .call_left _ _ _ _ h => .call_left _ _ _ _ (context_compose h1 h)
  | _, _, .call_right _ _ _ _ h => .call_right _ _ _ _ (contextlist_compose h1 h)
  | _, _, .builtin _ _ _ _ _ h => .builtin _ _ _ _ _ (contextlist_compose h1 h)
  | _, _, .comma _ _ _ _ h => .comma _ _ _ _ (context_compose h1 h)
  | _, _, .paren _ _ _ _ h => .paren _ _ _ _ (context_compose h1 h)

/-- `Cstrategy.contextlist_compose` -/
theorem contextlist_compose {k1 k2 C1} (h1 : Csem.Context k1 k2 C1) :
    ∀ {C2}, Csem.ContextList k2 C2 → Csem.ContextList k1 (fun x => C2 (C1 x))
  | _, .head _ _ _ h => .head _ _ _ (context_compose h1 h)
  | _, .tail _ _ _ h => .tail _ _ _ (contextlist_compose h1 h)
end

/-! ## Safe executions -/

section SAFE

variable (ge : Csem.CGenv)

/-- `Cstrategy.safe`: a state of the nondeterministic semantics that cannot get
    stuck by silent transitions. -/
def Safe (s : Csem.State) : Prop :=
  ∀ s', Smallstep.Star (Csem.Step ge) s E0 s' →
    (∃ r, Csem.FinalState s' r) ∨ (∃ t s'', Csem.Step ge s' t s'')

variable {ge}

/-- `Cstrategy.safe_steps` -/
theorem safe_steps {s s'} (hs : Safe ge s) (h : Smallstep.Star (Csem.Step ge) s E0 s') :
    Safe ge s' :=
  fun s'' h' => hs s'' (Smallstep.star_trans h h' rfl)

/-- `Cstrategy.star_safe` -/
theorem star_safe {s1 s2 t s3} (hs : Safe ge s1) (h1 : Smallstep.Star (Csem.Step ge) s1 E0 s2)
    (h2 : Safe ge s2 → Smallstep.Star (Csem.Step ge) s2 t s3) :
    Smallstep.Star (Csem.Step ge) s1 t s3 :=
  Smallstep.star_trans h1 (h2 (safe_steps hs h1)) rfl

/-- `Cstrategy.plus_safe` -/
theorem plus_safe {s1 s2 t s3} (hs : Safe ge s1) (h1 : Smallstep.Star (Csem.Step ge) s1 E0 s2)
    (h2 : Safe ge s2 → Smallstep.Plus (Csem.Step ge) s2 t s3) :
    Smallstep.Plus (Csem.Step ge) s1 t s3 :=
  Smallstep.star_plus_trans h1 (h2 (safe_steps hs h1)) rfl

/-- `Cstrategy.safe_imm_safe`: in a safe expression state, the subexpression at
    any reduction context is immediately safe. -/
theorem safe_imm_safe {f C a k e m K} (hs : Safe ge (.ExprState f (C a) k e m))
    (hC : Csem.Context K .RV C) : Csem.ImmSafe ge e K a m := by
  refine Classical.byContradiction fun hn => ?_
  rcases hs .Stuckstate (Smallstep.star_one (.inl (.stuck C f a k e m K hC hn))) with
    ⟨r, hr⟩ | ⟨t, s'', hst⟩
  · cases hr
  · rcases hst with h | h <;> cases h

end SAFE

/-! ## L-values and r-values -/

/-- `Cstrategy.expr_kind` -/
def exprKind : Csyntax.Expr → Csem.Kind
  | .Eloc _ _ _ _ => .LV
  | .Evar _ _ => .LV
  | .Ederef _ _ => .LV
  | .Efield _ _ _ => .LV
  | _ => .RV

/-- `Cstrategy.lred_kind` -/
theorem lred_kind {ge : Csem.CGenv} {e a m a' m'} (h : Csem.Lred ge e a m a' m') : exprKind a = .LV := by
  cases h <;> rfl

/-- `Cstrategy.rred_kind` -/
theorem rred_kind {ge : Csem.CGenv} {a m t a' m'} (h : Csem.Rred ge a m t a' m') : exprKind a = .RV := by
  cases h <;> rfl

/-- `Cstrategy.callred_kind` -/
theorem callred_kind {ge : Csem.CGenv} {a m fd args ty} (h : Csem.Callred ge a m fd args ty) :
    exprKind a = .RV := by
  cases h; rfl

/-- `Cstrategy.context_kind` -/
theorem context_kind {a from_ to C} (h : Csem.Context from_ to C) (ha : exprKind a = from_) :
    exprKind (C a) = to := by
  cases h <;> first | exact ha | rfl

/-- `Cstrategy.imm_safe_kind` -/
theorem imm_safe_kind {ge : Csem.CGenv} {e k a m} (h : Csem.ImmSafe ge e k a m) : exprKind a = k := by
  cases h with
  | val => rfl
  | loc => rfl
  | lred _ _ _ _ _ _ hl hC => exact context_kind hC (lred_kind hl)
  | rred _ _ _ _ _ _ _ hr hC => exact context_kind hC (rred_kind hr)
  | callred _ _ _ _ _ _ _ hc hC => exact context_kind hC (callred_kind hc)

/-- `Cstrategy.safe_expr_kind` -/
theorem safe_expr_kind {ge : Csem.CGenv} {from_ C f a k e m} (hC : Csem.Context from_ .RV C)
    (hs : Safe ge (.ExprState f (C a) k e m)) : exprKind a = from_ :=
  imm_safe_kind (safe_imm_safe hs hC)

/-! ## Simple expressions evaluate by silent steps -/

section SIMPLE_EVAL
variable {ge : Csem.CGenv} {f : Csyntax.Function} {k : Csem.Cont} {e : Env} {m : Mem}

mutual
/-- `Cstrategy.eval_simple_rvalue_steps`: the big-step evaluation of a simple
    r-value is matched by silent steps of the nondeterministic semantics. -/
theorem eval_simple_rvalue_steps :
    ∀ {a v}, EvalSimpleRvalue ge e m a v → ∀ {C}, Csem.Context .RV .RV C →
    Smallstep.Star (Csem.Step ge) (.ExprState f (C a) k e m) E0
      (.ExprState f (C (.Eval v (Csyntax.typeof a))) k e m)
  | _, _, .val _ _, _, _ => .refl _
  | _, _, .rvalof b ofs bf l ty v hl hty _ hd, C, hC => by
    subst hty
    exact Smallstep.star_trans
      (eval_simple_lvalue_steps hl (C := fun x => C (.Evalof x (Csyntax.typeof l)))
        (context_compose (.rvalof _ _ _ (.top _)) hC))
      (Smallstep.star_one (.inl (.rred C f _ k e m _ _ m (.rvalof _ _ _ _ _ _ _ hd) hC))) rfl
  | _, _, .addrof b ofs l ty hl, C, hC =>
    Smallstep.star_trans
      (eval_simple_lvalue_steps hl (C := fun x => C (.Eaddrof x ty))
        (context_compose (.addrof _ _ _ (.top _)) hC))
      (Smallstep.star_one (.inl (.rred C f _ k e m _ _ m (.addrof _ _ _ _ _) hC))) rfl
  | _, _, .unop op r1 ty v1 v h1 hv, C, hC =>
    Smallstep.star_trans
      (eval_simple_rvalue_steps h1 (C := fun x => C (.Eunop op x ty))
        (context_compose (.unop _ _ _ _ (.top _)) hC))
      (Smallstep.star_one (.inl (.rred C f _ k e m _ _ m (.unop _ _ _ _ _ _ hv) hC))) rfl
  | _, _, .binop op r1 r2 ty v1 v2 v h1 h2 hv, C, hC =>
    Smallstep.star_trans
      (eval_simple_rvalue_steps h1 (C := fun x => C (.Ebinop op x r2 ty))
        (context_compose (.binop_left _ _ _ _ _ (.top _)) hC))
      (Smallstep.star_trans
        (eval_simple_rvalue_steps h2
          (C := fun x => C (.Ebinop op (.Eval v1 (Csyntax.typeof r1)) x ty))
          (context_compose (.binop_right _ _ _ _ _ (.top _)) hC))
        (Smallstep.star_one (.inl (.rred C f _ k e m _ _ m (.binop _ _ _ _ _ _ _ _ hv) hC))) rfl) rfl
  | _, _, .cast ty r1 v1 v h1 hv, C, hC =>
    Smallstep.star_trans
      (eval_simple_rvalue_steps h1 (C := fun x => C (.Ecast x ty))
        (context_compose (.cast _ _ _ (.top _)) hC))
      (Smallstep.star_one (.inl (.rred C f _ k e m _ _ m (.cast _ _ _ _ _ hv) hC))) rfl
  | _, _, .sizeof ty1 ty, C, hC =>
    Smallstep.star_one (.inl (.rred C f _ k e m _ _ m (.sizeof _ _ _) hC))
  | _, _, .alignof ty1 ty, C, hC =>
    Smallstep.star_one (.inl (.rred C f _ k e m _ _ m (.alignof _ _ _) hC))

/-- `Cstrategy.eval_simple_lvalue_steps` -/
theorem eval_simple_lvalue_steps :
    ∀ {a b ofs bf}, EvalSimpleLvalue ge e m a b ofs bf → ∀ {C}, Csem.Context .LV .RV C →
    Smallstep.Star (Csem.Step ge) (.ExprState f (C a) k e m) E0
      (.ExprState f (C (.Eloc b ofs bf (Csyntax.typeof a))) k e m)
  | _, _, _, _, .loc _ _ _ _, _, _ => .refl _
  | _, _, _, _, .var_local x ty b hx, C, hC =>
    Smallstep.star_one (.inl (.lred C f _ k e m _ m (.var_local _ _ _ _ hx) hC))
  | _, _, _, _, .var_global x ty b hx hs, C, hC =>
    Smallstep.star_one (.inl (.lred C f _ k e m _ m (.var_global _ _ _ _ hx hs) hC))
  | _, _, _, _, .deref r ty b ofs h, C, hC =>
    Smallstep.star_trans
      (eval_simple_rvalue_steps h (C := fun x => C (.Ederef x ty))
        (context_compose (.deref _ _ _ (.top _)) hC))
      (Smallstep.star_one (.inl (.lred C f _ k e m _ m (.deref _ _ _ _ _) hC))) rfl
  | _, _, _, _, .field_struct r fl ty b ofs id co a delta bf h hty hco hfo, C, hC => by
    refine Smallstep.star_trans
      (eval_simple_rvalue_steps h (C := fun x => C (.Efield x fl ty))
        (context_compose (.field _ _ _ _ (.top _)) hC)) ?_ rfl
    rw [hty]
    exact Smallstep.star_one (.inl (.lred C f _ k e m _ m (.field_struct _ _ _ _ _ _ _ _ _ _ hco hfo) hC))
  | _, _, _, _, .field_union r fl ty b ofs id co a delta bf h hty hfo hco, C, hC => by
    refine Smallstep.star_trans
      (eval_simple_rvalue_steps h (C := fun x => C (.Efield x fl ty))
        (context_compose (.field _ _ _ _ (.top _)) hC)) ?_ rfl
    rw [hty]
    exact Smallstep.star_one (.inl (.lred C f _ k e m _ m (.field_union _ _ _ _ _ _ _ _ _ _ hco hfo) hC))
end


/-- `Cstrategy.eval_simple_rvalue_safe` -/
theorem eval_simple_rvalue_safe {C a v} (h : EvalSimpleRvalue ge e m a v)
    (hC : Csem.Context .RV .RV C) (hs : Safe ge (.ExprState f (C a) k e m)) :
    Safe ge (.ExprState f (C (.Eval v (Csyntax.typeof a))) k e m) :=
  safe_steps hs (eval_simple_rvalue_steps h hC)

/-- `Cstrategy.eval_simple_lvalue_safe` -/
theorem eval_simple_lvalue_safe {C a b ofs bf} (h : EvalSimpleLvalue ge e m a b ofs bf)
    (hC : Csem.Context .LV .RV C) (hs : Safe ge (.ExprState f (C a) k e m)) :
    Safe ge (.ExprState f (C (.Eloc b ofs bf (Csyntax.typeof a))) k e m) :=
  safe_steps hs (eval_simple_lvalue_steps h hC)

end SIMPLE_EVAL

/-! ## The strategy as a semantics -/

/-- `Cstrategy.semantics`: CompCert C executed with the compiler's evaluation
    order. -/
def semantics (p : Csyntax.Program) : Smallstep.Semantics where
  state := Csem.State
  step := Step (Csem.globalenv p)
  initial_state := Csem.InitialState p
  final_state := Csem.FinalState
  symbolenv := Genv.toSenv (Csem.globalenv p).genv_genv

end Cstrategy
end CC
