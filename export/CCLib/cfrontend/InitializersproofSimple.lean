/-
  Correctness of the compile-time evaluation of constant expressions — port
  of the first part of `cfrontend/Initializersproof.v` (up to
  `constval_steps`):

  * `Simple`: expressions without assignments or calls;
  * a big-step semantics `EvalSimpleLvalue`/`EvalSimpleRvalue` for simple
    expressions (as in Rocq, it is separate from the one of `Cstrategy`: it
    also covers conditionals, comma and parenthesized expressions);
  * `eval_simple_steps`: if a simple expression reduces to a value by steps of
    the CompCert C semantics, it evaluates to this value;
  * `constval_rvalue`/`constval_lvalue`, `constval_steps`: the value computed
    by `constval` is related, by the injection `inj` that maps a global's
    identifier to its block, to the value computed at run time.
-/
import CCLib.cfrontend.Initializers
import CCLib.cfrontend.Csem
import CCLib.cfrontend.CopInject

namespace CC
namespace Initializersproof

open Csyntax

/-- `Initializersproof.simple`: the expression contains no assignments and no
    function calls. -/
def Simple : Csyntax.Expr → Prop
  | .Eloc _ _ _ _ => True
  | .Evar _ _ => True
  | .Ederef r _ => Simple r
  | .Efield l1 _ _ => Simple l1
  | .Eval _ _ => True
  | .Evalof l _ => Simple l
  | .Eaddrof l _ => Simple l
  | .Eunop _ r1 _ => Simple r1
  | .Ebinop _ r1 r2 _ => Simple r1 ∧ Simple r2
  | .Ecast r1 _ => Simple r1
  | .Eseqand r1 r2 _ => Simple r1 ∧ Simple r2
  | .Eseqor r1 r2 _ => Simple r1 ∧ Simple r2
  | .Econdition r1 r2 r3 _ => Simple r1 ∧ Simple r2 ∧ Simple r3
  | .Esizeof _ _ => True
  | .Ealignof _ _ => True
  | .Eassign _ _ _ => False
  | .Eassignop _ _ _ _ _ => False
  | .Epostincr _ _ _ => False
  | .Ecomma r1 r2 _ => Simple r1 ∧ Simple r2
  | .Ecall _ _ _ => False
  | .Ebuiltin _ _ _ _ => False
  | .Eparen r1 _ _ => Simple r1

section SIMPLE_EXPRS

variable (ge : Csem.CGenv) (e : Env) (m : Mem)

mutual
/-- `Initializersproof.eval_simple_lvalue` -/
inductive EvalSimpleLvalue : Csyntax.Expr → Block → Integers.Ptrofs → Bitfield → Prop where
  | loc (b ofs bf ty) : EvalSimpleLvalue (.Eloc b ofs bf ty) b ofs bf
  | var_local (x ty b) :
      e.get x = some (b, ty) → EvalSimpleLvalue (.Evar x ty) b Integers.Ptrofs.zero .Full
  | var_global (x ty b) :
      e.get x = none → Genv.findSymbol ge.genv_genv x = some b →
      EvalSimpleLvalue (.Evar x ty) b Integers.Ptrofs.zero .Full
  | deref (r ty b ofs) :
      EvalSimpleRvalue r (.Vptr b ofs) → EvalSimpleLvalue (.Ederef r ty) b ofs .Full
  | field_struct (r f ty b ofs id co a delta bf) :
      EvalSimpleRvalue r (.Vptr b ofs) →
      Csyntax.typeof r = .Tstruct id a → ge.genv_cenv.get id = some co →
      fieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      EvalSimpleLvalue (.Efield r f ty) b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf
  | field_union (r f ty b ofs id co a delta bf) :
      EvalSimpleRvalue r (.Vptr b ofs) →
      Csyntax.typeof r = .Tunion id a → ge.genv_cenv.get id = some co →
      unionFieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf) →
      EvalSimpleLvalue (.Efield r f ty) b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf

/-- `Initializersproof.eval_simple_rvalue` -/
inductive EvalSimpleRvalue : Csyntax.Expr → Val → Prop where
  | val (v ty) : EvalSimpleRvalue (.Eval v ty) v
  | rvalof (b ofs bf l ty v) :
      EvalSimpleLvalue l b ofs bf → ty = Csyntax.typeof l →
      Csem.DerefLoc ge ty m b ofs bf E0 v → EvalSimpleRvalue (.Evalof l ty) v
  | addrof (b ofs l ty) :
      EvalSimpleLvalue l b ofs .Full → EvalSimpleRvalue (.Eaddrof l ty) (.Vptr b ofs)
  | unop (op r1 ty v1 v) :
      EvalSimpleRvalue r1 v1 → Cop.semUnaryOperation op v1 (Csyntax.typeof r1) m = some v →
      EvalSimpleRvalue (.Eunop op r1 ty) v
  | binop (op r1 r2 ty v1 v2 v) :
      EvalSimpleRvalue r1 v1 → EvalSimpleRvalue r2 v2 →
      Cop.semBinaryOperation ge.genv_cenv op v1 (Csyntax.typeof r1) v2 (Csyntax.typeof r2) m = some v →
      EvalSimpleRvalue (.Ebinop op r1 r2 ty) v
  | cast (ty r1 v1 v) :
      EvalSimpleRvalue r1 v1 → Cop.semCast v1 (Csyntax.typeof r1) ty m = some v →
      EvalSimpleRvalue (.Ecast r1 ty) v
  | sizeof (ty1 ty) :
      EvalSimpleRvalue (.Esizeof ty1 ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (sizeof ge.genv_cenv ty1)))
  | alignof (ty1 ty) :
      EvalSimpleRvalue (.Ealignof ty1 ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (alignof ge.genv_cenv ty1)))
  | seqand_true (r1 r2 ty v1 v2 v3) :
      EvalSimpleRvalue r1 v1 → Cop.boolVal v1 (Csyntax.typeof r1) m = some true →
      EvalSimpleRvalue r2 v2 → Cop.semCast v2 (Csyntax.typeof r2) type_bool m = some v3 →
      EvalSimpleRvalue (.Eseqand r1 r2 ty) v3
  | seqand_false (r1 r2 ty v1) :
      EvalSimpleRvalue r1 v1 → Cop.boolVal v1 (Csyntax.typeof r1) m = some false →
      EvalSimpleRvalue (.Eseqand r1 r2 ty) (.Vint Integers.Int.zero)
  | seqor_false (r1 r2 ty v1 v2 v3) :
      EvalSimpleRvalue r1 v1 → Cop.boolVal v1 (Csyntax.typeof r1) m = some false →
      EvalSimpleRvalue r2 v2 → Cop.semCast v2 (Csyntax.typeof r2) type_bool m = some v3 →
      EvalSimpleRvalue (.Eseqor r1 r2 ty) v3
  | seqor_true (r1 r2 ty v1) :
      EvalSimpleRvalue r1 v1 → Cop.boolVal v1 (Csyntax.typeof r1) m = some true →
      EvalSimpleRvalue (.Eseqor r1 r2 ty) (.Vint Integers.Int.one)
  | condition (r1 r2 r3 ty v v1 b v') :
      EvalSimpleRvalue r1 v1 → Cop.boolVal v1 (Csyntax.typeof r1) m = some b →
      EvalSimpleRvalue (if b then r2 else r3) v' →
      Cop.semCast v' (Csyntax.typeof (if b then r2 else r3)) ty m = some v →
      EvalSimpleRvalue (.Econdition r1 r2 r3 ty) v
  | comma (r1 r2 ty v1 v) :
      EvalSimpleRvalue r1 v1 → EvalSimpleRvalue r2 v → EvalSimpleRvalue (.Ecomma r1 r2 ty) v
  | paren (r tycast ty v v') :
      EvalSimpleRvalue r v → Cop.semCast v (Csyntax.typeof r) tycast m = some v' →
      EvalSimpleRvalue (.Eparen r tycast ty) v'
end

end SIMPLE_EXPRS

/-! ## Correctness of the big-step semantics with respect to reduction sequences -/

section COMPAT

variable {ge : Csem.CGenv}

/-- `Initializersproof.compat_eval` -/
def CompatEval (ge : Csem.CGenv) (k : Csem.Kind) (e : Env) (a a' : Csyntax.Expr) (m : Mem) :
    Prop :=
  Csyntax.typeof a = Csyntax.typeof a' ∧
  match k with
  | .LV => ∀ b ofs bf, EvalSimpleLvalue ge e m a' b ofs bf → EvalSimpleLvalue ge e m a b ofs bf
  | .RV => ∀ v, EvalSimpleRvalue ge e m a' v → EvalSimpleRvalue ge e m a v

/-- `Initializersproof.lred_simple` -/
theorem lred_simple {e : Env} {l : Csyntax.Expr} {m : Mem} {l' : Csyntax.Expr} {m' : Mem}
    (h : Csem.Lred ge e l m l' m') (_hs : Simple l) : Simple l' := by
  cases h <;> trivial

/-- `Initializersproof.lred_compat` -/
theorem lred_compat {e : Env} {l : Csyntax.Expr} {m : Mem} {l' : Csyntax.Expr} {m' : Mem}
    (h : Csem.Lred ge e l m l' m') : m = m' ∧ CompatEval ge .LV e l l' m := by
  cases h with
  | var_local x ty m b he =>
    refine ⟨rfl, rfl, fun bx ofsx bf' ev => ?_⟩
    cases ev; exact .var_local _ _ _ he
  | var_global x ty m b he hs =>
    refine ⟨rfl, rfl, fun bx ofsx bf' ev => ?_⟩
    cases ev; exact .var_global _ _ _ he hs
  | deref b ofs ty1 ty m =>
    refine ⟨rfl, rfl, fun bx ofsx bf' ev => ?_⟩
    cases ev; exact .deref _ _ _ _ (.val _ _)
  | field_struct b ofs id co a f ty m delta bf hco hf =>
    refine ⟨rfl, rfl, fun bx ofsx bf' ev => ?_⟩
    cases ev; exact .field_struct _ _ _ _ _ _ _ _ _ _ (.val _ _) rfl hco hf
  | field_union b ofs id co a f ty m delta bf hco hf =>
    refine ⟨rfl, rfl, fun bx ofsx bf' ev => ?_⟩
    cases ev; exact .field_union _ _ _ _ _ _ _ _ _ _ (.val _ _) rfl hco hf

/-- `Initializersproof.rred_simple` -/
theorem rred_simple {r : Csyntax.Expr} {m : Mem} {t : Trace} {r' : Csyntax.Expr} {m' : Mem}
    (h : Csem.Rred ge r m t r' m') (hs : Simple r) : Simple r' := by
  cases h <;> (try simp only [Simple] at hs) <;> (try simp only [Simple]) <;> try trivial
  case seqand_true => exact hs.2
  case seqor_false => exact hs.2
  case comma => exact hs.2
  case condition b _ => cases b <;> first | exact hs.2.1 | exact hs.2.2

/-- `Initializersproof.rred_compat` -/
theorem rred_compat {e : Env} {r : Csyntax.Expr} {m : Mem} {r' : Csyntax.Expr} {m' : Mem}
    (h : Csem.Rred ge r m E0 r' m') (hs : Simple r) : m = m' ∧ CompatEval ge .RV e r r' m := by
  cases h with
  | rvalof b ofs bf ty m t v hd =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .rvalof _ _ _ _ _ _ (.loc _ _ _ _) rfl hd
  | addrof b ofs ty1 ty m =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .addrof _ _ _ _ (.loc _ _ _ _)
  | unop op v1 ty1 ty m v hs' =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .unop _ _ _ _ _ (.val _ _) hs'
  | binop op v1 ty1 v2 ty2 ty m v hs' =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .binop _ _ _ _ _ _ _ (.val _ _) (.val _ _) hs'
  | cast ty v1 ty1 m v hs' =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .cast _ _ _ _ (.val _ _) hs'
  | seqand_true v1 ty1 r2 ty m hb =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev with
    | paren _ _ _ _ _ h1 h2 => exact .seqand_true _ _ _ _ _ _ (.val _ _) hb h1 h2
  | seqand_false v1 ty1 r2 ty m hb =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .seqand_false _ _ _ _ (.val _ _) hb
  | seqor_true v1 ty1 r2 ty m hb =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .seqor_true _ _ _ _ (.val _ _) hb
  | seqor_false v1 ty1 r2 ty m hb =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev with
    | paren _ _ _ _ _ h1 h2 => exact .seqor_false _ _ _ _ _ _ (.val _ _) hb h1 h2
  | condition v1 ty1 r1 r2 ty b m hb =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev with
    | paren _ _ _ _ _ h1 h2 => exact .condition _ _ _ _ _ _ _ _ (.val _ _) hb h1 h2
  | sizeof =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .sizeof _ _
  | alignof =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .alignof _ _
  | assign => exact hs.elim
  | assignop => exact hs.elim
  | postincr => exact hs.elim
  | comma v ty1 r2 ty m hty =>
    exact ⟨rfl, hty.symm, fun vx ev => .comma _ _ _ _ _ (.val _ _) ev⟩
  | paren v1 ty1 ty2 ty m v hs' =>
    refine ⟨rfl, rfl, fun vx ev => ?_⟩
    cases ev; exact .paren _ _ _ _ _ (.val _ _) hs'
  | builtin => exact hs.elim

/-- `Initializersproof.compat_eval_context` -/
theorem compat_eval_context {e : Env} {a a' : Csyntax.Expr} {m : Mem} {from_ : Csem.Kind} :
    ∀ {to C}, Csem.Context from_ to C → CompatEval ge from_ e a a' m →
      CompatEval ge to e (C a) (C a') m
  | _, _, .top _, CE => CE
  | _, _, .deref _ _ _ hC, CE => by
      obtain ⟨_, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun b ofs bf ev => ?_⟩
      cases ev with
      | deref _ _ _ _ h => exact .deref _ _ _ _ (EV _ h)
  | _, _, .field _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun b ofs bf ev => ?_⟩
      cases ev with
      | field_struct _ _ _ _ _ _ _ _ _ _ h ht hco hf =>
        exact .field_struct _ _ _ _ _ _ _ _ _ _ (EV _ h) (TY.trans ht) hco hf
      | field_union _ _ _ _ _ _ _ _ _ _ h ht hco hf =>
        exact .field_union _ _ _ _ _ _ _ _ _ _ (EV _ h) (TY.trans ht) hco hf
  | _, _, .rvalof _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | rvalof _ _ _ _ _ _ h hty hd => exact .rvalof _ _ _ _ _ _ (EV _ _ _ h) (hty.trans TY.symm) hd
  | _, _, .addrof _ _ _ hC, CE => by
      obtain ⟨_, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | addrof _ _ _ _ h => exact .addrof _ _ _ _ (EV _ _ _ h)
  | _, _, .unop _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | unop _ _ _ _ _ h1 h2 => exact .unop _ _ _ _ _ (EV _ h1) (by rw [TY]; exact h2)
  | _, _, .binop_left _ _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | binop _ _ _ _ _ _ _ h1 h2 h3 =>
        exact .binop _ _ _ _ _ _ _ (EV _ h1) h2 (by rw [TY]; exact h3)
  | _, _, .binop_right _ _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | binop _ _ _ _ _ _ _ h1 h2 h3 =>
        exact .binop _ _ _ _ _ _ _ h1 (EV _ h2) (by rw [TY]; exact h3)
  | _, _, .cast _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | cast _ _ _ _ h1 h2 => exact .cast _ _ _ _ (EV _ h1) (by rw [TY]; exact h2)
  | _, _, .seqand _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | seqand_true _ _ _ _ _ _ h1 h2 h3 h4 =>
        exact .seqand_true _ _ _ _ _ _ (EV _ h1) (by rw [TY]; exact h2) h3 h4
      | seqand_false _ _ _ _ h1 h2 =>
        exact .seqand_false _ _ _ _ (EV _ h1) (by rw [TY]; exact h2)
  | _, _, .seqor _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | seqor_false _ _ _ _ _ _ h1 h2 h3 h4 =>
        exact .seqor_false _ _ _ _ _ _ (EV _ h1) (by rw [TY]; exact h2) h3 h4
      | seqor_true _ _ _ _ h1 h2 =>
        exact .seqor_true _ _ _ _ (EV _ h1) (by rw [TY]; exact h2)
  | _, _, .condition _ _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | condition _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
        exact .condition _ _ _ _ _ _ _ _ (EV _ h1) (by rw [TY]; exact h2) h3 h4
  | _, _, .assign_left _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .assign_right _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .assignop_left _ _ _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .assignop_right _ _ _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .postincr _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .call_left _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .call_right _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .builtin _ _ _ _ _ _, _ => ⟨rfl, fun _ ev => by cases ev⟩
  | _, _, .comma _ _ _ _ hC, CE => by
      obtain ⟨_, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | comma _ _ _ _ _ h1 h2 => exact .comma _ _ _ _ _ (EV _ h1) h2
  | _, _, .paren _ _ _ _ hC, CE => by
      obtain ⟨TY, EV⟩ := compat_eval_context hC CE
      refine ⟨rfl, fun v ev => ?_⟩
      cases ev with
      | paren _ _ _ _ _ h1 h2 => exact .paren _ _ _ _ _ (EV _ h1) (by rw [TY]; exact h2)

/-- `Initializersproof.simple_context_1` -/
theorem simple_context_1 {a : Csyntax.Expr} {from_ : Csem.Kind} :
    ∀ {to C}, Csem.Context from_ to C → Simple (C a) → Simple a
  | _, _, .top _, h => h
  | _, _, .deref _ _ _ hC, h => simple_context_1 hC h
  | _, _, .field _ _ _ _ hC, h => simple_context_1 hC h
  | _, _, .rvalof _ _ _ hC, h => simple_context_1 hC h
  | _, _, .addrof _ _ _ hC, h => simple_context_1 hC h
  | _, _, .unop _ _ _ _ hC, h => simple_context_1 hC h
  | _, _, .binop_left _ _ _ _ _ hC, h => simple_context_1 hC h.1
  | _, _, .binop_right _ _ _ _ _ hC, h => simple_context_1 hC h.2
  | _, _, .cast _ _ _ hC, h => simple_context_1 hC h
  | _, _, .seqand _ _ _ _ hC, h => simple_context_1 hC h.1
  | _, _, .seqor _ _ _ _ hC, h => simple_context_1 hC h.1
  | _, _, .condition _ _ _ _ _ hC, h => simple_context_1 hC h.1
  | _, _, .assign_left _ _ _ _ _, h => h.elim
  | _, _, .assign_right _ _ _ _ _, h => h.elim
  | _, _, .assignop_left _ _ _ _ _ _ _, h => h.elim
  | _, _, .assignop_right _ _ _ _ _ _ _, h => h.elim
  | _, _, .postincr _ _ _ _ _, h => h.elim
  | _, _, .call_left _ _ _ _ _, h => h.elim
  | _, _, .call_right _ _ _ _ _, h => h.elim
  | _, _, .builtin _ _ _ _ _ _, h => h.elim
  | _, _, .comma _ _ _ _ hC, h => simple_context_1 hC h.1
  | _, _, .paren _ _ _ _ hC, h => simple_context_1 hC h

/-- `Initializersproof.simple_context_2` -/
theorem simple_context_2 {a a' : Csyntax.Expr} (ha' : Simple a') {from_ : Csem.Kind} :
    ∀ {to C}, Csem.Context from_ to C → Simple (C a) → Simple (C a')
  | _, _, .top _, _ => ha'
  | _, _, .deref _ _ _ hC, h => simple_context_2 ha' hC h
  | _, _, .field _ _ _ _ hC, h => simple_context_2 ha' hC h
  | _, _, .rvalof _ _ _ hC, h => simple_context_2 ha' hC h
  | _, _, .addrof _ _ _ hC, h => simple_context_2 ha' hC h
  | _, _, .unop _ _ _ _ hC, h => simple_context_2 ha' hC h
  | _, _, .binop_left _ _ _ _ _ hC, h => ⟨simple_context_2 ha' hC h.1, h.2⟩
  | _, _, .binop_right _ _ _ _ _ hC, h => ⟨h.1, simple_context_2 ha' hC h.2⟩
  | _, _, .cast _ _ _ hC, h => simple_context_2 ha' hC h
  | _, _, .seqand _ _ _ _ hC, h => ⟨simple_context_2 ha' hC h.1, h.2⟩
  | _, _, .seqor _ _ _ _ hC, h => ⟨simple_context_2 ha' hC h.1, h.2⟩
  | _, _, .condition _ _ _ _ _ hC, h => ⟨simple_context_2 ha' hC h.1, h.2⟩
  | _, _, .assign_left _ _ _ _ _, h => h.elim
  | _, _, .assign_right _ _ _ _ _, h => h.elim
  | _, _, .assignop_left _ _ _ _ _ _ _, h => h.elim
  | _, _, .assignop_right _ _ _ _ _ _ _, h => h.elim
  | _, _, .postincr _ _ _ _ _, h => h.elim
  | _, _, .call_left _ _ _ _ _, h => h.elim
  | _, _, .call_right _ _ _ _ _, h => h.elim
  | _, _, .builtin _ _ _ _ _ _, h => h.elim
  | _, _, .comma _ _ _ _ hC, h => ⟨simple_context_2 ha' hC h.1, h.2⟩
  | _, _, .paren _ _ _ _ hC, h => simple_context_2 ha' hC h

/-- `Initializersproof.compat_eval_steps_aux` -/
theorem compat_eval_steps_aux {f : Csyntax.Function} {r : Csyntax.Expr} {e : Env} {m : Mem}
    {r' : Csyntax.Expr} {m' : Mem} {s2 : Csem.State} (hs : Simple r)
    (hstar : Smallstep.Star (Csem.Step ge) s2 E0 (.ExprState f r' .Kstop e m'))
    (hstep : Csem.Estep ge (.ExprState f r .Kstop e m) E0 s2) :
    ∃ r1, s2 = .ExprState f r1 .Kstop e m ∧ CompatEval ge .RV e r r1 m ∧ Simple r1 := by
  cases hstep with
  | lred C _ a _ _ _ a' m'' hl hC =>
    have S := simple_context_1 hC hs
    obtain ⟨rfl, B⟩ := lred_compat hl
    exact ⟨_, rfl, compat_eval_context hC B, simple_context_2 (lred_simple hl S) hC hs⟩
  | rred C _ a _ _ _ _ a' m'' hr hC =>
    have S := simple_context_1 hC hs
    obtain ⟨rfl, B⟩ := rred_compat (e := e) hr S
    exact ⟨_, rfl, compat_eval_context hC B, simple_context_2 (rred_simple hr S) hC hs⟩
  | call C _ a _ _ _ fd vargs ty hc hC =>
    have S := simple_context_1 hC hs
    cases hc; exact S.elim
  | stuck =>
    cases hstar with
    | step h _ _ => rcases h with h | h <;> cases h

/-- `Initializersproof.compat_eval_steps` -/
theorem compat_eval_steps {f : Csyntax.Function} {r : Csyntax.Expr} {e : Env} {m : Mem}
    {r' : Csyntax.Expr} {m' : Mem}
    (h : Smallstep.Star (Csem.Step ge) (.ExprState f r .Kstop e m) E0 (.ExprState f r' .Kstop e m'))
    (hs : Simple r) : m' = m ∧ CompatEval ge .RV e r r' m := by
  generalize hS1 : Csem.State.ExprState f r .Kstop e m = S1 at h
  generalize hS3 : Csem.State.ExprState f r' .Kstop e m' = S3 at h
  generalize ht : (E0 : Trace) = t at h
  induction h generalizing r m with
  | refl =>
    subst hS1; cases hS3; exact ⟨rfl, rfl, fun _ h => h⟩
  | step hstep hrest heq ih =>
    subst hS1 hS3
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp (heq.symm.trans ht.symm)
    rcases hstep with hstep | hstep
    · obtain ⟨r1, rfl, ⟨TY, EV⟩, S1⟩ := compat_eval_steps_aux hs hrest hstep
      obtain ⟨hm, TY2, EV2⟩ := ih S1 rfl rfl rfl
      exact ⟨hm, TY.trans TY2, fun v h => EV v (EV2 v h)⟩
    · cases hstep

/-- `Initializersproof.eval_simple_steps` -/
theorem eval_simple_steps {f : Csyntax.Function} {r : Csyntax.Expr} {e : Env} {m : Mem}
    {v : Val} {ty : Ty} {m' : Mem}
    (h : Smallstep.Star (Csem.Step ge) (.ExprState f r .Kstop e m) E0
      (.ExprState f (.Eval v ty) .Kstop e m'))
    (hs : Simple r) : m' = m ∧ ty = Csyntax.typeof r ∧ EvalSimpleRvalue ge e m r v := by
  obtain ⟨hm, TY, EV⟩ := compat_eval_steps h hs
  exact ⟨hm, TY.symm, EV _ (.val _ _)⟩

end COMPAT


/-! ## Soundness of the compile-time evaluator -/

section SOUNDNESS

variable (ge : Csem.CGenv)

/-- `Initializersproof.inj`: the memory injection mapping the symbolic
    pointer `Vptr id ofs` computed by `constval` to the run-time pointer
    `Vptr b ofs`, where `b` is the block of global `id`. -/
def inj : Val.Meminj := fun b =>
  match Genv.findSymbol ge.genv_genv b with
  | some b' => some (b', 0)
  | none => none

variable {ge}

private theorem res_bind_eq_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

/-- `Initializersproof.mem_empty_not_valid_pointer` -/
theorem mem_empty_not_valid_pointer (b : Block) (ofs : Z) :
    Mem.validPointer Mem.empty b ofs = false := by
  simp [Mem.validPointer, Mem.perm, Mem.empty, PMap.gi]
  rfl

/-- `Initializersproof.mem_empty_not_weak_valid_pointer` -/
theorem mem_empty_not_weak_valid_pointer (b : Block) (ofs : Z) :
    Mem.weakValidPointer Mem.empty b ofs = false := by
  simp [Mem.weakValidPointer, mem_empty_not_valid_pointer]

/-- The injection hypotheses hold trivially from the empty memory. -/
theorem copInjHyps_empty (f : Val.Meminj) (m : Mem) : Cop.CopInjHyps f Mem.empty m where
  valid_pointer_inj := by intros; simp_all [mem_empty_not_valid_pointer]
  weak_valid_pointer_inj := by intros; simp_all [Val.weakValidPtr, mem_empty_not_valid_pointer]
  weak_valid_pointer_no_overflow := by
    intros; simp_all [Val.weakValidPtr, mem_empty_not_valid_pointer]
  valid_different_pointers_inj := by intros; simp_all [mem_empty_not_valid_pointer]

/-- `Initializersproof.sem_cast_match` -/
theorem sem_cast_match {v1 : Val} {ty1 ty2 : Ty} {m : Mem} {v2 v1' v2' : Val}
    (h1 : Cop.semCast v1 ty1 ty2 m = some v2) (h2 : Initializers.doCast v1' ty1 ty2 = .OK v2')
    (hi : Val.Inject (inj ge) v1' v1) : Val.Inject (inj ge) v2' v2 := by
  unfold Initializers.doCast at h2
  cases E : Cop.semCast v1' ty1 ty2 Mem.empty with
  | none => rw [E] at h2; cases h2
  | some v2'' =>
    rw [E] at h2; cases h2
    obtain ⟨tv, A, B⟩ := Cop.semCast_inj (copInjHyps_empty (inj ge) m) E hi
    rw [h1] at A; cases A; exact B

/-- `Initializersproof.bool_val_match` -/
theorem bool_val_match {v : Val} {ty : Ty} {b : Bool} {v' : Val} (m : Mem)
    (h : Cop.boolVal v ty Mem.empty = some b) (hi : Val.Inject (inj ge) v v') :
    Cop.boolVal v' ty m = some b :=
  Cop.boolVal_inj (copInjHyps_empty (inj ge) m) h hi

/-- `Initializersproof.add_offset_match` -/
theorem add_offset_match {v : Val} {b : Block} {ofs : Integers.Ptrofs} {delta : Z}
    (h : Val.Inject (inj ge) v (.Vptr b ofs)) :
    Val.Inject (inj ge)
      (if Archi.ptr64 then Val.addl v (.Vlong (Integers.Int64.repr delta))
       else Val.add v (.Vint (Integers.Int.repr delta)))
      (.Vptr b (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta))) := by
  have hr : Integers.Ptrofs.of_int64 (Integers.Int64.repr delta) = Integers.Ptrofs.repr delta :=
    Integers.MI.repr_unsigned _
  cases h with
  | ptr delta0 hf hofs =>
    subst hofs
    simp only [Archi.ptr64, if_true, Val.addl, hr]
    refine .ptr delta0 hf ?_
    rw [Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_commut (Integers.Ptrofs.repr delta0)]
  | undef => simp [Archi.ptr64, Val.addl]; exact .undef _

private theorem inject_vptrofs (f : Val.Meminj) (n : Integers.Ptrofs) :
    Val.Inject f (Val.Vptrofs n) (Val.Vptrofs n) := by
  unfold Val.Vptrofs; split <;> constructor

mutual
/-- `Initializersproof.constval_rvalue` -/
theorem constval_rvalue {m : Mem} : ∀ {a : Csyntax.Expr} {v : Val},
    EvalSimpleRvalue ge emptyEnv m a v → ∀ v', Initializers.constval ge.genv_cenv a = .OK v' →
      Val.Inject (inj ge) v' v
  | _, _, .val v ty, v', CV => by
      cases v <;> simp only [Initializers.constval] at CV <;> cases CV <;> constructor
  | _, _, .rvalof b ofs bf l ty v hl hty hd, v', CV => by
      have IH := constval_lvalue hl
      have CV' : Initializers.constval ge.genv_cenv l = .OK v' := by
        simp only [Initializers.constval] at CV; split at CV <;> first | exact CV | cases CV
      obtain ⟨rfl, B⟩ := IH _ CV'
      cases hd with
      | value chunk v h1 _ _ => simp only [Initializers.constval, h1] at CV; cases CV
      | volatile chunk t v h1 _ _ => simp only [Initializers.constval, h1] at CV; cases CV
      | reference => exact B
      | copy => exact B
  | _, _, .addrof b ofs l ty hl, v', CV => (constval_lvalue hl _ CV).2
  | _, _, .unop op r1 ty v1 v h1 h2, v', CV => by
      have IH := constval_rvalue h1
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, CV⟩ := CV
      cases E : Cop.semUnaryOperation op x (Csyntax.typeof r1) Mem.empty with
      | none => rw [E] at CV; cases CV
      | some w =>
        rw [E] at CV; cases CV
        obtain ⟨tv, A, B⟩ := Cop.semUnaryOperation_inj (copInjHyps_empty (inj ge) m) E (IH _ hx)
        rw [h2] at A; cases A; exact B
  | _, _, .binop op r1 r2 ty v1 v2 v h1 h2 h3, v', CV => by
      have IH1 := constval_rvalue h1
      have IH2 := constval_rvalue h2
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, y, hy, CV⟩ := CV
      cases E : Cop.semBinaryOperation ge.genv_cenv op x (Csyntax.typeof r1) y (Csyntax.typeof r2)
          Mem.empty with
      | none => rw [E] at CV; cases CV
      | some w =>
        rw [E] at CV; cases CV
        obtain ⟨tv, A, B⟩ :=
          Cop.semBinaryOperation_inj (copInjHyps_empty (inj ge) m) E (IH1 _ hx) (IH2 _ hy)
        rw [h3] at A; cases A; exact B
  | _, _, .cast ty r1 v1 v h1 h2, v', CV => by
      have IH := constval_rvalue h1
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, CV⟩ := CV
      exact sem_cast_match h2 CV (IH _ hx)
  | _, _, .sizeof ty1 ty, v', CV => by
      simp only [Initializers.constval] at CV; cases CV; exact inject_vptrofs _ _
  | _, _, .alignof ty1 ty, v', CV => by
      simp only [Initializers.constval] at CV; cases CV; exact inject_vptrofs _ _
  | _, _, .seqand_true r1 r2 ty v1 v2 v3 h1 hb h2 hc, v', CV => by
      have IH1 := constval_rvalue h1
      have IH2 := constval_rvalue h2
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, y, hy, CV⟩ := CV
      cases E : Cop.boolVal x (Csyntax.typeof r1) Mem.empty with
      | none => rw [E] at CV; cases CV
      | some b =>
        have E' := bool_val_match m E (IH1 _ hx)
        rw [hb] at E'; cases E'
        rw [E] at CV
        exact sem_cast_match hc CV (IH2 _ hy)
  | _, _, .seqand_false r1 r2 ty v1 h1 hb, v', CV => by
      have IH1 := constval_rvalue h1
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, y, hy, CV⟩ := CV
      cases E : Cop.boolVal x (Csyntax.typeof r1) Mem.empty with
      | none => rw [E] at CV; cases CV
      | some b =>
        have E' := bool_val_match m E (IH1 _ hx)
        rw [hb] at E'; cases E'
        rw [E] at CV; cases CV; constructor
  | _, _, .seqor_false r1 r2 ty v1 v2 v3 h1 hb h2 hc, v', CV => by
      have IH1 := constval_rvalue h1
      have IH2 := constval_rvalue h2
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, y, hy, CV⟩ := CV
      cases E : Cop.boolVal x (Csyntax.typeof r1) Mem.empty with
      | none => rw [E] at CV; cases CV
      | some b =>
        have E' := bool_val_match m E (IH1 _ hx)
        rw [hb] at E'; cases E'
        rw [E] at CV
        exact sem_cast_match hc CV (IH2 _ hy)
  | _, _, .seqor_true r1 r2 ty v1 h1 hb, v', CV => by
      have IH1 := constval_rvalue h1
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, y, hy, CV⟩ := CV
      cases E : Cop.boolVal x (Csyntax.typeof r1) Mem.empty with
      | none => rw [E] at CV; cases CV
      | some b =>
        have E' := bool_val_match m E (IH1 _ hx)
        rw [hb] at E'; cases E'
        rw [E] at CV; cases CV; constructor
  | _, _, .condition r1 r2 r3 ty v v1 b vv h1 hb h2 hc, v', CV => by
      have IH1 := constval_rvalue h1
      have IH2 := constval_rvalue h2
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, y, hy, z, hz, CV⟩ := CV
      cases E : Cop.boolVal x (Csyntax.typeof r1) Mem.empty with
      | none => rw [E] at CV; cases CV
      | some b' =>
        have E' := bool_val_match m E (IH1 _ hx)
        rw [hb] at E'; cases E'
        rw [E] at CV
        cases b
        · exact sem_cast_match hc CV (IH2 _ hz)
        · exact sem_cast_match hc CV (IH2 _ hy)
  | _, _, .comma r1 r2 ty v1 v h1 h2, v', CV => by
      have IH2 := constval_rvalue h2
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, _, CV⟩ := CV
      exact IH2 _ CV
  | _, _, .paren r tycast ty v vv h1 h2, v', CV => by
      have IH := constval_rvalue h1
      simp only [Initializers.constval, res_bind_eq_OK] at CV
      obtain ⟨x, hx, CV⟩ := CV
      exact sem_cast_match h2 CV (IH _ hx)

/-- `Initializersproof.constval_lvalue` -/
theorem constval_lvalue {m : Mem} : ∀ {a : Csyntax.Expr} {b : Block} {ofs : Integers.Ptrofs}
    {bf : Bitfield}, EvalSimpleLvalue ge emptyEnv m a b ofs bf →
    ∀ v', Initializers.constval ge.genv_cenv a = .OK v' →
      bf = .Full ∧ Val.Inject (inj ge) v' (.Vptr b ofs)
  | _, _, _, _, .loc b ofs bf ty, v', CV => by simp only [Initializers.constval] at CV; cases CV
  | _, _, _, _, .var_local x ty b he, v', CV => by simp [emptyEnv] at he
  | _, _, _, _, .var_global x ty b he hs, v', CV => by
      simp only [Initializers.constval] at CV; cases CV
      refine ⟨rfl, .ptr 0 (by simp [inj, hs]) ?_⟩
      rfl
  | _, _, _, _, .deref r ty b ofs h, v', CV => ⟨rfl, constval_rvalue h _ CV⟩
  | _, _, _, _, .field_struct r f ty b ofs id co a delta bf h ht hco hf, v', CV => by
      have IH := constval_rvalue h
      simp only [Initializers.constval, ht, Initializers.lookupComposite, hco, bind, Res.bind,
        hf] at CV
      cases hx : Initializers.constval ge.genv_cenv r with
      | Error _ => rw [hx] at CV; cases CV
      | OK x =>
        rw [hx] at CV
        cases bf with
        | Full => cases CV; exact ⟨rfl, add_offset_match (IH _ hx)⟩
        | Bits => cases CV
  | _, _, _, _, .field_union r f ty b ofs id co a delta bf h ht hco hf, v', CV => by
      have IH := constval_rvalue h
      simp only [Initializers.constval, ht, Initializers.lookupComposite, hco, bind, Res.bind,
        hf] at CV
      cases hx : Initializers.constval ge.genv_cenv r with
      | Error _ => rw [hx] at CV; cases CV
      | OK x =>
        rw [hx] at CV
        cases bf with
        | Full => cases CV; exact ⟨rfl, add_offset_match (IH _ hx)⟩
        | Bits => cases CV
end

/-- `Initializersproof.constval_simple` -/
theorem constval_simple {ce : CompositeEnv} : ∀ {a : Csyntax.Expr} {v : Val},
    Initializers.constval ce a = .OK v → Simple a
  | .Eloc _ _ _ _, _, _ => trivial
  | .Evar _ _, _, _ => trivial
  | .Eval _ _, _, _ => trivial
  | .Esizeof _ _, _, _ => trivial
  | .Ealignof _ _, _, _ => trivial
  | .Ederef r _, _, h => constval_simple (a := r) h
  | .Eaddrof l _, _, h => constval_simple (a := l) h
  | .Evalof l ty, _, h => by
      simp only [Initializers.constval] at h
      split at h
      · exact constval_simple (a := l) h
      · exact constval_simple (a := l) h
      · cases h
  | .Efield l f ty, _, h => by
      simp only [Initializers.constval] at h
      split at h <;> simp only [res_bind_eq_OK] at h
      · obtain ⟨_, _, _, _, _, hx, _⟩ := h
        exact constval_simple (a := l) hx
      · obtain ⟨_, _, _, _, _, hx, _⟩ := h
        exact constval_simple (a := l) hx
      · obtain ⟨_, h, _⟩ := h
        cases h
  | .Eunop _ r1 _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, _⟩ := h
      exact constval_simple (a := r1) hx
  | .Ecast r1 _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, _⟩ := h
      exact constval_simple (a := r1) hx
  | .Eparen r1 _ _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, _⟩ := h
      exact constval_simple (a := r1) hx
  | .Ebinop _ r1 r2 _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, y, hy, _⟩ := h
      exact ⟨constval_simple (a := r1) hx, constval_simple (a := r2) hy⟩
  | .Eseqand r1 r2 _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, y, hy, _⟩ := h
      exact ⟨constval_simple (a := r1) hx, constval_simple (a := r2) hy⟩
  | .Eseqor r1 r2 _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, y, hy, _⟩ := h
      exact ⟨constval_simple (a := r1) hx, constval_simple (a := r2) hy⟩
  | .Ecomma r1 r2 _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, hy⟩ := h
      exact ⟨constval_simple (a := r1) hx, constval_simple (a := r2) hy⟩
  | .Econdition r1 r2 r3 _, _, h => by
      simp only [Initializers.constval, res_bind_eq_OK] at h
      obtain ⟨x, hx, y, hy, z, hz, _⟩ := h
      exact ⟨constval_simple (a := r1) hx, constval_simple (a := r2) hy, constval_simple (a := r3) hz⟩
  | .Eassign _ _ _, _, h => by simp [Initializers.constval] at h
  | .Eassignop _ _ _ _ _, _, h => by simp [Initializers.constval] at h
  | .Epostincr _ _ _, _, h => by simp [Initializers.constval] at h
  | .Ecall _ _ _, _, h => by simp [Initializers.constval] at h
  | .Ebuiltin _ _ _ _, _, h => by simp [Initializers.constval] at h

/-- `Initializersproof.constval_steps`: soundness of `constval` with respect
    to the reduction semantics of CompCert C.  If the constant expression `r`
    evaluates at compile time to `v`, and at run time (in the empty local
    environment) to `v'`, then the memory is unchanged, the type is that of `r`,
    and `v` and `v'` are related by the injection `inj ge` that maps each
    global's identifier to its block. -/
theorem constval_steps {f : Csyntax.Function} {r : Csyntax.Expr} {m : Mem} {v v' : Val} {ty : Ty}
    {m' : Mem}
    (h : Smallstep.Star (Csem.Step ge) (.ExprState f r .Kstop emptyEnv m) E0
      (.ExprState f (.Eval v' ty) .Kstop emptyEnv m'))
    (hc : Initializers.constval ge.genv_cenv r = .OK v) :
    m' = m ∧ ty = Csyntax.typeof r ∧ Val.Inject (inj ge) v v' := by
  obtain ⟨A, B, C⟩ := eval_simple_steps h (constval_simple hc)
  exact ⟨A, B, constval_rvalue C _ hc⟩

end SOUNDNESS

end Initializersproof
end CC
