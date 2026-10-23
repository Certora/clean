/-
  `cfrontend/Cstrategy.v`, continued: argument lists of calls and builtins
  (`rval_list`, `eval_simple_list'`, `exprlist_app`, `contextlist'`,
  `eval_simple_list_steps`, `simple_list_can_eval`), the decomposition of a safe
  expression into a left context around a simple side effect
  (`decompose_expr`, `decompose_topexpr`).
-/
import CCLib.cfrontend.CstrategyInversion

namespace CC
namespace Cstrategy

section SIMPLE_LISTS
variable {ge : Csem.CGenv} {f : Csyntax.Function} {k : Csem.Cont} {e : Env} {m : Mem}

/-- `Cstrategy.rval_list` -/
def rvalList : List Val → Csyntax.ExprList → Csyntax.ExprList
  | v1 :: vl', .Econs r1 rl' => .Econs (.Eval v1 (Csyntax.typeof r1)) (rvalList vl' rl')
  | _, _ => .Enil

variable (ge e m) in
/-- `Cstrategy.eval_simple_list'` -/
inductive EvalSimpleList' : Csyntax.ExprList → List Val → Prop where
  | nil : EvalSimpleList' .Enil []
  | cons (r rl v vl) :
      EvalSimpleRvalue ge e m r v → EvalSimpleList' rl vl → EvalSimpleList' (.Econs r rl) (v :: vl)

/-- `Cstrategy.eval_simple_list_implies` -/
theorem eval_simple_list_implies {rl tyl vl} (h : EvalSimpleList ge e m rl tyl vl) :
    ∃ vl', Csem.CastArguments m (rvalList vl' rl) tyl vl ∧ EvalSimpleList' ge e m rl vl' := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons r rl ty tyl v vl v' hr hc _ ih =>
    obtain ⟨vl', A, B⟩ := ih
    exact ⟨v' :: vl', .cons _ _ _ _ _ _ _ hc A, .cons _ _ _ _ hr B⟩

/-- `Cstrategy.can_eval_simple_list` -/
theorem can_eval_simple_list {rl vl} (h : EvalSimpleList' ge e m rl vl) :
    ∀ {tyl vl'}, Csem.CastArguments m (rvalList vl rl) tyl vl' → EvalSimpleList ge e m rl tyl vl' := by
  induction h with
  | nil => intro tyl vl' hc; cases hc; exact .nil
  | cons r rl v vl hr _ ih =>
    intro tyl vl' hc
    cases hc with
    | cons _ _ _ _ _ _ _ hcast hrest => exact .cons _ _ _ _ _ _ _ hr hcast (ih hrest)

/-- `Cstrategy.exprlist_app` -/
def exprlistApp : Csyntax.ExprList → Csyntax.ExprList → Csyntax.ExprList
  | .Enil, rl2 => rl2
  | .Econs r1 rl1', rl2 => .Econs r1 (exprlistApp rl1' rl2)

/-- `Cstrategy.exprlist_app_assoc` -/
theorem exprlist_app_assoc (rl2 rl3 : Csyntax.ExprList) : ∀ rl1,
    exprlistApp (exprlistApp rl1 rl2) rl3 = exprlistApp rl1 (exprlistApp rl2 rl3)
  | .Enil => rfl
  | .Econs r rl1 => by simp only [exprlistApp, exprlist_app_assoc rl2 rl3 rl1]

/-- `Cstrategy.contextlist'`: contexts whose hole is the tail of the argument list
    of a call or builtin. -/
inductive ContextList' : (Csyntax.ExprList → Csyntax.Expr) → Prop where
  | call (r1 rl0 ty C) : Csem.Context .RV .RV C →
      ContextList' (fun rl => C (.Ecall r1 (exprlistApp rl0 rl) ty))
  | builtin (ef tyargs rl0 ty C) : Csem.Context .RV .RV C →
      ContextList' (fun rl => C (.Ebuiltin ef tyargs (exprlistApp rl0 rl) ty))

/-- `Cstrategy.exprlist_app_context` -/
theorem exprlist_app_context (rl2 : Csyntax.ExprList) : ∀ rl1,
    Csem.ContextList .RV (fun x => exprlistApp rl1 (.Econs x rl2))
  | .Enil => .head _ _ _ (.top _)
  | .Econs _ rl1 => .tail _ _ _ (exprlist_app_context rl2 rl1)

/-- `Cstrategy.contextlist'_head` -/
theorem contextlist'_head (rl : Csyntax.ExprList) {C} (h : ContextList' C) :
    Csem.Context .RV .RV (fun x => C (.Econs x rl)) := by
  cases h with
  | call r1 rl0 ty C hC =>
    exact context_compose (.call_right _ _ r1 ty (exprlist_app_context rl rl0)) hC
  | builtin ef tyargs rl0 ty C hC =>
    exact context_compose (.builtin _ _ ef tyargs ty (exprlist_app_context rl rl0)) hC

/-- `Cstrategy.contextlist'_tail` -/
theorem contextlist'_tail (r1 : Csyntax.Expr) {C} (h : ContextList' C) :
    ContextList' (fun x => C (.Econs r1 x)) := by
  cases h with
  | call r0 rl0 ty C hC =>
    have := ContextList'.call r0 (exprlistApp rl0 (.Econs r1 .Enil)) ty C hC
    simp only [exprlist_app_assoc] at this
    exact this
  | builtin ef tyargs rl0 ty C hC =>
    have := ContextList'.builtin ef tyargs (exprlistApp rl0 (.Econs r1 .Enil)) ty C hC
    simp only [exprlist_app_assoc] at this
    exact this

/-- `Cstrategy.eval_simple_list_steps` -/
theorem eval_simple_list_steps {rl vl} (h : EvalSimpleList' ge e m rl vl) :
    ∀ {C}, ContextList' C →
    Smallstep.Star (Csem.Step ge) (.ExprState f (C rl) k e m) E0
      (.ExprState f (C (rvalList vl rl)) k e m) := by
  induction h with
  | nil => intro C _; exact .refl _
  | cons r rl v vl hr _ ih =>
    intro C hC
    exact Smallstep.star_trans
      (eval_simple_rvalue_steps hr (C := fun x => C (.Econs x rl)) (contextlist'_head rl hC))
      (ih (C := fun x => C (.Econs (.Eval v (Csyntax.typeof r)) x)) (contextlist'_tail _ hC)) rfl

/-- `Cstrategy.simple_list_can_eval` -/
theorem simple_list_can_eval : ∀ (rl : Csyntax.ExprList) {C}, simplelist rl = true →
    ContextList' C → Safe ge (.ExprState f (C rl) k e m) → ∃ vl, EvalSimpleList' ge e m rl vl
  | .Enil, _, _, _, _ => ⟨[], .nil⟩
  | .Econs r1 rl, C, hs, hC, hsafe => by
    simp only [simplelist, Bool.and_eq_true] at hs
    obtain ⟨v1, E1⟩ := simple_can_eval r1 (from_ := .RV) (C := fun x => C (.Econs x rl)) hs.1
      (contextlist'_head rl hC) hsafe
    obtain ⟨vl, El⟩ := simple_list_can_eval rl (C := fun x => C (.Econs (.Eval v1 (Csyntax.typeof r1)) x))
      hs.2 (contextlist'_tail _ hC)
      (eval_simple_rvalue_safe (C := fun x => C (.Econs x rl)) E1 (contextlist'_head rl hC) hsafe)
    exact ⟨v1 :: vl, .cons _ _ _ _ E1 El⟩

/-- `Cstrategy.rval_list_all_values` -/
theorem rval_list_all_values : ∀ (vl : List Val) (rl : Csyntax.ExprList),
    exprlistAllValues (rvalList vl rl)
  | [], rl => by cases rl <;> trivial
  | _ :: vl, .Enil => trivial
  | _ :: vl, .Econs _ rl => rval_list_all_values vl rl

end SIMPLE_LISTS

section DECOMPOSITION
variable {ge : Csem.CGenv} {f : Csyntax.Function} {k : Csem.Cont} {e : Env} {m : Mem}

/-- `Cstrategy.simple_side_effect`: the redexes the strategy reduces — a side
    effect whose arguments are all simple. -/
def SimpleSideEffect : Csyntax.Expr → Prop
  | .Evalof l _ => simple l = true ∧ typeIsVolatile (Csyntax.typeof l) = true
  | .Eseqand r1 _ _ => simple r1 = true
  | .Eseqor r1 _ _ => simple r1 = true
  | .Econdition r1 _ _ _ => simple r1 = true
  | .Eassign l1 r2 _ => simple l1 = true ∧ simple r2 = true
  | .Eassignop _ l1 r2 _ _ => simple l1 = true ∧ simple r2 = true
  | .Epostincr _ l1 _ => simple l1 = true
  | .Ecomma r1 _ _ => simple r1 = true
  | .Ecall r1 rl _ => simple r1 = true ∧ simplelist rl = true
  | .Ebuiltin _ _ rl _ => simplelist rl = true
  | .Eparen r1 _ _ => simple r1 = true
  | _ => False

/-- The conclusion of `decompose_expr`. -/
def Decomposes (kind : Csem.Kind) (a : Csyntax.Expr) : Prop :=
  simple a = true ∨ ∃ C' a', a = C' a' ∧ SimpleSideEffect a' ∧ LeftContext .RV kind C'

/-- The conclusion of `decompose_expr` for argument lists. -/
def DecomposesList (rl : Csyntax.ExprList) : Prop :=
  simplelist rl = true ∨ ∃ C' a', rl = C' a' ∧ SimpleSideEffect a' ∧ LeftContextList .RV C'

/-- A decomposition of `a1` lifts through a left-context constructor `W`. -/
theorem Decomposes.wrap {kin kout : Csem.Kind} {a1 : Csyntax.Expr} {W : Csyntax.Expr → Csyntax.Expr}
    (h : Decomposes kin a1)
    (hW : ∀ {C'}, LeftContext .RV kin C' → LeftContext .RV kout (fun x => W (C' x)))
    (hs : simple a1 = true → Decomposes kout (W a1)) : Decomposes kout (W a1) := by
  rcases h with h | ⟨C', a', rfl, hse, hlc⟩
  · exact hs h
  · exact .inr ⟨_, a', rfl, hse, hW hlc⟩

/-- A simple side effect is its own decomposition. -/
theorem Decomposes.base {a : Csyntax.Expr} (h : SimpleSideEffect a) : Decomposes .RV a :=
  .inr ⟨fun x => x, a, rfl, h, .top _⟩

mutual
/-- `Cstrategy.decompose_expr` (expressions): a safe expression is simple, or is
    a simple side effect inside a left context. -/
theorem decompose_expr (a : Csyntax.Expr) : ∀ {from_ C}, Csem.Context from_ .RV C →
    Safe ge (.ExprState f (C a) k e m) → Decomposes from_ a := by
  intro from_ C hC hsafe
  have K := safe_expr_kind hC hsafe
  subst K
  cases a with
  | Eval v ty => exact .inl rfl
  | Evar x ty => exact .inl rfl
  | Eloc b ofs bf ty => exact .inl rfl
  | Esizeof _ _ => exact .inl rfl
  | Ealignof _ _ => exact .inl rfl
  | Efield a1 fl ty =>
    exact (decompose_expr a1 (C := fun x => C (.Efield x fl ty))
      (context_compose (.field _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Efield x fl ty)
      (fun h => .field _ _ _ _ h) (fun h => .inl h)
  | Ederef a1 ty =>
    exact (decompose_expr a1 (C := fun x => C (.Ederef x ty))
      (context_compose (.deref _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Ederef x ty)
      (fun h => .deref _ _ _ h) (fun h => .inl h)
  | Eaddrof a1 ty =>
    exact (decompose_expr a1 (C := fun x => C (.Eaddrof x ty))
      (context_compose (.addrof _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eaddrof x ty)
      (fun h => .addrof _ _ _ h) (fun h => .inl h)
  | Eunop op a1 ty =>
    exact (decompose_expr a1 (C := fun x => C (.Eunop op x ty))
      (context_compose (.unop _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eunop op x ty)
      (fun h => .unop _ _ _ _ h) (fun h => .inl h)
  | Ecast a1 ty =>
    exact (decompose_expr a1 (C := fun x => C (.Ecast x ty))
      (context_compose (.cast _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Ecast x ty)
      (fun h => .cast _ _ _ h) (fun h => .inl h)
  | Evalof l ty =>
    refine (decompose_expr l (C := fun x => C (.Evalof x ty))
      (context_compose (.rvalof _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Evalof x ty)
      (fun h => .rvalof _ _ _ h) (fun h => ?_)
    cases hv : typeIsVolatile (Csyntax.typeof l)
    · exact .inl (by simp [simple, h, hv])
    · exact .base ⟨h, hv⟩
  | Ebinop op r1 r2 ty =>
    refine (decompose_expr r1 (C := fun x => C (.Ebinop op x r2 ty))
      (context_compose (.binop_left _ _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Ebinop op x r2 ty)
      (fun h => .binop_left _ _ _ _ _ h) (fun h1 => ?_)
    exact (decompose_expr r2 (C := fun x => C (.Ebinop op r1 x ty))
      (context_compose (.binop_right _ _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Ebinop op r1 x ty)
      (fun h => .binop_right _ _ _ _ _ h1 h) (fun h2 => .inl (by simp [simple, h1, h2]))
  | Eseqand r1 r2 ty =>
    exact (decompose_expr r1 (C := fun x => C (.Eseqand x r2 ty))
      (context_compose (.seqand _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eseqand x r2 ty)
      (fun h => .seqand _ _ _ _ h) (fun h => .base h)
  | Eseqor r1 r2 ty =>
    exact (decompose_expr r1 (C := fun x => C (.Eseqor x r2 ty))
      (context_compose (.seqor _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eseqor x r2 ty)
      (fun h => .seqor _ _ _ _ h) (fun h => .base h)
  | Econdition r1 r2 r3 ty =>
    exact (decompose_expr r1 (C := fun x => C (.Econdition x r2 r3 ty))
      (context_compose (.condition _ _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Econdition x r2 r3 ty)
      (fun h => .condition _ _ _ _ _ h) (fun h => .base h)
  | Eassign l r ty =>
    refine (decompose_expr l (C := fun x => C (.Eassign x r ty))
      (context_compose (.assign_left _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eassign x r ty)
      (fun h => .assign_left _ _ _ _ h) (fun h1 => ?_)
    exact (decompose_expr r (C := fun x => C (.Eassign l x ty))
      (context_compose (.assign_right _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eassign l x ty)
      (fun h => .assign_right _ _ _ _ h1 h) (fun h2 => .base ⟨h1, h2⟩)
  | Eassignop op l r tyres ty =>
    refine (decompose_expr l (C := fun x => C (.Eassignop op x r tyres ty))
      (context_compose (.assignop_left _ _ _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eassignop op x r tyres ty)
      (fun h => .assignop_left _ _ _ _ _ _ h) (fun h1 => ?_)
    exact (decompose_expr r (C := fun x => C (.Eassignop op l x tyres ty))
      (context_compose (.assignop_right _ _ _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eassignop op l x tyres ty)
      (fun h => .assignop_right _ _ _ _ _ _ h1 h) (fun h2 => .base ⟨h1, h2⟩)
  | Epostincr id l ty =>
    exact (decompose_expr l (C := fun x => C (.Epostincr id x ty))
      (context_compose (.postincr _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Epostincr id x ty)
      (fun h => .postincr _ _ _ _ h) (fun h => .base h)
  | Ecomma r1 r2 ty =>
    exact (decompose_expr r1 (C := fun x => C (.Ecomma x r2 ty))
      (context_compose (.comma _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Ecomma x r2 ty)
      (fun h => .comma _ _ _ _ h) (fun h => .base h)
  | Eparen r1 tycast ty =>
    exact (decompose_expr r1 (C := fun x => C (.Eparen x tycast ty))
      (context_compose (.paren _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Eparen x tycast ty)
      (fun h => .paren _ _ _ _ h) (fun h => .base h)
  | Ecall r1 rargs ty =>
    refine (decompose_expr r1 (C := fun x => C (.Ecall x rargs ty))
      (context_compose (.call_left _ _ _ _ (.top _)) hC) hsafe).wrap (W := fun x => .Ecall x rargs ty)
      (fun h => .call_left _ _ _ _ h) (fun h1 => ?_)
    rcases decompose_exprlist rargs (C := fun rl => C (.Ecall r1 (exprlistApp .Enil rl) ty))
      (.call r1 .Enil ty C hC) hsafe with h2 | ⟨C', a', rfl, hse, hlc⟩
    · exact .base ⟨h1, h2⟩
    · exact .inr ⟨fun x => .Ecall r1 (C' x) ty, a', rfl, hse, .call_right _ _ _ _ h1 hlc⟩
  | Ebuiltin ef tyargs rargs ty =>
    rcases decompose_exprlist rargs (C := fun rl => C (.Ebuiltin ef tyargs (exprlistApp .Enil rl) ty))
      (.builtin ef tyargs .Enil ty C hC) hsafe with h2 | ⟨C', a', rfl, hse, hlc⟩
    · exact .base h2
    · exact .inr ⟨fun x => .Ebuiltin ef tyargs (C' x) ty, a', rfl, hse, .builtin _ _ _ _ _ hlc⟩
termination_by sizeOf a

/-- `Cstrategy.decompose_expr` (argument lists). -/
theorem decompose_exprlist (rl : Csyntax.ExprList) : ∀ {C}, ContextList' C →
    Safe ge (.ExprState f (C rl) k e m) → DecomposesList rl := by
  intro C hC hsafe
  cases rl with
  | Enil => exact .inl rfl
  | Econs r1 rl =>
    rcases decompose_expr r1 (C := fun x => C (.Econs x rl)) (contextlist'_head rl hC) hsafe with
      h1 | ⟨C', a', rfl, hse, hlc⟩
    · rcases decompose_exprlist rl (C := fun x => C (.Econs r1 x)) (contextlist'_tail r1 hC) hsafe with
        h2 | ⟨C', a', rfl, hse, hlc⟩
      · exact .inl (by simp [simplelist, h1, h2])
      · exact .inr ⟨fun x => .Econs r1 (C' x), a', rfl, hse, .tail _ _ _ h1 hlc⟩
    · exact .inr ⟨fun x => .Econs (C' x) rl, a', rfl, hse, .head _ _ _ hlc⟩
termination_by sizeOf rl
end

/-- `Cstrategy.decompose_topexpr` -/
theorem decompose_topexpr {a} (hsafe : Safe ge (.ExprState f a k e m)) : Decomposes .RV a :=
  decompose_expr a (C := fun x => x) (.top _) hsafe

end DECOMPOSITION

end Cstrategy
end CC
