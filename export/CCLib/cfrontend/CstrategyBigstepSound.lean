/-
  From the big-step semantics of CompCert C to the strategy's transitions:
  `bigstep_to_steps`, `evalinf_funcall_steps` and `bigstep_semantics_sound`
  of `cfrontend/Cstrategy.v`.  The terminating half is `bigstep_to_steps`
  (`eval_expression_to_steps`, `eval_expr_to_steps`, `eval_exprlist_to_steps`,
  `exec_stmt_to_steps`, `eval_funcall_to_steps`), with the auxiliary
  `outcome_state_match`, `is_call_cont_call_cont`, `leftcontext_compose`,
  `exprlist_app_leftcontext` and `exprlist_app_simple`.

  The diverging half (`esize`, `leftcontext_size`, `evalinf_funcall_steps`,
  here stated with `forever` via `Smallstep.forever_of_measure`, Rocq's
  `forever_N` for the order `<` on `Nat`) and the whole-program
  `bigstep_semantics_sound` follow.
-/
import CCLib.cfrontend.CstrategyBigstep
import CCLib.cfrontend.CstrategyDecompose

namespace CC
namespace Cstrategy

open Smallstep
open ClightBigstep (Outcome OutNormalOrContinue OutBreakOrReturn outcomeSwitch outcomeResultValue)
open ClightBigstep.Outcome

/-! ## Auxiliary lemmas -/

/-- `Cstrategy.is_call_cont_call_cont` -/
theorem isCallCont_callCont {k : Csem.Cont} (h : Csem.IsCallCont k) : Csem.callCont k = k := by
  cases k <;> simp_all [Csem.IsCallCont, Csem.callCont]

mutual
/-- `Cstrategy.leftcontext_compose` -/
theorem leftcontext_compose {k1 k2} : ∀ {k3 C2 C1}, LeftContext k2 k3 C2 → LeftContext k1 k2 C1 →
    LeftContext k1 k3 (fun x => C2 (C1 x))
  | _, _, _, .top _, h1 => h1
  | _, _, _, .deref _ _ ty h, h1 => .deref _ _ ty (leftcontext_compose h h1)
  | _, _, _, .field _ _ f ty h, h1 => .field _ _ f ty (leftcontext_compose h h1)
  | _, _, _, .rvalof _ _ ty h, h1 => .rvalof _ _ ty (leftcontext_compose h h1)
  | _, _, _, .addrof _ _ ty h, h1 => .addrof _ _ ty (leftcontext_compose h h1)
  | _, _, _, .unop _ _ op ty h, h1 => .unop _ _ op ty (leftcontext_compose h h1)
  | _, _, _, .binop_left _ _ op e2 ty h, h1 => .binop_left _ _ op e2 ty (leftcontext_compose h h1)
  | _, _, _, .binop_right _ _ op e1 ty hs h, h1 =>
    .binop_right _ _ op e1 ty hs (leftcontext_compose h h1)
  | _, _, _, .cast _ _ ty h, h1 => .cast _ _ ty (leftcontext_compose h h1)
  | _, _, _, .seqand _ _ r2 ty h, h1 => .seqand _ _ r2 ty (leftcontext_compose h h1)
  | _, _, _, .seqor _ _ r2 ty h, h1 => .seqor _ _ r2 ty (leftcontext_compose h h1)
  | _, _, _, .condition _ _ r2 r3 ty h, h1 => .condition _ _ r2 r3 ty (leftcontext_compose h h1)
  | _, _, _, .assign_left _ _ e2 ty h, h1 => .assign_left _ _ e2 ty (leftcontext_compose h h1)
  | _, _, _, .assign_right _ _ e1 ty hs h, h1 =>
    .assign_right _ _ e1 ty hs (leftcontext_compose h h1)
  | _, _, _, .assignop_left _ _ op e2 tyres ty h, h1 =>
    .assignop_left _ _ op e2 tyres ty (leftcontext_compose h h1)
  | _, _, _, .assignop_right _ _ op e1 tyres ty hs h, h1 =>
    .assignop_right _ _ op e1 tyres ty hs (leftcontext_compose h h1)
  | _, _, _, .postincr _ _ id ty h, h1 => .postincr _ _ id ty (leftcontext_compose h h1)
  | _, _, _, .call_left _ _ el ty h, h1 => .call_left _ _ el ty (leftcontext_compose h h1)
  | _, _, _, .call_right _ _ e1 ty hs h, h1 =>
    .call_right _ _ e1 ty hs (leftcontextlist_compose h h1)
  | _, _, _, .builtin _ _ ef tyargs ty h, h1 =>
    .builtin _ _ ef tyargs ty (leftcontextlist_compose h h1)
  | _, _, _, .comma _ _ e2 ty h, h1 => .comma _ _ e2 ty (leftcontext_compose h h1)
  | _, _, _, .paren _ _ tycast ty h, h1 => .paren _ _ tycast ty (leftcontext_compose h h1)

/-- `Cstrategy.leftcontextlist_compose` -/
theorem leftcontextlist_compose {k1 k2} : ∀ {C2 C1}, LeftContextList k2 C2 → LeftContext k1 k2 C1 →
    LeftContextList k1 (fun x => C2 (C1 x))
  | _, _, .head _ _ el h, h1 => .head _ _ el (leftcontext_compose h h1)
  | _, _, .tail _ _ e1 hs h, h1 => .tail _ _ e1 hs (leftcontextlist_compose h h1)
end

/-- `Cstrategy.exprlist_app_leftcontext` -/
theorem exprlist_app_leftcontext (rl2 : Csyntax.ExprList) : ∀ rl1, simplelist rl1 = true →
    LeftContextList .RV (fun x => exprlistApp rl1 (.Econs x rl2))
  | .Enil, _ => .head _ _ _ (.top _)
  | .Econs r rl1, h => by
    simp only [simplelist, Bool.and_eq_true] at h
    exact .tail _ _ _ h.1 (exprlist_app_leftcontext rl2 rl1 h.2)

/-- `Cstrategy.exprlist_app_simple` -/
theorem exprlist_app_simple (rl2 : Csyntax.ExprList) : ∀ rl1,
    simplelist (exprlistApp rl1 rl2) = (simplelist rl1 && simplelist rl2)
  | .Enil => by simp [exprlistApp, simplelist]
  | .Econs r rl1 => by
    simp only [exprlistApp, simplelist, exprlist_app_simple rl2 rl1, Bool.and_assoc]

/-! ## Terminating evaluations -/

/-- `Cstrategy.outcome_state_match`: the strategy state reached after
    executing a statement with the given outcome. -/
inductive OutcomeStateMatch (e : Env) (m : Mem) (f : Csyntax.Function) (k : Csem.Cont) :
    Outcome → Csem.State → Prop where
  | normal : OutcomeStateMatch e m f k Out_normal (.State f .Sskip k e m)
  | break_ : OutcomeStateMatch e m f k Out_break (.State f .Sbreak k e m)
  | continue_ : OutcomeStateMatch e m f k Out_continue (.State f .Scontinue k e m)
  | return_none (k') :
      Csem.callCont k' = Csem.callCont k →
      OutcomeStateMatch e m f k (Out_return none) (.State f (.Sreturn none) k' e m)
  | return_some (v ty k') :
      Csem.callCont k' = Csem.callCont k →
      OutcomeStateMatch e m f k (Out_return (some (v, ty)))
        (.ExprState f (.Eval v ty) (.Kreturn k') e m)

/-- The trace bookkeeping of the proofs below. -/
local macro "trace_eq" : tactic => `(tactic| simp [Eapp, E0, List.append_assoc])

variable {ge : Csem.CGenv}

private theorem es {S t S'} (h : Estep ge S t S') : Step ge S t S' := Or.inl h
private theorem ss {S t S'} (h : Csem.Sstep ge S t S') : Step ge S t S' := Or.inr h

private theorem sc_while {e m f x s k out S} (hnc : OutNormalOrContinue out)
    (hB : OutcomeStateMatch e m f (.Kwhile2 x s k) out S) :
    Step ge S E0 (.State f (.Swhile x s) k e m) := by
  cases hnc <;> cases hB <;> exact ss (.skip_or_continue_while _ _ _ _ _ _ _ (by simp))

private theorem sc_dowhile {e m f x s k out S} (hnc : OutNormalOrContinue out)
    (hB : OutcomeStateMatch e m f (.Kdowhile1 x s k) out S) :
    Step ge S E0 (.ExprState f x (.Kdowhile2 x s k) e m) := by
  cases hnc <;> cases hB <;> exact ss (.skip_or_continue_dowhile _ _ _ _ _ _ _ (by simp))

private theorem sc_for3 {e m f a2 a3 s k out S} (hnc : OutNormalOrContinue out)
    (hB : OutcomeStateMatch e m f (.Kfor3 a2 a3 s k) out S) :
    Step ge S E0 (.State f a3 (.Kfor4 a2 a3 s k) e m) := by
  cases hnc <;> cases hB <;> exact ss (.skip_or_continue_for3 _ _ _ _ _ _ _ _ (by simp))

private theorem execStmt_skip_inv {e m t m' out} (h : ExecStmt ge e m .Sskip t m' out) :
    t = E0 ∧ m' = m ∧ out = Out_normal := by
  cases h; exact ⟨rfl, rfl, rfl⟩

mutual
/-- `Cstrategy.eval_expression_to_steps` -/
theorem eval_expression_steps {e m a t m' v} (h : EvalExpression ge e m a t m' v)
    (f : Csyntax.Function) (k : Csem.Cont) :
    Smallstep.Star (Step ge) (.ExprState f a k e m) t (.ExprState f (.Eval v (Csyntax.typeof a)) k e m') := by
  match h with
  | .intro _ _ _ _ _ a' _ h1 hv =>
    obtain ⟨_, B, D⟩ := eval_expr_steps h1 (fun x => x) f k (.top _)
    by_cases hval : ∃ v0 ty0, a' = .Eval v0 ty0
    · obtain ⟨v0, ty0, rfl⟩ := hval
      cases hv
      simp only [Csyntax.typeof] at B
      subst B
      exact D
    · refine star_right D (es (.expr _ _ _ _ _ _ _ hv ?_ B.symm)) (by trace_eq)
      cases a' <;> first | trivial | exact hval ⟨_, _, rfl⟩

/-- `Cstrategy.eval_expr_to_steps` -/
theorem eval_expr_steps {e m K a t m' a'} (h : EvalExpr ge e m K a t m' a')
    (C : Csyntax.Expr → Csyntax.Expr) (f : Csyntax.Function) (k : Csem.Cont)
    (hC : LeftContext K .RV C) :
    simple a' = true ∧ Csyntax.typeof a' = Csyntax.typeof a ∧
      Smallstep.Star (Step ge) (.ExprState f (C a) k e m) t (.ExprState f (C a') k e m') := by
  match h with
  | .val .. => exact ⟨rfl, rfl, .refl _⟩
  | .var .. => exact ⟨rfl, rfl, .refl _⟩
  | .field _ _ _ _ _ _ fid ty h1 =>
    obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Efield x fid ty)) f k
      (leftcontext_compose hC (.field _ _ _ _ (.top _)))
    exact ⟨by simpa [simple] using A, rfl, D⟩
  | .valof _ _ _ _ _ _ ty hvol h1 =>
    obtain ⟨A, B, D⟩ := eval_expr_steps h1 (fun x => C (.Evalof x ty)) f k
      (leftcontext_compose hC (.rvalof _ _ _ (.top _)))
    exact ⟨by simp [simple, A, B, hvol], rfl, D⟩
  | .valof_volatile _ _ _ _ _ a' ty b ofs bf t2 v hvol h1 hl hd hty =>
    obtain ⟨_, B, D⟩ := eval_expr_steps h1 (fun x => C (.Evalof x ty)) f k
      (leftcontext_compose hC (.rvalof _ _ _ (.top _)))
    refine ⟨rfl, rfl, star_right D (es (.rvalof_volatile f C a' ty k e _ b ofs bf t2 v hC hl
      (by rw [hty]; exact hd) (hty.trans B.symm) (by rw [hty]; exact hvol))) rfl⟩
  | .deref _ _ _ _ _ _ ty h1 =>
    obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Ederef x ty)) f k
      (leftcontext_compose hC (.deref _ _ _ (.top _)))
    exact ⟨by simpa [simple] using A, rfl, D⟩
  | .addrof _ _ _ _ _ _ ty h1 =>
    obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Eaddrof x ty)) f k
      (leftcontext_compose hC (.addrof _ _ _ (.top _)))
    exact ⟨by simpa [simple] using A, rfl, D⟩
  | .unop _ _ _ _ _ _ op ty h1 =>
    obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Eunop op x ty)) f k
      (leftcontext_compose hC (.unop _ _ _ _ (.top _)))
    exact ⟨by simpa [simple] using A, rfl, D⟩
  | .binop _ _ _ _ _ a1' a2 _ _ _ op ty h1 h2 =>
    obtain ⟨A1, _, D1⟩ := eval_expr_steps h1 (fun x => C (.Ebinop op x a2 ty)) f k
      (leftcontext_compose hC (.binop_left _ _ _ _ _ (.top _)))
    obtain ⟨A2, _, D2⟩ := eval_expr_steps h2 (fun x => C (.Ebinop op a1' x ty)) f k
      (leftcontext_compose hC (.binop_right _ _ _ _ _ A1 (.top _)))
    exact ⟨by simp [simple, A1, A2], rfl, star_trans D1 D2 rfl⟩
  | .cast _ _ _ _ _ _ ty h1 =>
    obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Ecast x ty)) f k
      (leftcontext_compose hC (.cast _ _ _ (.top _)))
    exact ⟨by simpa [simple] using A, rfl, D⟩
  | .seqand_true _ _ a1 a2 ty _ _ a1' v1 _ _ a2' v2 v h1 hv1 hb h2 hv2 hc =>
    obtain ⟨_, B1, D1⟩ := eval_expr_steps h1 (fun x => C (.Eseqand x a2 ty)) f k
      (leftcontext_compose hC (.seqand _ _ _ _ (.top _)))
    obtain ⟨_, F, D2⟩ := eval_expr_steps h2 (fun x => C (.Eparen x type_bool ty)) f k
      (leftcontext_compose hC (.paren _ _ _ _ (.top _)))
    refine ⟨rfl, rfl, star_trans D1 (star_left (es (.seqand_true f C a1' a2 ty k e _ v1 hC hv1
      (by rw [B1]; exact hb))) (star_right D2 (es (.paren f C a2' type_bool ty k e _ v2 v hC hv2
      (by rw [F]; exact hc))) rfl) rfl) (by trace_eq)⟩
  | .seqand_false _ _ a1 a2 ty _ _ a1' v1 h1 hv1 hb =>
    obtain ⟨_, B1, D1⟩ := eval_expr_steps h1 (fun x => C (.Eseqand x a2 ty)) f k
      (leftcontext_compose hC (.seqand _ _ _ _ (.top _)))
    exact ⟨rfl, rfl, star_right D1 (es (.seqand_false f C a1' a2 ty k e _ v1 hC hv1
      (by rw [B1]; exact hb))) (by trace_eq)⟩
  | .seqor_false _ _ a1 a2 ty _ _ a1' v1 _ _ a2' v2 v h1 hv1 hb h2 hv2 hc =>
    obtain ⟨_, B1, D1⟩ := eval_expr_steps h1 (fun x => C (.Eseqor x a2 ty)) f k
      (leftcontext_compose hC (.seqor _ _ _ _ (.top _)))
    obtain ⟨_, F, D2⟩ := eval_expr_steps h2 (fun x => C (.Eparen x type_bool ty)) f k
      (leftcontext_compose hC (.paren _ _ _ _ (.top _)))
    refine ⟨rfl, rfl, star_trans D1 (star_left (es (.seqor_false f C a1' a2 ty k e _ v1 hC hv1
      (by rw [B1]; exact hb))) (star_right D2 (es (.paren f C a2' type_bool ty k e _ v2 v hC hv2
      (by rw [F]; exact hc))) rfl) rfl) (by trace_eq)⟩
  | .seqor_true _ _ a1 a2 ty _ _ a1' v1 h1 hv1 hb =>
    obtain ⟨_, B1, D1⟩ := eval_expr_steps h1 (fun x => C (.Eseqor x a2 ty)) f k
      (leftcontext_compose hC (.seqor _ _ _ _ (.top _)))
    exact ⟨rfl, rfl, star_right D1 (es (.seqor_true f C a1' a2 ty k e _ v1 hC hv1
      (by rw [B1]; exact hb))) (by trace_eq)⟩
  | .condition _ _ a1 a2 a3 ty _ _ a1' v1 _ _ a' v' b v h1 hv1 hb h2 hv' hc =>
    obtain ⟨_, B1, D1⟩ := eval_expr_steps h1 (fun x => C (.Econdition x a2 a3 ty)) f k
      (leftcontext_compose hC (.condition _ _ _ _ _ (.top _)))
    obtain ⟨_, F, D2⟩ := eval_expr_steps h2 (fun x => C (.Eparen x ty ty)) f k
      (leftcontext_compose hC (.paren _ _ _ _ (.top _)))
    refine ⟨rfl, rfl, star_trans D1 (star_left (es (.condition f C a1' a2 a3 ty k e _ v1 b hC
      hv1 (by rw [B1]; exact hb))) (star_right D2 (es (.paren f C a' ty ty k e _ v' v hC hv'
      (by rw [F]; exact hc))) rfl) rfl) (by trace_eq)⟩
  | .sizeof .. => exact ⟨rfl, rfl, .refl _⟩
  | .alignof .. => exact ⟨rfl, rfl, .refl _⟩
  | .assign _ _ l r ty _ _ l' _ _ r' b ofs bf v v1 v' t3 m3 h1 h2 hl hr hc ha hty =>
    obtain ⟨A, B, D1⟩ := eval_expr_steps h1 (fun x => C (.Eassign x r ty)) f k
      (leftcontext_compose hC (.assign_left _ _ _ _ (.top _)))
    obtain ⟨_, F, D2⟩ := eval_expr_steps h2 (fun x => C (.Eassign l' x ty)) f k
      (leftcontext_compose hC (.assign_right _ _ _ _ A (.top _)))
    refine ⟨rfl, rfl, star_trans D1 (star_right D2 (es (.assign f C l' r' ty k e _ b ofs bf v v1
      t3 m3 v' hC hl hr (by rw [B, F]; exact hc) (by rw [B]; exact ha) (hty.trans B.symm))) rfl)
      (by trace_eq)⟩
  | .assignop _ _ op l r tyres ty _ _ l' _ _ r' b ofs bf v1 v2 v3 v4 v' t3 t4 m3 h1 h2 hl hd hr hop
      hc ha hty =>
    obtain ⟨A, B, D1⟩ := eval_expr_steps h1 (fun x => C (.Eassignop op x r tyres ty)) f k
      (leftcontext_compose hC (.assignop_left _ _ _ _ _ _ (.top _)))
    obtain ⟨_, F, D2⟩ := eval_expr_steps h2 (fun x => C (.Eassignop op l' x tyres ty)) f k
      (leftcontext_compose hC (.assignop_right _ _ _ _ _ _ A (.top _)))
    refine ⟨rfl, rfl, star_trans D1 (star_right D2 (es (.assignop f C op l' r' tyres ty k e _ b ofs
      bf v1 v2 v3 v4 t3 t4 m3 v' _ hC hl (by rw [B]; exact hd) hr (by rw [B, F]; exact hop)
      (by rw [B]; exact hc) (by rw [B]; exact ha) (hty.trans B.symm) rfl)) rfl) (by trace_eq)⟩
  | .postincr _ _ id l ty _ _ l' b ofs bf v1 v2 v3 v' m2 t2 t3 h1 hl hd hinc hc ha hty =>
    obtain ⟨_, B, D1⟩ := eval_expr_steps h1 (fun x => C (.Epostincr id x ty)) f k
      (leftcontext_compose hC (.postincr _ _ _ _ (.top _)))
    exact ⟨rfl, rfl, star_right D1 (es (.postincr f C id l' ty k e _ b ofs bf v1 v2 v3 t2 t3 m2 v'
      _ hC hl hd hinc hc ha (hty.trans B.symm) rfl)) (by trace_eq)⟩
  | .comma _ _ r1 r2 ty _ _ r1' v1 _ _ _ h1 hv1 h2 hty =>
    obtain ⟨_, _, D1⟩ := eval_expr_steps h1 (fun x => C (.Ecomma x r2 ty)) f k
      (leftcontext_compose hC (.comma _ _ _ _ (.top _)))
    obtain ⟨E, F, D2⟩ := eval_expr_steps h2 C f k hC
    exact ⟨E, F.trans hty.symm, star_trans D1 (star_left (es (.comma f C r1' r2 ty k e _ v1 hC
      hv1 hty)) D2 rfl) (by trace_eq)⟩
  | .call _ _ rf rargs ty _ _ rf' _ _ rargs' vf vargs targs tres cconv fd _ _ vres h1 h2 hvf
      hvargs hcl hfind hty hfun =>
    obtain ⟨A, B, D1⟩ := eval_expr_steps h1 (fun x => C (.Ecall x rargs ty)) f k
      (leftcontext_compose hC (.call_left _ _ _ _ (.top _)))
    obtain ⟨_, D2⟩ := eval_exprlist_steps h2 rf' .Enil ty C f k hC A rfl
    refine ⟨rfl, rfl, star_trans D1 (star_trans D2 (star_left (es (.call f C rf' rargs' ty k e _
      targs tres cconv vf vargs fd hC (by rw [B]; exact hcl) hvf hvargs hfind hty))
      (star_right (eval_funcall_steps hfun (.Kcall f e C ty k) trivial)
        (ss (.returnstate vres f e C ty k _)) rfl) rfl) rfl) (by trace_eq)⟩

/-- `Cstrategy.eval_exprlist_to_steps` -/
theorem eval_exprlist_steps {e m al t m' al'} (h : EvalExprlist ge e m al t m' al')
    (a1 : Csyntax.Expr) (al2 : Csyntax.ExprList) (ty : Ty) (C : Csyntax.Expr → Csyntax.Expr)
    (f : Csyntax.Function) (k : Csem.Cont)
    (hC : LeftContext .RV .RV C) (hs1 : simple a1 = true) (hs2 : simplelist al2 = true) :
    simplelist al' = true ∧
      Smallstep.Star (Step ge) (.ExprState f (C (.Ecall a1 (exprlistApp al2 al) ty)) k e m) t
        (.ExprState f (C (.Ecall a1 (exprlistApp al2 al') ty)) k e m') := by
  match h with
  | .nil .. => exact ⟨rfl, .refl _⟩
  | .cons _ _ a0 al0 _ _ a0' _ _ al0' h1 h2 =>
    obtain ⟨A, _, D1⟩ := eval_expr_steps h1
      (fun x => C (.Ecall a1 (exprlistApp al2 (.Econs x al0)) ty)) f k
      (leftcontext_compose hC (.call_right _ _ _ _ hs1 (exprlist_app_leftcontext al0 al2 hs2)))
    obtain ⟨E, D2⟩ := eval_exprlist_steps h2 a1 (exprlistApp al2 (.Econs a0' .Enil)) ty C f k hC hs1
      (by rw [exprlist_app_simple]; simp [simplelist, hs2, A])
    rw [exprlist_app_assoc, exprlist_app_assoc] at D2
    exact ⟨by simp [simplelist, A, E], star_trans D1 D2 rfl⟩

/-- `Cstrategy.exec_stmt_to_steps` -/
theorem exec_stmt_steps {e m s t m' out} (h : ExecStmt ge e m s t m' out)
    (f : Csyntax.Function) (k : Csem.Cont) :
    ∃ S, Smallstep.Star (Step ge) (.State f s k e m) t S ∧ OutcomeStateMatch e m' f k out S := by
  match h with
  | .skip .. => exact ⟨_, .refl _, .normal⟩
  | .do_ _ _ a _ _ v h1 =>
    exact ⟨_, star_left (ss (.do_1 _ _ _ _ _))
      (star_right (eval_expression_steps h1 f (.Kdo k)) (ss (.do_2 _ _ _ _ _ _)) rfl)
      (by trace_eq), .normal⟩
  | .seq_1 _ _ _ s2 _ _ _ _ _ h1 h2 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq s2 k)
    cases B1
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 f k
    exact ⟨S2, star_left (ss (.seq _ _ _ _ _ _))
      (star_trans A1 (star_left (ss (.skip_seq _ _ _ _ _)) A2 rfl) rfl) (by trace_eq), B2⟩
  | .seq_2 _ _ _ s2 _ _ _ h1 hne =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq s2 k)
    cases B1 with
    | normal => exact absurd rfl hne
    | break_ =>
      exact ⟨_, star_left (ss (.seq _ _ _ _ _ _))
        (star_right A1 (ss (.break_seq _ _ _ _ _)) rfl) (by trace_eq), .break_⟩
    | continue_ =>
      exact ⟨_, star_left (ss (.seq _ _ _ _ _ _))
        (star_right A1 (ss (.continue_seq _ _ _ _ _)) rfl) (by trace_eq), .continue_⟩
    | return_none k' hk =>
      exact ⟨_, star_left (ss (.seq _ _ _ _ _ _)) A1 (by trace_eq),
        .return_none k' (by simpa [Csem.callCont] using hk)⟩
    | return_some v ty k' hk =>
      exact ⟨_, star_left (ss (.seq _ _ _ _ _ _)) A1 (by trace_eq),
        .return_some v ty k' (by simpa [Csem.callCont] using hk)⟩
  | .ifthenelse _ _ a s1 s2 _ _ v1 _ _ b _ h1 hb h2 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f k
    exact ⟨S1, star_left (ss (.ifthenelse_1 _ _ _ _ _ _ _))
      (star_trans (eval_expression_steps h1 f (.Kifthenelse s1 s2 k))
        (star_left (ss (.ifthenelse_2 _ _ _ _ _ _ _ _ _ hb)) A1 rfl) rfl) (by trace_eq), B1⟩
  | .return_none .. => exact ⟨_, .refl _, .return_none k rfl⟩
  | .return_some _ _ a _ _ v h1 =>
    exact ⟨_, star_left (ss (.return_1 _ _ _ _ _)) (eval_expression_steps h1 f (.Kreturn k))
      (by trace_eq), .return_some v _ k rfl⟩
  | .break_ .. => exact ⟨_, .refl _, .break_⟩
  | .continue_ .. => exact ⟨_, .refl _, .continue_⟩
  | .while_false _ _ a s _ _ v h1 hb =>
    exact ⟨_, star_left (ss (Csem.Sstep.while _ _ _ _ _ _))
      (star_right (eval_expression_steps h1 f (.Kwhile1 a s k))
        (ss (.while_false _ _ _ _ _ _ _ _ hb)) rfl) (by trace_eq), .normal⟩
  | .while_stop _ _ a s _ _ v _ _ _ _ h1 hb h2 hbr =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kwhile2 a s k)
    have A0 := star_left (ss (Csem.Sstep.while f a s k e _))
      (star_trans (eval_expression_steps h1 f (.Kwhile1 a s k))
        (star_left (ss (.while_true _ _ _ _ _ _ _ _ hb)) A1 rfl) rfl) rfl
    cases hbr with
    | B =>
      cases B1
      exact ⟨_, star_right A0 (ss (.break_while _ _ _ _ _ _)) (by trace_eq), .normal⟩
    | R ov =>
      cases B1 with
      | return_none k' hk =>
        exact ⟨_, A0.trace_cast (by trace_eq), .return_none k' (by simpa [Csem.callCont] using hk)⟩
      | return_some v ty k' hk =>
        exact ⟨_, A0.trace_cast (by trace_eq),
          .return_some v ty k' (by simpa [Csem.callCont] using hk)⟩
  | .while_loop _ _ a s _ _ v _ _ _ _ _ _ h1 hb h2 hnc h3 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kwhile2 a s k)
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h3 f k
    exact ⟨S2, star_left (ss (Csem.Sstep.while f a s k e _))
      (star_trans (eval_expression_steps h1 f (.Kwhile1 a s k))
        (star_left (ss (.while_true _ _ _ _ _ _ _ _ hb))
          (star_trans A1 (star_left (sc_while hnc B1) A2 rfl) rfl) rfl) rfl)
      (by trace_eq), B2⟩
  | .dowhile_false _ _ s a _ _ _ _ _ v h1 hnc h2 hb =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kdowhile1 a s k)
    exact ⟨_, star_left (ss (.dowhile _ _ _ _ _ _))
      (star_trans A1 (star_left (sc_dowhile hnc B1)
        (star_right (eval_expression_steps h2 f (.Kdowhile2 a s k))
          (ss (.dowhile_false _ _ _ _ _ _ _ _ hb)) rfl) rfl) rfl) (by trace_eq), .normal⟩
  | .dowhile_stop _ _ s a _ _ _ _ h1 hbr =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kdowhile1 a s k)
    have A0 := star_left (ss (.dowhile f a s k e _)) A1 rfl
    cases hbr with
    | B =>
      cases B1
      exact ⟨_, star_right A0 (ss (.break_dowhile _ _ _ _ _ _)) (by trace_eq), .normal⟩
    | R ov =>
      cases B1 with
      | return_none k' hk =>
        exact ⟨_, A0.trace_cast (by trace_eq), .return_none k' (by simpa [Csem.callCont] using hk)⟩
      | return_some v ty k' hk =>
        exact ⟨_, A0.trace_cast (by trace_eq),
          .return_some v ty k' (by simpa [Csem.callCont] using hk)⟩
  | .dowhile_loop _ _ s a _ _ _ _ _ v _ _ _ h1 hnc h2 hb h3 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kdowhile1 a s k)
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h3 f k
    exact ⟨S2, star_left (ss (.dowhile _ _ _ _ _ _))
      (star_trans A1 (star_left (sc_dowhile hnc B1)
        (star_trans (eval_expression_steps h2 f (.Kdowhile2 a s k))
          (star_left (ss (.dowhile_true _ _ _ _ _ _ _ _ hb)) A2 rfl) rfl) rfl) rfl)
      (by trace_eq), B2⟩
  | .for_start _ _ s a1 a2 a3 _ _ _ _ _ h1 h2 =>
    by_cases ha1 : a1 = .Sskip
    · subst ha1
      obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 f k
      obtain ⟨rfl, rfl, -⟩ := execStmt_skip_inv h1
      exact ⟨S2, A2, B2⟩
    · obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq (.Sfor .Sskip a2 a3 s) k)
      cases B1
      obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 f k
      exact ⟨S2, star_left (ss (.for_start _ _ _ _ _ _ _ _ ha1))
        (star_trans A1 (star_left (ss (.skip_seq _ _ _ _ _)) A2 rfl) rfl) (by trace_eq), B2⟩
  | .for_false _ _ s a2 a3 _ _ v h1 hb =>
    exact ⟨_, star_left (ss (Csem.Sstep.for _ _ _ _ _ _ _))
      (star_right (eval_expression_steps h1 f (.Kfor2 a2 a3 s k))
        (ss (.for_false _ _ _ _ _ _ _ _ _ hb)) rfl) (by trace_eq), .normal⟩
  | .for_stop _ _ s a2 a3 _ _ v _ _ _ _ h1 hb h2 hbr =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kfor3 a2 a3 s k)
    have A0 := star_left (ss (Csem.Sstep.for f a2 a3 s k e _))
      (star_trans (eval_expression_steps h1 f (.Kfor2 a2 a3 s k))
        (star_left (ss (.for_true _ _ _ _ _ _ _ _ _ hb)) A1 rfl) rfl) rfl
    cases hbr with
    | B =>
      cases B1
      exact ⟨_, star_right A0 (ss (.break_for3 _ _ _ _ _ _ _)) (by trace_eq), .normal⟩
    | R ov =>
      cases B1 with
      | return_none k' hk =>
        exact ⟨_, A0.trace_cast (by trace_eq), .return_none k' (by simpa [Csem.callCont] using hk)⟩
      | return_some v ty k' hk =>
        exact ⟨_, A0.trace_cast (by trace_eq),
          .return_some v ty k' (by simpa [Csem.callCont] using hk)⟩
  | .for_loop _ _ s a2 a3 _ _ v _ _ _ _ _ _ _ _ h1 hb h2 hnc h3 h4 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kfor3 a2 a3 s k)
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h3 f (.Kfor4 a2 a3 s k)
    cases B2
    obtain ⟨S3, A3, B3⟩ := exec_stmt_steps h4 f k
    exact ⟨S3, star_left (ss (Csem.Sstep.for f a2 a3 s k e _))
      (star_trans (eval_expression_steps h1 f (.Kfor2 a2 a3 s k))
        (star_left (ss (.for_true _ _ _ _ _ _ _ _ _ hb))
          (star_trans A1 (star_left (sc_for3 hnc B1)
            (star_trans A2 (star_left (ss (.skip_for4 _ _ _ _ _ _ _)) A3 rfl) rfl) rfl) rfl) rfl)
        rfl) (by trace_eq), B3⟩
  | .switch _ _ a sl _ _ v n _ _ _ h1 hsw h2 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kswitch2 k)
    have A0 := star_left (ss (.switch f a sl k e _))
      (star_trans (eval_expression_steps h1 f (.Kswitch1 sl k))
        (star_left (ss (.expr_switch _ _ _ _ _ _ _ _ hsw)) A1 rfl) rfl) rfl
    cases B1 with
    | normal =>
      exact ⟨_, star_right A0 (ss (.skip_break_switch _ _ _ _ _ (Or.inl rfl))) (by trace_eq),
        .normal⟩
    | break_ =>
      exact ⟨_, star_right A0 (ss (.skip_break_switch _ _ _ _ _ (Or.inr rfl))) (by trace_eq),
        .normal⟩
    | continue_ =>
      exact ⟨_, star_right A0 (ss (.continue_switch _ _ _ _)) (by trace_eq), .continue_⟩
    | return_none k' hk =>
      exact ⟨_, A0.trace_cast (by trace_eq), .return_none k' (by simpa [Csem.callCont] using hk)⟩
    | return_some v ty k' hk =>
      exact ⟨_, A0.trace_cast (by trace_eq),
        .return_some v ty k' (by simpa [Csem.callCont] using hk)⟩

/-- `Cstrategy.eval_funcall_to_steps` -/
theorem eval_funcall_steps {m fd args t m' res} (h : EvalFuncall ge m fd args t m' res)
    (k : Csem.Cont) (hk : Csem.IsCallCont k) :
    Smallstep.Star (Step ge) (.Callstate fd args k m) t (.Returnstate res k m') := by
  match h with
  | .internal _ f _ _ e _ _ m3 _ _ _ hnr halloc hbind hbody hres hfree =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps hbody f k
    have A0 := star_left (ss (.internal_function _ _ _ _ _ _ _ hnr halloc hbind)) A1 rfl
    have hck := isCallCont_callCont hk
    generalize hty : f.fn_return = ty at hres
    cases B1 with
    | normal =>
      cases ty <;> simp [outcomeResultValue] at hres
      subst hres
      exact star_right A0 (ss (.skip_call _ _ _ _ _ hk hfree)) (by trace_eq)
    | break_ => cases ty <;> simp [outcomeResultValue] at hres
    | continue_ => cases ty <;> simp [outcomeResultValue] at hres
    | return_none k' hk' =>
      cases ty <;> simp [outcomeResultValue] at hres
      subst hres
      have := Csem.Sstep.return_0 (ge := ge) f k' e m3 _ hfree
      rw [hk', hck] at this
      exact star_right A0 (ss this) (by trace_eq)
    | return_some v ty' k' hk' =>
      simp only [outcomeResultValue] at hres
      have := Csem.Sstep.return_2 (ge := ge) f v ty' k' e m3 _ _ (hty ▸ hres.2) hfree
      rw [hk', hck] at this
      exact star_right A0 (ss this) (by trace_eq)
  | .external _ _ _ _ _ _ _ _ _ h1 =>
    exact star_one (ss (.external_function _ _ _ _ _ _ _ _ _ _ h1))
end


/-! ## Diverging evaluations -/

/-- Rocq's `forever_N` with the order `<` on natural numbers: if every state
    satisfying `P` (with measure `n`) either makes at least one transition, or
    makes none but decreases the measure, and lands in `P` again, then `P`
    implies an infinite run (`forever_N_forever`). -/
theorem _root_.CC.Smallstep.forever_of_measure {σ : Type} {R : σ → Trace → σ → Prop}
    (P : σ → Nat → Traceinf → Prop)
    (hP : ∀ s n T, P s n T → ∃ (s' : σ) (n' : Nat) (t : Trace) (T' : Traceinf),
      (Smallstep.Plus R s t s' ∨ (Smallstep.Star R s t s' ∧ n' < n)) ∧ P s' n' T' ∧ T = Eappinf t T') :
    ∀ s n T, P s n T → Smallstep.Forever R s T := by
  have key : ∀ n s T, P s n T → ∃ (s' : σ) (t : Trace) (T' : Traceinf) (n' : Nat),
      Smallstep.Plus R s t s' ∧ P s' n' T' ∧ T = Eappinf t T' := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s T h
      obtain ⟨s', n', t, T', hst | ⟨hst, hlt⟩, hP', hT⟩ := hP s n T h
      · exact ⟨s', t, T', n', hst, hP', hT⟩
      · obtain ⟨s'', t'', T'', n'', hpl, hP'', hT'⟩ := ih n' hlt s' T' hP'
        exact ⟨s'', Eapp t t'', T'', n'', star_plus_trans hst hpl rfl, hP'',
          by rw [hT, hT', Eappinf_assoc]⟩
  intro s n T h
  refine forever_of_plus (fun s T => ∃ n, P s n T) ?_ s T ⟨n, h⟩
  intro s T ⟨n, h⟩
  obtain ⟨s', t, T', n', h1, h2, h3⟩ := key n s T h
  exact ⟨s', t, T', h1, ⟨n', h2⟩, h3⟩

mutual
/-- `Cstrategy.esize` -/
def esize : Csyntax.Expr → Nat
  | .Eloc _ _ _ _ => 1
  | .Evar _ _ => 1
  | .Ederef r1 _ => esize r1 + 1
  | .Efield l1 _ _ => esize l1 + 1
  | .Eval _ _ => 0
  | .Evalof l1 _ => esize l1 + 1
  | .Eaddrof l1 _ => esize l1 + 1
  | .Eunop _ r1 _ => esize r1 + 1
  | .Ebinop _ r1 r2 _ => esize r1 + esize r2 + 1
  | .Ecast r1 _ => esize r1 + 1
  | .Eseqand r1 _ _ => esize r1 + 1
  | .Eseqor r1 _ _ => esize r1 + 1
  | .Econdition r1 _ _ _ => esize r1 + 1
  | .Esizeof _ _ => 1
  | .Ealignof _ _ => 1
  | .Eassign l1 r2 _ => esize l1 + esize r2 + 1
  | .Eassignop _ l1 r2 _ _ => esize l1 + esize r2 + 1
  | .Epostincr _ l1 _ => esize l1 + 1
  | .Ecomma r1 r2 _ => esize r1 + esize r2 + 1
  | .Ecall r1 rl2 _ => esize r1 + esizelist rl2 + 1
  | .Ebuiltin _ _ rl _ => esizelist rl + 1
  | .Eparen r1 _ _ => esize r1 + 1

/-- `Cstrategy.esizelist` -/
def esizelist : Csyntax.ExprList → Nat
  | .Enil => 0
  | .Econs r1 rl2 => esize r1 + esizelist rl2 + 1
end

mutual
/-- `Cstrategy.leftcontext_size` -/
theorem leftcontext_size {k1} : ∀ {k2 C}, LeftContext k1 k2 C → ∀ e1 e2,
    esize e1 < esize e2 → esize (C e1) < esize (C e2)
  | _, _, .top _, _, _, h => h
  | _, _, .deref _ _ _ hC, _, _, h | _, _, .field _ _ _ _ hC, _, _, h
  | _, _, .rvalof _ _ _ hC, _, _, h | _, _, .addrof _ _ _ hC, _, _, h
  | _, _, .unop _ _ _ _ hC, _, _, h | _, _, .cast _ _ _ hC, _, _, h
  | _, _, .seqand _ _ _ _ hC, _, _, h | _, _, .seqor _ _ _ _ hC, _, _, h
  | _, _, .condition _ _ _ _ _ hC, _, _, h | _, _, .postincr _ _ _ _ hC, _, _, h
  | _, _, .paren _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC _ _ h; simp only [esize]; omega
  | _, _, .binop_left _ _ _ _ _ hC, _, _, h | _, _, .binop_right _ _ _ _ _ _ hC, _, _, h
  | _, _, .assign_left _ _ _ _ hC, _, _, h | _, _, .assign_right _ _ _ _ _ hC, _, _, h
  | _, _, .assignop_left _ _ _ _ _ _ hC, _, _, h
  | _, _, .assignop_right _ _ _ _ _ _ _ hC, _, _, h
  | _, _, .call_left _ _ _ _ hC, _, _, h | _, _, .comma _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC _ _ h; simp only [esize]; omega
  | _, _, .call_right _ _ _ _ _ hC, _, _, h | _, _, .builtin _ _ _ _ _ hC, _, _, h => by
    have := leftcontextlist_size hC _ _ h; simp only [esize]; omega

/-- `Cstrategy.leftcontextlist_size` -/
theorem leftcontextlist_size {k1} : ∀ {C}, LeftContextList k1 C → ∀ e1 e2,
    esize e1 < esize e2 → esizelist (C e1) < esizelist (C e2)
  | _, .head _ _ _ hC, _, _, h => by
    have := leftcontext_size hC _ _ h; simp only [esizelist]; omega
  | _, .tail _ _ _ _ hC, _, _, h => by
    have := leftcontextlist_size hC _ _ h; simp only [esizelist]; omega
end

/-- The strategy states from which a diverging big-step evaluation is
    pending, with the measure used by `forever_of_measure` (the four
    coinductive hypotheses `COF`, `COS`, `COE`, `COEL` of Rocq's
    `evalinf_funcall_steps`). -/
private inductive DivState (ge : Csem.CGenv) : Csem.State → Nat → Traceinf → Prop where
  | call (fd args k m T) : EvalinfFuncall ge m fd args T → DivState ge (.Callstate fd args k m) 0 T
  | stmt (f s k e m T) : ExecinfStmt ge e m s T → DivState ge (.State f s k e m) 0 T
  | expr (f K C a k e m T) :
      EvalinfExpr ge e m K a T → LeftContext K .RV C →
      DivState ge (.ExprState f (C a) k e m) (esize a) T
  | list (f C a1 al a ty k e m T) :
      EvalinfExprlist ge e m a T → LeftContext .RV .RV C → simple a1 = true →
      simplelist al = true →
      DivState ge (.ExprState f (C (.Ecall a1 (exprlistApp al a) ty)) k e m) (esizelist a) T

/-- The conclusion of one step of the divergence argument. -/
private abbrev DivNext (ge : Csem.CGenv) (S : Csem.State) (n : Nat) (T : Traceinf) : Prop :=
  ∃ (S' : Csem.State) (n' : Nat) (t : Trace) (T' : Traceinf),
    (Smallstep.Plus (Step ge) S t S' ∨ (Smallstep.Star (Step ge) S t S' ∧ n' < n)) ∧
      DivState ge S' n' T' ∧ T = Eappinf t T'

private theorem div_plus {S S' n n' T T'} (t : Trace) (h : Smallstep.Plus (Step ge) S t S')
    (hd : DivState ge S' n' T') (hT : T = Eappinf t T') : DivNext ge S n T :=
  ⟨S', n', t, T', .inl h, hd, hT⟩

private theorem div_star {S S' n n' T T'} (t : Trace) (h : Smallstep.Star (Step ge) S t S')
    (hd : DivState ge S' n' T') (hlt : n' < n) (hT : T = Eappinf t T') : DivNext ge S n T :=
  ⟨S', n', t, T', .inr ⟨h, hlt⟩, hd, hT⟩

/-- A pending subexpression evaluation in a smaller left context position. -/
private theorem div_left {S f k e m K' a0 T C' n} (hinf : EvalinfExpr ge e m K' a0 T)
    (hC : LeftContext K' .RV C') (hlt : esize a0 < n)
    (hS : S = .ExprState f (C' a0) k e m := by rfl) : DivNext ge S n T :=
  hS ▸ div_star E0 (.refl _) (.expr f K' C' a0 k e m T hinf hC) hlt (Eappinf_E0 T).symm

/-- One step of the divergence argument (Rocq: the body of
    `evalinf_funcall_steps`). -/
private theorem divState_next {S n T} (h : DivState ge S n T) : DivNext ge S n T := by
  cases h with
  | call fd args k m T hf =>
    cases hf with
    | internal _ f _ _ e _ _ hnr halloc hbind hbody =>
      exact div_plus E0 (plus_one (ss (.internal_function _ _ _ _ _ _ _ hnr halloc hbind)))
        (.stmt _ _ _ _ _ _ hbody) (Eappinf_E0 T).symm
  | stmt f s k e m T hs =>
    cases hs with
    | do_ _ _ a _ h1 =>
      exact div_plus E0 (plus_one (ss (.do_1 _ _ _ _ _)))
        (.expr f _ (fun x => x) a _ e m _ h1 (.top _)) (Eappinf_E0 _).symm
    | seq_1 _ _ s1 s2 _ h1 =>
      exact div_plus E0 (plus_one (ss (.seq _ _ _ _ _ _))) (.stmt _ _ _ _ _ _ h1)
        (Eappinf_E0 _).symm
    | seq_2 _ _ s1 s2 t1 m1 t2 h1 h2 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq s2 k)
      cases B1
      refine div_plus t1 (plus_left (ss (.seq _ _ _ _ _ _))
        (star_right A1 (ss (.skip_seq _ _ _ _ _)) rfl) ?_)
        (.stmt _ _ _ _ _ _ h2) rfl
      all_goals trace_eq
    | ifthenelse_test _ _ a s1 s2 _ h1 =>
      exact div_plus E0 (plus_one (ss (.ifthenelse_1 _ _ _ _ _ _ _)))
        (.expr f _ (fun x => x) a _ e m _ h1 (.top _)) (Eappinf_E0 _).symm
    | ifthenelse _ _ a s1 s2 t1 m1 v1 t2 b h1 hb h2 =>
      refine div_plus t1 (plus_left (ss (.ifthenelse_1 _ _ _ _ _ _ _))
        (star_right (eval_expression_steps h1 f (.Kifthenelse s1 s2 k))
          (ss (.ifthenelse_2 _ _ _ _ _ _ _ _ _ hb)) rfl) ?_)
        (.stmt _ _ _ _ _ _ h2) rfl
      all_goals trace_eq
    | return_some _ _ a _ h1 =>
      exact div_plus E0 (plus_one (ss (.return_1 _ _ _ _ _)))
        (.expr f _ (fun x => x) a _ e m _ h1 (.top _)) (Eappinf_E0 _).symm
    | while_test _ _ a s _ h1 =>
      exact div_plus E0 (plus_one (ss (Csem.Sstep.while _ _ _ _ _ _)))
        (.expr f _ (fun x => x) a _ e m _ h1 (.top _)) (Eappinf_E0 _).symm
    | while_body _ _ a s t1 m1 v t2 h1 hb h2 =>
      refine div_plus t1 (plus_left (ss (Csem.Sstep.while _ _ _ _ _ _))
        (star_right (eval_expression_steps h1 f (.Kwhile1 a s k))
          (ss (.while_true _ _ _ _ _ _ _ _ hb)) rfl) ?_)
        (.stmt _ _ _ _ _ _ h2) rfl
      all_goals trace_eq
    | while_loop _ _ a s t1 m1 v t2 m2 out1 t3 h1 hb h2 hnc h3 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kwhile2 a s k)
      refine div_plus (Eapp t1 t2) (plus_left (ss (Csem.Sstep.while _ _ _ _ _ _))
        (star_trans (eval_expression_steps h1 f (.Kwhile1 a s k))
          (star_left (ss (.while_true _ _ _ _ _ _ _ _ hb))
            (star_right A1 (sc_while hnc B1) rfl) rfl) rfl) ?_)
        (.stmt _ _ _ _ _ _ h3) (Eappinf_assoc _ _ _).symm
      all_goals trace_eq
    | dowhile_body _ _ s a _ h1 =>
      exact div_plus E0 (plus_one (ss (.dowhile _ _ _ _ _ _))) (.stmt _ _ _ _ _ _ h1)
        (Eappinf_E0 _).symm
    | dowhile_test _ _ s a t1 m1 out1 t2 h1 hnc h2 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kdowhile1 a s k)
      refine div_plus t1 (plus_left (ss (.dowhile _ _ _ _ _ _))
        (star_right A1 (sc_dowhile hnc B1) rfl) ?_)
        (.expr f _ (fun x => x) a _ e _ _ h2 (.top _)) rfl
      all_goals trace_eq
    | dowhile_loop _ _ s a t1 m1 out1 t2 m2 v t3 h1 hnc h2 hb h3 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kdowhile1 a s k)
      refine div_plus (Eapp t1 t2) (plus_left (ss (.dowhile _ _ _ _ _ _))
        (star_trans A1 (star_left (sc_dowhile hnc B1)
          (star_right (eval_expression_steps h2 f (.Kdowhile2 a s k))
            (ss (.dowhile_true _ _ _ _ _ _ _ _ hb)) rfl) rfl) rfl) ?_)
        (.stmt _ _ _ _ _ _ h3) (Eappinf_assoc _ _ _).symm
      all_goals trace_eq
    | for_start_1 _ _ s a1 a2 a3 _ h1 =>
      have hne : a1 ≠ .Sskip := by
        intro heq; subst heq; cases h1
      exact div_plus E0 (plus_one (ss (.for_start _ _ _ _ _ _ _ _ hne)))
        (.stmt _ _ _ _ _ _ h1) (Eappinf_E0 _).symm
    | for_start_2 _ _ s a1 a2 a3 m1 t1 t2 h1 hne h2 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq (.Sfor .Sskip a2 a3 s) k)
      cases B1
      refine div_plus t1 (plus_left (ss (.for_start _ _ _ _ _ _ _ _ hne))
        (star_right A1 (ss (.skip_seq _ _ _ _ _)) rfl) ?_)
        (.stmt _ _ _ _ _ _ h2) rfl
      all_goals trace_eq
    | for_test _ _ s a2 a3 _ h1 =>
      exact div_plus E0 (plus_one (ss (Csem.Sstep.for _ _ _ _ _ _ _)))
        (.expr f _ (fun x => x) a2 _ e m _ h1 (.top _)) (Eappinf_E0 _).symm
    | for_body _ _ s a2 a3 t1 m1 v t2 h1 hb h2 =>
      refine div_plus t1 (plus_left (ss (Csem.Sstep.for _ _ _ _ _ _ _))
        (star_right (eval_expression_steps h1 f (.Kfor2 a2 a3 s k))
          (ss (.for_true _ _ _ _ _ _ _ _ _ hb)) rfl) ?_)
        (.stmt _ _ _ _ _ _ h2) rfl
      all_goals trace_eq
    | for_next _ _ s a2 a3 t1 m1 v t2 m2 out1 t3 h1 hb h2 hnc h3 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kfor3 a2 a3 s k)
      refine div_plus (Eapp t1 t2) (plus_left (ss (Csem.Sstep.for _ _ _ _ _ _ _))
        (star_trans (eval_expression_steps h1 f (.Kfor2 a2 a3 s k))
          (star_left (ss (.for_true _ _ _ _ _ _ _ _ _ hb))
            (star_right A1 (sc_for3 hnc B1) rfl) rfl) rfl) ?_)
        (.stmt _ _ _ _ _ _ h3) (Eappinf_assoc _ _ _).symm
      all_goals trace_eq
    | for_loop _ _ s a2 a3 t1 m1 v t2 m2 out1 t3 m3 t4 h1 hb h2 hnc h3 h4 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h2 f (.Kfor3 a2 a3 s k)
      obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h3 f (.Kfor4 a2 a3 s k)
      cases B2
      refine div_plus (Eapp t1 (Eapp t2 t3)) (plus_left (ss (Csem.Sstep.for _ _ _ _ _ _ _))
        (star_trans (eval_expression_steps h1 f (.Kfor2 a2 a3 s k))
          (star_left (ss (.for_true _ _ _ _ _ _ _ _ _ hb))
            (star_trans A1 (star_left (sc_for3 hnc B1)
              (star_right A2 (ss (.skip_for4 _ _ _ _ _ _ _)) rfl) rfl) rfl) rfl) rfl) ?_)
        (.stmt _ _ _ _ _ _ h4) (by rw [Eappinf_assoc, Eappinf_assoc])
      all_goals trace_eq
    | switch_expr _ _ a sl _ h1 =>
      exact div_plus E0 (plus_one (ss (.switch _ _ _ _ _ _)))
        (.expr f _ (fun x => x) a _ e m _ h1 (.top _)) (Eappinf_E0 _).symm
    | switch_body _ _ a sl t1 m1 v n t2 h1 hsw h2 =>
      refine div_plus t1 (plus_left (ss (.switch _ _ _ _ _ _))
        (star_right (eval_expression_steps h1 f (.Kswitch1 sl k))
          (ss (.expr_switch _ _ _ _ _ _ _ _ hsw)) rfl) ?_)
        (.stmt _ _ _ _ _ _ h2) rfl
      all_goals trace_eq
  | expr f K C a k e m T hinf hC =>
    cases hinf with
    | field _ _ a0 _ fid ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.field _ _ fid ty (.top _)))
        (by simp only [esize]; omega)
    | valof _ _ a0 _ ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.rvalof _ _ ty (.top _)))
        (by simp only [esize]; omega)
    | deref _ _ a0 _ ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.deref _ _ ty (.top _)))
        (by simp only [esize]; omega)
    | addrof _ _ a0 _ ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.addrof _ _ ty (.top _)))
        (by simp only [esize]; omega)
    | unop _ _ a0 _ op ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.unop _ _ op ty (.top _)))
        (by simp only [esize]; omega)
    | binop_left _ _ a1 _ a2 op ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.binop_left _ _ op a2 ty (.top _)))
        (by simp only [esize]; omega)
    | binop_right _ _ a1 t1 m' a1' a2 t2 op ty h1 h2 =>
      obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Ebinop op x a2 ty)) f k
        (leftcontext_compose hC (.binop_left _ _ _ _ _ (.top _)))
      exact div_star t1 D (.expr f _ (fun x => C (.Ebinop op a1' x ty)) a2 k e m' t2 h2
        (leftcontext_compose hC (.binop_right _ _ _ _ _ A (.top _))))
        (by simp only [esize]; omega) rfl
    | cast _ _ a0 _ ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.cast _ _ ty (.top _)))
        (by simp only [esize]; omega)
    | seqand _ _ a1 a2 ty _ h0 =>
      exact div_left h0 (leftcontext_compose hC (.seqand _ _ a2 ty (.top _)))
        (by simp only [esize]; omega)
    | seqand_2 _ _ a1 a2 ty t1 m' a1' v1 t2 h1 hv1 hb h2 =>
      obtain ⟨_, B, D⟩ := eval_expr_steps h1 (fun x => C (.Eseqand x a2 ty)) f k
        (leftcontext_compose hC (.seqand _ _ _ _ (.top _)))
      exact div_plus t1 (star_plus_trans D (plus_one (es (.seqand_true f C a1' a2 ty k e m' v1 hC
        hv1 (by rw [B]; exact hb)))) (E0_right t1).symm)
        (.expr f _ (fun x => C (.Eparen x type_bool ty)) a2 k e m' t2 h2
          (leftcontext_compose hC (.paren _ _ _ _ (.top _)))) rfl
    | seqor _ _ a1 a2 ty _ h0 =>
      exact div_left h0 (leftcontext_compose hC (.seqor _ _ a2 ty (.top _)))
        (by simp only [esize]; omega)
    | seqor_2 _ _ a1 a2 ty t1 m' a1' v1 t2 h1 hv1 hb h2 =>
      obtain ⟨_, B, D⟩ := eval_expr_steps h1 (fun x => C (.Eseqor x a2 ty)) f k
        (leftcontext_compose hC (.seqor _ _ _ _ (.top _)))
      exact div_plus t1 (star_plus_trans D (plus_one (es (.seqor_false f C a1' a2 ty k e m' v1 hC
        hv1 (by rw [B]; exact hb)))) (E0_right t1).symm)
        (.expr f _ (fun x => C (.Eparen x type_bool ty)) a2 k e m' t2 h2
          (leftcontext_compose hC (.paren _ _ _ _ (.top _)))) rfl
    | condition _ _ a1 a2 a3 ty _ h0 =>
      exact div_left h0 (leftcontext_compose hC (.condition _ _ a2 a3 ty (.top _)))
        (by simp only [esize]; omega)
    | condition_2 _ _ a1 a2 a3 ty t1 m' a1' v1 t2 b h1 hv1 hb h2 =>
      obtain ⟨_, B, D⟩ := eval_expr_steps h1 (fun x => C (.Econdition x a2 a3 ty)) f k
        (leftcontext_compose hC (.condition _ _ _ _ _ (.top _)))
      exact div_plus t1 (star_plus_trans D (plus_one (es (.condition f C a1' a2 a3 ty k e m' v1 b hC
        hv1 (by rw [B]; exact hb)))) (E0_right t1).symm)
        (.expr f _ (fun x => C (.Eparen x ty ty)) _ k e m' t2 h2
          (leftcontext_compose hC (.paren _ _ _ _ (.top _)))) rfl
    | assign_left _ _ a1 _ a2 ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.assign_left _ _ a2 ty (.top _)))
        (by simp only [esize]; omega)
    | assign_right _ _ a1 t1 m' a1' a2 t2 ty h1 h2 =>
      obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Eassign x a2 ty)) f k
        (leftcontext_compose hC (.assign_left _ _ _ _ (.top _)))
      exact div_star t1 D (.expr f _ (fun x => C (.Eassign a1' x ty)) a2 k e m' t2 h2
        (leftcontext_compose hC (.assign_right _ _ _ _ A (.top _))))
        (by simp only [esize]; omega) rfl
    | assignop_left _ _ a1 _ a2 op tyres ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.assignop_left _ _ op a2 tyres ty (.top _)))
        (by simp only [esize]; omega)
    | assignop_right _ _ a1 t1 m' a1' a2 t2 op tyres ty h1 h2 =>
      obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Eassignop op x a2 tyres ty)) f k
        (leftcontext_compose hC (.assignop_left _ _ _ _ _ _ (.top _)))
      exact div_star t1 D (.expr f _ (fun x => C (.Eassignop op a1' x tyres ty)) a2 k e m' t2 h2
        (leftcontext_compose hC (.assignop_right _ _ _ _ _ _ A (.top _))))
        (by simp only [esize]; omega) rfl
    | postincr _ _ a0 _ id ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.postincr _ _ id ty (.top _)))
        (by simp only [esize]; omega)
    | comma_left _ _ a1 _ a2 ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.comma _ _ a2 ty (.top _)))
        (by simp only [esize]; omega)
    | comma_right _ _ a1 t1 m1 a1' v1 a2 t2 ty h1 hv1 hty h2 =>
      obtain ⟨_, _, D⟩ := eval_expr_steps h1 (fun x => C (.Ecomma x a2 ty)) f k
        (leftcontext_compose hC (.comma _ _ _ _ (.top _)))
      exact div_plus t1 (star_plus_trans D (plus_one (es (.comma f C a1' a2 ty k e m1 v1 hC hv1 hty)))
        (E0_right t1).symm) (.expr f _ C a2 k e m1 t2 h2 hC) rfl
    | call_left _ _ a1 _ a2 ty h0 =>
      exact div_left h0 (leftcontext_compose hC (.call_left _ _ a2 ty (.top _)))
        (by simp only [esize]; omega)
    | call_right _ _ a1 t1 m1 a1' a2 t2 ty h1 h2 =>
      obtain ⟨A, _, D⟩ := eval_expr_steps h1 (fun x => C (.Ecall x a2 ty)) f k
        (leftcontext_compose hC (.call_left _ _ _ _ (.top _)))
      exact div_star t1 D (.list f C a1' .Enil a2 ty k e m1 t2 h2 hC A rfl)
        (by simp only [esize]; omega) rfl
    | call _ _ rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs targs tres cconv fd t3 h1 h2 hvf hvargs
        hcl hfind hty h3 =>
      obtain ⟨A, B, D1⟩ := eval_expr_steps h1 (fun x => C (.Ecall x rargs ty)) f k
        (leftcontext_compose hC (.call_left _ _ _ _ (.top _)))
      obtain ⟨_, D2⟩ := eval_exprlist_steps h2 rf' .Enil ty C f k hC A rfl
      exact div_plus (Eapp t1 t2) (star_plus_trans D1 (star_plus_trans D2
        (plus_one (es (.call f C rf' rargs' ty k e m2 targs tres cconv vf vargs fd hC
          (by rw [B]; exact hcl) hvf hvargs hfind hty))) (E0_right t2).symm) rfl)
        (.call _ _ _ _ _ h3) (Eappinf_assoc _ _ _).symm
  | list f C a1 al a ty k e m T hinf hC hs1 hs2 =>
    cases hinf with
    | cons_left _ _ a0 al0 _ h0 =>
      exact div_left h0 (leftcontext_compose hC
        (.call_right _ _ _ _ hs1 (exprlist_app_leftcontext al0 al hs2)))
        (by simp only [esizelist]; omega)
    | cons_right _ _ a0 al0 t1 m1 a0' t2 h1 h2 =>
      obtain ⟨A, _, D⟩ := eval_expr_steps h1
        (fun x => C (.Ecall a1 (exprlistApp al (.Econs x al0)) ty)) f k
        (leftcontext_compose hC (.call_right _ _ _ _ hs1 (exprlist_app_leftcontext al0 al hs2)))
      have hd := DivState.list f C a1 (exprlistApp al (.Econs a0' .Enil)) al0 ty k e m1 t2 h2 hC hs1
        (by rw [exprlist_app_simple]; simp [simplelist, hs2, A])
      rw [exprlist_app_assoc] at hd
      exact div_star t1 D hd (by simp only [esizelist]; omega) rfl

/-- `Cstrategy.evalinf_funcall_steps` (as `forever` rather than `forever_N`). -/
theorem evalinf_funcall_forever {m fd args T} (k : Csem.Cont) (h : EvalinfFuncall ge m fd args T) :
    Smallstep.Forever (Step ge) (.Callstate fd args k m) T :=
  Smallstep.forever_of_measure (DivState ge) (fun _ _ _ h => divState_next h) _ 0 T
    (.call _ _ _ _ _ h)

/-- A diverging statement execution gives an infinite run of the strategy. -/
theorem execinf_stmt_forever {e m s T} (f : Csyntax.Function) (k : Csem.Cont)
    (h : ExecinfStmt ge e m s T) : Smallstep.Forever (Step ge) (.State f s k e m) T :=
  Smallstep.forever_of_measure (DivState ge) (fun _ _ _ h => divState_next h) _ 0 T
    (.stmt _ _ _ _ _ _ h)

/-- A diverging expression evaluation gives an infinite run of the strategy. -/
theorem evalinf_expr_forever {e m K a T} (C : Csyntax.Expr → Csyntax.Expr) (f : Csyntax.Function)
    (k : Csem.Cont) (h : EvalinfExpr ge e m K a T) (hC : LeftContext K .RV C) :
    Smallstep.Forever (Step ge) (.ExprState f (C a) k e m) T :=
  Smallstep.forever_of_measure (DivState ge) (fun _ _ _ h => divState_next h) _ _ T
    (.expr _ _ _ _ _ _ _ _ h hC)

/-! ## Whole programs -/

/-- `Cstrategy.bigstep_semantics_sound`: every terminating or diverging
    big-step execution of `p` is matched by a run of the strategy semantics
    `Cstrategy.semantics p`. -/
theorem bigstep_semantics_sound (p : Csyntax.Program) :
    BigstepSound (bigstepSemantics p) (semantics p) where
  bigstep_terminates_sound := by
    intro t r h
    cases h with
    | intro b f m0 m1 _ _ hinit hsym hfun htype heval =>
      exact ⟨_, _, .intro b f m0 hinit hsym hfun htype,
        eval_funcall_steps heval .Kstop trivial, .intro r m1⟩
  bigstep_diverges_sound := by
    intro T h
    cases h with
    | intro b f m0 _ hinit hsym hfun htype heval =>
      exact ⟨_, .intro b f m0 hinit hsym hfun htype, evalinf_funcall_forever .Kstop heval⟩


/-- A terminating big-step execution of `p` is a `Terminates` behaviour of
    the strategy semantics (`behavior_bigstep_terminates`). -/
theorem bigstep_terminates_behaves {p : Csyntax.Program} {t r}
    (h : (bigstepSemantics p).bigstep_terminates t r) :
    ProgramBehaves (semantics p) (.Terminates t r) :=
  behavior_bigstep_terminates (bigstep_semantics_sound p) h

/-- A diverging big-step execution of `p` is a reactive behaviour of the
    strategy semantics, or a silent divergence after a finite prefix of its
    trace (`behavior_bigstep_diverges`). -/
theorem bigstep_diverges_behaves {p : Csyntax.Program} {T}
    (h : (bigstepSemantics p).bigstep_diverges T) :
    ProgramBehaves (semantics p) (.Reacts T) ∨
    ∃ t, ProgramBehaves (semantics p) (.Diverges t) ∧ ∃ T', T = Eappinf t T' :=
  behavior_bigstep_diverges (bigstep_semantics_sound p) h

end Cstrategy
end CC
