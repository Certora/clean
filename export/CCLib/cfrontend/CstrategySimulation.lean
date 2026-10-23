/-
  `cfrontend/Cstrategy.v`, continued: correctness of the strategy.
  `estep_simulation`: every step of the deterministic strategy is matched by a
  nonempty sequence of steps of the nondeterministic CompCert C semantics.
-/
import CCLib.cfrontend.CstrategyDecompose

namespace CC
namespace Cstrategy
open Smallstep (star_trans star_one star_left plus_left plus_right star_plus_trans star_inv)

section SIMULATION
variable {ge : Csem.CGenv}

/-- A head r-reduction at a reduction context is a step. -/
theorem rstep {C f a k e m t a' m'} (hC : Csem.Context .RV .RV C) (hr : Csem.Rred ge a m t a' m') :
    Csem.Step ge (.ExprState f (C a) k e m) t (.ExprState f (C a') k e m') :=
  .inl (.rred C f a k e m t a' m' hr hC)

/-- Composition of a left context with a one-constructor context. -/
theorem lctx {k1 k2 C1 C} (h1 : Csem.Context k1 k2 C1) (hC : LeftContext k2 .RV C) :
    Csem.Context k1 .RV (fun x => C (C1 x)) :=
  context_compose h1 (leftcontext_context hC)

theorem semIncrdecr_eq (id : Cop.IncrOrDecr) (cenv v ty m) :
    Cop.semBinaryOperation cenv (match id with | .Incr => Binop.Oadd | .Decr => Binop.Osub)
      v ty (.Vint Integers.Int.one) type_int32s m = Cop.semIncrdecr cenv id v ty m := by
  cases id <;> rfl

/-- `Cstrategy.estep_simulation`: every step of the strategy is a nonempty
    sequence of steps of the nondeterministic semantics. -/
theorem estep_simulation {S t S'} (h : Estep ge S t S') : Smallstep.Plus (Csem.Step ge) S t S' := by
  cases h with
  | expr f r k e m v ty hr hnv hty =>
    subst hty
    rcases star_inv (eval_simple_rvalue_steps (f := f) (k := k) hr (C := fun x => x) (.top _)) with
      ⟨heq, _⟩ | hp
    · injection heq with _ h2; rw [← h2] at hnv; exact (hnv : False).elim
    · exact hp
  | rvalof_volatile f C l ty k e m b ofs bf t v hC hl hd hty hvol =>
    subst hty
    exact plus_right (eval_simple_lvalue_steps hl (lctx (.rvalof _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.rvalof _ _ _ _ _ _ _ hd)) rfl
  | seqand_true f C r1 r2 ty k e m v hC hr hb =>
    exact plus_right (eval_simple_rvalue_steps hr (lctx (.seqand _ _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.seqand_true _ _ _ _ _ hb)) rfl
  | seqand_false f C r1 r2 ty k e m v hC hr hb =>
    exact plus_right (eval_simple_rvalue_steps hr (lctx (.seqand _ _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.seqand_false _ _ _ _ _ hb)) rfl
  | seqor_true f C r1 r2 ty k e m v hC hr hb =>
    exact plus_right (eval_simple_rvalue_steps hr (lctx (.seqor _ _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.seqor_true _ _ _ _ _ hb)) rfl
  | seqor_false f C r1 r2 ty k e m v hC hr hb =>
    exact plus_right (eval_simple_rvalue_steps hr (lctx (.seqor _ _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.seqor_false _ _ _ _ _ hb)) rfl
  | condition f C r1 r2 r3 ty k e m v b hC hr hb =>
    exact plus_right (eval_simple_rvalue_steps hr (lctx (.condition _ _ _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.condition _ _ _ _ _ _ _ hb)) rfl
  | assign f C l r ty k e m b ofs bf v v1 t m' v' hC hl hr hc ha hty =>
    subst hty
    exact star_plus_trans (eval_simple_lvalue_steps hl (lctx (.assign_left _ _ _ _ (.top _)) hC))
      (plus_right (eval_simple_rvalue_steps hr (lctx (.assign_right _ _ _ _ (.top _)) hC))
        (rstep (leftcontext_context hC) (.assign _ _ _ _ _ _ _ _ _ _ _ hc ha)) rfl) rfl
  | assignop f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1 t2 m' v' t hC hl hd hr hop hcast ha
      hty ht =>
    subst hty ht
    refine star_plus_trans (eval_simple_lvalue_steps hl (lctx (.assignop_left _ _ _ _ _ _ (.top _)) hC))
      (star_plus_trans (eval_simple_rvalue_steps hr (lctx (.assignop_right _ _ _ _ _ _ (.top _)) hC))
        (plus_left (rstep (leftcontext_context hC) (.assignop _ _ _ _ _ _ _ _ _ _ _ hd))
          (star_left (rstep (C := fun x => C (.Eassign (.Eloc b ofs bf (Csyntax.typeof l)) x (Csyntax.typeof l)))
              (lctx (.assign_right _ _ _ _ (.top _)) hC) (.binop _ _ _ _ _ _ _ _ hop))
            (star_one (rstep (leftcontext_context hC) (.assign _ _ _ _ _ _ _ _ _ _ _ hcast ha))) rfl)
          rfl) rfl) ?_
    simp [E0, Eapp]
  | assignop_stuck f C op l r tyres ty k e m b ofs bf v1 v2 t hC hl hd hr hmatch hty =>
    subst hty
    refine star_plus_trans (eval_simple_lvalue_steps hl (lctx (.assignop_left _ _ _ _ _ _ (.top _)) hC))
      (star_plus_trans (eval_simple_rvalue_steps hr (lctx (.assignop_right _ _ _ _ _ _ (.top _)) hC))
        (plus_left (rstep (leftcontext_context hC) (.assignop _ _ _ _ _ _ _ _ _ _ _ hd)) ?_
          (show t = Eapp t E0 by simp [E0, Eapp])) rfl) rfl
    cases hop : Cop.semBinaryOperation ge.genv_cenv op v1 (Csyntax.typeof l) v2 (Csyntax.typeof r) m with
    | some v3 =>
      refine star_left (rstep (C := fun x => C (.Eassign (.Eloc b ofs bf (Csyntax.typeof l)) x (Csyntax.typeof l)))
          (lctx (.assign_right _ _ _ _ (.top _)) hC) (.binop _ _ _ _ _ _ _ _ hop))
        (star_one (.inl (.stuck C f _ k e m .RV (leftcontext_context hC) ?_))) rfl
      intro hsafe
      obtain ⟨v4, m', v', t', _, hc, ha⟩ := imm_safe_inv hsafe
      simp only [hop, hc] at hmatch
      exact hmatch t' m' v' ha
    | none =>
      refine star_one (.inl (.stuck (fun x => C (.Eassign (.Eloc b ofs bf (Csyntax.typeof l)) x
        (Csyntax.typeof l))) f _ k e m .RV (lctx (.assign_right _ _ _ _ (.top _)) hC) ?_))
      intro hsafe
      obtain ⟨v3, hv3⟩ := imm_safe_inv hsafe
      rw [hop] at hv3; cases hv3
  | postincr f C id l ty k e m b ofs bf v1 v2 v3 t1 t2 m' v' t hC hl hd hinc hcast ha hty ht =>
    subst hty ht
    have hC0 := leftcontext_context hC
    refine star_plus_trans (eval_simple_lvalue_steps hl (lctx (.postincr _ _ _ _ (.top _)) hC))
      (plus_left (rstep hC0 (.postincr _ _ _ _ _ _ _ _ _ hd rfl))
        (star_left (rstep (C := fun x => C (.Ecomma (.Eassign (.Eloc b ofs bf (Csyntax.typeof l)) x (Csyntax.typeof l)) (.Eval v1 (Csyntax.typeof l)) (Csyntax.typeof l))) (context_compose (.assign_right _ _ _ _ (.top _))
            (context_compose (.comma _ _ _ _ (.top _)) hC0))
          (.binop _ _ _ _ _ _ _ _ ((semIncrdecr_eq id _ _ _ _).trans hinc)))
          (star_left (rstep (C := fun x => C (.Ecomma x (.Eval v1 (Csyntax.typeof l)) (Csyntax.typeof l))) (context_compose (.comma _ _ _ _ (.top _)) hC0)
              (.assign _ _ _ _ _ _ _ _ _ _ _ hcast ha))
            (star_one (rstep (C := C) hC0 (.comma _ _ _ _ _ rfl))) rfl) rfl) rfl) ?_
    simp [E0, Eapp]
  | postincr_stuck f C id l ty k e m b ofs bf v1 t hC hl hd hmatch hty =>
    subst hty
    have hC0 := leftcontext_context hC
    refine star_plus_trans (eval_simple_lvalue_steps hl (lctx (.postincr _ _ _ _ (.top _)) hC))
      (plus_left (rstep hC0 (.postincr _ _ _ _ _ _ _ _ _ hd rfl)) ?_
        (show t = Eapp t E0 by simp [E0, Eapp])) rfl
    cases hinc : Cop.semIncrdecr ge.genv_cenv id v1 (Csyntax.typeof l) m with
    | some v2 =>
      refine star_left (rstep (C := fun x => C (.Ecomma (.Eassign (.Eloc b ofs bf (Csyntax.typeof l)) x (Csyntax.typeof l)) (.Eval v1 (Csyntax.typeof l)) (Csyntax.typeof l))) (context_compose (.assign_right _ _ _ _ (.top _))
            (context_compose (.comma _ _ _ _ (.top _)) hC0))
          (.binop _ _ _ _ _ _ _ _ ((semIncrdecr_eq id _ _ _ _).trans hinc)))
        (star_one (.inl (.stuck (fun x => C (.Ecomma x (.Eval v1 (Csyntax.typeof l)) (Csyntax.typeof l))) f _ k e m .RV (context_compose (.comma _ _ _ _ (.top _)) hC0) ?_)))
        rfl
      intro hsafe
      obtain ⟨v4, m', v', t', _, hc, ha⟩ := imm_safe_inv hsafe
      simp only [hinc, hc] at hmatch
      exact hmatch t' m' v' ha
    | none =>
      refine star_one (.inl (.stuck (fun x => C (.Ecomma (.Eassign (.Eloc b ofs bf (Csyntax.typeof l)) x (Csyntax.typeof l)) (.Eval v1 (Csyntax.typeof l)) (Csyntax.typeof l))) f _ k e m .RV (context_compose (.assign_right _ _ _ _ (.top _))
            (context_compose (.comma _ _ _ _ (.top _)) hC0)) ?_))
      intro hsafe
      obtain ⟨v3, hv3⟩ := imm_safe_inv hsafe
      have h' := (semIncrdecr_eq id ge.genv_cenv v1 (Csyntax.typeof l) m).symm.trans hv3
      rw [hinc] at h'; cases h'
  | comma f C r1 r2 ty k e m v hC hr hty =>
    exact plus_right (eval_simple_rvalue_steps hr (lctx (.comma _ _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.comma _ _ _ _ _ hty.symm)) rfl
  | paren f C r tycast ty k e m v1 v hC hr hc =>
    exact plus_right (eval_simple_rvalue_steps hr (lctx (.paren _ _ _ _ (.top _)) hC))
      (rstep (leftcontext_context hC) (.paren _ _ _ _ _ _ hc)) rfl
  | call f C rf rargs ty k e m targs tres cconv vf vargs fd hC hcl hrf hargs hfd hty =>
    obtain ⟨vl', A, B⟩ := eval_simple_list_implies hargs
    have hC0 := leftcontext_context hC
    exact star_plus_trans (eval_simple_rvalue_steps hrf (lctx (.call_left _ _ _ _ (.top _)) hC))
      (plus_right (eval_simple_list_steps B (C := fun x => C (.Ecall (.Eval vf (Csyntax.typeof rf)) x ty))
          (.call _ .Enil ty C hC0))
        (.inl (.call C f _ k e m fd vargs ty (.call _ _ _ _ _ _ _ _ _ _ hfd A hty hcl) hC0)) rfl) rfl
  | builtin f C ef tyargs rargs ty k e m vargs t vres m' hC hargs hext =>
    obtain ⟨vl', A, B⟩ := eval_simple_list_implies hargs
    have hC0 := leftcontext_context hC
    exact plus_right (eval_simple_list_steps B (C := fun x => C (.Ebuiltin ef tyargs x ty))
        (.builtin _ _ .Enil ty C hC0))
      (rstep hC0 (.builtin _ _ _ _ _ _ _ _ _ A hext)) rfl

end SIMULATION

section CANSTEP
variable {ge : Csem.CGenv}

/-- The expression is not a value (`match a with Eval _ _ => False | _ => True`). -/
def NotVal : Csyntax.Expr → Prop
  | .Eval _ _ => False
  | _ => True

/-- `Cstrategy.can_estep`: a safe expression state whose expression is not a
    value can take a step of the strategy. -/
theorem can_estep {f a k e m} (hsafe : Safe ge (.ExprState f a k e m))
    (hnv : NotVal a) :
    ∃ t S, Estep ge (.ExprState f a k e m) t S := by
  rcases decompose_topexpr hsafe with hs | ⟨C, b, rfl, hse, hC⟩
  · obtain ⟨v, E⟩ := simple_can_eval a (from_ := .RV) (C := fun x => x) hs (.top _) hsafe
    exact ⟨_, _, .expr _ _ _ _ _ _ _ E (by cases a <;> first | exact hnv.elim | trivial) rfl⟩
  clear hnv
  have hC0 := leftcontext_context hC
  cases b with
  | Evalof l ty =>
    obtain ⟨hs, hvol⟩ := hse
    obtain ⟨b1, ofs, bf, E1, S1⟩ :=
      simple_can_eval_lval (C := fun x => C (.Evalof x ty)) hs (lctx (.rvalof _ _ _ (.top _)) hC) hsafe
    obtain ⟨hty, t, v, hd⟩ := safe_inv S1 hC0
    subst hty
    exact ⟨_, _, .rvalof_volatile _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd rfl hvol⟩
  | Eseqand r1 r2 ty =>
    obtain ⟨v1, E1, S1⟩ :=
      simple_can_eval_rval (C := fun x => C (.Eseqand x r2 ty)) hse (lctx (.seqand _ _ _ _ (.top _)) hC) hsafe
    obtain ⟨bb, hb⟩ := safe_inv S1 hC0
    cases bb
    · exact ⟨_, _, .seqand_false _ _ _ _ _ _ _ _ _ hC E1 hb⟩
    · exact ⟨_, _, .seqand_true _ _ _ _ _ _ _ _ _ hC E1 hb⟩
  | Eseqor r1 r2 ty =>
    obtain ⟨v1, E1, S1⟩ :=
      simple_can_eval_rval (C := fun x => C (.Eseqor x r2 ty)) hse (lctx (.seqor _ _ _ _ (.top _)) hC) hsafe
    obtain ⟨bb, hb⟩ := safe_inv S1 hC0
    cases bb
    · exact ⟨_, _, .seqor_false _ _ _ _ _ _ _ _ _ hC E1 hb⟩
    · exact ⟨_, _, .seqor_true _ _ _ _ _ _ _ _ _ hC E1 hb⟩
  | Econdition r1 r2 r3 ty =>
    obtain ⟨v1, E1, S1⟩ := simple_can_eval_rval (C := fun x => C (.Econdition x r2 r3 ty)) hse
      (lctx (.condition _ _ _ _ _ (.top _)) hC) hsafe
    obtain ⟨bb, hb⟩ := safe_inv S1 hC0
    exact ⟨_, _, .condition _ _ _ _ _ _ _ _ _ _ _ hC E1 hb⟩
  | Eassign l r ty =>
    obtain ⟨hs1, hs2⟩ := hse
    obtain ⟨b1, ofs, bf, E1, S1⟩ := simple_can_eval_lval (C := fun x => C (.Eassign x r ty)) hs1
      (lctx (.assign_left _ _ _ _ (.top _)) hC) hsafe
    obtain ⟨v, E2, S2⟩ := simple_can_eval_rval
      (C := fun x => C (.Eassign (.Eloc b1 ofs bf (Csyntax.typeof l)) x ty)) hs2
      (lctx (.assign_right _ _ _ _ (.top _)) hC) S1
    obtain ⟨v1, m', v', t, hty, hc, ha⟩ := safe_inv S2 hC0
    subst hty
    exact ⟨_, _, .assign _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 E2 hc ha rfl⟩
  | Eassignop op l r tyres ty =>
    obtain ⟨hs1, hs2⟩ := hse
    obtain ⟨b1, ofs, bf, E1, S1⟩ := simple_can_eval_lval (C := fun x => C (.Eassignop op x r tyres ty))
      hs1 (lctx (.assignop_left _ _ _ _ _ _ (.top _)) hC) hsafe
    obtain ⟨v, E2, S2⟩ := simple_can_eval_rval
      (C := fun x => C (.Eassignop op (.Eloc b1 ofs bf (Csyntax.typeof l)) x tyres ty)) hs2
      (lctx (.assignop_right _ _ _ _ _ _ (.top _)) hC) S1
    obtain ⟨t1, v1, hty, hd⟩ := safe_inv S2 hC0
    subst hty
    cases hop : Cop.semBinaryOperation ge.genv_cenv op v1 (Csyntax.typeof l) v (Csyntax.typeof r) m with
    | none =>
      exact ⟨_, _, .assignop_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd E2 (by simp [hop]) rfl⟩
    | some v3 =>
      cases hc : Cop.semCast v3 tyres (Csyntax.typeof l) m with
      | none =>
        exact ⟨_, _, .assignop_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd E2
          (by simp [hop, hc]) rfl⟩
      | some v4 =>
        by_cases hex : ∃ t2 m' v', Csem.AssignLoc ge (Csyntax.typeof l) m b1 ofs bf v4 t2 m' v'
        · obtain ⟨t2, m', v', ha⟩ := hex
          exact ⟨_, _, .assignop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd E2 hop hc ha
            rfl rfl⟩
        · refine ⟨_, _, .assignop_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd E2 ?_ rfl⟩
          simp only [hop, hc]
          exact fun t2 m' v' ha => hex ⟨t2, m', v', ha⟩
  | Epostincr id l ty =>
    obtain ⟨b1, ofs, bf, E1, S1⟩ := simple_can_eval_lval (C := fun x => C (.Epostincr id x ty))
      hse (lctx (.postincr _ _ _ _ (.top _)) hC) hsafe
    obtain ⟨t1, v1, hty, hd⟩ := safe_inv S1 hC0
    subst hty
    cases hinc : Cop.semIncrdecr ge.genv_cenv id v1 (Csyntax.typeof l) m with
    | none =>
      exact ⟨_, _, .postincr_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd (by simp [hinc]) rfl⟩
    | some v2 =>
      cases hc : Cop.semCast v2 (Cop.incrdecrType (Csyntax.typeof l)) (Csyntax.typeof l) m with
      | none =>
        exact ⟨_, _, .postincr_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd (by simp [hinc, hc]) rfl⟩
      | some v3 =>
        by_cases hex : ∃ t2 m' v', Csem.AssignLoc ge (Csyntax.typeof l) m b1 ofs bf v3 t2 m' v'
        · obtain ⟨t2, m', v', ha⟩ := hex
          exact ⟨_, _, .postincr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd hinc hc ha rfl rfl⟩
        · refine ⟨_, _, .postincr_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ hC E1 hd ?_ rfl⟩
          simp only [hinc, hc]
          exact fun t2 m' v' ha => hex ⟨t2, m', v', ha⟩
  | Ecomma r1 r2 ty =>
    obtain ⟨v1, E1, S1⟩ :=
      simple_can_eval_rval (C := fun x => C (.Ecomma x r2 ty)) hse (lctx (.comma _ _ _ _ (.top _)) hC) hsafe
    have hty : Csyntax.typeof r2 = ty := safe_inv S1 hC0
    exact ⟨_, _, .comma _ _ _ _ _ _ _ _ _ hC E1 hty.symm⟩
  | Ecall rf rargs ty =>
    obtain ⟨hs1, hs2⟩ := hse
    obtain ⟨vf, E1, S1⟩ :=
      simple_can_eval_rval (C := fun x => C (.Ecall x rargs ty)) hs1 (lctx (.call_left _ _ _ _ (.top _)) hC) hsafe
    have hCl : ContextList' (fun x => C (.Ecall (.Eval vf (Csyntax.typeof rf)) (exprlistApp .Enil x) ty)) :=
      .call _ .Enil ty C hC0
    obtain ⟨vl, E2⟩ := simple_list_can_eval rargs hs2 hCl S1
    have S2 := safe_steps S1 (eval_simple_list_steps E2 hCl)
    obtain ⟨tyargs, tyres, cconv, fd, vargs, hcl, hfd, hca, hty⟩ :=
      safe_inv S2 hC0 (rval_list_all_values vl rargs)
    exact ⟨_, _, .call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hcl E1 (can_eval_simple_list E2 hca) hfd hty⟩
  | Ebuiltin ef tyargs rargs ty =>
    have hCl : ContextList' (fun x => C (.Ebuiltin ef tyargs (exprlistApp .Enil x) ty)) :=
      .builtin _ _ .Enil ty C hC0
    obtain ⟨vl, E2⟩ := simple_list_can_eval rargs hse hCl hsafe
    have S2 := safe_steps hsafe (eval_simple_list_steps E2 hCl)
    obtain ⟨vargs, t, vres, m', hca, hext⟩ := safe_inv S2 hC0 (rval_list_all_values vl rargs)
    exact ⟨_, _, .builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hC (can_eval_simple_list E2 hca) hext⟩
  | Eparen r tycast ty =>
    obtain ⟨v1, E1, S1⟩ :=
      simple_can_eval_rval (C := fun x => C (.Eparen x tycast ty)) hse (lctx (.paren _ _ _ _ (.top _)) hC) hsafe
    obtain ⟨v, hc⟩ := safe_inv S1 hC0
    exact ⟨_, _, .paren _ _ _ _ _ _ _ _ _ _ hC E1 hc⟩
  | _ => exact hse.elim

end CANSTEP

end Cstrategy
end CC
