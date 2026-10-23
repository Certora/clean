/-
  Port of `cfrontend/Cexec.v`, part 6: transitions over states
  (`Cexec.v` lines 1946–2300): function entry (`do_alloc_variables`,
  `sem_bind_parameters`), and the soundness and completeness of the
  transition function `do_step`:

  * `do_step_sound`: every transition listed by `doStep w S` is a step of
    `Csem.step`, or a transition to `Stuckstate` from a state that can emit a
    trace world `w` rejects ("crash the world");
  * `do_step_complete`: every step of `Csem.step` whose trace world `w` accepts
    is listed by `doStep w S`.

  Both take the hypotheses of `step_expr_sound` (injective symbol table, and a
  sound and complete oracle for external functions and inline assembly).
-/
import CCLib.cfrontend.CexecComplete

namespace CC
namespace Cexec

open Csyntax

/-- `Cexec.do_alloc_variables_sound` -/
theorem doAllocVariables_sound (ge : Csem.CGenv) :
    ∀ (l : List (Ident × Ty)) (e : Env) (m : Mem),
      Csem.AllocVariables ge e m l (doAllocVariables ge e m l).1 (doAllocVariables ge e m l).2
  | [], e, m => .nil _ _
  | (id, ty) :: l, e, m => by
      simp only [doAllocVariables]
      exact .cons _ _ _ _ _ _ _ _ _ rfl (doAllocVariables_sound ge l _ _)

/-- `Cexec.do_alloc_variables_complete` -/
theorem doAllocVariables_complete (ge : Csem.CGenv) {e1 m1 l e2 m2}
    (h : Csem.AllocVariables ge e1 m1 l e2 m2) : doAllocVariables ge e1 m1 l = (e2, m2) := by
  induction h with
  | nil => rfl
  | cons e m id ty vars m1 b1 m2 e2 ha _ ih => simp only [doAllocVariables, ha]; exact ih

/-- `Cexec.sem_bind_parameters_sound` -/
theorem semBindParameters_sound (ge : Csem.CGenv) (w : World) (e : Env) :
    ∀ (m : Mem) (l : List (Ident × Ty)) (lv : List Val) (m' : Mem),
      semBindParameters ge w e m l lv = some m' → Csem.BindParameters ge e m l lv m'
  | m, [], [], m', h => by simp only [semBindParameters, Option.some.injEq] at h; subst h; exact .nil _
  | m, (id, ty) :: params, v1 :: lv, m', h => by
      simp only [semBindParameters] at h
      split at h
      · next b ty' hget =>
          split at h
          · next hty =>
              subst hty
              split at h
              · next w' t m1 v' ha =>
                  split at h
                  · obtain ⟨h1, _⟩ := doAssignLoc_sound ge ha
                    exact .cons _ _ _ _ _ _ _ _ _ _ hget h1 (semBindParameters_sound ge w e m1 params lv m' h)
                  · cases h
              · cases h
          · cases h
      · cases h
  | _, [], _ :: _, _, h => by simp [semBindParameters] at h
  | _, _ :: _, [], _, h => by simp [semBindParameters] at h

/-- `Cexec.sem_bind_parameters_complete` -/
theorem semBindParameters_complete (ge : Csem.CGenv) (w : World) (hinj : Genv.SymbInjective ge.genv_genv)
    {e m l lv m'} (h : Csem.BindParameters ge e m l lv m') :
    semBindParameters ge w e m l lv = some m' := by
  induction h with
  | nil => rfl
  | cons m id ty params v1 vl v1' b m1 m2 hget ha _ ih =>
      simp [semBindParameters, hget, doAssignLoc_complete ge hinj ha (.nil w), ih, E0]

/-- Inversion of a membership in a one-element list of transitions. -/
theorem mem_ret {rule t S' rule' S} (h : Transition.TR rule t S' ∈ ret rule' S) :
    t = E0 ∧ S' = S := by
  simp only [ret, List.mem_singleton, Transition.TR.injEq] at h
  exact ⟨h.2.1, h.2.2⟩

/-- `Cexec.do_step_sound` (statement states). -/
theorem doStep_sound_State (ge : Csem.CGenv) (ox : ExtOracle) (w : World)
    {f s k e m rule t S'} (h : Transition.TR rule t S' ∈ doStep ge ox w (.State f s k e m)) :
    Csem.Sstep ge (.State f s k e m) t S' := by
  cases s with
  | Sskip =>
      cases k <;> simp only [doStep] at h
      case Kstop | Kcall =>
        split at h
        · next m' hf =>
            obtain ⟨rfl, rfl⟩ := mem_ret h
            exact .skip_call _ _ _ _ _ trivial hf
        · cases h
      all_goals first
        | (obtain ⟨rfl, rfl⟩ := mem_ret h
           first
           | exact .skip_seq _ _ _ _ _
           | exact .skip_or_continue_while _ _ _ _ _ _ _ (.inl rfl)
           | exact .skip_or_continue_dowhile _ _ _ _ _ _ _ (.inl rfl)
           | exact .skip_or_continue_for3 _ _ _ _ _ _ _ _ (.inl rfl)
           | exact .skip_for4 _ _ _ _ _ _ _
           | exact .skip_break_switch _ _ _ _ _ (.inl rfl))
        | cases h
  | Sdo x => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .do_1 _ _ _ _ _
  | Ssequence s1 s2 => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .seq _ _ _ _ _ _
  | Sifthenelse a s1 s2 => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .ifthenelse_1 _ _ _ _ _ _ _
  | Swhile x s => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .while _ _ _ _ _ _
  | Sdowhile x s => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .dowhile _ _ _ _ _ _
  | Sfor a1 a2 a3 s =>
      simp only [doStep] at h
      split at h
      · next hsk =>
          obtain ⟨rfl, rfl⟩ := mem_ret h
          cases a1 <;> simp [isSkip] at hsk
          exact .for _ _ _ _ _ _ _
      · next hsk =>
          obtain ⟨rfl, rfl⟩ := mem_ret h
          exact .for_start _ _ _ _ _ _ _ _ (by rintro rfl; simp [isSkip] at hsk)
  | Sbreak =>
      cases k <;> simp only [doStep] at h
      all_goals first
        | (obtain ⟨rfl, rfl⟩ := mem_ret h
           first
           | exact .break_seq _ _ _ _ _
           | exact .break_while _ _ _ _ _ _
           | exact .break_dowhile _ _ _ _ _ _
           | exact .break_for3 _ _ _ _ _ _ _
           | exact .skip_break_switch _ _ _ _ _ (.inr rfl))
        | cases h
  | Scontinue =>
      cases k <;> simp only [doStep] at h
      all_goals first
        | (obtain ⟨rfl, rfl⟩ := mem_ret h
           first
           | exact .continue_seq _ _ _ _ _
           | exact .skip_or_continue_while _ _ _ _ _ _ _ (.inr rfl)
           | exact .skip_or_continue_dowhile _ _ _ _ _ _ _ (.inr rfl)
           | exact .skip_or_continue_for3 _ _ _ _ _ _ _ _ (.inr rfl)
           | exact .continue_switch _ _ _ _)
        | cases h
  | Sreturn x =>
      cases x with
      | none =>
          simp only [doStep] at h
          split at h
          · next m' hf =>
              obtain ⟨rfl, rfl⟩ := mem_ret h
              exact .return_0 _ _ _ _ _ hf
          · cases h
      | some x => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .return_1 _ _ _ _ _
  | Sswitch x sl => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .switch _ _ _ _ _ _
  | Slabel lbl s => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .label _ _ _ _ _ _
  | Sgoto lbl =>
      simp only [doStep] at h
      split at h
      · next s' k' hfl =>
          obtain ⟨rfl, rfl⟩ := mem_ret h
          exact .goto _ _ _ _ _ _ _ hfl
      · cases h

/-- `Cexec.do_step_sound`: every transition listed by `doStep` is a step of
    the semantics, or goes to `Stuckstate` from a state that can crash the
    world. -/
theorem do_step_sound (ge : Csem.CGenv) (ox : ExtOracle) (hinj : Genv.SymbInjective ge.genv_genv)
    (hS : ox.Sound) (hC : ox.Complete) {w S rule t S'}
    (h : Transition.TR rule t S' ∈ doStep ge ox w S) :
    Csem.Step ge S t S' ∨ (t = E0 ∧ S' = .Stuckstate ∧ CanCrashWorld ge w S) := by
  cases S with
  | State f s k e m => exact .inl (.inr (doStep_sound_State ge ox w h))
  | ExprState f a k e m =>
      simp only [doStep] at h
      split at h
      · next v ty hv =>
          have := isVal_inv hv; subst this
          refine .inl (.inr ?_)
          cases k <;> simp only at h
          case Kdo k => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .do_2 _ _ _ _ _ _
          case Kifthenelse s1 s2 k =>
            split at h
            · next b hb => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .ifthenelse_2 _ _ _ _ _ _ _ _ _ hb
            · cases h
          case Kwhile1 x s k =>
            split at h
            · next b hb =>
                cases b
                · obtain ⟨rfl, rfl⟩ := mem_ret h; exact .while_false _ _ _ _ _ _ _ _ hb
                · obtain ⟨rfl, rfl⟩ := mem_ret h; exact .while_true _ _ _ _ _ _ _ _ hb
            · cases h
          case Kdowhile2 x s k =>
            split at h
            · next b hb =>
                cases b
                · obtain ⟨rfl, rfl⟩ := mem_ret h; exact .dowhile_false _ _ _ _ _ _ _ _ hb
                · obtain ⟨rfl, rfl⟩ := mem_ret h; exact .dowhile_true _ _ _ _ _ _ _ _ hb
            · cases h
          case Kfor2 a2 a3 s k =>
            split at h
            · next b hb =>
                cases b
                · obtain ⟨rfl, rfl⟩ := mem_ret h; exact .for_false _ _ _ _ _ _ _ _ _ hb
                · obtain ⟨rfl, rfl⟩ := mem_ret h; exact .for_true _ _ _ _ _ _ _ _ _ hb
            · cases h
          case Kreturn k =>
            split at h
            · next v' hc =>
                split at h
                · next m' hf => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .return_2 _ _ _ _ _ _ _ _ hc hf
                · cases h
            · cases h
          case Kswitch1 sl k =>
            split at h
            · next n hn => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .expr_switch _ _ _ _ _ _ _ _ hn
            · cases h
          all_goals cases h
      · next hv =>
          simp only [List.mem_map] at h
          obtain ⟨⟨C, rd⟩, hmem, heq⟩ := h
          obtain ⟨P, _⟩ := stepExpr_sound ge ox e w hinj hS hC a .RV m
          obtain ⟨a', k', hctx, rfl, hrd⟩ := P C rd hmem
          cases k' <;> cases rd <;> simp only [ReductionOk] at hrd <;>
            simp only [exprFinalState, Transition.TR.injEq] at heq
          · obtain ⟨-, rfl, rfl⟩ := heq
            exact .inl (.inl (.lred _ _ _ _ _ _ _ _ hrd hctx))
          · obtain ⟨-, rfl, rfl⟩ := heq
            rcases not_imm_safe_t ge e w (f := f) (k := k) hctx hrd with h' | h'
            · exact .inl h'
            · exact .inr ⟨rfl, rfl, h'⟩
          · obtain ⟨-, rfl, rfl⟩ := heq
            exact .inl (.inl (.rred _ _ _ _ _ _ _ _ _ hrd.1 hctx))
          · obtain ⟨-, rfl, rfl⟩ := heq
            obtain ⟨hr, rfl⟩ := hrd
            exact .inl (.inl (.call _ _ _ _ _ _ _ _ _ hr hctx))
          · obtain ⟨-, rfl, rfl⟩ := heq
            rcases not_imm_safe_t ge e w (f := f) (k := k) hctx hrd with h' | h'
            · exact .inl h'
            · exact .inr ⟨rfl, rfl, h'⟩
  | Callstate fd vargs k m =>
      refine .inl (.inr ?_)
      cases fd with
      | Internal f =>
          simp only [doStep] at h
          split at h
          · next hnr =>
              split at h
              · next m2 hb =>
                  obtain ⟨rfl, rfl⟩ := mem_ret h
                  exact .internal_function _ _ _ _ _ _ _ hnr
                    (doAllocVariables_sound ge _ emptyEnv m)
                    (semBindParameters_sound ge w _ _ _ _ _ hb)
              · cases h
          · cases h
      | External ef targs tres cc =>
          simp only [doStep] at h
          split at h
          · cases h
          · next w' t' v m' hext =>
              simp only [List.mem_singleton, Transition.TR.injEq] at h
              obtain ⟨-, rfl, rfl⟩ := h
              exact .external_function _ _ _ _ _ _ _ _ _ _ (doExternal_sound ge ox hS hext).1
  | Returnstate v k m =>
      refine .inl (.inr ?_)
      cases k <;> simp only [doStep] at h
      case Kcall f e C ty k => obtain ⟨rfl, rfl⟩ := mem_ret h; exact .returnstate _ _ _ _ _ _ _
      all_goals cases h
  | Stuckstate => simp [doStep] at h

/-- A reduction context other than the empty one has a head that is not a
    value. -/
theorem context_isVal {from_ to C} (b : Csyntax.Expr) (h : Csem.Context from_ to C) :
    (from_ = to ∧ ∀ x, C x = x) ∨ isVal (C b) = none := by
  cases h <;> first | exact .inl ⟨rfl, fun _ => rfl⟩ | exact .inr rfl

/-- `Cexec.estep_not_val` -/
theorem estep_not_val {ge : Csem.CGenv} {f a k e m t S}
    (h : Csem.Estep ge (.ExprState f a k e m) t S) : isVal a = none := by
  cases h with
  | lred C _ a0 _ _ _ a' m' hl hctx =>
      rcases context_isVal a0 hctx with ⟨h1, _⟩ | h'
      · cases h1
      · exact h'
  | rred C _ a0 _ _ _ _ a' m' hr hctx =>
      rcases context_isVal a0 hctx with ⟨_, h2⟩ | h'
      · rw [h2]; cases hr <;> rfl
      · exact h'
  | call C _ a0 _ _ _ fd vargs ty hc hctx =>
      rcases context_isVal a0 hctx with ⟨_, h2⟩ | h'
      · rw [h2]; cases hc; rfl
      · exact h'
  | stuck C _ a0 _ _ _ K hctx hns =>
      rcases context_isVal a0 hctx with ⟨rfl, h2⟩ | h'
      · rw [h2]
        cases a0 <;> try rfl
        exact absurd (.val _ _ _) hns
      · exact h'

/-- `Cexec.do_step_complete`: every step whose trace world `w` accepts is
    listed by `doStep`. -/
theorem do_step_complete (ge : Csem.CGenv) (ox : ExtOracle)
    (hinj : Genv.SymbInjective ge.genv_genv) (hS : ox.Sound) (hC : ox.Complete)
    {w S t S' w'} (hp : PossibleTrace w t w') (h : Csem.Step ge S t S') :
    ∃ rule, Transition.TR rule t S' ∈ doStep ge ox w S := by
  rcases h with h | h
  · cases h with
    | lred C f a k e m a' m' hl hctx =>
        have NOTVAL := estep_not_val (ge := ge) (.lred C f a k e m a' m' hl hctx)
        obtain ⟨rule, hst⟩ := lred_topred ge ox e w hl
        refine ⟨rule, ?_⟩
        simp only [doStep, NOTVAL, List.mem_map]
        refine ⟨(C, .Lred rule a' m'), ?_, rfl⟩
        exact step_expr_context ge ox e w hctx a m (fun x => x) _ (by rw [hst]; simp [topred])
    | rred C f a k e m t a' m' hr hctx =>
        have NOTVAL := estep_not_val (ge := ge) (.rred C f a k e m t a' m' hr hctx)
        obtain ⟨rule, hst⟩ := rred_topred ge ox e w hinj hC hr hp
        refine ⟨rule, ?_⟩
        simp only [doStep, NOTVAL, List.mem_map]
        refine ⟨(C, .Rred rule a' m' t), ?_, rfl⟩
        exact step_expr_context ge ox e w hctx a m (fun x => x) _ (by rw [hst]; simp [topred])
    | call C f a k e m fd vargs ty hc hctx =>
        have NOTVAL := estep_not_val (ge := ge) (.call C f a k e m fd vargs ty hc hctx)
        obtain ⟨rule, hst⟩ := callred_topred ge ox e w hc
        refine ⟨rule, ?_⟩
        simp only [doStep, NOTVAL, List.mem_map]
        refine ⟨(C, .Callred rule fd vargs ty m), ?_, rfl⟩
        exact step_expr_context ge ox e w hctx a m (fun x => x) _ (by rw [hst]; simp [topred])
    | stuck C f a k e m K hctx hns =>
        have NOTVAL := estep_not_val (ge := ge) (.stuck C f a k e m K hctx hns)
        obtain ⟨C', hin⟩ := not_imm_safe_stuck_red ge ox e w hinj hS hC hctx
          (fun hs => hns (immSafeT_immSafe ge e w hs))
        refine ⟨"step_stuck", ?_⟩
        simp only [doStep, NOTVAL, List.mem_map]
        exact ⟨(C', .Stuckred), hin, rfl⟩
  · cases h with
    | skip_or_continue_while f s0 x s k e m hs =>
        rcases hs with rfl | rfl <;> simp [doStep, ret]
    | skip_or_continue_dowhile f s0 x s k e m hs =>
        rcases hs with rfl | rfl <;> simp [doStep, ret]
    | skip_or_continue_for3 f x a2 a3 s k e m hs =>
        rcases hs with rfl | rfl <;> simp [doStep, ret]
    | skip_break_switch f x k e m hs =>
        rcases hs with rfl | rfl <;> simp [doStep, ret]
    | for_start f a1 a2 a3 s k e m hne =>
        cases a1 <;> first | exact absurd rfl hne | simp [doStep, ret, isSkip]
    | skip_call f k e m m' hcc hf =>
        cases k <;> simp [Csem.IsCallCont] at hcc <;> simp [doStep, ret, hf]
    | internal_function f vargs k m e m1 m2 hnr ha hb =>
        cases possibleTrace_E0_inv hp
        simp [doStep, ret, hnr, doAllocVariables_complete ge ha,
          semBindParameters_complete ge w hinj hb]
    | external_function ef targs tres cc vargs k m vres t m' hec =>
        simp [doStep, doExternal_complete ge ox hinj hC hec hp]
    | _ => simp_all [doStep, ret, isVal, isSkip]

end Cexec
end CC
