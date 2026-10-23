/-
  Expression simplification: semantic preservation — port of
  `cfrontend/SimplExprproof.v`, part 6: the forward simulation for statement
  steps (`sstep_simulation`), the initial and final states, and the main
  theorem `transl_program_correct`.

  Differences from Rocq:
  * whole-program statement: the hypothesis is `translProgram fu prog = .OK
    tprog` (no linking);
  * `match_cont_is_call_cont` is replaced by `match_cont_isCallCont`, since
    the port's `Clight.is_call_cont` is a Boolean function.
-/
import CCLib.cfrontend.SimplExprproofEstep
import CCLib.common.Simulation

namespace CC
namespace SimplExpr

open Destination SetDestination Cstrategy Smallstep

/-! ## Auxiliary results -/

theorem plus_two {σ : Type} {R : σ → Trace → σ → Prop} {s1 t1 s2 t2 s3 t} (h1 : R s1 t1 s2)
    (h2 : R s2 t2 s3) (ht : t = Eapp t1 t2) : Smallstep.Plus R s1 t s3 :=
  plus_left h1 (star_one h2) ht

/-- `SimplExprproof.tr_top_val_for_val_inv` -/
theorem tr_top_val_for_val_inv {ce : CompositeEnv} {tge : CGenv} {e le m v ty sl a tmps}
    (h : TrTop ce tge e le m For_val (.Eval v ty) sl a tmps) :
    sl = [] ∧ typeof a = ty ∧ EvalExpr tge e le m a v := by
  cases h with
  | tr_top_val_val _ _ _ _ hty hev => exact ⟨rfl, hty, hev⟩
  | tr_top_base _ _ _ _ _ h =>
    cases h with
    | tr_val_value _ _ _ _ hty hev => exact ⟨rfl, hty, hev _ _ _ _ fun _ _ => rfl⟩

theorem match_cont_isCallCont {ce : CompositeEnv} {tge : CGenv} {k tk}
    (hk : MatchCont ce tge k tk) (hc : Csem.IsCallCont k) : isCallCont tk = true := by
  cases hk <;> first | rfl | exact hc.elim

theorem sizeChunk_le_modulus (chunk : Chunk) : sizeChunk chunk ≤ Integers.Ptrofs.modulus := by
  cases chunk <;> decide

section PRESERVED
variable {ge : Csem.CGenv} {tge : CGenv} (GR : GenvRel ge tge)
include GR

/-- `SimplExprproof.alloc_variables_preserved` -/
theorem alloc_variables_preserved {e m params e' m'} (h : Csem.AllocVariables ge e m params e' m') :
    AllocVariables tge.genv_cenv e m params e' m' := by
  induction h with
  | nil => exact .nil _ _
  | cons _ _ _ _ _ _ _ _ _ halloc _ ih => exact .cons _ _ _ _ _ _ _ _ _ (by rw [GR.cenv]; exact halloc) ih

/-- `SimplExprproof.bind_parameters_preserved` -/
theorem bind_parameters_preserved {e m params args m'}
    (h : Csem.BindParameters ge e m params args m') :
    BindParameters tge.genv_cenv e m params args m' := by
  induction h with
  | nil => exact .nil _
  | cons _ _ ty _ _ _ _ b _ _ hget ha _ ih =>
    refine .cons _ _ _ _ _ _ _ _ _ hget ?_ ih
    have ha' := assign_loc_translated GR.senv GR.cenv ha
    split at ha'
    · exact ha'.2
    · rename_i chunk hc
      obtain ⟨-, hvs⟩ := ha'
      obtain ⟨-, hacc, -⟩ := chunkForVolatileType_eq_some.1 hc
      cases hvs with
      | nonvol _ _ _ hst =>
        refine .value _ _ _ hacc ?_
        simp only [Mem.storev]
        have h0 : Integers.Ptrofs.unsigned Integers.Ptrofs.zero = 0 := rfl
        rw [if_pos (by rw [h0, Int.zero_add]; exact sizeChunk_le_modulus chunk)]
        exact hst

/-- `SimplExprproof.blocks_of_env_preserved` -/
theorem blocks_of_env_preserved (e : Env) : blocksOfEnv tge.genv_cenv e = blocksOfEnv ge.genv_cenv e := by
  rw [GR.cenv]

end PRESERVED

/-! ## Forward simulation for statements -/

section SSTEP
variable {p : Csyntax.Program} {tge : CGenv} (GR : GenvRel (Csem.globalenv p) tge)
include GR

/-- `SimplExprproof.sstep_simulation` -/
theorem sstep_simulation {S1 t S2} (h : Csem.Sstep (Csem.globalenv p) S1 t S2) {S1'}
    (hm : MatchStates p tge S1 S1') : SimGoal p tge S1 t S2 S1' := by
  cases h with
  | do_1 f x k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with | tr_do _ _ hes =>
    cases hes with | tr_expr_stmt_intro sl a tmps htop =>
    exact ⟨_, .inr ⟨push_seq, by simp only [measure]; omega⟩,
      ms_expr tmps hf (htop _ _ _ _) (.Kdo _ _ _ hk)⟩
  | do_2 f v ty k e m =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kdo _ _ _ hk =>
    cases htop with | tr_top_base _ _ _ _ _ htr =>
    cases htr with | tr_val_effect =>
    exact ⟨_, .inr ⟨Smallstep.Star.refl _, by simp only [measure, esize]; omega⟩,
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | seq f s1 s2 k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with | tr_seq _ _ _ _ h1 h2 =>
    exact ⟨_, .inl (plus_one (Step.seq _ _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf h1 (.Kseq _ _ _ _ h2 hk)⟩
  | skip_seq f s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kseq _ _ _ _ hs hk =>
    exact ⟨_, .inl (plus_one (Step.skip_seq _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf hs hk⟩
  | continue_seq f s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kseq _ _ _ _ hs hk =>
    exact ⟨_, .inl (plus_one (Step.continue_seq _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_continue hk⟩
  | break_seq f s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kseq _ _ _ _ hs hk =>
    exact ⟨_, .inl (plus_one (Step.break_seq _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_break hk⟩
  | ifthenelse_1 f a s1 s2 k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with
    | tr_ifthenelse_empty _ _ _ hex =>
      cases hex with | tr_expression_intro sl a' tmps htop =>
      exact ⟨_, .inl (plus_left (Step.seq _ _ _ _ _ _ _) push_seq rfl),
        ms_expr tmps hf (htop _ _ _ _) (.Kifthenelse_empty _ _ _ hk)⟩
    | tr_ifthenelse _ _ _ _ _ ts1 ts2 hex h1 h2 =>
      cases hex with | tr_expression_intro sl a' tmps htop =>
      exact ⟨_, .inl (plus_left (Step.seq _ _ _ _ _ _ _) push_seq rfl),
        ms_expr tmps hf (htop _ _ _ _) (.Kifthenelse_1 _ _ _ _ _ _ _ h1 h2 hk)⟩
  | ifthenelse_2 f v ty s1 s2 k e m b hb =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with
    | Kifthenelse_empty _ _ _ hk =>
      obtain ⟨rfl, -, -⟩ := tr_top_val_for_val_inv htop
      cases b <;>
      exact ⟨_, .inr ⟨star_one (Step.skip_seq _ _ _ _ _ _), by simp [measure, esize]⟩,
        .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
    | Kifthenelse_1 _ _ _ _ _ _ _ h1 h2 hk =>
      obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
      subst hty
      cases b
      · exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
            (star_one (Step.ifthenelse _ _ _ _ _ _ _ _ _ _ hev hb)) rfl),
          .regularstates _ _ _ _ _ _ _ _ _ hf h2 hk⟩
      · exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
            (star_one (Step.ifthenelse _ _ _ _ _ _ _ _ _ _ hev hb)) rfl),
          .regularstates _ _ _ _ _ _ _ _ _ hf h1 hk⟩
  | «while» f x s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with | tr_while _ _ _ ts1 hif h1 =>
    cases hif with | tr_if_intro sl a tmps htop =>
    refine ⟨_, .inl (plus_left (Step.loop _ _ _ _ _ _ _)
      (star_left (Step.seq _ _ _ _ _ _ _) push_seq rfl) rfl), ?_⟩
    rw [Kseqlist_app]
    exact ms_expr tmps hf (htop _ _ _ _)
      (.Kwhile1 _ _ _ _ _ _ _ (.tr_if_intro _ _ _ _ _ _ htop) h1 hk)
  | while_false f v ty x s k e m hb =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kwhile1 _ _ _ _ _ ts _ hif h1 hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_trans (step_makeif hev hb)
          (star_two (Step.break_seq _ _ _ _ _ _) (Step.break_loop1 _ _ _ _ _ _ _) rfl) rfl) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | while_true f v ty x s k e m hb =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kwhile1 _ _ _ _ _ ts _ hif h1 hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_right (step_makeif hev hb) (Step.skip_seq _ _ _ _ _ _) rfl) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf h1 (.Kwhile2 _ _ _ _ _ _ hif h1 hk)⟩
  | skip_or_continue_while f s0 x s k e m hs0 =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hk with | Kwhile2 _ _ _ _ ts1 _ hif h1 hk =>
    rcases hs0 with rfl | rfl <;> cases hts <;>
    exact ⟨_, .inl (plus_two (Step.skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp))
        (Step.skip_loop2 _ _ _ _ _ _ _) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf (.tr_while _ _ _ _ hif h1) hk⟩
  | break_while f x s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kwhile2 _ _ _ _ ts1 _ hif h1 hk =>
    exact ⟨_, .inl (plus_one (Step.break_loop1 _ _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | dowhile f a s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with | tr_dowhile _ _ _ ts1 hif h1 =>
    exact ⟨_, .inl (plus_one (Step.loop _ _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf h1 (.Kdowhile1 _ _ _ _ _ _ hif h1 hk)⟩
  | skip_or_continue_dowhile f s0 x s k e m hs0 =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hk with | Kdowhile1 _ _ _ _ ts1 _ hif h1 hk =>
    cases hif with | tr_if_intro sl a tmps htop =>
    rcases hs0 with rfl | rfl <;> cases hts <;>
    · refine ⟨_, .inl (plus_left (Step.skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp))
        push_seq rfl), ?_⟩
      rw [Kseqlist_app]
      exact ms_expr tmps hf (htop _ _ _ _)
        (.Kdowhile2 _ _ _ _ _ _ _ (.tr_if_intro _ _ _ _ _ _ htop) h1 hk)
  | dowhile_false f v ty x s k e m hb =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kdowhile2 _ _ _ _ _ ts _ hif h1 hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_right (step_makeif hev hb) (Step.break_loop2 _ _ _ _ _ _ _) rfl) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | dowhile_true f v ty x s k e m hb =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kdowhile2 _ _ _ _ _ ts _ hif h1 hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_right (step_makeif hev hb) (Step.skip_loop2 _ _ _ _ _ _ _) rfl) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf (.tr_dowhile _ _ _ _ hif h1) hk⟩
  | break_dowhile f a s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kdowhile1 _ _ _ _ ts1 _ hif h1 hk =>
    exact ⟨_, .inl (plus_one (Step.break_loop1 _ _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | for_start f a1 a2 a3 s k e m hne =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with
    | tr_for_1 => exact absurd rfl hne
    | tr_for_2 _ _ _ _ _ ts1 ts3 ts4 hif _ h1 h3 h4 =>
      exact ⟨_, .inl (plus_one (Step.seq _ _ _ _ _ _ _)),
        .regularstates _ _ _ _ _ _ _ _ _ hf h1 (.Kseq _ _ _ _ (.tr_for_1 _ _ _ _ _ _ hif h3 h4) hk)⟩
  | «for» f a2 a3 s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with
    | tr_for_2 _ _ _ _ _ _ _ _ _ hne => exact absurd rfl hne
    | tr_for_1 _ _ _ _ ts3 ts4 hif h3 h4 =>
      cases hif with | tr_if_intro sl a tmps htop =>
      refine ⟨_, .inl (plus_left (Step.loop _ _ _ _ _ _ _)
        (star_left (Step.seq _ _ _ _ _ _ _) push_seq rfl) rfl), ?_⟩
      rw [Kseqlist_app]
      exact ms_expr tmps hf (htop _ _ _ _)
        (.Kfor2 _ _ _ _ _ _ _ _ _ (.tr_if_intro _ _ _ _ _ _ htop) h3 h4 hk)
  | for_false f v ty a2 a3 s k e m hb =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kfor2 _ _ _ _ _ _ ts3 ts _ hif h3 h hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_trans (step_makeif hev hb)
          (star_two (Step.break_seq _ _ _ _ _ _) (Step.break_loop1 _ _ _ _ _ _ _) rfl) rfl) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | for_true f v ty a2 a3 s k e m hb =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kfor2 _ _ _ _ _ _ ts3 ts _ hif h3 h hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_right (step_makeif hev hb) (Step.skip_seq _ _ _ _ _ _) rfl) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf h (.Kfor3 _ _ _ _ _ _ _ _ hif h3 h hk)⟩
  | skip_or_continue_for3 f x a2 a3 s k e m hx =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hk with | Kfor3 _ _ _ _ ts3 _ ts1 _ hif h3 h hk =>
    rcases hx with rfl | rfl <;> cases hts <;>
    exact ⟨_, .inl (plus_one (Step.skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp))),
      .regularstates _ _ _ _ _ _ _ _ _ hf h3 (.Kfor4 _ _ _ _ _ _ _ _ hif h3 h hk)⟩
  | break_for3 f a2 a3 s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kfor3 _ _ _ _ ts3 _ ts1 _ hif h3 h hk =>
    exact ⟨_, .inl (plus_one (Step.break_loop1 _ _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | skip_for4 f a2 a3 s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kfor4 _ _ _ _ ts3 _ ts1 _ hif h3 h hk =>
    exact ⟨_, .inl (plus_one (Step.skip_loop2 _ _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf (.tr_for_1 _ _ _ _ _ _ hif h3 h) hk⟩
  | return_0 f k e m m' hfree =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    exact ⟨_, .inl (plus_one (Step.return_0 _ _ _ _ _ _
        (by rw [blocks_of_env_preserved GR]; exact hfree))),
      .returnstates _ _ _ _ (match_cont_call_cont hk)⟩
  | return_1 f x k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with | tr_return_some _ _ _ hex =>
    cases hex with | tr_expression_intro sl a tmps htop =>
    exact ⟨_, .inl (plus_left (Step.seq _ _ _ _ _ _ _) push_seq rfl),
      ms_expr tmps hf (htop _ _ _ _) (.Kreturn _ _ _ hk)⟩
  | return_2 f v1 ty k e m v2 m' hc hfree =>
    cases hm with | exprstates _ _ _ _ _ tf sl tk le dest a tmps hf htop hk =>
    cases hk with | Kreturn _ _ _ hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_two (Step.skip_seq _ _ _ _ _ _)
        (Step.return_1 _ _ _ _ _ _ _ _ _ hev (by rw [function_return_preserved hf]; exact hc)
          (by rw [blocks_of_env_preserved GR]; exact hfree)) rfl),
      .returnstates _ _ _ _ (match_cont_call_cont hk)⟩
  | skip_call f k e m m' hcc hfree =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    exact ⟨_, .inl (plus_one (Step.skip_call _ _ _ _ _ _ (match_cont_isCallCont hk hcc)
        (by rw [blocks_of_env_preserved GR]; exact hfree))),
      .returnstates _ _ _ _ hk⟩
  | switch f x sl k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with | tr_switch _ _ _ _ tls hex hls =>
    cases hex with | tr_expression_intro sl' a tmps htop =>
    exact ⟨_, .inl (plus_left (Step.seq _ _ _ _ _ _ _) push_seq rfl),
      ms_expr tmps hf (htop _ _ _ _) (.Kswitch1 _ _ _ _ _ hls hk)⟩
  | expr_switch f ty sl k e m v n hsw =>
    cases hm with | exprstates _ _ _ _ _ tf sl' tk le dest a tmps hf htop hk =>
    cases hk with | Kswitch1 _ _ _ tls _ hls hk =>
    obtain ⟨rfl, hty, hev⟩ := tr_top_val_for_val_inv htop
    subst hty
    exact ⟨_, .inl (plus_two (Step.skip_seq _ _ _ _ _ _)
        (Step.switch _ _ _ _ _ _ _ _ _ hev hsw) rfl),
      .regularstates _ _ _ _ _ _ _ _ _ hf (tr_seq_of_labeled_statement (tr_select_switch n hls))
        (.Kswitch2 _ _ hk)⟩
  | skip_break_switch f x k e m hx =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hk with | Kswitch2 _ _ hk =>
    rcases hx with rfl | rfl <;> cases hts <;>
    exact ⟨_, .inl (plus_one (Step.skip_break_switch _ _ _ _ _ _ (by simp))),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_skip hk⟩
  | continue_switch f k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    cases hk with | Kswitch2 _ _ hk =>
    exact ⟨_, .inl (plus_one (Step.continue_switch _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf .tr_continue hk⟩
  | label f lbl s k e m =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts with | tr_label _ _ _ h1 =>
    exact ⟨_, .inl (plus_one (Step.label _ _ _ _ _ _ _)),
      .regularstates _ _ _ _ _ _ _ _ _ hf h1 hk⟩
  | goto f lbl k e m s' k' hfind =>
    cases hm with | regularstates _ _ _ _ _ tf ts tk le hf hts hk =>
    cases hts
    have hf' := hf
    cases hf' with | tr_function_intro hbody =>
    have hfl := tr_find_label (lbl := lbl) hbody (match_cont_call_cont hk)
    rw [hfind] at hfl
    obtain ⟨ts', tk', h1, h2, h3⟩ := hfl
    exact ⟨_, .inl (plus_one (Step.goto _ _ _ _ _ _ _ _ h1)),
      .regularstates _ _ _ _ _ _ _ _ _ hf h2 h3⟩
  | internal_function f vargs k m e m1 m2 hnr halloc hbind =>
    cases hm with | callstates _ _ _ _ tfd tk htfd hk =>
    cases htfd with | tr_internal _ tf htf =>
    have htf' := htf
    cases htf' with | tr_function_intro hbody hret hcc hparams hvars =>
    refine ⟨_, .inl (plus_one (Step.internal_function _ _ _ _ _ _ _
      (.intro m1 ?_ ?_ ?_ rfl))), .regularstates _ _ _ _ _ _ _ _ _ htf hbody hk⟩
    · rw [hparams, hvars]; exact hnr
    · rw [hparams, hvars]; exact alloc_variables_preserved GR halloc
    · rw [hparams]; exact bind_parameters_preserved GR hbind
  | external_function ef targs tres cc vargs k m vres t m' hext =>
    cases hm with | callstates _ _ _ _ tfd tk htfd hk =>
    cases htfd with | tr_external =>
    exact ⟨_, .inl (plus_one (Step.external_function _ _ _ _ _ _ _ _ _ _
        (by rw [GR.senv]; exact hext))), .returnstates _ _ _ _ hk⟩
  | returnstate v f e C ty k m =>
    cases hm with | returnstates _ _ _ tk hk =>
    cases hk with | Kcall _ _ _ _ _ optid tf le sl tk a dest tmps hf hC htop hk =>
    exact ⟨_, .inl (plus_one (Step.returnstate _ _ _ _ _ _ _)),
      ms_expr tmps hf (htop v m) hk⟩

/-- `SimplExprproof.simulation` -/
theorem simulation (FT : FunsTranslated p tge) {S1 t S2}
    (h : Cstrategy.Step (Csem.globalenv p) S1 t S2) {S1'} (hm : MatchStates p tge S1 S1') :
    SimGoal p tge S1 t S2 S1' := by
  rcases h with h | h
  · exact estep_simulation GR FT h hm
  · exact sstep_simulation GR h hm

end SSTEP

/-! ## Semantic preservation -/

section PRESERVATION
variable {fu : Ident} {prog : Csyntax.Program} {tprog : Program}
  (TRANSL : translProgram fu prog = .OK tprog)
include TRANSL

theorem funsTranslated_of_transl : FunsTranslated prog tprog.globalenv :=
  fun _ _ h => functions_translated TRANSL h

/-- `SimplExprproof.transl_initial_states` -/
theorem transl_initial_states {S : Csem.State} (h : Csem.InitialState prog S) :
    ∃ S', InitialState tprog S' ∧ MatchStates prog tprog.globalenv S S' := by
  cases h with
  | intro b f m0 hm hs hf ht =>
  obtain ⟨tf, A, B⟩ := function_ptr_translated TRANSL hf
  refine ⟨_, .intro b tf m0 ?_ ?_ A (by rw [type_of_fundef_preserved B]; exact ht),
    .callstates _ _ _ _ _ _ B .Kstop⟩
  · rw [Program.initMem_toAST, (transf_program_match TRANSL).init_mem]; exact hm
  · have hmain : tprog.prog_main = prog.prog_main := (transf_program_match TRANSL).main_eq
    rw [symbols_preserved TRANSL, hmain]; exact hs

omit TRANSL in
/-- `SimplExprproof.transl_final_states` -/
theorem transl_final_states {S : Csem.State} {S' : State} {r : Integers.Int}
    (hm : MatchStates prog tprog.globalenv S S') (h : Csem.FinalState S r) : FinalState S' r := by
  cases h with
  | intro r m =>
  cases hm with
  | returnstates _ _ _ tk hk =>
  cases hk
  exact .intro _ _

end PRESERVATION

/-- `SimplExprproof.transl_program_correct`: the first pass of the compiler,
    from CompCert C (executed with the compiler's evaluation order,
    `Cstrategy.semantics`) to Clight with parameters in memory
    (`Clight.semantics1`), preserves the semantics: there is a forward
    simulation between the source and the target program. -/
theorem transl_program_correct (fu : Ident) (prog : Csyntax.Program) (tprog : Program)
    (TRANSL : translProgram fu prog = .OK tprog) :
    ForwardSimulation (Cstrategy.semantics prog) (Clight.semantics1 tprog) :=
  forward_simulation_star_wf (L1 := Cstrategy.semantics prog) (L2 := Clight.semantics1 tprog)
    (MatchStates prog tprog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv.genv_genv).public_symbol id = _
      rw [senv_preserved TRANSL]; rfl)
    (fun _ h => transl_initial_states TRANSL h)
    (fun _ _ _ hm h => transl_final_states hm h)
    (fun x y => measure x < measure y) (InvImage.wf measure Nat.lt_wfRel.wf)
    (fun _ _ _ hst _ hm =>
      simulation (genvRel_of_transl TRANSL) (funsTranslated_of_transl TRANSL) hst hm)

end SimplExpr
end CC
