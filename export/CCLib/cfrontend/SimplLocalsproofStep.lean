/-
  Pulling local scalar variables into temporaries: semantic preservation —
  port of `cfrontend/SimplLocalsproof.v`, part 5: the simulation diagram
  (`step_simulation`), initial and final states, and the main theorem
  `transf_program_correct`.
-/
import CCLib.cfrontend.SimplLocalsproofMatch
import CCLib.cfrontend.ClightBehaviors
import CCLib.cfrontend.ClightGlobalenv
import CCLib.cfrontend.CopInject
import CCLib.cfrontend.CopTheory
import CCLib.common.Simulation

namespace CC
namespace SimplLocals

open Smallstep

theorem step2_plus {ge : CGenv} {S : State} {t : Trace} {S' : State}
    (h : Step ge (FunctionEntry2 ge) S t S') : Smallstep.Plus (Step2 ge) S t S' := plus_one h

/-- Inversion of `transfFunction`. -/
theorem transfFunction_inv {opts : Options} {f tf : Function} (h : transfFunction opts f = .OK tf) :
    ∃ body', simplStmt opts (cenvFor f) f.fn_body = .OK body' ∧
      listDisjoint (varNames f.fn_params) (varNames f.fn_temps) ∧
      tf = { fn_return := f.fn_return, fn_callconv := f.fn_callconv, fn_params := f.fn_params,
             fn_vars := removeLifted (cenvFor f) (f.fn_params ++ f.fn_vars),
             fn_temps := addLifted (cenvFor f) f.fn_vars f.fn_temps,
             fn_body := addDebugParams opts f.fn_params (storeParams opts (cenvFor f) f.fn_params
               (addDebugVars opts (removeLifted (cenvFor f) (f.fn_params ++ f.fn_vars)) body')) } := by
  unfold transfFunction at h
  split at h
  · rename_i hd
    dsimp only at h
    split at h
    · cases h
    · rename_i body' hb; cases h; exact ⟨body', hb, hd, rfl⟩
  · cases h

theorem semSwitchArg_inject {f : Val.Meminj} {v tv : Val} {ty : Ty} {n : Z}
    (hi : Val.Inject f v tv) (h : Cop.semSwitchArg v ty = some n) : Cop.semSwitchArg tv ty = some n := by
  unfold Cop.semSwitchArg at *
  split at h <;> cases hi <;> simp_all

theorem assign_loc_unmapped_inject {j : Val.Meminj} {m tm m' : Mem} {ce : CompositeEnv} {ty : Ty}
    {b : Block} {ofs : Integers.Ptrofs} {v : Val} {chunk : Chunk}
    (MINJ : Mem.Inject j m tm) (ha : AssignLoc ce ty m b ofs .Full v m')
    (hm : accessMode ty = .By_value chunk) (hf : j b = none) : Mem.Inject j m' tm := by
  cases ha with
  | value _ _ _ _ hs =>
    simp only [Mem.storev] at hs
    split at hs
    · exact Mem.store_unmapped_inject MINJ hs hf
    · cases hs
  | copy _ _ _ _ hc => rw [hm] at hc; cases hc

theorem valCastedList_inject {f : Val.Meminj} {vl tvl : List Val} (hi : Val.InjectList f vl tvl) :
    ∀ {tyl : List Ty}, ValCastedList vl tyl → ValCastedList tvl tyl := by
  induction hi with
  | nil => intro _ h; cases h; exact .nil
  | cons hv _ ih => intro _ h; cases h with | cons h1 h2 => exact .cons (val_casted_inject hv h1) (ih h2)

section STEP
variable {opts : Options} {prog tprog : Program} (TRANSF : transfProgram opts prog = .OK tprog)
  (hwf : CompositeEnv.WF prog.prog_comp_env)
  (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
  (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))

include TRANSF hwf hext hasm in
/-- `SimplLocalsproof.step_simulation` -/
theorem step_simulation {S1 : State} {t : Trace} {S2 : State} (hst : Step1 prog.globalenv S1 t S2)
    {S1' : State} (MS : MatchStates opts prog.globalenv.genv_genv S1 S1') :
    ∃ S2', Smallstep.Plus (Step2 tprog.globalenv) S1' t S2' ∧
      MatchStates opts prog.globalenv.genv_genv S2 S2' := by
  have hce : tprog.globalenv.genv_cenv = prog.globalenv.genv_cenv := genv_cenv_preserved TRANSF
  have hsym := symbols_preserved TRANSF
  cases hst with
  | seq f s1 s2 k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨ts1, h1, ts2, h2, h⟩ := TRS; cases h
    exact ⟨_, step2_plus (.seq _ _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF h1 MENV
        (.Kseq _ _ _ _ _ _ _ _ h2 MCONT (compat_cenv_union_r COMPAT)) MINJ
        (compat_cenv_union_l COMPAT) HB THB⟩
  | skip_seq f s k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    cases MCONT with
    | Kseq _ _ _ ts' tk' _ _ _ h1 MC hc =>
    exact ⟨_, step2_plus (.skip_seq _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF h1 MENV MC MINJ hc HB THB⟩
  | continue_seq f s k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    cases MCONT with
    | Kseq _ _ _ ts' tk' _ _ _ h1 MC hc =>
    exact ⟨_, step2_plus (.continue_seq _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl MENV MC MINJ COMPAT HB THB⟩
  | break_seq f s k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    cases MCONT with
    | Kseq _ _ _ ts' tk' _ _ _ h1 MC hc =>
    exact ⟨_, step2_plus (.break_seq _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl MENV MC MINJ COMPAT HB THB⟩
  | loop f s1 s2 k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨ts1, h1, ts2, h2, h⟩ := TRS; cases h
    exact ⟨_, step2_plus (.loop _ _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF h1 MENV
        (.Kloop1 _ _ _ _ _ _ _ _ _ _ h1 h2 MCONT COMPAT) MINJ
        (compat_cenv_union_l COMPAT) HB THB⟩
  | skip_or_continue_loop1 f s1 s2 k e le m x hx =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    cases MCONT with
    | Kloop1 _ _ _ _ ts1 ts2 _ _ _ _ h1 h2 MC hc =>
    have hts : ts = .Sskip ∨ ts = .Scontinue := by
      rcases hx with rfl | rfl <;> simp only [simplStmt] at TRS <;> cases TRS <;> simp
    exact ⟨_, step2_plus (.skip_or_continue_loop1 _ _ _ _ _ _ _ _ hts),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF h2 MENV
        (.Kloop2 _ _ _ _ _ _ _ _ _ _ h1 h2 MC hc) MINJ (compat_cenv_union_r hc) HB THB⟩
  | break_loop1 f s1 s2 k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    cases MCONT with
    | Kloop1 _ _ _ _ ts1 ts2 _ _ _ _ h1 h2 MC hc =>
    exact ⟨_, step2_plus (.break_loop1 _ _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl MENV MC MINJ
        (compat_cenv_empty _) HB THB⟩
  | skip_loop2 f s1 s2 k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    cases MCONT with
    | Kloop2 _ _ _ _ ts1 ts2 _ _ _ _ h1 h2 MC hc =>
    exact ⟨_, step2_plus (.skip_loop2 _ _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF
        (by simp only [simplStmt, Cshmgen.res_bind_eq_OK]; exact ⟨ts1, h1, ts2, h2, rfl⟩)
        MENV MC MINJ hc HB THB⟩
  | break_loop2 f s1 s2 k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    cases MCONT with
    | Kloop2 _ _ _ _ ts1 ts2 _ _ _ _ h1 h2 MC hc =>
    exact ⟨_, step2_plus (.break_loop2 _ _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl MENV MC MINJ
        (compat_cenv_empty _) HB THB⟩
  | skip_break_switch f x k e le m hx =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    cases MCONT with
    | Kswitch _ _ _ _ _ _ MC =>
    have hts : ts = .Sskip ∨ ts = .Sbreak := by
      rcases hx with rfl | rfl <;> simp only [simplStmt] at TRS <;> cases TRS <;> simp
    exact ⟨_, step2_plus (.skip_break_switch _ _ _ _ _ _ hts),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl MENV MC MINJ
        (compat_cenv_empty _) HB THB⟩
  | continue_switch f k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    cases MCONT with
    | Kswitch _ _ _ _ _ _ MC =>
    exact ⟨_, step2_plus (.continue_switch _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl MENV MC MINJ COMPAT HB THB⟩
  | label f lbl s k e le m =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨ts', h1, h⟩ := TRS; cases h
    exact ⟨_, step2_plus (.label _ _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF h1 MENV MCONT MINJ COMPAT HB THB⟩
  | returnstate v optid f e le k m =>
    cases MS with
    | ret _ _ _ tv tk tm j MCONT MINJ VINJ =>
    cases MCONT (cenvFor f) with
    | Kcall _ _ _ _ _ _ tfn te tle tk' _ hi thi lo tlo _ _ x TRF ME MC hx h5 h6 =>
    exact ⟨_, step2_plus (.returnstate _ _ _ _ _ _ _),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl
        (match_envs_set_opttemp ME VINJ hx) MC MINJ (compat_cenv_empty _) h5 h6⟩
  | set f id a k e le m v hev =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨x, hx, h⟩ := TRS; cases h
    obtain ⟨tv, A, B⟩ := eval_simpl_expr hce hsym MENV MINJ (match_cont_globalenv MCONT) hev COMPAT
    exact ⟨_, step2_plus (.set _ _ _ _ _ _ _ _ A),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl
        (match_envs_set_temp MENV B hx) MCONT MINJ (compat_cenv_empty _) HB THB⟩
  | ifthenelse f a s1 s2 k e le m v1 b hev hb =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨ts1, h1, ts2, h2, h⟩ := TRS; cases h
    obtain ⟨tv, A, B⟩ := eval_simpl_expr hce hsym MENV MINJ (match_cont_globalenv MCONT) hev
      (compat_cenv_union_l COMPAT)
    have hb' := Cop.boolVal_inject hb B MINJ
    rw [← typeof_simpl_expr (cenvFor f) a] at hb'
    have hc' := compat_cenv_union_r COMPAT
    refine ⟨_, step2_plus (.ifthenelse _ _ _ _ _ _ _ _ _ _ A hb'), ?_⟩
    cases b
    · exact .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF h2 MENV MCONT MINJ
        (compat_cenv_union_r hc') HB THB
    · exact .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF h1 MENV MCONT MINJ
        (compat_cenv_union_l hc') HB THB
  | return_0 f k e le m m' hfr =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Option.map] at TRS; cases TRS
    obtain ⟨tm', P, Q⟩ := match_envs_free_blocks MENV MINJ hfr
    refine ⟨_, step2_plus (.return_0 _ _ _ _ _ _ (by rw [hce]; exact P)),
      .ret _ _ _ _ _ _ j (fun cenv => match_cont_call_cont (cenv := cenvFor f) ?_ cenv) Q (.undef _)⟩
    exact match_cont_free_env MENV MCONT HB THB hfr P
  | return_1 f a k e le m v v' m' hev hcast hfr =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Option.map] at TRS; cases TRS
    obtain ⟨tv, A, B⟩ := eval_simpl_expr hce hsym MENV MINJ (match_cont_globalenv MCONT) hev COMPAT
    obtain ⟨tv', C, D⟩ := Cop.semCast_inject hcast B MINJ
    obtain ⟨tm', P, Q⟩ := match_envs_free_blocks MENV MINJ hfr
    rw [← typeof_simpl_expr (cenvFor f) a, ← (transfFunction_sig TRF).1] at C
    refine ⟨_, step2_plus (.return_1 _ _ _ _ _ _ _ _ _ A C (by rw [hce]; exact P)),
      .ret _ _ _ _ _ _ j (fun cenv => match_cont_call_cont (cenv := cenvFor f) ?_ cenv) Q D⟩
    exact match_cont_free_env MENV MCONT HB THB hfr P
  | skip_call f k e le m m' hk hfr =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    obtain ⟨tm', P, Q⟩ := match_envs_free_blocks MENV MINJ hfr
    refine ⟨_, step2_plus (.skip_call _ _ _ _ _ _ (match_cont_is_call_cont MCONT hk)
        (by rw [hce]; exact P)),
      .ret _ _ _ _ _ _ j (fun cenv => match_cont_change_cenv (cenv := cenvFor f) ?_ hk cenv) Q (.undef _)⟩
    exact match_cont_free_env MENV MCONT HB THB hfr P
  | switch f a sl k e le m v n hev hsw =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨tls, hls, h⟩ := TRS; cases h
    obtain ⟨tv, A, B⟩ := eval_simpl_expr hce hsym MENV MINJ (match_cont_globalenv MCONT) hev
      (compat_cenv_union_l COMPAT)
    have hsw' := semSwitchArg_inject B hsw
    rw [← typeof_simpl_expr (cenvFor f) a] at hsw'
    refine ⟨_, step2_plus (.switch _ _ _ _ _ _ _ _ _ A hsw'),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF
        (simpl_seq_of_labeled_statement (simpl_select_switch n hls)) MENV (.Kswitch _ _ _ _ _ _ MCONT)
        MINJ ?_ HB THB⟩
    rw [addr_taken_seq_of_labeled_statement]
    exact compat_cenv_select_switch n (compat_cenv_union_r COMPAT)
  | goto f lbl k e le m s' k' hfl =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt] at TRS; cases TRS
    obtain ⟨body', hb, _, htf⟩ := transfFunction_inv TRF
    have FL := simpl_find_label (ge := prog.globalenv.genv_genv) (f := j) (m := m) (bound := lo)
      (tbound := tlo) lbl f.fn_body hb (match_cont_call_cont MCONT (cenvFor f)) (compat_cenv_for f)
    rw [hfl] at FL
    obtain ⟨ts', tk', A, B, C, D⟩ := FL
    refine ⟨_, step2_plus (.goto _ _ _ _ _ _ ts' tk' ?_),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF C MENV D MINJ B HB THB⟩
    subst htf
    simp only
    rw [find_label_add_debug_params, find_label_store_params, find_label_add_debug_vars]
    exact A
  | call f optid a al k e le m tyargs tyres cconv vf vargs fd hcl hev hevl hfd hty =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨x, hx, h⟩ := TRS; cases h
    obtain ⟨tvf, A, B⟩ := eval_simpl_expr hce hsym MENV MINJ (match_cont_globalenv MCONT) hev
      (compat_cenv_union_l COMPAT)
    obtain ⟨CASTED, tvargs, C, D⟩ := eval_simpl_exprlist hce hsym MENV MINJ
      (match_cont_globalenv MCONT) hevl (compat_cenv_union_r COMPAT)
    obtain ⟨tfd, P, Q⟩ := match_cont_find_funct TRANSF MCONT hfd B
    rw [← typeof_simpl_expr (cenvFor f) a] at hcl
    refine ⟨_, step2_plus (.call _ _ _ _ _ _ _ _ _ _ _ _ _ tfd hcl A C P
        (by rw [type_of_fundef_preserved Q]; exact hty)),
      .call _ _ _ _ _ _ _ _ j tyargs tyres cconv Q
        (fun cenv => .Kcall cenv optid f e le k tf te tle tk m hi thi lo tlo _ _ x TRF MENV MCONT hx
          HB THB) MINJ D hty CASTED⟩
  | builtin f optid ef tyargs al k e le m vargs t vres m' hevl hec =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at TRS
    obtain ⟨x, hx, h⟩ := TRS; cases h
    obtain ⟨CASTED, tvargs, C, D⟩ := eval_simpl_exprlist hce hsym MENV MINJ
      (match_cont_globalenv MCONT) hevl COMPAT
    obtain ⟨bnd, MG⟩ := match_cont_globalenv MCONT
    obtain ⟨j', tvres, tm', P, Q, R, S, T, U, V⟩ := externalCall_memInject ef hext hasm
      _ _ _ _ _ _ _ _ _ _ (match_globalenvs_symbols_inject MG rfl) hec MINJ D
    refine ⟨_, step2_plus (.builtin _ _ _ _ _ _ _ _ _ _ _ _ _ C (by rw [senv_preserved TRANSF]; exact P)),
      .regular _ _ _ _ _ _ _ _ _ _ _ _ j' lo hi tlo thi TRF rfl
        (match_envs_set_opttemp (match_envs_extcall MENV S U V HB THB) Q hx)
        (match_cont_extcall MCONT S U V (pos_le_trans MENV.me_incr HB)
          (pos_le_trans MENV.me_tincr THB)) R (compat_cenv_empty _)
        (pos_le_trans HB S.nextblock_le) (pos_le_trans THB T.nextblock_le)⟩
  | external_function ef targs tres cconv vargs k m vres t m' hec =>
    cases MS with
    | call _ _ _ _ tfd tvargs tk tm j targs' tres' cconv' TRFD MCONT MINJ VINJ FUNTY CASTED =>
    simp only [transfFundef] at TRFD; cases TRFD
    obtain ⟨bnd, MG⟩ := match_cont_globalenv (MCONT VSet.empty)
    obtain ⟨j', tvres, tm', P, Q, R, S, T, U, V⟩ := externalCall_memInject ef hext hasm
      _ _ _ _ _ _ _ _ _ _ (match_globalenvs_symbols_inject MG rfl) hec MINJ VINJ
    refine ⟨_, step2_plus (.external_function _ _ _ _ _ _ _ _ _ _
        (by rw [senv_preserved TRANSF]; exact P)),
      .ret _ _ _ _ _ _ j' (fun cenv => match_cont_incr_bounds
        (match_cont_extcall (MCONT cenv) S U V (Nat.le_refl _) (Nat.le_refl _))
        S.nextblock_le T.nextblock_le) R Q⟩
  | assign f a1 a2 k e le m loc ofs bf v2 v m' hlv hev hcast hass =>
    cases MS with
    | regular _ _ _ _ _ _ tf ts tk te tle tm j lo hi tlo thi TRF TRS MENV MCONT MINJ COMPAT HB THB =>
    have CH := is_liftable_var_charact (cenvFor f) a1
    simp only [simplStmt] at TRS
    obtain ⟨tv2, A, B⟩ := eval_simpl_expr hce hsym MENV MINJ (match_cont_globalenv MCONT) hev
      (compat_cenv_union_r COMPAT)
    obtain ⟨tv, C, D⟩ := Cop.semCast_inject hcast B MINJ
    rw [← typeof_simpl_expr (cenvFor f) a2] at C
    cases hlift : isLiftableVar (cenvFor f) a1 with
    | some id =>
      rw [hlift] at TRS CH
      cases TRS
      obtain ⟨ty, rfl, hmem⟩ := CH
      cases hlv with
      | Evar_global _ _ _ he _ =>
        cases MENV.me_vars id with
        | lifted _ _ _ _ _ h1 => rw [he] at h1; cases h1
        | not_lifted _ _ _ _ _ h3 => rw [hmem] at h3; cases h3
        | not_local _ _ h3 => rw [hmem] at h3; cases h3
      | Evar_local _ _ _ he =>
        cases MENV.me_vars id with
        | not_lifted _ _ _ _ _ h3 => rw [hmem] at h3; cases h3
        | not_local _ _ h3 => rw [hmem] at h3; cases h3
        | lifted b0 ty0 chunk v0 tv0 h1 _ _ hj hacc _ _ _ =>
        rw [he] at h1; cases h1
        refine ⟨_, step_Sset_debug A C, .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl
          (match_envs_assign_lifted MENV he (Cop.cast_val_is_casted hcast) D hass hmem)
          (match_cont_assign_loc MCONT hass (MENV.me_range id _ _ he).1)
          (assign_loc_unmapped_inject MINJ hass hacc hj) (compat_cenv_empty _)
          (by rw [assign_loc_nextblock hass]; exact HB) THB⟩
    | none =>
      rw [hlift] at TRS CH
      cases TRS
      obtain ⟨tb, tofs, E, F⟩ := eval_simpl_lvalue hce hsym MENV MINJ (match_cont_globalenv MCONT) hlv
        (compat_cenv_union_l COMPAT) CH
      obtain ⟨tm', X, Y, Z⟩ := assign_loc_inject hwf hass F D MINJ
      rw [← typeof_simpl_expr (cenvFor f) a1] at C X
      refine ⟨_, step2_plus (.assign _ _ _ _ _ _ _ _ _ _ _ _ _ E A C (by rw [hce]; exact X)),
        .regular _ _ _ _ _ _ _ _ _ _ _ _ j lo hi tlo thi TRF rfl
          (match_envs_invariant MENV (fun b chunk v hf _ hl => Z b chunk v hf hl)
            (Val.inject_incr_refl _) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
          (match_cont_invariant MCONT (fun b chunk v hf _ hl => Z b chunk v hf hl)
            (Val.inject_incr_refl _) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
          Y (compat_cenv_empty _)
          (by rw [assign_loc_nextblock hass]; exact HB)
          (by rw [assign_loc_nextblock X]; exact THB)⟩
  | internal_function f vargs k m e le m1 hentry =>
    cases MS with
    | call _ _ _ _ tfd tvargs tk tm j targs tres cconv TRFD MCONT MINJ VINJ FUNTY CASTED =>
    simp only [transfFundef] at TRFD
    split at TRFD
    · rename_i tf TRF
      cases TRFD
      obtain ⟨body', hb, hdisj, htf⟩ := transfFunction_inv TRF
      cases hentry with
      | intro m0 H0 H1 H2 hle =>
      subst hle
      have hnr : listNorepet (varNames (f.fn_params ++ f.fn_vars)) := by
        rw [varNames_app]; exact H0
      obtain ⟨j', te, tm0, A, B, C, D, E, F, G⟩ := match_envs_alloc_variables prog.globalenv.genv_cenv
        (cenv := cenvFor f) f.fn_temps H1 hnr MINJ
        (fun id ty hin hmem => cenv_for_gen_by_value hin hnr hmem)
        (fun id hmem => cenv_for_gen_domain hmem)
      have K : ValCastedList vargs (typeOfParams f.fn_params) := by
        simp only [typeOfFundef, typeOfFunction] at FUNTY
        cases FUNTY; exact CASTED
      obtain ⟨X, Y, Z⟩ := vars_and_temps_properties (cenv := cenvFor f) H0 hdisj
      obtain ⟨tel, tm1, P, Q, R, S, T⟩ := store_params_correct opts hwf (tge := tprog.globalenv) hce
        (f := tf) (k := tk) H2
        (s := addDebugVars opts (removeLifted (cenvFor f) (f.fn_params ++ f.fn_vars)) body')
        (tle2 := createUndefTemps (addLifted (cenvFor f) f.fn_vars f.fn_temps))
        X K (Val.inject_incr_inject_list D VINJ) B C
        (fun id hid => create_undef_temps_lifted hid)
        (fun id hid => create_undef_temps_none (hdisj id hid))
      subst htf
      refine ⟨_, plus_left (.internal_function _ _ _ _ _ _ _
          (FunctionEntry2.intro Y X Z (by rw [hce]; exact A) Q))
        (star_trans (step_add_debug_params X (valCastedList_inject VINJ K) Q)
          (star_trans P (step_add_debug_vars ?_) rfl) rfl) rfl,
        .regular _ _ _ _ _ _ _ _ _ _ _ _ j' _ _ _ _ TRF hb S ?_ R (compat_cenv_for f)
          (by rw [bind_parameters_nextblock H2]; exact Nat.le_refl _)
          (by rw [T]; exact Nat.le_refl _)⟩
      · intro id ty hin
        simp only [removeLifted, List.mem_filter, Bool.not_eq_true'] at hin
        exact G id ty hin.1 (by simpa using hin.2)
      · refine match_cont_invariant (MCONT (cenvFor f)) ?_ D ?_ ?_
        · intro b chunk v _ hblt hl
          refine bind_parameters_load ?_ H2 (alloc_variables_load H1 hl)
          intro id b' ty he heq
          subst heq
          rcases alloc_variables_range H1 he with h | h
          · simp [emptyEnv] at h
          · exact absurd (Nat.lt_of_lt_of_le hblt h.1) (Nat.lt_irrefl _)
        · intro b hb'
          exact E b (by simp [Mem.validBlock, hb'])
        · intro b b' delta hj hb'
          exact F b b' delta hj (by simp [Mem.validBlock, hb'])
    · cases TRFD

end STEP

section INIT
variable {opts : Options} {prog tprog : Program} (TRANSF : transfProgram opts prog = .OK tprog)
include TRANSF

/-- `SimplLocalsproof.initial_states_simulation` -/
theorem initial_states_simulation {S : State} (h : InitialState prog S) :
    ∃ R, InitialState tprog R ∧ MatchStates opts prog.globalenv.genv_genv S R := by
  cases h with
  | intro b f m0 hm hs hf ht =>
  obtain ⟨tf, A, B⟩ := function_ptr_translated TRANSF hf
  have MG : MatchGlobalenvs prog.globalenv.genv_genv (Mem.flatInj m0.nextblock) m0.nextblock :=
    { domain := fun b hb => by simp [Mem.flatInj, hb]
      image := fun b1 b2 delta h _ => by
        simp only [Mem.flatInj] at h
        split at h
        · cases h; rfl
        · cases h
      symbols := fun id b hs => by
        have := Program.findSymbol_not_fresh prog hm hs
        simpa [Mem.validBlock] using this
      functions := fun b fd hf => by
        have := Genv.findFunctPtr_not_fresh hm hf
        simpa [Mem.validBlock] using this
      varinfos := fun b gv hv => by
        have := Genv.findVarInfo_not_fresh hm hv
        simpa [Mem.validBlock] using this }
  refine ⟨_, .intro b tf m0 ?_ ?_ A (by rw [type_of_fundef_preserved B]; exact ht),
    .call _ _ _ _ _ _ _ _ (Mem.flatInj m0.nextblock) [] type_int32s cc_default B
      (fun cenv => .Kstop cenv m0 _ _ m0.nextblock MG (Nat.le_refl _) (Nat.le_refl _))
      (Program.initmem_inject prog hm) .nil ht .nil⟩
  · rw [Program.initMem_toAST, (transf_program_match TRANSF).init_mem]; exact hm
  · rw [symbols_preserved TRANSF]
    have hmain : tprog.prog_main = prog.prog_main := (transf_program_match TRANSF).main_eq
    rw [hmain]; exact hs

end INIT

/-- `SimplLocalsproof.final_states_simulation` -/
theorem final_states_simulation {opts : Options} {ge : Genv FunDef Ty} {S R : State}
    {r : Integers.Int} (hm : MatchStates opts ge S R) (h : FinalState S r) : FinalState R r := by
  cases h with
  | intro r m =>
  cases hm with
  | ret _ _ _ tv tk tm j MCONT _ RINJ =>
  cases MCONT VSet.empty
  cases RINJ
  exact .intro _ _

/-- `SimplLocalsproof.transf_program_correct`: pulling scalar local variables
    into temporaries preserves the semantics — a forward simulation from
    Clight with parameters in memory (`semantics1 prog`) to Clight with
    parameters as temporaries (`semantics2 tprog`).

    * `hwf`: the composite environment of `prog` is well formed (CompCert's
      `prog_comp_env_eq`; holds for programs built by `mkprogram`);
    * `hext` / `hasm`: external functions and inline assembly commute with
      memory injections (CompCert's `ec_mem_inject`, part of the
      `external_functions_properties` / `inline_assembly_properties` axioms). -/
theorem transf_program_correct (opts : Options) (prog tprog : Program)
    (TRANSF : transfProgram opts prog = .OK tprog)
    (hwf : CompositeEnv.WF prog.prog_comp_env)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg)) :
    ForwardSimulation (Clight.semantics1 prog) (Clight.semantics2 tprog) :=
  forward_simulation_plus (L1 := Clight.semantics1 prog) (L2 := Clight.semantics2 tprog)
    (MatchStates opts prog.globalenv.genv_genv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv.genv_genv).public_symbol id = _
      rw [senv_preserved TRANSF]; rfl)
    (fun _ h => initial_states_simulation TRANSF h)
    (fun _ _ _ hm h => final_states_simulation hm h)
    (fun _ _ _ hst _ hm => step_simulation TRANSF hwf hext hasm hst hm)

end SimplLocals
end CC
