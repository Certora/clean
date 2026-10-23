/-
  Translation from Clight to Csharpminor: semantic preservation — port of
  `cfrontend/Cshmgenproof.v`, part 6: the simulation proof (`transl_step`,
  `transl_initial_states`, `transl_final_states`) and the main theorem
  `transl_program_correct`: a forward simulation from `Clight.semantics2 prog`
  to `Csharpminor.semantics tprog`.

  Differences from Rocq:
  * whole-program statement (the translation of `prog` itself, not a
    `match_prog` with linking-order compilation units);
  * the port's Clight programs do not carry `prog_comp_env_eq`, so the well
    formedness of the composite environment is a hypothesis `hwf`
    (it holds for every program built by `mkprogram`:
    `mkprogram_compEnv_wf`);
  * external functions and inline assembly are uninterpreted in the port,
    so the well-typedness of their results (an axiom in CompCert, used through
    `external_call_well_typed_gen`) is taken as hypotheses `hextw`/`hasmw`;
  * the port's `PTree` is not canonical; `PTree.set2` (setting the same key
    twice) still holds structurally and is proved here as `ptree_set_set`.
-/
import CCLib.cfrontend.CshmgenproofMatch
import CCLib.common.EventsProps
import CCLib.common.Simulation

namespace CC
namespace Cshmgen

open Conventions1 (AbiKind)
open Smallstep

/-- `PTree.set2` (holds structurally for the port's non-canonical trees). -/
theorem ptree_set_set {A : Type} : ∀ (i : Positive) (v w : A) (t : PTree A),
    PTree.set i w (PTree.set i v t) = PTree.set i w t
  | .xH, _, _, .Leaf => rfl
  | .xH, _, _, .Node _ _ _ => rfl
  | .xO i, v, w, .Leaf => by simp only [PTree.set, ptree_set_set i v w]
  | .xO i, v, w, .Node _ _ _ => by simp only [PTree.set, ptree_set_set i v w]
  | .xI i, v, w, .Leaf => by simp only [PTree.set, ptree_set_set i v w]
  | .xI i, v, w, .Node _ _ _ => by simp only [PTree.set, ptree_set_set i v w]

theorem setOpttemp_eq (optid : Option Ident) (v : Val) (le : TempEnv) :
    setOpttemp optid v le = Cminor.setOptvar optid v le := by
  cases optid <;> rfl

theorem makeStore_not_block {ce : CompositeEnv} {addr rhs : Csharpminor.Expr} {ty : Ty}
    {bf : Bitfield} {s : Csharpminor.Stmt} (h : makeStore ce addr ty bf rhs = .OK s) :
    ∀ x, s ≠ .Sblock x := by
  intro x hx; subst hx
  unfold makeStore at h
  split at h
  · split at h
    · cases h
    · simp only [makeMemcpy, res_bind_eq_OK] at h
      obtain ⟨_, _, h⟩ := h; cases h
    · cases h
  · unfold makeStoreBitfield at h
    split at h <;> cases h

theorem matchTransl_nonblock {ts ts' : Csharpminor.Stmt} {tk tk' : Csharpminor.Cont}
    (h : MatchTransl ts tk ts' tk') (hnb : ∀ x, ts ≠ .Sblock x) : ts' = ts ∧ tk' = tk := by
  cases h with
  | zero => exact ⟨rfl, rfl⟩
  | one => exact (hnb _ rfl).elim

section STEP
variable {rvNorm : XType → Bool} {prog : Program} {tprog : Csharpminor.Program}
  (TRANSL : MatchProgram (MatchFundef rvNorm prog.prog_comp_env) (fun _ _ => True) prog.toAST tprog)
  (hwf : prog.prog_comp_env.WF)
  (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
  (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)

local notation "MS" => MatchStates rvNorm prog.prog_comp_env tprog.globalenv
local notation "TPLUS" => Smallstep.Plus (Csharpminor.Step tprog.globalenv)

include TRANSL hwf hextw hasmw in
/-- `Cshmgenproof.transl_step` -/
theorem transl_step {S1 : State} {t : Trace} {S2 : State}
    (hstep : Step2 prog.globalenv S1 t S2) {T1 : Csharpminor.State} (hms : MS S1 T1) :
    ∃ T2, TPLUS T1 t T2 ∧ MS S2 T2 := by
  cases hstep with
  | assign f a1 a2 k e le m loc ofs bf v2 v m' hl he hc ha =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨⟨tb, bf'⟩, hlv, tc, htc, tc', hcast, hst⟩ := htr
    obtain ⟨rfl, rfl⟩ := matchTransl_nonblock hmt (makeStore_not_block hst)
    obtain ⟨rfl, hev1⟩ := transl_lvalue_correct TRANSL hme hl hlv
    exact ⟨_, plus_one (make_store_correct hwf hst hev1
      (make_cast_correct hcast (transl_expr_correct TRANSL hme he htc) hc) ha),
      match_states_skip _ _ _ htf hme hk⟩
  | set f id a k e le m v he =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, htr⟩ := htr
    cases htr; cases hmt
    exact ⟨_, plus_one (.set _ _ _ _ _ _ _ _ (transl_expr_correct TRANSL hme he htb)),
      match_states_skip _ _ _ htf hme hk⟩
  | call f optid a al k e le m tyargs tyres cconv vf vargs fd hcf hev hevl hfind htype =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, hcf, res_bind_eq_OK] at htr
    obtain ⟨tb, htb, tcl, htcl, htr⟩ := htr
    cases htr
    obtain ⟨tfd, hfind', hmf⟩ := functions_translated TRANSL hfind
    have SIG : Csharpminor.funsig tfd =
        { sig_args := typlistOfArglist al tyargs, sig_res := rettypeOfType tyres,
          sig_cc := cconv } := by
      rw [typlist_of_arglist_eq hevl, transl_fundef_sig1 hmf (by rw [htype]; rfl)]
      rfl
    have EV := transl_expr_correct TRANSL hme hev htb
    have EVL := transl_arglist_correct TRANSL hme hevl htcl
    have TYPED := transl_arglist_typed hevl
    unfold makeFuncall at hmt
    split at hmt
    · -- with normalization of the return value
      next id _ =>
      cases hmt
      refine ⟨_, plus_left (.seq _ _ _ _ _ _ _)
        (star_one (.call _ _ _ _ _ _ _ _ _ _ _ _ EV EVL hfind' SIG)) rfl, ?_⟩
      exact .callstate _ _ _ _ _ _ _ _ _ hmf
        (.Kcall_normalize _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf hme
          hk
          (fun v e le m hwt hget => make_normalization_correct (.Evar _ _ hget) hwt))
        rfl htype TYPED
    · -- without normalization
      cases hmt
      exact ⟨_, plus_one (.call _ _ _ _ _ _ _ _ _ _ _ _ EV EVL hfind' SIG),
        .callstate _ _ _ _ _ _ _ _ _ hmf (.Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ htf hme hk) rfl
          htype TYPED⟩
  | builtin f optid ef tyargs al k e le m vargs t vres m' hevl hec =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨tbl, htbl, htr⟩ := htr
    cases htr; cases hmt
    refine ⟨_, plus_one (.builtin _ _ _ _ _ _ _ _ _ _ _ _
      (transl_arglist_correct TRANSL hme hevl htbl)
      (by rw [senv_preserved TRANSL]; exact hec)), ?_⟩
    rw [← setOpttemp_eq]
    exact match_states_skip _ _ _ htf hme hk
  | seq f s1 s2 k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ts1, h1, ts2, h2, htr⟩ := htr
    cases htr; cases hmt
    exact ⟨_, plus_one (.seq _ _ _ _ _ _ _),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf h1 (.zero _ _) hme (.Kseq _ _ _ _ _ _ _ h2 hk)⟩
  | skip_seq f s k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    cases hk with
    | Kseq _ _ _ _ _ ts0 tk0 hts hk0 =>
    exact ⟨_, plus_one (.skip_seq _ _ _ _ _ _),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf hts (.zero _ _) hme hk0⟩
  | continue_seq f s k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    cases hk with
    | Kseq _ _ _ _ _ ts0 tk0 hts hk0 =>
    exact ⟨_, plus_one (.exit_seq _ _ _ _ _ _ _),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf rfl (.zero _ _) hme hk0⟩
  | break_seq f s k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    cases hk with
    | Kseq _ _ _ _ _ ts0 tk0 hts hk0 =>
    exact ⟨_, plus_one (.exit_seq _ _ _ _ _ _ _),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf rfl (.zero _ _) hme hk0⟩
  | ifthenelse f a s1 s2 k e le m v1 b hev hb =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ta, hta, ts1, h1, ts2, h2, htr⟩ := htr
    cases htr; cases hmt
    obtain ⟨vb, A, B⟩ := make_boolean_correct (transl_expr_correct TRANSL hme hev hta) hb
    refine ⟨_, plus_one (.ifthenelse _ _ _ _ _ _ _ _ _ _ A B), ?_⟩
    cases b
    · exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf h2 (.zero _ _) hme hk
    · exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf h1 (.zero _ _) hme hk
  | loop f s1 s2 k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ts1, h1, ts2, h2, htr⟩ := htr
    cases htr
    refine ⟨_, star_plus_trans (match_transl_step _ hmt)
      (plus_left (.loop _ _ _ _ _ _)
        (star_left (.seq _ _ _ _ _ _ _) (star_one (.block _ _ _ _ _ _)) rfl) rfl) rfl, ?_⟩
    exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf h1 (.zero _ _) hme
      (.Kloop1 _ _ _ _ _ _ _ _ _ h1 h2 hk)
  | skip_or_continue_loop1 f s1 s2 k e le m x hx =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    cases hk with
    | Kloop1 _ _ _ _ ts1 ts2 nbrk0 ncnt0 tk0 h1 h2 hk0 =>
    rcases hx with rfl | rfl
    · simp only [translStatement] at htr
      cases htr; cases hmt
      exact ⟨_, plus_left (.skip_block _ _ _ _ _) (star_one (.skip_seq _ _ _ _ _ _)) rfl,
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf h2 (.zero _ _) hme
          (.Kloop2 _ _ _ _ _ _ _ _ _ h1 h2 hk0)⟩
    · simp only [translStatement] at htr
      cases htr; cases hmt
      exact ⟨_, plus_left (.exit_block_0 _ _ _ _ _) (star_one (.skip_seq _ _ _ _ _ _)) rfl,
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf h2 (.zero _ _) hme
          (.Kloop2 _ _ _ _ _ _ _ _ _ h1 h2 hk0)⟩
  | break_loop1 f s1 s2 k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    cases hk with
    | Kloop1 _ _ _ _ ts1 ts2 nbrk0 ncnt0 tk0 h1 h2 hk0 =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    exact ⟨_, plus_left (.exit_block_S _ _ _ _ _ _)
      (star_left (.exit_seq _ _ _ _ _ _ _)
        (star_left (.exit_seq _ _ _ _ _ _ _) (star_one (.exit_block_0 _ _ _ _ _)) rfl) rfl) rfl,
      match_states_skip _ _ _ htf hme hk0⟩
  | skip_loop2 f s1 s2 k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    cases hk with
    | Kloop2 _ _ _ _ ts1 ts2 nbrk0 ncnt0 tk0 h1 h2 hk0 =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    exact ⟨_, plus_one (.skip_seq _ _ _ _ _ _),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf (by simp only [translStatement, h1, h2]; rfl)
        (.one _ _) hme hk0⟩
  | break_loop2 f s1 s2 k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    cases hk with
    | Kloop2 _ _ _ _ ts1 ts2 nbrk0 ncnt0 tk0 h1 h2 hk0 =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    exact ⟨_, plus_left (.exit_seq _ _ _ _ _ _ _) (star_one (.exit_block_0 _ _ _ _ _)) rfl,
      match_states_skip _ _ _ htf hme hk0⟩
  | return_0 f k e le m m' hfree =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    exact ⟨_, plus_one (.return_0 _ _ _ _ _ _ (match_env_free_blocks hme hfree)),
      .returnstate _ _ _ _ _ (match_cont_call_cont _ _ _ hk 0 0) (.undef _)⟩
  | return_1 f a k e le m v v' m' hev hcast hfree =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ta, hta, ta', hta', htr⟩ := htr
    cases htr; cases hmt
    exact ⟨_, plus_one (.return_1 _ _ _ _ _ _ _ _
        (make_cast_correct hta' (transl_expr_correct TRANSL hme hev hta) hcast)
        (match_env_free_blocks hme hfree)),
      .returnstate _ _ _ _ _ (match_cont_call_cont _ _ _ hk 0 0)
        (Ctyping.wt_val_casted (Cop.cast_val_is_casted hcast))⟩
  | skip_call f k e le m m' hcc hfree =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    obtain ⟨A, B⟩ := match_cont_is_call_cont _ _ _ hk hcc 0 0
    exact ⟨_, plus_one (.skip_call _ _ _ _ _ _ B (match_env_free_blocks hme hfree)),
      .returnstate _ _ _ _ _ A (.undef _)⟩
  | switch f a sl k e le m v n hev harg =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ta, hta, tsl, hsl, htr⟩ := htr
    have E : ∃ b, ts = .Sblock (.Sswitch b ta tsl) ∧ Switch.SwitchArgument b v n := by
      unfold Cop.semSwitchArg at harg
      split at htr <;> rename_i hcs <;> rw [hcs] at harg <;> cases htr
      · cases v <;> simp at harg; subst harg; exact ⟨_, rfl, .arg32 _⟩
      · cases v <;> simp at harg; subst harg; exact ⟨_, rfl, .arg64 _⟩
    obtain ⟨b, rfl, B⟩ := E
    refine ⟨_, star_plus_trans (match_transl_step _ hmt)
      (plus_one (.switch _ _ _ _ _ _ _ _ _ _ (transl_expr_correct TRANSL hme hev hta) B)) rfl, ?_⟩
    exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf (transl_lbl_stmt_2 (transl_lbl_stmt_1 n hsl))
      (.zero _ _) hme (.Kswitch _ _ _ _ _ hk)
  | skip_break_switch f x k e le m hx =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    cases hk with
    | Kswitch _ nbrk0 ncnt0 _ tk0 hk0 =>
    rcases hx with rfl | rfl
    · simp only [translStatement] at htr
      cases htr; cases hmt
      exact ⟨_, plus_one (.skip_block _ _ _ _ _), match_states_skip _ _ _ htf hme hk0⟩
    · simp only [translStatement] at htr
      cases htr; cases hmt
      exact ⟨_, plus_one (.exit_block_0 _ _ _ _ _), match_states_skip _ _ _ htf hme hk0⟩
  | continue_switch f k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    cases hk with
    | Kswitch _ nbrk0 ncnt0 _ tk0 hk0 =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    exact ⟨_, plus_one (.exit_block_S _ _ _ _ _ _),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf rfl (.zero _ _) hme hk0⟩
  | label f lbl s k e le m =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement, res_bind_eq_OK] at htr
    obtain ⟨ts0, h0, htr⟩ := htr
    cases htr; cases hmt
    exact ⟨_, plus_one (.label _ _ _ _ _ _ _),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf h0 (.zero _ _) hme hk⟩
  | goto f lbl k e le m s' k' hfl =>
    cases hms with
    | state _ nbrk ncnt _ _ _ _ _ tf ts tk te ts' tk' htf htr hmt hme hk =>
    simp only [translStatement] at htr
    cases htr; cases hmt
    have htf' := htf
    simp only [translFunction, res_bind_eq_OK] at htf'
    obtain ⟨tbody, hbody, tvars, _, htf'⟩ := htf'
    cases htf'
    have A := transl_find_label rvNorm prog.prog_comp_env tprog.globalenv lbl f.fn_return f.fn_body
      hbody (match_cont_call_cont _ _ _ hk 1 0)
    rw [hfl] at A
    obtain ⟨ts'', tk'', nbrk', ncnt', B, C, D⟩ := A
    exact ⟨_, plus_one (.goto _ _ _ _ _ _ _ _ B),
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf C (.zero _ _) hme D⟩
  | internal_function f vargs k m e le m1 hentry =>
    cases hms with
    | callstate _ _ _ _ tfd tk targs tres cconv hmf hk hcc htype hargs =>
    cases hmf with
    | internal _ tf htf =>
    cases hentry with
    | intro hnr1 hnr2 hdisj halloc hbind =>
    have htf' := htf
    simp only [translFunction, res_bind_eq_OK] at htf'
    obtain ⟨tbody, hbody, tvars, htvars, htf'⟩ := htf'
    cases htf'
    obtain ⟨A, B⟩ := match_cont_is_call_cont _ _ _ hk hcc 1 0
    obtain ⟨te1, C, D⟩ := match_env_alloc_variables halloc htvars match_env_empty
    simp only [typeOfFundef, typeOfFunction] at htype
    cases htype
    refine ⟨_, plus_one (.internal_function _ _ _ _ _ _ le ?_ ?_ hnr2 hdisj C ?_), ?_⟩
    · exact hargs
    · show listNorepet (tvars.map Prod.fst)
      rw [transl_vars_names htvars]; exact hnr1
    · show Csharpminor.bindParameters (f.fn_params.map (·.1)) vargs
        (Csharpminor.createUndefTemps (f.fn_temps.map (·.1))) = some le
      rw [create_undef_temps_match]
      exact bind_parameter_temps_match _ _ _ _ hbind
    · exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ htf hbody (.zero _ _) D A
  | external_function ef targs tres cconv vargs k m vres t m' hec =>
    cases hms with
    | callstate _ _ _ _ tfd tk targs' tres' cconv' hmf hk hcc htype hargs =>
    cases hmf with
    | external _ _ _ _ hsig =>
    simp only [typeOfFundef] at htype
    cases htype
    obtain ⟨A, B⟩ := match_cont_is_call_cont _ _ _ hk hcc 0 0
    have hwt := externalCall_wellTyped ef hextw hasmw _ _ _ _ _ _ hec
    rw [hsig] at hwt
    exact ⟨_, plus_one (.external_function _ _ _ _ _ _ _ (by rw [senv_preserved TRANSL]; exact hec)),
      .returnstate _ _ _ _ _ A (Ctyping.has_rettype_wt_val hwt)⟩
  | returnstate v optid f e le k m =>
    cases hms with
    | returnstate _ tres _ _ tk hk hwt =>
    cases hk with
    | Kcall _ _ _ nbrk' ncnt' _ _ _ _ tf te _ tk0 htf hme hk0 =>
      refine ⟨_, plus_one (.return _ _ _ _ _ _ _), ?_⟩
      rw [← setOpttemp_eq]
      exact match_states_skip _ _ _ htf hme hk0
    | Kcall_normalize _ _ _ nbrk' ncnt' _ _ _ id a tf te _ tk0 htf hme hk0 hnorm =>
      refine ⟨_, plus_left (.return _ _ _ _ _ _ _)
        (star_left (.skip_seq _ _ _ _ _ _)
          (star_one (.set _ _ _ _ _ _ _ _ (hnorm _ _ _ _ hwt (PTree.gss _ _ _)))) rfl) rfl, ?_⟩
      simp only [Cminor.setOptvar, ptree_set_set]
      exact match_states_skip _ _ _ htf hme hk0

include TRANSL in
/-- `Cshmgenproof.transl_initial_states` -/
theorem transl_initial_states {S : State} (h : InitialState prog S) :
    ∃ R, Csharpminor.InitialState tprog R ∧ MS S R := by
  cases h with
  | intro b f m0 hm hs hf ht =>
  obtain ⟨tf, hf', hmf⟩ := function_ptr_translated TRANSL hf
  refine ⟨_, .intro b tf m0 ?_ ?_ hf' ?_,
    .callstate _ _ _ _ _ _ [] type_int32s cc_default hmf (.Kstop _ _ _) rfl ht (by trivial)⟩
  · rw [TRANSL.init_mem]; exact hm
  · rw [symbols_preserved TRANSL, TRANSL.main_eq]
    exact hs
  · rw [transl_fundef_sig2 hmf ht]; rfl

/-- `Cshmgenproof.transl_final_states` -/
theorem transl_final_states {S : State} {R : Csharpminor.State} {r : Integers.Int}
    (hm : MS S R) (h : FinalState S r) : Csharpminor.FinalState R r := by
  cases h with
  | intro r m =>
  cases hm with
  | returnstate _ _ _ _ _ hk _ =>
  cases hk
  exact .intro _ _

end STEP

/-- `Cshmgenproof.transl_program_correct`: the translation from Clight
    (`semantics2`, parameters as temporaries) to Csharpminor preserves the
    semantics (forward simulation).  Whole-program version.

    * `hwf`: the composite environment of `prog` is well formed (CompCert's
      `prog_comp_env_eq`; holds for programs built by `mkprogram`);
    * `hextw` / `hasmw`: external functions and inline assembly return
      well-typed results (CompCert's `external_call_well_typed_gen`, an
      axiom there). -/
theorem transl_program_correct_gen (rvNorm : XType → Bool) (prog : Program)
    (tprog : Csharpminor.Program)
    (TRANSL : MatchProgram (MatchFundef rvNorm prog.prog_comp_env) (fun _ _ => True) prog.toAST tprog)
    (hwf : prog.prog_comp_env.WF)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ForwardSimulation (Clight.semantics2 prog) (Csharpminor.semantics tprog) :=
  forward_simulation_plus (L1 := Clight.semantics2 prog) (L2 := Csharpminor.semantics tprog)
    (MatchStates rvNorm prog.prog_comp_env tprog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id = _
      rw [senv_preserved TRANSL]; rfl)
    (fun _ h => transl_initial_states TRANSL h)
    (fun _ _ _ hm h => transl_final_states hm h)
    (fun _ _ _ hst _ hm => transl_step TRANSL hwf hextw hasmw hst hm)

/-- `Cshmgenproof.transl_program_correct`, for the output of `transl_program`. -/
theorem transl_program_correct (rvNorm : XType → Bool) (prog : Program) (tprog : Csharpminor.Program)
    (TRANSL : translProgram rvNorm prog = .OK tprog)
    (hwf : prog.prog_comp_env.WF)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ForwardSimulation (Clight.semantics2 prog) (Csharpminor.semantics tprog) :=
  transl_program_correct_gen rvNorm prog tprog (transf_program_match TRANSL) hwf hextw hasmw

end Cshmgen
end CC
