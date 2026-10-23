/-
  Correctness of Cminor generation — port of `cfrontend/Cminorgenproof.v`,
  part 5: the simulation diagram (`transl_step_correct`), the initial and
  final states (`match_globalenvs_init`, `transl_initial_states`,
  `transl_final_states`) and the main theorem `transl_program_correct`.

  Differences from Rocq:
  * whole-program statement (`translProgram prog = .OK tprog`);
  * the injection property of external functions and inline assembly
    (`ec_mem_inject`) and their memory properties (`ec_max_perm`, …), which
    CompCert takes from the axioms `external_functions_properties` /
    `inline_assembly_properties`, are hypotheses `hext`/`hasm` and
    `hextp`/`hasmp` of `transl_program_correct`;
  * the cases of `transl_step_correct` that CompCert proves by `dependent
    induction` on `match_cont` are separate lemmas (`skip_seq_correct`,
    `skip_block_correct`, `exit_seq_correct`, `exit_block_0_correct`,
    `exit_block_S_correct`).
-/
import CCLib.cfrontend.CminorgenproofMatch
import CCLib.common.EventsMem
import CCLib.common.Simulation
import CCLib.common.LinkingFundef

namespace CC
namespace Cminorgen

open Smallstep

local macro "blk_omega" : tactic =>
  `(tactic| (simp only [Positive.lt_iff, pos_le_iff, Positive.toNat_succ] at *; omega))

/-! ## Auxiliary facts -/

theorem storev_perm {chunk : Chunk} {m : Mem} {a v : Val} {m' : Mem}
    (h : Mem.storev chunk m a v = some m') (b : Block) (ofs : Z) (k : PermKind) (p : Permission) :
    Mem.perm m' b ofs k p = Mem.perm m b ofs k p := by
  cases a with
  | Vptr b0 ofs0 => exact Mem.perm_store (Mem.storev_store h) b ofs k p
  | _ => cases h

/-- A `match_cont` for a call continuation does not depend on the
    compilation environment. -/
theorem match_cont_call_cenv {k : Csharpminor.Cont} {tk : Cminor.Cont} {cenv0 : Compilenv}
    {cs : Callstack} (cenv : Compilenv) (h : MatchCont k tk cenv0 [] cs)
    (hcc : Csharpminor.isCallCont k = true) : MatchCont k tk cenv [] cs := by
  cases h with
  | Kstop => exact .Kstop _ _
  | Kseq => simp [Csharpminor.isCallCont] at hcc
  | Kseq2 => simp [Csharpminor.isCallCont] at hcc
  | Kcall optid fn e le k tfn sp te tk cenv1 xenv lo hi cs sz _ h1 h2 =>
    exact .Kcall optid fn e le k tfn sp te tk cenv1 xenv lo hi cs sz cenv h1 h2

theorem translFunbody_inv {cenv : Compilenv} {sz : Z} {f : Csharpminor.Function}
    {tf : Cminor.Function} (h : translFunbody cenv sz f = .OK tf) :
    ∃ tbody, translStmt cenv [] f.fn_body = .OK tbody ∧
      tf = { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_vars := f.fn_temps,
             fn_stackspace := sz, fn_body := tbody } := by
  simp only [translFunbody, Cshmgen.res_bind_eq_OK] at h
  obtain ⟨tbody, h1, h⟩ := h
  cases h
  exact ⟨tbody, h1, rfl⟩

/-- `Cminorgenproof.seq_left_depth` -/
def seqLeftDepth : Csharpminor.Stmt → Nat
  | .Sseq s1 _ => seqLeftDepth s1 + 1
  | _ => 0

/-- `Cminorgenproof.measure` -/
def measure : Csharpminor.State → Nat
  | .State _ s _ _ _ _ => seqLeftDepth s
  | _ => 0

/-! ## The cases of the simulation proved by induction on `match_cont` -/

section CONT
variable {ge : Csharpminor.CGenv} {tge : Cminor.CGenv} {fn : Csharpminor.Function}
  {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {m : Mem} {tfn : Cminor.Function}
  {sp : Block} {te : Cminor.Env} {tm : Mem} {cenv : Compilenv} {f : Val.Meminj} {lo hi : Block}
  {cs : Callstack} {sz : Z}
  (TRF : translFunbody cenv sz fn = .OK tfn) (MINJ : Mem.Inject f m tm)
  (MCS : MatchCallstack ge f m tm (⟨cenv, tfn, e, le, te, sp, lo, hi⟩ :: cs) m.nextblock tm.nextblock)
include TRF MINJ MCS

theorem skip_seq_correct {s : Csharpminor.Stmt} {k : Csharpminor.Cont} :
    ∀ {k0 tk xenv}, MatchCont k0 tk cenv xenv cs → k0 = .Kseq s k →
    ∃ T2, Smallstep.Plus (Cminor.Step tge)
      (Cminor.State.State tfn .Sskip tk (.Vptr sp Integers.Ptrofs.zero) te tm) E0 T2 ∧
      MatchStates ge (.State fn s k e le m) T2 := by
  intro k0 tk xenv MK
  induction MK with
  | Kseq s' k' ts tk' cenv' xenv' cs' h1 h2 =>
    intro heq; cases heq
    exact ⟨_, plus_one (.skip_seq _ _ _ _ _ _), .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      TRF h1 MINJ MCS h2⟩
  | Kseq2 s1 s2 k' ts1 tk' cenv' xenv' cs' h1 h2 =>
    intro heq; cases heq
    exact ⟨_, plus_one (.skip_seq _ _ _ _ _ _), .state_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      TRF h1 MINJ MCS h2⟩
  | Kblock2 k' tk' cenv' xenv' cs' _ ih =>
    intro heq
    obtain ⟨T2, A, B⟩ := ih TRF MCS heq
    exact ⟨T2, plus_left (.skip_block _ _ _ _ _) (plus_star A) rfl, B⟩
  | Kstop => intro heq; cases heq
  | Kblock => intro heq; cases heq
  | Kcall => intro heq; cases heq

theorem skip_block_correct {k : Csharpminor.Cont} :
    ∀ {k0 tk xenv}, MatchCont k0 tk cenv xenv cs → k0 = .Kblock k →
    ∃ T2, Smallstep.Plus (Cminor.Step tge)
      (Cminor.State.State tfn .Sskip tk (.Vptr sp Integers.Ptrofs.zero) te tm) E0 T2 ∧
      MatchStates ge (.State fn .Sskip k e le m) T2 := by
  intro k0 tk xenv MK
  induction MK with
  | Kblock k' tk' cenv' xenv' cs' h =>
    intro heq; cases heq
    exact ⟨_, plus_one (.skip_block _ _ _ _ _), .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      TRF (translStmt_skip _ _) MINJ MCS h⟩
  | Kblock2 k' tk' cenv' xenv' cs' _ ih =>
    intro heq
    obtain ⟨T2, A, B⟩ := ih TRF MCS heq
    exact ⟨T2, plus_left (.skip_block _ _ _ _ _) (plus_star A) rfl, B⟩
  | Kstop => intro heq; cases heq
  | Kseq => intro heq; cases heq
  | Kseq2 => intro heq; cases heq
  | Kcall => intro heq; cases heq

theorem exit_seq_correct {k : Csharpminor.Cont} {n : Nat} :
    ∀ {k0 tk xenv}, MatchCont k0 tk cenv xenv cs → ∀ (s : Csharpminor.Stmt), k0 = .Kseq s k →
    ∃ T2, Smallstep.Plus (Cminor.Step tge)
      (Cminor.State.State tfn (.Sexit (shiftExit xenv n)) tk (.Vptr sp Integers.Ptrofs.zero) te tm) E0 T2 ∧
      MatchStates ge (.State fn (.Sexit n) k e le m) T2 := by
  intro k0 tk xenv MK
  induction MK with
  | Kseq s' k' ts tk' cenv' xenv' cs' h1 h2 =>
    intro s heq; cases heq
    exact ⟨_, plus_one (.exit_seq _ _ _ _ _ _ _), .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      TRF (by simp [translStmt]) MINJ MCS h2⟩
  | Kseq2 s1 s2 k' ts1 tk' cenv' xenv' cs' h1 h2 ih =>
    intro s heq; cases heq
    obtain ⟨T2, A, B⟩ := ih TRF MCS s2 rfl
    exact ⟨T2, plus_left (.exit_seq _ _ _ _ _ _ _) (plus_star A) rfl, B⟩
  | Kblock2 k' tk' cenv' xenv' cs' _ ih =>
    intro s heq
    obtain ⟨T2, A, B⟩ := ih TRF MCS s heq
    exact ⟨T2, plus_left (.exit_block_S _ _ _ _ _ _) (plus_star A) rfl, B⟩
  | Kstop => intro s heq; cases heq
  | Kblock => intro s heq; cases heq
  | Kcall => intro s heq; cases heq

theorem exit_block_0_correct {k : Csharpminor.Cont} :
    ∀ {k0 tk xenv}, MatchCont k0 tk cenv xenv cs → k0 = .Kblock k →
    ∃ T2, Smallstep.Plus (Cminor.Step tge)
      (Cminor.State.State tfn (.Sexit (shiftExit xenv 0)) tk (.Vptr sp Integers.Ptrofs.zero) te tm) E0 T2 ∧
      MatchStates ge (.State fn .Sskip k e le m) T2 := by
  intro k0 tk xenv MK
  induction MK with
  | Kblock k' tk' cenv' xenv' cs' h =>
    intro heq; cases heq
    exact ⟨_, plus_one (.exit_block_0 _ _ _ _ _), .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      TRF (translStmt_skip _ _) MINJ MCS h⟩
  | Kblock2 k' tk' cenv' xenv' cs' _ ih =>
    intro heq
    obtain ⟨T2, A, B⟩ := ih TRF MCS heq
    exact ⟨T2, plus_left (.exit_block_S _ _ _ _ _ _) (plus_star A) rfl, B⟩
  | Kstop => intro heq; cases heq
  | Kseq => intro heq; cases heq
  | Kseq2 => intro heq; cases heq
  | Kcall => intro heq; cases heq

theorem exit_block_S_correct {k : Csharpminor.Cont} {n : Nat} :
    ∀ {k0 tk xenv}, MatchCont k0 tk cenv xenv cs → k0 = .Kblock k →
    ∃ T2, Smallstep.Plus (Cminor.Step tge)
      (Cminor.State.State tfn (.Sexit (shiftExit xenv (n + 1))) tk (.Vptr sp Integers.Ptrofs.zero) te tm)
      E0 T2 ∧ MatchStates ge (.State fn (.Sexit n) k e le m) T2 := by
  intro k0 tk xenv MK
  induction MK with
  | Kblock k' tk' cenv' xenv' cs' h =>
    intro heq; cases heq
    exact ⟨_, plus_one (.exit_block_S _ _ _ _ _ _), .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      TRF (by simp [translStmt]) MINJ MCS h⟩
  | Kblock2 k' tk' cenv' xenv' cs' _ ih =>
    intro heq
    obtain ⟨T2, A, B⟩ := ih TRF MCS heq
    exact ⟨T2, plus_left (.exit_block_S _ _ _ _ _ _) (plus_star A) rfl, B⟩
  | Kstop => intro heq; cases heq
  | Kseq => intro heq; cases heq
  | Kseq2 => intro heq; cases heq
  | Kcall => intro heq; cases heq

end CONT

/-! ## The simulation diagram -/

section TRANSLATION
variable {prog : Csharpminor.Program} {tprog : Cminor.Program}
  (TRANSL : translProgram prog = .OK tprog)
  (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
  (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
  (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
  (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)

include TRANSL hext hasm hextp hasmp in
/-- External calls preserve `match_callstack` and the memory injection. -/
theorem external_call_correct {ef : ExtFun} {vargs : List Val} {m : Mem} {t : Trace} {vres : Val}
    {m' : Mem} {f : Val.Meminj} {tm : Mem} {tvargs : List Val} {cs : Callstack}
    (hec : externalCall ef (Genv.toSenv prog.globalenv) vargs m t vres m')
    (MINJ : Mem.Inject f m tm)
    (MCS : MatchCallstack prog.globalenv f m tm cs m.nextblock tm.nextblock)
    (VINJ : Val.InjectList f vargs tvargs) :
    ∃ f' tvres tm', externalCall ef (Genv.toSenv tprog.globalenv) tvargs tm t tvres tm' ∧
      Val.Inject f' vres tvres ∧ Mem.Inject f' m' tm' ∧ Val.inject_incr f f' ∧
      MatchCallstack prog.globalenv f' m' tm' cs m'.nextblock tm'.nextblock := by
  obtain ⟨bnd, MG⟩ := match_callstack_match_globalenvs MCS
  obtain ⟨f', tvres, tm', EC, VI, MINJ', UNMAPPED, OUTOFREACH, INCR, SEP⟩ :=
    externalCall_memInject ef hext hasm _ _ _ _ _ _ _ _ _ _ (match_globalenvs_symbols_inject MG)
      hec MINJ VINJ
  have MP := externalCall_memProps ef (Genv.toSenv prog.globalenv) (fun n sg => hextp n sg _)
    (fun n sg => hasmp n sg _)
  refine ⟨f', tvres, tm', by rw [senv_preserved TRANSL]; exact EC, VI, MINJ', INCR, ?_⟩
  refine match_callstack_incr_bound (match_callstack_external_call OUTOFREACH INCR SEP
    (fun b ofs p hv hp => MP.maxPerm _ _ _ _ _ b ofs p hec hv hp) MCS (Nat.le_refl _)
    (Nat.le_refl _)) UNMAPPED.nextblock_le OUTOFREACH.nextblock_le

include TRANSL hext hasm hextp hasmp

set_option maxHeartbeats 2000000 in
/-- `Cminorgenproof.transl_step_correct` -/
theorem transl_step_correct {S1 : Csharpminor.State} {t : Trace} {S2 : Csharpminor.State}
    (hst : Csharpminor.Step prog.globalenv S1 t S2) {T1 : Cminor.State}
    (MS : MatchStates prog.globalenv S1 T1) :
    (∃ T2, Smallstep.Plus (Cminor.Step tprog.globalenv) T1 t T2 ∧ MatchStates prog.globalenv S2 T2) ∨
      (measure S2 < measure S1 ∧ t = E0 ∧ MatchStates prog.globalenv S2 T1) := by
  cases hst with
  | skip_seq fn s k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      exact .inl (skip_seq_correct TRF MINJ MCS MK rfl)
  | skip_block fn k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      exact .inl (skip_block_correct TRF MINJ MCS MK rfl)
  | skip_call fn k e le m m' hcc hfl =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      obtain ⟨tk', A, B, C⟩ := match_is_call_cont (tge := tprog.globalenv) (tfn := tfn) (te := te)
        (sp := .Vptr sp Integers.Ptrofs.zero) (tm := tm) MK hcc
      obtain ⟨tm', P, Q, R⟩ := match_callstack_freelist MINJ hfl MCS
      exact .inl ⟨_, plus_right A (.skip_call _ _ _ _ _ _ B P) rfl,
        .returnstate _ _ _ _ _ _ _ _ _ R Q C (.undef _)⟩
  | set fn id a k e le m v hev =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ta, h1, h⟩ := TR; cases h
      obtain ⟨tv, A, B⟩ := transl_expr_correct TRANSL MINJ MCS hev h1
      exact .inl ⟨_, plus_one (.assign _ _ _ _ _ _ _ _ A),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF (translStmt_skip _ _) MINJ
          (match_callstack_set_temp B MCS) MK⟩
  | store fn chunk addr a k e le m vaddr v m' hev1 hev2 hst =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ta1, h1, ta2, h2, h⟩ := TR; cases h
      obtain ⟨tv1, A1, B1⟩ := transl_expr_correct TRANSL MINJ MCS hev1 h1
      obtain ⟨tv2, A2, B2⟩ := transl_expr_correct TRANSL MINJ MCS hev2 h2
      obtain ⟨tm', STORE', MINJ'⟩ := Mem.storev_mapped_inject MINJ hst B1 B2
      have MCS' : MatchCallstack prog.globalenv f m' tm'
          (⟨cenv, tfn, e, le, te, sp, lo, hi⟩ :: cs) m'.nextblock tm'.nextblock := by
        rw [Mem.storev_nextblock hst, Mem.storev_nextblock STORE']
        exact match_callstack_invariant MCS (Val.inject_incr_refl f)
          (fun b ofs p _ hp => by rwa [storev_perm hst] at hp)
          (fun sp' ofs _ hp => by rwa [storev_perm STORE'])
          (fun _ _ => rfl) (fun _ _ _ h _ => h)
      exact .inl ⟨_, plus_one (.store _ _ _ _ _ _ _ _ _ _ _ A1 A2 STORE'),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF (translStmt_skip _ _) MINJ' MCS' MK⟩
  | call fn optid sig a bl k e le m vf vargs fd hev hevl hff hsig =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ta, h1, tal, h2, h⟩ := TR; cases h
      obtain ⟨tfd, FIND, TRANS⟩ := functions_translated TRANSL hff
      obtain ⟨tvf, A, B⟩ := transl_expr_correct TRANSL MINJ MCS hev h1
      obtain ⟨bnd, MG⟩ := match_callstack_match_globalenvs MCS
      have := val_inject_function_pointer hff MG B
      subst this
      obtain ⟨tvargs, C, D⟩ := transl_exprlist_correct TRANSL MINJ MCS hevl h2
      exact .inl ⟨_, plus_one (.call _ _ _ _ _ _ _ _ _ _ _ _ A C FIND
          (by rw [sig_preserved TRANS]; exact hsig)),
        .callstate _ _ _ _ _ _ _ _ f _ cenv TRANS MINJ MCS
          (.Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cenv TRF MK) rfl D⟩
  | builtin fn optid ef bl k e le m vargs t vres m' hevl hec =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨tal, h1, h⟩ := TR; cases h
      obtain ⟨tvargs, A, B⟩ := transl_exprlist_correct TRANSL MINJ MCS hevl h1
      obtain ⟨f', tvres, tm', EC, VI, MINJ', INCR, MCS'⟩ :=
        external_call_correct TRANSL hext hasm hextp hasmp hec MINJ MCS B
      have MCS'' : MatchCallstack prog.globalenv f' m' tm'
          (⟨cenv, tfn, e, Cminor.setOptvar optid vres le, Cminor.setOptvar optid tvres te, sp, lo, hi⟩ :: cs)
          m'.nextblock tm'.nextblock := by
        cases optid with
        | none => exact MCS'
        | some id => exact match_callstack_set_temp VI MCS'
      exact .inl ⟨_, plus_one (.builtin _ _ _ _ _ _ _ _ _ _ _ _ A EC),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF (translStmt_skip _ _) MINJ' MCS'' MK⟩
  | seq fn s1 s2 k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ts1, h1, ts2, h2, h⟩ := TR; cases h
      exact .inl ⟨_, plus_one (.seq _ _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF h1 MINJ MCS (.Kseq _ _ _ _ _ _ _ h2 MK)⟩
    | state_seq _ _ _ _ _ _ _ tfn ts1 tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      exact .inr ⟨by simp [measure, seqLeftDepth], rfl,
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF TR MINJ MCS MK⟩
  | ifthenelse fn a s1 s2 k e le m v b hev hb =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ta, h0, ts1, h1, ts2, h2, h⟩ := TR; cases h
      obtain ⟨tv, A, B⟩ := transl_expr_correct TRANSL MINJ MCS hev h0
      refine .inl ⟨_, plus_one (.ifthenelse _ _ _ _ _ _ _ _ _ b A (bool_of_val_inject hb B)),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF ?_ MINJ MCS MK⟩
      cases b
      · exact h2
      · exact h1
  | loop fn s k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ts1, h1, h⟩ := TR; cases h
      exact .inl ⟨_, plus_one (.loop _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF h1 MINJ MCS
          (.Kseq _ _ _ _ _ _ _ (by simp only [translStmt, h1]; rfl) MK)⟩
  | block fn s k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ts1, h1, h⟩ := TR; cases h
      exact .inl ⟨_, plus_one (.block _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF h1 MINJ MCS (.Kblock _ _ _ _ _ MK)⟩
  | exit_seq fn n s k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      exact .inl (exit_seq_correct TRF MINJ MCS MK _ rfl)
  | exit_block_0 fn k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      exact .inl (exit_block_0_correct TRF MINJ MCS MK rfl)
  | exit_block_S fn n k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      exact .inl (exit_block_S_correct TRF MINJ MCS MK rfl)
  | switch fn islong a cases k e le m v n hev hsa =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR
      rcases STBL : switchTable cases 0 with ⟨tbl, dfl⟩
      rw [STBL] at TR
      simp only [Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ta, h1, TR⟩ := TR
      obtain ⟨tv, A, B⟩ := transl_expr_correct TRANSL MINJ MCS hev h1
      have SA : Switch.SwitchArgument islong tv n := by
        cases hsa <;> cases B <;> constructor
      obtain ⟨k1, P, Q⟩ := switch_descent (tge := tprog.globalenv) (k := tk) TR
      have TAIL := switch_table_select n cases
      rw [STBL] at TAIL
      obtain ⟨k2, C, D⟩ := switch_ascent (tge := tprog.globalenv) (f := tfn)
        (sp := .Vptr sp Integers.Ptrofs.zero) (e := te) (m := tm) TAIL P
      obtain ⟨body', ts', E⟩ := transl_lblstmt_suffix TAIL TR
      obtain ⟨T2, F, G⟩ := switch_match_states (tge := tprog.globalenv) TRF E MINJ MCS MK D
      exact .inl ⟨T2, plus_star_trans (Q _ _ _ _)
        (star_left (.switch _ _ _ _ _ _ _ _ _ _ _ A SA)
          (star_trans C (plus_star F) rfl) rfl) rfl, G⟩
  | return_0 fn k e le m m' hfl =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      obtain ⟨tm', P, Q, R⟩ := match_callstack_freelist MINJ hfl MCS
      exact .inl ⟨_, plus_one (.return_0 _ _ _ _ _ _ P),
        .returnstate _ _ _ _ _ _ _ _ _ R Q (match_call_cont MK) (.undef _)⟩
  | return_1 fn a k e le m v m' hev hfl =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ta, h1, h⟩ := TR; cases h
      obtain ⟨tv, A, B⟩ := transl_expr_correct TRANSL MINJ MCS hev h1
      obtain ⟨tm', P, Q, R⟩ := match_callstack_freelist MINJ hfl MCS
      exact .inl ⟨_, plus_one (.return_1 _ _ _ _ _ _ _ _ A P),
        .returnstate _ _ _ _ _ _ _ _ _ R Q (match_call_cont MK) B⟩
  | label fn lbl s k e le m =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt, Cshmgen.res_bind_eq_OK] at TR
      obtain ⟨ts1, h1, h⟩ := TR; cases h
      exact .inl ⟨_, plus_one (.label _ _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF h1 MINJ MCS MK⟩
  | goto fn lbl k e le m s' k' hfl =>
    cases MS with
    | state _ _ _ _ _ _ tfn ts tk sp te tm cenv xenv f lo hi cs sz TRF TR MINJ MCS MK =>
      simp only [translStmt] at TR; cases TR
      obtain ⟨ts', tk', xenv', A, B, C⟩ := transl_find_label_body TRF MK hfl
      exact .inl ⟨_, plus_one (.goto _ _ _ _ _ _ _ _ A),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF B MINJ MCS C⟩
  | internal_function fn vargs k m m1 e le hty hnr1 hnr2 hdisj hav hbp =>
    cases MS with
    | callstate _ _ _ _ tfd targs tk tm f cs cenv0 TR MINJ MCS MK ISCC ARGS =>
      simp only [translFundef, ASTFundef.transfPartial] at TR
      split at TR
      · rename_i tf htf
        cases TR
        obtain ⟨cenv, BC, REPRES, TRF⟩ := translFunction_inv htf
        obtain ⟨tbody, TB, htf'⟩ := translFunbody_inv TRF
        rcases ALLOC : Mem.alloc tm 0 tf.fn_stackspace with ⟨tm', sp⟩
        obtain ⟨f2, MCS2, MINJ2⟩ := match_callstack_function_entry BC REPRES hnr1 hnr2 hdisj hav hbp
          ARGS ALLOC MCS MINJ
        have HP : tf.fn_params = fn.fn_params := by rw [htf']
        have HV : tf.fn_vars = fn.fn_temps := by rw [htf']
        have HS : tf.fn_sig = fn.fn_sig := by rw [htf']
        have HB : tf.fn_body = tbody := by rw [htf']
        refine .inl ⟨_, plus_one (.internal_function _ _ _ _ _ _ _
            (by rw [HS]; exact Val.has_argtype_list_inject hty ARGS) ALLOC rfl), ?_⟩
        rw [HB, HV, HP]
        exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ [] _ _ _ _ _ TRF TB MINJ2 MCS2
          (match_cont_call_cenv cenv MK ISCC)
      · cases TR
  | external_function ef vargs k m t vres m' hec =>
    cases MS with
    | callstate _ _ _ _ tfd targs tk tm f cs cenv0 TR MINJ MCS MK ISCC ARGS =>
      simp only [translFundef, ASTFundef.transfPartial] at TR
      cases TR
      obtain ⟨f', tvres, tm', EC, VI, MINJ', INCR, MCS'⟩ :=
        external_call_correct TRANSL hext hasm hextp hasmp hec MINJ MCS ARGS
      exact .inl ⟨_, plus_one (.external_function _ _ _ _ _ _ _ EC),
        .returnstate _ _ _ _ _ _ _ _ _ MINJ' MCS' MK VI⟩
  | «return» v optid fn e le k m =>
    cases MS with
    | returnstate _ _ _ tv tk tm f cs cenv0 MINJ MCS MK VI =>
      cases MK with
      | Kcall _ _ _ _ _ tfn sp te tk' cenv xenv lo hi cs' sz _ TRF MK' =>
        have MCS' : MatchCallstack prog.globalenv f m tm
            (⟨cenv, tfn, e, Cminor.setOptvar optid v le, Cminor.setOptvar optid tv te, sp, lo, hi⟩ :: cs')
            m.nextblock tm.nextblock := by
          cases optid with
          | none => exact MCS
          | some id => exact match_callstack_set_temp VI MCS
        exact .inl ⟨_, plus_one (.return _ _ _ _ _ _ _),
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ xenv _ _ _ _ _ TRF (translStmt_skip _ _) MINJ MCS' MK'⟩

end TRANSLATION

/-! ## Initial and final states -/

/-- `Cminorgenproof.match_globalenvs_init` -/
theorem match_globalenvs_init {prog : Csharpminor.Program} {m : Mem} (h : prog.initMem = some m) :
    MatchGlobalenvs prog.globalenv (Mem.flatInj m.nextblock) m.nextblock where
  domain b hb := by simp [Mem.flatInj, hb]
  image b1 b2 delta h _ := by
    simp only [Mem.flatInj] at h
    split at h
    · cases h; rfl
    · cases h
  symbols id b hs := by
    have := Genv.findSymbol_not_fresh h hs
    simpa [Mem.validBlock] using this
  functions b fd hf := by
    have := Genv.findFunctPtr_not_fresh h hf
    simpa [Mem.validBlock] using this
  varinfos b gv hv := by
    have := Genv.findVarInfo_not_fresh h hv
    simpa [Mem.validBlock] using this

/-- `Cminorgenproof.transl_initial_states` -/
theorem transl_initial_states {prog : Csharpminor.Program} {tprog : Cminor.Program}
    (TRANSL : translProgram prog = .OK tprog) {S : Csharpminor.State}
    (h : Csharpminor.InitialState prog S) :
    ∃ R, Cminor.InitialState tprog R ∧ MatchStates prog.globalenv S R := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, A, B⟩ := function_ptr_translated TRANSL hf
    refine ⟨_, .intro b tf m0 ?_ ?_ A (by rw [sig_preserved B]; exact hsig),
      .callstate _ _ _ _ _ _ _ _ (Mem.flatInj m0.nextblock) [] PTree.empty B
        (Genv.initmem_inject hm)
        (.nil m0.nextblock _ _ (match_globalenvs_init hm) (Nat.le_refl _) (Nat.le_refl _))
        (.Kstop _ _) rfl .nil⟩
    · exact (init_mem_transf_partial TRANSL).trans hm
    · rw [(match_transform_partial_program TRANSL).main_eq, symbols_preserved TRANSL]
      exact hs

/-- `Cminorgenproof.transl_final_states` -/
theorem transl_final_states {ge : Csharpminor.CGenv} {S : Csharpminor.State} {R : Cminor.State}
    {r : Integers.Int} (hm : MatchStates ge S R) (h : Csharpminor.FinalState S r) :
    Cminor.FinalState R r := by
  cases h with
  | intro r m =>
    cases hm with
    | returnstate _ _ _ tv tk tm f cs cenv MINJ MCS MK VI =>
      cases MK
      cases VI
      exact .intro _ _

/-- `Cminorgenproof.transl_program_correct`: the translation from Csharpminor
    to Cminor preserves the semantics (forward simulation).

    * `hext` / `hasm`: external functions and inline assembly commute with
      memory injections (CompCert's `ec_mem_inject`);
    * `hextp` / `hasmp`: their memory properties (`ec_valid_block`,
      `ec_max_perm`, `ec_readonly`, `ec_trace_length`).

    CompCert takes both from the axioms `external_functions_properties` and
    `inline_assembly_properties`. -/
theorem transl_program_correct (prog : Csharpminor.Program) (tprog : Cminor.Program)
    (TRANSL : translProgram prog = .OK tprog)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Csharpminor.semantics prog) (Cminor.semantics tprog) :=
  forward_simulation_star (L1 := Csharpminor.semantics prog) (L2 := Cminor.semantics tprog)
    (MatchStates prog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved TRANSL])
    (fun _ h => transl_initial_states TRANSL h)
    (fun _ _ _ hm h => transl_final_states hm h)
    measure
    (fun _ _ _ hst _ hm => transl_step_correct TRANSL hext hasm hextp hasmp hst hm)

/-! ## Linking (`match_prog`, `transf_program_match`, `TransfCminorgenLink`) -/

/-- `Cminorgenproof.match_prog` -/
def MatchProgLink (p : Csharpminor.Program) (tp : Cminor.Program) : Prop :=
  Linking.MatchProgramCtx (fun _ f tf => translFundef f = .OK tf) Eq p tp

/-- `Cminorgenproof.transf_program_match` -/
theorem transf_program_match {p : Csharpminor.Program} {tp : Cminor.Program}
    (h : translProgram p = .OK tp) : MatchProgLink p tp :=
  Linking.match_transform_partial_program h

/-- `Cminorgenproof.TransfCminorgenLink` -/
instance transfCminorgenLink : Linking.TransfLink MatchProgLink :=
  Linking.transfPartialLinkAST _

/-- `Cminorgenproof.transl_program_correct`, stated for `match_prog`. -/
theorem transl_program_correct_match {p : Csharpminor.Program} {tp : Cminor.Program}
    (h : MatchProgLink p tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Csharpminor.semantics p) (Cminor.semantics tp) :=
  transl_program_correct p tp (Linking.transformPartialProgram_of_match h) hext hasm hextp hasmp

end Cminorgen
end CC
