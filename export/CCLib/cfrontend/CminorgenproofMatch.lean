/-
  Correctness of Cminor generation — port of `cfrontend/Cminorgenproof.v`,
  part 4: matching of continuations (`match_cont`) and of execution states
  (`match_states`), the properties of call continuations, the compilation of
  `switch` statements (`lbl_stmt_tail`, `switch_table_*`,
  `transl_lblstmt_cont`, `switch_descent`, `switch_ascent`,
  `switch_match_cont`, `switch_match_states`, `transl_lblstmt_suffix`) and the
  commutation between `find_label` and compilation (`transl_find_label`,
  `transl_lblstmt_find_label`, `transl_find_label_body`).
-/
import CCLib.cfrontend.CminorgenproofExpr

namespace CC
namespace Cminorgen

open Smallstep

/-! ## Matching of continuations and states -/

/-- `Cminorgenproof.match_cont` -/
inductive MatchCont : Csharpminor.Cont → Cminor.Cont → Compilenv → ExitEnv → Callstack → Prop where
  | Kstop (cenv xenv) : MatchCont .Kstop .Kstop cenv xenv []
  | Kseq (s k ts tk cenv xenv cs) :
      translStmt cenv xenv s = .OK ts → MatchCont k tk cenv xenv cs →
      MatchCont (.Kseq s k) (.Kseq ts tk) cenv xenv cs
  | Kseq2 (s1 s2 k ts1 tk cenv xenv cs) :
      translStmt cenv xenv s1 = .OK ts1 → MatchCont (.Kseq s2 k) tk cenv xenv cs →
      MatchCont (.Kseq (.Sseq s1 s2) k) (.Kseq ts1 tk) cenv xenv cs
  | Kblock (k tk cenv xenv cs) :
      MatchCont k tk cenv xenv cs → MatchCont (.Kblock k) (.Kblock tk) cenv (true :: xenv) cs
  | Kblock2 (k tk cenv xenv cs) :
      MatchCont k tk cenv xenv cs → MatchCont k (.Kblock tk) cenv (false :: xenv) cs
  | Kcall (optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv') :
      translFunbody cenv sz fn = .OK tfn → MatchCont k tk cenv xenv cs →
      MatchCont (.Kcall optid fn e le k) (.Kcall optid tfn (.Vptr sp Integers.Ptrofs.zero) te tk)
        cenv' [] (⟨cenv, tfn, e, le, te, sp, lo, hi⟩ :: cs)

/-- `Cminorgenproof.match_states` -/
inductive MatchStates (ge : Csharpminor.CGenv) : Csharpminor.State → Cminor.State → Prop where
  | state (fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz) :
      translFunbody cenv sz fn = .OK tfn →
      translStmt cenv xenv s = .OK ts →
      Mem.Inject f m tm →
      MatchCallstack ge f m tm (⟨cenv, tfn, e, le, te, sp, lo, hi⟩ :: cs) m.nextblock tm.nextblock →
      MatchCont k tk cenv xenv cs →
      MatchStates ge (.State fn s k e le m) (.State tfn ts tk (.Vptr sp Integers.Ptrofs.zero) te tm)
  | state_seq (fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz) :
      translFunbody cenv sz fn = .OK tfn →
      translStmt cenv xenv s1 = .OK ts1 →
      Mem.Inject f m tm →
      MatchCallstack ge f m tm (⟨cenv, tfn, e, le, te, sp, lo, hi⟩ :: cs) m.nextblock tm.nextblock →
      MatchCont (.Kseq s2 k) tk cenv xenv cs →
      MatchStates ge (.State fn (.Sseq s1 s2) k e le m)
        (.State tfn ts1 tk (.Vptr sp Integers.Ptrofs.zero) te tm)
  | callstate (fd args k m tfd targs tk tm f cs cenv) :
      translFundef fd = .OK tfd →
      Mem.Inject f m tm →
      MatchCallstack ge f m tm cs m.nextblock tm.nextblock →
      MatchCont k tk cenv [] cs →
      Csharpminor.isCallCont k = true →
      Val.InjectList f args targs →
      MatchStates ge (.Callstate fd args k m) (.Callstate tfd targs tk tm)
  | returnstate (v k m tv tk tm f cs cenv) :
      Mem.Inject f m tm →
      MatchCallstack ge f m tm cs m.nextblock tm.nextblock →
      MatchCont k tk cenv [] cs →
      Val.Inject f v tv →
      MatchStates ge (.Returnstate v k m) (.Returnstate tv tk tm)

/-- `Cminorgenproof.val_inject_function_pointer` -/
theorem val_inject_function_pointer {ge : Csharpminor.CGenv} {bound : Block} {v : Val}
    {fd : Csharpminor.Fundef} {f : Val.Meminj} {tv : Val} (hf : Genv.findFunct ge v = some fd)
    (MG : MatchGlobalenvs ge f bound) (hi : Val.Inject f v tv) : tv = v := by
  cases v with
  | Vptr b ofs =>
    simp only [Genv.findFunct] at hf
    split at hf
    · rename_i heq
      cases hi with
      | ptr delta hb ho =>
        rw [MG.domain b (MG.functions b fd hf)] at hb
        cases hb
        rw [ho, EventsInject.ptrofs_add_repr_zero]
    · cases hf
  | _ => simp [Genv.findFunct] at hf

/-- `Cminorgenproof.match_call_cont` -/
theorem match_call_cont {k : Csharpminor.Cont} {tk : Cminor.Cont} {cenv : Compilenv}
    {xenv : ExitEnv} {cs : Callstack} (h : MatchCont k tk cenv xenv cs) :
    MatchCont (Csharpminor.callCont k) (Cminor.callCont tk) cenv [] cs := by
  induction h with
  | Kstop => exact .Kstop _ _
  | Kseq _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kseq2 _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kblock _ _ _ _ _ _ ih => exact ih
  | Kblock2 _ _ _ _ _ _ ih => exact ih
  | Kcall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv' h1 h2 _ =>
    exact .Kcall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv' h1 h2

/-- `Cminorgenproof.match_is_call_cont` -/
theorem match_is_call_cont {tge : Cminor.CGenv} {tfn : Cminor.Function} {te : Cminor.Env}
    {sp : Val} {tm : Mem} {k : Csharpminor.Cont} {tk : Cminor.Cont} {cenv : Compilenv}
    {xenv : ExitEnv} {cs : Callstack} (h : MatchCont k tk cenv xenv cs)
    (hcc : Csharpminor.isCallCont k = true) :
    ∃ tk', Smallstep.Star (Cminor.Step tge) (Cminor.State.State tfn .Sskip tk sp te tm) E0 (Cminor.State.State tfn .Sskip tk' sp te tm) ∧
      Cminor.isCallCont tk' = true ∧ MatchCont k tk' cenv [] cs := by
  induction h with
  | Kstop cenv xenv => exact ⟨_, .refl _, rfl, .Kstop _ _⟩
  | Kseq => simp [Csharpminor.isCallCont] at hcc
  | Kseq2 => simp [Csharpminor.isCallCont] at hcc
  | Kblock => simp [Csharpminor.isCallCont] at hcc
  | Kblock2 k tk cenv xenv cs _ ih =>
    obtain ⟨tk', A, B, C⟩ := ih hcc
    exact ⟨tk', star_left (Cminor.Step.skip_block _ _ _ _ _) A rfl, B, C⟩
  | Kcall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv' h1 h2 _ =>
    exact ⟨_, .refl _, rfl, .Kcall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv' h1 h2⟩

/-! ## Properties of `switch` compilation -/

/-- `Cminorgenproof.lbl_stmt_tail` -/
inductive LblStmtTail : Csharpminor.LblStmt → Nat → Csharpminor.LblStmt → Prop where
  | O (sl) : LblStmtTail sl 0 sl
  | S (c s sl n sl') : LblStmtTail sl n sl' → LblStmtTail (.LScons c s sl) (n + 1) sl'

/-- `Cminorgenproof.switch_table_default` -/
theorem switch_table_default : ∀ (sl : Csharpminor.LblStmt) (base : Nat),
    ∃ n, LblStmtTail sl n (Csharpminor.selectSwitchDefault sl) ∧ (switchTable sl base).2 = n + base
  | .LSnil, base => ⟨0, .O _, by simp [switchTable]⟩
  | .LScons none s sl, base => ⟨0, .O _, by simp [switchTable]⟩
  | .LScons (some z) s sl, base => by
    obtain ⟨n, P, Q⟩ := switch_table_default sl (base + 1)
    refine ⟨n + 1, .S _ _ _ _ _ P, ?_⟩
    simp only [switchTable]
    rw [Q]; omega

/-- `Cminorgenproof.switch_table_case` -/
theorem switch_table_case (i : Z) : ∀ (sl : Csharpminor.LblStmt) (base dfl : Nat),
    match Csharpminor.selectSwitchCase i sl with
    | none => Switch.switchTarget i dfl (switchTable sl base).1 = dfl
    | some sl' => ∃ n, LblStmtTail sl n sl' ∧
        Switch.switchTarget i dfl (switchTable sl base).1 = n + base
  | .LSnil, base, dfl => by simp [Csharpminor.selectSwitchCase, switchTable, Switch.switchTarget]
  | .LScons o s sl, base, dfl => by
    have IH := switch_table_case i sl (base + 1) dfl
    cases o with
    | none =>
      simp only [Csharpminor.selectSwitchCase, switchTable]
      revert IH
      cases Csharpminor.selectSwitchCase i sl with
      | none => exact id
      | some sl' =>
        intro ⟨x, P, Q⟩
        exact ⟨x + 1, .S _ _ _ _ _ P, by rw [Q]; omega⟩
    | some z =>
      simp only [Csharpminor.selectSwitchCase, switchTable]
      by_cases hz : z = i
      · subst hz
        simp only [if_true]
        exact ⟨0, .O _, by simp [Switch.switchTarget]⟩
      · simp only [hz, if_false]
        have hz' : ¬ (i = z) := fun h => hz h.symm
        simp only [Switch.switchTarget, hz', if_false]
        revert IH
        cases Csharpminor.selectSwitchCase i sl with
        | none => exact id
        | some sl' =>
          intro ⟨x, P, Q⟩
          exact ⟨x + 1, .S _ _ _ _ _ P, by rw [Q]; omega⟩

/-- `Cminorgenproof.switch_table_select` -/
theorem switch_table_select (i : Z) (sl : Csharpminor.LblStmt) :
    LblStmtTail sl (Switch.switchTarget i (switchTable sl 0).2 (switchTable sl 0).1)
      (Csharpminor.selectSwitch i sl) := by
  have := switch_table_case i sl 0 (switchTable sl 0).2
  unfold Csharpminor.selectSwitch
  revert this
  cases Csharpminor.selectSwitchCase i sl with
  | some sl' =>
    intro ⟨n, P, Q⟩
    rw [Q]; exact P
  | none =>
    intro E
    rw [E]
    obtain ⟨n, P, Q⟩ := switch_table_default sl 0
    rw [Q]; exact P

/-- `Cminorgenproof.transl_lblstmt_cont` -/
inductive TranslLblstmtCont (cenv : Compilenv) (xenv : ExitEnv) :
    Csharpminor.LblStmt → Cminor.Cont → Cminor.Cont → Prop where
  | default (k) : TranslLblstmtCont cenv xenv .LSnil k (.Kblock (.Kseq .Sskip k))
  | case (i s ls k ts k') :
      translStmt cenv (switchEnv (.LScons i s ls) xenv) s = .OK ts →
      TranslLblstmtCont cenv xenv ls k k' →
      TranslLblstmtCont cenv xenv (.LScons i s ls) k (.Kblock (.Kseq ts k'))

theorem translLblstmt_nil (cenv : Compilenv) (xenv : ExitEnv) (body : Cminor.Stmt) :
    translLblstmt cenv xenv .LSnil body = .OK (.Sseq (.Sblock body) .Sskip) := by
  simp [translLblstmt]

theorem translLblstmt_cons {cenv : Compilenv} {xenv : ExitEnv} {c : Option Z}
    {s : Csharpminor.Stmt} {ls : Csharpminor.LblStmt} {body ts : Cminor.Stmt}
    (h : translLblstmt cenv xenv (.LScons c s ls) body = .OK ts) :
    ∃ ts1, translStmt cenv xenv s = .OK ts1 ∧
      translLblstmt cenv xenv.tail ls (.Sseq (.Sblock body) ts1) = .OK ts := by
  simp only [translLblstmt, Cshmgen.res_bind_eq_OK] at h
  exact h

theorem translStmt_skip (cenv : Compilenv) (xenv : ExitEnv) :
    translStmt cenv xenv .Sskip = .OK .Sskip := by
  simp [translStmt]

/-- The continuation part of `Cminorgenproof.switch_descent`. -/
theorem switch_descent_cont {cenv : Compilenv} {xenv : ExitEnv} {k : Cminor.Cont} :
    ∀ {ls : Csharpminor.LblStmt} {body s : Cminor.Stmt},
    translLblstmt cenv (switchEnv ls xenv) ls body = .OK s →
    ∃ k', TranslLblstmtCont cenv xenv ls k k'
  | .LSnil, _, _, _ => ⟨_, .default _⟩
  | .LScons i s1 ls, body, s, h => by
    obtain ⟨ts, A, B⟩ := translLblstmt_cons h
    obtain ⟨k', P⟩ := switch_descent_cont (k := k) B
    exact ⟨_, .case _ _ _ _ _ _ A P⟩

/-- `Cminorgenproof.switch_descent` -/
theorem switch_descent {tge : Cminor.CGenv} {cenv : Compilenv} {xenv : ExitEnv}
    {k : Cminor.Cont} : ∀ {ls : Csharpminor.LblStmt} {body s : Cminor.Stmt},
    translLblstmt cenv (switchEnv ls xenv) ls body = .OK s →
    ∃ k', TranslLblstmtCont cenv xenv ls k k' ∧
      ∀ f sp e m, Smallstep.Plus (Cminor.Step tge) (Cminor.State.State f s k sp e m) E0 (Cminor.State.State f body k' sp e m)
  | .LSnil, body, s, h => by
    rw [translLblstmt_nil] at h; cases h
    exact ⟨_, .default _, fun f sp e m =>
      plus_left (.seq _ _ _ _ _ _ _) (star_one (.block _ _ _ _ _ _)) rfl⟩
  | .LScons i s1 ls, body, s, h => by
    obtain ⟨ts, A, B⟩ := translLblstmt_cons h
    obtain ⟨k', P, Q⟩ := switch_descent (k := k) B
    exact ⟨_, .case _ _ _ _ _ _ A P, fun f sp e m =>
      plus_star_trans (Q f sp e m) (star_left (.seq _ _ _ _ _ _ _)
        (star_one (.block _ _ _ _ _ _)) rfl) rfl⟩

/-- `Cminorgenproof.switch_ascent` -/
theorem switch_ascent {tge : Cminor.CGenv} {f : Cminor.Function} {sp : Val} {e : Cminor.Env}
    {m : Mem} {cenv : Compilenv} {xenv : ExitEnv} {ls : Csharpminor.LblStmt} {n : Nat}
    {ls' : Csharpminor.LblStmt} (h : LblStmtTail ls n ls') :
    ∀ {k k1}, TranslLblstmtCont cenv xenv ls k k1 →
    ∃ k2, Smallstep.Star (Cminor.Step tge) (Cminor.State.State f (.Sexit n) k1 sp e m) E0 (Cminor.State.State f (.Sexit 0) k2 sp e m) ∧
      TranslLblstmtCont cenv xenv ls' k k2 := by
  induction h with
  | O sl => intro k k1 h; exact ⟨k1, .refl _, h⟩
  | S c s sl n sl' _ ih =>
    intro k k1 h
    cases h with
    | case _ _ _ _ ts k' _ h2 =>
      obtain ⟨k2, P, Q⟩ := ih h2
      exact ⟨k2, star_left (.exit_block_S _ _ _ _ _ _) (star_left (.exit_seq _ _ _ _ _ _ _) P rfl) rfl, Q⟩

/-- `Cminorgenproof.switch_match_cont` -/
theorem switch_match_cont {cenv : Compilenv} {xenv : ExitEnv} {k : Csharpminor.Cont}
    {cs : Callstack} {tk : Cminor.Cont} : ∀ {ls : Csharpminor.LblStmt} {tk' : Cminor.Cont},
    MatchCont k tk cenv xenv cs → TranslLblstmtCont cenv xenv ls tk tk' →
    MatchCont (.Kseq (Csharpminor.seqOfLblStmt ls) k) tk' cenv (false :: switchEnv ls xenv) cs
  | .LSnil, _, MK, h => by
    cases h
    exact .Kblock2 _ _ _ _ _ (.Kseq _ _ _ _ _ _ _ (translStmt_skip _ _) MK)
  | .LScons i s ls, _, MK, h => by
    cases h with
    | case _ _ _ _ ts k' h1 h2 =>
      exact .Kblock2 _ _ _ _ _ (.Kseq2 _ _ _ _ _ _ _ _ h1 (switch_match_cont MK h2))

/-- `Cminorgenproof.switch_match_states` -/
theorem switch_match_states {ge : Csharpminor.CGenv} {tge : Cminor.CGenv}
    {fn : Csharpminor.Function} {k : Csharpminor.Cont} {e : Csharpminor.Env}
    {le : Csharpminor.TempEnv} {m : Mem} {tfn : Cminor.Function} {ts : Cminor.Stmt}
    {tk : Cminor.Cont} {sp : Block} {te : Cminor.Env} {tm : Mem} {cenv : Compilenv}
    {xenv : ExitEnv} {f : Val.Meminj} {lo hi : Block} {cs : Callstack} {sz : Z}
    {ls : Csharpminor.LblStmt} {body : Cminor.Stmt} {tk' : Cminor.Cont}
    (TRF : translFunbody cenv sz fn = .OK tfn)
    (TR : translLblstmt cenv (switchEnv ls xenv) ls body = .OK ts)
    (MINJ : Mem.Inject f m tm)
    (MCS : MatchCallstack ge f m tm (⟨cenv, tfn, e, le, te, sp, lo, hi⟩ :: cs) m.nextblock tm.nextblock)
    (MK : MatchCont k tk cenv xenv cs) (TK : TranslLblstmtCont cenv xenv ls tk tk') :
    ∃ S, Smallstep.Plus (Cminor.Step tge) (Cminor.State.State tfn (.Sexit 0) tk' (.Vptr sp Integers.Ptrofs.zero) te tm) E0 S ∧
      MatchStates ge (.State fn (Csharpminor.seqOfLblStmt ls) k e le m) S := by
  cases TK with
  | default =>
    exact ⟨_, plus_left (.exit_block_0 _ _ _ _ _) (star_one (.skip_seq _ _ _ _ _ _)) rfl,
      .state _ _ _ _ _ _ _ _ _ _ _ _ _ xenv _ _ _ _ _ TRF (translStmt_skip _ _) MINJ MCS MK⟩
  | case i s ls k ts' k' h1 h2 =>
    exact ⟨_, plus_left (.exit_block_0 _ _ _ _ _) (star_one (.skip_seq _ _ _ _ _ _)) rfl,
      .state_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF h1 MINJ MCS
        (switch_match_cont MK h2)⟩

/-- `Cminorgenproof.transl_lblstmt_suffix` -/
theorem transl_lblstmt_suffix {cenv : Compilenv} {xenv : ExitEnv} {ls : Csharpminor.LblStmt}
    {n : Nat} {ls' : Csharpminor.LblStmt} (h : LblStmtTail ls n ls') :
    ∀ {body ts}, translLblstmt cenv (switchEnv ls xenv) ls body = .OK ts →
    ∃ body' ts', translLblstmt cenv (switchEnv ls' xenv) ls' body' = .OK ts' := by
  induction h with
  | O sl => intro body ts h; exact ⟨body, ts, h⟩
  | S c s sl n sl' _ ih =>
    intro body ts h
    obtain ⟨ts1, _, B⟩ := translLblstmt_cons h
    exact ih B

/-! ## Commutation between `find_label` and compilation -/

section FIND_LABEL
variable (lbl : Csharpminor.Label) (cenv : Compilenv) (cs : Callstack)

/-- `Cminorgenproof.transl_lblstmt_find_label_context` -/
theorem transl_lblstmt_find_label_context {xenv : ExitEnv} : ∀ {ls : Csharpminor.LblStmt}
    {body ts : Cminor.Stmt} {tk1 tk2 : Cminor.Cont} {ts' : Cminor.Stmt} {tk' : Cminor.Cont},
    translLblstmt cenv (switchEnv ls xenv) ls body = .OK ts →
    TranslLblstmtCont cenv xenv ls tk1 tk2 →
    Cminor.findLabel lbl body tk2 = some (ts', tk') →
    Cminor.findLabel lbl ts tk1 = some (ts', tk')
  | .LSnil, body, ts, tk1, tk2, ts', tk', h, ht, hf => by
    rw [translLblstmt_nil] at h; cases h
    cases ht
    simp only [Cminor.findLabel, hf]
  | .LScons i s ls, body, ts, tk1, tk2, ts', tk', h, ht, hf => by
    obtain ⟨ts1, A, B⟩ := translLblstmt_cons h
    cases ht with
    | case _ _ _ _ ts0 k' h1 h2 =>
      rw [A] at h1; cases h1
      refine transl_lblstmt_find_label_context B h2 ?_
      simp only [Cminor.findLabel, hf]

mutual
/-- `Cminorgenproof.transl_find_label` -/
theorem transl_find_label : ∀ (s : Csharpminor.Stmt) (k : Csharpminor.Cont) (xenv : ExitEnv)
    (ts : Cminor.Stmt) (tk : Cminor.Cont),
    translStmt cenv xenv s = .OK ts → MatchCont k tk cenv xenv cs →
    match Csharpminor.findLabel lbl s k with
    | none => Cminor.findLabel lbl ts tk = none
    | some (s', k') => ∃ ts' tk' xenv', Cminor.findLabel lbl ts tk = some (ts', tk') ∧
        translStmt cenv xenv' s' = .OK ts' ∧ MatchCont k' tk' cenv xenv' cs
  | .Sskip, k, xenv, ts, tk, h, _ => by simp only [translStmt] at h; cases h; rfl
  | .Sset id a, k, xenv, ts, tk, h, _ => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, h⟩ := h; cases h; rfl
  | .Sstore chunk a1 a2, k, xenv, ts, tk, h, _ => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h; rfl
  | .Scall optid sig a al, k, xenv, ts, tk, h, _ => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h; rfl
  | .Sbuiltin optid ef al, k, xenv, ts, tk, h, _ => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, h⟩ := h; cases h; rfl
  | .Sseq s1 s2, k, xenv, ts, tk, h, MK => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts1, h1, ts2, h2, h⟩ := h; cases h
    have IH1 := transl_find_label s1 (.Kseq s2 k) xenv ts1 (.Kseq ts2 tk) h1 (.Kseq _ _ _ _ _ _ _ h2 MK)
    simp only [Csharpminor.findLabel, Cminor.findLabel]
    revert IH1
    cases Csharpminor.findLabel lbl s1 (.Kseq s2 k) with
    | some p =>
      obtain ⟨s', k'⟩ := p
      intro ⟨ts', tk', xenv', A, B, C⟩
      exact ⟨ts', tk', xenv', by rw [A], B, C⟩
    | none =>
      intro A
      rw [A]
      exact transl_find_label s2 k xenv ts2 tk h2 MK
  | .Sifthenelse a s1 s2, k, xenv, ts, tk, h, MK => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, ts1, h1, ts2, h2, h⟩ := h; cases h
    have IH1 := transl_find_label s1 k xenv ts1 tk h1 MK
    simp only [Csharpminor.findLabel, Cminor.findLabel]
    revert IH1
    cases Csharpminor.findLabel lbl s1 k with
    | some p =>
      obtain ⟨s', k'⟩ := p
      intro ⟨ts', tk', xenv', A, B, C⟩
      exact ⟨ts', tk', xenv', by rw [A], B, C⟩
    | none =>
      intro A
      rw [A]
      exact transl_find_label s2 k xenv ts2 tk h2 MK
  | .Sloop s, k, xenv, ts, tk, h, MK => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts1, h1, h⟩ := h; cases h
    simp only [Csharpminor.findLabel, Cminor.findLabel]
    exact transl_find_label s _ xenv ts1 _ h1
      (.Kseq _ _ _ _ _ _ _ (by simp only [translStmt, h1]; rfl) MK)
  | .Sblock s, k, xenv, ts, tk, h, MK => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts1, h1, h⟩ := h; cases h
    simp only [Csharpminor.findLabel, Cminor.findLabel]
    exact transl_find_label s _ (true :: xenv) ts1 _ h1 (.Kblock _ _ _ _ _ MK)
  | .Sexit n, k, xenv, ts, tk, h, _ => by simp only [translStmt] at h; cases h; rfl
  | .Sswitch long a ls, k, xenv, ts, tk, h, MK => by
    simp only [translStmt] at h
    rcases hst : switchTable ls 0 with ⟨tbl, dfl⟩
    rw [hst] at h
    simp only [Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ta, _, h⟩ := h
    obtain ⟨k', A⟩ := switch_descent_cont (k := tk) h
    simp only [Csharpminor.findLabel]
    exact transl_lblstmt_find_label ls xenv _ k ts tk k' h MK A rfl
  | .Sreturn none, k, xenv, ts, tk, h, _ => by simp only [translStmt] at h; cases h; rfl
  | .Sreturn (some a), k, xenv, ts, tk, h, _ => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, h⟩ := h; cases h; rfl
  | .Slabel l s, k, xenv, ts, tk, h, MK => by
    simp only [translStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts1, h1, h⟩ := h; cases h
    simp only [Csharpminor.findLabel, Cminor.findLabel]
    by_cases hl : lbl = l
    · simp only [hl, if_true]
      exact ⟨ts1, tk, xenv, rfl, h1, MK⟩
    · simp only [hl, if_false]
      exact transl_find_label s k xenv ts1 tk h1 MK
  | .Sgoto l, k, xenv, ts, tk, h, _ => by simp only [translStmt] at h; cases h; rfl

/-- `Cminorgenproof.transl_lblstmt_find_label` -/
theorem transl_lblstmt_find_label : ∀ (ls : Csharpminor.LblStmt) (xenv : ExitEnv)
    (body : Cminor.Stmt) (k : Csharpminor.Cont) (ts : Cminor.Stmt) (tk tk1 : Cminor.Cont),
    translLblstmt cenv (switchEnv ls xenv) ls body = .OK ts →
    MatchCont k tk cenv xenv cs →
    TranslLblstmtCont cenv xenv ls tk tk1 →
    Cminor.findLabel lbl body tk1 = none →
    match Csharpminor.findLabelLs lbl ls k with
    | none => Cminor.findLabel lbl ts tk = none
    | some (s', k') => ∃ ts' tk' xenv', Cminor.findLabel lbl ts tk = some (ts', tk') ∧
        translStmt cenv xenv' s' = .OK ts' ∧ MatchCont k' tk' cenv xenv' cs
  | .LSnil, xenv, body, k, ts, tk, tk1, h, _, ht, hf => by
    rw [translLblstmt_nil] at h; cases h
    cases ht
    simp only [Csharpminor.findLabelLs, Cminor.findLabel, hf]
  | .LScons i s ls, xenv, body, k, ts, tk, tk1, h, MK, ht, hf => by
    obtain ⟨ts1, A, B⟩ := translLblstmt_cons h
    cases ht with
    | case _ _ _ _ ts0 k' h1 h2 =>
      rw [A] at h1; cases h1
      have IH := transl_find_label s (.Kseq (Csharpminor.seqOfLblStmt ls) k)
        (switchEnv (.LScons i s ls) xenv) ts1 k' A (switch_match_cont MK h2)
      simp only [Csharpminor.findLabelLs]
      revert IH
      cases Csharpminor.findLabel lbl s (.Kseq (Csharpminor.seqOfLblStmt ls) k) with
      | some p =>
        obtain ⟨s', k''⟩ := p
        intro ⟨ts', tk', xenv', P, Q, R⟩
        refine ⟨ts', tk', xenv', ?_, Q, R⟩
        refine transl_lblstmt_find_label_context lbl cenv B h2 ?_
        simp only [Cminor.findLabel, hf, P]
      | none =>
        intro P
        refine transl_lblstmt_find_label ls xenv _ k ts tk k' B MK h2 ?_
        simp only [Cminor.findLabel, hf, P]
end

end FIND_LABEL

/-- `Cminorgenproof.transl_find_label_body` -/
theorem transl_find_label_body {cenv : Compilenv} {xenv : ExitEnv} {size : Z}
    {f : Csharpminor.Function} {tf : Cminor.Function} {k : Csharpminor.Cont} {tk : Cminor.Cont}
    {cs : Callstack} {lbl : Csharpminor.Label} {s' : Csharpminor.Stmt} {k' : Csharpminor.Cont}
    (TRF : translFunbody cenv size f = .OK tf) (MK : MatchCont k tk cenv xenv cs)
    (hf : Csharpminor.findLabel lbl f.fn_body (Csharpminor.callCont k) = some (s', k')) :
    ∃ ts' tk' xenv', Cminor.findLabel lbl tf.fn_body (Cminor.callCont tk) = some (ts', tk') ∧
      translStmt cenv xenv' s' = .OK ts' ∧ MatchCont k' tk' cenv xenv' cs := by
  simp only [translFunbody, Cshmgen.res_bind_eq_OK] at TRF
  obtain ⟨tbody, h1, h⟩ := TRF; cases h
  have := transl_find_label lbl cenv cs f.fn_body _ [] tbody _ h1 (match_call_cont MK)
  rw [hf] at this
  exact this

end Cminorgen
end CC
