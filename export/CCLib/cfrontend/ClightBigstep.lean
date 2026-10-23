/-
  A big-step semantics for Clight — port of `cfrontend/ClightBigstep.v`.

  * `ExecStmt` / `EvalFuncall` : terminating executions of statements and
    function calls (Rocq: `exec_stmt` / `eval_funcall`, mutually inductive);
  * `ExecinfStmt` / `EvalinfFuncall` : diverging executions (Rocq:
    `execinf_stmt` / `evalinf_funcall`, mutually *coinductive*; here Lean
    `coinductive` predicates);
  * `bigstepSemantics p` and `bigstep_semantics_sound` : every big-step
    execution is matched by a run of the small-step semantics
    (`Clight1.bigstep_semantics_sound`, `Clight2.bigstep_semantics_sound`).

  As in Rocq, everything is parameterised over the `function_entry` predicate
  (`FE`), so that both calling conventions share one development.  Rocq's
  `semantics_fe` is not needed: the step relation `Step ge (FE ge)` is used
  directly, and `semantics1`/`semantics2` are its instances.
-/
import CCLib.common.Bigstep
import CCLib.cfrontend.ClightBehaviors

namespace CC
namespace ClightBigstep

open Smallstep

/-! ## Outcomes -/

/-- `ClightBigstep.outcome`: how the execution of a statement terminated. -/
inductive Outcome where
  /-- terminated by `break` -/
  | Out_break
  /-- terminated by `continue` -/
  | Out_continue
  /-- terminated normally -/
  | Out_normal
  /-- terminated by `return` -/
  | Out_return (ov : Option (Val × Ty))

open Outcome

/-- `ClightBigstep.out_normal_or_continue` -/
inductive OutNormalOrContinue : Outcome → Prop where
  | N : OutNormalOrContinue Out_normal
  | C : OutNormalOrContinue Out_continue

/-- `ClightBigstep.out_break_or_return` -/
inductive OutBreakOrReturn : Outcome → Outcome → Prop where
  | B : OutBreakOrReturn Out_break Out_normal
  | R (ov : Option (Val × Ty)) : OutBreakOrReturn (Out_return ov) (Out_return ov)

/-- `ClightBigstep.outcome_switch` -/
def outcomeSwitch : Outcome → Outcome
  | Out_break => Out_normal
  | o => o

/-- `ClightBigstep.outcome_result_value` -/
def outcomeResultValue : Outcome → Ty → Val → Mem → Prop
  | Out_normal, .Tvoid, v, _ => v = .Vundef
  | Out_return none, .Tvoid, v, _ => v = .Vundef
  | Out_return (some (v', t')), ty, v, m => ty ≠ .Tvoid ∧ Cop.semCast v' t' ty m = some v
  | _, _, _, _ => False

/-! ## Terminating executions -/

section BIGSTEP

variable (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop) (ge : CGenv)

mutual
/-- `ClightBigstep.exec_stmt`: `ExecStmt FE ge e le m s t le' m' out` — executing
    `s` from temporaries `le` and memory `m` terminates with outcome `out`,
    temporaries `le'` and memory `m'`, emitting the trace `t`. -/
inductive ExecStmt : Env → TempEnv → Mem → Stmt → Trace → TempEnv → Mem → Outcome → Prop where
  | exec_Sskip (e le m) : ExecStmt e le m .Sskip E0 le m Out_normal
  | exec_Sassign (e le m a1 a2 loc ofs bf v2 v m') :
      EvalLvalue ge e le m a1 loc ofs bf →
      EvalExpr ge e le m a2 v2 →
      Cop.semCast v2 (typeof a2) (typeof a1) m = some v →
      AssignLoc ge.genv_cenv (typeof a1) m loc ofs bf v m' →
      ExecStmt e le m (.Sassign a1 a2) E0 le m' Out_normal
  | exec_Sset (e le m id a v) :
      EvalExpr ge e le m a v →
      ExecStmt e le m (.Sset id a) E0 (le.set id v) m Out_normal
  | exec_Scall (e le m optid a al tyargs tyres cconv vf vargs f t m' vres) :
      Cop.classifyFun (typeof a) = .f tyargs tyres cconv →
      EvalExpr ge e le m a vf →
      EvalExprlist ge e le m al tyargs vargs →
      Genv.findFunct ge.genv_genv vf = some f →
      typeOfFundef f = .Tfunction tyargs tyres cconv →
      EvalFuncall m f vargs t m' vres →
      ExecStmt e le m (.Scall optid a al) t (setOpttemp optid vres le) m' Out_normal
  | exec_Sbuiltin (e le m optid ef al tyargs vargs t m' vres) :
      EvalExprlist ge e le m al tyargs vargs →
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      ExecStmt e le m (.Sbuiltin optid ef tyargs al) t (setOpttemp optid vres le) m' Out_normal
  | exec_Sseq_1 (e le m s1 s2 t1 le1 m1 t2 le2 m2 out) :
      ExecStmt e le m s1 t1 le1 m1 Out_normal →
      ExecStmt e le1 m1 s2 t2 le2 m2 out →
      ExecStmt e le m (.Ssequence s1 s2) (Eapp t1 t2) le2 m2 out
  | exec_Sseq_2 (e le m s1 s2 t1 le1 m1 out) :
      ExecStmt e le m s1 t1 le1 m1 out →
      out ≠ Out_normal →
      ExecStmt e le m (.Ssequence s1 s2) t1 le1 m1 out
  | exec_Sifthenelse (e le m a s1 s2 v1 b t le' m' out) :
      EvalExpr ge e le m a v1 →
      Cop.boolVal v1 (typeof a) m = some b →
      ExecStmt e le m (if b then s1 else s2) t le' m' out →
      ExecStmt e le m (.Sifthenelse a s1 s2) t le' m' out
  | exec_Sreturn_none (e le m) :
      ExecStmt e le m (.Sreturn none) E0 le m (Out_return none)
  | exec_Sreturn_some (e le m a v) :
      EvalExpr ge e le m a v →
      ExecStmt e le m (.Sreturn (some a)) E0 le m (Out_return (some (v, typeof a)))
  | exec_Sbreak (e le m) : ExecStmt e le m .Sbreak E0 le m Out_break
  | exec_Scontinue (e le m) : ExecStmt e le m .Scontinue E0 le m Out_continue
  | exec_Sloop_stop1 (e le m s1 s2 t le' m' out' out) :
      ExecStmt e le m s1 t le' m' out' →
      OutBreakOrReturn out' out →
      ExecStmt e le m (.Sloop s1 s2) t le' m' out
  | exec_Sloop_stop2 (e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out) :
      ExecStmt e le m s1 t1 le1 m1 out1 →
      OutNormalOrContinue out1 →
      ExecStmt e le1 m1 s2 t2 le2 m2 out2 →
      OutBreakOrReturn out2 out →
      ExecStmt e le m (.Sloop s1 s2) (Eapp t1 t2) le2 m2 out
  | exec_Sloop_loop (e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out) :
      ExecStmt e le m s1 t1 le1 m1 out1 →
      OutNormalOrContinue out1 →
      ExecStmt e le1 m1 s2 t2 le2 m2 Out_normal →
      ExecStmt e le2 m2 (.Sloop s1 s2) t3 le3 m3 out →
      ExecStmt e le m (.Sloop s1 s2) (Eapp t1 (Eapp t2 t3)) le3 m3 out
  | exec_Sswitch (e le m a t v n sl le1 m1 out) :
      EvalExpr ge e le m a v →
      Cop.semSwitchArg v (typeof a) = some n →
      ExecStmt e le m (seqOfLabeledStatement (selectSwitch n sl)) t le1 m1 out →
      ExecStmt e le m (.Sswitch a sl) t le1 m1 (outcomeSwitch out)

/-- `ClightBigstep.eval_funcall`: `EvalFuncall FE ge m fd args t m' res` — calling
    `fd` on `args` in memory `m` returns `res` in memory `m'`, emitting `t`. -/
inductive EvalFuncall : Mem → FunDef → List Val → Trace → Mem → Val → Prop where
  | eval_funcall_internal (m f vargs t e le1 le2 m1 m2 out vres m3) :
      FE ge f vargs m e le1 m1 →
      ExecStmt e le1 m1 f.fn_body t le2 m2 out →
      outcomeResultValue out f.fn_return vres m2 →
      Mem.freeList m2 (blocksOfEnv ge.genv_cenv e) = some m3 →
      EvalFuncall m (.Internal f) vargs t m3 vres
  | eval_funcall_external (m ef targs tres cconv vargs t vres m') :
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      EvalFuncall m (.External ef targs tres cconv) vargs t m' vres
end

/-! ## Diverging executions -/

mutual
/-- `ClightBigstep.execinf_stmt`: the execution of the statement diverges, with
    (possibly infinite) trace `T`. -/
coinductive ExecinfStmt : Env → TempEnv → Mem → Stmt → Traceinf → Prop where
  | execinf_Scall (e le m optid a al vf tyargs tyres cconv vargs f T) :
      Cop.classifyFun (typeof a) = .f tyargs tyres cconv →
      EvalExpr ge e le m a vf →
      EvalExprlist ge e le m al tyargs vargs →
      Genv.findFunct ge.genv_genv vf = some f →
      typeOfFundef f = .Tfunction tyargs tyres cconv →
      EvalinfFuncall m f vargs T →
      ExecinfStmt e le m (.Scall optid a al) T
  | execinf_Sseq_1 (e le m s1 s2 T) :
      ExecinfStmt e le m s1 T →
      ExecinfStmt e le m (.Ssequence s1 s2) T
  | execinf_Sseq_2 (e le m s1 s2 t1 le1 m1 T2) :
      ExecStmt FE ge e le m s1 t1 le1 m1 Out_normal →
      ExecinfStmt e le1 m1 s2 T2 →
      ExecinfStmt e le m (.Ssequence s1 s2) (Eappinf t1 T2)
  | execinf_Sifthenelse (e le m a s1 s2 v1 b T) :
      EvalExpr ge e le m a v1 →
      Cop.boolVal v1 (typeof a) m = some b →
      ExecinfStmt e le m (if b then s1 else s2) T →
      ExecinfStmt e le m (.Sifthenelse a s1 s2) T
  | execinf_Sloop_body1 (e le m s1 s2 T) :
      ExecinfStmt e le m s1 T →
      ExecinfStmt e le m (.Sloop s1 s2) T
  | execinf_Sloop_body2 (e le m s1 s2 t1 le1 m1 out1 T2) :
      ExecStmt FE ge e le m s1 t1 le1 m1 out1 →
      OutNormalOrContinue out1 →
      ExecinfStmt e le1 m1 s2 T2 →
      ExecinfStmt e le m (.Sloop s1 s2) (Eappinf t1 T2)
  | execinf_Sloop_loop (e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 T3) :
      ExecStmt FE ge e le m s1 t1 le1 m1 out1 →
      OutNormalOrContinue out1 →
      ExecStmt FE ge e le1 m1 s2 t2 le2 m2 Out_normal →
      ExecinfStmt e le2 m2 (.Sloop s1 s2) T3 →
      ExecinfStmt e le m (.Sloop s1 s2) (Eappinf t1 (Eappinf t2 T3))
  | execinf_Sswitch (e le m a T v n sl) :
      EvalExpr ge e le m a v →
      Cop.semSwitchArg v (typeof a) = some n →
      ExecinfStmt e le m (seqOfLabeledStatement (selectSwitch n sl)) T →
      ExecinfStmt e le m (.Sswitch a sl) T

/-- `ClightBigstep.evalinf_funcall`: the call diverges with trace `T`. -/
coinductive EvalinfFuncall : Mem → FunDef → List Val → Traceinf → Prop where
  | evalinf_funcall_internal (m f vargs T e m1 le1) :
      FE ge f vargs m e le1 m1 →
      ExecinfStmt e le1 m1 f.fn_body T →
      EvalinfFuncall m (.Internal f) vargs T
end

end BIGSTEP

/-! ## Whole programs -/

/-- `ClightBigstep.bigstep_program_terminates` -/
inductive BigstepProgramTerminates
    (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop) (p : Program) :
    Trace → Integers.Int → Prop where
  | intro (b f m0 m1 t r) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv.genv_genv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv.genv_genv b = some f →
      typeOfFundef f = .Tfunction [] type_int32s cc_default →
      EvalFuncall FE p.globalenv m0 f [] t m1 (.Vint r) →
      BigstepProgramTerminates FE p t r

/-- `ClightBigstep.bigstep_program_diverges` -/
inductive BigstepProgramDiverges
    (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop) (p : Program) :
    Traceinf → Prop where
  | intro (b f m0 T) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv.genv_genv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv.genv_genv b = some f →
      typeOfFundef f = .Tfunction [] type_int32s cc_default →
      EvalinfFuncall FE p.globalenv m0 f [] T →
      BigstepProgramDiverges FE p T

/-- `ClightBigstep.bigstep_semantics` -/
def bigstepSemantics (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop)
    (p : Program) : BigstepSemantics :=
  ⟨BigstepProgramTerminates FE p, BigstepProgramDiverges FE p⟩

/-! ## From big-step to small-step -/

section BIGSTEP_TO_TRANSITIONS

variable {FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop} {ge : CGenv}

/-- `ClightBigstep.outcome_state_match`: the small-step state reached after
    executing a statement with the given outcome. -/
inductive OutcomeStateMatch (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) (f : Function)
    (k : Cont) : Outcome → State → Prop where
  | osm_normal : OutcomeStateMatch ge e le m f k Out_normal (.State f .Sskip k e le m)
  | osm_break : OutcomeStateMatch ge e le m f k Out_break (.State f .Sbreak k e le m)
  | osm_continue : OutcomeStateMatch ge e le m f k Out_continue (.State f .Scontinue k e le m)
  | osm_return_none (k') :
      callCont k' = callCont k →
      OutcomeStateMatch ge e le m f k (Out_return none) (.State f (.Sreturn none) k' e le m)
  | osm_return_some (a v k') :
      callCont k' = callCont k →
      EvalExpr ge e le m a v →
      OutcomeStateMatch ge e le m f k (Out_return (some (v, typeof a)))
        (.State f (.Sreturn (some a)) k' e le m)

/-- `ClightBigstep.is_call_cont_call_cont` -/
theorem isCallCont_callCont {k : Cont} (h : isCallCont k = true) : callCont k = k := by
  cases k <;> simp_all [isCallCont, callCont]

/-- The trace bookkeeping of the proofs below. -/
local macro "trace_eq" : tactic => `(tactic| simp [Eapp, E0, List.append_assoc])

mutual
/-- `ClightBigstep.exec_stmt_steps` -/
theorem exec_stmt_steps {e le m s t le' m' out}
    (h : ExecStmt FE ge e le m s t le' m' out) (f : Function) (k : Cont) :
    ∃ S, Smallstep.Star (Step ge (FE ge)) (.State f s k e le m) t S ∧
      OutcomeStateMatch ge e le' m' f k out S := by
  match h with
  | .exec_Sskip .. => exact ⟨_, .refl _, .osm_normal⟩
  | .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
    exact ⟨_, star_one (.assign _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4), .osm_normal⟩
  | .exec_Sset _ _ _ _ _ _ h1 =>
    exact ⟨_, star_one (.set _ _ _ _ _ _ _ _ h1), .osm_normal⟩
  | .exec_Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact ⟨_, star_left (.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5)
      (star_right (eval_funcall_steps h6 _ rfl) (.returnstate _ _ _ _ _ _ _) rfl) (by trace_eq),
      .osm_normal⟩
  | .exec_Sbuiltin _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact ⟨_, star_one (.builtin _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2), .osm_normal⟩
  | .exec_Sseq_1 _ _ _ _ s2 _ _ _ _ _ _ _ h1 h2 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq s2 k)
    cases B1
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 f k
    exact ⟨S2, star_left (.seq _ _ _ _ _ _ _)
      (star_trans A1 (star_left (.skip_seq _ _ _ _ _ _) A2 rfl) rfl) (by trace_eq), B2⟩
  | .exec_Sseq_2 _ _ _ _ s2 _ _ _ _ h1 hne =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq s2 k)
    cases B1 with
    | osm_normal => exact absurd rfl hne
    | osm_break =>
      exact ⟨_, star_left (.seq _ _ _ _ _ _ _)
        (star_right A1 (.break_seq _ _ _ _ _ _) rfl) (by trace_eq), .osm_break⟩
    | osm_continue =>
      exact ⟨_, star_left (.seq _ _ _ _ _ _ _)
        (star_right A1 (.continue_seq _ _ _ _ _ _) rfl) (by trace_eq), .osm_continue⟩
    | osm_return_none k' hk =>
      exact ⟨_, star_left (.seq _ _ _ _ _ _ _) A1 (by trace_eq),
        .osm_return_none k' (by simpa [callCont] using hk)⟩
    | osm_return_some a v k' hk hv =>
      exact ⟨_, star_left (.seq _ _ _ _ _ _ _) A1 (by trace_eq),
        .osm_return_some a v k' (by simpa [callCont] using hk) hv⟩
  | .exec_Sifthenelse _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h3 f k
    exact ⟨S1, star_left (.ifthenelse _ _ _ _ _ _ _ _ _ _ h1 h2) A1 (by trace_eq), B1⟩
  | .exec_Sreturn_none .. => exact ⟨_, .refl _, .osm_return_none k rfl⟩
  | .exec_Sreturn_some _ _ _ a v h1 => exact ⟨_, .refl _, .osm_return_some a v k rfl h1⟩
  | .exec_Sbreak .. => exact ⟨_, .refl _, .osm_break⟩
  | .exec_Scontinue .. => exact ⟨_, .refl _, .osm_continue⟩
  | .exec_Sloop_stop1 _ _ _ s1 s2 _ _ _ _ _ h1 hbr =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kloop1 s1 s2 k)
    cases hbr with
    | B =>
      cases B1
      exact ⟨_, star_left (.loop _ _ _ _ _ _ _)
        (star_right A1 (.break_loop1 _ _ _ _ _ _ _) rfl) (by trace_eq), .osm_normal⟩
    | R ov =>
      cases B1 with
      | osm_return_none k' hk =>
        exact ⟨_, star_left (.loop _ _ _ _ _ _ _) A1 (by trace_eq),
          .osm_return_none k' (by simpa [callCont] using hk)⟩
      | osm_return_some a v k' hk hv =>
        exact ⟨_, star_left (.loop _ _ _ _ _ _ _) A1 (by trace_eq),
          .osm_return_some a v k' (by simpa [callCont] using hk) hv⟩
  | .exec_Sloop_stop2 _ _ _ s1 s2 _ _ _ _ _ _ _ _ _ h1 hnc h2 hbr =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kloop1 s1 s2 k)
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 f (.Kloop2 s1 s2 k)
    have A12 := star_trans (star_left (.loop _ _ _ _ _ _ _) A1 rfl)
      (star_left (by cases hnc <;> cases B1 <;>
          exact .skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp)) A2 rfl) rfl
    cases hbr with
    | B =>
      cases B2
      exact ⟨_, star_right A12 (.break_loop2 _ _ _ _ _ _ _) (by trace_eq), .osm_normal⟩
    | R ov =>
      cases B2 with
      | osm_return_none k' hk =>
        exact ⟨_, A12.trace_cast (by trace_eq), .osm_return_none k' (by simpa [callCont] using hk)⟩
      | osm_return_some a v k' hk hv =>
        exact ⟨_, A12.trace_cast (by trace_eq),
          .osm_return_some a v k' (by simpa [callCont] using hk) hv⟩
  | .exec_Sloop_loop _ _ _ s1 s2 _ _ _ _ _ _ _ _ _ _ _ h1 hnc h2 h3 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kloop1 s1 s2 k)
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 f (.Kloop2 s1 s2 k)
    obtain ⟨S3, A3, B3⟩ := exec_stmt_steps h3 f k
    cases B2
    have A12 := star_trans (star_left (.loop _ _ _ _ _ _ _) A1 rfl)
      (star_left (by cases hnc <;> cases B1 <;>
          exact .skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp)) A2 rfl) rfl
    exact ⟨S3, star_trans A12 (star_left (.skip_loop2 _ _ _ _ _ _ _) A3 rfl) (by trace_eq), B3⟩
  | .exec_Sswitch _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h3 f (.Kswitch k)
    have A0 := star_left (.switch _ _ _ _ _ _ _ _ _ h1 h2) A1 rfl
    cases B1 with
    | osm_normal =>
      exact ⟨_, star_right A0 (.skip_break_switch _ _ _ _ _ _ (Or.inl rfl)) (by trace_eq),
        .osm_normal⟩
    | osm_break =>
      exact ⟨_, star_right A0 (.skip_break_switch _ _ _ _ _ _ (Or.inr rfl)) (by trace_eq),
        .osm_normal⟩
    | osm_continue =>
      exact ⟨_, star_right A0 (.continue_switch _ _ _ _ _) (by trace_eq), .osm_continue⟩
    | osm_return_none k' hk =>
      exact ⟨_, A0.trace_cast (by trace_eq), .osm_return_none k' (by simpa [callCont] using hk)⟩
    | osm_return_some a v k' hk hv =>
      exact ⟨_, A0.trace_cast (by trace_eq),
        .osm_return_some a v k' (by simpa [callCont] using hk) hv⟩

/-- `ClightBigstep.eval_funcall_steps` -/
theorem eval_funcall_steps {m fd args t m' res}
    (h : EvalFuncall FE ge m fd args t m' res) (k : Cont) (hk : isCallCont k = true) :
    Smallstep.Star (Step ge (FE ge)) (.Callstate fd args k m) t (.Returnstate res k m') := by
  match h with
  | .eval_funcall_internal _ f _ _ e _ le2 _ m2 _ _ _ hfe hbody hres hfree =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps hbody f k
    have A0 := star_left (.internal_function _ _ _ _ _ _ _ hfe) A1 rfl
    have hck := isCallCont_callCont hk
    generalize hty : f.fn_return = ty at hres
    cases B1 with
    | osm_normal =>
      cases ty <;> simp [outcomeResultValue] at hres
      subst hres
      exact star_right A0 (.skip_call _ _ _ _ _ _ hk hfree) (by trace_eq)
    | osm_break => cases ty <;> simp [outcomeResultValue] at hres
    | osm_continue => cases ty <;> simp [outcomeResultValue] at hres
    | osm_return_none k' hk' =>
      cases ty <;> simp [outcomeResultValue] at hres
      subst hres
      have := Step.return_0 (ge := ge) (functionEntry := FE ge) f k' e le2 m2 _ hfree
      rw [hk', hck] at this
      exact star_right A0 this (by trace_eq)
    | osm_return_some a v k' hk' hv =>
      simp only [outcomeResultValue] at hres
      have := Step.return_1 (ge := ge) (functionEntry := FE ge) f a k' _ _ _ v _ _ hv
        (hty ▸ hres.2) hfree
      rw [hk', hck] at this
      exact star_right A0 this (by trace_eq)
  | .eval_funcall_external _ _ _ _ _ _ _ _ _ h1 =>
    exact star_one (.external_function _ _ _ _ _ _ _ _ _ _ h1)
end

/-- The states from which a diverging big-step execution is pending. -/
private def DivState (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop)
    (ge : CGenv) (S : State) (T : Traceinf) : Prop :=
  (∃ fd args k m, S = .Callstate fd args k m ∧ EvalinfFuncall FE ge m fd args T) ∨
  (∃ f s k e le m, S = .State f s k e le m ∧ ExecinfStmt FE ge e le m s T)

/-- Each pending divergence makes at least one small step and stays pending. -/
private theorem divState_plus {S T} (h : DivState FE ge S T) :
    ∃ S' t T', Smallstep.Plus (Step ge (FE ge)) S t S' ∧ DivState FE ge S' T' ∧ T = Eappinf t T' := by
  rcases h with ⟨fd, args, k, m, rfl, hf⟩ | ⟨f, s, k, e, le, m, rfl, hs⟩
  · cases hf with
    | evalinf_funcall_internal _ f _ _ e _ le1 hfe hbody =>
      exact ⟨_, E0, T, plus_one (.internal_function _ _ _ _ _ _ _ hfe),
        .inr ⟨_, _, _, _, _, _, rfl, hbody⟩, (Eappinf_E0 T).symm⟩
  · cases hs with
    | execinf_Scall _ _ _ optid _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact ⟨_, E0, T, plus_one (.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5),
        .inl ⟨_, _, _, _, rfl, h6⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sseq_1 _ _ _ _ _ _ h1 =>
      exact ⟨_, E0, T, plus_one (.seq _ _ _ _ _ _ _),
        .inr ⟨_, _, _, _, _, _, rfl, h1⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sseq_2 _ _ _ _ s2 t1 _ _ T2 h1 h2 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kseq s2 k)
      cases B1
      exact ⟨_, t1, T2, plus_left (.seq _ _ _ _ _ _ _)
          (star_right A1 (.skip_seq _ _ _ _ _ _) rfl) (by trace_eq),
        .inr ⟨_, _, _, _, _, _, rfl, h2⟩, rfl⟩
    | execinf_Sifthenelse _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      exact ⟨_, E0, T, plus_one (.ifthenelse _ _ _ _ _ _ _ _ _ _ h1 h2),
        .inr ⟨_, _, _, _, _, _, rfl, h3⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sloop_body1 _ _ _ _ _ _ h1 =>
      exact ⟨_, E0, T, plus_one (.loop _ _ _ _ _ _ _),
        .inr ⟨_, _, _, _, _, _, rfl, h1⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sloop_body2 _ _ _ s1 s2 t1 _ _ _ T2 h1 hnc h2 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kloop1 s1 s2 k)
      exact ⟨_, t1, T2, plus_left (.loop _ _ _ _ _ _ _)
          (star_right A1 (by cases hnc <;> cases B1 <;>
            exact .skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp)) rfl) (by trace_eq),
        .inr ⟨_, _, _, _, _, _, rfl, h2⟩, rfl⟩
    | execinf_Sloop_loop _ _ _ s1 s2 t1 _ _ _ t2 _ _ T3 h1 hnc h2 h3 =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 f (.Kloop1 s1 s2 k)
      obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 f (.Kloop2 s1 s2 k)
      cases B2
      exact ⟨_, Eapp t1 t2, T3, plus_left (.loop _ _ _ _ _ _ _)
          (star_trans A1 (star_left (by cases hnc <;> cases B1 <;>
              exact .skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp))
            (star_right A2 (.skip_loop2 _ _ _ _ _ _ _) rfl) rfl) rfl) (by trace_eq),
        .inr ⟨_, _, _, _, _, _, rfl, h3⟩, (Eappinf_assoc _ _ _).symm⟩
    | execinf_Sswitch _ _ _ _ _ _ _ _ h1 h2 h3 =>
      exact ⟨_, E0, T, plus_one (.switch _ _ _ _ _ _ _ _ _ h1 h2),
        .inr ⟨_, _, _, _, _, _, rfl, h3⟩, (Eappinf_E0 T).symm⟩

/-- A diverging statement execution gives an infinite small-step run. -/
theorem execinf_stmt_forever {e le m s T} (f : Function) (k : Cont)
    (h : ExecinfStmt FE ge e le m s T) :
    Forever (Step ge (FE ge)) (.State f s k e le m) T :=
  forever_of_plus (DivState FE ge) (fun _ _ h => divState_plus h) _ _
    (.inr ⟨_, _, _, _, _, _, rfl, h⟩)

/-- `ClightBigstep.evalinf_funcall_forever` -/
theorem evalinf_funcall_forever {m fd args T} (k : Cont)
    (h : EvalinfFuncall FE ge m fd args T) :
    Forever (Step ge (FE ge)) (.Callstate fd args k m) T :=
  forever_of_plus (DivState FE ge) (fun _ _ h => divState_plus h) _ _
    (.inl ⟨_, _, _, _, rfl, h⟩)

end BIGSTEP_TO_TRANSITIONS

/-- `ClightBigstep.semantics_fe`: the small-step semantics of Clight for the
    function-entry predicate `FE`. -/
def semanticsFe (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop)
    (p : Program) : Semantics where
  state := State
  step := Step p.globalenv (FE p.globalenv)
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv.genv_genv

/-- `ClightBigstep.bigstep_semantics_sound`: every terminating or diverging
    big-step execution of `p` is matched by a run of the small-step semantics. -/
theorem bigstep_semantics_sound
    (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop) (p : Program) :
    BigstepSound (bigstepSemantics FE p) (semanticsFe FE p) where
  bigstep_terminates_sound := by
    intro t r h
    cases h with
    | intro b f m0 m1 _ _ hinit hsym hfun htype heval =>
      exact ⟨_, _, .intro b f m0 hinit hsym hfun htype,
        eval_funcall_steps heval .Kstop rfl, .intro r m1⟩
  bigstep_diverges_sound := by
    intro T h
    cases h with
    | intro b f m0 _ hinit hsym hfun htype heval =>
      exact ⟨_, .intro b f m0 hinit hsym hfun htype, evalinf_funcall_forever .Kstop heval⟩

end ClightBigstep

/-! ## Clight1 and Clight2 -/

namespace Clight1
open ClightBigstep Smallstep

/-- `Clight1.exec_stmt` -/
abbrev exec_stmt (ge : CGenv) := ExecStmt FunctionEntry1 ge
/-- `Clight1.eval_funcall` -/
abbrev eval_funcall (ge : CGenv) := EvalFuncall FunctionEntry1 ge
/-- `Clight1.execinf_stmt` -/
abbrev execinf_stmt (ge : CGenv) := ExecinfStmt FunctionEntry1 ge
/-- `Clight1.evalinf_funcall` -/
abbrev evalinf_funcall (ge : CGenv) := EvalinfFuncall FunctionEntry1 ge
/-- `Clight1.bigstep_semantics` -/
abbrev bigstep_semantics (p : Program) := bigstepSemantics FunctionEntry1 p

/-- `Clight1.bigstep_semantics_sound` -/
theorem bigstep_semantics_sound (p : Program) :
    BigstepSound (bigstep_semantics p) (Clight.semantics1 p) :=
  ClightBigstep.bigstep_semantics_sound _ p

/-- A terminating big-step execution of `p` is a `Terminates` behaviour of
    `Clight.semantics1 p` (`behavior_bigstep_terminates`). -/
theorem bigstep_terminates_behaves {p : Program} {t r}
    (h : (bigstep_semantics p).bigstep_terminates t r) :
    ProgramBehaves (Clight.semantics1 p) (.Terminates t r) :=
  behavior_bigstep_terminates (bigstep_semantics_sound p) h

/-- A diverging big-step execution of `p` is a reactive behaviour of
    `Clight.semantics1 p`, or a silent divergence after a finite prefix of its
    trace (`behavior_bigstep_diverges`). -/
theorem bigstep_diverges_behaves {p : Program} {T}
    (h : (bigstep_semantics p).bigstep_diverges T) :
    ProgramBehaves (Clight.semantics1 p) (.Reacts T) ∨
    ∃ t, ProgramBehaves (Clight.semantics1 p) (.Diverges t) ∧ ∃ T', T = Eappinf t T' :=
  behavior_bigstep_diverges (bigstep_semantics_sound p) h

end Clight1

namespace Clight2
open ClightBigstep Smallstep

/-- `Clight2.exec_stmt` -/
abbrev exec_stmt (ge : CGenv) := ExecStmt FunctionEntry2 ge
/-- `Clight2.eval_funcall` -/
abbrev eval_funcall (ge : CGenv) := EvalFuncall FunctionEntry2 ge
/-- `Clight2.execinf_stmt` -/
abbrev execinf_stmt (ge : CGenv) := ExecinfStmt FunctionEntry2 ge
/-- `Clight2.evalinf_funcall` -/
abbrev evalinf_funcall (ge : CGenv) := EvalinfFuncall FunctionEntry2 ge
/-- `Clight2.bigstep_semantics` -/
abbrev bigstep_semantics (p : Program) := bigstepSemantics FunctionEntry2 p

/-- `Clight2.bigstep_semantics_sound` -/
theorem bigstep_semantics_sound (p : Program) :
    BigstepSound (bigstep_semantics p) (Clight.semantics2 p) :=
  ClightBigstep.bigstep_semantics_sound _ p

/-- A terminating big-step execution of `p` is a `Terminates` behaviour of
    `Clight.semantics2 p` (`behavior_bigstep_terminates`). -/
theorem bigstep_terminates_behaves {p : Program} {t r}
    (h : (bigstep_semantics p).bigstep_terminates t r) :
    ProgramBehaves (Clight.semantics2 p) (.Terminates t r) :=
  behavior_bigstep_terminates (bigstep_semantics_sound p) h

/-- A diverging big-step execution of `p` is a reactive behaviour of
    `Clight.semantics2 p`, or a silent divergence after a finite prefix of its
    trace (`behavior_bigstep_diverges`). -/
theorem bigstep_diverges_behaves {p : Program} {T}
    (h : (bigstep_semantics p).bigstep_diverges T) :
    ProgramBehaves (Clight.semantics2 p) (.Reacts T) ∨
    ∃ t, ProgramBehaves (Clight.semantics2 p) (.Diverges t) ∧ ∃ T', T = Eappinf t T' :=
  behavior_bigstep_diverges (bigstep_semantics_sound p) h

end Clight2

end CC
