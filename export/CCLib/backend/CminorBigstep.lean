/-
  Big-step semantics of Cminor — port of the "alternate operational
  semantics (big-step)" part of `backend/Cminor.v` (`outcome`,
  `eval_funcall`/`exec_stmt`, `evalinf_funcall`/`execinf_stmt`,
  `bigstep_semantics`) and of section `BIGSTEP_TO_TRANSITION`
  (`outcome_state_match`, `eval_funcall_exec_stmt_steps`,
  `evalinf_funcall_forever`, `bigstep_semantics_sound`).

  As in `CCLib.cfrontend.ClightBigstep`, the mutually inductive and mutually
  coinductive predicates are Lean `mutual` blocks of `inductive` and
  `coinductive` declarations, the proof of `exec_stmt_steps` is by mutual
  structural recursion, and the divergence proof is one application of
  `forever_of_plus` (`CCLib.common.SmallstepForever`) instead of a `cofix`
  producing `forever_plus`.  The big-step semantics covers Cminor without
  `goto`, as in Rocq.
-/
import CCLib.backend.CminorSem
import CCLib.common.Bigstep

namespace CC
namespace Cminor

open Smallstep

/-! ## Outcomes -/

/-- `Cminor.outcome`: how the execution of a statement terminated. -/
inductive Outcome where
  /-- continue in sequence -/
  | Out_normal
  /-- terminate `n+1` enclosing blocks -/
  | Out_exit (n : Nat)
  /-- return immediately to the caller -/
  | Out_return (ov : Option Val)
  /-- already returned to the caller via a tail call -/
  | Out_tailcall_return (v : Val)

open Outcome

/-- `Cminor.outcome_block` -/
def outcomeBlock : Outcome → Outcome
  | Out_exit 0 => Out_normal
  | Out_exit (n + 1) => Out_exit n
  | out => out

/-- `Cminor.outcome_result_value` -/
def outcomeResultValue : Outcome → Val → Prop
  | Out_normal, vres => vres = .Vundef
  | Out_return none, vres => vres = .Vundef
  | Out_return (some v), vres => vres = v
  | Out_tailcall_return v, vres => vres = v
  | Out_exit _, _ => False

/-- `Cminor.outcome_free_mem` -/
def outcomeFreeMem : Outcome → Mem → Block → Z → Mem → Prop
  | Out_tailcall_return _, m, _, _, m' => m' = m
  | _, m, sp, sz, m' => Mem.free m sp 0 sz = some m'

/-! ## Terminating executions -/

section NATURALSEM
variable (ge : CGenv)

mutual
/-- `Cminor.eval_funcall`: the call of `fd` on `vargs` from memory `m`
    returns `vres` in memory `m'`, emitting the trace `t`. -/
inductive EvalFuncall : Mem → Fundef → List Val → Trace → Mem → Val → Prop where
  | eval_funcall_internal (m f vargs m1 sp e t e2 m2 out vres m3) :
      Val.HasArgtypeList vargs f.fn_sig.sig_args →
      Mem.alloc m 0 f.fn_stackspace = (m1, sp) →
      setLocals f.fn_vars (setParams vargs f.fn_params) = e →
      ExecStmt f (.Vptr sp Integers.Ptrofs.zero) e m1 f.fn_body t e2 m2 out →
      outcomeResultValue out vres →
      outcomeFreeMem out m2 sp f.fn_stackspace m3 →
      EvalFuncall m (.Internal f) vargs t m3 vres
  | eval_funcall_external (ef m args t res m') :
      externalCall ef ge.toSenv args m t res m' →
      EvalFuncall m (.External ef) args t m' res

/-- `Cminor.exec_stmt`: executing `s` in function `f` with stack pointer `sp`,
    from environment `e` and memory `m`, terminates with outcome `out`,
    environment `e'` and memory `m'`, emitting the trace `t`. -/
inductive ExecStmt : Function → Val → Env → Mem → Stmt → Trace → Env → Mem → Outcome → Prop where
  | exec_Sskip (f sp e m) : ExecStmt f sp e m .Sskip E0 e m Out_normal
  | exec_Sassign (f sp e m id a v) :
      EvalExpr ge sp e m a v →
      ExecStmt f sp e m (.Sassign id a) E0 (e.set id v) m Out_normal
  | exec_Sstore (f sp e m chunk addr a vaddr v m') :
      EvalExpr ge sp e m addr vaddr →
      EvalExpr ge sp e m a v →
      Mem.storev chunk m vaddr v = some m' →
      ExecStmt f sp e m (.Sstore chunk addr a) E0 e m' Out_normal
  | exec_Scall (f sp e m optid sig a bl vf vargs fd t m' vres e') :
      EvalExpr ge sp e m a vf →
      EvalExprlist ge sp e m bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      EvalFuncall m fd vargs t m' vres →
      e' = setOptvar optid vres e →
      ExecStmt f sp e m (.Scall optid sig a bl) t e' m' Out_normal
  | exec_Sbuiltin (f sp e m optid ef bl t m' vargs vres e') :
      EvalExprlist ge sp e m bl vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      e' = setOptvar optid vres e →
      ExecStmt f sp e m (.Sbuiltin optid ef bl) t e' m' Out_normal
  | exec_Sifthenelse (f sp e m a s1 s2 v b t e' m' out) :
      EvalExpr ge sp e m a v →
      Val.BoolOfVal v b →
      ExecStmt f sp e m (if b then s1 else s2) t e' m' out →
      ExecStmt f sp e m (.Sifthenelse a s1 s2) t e' m' out
  | exec_Sseq_continue (f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out) :
      ExecStmt f sp e m s1 t1 e1 m1 Out_normal →
      ExecStmt f sp e1 m1 s2 t2 e2 m2 out →
      t = Eapp t1 t2 →
      ExecStmt f sp e m (.Sseq s1 s2) t e2 m2 out
  | exec_Sseq_stop (f sp e m t s1 s2 e1 m1 out) :
      ExecStmt f sp e m s1 t e1 m1 out →
      out ≠ Out_normal →
      ExecStmt f sp e m (.Sseq s1 s2) t e1 m1 out
  | exec_Sloop_loop (f sp e m s t t1 e1 m1 t2 e2 m2 out) :
      ExecStmt f sp e m s t1 e1 m1 Out_normal →
      ExecStmt f sp e1 m1 (.Sloop s) t2 e2 m2 out →
      t = Eapp t1 t2 →
      ExecStmt f sp e m (.Sloop s) t e2 m2 out
  | exec_Sloop_stop (f sp e m t s e1 m1 out) :
      ExecStmt f sp e m s t e1 m1 out →
      out ≠ Out_normal →
      ExecStmt f sp e m (.Sloop s) t e1 m1 out
  | exec_Sblock (f sp e m s t e1 m1 out) :
      ExecStmt f sp e m s t e1 m1 out →
      ExecStmt f sp e m (.Sblock s) t e1 m1 (outcomeBlock out)
  | exec_Sexit (f sp e m n) : ExecStmt f sp e m (.Sexit n) E0 e m (Out_exit n)
  | exec_Sswitch (f sp e m islong a cases default v n) :
      EvalExpr ge sp e m a v →
      Switch.SwitchArgument islong v n →
      ExecStmt f sp e m (.Sswitch islong a cases default) E0 e m
        (Out_exit (Switch.switchTarget n default cases))
  | exec_Sreturn_none (f sp e m) : ExecStmt f sp e m (.Sreturn none) E0 e m (Out_return none)
  | exec_Sreturn_some (f sp e m a v) :
      EvalExpr ge sp e m a v →
      ExecStmt f sp e m (.Sreturn (some a)) E0 e m (Out_return (some v))
  | exec_Stailcall (f sp e m sig a bl vf vargs fd t m' m'' vres) :
      EvalExpr ge (.Vptr sp Integers.Ptrofs.zero) e m a vf →
      EvalExprlist ge (.Vptr sp Integers.Ptrofs.zero) e m bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      EvalFuncall m' fd vargs t m'' vres →
      ExecStmt f (.Vptr sp Integers.Ptrofs.zero) e m (.Stailcall sig a bl) t e m''
        (Out_tailcall_return vres)
end

/-! ## Diverging executions -/

mutual
/-- `Cminor.evalinf_funcall`: the call of `fd` on `vargs` diverges with the
    infinite trace `T`. -/
coinductive EvalinfFuncall : Mem → Fundef → List Val → Traceinf → Prop where
  | evalinf_funcall_internal (m f vargs m1 sp e T) :
      Val.HasArgtypeList vargs f.fn_sig.sig_args →
      Mem.alloc m 0 f.fn_stackspace = (m1, sp) →
      setLocals f.fn_vars (setParams vargs f.fn_params) = e →
      ExecinfStmt f (.Vptr sp Integers.Ptrofs.zero) e m1 f.fn_body T →
      EvalinfFuncall m (.Internal f) vargs T

/-- `Cminor.execinf_stmt`: the statement `s` diverges with the infinite
    trace `T`. -/
coinductive ExecinfStmt : Function → Val → Env → Mem → Stmt → Traceinf → Prop where
  | execinf_Scall (f sp e m optid sig a bl vf vargs fd T) :
      EvalExpr ge sp e m a vf →
      EvalExprlist ge sp e m bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      EvalinfFuncall m fd vargs T →
      ExecinfStmt f sp e m (.Scall optid sig a bl) T
  | execinf_Sifthenelse (f sp e m a s1 s2 v b T) :
      EvalExpr ge sp e m a v →
      Val.BoolOfVal v b →
      ExecinfStmt f sp e m (if b then s1 else s2) T →
      ExecinfStmt f sp e m (.Sifthenelse a s1 s2) T
  | execinf_Sseq_1 (f sp e m T s1 s2) :
      ExecinfStmt f sp e m s1 T →
      ExecinfStmt f sp e m (.Sseq s1 s2) T
  | execinf_Sseq_2 (f sp e m T s1 t1 e1 m1 s2 T2) :
      ExecStmt ge f sp e m s1 t1 e1 m1 Out_normal →
      ExecinfStmt f sp e1 m1 s2 T2 →
      T = Eappinf t1 T2 →
      ExecinfStmt f sp e m (.Sseq s1 s2) T
  | execinf_Sloop_body (f sp e m s T) :
      ExecinfStmt f sp e m s T →
      ExecinfStmt f sp e m (.Sloop s) T
  | execinf_Sloop_loop (f sp e m s T t1 e1 m1 T2) :
      ExecStmt ge f sp e m s t1 e1 m1 Out_normal →
      ExecinfStmt f sp e1 m1 (.Sloop s) T2 →
      T = Eappinf t1 T2 →
      ExecinfStmt f sp e m (.Sloop s) T
  | execinf_Sblock (f sp e m s T) :
      ExecinfStmt f sp e m s T →
      ExecinfStmt f sp e m (.Sblock s) T
  | execinf_Stailcall (f sp e m sig a bl vf vargs fd m' T) :
      EvalExpr ge (.Vptr sp Integers.Ptrofs.zero) e m a vf →
      EvalExprlist ge (.Vptr sp Integers.Ptrofs.zero) e m bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      EvalinfFuncall m' fd vargs T →
      ExecinfStmt f (.Vptr sp Integers.Ptrofs.zero) e m (.Stailcall sig a bl) T
end

end NATURALSEM

/-! ## Whole programs -/

/-- `Cminor.bigstep_program_terminates` -/
inductive BigstepProgramTerminates (p : Program) : Trace → Integers.Int → Prop where
  | intro (b f m0 t m r) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      EvalFuncall p.globalenv m0 f [] t m (.Vint r) →
      BigstepProgramTerminates p t r

/-- `Cminor.bigstep_program_diverges` -/
inductive BigstepProgramDiverges (p : Program) : Traceinf → Prop where
  | intro (b f m0 T) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      EvalinfFuncall p.globalenv m0 f [] T →
      BigstepProgramDiverges p T

/-- `Cminor.bigstep_semantics` -/
def bigstepSemantics (p : Program) : BigstepSemantics :=
  ⟨BigstepProgramTerminates p, BigstepProgramDiverges p⟩

/-! ## From big-step to small-step (`BIGSTEP_TO_TRANSITION`) -/

section BIGSTEP_TO_TRANSITION
variable {ge : CGenv}

/-- `Cminor.outcome_state_match`: the small-step state reached after executing
    a statement with the given outcome. -/
inductive OutcomeStateMatch (ge : CGenv) (sp : Val) (e : Env) (m : Mem) (f : Function)
    (k : Cont) : Outcome → State → Prop where
  | osm_normal : OutcomeStateMatch ge sp e m f k Out_normal (.State f .Sskip k sp e m)
  | osm_exit (n) : OutcomeStateMatch ge sp e m f k (Out_exit n) (.State f (.Sexit n) k sp e m)
  | osm_return_none (k') :
      callCont k' = callCont k →
      OutcomeStateMatch ge sp e m f k (Out_return none) (.State f (.Sreturn none) k' sp e m)
  | osm_return_some (k' a v) :
      callCont k' = callCont k →
      EvalExpr ge sp e m a v →
      OutcomeStateMatch ge sp e m f k (Out_return (some v))
        (.State f (.Sreturn (some a)) k' sp e m)
  | osm_tail (v) :
      OutcomeStateMatch ge sp e m f k (Out_tailcall_return v) (.Returnstate v (callCont k) m)

/-- `Cminor.is_call_cont_call_cont` -/
theorem isCallCont_callCont (k : Cont) : isCallCont (callCont k) = true := by
  induction k <;> simp_all [callCont, isCallCont]

/-- `Cminor.call_cont_is_call_cont` -/
theorem callCont_of_isCallCont {k : Cont} (h : isCallCont k = true) : callCont k = k := by
  cases k <;> simp_all [isCallCont, callCont]

/-- The trace bookkeeping of the proofs below. -/
local macro "trace_eq" : tactic => `(tactic| simp [Eapp, E0, List.append_assoc])

/-- The end of a statement that stopped with a non-normal outcome, inside
    `Kseq`: an `exit` propagates out of the sequence, the other outcomes are
    already in their final state (shared by `exec_Sseq_stop` and
    `exec_Sloop_stop`). -/
private theorem seq_stop {f : Function} {sp : Val} {e0 e : Env} {m0 m : Mem} {s s1 : Stmt}
    {k : Cont} {t : Trace} {S1 : State} {out : Outcome}
    (A1 : Smallstep.Star (Step ge) (.State f s1 (.Kseq s k) sp e0 m0) t S1)
    (B1 : OutcomeStateMatch ge sp e m f (.Kseq s k) out S1) (hne : out ≠ Out_normal) :
    ∃ S, Smallstep.Star (Step ge) (.State f s1 (.Kseq s k) sp e0 m0) t S ∧
      OutcomeStateMatch ge sp e m f k out S := by
  cases B1 with
  | osm_normal => exact absurd rfl hne
  | osm_exit n => exact ⟨_, star_right A1 (.exit_seq _ _ _ _ _ _ _) (by trace_eq), .osm_exit n⟩
  | osm_return_none k' hk => exact ⟨_, A1, .osm_return_none k' (by simpa [callCont] using hk)⟩
  | osm_return_some k' a v hk hv =>
    exact ⟨_, A1, .osm_return_some k' a v (by simpa [callCont] using hk) hv⟩
  | osm_tail v => exact ⟨_, A1, .osm_tail v⟩

mutual
/-- `Cminor.eval_funcall_steps` -/
theorem eval_funcall_steps {m fd args t m' res}
    (h : EvalFuncall ge m fd args t m' res) (k : Cont) (hk : isCallCont k = true) :
    Smallstep.Star (Step ge) (.Callstate fd args k m) t (.Returnstate res k m') := by
  match h with
  | .eval_funcall_internal _ f _ _ sp _ _ _ _ out vres _ h1 h2 h3 h4 h5 h6 =>
    obtain ⟨S, A, B⟩ := exec_stmt_steps h4 k
    have hck := callCont_of_isCallCont hk
    have hrest : Smallstep.Star (Step ge) S E0 (.Returnstate vres k m') := by
      cases B with
      | osm_normal =>
        subst h5
        exact star_one (.skip_call _ _ _ _ _ _ hk h6)
      | osm_exit n => exact h5.elim
      | osm_return_none k' hk' =>
        subst h5
        rw [← hck, ← hk']
        exact star_one (.return_0 _ _ _ _ _ _ h6)
      | osm_return_some k' a v hk' hv =>
        subst h5
        rw [← hck, ← hk']
        exact star_one (.return_1 _ _ _ _ _ _ _ _ hv h6)
      | osm_tail v =>
        subst h5
        have h6' : _ = _ := h6
        subst h6'
        rw [hck]
        exact .refl _
    exact star_left (.internal_function _ _ _ _ _ _ _ h1 h2 h3) (star_trans (t := t) A hrest (by trace_eq))
      (by trace_eq)
  | .eval_funcall_external _ _ _ _ _ _ h1 =>
    exact star_one (.external_function _ _ _ _ _ _ _ h1)

/-- `Cminor.exec_stmt_steps` -/
theorem exec_stmt_steps {f sp e m s t e' m' out}
    (h : ExecStmt ge f sp e m s t e' m' out) (k : Cont) :
    ∃ S, Smallstep.Star (Step ge) (.State f s k sp e m) t S ∧ OutcomeStateMatch ge sp e' m' f k out S := by
  match h with
  | .exec_Sskip .. => exact ⟨_, .refl _, .osm_normal⟩
  | .exec_Sassign _ _ _ _ _ _ _ h1 => exact ⟨_, star_one (.assign _ _ _ _ _ _ _ _ h1), .osm_normal⟩
  | .exec_Sstore _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    exact ⟨_, star_one (.store _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3), .osm_normal⟩
  | .exec_Scall _ _ _ _ optid _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    subst h6
    exact ⟨_, star_left (.call _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4)
      (star_right (eval_funcall_steps h5 _ rfl) (.return _ _ _ _ _ _ _) rfl) (by trace_eq),
      .osm_normal⟩
  | .exec_Sbuiltin _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    subst h3
    exact ⟨_, star_one (.builtin _ _ _ _ _ _ _ _ _ _ _ _ h1 h2), .osm_normal⟩
  | .exec_Sifthenelse _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    obtain ⟨S, A, B⟩ := exec_stmt_steps h3 k
    exact ⟨S, star_left (.ifthenelse _ _ _ _ _ _ _ _ _ _ h1 h2) A (by trace_eq), B⟩
  | .exec_Sseq_continue _ _ _ _ _ _ _ _ _ s2 _ _ _ _ h1 h2 ht =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 (.Kseq s2 k)
    cases B1
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 k
    subst ht
    exact ⟨S2, star_left (.seq _ _ _ _ _ _ _)
      (star_trans A1 (star_left (.skip_seq _ _ _ _ _ _) A2 rfl) rfl) (by trace_eq), B2⟩
  | .exec_Sseq_stop _ _ _ _ _ _ s2 _ _ _ h1 hne =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 (.Kseq s2 k)
    obtain ⟨S, A, B⟩ := seq_stop A1 B1 hne
    exact ⟨S, star_left (.seq _ _ _ _ _ _ _) A (by trace_eq), B⟩
  | .exec_Sloop_loop _ _ _ _ s _ _ _ _ _ _ _ _ h1 h2 ht =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 (.Kseq (.Sloop s) k)
    cases B1
    obtain ⟨S2, A2, B2⟩ := exec_stmt_steps h2 k
    subst ht
    exact ⟨S2, star_left (.loop _ _ _ _ _ _)
      (star_trans A1 (star_left (.skip_seq _ _ _ _ _ _) A2 rfl) rfl) (by trace_eq), B2⟩
  | .exec_Sloop_stop _ _ _ _ _ s _ _ _ h1 hne =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 (.Kseq (.Sloop s) k)
    obtain ⟨S, A, B⟩ := seq_stop A1 B1 hne
    exact ⟨S, star_left (.loop _ _ _ _ _ _) A (by trace_eq), B⟩
  | .exec_Sblock _ _ _ _ s1 t1 _ _ out h1 =>
    obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 (.Kblock k)
    have A1' : Smallstep.Star (Step ge) (.State f (.Sblock s1) k sp e m) t1 S1 :=
      star_left (.block _ _ _ _ _ _) A1 (by trace_eq)
    cases B1 with
    | osm_normal =>
      exact ⟨_, star_right A1' (.skip_block _ _ _ _ _) (by trace_eq), .osm_normal⟩
    | osm_exit n =>
      cases n with
      | zero => exact ⟨_, star_right A1' (.exit_block_0 _ _ _ _ _) (by trace_eq), .osm_normal⟩
      | succ n =>
        exact ⟨_, star_right A1' (.exit_block_S _ _ _ _ _ _) (by trace_eq), .osm_exit n⟩
    | osm_return_none k' hk =>
      exact ⟨_, A1', .osm_return_none k' (by simpa [callCont] using hk)⟩
    | osm_return_some k' a v hk hv =>
      exact ⟨_, A1', .osm_return_some k' a v (by simpa [callCont] using hk) hv⟩
    | osm_tail v => exact ⟨_, A1', .osm_tail v⟩
  | .exec_Sexit .. => exact ⟨_, .refl _, .osm_exit _⟩
  | .exec_Sswitch _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact ⟨_, star_one (.switch _ _ _ _ _ _ _ _ _ _ _ h1 h2), .osm_exit _⟩
  | .exec_Sreturn_none .. => exact ⟨_, .refl _, .osm_return_none k rfl⟩
  | .exec_Sreturn_some _ _ _ _ a v h1 => exact ⟨_, .refl _, .osm_return_some k a v rfl h1⟩
  | .exec_Stailcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact ⟨_, star_left (.tailcall _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5)
      (eval_funcall_steps h6 _ (isCallCont_callCont k)) (by trace_eq), .osm_tail _⟩
end

/-- The states from which a diverging big-step execution is pending. -/
private def DivState (ge : CGenv) (S : State) (T : Traceinf) : Prop :=
  (∃ fd args k m, S = .Callstate fd args k m ∧ EvalinfFuncall ge m fd args T) ∨
  (∃ f s k sp e m, S = .State f s k sp e m ∧ ExecinfStmt ge f sp e m s T)

/-- Each pending divergence makes at least one small step and stays pending. -/
private theorem divState_plus {S T} (h : DivState ge S T) :
    ∃ S' t T', Smallstep.Plus (Step ge) S t S' ∧ DivState ge S' T' ∧ T = Eappinf t T' := by
  rcases h with ⟨fd, args, k, m, rfl, hf⟩ | ⟨f, s, k, sp, e, m, rfl, hs⟩
  · cases hf with
    | evalinf_funcall_internal _ f _ _ _ _ _ h1 h2 h3 h4 =>
      exact ⟨_, E0, T, plus_one (.internal_function _ _ _ _ _ _ _ h1 h2 h3),
        .inr ⟨_, _, _, _, _, _, rfl, h4⟩, (Eappinf_E0 T).symm⟩
  · cases hs with
    | execinf_Scall _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      exact ⟨_, E0, T, plus_one (.call _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4),
        .inl ⟨_, _, _, _, rfl, h5⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sifthenelse _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      exact ⟨_, E0, T, plus_one (.ifthenelse _ _ _ _ _ _ _ _ _ _ h1 h2),
        .inr ⟨_, _, _, _, _, _, rfl, h3⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sseq_1 _ _ _ _ _ _ _ h1 =>
      exact ⟨_, E0, T, plus_one (.seq _ _ _ _ _ _ _),
        .inr ⟨_, _, _, _, _, _, rfl, h1⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sseq_2 _ _ _ _ _ _ t1 _ _ s2 T2 h1 h2 hT =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 (.Kseq s2 k)
      cases B1
      exact ⟨_, t1, T2, plus_left (.seq _ _ _ _ _ _ _)
          (star_right A1 (.skip_seq _ _ _ _ _ _) rfl) (by trace_eq),
        .inr ⟨_, _, _, _, _, _, rfl, h2⟩, hT⟩
    | execinf_Sloop_body _ _ _ _ _ _ h1 =>
      exact ⟨_, E0, T, plus_one (.loop _ _ _ _ _ _),
        .inr ⟨_, _, _, _, _, _, rfl, h1⟩, (Eappinf_E0 T).symm⟩
    | execinf_Sloop_loop _ _ _ _ s _ t1 _ _ T2 h1 h2 hT =>
      obtain ⟨S1, A1, B1⟩ := exec_stmt_steps h1 (.Kseq (.Sloop s) k)
      cases B1
      exact ⟨_, t1, T2, plus_left (.loop _ _ _ _ _ _)
          (star_right A1 (.skip_seq _ _ _ _ _ _) rfl) (by trace_eq),
        .inr ⟨_, _, _, _, _, _, rfl, h2⟩, hT⟩
    | execinf_Sblock _ _ _ _ _ _ h1 =>
      exact ⟨_, E0, T, plus_one (.block _ _ _ _ _ _),
        .inr ⟨_, _, _, _, _, _, rfl, h1⟩, (Eappinf_E0 T).symm⟩
    | execinf_Stailcall _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact ⟨_, E0, T, plus_one (.tailcall _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5),
        .inl ⟨_, _, _, _, rfl, h6⟩, (Eappinf_E0 T).symm⟩

/-- A diverging statement execution gives an infinite small-step run. -/
theorem execinf_stmt_forever {f sp e m s T} (k : Cont) (h : ExecinfStmt ge f sp e m s T) :
    Forever (Step ge) (.State f s k sp e m) T :=
  forever_of_plus (DivState ge) (fun _ _ h => divState_plus h) _ _
    (.inr ⟨_, _, _, _, _, _, rfl, h⟩)

/-- `Cminor.evalinf_funcall_forever` (stated with `forever`, which
    `forever_plus` implies). -/
theorem evalinf_funcall_forever {m fd args T} (k : Cont) (h : EvalinfFuncall ge m fd args T) :
    Forever (Step ge) (.Callstate fd args k m) T :=
  forever_of_plus (DivState ge) (fun _ _ h => divState_plus h) _ _
    (.inl ⟨_, _, _, _, rfl, h⟩)

end BIGSTEP_TO_TRANSITION

/-- `Cminor.bigstep_semantics_sound`: every terminating or diverging big-step
    execution of `p` is matched by a run of the small-step semantics. -/
theorem bigstep_semantics_sound (p : Program) :
    BigstepSound (bigstepSemantics p) (semantics p) where
  bigstep_terminates_sound := by
    intro t r h
    cases h with
    | intro b f m0 _ m1 _ hinit hsym hfun hsig heval =>
      exact ⟨_, _, .intro b f m0 hinit hsym hfun hsig, eval_funcall_steps heval .Kstop rfl,
        .intro r m1⟩
  bigstep_diverges_sound := by
    intro T h
    cases h with
    | intro b f m0 _ hinit hsym hfun hsig heval =>
      exact ⟨_, .intro b f m0 hinit hsym hfun hsig, evalinf_funcall_forever .Kstop heval⟩

end Cminor
end CC
