/-
  `Clight.semantics_receptive` (`cfrontend/Clight.v`): both Clight semantics
  are receptive — whenever a step can emit trace `t1`, it can also emit any
  trace `t2` that `match_traces` relates to `t1`.

  The only Clight steps that emit events are the built-in and external-call
  steps, so this reduces to `ec_receptive` (`externalCall_receptive` in
  `CCLib.common.EventsReceptive`).  For the uninterpreted externals, whose
  receptiveness CompCert assumes by axiom, it is a hypothesis
  (`ExternalsReceptive`).
-/
import CCLib.common.EventsReceptive
import CCLib.cfrontend.ClightBehaviors

namespace CC

/-- The receptiveness of the uninterpreted external functions and inline
    assembly in symbol environment `ge`: what CompCert's
    `external_functions_properties` / `inline_assembly_properties` axioms
    provide (field `ec_receptive`). -/
structure ExternalsReceptive (ge : Senv) : Prop where
  ext : ∀ name sg, ExtcallReceptive (externalFunctionsSem name sg) ge
  asm : ∀ name sg, ExtcallReceptive (inlineAssemblySem name sg) ge

namespace ClightReceptive

/-- One Clight step (for any function-entry relation) is receptive. -/
theorem step_receptive {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hx : ExternalsReceptive ge.genv_genv.toSenv) {s : State} {t1 : Trace} {s1 : State}
    {t2 : Trace} (h : Step ge fe s t1 s1) (hm : MatchTraces ge.genv_genv.toSenv t1 t2) :
    ∃ s2, Step ge fe s t2 s2 := by
  have hp := Genv.toSenv_publicSymbolExists ge.genv_genv
  have h' := h
  cases h with
  | builtin f optid ef tyargs al k e le m vargs t vres m' hevl hec =>
    obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
    exact ⟨_, .builtin f optid ef tyargs al k e le m vargs t2 vres2 m2 hevl h2⟩
  | external_function ef targs tres cconv vargs k m vres t m' hec =>
    obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
    exact ⟨_, .external_function ef targs tres cconv vargs k m vres2 t2 m2 h2⟩
  | _ => rw [EventsReceptive.matchTraces_E0 hm]; exact ⟨_, h'⟩

end ClightReceptive

namespace Clight

/-- `Clight.semantics_receptive` for `semantics1`. -/
theorem semantics1_receptive (p : Program)
    (hx : ExternalsReceptive p.globalenv.genv_genv.toSenv) :
    Smallstep.Receptive (semantics1 p) where
  sr_receptive := fun _ _ _ _ h hm => ClightReceptive.step_receptive hx h hm
  sr_traces := (semantics1_determinate p).sd_traces

/-- `Clight.semantics_receptive` for `semantics2`. -/
theorem semantics2_receptive (p : Program)
    (hx : ExternalsReceptive p.globalenv.genv_genv.toSenv) :
    Smallstep.Receptive (semantics2 p) where
  sr_receptive := fun _ _ _ _ h hm => ClightReceptive.step_receptive hx h hm
  sr_traces := (semantics2_determinate p).sd_traces

end Clight
end CC
