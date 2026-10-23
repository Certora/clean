/-
  Corollaries of the main semantic preservation theorem — port of the
  whole-program part of `driver/Complements.v`:
  `transf_c_program_preservation`, `transf_c_program_is_refinement`,
  `transf_cstrategy_program_preservation`, `bigstep_cstrategy_preservation`,
  `specification`, `c_program_satisfies_spec`, `asm_program_satisfies_spec`,
  `safety_enforcing_specification`, `transf_c_program_preserves_spec`,
  `c_program_has_initial_trace`, `asm_program_has_initial_trace` and
  `transf_c_program_preserves_initial_trace`.

  Differences from Rocq: the hypotheses of `Compiler.transfCProgram_correct`
  (CompCert's axioms on external functions
  and inline assembly) are section variables.  Not ported: the section on separate compilation
  (linking is not ported).
-/
import CCLib.driver.CompilerCorrect
import CCLib.common.BehaviorsAtomic
import CCLib.cfrontend.CstrategyBigstepSound

namespace CC
namespace Complements

open Smallstep Compiler ProgramBehavior

/-- `Complements.specification`: a set of observable behaviors. -/
def Specification := ProgramBehavior → Prop

/-- `Complements.c_program_satisfies_spec` -/
def CProgramSatisfiesSpec (p : Csyntax.Program) (spec : Specification) : Prop :=
  ∀ beh, ProgramBehaves (Csem.semantics p) beh → spec beh

/-- `Complements.asm_program_satisfies_spec` -/
def AsmProgramSatisfiesSpec (sym : Asm.SymbolSplit) (abi : Conventions1.AbiKind)
    (p : Asm.Program) (spec : Specification) : Prop :=
  ∀ beh, ProgramBehaves (Asm.semantics sym abi p) beh → spec beh

/-- `Complements.safety_enforcing_specification` -/
def SafetyEnforcingSpecification (spec : Specification) : Prop :=
  ∀ beh, spec beh → beh.not_wrong

/-- `Complements.c_program_has_initial_trace` -/
def CProgramHasInitialTrace (p : Csyntax.Program) (t : Trace) : Prop :=
  ∀ beh, ProgramBehaves (Csem.semantics p) beh → behavior_prefix t beh

/-- `Complements.asm_program_has_initial_trace` -/
def AsmProgramHasInitialTrace (sym : Asm.SymbolSplit) (abi : Conventions1.AbiKind)
    (p : Asm.Program) (t : Trace) : Prop :=
  ∀ beh, ProgramBehaves (Asm.semantics sym abi p) beh → behavior_prefix t beh

section WHOLE_PROGRAM
variable (c : Config) (sym : Asm.SymbolSplit)
  (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
  (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
  (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
  (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
  (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
  (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
  (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
  (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)
include hext hasm hextx hasmx hextw hasmw hextp hasmp

/-- `Complements.transf_c_program_preservation`: every behavior of the
    generated assembly code is an improvement of a behavior of the source C
    program. -/
theorem transf_c_program_preservation {p : Csyntax.Program} {tp : Asm.Program}
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv)
    (h : transfCProgram c p = .OK tp) {beh : ProgramBehavior}
    (hb : ProgramBehaves (Asm.semantics sym c.abi tp) beh) :
    ∃ beh', ProgramBehaves (Csem.semantics p) beh' ∧ behavior_improves beh' beh :=
  backward_simulation_behavior_improves
    (transfCProgram_correct c sym p tp h hext hasm hextx hasmx hextw hasmw
      hextp hasmp hrec) hb

/-- `Complements.transf_c_program_is_refinement`: if the source C program
    cannot go wrong, every behavior of the generated code is a behavior of the
    source. -/
theorem transf_c_program_is_refinement {p : Csyntax.Program} {tp : Asm.Program}
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv)
    (h : transfCProgram c p = .OK tp)
    (hsafe : ∀ beh, ProgramBehaves (Csem.semantics p) beh → beh.not_wrong)
    {beh : ProgramBehavior} (hb : ProgramBehaves (Asm.semantics sym c.abi tp) beh) :
    ProgramBehaves (Csem.semantics p) beh :=
  backward_simulation_same_safe_behavior
    (transfCProgram_correct c sym p tp h hext hasm hextx hasmx hextw hasmw
      hextp hasmp hrec) hsafe hb

/-- The forward half of `Complements.transf_cstrategy_program_preservation`:
    for the evaluation strategy implemented by the compiler, every behavior of
    the source is improved by a behavior of the generated code, and every
    behavior of the source that does not go wrong is a behavior of the
    generated code. -/
theorem transf_cstrategy_program_preservation_forward {p : Csyntax.Program}
    {tp : Asm.Program} (h : transfCProgram c p = .OK tp) :
    (∀ beh, ProgramBehaves (Cstrategy.semantics p) beh →
      ∃ beh', ProgramBehaves (Asm.semantics sym c.abi tp) beh' ∧ behavior_improves beh beh') ∧
    (∀ beh, beh.not_wrong → ProgramBehaves (Cstrategy.semantics p) beh →
      ProgramBehaves (Asm.semantics sym c.abi tp) beh) := by
  have FS := transfCProgram_correct_strategy c sym p tp h hext hasm hextx
    hasmx hextw hasmw hextp hasmp
  exact ⟨fun _ hb => forward_simulation_behavior_improves FS hb,
    fun _ hnw hb => forward_simulation_same_safe_behavior FS hb hnw⟩

/-- `Complements.transf_cstrategy_program_preservation`: for the evaluation
    strategy implemented by the compiler, behaviors are preserved in both
    directions (up to improvement), and exactly when the source cannot go
    wrong. -/
theorem transf_cstrategy_program_preservation {p : Csyntax.Program}
    {tp : Asm.Program}
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv)
    (h : transfCProgram c p = .OK tp) :
    (∀ beh, ProgramBehaves (Cstrategy.semantics p) beh →
      ∃ beh', ProgramBehaves (Asm.semantics sym c.abi tp) beh' ∧ behavior_improves beh beh') ∧
    (∀ beh, ProgramBehaves (Asm.semantics sym c.abi tp) beh →
      ∃ beh', ProgramBehaves (Cstrategy.semantics p) beh' ∧ behavior_improves beh' beh) ∧
    (∀ beh, beh.not_wrong → ProgramBehaves (Cstrategy.semantics p) beh →
      ProgramBehaves (Asm.semantics sym c.abi tp) beh) ∧
    (∀ beh, (∀ beh', ProgramBehaves (Cstrategy.semantics p) beh' → beh'.not_wrong) →
      ProgramBehaves (Asm.semantics sym c.abi tp) beh →
      ProgramBehaves (Cstrategy.semantics p) beh) := by
  have WBT := (Cstrategy.semantics_strongly_receptive p hrec).ssr_well_behaved
  have BS := cstrategy_backward_simulation c sym p tp h hext hasm hextx
    hasmx hextw hasmw hextp hasmp hrec
  obtain ⟨F1, F2⟩ := transf_cstrategy_program_preservation_forward c sym
    hext hasm hextx hasmx hextw hasmw hextp hasmp h
  refine ⟨F1, ?_, F2, ?_⟩
  · intro beh hb
    obtain ⟨beh1, A, B⟩ := backward_simulation_behavior_improves BS hb
    exact ⟨beh1, (atomic_behaviors WBT beh1).2 A, B⟩
  · intro beh hsafe hb
    refine (atomic_behaviors WBT beh).2 (backward_simulation_same_safe_behavior BS ?_ hb)
    intro beh' hb'
    exact hsafe beh' ((atomic_behaviors WBT beh').2 hb')

/-- `Complements.bigstep_cstrategy_preservation`: terminating and diverging
    executions of the big-step semantics of CompCert C (for the compiler's
    evaluation strategy) are preserved by compilation. -/
theorem bigstep_cstrategy_preservation {p : Csyntax.Program} {tp : Asm.Program}
    (h : transfCProgram c p = .OK tp) :
    (∀ t r, Cstrategy.BigstepProgramTerminates p t r →
      ProgramBehaves (Asm.semantics sym c.abi tp) (.Terminates t r)) ∧
    (∀ T, Cstrategy.BigstepProgramDiverges p T →
      ProgramBehaves (Asm.semantics sym c.abi tp) (.Reacts T) ∨
      ∃ t, ProgramBehaves (Asm.semantics sym c.abi tp) (.Diverges t) ∧ ∃ T', T = Eappinf t T') := by
  have F := (transf_cstrategy_program_preservation_forward c sym
    hext hasm hextx hasmx hextw hasmw hextp hasmp h).2
  refine ⟨fun t r hb => F _ trivial (Cstrategy.bigstep_terminates_behaves hb), fun T hb => ?_⟩
  rcases Cstrategy.bigstep_diverges_behaves hb with A | ⟨t, A, B⟩
  · exact Or.inl (F _ trivial A)
  · exact Or.inr ⟨t, F _ trivial A, B⟩

/-- `Complements.transf_c_program_preserves_spec`: compilation preserves
    safety-enforcing specifications. -/
theorem transf_c_program_preserves_spec {p : Csyntax.Program} {tp : Asm.Program}
    {spec : Specification}
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv)
    (h : transfCProgram c p = .OK tp) (hses : SafetyEnforcingSpecification spec)
    (hc : CProgramSatisfiesSpec p spec) : AsmProgramSatisfiesSpec sym c.abi tp spec := by
  intro beh hb
  obtain ⟨beh', hc', himp⟩ := transf_c_program_preservation c sym hext hasm
    hextx hasmx hextw hasmw hextp hasmp hrec h hb
  have hs := hc _ hc'
  rcases himp with rfl | ⟨t, rfl, _⟩
  · exact hs
  · exact (hses _ hs).elim

/-- `Complements.transf_c_program_preserves_initial_trace`: compilation
    preserves the property "every execution starts by producing trace `t`". -/
theorem transf_c_program_preserves_initial_trace {p : Csyntax.Program} {tp : Asm.Program}
    {t : Trace}
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv)
    (h : transfCProgram c p = .OK tp) (hc : CProgramHasInitialTrace p t) :
    AsmProgramHasInitialTrace sym c.abi tp t := by
  intro beh hb
  obtain ⟨beh', hc', himp⟩ := transf_c_program_preservation c sym hext hasm
    hextx hasmx hextw hasmw hextp hasmp hrec h hb
  have hpre := hc _ hc'
  rcases himp with rfl | ⟨t', rfl, beh1, rfl⟩
  · exact hpre
  · obtain ⟨beh1', hEq⟩ := hpre
    cases beh1' with
    | Goes_wrong t0 =>
      simp only [behavior_app, ProgramBehavior.Goes_wrong.injEq] at hEq
      subst hEq
      exact ⟨behavior_app t0 beh1, (behavior_app_assoc _ _ _)⟩
    | _ => simp [behavior_app] at hEq

end WHOLE_PROGRAM

end Complements
end CC
