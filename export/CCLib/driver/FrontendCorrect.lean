/-
  Correctness of the front end of the compiler, CompCert C → Cminor: the
  composition of the semantic-preservation theorems of `SimplExpr`,
  `SimplLocals`, `Cshmgen` and `Cminorgen` (the front-end part of
  `driver/Compiler.v`, `transf_c_program_correct`).

  Differences from Rocq:
  * whole programs only (no linking, no `match_prog` composition);
  * the source semantics is `Cstrategy.semantics` (CompCert C executed with
    the compiler's evaluation order); the step from `Csem.semantics` to
    `Cstrategy.semantics` (`Cstrategy.strategy_simulation`) and the back end
    are not part of this theorem;
  * the properties of external functions and inline assembly that CompCert
    states as axioms (`external_functions_properties`,
    `inline_assembly_properties`) are hypotheses.
-/
import CCLib.driver.Compiler
import CCLib.cfrontend.SimplExprproofStep
import CCLib.cfrontend.SimplLocalsproofStep
import CCLib.cfrontend.CshmgenproofStep
import CCLib.cfrontend.CminorgenproofStep

namespace CC
namespace Compiler

open Config Smallstep

/-- `apply_partial` is associative. -/
theorem applyPartial_assoc {A B C : Type} (x : Res A) (f : A → Res B) (g : B → Res C) :
    applyPartial (applyPartial x f) g = applyPartial x (fun a => applyPartial (f a) g) := by
  cases x <;> rfl

variable (c : Config)

/-- The front end of `transf_c_program`: from CompCert C to Cminor. -/
def transfCFrontend (p : Csyntax.Program) : Res Cminor.Program :=
  Res.OK p
  @@@ time "Clight generation" (SimplExpr.translProgram (c.firstUnusedIdent p))
  @@@ time "Simplification of locals" (SimplLocals.transfProgram c.simplLocalsOptions)
  @@@ time "C#minor generation" (Cshmgen.translProgram (Conventions1.returnValueNeedsNormalization c.abi))
  @@@ time "Cminor generation" Cminorgen.translProgram

/-- The whole compiler is its front end followed by `transf_cminor_program`. -/
theorem transfCProgram_eq (p : Csyntax.Program) :
    transfCProgram c p = applyPartial (transfCFrontend c p) (transfCminorProgram c) := by
  simp only [transfCProgram, transfCFrontend, time, applyPartial_assoc, applyPartial_OK]
  congr 1; funext a
  simp only [transfClightProgram, time, applyPartial_assoc, applyPartial_OK]

/-- Semantic preservation for the front end: if `transfCFrontend` compiles the
    CompCert C program `p` to the Cminor program `tp`, then there is a forward
    simulation from `p` (executed with the compiler's evaluation order) to
    `tp`.

    * `hext` / `hasm`: external functions and inline assembly commute with
      memory injections (`ec_mem_inject`);
    * `hextw` / `hasmw`: their results are well typed (`ec_well_typed`);
    * `hextp` / `hasmp`: they satisfy the memory properties `ec_max_perm`,
      `ec_readonly`, … (`extcall_properties`).

    In CompCert these are parts of the axioms `external_functions_properties`
    and `inline_assembly_properties`. -/
theorem transfCFrontend_correct (p : Csyntax.Program) (tp : Cminor.Program)
    (h : transfCFrontend c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Cstrategy.semantics p) (Cminor.semantics tp) := by
  obtain ⟨p3, h123, h4⟩ := applyPartial_OK_inv h
  obtain ⟨p2, h12, h3⟩ := applyPartial_OK_inv h123
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h12
  rw [applyPartial_OK] at h1
  simp only [time] at h1 h2 h3 h4
  have hwf1 : p1.prog_comp_env.WF := by
    rw [SimplExpr.comp_env_preserved h1]; exact buildCompositeEnv_wf p.prog_comp_env_eq
  have hwf2 : p2.prog_comp_env.WF := by
    rw [SimplLocals.comp_env_preserved h2]; exact hwf1
  exact compose_forward_simulations (SimplExpr.transl_program_correct _ p p1 h1)
    (compose_forward_simulations (SimplLocals.transf_program_correct _ p1 p2 h2 hwf1 hext hasm)
      (compose_forward_simulations (Cshmgen.transl_program_correct _ p2 p3 h3 hwf2 hextw hasmw)
        (Cminorgen.transl_program_correct p3 tp h4 hext hasm hextp hasmp)))

end Compiler
end CC
