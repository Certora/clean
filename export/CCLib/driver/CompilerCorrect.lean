/-
  Semantic preservation for the whole compiler as a backward simulation —
  the part of `driver/Compiler.v` that proves `c_semantic_preservation` /
  `transf_c_program_correct`:

    `Csem.semantics p`  ⇐  `atomic (Cstrategy.semantics p)`  ⇐  `Asm.semantics tp`

  obtained, as in Rocq, by composing
  * `Cstrategy.strategy_simulation` (factored through `atomic` with
    `factor_backward_simulation`), and
  * the forward simulation `transfCProgram_correct_strategy` from
    `Cstrategy.semantics` to `Asm.semantics` (factored through `atomic` with
    `factor_forward_simulation`), turned into a backward simulation by
    `forward_to_backward_simulation`, using that `atomic (Cstrategy.semantics p)`
    is receptive and that `Asm.semantics` is determinate.

  Differences from Rocq: whole programs only (no linking), and CompCert's axioms on external functions and inline assembly
  (including their receptiveness, `ExternalsReceptive`) are hypotheses.
-/
import CCLib.driver.BackendCorrect
import CCLib.aarch64.AsmDeterm
import CCLib.cfrontend.CstrategyBackward
import CCLib.cfrontend.CstrategyReceptive
import CCLib.common.SmallstepFactor
import CCLib.common.ForwardToBackward

namespace CC
namespace Compiler

open Smallstep

variable (c : Config)

/-- The backward half of `Compiler.cstrategy_semantic_preservation`:
    `Asm.semantics tp` is a backward simulation of
    `atomic (Cstrategy.semantics p)`.  Same hypotheses as
    `transfCProgram_correct`. -/
theorem cstrategy_backward_simulation (sym : Asm.SymbolSplit) (p : Csyntax.Program)
    (tp : Asm.Program) (h : transfCProgram c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv) :
    BackwardSimulation (atomic (Cstrategy.semantics p)) (Asm.semantics sym c.abi tp) := by
  have hdet := Asm.semantics_determinate sym c.abi tp
  have hssr := Cstrategy.semantics_strongly_receptive p hrec
  exact forward_to_backward_simulation
      (factor_forward_simulation
        (transfCProgram_correct_strategy c sym p tp h hext hasm hextx hasmx
          hextw hasmw hextp hasmp)
        hdet.sd_traces)
      (atomic_receptive hssr) hdet

/-- `Compiler.transf_c_program_correct`: if the compiler translates the
    CompCert C program `p` to the AArch64 assembly program `tp`, then
    `Asm.semantics tp` is a backward simulation of `Csem.semantics p` (every
    behavior of `tp` is a behavior of `p`, for safe `p`). -/
theorem transfCProgram_correct (sym : Asm.SymbolSplit) (p : Csyntax.Program)
    (tp : Asm.Program) (h : transfCProgram c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv) :
    BackwardSimulation (Csem.semantics p) (Asm.semantics sym c.abi tp) := by
  have hdet := Asm.semantics_determinate sym c.abi tp
  have hssr := Cstrategy.semantics_strongly_receptive p hrec
  exact compose_backward_simulation hdet.sd_traces
    (factor_backward_simulation (Cstrategy.strategy_simulation p)
      (Csem.semantics_single_events p) hssr.ssr_well_behaved)
    (cstrategy_backward_simulation c sym p tp h hext hasm hextx hasmx
      hextw hasmw hextp hasmp hrec)

end Compiler
end CC
