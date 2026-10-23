/-
  [RISC-V instance of `CCLib/driver/CompilerCorrect.lean`.]

  Semantic preservation for the whole RISC-V compiler as a backward
  simulation — `Compiler.transf_c_program_correct` for the RISC-V target:

    `Csem.semantics p`  ⇐  `atomic (Cstrategy.semantics p)`  ⇐  `Asm.semantics tp`

  obtained, as in Rocq, by composing `Cstrategy.strategy_simulation` with the
  forward simulation `transfCProgram_correct_strategy` (turned into a
  backward simulation using that `atomic (Cstrategy.semantics p)` is
  receptive and that the RISC-V `Asm.semantics` is determinate).

  Differences from Rocq: whole programs only (no linking), and CompCert's
  axioms on external functions and inline assembly (including their
  receptiveness, `ExternalsReceptive`) are hypotheses.
-/
import CCLib.riscV.BackendCorrect
import CCLib.riscV.AsmDeterm
import CCLib.cfrontend.CstrategyBackward
import CCLib.cfrontend.CstrategyReceptive
import CCLib.common.SmallstepFactor
import CCLib.common.ForwardToBackward

namespace CC
namespace RiscV
namespace Compiler

open Smallstep

variable (c : Config)

/-- The backward half of `Compiler.cstrategy_semantic_preservation`
    (RISC-V): `Asm.semantics tp` is a backward simulation of
    `atomic (Cstrategy.semantics p)`. -/
theorem cstrategy_backward_simulation (sym : Asm.HalfSplit) (p : Csyntax.Program)
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
    BackwardSimulation (atomic (Cstrategy.semantics p)) (Asm.semantics sym tp) := by
  have hdet := Asm.semantics_determinate sym tp
  have hssr := Cstrategy.semantics_strongly_receptive p hrec
  exact forward_to_backward_simulation
      (factor_forward_simulation
        (transfCProgram_correct_strategy c sym p tp h hext hasm hextx hasmx
          hextw hasmw hextp hasmp)
        hdet.sd_traces)
      (atomic_receptive hssr) hdet

/-- `Compiler.transf_c_program_correct` (RISC-V): if the compiler translates
    the CompCert C program `p` to the RISC-V assembly program `tp`, then
    `Asm.semantics tp` is a backward simulation of `Csem.semantics p` (every
    behavior of `tp` is a behavior of `p`, for safe `p`). -/
theorem transfCProgram_correct (sym : Asm.HalfSplit) (p : Csyntax.Program)
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
    BackwardSimulation (Csem.semantics p) (Asm.semantics sym tp) := by
  have hdet := Asm.semantics_determinate sym tp
  have hssr := Cstrategy.semantics_strongly_receptive p hrec
  exact compose_backward_simulation hdet.sd_traces
    (factor_backward_simulation (Cstrategy.strategy_simulation p)
      (Csem.semantics_single_events p) hssr.ssr_well_behaved)
    (cstrategy_backward_simulation c sym p tp h hext hasm hextx hasmx
      hextw hasmw hextp hasmp hrec)

end Compiler
end RiscV
end CC
