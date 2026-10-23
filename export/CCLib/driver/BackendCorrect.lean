/-
  Correctness of the back end of the compiler — the back-end part of
  `driver/Compiler.v` (`transf_rtl_program`, `transf_cminor_program`),
  obtained by composing the semantic-preservation theorems of the passes
  that have been ported:

  * `transfCminorToRtl` (Selection, RTLgen, Tailcall, Inlining, Renumber):
    Cminor → RTL;
  * `transfRtlMiddle` (Constprop, Renumber, CSE, Deadcode, Unusedglob):
    RTL → RTL (constant propagation is proved correct in
    `backend/ConstpropproofStep.lean`, CSE in `backend/CSEproofStep.lean`,
    redundancy elimination in `backend/DeadcodeproofMain.lean`);
  * `Allocation.transfProgram`: RTL → LTL;
  * `transfLtlProgram` (Tunneling, Linearize, CleanupLabels, Debugvar,
    Stacking, Asmgen): LTL → Asm.

  `transfCminorProgram_eq` proves that `transf_cminor_program` is the
  composition of these four stages.

  Differences from Rocq: whole programs only (no linking); the properties of
  external functions and inline assembly that CompCert states as axioms are
  hypotheses.  The Flocq lemmas used by instruction selection
  (`Float.div_mul_inverse`) and constant propagation (`Float.mul2_add`) are
  proved in `lib/FloatsArith.lean`.  All the optional
  optimisations are proved correct.  Register allocation is proved correct in
  `backend/Allocproof.lean` (`Allocproof.transf_program_correct`).
-/
import CCLib.driver.FrontendCorrect
import CCLib.backend.SelectionproofMain
import CCLib.backend.RTLgenproofMain
import CCLib.backend.Tailcallproof
import CCLib.backend.InliningproofMain
import CCLib.backend.Renumberproof
import CCLib.backend.UnusedglobproofMain
import CCLib.backend.Tunnelingproof
import CCLib.backend.Linearizeproof
import CCLib.backend.CleanupLabelsproof
import CCLib.backend.Debugvarproof
import CCLib.backend.StackingproofStep
import CCLib.aarch64.Asmgenproof
import CCLib.backend.Allocproof
import CCLib.backend.ConstpropproofStep
import CCLib.backend.CSEproofStep
import CCLib.backend.DeadcodeproofMain

namespace CC
namespace Compiler

open Config Smallstep

variable (c : Config)

/-! ## The stages of the back end -/

/-- Cminor → RTL: instruction selection, RTL generation, tail calls,
    inlining and renumbering. -/
def transfCminorToRtl (p : Cminor.Program) : Res RTL.Program :=
  Res.OK p
  @@@ time "Instruction selection" (Selection.selProgram c.selectionOptions)
  @@@ time "RTL generation" (RTLgen.translProgram c.moreLikely)
   @@ totalIf (fun _ => c.optimTailcalls) (time "Tail calls" (Tailcall.transfProgram c.abi))
  @@@ time "Inlining" (Inlining.transfProgram id c.shouldInline)
   @@ time "Renumbering" Renumber.transfProgram

/-- RTL → RTL: the optional optimisations and the removal of unused globals. -/
def transfRtlMiddle (p : RTL.Program) : Res RTL.Program :=
  Res.OK p
   @@ totalIf (fun _ => c.optimConstprop)
        (time "Constant propagation" (Constprop.transfProgram c.constpropOptions c.abi))
   @@ totalIf (fun _ => c.optimConstprop) (time "Renumbering" Renumber.transfProgram)
  @@@ partialIf (fun _ => c.optimCSE) (time "CSE" (CSE.transfProgram c.vaOptions c.abi))
  @@@ partialIf (fun _ => c.optimRedundancy)
        (time "Redundancy elimination" (Deadcode.transfProgram c.vaOptions c.abi))
  @@@ time "Unused globals" Unusedglob.transformProgram

/-- LTL → Asm: branch tunneling, linearization, label cleanup, debugging
    information, Mach generation and Asm generation. -/
def transfLtlProgram (p : LTL.Program) : Res Asm.Program :=
  Res.OK p
   @@ time "Branch tunneling" Tunneling.tunnelProgram
  @@@ time "CFG linearization" (Linearize.transfProgram c.enumerateAux)
   @@ time "Label cleanup" CleanupLabels.transfProgram
  @@@ partialIf (fun _ => c.debug)
        (time "Debugging info for local variables" Debugvar.transfProgram)
  @@@ time "Mach generation" (Stacking.transfProgram c.abi)
  @@@ time "Asm generation" (Asmgen.transfProgram c.asmgenOptions)

theorem applyTotal_eq_applyPartial {A B : Type} (x : Res A) (f : A → B) :
    applyTotal x f = applyPartial x (fun a => .OK (f a)) := by
  cases x <;> rfl

/-- `transf_cminor_program` is the composition of the four stages. -/
theorem transfCminorProgram_eq (p : Cminor.Program) :
    transfCminorProgram c p =
      applyPartial (applyPartial (applyPartial (transfCminorToRtl c p) (transfRtlMiddle c))
        (Allocation.transfProgram c.abi c.regalloc)) (transfLtlProgram c) := by
  have E : transfLtlProgram c = fun q => transfLtlProgram c q := rfl
  rw [E]
  simp only [transfCminorProgram, transfCminorToRtl, applyTotal_eq_applyPartial,
    applyPartial_assoc, applyPartial_OK]
  congr 1; funext a; congr 1; funext b
  simp only [transfRtlProgram, transfRtlMiddle, transfLtlProgram, applyTotal_eq_applyPartial, time,
    applyPartial_assoc, applyPartial_OK]

/-! ## Correctness of the stages -/

/-- Semantic preservation for the LTL → Asm stage. -/
theorem transfLtlProgram_correct (sym : Asm.SymbolSplit) (p : LTL.Program) (tp : Asm.Program)
    (h : transfLtlProgram c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (LTL.semantics c.abi p) (Asm.semantics sym c.abi tp) := by
  obtain ⟨p5, h5, h6⟩ := applyPartial_OK_inv h
  obtain ⟨p4, h4, h5⟩ := applyPartial_OK_inv h5
  obtain ⟨p3, h3, h4⟩ := applyPartial_OK_inv h4
  obtain ⟨p2, h2, h3⟩ := applyTotal_OK_inv h3
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h2
  rw [applyTotal_OK] at h1
  cases h1; subst h3
  simp only [time] at h2 h4 h5 h6
  have S1 := Tunnelingproof.transf_program_correct c.abi p hextx hasmx
  have S2 := Linearizeproof.transf_program_correct c.enumerateAux c.abi h2
  have S3 := CleanupLabelsproof.transf_program_correct c.abi p2
  have S4 : ForwardSimulation (Linear.semantics c.abi (CleanupLabels.transfProgram p2))
      (Linear.semantics c.abi p4) := by
    simp only [partialIf] at h4
    split at h4
    · exact Debugvarproof.transf_program_correct c.abi h4
    · cases h4; exact forward_simulation_refl _
  have S5 := Stackingproof.transf_program_correct c.abi
    (Asmgenproof0.ReturnAddressOffset c.asmgenOptions) h5
    (fun f sg ros k hk => Asmgenproof.return_address_exists c.asmgenOptions f sg ros k hk)
    hext hasm hextp hasmp hextw hasmw
  have S6 := Asmgenproof.transf_program_correct h6 sym c.abi (fun n sg => hextx n sg _)
    (fun n sg => hasmx n sg _)
  exact compose_forward_simulations S1 (compose_forward_simulations S2
    (compose_forward_simulations S3 (compose_forward_simulations S4
      (compose_forward_simulations S5 S6))))

/-- Semantic preservation for the Cminor → RTL stage. -/
theorem transfCminorToRtl_correct (p : Cminor.Program) (tp : RTL.Program)
    (h : transfCminorToRtl c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Cminor.semantics p) (RTL.semantics tp) := by
  obtain ⟨p4, h4, h5⟩ := applyTotal_OK_inv h
  obtain ⟨p3, h3, h4⟩ := applyPartial_OK_inv h4
  obtain ⟨p2, h2, h3⟩ := applyTotal_OK_inv h3
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h2
  rw [applyPartial_OK] at h1
  subst h3 h5
  simp only [time] at h1 h2 h4
  have S1 := Selectionproof.transf_program_correct c.selectionOptions p p1 h1 hextx hasmx
    hextw hasmw
  have S2 := RTLgen.transf_program_correct c.moreLikely p1 p2 h2 hextx hasmx
  have S3 : ForwardSimulation (RTL.semantics p2)
      (RTL.semantics (totalIf (fun _ => c.optimTailcalls) (Tailcall.transfProgram c.abi) p2)) := by
    simp only [totalIf]
    split
    · exact Tailcallproof.transf_program_correct c.abi p2 hextx hasmx
    · exact forward_simulation_refl _
  have S4 := Inlining.transf_program_correct id c.shouldInline _ p4 h4 hext hasm hextp hasmp
  have S5 := Renumberproof.transf_program_correct p4
  exact compose_forward_simulations S1 (compose_forward_simulations S2
    (compose_forward_simulations S3 (compose_forward_simulations S4 S5)))

/-- Semantic preservation for the RTL → RTL stage (constant propagation,
    renumbering, CSE, redundancy elimination and the removal of unused
    globals). -/
theorem transfRtlMiddle_correct (p : RTL.Program) (tp : RTL.Program)
    (h : transfRtlMiddle c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (RTL.semantics p) (RTL.semantics tp) := by
  unfold transfRtlMiddle at h
  obtain ⟨p3, h3, h4⟩ := applyPartial_OK_inv h
  obtain ⟨p2, h2, h3⟩ := applyPartial_OK_inv h3
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h2
  simp only [partialIf, time, applyTotal_OK] at h1 h2 h3 h4
  cases h1
  refine compose_forward_simulations ?_ (Unusedglob.transf_program_correct _ tp h4 hext hasm)
  refine compose_forward_simulations (L2 := RTL.semantics p2) ?_ ?_
  · refine compose_forward_simulations (L2 := RTL.semantics (totalIf (fun _ => c.optimConstprop)
      Renumber.transfProgram (totalIf (fun _ => c.optimConstprop)
        (Constprop.transfProgram c.constpropOptions c.abi) p))) ?_ ?_
    · simp only [totalIf]
      split
      · exact compose_forward_simulations
          (Constpropproof.transf_program_correct hextx hasmx hext hasm hextp hasmp)
          (Renumberproof.transf_program_correct _)
      · exact forward_simulation_refl _
    · split at h2
      · exact CSEproof.transf_program_correct h2 hextx hasmx hext hasm hextp hasmp
      · cases h2; exact forward_simulation_refl _
  · split at h3
    · exact Deadcodeproof.transf_program_correct h3 hextx hasmx hext hasm hextp hasmp
    · cases h3; exact forward_simulation_refl _

/-- Semantic preservation for `transf_cminor_program` (Cminor → Asm). -/
theorem transfCminorProgram_correct (sym : Asm.SymbolSplit) (p : Cminor.Program)
    (tp : Asm.Program) (h : transfCminorProgram c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Cminor.semantics p) (Asm.semantics sym c.abi tp) := by
  rw [transfCminorProgram_eq] at h
  obtain ⟨p3, h3, h4⟩ := applyPartial_OK_inv h
  obtain ⟨p2, h2, h3⟩ := applyPartial_OK_inv h3
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h2
  exact compose_forward_simulations
    (transfCminorToRtl_correct c p p1 h1 hext hasm hextx hasmx hextw hasmw hextp hasmp)
    (compose_forward_simulations (transfRtlMiddle_correct c p1 p2 h2 hext hasm
      hextx hasmx hextp hasmp)
      (compose_forward_simulations
        (Allocproof.transf_program_correct c.abi c.regalloc h3 hextx hasmx hextw hasmw)
        (transfLtlProgram_correct c sym p3 tp h4 hext hasm hextx hasmx hextw hasmw hextp hasmp)))

/-- Semantic preservation for the whole compiler `transf_c_program`, as a
    forward simulation from CompCert C (executed with the compiler's
    evaluation order, `Cstrategy.semantics`) to AArch64 assembly, under the
    same assumptions as `transfCminorProgram_correct`. -/
theorem transfCProgram_correct_strategy (sym : Asm.SymbolSplit) (p : Csyntax.Program)
    (tp : Asm.Program) (h : transfCProgram c p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Cstrategy.semantics p) (Asm.semantics sym c.abi tp) := by
  rw [transfCProgram_eq] at h
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h
  exact compose_forward_simulations
    (transfCFrontend_correct c p p1 h1 hext hasm hextw hasmw hextp hasmp)
    (transfCminorProgram_correct c sym p1 tp h2 hext hasm hextx hasmx
      hextw hasmw hextp hasmp)

end Compiler
end CC
