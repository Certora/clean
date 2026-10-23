/-
  Correctness proof for AArch64 code generation, final part — port of the
  end of `aarch64/Asmgenproof.v`: `step_simulation` (dispatching to the
  per-instruction cases of `AsmgenproofStep1` and `AsmgenproofStep2`),
  `transf_initial_states`, `transf_final_states` and the main theorem
  `transf_program_correct`, a forward simulation from Mach to Asm.

  Differences from Rocq: the `Asmgen.Options`, the `Asm.SymbolSplit` linker
  parameter and the ABI are explicit arguments; the memory-extension
  property of external functions and inline assembly, which CompCert takes
  as an axiom, is a pair of hypotheses (`hext`, `hasm`).
-/
import CCLib.aarch64.AsmgenproofStep2
import CCLib.common.LinkingFundef

namespace CC
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Smallstep Conventions1

section PRESERVATION
variable {o : Options} {prog : Mach.Program} {tprog : Asm.Program}
  (TRANSF : MatchProg o prog tprog) (sym : SymbolSplit) (abi : AbiKind)
include TRANSF

/-- `Asmgenproof.step_simulation` -/
theorem step_simulation
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv))
    {S1 : Mach.State} {t : Trace} {S2 : Mach.State}
    (hst : Mach.Step abi (ReturnAddressOffset o) prog.globalenv S1 t S2)
    {S1' : Asm.State} (MS : MatchStates o prog.globalenv S1 S1') :
    (∃ S2', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) S1' t S2' ∧
        MatchStates o prog.globalenv S2 S2') ∨
      (measure S2 < measure S1 ∧ t = E0 ∧ MatchStates o prog.globalenv S2 S1') := by
  cases hst with
  | Mlabel => exact .inl (step_Mlabel TRANSF sym abi MS)
  | Mgetstack _ _ _ _ _ _ _ _ _ _ H => exact .inl (step_Mgetstack TRANSF sym abi MS H)
  | Msetstack _ _ _ _ _ _ _ _ _ _ _ H E => subst E; exact .inl (step_Msetstack TRANSF sym abi MS H)
  | Mgetparam _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 E =>
    subst E; exact .inl (step_Mgetparam TRANSF sym abi MS H0 H1 H2)
  | Mop _ _ _ _ _ _ _ _ _ _ _ H E => subst E; exact .inl (step_Mop TRANSF sym abi MS H)
  | Mload _ _ _ _ _ _ _ _ _ _ _ _ _ H H1 E =>
    subst E; exact .inl (step_Mload TRANSF sym abi MS H H1)
  | Mstore _ _ _ _ _ _ _ _ _ _ _ _ _ H H1 E =>
    subst E; exact .inl (step_Mstore TRANSF sym abi MS H H1)
  | Mcall _ _ _ _ _ _ _ _ _ _ _ H H0 H1 => exact .inl (step_Mcall TRANSF sym abi MS H H0 H1)
  | Mtailcall _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 =>
    exact .inl (step_Mtailcall TRANSF sym abi MS H H0 H1 H2 H3)
  | Mbuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H1 E =>
    subst E; exact .inl (step_Mbuiltin TRANSF sym abi hext hasm MS H H1)
  | Mgoto _ _ _ _ _ _ _ _ _ H H1 => exact .inl (step_Mgoto TRANSF sym abi MS H H1)
  | Mcond_true _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 E =>
    subst E; exact .inl (step_Mcond_true TRANSF sym abi MS H H0 H1)
  | Mcond_false _ _ _ _ _ _ _ _ _ _ H E => subst E; exact .inl (step_Mcond_false TRANSF sym abi MS H)
  | Mjumptable _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 E =>
    subst E; exact .inl (step_Mjumptable TRANSF sym abi MS H H0 H1 H2)
  | Mreturn _ _ _ _ _ _ _ _ _ H0 H1 H2 H3 => exact .inl (step_Mreturn TRANSF sym abi MS H0 H1 H2 H3)
  | function_internal _ _ _ _ _ _ _ _ _ _ H H1 H2 H3 E =>
    subst E; exact .inl (step_internal TRANSF sym abi MS H H1 H2 H3)
  | function_external _ _ _ _ _ _ _ _ _ _ H H1 H2 E =>
    subst E; exact .inl (step_external TRANSF sym abi hext hasm MS H H1 H2)
  | «return» =>
    exact .inr ⟨by simp [measure], rfl, step_return MS⟩

/-- `Asmgenproof.transf_initial_states` -/
theorem transf_initial_states {st1 : Mach.State} (h : Mach.InitialState prog st1) :
    ∃ st2, Asm.InitialState tprog st2 ∧ MatchStates o prog.globalenv st1 st2 := by
  cases h with
  | intro fb m0 H0 H1 =>
    refine ⟨_, .intro m0 (by rw [init_mem_transf_partial TRANSF]; exact H0), ?_⟩
    have hmain : Genv.symbolAddress tprog.globalenv tprog.prog_main Integers.Ptrofs.zero =
        .Vptr fb Integers.Ptrofs.zero := by
      rw [(match_transform_partial_program TRANSF).main_eq]
      simp [Genv.symbolAddress, symbols_preserved TRANSF, H1]
    refine .call _ _ _ _ _ _ MatchStack.nil (Mem.extends_refl _) ?_ ?_ ?_
    · refine ⟨?_, ?_, fun r => .undef _⟩
      · simp [Mach.parentSp, Regset.set]
      · simp [Mach.parentSp, Val.Vnullptr]
    · simp [Regset.set, hmain]
    · simp [Mach.parentRa, Regset.set]

omit TRANSF in
/-- `Asmgenproof.transf_final_states` -/
theorem transf_final_states {st1 : Mach.State} {st2 : Asm.State} {r : Integers.Int}
    (hm : MatchStates o prog.globalenv st1 st2) (h : Mach.FinalState st1 r) :
    Asm.FinalState st2 r := by
  cases h with
  | intro rs m r0 _ H1 H2 =>
    cases hm with
    | ret _ _ _ m' rs' STACKS MEXT AG ATPC =>
      refine .intro _ _ _ ATPC ?_
      have hr0 : r0 = .R0 := by
        have E : locResult signature_main = .One .R0 := rfl
        rw [E] at H1
        cases H1; rfl
      subst hr0
      have LD := preg_val AG .R0
      rw [H2] at LD
      show rs' (pregOf .R0) = _
      generalize rs' (pregOf .R0) = v at LD ⊢
      cases LD; rfl

/-- `Asmgenproof.transf_program_correct`: AArch64 code generation is a forward
    simulation from Mach (with the return-address relation induced by the code
    generator) to Asm. -/
theorem transf_program_correct
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv)) :
    ForwardSimulation (Mach.semantics abi (ReturnAddressOffset o) prog)
      (Asm.semantics sym abi tprog) :=
  forward_simulation_star (L1 := Mach.semantics abi (ReturnAddressOffset o) prog)
    (L2 := Asm.semantics sym abi tprog) (MatchStates o prog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved TRANSF])
    (fun _ h => transf_initial_states TRANSF h)
    (fun _ _ _ hm h => transf_final_states hm h)
    measure
    (fun _ _ _ hst _ hm => step_simulation TRANSF sym abi hext hasm hst hm)

end PRESERVATION

/-! ## Linking (`match_prog`, `transf_program_match`, `TransfAsmgenLink`) -/

/-- `Asmgenproof.match_prog`, as a relation that commutes with linking
    (`MatchProg` is the whole-program equation). -/
def MatchProgLink (o : Options) (p : Mach.Program) (tp : Asm.Program) : Prop :=
  Linking.MatchProgramCtx (fun _ f tf => Asmgen.transfFundef o f = .OK tf) Eq p tp

/-- `Asmgenproof.transf_program_match` -/
theorem transf_program_match_link {o : Options} {p : Mach.Program} {tp : Asm.Program}
    (h : Asmgen.transfProgram o p = .OK tp) : MatchProgLink o p tp :=
  Linking.match_transform_partial_program h

/-- `Asmgenproof.TransfAsmgenLink` -/
instance transfAsmgenLink (o : Options) : Linking.TransfLink (MatchProgLink o) :=
  Linking.transfPartialLinkAST _

/-- `Asmgenproof.transf_program_correct`, stated for `match_prog`. -/
theorem transf_program_correct_match {o : Options} {p : Mach.Program} {tp : Asm.Program}
    (h : MatchProgLink o p tp) (sym : SymbolSplit) (abi : AbiKind)
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv p.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv p.globalenv)) :
    ForwardSimulation (Mach.semantics abi (ReturnAddressOffset o) p)
      (Asm.semantics sym abi tp) :=
  transf_program_correct (Linking.transformPartialProgram_of_match h) sym abi hext hasm

end Asmgenproof
end CC
