/-
  Correctness proof for x86-64 code generation, final part — port of the
  end of `x86/Asmgenproof.v`: `step_simulation` (dispatching to the
  per-instruction cases of `AsmgenproofStep1` and `AsmgenproofStep2`),
  `transf_initial_states`, `transf_final_states` and the main theorem
  `transf_program_correct`, a forward simulation from Mach to Asm.

  Differences from Rocq: the Windows-ABI flag `win64` of the Mach and Asm
  semantics is an explicit argument; the memory-extension property of
  external functions and inline assembly, which CompCert takes as an axiom
  (`external_functions_properties`, `inline_assembly_properties`), is a pair
  of hypotheses (`hext`, `hasm`).
-/
import CCLib.x86.AsmgenproofStep2

namespace CC
namespace X86
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Smallstep Conventions1

section PRESERVATION
variable {prog : Mach.Program} {tprog : Asm.Program}
  (TRANSF : MatchProg prog tprog) (win64 : Bool)
include TRANSF

/-- `Asmgenproof.step_simulation` -/
theorem step_simulation
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv))
    {S1 : Mach.State} {t : Trace} {S2 : Mach.State}
    (hst : Mach.Step win64 ReturnAddressOffset prog.globalenv S1 t S2)
    {S1' : Asm.State} (MS : MatchStates prog.globalenv S1 S1') :
    (∃ S2', Smallstep.Plus (Asm.Step win64 tprog.globalenv) S1' t S2' ∧
        MatchStates prog.globalenv S2 S2') ∨
      (measure S2 < measure S1 ∧ t = E0 ∧ MatchStates prog.globalenv S2 S1') := by
  cases hst with
  | Mlabel => exact .inl (step_Mlabel TRANSF win64 MS)
  | Mgetstack _ _ _ _ _ _ _ _ _ _ H => exact .inl (step_Mgetstack TRANSF win64 MS H)
  | Msetstack _ _ _ _ _ _ _ _ _ _ _ H E => subst E; exact .inl (step_Msetstack TRANSF win64 MS H)
  | Mgetparam _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 E =>
    subst E; exact .inl (step_Mgetparam TRANSF win64 MS H0 H1 H2)
  | Mop _ _ _ _ _ _ _ _ _ _ _ H E => subst E; exact .inl (step_Mop TRANSF win64 MS H)
  | Mload _ _ _ _ _ _ _ _ _ _ _ _ _ H H1 E =>
    subst E; exact .inl (step_Mload TRANSF win64 MS H H1)
  | Mstore _ _ _ _ _ _ _ _ _ _ _ _ _ H H1 E =>
    subst E; exact .inl (step_Mstore TRANSF win64 MS H H1)
  | Mcall _ _ _ _ _ _ _ _ _ _ _ H H0 H1 => exact .inl (step_Mcall TRANSF win64 MS H H0 H1)
  | Mtailcall _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 =>
    exact .inl (step_Mtailcall TRANSF win64 MS H H0 H1 H2 H3)
  | Mbuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H1 E =>
    subst E; exact .inl (step_Mbuiltin TRANSF win64 hext hasm MS H H1)
  | Mgoto _ _ _ _ _ _ _ _ _ H H1 => exact .inl (step_Mgoto TRANSF win64 MS H H1)
  | Mcond_true _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 E =>
    subst E; exact .inl (step_Mcond_true TRANSF win64 MS H H0 H1)
  | Mcond_false _ _ _ _ _ _ _ _ _ _ H E => subst E; exact .inl (step_Mcond_false TRANSF win64 MS H)
  | Mjumptable _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 E =>
    subst E; exact .inl (step_Mjumptable TRANSF win64 MS H H0 H1 H2)
  | Mreturn _ _ _ _ _ _ _ _ _ H0 H1 H2 H3 => exact .inl (step_Mreturn TRANSF win64 MS H0 H1 H2 H3)
  | function_internal _ _ _ _ _ _ _ _ _ _ H H1 H2 H3 E =>
    subst E; exact .inl (step_internal TRANSF win64 MS H H1 H2 H3)
  | function_external _ _ _ _ _ _ _ _ _ _ H H1 H2 E =>
    subst E; exact .inl (step_external TRANSF win64 hext hasm MS H H1 H2)
  | «return» =>
    exact .inr ⟨by simp [measure], rfl, step_return MS⟩

omit win64 in
/-- `Asmgenproof.transf_initial_states` -/
theorem transf_initial_states {st1 : Mach.State} (h : Mach.InitialState prog st1) :
    ∃ st2, Asm.InitialState tprog st2 ∧ MatchStates prog.globalenv st1 st2 := by
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

omit TRANSF win64 in
/-- `Asmgenproof.transf_final_states` -/
theorem transf_final_states {st1 : Mach.State} {st2 : Asm.State} {r : Integers.Int}
    (hm : MatchStates prog.globalenv st1 st2) (h : Mach.FinalState st1 r) :
    Asm.FinalState st2 r := by
  cases h with
  | intro rs m r0 _ H1 H2 =>
    cases hm with
    | ret _ _ _ m' rs' STACKS MEXT AG ATPC =>
      refine .intro _ _ _ ATPC ?_
      have hr0 : r0 = .AX := by
        have E : locResult signature_main = .One .AX := rfl
        rw [E] at H1
        cases H1; rfl
      subst hr0
      have LD := preg_val AG .AX
      rw [H2] at LD
      show rs' (pregOf .AX) = _
      generalize rs' (pregOf .AX) = v at LD ⊢
      cases LD; rfl

/-- `Asmgenproof.transf_program_correct`: x86-64 code generation is a forward
    simulation from Mach (with the return-address relation induced by the code
    generator) to Asm. -/
theorem transf_program_correct
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv)) :
    ForwardSimulation (Mach.semantics win64 ReturnAddressOffset prog)
      (Asm.semantics win64 tprog) :=
  forward_simulation_star (L1 := Mach.semantics win64 ReturnAddressOffset prog)
    (L2 := Asm.semantics win64 tprog) (MatchStates prog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved TRANSF])
    (fun _ h => transf_initial_states TRANSF h)
    (fun _ _ _ hm h => transf_final_states hm h)
    measure
    (fun _ _ _ hst _ hm => step_simulation TRANSF win64 hext hasm hst hm)

end PRESERVATION

end Asmgenproof
end X86
end CC
