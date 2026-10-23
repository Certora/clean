/-
  [x86-64 instance of `CCLib/backend/Allocproof.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness of register allocation — end of `backend/Allocproof.v`:
  `step_simulation`, `initial_states_simulation`, `final_states_simulation`,
  `wt_prog` and **`transf_program_correct`**.

  The proof is split over several files, following the structure of
  `backend/Allocproof.v`:
  * `AllocproofShape` — `match_prog`, `expand_block_shape` and the soundness
    of the structural checks;
  * `AllocproofEqs` — the `satisf` relation and its preservation lemmas;
  * `AllocproofCall` — calls, builtins, the dataflow analysis, `transf_function_inv`;
  * `AllocproofStep` — `exec_moves`, `match_stackframes`, `match_states`;
  * `AllocproofSimBasic`, `AllocproofSimOp`, `AllocproofSimCall`,
    `AllocproofSimFun` — the global environment and the cases of
    `step_simulation`;
  * this file — the simulation theorem.

  As elsewhere in the port, CompCert's axioms `external_call_mem_extends` and
  `external_call_well_typed` for the (uninterpreted) external functions and
  inline assembly are explicit hypotheses (`hextx`, `hasmx`, `hextw`,
  `hasmw`).  Since the simulation relation carries the typing information, the
  RTL typing invariant `wt_state` is not needed; `wt_prog` is still proved.
-/
import CCLib.x86.AllocproofSimFun

namespace CC
namespace X86

/- `Archi.win64` (a Rocq `Parameter`): whether the Windows x86-64 ABI is used. -/
variable (win64 : Bool)
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions Smallstep

section PRESERVATION
variable (win64 : Bool) (regalloc : RTL.Function → Res LTL.Function)
  {prog : RTL.Program} {tprog : LTL.Program}
  (TRANSF : Allocation.transfProgram win64 regalloc prog = .OK tprog)
  (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
  (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
  (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
  (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
include TRANSF

include hextx hasmx hextw hasmw in
/-- `Allocproof.step_simulation` -/
theorem step_simulation {S1 : RTL.State} {t : Trace} {S2 : RTL.State}
    (hst : RTL.Step prog.globalenv S1 t S2) {S1' : LTL.State}
    (hm : MatchStates win64 regalloc tprog.globalenv S1 S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step win64 tprog.globalenv) S1' t S2' ∧
      MatchStates win64 regalloc tprog.globalenv S2 S2' := by
  cases hst with
  | Inop _ _ _ _ _ _ _ hc => exact step_simulation_nop win64 regalloc hc hm
  | Iop _ _ _ _ _ _ _ _ _ _ _ hc hev => exact step_simulation_op win64 regalloc TRANSF hc hev hm
  | Iload _ _ _ _ _ _ _ _ _ _ _ _ _ hc hea hl =>
    exact step_simulation_load win64 regalloc TRANSF hc hea hl hm
  | Istore _ _ _ _ _ _ _ _ _ _ _ _ _ hc hea hs =>
    exact step_simulation_store win64 regalloc TRANSF hc hea hs hm
  | Icall _ _ _ _ _ _ _ _ _ _ _ _ hc hff hsig =>
    exact step_simulation_call win64 regalloc TRANSF hc hff hsig hm
  | Itailcall _ _ _ _ _ _ _ _ _ _ _ hc hff hsig hfree =>
    exact step_simulation_tailcall win64 regalloc TRANSF hc hff hsig hfree hm
  | Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hargs hcall =>
    exact step_simulation_builtin win64 regalloc TRANSF hextx hasmx hextw hasmw hc hargs hcall hm
  | Icond _ _ _ _ _ _ _ _ _ _ _ _ hc hcond hpc =>
    exact step_simulation_cond win64 regalloc hc hcond hpc hm
  | Ijumptable _ _ _ _ _ _ _ _ _ _ hc harg hnth =>
    exact step_simulation_jumptable win64 regalloc hc harg hnth hm
  | Ireturn _ _ _ _ _ _ _ _ hc hfree => exact step_simulation_return win64 regalloc hc hfree hm
  | function_internal _ _ _ _ _ _ _ halloc =>
    exact step_simulation_internal win64 regalloc halloc hm
  | function_external _ _ _ _ _ _ _ hcall =>
    exact step_simulation_external win64 regalloc TRANSF hextx hasmx hextw hasmw hcall hm
  | «return» => exact step_simulation_return_state win64 regalloc hm

/-- `Allocproof.initial_states_simulation` -/
theorem initial_states_simulation {st1 : RTL.State} (h : RTL.InitialState prog st1) :
    ∃ st2, LTL.InitialState tprog st2 ∧ MatchStates win64 regalloc tprog.globalenv st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, FIND, TR⟩ := function_ptr_translated win64 regalloc TRANSF hf
    have SIG : LTL.funsig tf = signature_main := (sig_function_translated win64 regalloc TR).trans hsig
    refine ⟨_, .intro b tf m0 ?_ ?_ FIND SIG, .call _ _ _ _ _ _ _ _ ?_ TR ?_ (fun _ _ => rfl)
      (Mem.extends_refl _) ?_⟩
    · exact (init_mem_transf_partial TRANSF).trans hm
    · rw [(match_transform_partial_program TRANSF).main_eq, symbols_preserved win64 regalloc TRANSF]
      exact hs
    · exact .nil _ (by rw [SIG]; rfl)
    · rw [SIG, locArguments_main]; exact .nil
    · rw [SIG]; trivial

omit TRANSF in
/-- `Allocproof.final_states_simulation` -/
theorem final_states_simulation {st1 : RTL.State} {st2 : LTL.State} {r : Integers.Int}
    (hm : MatchStates win64 regalloc tprog.globalenv st1 st2) (h : RTL.FinalState st1 r) :
    LTL.FinalState st2 r := by
  cases h with
  | intro r m =>
    cases hm with
    | ret _ _ _ ts ls m' sg STK LD _ _ _ =>
      cases STK with
      | nil _ hres =>
        refine .intro _ _ _ ?_
        rw [← locResult_exten (s1 := sg) (by rw [hres]; rfl)]
        generalize Locmap.getpair ((locResult sg).map Loc.R) ls = w at LD
        cases LD; rfl

/-- `Allocproof.wt_prog`: every function of a program accepted by the register
    allocator is well typed. -/
theorem wt_prog : WtProgram win64 prog := by
  intro i f hin
  obtain ⟨tf, htf⟩ := matchDefs_gfun (match_transform_partial_program TRANSF).defs hin
  cases f with
  | External ef => exact .external ef
  | Internal f =>
    obtain ⟨tf', _, TF⟩ := transfFundef_internal win64 regalloc htf
    cases transf_function_inv TF with
    | intro env _ _ _ _ _ WTF _ _ _ _ _ _ _ _ _ => exact .internal f env WTF

include hextx hasmx hextw hasmw in
/-- `Allocproof.transf_program_correct`: register allocation preserves the
    semantics of programs (forward simulation from RTL to LTL), for any
    external register allocator `regalloc`. -/
theorem transf_program_correct :
    Smallstep.ForwardSimulation (RTL.semantics prog) (LTL.semantics win64 tprog) :=
  Smallstep.forward_simulation_plus (L1 := RTL.semantics prog) (L2 := LTL.semantics win64 tprog)
    (MatchStates win64 regalloc tprog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved win64 regalloc TRANSF])
    (fun _ h => initial_states_simulation win64 regalloc TRANSF h)
    (fun _ _ _ hm h => final_states_simulation win64 regalloc hm h)
    (fun _ _ _ hst _ hm => step_simulation win64 regalloc TRANSF hextx hasmx hextw hasmw hst hm)

end PRESERVATION

end Allocproof
end X86
end CC
