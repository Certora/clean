/-
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
import CCLib.backend.AllocproofSimFun
import CCLib.common.LinkingFundef

namespace CC
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions Smallstep

section PRESERVATION
variable (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function)
  {prog : RTL.Program} {tprog : LTL.Program}
  (TRANSF : Allocation.transfProgram abi regalloc prog = .OK tprog)
  (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
  (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
  (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
  (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
include TRANSF

include hextx hasmx hextw hasmw in
/-- `Allocproof.step_simulation` -/
theorem step_simulation {S1 : RTL.State} {t : Trace} {S2 : RTL.State}
    (hst : RTL.Step prog.globalenv S1 t S2) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv S1 S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' t S2' ∧
      MatchStates abi regalloc tprog.globalenv S2 S2' := by
  cases hst with
  | Inop _ _ _ _ _ _ _ hc => exact step_simulation_nop abi regalloc hc hm
  | Iop _ _ _ _ _ _ _ _ _ _ _ hc hev => exact step_simulation_op abi regalloc TRANSF hc hev hm
  | Iload _ _ _ _ _ _ _ _ _ _ _ _ _ hc hea hl =>
    exact step_simulation_load abi regalloc TRANSF hc hea hl hm
  | Istore _ _ _ _ _ _ _ _ _ _ _ _ _ hc hea hs =>
    exact step_simulation_store abi regalloc TRANSF hc hea hs hm
  | Icall _ _ _ _ _ _ _ _ _ _ _ _ hc hff hsig =>
    exact step_simulation_call abi regalloc TRANSF hc hff hsig hm
  | Itailcall _ _ _ _ _ _ _ _ _ _ _ hc hff hsig hfree =>
    exact step_simulation_tailcall abi regalloc TRANSF hc hff hsig hfree hm
  | Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hargs hcall =>
    exact step_simulation_builtin abi regalloc TRANSF hextx hasmx hextw hasmw hc hargs hcall hm
  | Icond _ _ _ _ _ _ _ _ _ _ _ _ hc hcond hpc =>
    exact step_simulation_cond abi regalloc hc hcond hpc hm
  | Ijumptable _ _ _ _ _ _ _ _ _ _ hc harg hnth =>
    exact step_simulation_jumptable abi regalloc hc harg hnth hm
  | Ireturn _ _ _ _ _ _ _ _ hc hfree => exact step_simulation_return abi regalloc hc hfree hm
  | function_internal _ _ _ _ _ _ _ halloc =>
    exact step_simulation_internal abi regalloc halloc hm
  | function_external _ _ _ _ _ _ _ hcall =>
    exact step_simulation_external abi regalloc TRANSF hextx hasmx hextw hasmw hcall hm
  | «return» => exact step_simulation_return_state abi regalloc hm

/-- `Allocproof.initial_states_simulation` -/
theorem initial_states_simulation {st1 : RTL.State} (h : RTL.InitialState prog st1) :
    ∃ st2, LTL.InitialState tprog st2 ∧ MatchStates abi regalloc tprog.globalenv st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, FIND, TR⟩ := function_ptr_translated abi regalloc TRANSF hf
    have SIG : LTL.funsig tf = signature_main := (sig_function_translated abi regalloc TR).trans hsig
    refine ⟨_, .intro b tf m0 ?_ ?_ FIND SIG, .call _ _ _ _ _ _ _ _ ?_ TR ?_ (fun _ _ => rfl)
      (Mem.extends_refl _) ?_⟩
    · exact (init_mem_transf_partial TRANSF).trans hm
    · rw [(match_transform_partial_program TRANSF).main_eq, symbols_preserved abi regalloc TRANSF]
      exact hs
    · exact .nil _ (by rw [SIG]; rfl)
    · rw [SIG, locArguments_main]; exact .nil
    · rw [SIG]; trivial

omit TRANSF in
/-- `Allocproof.final_states_simulation` -/
theorem final_states_simulation {st1 : RTL.State} {st2 : LTL.State} {r : Integers.Int}
    (hm : MatchStates abi regalloc tprog.globalenv st1 st2) (h : RTL.FinalState st1 r) :
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
theorem wt_prog : WtProgram abi prog := by
  intro i f hin
  obtain ⟨tf, htf⟩ := matchDefs_gfun (match_transform_partial_program TRANSF).defs hin
  cases f with
  | External ef => exact .external ef
  | Internal f =>
    obtain ⟨tf', _, TF⟩ := transfFundef_internal abi regalloc htf
    cases transf_function_inv TF with
    | intro env _ _ _ _ _ WTF _ _ _ _ _ _ _ _ _ => exact .internal f env WTF

include hextx hasmx hextw hasmw in
/-- `Allocproof.transf_program_correct`: register allocation preserves the
    semantics of programs (forward simulation from RTL to LTL), for any
    external register allocator `regalloc`. -/
theorem transf_program_correct :
    Smallstep.ForwardSimulation (RTL.semantics prog) (LTL.semantics abi tprog) :=
  Smallstep.forward_simulation_plus (L1 := RTL.semantics prog) (L2 := LTL.semantics abi tprog)
    (MatchStates abi regalloc tprog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved abi regalloc TRANSF])
    (fun _ h => initial_states_simulation abi regalloc TRANSF h)
    (fun _ _ _ hm h => final_states_simulation abi regalloc hm h)
    (fun _ _ _ hst _ hm => step_simulation abi regalloc TRANSF hextx hasmx hextw hasmw hst hm)

end PRESERVATION

/-! ## Linking (`match_prog`, `transf_program_match`, `TransfAllocLink`) -/

/-- `Allocproof.match_prog`, as a relation that commutes with linking
    (`MatchProg` above is the whole-program equation). -/
def MatchProgLink (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function)
    (p : RTL.Program) (tp : LTL.Program) : Prop :=
  Linking.MatchProgramCtx (fun _ f tf => Allocation.transfFundef abi regalloc f = .OK tf) Eq p tp

/-- `Allocproof.transf_program_match` -/
theorem transf_program_match (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function)
    {p : RTL.Program} {tp : LTL.Program}
    (h : Allocation.transfProgram abi regalloc p = .OK tp) : MatchProgLink abi regalloc p tp :=
  Linking.match_transform_partial_program h

/-- `Allocproof.TransfAllocLink` -/
instance transfAllocLink (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function) :
    Linking.TransfLink (MatchProgLink abi regalloc) :=
  Linking.transfPartialLinkAST _

/-- `Allocproof.transf_program_correct`, stated for `match_prog`. -/
theorem transf_program_correct_match (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function)
    {p : RTL.Program} {tp : LTL.Program} (h : MatchProgLink abi regalloc p tp)
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    Smallstep.ForwardSimulation (RTL.semantics p) (LTL.semantics abi tp) :=
  transf_program_correct abi regalloc (Linking.transformPartialProgram_of_match h)
    hext hasm hextw hasmw

end Allocproof
end CC
