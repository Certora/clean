/-
  RTL function inlining: semantic preservation — port of
  `backend/Inliningproof.v`, part 5: initial and final states and the main
  theorem `transf_program_correct`.
-/
import CCLib.backend.InliningproofStep
import CCLib.common.LinkingFundef

namespace CC
namespace Inlining

open Op RTL Smallstep
open Integers (Ptrofs)

section INITFINAL
variable {prog tprog : RTL.Program}
  (TRANSF : MatchProgFenv prog tprog)
include TRANSF

/-- `Inliningproof.transf_initial_states` -/
theorem transf_initial_states {st1 : RTL.State} (h : RTL.InitialState prog st1) :
    ∃ st2, RTL.InitialState tprog st2 ∧ MatchStates prog st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, A, B⟩ := MatchProgram.find_funct_ptr TRANSF hf
    have MG : MatchGlobalenvs prog.globalenv (Mem.flatInj m0.nextblock) m0.nextblock :=
      { domain := fun b h => by simp [Mem.flatInj, h]
        image := fun b1 b2 delta hf' _ => (Mem.flatInj_some hf').1.symm
        symbols := fun id b hs' => lt_of_validBlock (Genv.findSymbol_not_fresh hm hs')
        functions := fun b fd hf' => lt_of_validBlock (Genv.findFunctPtr_not_fresh hm hf')
        varinfos := fun b gv hv => lt_of_validBlock (Genv.findVarInfo_not_fresh hm hv) }
    refine ⟨_, .intro b tf m0 ?_ ?_ A ?_,
      .call _ _ _ _ _ _ _ _ _ (.nil _ _ MG (Nat.le_refl _)) B .nil (Genv.initmem_inject hm)⟩
    · exact (MatchProgram.init_mem TRANSF).trans hm
    · rw [TRANSF.main_eq, symbols_preserved TRANSF]
      exact hs
    · obtain ⟨_, _, B'⟩ := B
      rw [sig_function_translated B']; exact hsig

end INITFINAL

/-- `Inliningproof.transf_final_states` -/
theorem transf_final_states {prog : RTL.Program} {st1 st2 : RTL.State}
    {r : Integers.Int} (hm : MatchStates prog st1 st2) (h : RTL.FinalState st1 r) :
    RTL.FinalState st2 r := by
  cases h with
  | intro r m =>
    cases hm with
    | ret _ _ _ _ _ _ _ MS VINJ _ =>
      cases match_stacks_empty MS rfl
      cases VINJ
      exact .intro _ _
    | return_regular _ _ _ _ _ _ _ _ _ _ _ _ _ MS RET _ _ _ _ _ _ _ _ =>
      rw [(match_stacks_inside_empty MS rfl).2] at RET
      cases RET

/-- `Inliningproof.transf_program_correct`: function inlining preserves the
    semantics of RTL programs (forward simulation), for any inlining heuristic
    (`inliningAnalysis`, `shouldInline`).

    The hypotheses describe the external functions and inline assembly, whose
    semantics the port leaves uninterpreted: compatibility with memory
    injections (`hext`, `hasm`, i.e. `ec_mem_inject`) and the memory properties
    `ec_valid_block`, `ec_max_perm`, `ec_readonly`, `ec_trace_length`
    (`hextp`, `hasmp`).  CompCert assumes both by axiom
    (`external_functions_properties`, `inline_assembly_properties`). -/
theorem transf_program_correct_fenv {prog tprog : RTL.Program}
    (TRANSF : MatchProgFenv prog tprog)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (RTL.semantics prog) (RTL.semantics tprog) :=
  forward_simulation_star (L1 := RTL.semantics prog) (L2 := RTL.semantics tprog)
    (MatchStates prog)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved TRANSF])
    (fun _ h => transf_initial_states TRANSF h)
    (fun _ _ _ hm h => transf_final_states hm h)
    measure
    (fun _ _ _ hst _ hm => step_simulation TRANSF hext hasm hextp hasmp hst hm)

section LINKING
variable {Info : Type} (inliningAnalysis : RTL.Program → Info)
  (shouldInline : Info → Ident → RTL.Function → Bool)

/-- `Inliningproof.match_prog`: every function is inlined with the function
    environment of its compilation unit. -/
def MatchProgLink (p tp : RTL.Program) : Prop :=
  Linking.MatchProgramCtx
    (fun cu f tf => transfFundef (funenvProgram inliningAnalysis shouldInline cu) f = .OK tf)
    Eq p tp

/-- `Inliningproof.transf_program_match` -/
theorem transf_program_match {p tp : RTL.Program}
    (h : transfProgram inliningAnalysis shouldInline p = .OK tp) :
    MatchProgLink inliningAnalysis shouldInline p tp :=
  Linking.match_transform_partial_program_contextual _ h (fun _ _ e => e)

/-- `Inliningproof.TransfInliningLink` -/
instance transfInliningLink : Linking.TransfLink (MatchProgLink inliningAnalysis shouldInline) :=
  Linking.transfPartialContextualLinkAST (fun fenv => transfFunction fenv)
    (fun cu => funenvProgram inliningAnalysis shouldInline cu)

/-- `fenv_compat` is preserved when the compilation unit is linked into a
    larger program. -/
theorem fenvCompat_linkorder {cu prog : RTL.Program} {fenv : Funenv}
    (hc : FenvCompat cu fenv) (hl : Linker.linkorder cu prog) : FenvCompat prog fenv := by
  intro id f hf
  obtain ⟨gd, P, Q⟩ := Linking.prog_defmap_linkorder hl (hc id f hf)
  change Linking.LinkorderDef _ _ at Q
  cases Q with
  | gfun h2 =>
    change Linking.LinkorderASTFundef _ _ at h2
    cases h2 with
    | refl => exact P

theorem matchProgFenv_of_link {p tp : RTL.Program}
    (h : MatchProgLink inliningAnalysis shouldInline p tp) : MatchProgFenv p tp := by
  have h' := Linking.MatchProgramGen.toMatchProgram h
  refine ⟨Genv.MatchDefs.imp (fun f1 f2 ⟨cu, hl, e⟩ => ?_) (fun _ _ e => e) h'.defs,
    h'.main_eq, h'.public_eq⟩
  exact ⟨_, fenvCompat_linkorder (funenv_program_compat inliningAnalysis shouldInline cu) hl, e⟩

/-- `Inliningproof.transf_program_correct`, for `match_prog` (separate
    compilation). -/
theorem transf_program_correct_match {prog tprog : RTL.Program}
    (TRANSF : MatchProgLink inliningAnalysis shouldInline prog tprog)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (RTL.semantics prog) (RTL.semantics tprog) :=
  transf_program_correct_fenv (matchProgFenv_of_link inliningAnalysis shouldInline TRANSF)
    hext hasm hextp hasmp

end LINKING

/-- `Inliningproof.transf_program_correct` -/
theorem transf_program_correct {Info : Type} (inliningAnalysis : RTL.Program → Info)
    (shouldInline : Info → Ident → RTL.Function → Bool) (prog tprog : RTL.Program)
    (TRANSF : transfProgram inliningAnalysis shouldInline prog = .OK tprog)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (RTL.semantics prog) (RTL.semantics tprog) :=
  transf_program_correct_match inliningAnalysis shouldInline
    (transf_program_match inliningAnalysis shouldInline TRANSF) hext hasm hextp hasmp

end Inlining
end CC
