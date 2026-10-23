/-
  [RISC-V instance of `CCLib/backend/DeadcodeproofMain.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Elimination of unneeded computations over RTL: correctness proof — port of
  the end of CompCert `backend/Deadcodeproof.v`: `step_simulation`,
  `transf_initial_states`, `transf_final_states` and
  `transf_program_correct`.

  The individual cases of `step_simulation` are in `DeadcodeproofStep.lean`
  (all instructions except `Ibuiltin`) and `DeadcodeproofBuiltin.lean`
  (`Ibuiltin`).  As in Rocq, the simulation is proved with
  `forward_simulation_eventually_star`, the invariant being the conjunction of
  `match_states` and the soundness of the value analysis (`sound_state`).
-/
import CCLib.riscV.DeadcodeproofBuiltin

namespace CC
namespace RiscV
namespace Deadcodeproof

open ValueDomain ValueAnalysis RTL NeedDomain NeedOp Deadcode Op Smallstep
open Integers (Ptrofs)

section PRESERVATION
variable {o : ValueAOp.Options} {prog : RTL.Program}
variable {tprog : RTL.Program} (TRANSF : Deadcode.transfProgram o  prog = .OK tprog)
include TRANSF

/-- `Deadcodeproof.step_simulation` -/
theorem step_simulation
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    {s1 : RTL.State} {t : Trace} {s1' : RTL.State} (hst : RTL.Step prog.globalenv s1 t s1')
    {s2 : RTL.State} (MS : MatchStates o  prog s1 s2) (SS : SoundState o  prog s1) :
    (∃ s2', RTL.Step tprog.globalenv s2 t s2' ∧ MatchStates o  prog s1' s2') ∨
    (∃ s2' n, Smallstep.Plus (RTL.Step tprog.globalenv) s2 t s2' ∧
      Smallstep.Eventually (RTL.Step prog.globalenv) RTL.FinalState n s1'
        (fun s1'' => MatchStates o  prog s1'' s2')) := by
  have hsenv := senv_preserved TRANSF
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  cases hst with
  | Inop s f sp pc rs m pc' hc =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Inop (tprog := tprog) STACKS AN ENV MEM hc)
  | Iop s f sp pc rs m op args res pc' v hc hv =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Iop TRANSF STACKS AN ENV MEM hc hv)
  | Iload s f sp pc rs m chunk addr args dst pc' a v hc ha hl =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Iload TRANSF STACKS AN ENV MEM SS hc ha hl)
  | Istore s f sp pc rs m chunk addr args src pc' a m' hc ha hs =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Istore TRANSF STACKS AN ENV MEM SS hc ha hs)
  | Icall s f sp pc rs m sig ros args res pc' fd hc hf hsig =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact step_Icall TRANSF STACKS AN ENV MEM hc hf hsig
  | Itailcall s f stk pc rs m sig ros args fd m' hc hf hsig hfree =>
    cases MS with
    | regular _ _ _ _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Itailcall TRANSF STACKS ENV MEM hc hf hsig hfree)
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m' hc hargs hcall =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Ibuiltin TRANSF hext hasm STACKS AN ENV MEM SS hc hargs hcall)
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hc hcond hpc =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      subst hpc
      exact .inl (step_Icond (tprog := tprog) STACKS AN ENV MEM hc hcond)
  | Ijumptable s f sp pc rs m arg tbl n pc' hc hn hl =>
    cases MS with
    | regular _ _ sp _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Ijumptable (tprog := tprog) STACKS AN ENV MEM hc hn hl)
  | Ireturn s f stk pc rs m or m' hc hfree =>
    cases MS with
    | regular _ _ _ _ _ _ ts te tm an STACKS AN ENV MEM =>
      exact .inl (step_Ireturn (tprog := tprog) STACKS ENV MEM hc hfree)
  | function_internal s f args m m' stk htyp halloc =>
    cases MS with
    | call _ _ _ _ ts tf targs tm STACKS TFD LDA MEXT =>
      unfold Deadcode.transfFundef ASTFundef.transfPartial at TFD
      dsimp only at TFD
      cases h' : Deadcode.transfFunction o  prog.defmap (romemFor o prog) f with
      | Error _ => rw [h'] at TFD; cases TFD
      | OK tf' =>
        rw [h'] at TFD; cases TFD
        unfold Deadcode.transfFunction at h'
        dsimp only at h'
        split at h'
        · rename_i an AN
          cases h'
          obtain ⟨tm', ALLOC, MEM'⟩ :=
            Mem.alloc_extends MEXT halloc (Int.le_refl _) (Int.le_refl _)
          exact .inl ⟨_, RTL.Step.function_internal (ge := tprog.globalenv) ts
            (transfFunction' o  prog f an) targs tm tm' stk
            (Val.has_argtype_list_lessdef htyp LDA) ALLOC,
            .regular _ _ _ _ _ _ _ _ _ _ STACKS AN (eagree_init_regs _ _ LDA)
              (mextends_agree MEM' _)⟩
        · cases h'
  | function_external s ef args res t m m' hcall =>
    cases MS with
    | call _ _ _ _ ts tf targs tm STACKS TFD LDA MEXT =>
      unfold Deadcode.transfFundef ASTFundef.transfPartial at TFD
      cases TFD
      obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hcall MEXT LDA
      refine .inl ⟨_, .function_external _ _ _ _ _ _ _ ?_, .ret _ _ _ _ _ _ STACKS B C⟩
      rw [hsenv]; exact A
  | «return» res f sp pc rs s vres m =>
    cases MS with
    | ret _ _ _ ts tv tm STACKS LD MEXT =>
      cases STACKS with
      | cons FR STACKS =>
        cases FR with
        | intro _ _ sp _ _ te an AN H =>
          exact .inl ⟨_, .return _ _ _ _ _ _ _ _,
            .regular _ _ _ _ _ _ _ _ _ _ STACKS AN (H _ _ LD) (mextends_agree MEXT _)⟩

/-- `Deadcodeproof.transf_initial_states` -/
theorem transf_initial_states {st1 : RTL.State} (h : RTL.InitialState prog st1) :
    ∃ st2, RTL.InitialState tprog st2 ∧ MatchStates o  prog st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, A, B⟩ := function_ptr_translated TRANSF hf
    refine ⟨_, .intro b tf m0 ?_ ?_ A ?_, .call _ _ _ _ _ _ _ _ .nil B .nil (Mem.extends_refl _)⟩
    · rw [init_mem_transf_partial TRANSF]; exact hm
    · rw [(match_transform_partial_program TRANSF).main_eq, symbols_preserved TRANSF]; exact hs
    · rw [sig_function_translated B]; exact hsig

omit TRANSF in
/-- `Deadcodeproof.transf_final_states` -/
theorem transf_final_states {st1 st2 : RTL.State} {r : Integers.Int}
    (hm : MatchStates o  prog st1 st2) (h : RTL.FinalState st1 r) : RTL.FinalState st2 r := by
  cases h with
  | intro r m =>
    cases hm with
    | ret _ _ _ ts tv tm STACKS LD MEXT =>
      cases STACKS
      cases LD
      exact .intro _ _

/-- `Deadcodeproof.transf_program_correct`: the elimination of unneeded
    computations preserves the semantics of RTL programs (forward simulation).
    The hypotheses are the properties of external functions and inline
    assembly that CompCert assumes as axioms (compatibility with memory
    extensions and injections, `extcall_properties`). -/
theorem transf_program_correct
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextj : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasmj : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (RTL.semantics prog) (RTL.semantics tprog) := by
  have hinj : ∀ ef, ExtcallMemInject (externalCall ef) :=
    fun ef => externalCall_memInject ef hextj hasmj
  have hprops : ∀ ef, ExtcallMemProps (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memProps ef _ (fun n sg => hextp n sg _) (fun n sg => hasmp n sg _)
  refine forward_simulation_eventually_star (L1 := RTL.semantics prog) (L2 := RTL.semantics tprog)
    (fun s1 s2 => MatchStates o  prog s1 s2 ∧ SoundState o  prog s1) ?_ ?_ ?_
    (fun _ => 0) ?_
  · intro id
    show (Genv.toSenv tprog.globalenv).public_symbol id =
      (Genv.toSenv prog.globalenv).public_symbol id
    rw [senv_preserved TRANSF]
  · intro s1 h
    obtain ⟨s2, A, B⟩ := transf_initial_states TRANSF h
    exact ⟨s2, A, B, sound_initial h⟩
  · intro s1 s2 r ⟨hm, _⟩ h
    exact transf_final_states hm h
  · intro s1 t s1' hst s2 ⟨MS, SS⟩
    have SS' := sound_step hinj hprops hst SS
    rcases step_simulation TRANSF hext hasm hst MS SS with ⟨s2', A, B⟩ | ⟨s2', n, A, B⟩
    · exact .inl ⟨s2', .inl (plus_one A), B, SS'⟩
    · exact .inr ⟨n, s2', A, eventually_and_invariant (SoundState o  prog)
        (fun _ _ _ h hs => sound_step hinj hprops h hs) B SS'⟩

end PRESERVATION

end Deadcodeproof
end RiscV
end CC
