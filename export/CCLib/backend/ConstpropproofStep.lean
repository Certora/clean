/-
  Correctness proof for constant propagation — port of
  `backend/Constpropproof.v`, part 2: `init_regs_lessdef`,
  `const_for_result_correct`, the simulation diagram `transf_step_correct`,
  `transf_initial_states`, `transf_final_states` and
  `transf_program_correct`.

  As in Rocq, the simulation relation is `sound_state prog s1 ∧ match_states n s1 s2`:
  the soundness of the value analysis (`ValueAnalysis.sound_initial`,
  `ValueAnalysis.sound_step`) justifies the static information used by the
  transformation.

  Assumptions, which CompCert states as axioms, are
  explicit hypotheses:
  * `hext`/`hasm` (memory extensions), `hinj`/`hinja` (memory injections) and
    `hprops`/`hpropsa` (`extcall_properties`) for the uninterpreted external
    functions and inline assembly.
  Flocq's `Float.mul2_add` / `Float32.mul2_add`, used by the strength
  reduction of floating-point multiplications by 2, are proved in
  `lib/FloatsArith.lean`.
-/
import CCLib.backend.Constpropproof
import CCLib.common.EventsInject
import CCLib.common.EventsMem

namespace CC
namespace Constpropproof

open RTL Constprop ConstpropOp ValueDomain ValueAnalysis Smallstep
open Integers (Ptrofs)

/-- `Constpropproof.init_regs_lessdef` -/
theorem init_regs_lessdef : ∀ (rl : List Reg) {vl1 vl2 : List Val},
    Val.LessdefList vl1 vl2 → RegsLessdef (initRegs vl1 rl) (initRegs vl2 rl) :=
  Tailcallproof.regs_lessdef_init_regs

section PRESERVATION
variable {o : ConstpropOp.Options} {abi : Conventions1.AbiKind} {prog tprog : RTL.Program}

/-- `Constpropproof.const_for_result_correct` -/
theorem const_for_result_correct (TRANSL : MatchProgLink o abi prog tprog) {a : Aval} {op : Op.Operation} {bc : BlockClassification}
    {v : Val} {sp : Block} {m : Mem} (h : constForResult o a = some op) (hv : Vmatch bc v a)
    (hsp : bc sp = .BCstack) (GE : GenvMatch bc prog.globalenv) :
    ∃ v', Op.evalOperation tprog.globalenv (.Vptr sp Ptrofs.zero) op [] m = some v' ∧
      Val.Lessdef v v' := by
  obtain ⟨v', A, B⟩ := ConstpropOpproof.const_for_result_correct (m := m) o GE hsp h hv
  refine ⟨v', ?_, B⟩
  rw [evalOperation_preserved prog.globalenv tprog.globalenv (symbols_preserved TRANSL)]
  exact A

/-- Instructions other than `Inop` / `Icond` cannot be skipped over by `match_pc`. -/
theorem matchPc_other {f : RTL.Function} {rs : RTL.Regset} {m : Mem} {n : Nat} {pc pcx : Node}
    {i : RTL.Instruction} (PC : MatchPc f rs m n pc pcx) (hc : f.fn_code.get pc = some i)
    (hnop : ∀ s, i ≠ .Inop s) (hcond : ∀ c args s1 s2, i ≠ .Icond c args s1 s2) : pcx = pc := by
  cases PC with
  | base => rfl
  | nop _ _ s _ h _ => rw [hc] at h; cases h; exact absurd rfl (hnop s)
  | cond _ _ c args s1 s2 _ h _ => rw [hc] at h; cases h; exact absurd rfl (hcond c args s1 s2)

set_option maxHeartbeats 4000000 in
/-- `Constpropproof.transf_step_correct` -/
theorem transf_step_correct (TRANSL : MatchProgLink o abi prog tprog)
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    {s1 t s2} (hst : RTL.Step prog.globalenv s1 t s2) {n1 : Nat} {s1'}
    (SS : SoundStateLink o.toOptions abi prog s1) (hm : MatchStates o abi prog n1 s1 s1') :
    (∃ n2 s2', RTL.Step tprog.globalenv s1' t s2' ∧ MatchStates o abi prog n2 s2 s2') ∨
    (∃ n2, n2 < n1 ∧ t = E0 ∧ MatchStates o abi prog n2 s2 s1') := by
  have hsym := symbols_preserved TRANSL
  have hsenv := senv_preserved TRANSL
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  cases hst with
  | Inop s f sp pc rs m pc' hc =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      cases PC with
      | base =>
        cases SS cu LINK with
        | regular _ AN EM RO MM GE SP =>
          have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
          simp only [transfInstr, AN] at hi
          exact .inl ⟨_, _, .Inop _ _ _ _ _ _ _ hi, match_states_succ LINK STK RLD MLD⟩
      | nop _ _ s0 _ h MP =>
        rw [hc] at h; cases h
        exact .inr ⟨_, Nat.lt_succ_self _, rfl, .intro _ _ _ _ _ _ _ _ _ _ _ _ LINK STK MP RLD MLD⟩
      | cond _ _ _ _ _ _ _ h _ => rw [hc] at h; cases h
  | Iop s f sp pc rs m op args res pc' v hc hv =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        simp only [transfInstr, AN] at hi
        have VM : Vmatch bc v (ValueAOp.evalStaticOperation o.toOptions op (aregs ae args)) :=
          ValueAOp.eval_static_operation_sound o.toOptions GE SP op hv (aregs_sound EM args)
        have EM' := ematch_update res EM VM
        have MS := match_successor (o := o) f m pc' EM'
        split at hi
        · rename_i cop hcop
          obtain ⟨v', A, B⟩ := const_for_result_correct TRANSL (m := m') hcop VM SP GE
          exact .inl ⟨_, _, .Iop _ _ _ _ _ _ _ _ _ _ v' hi A,
            .intro _ _ _ _ _ _ _ _ _ _ _ _ LINK STK MS (set_reg_lessdef B RLD) MLD⟩
        · have OP := ConstpropOpproof.op_strength_reduction_correct o EM op args
            (aregs ae args) v rfl hv
          revert hi OP
          generalize opStrengthReduction o op args (aregs ae args) = p
          rcases p with ⟨op', args'⟩
          intro hi OP
          obtain ⟨w, EV, LD⟩ := OP
          obtain ⟨w', EV', LD'⟩ :=
            Op.evalOperation_lessdef _ _ _ (regsLessdef_regs RLD args') MLD EV
          exact .inl ⟨_, _, .Iop _ _ _ _ _ _ _ _ _ _ w' hi
            (by rw [evalOperation_preserved prog.globalenv tprog.globalenv hsym]; exact EV'),
            .intro _ _ _ _ _ _ _ _ _ _ _ _ LINK STK MS (set_reg_lessdef (Val.lessdef_trans LD LD') RLD) MLD⟩
  | Iload s f sp pc rs m chunk addr args dst pc' a v hc ha hl =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        simp only [transfInstr, AN] at hi
        have VM1 := ValueAOp.eval_static_addressing_sound GE SP addr ha (aregs_sound EM args)
        have VM2 := loadv_sound o.strict hl RO MM VM1
        split at hi
        · rename_i cop hcop
          obtain ⟨v', A, B⟩ := const_for_result_correct TRANSL (m := m') hcop VM2 SP GE
          exact .inl ⟨_, _, .Iop _ _ _ _ _ _ _ _ _ _ v' hi A,
            match_states_succ LINK STK (set_reg_lessdef B RLD) MLD⟩
        · have ADDR := ConstpropOpproof.addr_strength_reduction_correct o GE SP EM addr args
            (aregs ae args) a rfl ha
          revert hi ADDR
          generalize addrStrengthReduction o addr args (aregs ae args) = p
          rcases p with ⟨addr', args'⟩
          intro hi ADDR
          obtain ⟨a', P, Q⟩ := ADDR
          obtain ⟨a'', U, V⟩ := Op.evalAddressing_lessdef _ _ _ (regsLessdef_regs RLD args') P
          obtain ⟨v', X, Y⟩ := Mem.loadv_extends MLD hl (Val.lessdef_trans Q V)
          exact .inl ⟨_, _, .Iload _ _ _ _ _ _ _ _ _ _ _ a'' v' hi
            (by rw [evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact U) X,
            match_states_succ LINK STK (set_reg_lessdef Y RLD) MLD⟩
  | Istore s f sp pc rs m chunk addr args src pc' a m1 hc ha hs =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        simp only [transfInstr, AN] at hi
        have ADDR := ConstpropOpproof.addr_strength_reduction_correct o GE SP EM addr args
          (aregs ae args) a rfl ha
        revert hi ADDR
        generalize addrStrengthReduction o addr args (aregs ae args) = p
        rcases p with ⟨addr', args'⟩
        intro hi ADDR
        obtain ⟨a', P, Q⟩ := ADDR
        obtain ⟨a'', U, V⟩ := Op.evalAddressing_lessdef _ _ _ (regsLessdef_regs RLD args') P
        obtain ⟨tm', X, Y⟩ := Mem.storev_extends MLD hs (Val.lessdef_trans Q V) (RLD src)
        exact .inl ⟨_, _, .Istore _ _ _ _ _ _ _ _ _ _ _ a'' tm' hi
          (by rw [evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact U) X,
          match_states_succ LINK STK RLD Y⟩
  | Icall s f sp pc rs m sig ros args res pc' fd hc hf hsig =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        simp only [transfInstr, AN] at hi
        obtain ⟨cu', FIND, LINK'⟩ := transf_ros_correct TRANSL GE EM hf RLD
        exact .inl ⟨_, _, .Icall _ _ _ _ _ _ _ _ _ _ _ _ hi FIND
          (by rw [sig_function_translated]; exact hsig),
          .call _ _ _ _ _ _ _ _ LINK' (.cons (.intro _ _ _ _ _ _ _ LINK RLD) STK)
            (regsLessdef_regs RLD args) MLD⟩
  | Itailcall s f stk pc rs m sig ros args fd m1 hc hf hsig hfree =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        simp only [transfInstr, AN] at hi
        obtain ⟨cu', FIND, LINK'⟩ := transf_ros_correct TRANSL GE EM hf RLD
        obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MLD hfree
        exact .inl ⟨_, _, .Itailcall _ _ _ _ _ _ _ _ _ _ _ hi FIND
          (by rw [sig_function_translated]; exact hsig) FREE,
          .call _ _ _ _ _ _ _ _ LINK' STK (regsLessdef_regs RLD args) MEM'⟩
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m1 hc hargs hcall =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        have DFL : (Constprop.transfFunction o abi (romemFor o.toOptions cu) f).fn_code.get pc =
            some (.Ibuiltin ef (builtinStrengthReduction o ae ef args) res pc') →
            ∃ n2 s2', RTL.Step tprog.globalenv
              (.State s' (Constprop.transfFunction o abi (romemFor o.toOptions cu) f) (.Vptr sp0 Ptrofs.zero) pc rs' m')
              t s2' ∧
              MatchStates o abi prog n2
                (.State s f (.Vptr sp0 Ptrofs.zero) pc' (regmapSetres res vres rs) m1) s2' := by
          intro hi
          obtain ⟨vargs', P, Q⟩ := builtin_strength_reduction_correct (o := o) EM hargs hcall
          obtain ⟨vargs'', U, V⟩ := evalBuiltinArgs_lessdef (e2 := fun r => rs'.get r) RLD MLD P
          obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ Q MLD V
          exact ⟨_, _, .Ibuiltin _ _ _ _ _ _ _ _ _ _ vargs'' t tvres tm' hi
            (by rw [hsenv]; exact U) (by rw [hsenv]; exact A),
            match_states_succ LINK STK (set_res_lessdef B RLD) C⟩
        simp only [transfInstr, AN] at hi
        split at hi
        · rename_i name sg rd
          split at hi
          · rename_i bf LK
            split at hi
            · rename_i a ES
              split at hi
              · rename_i cop CR
                change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
                simp only [builtinOrExternalSem, LK] at hcall
                cases hcall with
                | intro _ _ _ _ hsem =>
                have VM := eval_static_builtin_function_sound o.toOptions EM RO MM GE SP hargs ES hsem
                obtain ⟨v', A, B⟩ := const_for_result_correct TRANSL (m := m') CR VM SP GE
                exact .inl ⟨_, _, .Iop _ _ _ _ _ _ _ _ _ _ v' hi A,
                  match_states_succ LINK STK (set_reg_lessdef B RLD) MLD⟩
              · exact .inl (DFL hi)
            · exact .inl (DFL hi)
          · exact .inl (DFL hi)
        · exact .inl (DFL hi)
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hc hcond hpc =>
    subst hpc
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      cases PC with
      | base =>
        cases SS cu LINK with
        | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
          have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
          simp only [transfInstr, AN] at hi
          have C := ValueAOp.eval_static_condition_sound o.toOptions cond m (aregs_sound EM args)
          rw [hcond] at C
          split at hi
          · rename_i b0 hrb
            have hb := resolve_branch_sound C hrb
            subst hb
            refine .inl ⟨_, _, ?_, match_states_succ LINK STK RLD MLD⟩
            cases b0
            · exact .Inop _ _ _ _ _ _ _ hi
            · exact .Inop _ _ _ _ _ _ _ hi
          · have EV1 := ConstpropOpproof.cond_strength_reduction_correct (m := m) EM cond args
              (aregs ae args) rfl
            revert hi EV1
            generalize condStrengthReduction cond args (aregs ae args) = p
            rcases p with ⟨cond', args'⟩
            intro hi EV1
            exact .inl ⟨_, _, .Icond _ _ _ _ _ _ _ _ _ _ b _ hi
              (Op.evalCondition_lessdef (regsLessdef_regs RLD args') MLD (EV1.trans hcond)) rfl,
              match_states_succ LINK STK RLD MLD⟩
      | nop _ _ _ _ h _ => rw [hc] at h; cases h
      | cond _ _ _ _ _ _ _ h MP =>
        rw [hc] at h; cases h
        exact .inr ⟨_, Nat.lt_succ_self _, rfl,
          .intro _ _ _ _ _ _ _ _ _ _ _ _ LINK STK (MP b hcond) RLD MLD⟩
  | Ijumptable s f sp pc rs m arg tbl n0 pc' hc hn hl =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        simp only [transfInstr, AN] at hi
        have hn' : rs'.get arg = .Vint n0 := by
          have := RLD arg
          rw [hn] at this
          generalize rs'.get arg = w at this ⊢
          cases this
          rfl
        have DFL : (Constprop.transfFunction o abi (romemFor o.toOptions cu) f).fn_code.get pc = some (.Ijumptable arg tbl) →
            ∃ n2 s2', RTL.Step tprog.globalenv
              (.State s' (Constprop.transfFunction o abi (romemFor o.toOptions cu) f) (.Vptr sp0 Ptrofs.zero) pc rs' m')
              E0 s2' ∧
              MatchStates o abi prog n2 (.State s f (.Vptr sp0 Ptrofs.zero) pc' rs m) s2' :=
          fun hi => ⟨_, _, .Ijumptable _ _ _ _ _ _ _ _ n0 _ hi hn' hl, match_states_succ LINK STK RLD MLD⟩
        split at hi
        · rename_i k hA
          have VM := EM arg
          change Vmatch bc (rs.get arg) (areg ae arg) at VM
          rw [hA, hn] at VM
          cases VM
          rw [hl] at hi
          exact .inl ⟨_, _, .Inop _ _ _ _ _ _ _ hi, match_states_succ LINK STK RLD MLD⟩
        · exact .inl (DFL hi)
  | Ireturn s f stk pc rs m or m1 hc hfree =>
    cases hm with
    | intro _ _ _ _ _ _ s' pcx rs' m' cu n LINK STK PC RLD MLD =>
      obtain rfl := (matchPc_other PC hc (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)).symm
      cases SS cu LINK with
      | @regular _ _ sp0 _ _ _ ae am bc _ AN EM RO MM GE SP =>
        have hi := transf_instr_at (o := o) (abi := abi) (romemFor o.toOptions cu) hc
        simp only [transfInstr, AN] at hi
        obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MLD hfree
        refine .inl ⟨_, _, .Ireturn _ _ _ _ _ _ _ _ hi FREE, .ret _ _ _ _ _ _ STK ?_ MEM'⟩
        cases or with
        | none => exact .refl _
        | some r => exact RLD r
  | function_internal s f args m m1 stk htyp halloc =>
    cases hm with
    | call _ _ _ _ s' args' m' cu LINK STK LDA MLD =>
      obtain ⟨tm', ALLOC, MEM'⟩ := Mem.alloc_extends MLD halloc (Int.le_refl _) (Int.le_refl _)
      exact .inl ⟨_, _, RTL.Step.function_internal (ge := tprog.globalenv) s'
        (Constprop.transfFunction o abi (romemFor o.toOptions cu) f) args' m' tm' stk
        (Val.has_argtype_list_lessdef htyp LDA) ALLOC,
        match_states_succ LINK STK (init_regs_lessdef _ LDA) MEM'⟩
  | function_external s ef args res t m m1 hcall =>
    cases hm with
    | call _ _ _ _ s' args' m' _ _ STK LDA MLD =>
      obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hcall MLD LDA
      refine .inl ⟨_, _, .function_external _ _ _ _ _ _ _ ?_, .ret _ _ _ _ _ _ STK B C⟩
      rw [hsenv]; exact A
  | «return» res f sp pc rs s vres m =>
    cases hm with
    | ret _ _ _ s' v' m' STK LD MLD =>
      cases STK with
      | cons hfr STK =>
        cases hfr with
        | intro _ _ _ _ _ rs' cu LINK RLD =>
          exact .inl ⟨_, _, .return _ _ _ _ _ _ _ _, match_states_succ LINK STK (set_reg_lessdef LD RLD) MLD⟩

/-- `Constpropproof.transf_initial_states` -/
theorem transf_initial_states (TRANSL : MatchProgLink o abi prog tprog) {st1 : RTL.State}
    (h : RTL.InitialState prog st1) :
    ∃ n st2, RTL.InitialState tprog st2 ∧ MatchStates o abi prog n st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨cu, FIND, LINK⟩ := function_ptr_translated TRANSL hf
    refine ⟨0, _, .intro b (Constprop.transfFundef o abi (romemFor o.toOptions cu) f) m0 ?_ ?_
      FIND ?_, .call _ _ _ _ _ _ _ _ LINK .nil .nil (Mem.extends_refl _)⟩
    · exact (Linking.MatchProgramGen.toMatchProgram TRANSL).init_mem.trans hm
    · rw [symbols_preserved TRANSL, TRANSL.main_eq]; exact hs
    · rw [sig_function_translated]; exact hsig

/-- `Constpropproof.transf_final_states` -/
theorem transf_final_states {n : Nat} {st1 st2 : RTL.State} {r : Integers.Int}
    (hm : MatchStates o abi prog n st1 st2) (h : RTL.FinalState st1 r) : RTL.FinalState st2 r := by
  cases h with
  | intro r m =>
    cases hm with
    | ret _ _ _ s' v' m' STK LD MLD =>
      cases STK
      cases LD
      exact .intro _ _

/-- `Constpropproof.transf_program_correct`: constant propagation preserves
    the semantics of RTL programs (forward simulation), for any `tprog` with
    `match_prog prog tprog` — in particular for separately compiled units.
    The hypotheses are the properties of external functions and inline
    assembly that CompCert assumes as axioms (compatibility with memory
    extensions and injections, `extcall_properties`). -/
theorem transf_program_correct_match (TRANSL : MatchProgLink o abi prog tprog)
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
  refine ⟨Nat, (· < ·), fun n s1 s2 => SoundStateLink o.toOptions abi prog s1 ∧
    MatchStates o abi prog n s1 s2, ?_⟩
  refine ⟨Nat.lt_wfRel.wf, ?_, ?_, ?_, ?_⟩
  · intro s1 h
    obtain ⟨n, s2, A, B⟩ := transf_initial_states TRANSL h
    exact ⟨n, s2, A, sound_initial_link h, B⟩
  · intro n s1 s2 r ⟨_, hm⟩ h
    exact transf_final_states hm h
  · intro s1 t s1' hst n s2 ⟨SS, hm⟩
    have SS' := sound_step_link hinj hprops hst SS
    rcases transf_step_correct TRANSL hext hasm hst SS hm with
      ⟨n2, s2', A, B⟩ | ⟨n2, A, rfl, C⟩
    · exact ⟨n2, s2', .inl (plus_one A), SS', B⟩
    · exact ⟨n2, s2, .inr ⟨.refl _, A⟩, SS', C⟩
  · intro id
    show (Genv.toSenv tprog.globalenv).public_symbol id =
      (Genv.toSenv prog.globalenv).public_symbol id
    rw [senv_preserved TRANSL]

/-- `Constpropproof.transf_program_correct` for the whole-program
    transformation `Constprop.transfProgram`. -/
theorem transf_program_correct
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextj : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasmj : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (RTL.semantics prog) (RTL.semantics (Constprop.transfProgram o abi prog)) :=
  transf_program_correct_match (transf_program_match o abi prog) hext hasm hextj hasmj hextp hasmp

end PRESERVATION

end Constpropproof
end CC
