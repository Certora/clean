/-
  [x86-64 instance of `CCLib/backend/CSEproofStep.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness proof for common subexpression elimination — port of the
  `PRESERVATION` section of CompCert `backend/CSEproof.v`:
  `symbols_preserved`, `senv_preserved`, `functions_translated`,
  `funct_ptr_translated`, `sig_preserved`, `find_function_translated`,
  `match_stackframes`, `match_states`, `transf_step_correct`,
  `transf_initial_states`, `transf_final_states` and `transf_program_correct`.

  Differences from Rocq:
  * as for the other value-analysis-based passes of this port, the program is
    transformed as a whole (no separate compilation): the definitions map and
    read-only memory used by the transformation are those of the whole source
    program (`prog.defmap`, `romemFor o prog`), so the `linkorder cu prog`
    components of `match_states` are dropped;
  * `RTL.is_known_runtime_function_sound` is proved here for the whole program
    (`isKnownRuntimeFunction_sound`).
  * The properties of external functions and inline assembly that CompCert
    assumes as axioms are explicit hypotheses (`hext`, `hasm`, `hextj`,
    `hasmj`, `hextp`, `hasmp`).
-/
import CCLib.x86.CSEproofMem
import CCLib.x86.CSEproofReduce
import CCLib.x86.CombineOpproof
import CCLib.x86.OpInject
import CCLib.x86.OpTheory
import CCLib.x86.Conventions
import CCLib.x86.Tailcallproof
import CCLib.common.SimulationEventually
import CCLib.common.EventsInject
import CCLib.common.EventsMem
import CCLib.common.EventsExtends

namespace CC
namespace X86
namespace CSEproof

open ValueDomain ValueAnalysis RTL CSEdomain CSE Op Smallstep CombineOp
open Integers (Ptrofs)

/-- `RTL.is_known_runtime_function_sound`, for the definitions of the whole program. -/
theorem isKnownRuntimeFunction_sound {prog : RTL.Program} {ros : Sum Reg Ident}
    {bf : Builtins.BuiltinFunction} {rs : RTL.Regset} {fd : RTL.Fundef}
    (h : isKnownRuntimeFunction prog.defmap ros = some bf)
    (hf : findFunction prog.globalenv ros rs = some fd) :
    ∃ name sg, fd = .External (.EF_runtime name sg) ∧
      Builtins.lookupBuiltinFunction name sg = some bf := by
  unfold isKnownRuntimeFunction at h
  cases ros with
  | inl r => cases h
  | inr id =>
    dsimp only at h
    split at h
    · rename_i name sg D
      rw [ASTProgram.defmap_eq, Genv.find_def_symbol] at D
      obtain ⟨b, F1, F2⟩ := D
      simp only [findFunction, ASTProgram.globalenv] at hf
      rw [F1] at hf
      rw [Genv.findFunctPtr_iff, F2] at hf
      cases hf
      exact ⟨name, sg, rfl, h⟩
    · cases h


/-- Shape of the transformed `Icall` instruction. -/
theorem transfInstr_Icall {dm : Defmap} {n : Numbering} {sig : Signature} {ros : Sum Reg Ident}
    {args : List Reg} {res : Reg} {s : Node} {i : Instruction}
    (h : transfInstr dm n (.Icall sig ros args res s) = i) :
    i = .Icall sig ros args res s ∨ ∃ bf n1 args' r, isKnownRuntimeFunction dm ros = some bf ∧
      valnumBuiltinArgs n (args.map .BA) = (n1, args') ∧ findRhs n1 (.Builtin bf args') = some r ∧
      i = .Iop .Omove [r] res s := by
  simp only [transfInstr] at h
  split at h
  · exact .inl h.symm
  · rename_i bf IK
    rcases VB : valnumBuiltinArgs n (args.map .BA) with ⟨n1, args'⟩
    rw [VB] at h
    dsimp only at h
    split at h
    · rename_i r FR; exact .inr ⟨bf, n1, args', r, IK, rfl, FR, h.symm⟩
    · exact .inl h.symm

/-- Shape of the transformed `Ibuiltin` instruction. -/
theorem transfInstr_Ibuiltin {dm : Defmap} {n : Numbering} {ef : ExtFun}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {s : Node} {i : Instruction}
    (h : transfInstr dm n (.Ibuiltin ef args res s) = i) :
    i = .Ibuiltin ef args res s ∨ ∃ name sg rd bf n1 args' r, ef = .EF_builtin name sg ∧
      res = .BR rd ∧ Builtins.lookupBuiltinFunction name sg = some bf ∧
      valnumBuiltinArgs n args = (n1, args') ∧ findRhs n1 (.Builtin bf args') = some r ∧
      i = .Iop .Omove [r] rd s := by
  cases ef <;> cases res <;> simp only [transfInstr] at h <;> try exact .inl h.symm
  rename_i name sg rd
  split at h
  · rename_i bf LK
    rcases VB : valnumBuiltinArgs n args with ⟨n1, args'⟩
    rw [VB] at h
    dsimp only at h
    split at h
    · rename_i r FR; exact .inr ⟨name, sg, rd, bf, n1, args', r, rfl, rfl, LK, rfl, FR, h.symm⟩
    · exact .inl h.symm
  · exact .inl h.symm

section PRESERVATION
variable (o : ValueAOp.Options) (prog : RTL.Program)


/-- `CSEproof.analyze` -/
def analyzeFn (f : RTL.Function) : Option (PMap Numbering) :=
  CSE.analyze o f prog.defmap (vanalyze o  (romemFor o prog) f)

/-- `CSEproof.transf_function'` -/
def transfFunction' (f : RTL.Function) (approxs : PMap Numbering) : RTL.Function :=
  { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_stacksize := f.fn_stacksize,
    fn_code := transfCode prog.defmap approxs f.fn_code, fn_entrypoint := f.fn_entrypoint }

/-- `CSEproof.match_stackframes` (one frame) -/
inductive MatchStackframe : RTL.Stackframe → RTL.Stackframe → Prop where
  | intro (res f sp pc rs rs' approx) :
      analyzeFn o  prog f = some approx →
      (∀ v m, ∃ valu, NumberingHolds valu prog.globalenv sp (rs.set res v) m (approx.get pc)) →
      RegsLessdef rs rs' →
      MatchStackframe (.Stackframe res f sp pc rs)
        (.Stackframe res (transfFunction' prog f approx) sp pc rs')

/-- `CSEproof.match_states` -/
inductive MatchStates : RTL.State → RTL.State → Prop where
  | intro (s sp pc rs m s' rs' m' f approx) :
      analyzeFn o  prog f = some approx →
      (∃ valu, NumberingHolds valu prog.globalenv sp rs m (approx.get pc)) →
      RegsLessdef rs rs' → Mem.Extends m m' →
      ListForall2 (MatchStackframe o  prog) s s' →
      MatchStates (.State s f sp pc rs m)
        (.State s' (transfFunction' prog f approx) sp pc rs' m')
  | call (s f tf args m s' args' m') :
      ListForall2 (MatchStackframe o  prog) s s' →
      CSE.transfFundef o  prog.defmap (romemFor o prog) f = .OK tf →
      Val.LessdefList args args' → Mem.Extends m m' →
      MatchStates (.Callstate s f args m) (.Callstate s' tf args' m')
  | ret (s s' v v' m m') :
      ListForall2 (MatchStackframe o  prog) s s' → Val.Lessdef v v' → Mem.Extends m m' →
      MatchStates (.Returnstate s v m) (.Returnstate s' v' m')

variable {o  prog} in
/-- Matching after an instruction, from the numbering computed by `transfer`. -/
theorem match_succ {s s' : List RTL.Stackframe} {f : RTL.Function} {sp : Val} {pc pc' : Node}
    {rs rs' : RTL.Regset} {m m' : Mem} {approx : PMap Numbering} {i : Instruction}
    (AN : analyzeFn o  prog f = some approx) (hc : f.fn_code.get pc = some i)
    (hs : pc' ∈ successorsInstr i)
    (NH : ∃ valu, NumberingHolds valu prog.globalenv sp rs m
      (CSE.transfer o f prog.defmap (vanalyze o  (romemFor o prog) f) pc (approx.get pc)))
    (RLD : RegsLessdef rs rs') (MEXT : Mem.Extends m m')
    (STK : ListForall2 (MatchStackframe o  prog) s s') :
    MatchStates o  prog (.State s f sp pc' rs m)
      (.State s' (transfFunction' prog f approx) sp pc' rs' m') :=
  .intro _ _ _ _ _ _ _ _ _ _ AN (analysis_correct_1 o AN hc hs NH) RLD MEXT STK

variable {o  prog} {tprog : RTL.Program}
  (TRANSF : CSE.transfProgram o  prog = .OK tprog)
include TRANSF

theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

theorem functions_translated {v : Val} {f : RTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧
      CSE.transfFundef o  prog.defmap (romemFor o prog) f = .OK tf :=
  find_funct_transf_partial TRANSF h

theorem funct_ptr_translated {b : Block} {f : RTL.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧
      CSE.transfFundef o  prog.defmap (romemFor o prog) f = .OK tf :=
  find_funct_ptr_transf_partial TRANSF h

omit TRANSF in
/-- `CSEproof.sig_preserved` -/
theorem sig_preserved {dm : Defmap} {rm' : Romem} {f tf : RTL.Fundef}
    (h : CSE.transfFundef o  dm rm' f = .OK tf) : funsig tf = funsig f := by
  cases f with
  | Internal f =>
    unfold CSE.transfFundef ASTFundef.transfPartial at h
    dsimp only at h
    cases h' : CSE.transfFunction o  dm rm' f with
    | Error _ => rw [h'] at h; cases h
    | OK tf' =>
      rw [h'] at h; cases h
      unfold CSE.transfFunction at h'
      dsimp only at h'
      split at h'
      · cases h'
      · cases h'; rfl
  | External ef =>
    unfold CSE.transfFundef ASTFundef.transfPartial at h
    cases h; rfl

/-- `CSEproof.find_function_translated` -/
theorem find_function_translated {ros : Sum Reg Ident} {rs rs' : RTL.Regset} {fd : RTL.Fundef}
    (h : findFunction prog.globalenv ros rs = some fd) (RLD : RegsLessdef rs rs') :
    ∃ tfd, findFunction tprog.globalenv ros rs' = some tfd ∧
      CSE.transfFundef o  prog.defmap (romemFor o prog) fd = .OK tfd := by
  cases ros with
  | inl r =>
    simp only [findFunction] at h ⊢
    have L := RLD r
    revert h
    generalize rs.get r = a at L
    generalize rs'.get r = b at L
    intro h
    cases L with
    | refl => exact functions_translated TRANSF h
    | undef => simp [Genv.findFunct] at h
  | inr id =>
    simp only [findFunction] at h ⊢
    rw [symbols_preserved TRANSF]
    cases e : Genv.findSymbol prog.globalenv id with
    | none => rw [e] at h; cases h
    | some b => rw [e] at h; exact funct_ptr_translated TRANSF h

omit TRANSF in
/-- The `TransfInstr` tactic of `CSEproof.v`. -/
theorem transf_instr_at {f : RTL.Function} {approx : PMap Numbering} {pc : Node}
    {i : Instruction} (h : f.fn_code.get pc = some i) :
    (transfFunction' prog f approx).fn_code.get pc =
      some (transfInstr prog.defmap (approx.get pc) i) := by
  simp [transfFunction', transfCode, PTree.gmap, h]

set_option maxHeartbeats 4000000 in
/-- `CSEproof.transf_step_correct` -/
theorem transf_step_correct
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    {s1 t s2} (hst : RTL.Step prog.globalenv s1 t s2) {s1'}
    (MS : MatchStates o  prog s1 s1') (SOUND : SoundState o  prog s1) :
    (∃ s2', RTL.Step tprog.globalenv s1' t s2' ∧ MatchStates o  prog s2 s2') ∨
    (∃ s2' n, Smallstep.Plus (RTL.Step tprog.globalenv) s1' t s2' ∧
      Smallstep.Eventually (RTL.Step prog.globalenv) RTL.FinalState n s2
        (fun s3 => MatchStates o  prog s3 s2')) := by
  have hsym := symbols_preserved TRANSF
  have hsenv := senv_preserved TRANSF
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  cases hst with
  | Inop s f sp pc rs m pc' hc =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      refine .inl ⟨_, .Inop _ _ _ _ _ _ _ hi, match_succ AN hc (by simp [successorsInstr]) ?_
        RLD MEXT STK⟩
      unfold CSE.transfer; rw [hc]; exact SAT
  | Iop s f sp pc rs m op args res pc' v hc hv =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      obtain ⟨valu1, NH1⟩ := SAT
      have POST : ∃ valu, NumberingHolds valu prog.globalenv sp (rs.set res v) m
          (CSE.transfer o f prog.defmap (vanalyze o  (romemFor o prog) f) pc (approx.get pc)) := by
        unfold CSE.transfer; rw [hc]; exact add_op_holds NH1 hv
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      split at hi
      · obtain ⟨v', A, B⟩ := Op.evalOperation_lessdef _ _ _ (regsLessdef_regs RLD args) MEXT hv
        exact .inl ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ v' hi
          (by rw [Op.evalOperation_preserved prog.globalenv tprog.globalenv hsym]; exact A),
          match_succ AN hc (by simp [successorsInstr]) POST (set_reg_lessdef B RLD) MEXT STK⟩
      · rcases EV : valnumRegs (approx.get pc) args with ⟨n1, vl⟩
        rw [EV] at hi
        dsimp only at hi
        obtain ⟨valu2, NH2, EQ, _, _, _⟩ := valnum_regs_holds args NH1 EV
        split at hi
        · rename_i r FR
          obtain ⟨v', EVr, LD⟩ := find_rhs_sound FR NH2
          have : v' = v := by
            cases EVr with
            | op_eval_to _ _ _ h => rw [EQ] at hv; rw [hv] at h; cases h; rfl
          subst this
          exact .inl ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ (rs'.get r) hi rfl,
            match_succ AN hc (by simp [successorsInstr]) POST
              (set_reg_lessdef (Val.lessdef_trans LD (RLD r)) RLD) MEXT STK⟩
        · rcases ER : reduce combineOp n1 op args vl with ⟨op', args'⟩
          rw [ER] at hi
          dsimp only at hi
          obtain ⟨v', EV', LD'⟩ := reduce_lessdef_sound
            (sem := fun op vl => evalOperation prog.globalenv sp op vl m)
            (fun _ _ _ _ _ _ _ H1 H2 H3 => CombineOp.combine_op_sound H1 H2 H3) NH2 ER EQ.symm hv
          obtain ⟨v'', EV'', LD''⟩ :=
            Op.evalOperation_lessdef _ _ _ (regsLessdef_regs RLD args') MEXT EV'
          exact .inl ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ v'' hi
            (by rw [Op.evalOperation_preserved prog.globalenv tprog.globalenv hsym]; exact EV''),
            match_succ AN hc (by simp [successorsInstr]) POST
              (set_reg_lessdef (Val.lessdef_trans LD' LD'') RLD) MEXT STK⟩
  | Iload s f sp pc rs m chunk addr args dst pc' a v hc ha hl =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      cases SOUND with
      | @regular _ _ sp0 _ _ _ ae am bc _ ANv EM RO MM GE SP =>
      obtain ⟨valu1, NH1⟩ := SAT
      obtain ⟨b, ofs, rfl⟩ : ∃ b ofs, a = .Vptr b ofs := by
        cases a <;> first | exact ⟨_, _, rfl⟩ | simp [Mem.loadv] at hl
      have POST : ∃ valu, NumberingHolds valu prog.globalenv (.Vptr sp0 Ptrofs.zero) (rs.set dst v) m
          (CSE.transfer o f prog.defmap (vanalyze o  (romemFor o prog) f) pc (approx.get pc)) := by
        unfold CSE.transfer; rw [hc]
        dsimp only
        have PM := match_aptr_of_aval o.strict
          (ValueAOp.eval_static_addressing_sound GE SP addr ha (aregs_sound EM args))
        rw [show vanalyze o  (romemFor o prog) f = ValueAnalysis.analyze o  (romemFor o prog) f
          from rfl, ANv]
        exact add_load_holds NH1 ha hl PM GE SP
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      rcases EV : valnumRegs (approx.get pc) args with ⟨n1, vl⟩
      rw [EV] at hi
      dsimp only at hi
      obtain ⟨valu2, NH2, EQ, _, _, _⟩ := valnum_regs_holds args NH1 EV
      split at hi
      · rename_i r FR
        obtain ⟨v', EVr, LD⟩ := find_rhs_sound FR NH2
        have : v' = v := by
          cases EVr with
          | load_eval_to _ _ _ a' _ _ h1 h2 =>
            rw [EQ] at ha; rw [ha] at h1; cases h1; rw [hl] at h2; cases h2; rfl
        subst this
        exact .inl ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ (rs'.get r) hi rfl,
          match_succ AN hc (by simp [successorsInstr]) POST
            (set_reg_lessdef (Val.lessdef_trans LD (RLD r)) RLD) MEXT STK⟩
      · rcases ER : reduce combineAddr n1 addr args vl with ⟨addr', args'⟩
        rw [ER] at hi
        dsimp only at hi
        have ADDR := reduce_sound
          (sem := fun addr vl => evalAddressing prog.globalenv (.Vptr sp0 Ptrofs.zero) addr vl)
          (fun _ _ _ _ _ _ H1 H2 => CombineOp.combine_addr_sound H1 H2) NH2 ER EQ.symm ha
        obtain ⟨a', A, B⟩ := Op.evalAddressing_lessdef _ _ _ (regsLessdef_regs RLD args') ADDR
        obtain ⟨v', X, Y⟩ := Mem.loadv_extends MEXT hl B
        exact .inl ⟨_, .Iload _ _ _ _ _ _ _ _ _ _ _ a' v' hi
          (by rw [Op.evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact A) X,
          match_succ AN hc (by simp [successorsInstr]) POST (set_reg_lessdef Y RLD) MEXT STK⟩
  | Istore s f sp pc rs m chunk addr args src pc' a m1 hc ha hs =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      cases SOUND with
      | @regular _ _ sp0 _ _ _ ae am bc _ ANv EM RO MM GE SP =>
      obtain ⟨valu1, NH1⟩ := SAT
      have POST : ∃ valu, NumberingHolds valu prog.globalenv (.Vptr sp0 Ptrofs.zero) rs m1
          (CSE.transfer o f prog.defmap (vanalyze o  (romemFor o prog) f) pc (approx.get pc)) := by
        unfold CSE.transfer; rw [hc]
        dsimp only
        rw [show vanalyze o  (romemFor o prog) f = ValueAnalysis.analyze o  (romemFor o prog) f
          from rfl, ANv]
        exact add_store_result_hold o (kill_loads_after_store_holds o NH1 ha hs GE SP EM) ha hs GE SP EM
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      rcases EV : valnumRegs (approx.get pc) args with ⟨n1, vl⟩
      rw [EV] at hi
      dsimp only at hi
      obtain ⟨valu2, NH2, EQ, _, _, _⟩ := valnum_regs_holds args NH1 EV
      rcases ER : reduce combineAddr n1 addr args vl with ⟨addr', args'⟩
      rw [ER] at hi
      dsimp only at hi
      have ADDR := reduce_sound
        (sem := fun addr vl => evalAddressing prog.globalenv (.Vptr sp0 Ptrofs.zero) addr vl)
        (fun _ _ _ _ _ _ H1 H2 => CombineOp.combine_addr_sound H1 H2) NH2 ER EQ.symm ha
      obtain ⟨a', A, B⟩ := Op.evalAddressing_lessdef _ _ _ (regsLessdef_regs RLD args') ADDR
      obtain ⟨tm', X, Y⟩ := Mem.storev_extends MEXT hs B (RLD src)
      exact .inl ⟨_, .Istore _ _ _ _ _ _ _ _ _ _ _ a' tm' hi
        (by rw [Op.evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact A) X,
        match_succ AN hc (by simp [successorsInstr]) POST RLD Y STK⟩
  | Icall s f sp pc rs m sig ros args res pc' fd hc hf hsig =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      obtain ⟨valu1, NH1⟩ := SAT
      obtain ⟨tf, FIND', TRANSF'⟩ := find_function_translated TRANSF hf RLD
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      cases IK : isKnownRuntimeFunction prog.defmap ros with
      | none =>
        have HI : transfInstr prog.defmap (approx.get pc) (.Icall sig ros args res pc') =
            .Icall sig ros args res pc' := by
          simp only [transfInstr, IK]
        rw [HI] at hi
        refine .inl ⟨_, .Icall _ _ _ _ _ _ _ _ _ _ _ _ hi FIND'
          (by rw [sig_preserved TRANSF']; exact hsig),
          .call _ _ _ _ _ _ _ _ (.cons (.intro _ _ _ _ _ _ approx AN (fun v m0 => ?_) RLD) STK)
            TRANSF' (regsLessdef_regs RLD args) MEXT⟩
        refine analysis_correct_1 o AN hc (by simp [successorsInstr]) ?_
        unfold CSE.transfer; rw [hc]; dsimp only; rw [IK]
        exact ⟨fun _ => .Vundef, empty_numbering_holds _ _ _ _ _⟩
      | some bf =>
        obtain ⟨name, sg, rfl, E2⟩ := isKnownRuntimeFunction_sound IK hf
        unfold CSE.transfFundef ASTFundef.transfPartial at TRANSF'
        cases TRANSF'
        have EV : ∀ (P : RTL.State → Prop),
            (∀ v, (Builtins.builtinFunctionSem bf).sem (rs.getList args) = some v →
              P (.State s f sp pc' (rs.set res v) m)) →
            Smallstep.Eventually (RTL.Step prog.globalenv) RTL.FinalState 2
              (.Callstate (.Stackframe res f sp pc' rs :: s) (.External (.EF_runtime name sg))
                (rs.getList args) m) P := by
          intro P PSPEC
          refine .later (fun r F => by cases F) (fun t s1 S1 => ?_) (fun t s1 S1 => ?_)
          · cases S1 with
            | function_external _ _ _ _ _ _ _ hcall =>
              change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
              simp only [builtinOrExternalSem, E2] at hcall
              cases hcall; rfl
          · cases S1 with
            | function_external _ _ _ _ _ _ _ hcall =>
              change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
              simp only [builtinOrExternalSem, E2] at hcall
              cases hcall with
              | intro _ _ vr _ hsem =>
              exact .later (fun r F => by cases F) (fun t s2 S2 => by cases S2; rfl)
                (fun t s2 S2 => by cases S2; exact .now (PSPEC _ hsem))
        have POST : ∀ v, (Builtins.builtinFunctionSem bf).sem (rs.getList args) = some v →
            ∃ valu, NumberingHolds valu prog.globalenv sp (rs.set res v) m
              (CSE.transfer o f prog.defmap (vanalyze o  (romemFor o prog) f) pc
                (approx.get pc)) := by
          intro v hsem
          unfold CSE.transfer; rw [hc]; dsimp only; rw [IK]; dsimp only
          exact add_builtin_holds (res := .BR res) (kill_cheap_computations_hold NH1)
            (eval_builtin_args_trivial args) hsem
        rcases transfInstr_Icall (rfl : transfInstr prog.defmap (approx.get pc)
            (.Icall sig ros args res pc') = _) with HI | ⟨bf', n1, args', r, IK', VB, FR, HI⟩
        · rw [HI] at hi
          cases SEM : (Builtins.builtinFunctionSem bf).sem (rs.getList args) with
          | some vres =>
            obtain ⟨vres', SEM', LDRES⟩ :=
              Builtins.builtinFunctionSem_lessdef bf SEM (regsLessdef_regs RLD args)
            refine .inr ⟨_, 2, plus_left (.Icall _ _ _ _ _ _ _ _ _ _ _ _ hi FIND' hsig)
              (star_two (.function_external _ _ _ vres' E0 m' m' ?_) (.return _ _ _ _ _ _ _ _) rfl) rfl,
              EV _ (fun v hv => ?_)⟩
            · change builtinOrExternalSem name sg _ _ _ _ _ _
              simp only [builtinOrExternalSem, E2]
              exact .intro _ _ _ _ SEM'
            · rw [SEM] at hv; cases hv
              exact match_succ AN hc (by simp [successorsInstr]) (POST _ SEM)
                (set_reg_lessdef LDRES RLD) MEXT STK
          | none =>
            refine .inr ⟨_, 1, plus_one (.Icall _ _ _ _ _ _ _ _ _ _ _ _ hi FIND' hsig),
              .later (fun r F => by cases F) (fun t s1 S1 => ?_) (fun t s1 S1 => ?_)⟩
            all_goals
              cases S1 with
              | function_external _ _ _ _ _ _ _ hcall =>
                change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
                simp only [builtinOrExternalSem, E2] at hcall
                cases hcall with
                | intro _ _ _ _ hsem => simp [SEM] at hsem
        · rw [IK] at IK'; cases IK'
          rw [HI] at hi
          obtain ⟨valu2, X, Y, _, _, _⟩ :=
            valnum_builtin_args_holds (eval_builtin_args_trivial args) NH1 VB
          obtain ⟨v, D, E⟩ := find_rhs_sound FR X
          cases D with
          | builtin_eval_to _ _ vargs0 _ hev hsem0 =>
          have := evalBuiltinArgs_determ Y hev
          subst this
          exact .inr ⟨_, 2, plus_one (.Iop _ _ _ _ _ _ _ _ _ _ (rs'.get r) hi rfl),
            EV _ (fun v' hv' => by
              rw [hsem0] at hv'; cases hv'
              exact match_succ AN hc (by simp [successorsInstr]) (POST _ hsem0)
                (set_reg_lessdef (Val.lessdef_trans E (RLD r)) RLD) MEXT STK)⟩
  | Itailcall s f stk pc rs m sig ros args fd m1 hc hf hsig hfree =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      obtain ⟨tf, FIND', TRANSF'⟩ := find_function_translated TRANSF hf RLD
      obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MEXT hfree
      exact .inl ⟨_, .Itailcall _ _ _ _ _ _ _ _ _ _ _ hi FIND'
        (by rw [sig_preserved TRANSF']; exact hsig) FREE,
        .call _ _ _ _ _ _ _ _ STK TRANSF' (regsLessdef_regs RLD args) MEM'⟩
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m1 hc hargs hcall =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      cases SOUND with
      | @regular _ _ sp0 _ _ _ ae am bc _ ANv EM RO MM GE SP =>
      obtain ⟨valu1, NH1⟩ := SAT
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      rcases transfInstr_Ibuiltin (rfl : transfInstr prog.defmap (approx.get pc)
          (.Ibuiltin ef args res pc') = _) with
        HI | ⟨name, sg, rd, bf, n1, args', r, rfl, rfl, LK, VB, FR, HI⟩
      · rw [HI] at hi
        obtain ⟨vargs', A, B⟩ := evalBuiltinArgs_lessdef (e2 := fun r => rs'.get r) RLD MEXT hargs
        obtain ⟨tvres, tm', P, Q, R, _⟩ := hec ef _ _ _ _ _ _ _ hcall MEXT B
        exact .inl ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ vargs' t tvres tm' hi
          (by rw [hsenv]; exact A) (by rw [hsenv]; exact P),
          match_succ AN hc (by simp [successorsInstr])
            (transfer_builtin_holds o (vapprox := vanalyze o  (romemFor o prog) f)
              hc hargs hcall NH1 ANv EM RO MM GE SP)
            (set_res_lessdef Q RLD) R STK⟩
      · rw [HI] at hi
        change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
        simp only [builtinOrExternalSem, LK] at hcall
        cases hcall with
        | intro _ _ _ _ hsem =>
        obtain ⟨valu2, X, Y, _, _, _⟩ := valnum_builtin_args_holds hargs NH1 VB
        obtain ⟨v, D, E⟩ := find_rhs_sound FR X
        cases D with
        | builtin_eval_to _ _ vargs0 _ hev hsem0 =>
        have := evalBuiltinArgs_determ Y hev
        subst this
        rw [hsem] at hsem0; cases hsem0
        exact .inl ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ (rs'.get r) hi rfl,
          match_succ AN hc (by simp [successorsInstr])
            (by unfold CSE.transfer; rw [hc]; dsimp only; rw [LK]
                exact add_builtin_holds NH1 hargs hsem)
            (set_reg_lessdef (Val.lessdef_trans E (RLD r)) RLD) MEXT STK⟩
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hc hcond hpc =>
    subst hpc
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      have SUCC : (if b then ifso else ifnot) ∈ successorsInstr (.Icond cond args ifso ifnot) := by
        cases b <;> simp [successorsInstr]
      have POST : ∃ valu, NumberingHolds valu prog.globalenv sp rs m
          (CSE.transfer o f prog.defmap (vanalyze o  (romemFor o prog) f) pc (approx.get pc)) := by
        unfold CSE.transfer; rw [hc]; exact SAT
      obtain ⟨valu1, NH1⟩ := SAT
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      rcases EV : valnumRegs (approx.get pc) args with ⟨n1, vl⟩
      rw [EV] at hi
      dsimp only at hi
      obtain ⟨valu2, NH2, EQ, _, _, _⟩ := valnum_regs_holds args NH1 EV
      split at hi
      · rename_i b0 CC
        have : b = b0 := CombineOp.combine_cond'_sound CC (by rw [← EQ]; exact hcond)
        subst this
        exact .inl ⟨_, .Inop _ _ _ _ _ _ _ hi, match_succ AN hc SUCC POST RLD MEXT STK⟩
      · rcases ER : reduce combineCond n1 cond args vl with ⟨cond', args'⟩
        rw [ER] at hi
        dsimp only at hi
        have RES := reduce_sound (sem := fun cond vl => evalCondition cond vl m)
          (fun _ _ _ _ _ _ H1 H2 => CombineOp.combine_cond_sound H1 H2) NH2 ER EQ.symm hcond
        exact .inl ⟨_, .Icond _ _ _ _ _ _ _ _ _ _ b _ hi
          (Op.evalCondition_lessdef (regsLessdef_regs RLD args') MEXT RES) rfl,
          match_succ AN hc SUCC POST RLD MEXT STK⟩
  | Ijumptable s f sp pc rs m arg tbl n0 pc' hc hn hl =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      have hn' : rs'.get arg = .Vint n0 := by
        have := RLD arg
        rw [hn] at this
        generalize rs'.get arg = w at this ⊢
        cases this
        rfl
      exact .inl ⟨_, .Ijumptable _ _ _ _ _ _ _ _ n0 _ hi hn' hl,
        match_succ AN hc (CminorSel.listNthZ_mem hl)
          (by unfold CSE.transfer; rw [hc]; exact SAT) RLD MEXT STK⟩
  | Ireturn s f stk pc rs m or m1 hc hfree =>
    cases MS with
    | intro _ _ _ _ _ s' rs' m' _ approx AN SAT RLD MEXT STK =>
      have hi := transf_instr_at (prog := prog) (approx := approx) hc
      simp only [transfInstr] at hi
      obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MEXT hfree
      refine .inl ⟨_, .Ireturn _ _ _ _ _ _ _ _ hi FREE, .ret _ _ _ _ _ _ STK ?_ MEM'⟩
      cases or with
      | none => exact .refl _
      | some r => exact RLD r
  | function_internal s f args m m1 stk htyp halloc =>
    cases MS with
    | call _ _ tf _ _ s' args' m' STK TFD LDA MEXT =>
      unfold CSE.transfFundef ASTFundef.transfPartial at TFD
      dsimp only at TFD
      cases h' : CSE.transfFunction o  prog.defmap (romemFor o prog) f with
      | Error _ => rw [h'] at TFD; cases TFD
      | OK tf' =>
        rw [h'] at TFD; cases TFD
        unfold CSE.transfFunction at h'
        dsimp only at h'
        split at h'
        · cases h'
        · rename_i approxs AN
          cases h'
          obtain ⟨tm', ALLOC, MEM'⟩ := Mem.alloc_extends MEXT halloc (Int.le_refl _) (Int.le_refl _)
          exact .inl ⟨_, RTL.Step.function_internal (ge := tprog.globalenv) s'
            (transfFunction' prog f approxs) args' m' tm' stk
            (Val.has_argtype_list_lessdef htyp LDA) ALLOC,
            .intro _ _ _ _ _ _ _ _ _ _ AN (analysis_correct_entry o AN)
              (Tailcallproof.regs_lessdef_init_regs _ LDA) MEM' STK⟩
  | function_external s ef args res t m m1 hcall =>
    cases MS with
    | call _ _ tf _ _ s' args' m' STK TFD LDA MEXT =>
      unfold CSE.transfFundef ASTFundef.transfPartial at TFD
      cases TFD
      obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hcall MEXT LDA
      refine .inl ⟨_, .function_external _ _ _ _ _ _ _ ?_, .ret _ _ _ _ _ _ STK B C⟩
      rw [hsenv]; exact A
  | «return» res f sp pc rs s vres m =>
    cases MS with
    | ret _ s' _ v' _ m' STK LD MEXT =>
      cases STK with
      | cons hfr STK =>
        cases hfr with
        | intro _ _ _ _ _ rs' approx AN SATF RLD =>
          exact .inl ⟨_, .return _ _ _ _ _ _ _ _,
            .intro _ _ _ _ _ _ _ _ _ _ AN (SATF vres m) (set_reg_lessdef LD RLD) MEXT STK⟩

/-- `CSEproof.transf_initial_states` -/
theorem transf_initial_states {st1 : RTL.State} (h : RTL.InitialState prog st1) :
    ∃ st2, RTL.InitialState tprog st2 ∧ MatchStates o  prog st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, A, B⟩ := funct_ptr_translated TRANSF hf
    refine ⟨_, .intro b tf m0 ?_ ?_ A ?_, .call _ _ _ _ _ _ _ _ .nil B .nil (Mem.extends_refl _)⟩
    · rw [init_mem_transf_partial TRANSF]; exact hm
    · rw [(match_transform_partial_program TRANSF).main_eq, symbols_preserved TRANSF]; exact hs
    · rw [sig_preserved B]; exact hsig

omit TRANSF in
/-- `CSEproof.transf_final_states` -/
theorem transf_final_states {st1 st2 : RTL.State} {r : Integers.Int}
    (hm : MatchStates o  prog st1 st2) (h : RTL.FinalState st1 r) : RTL.FinalState st2 r := by
  cases h with
  | intro r m =>
    cases hm with
    | ret _ s' _ v' _ m' STK LD MLD =>
      cases STK
      cases LD
      exact .intro _ _

/-- `CSEproof.transf_program_correct`: common subexpression elimination
    preserves the semantics of RTL programs (forward simulation).  The
    hypotheses are the properties of external functions and inline assembly
    that CompCert assumes as axioms (compatibility with memory extensions and
    injections, `extcall_properties`). -/
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
    rcases transf_step_correct TRANSF hext hasm hst MS SS with ⟨s2', A, B⟩ | ⟨s2', n, A, B⟩
    · exact .inl ⟨s2', .inl (plus_one A), B, SS'⟩
    · exact .inr ⟨n, s2', A, eventually_and_invariant (SoundState o  prog)
        (fun _ _ _ h hs => sound_step hinj hprops h hs) B SS'⟩

end PRESERVATION

end CSEproof
end X86
end CC
