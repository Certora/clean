/-
  [x86-64 instance of `CCLib/backend/DeadcodeproofStep.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Elimination of unneeded computations over RTL: correctness proof — port of
  the `PRESERVATION` section of CompCert `backend/Deadcodeproof.v`:
  `symbols_preserved`, `senv_preserved`, `functions_translated`,
  `function_ptr_translated`, `sig_function_translated`,
  `stacksize_translated`, `transf_function_at`, `find_function_translated`,
  `match_stackframes`, `match_states`, `analyze_successors`,
  `match_succ_states`, `step_simulation`, `transf_initial_states`,
  `transf_final_states` and `transf_program_correct`.

  Differences from Rocq:
  * as for the other value-analysis-based passes of this port (see
    `CSEproofStep.lean`), the program is transformed as a whole: the
    definitions map and read-only memory used by the transformation are those
    of the whole source program, so the `linkorder cu prog` components of
    `match_states` are dropped;
  * the transformed function is described explicitly (`transfFunction'`), as
    in `CSEproofStep.lean`;
  * the neededness analysis is solved in the free lattice `NA.lat`; its
    results are read with CompCert's order through `NAge_of_free`;
  * the properties of external functions and inline assembly that CompCert
    assumes as axioms are explicit hypotheses (`hext`, `hasm`, `hextj`,
    `hasmj`, `hextp`, `hasmp`).
-/
import CCLib.x86.Deadcodeproof
import CCLib.x86.CSEproofStep
import CCLib.x86.ValueAnalysisSoundInit
import CCLib.common.SimulationEventually

namespace CC
namespace X86
namespace Deadcodeproof

open ValueDomain ValueAnalysis RTL NeedDomain NeedOp Deadcode Op Smallstep
open Integers (Ptrofs)

theorem vagree_int_zero (v : Val) : vagree v (.Vint Integers.Int.zero) (.I Integers.Int.zero) := by
  cases v <;> simp only [vagree]
  intro i _ h
  simp [Integers.Int.testbit, Integers.Int.zero, Integers.MI.testbit, Integers.MI.zero] at h

section PRESERVATION
variable (o : ValueAOp.Options) (prog : RTL.Program)

/-- `Deadcodeproof.vanalyze` -/
def vanalyze (f : RTL.Function) : PMap VAState :=
  ValueAnalysis.analyze o  (romemFor o prog) f

/-- The neededness analysis of `f`, as computed by `transf_function`. -/
def analyzeFn (f : RTL.Function) : Option (PMap NAT) :=
  Deadcode.analyze o f prog.defmap (vanalyze o  prog f)

/-- The transformed function, for a given result of the analysis. -/
def transfFunction' (f : RTL.Function) (an : PMap NAT) : RTL.Function :=
  { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_stacksize := f.fn_stacksize,
    fn_code := PTree.map (transfInstr o prog.defmap (vanalyze o  prog f) an) f.fn_code,
    fn_entrypoint := f.fn_entrypoint }

/-- The abstract state after instruction `pc` (`transfer f … pc an!!pc`). -/
abbrev transferAt (f : RTL.Function) (an : PMap NAT) (pc : Node) : NAT :=
  Deadcode.transfer o f prog.defmap (vanalyze o  prog f) pc (an.get pc)

/-- `Deadcodeproof.match_stackframes` (one frame) -/
inductive MatchStackframe : RTL.Stackframe → RTL.Stackframe → Prop where
  | intro (res f sp pc e te an) :
      analyzeFn o  prog f = some an →
      (∀ v tv, Val.Lessdef v tv →
        eagree (e.set res v) (te.set res tv) (transferAt o  prog f an pc).1) →
      MatchStackframe (.Stackframe res f (.Vptr sp Ptrofs.zero) pc e)
        (.Stackframe res (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te)

/-- `Deadcodeproof.match_states` -/
inductive MatchStates : RTL.State → RTL.State → Prop where
  | regular (s f sp pc e m ts te tm an) :
      ListForall2 (MatchStackframe o  prog) s ts →
      analyzeFn o  prog f = some an →
      eagree e te (transferAt o  prog f an pc).1 →
      Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2) →
      MatchStates (.State s f (.Vptr sp Ptrofs.zero) pc e m)
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm)
  | call (s f args m ts tf targs tm) :
      ListForall2 (MatchStackframe o  prog) s ts →
      Deadcode.transfFundef o  prog.defmap (romemFor o prog) f = .OK tf →
      Val.LessdefList args targs → Mem.Extends m tm →
      MatchStates (.Callstate s f args m) (.Callstate ts tf targs tm)
  | ret (s v m ts tv tm) :
      ListForall2 (MatchStackframe o  prog) s ts → Val.Lessdef v tv → Mem.Extends m tm →
      MatchStates (.Returnstate s v m) (.Returnstate ts tv tm)

variable {o  prog}

/-- `Deadcodeproof.analyze_successors` -/
theorem analyze_successors {f : RTL.Function} {an : PMap NAT} {pc pc' : Node} {i : Instruction}
    (AN : analyzeFn o  prog f = some an) (hc : f.fn_code.get pc = some i)
    (hs : pc' ∈ successorsInstr i) :
    NAge (an.get pc) (transferAt o  prog f an pc') := by
  apply NAge_of_free
  letI := NA.lat
  refine Kildall.Backward.fixpoint_solution (NS := NodeSetBackward) f.fn_code successorsInstr
    (Deadcode.transfer o f prog.defmap (vanalyze o  prog f)) an pc i pc' AN hc hs ?_
  intro n a hn
  unfold Deadcode.transfer
  rw [hn]
  exact Semilattice.eq_refl _

/-- `Deadcodeproof.match_succ_states` -/
theorem match_succ_states {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block}
    {pc pc' : Node} {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {i : Instruction}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an) (hc : f.fn_code.get pc = some i)
    (hs : pc' ∈ successorsInstr i)
    (ENV : eagree e te (an.get pc).1) (MEM : Magree m tm (nlive prog.globalenv sp (an.get pc).2)) :
    MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' e m)
      (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc' te tm) := by
  obtain ⟨A, B⟩ := analyze_successors AN hc hs
  exact .regular _ _ _ _ _ _ _ _ _ _ STACKS AN (eagree_ge ENV A)
    (magree_monotone MEM fun b ofs h => B _ _ _ _ h)

omit o  prog in
/-- `Deadcodeproof.transf_function_at` -/
theorem transf_function_at {o : ValueAOp.Options}
    {prog : RTL.Program} {f : RTL.Function} {an : PMap NAT} {pc : Node}
    {i : Instruction} (h : f.fn_code.get pc = some i) :
    (transfFunction' o  prog f an).fn_code.get pc =
      some (transfInstr o prog.defmap (vanalyze o  prog f) an pc i) := by
  simp [transfFunction', PTree.gmap, h]

omit o  prog in
/-- `Deadcodeproof.sig_function_translated` -/
theorem sig_function_translated {o : ValueAOp.Options}
    {dm : Defmap} {rm : Romem} {f tf : RTL.Fundef}
    (h : Deadcode.transfFundef o  dm rm f = .OK tf) : funsig tf = funsig f := by
  cases f with
  | Internal f =>
    unfold Deadcode.transfFundef ASTFundef.transfPartial at h
    dsimp only at h
    cases h' : Deadcode.transfFunction o  dm rm f with
    | Error _ => rw [h'] at h; cases h
    | OK tf' =>
      rw [h'] at h; cases h
      unfold Deadcode.transfFunction at h'
      dsimp only at h'
      split at h'
      · cases h'; rfl
      · cases h'
  | External ef =>
    unfold Deadcode.transfFundef ASTFundef.transfPartial at h
    cases h; rfl

variable {tprog : RTL.Program} (TRANSF : Deadcode.transfProgram o  prog = .OK tprog)
include TRANSF

theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

theorem functions_translated {v : Val} {f : RTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧
      Deadcode.transfFundef o  prog.defmap (romemFor o prog) f = .OK tf :=
  find_funct_transf_partial TRANSF h

theorem function_ptr_translated {b : Block} {f : RTL.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧
      Deadcode.transfFundef o  prog.defmap (romemFor o prog) f = .OK tf :=
  find_funct_ptr_transf_partial TRANSF h

/-- `Deadcodeproof.find_function_translated` -/
theorem find_function_translated {ros : Sum Reg Ident} {rs trs : RTL.Regset} {fd : RTL.Fundef}
    {ne : Nenv} (h : findFunction prog.globalenv ros rs = some fd)
    (EA : eagree rs trs (addRosNeedAll ros ne)) :
    ∃ tfd, findFunction tprog.globalenv ros trs = some tfd ∧
      Deadcode.transfFundef o  prog.defmap (romemFor o prog) fd = .OK tfd := by
  cases ros with
  | inl r =>
    simp only [findFunction] at h ⊢
    have L := add_need_all_lessdef (r := r) EA
    revert h
    generalize rs.get r = a at L
    generalize trs.get r = b at L
    intro h
    cases L with
    | refl => exact functions_translated TRANSF h
    | undef => simp [Genv.findFunct] at h
  | inr id =>
    simp only [findFunction] at h ⊢
    rw [symbols_preserved TRANSF]
    cases e : Genv.findSymbol prog.globalenv id with
    | none => rw [e] at h; cases h
    | some b => rw [e] at h; exact function_ptr_translated TRANSF h


/-! ## The simulation diagram: individual instructions -/

omit TRANSF in
/-- `step_simulation`, case `Inop`. -/
theorem step_Inop {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (hc : f.fn_code.get pc = some (.Inop pc')) :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' e m) S2' := by
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  simp only [transfInstr] at TI
  have ST : transferAt o  prog f an pc = an.get pc := by
    simp only [transferAt, Deadcode.transfer, hc]
  rw [ST] at ENV MEM
  exact ⟨_, .Inop _ _ _ _ _ _ _ TI,
    match_succ_states STACKS AN hc (by simp [successorsInstr]) ENV MEM⟩

/-- `step_simulation`, case `Iop`. -/
theorem step_Iop {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {op : Operation} {args : List Reg}
    {res : Reg} {v : Val}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (hc : f.fn_code.get pc = some (.Iop op args res pc'))
    (hv : evalOperation prog.globalenv (.Vptr sp Ptrofs.zero) op (e.getList args) m = some v) :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' (e.set res v) m) S2' := by
  have hsym := symbols_preserved TRANSF
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  have SUCC : pc' ∈ successorsInstr (.Iop op args res pc') := by simp [successorsInstr]
  rcases ANPC : an.get pc with ⟨ne, nm⟩
  simp only [transfInstr, ANPC] at TI
  simp only [transferAt, Deadcode.transfer, hc, ANPC] at ENV MEM
  have PRESERVED : isDead (nreg ne res) = false →
      eagree e te (addNeeds args (needsOfOperation op (nreg ne res)) (kill res ne)) →
      Magree m tm (nlive prog.globalenv sp nm) →
      (transfFunction' o  prog f an).fn_code.get pc = some (.Iop op args res pc') →
      ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' (e.set res v) m) S2' := by
    intro DEAD ENV MEM TI
    obtain ⟨tv, A, B⟩ := needs_of_operation_sound prog.globalenv sp MEM.ma_perm hv
      (add_needs_vagree ENV) (is_dead_sound_2 DEAD)
    refine ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ tv TI
      (by rw [Op.evalOperation_preserved _ _ hsym]; exact A), ?_⟩
    exact match_succ_states STACKS AN hc SUCC
      (by rw [ANPC]; exact eagree_update res B (add_needs_eagree ENV)) (by rw [ANPC]; exact MEM)
  cases DEAD : isDead (nreg ne res)
  · cases INTZERO : isIntZero (nreg ne res)
    · cases RED : operationIsRedundant op (nreg ne res)
      · simp only [DEAD, INTZERO, RED, Bool.false_eq_true, if_false] at ENV MEM TI
        exact PRESERVED DEAD ENV MEM TI
      · simp only [DEAD, INTZERO, RED, Bool.false_eq_true, if_false, if_true] at ENV MEM TI
        cases args with
        | nil => exact PRESERVED DEAD ENV MEM TI
        | cons r args =>
          have VA : vagree v (te.get r) (nreg ne res) :=
            operation_is_redundant_sound prog.globalenv sp (arg1' := te.get r)
              (args' := te.getList args) RED hv (add_needs_vagree ENV)
          exact ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ (te.get r) TI rfl,
            match_succ_states STACKS AN hc SUCC
              (by rw [ANPC]; exact eagree_update res VA (add_needs_eagree ENV))
              (by rw [ANPC]; exact MEM)⟩
    · simp only [DEAD, INTZERO, Bool.false_eq_true, if_false, if_true] at ENV MEM TI
      have VZ : vagree v (.Vint Integers.Int.zero) (nreg ne res) := by
        rw [is_int_zero_sound INTZERO]; exact vagree_int_zero v
      exact ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ (.Vint Integers.Int.zero) TI rfl,
        match_succ_states STACKS AN hc SUCC
          (by rw [ANPC]; exact eagree_update res VZ ENV) (by rw [ANPC]; exact MEM)⟩
  · simp only [DEAD, if_true] at ENV MEM TI
    exact ⟨_, .Inop _ _ _ _ _ _ _ TI,
      match_succ_states STACKS AN hc SUCC
        (by rw [ANPC]; exact eagree_update_dead res (is_dead_sound_1 DEAD) ENV)
        (by rw [ANPC]; exact MEM)⟩

/-- `step_simulation`, case `Iload`. -/
theorem step_Iload {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {chunk : Chunk} {addr : Addressing}
    {args : List Reg} {dst : Reg} {a v : Val}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Iload chunk addr args dst pc'))
    (ha : evalAddressing prog.globalenv (.Vptr sp Ptrofs.zero) addr (e.getList args) = some a)
    (hl : Mem.loadv chunk m a = some v) :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' (e.set dst v) m) S2' := by
  have hsym := symbols_preserved TRANSF
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  have SUCC : pc' ∈ successorsInstr (.Iload chunk addr args dst pc') := by simp [successorsInstr]
  rcases ANPC : an.get pc with ⟨ne, nm⟩
  simp only [transfInstr, ANPC] at TI
  simp only [transferAt, Deadcode.transfer, hc, ANPC] at ENV MEM
  cases DEAD : isDead (nreg ne dst)
  · cases INTZERO : isIntZero (nreg ne dst)
    · simp only [DEAD, INTZERO, Bool.false_eq_true, if_false] at ENV MEM TI
      obtain ⟨ta, U, V⟩ := Op.evalAddressing_lessdef _ _ _ (add_needs_all_lessdef ENV) ha
      obtain ⟨b, i, rfl⟩ : ∃ b i, a = .Vptr b i := by
        cases a <;> first | exact ⟨_, _, rfl⟩ | simp [Mem.loadv] at hl
      cases V
      obtain ⟨bc, P, GM, SPM⟩ := aaddressing_sound SOUND ha
      obtain ⟨tv, A, B⟩ := magree_loadv MEM hl (fun j h1 h2 =>
        nlive_add prog.globalenv sp nm GM SPM P ⟨h1, h2⟩)
      exact ⟨_, .Iload _ _ _ _ _ _ _ _ _ _ _ (.Vptr b i) tv TI
        (by rw [Op.evalAddressing_preserved _ _ hsym]; exact U) A,
        match_succ_states STACKS AN hc SUCC
          (by rw [ANPC]; exact eagree_update dst (vagree_lessdef _ B) (add_needs_all_eagree ENV))
          (by rw [ANPC]; exact magree_monotone MEM fun _ _ h => incl_nmem_add _ _ _ _ h)⟩
    · simp only [DEAD, INTZERO, Bool.false_eq_true, if_false, if_true] at ENV MEM TI
      have VZ : vagree v (.Vint Integers.Int.zero) (nreg ne dst) := by
        rw [is_int_zero_sound INTZERO]; exact vagree_int_zero v
      exact ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ (.Vint Integers.Int.zero) TI rfl,
        match_succ_states STACKS AN hc SUCC
          (by rw [ANPC]; exact eagree_update dst VZ ENV) (by rw [ANPC]; exact MEM)⟩
  · simp only [DEAD, if_true] at ENV MEM TI
    exact ⟨_, .Inop _ _ _ _ _ _ _ TI,
      match_succ_states STACKS AN hc SUCC
        (by rw [ANPC]; exact eagree_update_dead dst (is_dead_sound_1 DEAD) ENV)
        (by rw [ANPC]; exact MEM)⟩

/-- `step_simulation`, case `Istore`. -/
theorem step_Istore {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {chunk : Chunk} {addr : Addressing}
    {args : List Reg} {src : Reg} {a : Val} {m' : Mem}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (SOUND : SoundState o  prog (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hc : f.fn_code.get pc = some (.Istore chunk addr args src pc'))
    (ha : evalAddressing prog.globalenv (.Vptr sp Ptrofs.zero) addr (e.getList args) = some a)
    (hs : Mem.storev chunk m a (e.get src) = some m') :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' e m') S2' := by
  have hsym := symbols_preserved TRANSF
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  have SUCC : pc' ∈ successorsInstr (.Istore chunk addr args src pc') := by simp [successorsInstr]
  rcases ANPC : an.get pc with ⟨ne, nm⟩
  simp only [transfInstr, ANPC] at TI
  simp only [transferAt, Deadcode.transfer, hc, ANPC] at ENV MEM
  obtain ⟨b, i, rfl⟩ : ∃ b i, a = .Vptr b i := by
    cases a <;> first | exact ⟨_, _, rfl⟩ | simp [Mem.storev] at hs
  obtain ⟨bc, P, GM, SPM⟩ := aaddressing_sound SOUND ha
  cases CONTAINS : nmemContains nm (aaddressing o ((vanalyze o  prog f).get pc) addr args)
      (sizeChunk chunk)
  · simp only [CONTAINS, Bool.false_eq_true, if_false] at ENV MEM TI
    have MEM' := magree_store_left MEM (Mem.storev_store hs)
      (fun j h1 h2 => nlive_contains prog.globalenv sp GM SPM P CONTAINS ⟨h1, h2⟩)
    exact ⟨_, .Inop _ _ _ _ _ _ _ TI,
      match_succ_states STACKS AN hc SUCC (by rw [ANPC]; exact ENV) (by rw [ANPC]; exact MEM')⟩
  · simp only [CONTAINS, if_true] at ENV MEM TI
    obtain ⟨ta, U, V⟩ := Op.evalAddressing_lessdef _ _ _ (add_needs_all_lessdef ENV) ha
    cases V
    obtain ⟨tm', A, B⟩ := magree_storev_parallel (Q := nlive prog.globalenv sp nm) MEM hs
      (add_need_vagree (add_needs_all_eagree ENV))
      (fun b' j hq hout => nlive_remove prog.globalenv sp GM SPM P hq hout)
    exact ⟨_, .Istore _ _ _ _ _ _ _ _ _ _ _ (.Vptr b i) tm' TI
      (by rw [Op.evalAddressing_preserved _ _ hsym]; exact U) A,
      match_succ_states STACKS AN hc SUCC
        (by rw [ANPC]; exact add_need_eagree (add_needs_all_eagree ENV)) (by rw [ANPC]; exact B)⟩

/-- `step_simulation`, case `Icall`. -/
theorem step_Icall {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc pc' : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {sig : Signature} {ros : Sum Reg Ident}
    {args : List Reg} {res : Reg} {fd : RTL.Fundef}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (hc : f.fn_code.get pc = some (.Icall sig ros args res pc'))
    (hf : findFunction prog.globalenv ros e = some fd) (hsig : funsig fd = sig) :
    (∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog
        (.Callstate (.Stackframe res f (.Vptr sp Ptrofs.zero) pc' e :: s) fd (e.getList args) m)
        S2') ∨
    (∃ S2' n, Smallstep.Plus (RTL.Step tprog.globalenv)
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      Smallstep.Eventually (RTL.Step prog.globalenv) RTL.FinalState n
        (.Callstate (.Stackframe res f (.Vptr sp Ptrofs.zero) pc' e :: s) fd (e.getList args) m)
        (fun S3 => MatchStates o  prog S3 S2')) := by
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  have SUCC : pc' ∈ successorsInstr (.Icall sig ros args res pc') := by simp [successorsInstr]
  rcases ANPC : an.get pc with ⟨ne, nm⟩
  simp only [transfInstr, ANPC] at TI
  simp only [transferAt, Deadcode.transfer, hc, ANPC] at ENV MEM
  cases IK : isKnownRuntimeFunction prog.defmap ros with
  | none =>
    simp only [IK] at ENV MEM TI
    obtain ⟨tfd, FIND', TFD⟩ := find_function_translated TRANSF hf (add_needs_all_eagree ENV)
    refine .inl ⟨_, .Icall _ _ _ _ _ _ _ _ _ _ _ _ TI FIND'
      (by rw [sig_function_translated TFD]; exact hsig),
      .call _ _ _ _ _ _ _ _ (.cons (.intro _ _ _ _ _ _ _ AN (fun v tv LD => ?_)) STACKS) TFD
        (add_needs_all_lessdef ENV) (magree_extends (nlive_all _ _) MEM)⟩
    obtain ⟨A, _⟩ := analyze_successors AN hc SUCC
    rw [ANPC] at A
    exact eagree_ge (eagree_update res (vagree_lessdef _ LD)
      (add_ros_need_eagree (add_needs_all_eagree ENV))) A
  | some bf =>
    simp only [IK] at ENV MEM TI
    obtain ⟨name, sg, rfl, LK⟩ := CSEproof.isKnownRuntimeFunction_sound IK hf
    have EV : ∀ (P : RTL.State → Prop),
        (∀ v, (Builtins.builtinFunctionSem bf).sem (e.getList args) = some v →
          P (.State s f (.Vptr sp Ptrofs.zero) pc' (e.set res v) m)) →
        Smallstep.Eventually (RTL.Step prog.globalenv) RTL.FinalState 2
          (.Callstate (.Stackframe res f (.Vptr sp Ptrofs.zero) pc' e :: s)
            (.External (.EF_runtime name sg)) (e.getList args) m) P := by
      intro P PSPEC
      refine .later (fun r F => by cases F) (fun t s1 S1 => ?_) (fun t s1 S1 => ?_)
      · cases S1 with
        | function_external _ _ _ _ _ _ _ hcall =>
          change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
          simp only [builtinOrExternalSem, LK] at hcall
          cases hcall; rfl
      · cases S1 with
        | function_external _ _ _ _ _ _ _ hcall =>
          change builtinOrExternalSem name sg _ _ _ _ _ _ at hcall
          simp only [builtinOrExternalSem, LK] at hcall
          cases hcall with
          | intro _ _ vr _ hsem =>
          exact .later (fun r F => by cases F) (fun t s2 S2 => by cases S2; rfl)
            (fun t s2 S2 => by cases S2; exact .now (PSPEC _ hsem))
    cases DEAD : isDead (nreg ne res)
    · simp only [DEAD, Bool.false_eq_true, if_false] at ENV MEM TI
      obtain ⟨tfd, FIND', TFD⟩ := find_function_translated TRANSF hf (add_needs_all_eagree ENV)
      unfold Deadcode.transfFundef ASTFundef.transfPartial at TFD
      cases TFD
      cases SEM : (Builtins.builtinFunctionSem bf).sem (e.getList args) with
      | some vres =>
        obtain ⟨vres', SEM', LDRES⟩ :=
          Builtins.builtinFunctionSem_lessdef bf SEM (add_needs_all_lessdef ENV)
        refine .inr ⟨_, 2, plus_left (.Icall _ _ _ _ _ _ _ _ _ _ _ _ TI FIND' hsig)
          (star_two (.function_external _ _ _ vres' E0 tm tm ?_) (.return _ _ _ _ _ _ _ _) rfl)
          rfl, EV _ (fun v hv => ?_)⟩
        · change builtinOrExternalSem name sg _ _ _ _ _ _
          simp only [builtinOrExternalSem, LK]
          exact .intro _ _ _ _ SEM'
        · rw [SEM] at hv; cases hv
          have ENV' := eagree_update res (vagree_lessdef _ LDRES)
            (add_ros_need_eagree (add_needs_all_eagree ENV))
          exact match_succ_states STACKS AN hc SUCC (by rw [ANPC]; exact ENV')
            (by rw [ANPC]; exact MEM)
      | none =>
        exact .inr ⟨_, 2, plus_one (.Icall _ _ _ _ _ _ _ _ _ _ _ _ TI FIND' hsig),
          EV _ (fun v hv => by rw [SEM] at hv; cases hv)⟩
    · simp only [DEAD, if_true] at ENV MEM TI
      exact .inr ⟨_, 2, plus_one (.Inop _ _ _ _ _ _ _ TI), EV _ (fun v _ =>
        match_succ_states STACKS AN hc SUCC
          (by rw [ANPC]; exact eagree_update_dead res (is_dead_sound_1 DEAD) ENV)
          (by rw [ANPC]; exact MEM))⟩

/-- `step_simulation`, case `Itailcall`. -/
theorem step_Itailcall {s ts : List RTL.Stackframe} {f : RTL.Function} {stk : Block} {pc : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {sig : Signature} {ros : Sum Reg Ident}
    {args : List Reg} {fd : RTL.Fundef} {m' : Mem}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv stk (transferAt o  prog f an pc).2))
    (hc : f.fn_code.get pc = some (.Itailcall sig ros args))
    (hf : findFunction prog.globalenv ros e = some fd) (hsig : funsig fd = sig)
    (hfree : Mem.free m stk 0 f.fn_stacksize = some m') :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr stk Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.Callstate s fd (e.getList args) m') S2' := by
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  simp only [transfInstr] at TI
  simp only [transferAt, Deadcode.transfer, hc] at ENV MEM
  obtain ⟨tfd, FIND', TFD⟩ := find_function_translated TRANSF hf (add_needs_all_eagree ENV)
  obtain ⟨tm', C, D⟩ := magree_free (Q := nlive prog.globalenv stk nmemAll) MEM hfree
    (fun b' i _ hout => nlive_dead_stack prog.globalenv stk _ b' i hout)
  exact ⟨_, .Itailcall _ _ _ _ _ _ _ _ _ _ _ TI FIND'
    (by rw [sig_function_translated TFD]; exact hsig) C,
    .call _ _ _ _ _ _ _ _ STACKS TFD (add_needs_all_lessdef ENV)
      (magree_extends (nlive_all _ _) D)⟩

omit TRANSF in
/-- `step_simulation`, case `Icond`. -/
theorem step_Icond {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {cond : Condition} {args : List Reg}
    {ifso ifnot : Node} {b : Bool}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (hc : f.fn_code.get pc = some (.Icond cond args ifso ifnot))
    (hcond : evalCondition cond (e.getList args) m = some b) :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog
        (.State s f (.Vptr sp Ptrofs.zero) (if b then ifso else ifnot) e m) S2' := by
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  have SUCC : (if b then ifso else ifnot) ∈ successorsInstr (.Icond cond args ifso ifnot) := by
    cases b <;> simp [successorsInstr]
  rcases ANPC : an.get pc with ⟨ne, nm⟩
  simp only [transfInstr] at TI
  simp only [transferAt, Deadcode.transfer, hc, ANPC] at ENV MEM
  by_cases EQ : ifso = ifnot
  · subst EQ
    simp only [if_true] at ENV MEM TI
    have : (if b then ifso else ifso) = ifso := by cases b <;> rfl
    rw [this] at SUCC ⊢
    exact ⟨_, .Inop _ _ _ _ _ _ _ TI,
      match_succ_states STACKS AN hc SUCC (by rw [ANPC]; exact ENV) (by rw [ANPC]; exact MEM)⟩
  · simp only [EQ, if_false] at ENV MEM TI
    exact ⟨_, .Icond _ _ _ _ _ _ _ _ _ _ b _ TI
      (needs_of_condition_sound MEM.ma_perm hcond (add_needs_vagree ENV)) rfl,
      match_succ_states STACKS AN hc SUCC (by rw [ANPC]; exact add_needs_eagree ENV)
        (by rw [ANPC]; exact MEM)⟩

omit TRANSF in
/-- `step_simulation`, case `Ijumptable`. -/
theorem step_Ijumptable {s ts : List RTL.Stackframe} {f : RTL.Function} {sp : Block}
    {pc pc' : Node} {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {arg : Reg}
    {tbl : List Node} {n : Integers.Int}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (AN : analyzeFn o  prog f = some an)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv sp (transferAt o  prog f an pc).2))
    (hc : f.fn_code.get pc = some (.Ijumptable arg tbl))
    (hn : e.get arg = .Vint n) (hl : CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some pc') :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr sp Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.State s f (.Vptr sp Ptrofs.zero) pc' e m) S2' := by
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  rcases ANPC : an.get pc with ⟨ne, nm⟩
  simp only [transfInstr] at TI
  simp only [transferAt, Deadcode.transfer, hc, ANPC] at ENV MEM
  have hn' : te.get arg = .Vint n := by
    have := add_need_all_lessdef ENV
    rw [hn] at this
    generalize te.get arg = w at this ⊢
    cases this
    rfl
  exact ⟨_, .Ijumptable _ _ _ _ _ _ _ _ n _ TI hn' hl,
    match_succ_states STACKS AN hc (CminorSel.listNthZ_mem hl)
      (by rw [ANPC]; exact add_need_all_eagree ENV) (by rw [ANPC]; exact MEM)⟩

omit TRANSF in
/-- `step_simulation`, case `Ireturn`. -/
theorem step_Ireturn {s ts : List RTL.Stackframe} {f : RTL.Function} {stk : Block} {pc : Node}
    {e te : RTL.Regset} {m tm : Mem} {an : PMap NAT} {or : Option Reg} {m' : Mem}
    (STACKS : ListForall2 (MatchStackframe o  prog) s ts)
    (ENV : eagree e te (transferAt o  prog f an pc).1)
    (MEM : Magree m tm (nlive prog.globalenv stk (transferAt o  prog f an pc).2))
    (hc : f.fn_code.get pc = some (.Ireturn or))
    (hfree : Mem.free m stk 0 f.fn_stacksize = some m') :
    ∃ S2', RTL.Step tprog.globalenv
        (.State ts (transfFunction' o  prog f an) (.Vptr stk Ptrofs.zero) pc te tm) E0 S2' ∧
      MatchStates o  prog (.Returnstate s (regmapOptget or .Vundef e) m') S2' := by
  have TI := transf_function_at (o := o)  (prog := prog) (an := an) hc
  simp only [transfInstr] at TI
  simp only [transferAt, Deadcode.transfer, hc] at ENV MEM
  obtain ⟨tm', A, B⟩ := magree_free (Q := nlive prog.globalenv stk nmemAll) MEM hfree
    (fun b' i _ hout => nlive_dead_stack prog.globalenv stk _ b' i hout)
  refine ⟨_, .Ireturn _ _ _ _ _ _ _ _ TI A, .ret _ _ _ _ _ _ STACKS ?_
    (magree_extends (nlive_all _ _) B)⟩
  cases or with
  | none => exact .refl _
  | some r => exact add_need_all_lessdef ENV

end PRESERVATION

end Deadcodeproof
end X86
end CC
