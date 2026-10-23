/-
  [RISC-V instance of `CCLib/backend/Tailcallproof.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Recognition of tail calls: correctness proof — port of
  `backend/Tailcallproof.v`.

  Main result: `Tailcallproof.transf_program_correct`, a forward simulation
  from the RTL semantics of a program to the RTL semantics of
  `Tailcall.transfProgram abi` of it.

  Differences from Rocq: `Senv.equiv` is the equality of symbol
  environments `senv_transf`.  Rocq's `external_call_mem_extends` comes
  from the axiom `external_functions_properties` (and
  `inline_assembly_properties`); in the port the semantics of external
  functions and inline assembly are uninterpreted, so the corresponding
  property `ExtcallMemExtends` is an explicit hypothesis (`hext`, `hasm`)
  of the theorem.
-/
import CCLib.riscV.Tailcall
import CCLib.riscV.OpInject
import CCLib.common.EventsExtends
import CCLib.riscV.OpTheory
import CCLib.riscV.Conventions
import CCLib.riscV.Renumberproof

namespace CC
namespace RiscV
namespace Tailcallproof

open RTL Tailcall Smallstep

/-! ### Measuring the number of instructions eliminated -/

/-- `return_measure_rec` -/
def returnMeasureRec : Nat → RTL.Code → RTL.Node → Nat
  | 0, _, _ => 0
  | n + 1, c, pc =>
      match c.get pc with
      | some (.Inop s) => returnMeasureRec n c s + 1
      | some (.Iop _ _ _ s) => returnMeasureRec n c s + 1
      | _ => 0

/-- `return_measure` -/
def returnMeasure (c : RTL.Code) (pc : RTL.Node) : Nat := returnMeasureRec niter c pc

theorem returnMeasureRec_le : ∀ (n : Nat) (c : RTL.Code) (pc : RTL.Node),
    returnMeasureRec n c pc ≤ n
  | 0, _, _ => Nat.le_refl _
  | n + 1, c, pc => by
      simp only [returnMeasureRec]
      split
      · have := returnMeasureRec_le n c ‹_›; omega
      · have := returnMeasureRec_le n c ‹_›; omega
      · omega

/-- `return_measure_bounds` -/
theorem returnMeasure_bounds (c : RTL.Code) (pc : RTL.Node) : returnMeasure c pc ≤ niter :=
  returnMeasureRec_le _ _ _

/-- `is_return_measure_rec` -/
theorem isReturn_measure_rec (f : RTL.Function) :
    ∀ (n n' : Nat) (pc : RTL.Node) (r : Reg), isReturn n f pc r = true → n ≤ n' →
      returnMeasureRec n f.fn_code pc = returnMeasureRec n' f.fn_code pc
  | 0, _, _, _, h, _ => by simp [isReturn] at h
  | n + 1, 0, _, _, _, hle => by omega
  | n + 1, n' + 1, pc, r, h, hle => by
      simp only [isReturn] at h
      simp only [returnMeasureRec]
      split at h
      · rename_i heq; rw [heq]
      · rename_i heq; rw [heq]
      · rename_i s heq
        simp only [heq, isReturn_measure_rec f n n' s r h (by omega)]
      · rename_i op args dst s heq
        simp only [heq]
        split at h
        · cases h
        · rename_i src _
          split at h
          · rw [isReturn_measure_rec f n n' s dst h (by omega)]
          · cases h
      · cases h

/-- `is_return_spec` -/
inductive IsReturnSpec (f : RTL.Function) : RTL.Node → Reg → Prop where
  | none (pc r) : f.fn_code.get pc = some (.Ireturn none) → IsReturnSpec f pc r
  | some (pc r) : f.fn_code.get pc = some (.Ireturn (some r)) → IsReturnSpec f pc r
  | nop (pc r s) : f.fn_code.get pc = some (.Inop s) → IsReturnSpec f s r →
      returnMeasure f.fn_code s < returnMeasure f.fn_code pc → IsReturnSpec f pc r
  | move (pc r r' s) : f.fn_code.get pc = some (.Iop .Omove [r] r' s) → IsReturnSpec f s r' →
      returnMeasure f.fn_code s < returnMeasure f.fn_code pc → IsReturnSpec f pc r

/-- `is_return_charact` -/
theorem isReturn_charact (f : RTL.Function) :
    ∀ (n : Nat) (pc : RTL.Node) (rret : Reg), isReturn n f pc rret = true → n ≤ niter →
      IsReturnSpec f pc rret
  | 0, _, _, h, _ => by simp [isReturn] at h
  | n + 1, pc, rret, h, hle => by
      have hm := isReturn_measure_rec f (n + 1) niter pc rret h hle
      simp only [isReturn] at h
      split at h
      · rename_i heq; exact .none _ _ heq
      · rename_i r heq
        have : r = rret := by simpa using h
        subst this; exact .some _ _ heq
      · rename_i s heq
        refine .nop _ _ s heq (isReturn_charact f n s rret h (by omega)) ?_
        unfold returnMeasure
        rw [← hm, ← isReturn_measure_rec f n niter s rret h (by omega)]
        simp only [returnMeasureRec, heq]; omega
      · rename_i op args dst s heq
        split at h
        · cases h
        · rename_i src hmove
          split at h
          · rename_i hr
            subst hr
            have hop : op = .Omove ∧ args = [rret] := by
              unfold Op.isMoveOperation at hmove
              split at hmove
              · cases hmove; exact ⟨rfl, rfl⟩
              · cases hmove
            obtain ⟨rfl, rfl⟩ := hop
            refine .move _ _ dst s heq (isReturn_charact f n s dst h (by omega)) ?_
            unfold returnMeasure
            rw [← hm, ← isReturn_measure_rec f n niter s dst h (by omega)]
            simp only [returnMeasureRec, heq]; omega
          · cases h
      · cases h

/-- `transf_instr_spec` -/
inductive TransfInstrSpec (f : RTL.Function) : RTL.Instruction → RTL.Instruction → Prop where
  | tailcall (sig ros args res s) : f.fn_stacksize = 0 → IsReturnSpec f s res →
      TransfInstrSpec f (.Icall sig ros args res s) (.Itailcall sig ros args)
  | default (i) : TransfInstrSpec f i i

section

/-- `transf_instr_charact` -/
theorem transfInstr_charact (f : RTL.Function) (pc : RTL.Node) (instr : RTL.Instruction)
    (hs : f.fn_stacksize = 0) : TransfInstrSpec f instr (transfInstr  f pc instr) := by
  cases instr with
  | Icall sig ros args res s =>
      simp only [transfInstr]
      split
      · rename_i h
        simp only [Bool.and_eq_true] at h
        exact .tailcall _ _ _ _ _ hs (isReturn_charact f _ _ _ h.1.1 (Nat.le_refl _))
      · exact .default _
  | _ => exact .default _

/-- `transf_instr_lookup` -/
theorem transfInstr_lookup {f : RTL.Function} {pc : RTL.Node} {i : RTL.Instruction}
    (h : f.fn_code.get pc = some i) :
    ∃ i', (Tailcall.transfFunction  f).fn_code.get pc = some i' ∧ TransfInstrSpec f i i' := by
  unfold Tailcall.transfFunction
  split
  · rename_i hc
    refine ⟨transfInstr  f pc i, ?_, transfInstr_charact  f pc i hc.1⟩
    simp [RTL.transfFunction, h]
  · exact ⟨i, h, .default _⟩

theorem stacksize_preserved (f : RTL.Function) :
    (Tailcall.transfFunction  f).fn_stacksize = f.fn_stacksize := by
  unfold Tailcall.transfFunction; split <;> rfl

theorem entrypoint_preserved (f : RTL.Function) :
    (Tailcall.transfFunction  f).fn_entrypoint = f.fn_entrypoint := by
  unfold Tailcall.transfFunction; split <;> rfl

theorem params_preserved (f : RTL.Function) :
    (Tailcall.transfFunction  f).fn_params = f.fn_params := by
  unfold Tailcall.transfFunction; split <;> rfl

theorem fnsig_preserved (f : RTL.Function) :
    (Tailcall.transfFunction  f).fn_sig = f.fn_sig := by
  unfold Tailcall.transfFunction; split <;> rfl

/-- `sig_preserved` -/
theorem sig_preserved (f : RTL.Fundef) : RTL.funsig (Tailcall.transfFundef  f) = RTL.funsig f := by
  cases f with
  | Internal f => exact fnsig_preserved  f
  | External _ => rfl

end

/-- `regs_lessdef_init_regs` -/
theorem regs_lessdef_init_regs : ∀ (params : List Reg) {vl vl' : List Val},
    Val.LessdefList vl vl' → RegsLessdef (initRegs vl params) (initRegs vl' params)
  | [], vl, vl', h => by
      cases h <;> (intro r; simp [initRegs]; exact .refl _)
  | p :: params, _, _, .nil => by intro r; simp [initRegs]; exact .refl _
  | p :: params, _, _, .cons hv hl => set_reg_lessdef hv (regs_lessdef_init_regs params hl)

/-! ### The simulation -/

section PRESERVATION
variable (prog : RTL.Program)

local notation "tprog" => Tailcall.transfProgram  prog

theorem symbols_preserved (id : Ident) :
    Genv.findSymbol (tprog).globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf (Tailcall.transfFundef ) prog id

theorem senv_preserved : Genv.toSenv (tprog).globalenv = Genv.toSenv prog.globalenv :=
  senv_transf (Tailcall.transfFundef ) prog

theorem functions_translated {v : Val} {f : RTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    Genv.findFunct (tprog).globalenv v = some (Tailcall.transfFundef  f) :=
  find_funct_transf (Tailcall.transfFundef ) h

theorem function_ptr_translated {b : Block} {f : RTL.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    Genv.findFunctPtr (tprog).globalenv b = some (Tailcall.transfFundef  f) :=
  find_funct_ptr_transf (Tailcall.transfFundef ) h

/-- `find_function_translated` -/
theorem find_function_translated {ros : Sum Reg Ident} {rs rs' : RTL.Regset} {fd : RTL.Fundef}
    (h : RTL.findFunction prog.globalenv ros rs = some fd) (hrs : RegsLessdef rs rs') :
    RTL.findFunction (tprog).globalenv ros rs' = some (Tailcall.transfFundef  fd) := by
  cases ros with
  | inl r =>
      simp only [RTL.findFunction] at h ⊢
      have hl := hrs r
      generalize rs.get r = v at hl h
      generalize rs'.get r = v' at hl ⊢
      cases hl with
      | refl => exact functions_translated  prog h
      | undef => cases h
  | inr id =>
      simp only [RTL.findFunction, symbols_preserved] at h ⊢
      cases e : Genv.findSymbol prog.globalenv id with
      | none => rw [e] at h; cases h
      | some b => rw [e] at h; exact function_ptr_translated  prog h

/-- `match_stackframes` -/
inductive MatchStackframes : List RTL.Stackframe → List RTL.Stackframe → Prop where
  | nil : MatchStackframes [] []
  | normal (stk stk' res sp pc rs rs' f) : MatchStackframes stk stk' → RegsLessdef rs rs' →
      MatchStackframes (.Stackframe res f (.Vptr sp Integers.Ptrofs.zero) pc rs :: stk)
        (.Stackframe res (Tailcall.transfFunction  f) (.Vptr sp Integers.Ptrofs.zero) pc rs' :: stk')
  | tail (stk stk' res sp pc rs f) : MatchStackframes stk stk' → IsReturnSpec f pc res →
      f.fn_stacksize = 0 →
      MatchStackframes (.Stackframe res f (.Vptr sp Integers.Ptrofs.zero) pc rs :: stk) stk'

/-- `match_states` -/
inductive MatchStates : RTL.State → RTL.State → Prop where
  | normal (s sp pc rs m s' rs' m' f) : MatchStackframes  s s' → RegsLessdef rs rs' →
      Mem.Extends m m' →
      MatchStates (.State s f (.Vptr sp Integers.Ptrofs.zero) pc rs m)
        (.State s' (Tailcall.transfFunction  f) (.Vptr sp Integers.Ptrofs.zero) pc rs' m')
  | call (s f args m s' args' m') : MatchStackframes  s s' → Val.LessdefList args args' →
      Mem.Extends m m' →
      MatchStates (.Callstate s f args m) (.Callstate s' (Tailcall.transfFundef  f) args' m')
  | ret (s v m s' v' m') : MatchStackframes  s s' → Val.Lessdef v v' → Mem.Extends m m' →
      MatchStates (.Returnstate s v m) (.Returnstate s' v' m')
  | interm (s sp pc rs m s' m' f r v') : MatchStackframes  s s' → Mem.Extends m m' →
      IsReturnSpec f pc r → f.fn_stacksize = 0 → Val.Lessdef (rs.get r) v' →
      MatchStates (.State s f (.Vptr sp Integers.Ptrofs.zero) pc rs m) (.Returnstate s' v' m')

/-- `measure` -/
def measure : RTL.State → Nat
  | .State s f _ pc _ _ => s.length * (niter + 2) + returnMeasure f.fn_code pc + 1
  | .Callstate .. => 0
  | .Returnstate s _ _ => s.length * (niter + 2)

theorem rangePerm_zero (m : Mem) (b : Block) (k : PermKind) (p : Permission) :
    Mem.rangePerm m b 0 0 k p = true := by
  rfl

set_option maxHeartbeats 1000000 in
/-- `transf_step_correct` -/
theorem transf_step_correct
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    {s1 t s2} (hst : RTL.Step prog.globalenv s1 t s2) {s1'} (hm : MatchStates  s1 s1') :
    (∃ s2', RTL.Step (tprog).globalenv s1' t s2' ∧ MatchStates  s2 s2') ∨
    (measure s2 < measure s1 ∧ t = E0 ∧ MatchStates  s2 s1') := by
  have hsym := symbols_preserved  prog
  have hsenv := senv_preserved  prog
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  cases hst with
  | Inop s f sp pc rs m pc' hc =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      exact .inl ⟨_, .Inop _ _ _ _ _ _ _ hi', .normal _ _ _ _ _ _ _ _ _ STK RLD MLD⟩
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ s0 h hspec' hlt =>
        rw [hc] at h; cases h
        exact .inr ⟨by simp only [measure]; omega, rfl,
          .interm _ _ _ _ _ _ _ _ _ _ STK MLD hspec' hsz hv⟩
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Iop s f sp pc rs m op args res pc' v hc hv =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      obtain ⟨tv, EV, LD⟩ := Op.evalOperation_lessdef _ _ _ (regsLessdef_regs RLD args) MLD hv
      refine .inl ⟨_, .Iop _ _ _ _ _ _ _ _ _ _ tv hi' ?_,
        .normal _ _ _ _ _ _ _ _ _ STK (set_reg_lessdef LD RLD) MLD⟩
      rw [Op.evalOperation_preserved prog.globalenv (tprog).globalenv hsym]; exact EV
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ r' s0 h hspec' hlt =>
        rw [hc] at h; cases h
        have : v = rs.get r := by
          simp only [Regmap.getList, List.map] at hv
          injection hv with hv; exact hv.symm
        subst this
        exact .inr ⟨by simp only [measure]; omega, rfl,
          .interm _ _ _ _ _ _ _ _ _ _ STK MLD hspec' hsz (by rw [PMap.gss]; exact hrv)⟩
  | Iload s f sp pc rs m chunk addr args dst pc' a v hc ha hv =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      obtain ⟨ta, EV, LD⟩ := Op.evalAddressing_lessdef _ _ _ (regsLessdef_regs RLD args) ha
      obtain ⟨tv, LOAD, LD'⟩ := Mem.loadv_extends MLD hv LD
      refine .inl ⟨_, .Iload _ _ _ _ _ _ _ _ _ _ _ ta tv hi' ?_ LOAD,
        .normal _ _ _ _ _ _ _ _ _ STK (set_reg_lessdef LD' RLD) MLD⟩
      rw [Op.evalAddressing_preserved prog.globalenv (tprog).globalenv hsym]; exact EV
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Istore s f sp pc rs m chunk addr args src pc' a m1 hc ha hs =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      obtain ⟨ta, EV, LD⟩ := Op.evalAddressing_lessdef _ _ _ (regsLessdef_regs RLD args) ha
      obtain ⟨tm', STORE, MEM'⟩ := Mem.storev_extends MLD hs LD (RLD src)
      refine .inl ⟨_, .Istore _ _ _ _ _ _ _ _ _ _ _ ta tm' hi' ?_ STORE,
        .normal _ _ _ _ _ _ _ _ _ STK RLD MEM'⟩
      rw [Op.evalAddressing_preserved prog.globalenv (tprog).globalenv hsym]; exact EV
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Icall s f sp pc rs m sig ros args res pc' fd hc hf hsig =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      have FIND := find_function_translated  prog hf RLD
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec with
      | tailcall _ _ _ _ _ hsz hret =>
        have hfree : Mem.free m' sp0 0 (Tailcall.transfFunction  f).fn_stacksize =
            some (Mem.uncheckedFree m' sp0 0 0) := by
          rw [stacksize_preserved, hsz]; exact Mem.free_isSome (rangePerm_zero _ _ _ _)
        refine .inl ⟨_, .Itailcall _ _ _ _ _ _ _ _ _ _ _ hi' FIND
          (by rw [sig_preserved]; exact hsig) hfree,
          .call _ _ _ _ _ _ _ (.tail _ _ _ _ _ _ _ STK hret hsz) (regsLessdef_regs RLD args)
            (Mem.free_right_extends MLD hfree ?_)⟩
        intro ofs _ _ _ h1 h2
        rw [stacksize_preserved, hsz] at h2
        omega
      | default =>
        exact .inl ⟨_, .Icall _ _ _ _ _ _ _ _ _ _ _ _ hi' FIND
          (by rw [sig_preserved]; exact hsig),
          .call _ _ _ _ _ _ _ (.normal _ _ _ _ _ _ _ _ STK RLD) (regsLessdef_regs RLD args) MLD⟩
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Itailcall s f stk pc rs m sig ros args fd m1 hc hf hsig hfree =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      have FIND := find_function_translated  prog hf RLD
      obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MLD hfree
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      exact .inl ⟨_, .Itailcall _ _ _ _ _ _ _ _ _ _ _ hi' FIND
        (by rw [sig_preserved]; exact hsig) (by rw [stacksize_preserved]; exact FREE),
        .call _ _ _ _ _ _ _ STK (regsLessdef_regs RLD args) MEM'⟩
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m1 hc hargs hcall =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      obtain ⟨tvargs, EVA, LDA⟩ := evalBuiltinArgs_lessdef (e2 := fun r => rs'.get r) RLD MLD hargs
      obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hcall MLD LDA
      refine .inl ⟨_, .Ibuiltin _ _ _ _ _ _ _ _ _ _ tvargs t tvres tm' hi' ?_ ?_,
        .normal _ _ _ _ _ _ _ _ _ STK (set_res_lessdef B RLD) C⟩
      · rw [hsenv]; exact EVA
      · rw [hsenv]; exact A
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hc hcond hpc =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      exact .inl ⟨_, .Icond _ _ _ _ _ _ _ _ _ _ b _ hi'
        (Op.evalCondition_lessdef (regsLessdef_regs RLD args) MLD hcond) hpc,
        .normal _ _ _ _ _ _ _ _ _ STK RLD MLD⟩
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Ijumptable s f sp pc rs m arg tbl n pc' hc hn hl =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      have hn' : rs'.get arg = .Vint n := by
        have := RLD arg
        rw [hn] at this
        generalize rs'.get arg = v at this ⊢
        cases this
        rfl
      exact .inl ⟨_, .Ijumptable _ _ _ _ _ _ _ _ n _ hi' hn' hl,
        .normal _ _ _ _ _ _ _ _ _ STK RLD MLD⟩
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h => rw [hc] at h; cases h
      | some _ _ h => rw [hc] at h; cases h
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | Ireturn s f stk pc rs m or m1 hc hfree =>
    cases hm with
    | normal _ sp0 _ _ _ s' rs' m' _ STK RLD MLD =>
      obtain ⟨tm', FREE, MEM'⟩ := Mem.free_parallel_extends MLD hfree
      obtain ⟨i', hi', hspec⟩ := transfInstr_lookup  hc
      cases hspec
      refine .inl ⟨_, .Ireturn _ _ _ _ _ _ _ _ hi' (by rw [stacksize_preserved]; exact FREE),
        .ret _ _ _ _ _ _ STK ?_ MEM'⟩
      cases or with
      | none => exact .refl _
      | some r => exact RLD r
    | interm _ sp0 _ _ _ s' m' _ r v' STK MLD hspec hsz hrv =>
      cases hspec with
      | none _ _ h =>
        rw [hc] at h; cases h
        exact .inr ⟨by simp only [measure]; omega, rfl,
          .ret _ _ _ _ _ _ STK (.undef _) (Mem.free_left_extends MLD hfree)⟩
      | some _ _ h =>
        rw [hc] at h; cases h
        exact .inr ⟨by simp only [measure]; omega, rfl,
          .ret _ _ _ _ _ _ STK hrv (Mem.free_left_extends MLD hfree)⟩
      | nop _ _ _ h _ _ => rw [hc] at h; cases h
      | move _ _ _ _ h _ _ => rw [hc] at h; cases h
  | function_internal s f args m m1 stk htyp halloc =>
    cases hm with
    | call _ _ _ _ s' args' m' STK LDA MLD =>
      obtain ⟨tm', ALLOC, MEM'⟩ := Mem.alloc_extends MLD halloc (Int.le_refl _) (Int.le_refl _)
      have hstep := RTL.Step.function_internal (ge := (tprog).globalenv) s'
        (Tailcall.transfFunction  f) args' m' tm' stk
        (by rw [fnsig_preserved]; exact Val.has_argtype_list_lessdef htyp LDA)
        (by rw [stacksize_preserved]; exact ALLOC)
      rw [entrypoint_preserved, params_preserved] at hstep
      exact .inl ⟨_, hstep,
        .normal _ _ _ _ _ _ _ _ _ STK (regs_lessdef_init_regs _ LDA) MEM'⟩
  | function_external s ef args res t m m1 hcall =>
    cases hm with
    | call _ _ _ _ s' args' m' STK LDA MLD =>
      obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hcall MLD LDA
      refine .inl ⟨_, .function_external _ _ _ _ _ _ _ ?_, .ret _ _ _ _ _ _ STK B C⟩
      rw [hsenv]; exact A
  | «return» res f sp pc rs s vres m =>
    cases hm with
    | ret _ _ _ s' v' m' STK LD MLD =>
      cases STK with
      | normal _ stk' _ _ _ _ rs' _ STK RLD =>
        exact .inl ⟨_, .return _ _ _ _ _ _ _ _,
          .normal _ _ _ _ _ _ _ _ _ STK (set_reg_lessdef LD RLD) MLD⟩
      | tail _ _ _ _ _ _ _ STK hret hsz =>
        have := returnMeasure_bounds f.fn_code pc
        refine .inr ⟨?_, rfl,
          .interm _ _ _ _ _ _ _ _ _ _ STK MLD hret hsz (by rw [PMap.gss]; exact LD)⟩
        simp only [measure, List.length_cons, niter] at this ⊢
        rw [Nat.succ_mul]
        omega

/-- `transf_initial_states` -/
theorem transf_initial_states {st1 : RTL.State} (h : RTL.InitialState prog st1) :
    ∃ st2, RTL.InitialState (tprog) st2 ∧ MatchStates  st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
      refine ⟨_, .intro b (Tailcall.transfFundef  f) m0 ?_ ?_ (function_ptr_translated  prog hf) ?_,
        .call _ _ _ _ _ _ _ .nil .nil (Mem.extends_refl _)⟩
      · exact (init_mem_transf (Tailcall.transfFundef ) prog).trans hm
      · rw [symbols_preserved]; exact hs
      · rw [sig_preserved]; exact hsig

/-- `transf_final_states` -/
theorem transf_final_states {st1 st2 : RTL.State} {r : Integers.Int}
    (hm : MatchStates  st1 st2) (h : RTL.FinalState st1 r) : RTL.FinalState st2 r := by
  cases h with
  | intro r m =>
      cases hm with
      | ret _ _ _ s' v' m' STK LD MLD =>
          cases STK
          cases LD
          exact .intro _ _

/-- `transf_program_correct`: tail-call recognition preserves the semantics
    of RTL programs (forward simulation).  The hypotheses `hext` and `hasm`
    state that external functions and inline assembly are compatible with
    memory extensions (`ec_mem_extends`), which CompCert assumes by axiom. -/
theorem transf_program_correct
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge) :
    Smallstep.ForwardSimulation (RTL.semantics prog) (RTL.semantics (tprog)) :=
  Smallstep.forward_simulation_opt (L1 := RTL.semantics prog)
    (L2 := RTL.semantics (tprog)) (MatchStates )
    (fun id => by
      show (Genv.toSenv (tprog).globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved])
    (fun _ h => transf_initial_states  prog h)
    (fun _ _ _ hm h => transf_final_states  hm h)
    measure
    (fun _ _ _ hst _ hm => transf_step_correct  prog hext hasm hst hm)

end PRESERVATION

end Tailcallproof
end RiscV
end CC
