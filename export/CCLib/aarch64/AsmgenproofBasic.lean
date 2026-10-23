/-
  Correctness proof for AArch64 code generation, part 2 — port of the
  beginning of `aarch64/Asmgenproof.v` and of the lemmas preceding
  `step_simulation`: `match_prog`, preservation of symbols and functions,
  `transf_function_no_overflow`, `exec_straight_exec`, `exec_straight_at`,
  `find_label_goto_label`, `return_address_exists`, the simulation relation
  `match_states`, and the helpers `exec_straight_steps`,
  `exec_straight_steps_goto` and `exec_straight_opt_steps_goto`.

  Differences from Rocq: the `Asmgen.Options`, the `Asm.SymbolSplit` linker
  parameters and the ABI are explicit arguments; `match_prog` is stated as
  `transf_program p = OK tp`, from which the `match_program` facts are
  derived.
-/
import CCLib.aarch64.AsmgenproofLabel

namespace CC
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Smallstep Conventions1

/-- `omega` after unfolding the `Z` abbreviation. -/
local macro "zomega" : tactic => `(tactic| ((try simp only [Z] at *) <;> omega))

/-- `Asmgenproof.match_prog` -/
def MatchProg (o : Options) (p : Mach.Program) (tp : Asm.Program) : Prop :=
  transfProgram o p = .OK tp

/-- `Asmgenproof.transf_program_match` -/
theorem transf_program_match {o : Options} {p : Mach.Program} {tp : Asm.Program}
    (h : transfProgram o p = .OK tp) : MatchProg o p tp := h

/-- `Asmgenproof.transf_function_no_overflow` -/
theorem transf_function_no_overflow {o : Options} {f : Mach.Function} {tf : Asm.Function}
    (h : transfFunction o f = .OK tf) : (tf.fn_code.length : Z) ≤ Integers.Ptrofs.max_unsigned := by
  simp only [transfFunction, res_bind_OK] at h
  obtain ⟨tf', _, h2⟩ := h
  split at h2
  · cases h2
  · rename_i hlt
    simp only [res_pure_OK] at h2; subst h2
    zomega

/-- The code of a translated function is the translation of the Mach code,
    after the two prologue instructions (used for `return_address_exists`). -/
theorem transf_function_inv (o : Options) (f : Mach.Function) (tf : Asm.Function)
    (h : transfFunction o f = .OK tf) :
    ∃ tc ep, translCode o f f.fn_code ep = .OK tc ∧ tc <:+ tf.fn_code := by
  simp only [transfFunction, res_bind_OK] at h
  obtain ⟨tf', h1, h2⟩ := h
  split at h2
  · cases h2
  simp only [res_pure_OK] at h2; subst h2
  simp only [translFunction, res_bind_OK, res_pure_OK] at h1
  obtain ⟨c, hc, rfl⟩ := h1
  rw [transl_code'_transl_code] at hc
  exact ⟨c, true, hc, (List.suffix_cons _ _).trans (List.suffix_cons _ _)⟩

/-- The translation of an instruction ends with its continuation. -/
theorem transl_instr_tail (o : Options) (f : Mach.Function) (i : Mach.Instruction) (ep : Bool)
    (k c : Code) (h : translInstr o f i ep k = .OK c) : k <:+ c := by
  have A := transl_instr_label o f i ep k c h
  cases i <;> simp only [InstrLabelSpec] at A <;>
    first | exact A.1 | (subst A; exact List.suffix_cons _ _)

/-- `Asmgenproof.return_address_exists` -/
theorem return_address_exists (o : Options) (f : Mach.Function) (sg : Signature)
    (ros : Sum Mreg Ident) (c : Mach.Code) (h : (Mach.Instruction.Mcall sg ros :: c) <:+ f.fn_code) :
    ∃ ra, ReturnAddressOffset o f c ra :=
  Asmgenproof0.return_address_exists o (transl_instr_tail o) (transf_function_inv o)
    (fun _ _ h => transf_function_no_overflow h) f sg ros c h

/-! ## The simulation relation -/

/-- `Asmgenproof.match_states` -/
inductive MatchStates (o : Options) (ge : Mach.CGenv) : Mach.State → Asm.State → Prop where
  | intro (s : List Mach.Stackframe) (fb : Block) (sp : Val) (c : Mach.Code) (ep : Bool)
      (ms : Mach.Regset) (m m' : Mem) (rs : Regset) (f : Mach.Function) (tf : Asm.Function)
      (tc : Code) :
      MatchStack o ge s →
      Genv.findFunctPtr ge fb = some (.Internal f) →
      Mem.Extends m m' →
      TranslCodeAtPc o ge (rs .PC) fb f c ep tf tc →
      Agree ms sp rs →
      (ep = true → rs (.IR .X15) = Mach.parentSp s) →
      MatchStates o ge (.State s fb sp c ms m) (.State rs m')
  | call (s : List Mach.Stackframe) (fb : Block) (ms : Mach.Regset) (m m' : Mem) (rs : Regset) :
      MatchStack o ge s →
      Mem.Extends m m' →
      Agree ms (Mach.parentSp s) rs →
      rs .PC = .Vptr fb Integers.Ptrofs.zero →
      rs (.IR RA) = Mach.parentRa s →
      MatchStates o ge (.Callstate s fb ms m) (.State rs m')
  | ret (s : List Mach.Stackframe) (ms : Mach.Regset) (m m' : Mem) (rs : Regset) :
      MatchStack o ge s →
      Mem.Extends m m' →
      Agree ms (Mach.parentSp s) rs →
      rs .PC = Mach.parentRa s →
      MatchStates o ge (.Returnstate s ms m) (.State rs m')

/-- `Asmgenproof.measure` -/
def measure : Mach.State → Nat
  | .State .. => 0
  | .Callstate .. => 0
  | .Returnstate .. => 1

/-! ## Preservation of symbols and functions -/

section PRESERVATION
variable {o : Options} {prog : Mach.Program} {tprog : Asm.Program}
  (TRANSF : MatchProg o prog tprog)
include TRANSF

/-- `Asmgenproof.symbols_preserved` -/
theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

/-- `Asmgenproof.senv_preserved` -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

/-- `Asmgenproof.functions_translated` -/
theorem functions_translated {b : Block} {f : Mach.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧ Asmgen.transfFundef o f = .OK tf :=
  find_funct_ptr_transf_partial TRANSF h

/-- `Asmgenproof.functions_transl` -/
theorem functions_transl {fb : Block} {f : Mach.Function} {tf : Asm.Function}
    (h : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (ht : transfFunction o f = .OK tf) :
    Genv.findFunctPtr tprog.globalenv fb = some (.Internal tf) := by
  obtain ⟨tf', A, B⟩ := functions_translated TRANSF h
  simp only [Asmgen.transfFundef, ASTFundef.transfPartial, ht] at B
  cases B
  exact A

/-! ## Properties of control flow -/

variable (sym : SymbolSplit) (abi : AbiKind)

/-- `Asmgenproof.exec_straight_exec` -/
theorem exec_straight_exec {fb : Block} {f : Mach.Function} {c : Mach.Code} {ep : Bool}
    {tf : Asm.Function} {tc c' : Code} {rs : Regset} {m : Mem} {rs' : Regset} {m' : Mem}
    (h : TranslCodeAtPc o prog.globalenv (rs .PC) fb f c ep tf tc)
    (hx : ExecStraight sym tprog.globalenv tf tc rs m c' rs' m') :
    Smallstep.Plus (Asm.Step sym tprog.globalenv abi) (Asm.State.State rs m) E0 (Asm.State.State rs' m') := by
  generalize hpc : rs .PC = pc at h
  cases h with
  | intro b ofs _ _ _ _ _ FIND TF _ CT =>
    exact exec_straight_steps_1 abi hx (transf_function_no_overflow TF) hpc
      (functions_transl TRANSF FIND TF) CT

omit sym in
/-- `Asmgenproof.exec_straight_at` -/
theorem exec_straight_at {sym : SymbolSplit} {fb : Block} {f : Mach.Function} {c c' : Mach.Code}
    {ep ep' : Bool} {tf : Asm.Function} {tc tc' : Code} {rs : Regset} {m : Mem} {rs' : Regset}
    {m' : Mem}
    (h : TranslCodeAtPc o prog.globalenv (rs .PC) fb f c ep tf tc)
    (ht : translCode o f c' ep' = .OK tc')
    (hx : ExecStraight sym tprog.globalenv tf tc rs m tc' rs' m') :
    TranslCodeAtPc o prog.globalenv (rs' .PC) fb f c' ep' tf tc' := by
  generalize hpc : rs .PC = pc at h
  cases h with
  | intro b ofs _ _ _ _ _ FIND TF _ CT =>
    obtain ⟨ofs', P, Q⟩ := exec_straight_steps_2 hx (transf_function_no_overflow TF) hpc
      (functions_transl TRANSF FIND TF) CT
    rw [P]
    exact .intro _ _ _ _ _ _ _ FIND TF ht Q

omit TRANSF in
/-- `Asmgenproof.find_label_goto_label` -/
theorem find_label_goto_label {f : Mach.Function} {tf : Asm.Function} {lbl : Label}
    {rs : Regset} {m : Mem} {c' : Mach.Code} {b : Block} {ofs : Integers.Ptrofs}
    (hf : Genv.findFunctPtr prog.globalenv b = some (.Internal f))
    (ht : transfFunction o f = .OK tf) (hpc : rs .PC = .Vptr b ofs)
    (hl : Mach.findLabel lbl f.fn_code = some c') :
    ∃ tc' rs', gotoLabel tf lbl rs m = .Next rs' m ∧
      TranslCodeAtPc o prog.globalenv (rs' .PC) b f c' false tf tc' ∧
      ∀ r, r ≠ .PC → rs' r = rs r := by
  have A := transl_find_label lbl o f tf ht
  simp only [hl] at A
  obtain ⟨tc, A, B⟩ := A
  obtain ⟨pos', P, Q, _, R2⟩ := label_pos_code_tail lbl tf.fn_code 0 A
  refine ⟨tc, rs.set .PC (.Vptr b (Integers.Ptrofs.repr pos')), ?_, ?_,
    fun r hr => Regset.gso _ _ hr⟩
  · simp only [gotoLabel, P, hpc]
  · rw [Regset.gss]
    refine .intro _ _ _ _ _ _ _ hf ht B ?_
    have := transf_function_no_overflow ht
    have := code_tail_pos Q
    rw [Integers.Ptrofs.unsigned_repr (by zomega) (by zomega)]
    simpa using Q

/-! ## Helpers for the simulation diagram -/

/-- `Asmgenproof.exec_straight_steps` -/
theorem exec_straight_steps {s : List Mach.Stackframe} {fb : Block} {f : Mach.Function}
    {rs1 : Regset} {i : Mach.Instruction} {c : Mach.Code} {ep : Bool} {tf : Asm.Function}
    {tc : Code} {m1' m2 m2' : Mem} {sp : Val} {ms2 : Mach.Regset}
    (MS : MatchStack o prog.globalenv s) (MEXT : Mem.Extends m2 m2')
    (FIND : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (AT : TranslCodeAtPc o prog.globalenv (rs1 .PC) fb f (i :: c) ep tf tc)
    (H : ∀ k c, translInstr o f i ep k = .OK c →
      ∃ rs2, ExecStraight sym tprog.globalenv tf c rs1 m1' k rs2 m2' ∧ Agree ms2 sp rs2 ∧
        (it1IsParent ep i = true → rs2 (.IR .X15) = Mach.parentSp s)) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) (Asm.State.State rs1 m1') E0 st' ∧
      MatchStates o prog.globalenv (.State s fb sp c ms2 m2) st' := by
  have AT' := AT
  generalize hpc : rs1 .PC = pc at AT'
  cases AT' with
  | intro b ofs _ _ _ _ _ _ _ TC _ =>
    simp only [translCode, res_bind_OK] at TC
    obtain ⟨k, hk, TC⟩ := TC
    obtain ⟨rs2, A, B, C⟩ := H _ _ TC
    exact ⟨_, exec_straight_exec TRANSF sym abi AT A,
      .intro _ _ _ _ _ _ _ _ _ _ _ _ MS FIND MEXT (exec_straight_at TRANSF AT hk A) B C⟩

/-- `Asmgenproof.exec_straight_steps_goto` -/
theorem exec_straight_steps_goto {s : List Mach.Stackframe} {fb : Block} {f : Mach.Function}
    {rs1 : Regset} {i : Mach.Instruction} {c : Mach.Code} {ep : Bool} {tf : Asm.Function}
    {tc : Code} {m1' m2 m2' : Mem} {sp : Val} {ms2 : Mach.Regset} {lbl : Label}
    {c' : Mach.Code}
    (MS : MatchStack o prog.globalenv s) (MEXT : Mem.Extends m2 m2')
    (FIND : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (FL : Mach.findLabel lbl f.fn_code = some c')
    (AT : TranslCodeAtPc o prog.globalenv (rs1 .PC) fb f (i :: c) ep tf tc)
    (H : ∀ k c, translInstr o f i ep k = .OK c →
      ∃ jmp k' rs2, ExecStraight sym tprog.globalenv tf c rs1 m1' (jmp :: k') rs2 m2' ∧
        Agree ms2 sp rs2 ∧
        execInstr sym tprog.globalenv tf jmp rs2 m2' = gotoLabel tf lbl rs2 m2') :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) (Asm.State.State rs1 m1') E0 st' ∧
      MatchStates o prog.globalenv (.State s fb sp c' ms2 m2) st' := by
  generalize hpc : rs1 .PC = pc at AT
  cases AT with
  | intro b ofs _ _ _ _ _ FIND' TF TC CT =>
    simp only [translCode, res_bind_OK] at TC
    obtain ⟨k, _, TC⟩ := TC
    obtain ⟨jmp, k', rs2, A, B, C⟩ := H _ _ TC
    have FN := functions_transl TRANSF FIND' TF
    have NOOV := transf_function_no_overflow TF
    obtain ⟨ofs', PC2, CT2⟩ := exec_straight_steps_2 A NOOV hpc FN CT
    obtain ⟨tc', rs3, GOTO, AT', OTH⟩ := find_label_goto_label (m := m2') FIND' TF PC2 FL
    exact ⟨_, plus_right (plus_star (exec_straight_steps_1 abi A NOOV hpc FN CT))
        (.exec_step_internal _ _ _ _ _ _ _ _ PC2 FN (find_instr_tail CT2) (C.trans GOTO))
        (E0_right _).symm,
      .intro _ _ _ _ _ _ _ _ _ _ _ _ MS FIND MEXT AT'
        (agree_exten B (fun r hr => OTH r (dataPreg_ne_PC hr))) (fun h => by cases h)⟩

/-- `Asmgenproof.exec_straight_opt_steps_goto` -/
theorem exec_straight_opt_steps_goto {s : List Mach.Stackframe} {fb : Block} {f : Mach.Function}
    {rs1 : Regset} {i : Mach.Instruction} {c : Mach.Code} {ep : Bool} {tf : Asm.Function}
    {tc : Code} {m1' m2 m2' : Mem} {sp : Val} {ms2 : Mach.Regset} {lbl : Label}
    {c' : Mach.Code}
    (MS : MatchStack o prog.globalenv s) (MEXT : Mem.Extends m2 m2')
    (FIND : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (FL : Mach.findLabel lbl f.fn_code = some c')
    (AT : TranslCodeAtPc o prog.globalenv (rs1 .PC) fb f (i :: c) ep tf tc)
    (H : ∀ k c, translInstr o f i ep k = .OK c →
      ∃ jmp k' rs2, ExecStraightOpt sym tprog.globalenv tf c rs1 m1' (jmp :: k') rs2 m2' ∧
        Agree ms2 sp rs2 ∧
        execInstr sym tprog.globalenv tf jmp rs2 m2' = gotoLabel tf lbl rs2 m2') :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) (Asm.State.State rs1 m1') E0 st' ∧
      MatchStates o prog.globalenv (.State s fb sp c' ms2 m2) st' := by
  have AT0 := AT
  generalize hpc : rs1 .PC = pc at AT
  cases AT with
  | intro b ofs _ _ _ _ _ FIND' TF TC CT =>
    simp only [translCode, res_bind_OK] at TC
    obtain ⟨k, _, TC⟩ := TC
    obtain ⟨jmp, k', rs2, A, B, C⟩ := H _ _ TC
    have FN := functions_transl TRANSF FIND' TF
    have NOOV := transf_function_no_overflow TF
    cases A with
    | refl =>
      obtain ⟨tc', rs3, GOTO, AT', OTH⟩ := find_label_goto_label FIND' TF hpc FL
      exact ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT)
          (C.trans GOTO)),
        .intro _ _ _ _ _ _ _ _ _ _ _ _ MS FIND MEXT AT'
          (agree_exten B (fun r hr => OTH r (dataPreg_ne_PC hr))) (fun h => by cases h)⟩
    | intro =>
      rename_i A
      obtain ⟨ofs', PC2, CT2⟩ := exec_straight_steps_2 A NOOV hpc FN CT
      obtain ⟨tc', rs3, GOTO, AT', OTH⟩ := find_label_goto_label (m := m2') FIND' TF PC2 FL
      exact ⟨_, plus_right (plus_star (exec_straight_steps_1 abi A NOOV hpc FN CT))
          (.exec_step_internal _ _ _ _ _ _ _ _ PC2 FN (find_instr_tail CT2) (C.trans GOTO))
          (E0_right _).symm,
        .intro _ _ _ _ _ _ _ _ _ _ _ _ MS FIND MEXT AT'
          (agree_exten B (fun r hr => OTH r (dataPreg_ne_PC hr))) (fun h => by cases h)⟩

end PRESERVATION

end Asmgenproof
end CC
