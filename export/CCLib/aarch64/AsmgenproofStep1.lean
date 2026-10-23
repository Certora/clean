/-
  Correctness proof for AArch64 code generation, part 3 — the cases of
  `step_simulation` (`aarch64/Asmgenproof.v`) for the Mach instructions
  that translate to straight-line code: `Mlabel`, `Mgetstack`, `Msetstack`,
  `Mgetparam`, `Mop`, `Mload`, `Mstore` and `Mcond` (both outcomes).

  Each case is a separate theorem; `step_simulation` in
  `aarch64/Asmgenproof.lean` dispatches to them.
-/
import CCLib.aarch64.AsmgenproofBasic
import CCLib.backend.CleanupLabelsproof

namespace CC
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Smallstep Conventions1

section PRESERVATION
variable {o : Options} {prog : Mach.Program} {tprog : Asm.Program}
  (TRANSF : MatchProg o prog tprog) (sym : SymbolSplit) (abi : AbiKind)
include TRANSF

/-- `step_simulation`, case `Mlabel`. -/
theorem step_Mlabel {s fb sp lbl c ms m st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mlabel lbl :: c) ms m) st) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv (.State s fb sp c ms m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG _ =>
    refine exec_straight_steps TRANSF sym abi STACKS MEXT FIND AT ?_
    intro k c TR
    simp only [translInstr] at TR
    cases TR
    exact ⟨nextinstr rs, .one _ _ _ _ _ _ rfl (nextinstr_pc _), agree_nextinstr AG,
      fun h => by cases h⟩

/-- `step_simulation`, case `Mgetstack`. -/
theorem step_Mgetstack {s fb sp ofs ty dst c ms m v st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mgetstack ofs ty dst :: c) ms m) st)
    (H : Mach.loadStack m sp ty ofs = some v) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv (.State s fb sp c (Mach.Regset.set dst v ms) m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG _ =>
    obtain ⟨v', A, B⟩ := Mem.loadv_extends MEXT H (.refl _)
    rw [sp_val AG] at A
    refine exec_straight_steps TRANSF sym abi STACKS MEXT FIND AT ?_
    intro k c TR
    simp only [translInstr] at TR
    obtain ⟨rs', P, Q, R⟩ := loadind_correct sym tprog.globalenv tf .XSP ofs ty dst k c rs m' v'
      TR A (by simp [pregOfIregsp])
    exact ⟨rs', P, agree_set_mreg AG (by rw [Q]; exact B) R, fun h => by cases h⟩

/-- `step_simulation`, case `Msetstack`. -/
theorem step_Msetstack {s fb sp src ofs ty c ms m m2 st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Msetstack src ofs ty :: c) ms m) st)
    (H : Mach.storeStack m sp ty ofs (ms src) = some m2) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c (Mach.undefRegs (destroyedBySetstack ty) ms) m2) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG DXP =>
    obtain ⟨m2', A, B⟩ := Mem.storev_extends MEXT H (.refl _) (preg_val AG src)
    rw [sp_val AG] at A
    refine exec_straight_steps TRANSF sym abi STACKS B FIND AT ?_
    intro k c TR
    simp only [translInstr] at TR
    obtain ⟨rs2, P, Q⟩ := storeind_correct sym tprog.globalenv tf .XSP ofs ty src k c rs m' m2'
      TR A (by simp [pregOfIregsp])
    exact ⟨rs2, P, agree_undef_regs AG (fun r hd _ => Q r hd),
      fun h => by rw [Q _ rfl]; exact DXP h⟩

/-- `step_simulation`, case `Mgetparam`. -/
theorem step_Mgetparam {s fb f0 sp ofs ty dst c ms m v st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mgetparam ofs ty dst :: c) ms m) st)
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f0))
    (H1 : Mach.loadStack m sp Tptr f0.fn_link_ofs = some (Mach.parentSp s))
    (H2 : Mach.loadStack m (Mach.parentSp s) ty ofs = some v) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c (Mach.Regset.set dst v (Mach.Regset.set tempForParentFrame .Vundef ms)) m)
        st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG DXP =>
    rw [FIND] at H0; cases H0
    obtain ⟨parent', A, B⟩ := Mem.loadv_extends MEXT H1 (.refl _)
    rw [sp_val AG] at A
    have e := lessdef_parent_sp STACKS B
    subst e
    obtain ⟨v', C, D⟩ := Mem.loadv_extends MEXT H2 (.refl _)
    refine exec_straight_steps TRANSF sym abi STACKS MEXT FIND AT ?_
    intro k c TR
    simp only [translInstr, res_bind_OK, res_pure_OK] at TR
    obtain ⟨c1, EQ, rfl⟩ := TR
    have AG1 : ∀ {rs1 : Regset}, (∀ r', dataPreg r' = true → r' ≠ .IR .X15 → rs1 r' = rs r') →
        Agree (Mach.Regset.set tempForParentFrame .Vundef ms) sp rs1 :=
      fun ho => agree_set_mreg AG (.undef _) ho
    cases ep with
    | true =>
      obtain ⟨rs1, P, Q, R⟩ := loadind_correct sym tprog.globalenv tf (.RR1 .X15) ofs ty dst k c1
        rs m' v' EQ (by show Mem.loadv _ m' (Val.offsetPtr (rs (.IR .X15)) ofs) = _
                        rw [DXP rfl]; exact C) (by simp [pregOfIregsp])
      refine ⟨rs1, P, agree_set_mreg (AG1 (fun _ _ _ => rfl)) (by rw [Q]; exact D) R, ?_⟩
      intro h
      have hd : dst ≠ .R15 := by simpa [it1IsParent] using h
      rw [R (.IR .X15) rfl (fun he => hd (preg_of_injective (r1 := .R15) he).symm)]
      exact DXP rfl
    | false =>
      obtain ⟨rs1, P, Q, R⟩ := loadptr_correct sym tprog.globalenv tf .XSP f0.fn_link_ofs .X15 c1 m'
        _ rs A (by simp [pregOfIregsp])
      obtain ⟨rs2, S, T, U⟩ := loadind_correct sym tprog.globalenv tf (.RR1 .X15) ofs ty dst k c1
        rs1 m' v' EQ (by show Mem.loadv _ m' (Val.offsetPtr (rs1 (.IR .X15)) ofs) = _
                         rw [Q]; exact C) (by simp [pregOfIregsp])
      refine ⟨rs2, exec_straight_trans P S, agree_set_mreg
        (AG1 (fun r' hd hne => R r' (dataPreg_ne_PC hd) (dataPreg_ne_X16 hd) hne))
        (by rw [T]; exact D) U, ?_⟩
      intro h
      have hd : dst ≠ .R15 := by simpa [it1IsParent] using h
      rw [U (.IR .X15) rfl (fun he => hd (preg_of_injective (r1 := .R15) he).symm), Q]

omit TRANSF in
theorem pregNotin_X15_destroyedByOp (op : Op.Operation) : PregNotin (.IR .X15) (destroyedByOp op) := by
  intro mr hm
  cases op <;> simp [destroyedByOp] at hm <;> subst hm <;> simp [pregOf]

/-- `step_simulation`, case `Mop`. -/
theorem step_Mop {s fb sp op args res c ms m v st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mop op args res :: c) ms m) st)
    (H : Op.evalOperation prog.globalenv sp op (args.map ms) m = some v) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c (Mach.Regset.set res v (Mach.undefRegs (destroyedByOp op) ms)) m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG DXP =>
    have H' : Op.evalOperation tprog.globalenv sp op (args.map ms) m = some v := by
      rw [evalOperation_preserved prog.globalenv tprog.globalenv (symbols_preserved TRANSF)]
      exact H
    obtain ⟨v', A, B⟩ := Op.evalOperation_lessdef tprog.globalenv sp op (preg_vals AG args) MEXT H'
    rw [sp_val AG] at A
    refine exec_straight_steps TRANSF sym abi STACKS MEXT FIND AT ?_
    intro k c TR
    simp only [translInstr] at TR
    obtain ⟨rs2, P, Q, R⟩ := transl_op_correct sym tprog.globalenv tf o op args res k rs m' v' c TR A
    refine ⟨rs2, P, agree_set_undef_mreg AG (Val.lessdef_trans B Q) R, ?_⟩
    intro h
    simp only [it1IsParent, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    rw [R (.IR .X15) rfl (fun he => h.2 (preg_of_injective (r1 := .R15) he).symm)
      (pregNotin_X15_destroyedByOp op)]
    exact DXP h.1

/-- `step_simulation`, case `Mload`. -/
theorem step_Mload {s fb sp chunk addr args dst c ms m a v st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mload chunk addr args dst :: c) ms m) st)
    (H : Op.evalAddressing prog.globalenv sp addr (args.map ms) = some a)
    (H1 : Mem.loadv chunk m a = some v) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c (Mach.Regset.set dst v (Mach.undefRegs (destroyedByLoad chunk addr) ms)) m)
        st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG _ =>
    have H' : Op.evalAddressing tprog.globalenv sp addr (args.map ms) = some a := by
      rw [evalAddressing_preserved prog.globalenv tprog.globalenv (symbols_preserved TRANSF)]
      exact H
    obtain ⟨a', A, B⟩ := Op.evalAddressing_lessdef tprog.globalenv sp addr (preg_vals AG args) H'
    rw [sp_val AG] at A
    obtain ⟨v', C, D⟩ := Mem.loadv_extends MEXT H1 B
    refine exec_straight_steps TRANSF sym abi STACKS MEXT FIND AT ?_
    intro k c TR
    simp only [translInstr] at TR
    obtain ⟨rs2, P, Q, R⟩ := transl_load_correct sym tprog.globalenv tf o chunk addr args dst k c rs
      m' a' v' TR A C
    exact ⟨rs2, P, agree_set_undef_mreg AG (by rw [Q]; exact D) (fun r' hd hne _ => R r' hd hne),
      fun h => by cases h⟩

/-- `step_simulation`, case `Mstore`. -/
theorem step_Mstore {s fb sp chunk addr args src c ms m m2 a st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mstore chunk addr args src :: c) ms m) st)
    (H : Op.evalAddressing prog.globalenv sp addr (args.map ms) = some a)
    (H1 : Mem.storev chunk m a (ms src) = some m2) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c (Mach.undefRegs (destroyedByStore chunk addr) ms) m2) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG _ =>
    have H' : Op.evalAddressing tprog.globalenv sp addr (args.map ms) = some a := by
      rw [evalAddressing_preserved prog.globalenv tprog.globalenv (symbols_preserved TRANSF)]
      exact H
    obtain ⟨a', A, B⟩ := Op.evalAddressing_lessdef tprog.globalenv sp addr (preg_vals AG args) H'
    rw [sp_val AG] at A
    obtain ⟨m2', C, D⟩ := Mem.storev_extends MEXT H1 B (preg_val AG src)
    refine exec_straight_steps TRANSF sym abi STACKS D FIND AT ?_
    intro k c TR
    simp only [translInstr] at TR
    obtain ⟨rs2, P, Q⟩ := transl_store_correct sym tprog.globalenv tf o chunk addr args src k c rs
      m' m2' a' TR A C
    exact ⟨rs2, P, agree_undef_regs AG (fun r hd _ => Q r hd), fun h => by cases h⟩

/-- `step_simulation`, case `Mcond` (branch taken). -/
theorem step_Mcond_true {s fb f0 sp cond args lbl c ms m c' st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mcond cond args lbl :: c) ms m) st)
    (H : Op.evalCondition cond (args.map ms) m = some true)
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f0))
    (H1 : Mach.findLabel lbl f0.fn_code = some c') :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c' (Mach.undefRegs (destroyedByCond cond) ms) m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H0; cases H0
    have EC := Op.evalCondition_lessdef (preg_vals AG args) MEXT H
    refine exec_straight_opt_steps_goto TRANSF sym abi STACKS MEXT FIND H1 AT ?_
    intro k c TR
    simp only [translInstr] at TR
    obtain ⟨rs', jmp, A, B, C⟩ := transl_cond_branch_correct sym tprog.globalenv tf cond args lbl
      k c rs m' true TR EC
    exact ⟨jmp, k, rs', A, agree_undef_regs AG (fun r hd _ => C r hd), by rw [B]; rfl⟩

/-- `step_simulation`, case `Mcond` (branch not taken). -/
theorem step_Mcond_false {s fb sp cond args lbl c ms m st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mcond cond args lbl :: c) ms m) st)
    (H : Op.evalCondition cond (args.map ms) m = some false) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv abi) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c (Mach.undefRegs (destroyedByCond cond) ms) m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG _ =>
    have EC := Op.evalCondition_lessdef (preg_vals AG args) MEXT H
    refine exec_straight_steps TRANSF sym abi STACKS MEXT FIND AT ?_
    intro k c TR
    simp only [translInstr] at TR
    obtain ⟨rs', jmp, A, B, C⟩ := transl_cond_branch_correct sym tprog.globalenv tf cond args lbl
      k c rs m' false TR EC
    exact ⟨nextinstr rs', exec_straight_opt_right A (.one _ _ _ _ _ _ (by rw [B]; rfl) (nextinstr_pc _)),
      agree_nextinstr (agree_undef_regs AG (fun r hd _ => C r hd)), fun h => by cases h⟩

end PRESERVATION

end Asmgenproof
end CC
