/-
  Correctness of the AArch64 code generator's constructor functions,
  part 2 — port of the "Shifted operands", "Zero- and Sign- extensions" and
  "Extended right shift" sections of `aarch64/Asmgenproof1.v`:
  `transl_shift_not_none`, `or_zero_eval_shift_op_int/long`,
  `add_zero_eval_shift_op_long`, `transl_eval_shift(')`,
  `transl_eval_shiftl(',''')`, `exec_move_extended_base`,
  `exec_move_extended`, `exec_arith_extended`, `exec_shrx32`,
  `exec_shrx64`.
-/
import CCLib.aarch64.Asmgenproof1Imm

namespace CC
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1

/-! ## Shifted operands -/

/-- `Asmgenproof1.transl_shift_not_none` -/
theorem transl_shift_not_none (s : Op.Shift) (a : Integers.Int) : translShift s a ≠ .SOnone := by
  cases s <;> simp [translShift]

/-- `Asmgenproof1.or_zero_eval_shift_op_int` -/
theorem or_zero_eval_shift_op_int (v : Val) {s : ShiftOp} (hs : s ≠ .SOnone) :
    Val.or (.Vint Integers.Int.zero) (evalShiftOpInt v s) = evalShiftOpInt v s := by
  cases s with
  | SOnone => exact absurd rfl hs
  | _ n =>
    cases v <;> simp only [evalShiftOpInt, Val.shl, Val.shru, Val.shr, Val.ror] <;>
      (try split) <;> simp [Val.or, Integers.Int.or_zero_l]

/-- `Asmgenproof1.or_zero_eval_shift_op_long` -/
theorem or_zero_eval_shift_op_long (v : Val) {s : ShiftOp} (hs : s ≠ .SOnone) :
    Val.orl (.Vlong Integers.Int64.zero) (evalShiftOpLong v s) = evalShiftOpLong v s := by
  cases s with
  | SOnone => exact absurd rfl hs
  | _ n =>
    cases v <;> simp only [evalShiftOpLong, Val.shll, Val.shrlu, Val.shrl, Val.rorl] <;>
      (try split) <;> simp [Val.orl, Integers.Int64.or_zero_l]

/-- `Asmgenproof1.add_zero_eval_shift_op_long` -/
theorem add_zero_eval_shift_op_long (v : Val) {s : ShiftOp} (hs : s ≠ .SOnone) :
    Val.addl (.Vlong Integers.Int64.zero) (evalShiftOpLong v s) = evalShiftOpLong v s := by
  cases s with
  | SOnone => exact absurd rfl hs
  | _ n =>
    cases v <;> simp only [evalShiftOpLong, Val.shll, Val.shrlu, Val.shrl, Val.rorl] <;>
      (try split) <;> simp [Val.addl, Integers.Int64.add_zero_l]

/-- `Asmgenproof1.transl_eval_shift` -/
theorem transl_eval_shift (s : Op.Shift) (v : Val) (a : Op.Amount32) :
    evalShiftOpInt v (translShift s a.a32_amount) = Op.evalShift s v a := by
  cases s <;> rfl

/-- `Asmgenproof1.transl_eval_shift'` -/
theorem transl_eval_shift' (s : Op.Shift) (v : Val) (a : Op.Amount32) :
    Val.or (.Vint Integers.Int.zero) (evalShiftOpInt v (translShift s a.a32_amount)) =
      Op.evalShift s v a := by
  rw [or_zero_eval_shift_op_int _ (transl_shift_not_none _ _), transl_eval_shift]

/-- `Asmgenproof1.transl_eval_shiftl` -/
theorem transl_eval_shiftl (s : Op.Shift) (v : Val) (a : Op.Amount64) :
    evalShiftOpLong v (translShift s a.a64_amount) = Op.evalShiftl s v a := by
  cases s <;> rfl

/-- `Asmgenproof1.transl_eval_shiftl'` -/
theorem transl_eval_shiftl' (s : Op.Shift) (v : Val) (a : Op.Amount64) :
    Val.orl (.Vlong Integers.Int64.zero) (evalShiftOpLong v (translShift s a.a64_amount)) =
      Op.evalShiftl s v a := by
  rw [or_zero_eval_shift_op_long _ (transl_shift_not_none _ _), transl_eval_shiftl]

/-- `Asmgenproof1.transl_eval_shiftl''` -/
theorem transl_eval_shiftl'' (s : Op.Shift) (v : Val) (a : Op.Amount64) :
    Val.addl (.Vlong Integers.Int64.zero) (evalShiftOpLong v (translShift s a.a64_amount)) =
      Op.evalShiftl s v a := by
  rw [add_zero_eval_shift_op_long _ (transl_shift_not_none _ _), transl_eval_shiftl]

theorem or_zero_shr (v : Val) (n : Integers.Int) :
    Val.or (.Vint Integers.Int.zero) (Val.shr v (.Vint n)) = Val.shr v (.Vint n) :=
  or_zero_eval_shift_op_int v (s := .SOasr n) (by simp)

theorem orl_zero_shrl (v : Val) (n : Integers.Int) :
    Val.orl (.Vlong Integers.Int64.zero) (Val.shrl v (.Vint n)) = Val.shrl v (.Vint n) :=
  or_zero_eval_shift_op_long v (s := .SOasr n) (by simp)

theorem iwordsize_eq : Integers.Int.iwordsize = Integers.Int.repr 32 := by decide

section CONSTRUCTORS
variable (sym : SymbolSplit) (ge : Asm.CGenv) (fn : Asm.Function)

/-! ## Zero- and sign-extensions -/

/-- `Asmgenproof1.exec_move_extended_base` -/
theorem exec_move_extended_base (rd r1 : Ireg) (ex : Op.Extension) (k : Code) (rs : Regset)
    (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (moveExtendedBase rd r1 ex k) rs m k rs' m ∧
      rs' (.IR rd) = (match ex with
        | .Xsgn32 => Val.longofint (rs (.IR r1))
        | .Xuns32 => Val.longofintu (rs (.IR r1))) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  cases ex <;>
    exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd), nextinstr_set_same _ _ hrd,
      fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩

/-- `Asmgenproof1.exec_move_extended` -/
theorem exec_move_extended (rd r1 : Ireg) (ex : Op.Extension) (a : Op.Amount64) (k : Code)
    (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (moveExtended rd r1 ex a.a64_amount k) rs m k rs' m ∧
      rs' (.IR rd) = Op.evalExtend ex (rs (.IR r1)) a ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  unfold moveExtended
  split
  · rename_i he
    obtain ⟨rs', A, B, C⟩ := exec_move_extended_base sym ge fn rd r1 ex k rs m
    refine ⟨rs', A, ?_, C⟩
    have ha := (Integers.Int.eq_spec _ _).1 he
    rw [B]
    unfold Op.evalExtend
    rw [ha]
    cases ex <;> cases rs (.IR r1) <;>
      first | rfl | (simp only [Val.longofint, Val.longofintu]; rw [shll_zero])
  · obtain ⟨rs', A, B, C⟩ := exec_move_extended_base sym ge fn rd r1 ex
      (.Padd .X rd .XZR rd (.SOlsl a.a64_amount) :: k) rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd)), ?_,
      fun r h1 h2 => by rw [nextinstr_set_other _ _ h1 h2, C r h1 h2]⟩
    rw [nextinstr_set_same _ _ hrd]
    show Val.addl (Val.Vlong Integers.Int64.zero)
      (evalShiftOpLong (rs' (.IR rd)) (translShift .Slsl a.a64_amount)) = _
    rw [transl_eval_shiftl'', B]
    cases ex <;> rfl

/-- `Asmgenproof1.exec_arith_extended` -/
theorem exec_arith_extended (sem : Val → Val → Val)
    (insnX : Iregsp → Iregsp → Ireg → ExtendOp → Instruction)
    (insnS : Ireg → Ireg0 → Ireg → ShiftOp → Instruction)
    (EX : ∀ rd r1 r2 x rs m, execInstr sym ge fn (insnX rd r1 r2 x) rs m =
      .Next (nextinstr (rs.set (pregOfIregsp rd) (sem (rs (pregOfIregsp r1))
        (evalExtend (rs (.IR r2)) x)))) m)
    (ES : ∀ rd r1 r2 s rs m, execInstr sym ge fn (insnS rd r1 r2 s) rs m =
      .Next (nextinstr (rs.set (.IR rd) (sem (ir0x rs r1) (evalShiftOpLong (rs (.IR r2)) s)))) m)
    (rd r1 r2 : Ireg) (ex : Op.Extension) (a : Op.Amount64) (k : Code) (rs : Regset) (m : Mem)
    (hr1 : r1 ≠ .X16) :
    ∃ rs', ExecStraight sym ge fn (arithExtended insnX insnS rd r1 r2 ex a.a64_amount k) rs m k
        rs' m ∧
      rs' (.IR rd) = sem (rs (.IR r1)) (Op.evalExtend ex (rs (.IR r2)) a) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  have hr1' : Preg.IR r1 ≠ .IR .X16 := fun e => hr1 (Preg.IR.inj e)
  unfold arithExtended
  split
  · refine ⟨_, .one _ _ _ _ _ _ (EX (.RR1 rd) (.RR1 r1) _ _ _ _) (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    show nextinstr (rs.set (.IR rd) _) (.IR rd) = _
    rw [nextinstr_set_same _ _ hrd]
    cases ex <;> rfl
  · obtain ⟨rs', A, B, C⟩ := exec_move_extended_base sym ge fn .X16 r2 ex
      (insnS rd r1 .X16 (.SOlsl a.a64_amount) :: k) rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ (ES _ _ _ _ _ _)
      (nextinstr_set_PC _ _ hrd)), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      show sem (rs' (.IR r1)) _ = _
      rw [C _ (by simp) hr1', B]
      cases ex <;> rfl
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        C _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]

/-! ## Extended right shift -/

/-- `Asmgenproof1.exec_shrx32` -/
theorem exec_shrx32 (rd r1 : Ireg) (n : Integers.Int) (k : Code) (v : Val) (rs : Regset) (m : Mem)
    (hv : Val.shrx (rs (.IR r1)) (.Vint n) = some v) (hr1 : r1 ≠ .X16) :
    ∃ rs', ExecStraight sym ge fn (shrx32 rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = v ∧ ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  have hx : Preg.IR .X16 ≠ .PC := by simp
  have hr1' : Preg.IR r1 ≠ .IR .X16 := fun e => hr1 (Preg.IR.inj e)
  have H := Val.shrx_shr_2 hv
  unfold shrx32
  split
  · rename_i he
    rw [if_pos he] at H
    subst H
    exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd), nextinstr_set_same _ _ hrd,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
  · rename_i he
    rw [if_neg he] at H
    subst H
    refine ⟨_, exec_straight_three rfl rfl rfl (nextinstr_set_PC _ _ hx) (nextinstr_set_PC _ _ hx)
      (nextinstr_set_PC _ _ hrd), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      simp only [ir0w, evalShiftOpInt, or_zero_shr]
      rw [nextinstr_set_same _ _ hx, nextinstr_set_other _ _ (by simp) hr1',
        nextinstr_set_same _ _ hx]
      simp only [or_zero_shr, iwordsize_eq]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        nextinstr_set_other _ _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1),
        nextinstr_set_other _ _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]

/-- `Asmgenproof1.exec_shrx64` -/
theorem exec_shrx64 (rd r1 : Ireg) (n : Integers.Int) (k : Code) (v : Val) (rs : Regset) (m : Mem)
    (hv : Val.shrxl (rs (.IR r1)) (.Vint n) = some v) (hr1 : r1 ≠ .X16) :
    ∃ rs', ExecStraight sym ge fn (shrx64 rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = v ∧ ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  have hx : Preg.IR .X16 ≠ .PC := by simp
  have hr1' : Preg.IR r1 ≠ .IR .X16 := fun e => hr1 (Preg.IR.inj e)
  have H := Val.shrxl_shrl_2 hv
  unfold shrx64
  split
  · rename_i he
    rw [if_pos he] at H
    subst H
    exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd), nextinstr_set_same _ _ hrd,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
  · rename_i he
    rw [if_neg he] at H
    subst H
    refine ⟨_, exec_straight_three rfl rfl rfl (nextinstr_set_PC _ _ hx) (nextinstr_set_PC _ _ hx)
      (nextinstr_set_PC _ _ hrd), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      simp only [ir0x, evalShiftOpLong, orl_zero_shrl]
      rw [nextinstr_set_same _ _ hx, nextinstr_set_other _ _ (by simp) hr1',
        nextinstr_set_same _ _ hx]
      rfl
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        nextinstr_set_other _ _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1),
        nextinstr_set_other _ _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]

end CONSTRUCTORS

end Asmgenproof1
end CC
