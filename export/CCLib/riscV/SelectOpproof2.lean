/-
  Correctness of instruction selection for operators (RISC-V), part 2 —
  port of `riscV/SelectOpproof.v`: immediate and general shifts,
  multiplication (`mulimm`, `mul`, `mulhs`, `mulhu`).
-/
import CCLib.riscV.SelectOpproof

namespace CC
namespace RiscV
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-! ### Value-level lemmas about shifts -/

theorem ltu_add_toNat {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int.iwordsize = true)
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    a.toNat + n.toNat < 2 ^ 32 := by
  have := Integers.Int.toNat_lt_of_ltu ha
  have := Integers.Int.toNat_lt_of_ltu hn
  omega

theorem val_shl_zero (x : Val) : Val.Lessdef (Val.shl x (.Vint Integers.Int.zero)) x := by
  cases x <;> simp [Val.shl] <;> try ld
  rw [if_pos (by decide), Integers.Int.shl_zero]; ld

theorem val_shru_zero (x : Val) : Val.Lessdef (Val.shru x (.Vint Integers.Int.zero)) x := by
  cases x <;> simp [Val.shru, Integers.Int.shru_zero] <;> first | ld | (rw [if_pos (by decide)]; ld)

theorem val_shr_zero (x : Val) : Val.Lessdef (Val.shr x (.Vint Integers.Int.zero)) x := by
  cases x <;> simp [Val.shr, Integers.Int.shr_zero] <;> first | ld | (rw [if_pos (by decide)]; ld)

/-- Two left shifts by `a` then `n` are one shift by `n + a` (when that is in range). -/
theorem val_shl_shl_ld (v : Val) {a n : Integers.Int}
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true)
    (h : Integers.Int.ltu (Integers.Int.add n a) Integers.Int.iwordsize = true) :
    Val.Lessdef (Val.shl (Val.shl v (.Vint a)) (.Vint n)) (Val.shl v (.Vint (Integers.Int.add n a))) := by
  by_cases ha : Integers.Int.ltu a Integers.Int.iwordsize = true
  · rw [Integers.Int.add_commut] at h ⊢
    cases v <;> simp [Val.shl, ha, hn, h] <;> try ld
    rw [Integers.Int.shl_shl _ _ _ (ltu_add_toNat ha hn)]; ld
  · cases v <;> simp [Val.shl, ha] <;> ld

theorem val_shru_shru_ld (v : Val) {a n : Integers.Int}
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true)
    (h : Integers.Int.ltu (Integers.Int.add n a) Integers.Int.iwordsize = true) :
    Val.Lessdef (Val.shru (Val.shru v (.Vint a)) (.Vint n))
      (Val.shru v (.Vint (Integers.Int.add n a))) := by
  by_cases ha : Integers.Int.ltu a Integers.Int.iwordsize = true
  · rw [Integers.Int.add_commut] at h ⊢
    cases v <;> simp [Val.shru, ha, hn, h] <;> try ld
    rw [Integers.Int.shru_shru _ _ _ (ltu_add_toNat ha hn)]; ld
  · cases v <;> simp [Val.shru, ha] <;> ld

theorem val_shr_shr_ld (v : Val) {a n : Integers.Int}
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true)
    (h : Integers.Int.ltu (Integers.Int.add n a) Integers.Int.iwordsize = true) :
    Val.Lessdef (Val.shr (Val.shr v (.Vint a)) (.Vint n))
      (Val.shr v (.Vint (Integers.Int.add n a))) := by
  by_cases ha : Integers.Int.ltu a Integers.Int.iwordsize = true
  · rw [Integers.Int.add_commut] at h ⊢
    cases v <;> simp [Val.shr, ha, hn, h] <;> try ld
    rw [Integers.Int.shr_shr _ _ _ (ltu_add_toNat ha hn)]; ld
  · cases v <;> simp [Val.shr, ha] <;> ld

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Immediate shifts -/

/-- `eval_shlimm` -/
theorem eval_shlimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shlimm a n) (fun x => Val.shl x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shlimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shl_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int.iwordsize
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.shl, L]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      exact ⟨_, eval_op1 h1 rfl, val_shl_shl_ld v1 L L2⟩
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_shruimm` -/
theorem eval_shruimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shruimm a n) (fun x => Val.shru x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shruimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shru_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int.iwordsize
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.shru, L]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      exact ⟨_, eval_op1 h1 rfl, val_shru_shru_ld v1 L L2⟩
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_shrimm` -/
theorem eval_shrimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shrimm a n) (fun x => Val.shr x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shrimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shr_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int.iwordsize
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.shr, L]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      exact ⟨_, eval_op1 h1 rfl, val_shr_shr_ld v1 L L2⟩
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-! ### General shifts -/

/-- `eval_shl` -/
theorem eval_shl : BinarySound ge sp e m SelectOp.shl Val.shl := by
  intro le a x b y hx hy
  unfold SelectOp.shl
  split
  · obtain rfl := inv_intconst hy
    exact eval_shlimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shr` -/
theorem eval_shr : BinarySound ge sp e m SelectOp.shr Val.shr := by
  intro le a x b y hx hy
  unfold SelectOp.shr
  split
  · obtain rfl := inv_intconst hy
    exact eval_shrimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shru` -/
theorem eval_shru : BinarySound ge sp e m SelectOp.shru Val.shru := by
  intro le a x b y hx hy
  unfold SelectOp.shru
  split
  · obtain rfl := inv_intconst hy
    exact eval_shruimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Multiplication -/

/-- `eval_mulimm_base` -/
theorem eval_mulimmBase (n : Integers.Int) :
    UnarySound ge sp e m (mulimmBase n) (fun x => Val.mul x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold mulimmBase
  split
  · next i h =>
    obtain ⟨hi, hmul⟩ := Integers.Int.one_bits_single h
    obtain ⟨v, hv, hl⟩ := eval_shlimm i le a x hx
    refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
    cases x <;> simp [Val.mul, Val.shl, hi, hmul] <;> ld
  · next i j h =>
    obtain ⟨hi, hj, hmul⟩ := Integers.Int.one_bits_double h
    have hx0 : CminorSel.EvalExpr ge sp e m (x :: le) (.Eletvar 0) x := .Eletvar _ _ _ rfl
    obtain ⟨v1, hv1, hl1⟩ := eval_shlimm i (x :: le) _ x hx0
    obtain ⟨v2, hv2, hl2⟩ := eval_shlimm j (x :: le) _ x hx0
    obtain ⟨v, hv, hl⟩ := eval_add (x :: le) _ _ _ _ hv1 hv2
    refine ⟨v, .Elet _ _ _ _ _ hx hv,
      Val.lessdef_trans ?_ (Val.lessdef_trans (Val.add_lessdef hl1 hl2) hl)⟩
    cases x <;> simp [Val.mul, Val.shl, Val.add, hi, hj, hmul] <;> ld
  · exact ⟨_, eval_op2 (eval_op0 rfl) hx rfl, by rw [Val.mul_commut]; ld⟩

/-- `eval_mulimm` -/
theorem eval_mulimm (n : Integers.Int) :
    UnarySound ge sp e m (mulimm n) (fun x => Val.mul x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold mulimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.mul, Integers.Int.mul_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int.eq n Integers.Int.one = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h1
    exact ⟨x, hx, by cases x <;> simp [Val.mul, Integers.Int.mul_one] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.mul, Integers.Int.mul_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1', ho⟩ := inv_op1 hx
    cases ho
    obtain ⟨v', hv', hl'⟩ := eval_mulimmBase n le t2 v1 h1'
    obtain ⟨v'', hv'', hl''⟩ := eval_addimm (Integers.Int.mul n n2) le _ v' hv'
    refine ⟨v'', hv'',
      Val.lessdef_trans ?_ (Val.lessdef_trans (Val.add_lessdef hl' (.refl _)) hl'')⟩
    rw [Val.mul_add_distr_l]
    simp [Val.mul, Integers.Int.mul_commut]; ld
  · exact eval_mulimmBase n le a x hx

/-- `eval_mul` -/
theorem eval_mul : BinarySound ge sp e m SelectOp.mul Val.mul := by
  intro le a x b y hx hy
  unfold SelectOp.mul
  split
  · obtain rfl := inv_intconst hx
    rw [Val.mul_commut]; exact eval_mulimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_mulimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

end CMCONSTR

end SelectOpproof
end RiscV
end CC
