/-
  Correctness of instruction selection for operators (x86), part 2 — port
  of `x86/SelectOpproof.v`: opposite, subtraction, logical negation,
  immediate and general shifts, multiplication, bitwise operations.
-/
import CCLib.x86.SelectOpproof
import CCLib.lib.IntegersPow2

namespace CC
namespace X86
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-! ### Value-level lemmas -/

theorem val_sub_zero_neg (v : Val) : Val.Lessdef (Val.sub Val.Vzero v) (Val.neg v) := by
  cases v <;> simp [Val.sub, Val.neg, Val.Vzero, Integers.Int.sub_zero_l] <;> ld

theorem val_sub_add_l (v1 v2 : Val) (i : Integers.Int) :
    Val.sub (Val.add v1 (.Vint i)) v2 = Val.add (Val.sub v1 v2) (.Vint i) := by
  cases v1 <;> cases v2 <;> simp [Val.sub, Val.add, Archi.ptr64, Integers.Int.sub_add_l]

theorem val_sub_add_r (v1 v2 : Val) (i : Integers.Int) :
    Val.sub v1 (Val.add v2 (.Vint i)) = Val.add (Val.sub v1 v2) (.Vint (Integers.Int.neg i)) := by
  cases v1 <;> cases v2 <;> simp [Val.sub, Val.add, Archi.ptr64]
  rw [Integers.Int.add_commut, Integers.Int.sub_add_r]

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

/-- A left shift by `n` is a multiplication by `2^n` (with an added offset). -/
theorem val_shl_scaled (v : Val) (n k : Integers.Int)
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    Val.Lessdef (Val.shl (Val.add v (.Vint k)) (.Vint n))
      (Val.add (Val.mul v (.Vint (Integers.Int.repr
          (Integers.Int.unsigned (Integers.Int.shl Integers.Int.one n)))))
        (.Vint (Integers.Int.repr (Integers.Int.unsigned (Integers.Int.shl k n))))) := by
  rw [Integers.Int.repr_unsigned, Integers.Int.repr_unsigned]
  cases v <;> simp [Val.shl, Val.add, Val.mul, hn, Archi.ptr64] <;> try ld
  rw [Integers.Int.shl_mul, Integers.Int.mul_add_distr_l, ← Integers.Int.shl_mul,
    ← Integers.Int.shl_mul]; ld

theorem val_shl_scaled0 (v : Val) (n : Integers.Int)
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    Val.Lessdef (Val.shl v (.Vint n))
      (Val.add (Val.mul v (.Vint (Integers.Int.repr
          (Integers.Int.unsigned (Integers.Int.shl Integers.Int.one n)))))
        (.Vint (Integers.Int.repr 0))) := by
  rw [Integers.Int.repr_unsigned, show Integers.Int.repr 0 = Integers.Int.zero from rfl]
  cases v <;> simp [Val.shl, Val.add, Val.mul, hn, Archi.ptr64] <;> try ld
  rw [Integers.Int.add_zero, ← Integers.Int.shl_mul]; ld

theorem int_not_xor (a b : Integers.Int) :
    Integers.Int.not (Integers.Int.xor a b) = Integers.Int.xor a (Integers.Int.not b) := by
  rw [Integers.Int.not_eq_xor_mone, Integers.Int.not_eq_xor_mone b, Integers.Int.xor_assoc]

theorem int_xor_not (a b : Integers.Int) :
    Integers.Int.xor (Integers.Int.not a) b = Integers.Int.xor a (Integers.Int.not b) := by
  rw [Integers.Int.not_eq_xor_mone, Integers.Int.not_eq_xor_mone b, Integers.Int.xor_assoc,
    Integers.Int.xor_commut Integers.Int.mone]

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Opposite and subtraction -/

/-- `eval_negint` -/
theorem eval_negint : UnarySound ge sp e m negint (fun v => Val.sub Val.Vzero v) := by
  intro le a x hx
  unfold negint
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by
      simp [Val.sub, Val.Vzero, Integers.Int.sub_zero_l]; ld⟩
  · exact ⟨_, eval_op1 hx rfl, val_sub_zero_neg _⟩

/-- `eval_sub` -/
theorem eval_sub : BinarySound ge sp e m SelectOp.sub Val.sub := by
  intro le a x b y hx hy
  unfold SelectOp.sub
  split
  · obtain rfl := inv_intconst hy
    rw [Val.sub_add_opp]; exact eval_addimm _ le _ _ hx
  · rename_i n1 t1 n2 t2
    obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho1; cases ho2
    show ∃ v, _ ∧ Val.Lessdef (Val.sub (Val.add v1 _) (Val.add v2 _)) v
    rw [val_sub_add_l, val_sub_add_r, Val.add_assoc,
      show Val.add (.Vint (Integers.Int.neg (Integers.Int.repr n2))) (.Vint (Integers.Int.repr n1)) =
        .Vint (Integers.Int.repr (n1 - n2)) by
        simp only [Val.add]
        rw [Integers.Int.add_commut, ← Integers.Int.sub_add_opp, ← Integers.Int.repr_sub]]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Osub) h1 h2 rfl)
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    show ∃ v, _ ∧ Val.Lessdef (Val.sub (Val.add v1 _) y) v
    rw [val_sub_add_l]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Osub) h1 hy rfl)
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    show ∃ v, _ ∧ Val.Lessdef (Val.sub x (Val.add v2 _)) v
    rw [val_sub_add_r, Integers.Int.neg_repr]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Osub) hx h2 rfl)
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Logical negation -/

/-- `eval_notint` -/
theorem eval_notint : UnarySound ge sp e m notint Val.notint := by
  intro le a x hx
  unfold notint
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    cases v1 <;> simp [Val.notint, Val.xor, int_not_xor] <;> ld
  · exact ⟨_, eval_op1 hx rfl, .refl _⟩

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
  · next n1 t1 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · exact ⟨_, eval_op1 h1 rfl, val_shl_scaled v1 n _ L⟩
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · split
    · exact ⟨_, eval_op1 hx rfl, val_shl_scaled0 x n L⟩
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
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

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
    obtain ⟨v'', hv'', hl''⟩ := eval_addimm (Integers.Int.mul n (Integers.Int.repr n2)) le _ v' hv'
    refine ⟨v'', hv'',
      Val.lessdef_trans ?_ (Val.lessdef_trans (Val.add_lessdef hl' (.refl _)) hl'')⟩
    show Val.Lessdef (Val.mul (Val.add v1 _) _) _
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

/-- `eval_mulhs` -/
theorem eval_mulhs : BinarySound ge sp e m SelectOp.mulhs Val.mulhs :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩

/-- `eval_mulhu` -/
theorem eval_mulhu : BinarySound ge sp e m SelectOp.mulhu Val.mulhu :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩

/-! ### Conjunction -/

theorem val_and_and (v : Val) (n1 n2 : Integers.Int) :
    Val.and (Val.and v (.Vint n2)) (.Vint n1) = Val.and v (.Vint (Integers.Int.and n1 n2)) := by
  cases v <;> simp [Val.and]
  rw [Integers.Int.and_assoc, Integers.Int.and_commut n2]

theorem val_and_zeroExt (v : Val) (k : Nat) (n1 : Integers.Int) :
    Val.and (Val.zeroExt k v) (.Vint n1) =
      Val.and v (.Vint (Integers.Int.and n1 (Integers.Int.repr ((2 : Z) ^ k - 1)))) := by
  cases v <;> simp [Val.and, Val.zeroExt]
  rw [Integers.Int.zero_ext_and, Integers.Int.and_assoc, Integers.Int.and_commut n1]

/-- `eval_andimm` -/
theorem eval_andimm (n : Integers.Int) :
    UnarySound ge sp e m (andimm n) (fun x => Val.and x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold andimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.and, Integers.Int.and_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int.eq n Integers.Int.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h1
    exact ⟨x, hx, by cases x <;> simp [Val.and, Integers.Int.and_mone] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.and, Integers.Int.and_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    rw [val_and_and]
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    show Val.Lessdef (Val.and (Val.zeroExt 8 v1) _) _
    rw [val_and_zeroExt]; exact .refl _
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    show Val.Lessdef (Val.and (Val.zeroExt 16 v1) _) _
    rw [val_and_zeroExt]; exact .refl _
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_and` -/
theorem eval_and : BinarySound ge sp e m SelectOp.and Val.and := by
  intro le a x b y hx hy
  unfold SelectOp.and
  split
  · obtain rfl := inv_intconst hx
    rw [Val.and_commut]; exact eval_andimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_andimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Disjunction -/

/-- `eval_orimm` -/
theorem eval_orimm (n : Integers.Int) :
    UnarySound ge sp e m (orimm n) (fun x => Val.or x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold orimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.or, Integers.Int.or_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int.eq n Integers.Int.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h1
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.or, Integers.Int.or_mone] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.or, Integers.Int.or_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    cases v1 <;> simp [Val.or] <;> try ld
    rw [Integers.Int.or_assoc, Integers.Int.or_commut _ n]; ld
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `same_expr_pure` is sound: two pure-equal expressions evaluate to the same value. -/
theorem sameExprPure_eval {le : Letenv} {t1 t2 : SelectOp.Expr} {v1 v2 : Val}
    (h : sameExprPure t1 t2 = true) (h1 : CminorSel.EvalExpr ge sp e m le t1 v1)
    (h2 : CminorSel.EvalExpr ge sp e m le t2 v2) : v1 = v2 := by
  unfold sameExprPure at h
  split at h
  · next i1 i2 =>
    obtain rfl : i1 = i2 := of_decide_eq_true h
    cases h1 with
    | Evar _ _ _ g1 =>
      cases h2 with
      | Evar _ _ _ g2 => rw [g1] at g2; exact Option.some.inj g2
  · cases h

theorem val_or_ror_ld (v : Val) (n1 n2 : Integers.Int)
    (h : Integers.Int.add n1 n2 = Integers.Int.iwordsize) :
    Val.Lessdef (Val.or (Val.shl v (.Vint n1)) (Val.shru v (.Vint n2))) (Val.ror v (.Vint n2)) := by
  by_cases h1 : Integers.Int.ltu n1 Integers.Int.iwordsize = true
  · by_cases h2 : Integers.Int.ltu n2 Integers.Int.iwordsize = true
    · cases v <;> simp only [Val.or, Val.shl, Val.shru, Val.ror, h1, h2, if_true] <;> try ld
      rw [Integers.Int.or_ror _ _ _ (Integers.Int.toNat_lt_of_ltu h1)
        (Integers.Int.toNat_lt_of_ltu h2) h]
      ld
    · cases v <;> simp [Val.or, Val.shl, Val.shru, h2] <;> ld
  · cases v <;> simp [Val.or, Val.shl, h1] <;> ld

theorem int_n2_eq {n1 n2 : Integers.Int} (h : Integers.Int.add n1 n2 = Integers.Int.iwordsize) :
    n2 = Integers.Int.sub Integers.Int.iwordsize n1 := by
  rw [← h]
  show n2 = n1 + n2 - n1
  bv_omega

/-- `eval_or` -/
theorem eval_or : BinarySound ge sp e m SelectOp.or Val.or := by
  intro le a x b y hx hy
  unfold SelectOp.or
  split
  · obtain rfl := inv_intconst hx
    rw [Val.or_commut]; exact eval_orimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_orimm _ le _ _ hx
  · next n1 t1 n2 t2 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    split
    · next hc =>
      have hc' := (Integers.Int.eq_spec _ _).mp hc
      split
      · next hs =>
        obtain rfl := sameExprPure_eval hs h1 h2
        exact ⟨_, eval_op1 h1 rfl, val_or_ror_ld _ _ _ hc'⟩
      · refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
        show Val.Lessdef _ (Val.or (Val.shl v1 _) (Val.shru v2 (.Vint (Integers.Int.sub _ n1))))
        rw [← int_n2_eq hc']; ld
    · exact ⟨_, eval_op2 hx hy rfl, by ld⟩
  · next n2 t2 n1 t1 =>
    obtain ⟨v2, h2, ho⟩ := inv_op1 hx; cases ho
    obtain ⟨v1, h1, ho⟩ := inv_op1 hy; cases ho
    split
    · next hc =>
      have hc' := (Integers.Int.eq_spec _ _).mp hc
      split
      · next hs =>
        obtain rfl := sameExprPure_eval hs h1 h2
        refine ⟨_, eval_op1 h1 rfl, ?_⟩
        rw [Val.or_commut]; exact val_or_ror_ld _ _ _ hc'
      · refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
        show Val.Lessdef _ (Val.or (Val.shl v1 _) (Val.shru v2 (.Vint (Integers.Int.sub _ n1))))
        rw [← int_n2_eq hc', Val.or_commut]; ld
    · exact ⟨_, eval_op2 hx hy rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Exclusive or -/

/-- `eval_xorimm` -/
theorem eval_xorimm (n : Integers.Int) :
    UnarySound ge sp e m (xorimm n) (fun x => Val.xor x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold xorimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.xor, Integers.Int.xor_zero] <;> ld⟩
  rw [if_neg h0]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.xor, Integers.Int.xor_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    cases v1 <;> simp [Val.xor] <;> try ld
    rw [Integers.Int.xor_assoc, Integers.Int.xor_commut n2]; ld
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    cases v1 <;> simp [Val.xor, Val.notint] <;> try ld
    rw [int_xor_not]; ld
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_xor` -/
theorem eval_xor : BinarySound ge sp e m SelectOp.xor Val.xor := by
  intro le a x b y hx hy
  unfold SelectOp.xor
  split
  · obtain rfl := inv_intconst hx
    rw [Val.xor_commut]; exact eval_xorimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_xorimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

end CMCONSTR

end SelectOpproof
end X86
end CC
