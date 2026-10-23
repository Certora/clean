/-
  Theorems of `lib/Integers.v` (the `Make(WS)` functor), part 1: ranges,
  `repr`/`unsigned`/`signed` round trips, `eqm`, equality, constants, and the
  ring structure.

  Everything is stated once for an arbitrary word size `w` (namespace
  `CC.Integers.MI`, CompCert's functor body).  Where Rocq relies on
  `WS.wordsize_not_zero`, the statement carries `0 < w`; for the concrete
  instances (`Int`, `Int64`, `Byte`, `Ptrofs`) this is discharged by `decide`
  (see `IntegersInst.lean`).

  Names follow Rocq (`add_commut`, `unsigned_repr`, `eqm_samerepr`, …), so a
  CompCert proof script can be transliterated lemma by lemma.  Only Lean core
  is used (no Mathlib).
-/
import CCLib.lib.Integers

namespace CC
namespace Integers
namespace MI

variable {w : Nat}

/-- `omega` after unfolding the `Z` abbreviation (omega does not see through
    `CC.Z`; see the note in `MemdataLemmas.lean`). -/
macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

/-! ## Basic facts about the range constants -/

theorem modulus_eq : modulus w = 2 ^ w := rfl

theorem modulus_pos : 0 < modulus w := by
  unfold modulus; exact Int.pow_pos (by decide)

theorem modulus_natCast : modulus w = ((2 ^ w : Nat) : Z) := by
  unfold modulus; simp

theorem half_modulus_modulus (hw : 0 < w) : modulus w = 2 * half_modulus w := by
  unfold half_modulus modulus
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by zomega⟩
  rw [Int.pow_succ]; zomega

theorem half_modulus_pos (hw : 0 < w) : 0 < half_modulus w := by
  have := half_modulus_modulus hw; have := @modulus_pos w; zomega

theorem half_modulus_eq (hw : 0 < w) : half_modulus w = 2 ^ (w - 1) := by
  unfold half_modulus modulus
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by zomega⟩
  simp only [Nat.add_sub_cancel, Int.pow_succ]; zomega

theorem max_unsigned_eq : max_unsigned w = modulus w - 1 := rfl
theorem max_signed_eq : max_signed w = half_modulus w - 1 := rfl
theorem min_signed_eq : min_signed w = - half_modulus w := rfl

theorem min_signed_neg (hw : 0 < w) : min_signed w < 0 := by
  have := half_modulus_pos hw; unfold min_signed; zomega

theorem max_signed_pos (hw : 0 < w) : 0 ≤ max_signed w := by
  have := half_modulus_pos hw; unfold max_signed; zomega

theorem max_signed_unsigned : max_signed w < max_unsigned w := by
  have := @modulus_pos w
  unfold max_signed max_unsigned half_modulus; zomega

/-! ## `unsigned`, `signed`, `repr` -/

theorem unsigned_toNat (x : BitVec w) : unsigned x = (x.toNat : Z) := rfl
theorem signed_toInt (x : BitVec w) : signed x = x.toInt := rfl
theorem repr_ofInt (z : Z) : (repr z : BitVec w) = BitVec.ofInt w z := rfl

theorem unsigned_range (x : BitVec w) : 0 ≤ unsigned x ∧ unsigned x < modulus w := by
  have := x.isLt
  rw [modulus_natCast]; unfold unsigned; zomega

theorem unsigned_range_2 (x : BitVec w) : 0 ≤ unsigned x ∧ unsigned x ≤ max_unsigned w := by
  have := unsigned_range x; unfold max_unsigned; zomega

theorem unsigned_nonneg (x : BitVec w) : 0 ≤ unsigned x := (unsigned_range x).1

/-- The defining equation of `Int.signed` in Rocq. -/
theorem signed_eq (hw : 0 < w) (x : BitVec w) :
    signed x = if unsigned x < half_modulus w then unsigned x
               else unsigned x - modulus w := by
  have hm := half_modulus_modulus hw
  rw [signed, BitVec.toInt_eq_toNat_cond, ← modulus_natCast]
  unfold unsigned
  have : (2 * x.toNat < 2 ^ w) ↔ ((x.toNat : Z) < half_modulus w) := by
    have h2 : ((2 ^ w : Nat) : Z) = modulus w := modulus_natCast.symm
    zomega
  by_cases h : 2 * x.toNat < 2 ^ w
  · rw [if_pos h, if_pos (this.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

theorem signed_range (hw : 0 < w) (x : BitVec w) :
    min_signed w ≤ signed x ∧ signed x ≤ max_signed w := by
  have := unsigned_range x
  have := half_modulus_modulus hw
  rw [signed_eq hw]
  unfold min_signed max_signed
  split <;> zomega

theorem repr_unsigned (x : BitVec w) : repr (unsigned x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [repr, unsigned]

theorem repr_signed (x : BitVec w) : repr (signed x) = x := by
  simp [repr, signed, BitVec.ofInt_toInt]

theorem unsigned_repr_eq (z : Z) : unsigned (repr z : BitVec w) = z % modulus w := by
  unfold unsigned repr
  rw [BitVec.toNat_ofInt, ← modulus_natCast]
  have := Int.emod_nonneg z (Int.ne_of_gt (@modulus_pos w))
  zomega

theorem unsigned_repr {z : Z} (h1 : 0 ≤ z) (h2 : z ≤ max_unsigned w) :
    unsigned (repr z : BitVec w) = z := by
  rw [unsigned_repr_eq]
  unfold max_unsigned at h2
  exact Int.emod_eq_of_lt h1 (by zomega)

theorem signed_repr_eq (hw : 0 < w) (z : Z) :
    signed (repr z : BitVec w) =
      if z % modulus w < half_modulus w then z % modulus w
      else z % modulus w - modulus w := by
  rw [signed_eq hw, unsigned_repr_eq]

theorem signed_repr (hw : 0 < w) {z : Z} (h1 : min_signed w ≤ z) (h2 : z ≤ max_signed w) :
    signed (repr z : BitVec w) = z := by
  rw [signed_repr_eq hw]
  have hm := half_modulus_modulus hw
  unfold min_signed at h1; unfold max_signed at h2
  have hp := half_modulus_pos hw
  by_cases hz : 0 ≤ z
  · have : z % modulus w = z := Int.emod_eq_of_lt hz (by zomega)
    rw [this, if_pos (by zomega)]
  · have : z % modulus w = z + modulus w := by
      have h3 : (z + modulus w) % modulus w = z % modulus w := by
        simp
      rw [← h3]; exact Int.emod_eq_of_lt (by zomega) (by zomega)
    rw [this, if_neg (by zomega)]; zomega

theorem signed_eq_unsigned (hw : 0 < w) (x : BitVec w) (h : unsigned x ≤ max_signed w) :
    signed x = unsigned x := by
  rw [signed_eq hw, if_pos]; unfold max_signed at h; zomega

theorem signed_positive (hw : 0 < w) (x : BitVec w) :
    0 ≤ signed x ↔ unsigned x ≤ max_signed w := by
  have := unsigned_range x
  have := half_modulus_modulus hw
  rw [signed_eq hw]; unfold max_signed
  split <;> zomega

theorem unsigned_inj {x y : BitVec w} (h : unsigned x = unsigned y) : x = y := by
  rw [← repr_unsigned x, ← repr_unsigned y, h]

theorem unsigned_eq_iff {x y : BitVec w} : unsigned x = unsigned y ↔ x = y :=
  ⟨unsigned_inj, fun h => h ▸ rfl⟩

theorem signed_inj {x y : BitVec w} (h : signed x = signed y) : x = y := by
  rw [← repr_signed x, ← repr_signed y, h]

/-! ## `eqm`: congruence modulo `2^w` -/

/-- `Int.eqm`: `x ≡ y (mod modulus)`, i.e. Rocq's `eqmod modulus`. -/
def eqm (w : Nat) (x y : Z) : Prop := ∃ k : Z, x = k * modulus w + y

theorem eqm_iff_emod {x y : Z} : eqm w x y ↔ x % modulus w = y % modulus w := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [Int.add_comm, Int.add_mul_emod_self_right]
  · intro h
    refine ⟨x / modulus w - y / modulus w, ?_⟩
    have h1 := Int.emod_add_mul_ediv x (modulus w)
    have h2 := Int.emod_add_mul_ediv y (modulus w)
    rw [Int.sub_mul, Int.mul_comm (x / modulus w), Int.mul_comm (y / modulus w)]
    zomega

theorem eqm_refl (x : Z) : eqm w x x := ⟨0, by simp⟩

theorem eqm_refl2 {x y : Z} (h : x = y) : eqm w x y := h ▸ eqm_refl x

theorem eqm_sym {x y : Z} (h : eqm w x y) : eqm w y x := by
  rw [eqm_iff_emod] at *; exact h.symm

theorem eqm_trans {x y z : Z} (h1 : eqm w x y) (h2 : eqm w y z) : eqm w x z := by
  rw [eqm_iff_emod] at *; exact h1.trans h2

theorem eqm_add {a b c d : Z} (h1 : eqm w a b) (h2 : eqm w c d) : eqm w (a + c) (b + d) := by
  rw [eqm_iff_emod] at *; rw [Int.add_emod, h1, h2, ← Int.add_emod]

theorem eqm_neg {x y : Z} (h : eqm w x y) : eqm w (-x) (-y) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨-k, by rw [Int.neg_add, Int.neg_mul]⟩

theorem eqm_sub {a b c d : Z} (h1 : eqm w a b) (h2 : eqm w c d) : eqm w (a - c) (b - d) := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg]; exact eqm_add h1 (eqm_neg h2)

theorem eqm_mult {a b c d : Z} (h1 : eqm w a c) (h2 : eqm w b d) : eqm w (a * b) (c * d) := by
  rw [eqm_iff_emod] at *; rw [Int.mul_emod, h1, h2, ← Int.mul_emod]

theorem eqm_samerepr {x y : Z} (h : eqm w x y) : (repr x : BitVec w) = repr y := by
  apply unsigned_inj
  rw [unsigned_repr_eq, unsigned_repr_eq]; exact eqm_iff_emod.mp h

theorem eqm_unsigned_repr (z : Z) : eqm w z (unsigned (repr z : BitVec w)) := by
  rw [eqm_iff_emod, unsigned_repr_eq, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]

theorem eqm_unsigned_repr_l {a b : Z} (h : eqm w a b) :
    eqm w (unsigned (repr a : BitVec w)) b :=
  eqm_trans (eqm_sym (eqm_unsigned_repr a)) h

theorem eqm_unsigned_repr_r {a b : Z} (h : eqm w a b) :
    eqm w a (unsigned (repr b : BitVec w)) :=
  eqm_trans h (eqm_unsigned_repr b)

theorem eqm_repr_eq {x : Z} {y : BitVec w} (h : eqm w x (unsigned y)) : repr x = y := by
  rw [eqm_samerepr h, repr_unsigned]

theorem eqm_signed_unsigned (x : BitVec w) : eqm w (signed x) (unsigned x) := by
  rw [eqm_iff_emod]
  have := congrArg unsigned (repr_signed x)
  rw [unsigned_repr_eq] at this
  rw [this, Int.emod_eq_of_lt (unsigned_range x).1 (unsigned_range x).2]

theorem unsigned_eqm_iff {x y : BitVec w} : eqm w (unsigned x) (unsigned y) ↔ x = y := by
  constructor
  · intro h; rw [← repr_unsigned x]; exact eqm_repr_eq h
  · rintro rfl; exact eqm_refl _

/-! ## Equality test -/

theorem eq_spec (x y : BitVec w) : (eq x y = true ↔ x = y) := by
  simp [eq]

theorem eq_true (x : BitVec w) : eq x x = true := by simp [eq]

theorem eq_false {x y : BitVec w} (h : x ≠ y) : eq x y = false := by simp [eq, h]

theorem eq_sym (x y : BitVec w) : eq x y = eq y x := by
  rw [Bool.eq_iff_iff]; simp only [eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩

theorem same_if_eq {x y : BitVec w} (h : eq x y = true) : x = y := (eq_spec x y).mp h

theorem eq_unsigned (x y : BitVec w) : eq x y = decide (unsigned x = unsigned y) := by
  rw [Bool.eq_iff_iff]; simp only [eq, beq_iff_eq, decide_eq_true_eq]
  exact unsigned_eq_iff.symm

theorem eq_signed (x y : BitVec w) : eq x y = decide (signed x = signed y) := by
  rw [Bool.eq_iff_iff]; simp only [eq, beq_iff_eq, decide_eq_true_eq]
  exact ⟨fun h => h ▸ rfl, signed_inj⟩

/-! ## Constants -/

theorem unsigned_zero : unsigned (zero : BitVec w) = 0 := by simp [unsigned, zero]

theorem repr_one : (repr 1 : BitVec w) = one := by
  apply BitVec.eq_of_toNat_eq; simp [repr, one]

theorem two_le_modulus (hw : 0 < w) : 2 ≤ modulus w := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by zomega⟩
  unfold modulus; rw [Int.pow_succ]
  have := @modulus_pos k; unfold modulus at this; zomega

theorem modulus_zero : modulus 0 = 1 := rfl

theorem unsigned_w0 (x : BitVec 0) : unsigned x = 0 := by
  have := unsigned_range x; rw [modulus_zero] at this; zomega

theorem unsigned_one (hw : 0 < w) : unsigned (one : BitVec w) = 1 := by
  rw [← repr_one, unsigned_repr_eq]
  have := two_le_modulus hw
  exact Int.emod_eq_of_lt (by decide) (by zomega)

theorem unsigned_mone : unsigned (mone : BitVec w) = modulus w - 1 := by
  simp only [unsigned, mone, BitVec.toNat_allOnes, modulus_natCast]
  have := Nat.one_le_two_pow (n := w)
  zomega

theorem signed_zero : signed (zero : BitVec w) = 0 := by simp [signed, zero]

theorem signed_mone (hw : 0 < w) : signed (mone : BitVec w) = -1 := by
  rw [signed_eq hw, unsigned_mone]
  have := half_modulus_modulus hw; have := half_modulus_pos hw
  rw [if_neg (by zomega)]; zomega

theorem one_not_zero (hw : 0 < w) : (one : BitVec w) ≠ zero := by
  intro h
  have := congrArg unsigned h
  rw [unsigned_one hw, unsigned_zero] at this
  exact absurd this (by decide)

theorem mone_ne_zero (hw : 0 < w) : (mone : BitVec w) ≠ zero := by
  intro h
  have := congrArg unsigned h
  rw [unsigned_mone, unsigned_zero] at this
  have := two_le_modulus hw
  zomega

theorem repr_zero : (repr 0 : BitVec w) = zero := by simp [repr, zero]

theorem repr_mone : (repr (-1) : BitVec w) = mone := by
  apply unsigned_inj
  rw [unsigned_repr_eq, unsigned_mone]
  have hm := @modulus_pos w
  have : (-1 : Z) % modulus w = modulus w - 1 := by
    have h3 : (modulus w - 1 + -1 * modulus w) % modulus w = (modulus w - 1) % modulus w :=
      Int.add_mul_emod_self_right _ _ _
    rw [show modulus w - 1 + -1 * modulus w = -1 by zomega] at h3
    rw [h3]; exact Int.emod_eq_of_lt (by zomega) (by zomega)
  exact this

theorem unsigned_repr_wordsize (h : (w : Z) ≤ max_unsigned w) :
    unsigned (iwordsize w) = w := by
  unfold iwordsize unsigned
  simp only [BitVec.toNat_ofNat]
  unfold max_unsigned at h
  rw [modulus_natCast] at h
  rw [Nat.mod_eq_of_lt (by zomega)]

/-! ## Addition -/

theorem add_unsigned (x y : BitVec w) : add x y = repr (unsigned x + unsigned y) := by
  apply unsigned_inj
  rw [unsigned_repr_eq]
  simp only [add, unsigned, BitVec.toNat_add]
  rw [modulus_natCast, Int.natCast_emod, Int.natCast_add]

theorem add_signed (x y : BitVec w) : add x y = repr (signed x + signed y) := by
  rw [add_unsigned]
  exact eqm_samerepr (eqm_add (eqm_sym (eqm_signed_unsigned x)) (eqm_sym (eqm_signed_unsigned y)))

theorem add_commut (x y : BitVec w) : add x y = add y x := BitVec.add_comm x y

theorem add_zero (x : BitVec w) : add x zero = x := BitVec.add_zero x

theorem add_zero_l (x : BitVec w) : add zero x = x := BitVec.zero_add x

theorem add_assoc (x y z : BitVec w) : add (add x y) z = add x (add y z) :=
  BitVec.add_assoc x y z

theorem add_permut (x y z : BitVec w) : add x (add y z) = add y (add x z) := by
  unfold add; rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]

theorem add_neg_zero (x : BitVec w) : add x (neg x) = zero := by
  unfold add neg zero; rw [← BitVec.sub_eq_add_neg, BitVec.sub_self]; rfl

theorem unsigned_add_carry (x y : BitVec w) :
    unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * modulus w := by
  have hx := unsigned_range x; have hy := unsigned_range y
  rw [add_unsigned, unsigned_repr_eq]
  unfold add_carry
  rw [unsigned_zero, Int.add_zero]
  by_cases h : unsigned x + unsigned y < modulus w
  · rw [if_pos h, unsigned_zero, Int.zero_mul, Int.sub_zero]
    exact Int.emod_eq_of_lt (by zomega) h
  · rw [if_neg h]
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · exfalso; rw [unsigned_w0, unsigned_w0, modulus_zero] at h; zomega
      · exact hw
    have h1 := unsigned_one hw
    rw [h1, Int.one_mul]
    have : (unsigned x + unsigned y) % modulus w
        = (unsigned x + unsigned y - modulus w + 1 * modulus w) % modulus w := by
      congr 1; zomega
    rw [this, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by zomega) (by zomega)

theorem unsigned_add_either (x y : BitVec w) :
    unsigned (add x y) = unsigned x + unsigned y ∨
    unsigned (add x y) = unsigned x + unsigned y - modulus w := by
  rw [unsigned_add_carry]
  unfold add_carry
  split
  · left; rw [unsigned_zero]; zomega
  · right
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp only [unsigned_w0, modulus_zero] at *; zomega
    · rw [unsigned_one hw]; zomega

theorem repr_add (a b : Z) : (repr (a + b) : BitVec w) = add (repr a) (repr b) := by
  simp [repr, add, BitVec.ofInt_add]

/-! ## Negation -/

theorem neg_repr (z : Z) : neg (repr z : BitVec w) = repr (-z) := by
  apply BitVec.eq_of_toInt_eq
  simp [neg, repr, BitVec.toInt_neg, BitVec.toInt_ofInt]

theorem neg_zero : neg (zero : BitVec w) = zero := by simp [neg, zero]

theorem neg_involutive (x : BitVec w) : neg (neg x) = x := by simp [neg]

theorem neg_add_distr (x y : BitVec w) : neg (add x y) = add (neg x) (neg y) := by
  simp [neg, add, BitVec.neg_add, BitVec.sub_eq_add_neg]

theorem neg_unsigned (x : BitVec w) : neg x = repr (- unsigned x) := by
  conv => lhs; rw [← repr_unsigned x]
  exact neg_repr _

/-! ## Subtraction -/

theorem sub_zero_l (x : BitVec w) : sub zero x = neg x := by simp [sub, zero, neg]

theorem sub_zero_r (x : BitVec w) : sub x zero = x := by simp [sub, zero]

theorem sub_add_opp (x y : BitVec w) : sub x y = add x (neg y) := by
  simp [sub, add, neg, BitVec.sub_eq_add_neg]

theorem sub_idem (x : BitVec w) : sub x x = zero := by simp [sub, zero]

theorem sub_add_l (x y z : BitVec w) : sub (add x y) z = add (sub x z) y := by
  simp only [sub_add_opp, add_assoc, add_commut y (neg z)]

theorem sub_add_r (x y z : BitVec w) : sub x (add y z) = add (sub x z) (neg y) := by
  rw [sub_add_opp, sub_add_opp, neg_add_distr, add_assoc, add_commut (neg y) (neg z)]

theorem sub_shifted (x y z : BitVec w) : sub (add x z) (add y z) = sub x y := by
  rw [sub_add_opp, sub_add_opp, neg_add_distr, add_assoc, add_permut z, add_neg_zero,
    add_zero]

theorem sub_unsigned (x y : BitVec w) : sub x y = repr (unsigned x - unsigned y) := by
  rw [sub_add_opp, add_unsigned, neg_unsigned]
  apply eqm_samerepr
  rw [Int.sub_eq_add_neg]
  exact eqm_add (eqm_refl _) (eqm_sym (eqm_unsigned_repr _))

theorem sub_signed (x y : BitVec w) : sub x y = repr (signed x - signed y) := by
  rw [sub_unsigned]
  exact eqm_samerepr (eqm_sub (eqm_sym (eqm_signed_unsigned x)) (eqm_sym (eqm_signed_unsigned y)))

theorem repr_sub (a b : Z) : (repr (a - b) : BitVec w) = sub (repr a) (repr b) := by
  rw [sub_unsigned]
  exact eqm_samerepr (eqm_sub (eqm_unsigned_repr a) (eqm_unsigned_repr b))

theorem unsigned_sub_borrow (x y : BitVec w) :
    unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * modulus w := by
  have hx := unsigned_range x; have hy := unsigned_range y
  rw [sub_unsigned, unsigned_repr_eq]
  unfold sub_borrow
  rw [unsigned_zero, Int.sub_zero]
  by_cases h : unsigned x - unsigned y < 0
  · rw [if_pos h]
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · exfalso; rw [unsigned_w0, unsigned_w0] at h; zomega
      · exact hw
    have h1 := unsigned_one hw
    rw [h1, Int.one_mul]
    have : (unsigned x - unsigned y) % modulus w
        = (unsigned x - unsigned y + modulus w + (-1) * modulus w) % modulus w := by
      congr 1; zomega
    rw [this, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by zomega) (by zomega)
  · rw [if_neg h, unsigned_zero, Int.zero_mul, Int.add_zero]
    exact Int.emod_eq_of_lt (by zomega) (by zomega)

/-! ## Multiplication -/

theorem mul_unsigned (x y : BitVec w) : mul x y = repr (unsigned x * unsigned y) := by
  apply unsigned_inj
  rw [unsigned_repr_eq]
  simp only [mul, unsigned, BitVec.toNat_mul]
  rw [modulus_natCast, Int.natCast_emod, Int.natCast_mul]

theorem mul_signed (x y : BitVec w) : mul x y = repr (signed x * signed y) := by
  rw [mul_unsigned]
  exact eqm_samerepr (eqm_mult (eqm_sym (eqm_signed_unsigned x)) (eqm_sym (eqm_signed_unsigned y)))

theorem repr_mul (a b : Z) : (repr (a * b) : BitVec w) = mul (repr a) (repr b) := by
  simp [repr, mul, BitVec.ofInt_mul]

theorem mul_commut (x y : BitVec w) : mul x y = mul y x := BitVec.mul_comm x y

theorem mul_zero (x : BitVec w) : mul x zero = zero := by simp [mul, zero]

theorem mul_one (x : BitVec w) : mul x one = x := by simp [mul, one]

theorem mul_mone (x : BitVec w) : mul x mone = neg x := by
  rw [← repr_mone, mul_unsigned, neg_unsigned]
  apply eqm_samerepr
  rw [Int.mul_comm]
  exact eqm_mult (eqm_sym (eqm_unsigned_repr (-1))) (eqm_refl _) |> fun h =>
    by simpa [Int.neg_one_mul] using h

theorem mul_assoc (x y z : BitVec w) : mul (mul x y) z = mul x (mul y z) :=
  BitVec.mul_assoc x y z

theorem mul_add_distr_l (x y z : BitVec w) : mul (add x y) z = add (mul x z) (mul y z) := by
  simp only [mul, add, BitVec.add_mul]

theorem mul_add_distr_r (x y z : BitVec w) : mul x (add y z) = add (mul x y) (mul x z) := by
  simp only [mul, add, BitVec.mul_add]

theorem neg_mul_distr_l (x y : BitVec w) : neg (mul x y) = mul (neg x) y := by
  simp [neg, mul, BitVec.neg_mul]

theorem neg_mul_distr_r (x y : BitVec w) : neg (mul x y) = mul x (neg y) := by
  simp [neg, mul, BitVec.mul_neg]

end MI
end Integers
end CC
