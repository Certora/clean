/-
  Theorems of `lib/Integers.v`, part 2: comparisons, unsigned and signed
  division, bitwise operations, shifts and rotations, zero/sign extension.

  Generic in the word size `w` (namespace `CC.Integers.MI`); see
  `IntegersLemmas.lean` for conventions.  Bit-level statements use
  `testbit x i` with `i : Nat` (Rocq's `i : Z` with `0 ≤ i`).
-/
import CCLib.lib.IntegersLemmas

namespace CC
namespace Integers
namespace MI

variable {w : Nat}

/-! ## Comparisons -/

theorem ltu_def (x y : BitVec w) : ltu x y = decide (unsigned x < unsigned y) := by
  simp [ltu, unsigned, BitVec.ult]

theorem ltu_iff (x y : BitVec w) : ltu x y = true ↔ unsigned x < unsigned y := by
  rw [ltu_def]; simp

theorem lt_def (x y : BitVec w) : lt x y = decide (signed x < signed y) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]; exact BitVec.slt_iff_toInt_lt

theorem lt_iff (x y : BitVec w) : lt x y = true ↔ signed x < signed y := by
  rw [lt_def]; simp

theorem ltu_inv {x y : BitVec w} (h : ltu x y = true) :
    0 ≤ unsigned x ∧ unsigned x < unsigned y :=
  ⟨unsigned_nonneg x, (ltu_iff x y).mp h⟩

theorem lt_irrefl (x : BitVec w) : lt x x = false := by
  rw [lt_def]; simp

theorem ltu_irrefl (x : BitVec w) : ltu x x = false := by
  rw [ltu_def]; simp

theorem ltu_zero (x : BitVec w) : ltu x zero = false := by
  rw [ltu_def, unsigned_zero]; have := unsigned_nonneg x; simp only [decide_eq_false_iff_not]
  zomega

theorem not_lt (x y : BitVec w) : (!(lt y x)) = (lt x y || eq x y) := by
  rw [lt_def, lt_def, eq_signed]
  by_cases h1 : signed x < signed y
  · have : ¬ signed y < signed x := by zomega
    simp [h1, this]
  · by_cases h2 : signed x = signed y
    · simp [h2]
    · have : signed y < signed x := by zomega
      simp [h1, h2, this]

theorem not_ltu (x y : BitVec w) : (!(ltu y x)) = (ltu x y || eq x y) := by
  rw [ltu_def, ltu_def, eq_unsigned]
  by_cases h1 : unsigned x < unsigned y
  · have : ¬ unsigned y < unsigned x := by zomega
    simp [h1, this]
  · by_cases h2 : unsigned x = unsigned y
    · simp [h2]
    · have : unsigned y < unsigned x := by zomega
      simp [h1, h2, this]

theorem lt_not (x y : BitVec w) : lt y x = (!(lt x y) && !(eq x y)) := by
  rw [← Bool.not_or, ← not_lt, Bool.not_not]

theorem ltu_not (x y : BitVec w) : ltu y x = (!(ltu x y) && !(eq x y)) := by
  rw [← Bool.not_or, ← not_ltu, Bool.not_not]

theorem negate_cmp (c : Comparison) (x y : BitVec w) :
    cmp c.negate x y = !(cmp c x y) := by
  cases c <;> simp [cmp, Comparison.negate]

theorem negate_cmpu (c : Comparison) (x y : BitVec w) :
    cmpu c.negate x y = !(cmpu c x y) := by
  cases c <;> simp [cmpu, Comparison.negate]

theorem swap_cmp (c : Comparison) (x y : BitVec w) : cmp c.swap x y = cmp c y x := by
  cases c <;> simp [cmp, Comparison.swap, eq_sym]

theorem swap_cmpu (c : Comparison) (x y : BitVec w) : cmpu c.swap x y = cmpu c y x := by
  cases c <;> simp [cmpu, Comparison.swap, eq_sym]

theorem add_sub_cancel_r (x d : BitVec w) : sub (add x d) d = x := by
  rw [sub_add_opp, add_assoc, add_neg_zero, add_zero]

theorem eq_sub_of_add {a b c : BitVec w} (h : a = add b c) : c = sub a b := by
  rw [h, add_commut, add_sub_cancel_r]

theorem translate_eq (x y d : BitVec w) : eq (add x d) (add y d) = eq x y := by
  rw [Bool.eq_iff_iff, eq_spec, eq_spec]
  constructor
  · intro h; rw [← add_sub_cancel_r x d, h, add_sub_cancel_r]
  · intro h; rw [h]

theorem translate_ltu {x y d : BitVec w}
    (hx : unsigned x + unsigned d ≤ max_unsigned w)
    (hy : unsigned y + unsigned d ≤ max_unsigned w) :
    ltu (add x d) (add y d) = ltu x y := by
  have := unsigned_range x; have := unsigned_range y; have := unsigned_range d
  rw [ltu_def, ltu_def, add_unsigned, add_unsigned, unsigned_repr (by zomega) hx,
    unsigned_repr (by zomega) hy]
  simp only [decide_eq_decide]; zomega

theorem translate_cmpu (c : Comparison) {x y d : BitVec w}
    (hx : unsigned x + unsigned d ≤ max_unsigned w)
    (hy : unsigned y + unsigned d ≤ max_unsigned w) :
    cmpu c (add x d) (add y d) = cmpu c x y := by
  cases c <;> simp [cmpu, translate_eq, translate_ltu hx hy, translate_ltu hy hx]

/-! ## Unsigned division -/

theorem unsigned_divu (x y : BitVec w) : unsigned (divu x y) = unsigned x / unsigned y := by
  simp only [unsigned, divu, BitVec.toNat_udiv]; rw [Int.natCast_ediv]

theorem unsigned_modu (x y : BitVec w) : unsigned (modu x y) = unsigned x % unsigned y := by
  simp only [unsigned, modu, BitVec.toNat_umod]; rw [Int.natCast_emod]

/-- Rocq's definition: `divu x y = repr (unsigned x / unsigned y)`. -/
theorem divu_unsigned (x y : BitVec w) : divu x y = repr (unsigned x / unsigned y) := by
  rw [← unsigned_divu, repr_unsigned]

/-- Rocq's definition: `modu x y = repr (unsigned x mod unsigned y)`. -/
theorem modu_unsigned (x y : BitVec w) : modu x y = repr (unsigned x % unsigned y) := by
  rw [← unsigned_modu, repr_unsigned]

/-- `Int.modu_divu_Euclid`.  (Rocq assumes `y ≠ 0`; it is not needed here,
    since `x / 0 = 0` and `x % 0 = x`.) -/
theorem modu_divu_Euclid (x y : BitVec w) : x = add (mul (divu x y) y) (modu x y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [add, mul, divu, modu, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv,
    BitVec.toNat_umod]
  have hx := x.isLt
  have h1 : x.toNat / y.toNat * y.toNat ≤ x.toNat := Nat.div_mul_le_self _ _
  have h3 : x.toNat / y.toNat * y.toNat + x.toNat % y.toNat = x.toNat := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h1 hx), h3, Nat.mod_eq_of_lt hx]

theorem modu_divu (x y : BitVec w) : modu x y = sub x (mul (divu x y) y) :=
  eq_sub_of_add (modu_divu_Euclid x y)

theorem modu_bound (x y : BitVec w) (h : y ≠ zero) : unsigned (modu x y) < unsigned y := by
  rw [unsigned_modu]
  apply Int.emod_lt_of_pos
  have := unsigned_nonneg y
  have : unsigned y ≠ 0 := fun h' => h (unsigned_inj (h'.trans unsigned_zero.symm))
  zomega

theorem divu_one (x : BitVec w) : divu x one = x := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact BitVec.eq_of_toNat_eq (by have := x.isLt; have := (divu x one).isLt; simp at *; zomega)
  · rw [divu_unsigned, unsigned_one hw, Int.ediv_one, repr_unsigned]

theorem modu_one (x : BitVec w) : modu x one = zero := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact BitVec.eq_of_toNat_eq (by have := (modu x one).isLt; simp at *; zomega)
  · rw [modu_unsigned, unsigned_one hw, Int.emod_one, repr_zero]

theorem divu_zero (x : BitVec w) : divu x zero = zero := by simp [divu, zero]
theorem modu_zero (x : BitVec w) : modu x zero = x := by simp [modu, zero]

/-! ## Signed division -/

theorem eqm_bmod (z : Z) : eqm w (z.bmod (2 ^ w)) z := by
  rw [eqm_iff_emod]
  show z.bmod (2 ^ w) % (2 ^ w : Nat) = z % (2 ^ w : Nat)
  exact Int.bmod_emod

/-- Rocq's definition: `divs x y = repr (Z.quot (signed x) (signed y))`. -/
theorem divs_signed (x y : BitVec w) : divs x y = repr ((signed x).tdiv (signed y)) := by
  rw [← repr_signed (divs x y)]
  simp only [signed, divs, BitVec.toInt_sdiv]
  exact eqm_samerepr (eqm_bmod _)

/-- Rocq's definition: `mods x y = repr (Z.rem (signed x) (signed y))`. -/
theorem mods_signed (x y : BitVec w) : mods x y = repr ((signed x).tmod (signed y)) := by
  rw [← repr_signed (mods x y)]
  simp only [signed, mods, BitVec.toInt_srem]

theorem mods_divs_Euclid (x y : BitVec w) : x = add (mul (divs x y) y) (mods x y) := by
  have key : signed x = (signed x).tdiv (signed y) * signed y + (signed x).tmod (signed y) := by
    have := Int.tmod_add_mul_tdiv (signed x) (signed y)
    rw [Int.mul_comm]; zomega
  rw [divs_signed, mods_signed]
  calc x = repr (signed x) := (repr_signed x).symm
    _ = repr ((signed x).tdiv (signed y) * signed y + (signed x).tmod (signed y)) := by
        rw [← key]
    _ = add (mul (repr ((signed x).tdiv (signed y))) (repr (signed y)))
          (repr ((signed x).tmod (signed y))) := by rw [repr_add, repr_mul]
    _ = _ := by rw [repr_signed]

theorem mods_divs (x y : BitVec w) : mods x y = sub x (mul (divs x y) y) :=
  eq_sub_of_add (mods_divs_Euclid x y)

theorem signed_mods (x y : BitVec w) : signed (mods x y) = (signed x).tmod (signed y) := by
  simp [signed, mods, BitVec.toInt_srem]

/-! ## Bitwise operations -/

theorem testbit_def (x : BitVec w) (i : Nat) : testbit x i = x.getLsbD i := rfl

theorem testbit_unsigned (x : BitVec w) (i : Nat) :
    testbit x i = (unsigned x).toNat.testBit i := by
  simp [testbit, unsigned, BitVec.getLsbD]

theorem bits_above (x : BitVec w) {i : Nat} (h : w ≤ i) : testbit x i = false :=
  BitVec.getLsbD_of_ge x i h

theorem same_bits_eq {x y : BitVec w} (h : ∀ i, i < w → testbit x i = testbit y i) : x = y :=
  BitVec.eq_of_getLsbD_eq h

theorem bits_zero (i : Nat) : testbit (zero : BitVec w) i = false := by
  simp [testbit, zero]

theorem bits_mone {i : Nat} (h : i < w) : testbit (mone : BitVec w) i = true := by
  simp [testbit, mone, h]

theorem bits_and (x y : BitVec w) (i : Nat) :
    testbit (and x y) i = (testbit x i && testbit y i) := by
  simp [testbit, and]

theorem bits_or (x y : BitVec w) (i : Nat) :
    testbit (or x y) i = (testbit x i || testbit y i) := by
  simp [testbit, or]

theorem bits_xor (x y : BitVec w) (i : Nat) :
    testbit (xor x y) i = (testbit x i ^^ testbit y i) := by
  simp [testbit, xor]

theorem bits_not (x : BitVec w) {i : Nat} (h : i < w) :
    testbit (not x) i = !(testbit x i) := by
  simp [testbit, not, h]

set_option hygiene false in
/-- Proves an equation between bitwise expressions bit by bit. -/
local macro "bitwise" : tactic => `(tactic| (
  apply same_bits_eq; intro i hi
  simp only [bits_and, bits_or, bits_xor, bits_not _ hi, bits_zero, bits_mone hi]
  try generalize testbit x i = a
  try generalize testbit y i = b
  try generalize testbit z i = c
  try revert c
  try revert b
  try revert a
  decide))

theorem and_commut (x y : BitVec w) : and x y = and y x := by bitwise
theorem and_assoc (x y z : BitVec w) : and (and x y) z = and x (and y z) := by bitwise
theorem and_zero (x : BitVec w) : and x zero = zero := by bitwise
theorem and_zero_l (x : BitVec w) : and zero x = zero := by bitwise
theorem and_mone (x : BitVec w) : and x mone = x := by bitwise
theorem and_mone_l (x : BitVec w) : and mone x = x := by bitwise
theorem and_idem (x : BitVec w) : and x x = x := by bitwise

theorem or_commut (x y : BitVec w) : or x y = or y x := by bitwise
theorem or_assoc (x y z : BitVec w) : or (or x y) z = or x (or y z) := by bitwise
theorem or_zero (x : BitVec w) : or x zero = x := by bitwise
theorem or_zero_l (x : BitVec w) : or zero x = x := by bitwise
theorem or_mone (x : BitVec w) : or x mone = mone := by bitwise
theorem or_idem (x : BitVec w) : or x x = x := by bitwise

theorem and_or_distrib (x y z : BitVec w) : and x (or y z) = or (and x y) (and x z) := by
  bitwise
theorem and_or_distrib_l (x y z : BitVec w) : and (or x y) z = or (and x z) (and y z) := by
  bitwise
theorem or_and_distrib (x y z : BitVec w) : or x (and y z) = and (or x y) (or x z) := by
  bitwise
theorem or_and_distrib_l (x y z : BitVec w) : or (and x y) z = and (or x z) (or y z) := by
  bitwise
theorem and_or_absorb (x y : BitVec w) : and x (or x y) = x := by bitwise
theorem or_and_absorb (x y : BitVec w) : or x (and x y) = x := by bitwise

theorem xor_commut (x y : BitVec w) : xor x y = xor y x := by bitwise
theorem xor_assoc (x y z : BitVec w) : xor (xor x y) z = xor x (xor y z) := by bitwise
theorem xor_zero (x : BitVec w) : xor x zero = x := by bitwise
theorem xor_zero_l (x : BitVec w) : xor zero x = x := by bitwise
theorem xor_idem (x : BitVec w) : xor x x = zero := by bitwise
theorem and_xor_distrib (x y z : BitVec w) : and x (xor y z) = xor (and x y) (and x z) := by
  bitwise
theorem xor_is_zero (x y : BitVec w) : xor x y = zero ↔ x = y := by
  constructor
  · intro h
    apply same_bits_eq; intro i hi
    have := congrArg (fun v => testbit v i) h
    simp only [bits_xor, bits_zero] at this
    revert this; cases testbit x i <;> cases testbit y i <;> simp
  · rintro rfl; exact xor_idem x

theorem not_involutive (x : BitVec w) : not (not x) = x := by bitwise
theorem not_zero : not (zero : BitVec w) = mone := by bitwise
theorem not_mone : not (mone : BitVec w) = zero := by bitwise
theorem not_or_and_not (x y : BitVec w) : not (or x y) = and (not x) (not y) := by bitwise
theorem not_and_or_not (x y : BitVec w) : not (and x y) = or (not x) (not y) := by bitwise
theorem and_not_self (x : BitVec w) : and x (not x) = zero := by bitwise
theorem or_not_self (x : BitVec w) : or x (not x) = mone := by bitwise
theorem xor_not_self (x : BitVec w) : xor x (not x) = mone := by bitwise
theorem not_eq_xor_mone (x : BitVec w) : not x = xor x mone := by bitwise

theorem add_one_mone : add (one : BitVec w) mone = zero := by
  apply unsigned_inj
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [unsigned_w0, unsigned_w0]
  · rw [add_unsigned, unsigned_repr_eq, unsigned_mone, unsigned_zero, unsigned_one hw,
      show (1 : Z) + (modulus w - 1) = modulus w by zomega, Int.emod_self]

theorem neg_not (x : BitVec w) : neg x = add (not x) one := by
  unfold neg add not one; exact BitVec.neg_eq_not_add x

theorem not_neg (x : BitVec w) : not x = add (neg x) mone := by
  rw [neg_not, add_assoc, add_one_mone, add_zero]

theorem sub_add_not (x y : BitVec w) : sub x y = add (add x (not y)) one := by
  rw [sub_add_opp, neg_not, add_assoc]

end MI
end Integers
end CC
