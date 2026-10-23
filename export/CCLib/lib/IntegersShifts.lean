/-
  Theorems of `lib/Integers.v`, part 3: shifts, rotations, zero and sign
  extension.

  Generic in the word size `w` (namespace `CC.Integers.MI`).  Shift amounts
  are machine integers as in Rocq; `y.toNat` is `unsigned y` read as a `Nat`.
-/
import CCLib.lib.IntegersBits

namespace CC
namespace Integers
namespace MI

variable {w : Nat}

/-! ## Bits of shifts -/

theorem bits_shl (x y : BitVec w) {i : Nat} (hi : i < w) :
    testbit (shl x y) i = if i < y.toNat then false else testbit x (i - y.toNat) := by
  simp only [testbit, shl, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases h : i < y.toNat <;> simp [h]

theorem bits_shru (x y : BitVec w) {i : Nat} (_hi : i < w) :
    testbit (shru x y) i = if i + y.toNat < w then testbit x (i + y.toNat) else false := by
  simp only [testbit, shru, BitVec.getLsbD_ushiftRight]
  split
  · rw [Nat.add_comm]
  · exact BitVec.getLsbD_of_ge x _ (by zomega)

theorem bits_shr (x y : BitVec w) {i : Nat} (hi : i < w) :
    testbit (shr x y) i = testbit x (if i + y.toNat < w then i + y.toNat else w - 1) := by
  simp only [testbit, shr, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have : ¬ w ≤ i := by zomega
  simp only [this, decide_false, Bool.not_false, Bool.true_and]
  by_cases h : i + y.toNat < w
  · rw [if_pos (by zomega), if_pos h, Nat.add_comm]
  · rw [if_neg (by zomega), if_neg h]

/-! ## Shifting by zero, shifting zero -/

theorem shl_zero (x : BitVec w) : shl x zero = x := by simp [shl, zero]
theorem shru_zero (x : BitVec w) : shru x zero = x := by simp [shru, zero]
theorem shr_zero (x : BitVec w) : shr x zero = x := by simp [shr, zero]

theorem shl_zero_l (y : BitVec w) : shl zero y = zero := by
  apply same_bits_eq; intro i hi; rw [bits_shl _ _ hi]; simp [bits_zero]
theorem shru_zero_l (y : BitVec w) : shru zero y = zero := by
  apply same_bits_eq; intro i hi; rw [bits_shru _ _ hi]; simp [bits_zero]
theorem shr_zero_l (y : BitVec w) : shr zero y = zero := by
  apply same_bits_eq; intro i hi; rw [bits_shr _ _ hi]; simp [bits_zero]

/-! ## Composition of shifts -/

theorem toNat_add_of_lt {y z : BitVec w} (h : y.toNat + z.toNat < 2 ^ w) :
    (add y z).toNat = y.toNat + z.toNat := by
  simp only [add, BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

/-- `Int.shl_shl`.  Rocq states the side condition as `ltu y iwordsize`,
    `ltu z iwordsize`, `ltu (add y z) iwordsize`; here it is the weaker
    "`y + z` does not wrap". -/
theorem shl_shl (x y z : BitVec w) (h : y.toNat + z.toNat < 2 ^ w) :
    shl (shl x y) z = shl x (add y z) := by
  apply same_bits_eq; intro i hi
  rw [bits_shl _ _ hi, bits_shl _ _ hi, toNat_add_of_lt h]
  by_cases h1 : i < z.toNat
  · rw [if_pos h1, if_pos (by zomega)]
  · rw [if_neg h1, bits_shl _ _ (by zomega)]
    by_cases h2 : i - z.toNat < y.toNat
    · rw [if_pos h2, if_pos (by zomega)]
    · rw [if_neg h2, if_neg (by zomega)]; congr 1; zomega

theorem shru_shru (x y z : BitVec w) (h : y.toNat + z.toNat < 2 ^ w) :
    shru (shru x y) z = shru x (add y z) := by
  apply same_bits_eq; intro i hi
  rw [bits_shru _ _ hi, bits_shru _ _ hi, toNat_add_of_lt h]
  by_cases h1 : i + z.toNat < w
  · rw [if_pos h1, bits_shru _ _ h1]
    by_cases h2 : i + z.toNat + y.toNat < w
    · rw [if_pos h2, if_pos (by zomega)]; congr 1; zomega
    · rw [if_neg h2, if_neg (by zomega)]
  · rw [if_neg h1, if_neg (by zomega)]

theorem shr_shr (x y z : BitVec w) (h : y.toNat + z.toNat < 2 ^ w) :
    shr (shr x y) z = shr x (add y z) := by
  apply same_bits_eq; intro i hi
  rw [bits_shr _ _ hi, bits_shr _ _ hi, toNat_add_of_lt h]
  by_cases h1 : i + z.toNat < w
  · rw [if_pos h1, bits_shr _ _ h1]
    by_cases h2 : i + z.toNat + y.toNat < w
    · rw [if_pos h2, if_pos (by zomega)]; congr 1; zomega
    · rw [if_neg h2, if_neg (by zomega)]
  · rw [if_neg h1, bits_shr _ _ (by zomega)]
    by_cases h2 : w - 1 + y.toNat < w
    · rw [if_pos h2]
      have : y.toNat = 0 := by zomega
      rw [if_neg (by zomega)]; congr 1; zomega
    · rw [if_neg h2, if_neg (by zomega)]

/-! ## Shifts and bitwise operations -/

theorem and_shl (x y z : BitVec w) : and (shl x z) (shl y z) = shl (and x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_and, bits_shl _ _ hi, bits_shl _ _ hi, bits_shl _ _ hi]; split <;> simp [bits_and]

theorem or_shl (x y z : BitVec w) : or (shl x z) (shl y z) = shl (or x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_or, bits_shl _ _ hi, bits_shl _ _ hi, bits_shl _ _ hi]; split <;> simp [bits_or]

theorem xor_shl (x y z : BitVec w) : xor (shl x z) (shl y z) = shl (xor x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_xor, bits_shl _ _ hi, bits_shl _ _ hi, bits_shl _ _ hi]; split <;> simp [bits_xor]

theorem and_shru (x y z : BitVec w) : and (shru x z) (shru y z) = shru (and x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_and, bits_shru _ _ hi, bits_shru _ _ hi, bits_shru _ _ hi]; split <;> simp [bits_and]

theorem or_shru (x y z : BitVec w) : or (shru x z) (shru y z) = shru (or x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_or, bits_shru _ _ hi, bits_shru _ _ hi, bits_shru _ _ hi]; split <;> simp [bits_or]

theorem xor_shru (x y z : BitVec w) : xor (shru x z) (shru y z) = shru (xor x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_xor, bits_shru _ _ hi, bits_shru _ _ hi, bits_shru _ _ hi]; split <;> simp [bits_xor]

theorem and_shr (x y z : BitVec w) : and (shr x z) (shr y z) = shr (and x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_and, bits_shr _ _ hi, bits_shr _ _ hi, bits_shr _ _ hi, bits_and]

theorem or_shr (x y z : BitVec w) : or (shr x z) (shr y z) = shr (or x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_or, bits_shr _ _ hi, bits_shr _ _ hi, bits_shr _ _ hi, bits_or]

theorem xor_shr (x y z : BitVec w) : xor (shr x z) (shr y z) = shr (xor x y) z := by
  apply same_bits_eq; intro i hi
  rw [bits_xor, bits_shr _ _ hi, bits_shr _ _ hi, bits_shr _ _ hi, bits_xor]

/-! ## Shifts as multiplications and divisions -/

theorem shl_mul (x y : BitVec w) : shl x y = mul x (shl one y) := by
  unfold shl mul one
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.twoPow_eq]; rfl

theorem shl_mul_two_p (x y : BitVec w) : shl x y = mul x (repr ((2 : Z) ^ y.toNat)) := by
  rw [shl_mul]; congr 1
  apply unsigned_inj
  rw [unsigned_repr_eq]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [unsigned_w0, modulus_zero, Int.emod_one]
  · have h1 : (one : BitVec w).toNat = 1 := by
      have := unsigned_one hw; unfold unsigned at this; zomega
    simp only [unsigned, shl, BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq, Nat.one_mul]
    rw [modulus_natCast, Int.natCast_emod]; simp [Int.natCast_pow]

theorem shru_div_two_p (x y : BitVec w) :
    shru x y = repr (unsigned x / (2 : Z) ^ y.toNat) := by
  apply unsigned_inj
  have hx := x.isLt
  have hle : x.toNat / 2 ^ y.toNat ≤ x.toNat := Nat.div_le_self _ _
  rw [unsigned_repr]
  · simp only [unsigned, shru, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Int.natCast_ediv, Int.natCast_pow]; rfl
  · exact Int.ediv_nonneg (unsigned_nonneg x) (Int.le_of_lt (Int.pow_pos (by decide)))
  · have : ((x.toNat / 2 ^ y.toNat : Nat) : Z) = unsigned x / (2 : Z) ^ y.toNat := by
      rw [Int.natCast_ediv, Int.natCast_pow]; rfl
    rw [← this]; unfold max_unsigned; rw [modulus_natCast]; zomega

theorem shr_div_two_p (x y : BitVec w) :
    shr x y = repr (signed x / (2 : Z) ^ y.toNat) := by
  rw [← repr_signed (shr x y)]
  simp [signed, shr, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, Int.natCast_pow]

/-! ## Rotations -/

theorem rol_zero (x : BitVec w) : rol x zero = x := by
  unfold rol; split
  · rfl
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [zero, hi]

theorem ror_zero (x : BitVec w) : ror x zero = x := by
  unfold ror; split
  · rfl
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [zero, hi]

/-! ## Zero extension -/

theorem bits_zero_ext (n : Nat) (x : BitVec w) (i : Nat) :
    testbit (zero_ext n x) i = (decide (i < n) && testbit x i) := by
  unfold zero_ext
  split
  · by_cases hi : i < w
    · rw [decide_eq_true (by zomega)]; simp
    · rw [bits_above x (by zomega)]; simp
  · simp only [testbit, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
    by_cases hi : i < n
    · rw [decide_eq_true (by zomega), decide_eq_true hi]; simp
    · rw [decide_eq_false (by zomega), decide_eq_false hi]; simp

theorem zero_ext_above {n : Nat} (h : w ≤ n) (x : BitVec w) : zero_ext n x = x := by
  unfold zero_ext; rw [if_pos h]

theorem zero_ext_idem (n : Nat) (x : BitVec w) : zero_ext n (zero_ext n x) = zero_ext n x := by
  apply same_bits_eq; intro i _
  rw [bits_zero_ext, bits_zero_ext]; cases decide (i < n) <;> simp

theorem zero_ext_widen {n n' : Nat} (h : n ≤ n') (x : BitVec w) :
    zero_ext n' (zero_ext n x) = zero_ext n x := by
  apply same_bits_eq; intro i _
  rw [bits_zero_ext, bits_zero_ext]
  by_cases hi : i < n
  · rw [decide_eq_true (by zomega), decide_eq_true hi]; simp
  · rw [decide_eq_false hi]; simp

theorem zero_ext_narrow {n n' : Nat} (h : n ≤ n') (x : BitVec w) :
    zero_ext n (zero_ext n' x) = zero_ext n x := by
  apply same_bits_eq; intro i _
  rw [bits_zero_ext, bits_zero_ext, bits_zero_ext]
  by_cases hi : i < n
  · simp [hi, show i < n' by zomega]
  · simp [hi]

theorem zero_ext_mod (n : Nat) (x : BitVec w) :
    unsigned (zero_ext n x) = unsigned x % (2 : Z) ^ n := by
  have : (2 : Z) ^ n = ((2 ^ n : Nat) : Z) := by rw [Int.natCast_pow]; rfl
  rw [this]
  simp only [unsigned]
  rw [← Int.natCast_emod]
  congr 1
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_mod_two_pow, ← BitVec.getLsbD, ← BitVec.getLsbD]
  exact bits_zero_ext n x i

theorem zero_ext_range (n : Nat) (x : BitVec w) : unsigned (zero_ext n x) < (2 : Z) ^ n := by
  rw [zero_ext_mod]; exact Int.emod_lt_of_pos _ (Int.pow_pos (by decide))

/-! ## Sign extension -/

theorem bits_sign_ext {n : Nat} (hn : 0 < n) (x : BitVec w) {i : Nat} (hi : i < w) :
    testbit (sign_ext n x) i = testbit x (if i < n then i else n - 1) := by
  unfold sign_ext
  rw [if_neg (by zomega)]
  split
  · rw [if_pos (by zomega)]
  · rename_i hnw
    simp only [testbit, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_shiftLeft]
    have h1 : ¬ w ≤ i := by zomega
    simp only [h1, decide_false, Bool.not_false, Bool.true_and]
    by_cases h2 : i < n
    · rw [if_pos (by zomega), if_pos h2]
      rw [decide_eq_true (by zomega), decide_eq_false (by zomega)]
      simp only [Bool.not_false, Bool.true_and]; congr 1; zomega
    · rw [if_neg (by zomega), if_neg h2]
      rw [decide_eq_true (by zomega), decide_eq_false (by zomega)]
      simp only [Bool.not_false, Bool.true_and]; congr 1; zomega

theorem sign_ext_above {n : Nat} (hn : 0 < n) (h : w ≤ n) (x : BitVec w) : sign_ext n x = x := by
  unfold sign_ext; rw [if_neg (by zomega), if_pos h]

theorem sign_ext_widen {n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : BitVec w) :
    sign_ext n' (sign_ext n x) = sign_ext n x := by
  apply same_bits_eq; intro i hi
  rw [bits_sign_ext (by zomega) _ hi]
  split
  · rfl
  · rw [bits_sign_ext hn _ (by zomega), bits_sign_ext hn _ hi,
      if_neg (show ¬ i < n by zomega)]
    split <;> (congr 1 <;> zomega)

theorem sign_ext_idem {n : Nat} (hn : 0 < n) (x : BitVec w) :
    sign_ext n (sign_ext n x) = sign_ext n x :=
  sign_ext_widen hn (Nat.le_refl n) x

theorem sign_ext_narrow {n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : BitVec w) :
    sign_ext n (sign_ext n' x) = sign_ext n x := by
  apply same_bits_eq; intro i hi
  rw [bits_sign_ext hn _ hi, bits_sign_ext hn _ hi]
  split
  · rw [bits_sign_ext (by zomega) _ hi, if_pos (by zomega)]
  · by_cases hw : n - 1 < w
    · rw [bits_sign_ext (by zomega) _ hw, if_pos (by zomega)]
    · rw [bits_above _ (by zomega), bits_above _ (by zomega)]

theorem zero_ext_sign_ext {n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : BitVec w) :
    zero_ext n (sign_ext n' x) = zero_ext n x := by
  apply same_bits_eq; intro i hi
  rw [bits_zero_ext, bits_zero_ext]
  by_cases h2 : i < n
  · rw [decide_eq_true h2, bits_sign_ext (by zomega) _ hi, if_pos (by zomega)]
  · rw [decide_eq_false h2]; simp

theorem sign_ext_zero_ext {n n' : Nat} (hn : 0 < n) (h : n ≤ n') (x : BitVec w) :
    sign_ext n (zero_ext n' x) = sign_ext n x := by
  apply same_bits_eq; intro i hi
  rw [bits_sign_ext hn _ hi, bits_sign_ext hn _ hi, bits_zero_ext]
  split
  · rw [decide_eq_true (by zomega)]; simp
  · rw [decide_eq_true (by zomega)]; simp

end MI
end Integers
end CC
