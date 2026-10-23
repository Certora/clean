/-
  Neededness analysis — port of `backend/NeedDomain.v`, the sections
  "Properties of agreement between 32-bit integers" and "… 64-bit integers".

  `iagree` and `lagree` are the same notion at word sizes 32 and 64, so the
  lemmas are proved once, for an arbitrary word size `w`, about the generic
  relation `bagree` (namespace `CC.NeedDomain.Bits`), and then instantiated.
-/
import CCLib.backend.NeedDomain
import CCLib.lib.IntegersBits

namespace CC
namespace NeedDomain
namespace Bits

variable {w : Nat}

/-- Agreement of `p` and `q` on the bits set in `mask` (generic `iagree`). -/
def bagree (p q mask : BitVec w) : Prop :=
  ∀ i : Nat, i < w → mask.getLsbD i = true → p.getLsbD i = q.getLsbD i

theorem bagree_refl (p m : BitVec w) : bagree p p m := fun _ _ _ => rfl

theorem bagree_and_eq (x y m : BitVec w) : bagree x y m ↔ x &&& m = y &&& m := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and]
    cases hm : m.getLsbD i
    · simp
    · simp [h i hi hm]
  · intro h i hi hm
    have := congrArg (fun z => z.getLsbD i) h
    simpa [BitVec.getLsbD_and, hm] using this

theorem bagree_mone {p q : BitVec w} (h : bagree p q (BitVec.allOnes w)) : p = q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h i hi (by simp [hi])

theorem bagree_zero (p q : BitVec w) : bagree p q 0 := by
  intro i _ hm; simp at hm

theorem bagree_and {x y n m : BitVec w} (h : bagree x y (m &&& n)) :
    bagree (x &&& n) (y &&& n) m := by
  intro i hi hm
  simp only [BitVec.getLsbD_and]
  cases hn : n.getLsbD i
  · simp
  · simp [h i hi (by simp [hm, hn])]

theorem bagree_not {x y m : BitVec w} (h : bagree x y m) : bagree (~~~x) (~~~y) m := by
  intro i hi hm
  rw [BitVec.getLsbD_not, BitVec.getLsbD_not, h i hi hm]

theorem bagree_not' {x y m : BitVec w} (h : bagree (~~~x) (~~~y) m) : bagree x y m := by
  have := bagree_not h
  simpa using this

theorem bagree_or {x y n m : BitVec w} (h : bagree x y (m &&& ~~~n)) :
    bagree (x ||| n) (y ||| n) m := by
  intro i hi hm
  simp only [BitVec.getLsbD_or]
  cases hn : n.getLsbD i
  · rw [h i hi (by rw [BitVec.getLsbD_and, BitVec.getLsbD_not, hm, hn]; simp [hi])]
  · simp

theorem bagree_bitwise_binop (sem : Bool → Bool → Bool) (f : BitVec w → BitVec w → BitVec w)
    (hf : ∀ x y i, i < w → (f x y).getLsbD i = sem (x.getLsbD i) (y.getLsbD i))
    {x1 x2 y1 y2 m : BitVec w} (h1 : bagree x1 y1 m) (h2 : bagree x2 y2 m) :
    bagree (f x1 x2) (f y1 y2) m := by
  intro i hi hm
  rw [hf _ _ i hi, hf _ _ i hi, h1 i hi hm, h2 i hi hm]

theorem bagree_shl {x y m : BitVec w} {k : Nat} (h : bagree x y (m >>> k)) :
    bagree (x <<< k) (y <<< k) m := by
  intro i hi hm
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases hk : i < k
  · simp [hk]
  · have hik : i - k < w := by omega
    have := h (i - k) hik (by
      simp only [BitVec.getLsbD_ushiftRight]
      rw [show k + (i - k) = i by omega]; exact hm)
    simp [hk, hi, this]

theorem bagree_shru {x y m : BitVec w} {k : Nat} (h : bagree x y (m <<< k)) :
    bagree (x >>> k) (y >>> k) m := by
  intro i hi hm
  simp only [BitVec.getLsbD_ushiftRight]
  by_cases hk : k + i < w
  · apply h (k + i) hk
    simp only [BitVec.getLsbD_shiftLeft]
    simp [hk, show ¬ (k + i < k) by omega, show k + i - k = i by omega, hm]
  · rw [BitVec.getLsbD_of_ge x _ (by omega), BitVec.getLsbD_of_ge y _ (by omega)]

theorem bagree_shr_1 {x y m : BitVec w} {k : Nat} (hm : (m <<< k) >>> k = m)
    (h : bagree x y (m <<< k)) :
    bagree (x.sshiftRight k) (y.sshiftRight k) m := by
  intro i hi hmi
  rw [← hm, BitVec.getLsbD_ushiftRight] at hmi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_sshiftRight]
  simp only [show ¬ (w ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and]
  by_cases hk : k + i < w
  · simp only [hk, if_true]
    exact h (k + i) hk hmi
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)] at hmi
    exact absurd hmi (by simp)

/-- The constant `repr min_signed`: only the top bit set. -/
theorem bagree_shr {x y m : BitVec w} {k : Nat}
    (h : bagree x y ((m <<< k) ||| BitVec.twoPow w (w - 1))) :
    bagree (x.sshiftRight k) (y.sshiftRight k) m := by
  intro i hi hmi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_sshiftRight]
  simp only [show ¬ (w ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and]
  by_cases hk : k + i < w
  · simp only [hk, if_true]
    apply h (k + i) hk
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    simp [hk, show ¬ (k + i < k) by omega, show k + i - k = i by omega, hmi]
  · simp only [hk, if_false, BitVec.msb_eq_getLsbD_last]
    have hw : w - 1 < w := by omega
    exact h (w - 1) hw (by rw [BitVec.getLsbD_or, BitVec.getLsbD_twoPow]; simp [hw])

theorem bagree_rotateLeft {p q m : BitVec w} {k : Nat} (h : bagree p q (m.rotateRight k)) :
    bagree (p.rotateLeft k) (q.rotateLeft k) m := by
  intro i hi hmi
  have hw : 0 < w := by omega
  have hr : k % w < w := Nat.mod_lt _ hw
  rw [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateLeft]
  by_cases hik : i < k % w
  · simp only [hik, decide_true, cond_true]
    apply h (w - k % w + i) (by omega)
    rw [BitVec.getLsbD_rotateRight]
    simp only [show ¬ (w - k % w + i < w - k % w) by omega, decide_false, cond_false,
      show w - k % w + i < w by omega, decide_true, Bool.true_and]
    rwa [show w - k % w + i - (w - k % w) = i by omega]
  · simp only [hik, decide_false, cond_false, hi, decide_true, Bool.true_and]
    apply h (i - k % w) (by omega)
    rw [BitVec.getLsbD_rotateRight]
    simp only [show i - k % w < w - k % w by omega, decide_true, cond_true]
    rwa [show k % w + (i - k % w) = i by omega]

theorem bagree_rotateRight {p q m : BitVec w} {k : Nat} (h : bagree p q (m.rotateLeft k)) :
    bagree (p.rotateRight k) (q.rotateRight k) m := by
  intro i hi hmi
  have hw : 0 < w := by omega
  have hr : k % w < w := Nat.mod_lt _ hw
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateRight]
  by_cases hik : i < w - k % w
  · simp only [hik, decide_true, cond_true]
    apply h (k % w + i) (by omega)
    rw [BitVec.getLsbD_rotateLeft]
    simp only [show ¬ (k % w + i < k % w) by omega, decide_false, cond_false,
      show k % w + i < w by omega, decide_true, Bool.true_and]
    rwa [show k % w + i - k % w = i by omega]
  · simp only [hik, decide_false, cond_false, hi, decide_true, Bool.true_and]
    apply h (i - (w - k % w)) (by omega)
    rw [BitVec.getLsbD_rotateLeft]
    simp only [show i - (w - k % w) < k % w by omega, decide_true, cond_true]
    rwa [show w - k % w + (i - (w - k % w)) = i by omega]

/-! ### Agreement on the low bits (`complete_mask`, modular arithmetic) -/

/-- The mask of the `k` low bits, `zero_ext k mone`. -/
def lowMask (w k : Nat) : BitVec w := Integers.MI.zero_ext k (BitVec.allOnes w)

theorem getLsbD_lowMask (k i : Nat) : (lowMask w k).getLsbD i = (decide (i < k) && decide (i < w)) := by
  unfold lowMask Integers.MI.zero_ext
  split
  · simp only [BitVec.getLsbD_allOnes]
    by_cases hi : i < w
    · simp [hi, show i < k by omega]
    · simp [hi]
  · rw [BitVec.getLsbD_and, BitVec.getLsbD_allOnes, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < k
    · simp [hi, show i < w by omega, show w - k + i < w by omega]
    · simp [hi, show ¬ (w - k + i < w) by omega]

/-- The number of significant bits of `m`, as a natural number. -/
def nsize (m : BitVec w) : Nat := (Integers.MI.size m).toNat

theorem nsize_eq (m : BitVec w) : nsize m = if 0 < m.toNat then m.toNat.log2 + 1 else 0 := by
  unfold nsize Integers.MI.size Integers.Zsize Integers.MI.unsigned
  by_cases h : 0 < m.toNat
  · simp [h]
  · simp [h]

theorem nsize_le (m : BitVec w) : nsize m ≤ w := by
  rw [nsize_eq]
  split
  · have : m.toNat.log2 < w := (Nat.log2_lt (by omega)).2 m.isLt
    omega
  · omega

theorem size_eq_nsize (m : BitVec w) : Integers.MI.size m = (nsize m : Z) := by
  unfold nsize Integers.MI.size Integers.Zsize
  split <;> simp

theorem getLsbD_of_nsize_le (m : BitVec w) {i : Nat} (h : nsize m ≤ i) : m.getLsbD i = false := by
  rw [← BitVec.testBit_toNat]
  apply Nat.testBit_lt_two_pow
  rw [nsize_eq] at h
  split at h
  · have := @Nat.lt_log2_self m.toNat
    have : 2 ^ (m.toNat.log2 + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have : m.toNat = 0 := by omega
    rw [this]; exact Nat.two_pow_pos _

theorem lt_nsize_of_getLsbD (m : BitVec w) {i : Nat} (h : m.getLsbD i = true) : i < nsize m := by
  apply Nat.lt_of_not_le; intro hle
  rw [getLsbD_of_nsize_le m hle] at h; exact absurd h (by simp)

theorem bagree_lowMask_iff {x y : BitVec w} {k : Nat} :
    bagree x y (lowMask w k) ↔ BitVec.setWidth k x = BitVec.setWidth k y := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
    by_cases hw : i < w
    · rw [h i hw (by rw [getLsbD_lowMask]; simp [hi, hw])]
    · rw [BitVec.getLsbD_of_ge x _ (by omega), BitVec.getLsbD_of_ge y _ (by omega)]
  · intro h i hi hm
    rw [getLsbD_lowMask] at hm
    have hik : i < k := by simp at hm; omega
    have := congrArg (fun z => z.getLsbD i) h
    simpa [BitVec.getLsbD_setWidth, hik] using this

theorem bagree_of_setWidth {x y m : BitVec w} {k : Nat} (hk : nsize m ≤ k)
    (h : BitVec.setWidth k x = BitVec.setWidth k y) : bagree x y m := by
  intro i hi hm
  have hik : i < k := Nat.lt_of_lt_of_le (lt_nsize_of_getLsbD m hm) hk
  have := congrArg (fun z => z.getLsbD i) h
  simpa [BitVec.getLsbD_setWidth, hik] using this

theorem bagree_lowMask_mono {x y : BitVec w} {k k' : Nat} (hk : k' ≤ k)
    (h : bagree x y (lowMask w k)) : bagree x y (lowMask w k') := by
  intro i hi hm
  rw [getLsbD_lowMask] at hm
  exact h i hi (by rw [getLsbD_lowMask]; simp at hm ⊢; omega)

/-- Generic form of `add_sound`, `sub_sound`, `mul_sound`, `neg_sound`. -/
theorem bagree_add {a b c d m : BitVec w} (h1 : bagree a c (lowMask w (nsize m)))
    (h2 : bagree b d (lowMask w (nsize m))) : bagree (a + b) (c + d) m := by
  rw [bagree_lowMask_iff] at h1 h2
  apply bagree_of_setWidth (Nat.le_refl _)
  rw [BitVec.setWidth_add _ _ (nsize_le m), BitVec.setWidth_add _ _ (nsize_le m), h1, h2]

theorem bagree_mul {a b c d m : BitVec w} (h1 : bagree a c (lowMask w (nsize m)))
    (h2 : bagree b d (lowMask w (nsize m))) : bagree (a * b) (c * d) m := by
  rw [bagree_lowMask_iff] at h1 h2
  apply bagree_of_setWidth (Nat.le_refl _)
  rw [BitVec.setWidth_mul _ _ (nsize_le m), BitVec.setWidth_mul _ _ (nsize_le m), h1, h2]

theorem bagree_neg {a c m : BitVec w} (h1 : bagree a c (lowMask w (nsize m))) :
    bagree (-a) (-c) m := by
  rw [bagree_lowMask_iff] at h1
  apply bagree_of_setWidth (Nat.le_refl _)
  rw [BitVec.setWidth_neg_of_le (nsize_le m), BitVec.setWidth_neg_of_le (nsize_le m), h1]

theorem bagree_sub {a b c d m : BitVec w} (h1 : bagree a c (lowMask w (nsize m)))
    (h2 : bagree b d (lowMask w (nsize m))) : bagree (a - b) (c - d) m := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  rw [bagree_lowMask_iff] at h1 h2
  apply bagree_of_setWidth (Nat.le_refl _)
  rw [BitVec.setWidth_add _ _ (nsize_le m), BitVec.setWidth_add _ _ (nsize_le m),
    BitVec.setWidth_neg_of_le (nsize_le m), BitVec.setWidth_neg_of_le (nsize_le m), h1, h2]

theorem nsize_lowMask {k : Nat} (hk : k ≤ w) : nsize (lowMask w k) = k := by
  apply Nat.le_antisymm
  · have hlt : (lowMask w k).toNat < 2 ^ k := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [BitVec.testBit_toNat, getLsbD_lowMask]; simp; omega
    rw [nsize_eq]
    split
    · have := (Nat.log2_lt (by omega)).2 hlt
      omega
    · omega
  · apply Nat.le_of_not_lt; intro hlt
    have h1 := getLsbD_of_nsize_le (lowMask w k) (i := k - 1) (by omega)
    rw [getLsbD_lowMask] at h1
    simp at h1; omega

/-! ### Zero and sign extension -/

theorem getLsbD_zero_ext (k : Nat) (x : BitVec w) (i : Nat) :
    (Integers.MI.zero_ext k x).getLsbD i = (decide (i < k) && x.getLsbD i) := by
  unfold Integers.MI.zero_ext
  split
  · by_cases hi : i < k
    · simp [hi]
    · simp only [hi, decide_false, Bool.false_and]
      exact BitVec.getLsbD_of_ge x i (by omega)
  · rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
    by_cases hi : i < k
    · simp [hi, show w - k + i < w by omega]
    · simp [hi, show ¬ (w - k + i < w) by omega]

theorem getLsbD_sign_ext {k : Nat} (hk : 0 < k) (hkw : k < w) (x : BitVec w) {i : Nat}
    (hi : i < w) :
    (Integers.MI.sign_ext k x).getLsbD i = if i < k then x.getLsbD i else x.getLsbD (k - 1) := by
  unfold Integers.MI.sign_ext
  rw [if_neg (by omega), if_neg (by omega), BitVec.getLsbD_sshiftRight]
  simp only [show ¬ (w ≤ i) by omega, decide_false, Bool.not_false, Bool.true_and]
  by_cases hik : i < k
  · rw [if_pos (by omega), if_pos hik, BitVec.getLsbD_shiftLeft]
    simp [show w - k + i < w by omega, show ¬ (w - k + i < w - k) by omega,
      show w - k + i - (w - k) = i by omega]
  · rw [if_neg (by omega), if_neg hik, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
    simp [show w - 1 < w by omega, show ¬ (w - 1 < w - k) by omega,
      show w - 1 - (w - k) = k - 1 by omega]

theorem bagree_zero_ext {p q m : BitVec w} {k : Nat}
    (h : bagree p q (Integers.MI.zero_ext k m)) :
    bagree (Integers.MI.zero_ext k p) (Integers.MI.zero_ext k q) m := by
  intro i hi hm
  rw [getLsbD_zero_ext, getLsbD_zero_ext]
  by_cases hik : i < k
  · rw [h i hi (by rw [getLsbD_zero_ext]; simp [hik, hm])]
  · simp [hik]

theorem bagree_sign_ext {p q m : BitVec w} {k : Nat} (hk : 0 < k)
    (hlow : bagree p q (Integers.MI.zero_ext k m))
    (htop : k < w → p.getLsbD (k - 1) = q.getLsbD (k - 1)) :
    bagree (Integers.MI.sign_ext k p) (Integers.MI.sign_ext k q) m := by
  intro i hi hm
  by_cases hkw : k < w
  · rw [getLsbD_sign_ext hk hkw p hi, getLsbD_sign_ext hk hkw q hi]
    by_cases hik : i < k
    · rw [if_pos hik, if_pos hik]
      exact hlow i hi (by rw [getLsbD_zero_ext]; simp [hik, hm])
    · rw [if_neg hik, if_neg hik]; exact htop hkw
  · have e : ∀ x : BitVec w, Integers.MI.sign_ext k x = x := by
      intro x; unfold Integers.MI.sign_ext; rw [if_neg (by omega), if_pos (by omega)]
    rw [e, e]
    exact hlow i hi (by rw [getLsbD_zero_ext]; simp [show i < k by omega, hm])

end Bits
end NeedDomain
end CC
