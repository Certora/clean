/-
  Shift lemmas of `lib/Integers.v` about the 64-bit shifts whose amount is a
  32-bit integer (`Int64.shl'`, `Int64.shru'`, `Int64.shr'`), used by the
  correctness proof of 64-bit instruction selection
  (`aarch64/SelectLongproof.v`): `shl'_zero`, `shl'_shl'`, `shru'_shru'`,
  `shr'_shr'`, `shru'_shl'`, `shr'_shl'`, `shru'_zero_ext`,
  `shru'_zero_ext_0`, `shr'_sign_ext`.

  Since `Int64.shl' x y = x <<< y.toNat` (and similarly for the right
  shifts), the lemmas are stated with `Nat` shift amounts on `BitVec 64`.
-/
import CCLib.lib.IntegersShiftsExtra

namespace CC.Integers.Int64

theorem getLsbD_zero_ext (n : Nat) (x : Int64) (i : Nat) :
    (zero_ext n x).getLsbD i = (decide (i < n) && x.getLsbD i) :=
  bits_zero_ext n x i

theorem getLsbD_sign_ext {n : Nat} (hn : 0 < n) (x : Int64) {i : Nat} (hi : i < 64) :
    (sign_ext n x).getLsbD i = x.getLsbD (if i < n then i else n - 1) :=
  bits_sign_ext hn x hi

/-- `Int64.shl'_shl'` -/
theorem shl_shl_nat (x : Int64) (a n : Nat) : (x <<< a) <<< n = x <<< (a + n) :=
  (BitVec.shiftLeft_add x a n).symm

/-- `Int64.shru'_shru'` -/
theorem shru_shru_nat (x : Int64) (a n : Nat) : (x >>> a) >>> n = x >>> (a + n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight]; congr 1; omega

/-- `Int64.shr'_shr'` -/
theorem shr_shr_nat (x : Int64) (a n : Nat) :
    (x.sshiftRight a).sshiftRight n = x.sshiftRight (a + n) :=
  BitVec.sshiftRight_add.symm

/-- `Int64.shru'_shl'` -/
theorem shru_shl_nat (x : Int64) {a n : Nat} (ha : a < 64) (hn : n < 64) :
    (x <<< a) >>> n =
      if n < a then (zero_ext (64 - a) x) <<< (a - n)
      else zero_ext (64 - n) (x >>> (n - a)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hc : n < a
  · rw [if_pos hc]
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, getLsbD_zero_ext]
    by_cases h1 : n + i < 64
    · by_cases h2 : n + i < a
      · simp [h1, h2, hi, show i < a - n by omega]
      · simp [h1, h2, hi, show ¬ i < a - n by omega, show i - (a - n) = n + i - a by omega,
          show n + i - a < 64 - a by omega]
    · simp [h1, hi, show ¬ i < a - n by omega, show ¬ i - (a - n) < 64 - a by omega]
  · rw [if_neg hc]
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, getLsbD_zero_ext]
    by_cases h1 : n + i < 64
    · simp [h1, show ¬ n + i < a by omega, show i < 64 - n by omega,
        show n + i - a = n - a + i by omega]
    · simp [h1, show ¬ i < 64 - n by omega]

/-- `Int64.shr'_shl'` -/
theorem shr_shl_nat (x : Int64) {a n : Nat} (ha : a < 64) (hn : n < 64) :
    (x <<< a).sshiftRight n =
      if n < a then (sign_ext (64 - a) x) <<< (a - n)
      else sign_ext (64 - n) (x.sshiftRight (n - a)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hmsb : ∀ y : Int64, y.msb = y.getLsbD 63 := fun y => BitVec.msb_eq_getLsbD_last y
  by_cases hc : n < a
  · rw [if_pos hc]
    simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, hmsb]
    by_cases h1 : n + i < 64
    · by_cases h2 : n + i < a
      · simp [show ¬ (64 ≤ i) by omega, h1, h2, hi, show i < a - n by omega]
      · rw [getLsbD_sign_ext (by omega) _ (by omega)]
        simp [show ¬ (64 ≤ i) by omega, h1, h2, hi, show ¬ i < a - n by omega, show i - (a - n) = n + i - a by omega,
          show n + i - a < 64 - a by omega]
    · rw [getLsbD_sign_ext (by omega) _ (by omega)]
      simp [show ¬ (64 ≤ i) by omega, h1, hi, show ¬ i < a - n by omega, show ¬ i - (a - n) < 64 - a by omega,
        show ¬ (63 < a) by omega]
      congr 1; omega
  · rw [if_neg hc]
    rw [getLsbD_sign_ext (by omega) _ hi]
    simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, hmsb]
    by_cases h1 : n + i < 64
    · simp [show ¬ (64 ≤ i) by omega, h1, show ¬ n + i < a by omega, show i < 64 - n by omega,
        show n + i - a = n - a + i by omega, show n - a + i < 64 by omega]
    · simp [show ¬ (64 ≤ i) by omega, h1, show ¬ i < 64 - n by omega, show ¬ (63 < a) by omega,
        show n - a + (64 - n - 1) < 64 by omega]
      simp only [← BitVec.getLsbD_eq_getElem]
      simp [show ¬ (64 ≤ 64 - n - 1) by omega]
      congr 1; omega

/-- `Int64.shru'_zero_ext` -/
theorem shru_zero_ext_nat (x : Int64) (s n : Nat) :
    (zero_ext (s + n) x) >>> n = zero_ext s (x >>> n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, getLsbD_zero_ext]
  by_cases h : i < s
  · simp [h, show n + i < s + n by omega]
  · simp [h, show ¬ n + i < s + n by omega]

/-- `Int64.shru'_zero_ext_0` -/
theorem shru_zero_ext_0_nat (x : Int64) {s n : Nat} (h : s ≤ n) :
    (zero_ext s x) >>> n = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, getLsbD_zero_ext]
  simp [show ¬ n + i < s by omega]

/-- `Int64.shr'_sign_ext` -/
theorem shr_sign_ext_nat (x : Int64) {s n : Nat} (hs : 0 < s) (h : s + n < 64) :
    (sign_ext (s + n) x).sshiftRight n = sign_ext s (x.sshiftRight n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hmsb : ∀ y : Int64, y.msb = y.getLsbD 63 := fun y => BitVec.msb_eq_getLsbD_last y
  rw [getLsbD_sign_ext hs _ hi]
  simp only [BitVec.getLsbD_sshiftRight, hmsb]
  have n64 : ¬ (64 ≤ i) := by omega
  by_cases h2 : i < s
  · rw [getLsbD_sign_ext (n := s + n) (by omega) x (show n + i < 64 by omega)]
    simp [n64, h2, show n + i < 64 by omega, show n + i < s + n by omega]
  · by_cases h1 : n + i < 64
    · rw [getLsbD_sign_ext (n := s + n) (by omega) x h1]
      simp [n64, h1, h2, show ¬ n + i < s + n by omega, show n + (s - 1) < 64 by omega,
        show ¬ (64 ≤ s - 1) by omega]
      simp only [← BitVec.getLsbD_eq_getElem]
      congr 1; omega
    · rw [getLsbD_sign_ext (n := s + n) (by omega) x (show 63 < 64 by omega)]
      simp [n64, h1, h2, show ¬ 63 < s + n by omega, show n + (s - 1) < 64 by omega,
        show ¬ (64 ≤ s - 1) by omega]
      simp only [← BitVec.getLsbD_eq_getElem]
      congr 1; omega

end CC.Integers.Int64

namespace CC.Integers

theorem Int.repr_toNat_lt64 {k : Nat} (h : k < 64) : (Int.repr (k : Z) : Int).toNat = k := by
    have := Int.unsigned_repr (z := (k : Z)) (by zomega) (by
      have : @Eq _root_.Int Int.max_unsigned (2 ^ 32 - 1) := by decide
      zomega)
    have e : ((Int.repr (k : Z) : Int).toNat : _root_.Int) = k := this
    zomega

namespace Int64

theorem shl_nat_eq_mul (y : Int64) {m : Nat} (hm : m < 64) :
    y <<< m = mul y (repr ((2 : Z) ^ m)) := by
  have hu := unsigned_repr (z := (m : Z)) (by zomega) (by
    have : @Eq _root_.Int max_unsigned (2 ^ 64 - 1) := by decide
    zomega)
  have e : ((repr (m : Z) : Int64).toNat : _root_.Int) = m := hu
  have e' : (repr (m : Z) : Int64).toNat = m := by zomega
  have := shl_mul_two_p y (repr (m : Z))
  rw [e'] at this
  rw [← this]; show y <<< m = y <<< (repr (m : Z) : Int64).toNat; rw [e']

theorem ltu_iw'_of_toNat {y : Int} (h : y.toNat < 64) : Int.ltu y iwordsize' = true := by
  rw [Int.ltu_toNat]
  have : (iwordsize' : Int).toNat = 64 := by decide
  rw [this]; exact decide_eq_true h

/-- `Int64.one_bits'` with a single one bit: multiplication by `x` is a left shift. -/
theorem one_bits'_single {x : Int64} {i : Int} (h : one_bits' x = [i]) :
    Int.ltu i iwordsize' = true ∧ ∀ y, mul y x = y <<< i.toNat := by
  have hr := unsigned_range x
  have hm : modulus = (2 ^ 64 : _root_.Int) := by decide
  rw [hm] at hr
  have h' : (Z_one_bits 64 (unsigned x) 0).map Int.repr = [i] := h
  cases hz : Z_one_bits 64 (unsigned x) 0 with
  | nil => rw [hz] at h'; cases h'
  | cons k t =>
    cases t with
    | cons _ _ => rw [hz] at h'; simp at h'
    | nil =>
      rw [hz] at h'
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h'
      subst h'
      obtain ⟨m, rfl, hm, hx⟩ := Z_one_bits_single hr.1 hr.2 hz
      rw [_root_.Int.zero_add]
      have ht := Int.repr_toNat_lt64 hm
      refine ⟨ltu_iw'_of_toNat (by omega), fun y => ?_⟩
      rw [ht, shl_nat_eq_mul y hm, ← hx, repr_unsigned]

/-- `Int64.one_bits'` with two one bits: multiplication by `x` is a sum of two left shifts. -/
theorem one_bits'_double {x : Int64} {i j : Int} (h : one_bits' x = [i, j]) :
    Int.ltu i iwordsize' = true ∧ Int.ltu j iwordsize' = true ∧
      ∀ y, mul y x = add (y <<< i.toNat) (y <<< j.toNat) := by
  have hr := unsigned_range x
  have hm : modulus = (2 ^ 64 : _root_.Int) := by decide
  rw [hm] at hr
  have h' : (Z_one_bits 64 (unsigned x) 0).map Int.repr = [i, j] := h
  cases hz : Z_one_bits 64 (unsigned x) 0 with
  | nil => rw [hz] at h'; cases h'
  | cons k t =>
    cases t with
    | nil => rw [hz] at h'; simp at h'
    | cons k2 t =>
      cases t with
      | cons _ _ => rw [hz] at h'; simp at h'
      | nil =>
        rw [hz] at h'
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h'
        obtain ⟨rfl, rfl⟩ := h'
        obtain ⟨m1, m2, rfl, rfl, hm1, hm2, hx⟩ := Z_one_bits_double hr.1 hr.2 hz
        simp only [_root_.Int.zero_add]
        have ht1 := Int.repr_toNat_lt64 hm1
        have ht2 := Int.repr_toNat_lt64 hm2
        refine ⟨ltu_iw'_of_toNat (by omega), ltu_iw'_of_toNat (by omega), fun y => ?_⟩
        rw [ht1, ht2, shl_nat_eq_mul y hm1, shl_nat_eq_mul y hm2, ← mul_add_distr_r, ← repr_add,
          ← hx, repr_unsigned]

end Int64
end CC.Integers

namespace CC.Integers.Int64

/-- `Int64.shl'_zero_ext` -/
theorem shl_zero_ext_nat (x : Int64) {m n : Nat} (h : m ≤ n) :
    zero_ext n (x <<< m) = (zero_ext (n - m) x) <<< m := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_zero_ext, BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < m
  · simp [h1]
  · by_cases h2 : i < n
    · simp [h1, h2, hi, show i - m < n - m by omega]
    · simp [h1, h2, show ¬ i - m < n - m by omega]

/-- `Int64.or_ror'` -/
theorem ror_eq_or_nat (z y : Int64) {a : Nat} (hy : y.toNat < 64) (h : a + y.toNat = 64) :
    ror z y = or (z <<< a) (z >>> y.toNat) := by
  simp only [ror, MI.ror, or, MI.or]
  simp
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_rotateRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  rw [Nat.mod_eq_of_lt hy]
  by_cases hc : i < 64 - y.toNat
  · simp [hc, show i < a by omega]
  · simp [hc, show ¬ i < a by omega, show i - (64 - y.toNat) = i - a by omega,
      BitVec.getLsbD_of_ge z (y.toNat + i) (by omega)]

end CC.Integers.Int64
