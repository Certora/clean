/-
  Arithmetic theorems of `lib/Floats.v` used by the optimisations:
  `Float.mul2_add` / `Float32.mul2_add` (`x * 2 = x + x`, used by constant
  propagation) and `Float.div_mul_inverse` / `Float32.div_mul_inverse`
  (dividing by `±2^k` is multiplying by `±2^-k`, used by instruction
  selection).

  In Rocq these follow from Flocq's `Bmult2_Bplus` and `Bdiv_mult_inverse`.
  Here they are proved on the exact IEEE model of `CCLib.lib.FloatModel`.

  `Float.exact_inverse` / `Float32.exact_inverse` (`IEEE754_extra.Bexact_inverse`)
  are defined here, on the IEEE bit pattern: a finite normal number whose
  fraction field is zero, i.e. `±2^k`, has the exact inverse `±2^-k` when that
  is again a normal number (biased exponent `2*bias - E ≥ 1`); this is the
  condition `emin ≤ e'` of Rocq's definition (its other test, `e' ≤ emax`,
  always holds).
-/
import CCLib.lib.FloatsConv

namespace CC
namespace FloatModel
namespace UnpackedFloat

/-! ## Rounding helpers -/

/-- When the exponent is at most the target exponent, `round` does not need
to decrease the exponent first. -/
theorem round_eq_roundWithAccuracy (spec : Format) (s : Sign) (m : Nat) (e : Int)
    (h : e ≤ spec.targetExponent (totalExponent m e)) :
    round spec s m e = roundWithAccuracy spec s m e .exact := by
  unfold round
  simp only [decreaseExponent]
  have h0 : (e - spec.targetExponent (totalExponent m e)).toNat = 0 := by omega
  rw [h0, Nat.shiftLeft_zero]
  simp

theorem roundWithAccuracy_ne_nan (spec : Format) (s : Sign) (m : Nat) (e : Int) (a : Accuracy) :
    roundWithAccuracy spec s m e a ≠ .notANumber := by
  unfold roundWithAccuracy
  simp only []
  split <;> simp

theorem round_ne_nan (spec : Format) (s : Sign) (m : Nat) (e : Int) :
    round spec s m e ≠ .notANumber := by
  unfold round
  exact roundWithAccuracy_ne_nan _ _ _ _ _

theorem normalize_apply (spec : Format) (s : Sign) (n : Nat) (e : Int) (zs : Sign) (hn : 0 < n) :
    normalize spec (s.apply n) e zs = round spec s n e := by
  cases s with
  | negative =>
    have : compare (Sign.negative.apply (n : Int)) 0 = .lt := by
      have hn0 : n ≠ 0 := by omega
      simp [Sign.apply, compare, compareOfLessAndEq, hn0]
    simp only [normalize, this]
    congr 1
    simp [Sign.apply]
  | positive =>
    have h : (0 : Int) < n := by omega
    have : compare (Sign.positive.apply (n : Int)) 0 = .gt := by
      have hn0 : n ≠ 0 := by omega
      simp [Sign.apply, compare, compareOfLessAndEq, Int.not_lt.mpr (Int.le_of_lt h), hn0]
    simp only [normalize, this]
    congr 1

theorem sign_mul_positive (s : Sign) : s * .positive = s := by cases s <;> rfl

theorem sign_beq_self (s : Sign) : (s == s) = true := by cases s <;> rfl

/-! ## `x * 2 = x + x` -/

theorem mul_two_eq_add (spec : Format) (x : UnpackedFloat) (h2) :
    mul spec x (.finite .positive (2 <<< (spec.mantissaBits - 2))
      (-((spec.mantissaBits - 2 : Nat) : Int)) h2) = add spec x x := by
  cases x with
  | notANumber => rfl
  | infinity s => simp [mul, add, sign_mul_positive]
  | zero s => simp [mul, add, sign_mul_positive]
  | finite s m e hm =>
    simp only [mul, add, sign_mul_positive, Int.min_self, decreaseExponent, Int.sub_self,
      Int.toNat_zero, Nat.shiftLeft_zero]
    have happ : s.apply (m : Int) + s.apply (m : Int) = s.apply ((2 * m : Nat) : Int) := by
      cases s <;> simp [Sign.apply] <;> omega
    have hmb : 1 ≤ spec.mantissaBitsWithoutImplicit := spec.hm
    have h2m : 0 < 2 * m := by omega
    rw [happ, normalize_apply _ _ _ _ _ h2m,
      ← round_shift spec s (2 * m) (spec.mantissaBits - 2) e h2m,
      round_eq_roundWithAccuracy]
    · have hm2 : m * (2 <<< (spec.mantissaBits - 2)) = (2 * m) <<< (spec.mantissaBits - 2) := by
        simp only [Nat.shiftLeft_eq]
        rw [← Nat.mul_assoc, Nat.mul_comm m 2]
      rw [hm2, Int.sub_eq_add_neg]
    · rw [totalExponent_shift _ _ _ h2m]
      simp only [Format.targetExponent, totalExponent]
      have hl : 1 ≤ (2 * m).log2 := by
        rw [Nat.le_log2 (by omega)]; omega
      simp only [Format.mantissaBits] at *
      omega

/-! ## Division by a power of two -/

/-- The residual bits after shifting are exactly described by
`accuracyOfFraction` of the remainder (one step). -/
theorem ofMA_frac_step (M b r j : Nat) (hb : b < 2) (hr : r < 2 ^ j) :
    ExtendedMantissa.ofMantissaAndAccuracy M (accuracyOfFraction (r + 2 ^ j * b) (2 ^ (j + 1))) =
      ⟨M, b != 0, r != 0⟩ := by
  have hp : 0 < 2 ^ j := Nat.two_pow_pos j
  rw [Nat.pow_succ]
  unfold accuracyOfFraction
  by_cases hb0 : b = 0
  · subst hb0
    by_cases hr0 : r = 0
    · subst hr0; simp [ExtendedMantissa.ofMantissaAndAccuracy]
    · have hc : compare (2 * (r + 2 ^ j * 0)) (2 ^ j * 2) = .lt :=
        Nat.compare_eq_lt.mpr (by rw [Nat.mul_zero, Nat.add_zero, Nat.mul_comm]; omega)
      rw [if_neg (by omega), hc]
      simp [ExtendedMantissa.ofMantissaAndAccuracy, hr0]
  · have hb1 : b = 1 := by omega
    subst hb1
    by_cases hr0 : r = 0
    · subst hr0
      have hc : compare (2 * (0 + 2 ^ j * 1)) (2 ^ j * 2) = .eq :=
        Nat.compare_eq_eq.mpr (by omega)
      rw [if_neg (by omega), hc]
      simp [ExtendedMantissa.ofMantissaAndAccuracy]
    · have hc : compare (2 * (r + 2 ^ j * 1)) (2 ^ j * 2) = .gt :=
        Nat.compare_eq_gt.mpr (by omega)
      rw [if_neg (by omega), hc]
      simp [ExtendedMantissa.ofMantissaAndAccuracy, hr0]

theorem ofMA_frac_bits (q r j : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy q (accuracyOfFraction r (2 ^ j))).mantissa = q ∧
    ((ExtendedMantissa.ofMantissaAndAccuracy q (accuracyOfFraction r (2 ^ j))).roundBit ||
      (ExtendedMantissa.ofMantissaAndAccuracy q (accuracyOfFraction r (2 ^ j))).stickyBit) =
      (r != 0) := by
  unfold accuracyOfFraction
  by_cases hr0 : r = 0
  · subst hr0; simp [ExtendedMantissa.ofMantissaAndAccuracy]
  · rw [if_neg hr0]
    cases compare (2 * r) (2 ^ j) <;> simp [ExtendedMantissa.ofMantissaAndAccuracy, hr0]

/-- Shifting an exact mantissa right by `j` bits gives the quotient by `2^j`,
with the residual bits of the remainder. -/
theorem exact_shiftRight_eq_frac (N j : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy N .exact) >>> j =
      ExtendedMantissa.ofMantissaAndAccuracy (N / 2 ^ j) (accuracyOfFraction (N % 2 ^ j) (2 ^ j)) := by
  induction j with
  | zero => rw [Nat.pow_zero, Nat.mod_one, Nat.div_one]; rfl
  | succ j ih =>
    have hstep : (ExtendedMantissa.ofMantissaAndAccuracy N .exact) >>> (j + 1) =
        ExtendedMantissa.shiftRightOne ((ExtendedMantissa.ofMantissaAndAccuracy N .exact) >>> j) :=
      rfl
    rw [hstep, ih]
    obtain ⟨hmant, hbits⟩ := ofMA_frac_bits (N / 2 ^ j) (N % 2 ^ j) j
    rw [Nat.mod_pow_succ, ofMA_frac_step _ _ _ _ (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (Nat.two_pow_pos j))]
    simp only [ExtendedMantissa.shiftRightOne, hmant, hbits]
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]

theorem log2_div_pow (N j : Nat) (h : 2 ^ j ≤ N) : (N / 2 ^ j).log2 + j = N.log2 := by
  have hp : 0 < 2 ^ j := Nat.two_pow_pos j
  have hq : 0 < N / 2 ^ j := Nat.div_pos h hp
  have hN : N ≠ 0 := by omega
  have h1 := Nat.log2_self_le (Nat.ne_of_gt hq)
  have h2 := @Nat.lt_log2_self (N / 2 ^ j)
  have hdm := Nat.div_add_mod N (2 ^ j)
  have hml := Nat.mod_lt N hp
  apply Nat.le_antisymm
  · rw [Nat.le_log2 hN, Nat.pow_add]
    have := Nat.mul_le_mul_right (2 ^ j) h1
    rw [Nat.mul_comm (2 ^ j) (N / 2 ^ j)] at hdm
    omega
  · apply Nat.lt_succ_iff.mp
    rw [Nat.log2_lt hN, Nat.succ_eq_add_one, Nat.add_right_comm, Nat.pow_add]
    have : (N / 2 ^ j + 1) * 2 ^ j ≤ 2 ^ ((N / 2 ^ j).log2 + 1) * 2 ^ j :=
      Nat.mul_le_mul_right _ h2
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ j) (N / 2 ^ j)] at *
    omega

/-- Rounding the quotient by `2^j` together with the accuracy of the
remainder is the same as rounding the exact value, provided the exact value
needs to be shifted right by at least `j` bits. -/
theorem roundWithAccuracy_frac (spec : Format) (S : Sign) (N j : Nat) (E : Int)
    (h : E + j ≤ spec.targetExponent (totalExponent N E)) :
    roundWithAccuracy spec S (N / 2 ^ j) (E + j) (accuracyOfFraction (N % 2 ^ j) (2 ^ j)) =
      roundWithAccuracy spec S N E .exact := by
  have hmb : 2 ≤ spec.mantissaBits := by
    have := spec.hm; simp only [Format.mantissaBits]; omega
  have htgt : spec.targetExponent (totalExponent (N / 2 ^ j) (E + j)) =
      spec.targetExponent (totalExponent N E) := by
    by_cases hN : 2 ^ j ≤ N
    · have := log2_div_pow N j hN
      simp only [totalExponent]
      congr 1; omega
    · rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      have hq : N / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
      have hl : N.log2 < j := by
        by_cases hN0 : N = 0
        · subst hN0; rw [Nat.log2_zero]; exact hj
        · exact (Nat.log2_lt hN0).2 (by omega)
      simp only [Format.targetExponent, totalExponent, hq] at h ⊢
      simp only [Nat.log2_zero]
      omega
  have hfirst : shiftToTargetExponent spec (N / 2 ^ j) (E + j) (accuracyOfFraction (N % 2 ^ j) (2 ^ j)) =
      shiftToTargetExponent spec N E .exact := by
    simp only [shiftToTargetExponent, shiftToExponent, htgt]
    have h1 : (spec.targetExponent (totalExponent N E) - E).toNat =
        (spec.targetExponent (totalExponent N E) - (E + j)).toNat + j := by omega
    rw [h1, shiftRight_add_em, exact_shiftRight_eq_frac]
    congr 1; omega
  unfold roundWithAccuracy
  rw [hfirst]

/-- `divCore` by `2^w`, followed by rounding, is the rounding of the exact
quotient. -/
theorem div_pow2_finite (spec : Format) (S : Sign) (m : Nat) (e Ey : Int) (hm : 0 < m) :
    roundWithAccuracy spec S (divCore spec m e (2 ^ spec.mantissaBitsWithoutImplicit) Ey).1
      (divCore spec m e (2 ^ spec.mantissaBitsWithoutImplicit) Ey).2.1
      (divCore spec m e (2 ^ spec.mantissaBitsWithoutImplicit) Ey).2.2 =
    roundWithAccuracy spec S (m * 2 ^ spec.mantissaBitsWithoutImplicit)
      (e + (-Ey - 2 * (spec.mantissaBitsWithoutImplicit : Int))) .exact := by
  generalize hw : spec.mantissaBitsWithoutImplicit = w
  have hmb : spec.mantissaBits = w + 1 := by simp only [Format.mantissaBits]; omega
  have hw1 : 1 ≤ w := by have := spec.hm; omega
  simp only [divCore]
  generalize htq : min (e - Ey) (spec.targetExponent (totalExponent m e -
    totalExponent (2 ^ w) Ey)) = tq
  generalize hsh : (e - Ey - tq).toNat = sh
  have hlogw : (2 ^ w).log2 = w := Nat.log2_two_pow
  have hNpos : 0 < m <<< sh := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.two_pow_pos _)
  have htotN : totalExponent (m <<< sh) (tq - w) = m.log2 + 1 + e - Ey - w := by
    simp only [totalExponent, log2_shiftLeft m sh hm]; omega
  have hcond : tq ≤ spec.targetExponent (totalExponent (m <<< sh) (tq - w)) := by
    rw [htotN, ← htq]
    simp only [Format.targetExponent, totalExponent, hlogw, hmb]
    omega
  have hfr := roundWithAccuracy_frac spec S (m <<< sh) w (tq - w) (by omega)
  rw [show tq - (w : Int) + w = tq by omega] at hfr
  rw [hfr]
  by_cases hsw : w ≤ sh
  · have hN : m <<< sh = (m * 2 ^ w) <<< (sh - w) := by
      simp only [Nat.shiftLeft_eq]
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    have he : tq - (w : Int) = (e + (-Ey - 2 * (w : Int))) - ((sh - w : Nat) : Int) := by omega
    rw [hN, he]
    apply roundWithAccuracy_shift spec S (m * 2 ^ w) (sh - w) _ (Nat.mul_pos hm (Nat.two_pow_pos _))
    have : totalExponent (m * 2 ^ w) (e + (-Ey - 2 * (w : Int))) = m.log2 + 1 + e - Ey - w := by
      rw [← Nat.shiftLeft_eq]; simp only [totalExponent, log2_shiftLeft m w hm]; omega
    rw [this]
    simp only [Format.targetExponent, hmb]
    omega
  · have hM : m * 2 ^ w = (m <<< sh) <<< (w - sh) := by
      simp only [Nat.shiftLeft_eq]
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    have he : e + (-Ey - 2 * (w : Int)) = (tq - w) - ((w - sh : Nat) : Int) := by omega
    rw [hM, he]
    symm
    apply roundWithAccuracy_shift spec S (m <<< sh) (w - sh) _ hNpos
    omega

theorem sign_div_eq_mul (s t : Sign) : s / t = s * t := by cases s <;> cases t <;> rfl

/-- Dividing by `±2^k` (in canonical normal form) is multiplying by its
inverse `±2^-k`. -/
theorem div_eq_mul_inverse (spec : Format) (x : UnpackedFloat) (sy : Sign) (Ey : Int) (h1 h2) :
    div spec x (.finite sy (2 ^ spec.mantissaBitsWithoutImplicit) Ey h1) =
      mul spec x (.finite sy (2 ^ spec.mantissaBitsWithoutImplicit)
        (-Ey - 2 * (spec.mantissaBitsWithoutImplicit : Int)) h2) := by
  cases x with
  | notANumber => rfl
  | infinity s => simp [div, mul, sign_div_eq_mul]
  | zero s => simp [div, mul, sign_div_eq_mul]
  | finite s m e hm =>
    simp only [div, mul, sign_div_eq_mul]
    rw [← div_pow2_finite spec (s * sy) m e Ey hm]

end UnpackedFloat
end FloatModel

namespace Floats
namespace Gen

open FloatModel FloatModel.UnpackedFloat

variable {spec : Format}

theorem packOr_of_ne_nan (a b : BitVec spec.numBits) (r : UnpackedFloat)
    (h : r ≠ .notANumber) : packOr spec a r = packOr spec b r := by
  cases r <;> simp_all [packOr]

theorem add_self_ne_nan (x : UnpackedFloat) (hx : x ≠ .notANumber) :
    UnpackedFloat.add spec x x ≠ .notANumber := by
  cases x with
  | notANumber => exact absurd rfl hx
  | infinity s => simp [UnpackedFloat.add]
  | zero s => simp [UnpackedFloat.add]
  | finite s m e hm =>
    simp only [UnpackedFloat.add, Int.min_self, decreaseExponent, Int.sub_self, Int.toNat_zero,
      Nat.shiftLeft_zero]
    have happ : s.apply (m : Int) + s.apply (m : Int) = s.apply ((2 * m : Nat) : Int) := by
      cases s <;> simp [Sign.apply] <;> omega
    rw [happ, normalize_apply _ _ _ _ _ (by omega)]
    exact round_ne_nan _ _ _ _

/-- Generic `mul2_add`, for any NaN configuration whose `choose_nan` is
idempotent on a repeated NaN. -/
theorem mul2_add (nc : NanConfig spec) (hidem : ∀ n, nc.chooseNan [n, n] = nc.chooseNan [n])
    (x t : BitVec spec.numBits) (h2)
    (ht : unpack spec t = .finite .positive (2 <<< (spec.mantissaBits - 2))
      (-((spec.mantissaBits - 2 : Nat) : Int)) h2) :
    mul nc x t = add nc x x := by
  unfold mul add
  rw [ht, mul_two_eq_add]
  by_cases hx : isNan spec x = true
  · have htn : isNan spec t = false := by simp [isNan, ht, UnpackedFloat.isNaN]
    have : binopNan nc x t = binopNan nc x x := by
      simp [binopNan, consPl, hx, htn, hidem]
    rw [this]
  · apply packOr_of_ne_nan
    apply add_self_ne_nan
    intro h; apply hx; simp [isNan, h, UnpackedFloat.isNaN]

end Gen

namespace Float

/-- `Float.mul2_add` -/
theorem mul2_add (f : Float) :
    mul f (ofInt (Integers.Int.repr 2)) = add f f :=
  congrArg Float.mk (Gen.mul2_add nanConfig Archi.choose_nan_64_idem f.bits _ (by decide) rfl)

end Float

namespace Float32

/-- `Float32.mul2_add` -/
theorem mul2_add (f : Float32) :
    mul f (ofInt (Integers.Int.repr 2)) = add f f :=
  congrArg Float32.mk (Gen.mul2_add nanConfig Archi.choose_nan_32_idem f.bits _ (by decide) rfl)

end Float32

namespace Float
/-- `Float.exact_inverse` (`Bexact_inverse 53 1024`), on the binary64 bit pattern. -/
def exactInverse (f : Float) : Option Float :=
  let n := f.bits.toNat
  let frac := n % 2 ^ 52
  let e := (n / 2 ^ 52) % 2 ^ 11
  let s := n / 2 ^ 63
  if frac = 0 ∧ 1 ≤ e ∧ e < 2046 then
    some ⟨BitVec.ofNat 64 (s * 2 ^ 63 + (2046 - e) * 2 ^ 52)⟩
  else none
end Float

namespace Float32
/-- `Float32.exact_inverse` (`Bexact_inverse 24 128`), on the binary32 bit pattern. -/
def exactInverse (f : Float32) : Option Float32 :=
  let n := f.bits.toNat
  let frac := n % 2 ^ 23
  let e := (n / 2 ^ 23) % 2 ^ 8
  let s := n / 2 ^ 31
  if frac = 0 ∧ 1 ≤ e ∧ e < 254 then
    some ⟨BitVec.ofNat 32 (s * 2 ^ 31 + (254 - e) * 2 ^ 23)⟩
  else none
end Float32

namespace Gen

open FloatModel FloatModel.UnpackedFloat

variable {spec : Format}

/-- A normal float whose fraction field is zero unpacks to `±2^w · 2^E`. -/
theorem unpack_pow2 (b : BitVec spec.numBits) (hE0 : (unpackExponent b).toNat ≠ 0)
    (hE1 : (unpackExponent b).toNat + 1 ≠ 2 ^ spec.exponentBits)
    (hM : (unpackMantissa b).toNat = 0) :
    unpack spec b = .finite (Sign.ofBitVec (unpackSign b)) (2 ^ spec.mantissaBitsWithoutImplicit)
      ((unpackExponent b).toNat - (spec.exponentBias + spec.mantissaBitsWithoutImplicit : Int))
      (Nat.two_pow_pos _) := by
  have hpos : 0 < 2 ^ spec.exponentBits := Nat.two_pow_pos _
  have hE1' : unpackExponent b ≠ -1#_ := by
    intro h; apply hE1
    rw [h, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]; omega
  have hE0' : unpackExponent b ≠ 0#_ := by
    intro h; apply hE0; rw [h]; rfl
  have hM' : unpackMantissa b = 0#_ := BitVec.eq_of_toNat_eq (by simp [hM])
  unfold unpack
  simp only [hE1', hE0', if_false, hM']
  congr 1
  simp [BitVec.toNat_append, Nat.shiftLeft_eq]

/-- Generic `div_mul_inverse`. -/
theorem div_mul_inverse (nc : NanConfig spec) (x y z : BitVec spec.numBits) (sy : Sign)
    (Ey Ez : Int) (h1 h2)
    (hy : unpack spec y = .finite sy (2 ^ spec.mantissaBitsWithoutImplicit) Ey h1)
    (hz : unpack spec z = .finite sy (2 ^ spec.mantissaBitsWithoutImplicit) Ez h2)
    (hE : Ez = -Ey - 2 * (spec.mantissaBitsWithoutImplicit : Int)) :
    div nc x y = mul nc x z := by
  subst hE
  have hb : binopNan nc x y = binopNan nc x z := by
    simp [binopNan, consPl, isNan, hy, hz, UnpackedFloat.isNaN]
  unfold div mul
  rw [hy, hz, div_eq_mul_inverse, hb]

end Gen

namespace Float

open FloatModel FloatModel.UnpackedFloat

/-- A binary64 pattern `s · 2^63 + E · 2^52` with a normal exponent `E`
unpacks to `±2^52 · 2^(E - 1075)`. -/
theorem unpack_pow2_bits (b : BitVec 64) (s E : Nat) (hbn : b.toNat = s * 2 ^ 63 + E * 2 ^ 52)
    (hE1 : 1 ≤ E) (hE2 : E < 2047) :
    UnpackedFloat.unpack Format.binary64 b =
      .finite (Sign.ofBitVec (unpackSign (spec := Format.binary64) b)) (2 ^ 52)
      ((E : Int) - 1075) (Nat.two_pow_pos _) ∧
    (unpackSign (spec := Format.binary64) b).toNat = s := by
  have hE : (unpackExponent (spec := Format.binary64) b).toNat = E := by
    show (b.toNat >>> 52) % 2 ^ 11 = E
    rw [Nat.shiftRight_eq_div_pow, hbn]; omega
  have hM : (unpackMantissa (spec := Format.binary64) b).toNat = 0 := by
    show (b.toNat >>> 0) % 2 ^ 52 = 0
    rw [Nat.shiftRight_zero, hbn]; omega
  refine ⟨?_, ?_⟩
  · rw [Gen.unpack_pow2 (spec := Format.binary64) b (by rw [hE]; omega)
      (by rw [hE]; simp; omega) hM, hE]
    rfl
  · show (b.toNat >>> 63) % 2 ^ 1 = s
    rw [Nat.shiftRight_eq_div_pow, hbn]; omega

/-- `Float.div_mul_inverse` -/
theorem div_mul_inverse (x y z : Float) (h : exactInverse y = some z) : div x y = mul x z := by
  unfold exactInverse at h
  dsimp only at h
  split at h
  · rename_i hc
    obtain ⟨hfrac, he1, he2⟩ := hc
    cases h
    have hn := y.bits.isLt
    obtain ⟨hy, hsy⟩ := unpack_pow2_bits y.bits (y.bits.toNat / 2 ^ 63)
      (y.bits.toNat / 2 ^ 52 % 2 ^ 11) (by omega) he1 (by omega)
    obtain ⟨hz, hsz⟩ := unpack_pow2_bits
      (BitVec.ofNat 64 (y.bits.toNat / 2 ^ 63 * 2 ^ 63 + (2046 - y.bits.toNat / 2 ^ 52 % 2 ^ 11) * 2 ^ 52))
      (y.bits.toNat / 2 ^ 63) (2046 - y.bits.toNat / 2 ^ 52 % 2 ^ 11)
      (by rw [BitVec.toNat_ofNat]; omega) (by omega) (by omega)
    have hs : unpackSign (spec := Format.binary64) (BitVec.ofNat 64 (y.bits.toNat / 2 ^ 63 * 2 ^ 63 +
        (2046 - y.bits.toNat / 2 ^ 52 % 2 ^ 11) * 2 ^ 52)) = unpackSign (spec := Format.binary64) y.bits :=
      BitVec.eq_of_toNat_eq (by rw [hsy, hsz])
    rw [hs] at hz
    exact congrArg Float.mk (Gen.div_mul_inverse (spec := Format.binary64) nanConfig x.bits y.bits
      _ _ _ _ _ _ hy hz (by simp; omega))
  · cases h

end Float

namespace Float32

open FloatModel FloatModel.UnpackedFloat

/-- A binary32 pattern `s · 2^31 + E · 2^23` with a normal exponent `E`
unpacks to `±2^23 · 2^(E - 150)`. -/
theorem unpack_pow2_bits (b : BitVec 32) (s E : Nat) (hbn : b.toNat = s * 2 ^ 31 + E * 2 ^ 23)
    (hE1 : 1 ≤ E) (hE2 : E < 255) :
    UnpackedFloat.unpack Format.binary32 b =
      .finite (Sign.ofBitVec (unpackSign (spec := Format.binary32) b)) (2 ^ 23)
      ((E : Int) - 150) (Nat.two_pow_pos _) ∧
    (unpackSign (spec := Format.binary32) b).toNat = s := by
  have hE : (unpackExponent (spec := Format.binary32) b).toNat = E := by
    show (b.toNat >>> 23) % 2 ^ 8 = E
    rw [Nat.shiftRight_eq_div_pow, hbn]; omega
  have hM : (unpackMantissa (spec := Format.binary32) b).toNat = 0 := by
    show (b.toNat >>> 0) % 2 ^ 23 = 0
    rw [Nat.shiftRight_zero, hbn]; omega
  refine ⟨?_, ?_⟩
  · rw [Gen.unpack_pow2 (spec := Format.binary32) b (by rw [hE]; omega)
      (by rw [hE]; simp; omega) hM, hE]
    rfl
  · show (b.toNat >>> 31) % 2 ^ 1 = s
    rw [Nat.shiftRight_eq_div_pow, hbn]; omega

/-- `Float32.div_mul_inverse` -/
theorem div_mul_inverse (x y z : Float32) (h : exactInverse y = some z) : div x y = mul x z := by
  unfold exactInverse at h
  dsimp only at h
  split at h
  · rename_i hc
    obtain ⟨hfrac, he1, he2⟩ := hc
    cases h
    have hn := y.bits.isLt
    obtain ⟨hy, hsy⟩ := unpack_pow2_bits y.bits (y.bits.toNat / 2 ^ 31)
      (y.bits.toNat / 2 ^ 23 % 2 ^ 8) (by omega) he1 (by omega)
    obtain ⟨hz, hsz⟩ := unpack_pow2_bits
      (BitVec.ofNat 32 (y.bits.toNat / 2 ^ 31 * 2 ^ 31 + (254 - y.bits.toNat / 2 ^ 23 % 2 ^ 8) * 2 ^ 23))
      (y.bits.toNat / 2 ^ 31) (254 - y.bits.toNat / 2 ^ 23 % 2 ^ 8)
      (by rw [BitVec.toNat_ofNat]; omega) (by omega) (by omega)
    have hs : unpackSign (spec := Format.binary32) (BitVec.ofNat 32 (y.bits.toNat / 2 ^ 31 * 2 ^ 31 +
        (254 - y.bits.toNat / 2 ^ 23 % 2 ^ 8) * 2 ^ 23)) = unpackSign (spec := Format.binary32) y.bits :=
      BitVec.eq_of_toNat_eq (by rw [hsy, hsz])
    rw [hs] at hz
    exact congrArg Float32.mk (Gen.div_mul_inverse (spec := Format.binary32) nanConfig x.bits y.bits
      _ _ _ _ _ _ hy hz (by simp; omega))
  · cases h

end Float32

end Floats
end CC
