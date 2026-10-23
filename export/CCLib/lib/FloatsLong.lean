/-
  `Float.of_longu_of_long_2` of `lib/Floats.v`: an unsigned 64-bit integer
  `x ≥ 2^63` converts to binary64 like `2 · of_long ((x >> 1) | (x & 1))`.

  As in Rocq, the proof combines the round-to-odd lemma (`BofZ_round_odd`,
  here `Gen.ofZ_sticky`) with the exact multiplication of a rounded integer by
  `2` (`BofZ_mult_2p`, here `Float.mul_ofZ_two`).
-/
import CCLib.lib.FloatsDecomp
import Std.Tactic.BVDecide

namespace CC
namespace FloatModel.UnpackedFloat

theorem roundedMantissa_bounds (q : Nat) (a : Accuracy) :
    q ≤ (ExtendedMantissa.ofMantissaAndAccuracy q a).roundedMantissa ∧
      (ExtendedMantissa.ofMantissaAndAccuracy q a).roundedMantissa ≤ q + 1 := by
  cases a with
  | exact => simp [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
      ExtendedMantissa.accuracy, Accuracy.roundToNearestEven]
  | inexact o =>
    cases o <;> simp [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
      ExtendedMantissa.accuracy, Accuracy.roundToNearestEven] <;> omega

/-- Rounding a mantissa that already has exactly `mantissaBits` bits, at an
exponent that is not subnormal: the result does not depend on the exponent
except for a shift. -/
theorem roundWithAccuracy_canon (spec : Format) (s : Sign) (q : Nat) (a : Accuracy)
    (hq : q.log2 + 1 = spec.mantissaBits) :
    ∃ (M : Nat) (h : 0 < M) (d : Nat), d ≤ 1 ∧ M.log2 + 1 = spec.mantissaBits ∧
      ∀ t : Int, spec.minExponent ≤ t →
        roundWithAccuracy spec s q t a = .finite s M (t + d) h := by
  have hmb : 2 ≤ spec.mantissaBits := by
    have := spec.hm; simp only [Format.mantissaBits]; omega
  have hq0 : q ≠ 0 := by intro h; subst h; simp at hq; omega
  have hqlo : 2 ^ (spec.mantissaBits - 1) ≤ q := by
    have := Nat.log2_self_le hq0
    rw [show spec.mantissaBits - 1 = q.log2 by omega]; exact this
  have hqhi : q < 2 ^ spec.mantissaBits := by
    have := @Nat.lt_log2_self q; rw [show spec.mantissaBits = q.log2 + 1 by omega]; exact this
  obtain ⟨hr1, hr2⟩ := roundedMantissa_bounds q a
  generalize hr : (ExtendedMantissa.ofMantissaAndAccuracy q a).roundedMantissa = r at hr1 hr2
  have htq : ∀ t : Int, spec.minExponent ≤ t →
      spec.targetExponent (totalExponent q t) = t := by
    intro t ht; simp only [Format.targetExponent, totalExponent]; omega
  have hpow : 2 ^ spec.mantissaBits = 2 * 2 ^ (spec.mantissaBits - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  by_cases hrlt : r < 2 ^ spec.mantissaBits
  · have hr0 : 0 < r := by omega
    have hlr : r.log2 = spec.mantissaBits - 1 := by
      apply Nat.le_antisymm
      · have := (Nat.log2_lt (Nat.ne_of_gt hr0)).2 hrlt; omega
      · exact (Nat.le_log2 (Nat.ne_of_gt hr0)).2 (by omega)
    refine ⟨r, hr0, 0, by omega, by omega, fun t ht => ?_⟩
    have htr : spec.targetExponent (totalExponent r t) = t := by
      simp only [Format.targetExponent, totalExponent]; omega
    unfold roundWithAccuracy
    simp only [shiftToTargetExponent, shiftToExponent, htq t ht, Int.sub_self, Int.toNat_zero,
      shiftRight_zero_em, Int.natCast_zero, Int.add_zero, hr, htr]
    rw [dif_neg (show (ExtendedMantissa.ofMantissaAndAccuracy r .exact).mantissa ≠ 0 from
      Nat.ne_of_gt hr0)]
    rfl
  · have hreq : r = 2 ^ spec.mantissaBits := by omega
    have hM0 : 0 < 2 ^ (spec.mantissaBits - 1) := Nat.two_pow_pos _
    refine ⟨2 ^ (spec.mantissaBits - 1), hM0, 1, by omega,
      by rw [Nat.log2_two_pow]; omega, fun t ht => ?_⟩
    have htr : spec.targetExponent (totalExponent r t) = t + 1 := by
      simp only [Format.targetExponent, totalExponent, hreq, Nat.log2_two_pow]; omega
    unfold roundWithAccuracy
    simp only [shiftToTargetExponent, shiftToExponent, htq t ht, Int.sub_self, Int.toNat_zero,
      shiftRight_zero_em, Int.natCast_zero, Int.add_zero, hr, htr]
    have h1 : (t + 1 - t).toNat = 1 := by omega
    have hm : (ExtendedMantissa.ofMantissaAndAccuracy r .exact >>> (1 : Nat)).mantissa =
        2 ^ (spec.mantissaBits - 1) := by
      show r / 2 = _
      omega
    simp only [h1, hm]
    rw [dif_neg (Nat.ne_of_gt hM0)]

/-- Rounding a positive integer mantissa `N` of at least `mantissaBits` bits at
a nonnegative exponent `e`: the rounded mantissa does not depend on `e`, and
the exponent is `e + j + d` with `j = log2 N + 1 - mantissaBits`, `d ≤ 1`. -/
theorem round_large (spec : Format) (s : Sign) (N : Nat) (hN : spec.mantissaBits ≤ N.log2 + 1) :
    ∃ (M : Nat) (h : 0 < M) (d : Nat), d ≤ 1 ∧ M.log2 + 1 = spec.mantissaBits ∧
      ∀ e : Int, 0 ≤ e →
        round spec s N e = .finite s M (e + (N.log2 + 1 - spec.mantissaBits : Nat) + d) h := by
  generalize hj : N.log2 + 1 - spec.mantissaBits = j
  have hmb : 2 ≤ spec.mantissaBits := by
    have := spec.hm; simp only [Format.mantissaBits]; omega
  have hN0 : N ≠ 0 := by intro h; subst h; simp at hN; omega
  have h2j : 2 ^ j ≤ N :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.log2_self_le hN0)
  have hq : (N / 2 ^ j).log2 + 1 = spec.mantissaBits := by
    have := log2_div_pow N j h2j; omega
  obtain ⟨M, hM, d, hd, hlM, hall⟩ :=
    roundWithAccuracy_canon spec s (N / 2 ^ j) (accuracyOfFraction (N % 2 ^ j) (2 ^ j)) hq
  obtain ⟨-, -, hmin⟩ := exponentBits_facts spec
  refine ⟨M, hM, d, hd, hlM, fun e he => ?_⟩
  have ht : spec.targetExponent (totalExponent N e) = e + j := by
    simp only [Format.targetExponent, totalExponent]; omega
  rw [round_eq_roundWithAccuracy _ _ _ _ (by omega),
    ← roundWithAccuracy_frac spec s N j e (by omega)]
  exact hall _ (by omega)

end FloatModel.UnpackedFloat

namespace Floats

open FloatModel FloatModel.UnpackedFloat

namespace Float

theorem unpack_ofZ_two :
    UnpackedFloat.unpack Format.binary64 (Gen.ofZ Format.binary64 2) =
      UnpackedFloat.finite .positive (2 ^ 52) (-51) (Nat.two_pow_pos _) := by
  rw [Gen.unpack_ofZ _ _ (repr_n 2 (by decide)),
    show (2 : Int) = Sign.positive.apply ((2 : Nat) : Int) from rfl,
    normalize_apply _ _ _ _ _ (by decide)]
  have hl : (2 : Nat).log2 = 1 := Nat.log2_two_pow (n := 1)
  obtain ⟨h, hr⟩ := round_normal Format.binary64 .positive 2 0 (by decide)
    (by rw [hl]; decide) (by rw [hl]; decide)
  rw [hr]
  simp only [hl]
  rfl

/-- `BofZ_mult_2p` with `p = 1`, for integers of 53 to 64 bits: multiplying
the rounded integer by `2` is exact. -/
theorem mul_ofZ_two (z : Int) (h1 : 2 ^ 52 ≤ z.natAbs) (h2 : z.natAbs < 2 ^ 64) :
    mul (ofZ z) (ofZ 2) = ofZ (2 * z) := by
  generalize hN : z.natAbs = N at h1 h2
  obtain ⟨s, hz⟩ : ∃ s : Sign, z = s.apply (N : Int) := by
    rcases Int.natAbs_eq z with h | h
    · exact ⟨.positive, by simp [Sign.apply]; omega⟩
    · exact ⟨.negative, by simp [Sign.apply]; omega⟩
  have hN0 : 0 < N := by omega
  have hlog1 : 52 ≤ N.log2 := (Nat.le_log2 (by omega)).2 h1
  have hlog2 : N.log2 < 64 := (Nat.log2_lt (by omega)).2 h2
  obtain ⟨M, hM, d, hd, hlM, hall⟩ := round_large Format.binary64 s N
    (by simp only [Format.mantissaBits]; omega)
  have hlM' : M.log2 = 52 := by simp only [Format.mantissaBits] at hlM; omega
  have e0 := hall 0 (by decide)
  have e1 := hall 1 (by decide)
  have h2z : (2 : Int) * s.apply (N : Int) = s.apply ((N <<< 1 : Nat) : Int) := by
    cases s <;> simp [Sign.apply, Nat.shiftLeft_eq] <;> omega
  have hN1 : 0 < N <<< 1 := by rw [Nat.shiftLeft_eq]; omega
  have hsh : round Format.binary64 s (N <<< 1) 0 = round Format.binary64 s N 1 := by
    have := round_shift Format.binary64 s N 1 1 hN0
    simpa using this
  generalize hE : (0 : Int) + ((N.log2 + 1 - Format.binary64.mantissaBits : Nat) : Int) + d = E
    at e0
  have hE1 : (1 : Int) + ((N.log2 + 1 - Format.binary64.mantissaBits : Nat) : Int) + d = E + 1 := by
    omega
  rw [hE1] at e1
  have hj : (N.log2 + 1 - Format.binary64.mantissaBits : Nat) ≤ 11 := by
    simp only [Format.mantissaBits]; omega
  unfold mul ofZ
  apply congrArg Float.mk
  unfold Gen.mul
  rw [Floats.Float.unpack_ofZ_two]
  unfold Gen.ofZ
  rw [hz, h2z, normalize_apply _ _ _ _ _ hN0, normalize_apply _ _ _ _ _ hN1, hsh, e0, e1,
    unpack_pack_normal _ _ _ _ _ hlM
      (by simp only [Format.exponentBias]; omega)
      (by simp only [Format.exponentBias]; omega)]
  show Gen.packOr _ _ (roundWithAccuracy _ (s * .positive) (M * 2 ^ 52) (E + -51) .exact) = _
  rw [sign_mul_positive, ← round_eq_roundWithAccuracy]
  · have hr := round_shift Format.binary64 s M 52 (E + 1) hM
    rw [show M * 2 ^ 52 = M <<< 52 by rw [Nat.shiftLeft_eq],
      show E + -51 = E + 1 - ((52 : Nat) : Int) by omega, hr, packOr_round,
      round_exact _ _ _ _ hM]
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, hlM']
    have : Format.binary64.minExponent = -1074 := by decide
    omega
  · have : Format.binary64.minExponent = -1074 := by decide
    rw [← Nat.shiftLeft_eq]
    simp only [Format.targetExponent, totalExponent, log2_shiftLeft _ _ hM, hlM', Format.mantissaBits]
    omega

theorem halve_odd_bits (x : BitVec 64) :
    ((x >>> 1) ||| (x &&& 1#64)) >>> 1 = x >>> 2 ∧
      (((x >>> 1) ||| (x &&& 1#64)) &&& 1#64 = 0#64 ↔ x &&& 3#64 = 0#64) ∧
      ((x >>> 1) ||| (x &&& 1#64)) >>> 63 = 0#64 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-- `Float.of_longu_of_long_2` -/
theorem of_longu_of_long_2 (x : Integers.Int64)
    (h : Integers.Int64.ltu x (Integers.Int64.repr Integers.Int64.half_modulus) = false) :
    ofLongu x = mul (ofLong (Integers.Int64.or (Integers.Int64.shru x Integers.Int64.one)
                                              (Integers.Int64.and x Integers.Int64.one)))
                    (ofInt (Integers.Int.repr 2)) := by
  have hrepr : Integers.Int64.repr Integers.Int64.half_modulus = 9223372036854775808#64 := by
    decide
  rw [hrepr] at h
  have hx : 2 ^ 63 ≤ x.toNat := by
    have : ¬ x.toNat < 9223372036854775808 := by
      intro hlt
      have : x.ult 9223372036854775808#64 = true := by
        simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
      exact absurd this (by simpa [Integers.Int64.ltu, Integers.MI.ltu] using h)
    omega
  have hm : Integers.Int64.or (Integers.Int64.shru x Integers.Int64.one)
      (Integers.Int64.and x Integers.Int64.one) = (x >>> 1) ||| (x &&& 1#64) := rfl
  rw [hm]
  obtain ⟨F1, F2, F3⟩ := halve_odd_bits x
  generalize (x >>> 1) ||| (x &&& 1#64) = m at F1 F2 F3 ⊢
  have hxlt : x.toNat < 2 ^ 64 := x.isLt
  have hmlt : m.toNat < 2 ^ 64 := m.isLt
  have e1 : m.toNat / 2 = x.toNat / 4 := by
    have := congrArg BitVec.toNat F1
    simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this
  have e3 : m.toNat < 2 ^ 63 := by
    have := congrArg BitVec.toNat F3
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    omega
  have e2 : m.toNat % 2 = 0 ↔ x.toNat % 4 = 0 := by
    have hand : ∀ (y : BitVec 64) (k : Nat), k < 64 →
        (y &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = y.toNat % 2 ^ k := by
      intro y k hk
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
        have := Nat.pow_lt_pow_right (show 1 < 2 by decide) hk; omega),
        Nat.and_two_pow_sub_one_eq_mod]
    have h1 : (m &&& 1#64).toNat = m.toNat % 2 := hand m 1 (by decide)
    have h3 : (x &&& 3#64).toNat = x.toNat % 4 := hand x 2 (by decide)
    constructor
    · intro hm0
      have := congrArg BitVec.toNat (F2.1 (BitVec.eq_of_toNat_eq (by rw [h1]; simpa using hm0)))
      rw [h3] at this; simpa using this
    · intro hx0
      have := congrArg BitVec.toNat (F2.2 (BitVec.eq_of_toNat_eq (by rw [h3]; simpa using hx0)))
      rw [h1] at this; simpa using this
  have hsm : Integers.Int64.signed m = (m.toNat : Int) := by
    show m.toInt = _
    rw [BitVec.toInt_eq_toNat_cond, if_pos (by omega)]
  have h2 : ofInt (Integers.Int.repr 2) = ofZ 2 := rfl
  unfold ofLong
  rw [hsm, h2, mul_ofZ_two _ (by omega) (by omega)]
  unfold ofLongu ofZ
  congr 1
  show Gen.ofZ _ (Sign.positive.apply ((x.toNat : Nat) : Int)) =
    Gen.ofZ _ (Sign.positive.apply (((2 * m.toNat : Nat)) : Int))
  have eA : x.toNat = (x.toNat / 4) * 2 ^ 2 + x.toNat % 4 := by omega
  have eB : 2 * m.toNat = (x.toNat / 4) * 2 ^ 2 + 2 * (m.toNat % 2) := by omega
  rw [eA, eB]
  exact Gen.ofZ_sticky _ _ _ _ _ _ (by omega) (by omega) (by omega)
    (by simp only [Format.mantissaBits]; omega)

end Float
end Floats
end CC
