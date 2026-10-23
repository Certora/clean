/-
  Theorems of `lib/Floats.v` relating single- and double-precision
  conversions (`Float32.of_int_double`, `of_intu_double`, `to_int_double`,
  `to_intu_double`, `to_long_double`, `to_longu_double`).

  In Rocq these follow from Flocq's `Bconv_BofZ` and `ZofB_range_Bconv`.  Here
  they are proved directly on the exact IEEE model of `CCLib.lib.FloatModel`:
  * `round_shift`: rounding only depends on the value `m · 2^e`, not on the
    chosen representation `(m, e)`;
  * `round_normal`: rounding a value whose mantissa fits the format and whose
    exponent is in range is exact;
  * `unpack_pack_normal`: packing then unpacking a normal float is the identity.
-/
import CCLib.lib.FloatsLemmas

namespace CC
namespace FloatModel
namespace UnpackedFloat

/-! ## Representation independence of rounding -/

theorem repeat_add {α : Type} (f : α → α) (j k : Nat) (a : α) :
    Nat.repeat f (j + k) a = Nat.repeat f j (Nat.repeat f k a) := by
  induction j with
  | zero => simp [Nat.repeat]
  | succ j ih => rw [Nat.add_right_comm]; simp [Nat.repeat, ih]

theorem shiftRight_zero_em (em : ExtendedMantissa) : em >>> (0 : Nat) = em := rfl

theorem shiftRight_add_em (em : ExtendedMantissa) (j k : Nat) :
    em >>> (j + k) = (em >>> k) >>> j := by
  show Nat.repeat _ (j + k) em = Nat.repeat _ j (Nat.repeat _ k em)
  exact repeat_add _ j k em

/-- Shifting out `k` zero bits leaves the residual bits clear. -/
theorem exact_shiftLeft_shiftRight (m k : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy (m <<< k) .exact) >>> k =
      ExtendedMantissa.ofMantissaAndAccuracy m .exact := by
  induction k generalizing m with
  | zero => simp [Nat.shiftLeft_zero]; rfl
  | succ k ih =>
    rw [shiftRight_add_em]
    have h1 : (ExtendedMantissa.ofMantissaAndAccuracy (m <<< (k + 1)) .exact) >>> (1 : Nat) =
        ExtendedMantissa.ofMantissaAndAccuracy (m <<< k) .exact := by
      show ExtendedMantissa.shiftRightOne _ = _
      simp only [ExtendedMantissa.shiftRightOne, ExtendedMantissa.ofMantissaAndAccuracy,
        Nat.shiftLeft_eq, Nat.pow_succ, ← Nat.mul_assoc]
      congr 1
      · exact Nat.mul_div_cancel _ (by decide)
      · simp only [bne_eq_false_iff_eq]
        exact Nat.mul_mod_left _ _
    rw [h1, ih]

theorem log2_shiftLeft (m k : Nat) (hm : 0 < m) : (m <<< k).log2 = m.log2 + k := by
  have hmk : m <<< k ≠ 0 := by
    rw [Nat.shiftLeft_eq]; exact Nat.ne_of_gt (Nat.mul_pos hm (Nat.two_pow_pos k))
  apply Nat.le_antisymm
  · apply Nat.lt_succ_iff.mp
    rw [Nat.log2_lt hmk, Nat.shiftLeft_eq, Nat.succ_eq_add_one, Nat.add_right_comm,
      Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos k)
  · rw [Nat.le_log2 hmk, Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le (Nat.ne_of_gt hm))

theorem totalExponent_shift (m k : Nat) (e : Int) (hm : 0 < m) :
    totalExponent (m <<< k) (e - k) = totalExponent m e := by
  simp only [totalExponent, log2_shiftLeft m k hm]; omega

theorem roundWithAccuracy_shift (spec : Format) (s : Sign) (m k : Nat) (e : Int) (hm : 0 < m)
    (h : e ≤ spec.targetExponent (totalExponent m e)) :
    roundWithAccuracy spec s (m <<< k) (e - k) .exact = roundWithAccuracy spec s m e .exact := by
  have hfirst : shiftToTargetExponent spec (m <<< k) (e - k) .exact =
      shiftToTargetExponent spec m e .exact := by
    simp only [shiftToTargetExponent, shiftToExponent, totalExponent_shift m k e hm]
    have h1 : (spec.targetExponent (totalExponent m e) - (e - k)).toNat =
        (spec.targetExponent (totalExponent m e) - e).toNat + k := by omega
    rw [h1, shiftRight_add_em, exact_shiftLeft_shiftRight]
    congr 1; omega
  unfold roundWithAccuracy
  rw [hfirst]

theorem round_shift (spec : Format) (s : Sign) (m k : Nat) (e : Int) (hm : 0 < m) :
    round spec s (m <<< k) (e - k) = round spec s m e := by
  unfold round
  rw [totalExponent_shift m k e hm]
  generalize ht : spec.targetExponent (totalExponent m e) = t
  have hte : ∀ (m' : Nat) (e' : Int) (j : Nat), 0 < m' → totalExponent m' e' = totalExponent m e →
      e' ≤ t → roundWithAccuracy spec s (m' <<< j) (e' - j) .exact =
        roundWithAccuracy spec s m' e' .exact := by
    intro m' e' j hm' htot hle
    apply roundWithAccuracy_shift spec s m' j e' hm'
    rw [htot, ht]; exact hle
  simp only [decreaseExponent]
  by_cases hA : t ≤ e - k
  · have h1 : (e - k - t).toNat + k = (e - t).toNat := by omega
    have h2 : e - k - ((e - k - t).toNat : Int) = e - ((e - t).toNat : Int) := by omega
    rw [h2, ← Nat.shiftLeft_add, Nat.add_comm, h1]
  · by_cases hB : t ≤ e
    · obtain ⟨i, hi⟩ : ∃ i, k = (e - t).toNat + i := ⟨k - (e - t).toNat, by omega⟩
      have h0 : (e - k - t).toNat = 0 := by omega
      rw [h0, Nat.shiftLeft_zero, hi, Nat.shiftLeft_add]
      have h3 : e - (((e - t).toNat + i : Nat) : Int) - ((0 : Nat) : Int) =
          (e - ((e - t).toNat : Int)) - (i : Int) := by omega
      rw [h3]
      apply hte
      · rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.two_pow_pos _)
      · exact totalExponent_shift m _ e hm
      · omega
    · have h0 : (e - k - t).toNat = 0 := by omega
      have h0' : (e - t).toNat = 0 := by omega
      rw [h0, h0', Nat.shiftLeft_zero, Nat.shiftLeft_zero]
      simp only [Int.natCast_zero, Int.sub_zero]
      exact hte m e k hm rfl (by omega)

/-- Rounding a float that is already in canonical form is exact. -/
theorem round_exact (spec : Format) (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (h : spec.targetExponent (totalExponent m e) = e) :
    round spec s m e = .finite s m e hm := by
  unfold round
  rw [h]
  simp only [decreaseExponent, Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero, Int.natCast_zero,
    Int.sub_zero]
  unfold roundWithAccuracy
  simp only [shiftToTargetExponent, shiftToExponent, h, Int.sub_self, Int.toNat_zero,
    shiftRight_zero_em, Int.natCast_zero, Int.add_zero]
  have hr : (ExtendedMantissa.ofMantissaAndAccuracy m .exact).roundedMantissa = m := rfl
  simp only [hr, h, Int.sub_self, Int.toNat_zero, shiftRight_zero_em, Int.natCast_zero,
    Int.add_zero]
  have hne : (ExtendedMantissa.ofMantissaAndAccuracy m .exact).mantissa ≠ 0 := Nat.ne_of_gt hm
  rw [dif_neg hne]
  rfl

/-- Rounding a value whose mantissa fits in the format and whose normalized
exponent is in range is exact: the result is the normalized representation. -/
theorem round_normal (spec : Format) (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hlog : m.log2 < spec.mantissaBits)
    (hmin : spec.minExponent ≤ e - (spec.mantissaBits - 1 - m.log2 : Nat)) :
    ∃ h, round spec s m e =
      .finite s (m <<< (spec.mantissaBits - 1 - m.log2)) (e - (spec.mantissaBits - 1 - m.log2 : Nat)) h := by
  have hM : 0 < m <<< (spec.mantissaBits - 1 - m.log2) := by
    rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.two_pow_pos _)
  refine ⟨hM, ?_⟩
  rw [← round_shift spec s m (spec.mantissaBits - 1 - m.log2) e hm]
  apply round_exact
  simp only [Format.targetExponent, totalExponent, log2_shiftLeft m _ hm]
  omega

/-! ## Packing and unpacking normal floats -/

theorem unpack_pack_normal (spec : Format) (s : Sign) (M : Nat) (T : Int) (hM : 0 < M)
    (hlog : M.log2 + 1 = spec.mantissaBits)
    (hlo : 0 < T + spec.exponentBias + spec.mantissaBitsWithoutImplicit)
    (hhi : (T + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 < 2 ^ spec.exponentBits) :
    unpack spec (pack spec (.finite s M T hM)) = .finite s M T hM := by
  have hlog' : M.log2 = spec.mantissaBitsWithoutImplicit := by
    simp only [Format.mantissaBits] at hlog; omega
  have hMlo : 2 ^ spec.mantissaBitsWithoutImplicit ≤ M :=
    hlog' ▸ Nat.log2_self_le (Nat.ne_of_gt hM)
  have hMhi : M < 2 ^ (spec.mantissaBitsWithoutImplicit + 1) := hlog' ▸ Nat.lt_log2_self
  have hEpos : 0 < 2 ^ spec.exponentBits := Nat.two_pow_pos _
  unfold pack
  simp only []
  rw [if_neg (by omega), if_pos hlog]
  generalize hB : (T + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat = B at hhi
  have hBT : (B : Int) = T + spec.exponentBias + spec.mantissaBitsWithoutImplicit := by omega
  unfold unpack
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents, Sign.ofBitVec_toBitVec]
  have hBlt : B < 2 ^ spec.exponentBits := by omega
  have hE1 : BitVec.ofNat spec.exponentBits B ≠ -1#_ := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hBlt] at this
    omega
  have hE0 : BitVec.ofNat spec.exponentBits B ≠ 0#_ := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hBlt] at this
    simp at this; omega
  rw [if_neg hE1, if_neg hE0]
  have hm : (1#1 ++ BitVec.ofNat spec.mantissaBitsWithoutImplicit M).toNat = M := by
    rw [BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [Nat.pow_one, Nat.one_mod, Nat.shiftLeft_eq, Nat.one_mul]
    have hd : M / 2 ^ spec.mantissaBitsWithoutImplicit = 1 := by
      apply Nat.le_antisymm
      · apply Nat.lt_succ_iff.mp
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        rw [Nat.pow_succ] at hMhi; omega
      · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
    have := Nat.div_add_mod M (2 ^ spec.mantissaBitsWithoutImplicit)
    rw [hd] at this; omega
  have he : ((BitVec.ofNat spec.exponentBits B).toNat : Int) -
      (spec.exponentBias + spec.mantissaBitsWithoutImplicit : Int) = T := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hBlt]; omega
  simp only [hm, he]

/-- Bounds on the components of an unpacked finite float. -/
theorem unpack_finite_bounds (spec : Format) (b : BitVec spec.numBits) {s : Sign} {m : Nat} {e : Int}
    {hm : 0 < m} (h : unpack spec b = .finite s m e hm) :
    m < 2 ^ spec.mantissaBits ∧
    1 - (spec.exponentBias + spec.mantissaBitsWithoutImplicit : Int) ≤ e ∧
    e ≤ (2 ^ spec.exponentBits - 2 : Nat) - (spec.exponentBias + spec.mantissaBitsWithoutImplicit : Int) := by
  have h4 : 4 ≤ 2 ^ spec.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) spec.he
    simpa using this
  unfold unpack at h
  simp only [] at h
  split at h
  · split at h <;> cases h
  · rename_i hE1
    split at h
    · rename_i hE0
      split at h
      · cases h
      · obtain ⟨-, rfl, rfl⟩ := UnpackedFloat.finite.inj h
        refine ⟨?_, ?_, ?_⟩
        · have := (unpackMantissa b).isLt
          have : 2 ^ spec.mantissaBitsWithoutImplicit ≤ 2 ^ spec.mantissaBits :=
            Nat.pow_le_pow_right (by decide) (by simp [Format.mantissaBits])
          omega
        · rw [hE0]; simp; omega
        · rw [hE0]; simp; omega
    · rename_i hE0
      obtain ⟨-, rfl, rfl⟩ := UnpackedFloat.finite.inj h
      have hlt := (1#1 ++ unpackMantissa b).isLt
      have hE0' : (unpackExponent b).toNat ≠ 0 := by
        intro h0; apply hE0; exact BitVec.eq_of_toNat_eq (by simp [h0])
      have hE1' : (unpackExponent b).toNat ≠ 2 ^ spec.exponentBits - 1 := by
        intro h0; apply hE1; apply BitVec.eq_of_toNat_eq
        rw [h0, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
      have hElt := (unpackExponent b).isLt
      refine ⟨?_, ?_, ?_⟩
      · simpa [Format.mantissaBits, Nat.add_comm] using hlt
      · omega
      · omega

end UnpackedFloat
end FloatModel

namespace Floats

open FloatModel FloatModel.UnpackedFloat

/-- Truncation of `±m · 2^e` toward zero, as computed by `Gen.toZ`. -/
def truncZ (s : Sign) (m : Nat) (e : Int) : Int :=
  s.apply (if 0 ≤ e then ((m <<< e.toNat : Nat) : Int) else ((m >>> e.natAbs : Nat) : Int))

theorem truncZ_shift (s : Sign) (m k : Nat) (e : Int) :
    truncZ s (m <<< k) (e - k) = truncZ s m e := by
  unfold truncZ
  congr 1
  by_cases h1 : 0 ≤ e - k
  · have h2 : 0 ≤ e := by omega
    rw [if_pos h1, if_pos h2, ← Nat.shiftLeft_add]
    congr 3; omega
  · rw [if_neg h1]
    by_cases h2 : 0 ≤ e
    · rw [if_pos h2]
      obtain ⟨i, hi⟩ : ∃ i, k = e.toNat + i := ⟨k - e.toNat, by omega⟩
      have h3 : (e - (k : Int)).natAbs = i := by omega
      rw [h3, hi, Nat.shiftLeft_add, Nat.shiftLeft_shiftRight]
    · rw [if_neg h2]
      have h3 : (e - (k : Int)).natAbs = k + e.natAbs := by omega
      rw [h3, Nat.shiftRight_add, Nat.shiftLeft_shiftRight]

/-- Widening binary32 to binary64 preserves the truncated integer value. -/
theorem toZ_ofSingle (f : Float32) (z : Int) (h : Gen.toZ Format.binary32 f.bits = some z) :
    Gen.toZ Format.binary64 (Float.ofSingle f).bits = some z := by
  have hdef : (Float.ofSingle f).bits = Gen.packOr Format.binary64 (Float.ofSingleNan f).bits
      (Gen.convU Format.binary64 (unpack Format.binary32 f.bits)) := rfl
  rw [hdef]
  unfold Gen.toZ at h ⊢
  generalize hx : unpack Format.binary32 f.bits = x at h
  cases x with
  | zero sg =>
    simp only [Option.some.injEq] at h; subst h
    simp [Gen.convU, Gen.packOr, pack]
  | finite sg m e hm =>
    obtain ⟨hmb, hlo, hhi⟩ := unpack_finite_bounds _ _ hx
    simp only [Format.mantissaBits, Format.exponentBias] at hmb hlo hhi
    have hlog : m.log2 < 24 := (Nat.log2_lt (Nat.ne_of_gt hm)).2 hmb
    obtain ⟨hM, hr⟩ := round_normal Format.binary64 sg m e hm
      (by simp only [Format.mantissaBits]; omega)
      (by simp only [Format.mantissaBits, Format.minExponent]; omega)
    simp only [Gen.convU, hr, Gen.packOr]
    rw [unpack_pack_normal _ _ _ _ _
      (by rw [log2_shiftLeft _ _ hm]; simp only [Format.mantissaBits]; omega)
      (by simp only [Format.mantissaBits, Format.exponentBias]; omega)
      (by simp only [Format.mantissaBits, Format.exponentBias]; omega)]
    simp only [Option.some.injEq] at h ⊢
    rw [← h]
    exact truncZ_shift sg m _ e
  | infinity sg => simp at h
  | notANumber => simp at h

theorem toZRange_ofSingle (f : Float32) (lo hi z : Int)
    (h : Gen.toZRange Format.binary32 f.bits lo hi = some z) :
    Gen.toZRange Format.binary64 (Float.ofSingle f).bits lo hi = some z := by
  rw [Gen.toZRange_eq_some] at *
  exact ⟨toZ_ofSingle f z h.1, h.2⟩

theorem packOr_round (spec : Format) (nan : BitVec spec.numBits) (s : Sign) (m : Nat) (e : Int) :
    Gen.packOr spec nan (round spec s m e) = pack spec (round spec s m e) := by
  unfold round roundWithAccuracy
  simp only []
  split <;> rfl

theorem normalize_cases (spec : Format) (z : Int) :
    (z < 0 → normalize spec z 0 .positive = round spec .negative (-z).toNat 0) ∧
    (z = 0 → normalize spec z 0 .positive = .zero .positive) ∧
    (0 < z → normalize spec z 0 .positive = round spec .positive z.toNat 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : compare z 0 = .lt := by
      simp [compare, compareOfLessAndEq, h]
    simp [normalize, this]
  · subst h; rfl
  · have : compare z 0 = .gt := by
      simp [compare, compareOfLessAndEq, Int.not_lt.mpr (Int.le_of_lt h), Int.ne_of_gt h]
    simp [normalize, this]

/-- Rounding an integer below `2^53` to binary64, then to binary32, is the
same as rounding it to binary32 directly. -/
theorem round_via_double (nan : BitVec Format.binary32.numBits) (sg : Sign) (n : Nat)
    (hn : 0 < n) (hlt : n < 2 ^ 53) :
    Gen.packOr Format.binary32 nan (Gen.convU Format.binary32
      (unpack Format.binary64 (pack Format.binary64 (round Format.binary64 sg n 0)))) =
    pack Format.binary32 (round Format.binary32 sg n 0) := by
  have hlog : n.log2 < 53 := (Nat.log2_lt (Nat.ne_of_gt hn)).2 hlt
  obtain ⟨hM, hr⟩ := round_normal Format.binary64 sg n 0 hn
    (by simp only [Format.mantissaBits]; omega)
    (by simp only [Format.mantissaBits, Format.minExponent]; omega)
  rw [hr, unpack_pack_normal _ _ _ _ _
      (by rw [log2_shiftLeft _ _ hn]; simp only [Format.mantissaBits]; omega)
      (by simp only [Format.mantissaBits, Format.exponentBias]; omega)
      (by simp only [Format.mantissaBits, Format.exponentBias]; omega)]
  simp only [Gen.convU]
  rw [round_shift _ _ _ _ _ hn, packOr_round]

/-- Rounding an integer of at most 53 bits to binary32 directly, or via
binary64, gives the same result (no double rounding). -/
theorem ofZ_double (z : Int) (hz : -2 ^ 53 < z ∧ z < 2 ^ 53) :
    Float32.ofZ z = Float.toSingle (Float.ofZ z) := by
  obtain ⟨hneg, hzero, hpos⟩ := normalize_cases Format.binary32 z
  obtain ⟨hneg', hzero', hpos'⟩ := normalize_cases Format.binary64 z
  unfold Float32.ofZ Float.ofZ Float.toSingle Float.unpack Gen.ofZ
  congr 1
  simp only []
  rcases Int.lt_trichotomy z 0 with h | h | h
  · rw [hneg h, hneg' h, round_via_double _ _ _ (by omega) (by omega)]
  · rw [hzero h, hzero' h]; rfl
  · rw [hpos h, hpos' h, round_via_double _ _ _ (by omega) (by omega)]

namespace Float32

theorem of_int_double (n : Integers.Int) : ofInt n = ofDouble (Float.ofInt n) := by
  apply ofZ_double
  have h1 := Integers.Int.signed_range n
  have h2 : Integers.Int.min_signed = -2147483648 := by decide
  have h3 : Integers.Int.max_signed = 2147483647 := by decide
  rw [h2, h3] at h1
  exact ⟨Int.lt_of_lt_of_le (by decide) h1.1, Int.lt_of_le_of_lt h1.2 (by decide)⟩

theorem of_intu_double (n : Integers.Int) : ofIntu n = ofDouble (Float.ofIntu n) := by
  apply ofZ_double
  have h1 := Integers.Int.unsigned_range n
  have h2 : Integers.Int.modulus = 4294967296 := by decide
  rw [h2] at h1
  exact ⟨Int.lt_of_lt_of_le (by decide) h1.1, Int.lt_trans h1.2 (by decide)⟩

theorem to_int_double (f : Float32) (n : Integers.Int) (h : toInt f = some n) :
    Float.toInt (toDouble f) = some n := by
  simp only [toInt, Float.toInt, Option.map_eq_some_iff] at *
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨z, toZRange_ofSingle f _ _ z hz, rfl⟩

theorem to_intu_double (f : Float32) (n : Integers.Int) (h : toIntu f = some n) :
    Float.toIntu (toDouble f) = some n := by
  simp only [toIntu, Float.toIntu, Option.map_eq_some_iff] at *
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨z, toZRange_ofSingle f _ _ z hz, rfl⟩

theorem to_long_double (f : Float32) (n : Integers.Int64) (h : toLong f = some n) :
    Float.toLong (toDouble f) = some n := by
  simp only [toLong, Float.toLong, Option.map_eq_some_iff] at *
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨z, toZRange_ofSingle f _ _ z hz, rfl⟩

theorem to_longu_double (f : Float32) (n : Integers.Int64) (h : toLongu f = some n) :
    Float.toLongu (toDouble f) = some n := by
  simp only [toLongu, Float.toLongu, Option.map_eq_some_iff] at *
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨z, toZRange_ofSingle f _ _ z hz, rfl⟩

end Float32

end Floats
end CC
