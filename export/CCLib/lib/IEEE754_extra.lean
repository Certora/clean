/-
  Port of the integer-arithmetic part of `lib/IEEE754_extra.v`:
  `integer_representable`, `BofZ_exact`, `BofZ_representable`, `BofZ_plus`,
  `BofZ_minus`, `BofZ_mult`, and `ZofBofZ_exact` (`toZ_ofZ`, with its
  `ZofB_range` corollary `toZRange_ofZ`).

  In Rocq these results are stated on Flocq's `binary_float` and proved via
  the real-number semantics `B2R`.  Here they are proved on the exact IEEE
  model of `CCLib.lib.FloatModel`, where `IEEE754_extra.BofZ` is `Gen.ofZ`.

  Differences from Rocq:
  * `integer_representable` is replaced by `IntRepr`, which is Rocq's sufficient
    condition `integer_representable_n2p` (`n · 2^p` with `|n| < 2^prec` and
    `p ≤ emax - prec`); every use of `BofZ_plus` / `BofZ_minus` / `BofZ_mult`
    in `lib/Floats.v` establishes representability through
    `integer_representable_n` or `integer_representable_n2p`.
  * `BofZ_exact` / `BofZ_representable` are stated as "unpacking `ofZ z`
    gives back the exactly rounded value of `z`" (`unpack_ofZ`) together with
    a description of that value (`normalize_int_form`), instead of `B2R`
    equations.
-/
import CCLib.lib.FloatsArith

namespace CC
namespace FloatModel
namespace UnpackedFloat

/-! ## Representation independence of `normalize` -/

theorem normalize_shift (spec : Format) (N : Int) (j : Nat) (e : Int) (zs : Sign) :
    normalize spec (N * 2 ^ j) (e - j) zs = normalize spec N e zs := by
  rcases Int.lt_trichotomy N 0 with h | h | h
  · obtain ⟨n, rfl⟩ : ∃ n : Nat, N = Sign.negative.apply (n : Int) :=
      ⟨N.natAbs, by simp [Sign.apply]; omega⟩
    have hn : 0 < n := by simp [Sign.apply] at h; omega
    have : Sign.negative.apply (n : Int) * 2 ^ j = Sign.negative.apply ((n <<< j : Nat) : Int) := by
      simp [Sign.apply, Nat.shiftLeft_eq, Int.neg_mul]
    rw [this, normalize_apply _ _ _ _ _ (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hn (Nat.two_pow_pos _)),
      normalize_apply _ _ _ _ _ hn, round_shift _ _ _ _ _ hn]
  · subst h; simp [normalize]
  · obtain ⟨n, rfl⟩ : ∃ n : Nat, N = Sign.positive.apply (n : Int) :=
      ⟨N.natAbs, by simp [Sign.apply]; omega⟩
    have hn : 0 < n := by simp [Sign.apply] at h; omega
    have : Sign.positive.apply (n : Int) * 2 ^ j = Sign.positive.apply ((n <<< j : Nat) : Int) := by
      simp [Sign.apply, Nat.shiftLeft_eq]
    rw [this, normalize_apply _ _ _ _ _ (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hn (Nat.two_pow_pos _)),
      normalize_apply _ _ _ _ _ hn, round_shift _ _ _ _ _ hn]

/-- A finite value `s · M · 2^E` that equals the integer `z` (scaled by `2^K`)
rounds like `z`. -/
theorem round_eq_normalize (spec : Format) (s : Sign) (M : Nat) (E : Int) (hM : 0 < M)
    (z : Int) (K : Nat) (hEK : 0 ≤ E + K)
    (hv : s.apply ((M <<< (E + K).toNat : Nat) : Int) = z * 2 ^ K) :
    round spec s M E = normalize spec z 0 .positive := by
  rw [← round_shift spec s M (E + K).toNat E hM, ← normalize_apply spec s _ _ .positive
    (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hM (Nat.two_pow_pos _)), hv,
    ← normalize_shift spec z K 0 .positive]
  congr 1
  omega

theorem apply_shiftLeft_mul (s : Sign) (m a d : Nat) :
    s.apply ((m <<< a : Nat) : Int) * 2 ^ d = s.apply ((m <<< (a + d) : Nat) : Int) := by
  cases s <;> simp [Sign.apply, Nat.shiftLeft_eq, Nat.pow_add, Int.mul_assoc, Int.neg_mul]

/-- Sum of two finite floats, computed at any common exponent `k`. -/
theorem add_finite (spec : Format) (s₁ : Sign) (m₁ : Nat) (e₁ : Int) (h₁ : 0 < m₁)
    (s₂ : Sign) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) (k : Int) (hk₁ : k ≤ e₁) (hk₂ : k ≤ e₂) :
    add spec (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) =
      normalize spec (s₁.apply ((m₁ <<< (e₁ - k).toNat : Nat) : Int) +
        s₂.apply ((m₂ <<< (e₂ - k).toNat : Nat) : Int)) k .positive := by
  simp only [add, decreaseExponent]
  rw [← normalize_shift spec _ (min e₁ e₂ - k).toNat (min e₁ e₂), Int.add_mul,
    apply_shiftLeft_mul, apply_shiftLeft_mul]
  have h1 : (e₁ - min e₁ e₂).toNat + (min e₁ e₂ - k).toNat = (e₁ - k).toNat := by omega
  have h2 : (e₂ - min e₁ e₂).toNat + (min e₁ e₂ - k).toNat = (e₂ - k).toNat := by omega
  have h3 : min e₁ e₂ - ((min e₁ e₂ - k).toNat : Int) = k := by omega
  rw [h1, h2, h3]

/-- Difference of two finite floats, computed at any common exponent `k`. -/
theorem sub_finite (spec : Format) (s₁ : Sign) (m₁ : Nat) (e₁ : Int) (h₁ : 0 < m₁)
    (s₂ : Sign) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) (k : Int) (hk₁ : k ≤ e₁) (hk₂ : k ≤ e₂) :
    sub spec (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) =
      normalize spec (s₁.apply ((m₁ <<< (e₁ - k).toNat : Nat) : Int) -
        s₂.apply ((m₂ <<< (e₂ - k).toNat : Nat) : Int)) k .positive := by
  simp only [sub, decreaseExponent]
  rw [← normalize_shift spec _ (min e₁ e₂ - k).toNat (min e₁ e₂), Int.sub_mul,
    apply_shiftLeft_mul, apply_shiftLeft_mul]
  have h1 : (e₁ - min e₁ e₂).toNat + (min e₁ e₂ - k).toNat = (e₁ - k).toNat := by omega
  have h2 : (e₂ - min e₁ e₂).toNat + (min e₁ e₂ - k).toNat = (e₂ - k).toNat := by omega
  have h3 : min e₁ e₂ - ((min e₁ e₂ - k).toNat : Int) = k := by omega
  rw [h1, h2, h3]

theorem exponentBits_facts (spec : Format) :
    2 ^ spec.exponentBits = 2 * (spec.exponentBias + 1) ∧ 1 ≤ spec.exponentBias ∧
    spec.minExponent = 2 - (spec.exponentBias : Int) - spec.mantissaBits := by
  have he := spec.he
  have h1 : 2 ^ spec.exponentBits = 2 * 2 ^ (spec.exponentBits - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h2 : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ spec.exponentBits - 1 by omega)
    simpa using this
  have h3 : (2 : Int) ^ (spec.exponentBits - 1) = ((2 ^ (spec.exponentBits - 1) : Nat) : Int) := by
    simp [Int.natCast_pow]
  simp only [Format.exponentBias, Format.minExponent, h3]
  refine ⟨by omega, by omega, by omega⟩

/-! ## Rounding only depends on the high bits and on a sticky bit -/

theorem accFrac_sticky (R La Lb K u : Nat) (hR : R < 2 ^ (u + 1)) (hLa : La < 2 ^ K)
    (hLb : Lb < 2 ^ K) (hab : La = 0 ↔ Lb = 0) :
    accuracyOfFraction (R * 2 ^ K + La) (2 ^ (K + 1 + u)) =
      accuracyOfFraction (R * 2 ^ K + Lb) (2 ^ (K + 1 + u)) := by
  have hP := Nat.two_pow_pos K
  have hD := Nat.two_pow_pos u
  have hpow : 2 ^ (K + 1 + u) = 2 * (2 ^ u * 2 ^ K) := by
    rw [Nat.pow_add, Nat.pow_succ]; ac_rfl
  rw [hpow]
  unfold accuracyOfFraction
  have hz : R * 2 ^ K + La = 0 ↔ R * 2 ^ K + Lb = 0 := by
    constructor <;> intro h
    · have : R * 2 ^ K = 0 := by omega
      have : La = 0 := by omega
      have := hab.1 this; omega
    · have : R * 2 ^ K = 0 := by omega
      have : Lb = 0 := by omega
      have := hab.2 this; omega
  by_cases h0 : R * 2 ^ K + La = 0
  · rw [if_pos h0, if_pos (hz.1 h0)]
  · rw [if_neg h0, if_neg (fun h => h0 (hz.2 h))]
    congr 1
    rcases Nat.lt_trichotomy R (2 ^ u) with h | h | h
    · have h1 : (R + 1) * 2 ^ K ≤ 2 ^ u * 2 ^ K := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at h1
      rw [Nat.compare_eq_lt.2 (by omega), Nat.compare_eq_lt.2 (by omega)]
    · subst h
      by_cases hl : La = 0
      · have hl' := hab.1 hl
        subst hl hl'; rfl
      · have hl' : Lb ≠ 0 := fun h => hl (hab.2 h)
        rw [Nat.compare_eq_gt.2 (by omega), Nat.compare_eq_gt.2 (by omega)]
    · have h1 : (2 ^ u + 1) * 2 ^ K ≤ R * 2 ^ K := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at h1
      rw [Nat.compare_eq_gt.2 (by omega), Nat.compare_eq_gt.2 (by omega)]

theorem log2_add_low (Q L K : Nat) (hQ : 0 < Q) (hL : L < 2 ^ K) :
    (Q * 2 ^ K + L).log2 = Q.log2 + K := by
  have hP := Nat.two_pow_pos K
  have hne : Q * 2 ^ K + L ≠ 0 := by
    have : 0 < Q * 2 ^ K := Nat.mul_pos hQ hP
    omega
  have h1 := Nat.log2_self_le (Nat.ne_of_gt hQ)
  have h2 := @Nat.lt_log2_self Q
  apply Nat.le_antisymm
  · apply Nat.lt_succ_iff.mp
    rw [Nat.log2_lt hne, Nat.succ_eq_add_one, Nat.add_right_comm, Nat.pow_add]
    have : (Q + 1) * 2 ^ K ≤ 2 ^ (Q.log2 + 1) * 2 ^ K := Nat.mul_le_mul_right _ h2
    rw [Nat.succ_mul] at this
    omega
  · rw [Nat.le_log2 hne, Nat.pow_add]
    have := Nat.mul_le_mul_right (2 ^ K) h1
    omega

/-- Rounding an integer whose rounding position lies above bit `K` only
depends on the bits above `K` and on whether the bits below `K` are all
zero (the key property of round-to-odd, Rocq's `BofZ_round_odd`). -/
theorem round_sticky (spec : Format) (s : Sign) (Q La Lb K : Nat) (hLa : La < 2 ^ K)
    (hLb : Lb < 2 ^ K) (hab : La = 0 ↔ Lb = 0) (hQ : 2 ^ spec.mantissaBits ≤ Q) :
    round spec s (Q * 2 ^ K + La) 0 = round spec s (Q * 2 ^ K + Lb) 0 := by
  have hQ0 : 0 < Q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hQ
  have hlogQ : spec.mantissaBits ≤ Q.log2 := (Nat.le_log2 (Nat.ne_of_gt hQ0)).2 hQ
  have hla := log2_add_low Q La K hQ0 hLa
  have hlb := log2_add_low Q Lb K hQ0 hLb
  obtain ⟨u, hu⟩ : ∃ u, Q.log2 = spec.mantissaBits + u := ⟨Q.log2 - spec.mantissaBits, by omega⟩
  obtain ⟨-, hb1, hmin⟩ := exponentBits_facts spec
  have ht' : ∀ L, (Q * 2 ^ K + L).log2 = Q.log2 + K →
      spec.targetExponent (totalExponent (Q * 2 ^ K + L) 0) = ((K + 1 + u : Nat) : Int) := by
    intro L hL
    simp only [Format.targetExponent, totalExponent, hL, hmin, hu]
    omega
  rw [round_eq_roundWithAccuracy _ _ _ _ (by rw [ht' La hla]; omega),
    round_eq_roundWithAccuracy _ _ _ _ (by rw [ht' Lb hlb]; omega)]
  have hfa := roundWithAccuracy_frac spec s (Q * 2 ^ K + La) (K + 1 + u) 0 (by rw [ht' La hla]; omega)
  have hfb := roundWithAccuracy_frac spec s (Q * 2 ^ K + Lb) (K + 1 + u) 0 (by rw [ht' Lb hlb]; omega)
  rw [← hfa, ← hfb]
  have hdiv : ∀ L, L < 2 ^ K → (Q * 2 ^ K + L) / 2 ^ (K + 1 + u) = Q / 2 ^ (u + 1) := by
    intro L hL
    rw [show K + 1 + u = K + (u + 1) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.mul_comm Q, Nat.mul_add_div (Nat.two_pow_pos K), Nat.div_eq_of_lt hL, Nat.add_zero]
  have hmod : ∀ L, L < 2 ^ K → (Q * 2 ^ K + L) % 2 ^ (K + 1 + u) = (Q % 2 ^ (u + 1)) * 2 ^ K + L := by
    intro L hL
    rw [show K + 1 + u = K + (u + 1) by omega, Nat.pow_add, Nat.mod_mul, Nat.mul_comm Q,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hL, Nat.mul_add_div (Nat.two_pow_pos K),
      Nat.div_eq_of_lt hL, Nat.add_zero]
    have := Nat.mul_comm (2 ^ K) (Q % 2 ^ (u + 1))
    omega
  rw [hdiv La hLa, hdiv Lb hLb, hmod La hLa, hmod Lb hLb,
    accFrac_sticky _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) hLa hLb hab]

end UnpackedFloat
end FloatModel

namespace Floats
namespace Gen

open FloatModel FloatModel.UnpackedFloat

/-- `integer_representable_n2p`: `z = n · 2^p` with `|n| < 2^prec` and
`p ≤ emax - prec`.  Such integers are represented exactly by `ofZ`. -/
def IntRepr (spec : Format) (z : Int) : Prop :=
  ∃ (n : Int) (p : Nat), z = n * 2 ^ p ∧ n.natAbs < 2 ^ spec.mantissaBits ∧
    p + spec.mantissaBits ≤ spec.exponentBias + 1

/-- `integer_representable_n` -/
theorem intRepr_n (spec : Format) (hspec : spec.mantissaBits ≤ spec.exponentBias + 1)
    (z : Int) (h : z.natAbs < 2 ^ spec.mantissaBits) :
    IntRepr spec z :=
  ⟨z, 0, by simp, h, by omega⟩

/-- `integer_representable_n2p` -/
theorem intRepr_n2p (spec : Format) (n : Int) (p : Nat) (hn : n.natAbs < 2 ^ spec.mantissaBits)
    (hp : p + spec.mantissaBits ≤ spec.exponentBias + 1) :
    IntRepr spec (n * 2 ^ p) :=
  ⟨n, p, rfl, hn, hp⟩

/-- Description of the exactly rounded value of a representable nonzero
integer: a normal float `s · M · 2^E` in canonical form whose value is `z`. -/
theorem normalize_int_form (spec : Format) (z : Int) (hz : IntRepr spec z) (hz0 : z ≠ 0) :
    ∃ (s : Sign) (M : Nat) (E : Int) (hM : 0 < M) (K₀ : Nat),
      normalize spec z 0 .positive = .finite s M E hM ∧
      unpack spec (pack spec (.finite s M E hM)) = .finite s M E hM ∧
      M.log2 + 1 = spec.mantissaBits ∧
      spec.targetExponent (totalExponent M E) = E ∧
      ∀ K : Nat, K₀ ≤ K → 0 ≤ E + K ∧ s.apply ((M <<< (E + K).toNat : Nat) : Int) = z * 2 ^ K := by
  obtain ⟨n, p, rfl, hn, hp⟩ := hz
  obtain ⟨hE2, hbias, hmin⟩ := exponentBits_facts spec
  have hn0 : n ≠ 0 := by intro h; apply hz0; simp [h]
  obtain ⟨s, a, rfl, ha⟩ : ∃ (s : Sign) (a : Nat), n = s.apply (a : Int) ∧ 0 < a := by
    rcases Int.lt_or_gt_of_ne hn0 with h | h
    · exact ⟨.negative, n.natAbs, by simp [Sign.apply]; omega, by omega⟩
    · exact ⟨.positive, n.natAbs, by simp [Sign.apply]; omega, by omega⟩
  have han : (s.apply (a : Int)).natAbs = a := by cases s <;> simp [Sign.apply]
  rw [han] at hn
  have hlog : a.log2 < spec.mantissaBits := (Nat.log2_lt (Nat.ne_of_gt ha)).2 hn
  have hmb : spec.mantissaBits = 1 + spec.mantissaBitsWithoutImplicit := rfl
  have hz : s.apply (a : Int) * 2 ^ p = s.apply ((a <<< p : Nat) : Int) := by
    simpa using apply_shiftLeft_mul s a 0 p
  have hap : 0 < a <<< p := by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos ha (Nat.two_pow_pos _)
  rw [hz, normalize_apply _ _ _ _ _ hap]
  have hr : round spec s (a <<< p) 0 = round spec s a p := by
    have := round_shift spec s a p p ha
    simpa using this
  rw [hr]
  obtain ⟨hM, hround⟩ := round_normal spec s a p ha hlog (by rw [hmin]; omega)
  generalize hj : spec.mantissaBits - 1 - a.log2 = j at hM hround
  have hlogM : (a <<< j).log2 + 1 = spec.mantissaBits := by
    rw [log2_shiftLeft _ _ ha]; omega
  refine ⟨s, a <<< j, (p : Int) - j, hM, j, hround, ?_, hlogM, ?_, ?_⟩
  · apply unpack_pack_normal _ _ _ _ _ hlogM
    · omega
    · omega
  · simp only [Format.targetExponent, totalExponent]
    omega
  · intro K hK
    refine ⟨by omega, ?_⟩
    have h1 : ((p : Int) - j + K).toNat = p + K - j := by omega
    rw [h1, ← Nat.shiftLeft_add, show j + (p + K - j) = p + K by omega,
      ← apply_shiftLeft_mul]

/-- `BofZ_exact` / `BofZ_representable`: `ofZ` represents a representable
integer exactly. -/
theorem unpack_ofZ (spec : Format) (z : Int) (hz : IntRepr spec z) :
    unpack spec (ofZ spec z) = normalize spec z 0 .positive := by
  unfold ofZ
  by_cases hz0 : z = 0
  · subst hz0
    simp only [normalize]
    exact unpack_packedZero
  · obtain ⟨s, M, E, hM, K₀, hn, hup, -⟩ := normalize_int_form spec z hz hz0
    rw [hn, hup]

theorem packOr_normalize (spec : Format) (nan : BitVec spec.numBits) (z e : Int) (zs : Sign) :
    packOr spec nan (normalize spec z e zs) = pack spec (normalize spec z e zs) := by
  unfold normalize
  split
  · exact packOr_round _ _ _ _ _
  · rfl
  · exact packOr_round _ _ _ _ _

theorem add_normalize (spec : Format) (p q : Int) (hp : IntRepr spec p) (hq : IntRepr spec q) :
    UnpackedFloat.add spec (normalize spec p 0 .positive) (normalize spec q 0 .positive) =
      normalize spec (p + q) 0 .positive := by
  by_cases hp0 : p = 0
  · subst hp0
    by_cases hq0 : q = 0
    · subst hq0; rfl
    · obtain ⟨s, M, E, hM, K₀, hn, -⟩ := normalize_int_form spec q hq hq0
      rw [hn, Int.zero_add, hn]; rfl
  · obtain ⟨s₁, M₁, E₁, hM₁, K₁, hn₁, -, -, -, hv₁⟩ := normalize_int_form spec p hp hp0
    by_cases hq0 : q = 0
    · subst hq0
      rw [hn₁, Int.add_zero, hn₁]; rfl
    · obtain ⟨s₂, M₂, E₂, hM₂, K₂, hn₂, -, -, -, hv₂⟩ := normalize_int_form spec q hq hq0
      obtain ⟨h1, h1'⟩ := hv₁ (K₁ + K₂) (by omega)
      obtain ⟨h2, h2'⟩ := hv₂ (K₁ + K₂) (by omega)
      rw [hn₁, hn₂, add_finite spec _ _ _ _ _ _ _ _ (-((K₁ + K₂ : Nat) : Int)) (by omega) (by omega)]
      rw [show E₁ - -((K₁ + K₂ : Nat) : Int) = E₁ + ((K₁ + K₂ : Nat) : Int) by omega,
        show E₂ - -((K₁ + K₂ : Nat) : Int) = E₂ + ((K₁ + K₂ : Nat) : Int) by omega, h1', h2',
        ← Int.add_mul, show -((K₁ + K₂ : Nat) : Int) = 0 - ((K₁ + K₂ : Nat) : Int) by omega,
        normalize_shift]

theorem sub_normalize (spec : Format) (p q : Int) (hp : IntRepr spec p) (hq : IntRepr spec q) :
    UnpackedFloat.sub spec (normalize spec p 0 .positive) (normalize spec q 0 .positive) =
      normalize spec (p - q) 0 .positive := by
  by_cases hp0 : p = 0
  · subst hp0
    by_cases hq0 : q = 0
    · subst hq0; rfl
    · obtain ⟨s, M, E, hM, K₀, hn, -, -, hcan, hv⟩ := normalize_int_form spec q hq hq0
      obtain ⟨h1, h1'⟩ := hv K₀ (Nat.le_refl _)
      rw [hn]
      show UnpackedFloat.finite (-s) M E hM = _
      rw [← round_exact spec (-s) M E hM hcan]
      apply round_eq_normalize spec (-s) M E hM _ K₀ h1
      have : (-s).apply ((M <<< (E + K₀).toNat : Nat) : Int) =
          -(s.apply ((M <<< (E + K₀).toNat : Nat) : Int)) := by
        cases s
        · show ((M <<< (E + K₀).toNat : Nat) : Int) = - -((M <<< (E + K₀).toNat : Nat) : Int)
          rw [Int.neg_neg]
        · rfl
      rw [this, h1', Int.zero_sub, Int.neg_mul]
  · obtain ⟨s₁, M₁, E₁, hM₁, K₁, hn₁, -, -, -, hv₁⟩ := normalize_int_form spec p hp hp0
    by_cases hq0 : q = 0
    · subst hq0
      rw [hn₁, Int.sub_zero, hn₁]; rfl
    · obtain ⟨s₂, M₂, E₂, hM₂, K₂, hn₂, -, -, -, hv₂⟩ := normalize_int_form spec q hq hq0
      obtain ⟨h1, h1'⟩ := hv₁ (K₁ + K₂) (by omega)
      obtain ⟨h2, h2'⟩ := hv₂ (K₁ + K₂) (by omega)
      rw [hn₁, hn₂, sub_finite spec _ _ _ _ _ _ _ _ (-((K₁ + K₂ : Nat) : Int)) (by omega) (by omega)]
      rw [show E₁ - -((K₁ + K₂ : Nat) : Int) = E₁ + ((K₁ + K₂ : Nat) : Int) by omega,
        show E₂ - -((K₁ + K₂ : Nat) : Int) = E₂ + ((K₁ + K₂ : Nat) : Int) by omega, h1', h2',
        ← Int.sub_mul, show -((K₁ + K₂ : Nat) : Int) = 0 - ((K₁ + K₂ : Nat) : Int) by omega,
        normalize_shift]

theorem apply_mul_apply (s₁ s₂ : Sign) (x y : Nat) :
    s₁.apply (x : Int) * s₂.apply (y : Int) = (s₁ * s₂).apply ((x * y : Nat) : Int) := by
  cases s₁ <;> cases s₂ <;> simp only [Sign.apply, Int.natCast_mul,
    Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem mul_normalize (spec : Format) (p q : Int) (hp : IntRepr spec p) (hq : IntRepr spec q)
    (hq0 : 0 < q) :
    UnpackedFloat.mul spec (normalize spec p 0 .positive) (normalize spec q 0 .positive) =
      normalize spec (p * q) 0 .positive := by
  obtain ⟨s₂, M₂, E₂, hM₂, K₂, hn₂, -, hl₂, -, hv₂⟩ := normalize_int_form spec q hq (by omega)
  have hs₂ : s₂ = .positive := by
    obtain ⟨-, h⟩ := hv₂ K₂ (Nat.le_refl _)
    cases s₂
    · exfalso
      simp only [Sign.apply] at h
      have := Int.natCast_nonneg (M₂ <<< (E₂ + K₂).toNat)
      have : 0 < q * 2 ^ K₂ := Int.mul_pos hq0 (Int.pow_pos (by decide))
      omega
    · rfl
  subst hs₂
  by_cases hp0 : p = 0
  · subst hp0
    rw [hn₂, Int.zero_mul]; rfl
  · obtain ⟨s₁, M₁, E₁, hM₁, K₁, hn₁, -, hl₁, -, hv₁⟩ := normalize_int_form spec p hp hp0
    obtain ⟨h1, h1'⟩ := hv₁ K₁ (Nat.le_refl _)
    obtain ⟨h2, h2'⟩ := hv₂ K₂ (Nat.le_refl _)
    rw [hn₁, hn₂]
    show roundWithAccuracy spec (s₁ * .positive) (M₁ * M₂) (E₁ + E₂) .exact = _
    have hM12 : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
    rw [← round_eq_roundWithAccuracy]
    · apply round_eq_normalize spec _ _ _ hM12 _ (K₁ + K₂) (by omega)
      have h3 : (E₁ + E₂ + ((K₁ + K₂ : Nat) : Int)).toNat = (E₁ + K₁).toNat + (E₂ + K₂).toNat := by
        omega
      rw [h3, Nat.shiftLeft_eq, Nat.pow_add,
        show M₁ * M₂ * (2 ^ (E₁ + K₁).toNat * 2 ^ (E₂ + K₂).toNat) =
          (M₁ * 2 ^ (E₁ + K₁).toNat) * (M₂ * 2 ^ (E₂ + K₂).toNat) by
          simp only [Nat.mul_assoc, Nat.mul_left_comm],
        ← apply_mul_apply, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, h1', h2', Int.pow_add]
      simp only [Int.mul_assoc, Int.mul_left_comm]
    · have hlow : 2 ^ (spec.mantissaBits - 1) ≤ M₁ * M₂ := by
        have := Nat.log2_self_le (Nat.ne_of_gt hM₁)
        have h' : M₁ ≤ M₁ * M₂ := Nat.le_mul_of_pos_right _ hM₂
        rw [show M₁.log2 = spec.mantissaBits - 1 by omega] at this
        omega
      have hlog : spec.mantissaBits - 1 ≤ (M₁ * M₂).log2 := (Nat.le_log2 (Nat.ne_of_gt hM12)).2 hlow
      simp only [Format.targetExponent, totalExponent]
      omega

/-- `BofZ_plus` -/
theorem ofZ_plus {spec : Format} (nc : NanConfig spec) (p q : Int)
    (hp : IntRepr spec p) (hq : IntRepr spec q) :
    add nc (ofZ spec p) (ofZ spec q) = ofZ spec (p + q) := by
  unfold add
  rw [unpack_ofZ _ _ hp, unpack_ofZ _ _ hq, add_normalize _ _ _ hp hq, packOr_normalize]
  rfl

/-- `BofZ_minus` -/
theorem ofZ_minus {spec : Format} (nc : NanConfig spec) (p q : Int)
    (hp : IntRepr spec p) (hq : IntRepr spec q) :
    sub nc (ofZ spec p) (ofZ spec q) = ofZ spec (p - q) := by
  unfold sub
  rw [unpack_ofZ _ _ hp, unpack_ofZ _ _ hq, sub_normalize _ _ _ hp hq, packOr_normalize]
  rfl

/-- `BofZ_mult` -/
theorem ofZ_mult {spec : Format} (nc : NanConfig spec) (p q : Int)
    (hp : IntRepr spec p) (hq : IntRepr spec q) (hq0 : 0 < q) :
    mul nc (ofZ spec p) (ofZ spec q) = ofZ spec (p * q) := by
  unfold mul
  rw [unpack_ofZ _ _ hp, unpack_ofZ _ _ hq, mul_normalize _ _ _ hp hq hq0, packOr_normalize]
  rfl

/-- `BofZ_round_odd`, in the form used here: an integer whose rounding
position lies above bit `K` rounds like any other integer with the same bits
above `K` and the same "sticky" bit (whether the bits below `K` are zero). -/
theorem ofZ_sticky (spec : Format) (s : Sign) (Q La Lb K : Nat) (hLa : La < 2 ^ K)
    (hLb : Lb < 2 ^ K) (hab : La = 0 ↔ Lb = 0) (hQ : 2 ^ spec.mantissaBits ≤ Q) :
    ofZ spec (s.apply ((Q * 2 ^ K + La : Nat) : Int)) =
      ofZ spec (s.apply ((Q * 2 ^ K + Lb : Nat) : Int)) := by
  have hQ0 : 0 < Q := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hQ
  have hp : ∀ L, 0 < Q * 2 ^ K + L := fun L => by
    have := Nat.mul_pos hQ0 (Nat.two_pow_pos K); omega
  unfold ofZ
  rw [normalize_apply _ _ _ _ _ (hp La), normalize_apply _ _ _ _ _ (hp Lb),
    round_sticky spec s Q La Lb K hLa hLb hab hQ]

/-! ## Float-to-integer conversion: `ZofBofZ_exact` -/

theorem apply_shiftRight_of_eq (s : Sign) (N K : Nat) (z : Int)
    (h : s.apply (N : Int) = z * 2 ^ K) : s.apply ((N >>> K : Nat) : Int) = z := by
  have hpos : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  rw [Nat.shiftRight_eq_div_pow]
  cases s with
  | positive =>
    simp only [Sign.apply] at h ⊢
    rw [Int.natCast_ediv, h]; push_cast; exact Int.mul_ediv_cancel z (by omega)
  | negative =>
    simp only [Sign.apply] at h ⊢
    have : (N : Int) = (-z) * 2 ^ K := by rw [Int.neg_mul]; omega
    rw [Int.natCast_ediv, this]; push_cast
    rw [Int.mul_ediv_cancel _ (by omega)]; omega

theorem truncZ_of_eq (s : Sign) (M K : Nat) (E z : Int) (hEK : 0 ≤ E + K)
    (h : s.apply ((M <<< (E + K).toNat : Nat) : Int) = z * 2 ^ K) : truncZ s M E = z := by
  have e1 := truncZ_shift s M (E + K).toNat E
  have e2 : E - ((E + K).toNat : Int) = -(K : Int) := by omega
  rw [← e1, e2]
  unfold truncZ
  by_cases hK : K = 0
  · subst hK; simp at h ⊢; simpa using h
  · rw [if_neg (by omega)]
    have : (-(K : Int)).natAbs = K := by omega
    rw [this]; exact apply_shiftRight_of_eq s _ K z h

/-- `ZofBofZ_exact`: for representable integers, `toZ` (`ZofB`) is a left
inverse of `ofZ` (`BofZ`). -/
theorem toZ_ofZ (spec : Format) (z : Int) (hz : IntRepr spec z) :
    toZ spec (ofZ spec z) = some z := by
  unfold toZ
  rw [unpack_ofZ spec z hz]
  by_cases hz0 : z = 0
  · subst hz0; simp [normalize]
  · obtain ⟨s, M, E, hM, K₀, hn, -, -, -, hK⟩ := normalize_int_form spec z hz hz0
    rw [hn]
    obtain ⟨hEK, hv⟩ := hK K₀ (Nat.le_refl _)
    exact congrArg some (truncZ_of_eq s M K₀ E z hEK hv)
/-- `ZofB_range` applied to `BofZ`: a representable integer in `[lo, hi]` is
converted back exactly. -/
theorem toZRange_ofZ (spec : Format) (z lo hi : Int) (hz : IntRepr spec z)
    (hlo : lo ≤ z) (hhi : z ≤ hi) : toZRange spec (ofZ spec z) lo hi = some z :=
  toZRange_eq_some.mpr ⟨toZ_ofZ spec z hz, hlo, hhi⟩

end Gen
end Floats
end CC
