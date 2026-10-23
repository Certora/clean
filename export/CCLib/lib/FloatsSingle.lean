/-
  Theorems of `lib/Floats.v` (section `Float32`) relating binary32 and
  binary64: `of_longu_double_1`, `of_long_double_1` (64-bit integers that
  fit in 53 bits convert to binary32 directly or through binary64 with the
  same result) and `cmp_double` (comparing two binary32 floats is the same as
  comparing their binary64 widenings).

  `ofZ_double_repr` generalizes `ofZ_double` (`CCLib.lib.FloatsConv`) from
  integers below `2^53` to every integer exactly representable in binary64
  (Rocq's `Bconv_BofZ`).
-/
import CCLib.lib.FloatsDecomp

namespace CC
namespace FloatModel.UnpackedFloat

theorem compare_shiftLeft (a b d : Nat) : compare (a <<< d) (b <<< d) = compare a b := by
  have hp := Nat.two_pow_pos d
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by
      simp only [Nat.shiftLeft_eq]; exact Nat.mul_lt_mul_of_pos_right h hp)]
  · subst h; rw [Nat.compare_eq_eq.2 rfl, Nat.compare_eq_eq.2 rfl]
  · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by
      simp only [Nat.shiftLeft_eq]; exact Nat.mul_lt_mul_of_pos_right h hp)]

/-- Comparison of the values `m₁ · 2^e₁` and `m₂ · 2^e₂`, computed at the
common exponent `k`. -/
def valAt (k : Int) (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) : Ordering :=
  compare (m₁ <<< (e₁ - k).toNat) (m₂ <<< (e₂ - k).toNat)

theorem valAt_mono (k' k : Int) (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int)
    (hk : k' ≤ k) (h₁ : k ≤ e₁) (h₂ : k ≤ e₂) :
    valAt k' m₁ e₁ m₂ e₂ = valAt k m₁ e₁ m₂ e₂ := by
  unfold valAt
  rw [show (e₁ - k').toNat = (e₁ - k).toNat + (k - k').toNat by omega,
    show (e₂ - k').toNat = (e₂ - k).toNat + (k - k').toNat by omega,
    Nat.shiftLeft_add, Nat.shiftLeft_add, compare_shiftLeft]

/-- On canonical forms, the lexicographic comparison used by `compare` is the
comparison of values. -/
theorem lex_eq_val (p : Nat) (emin : Int) (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int)
    (C₁ : Canon p emin m₁ e₁) (C₂ : Canon p emin m₂ e₂) :
    (compare e₁ e₂).then (compare m₁ m₂) = valAt (min e₁ e₂) m₁ e₁ m₂ e₂ := by
  have hp : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold valAt
  rcases Int.lt_trichotomy e₁ e₂ with h | h | h
  · rw [Int.compare_eq_lt.2 h]
    have hm₂ : 2 ^ p ≤ m₂ := by
      rcases C₂ with C | C
      · exact C.1
      · rcases C₁ with C' | C' <;> omega
    have hm₁ : m₁ < 2 ^ (p + 1) := by rcases C₁ with C | C <;> omega
    rw [show (e₁ - min e₁ e₂).toNat = 0 by omega, Nat.shiftLeft_zero]
    obtain ⟨d, hd⟩ : ∃ d, (e₂ - min e₁ e₂).toNat = d + 1 := ⟨(e₂ - min e₁ e₂).toNat - 1, by omega⟩
    rw [hd]
    symm; apply Nat.compare_eq_lt.2
    rw [Nat.shiftLeft_eq, Nat.pow_succ]
    have : 2 ^ p * 2 ≤ m₂ * (2 ^ d * 2) := by
      have := Nat.two_pow_pos d
      calc 2 ^ p * 2 ≤ m₂ * 2 := Nat.mul_le_mul_right _ hm₂
        _ ≤ m₂ * (2 ^ d * 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  · subst h
    have : compare e₁ e₁ = .eq := by simp
    rw [this, Int.min_self, Int.sub_self]
    simp [Ordering.then]
  · rw [Int.compare_eq_gt.2 h]
    have hm₁ : 2 ^ p ≤ m₁ := by
      rcases C₁ with C | C
      · exact C.1
      · rcases C₂ with C' | C' <;> omega
    have hm₂ : m₂ < 2 ^ (p + 1) := by rcases C₂ with C | C <;> omega
    rw [show (e₂ - min e₁ e₂).toNat = 0 by omega, Nat.shiftLeft_zero]
    obtain ⟨d, hd⟩ : ∃ d, (e₁ - min e₁ e₂).toNat = d + 1 := ⟨(e₁ - min e₁ e₂).toNat - 1, by omega⟩
    rw [hd]
    symm; apply Nat.compare_eq_gt.2
    rw [Nat.shiftLeft_eq, Nat.pow_succ]
    have : 2 ^ p * 2 ≤ m₁ * (2 ^ d * 2) := by
      have := Nat.two_pow_pos d
      calc 2 ^ p * 2 ≤ m₁ * 2 := Nat.mul_le_mul_right _ hm₁
        _ ≤ m₁ * (2 ^ d * 2) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem unpack_packedInfinity (spec : Format) (s : Sign) :
    unpack spec (packedInfinity spec s) = .infinity s := by
  simp [unpack, packedInfinity, unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents, Sign.ofBitVec_toBitVec]

theorem unpack_quietNan (spec : Format) (sp : Bool × Nat) :
    unpack spec (Floats.Gen.quietNan spec sp) = .notANumber := by
  have hne : BitVec.ofNat spec.mantissaBitsWithoutImplicit
      (sp.2 ||| 2 ^ (spec.mantissaBitsWithoutImplicit - 1)) ≠ 0#_ := by
    intro h
    have h1 := congrArg (fun v => v.toNat.testBit (spec.mantissaBitsWithoutImplicit - 1)) h
    have hm := spec.hm
    simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_two_pow_self,
      Nat.zero_testBit] at h1
    simp at h1
    omega
  unfold unpack Floats.Gen.quietNan
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents]
  rw [if_pos trivial, if_neg hne]

end FloatModel.UnpackedFloat

namespace Floats

open FloatModel FloatModel.UnpackedFloat


/-- `Bconv_BofZ`: an integer that is exact in binary64 rounds to binary32 in
the same way directly or through binary64. -/
theorem ofZ_double_repr (z : Int) (hz : Gen.IntRepr Format.binary64 z) :
    Float32.ofZ z = Float.toSingle (Float.ofZ z) := by
  unfold Float32.ofZ Float.toSingle Float.unpack Float.ofZ
  congr 1
  simp only []
  rw [Gen.unpack_ofZ _ _ hz]
  by_cases hz0 : z = 0
  · subst hz0; rfl
  · obtain ⟨s, M, E, hM, K₀, hn, -, -, -, hv⟩ := Gen.normalize_int_form _ z hz hz0
    obtain ⟨h1, h2⟩ := hv K₀ (Nat.le_refl _)
    rw [hn]
    simp only [Gen.convU]
    rw [packOr_round, round_eq_normalize _ _ _ _ hM z K₀ h1 h2]
    rfl

/-- Integers of magnitude at most `2^53` are exact in binary64. -/
theorem repr_le_2p53 (z : Int) (h : z.natAbs ≤ 2 ^ 53) : Gen.IntRepr Format.binary64 z := by
  by_cases hlt : z.natAbs < 2 ^ 53
  · exact Float.repr_n z (by omega)
  · rcases Int.natAbs_eq z with hz | hz
    · exact Float.repr_of_eq z (2 ^ 52) 1 (by omega) (by decide) (by decide)
    · exact Float.repr_of_eq z (-2 ^ 52) 1 (by omega) (by decide) (by decide)

/-- `w` (binary64) is the exact widening of `u` (binary32). -/
def Widens : UnpackedFloat → UnpackedFloat → Prop
  | .notANumber, .notANumber => True
  | .infinity s, .infinity s' => s = s'
  | .zero s, .zero s' => s = s'
  | .finite s m e _, .finite s' M E _ =>
    s = s' ∧ Canon 23 (-149) m e ∧ 2 ^ 52 ≤ M ∧ M < 2 ^ 53 ∧ ∃ j : Nat, M = m <<< j ∧ E = e - j
  | _, _ => False

theorem widens_ofSingle (f : Float32) :
    Widens (unpack Format.binary32 f.bits) (unpack Format.binary64 (Float.ofSingle f).bits) := by
  have hdef : (Float.ofSingle f).bits = Gen.packOr Format.binary64 (Float.ofSingleNan f).bits
      (Gen.convU Format.binary64 (unpack Format.binary32 f.bits)) := rfl
  rw [hdef]
  generalize hx : unpack Format.binary32 f.bits = x
  cases x with
  | notANumber =>
    have hnan : f.isNaN = true := by
      simp only [Float32.isNaN, Gen.isNan, hx, UnpackedFloat.isNaN]
    simp only [Gen.convU, Gen.packOr, Float.ofSingleNan, hnan, if_true]
    simp only [Archi.float_conversion_default_nan, Archi.float_of_single_preserves_sNaN,
      Bool.false_eq_true, if_false, Float.quietNan]
    rw [unpack_quietNan]; trivial
  | infinity sg =>
    simp only [Gen.convU, Gen.packOr, pack]
    rw [unpack_packedInfinity]; rfl
  | zero sg =>
    simp only [Gen.convU, Gen.packOr, pack]
    rw [unpack_packedZero]; rfl
  | finite sg m e hm =>
    have hC := unpack_canon _ _ hx
    obtain ⟨hmb, hlo, hhi⟩ := unpack_finite_bounds _ _ hx
    simp only [Format.mantissaBits, Format.exponentBias] at hmb hlo hhi hC
    have hlog : m.log2 < 24 := (Nat.log2_lt (Nat.ne_of_gt hm)).2 hmb
    obtain ⟨hM, hr⟩ := round_normal Format.binary64 sg m e hm
      (by simp only [Format.mantissaBits]; omega)
      (by simp only [Format.mantissaBits, Format.minExponent]; omega)
    simp only [Gen.convU, hr, Gen.packOr]
    have hlogM : (m <<< (Format.binary64.mantissaBits - 1 - m.log2)).log2 = 52 := by
      rw [log2_shiftLeft _ _ hm]; simp only [Format.mantissaBits]; omega
    rw [unpack_pack_normal _ _ _ _ _
      (by rw [hlogM]; rfl)
      (by simp only [Format.mantissaBits, Format.exponentBias]; omega)
      (by simp only [Format.mantissaBits, Format.exponentBias]; omega)]
    refine ⟨rfl, ?_, ?_, ?_, _, rfl, rfl⟩
    · simpa [Canon] using hC
    · have := Nat.log2_self_le (Nat.ne_of_gt hM); rw [hlogM] at this; exact this
    · have := (Nat.log2_lt (Nat.ne_of_gt hM)).1 (by rw [hlogM]; omega : _ < 53); exact this

theorem lex_widen (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) (M₁ : Nat) (E₁ : Int) (M₂ : Nat)
    (E₂ : Int) (C₁ : Canon 23 (-149) m₁ e₁) (C₂ : Canon 23 (-149) m₂ e₂)
    (h₁ : 2 ^ 52 ≤ M₁ ∧ M₁ < 2 ^ 53) (h₂ : 2 ^ 52 ≤ M₂ ∧ M₂ < 2 ^ 53)
    (j₁ j₂ : Nat) (hM₁ : M₁ = m₁ <<< j₁) (hE₁ : E₁ = e₁ - j₁)
    (hM₂ : M₂ = m₂ <<< j₂) (hE₂ : E₂ = e₂ - j₂) :
    (compare e₁ e₂).then (compare m₁ m₂) = (compare E₁ E₂).then (compare M₁ M₂) := by
  rw [lex_eq_val _ _ _ _ _ _ C₁ C₂,
    lex_eq_val 52 (min E₁ E₂) _ _ _ _ (Or.inl ⟨h₁.1, h₁.2, Int.min_le_left _ _⟩)
      (Or.inl ⟨h₂.1, h₂.2, Int.min_le_right _ _⟩)]
  rw [← valAt_mono (min E₁ E₂) (min e₁ e₂) _ _ _ _ (by omega) (by omega) (by omega)]
  unfold valAt
  subst hM₁ hE₁ hM₂ hE₂
  rw [← Nat.shiftLeft_add, ← Nat.shiftLeft_add]
  congr 3 <;> omega

theorem compare_inf_finite (s s' : Sign) (m : Nat) (e : Int) (h : 0 < m) (M : Nat) (E : Int)
    (H : 0 < M) :
    UnpackedFloat.compare (.infinity s) (.finite s' m e h) =
      UnpackedFloat.compare (.infinity s) (.finite s' M E H) := by
  cases s <;> cases s' <;> rfl

theorem compare_zero_finite (s s' : Sign) (m : Nat) (e : Int) (h : 0 < m) (M : Nat) (E : Int)
    (H : 0 < M) :
    UnpackedFloat.compare (.zero s) (.finite s' m e h) =
      UnpackedFloat.compare (.zero s) (.finite s' M E H) := by
  cases s <;> cases s' <;> rfl

theorem compare_finite_inf (s s' : Sign) (m : Nat) (e : Int) (h : 0 < m) (M : Nat) (E : Int)
    (H : 0 < M) :
    UnpackedFloat.compare (.finite s' m e h) (.infinity s) =
      UnpackedFloat.compare (.finite s' M E H) (.infinity s) := by
  cases s <;> cases s' <;> rfl

theorem compare_finite_zero (s s' : Sign) (m : Nat) (e : Int) (h : 0 < m) (M : Nat) (E : Int)
    (H : 0 < M) :
    UnpackedFloat.compare (.finite s' m e h) (.zero s) =
      UnpackedFloat.compare (.finite s' M E H) (.zero s) := by
  cases s <;> cases s' <;> rfl

theorem compare_finite_congr (s₁ s₂ : Sign) (m₁ : Nat) (e₁ : Int) (h₁ : 0 < m₁) (m₂ : Nat)
    (e₂ : Int) (h₂ : 0 < m₂) (M₁ : Nat) (E₁ : Int) (H₁ : 0 < M₁) (M₂ : Nat) (E₂ : Int)
    (H₂ : 0 < M₂)
    (hl : (compare e₁ e₂).then (compare m₁ m₂) = (compare E₁ E₂).then (compare M₁ M₂)) :
    UnpackedFloat.compare (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) =
      UnpackedFloat.compare (.finite s₁ M₁ E₁ H₁) (.finite s₂ M₂ E₂ H₂) := by
  cases s₁ <;> cases s₂ <;> simp only [UnpackedFloat.compare, hl]

theorem compare_widen (u₁ w₁ u₂ w₂ : UnpackedFloat) (h₁ : Widens u₁ w₁) (h₂ : Widens u₂ w₂) :
    UnpackedFloat.compare u₁ u₂ = UnpackedFloat.compare w₁ w₂ := by
  cases u₁ <;> cases w₁ <;> simp only [Widens] at h₁ <;> cases u₂ <;> cases w₂ <;>
    simp only [Widens] at h₂
  all_goals first
    | (subst_vars; rfl)
    | (obtain ⟨rfl, -⟩ := h₂; subst h₁; apply compare_inf_finite)
    | (obtain ⟨rfl, -⟩ := h₂; subst h₁; apply compare_zero_finite)
    | (obtain ⟨rfl, -⟩ := h₁; subst h₂; apply compare_finite_inf)
    | (obtain ⟨rfl, -⟩ := h₁; subst h₂; apply compare_finite_zero)
    | (obtain ⟨rfl, C₁, a₁, b₁, j₁, rfl, rfl⟩ := h₁
       obtain ⟨rfl, C₂, a₂, b₂, j₂, rfl, rfl⟩ := h₂
       exact compare_finite_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
         (lex_widen _ _ _ _ _ _ _ _ C₁ C₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ j₁ j₂ rfl rfl rfl rfl))

namespace Float32

/-- `Float32.cmp_double` -/
theorem cmp_double (f1 f2 : Float32) (c : Comparison) :
    cmp c f1 f2 = Float.cmp c (toDouble f1) (toDouble f2) := by
  unfold cmp Float.cmp Gen.cmp Gen.compare
  rw [compare_widen _ _ _ _ (widens_ofSingle f1) (widens_ofSingle f2)]
  rfl

/-- `Float32.of_longu_double_1` -/
theorem of_longu_double_1 (n : Integers.Int64) (h : Integers.Int64.unsigned n ≤ 2 ^ 53) :
    ofLongu n = ofDouble (Float.ofLongu n) := by
  apply ofZ_double_repr
  apply repr_le_2p53
  have : 0 ≤ Integers.Int64.unsigned n := Int.natCast_nonneg _
  unfold CC.Z at *
  omega

/-- `Float32.of_long_double_1` -/
theorem of_long_double_1 (n : Integers.Int64) (h : (Integers.Int64.signed n).natAbs ≤ 2 ^ 53) :
    ofLong n = ofDouble (Float.ofLong n) := by
  exact ofZ_double_repr _ (repr_le_2p53 _ h)

/-- The round-to-odd at bit 11 computed by `of_longu_double_2` /
`of_long_double_2`. -/
def roundOdd11 (n : BitVec 64) : BitVec 64 :=
  (n ||| ((n &&& 2047#64) + 2047#64)) &&& BitVec.ofInt 64 (-2048)

theorem roundOdd11_eq (n : Integers.Int64) :
    Integers.Int64.and (Integers.Int64.or n (Integers.Int64.add
      (Integers.Int64.and n (Integers.Int64.repr 2047)) (Integers.Int64.repr 2047)))
      (Integers.Int64.repr (-2048)) = roundOdd11 n := rfl

theorem round_odd_bits (n : BitVec 64) :
    (roundOdd11 n).toNat / 4096 = n.toNat / 4096 ∧
      (n.toNat % 4096 = 0 ↔ (roundOdd11 n).toNat % 4096 = 0) ∧
      (roundOdd11 n).toNat % 2048 = 0 := by
  have F1 : roundOdd11 n >>> 12 = n >>> 12 := by unfold roundOdd11; bv_decide
  have F2 : n &&& 4095#64 = 0#64 → roundOdd11 n &&& 4095#64 = 0#64 := by
    unfold roundOdd11; bv_decide
  have F3 : roundOdd11 n &&& 4095#64 = 0#64 → n &&& 4095#64 = 0#64 := by
    unfold roundOdd11; bv_decide
  have F4 : roundOdd11 n &&& 2047#64 = 0#64 := by unfold roundOdd11; bv_decide
  have hand : ∀ (x : BitVec 64) (k : Nat), k < 64 →
      (x &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
    intro x k hk
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := Nat.pow_lt_pow_right (show 1 < 2 by decide) hk; omega),
      Nat.and_two_pow_sub_one_eq_mod]
  have h4095 : ∀ x : BitVec 64, (x &&& 4095#64).toNat = x.toNat % 4096 := fun x => hand x 12 (by decide)
  have h2047 : ∀ x : BitVec 64, (x &&& 2047#64).toNat = x.toNat % 2048 := fun x => hand x 11 (by decide)
  refine ⟨?_, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have := congrArg BitVec.toNat F1
    simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this
  · have := congrArg BitVec.toNat (F2 (BitVec.eq_of_toNat_eq (by rw [h4095]; simpa using h)))
    rw [h4095] at this; simpa using this
  · have := congrArg BitVec.toNat (F3 (BitVec.eq_of_toNat_eq (by rw [h4095]; simpa using h)))
    rw [h4095] at this; simpa using this
  · have := congrArg BitVec.toNat F4
    rw [h2047] at this; simpa using this

/-- `Float32.of_longu_double_2` -/
theorem of_longu_double_2 (n : Integers.Int64) (h : 2 ^ 36 ≤ Integers.Int64.unsigned n) :
    ofLongu n = ofDouble (Float.ofLongu
      (Integers.Int64.and (Integers.Int64.or n (Integers.Int64.add
        (Integers.Int64.and n (Integers.Int64.repr 2047)) (Integers.Int64.repr 2047)))
        (Integers.Int64.repr (-2048)))) := by
  rw [roundOdd11_eq]
  obtain ⟨hdiv, hlow, h11⟩ := round_odd_bits n
  generalize roundOdd11 n = n' at *
  have hA : n.toNat < 18446744073709551616 := n.isLt
  have hB : n'.toNat < 18446744073709551616 := n'.isLt
  have h36 : 2 ^ 36 ≤ n.toNat := by
    have : Integers.Int64.unsigned n = (n.toNat : Int) := rfl
    unfold CC.Z at h this; omega
  unfold ofDouble Float.ofLongu ofLongu
  rw [← ofZ_double_repr _ (Float.repr_of_eq _ ((n'.toNat / 2048 : Nat) : Int) 11
    (by show (n'.toNat : Int) = _; omega) (by omega) (by decide))]
  unfold ofZ
  congr 1
  show Gen.ofZ _ (Sign.positive.apply ((n.toNat : Nat) : Int)) =
    Gen.ofZ _ (Sign.positive.apply ((n'.toNat : Nat) : Int))
  have eA : n.toNat = (n.toNat / 4096) * 2 ^ 12 + n.toNat % 4096 := by omega
  have eB : n'.toNat = (n.toNat / 4096) * 2 ^ 12 + n'.toNat % 4096 := by omega
  rw [eA, eB]
  exact Gen.ofZ_sticky _ _ _ _ _ _ (by omega) (by omega) (by omega)
    (by simp only [Format.mantissaBits]; omega)

/-- `Float32.of_long_double_2` -/
theorem of_long_double_2 (n : Integers.Int64) (h : 2 ^ 36 ≤ (Integers.Int64.signed n).natAbs) :
    ofLong n = ofDouble (Float.ofLong
      (Integers.Int64.and (Integers.Int64.or n (Integers.Int64.add
        (Integers.Int64.and n (Integers.Int64.repr 2047)) (Integers.Int64.repr 2047)))
        (Integers.Int64.repr (-2048)))) := by
  rw [roundOdd11_eq]
  obtain ⟨hdiv, hlow, h11⟩ := round_odd_bits n
  generalize roundOdd11 n = n' at *
  have hA : n.toNat < 18446744073709551616 := n.isLt
  have hB : n'.toNat < 18446744073709551616 := n'.isLt
  have hsA : Integers.Int64.signed n = n.toInt := rfl
  have hsB : Integers.Int64.signed n' = n'.toInt := rfl
  rw [hsA] at h
  rw [BitVec.toInt_eq_toNat_cond] at h
  unfold ofDouble Float.ofLong ofLong
  rw [hsA, hsB, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp only [Nat.reducePow] at h ⊢
  by_cases hneg : 2 * n.toNat < 18446744073709551616
  · have hneg' : 2 * n'.toNat < 18446744073709551616 := by omega
    rw [if_pos hneg] at h ⊢
    rw [if_pos hneg']
    rw [← ofZ_double_repr _ (Float.repr_of_eq _ ((n'.toNat / 2048 : Nat) : Int) 11
      (by omega) (by omega) (by decide))]
    unfold ofZ
    congr 1
    show Gen.ofZ _ (Sign.positive.apply ((n.toNat : Nat) : Int)) =
      Gen.ofZ _ (Sign.positive.apply ((n'.toNat : Nat) : Int))
    have eA : n.toNat = (n.toNat / 4096) * 2 ^ 12 + n.toNat % 4096 := by omega
    have eB : n'.toNat = (n.toNat / 4096) * 2 ^ 12 + n'.toNat % 4096 := by omega
    rw [eA, eB]
    exact Gen.ofZ_sticky _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by simp only [Format.mantissaBits]; omega)
  · have hneg' : ¬ 2 * n'.toNat < 18446744073709551616 := by omega
    rw [if_neg hneg] at h ⊢
    rw [if_neg hneg']
    rw [← ofZ_double_repr _ (Float.repr_of_eq _ ((n'.toNat / 2048 : Nat) - 9007199254740992 : Int) 11
      (by omega) (by omega) (by decide))]
    unfold ofZ
    congr 1
    by_cases h0 : n.toNat % 4096 = 0
    · have h0' := hlow.1 h0
      have : n.toNat = n'.toNat := by omega
      rw [this]
    · have h0' : n'.toNat % 4096 ≠ 0 := fun h' => h0 (hlow.2 h')
      have eA : (n.toNat : Int) - 18446744073709551616 =
          Sign.negative.apply (((4503599627370495 - n.toNat / 4096) * 2 ^ 12 +
            (4096 - n.toNat % 4096) : Nat) : Int) := by
        simp only [Sign.apply]; omega
      have eB : (n'.toNat : Int) - 18446744073709551616 =
          Sign.negative.apply (((4503599627370495 - n.toNat / 4096) * 2 ^ 12 +
            (4096 - n'.toNat % 4096) : Nat) : Int) := by
        simp only [Sign.apply]; omega
      show Gen.ofZ _ ((n.toNat : Int) - ((18446744073709551616 : Nat) : Int)) =
        Gen.ofZ _ ((n'.toNat : Int) - ((18446744073709551616 : Nat) : Int))
      rw [show ((18446744073709551616 : Nat) : Int) = 18446744073709551616 from rfl, eA, eB]
      exact Gen.ofZ_sticky _ _ _ _ _ _ (by omega) (by omega) (by omega)
        (by simp only [Format.mantissaBits]; omega)

end Float32
end Floats
end CC
