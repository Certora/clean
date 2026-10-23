/-
  Lemmas about the backported IEEE model (`CCLib.lib.FloatModel`).

  * `Format.Valid`, `unpackMantissa_packComponents`, `unpackExponent_packComponents`,
    `valid_pack`: from Lean core (`Init/Data/Float/Model/Format/Valid.lean`,
    `Init/Data/Float/Model/Unpacked/Pack/Lemmas.lean`, Lean ≥ v4.33.0;
    copyright 2026 Lean FRO, LLC, Apache 2.0).
  * `pack_unpack`, `unpack_inj_of_valid`, `unpack_packedNaN`, `isNaN_iff`, … :
    from Batteries (`Batteries/Data/Float/Lemmas.lean`; copyright 2026 Robin
    Arnez, Apache 2.0) — the format-generic part, which does not mention the
    opaque `Float`/`Float32` types.

  Namespaces are moved from `Float.Model` to `CC.FloatModel`; proofs are
  adapted to the v4.32.1 core library where needed.
-/
import CCLib.lib.FloatModel

namespace CC.FloatModel

open UnpackedFloat

/--
Predicate asserting that the bit representation of a float is valid according to the given
format. By 'valid' we mean that `NaN` is encoded using the canonical `NaN`.
-/
structure Format.Valid (spec : Format) (b : BitVec spec.numBits) : Prop where
  /-- If the bit vector encodes a `NaN`, then it is the canonical `NaN`. -/
  eq_packedNaN : unpackExponent b = (-1#_) → unpackMantissa b ≠ 0#_ → b = packedNaN spec

end CC.FloatModel

namespace CC.FloatModel.UnpackedFloat

-- Backport note: replaces `BitVec.zero_eq_neg_one_iff`, which v4.32.1 lacks.
theorem zero_eq_neg_one_iff' {w : Nat} : (0#w = -1#w) ↔ w = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this
    simp at this
    have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have : 2 ^ w = 1 := by omega
    exact (Nat.pow_eq_one.mp this).resolve_left (by decide)
  · rintro rfl; decide

theorem zero_ne_neg_one_exponent (spec : Format) : ¬ (0#spec.exponentBits = -1#_) := by
  rw [zero_eq_neg_one_iff']; have := spec.he; omega

@[simp]
theorem unpackMantissa_packComponents {spec : Format} {sign exponent mantissa} :
    unpackMantissa (packComponents spec sign exponent mantissa) = mantissa := by
  ext i hi
  simp [unpackMantissa, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, hi]

@[simp]
theorem unpackExponent_packComponents {spec : Format} {sign exponent mantissa} :
    unpackExponent (packComponents spec sign exponent mantissa) = exponent := by
  ext i hi
  simp [unpackExponent, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, hi]

@[simp]
theorem valid_pack {spec : Format} {f : UnpackedFloat} : spec.Valid (pack spec f) := by
  refine ⟨?_⟩
  fun_cases pack with
  | case1 => simp
  | case2 s => simp [packedInfinity]
  | case3 s => simp [packedZero]
  | case4 s m e hm biasedExponent h => simp [packedInfinity]
  | case5 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    suffices biasedExponent % 2 ^ spec.exponentBits ≠ 2 ^ spec.exponentBits - 1 by
      simp [BitVec.neg_one_eq_allOnes, ← BitVec.toNat_inj, this]
    suffices biasedExponent < 2 ^ spec.exponentBits - 1 by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    omega
  | case6 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    simp [zero_ne_neg_one_exponent]

end CC.FloatModel.UnpackedFloat

namespace CC.FloatModel.UnpackedFloat

/-- Returns true if the bits represent an NaN value -/
def isNaNBits {spec : Format} (b : BitVec spec.numBits) : Bool :=
  unpackExponent b = -1#_ ∧ unpackMantissa b ≠ 0#_

namespace Sign

@[simp]
theorem ofBitVec_toBitVec (s : Sign) :
    Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

@[simp]
theorem toBitVec_ofBitVec (b : BitVec 1) :
    (Sign.ofBitVec b).toBitVec = b := by
  decide +revert

protected theorem forall_iff {p : Sign → Prop} :
    (∀ s : Sign, p s) ↔ p .positive ∧ p .negative := by
  constructor
  · intro h; simp [h]
  · rintro ⟨h, h'⟩ (_ | _) <;> assumption

instance {p : Sign → Prop} [∀ s, Decidable (p s)] : Decidable (∀ s : Sign, p s) :=
  decidable_of_decidable_of_iff Sign.forall_iff.symm

end Sign

@[simp]
theorem unpackSign_packComponents {spec : Format} (s e m) :
    unpackSign (packComponents spec s e m) = s.toBitVec := by
  ext i (_ | ⟨⟨⟩⟩)
  simp +arith [unpackSign, packComponents, BitVec.getElem_append]
  try rfl

theorem packComponents_unpackSign_unpackExponent_unpackMantissa
    {spec : Format} (b : BitVec spec.numBits) :
    packComponents spec
      (Sign.ofBitVec (unpackSign b)) (unpackExponent b) (unpackMantissa b) = b := by
  simp [packComponents]
  rw [unpackSign, unpackExponent, unpackMantissa]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb',
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
  · exact BitVec.extractLsb'_eq_self
  · simp
  · simp

theorem pack_unpack {spec : Format} (b : BitVec spec.numBits) :
    (unpack spec b).pack spec = if isNaNBits b then packedNaN spec else b := by
  conv => rhs; rw [← packComponents_unpackSign_unpackExponent_unpackMantissa b]
  unfold isNaNBits
  fun_cases unpack with
  | case1 mvec evec svec s hevec hmvec =>
    -- infinity
    simp +zetaDelta [pack, packedInfinity, hmvec, hevec]
  | case2 mvec evec hevec hmvec =>
    -- nan
    simp +zetaDelta [pack, packedNaN, hevec, hmvec]
  | case3 mvec evec svec s _ hevec hmvec =>
    -- zero
    simp +zetaDelta [pack, packedZero, hevec, hmvec]
  | case4 mvec evec e svec s _ hevec hmvec =>
    -- subnormal
    simp only [hevec, unpackExponent_packComponents, zero_ne_neg_one_exponent, unpackMantissa_packComponents, ne_eq, false_and, decide_false,
      Bool.false_eq_true, ↓reduceIte, evec]
    unfold pack
    dsimp -zeta only
    extract_lets mantbits biasedexp
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, mvec]
    rw [if_neg, if_neg]
    · rw [Format.mantissaBits, Nat.add_comm, Nat.add_left_cancel_iff]
      apply Nat.ne_of_lt
      have := mt BitVec.toNat_inj.mp hmvec
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
      simp only [ne_eq, this, not_false_eq_true, Nat.log2_lt, gt_iff_lt, mantbits]
      exact BitVec.isLt _
    · simp +arith [biasedexp, e, hevec]
      have := Nat.pow_le_pow_right (n := 2) (by decide) spec.he
      lia
  | case5 mvec evec e svec s hevec hevec' =>
    -- normal
    simp only [unpackExponent_packComponents, hevec, unpackMantissa_packComponents, ne_eq,
      false_and, decide_false, Bool.false_eq_true, ↓reduceIte, evec]
    unfold pack
    dsimp -zeta only
    extract_lets mantbits biasedexp
    rw [if_neg, if_pos]
    · congr 1
      · simp +arith [biasedexp, e, evec]
      · rw [BitVec.ofNat_toNat, BitVec.setWidth_append]
        simp [mvec]
    · subst mantbits
      have := Nat.two_pow_add_eq_or_of_lt mvec.isLt (a := 1)
      rw [Nat.mul_one] at this
      simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.pow_one, Nat.mod_succ,
        Format.mantissaBits, Nat.add_comm 1, Nat.add_right_cancel_iff,
        Nat.one_shiftLeft, ← this]
      rw [Nat.log2_eq_iff (by simp)]
      simp [Nat.two_pow_succ, mvec.isLt]
    · simp +arith [biasedexp, e]
      simp only [BitVec.neg_one_eq_allOnes, ← BitVec.lt_allOnes_iff, BitVec.lt_def,
        BitVec.toNat_allOnes] at hevec
      lia

theorem pack_unpack_of_valid {spec : Format} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : (unpack spec b).pack spec = b := by
  rw [pack_unpack b]
  simp +contextual [isNaNBits, ← hvalid.eq_packedNaN]

theorem unpack_inj_of_valid {spec : Format} {b b' : BitVec spec.numBits}
    (hb : spec.Valid b) (hb' : spec.Valid b') :
    unpack spec b = unpack spec b' ↔ b = b' := by
  constructor
  · intro h
    replace h := congrArg (pack spec) h
    rwa [pack_unpack_of_valid hb, pack_unpack_of_valid hb'] at h
  · rintro rfl; rfl

theorem isNaNBits_packedNaN {spec : Format} : isNaNBits (packedNaN spec) := by
  simp only [isNaNBits, packedNaN, unpackExponent_packComponents, unpackMantissa_packComponents,
    ne_eq, true_and, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  intro h
  replace h := congrArg (·.getLsbD (spec.mantissaBitsWithoutImplicit - 1)) h
  simp [Nat.sub_one_lt (Nat.ne_of_gt spec.hm)] at h

@[simp]
theorem unpack_packedNaN {spec : Format} : unpack spec (packedNaN spec) = notANumber := by
  have := @isNaNBits_packedNaN spec
  simp only [isNaNBits, decide_eq_true_eq] at this
  simp [unpack, this]

@[simp]
theorem unpack_packedZero {spec : Format} {sign : Sign} :
    unpack spec (packedZero spec sign) = .zero sign := by
  simp [unpack, packedZero, zero_ne_neg_one_exponent]

@[simp]
theorem isNaN_iff : isNaN x ↔ x = notANumber := by
  cases x <;> simp [isNaN]

theorem unpack_eq_notANumber_iff_of_valid {spec : Format} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : unpack spec b = notANumber ↔ b = packedNaN spec := by
  rw [← @unpack_packedNaN spec, unpack_inj_of_valid hvalid ⟨fun _ _ => rfl⟩]

theorem unpack_eq_zero_iff_of_valid {spec : Format} {sign : Sign} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : unpack spec b = zero sign ↔ b = packedZero spec sign := by
  rw [← @unpack_packedZero spec, unpack_inj_of_valid hvalid ⟨by simp [packedZero]⟩]

theorem isNaN_unpack_iff_of_valid {spec : Format} {b : BitVec spec.numBits}
    (hvalid : spec.Valid b) : (unpack spec b).isNaN ↔ b = packedNaN spec := by
  rw [isNaN_iff, unpack_eq_notANumber_iff_of_valid hvalid]

theorem beq_iff_ne_notANumber_and_eq (a b : UnpackedFloat) :
    a.beq b ↔ a ≠ notANumber ∧ b ≠ notANumber ∧
      (a = b ∨ (a = .zero .positive ∧ b = .zero .negative) ∨
        (a = .zero .negative ∧ b = .zero .positive)) := by
  simp only [UnpackedFloat.beq, beq_iff_eq, ne_eq]
  fun_cases UnpackedFloat.compare a b <;> simp_all [eq_comm (α := UnpackedFloat), and_comm] <;>
    rename_i s₁ s₂ <;> revert s₁ s₂ <;> decide

theorem unpack_beq_unpack_iff {spec : Format} {b b' : BitVec spec.numBits}
    (hb : spec.Valid b) (hb' : spec.Valid b') :
    (unpack spec b).beq (unpack spec b') ↔ b ≠ packedNaN spec ∧ b' ≠ packedNaN spec ∧
        (b = b' ∨ (b = packedZero spec .positive ∧ b' = packedZero spec .negative) ∨
          (b = packedZero spec .negative ∧ b' = packedZero spec .positive)) := by
  rw [beq_iff_ne_notANumber_and_eq]
  simp [unpack_eq_notANumber_iff_of_valid, unpack_eq_zero_iff_of_valid, unpack_inj_of_valid, *]

end CC.FloatModel.UnpackedFloat
