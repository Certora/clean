/-
  Theorems of `lib/Floats.v` that express integer-to-float conversions
  through float arithmetic on smaller pieces:
  * `of_intu_of_int_2`, `of_intu_of_int_3` (unsigned 32-bit via signed);
  * `from_words_eq`, `of_intu_from_words`, `of_int_from_words`,
    `from_words_eq'`, `of_longu_from_words`, `of_long_from_words` (the
    PowerPC-style bit tricks with `0x4330_0000` / `0x4530_0000`);
  * `of_longu_decomp`, `of_long_decomp` (64-bit via the 32-bit halves).

  As in Rocq, they follow from `BofZ_plus` / `BofZ_minus` / `BofZ_mult`
  (`CCLib.lib.IEEE754_extra`).  Rocq's `split_bits_or`, `from_words_value`
  and their primed variants are replaced by a direct computation of the bit
  pattern of `ofZ (m · 2^e)` (`ofZ_normal_bits`).
-/
import CCLib.lib.IEEE754_extra
import Std.Tactic.BVDecide

namespace CC
namespace FloatModel.UnpackedFloat

/-- Canonical form of a finite float with `p` mantissa bits after the implicit
bit and least exponent `emin`: normal or subnormal. -/
def Canon (p : Nat) (emin : Int) (m : Nat) (e : Int) : Prop :=
  (2 ^ p ≤ m ∧ m < 2 ^ (p + 1) ∧ emin ≤ e) ∨ (m < 2 ^ p ∧ e = emin)

/-- Unpacked finite floats are in canonical form. -/
theorem unpack_canon (spec : Format) (b : BitVec spec.numBits) {s : Sign} {m : Nat} {e : Int}
    {hm : 0 < m} (h : unpack spec b = .finite s m e hm) :
    Canon spec.mantissaBitsWithoutImplicit
      (1 - (spec.exponentBias + spec.mantissaBitsWithoutImplicit : Int)) m e := by
  unfold unpack at h
  simp only [] at h
  split at h
  · split at h <;> cases h
  · split at h
    · rename_i hE0
      split at h
      · cases h
      · obtain ⟨-, rfl, rfl⟩ := UnpackedFloat.finite.inj h
        right
        refine ⟨(unpackMantissa b).isLt, ?_⟩
        rw [hE0]; simp; omega
    · rename_i hE0
      obtain ⟨-, rfl, rfl⟩ := UnpackedFloat.finite.inj h
      left
      have hE0' : (unpackExponent b).toNat ≠ 0 := by
        intro h0; apply hE0; exact BitVec.eq_of_toNat_eq (by simp [h0])
      have hm := (unpackMantissa b).isLt
      rw [BitVec.toNat_append]
      simp only [BitVec.toNat_ofNat, Nat.pow_one, Nat.one_mod]
      rw [← Nat.shiftLeft_add_eq_or_of_lt hm, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
      refine ⟨by omega, by omega, by omega⟩

end FloatModel.UnpackedFloat

namespace Floats

open FloatModel FloatModel.UnpackedFloat

/-- `ox8000_0000` -/
def ox8000_0000 : Integers.Int := Integers.Int.repr Integers.Int.half_modulus
/-- `ox7FFF_FFFF` -/
def ox7FFF_FFFF : Integers.Int := Integers.Int.repr Integers.Int.max_signed
/-- `ox4330_0000` -/
def ox4330_0000 : Integers.Int := Integers.Int.repr 1127219200
/-- `ox4530_0000` -/
def ox4530_0000 : Integers.Int := Integers.Int.repr 1160773632

namespace Float

/-- Integers of at most 53 bits are represented exactly in binary64
(`integer_representable_n`). -/
theorem repr_n (z : Int) (h : -2 ^ 53 < z ∧ z < 2 ^ 53) : Gen.IntRepr Format.binary64 z :=
  Gen.intRepr_n _ (by decide) z (by simp only [Format.mantissaBits]; omega)

/-- `integer_representable_n2p` for binary64. -/
theorem repr_n2p (n : Int) (p : Nat) (h : -2 ^ 53 < n ∧ n < 2 ^ 53) (hp : p ≤ 971) :
    Gen.IntRepr Format.binary64 (n * 2 ^ p) :=
  Gen.intRepr_n2p _ n p (by simp only [Format.mantissaBits]; omega)
    (by simp only [Format.mantissaBits, Format.exponentBias]; omega)

theorem ofZ_add (p q : Int) (hp : Gen.IntRepr Format.binary64 p) (hq : Gen.IntRepr Format.binary64 q) :
    add (ofZ p) (ofZ q) = ofZ (p + q) :=
  congrArg Float.mk (Gen.ofZ_plus _ p q hp hq)

theorem ofZ_sub (p q : Int) (hp : Gen.IntRepr Format.binary64 p) (hq : Gen.IntRepr Format.binary64 q) :
    sub (ofZ p) (ofZ q) = ofZ (p - q) :=
  congrArg Float.mk (Gen.ofZ_minus _ p q hp hq)

theorem ofZ_mul (p q : Int) (hp : Gen.IntRepr Format.binary64 p) (hq : Gen.IntRepr Format.binary64 q)
    (hq0 : 0 < q) :
    mul (ofZ p) (ofZ q) = ofZ (p * q) :=
  congrArg Float.mk (Gen.ofZ_mult _ p q hp hq hq0)

theorem unsigned_range (x : Integers.Int) :
    0 ≤ Integers.Int.unsigned x ∧ Integers.Int.unsigned x < 4294967296 := by
  have : x.toNat < 4294967296 := x.isLt
  show (0 : _root_.Int) ≤ x.toNat ∧ (x.toNat : _root_.Int) < 4294967296
  omega

theorem signed_range (x : Integers.Int) :
    -2147483648 ≤ Integers.Int.signed x ∧ Integers.Int.signed x < 2147483648 := by
  show (-2147483648 : _root_.Int) ≤ x.toInt ∧ x.toInt < (2147483648 : _root_.Int)
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  simp at h1 h2
  omega

theorem repr_of_eq (z n : Int) (p : Nat) (hz : z = n * 2 ^ p) (h : -2 ^ 53 < n ∧ n < 2 ^ 53)
    (hp : p ≤ 971) : Gen.IntRepr Format.binary64 z := hz ▸ repr_n2p n p h hp

theorem ox8000_0000_eq : ox8000_0000 = 2147483648#32 := by decide
theorem ox7FFF_FFFF_eq : ox7FFF_FFFF = 2147483647#32 := by decide

theorem unsigned_ox8000_0000 : Integers.Int.unsigned ox8000_0000 = 2147483648 := by decide
theorem signed_ox8000_0000 : Integers.Int.signed ox8000_0000 = -2147483648 := by decide

theorem signed_sub_ox8000_0000 (x : Integers.Int) (h : Integers.Int.ltu x ox8000_0000 = false) :
    Integers.Int.signed (Integers.Int.sub x ox8000_0000) =
      Integers.Int.unsigned x - 2147483648 := by
  simp only [Integers.Int.ltu, Integers.MI.ltu, ox8000_0000_eq, Integers.Int.signed,
    Integers.MI.signed, Integers.Int.sub, Integers.MI.sub, Integers.Int.unsigned,
    Integers.MI.unsigned, BitVec.ult] at *
  simp only [decide_eq_false_iff_not, Nat.not_lt, BitVec.toNat_ofNat] at h
  have hsub : (x - 2147483648#32).toNat = x.toNat - 2147483648 := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]; simp
  rw [BitVec.toInt_eq_toNat_cond, hsub]
  have : x.toNat < 4294967296 := x.isLt
  unfold CC.Z
  simp only [Nat.reducePow]
  split <;> omega

/-- `Float.of_intu_of_int_2` -/
theorem of_intu_of_int_2 (x : Integers.Int) (h : Integers.Int.ltu x ox8000_0000 = false) :
    ofIntu x = add (ofInt (Integers.Int.sub x ox8000_0000)) (ofIntu ox8000_0000) := by
  have hx := unsigned_range x
  have hs := signed_sub_ox8000_0000 x h
  unfold ofIntu ofInt
  rw [ofZ_add, hs, unsigned_ox8000_0000]
  · congr 1; unfold CC.Z at *; omega
  · apply repr_n; rw [hs]; unfold CC.Z at *; omega
  · apply repr_n; rw [unsigned_ox8000_0000]; decide

theorem and_ox_split (x : Integers.Int) :
    (Integers.Int.and x ox7FFF_FFFF).toNat = x.toNat % 2147483648 ∧
    (Integers.Int.and x ox8000_0000 = 0#32 ∨ Integers.Int.and x ox8000_0000 = 2147483648#32) ∧
    (Integers.Int.and x ox8000_0000) + (Integers.Int.and x ox7FFF_FFFF) = x := by
  simp only [Integers.Int.and, Integers.MI.and, ox8000_0000_eq, ox7FFF_FFFF_eq]
  refine ⟨?_, by bv_decide, by bv_decide⟩
  rw [BitVec.toNat_and, show (2147483647#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- `Float.of_intu_of_int_3` -/
theorem of_intu_of_int_3 (x : Integers.Int) :
    ofIntu x = sub (ofInt (Integers.Int.and x ox7FFF_FFFF)) (ofInt (Integers.Int.and x ox8000_0000)) := by
  obtain ⟨hlo, hhi, hsum⟩ := and_ox_split x
  generalize Integers.Int.and x ox7FFF_FFFF = lo at *
  generalize Integers.Int.and x ox8000_0000 = hi at *
  have hlos : Integers.Int.signed lo = (lo.toNat : Int) := by
    simp only [Integers.Int.signed, Integers.MI.signed]
    rw [BitVec.toInt_eq_toNat_cond, if_pos (by omega)]
  have hl := signed_range lo
  have hh := signed_range hi
  unfold ofIntu ofInt
  rw [ofZ_sub _ _ (repr_n _ (by unfold CC.Z at *; omega)) (repr_n _ (by unfold CC.Z at *; omega))]
  congr 1
  subst hsum
  rcases hhi with rfl | rfl
  · simp only [Integers.Int.unsigned, Integers.MI.unsigned, BitVec.zero_add, hlos]
    show _ = _ - (0 : Int)
    unfold CC.Z; omega
  · have h1 : (2147483648#32 + lo).toNat = 2147483648 + lo.toNat := by
      rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
    simp only [Integers.Int.unsigned, Integers.MI.unsigned, h1, hlos]
    show _ = _ - Integers.Int.signed ox8000_0000
    rw [signed_ox8000_0000]
    unfold CC.Z; omega

/-- The bit pattern of a normal binary64 float `m · 2^e` with an integer value. -/
theorem ofZ_normal_bits (m e : Nat) (hm1 : 2 ^ 52 ≤ m) (hm2 : m < 2 ^ 53) (he : e ≤ 971) :
    ofZ ((m : Int) * 2 ^ e) =
      ⟨packComponents Format.binary64 .positive (BitVec.ofNat 11 (1075 + e)) (BitVec.ofNat 52 m)⟩ := by
  have hm : 0 < m := by omega
  have hlog : m.log2 = 52 := by
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.log2_lt (by omega)).2 hm2)
    · exact (Nat.le_log2 (by omega)).2 hm1
  unfold ofZ Gen.ofZ
  have h1 : ((m : Int) * 2 ^ e) = Sign.positive.apply ((m <<< e : Nat) : Int) := by
    simp [Sign.apply, Nat.shiftLeft_eq]
  rw [h1, normalize_apply _ _ _ _ _ (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hm (Nat.two_pow_pos _))]
  have h2 := round_shift Format.binary64 .positive m e e hm
  simp only [Int.sub_self] at h2
  rw [h2, round_exact _ _ _ _ hm (by
    simp only [Format.targetExponent, totalExponent, hlog, Format.mantissaBits, Format.minExponent]
    omega)]
  apply congrArg Float.mk
  unfold pack
  simp only [hlog, Format.exponentBias, Format.mantissaBits]
  rw [if_neg (by omega), if_pos (by decide)]
  congr 2
  omega

theorem ofwords_toNat (hi lo : Integers.Int) :
    (Integers.Int64.ofwords hi lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  have h1 := hi.isLt
  have h2 := lo.isLt
  unfold Integers.Int64.ofwords
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h2, Nat.shiftLeft_eq]

theorem packComponents_toNat (e : Nat) (m : Nat) (he : e < 2 ^ 11) :
    (packComponents Format.binary64 .positive (BitVec.ofNat 11 e) (BitVec.ofNat 52 m)).toNat =
      e * 2 ^ 52 + m % 2 ^ 52 := by
  unfold packComponents
  rw [BitVec.toNat_append, BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Sign.toBitVec]
  rw [Nat.mod_eq_of_lt he]
  simp only [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)),
    Nat.shiftLeft_eq]

/-- `Float.from_words_eq` -/
theorem from_words_eq (x : Integers.Int) :
    fromWords ox4330_0000 x = ofZ (2 ^ 52 + Integers.Int.unsigned x) := by
  have hx := x.isLt
  have h := ofZ_normal_bits (2 ^ 52 + x.toNat) 0 (by omega) (by omega) (by omega)
  simp only [Int.pow_zero, Int.mul_one] at h
  have h' : (2 ^ 52 + Integers.Int.unsigned x : Z) = (((2 ^ 52 + x.toNat : Nat)) : Int) := by
    simp [Integers.Int.unsigned, Integers.MI.unsigned]
  rw [h', h]
  unfold fromWords ofBits
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [ofwords_toNat, packComponents_toNat _ _ (by decide)]
  have : ox4330_0000.toNat = 1127219200 := by decide
  rw [this]
  omega

/-- `Float.of_intu_from_words` -/
theorem of_intu_from_words (x : Integers.Int) :
    ofIntu x = sub (fromWords ox4330_0000 x) (fromWords ox4330_0000 Integers.Int.zero) := by
  have hx := unsigned_range x
  have h0 : Integers.Int.unsigned Integers.Int.zero = 0 := by decide
  rw [from_words_eq, from_words_eq, h0, ofZ_sub]
  · unfold ofIntu; congr 1; unfold CC.Z at *; omega
  · apply repr_n; unfold CC.Z at *; omega
  · apply repr_n; decide

/-- `Float.ox8000_0000_signed_unsigned` -/
theorem ox8000_0000_signed_unsigned (x : Integers.Int) :
    Integers.Int.unsigned (Integers.Int.add x ox8000_0000) =
      Integers.Int.signed x + Integers.Int.half_modulus := by
  have hx : x.toNat < 4294967296 := x.isLt
  have hh : Integers.Int.half_modulus = 2147483648 := by decide
  rw [hh]
  simp only [Integers.Int.unsigned, Integers.MI.unsigned, Integers.Int.signed, Integers.MI.signed,
    Integers.Int.add, Integers.MI.add, ox8000_0000_eq]
  rw [BitVec.toNat_add, BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  unfold CC.Z
  split <;> omega

/-- `Float.of_int_from_words` -/
theorem of_int_from_words (x : Integers.Int) :
    ofInt x = sub (fromWords ox4330_0000 (Integers.Int.add x ox8000_0000))
                  (fromWords ox4330_0000 ox8000_0000) := by
  have hx := signed_range x
  have hh : Integers.Int.half_modulus = 2147483648 := by decide
  rw [from_words_eq, from_words_eq, ox8000_0000_signed_unsigned, unsigned_ox8000_0000, hh, ofZ_sub]
  · unfold ofInt; congr 1; unfold CC.Z at *; omega
  · apply repr_n; unfold CC.Z at *; omega
  · apply repr_n; decide

/-- `Float.from_words_eq'` -/
theorem from_words_eq' (x : Integers.Int) :
    fromWords ox4530_0000 x = ofZ (2 ^ 84 + Integers.Int.unsigned x * 2 ^ 32) := by
  have hx := x.isLt
  have h := ofZ_normal_bits (2 ^ 52 + x.toNat) 32 (by omega) (by omega) (by omega)
  have h' : (2 ^ 84 + Integers.Int.unsigned x * 2 ^ 32 : Z) = (((2 ^ 52 + x.toNat : Nat)) : Int) * 2 ^ 32 := by
    simp only [Integers.Int.unsigned, Integers.MI.unsigned]
    unfold CC.Z
    simp only [Int.reducePow]
    omega
  rw [h', h]
  unfold fromWords ofBits
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [ofwords_toNat, packComponents_toNat _ _ (by decide)]
  have : ox4530_0000.toNat = 1160773632 := by decide
  rw [this]
  omega

theorem unsigned_decomp (l : Integers.Int64) :
    Integers.Int64.unsigned l =
      Integers.Int.unsigned (Integers.Int64.hiword l) * 2 ^ 32 +
        Integers.Int.unsigned (Integers.Int64.loword l) := by
  have hl : l.toNat < 18446744073709551616 := l.isLt
  simp only [Integers.Int64.unsigned, Integers.MI.unsigned, Integers.Int.unsigned,
    Integers.Int64.hiword, Integers.Int64.loword, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  unfold CC.Z
  simp only [Int.reducePow, Nat.reducePow]
  omega

theorem signed_decomp (l : Integers.Int64) :
    Integers.Int64.signed l =
      Integers.Int.signed (Integers.Int64.hiword l) * 2 ^ 32 +
        Integers.Int.unsigned (Integers.Int64.loword l) := by
  have hl : l.toNat < 18446744073709551616 := l.isLt
  simp only [Integers.Int64.signed, Integers.MI.signed, Integers.Int.signed, Integers.MI.unsigned,
    Integers.Int.unsigned, Integers.Int64.hiword, Integers.Int64.loword]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  unfold CC.Z
  simp only [Int.reducePow, Nat.reducePow]
  split <;> split <;> omega

/-- `omega` for goals stated over `Z` with literal powers of two. -/
local macro "zomega" : tactic =>
  `(tactic| (unfold CC.Z at *; (try simp only [Int.reducePow] at *); omega))

theorem unsigned_two_p_20 : Integers.Int.unsigned (Integers.Int.repr (2 ^ 20)) = 1048576 := by decide
theorem unsigned_two_p_20_31 :
    Integers.Int.unsigned (Integers.Int.repr (2 ^ 20 + 2 ^ 31)) = 2148532224 := by decide

/-- `Float.of_longu_from_words` -/
theorem of_longu_from_words (l : Integers.Int64) :
    ofLongu l =
      add (sub (fromWords ox4530_0000 (Integers.Int64.hiword l))
               (fromWords ox4530_0000 (Integers.Int.repr (2 ^ 20))))
          (fromWords ox4330_0000 (Integers.Int64.loword l)) := by
  have hd := unsigned_decomp l
  have hh := unsigned_range (Integers.Int64.hiword l)
  have hl := unsigned_range (Integers.Int64.loword l)
  rw [from_words_eq', from_words_eq', from_words_eq, unsigned_two_p_20]
  generalize Integers.Int.unsigned (Integers.Int64.hiword l) = xh at *
  generalize Integers.Int.unsigned (Integers.Int64.loword l) = xl at *
  rw [ofZ_sub _ _ (repr_of_eq _ (2 ^ 52 + xh) 32 (by zomega) (by zomega) (by decide))
      (repr_of_eq _ (2 ^ 52 + 1048576) 32 (by zomega) (by decide) (by decide)),
    ofZ_add _ _ (repr_of_eq _ (xh - 1048576) 32 (by zomega) (by zomega) (by decide))
      (repr_n _ (by zomega))]
  unfold ofLongu
  congr 1
  zomega

/-- `Float.of_long_from_words` -/
theorem of_long_from_words (l : Integers.Int64) :
    ofLong l =
      add (sub (fromWords ox4530_0000 (Integers.Int.add (Integers.Int64.hiword l) ox8000_0000))
               (fromWords ox4530_0000 (Integers.Int.repr (2 ^ 20 + 2 ^ 31))))
          (fromWords ox4330_0000 (Integers.Int64.loword l)) := by
  have hd := signed_decomp l
  have hh := signed_range (Integers.Int64.hiword l)
  have hl := unsigned_range (Integers.Int64.loword l)
  have hm : Integers.Int.half_modulus = 2147483648 := by decide
  rw [from_words_eq', from_words_eq', from_words_eq, unsigned_two_p_20_31,
    ox8000_0000_signed_unsigned, hm]
  generalize Integers.Int.signed (Integers.Int64.hiword l) = xh at *
  generalize Integers.Int.unsigned (Integers.Int64.loword l) = xl at *
  rw [ofZ_sub _ _ (repr_of_eq _ (2 ^ 52 + xh + 2147483648) 32 (by zomega) (by zomega) (by decide))
      (repr_of_eq _ (2 ^ 52 + 2148532224) 32 (by zomega) (by decide) (by decide)),
    ofZ_add _ _ (repr_of_eq _ (xh - 1048576) 32 (by zomega) (by zomega) (by decide))
      (repr_n _ (by zomega))]
  unfold ofLong
  congr 1
  zomega

/-- `Float.of_longu_decomp` -/
theorem of_longu_decomp (l : Integers.Int64) :
    ofLongu l = add (mul (ofIntu (Integers.Int64.hiword l)) (ofZ (2 ^ 32)))
                    (ofIntu (Integers.Int64.loword l)) := by
  have hd := unsigned_decomp l
  have hh := unsigned_range (Integers.Int64.hiword l)
  have hl := unsigned_range (Integers.Int64.loword l)
  unfold ofIntu ofLongu
  generalize Integers.Int.unsigned (Integers.Int64.hiword l) = xh at *
  generalize Integers.Int.unsigned (Integers.Int64.loword l) = xl at *
  rw [ofZ_mul _ _ (repr_n _ (by zomega)) (repr_n _ (by decide)) (by decide),
    ofZ_add _ _ (repr_of_eq _ xh 32 rfl (by zomega) (by decide)) (repr_n _ (by zomega))]
  congr 1

/-- `Float.of_long_decomp` -/
theorem of_long_decomp (l : Integers.Int64) :
    ofLong l = add (mul (ofInt (Integers.Int64.hiword l)) (ofZ (2 ^ 32)))
                   (ofIntu (Integers.Int64.loword l)) := by
  have hd := signed_decomp l
  have hh := signed_range (Integers.Int64.hiword l)
  have hl := unsigned_range (Integers.Int64.loword l)
  unfold ofInt ofIntu ofLong
  generalize Integers.Int.signed (Integers.Int64.hiword l) = xh at *
  generalize Integers.Int.unsigned (Integers.Int64.loword l) = xl at *
  rw [ofZ_mul _ _ (repr_n _ (by zomega)) (repr_n _ (by decide)) (by decide),
    ofZ_add _ _ (repr_of_eq _ xh 32 rfl (by zomega) (by decide)) (repr_n _ (by zomega))]
  congr 1

theorem unpack_ofIntu_ox8000_0000 :
    unpack (ofIntu ox8000_0000) = .finite .positive (2 ^ 52) (-21) (by decide) := by
  rfl

theorem toIntu_inv (x : Float) (n : Integers.Int) (h : toIntu x = some n) :
    ∃ z : Int, Gen.toZ Format.binary64 x.bits = some z ∧ 0 ≤ z ∧ z ≤ 4294967295 ∧
      n = Integers.Int.repr z := by
  simp only [toIntu, Option.map_eq_some_iff, Gen.toZRange_eq_some] at h
  obtain ⟨z, ⟨h1, h2, h3⟩, rfl⟩ := h
  exact ⟨z, h1, h2, by have : Integers.Int.max_unsigned = 4294967295 := by decide
                       rw [this] at h3; exact h3, rfl⟩

/-- `Float.to_intu_to_int_1` -/
theorem to_intu_to_int_1 (x : Float) (n : Integers.Int)
    (hc : cmp .Clt x (ofIntu ox8000_0000) = true) (h : toIntu x = some n) :
    toInt x = some n := by
  obtain ⟨z, hz, h0, h1, rfl⟩ := toIntu_inv x n h
  have hlt : z ≤ 2147483647 := by
    unfold cmp Gen.cmp Gen.compare at hc
    rw [show UnpackedFloat.unpack Format.binary64 (ofIntu ox8000_0000).bits = .finite .positive (2 ^ 52) (-21)
      (by decide) from unpack_ofIntu_ox8000_0000] at hc
    unfold Gen.toZ at hz
    revert hc hz
    cases hx : UnpackedFloat.unpack Format.binary64 x.bits with
    | zero sg => intro _ hz; simp at hz; omega
    | infinity sg => intro _ hz; simp at hz
    | notANumber => intro _ hz; simp at hz
    | finite sg m e hm =>
      intro hc hz
      obtain ⟨hmb, -, -⟩ := unpack_finite_bounds _ _ hx
      simp only [Format.mantissaBits] at hmb
      rw [Option.some.injEq] at hz
      cases sg with
      | negative =>
        change -(_ : Int) = z at hz
        have := Int.natCast_nonneg (m <<< e.toNat)
        have := Int.natCast_nonneg (m >>> e.natAbs)
        split at hz <;> omega
      | positive =>
        have key : ∀ o : Ordering, cmpOfComparison .Clt (some o) = true → o = .lt := by
          intro o; cases o <;> simp [cmpOfComparison]
        have hc' := key _ hc
        have he : e < -21 ∨ (e = -21 ∧ m < 2 ^ 52) := by
          rcases Int.lt_trichotomy e (-21) with h' | h' | h'
          · exact Or.inl h'
          · subst h'
            right
            rw [Int.compare_eq_eq.2 rfl] at hc'
            exact ⟨rfl, Nat.compare_eq_lt.1 hc'⟩
          · rw [Int.compare_eq_gt.2 h'] at hc'
            exact absurd hc' (by simp [Ordering.then])
        simp only [Sign.apply] at hz
        rw [if_neg (by omega)] at hz
        subst hz
        rw [Nat.shiftRight_eq_div_pow]
        rcases he with he | ⟨rfl, hm'⟩
        · have : 2 ^ 22 ≤ 2 ^ e.natAbs := Nat.pow_le_pow_right (by decide) (by omega)
          have h2 : m / 2 ^ e.natAbs ≤ m / 2 ^ 22 := Nat.div_le_div_left this (by decide)
          have h3 : m / 2 ^ 22 < 2 ^ 31 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
          omega
        · have h3 : m / 2 ^ 21 < 2 ^ 31 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
          simp only [show (-21 : Int).natAbs = 21 from rfl]
          omega
  simp only [toInt, Option.map_eq_some_iff, Gen.toZRange_eq_some]
  refine ⟨z, ⟨hz, ?_, ?_⟩, rfl⟩
  · have : Integers.Int.min_signed = -2147483648 := by decide
    rw [this]; omega
  · have : Integers.Int.max_signed = 2147483647 := by decide
    rw [this]; omega

theorem repr_sub_ox8000_0000 (z : Int) :
    Integers.Int.repr (z - 2147483648) = Integers.Int.sub (Integers.Int.repr z) ox8000_0000 := by
  rw [ox8000_0000_eq]
  simp only [Integers.Int.repr, Integers.MI.repr, Integers.Int.sub, Integers.MI.sub]
  apply BitVec.eq_sub_iff_add_eq.2
  rw [show (2147483648#32) = BitVec.ofInt 32 2147483648 from rfl, ← BitVec.ofInt_add]
  congr 1
  omega

/-- `Float.to_intu_to_int_2` -/
theorem to_intu_to_int_2 (x : Float) (n : Integers.Int)
    (hc : cmp .Clt x (ofIntu ox8000_0000) = false) (h : toIntu x = some n) :
    toInt (sub x (ofIntu ox8000_0000)) = some (Integers.Int.sub n ox8000_0000) := by
  obtain ⟨z, hz, h0, h1, rfl⟩ := toIntu_inv x n h
  have hy : UnpackedFloat.unpack Format.binary64 (ofIntu ox8000_0000).bits =
      .finite .positive (2 ^ 52) (-21) (by decide) := unpack_ofIntu_ox8000_0000
  unfold cmp Gen.cmp Gen.compare at hc
  rw [hy] at hc
  have hsub : (sub x (ofIntu ox8000_0000)).bits =
      Gen.packOr Format.binary64 (Gen.binopNan nanConfig x.bits (ofIntu ox8000_0000).bits)
        (UnpackedFloat.sub Format.binary64 (UnpackedFloat.unpack Format.binary64 x.bits)
          (.finite .positive (2 ^ 52) (-21) (by decide))) := by
    rw [← hy]; rfl
  simp only [toInt, Option.map_eq_some_iff, Gen.toZRange_eq_some]
  refine ⟨z - 2147483648, ?_, (repr_sub_ox8000_0000 z)⟩
  have hmin : Integers.Int.min_signed = -2147483648 := by decide
  have hmax : Integers.Int.max_signed = 2147483647 := by decide
  rw [hmin, hmax, hsub]
  unfold Gen.toZ at hz
  revert hc hz
  cases hx : UnpackedFloat.unpack Format.binary64 x.bits with
  | zero sg => intro hc; simp [UnpackedFloat.compare, cmpOfComparison] at hc
  | infinity sg => intro _ hz; simp at hz
  | notANumber => intro _ hz; simp at hz
  | finite sg m e hm =>
    intro hc hz
    rw [Option.some.injEq] at hz
    cases sg with
    | negative => simp [UnpackedFloat.compare, cmpOfComparison] at hc
    | positive =>
      have key : ∀ o : Ordering, cmpOfComparison .Clt (some o) = false → o ≠ .lt := by
        intro o; cases o <;> simp [cmpOfComparison]
      have hc' := key _ hc
      have he : -21 < e ∨ (e = -21 ∧ 2 ^ 52 ≤ m) := by
        rcases Int.lt_trichotomy e (-21) with h' | h' | h'
        · rw [Int.compare_eq_lt.2 h'] at hc'
          exact absurd rfl hc'
        · subst h'
          right
          rw [Int.compare_eq_eq.2 rfl] at hc'
          refine ⟨rfl, Nat.not_lt.1 fun hlt => hc' (Nat.compare_eq_lt.2 hlt)⟩
        · exact Or.inl h'
      have hC := unpack_canon _ _ hx
      obtain ⟨hmb, -, -⟩ := unpack_finite_bounds _ _ hx
      simp only [Format.mantissaBits, Format.exponentBias] at hmb hC
      have hm52 : 2 ^ 52 ≤ m := by
        rcases hC with hC | hC
        · exact hC.1
        · omega
      change ((if 0 ≤ e then ((m <<< e.toNat : Nat) : Int) else ((m >>> e.natAbs : Nat) : Int))) = z
        at hz
      have he21 : e = -21 := by
        apply Classical.byContradiction
        intro hne
        have hge : -20 ≤ e := by omega
        split at hz
        · have : 2 ^ 52 ≤ m <<< e.toNat := by
            rw [Nat.shiftLeft_eq]; exact Nat.le_trans hm52 (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
          omega
        · rw [Nat.shiftRight_eq_div_pow] at hz
          have h2 : 2 ^ e.natAbs ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) (by omega)
          have h3 : m / 2 ^ 20 ≤ m / 2 ^ e.natAbs := Nat.div_le_div_left h2 (Nat.two_pow_pos _)
          have h4 : 2 ^ 32 ≤ m / 2 ^ 20 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
          omega
      subst he21
      rw [if_neg (by decide), Nat.shiftRight_eq_div_pow] at hz
      simp only [show (-21 : Int).natAbs = 21 from rfl] at hz
      obtain ⟨N, rfl⟩ : ∃ N, m = 2 ^ 52 + N := ⟨m - 2 ^ 52, by omega⟩
      have hzN : z = 2147483648 + ((N / 2 ^ 21 : Nat) : Int) := by
        rw [← hz, show 2 ^ 52 + N = N + 2 ^ 21 * 2 ^ 31 by omega, Nat.add_mul_div_left _ _ (by decide)]
        omega
      rw [sub_finite _ _ _ _ _ _ _ _ _ (-21) (Int.le_refl _) (Int.le_refl _)]
      simp only [Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero, Sign.apply]
      rw [Gen.packOr_normalize]
      have hN : ((2 ^ 52 + N : Nat) : Int) - ((2 ^ 52 : Nat) : Int) = Sign.positive.apply (N : Int) := by
        simp [Sign.apply] <;> omega
      rw [hN]
      by_cases hN0 : N = 0
      · subst hN0
        simp only [Nat.zero_div, Int.natCast_zero, Int.add_zero] at hzN
        subst hzN
        refine ⟨?_, by decide, by decide⟩
        rfl
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
        rw [normalize_apply _ _ _ _ _ hNpos]
        have hlog : N.log2 < 52 := (Nat.log2_lt hN0).2 (by omega)
        obtain ⟨hM, hr⟩ := round_normal Format.binary64 .positive N (-21) hNpos
          (by simp only [Format.mantissaBits]; omega)
          (by simp only [Format.mantissaBits, Format.minExponent]; omega)
        unfold Gen.toZ
        rw [hr, unpack_pack_normal _ _ _ _ _
          (by rw [log2_shiftLeft _ _ hNpos]; simp only [Format.mantissaBits]; omega)
          (by simp only [Format.mantissaBits, Format.exponentBias]; omega)
          (by simp only [Format.mantissaBits, Format.exponentBias]; omega)]
        have ht := truncZ_shift .positive N (Format.binary64.mantissaBits - 1 - N.log2) (-21)
        unfold truncZ at ht
        refine ⟨?_, ?_, ?_⟩
        · change some (Sign.positive.apply _) = _
          rw [ht]
          simp only [Sign.apply, show ¬ (0 : Int) ≤ -21 from by decide, if_false,
            Nat.shiftRight_eq_div_pow, show (-21 : Int).natAbs = 21 from rfl]
          rw [hzN]; congr 1; omega
        · omega
        · have : N / 2 ^ 21 < 2 ^ 31 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
          omega

end Float
end Floats
end CC
