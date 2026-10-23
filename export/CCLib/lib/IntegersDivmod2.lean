/-
  Double-width division (`divmodu2`, `divmods2`, used by the x86 `div` /
  `idiv` instructions) — port of the theorems `divmodu2_divu_modu` and
  `divmods2_divs_mods` of `lib/Integers.v`, for every word size and for the
  `Int` / `Int64` instances, together with `shr_lt_zero`.
-/
import CCLib.lib.IntegersLemmas

namespace CC
namespace Integers

namespace MI
variable {w : Nat}

/-- `Int.divmodu2_divu_modu` -/
theorem divmodu2_divu_modu (n d : BitVec w) (hd : d ≠ zero) :
    divmodu2 zero n d = some (divu n d, modu n d) := by
  unfold divmodu2
  rw [if_neg hd]
  have h1 : n.toNat / d.toNat < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) n.isLt
  have h2 : n.toNat % d.toNat < 2 ^ w := Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt
  have hq : ((n.toNat / d.toNat : Nat) : _root_.Int) ≤ max_unsigned w := by
    simp only [max_unsigned, modulus]
    have : ((2 : _root_.Int) ^ w) = ((2 ^ w : Nat) : _root_.Int) := by simp
    omega
  have e : unsigned (zero : BitVec w) * modulus w + unsigned n = (n.toNat : _root_.Int) := by
    simp [unsigned, zero]
  dsimp only
  rw [e, unsigned, ← _root_.Int.natCast_ediv, ← _root_.Int.natCast_emod, if_pos hq]
  simp only [repr, divu, modu]
  congr 2
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, BitVec.toNat_ofInt, ← _root_.Int.natCast_emod, _root_.Int.toNat_natCast]
    exact Nat.mod_eq_of_lt h1
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, BitVec.toNat_ofInt, ← _root_.Int.natCast_emod, _root_.Int.toNat_natCast]
    exact Nat.mod_eq_of_lt h2

/-- `repr min_signed` is the most negative bit vector. -/
theorem repr_min_signed_eq_intMin (hw : 0 < w) :
    (repr (min_signed w) : BitVec w) = BitVec.intMin w := by
  apply BitVec.eq_of_toInt_eq
  have hm := half_modulus_pos hw
  have h := signed_repr hw (z := min_signed w) (Int.le_refl _)
    (by unfold min_signed max_signed; zomega)
  rw [signed_toInt] at h
  rw [h, BitVec.toInt_intMin, min_signed_eq, half_modulus_eq hw,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega)), _root_.Int.natCast_pow]
  rfl

/-- The sign extension of `n` (high word) followed by `n` (low word) denotes
    `signed n`. -/
theorem signed_sign_ext_mul_add (hw : 0 < w) (n : BitVec w) :
    signed (if lt n zero then mone else zero : BitVec w) * modulus w + unsigned n = signed n := by
  have hs := signed_eq hw n
  have hr := unsigned_range n
  have hlt : lt n zero = decide (signed n < 0) := by
    simp only [lt, zero, signed]
    rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt]
    simp
  rw [hlt]
  by_cases h : signed n < 0
  · rw [decide_eq_true h, if_pos rfl]
    have : signed (mone : BitVec w) = -1 := by
      rw [signed_toInt, mone, BitVec.toInt_allOnes, if_pos hw]
    rw [this]
    split at hs <;> zomega
  · rw [decide_eq_false h]
    have : signed (zero : BitVec w) = 0 := by simp [signed, zero]
    simp only [Bool.false_eq_true, if_false, this]
    split at hs <;> zomega

/-- `Int.divmods2_divs_mods` -/
theorem divmods2_divs_mods (hw : 0 < w) (n d : BitVec w) (hd : d ≠ zero)
    (h : n ≠ repr (min_signed w) ∨ d ≠ mone) :
    divmods2 (if lt n zero then mone else zero) n d = some (divs n d, mods n d) := by
  unfold divmods2
  rw [if_neg hd]
  dsimp only
  rw [signed_sign_ext_mul_add hw]
  have h' : n ≠ BitVec.intMin w ∨ d ≠ -1#w := by
    rw [← repr_min_signed_eq_intMin hw, BitVec.neg_one_eq_allOnes]; exact h
  have hq : (signed n).tdiv (signed d) = signed (divs n d) := by
    rw [signed_toInt, signed_toInt, signed_toInt, divs, BitVec.toInt_sdiv_of_ne_or_ne _ _ h']
  have hr : (signed n).tmod (signed d) = signed (mods n d) := by
    rw [signed_toInt, signed_toInt, signed_toInt, mods, BitVec.toInt_srem]
  have hrange := signed_range hw (divs n d)
  rw [hq, hr, if_pos (by simp [hrange.1, hrange.2]), repr_signed, repr_signed]

/-- Arithmetic shift right by `w - 1` yields the sign mask. -/
theorem sshiftRight_pred_eq (x : BitVec w) :
    x.sshiftRight (w - 1) = if lt x zero then mone else zero := by
  have hlt : lt x zero = x.msb := by
    simp only [lt, zero]
    exact Bool.eq_iff_iff.mpr BitVec.slt_zero_iff_msb_cond
  rw [hlt]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have lhs : (x.sshiftRight (w - 1)).getLsbD i = x.msb := by
    rw [BitVec.getLsbD_sshiftRight]
    simp only [show ¬ w ≤ i from by omega, decide_false, Bool.not_false, Bool.true_and]
    split
    · have : w - 1 + i = w - 1 := by omega
      rw [this, BitVec.msb_eq_getLsbD_last]
    · rfl
  rw [lhs]
  cases x.msb <;> simp [mone, zero, hi]

/-- `Int.shr_lt_zero` -/
theorem shr_lt_zero (x y : BitVec w) (hy : y.toNat = w - 1) :
    shr x y = if lt x zero then mone else zero := by
  rw [shr, hy, sshiftRight_pred_eq]

end MI

namespace Int

theorem divmodu2_divu_modu (n d : Int) (hd : d ≠ zero) :
    divmodu2 zero n d = some (divu n d, modu n d) :=
  MI.divmodu2_divu_modu n d hd

theorem divmods2_divs_mods (n d : Int) (hd : d ≠ zero)
    (h : n ≠ repr min_signed ∨ d ≠ mone) :
    divmods2 (if lt n zero then mone else zero) n d = some (divs n d, mods n d) :=
  MI.divmods2_divs_mods (by decide) n d hd h

/-- `Int.shr_lt_zero` -/
theorem shr_lt_zero (x : Int) : shr x (repr 31) = if lt x zero then mone else zero :=
  MI.shr_lt_zero x _ (by decide)

end Int

namespace Int64

theorem divmodu2_divu_modu (n d : Int64) (hd : d ≠ zero) :
    divmodu2 zero n d = some (divu n d, modu n d) :=
  MI.divmodu2_divu_modu n d hd

theorem divmods2_divs_mods (n d : Int64) (hd : d ≠ zero)
    (h : n ≠ repr min_signed ∨ d ≠ mone) :
    divmods2 (if lt n zero then mone else zero) n d = some (divs n d, mods n d) :=
  MI.divmods2_divs_mods (by decide) n d hd h

/-- `Int64.shr_lt_zero` -/
theorem shr_lt_zero (x : Int64) : shr x (repr 63) = if lt x zero then mone else zero :=
  MI.shr_lt_zero x _ (by decide)

end Int64

end Integers
end CC
