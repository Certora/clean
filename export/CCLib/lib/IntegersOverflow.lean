/-
  Port of `Int.lt_sub_overflow` (`lib/Integers.v`): the signed "less than"
  test computed from the overflow and negative flags of a subtraction, as
  done by the condition codes of AArch64, ARM and PowerPC.
-/
import CCLib.lib.IntegersInt
import CCLib.lib.IntegersInt64

namespace CC
namespace Integers
namespace MI

variable {w : Nat}

theorem signed_sub_eq (hw : 0 < w) (x y : BitVec w) :
    signed (sub x y) =
      if signed x - signed y < min_signed w then signed x - signed y + modulus w
      else if signed x - signed y > max_signed w then signed x - signed y - modulus w
      else signed x - signed y := by
  rw [sub_signed, signed_repr_eq hw]
  have hm := half_modulus_modulus hw
  have hp := half_modulus_pos hw
  have ⟨hx1, hx2⟩ := signed_range hw x
  have ⟨hy1, hy2⟩ := signed_range hw y
  unfold min_signed max_signed at *
  generalize hsd : signed x - signed y = s at *
  generalize modulus w = m at *
  generalize half_modulus w = h at *
  subst hm
  by_cases hs : 0 ≤ s
  · have : s % (2 * h) = s := Int.emod_eq_of_lt hs (by zomega)
    rw [this]
    by_cases h1 : s < h
    · rw [if_pos h1, if_neg (by zomega), if_neg (by zomega)]
    · rw [if_neg h1, if_neg (by zomega), if_pos (by zomega)]
  · have : s % (2 * h) = s + 2 * h := by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by zomega) (by zomega)
    rw [this]
    by_cases h1 : s < -h
    · rw [if_pos (by zomega), if_pos h1]
    · rw [if_neg (by zomega), if_neg h1, if_neg (by zomega)]; zomega

/-- `Int.lt_sub_overflow` -/
theorem lt_sub_overflow (hw : 0 < w) (x y : BitVec w) :
    xor (sub_overflow x y zero) (negative (sub x y)) = if lt x y then one else zero := by
  have hsub := signed_sub_eq hw x y
  have hz : signed (zero : BitVec w) = 0 := signed_zero
  have hm := half_modulus_modulus hw
  have hp := half_modulus_pos hw
  have ⟨hx1, hx2⟩ := signed_range hw x
  have ⟨hy1, hy2⟩ := signed_range hw y
  unfold sub_overflow negative
  simp only [lt_def, hz, Int.sub_zero]
  unfold min_signed max_signed at *
  by_cases h1 : signed x - signed y < -half_modulus w
  · rw [if_pos h1] at hsub
    rw [hsub]
    simp only [show ¬(-half_modulus w ≤ signed x - signed y) from by zomega,
      show signed x < signed y from by zomega,
      show ¬(signed x - signed y + modulus w < 0) from by zomega,
      decide_false, decide_true, Bool.false_and, Bool.false_eq_true, if_false, if_true, xor_zero]
  · rw [if_neg h1] at hsub
    by_cases h2 : signed x - signed y > half_modulus w - 1
    · rw [if_pos h2] at hsub
      rw [hsub]
      simp only [show (-half_modulus w ≤ signed x - signed y) from by zomega,
        show ¬ (signed x - signed y ≤ half_modulus w - 1) from by zomega,
        show ¬ signed x < signed y from by zomega,
        show (signed x - signed y - modulus w < 0) from by zomega,
        decide_false, decide_true, Bool.true_and, Bool.false_eq_true, if_false, if_true, xor_idem]
    · rw [if_neg h2] at hsub
      rw [hsub]
      simp only [show (-half_modulus w ≤ signed x - signed y) from by zomega,
        show (signed x - signed y ≤ half_modulus w - 1) from by zomega,
        decide_true, Bool.true_and, if_true, xor_zero_l]
      by_cases h3 : signed x < signed y
      · simp [h3, show signed x - signed y < 0 from by zomega]
      · simp [h3, show ¬ signed x - signed y < 0 from by zomega]

end MI

namespace Int
/-- `Int.lt_sub_overflow` -/
theorem lt_sub_overflow (x y : Int) :
    xor (sub_overflow x y zero) (negative (sub x y)) = if lt x y then one else zero :=
  MI.lt_sub_overflow (by decide) x y
end Int

namespace Int64
/-- `Int64.lt_sub_overflow` -/
theorem lt_sub_overflow (x y : Int64) :
    xor (sub_overflow x y zero) (negative (sub x y)) = if lt x y then one else zero :=
  MI.lt_sub_overflow (by decide) x y
end Int64

end Integers
end CC
