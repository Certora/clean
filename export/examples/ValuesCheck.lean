/-
  Checks for the operations and theorems added from `common/Values.v` and
  `lib/Integers.v` (powers of two, rotations, `shrx`).
-/
import CCLib.common.ValuesInject

open CC CC.Val

namespace ValuesCheck

/-- `shrx` rounds towards zero: `-7 / 2 = -3` (an arithmetic shift would give `-4`). -/
example : shrx (.Vint (Integers.Int.repr (-7))) (.Vint (Integers.Int.repr 1)) =
    some (.Vint (Integers.Int.repr (-3))) := by decide

example : shr (.Vint (Integers.Int.repr (-7))) (.Vint (Integers.Int.repr 1)) =
    .Vint (Integers.Int.repr (-4)) := by decide

/-- `shrx` is undefined for a shift amount of 31 or more. -/
example : shrx (.Vint (Integers.Int.repr 5)) (.Vint (Integers.Int.repr 31)) = none := by decide

/-- `Val.cmpl` is partial, as in CompCert. -/
example : cmpl .Ceq (.Vlong Integers.Int64.zero) (.Vint Integers.Int.zero) = none := by decide
example : cmpl .Clt (.Vlong (Integers.Int64.repr (-1))) (.Vlong Integers.Int64.zero) =
    some Vtrue := by decide

/-- `is_power2` finds the logarithm. -/
example : Integers.Int.is_power2 (Integers.Int.repr 64) = some (Integers.Int.repr 6) := by decide
example : Integers.Int.is_power2 (Integers.Int.repr 48) = none := by decide
example : Integers.Int64.is_power2' (Integers.Int64.repr 1024) = some (Integers.Int.repr 10) := by
  decide

/-- Division by 8 turned into `shrx`, by the theorem `divs_pow2`. -/
example (x y : Val) (h : divs x (.Vint (Integers.Int.repr 8)) = some y) :
    shrx x (.Vint (Integers.Int.repr 3)) = some y :=
  divs_pow2 (by decide) (by decide) h

/-- The carry decomposition `shrx_carry` on a concrete value. -/
example : add (shr (.Vint (Integers.Int.repr (-7))) (.Vint (Integers.Int.repr 1)))
    (shr_carry (.Vint (Integers.Int.repr (-7))) (.Vint (Integers.Int.repr 1))) =
      .Vint (Integers.Int.repr (-3)) :=
  shrx_carry (by decide)

/-- The sign bit, extracted by a rotate-and-mask. -/
example : rolm (.Vint (Integers.Int.repr (-5))) Integers.Int.one Integers.Int.one = Vtrue := by
  rw [rolm_lt_zero]; decide

end ValuesCheck
