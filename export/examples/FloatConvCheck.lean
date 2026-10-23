/-
  Kernel-checked regression tests for the float ↔ integer conversions and the
  sign operations of `CCLib.lib.Floats`.

  These used to go through Lean's native `Float` (saturating `toInt64`, double
  rounding for `int64 → float32`, `if x < 0 then -x else x` for `abs`) and
  disagreed with CompCert's `lib/Floats.v`.  Like every float operation they
  are now computed exactly by the IEEE model in `CCLib.lib.Floats`, so they reduce
  in the kernel and the expected CompCert results can be checked by `decide`.

  Bit patterns are written in hex; the comment gives the value.
-/
import CCLib

namespace FloatConvCheck

open CC

/-- `2^63` as a binary64. -/
def two63 : Floats.Float := ⟨0x43E0000000000000#64⟩
/-- `-2^63` as a binary64. -/
def mtwo63 : Floats.Float := ⟨0xC3E0000000000000#64⟩
/-- `1e30` as a binary64. -/
def e30 : Floats.Float := ⟨0x46293E5939A08CEA#64⟩
/-- `1e19` as a binary64 (exactly `10^19`). -/
def e19 : Floats.Float := ⟨0x43E158E460913D00#64⟩
/-- `-2147483648.9` as a binary64. -/
def mInt32MinFrac : Floats.Float := ⟨0xC1E00000001CCCCD#64⟩
/-- `-0.9` as a binary64. -/
def m09 : Floats.Float := ⟨0xBFECCCCCCCCCCCCD#64⟩
/-- `+∞` and a quiet NaN as binary64. -/
def inf64 : Floats.Float := ⟨0x7FF0000000000000#64⟩
def nan64 : Floats.Float := ⟨0x7FF8000000000000#64⟩
/-- `-0.0` as binary64 / binary32. -/
def negZero64 : Floats.Float := ⟨0x8000000000000000#64⟩
def negZero32 : Floats.Float32 := ⟨0x80000000#32⟩

/-! ## 1. `to_long` / `to_longu` fail out of range instead of saturating -/

theorem toLong_two63 : two63.toLong = none := by decide
theorem toLong_mtwo63 : mtwo63.toLong = some (Integers.Int64.repr (-2^63)) := by decide
theorem toLong_e30 : e30.toLong = none := by decide
theorem toLongu_e30 : e30.toLongu = none := by decide
theorem toLongu_e19 : e19.toLongu = some (Integers.Int64.repr (10^19)) := by decide
theorem toLong_inf : inf64.toLong = none := by decide
theorem toLong_nan : nan64.toLong = none := by decide
theorem toInt_truncates : mInt32MinFrac.toInt = some (Integers.Int.repr (-2^31)) := by decide
theorem toIntu_small_negative : m09.toIntu = some (Integers.Int.repr 0) := by decide
/-- `1e30f` as binary32 does not convert to `unsigned long`. -/
theorem f32_toLongu_e30 : (⟨0x7149F2CA#32⟩ : Floats.Float32).toLongu = none := by decide

/-- The same in the Clight semantics: `(long) 1e30` has no value (undefined
behaviour), so the program is stuck rather than continuing with `LLONG_MAX`. -/
theorem semCast_double_long_e30 (m : Mem) :
    Cop.semCast (.Vfloat e30) tdouble tlong m = none := by
  simp only [Cop.semCast, Cop.classifyCast, tlong, tdouble]
  simp [Cop.castFloatLong, toLong_e30]

/-! ## 2. `int64 → float32` rounds once -/

/-- `2^62 + 2^38 + 1` rounds to `2^62 + 2^39` (bits `0x5E800001`), not to
`2^62`, which is what rounding through binary64 first gives. -/
theorem f32_ofLong_single_rounding :
    Floats.Float32.ofLong (Integers.Int64.repr (2^62 + 2^38 + 1)) = ⟨0x5E800001#32⟩ := by
  decide
theorem f32_ofLongu_single_rounding :
    Floats.Float32.ofLongu (Integers.Int64.repr (2^62 + 2^38 + 1)) = ⟨0x5E800001#32⟩ := by
  decide
/-- Ties go to even: `2^24 + 1` → `2^24`, `2^24 + 3` → `2^24 + 4`. -/
theorem f32_ofInt_tie_even :
    Floats.Float32.ofInt (Integers.Int.repr (2^24 + 1)) = ⟨0x4B800000#32⟩ ∧
    Floats.Float32.ofInt (Integers.Int.repr (2^24 + 3)) = ⟨0x4B800002#32⟩ := by
  decide
theorem f64_ofLong_min : Floats.Float.ofLong (Integers.Int64.repr (-2^63)) = mtwo63 := by decide +kernel
theorem f64_ofInt_zero : Floats.Float.ofInt (Integers.Int.repr 0) = ⟨0#64⟩ := by decide

/-! ## 3. `abs` clears and `neg` flips the sign bit -/

theorem abs_negZero64 : Floats.Float.abs negZero64 = ⟨0#64⟩ := by decide
theorem abs_negZero32 : Floats.Float32.abs negZero32 = ⟨0#32⟩ := by decide

/-! The sign laws hold for every float.  They are proved once, format-generically,
in `CCLib.lib.FloatsLemmas` (`Floats.Gen.neg_neg`, `abs_neg`, `abs_abs`); these are
the per-format instances. -/

theorem Float.neg_neg (f : Floats.Float) : Floats.Float.neg (Floats.Float.neg f) = f :=
  Floats.Float.neg_neg f
theorem Float.abs_abs (f : Floats.Float) : Floats.Float.abs (Floats.Float.abs f) = Floats.Float.abs f :=
  Floats.Float.abs_abs f
theorem Float.abs_neg (f : Floats.Float) : Floats.Float.abs (Floats.Float.neg f) = Floats.Float.abs f :=
  Floats.Float.abs_neg f
theorem Float32.neg_neg (f : Floats.Float32) : Floats.Float32.neg (Floats.Float32.neg f) = f :=
  Floats.Float32.neg_neg f
theorem Float32.abs_abs (f : Floats.Float32) :
    Floats.Float32.abs (Floats.Float32.abs f) = Floats.Float32.abs f :=
  Floats.Float32.abs_abs f
theorem Float32.abs_neg (f : Floats.Float32) :
    Floats.Float32.abs (Floats.Float32.neg f) = Floats.Float32.abs f :=
  Floats.Float32.abs_neg f

end FloatConvCheck
