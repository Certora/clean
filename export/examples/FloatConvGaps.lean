/-
  Executable reproducers for the floating-point fidelity gaps described in
  `PORT_GAP_ANALYSIS.md` (repository root).

  STATUS: FIXED.  Every `#eval` below now prints exactly the CompCert result
  given in the comment beside it (`lib/Floats.v`, aarch64).  The conversions and
  `abs`/`neg` are now computed exactly from the bit pattern, so the same facts
  are also proved by `decide` in `examples/FloatConvCheck.lean`, which is part
  of the default build.  The section text below describes the *former*
  behaviour, kept for reference.

  Not part of the default `Examples` roots.  Run with
      lake env lean export/examples/FloatConvGaps.lean   (from the repository root)
-/
import CCLib

open CC

namespace FloatConvGaps

/-- `2^63` as a binary64. -/
def two63 : Floats.Float := Floats.Float.ofNative 9223372036854775808.0

/-! ## 1. `Float.to_long` / `to_longu` saturate instead of failing

CompCert: `Float.to_long f = None` when `f` truncates outside
`[Int64.min_signed, Int64.max_signed]`, so `(long)f` is undefined behaviour
(no `sem_cast` result, the Clight step is stuck).  The port goes through
`Float.toInt64`, which saturates, and then range-checks the saturated value. -/

#eval Floats.Float.toLong two63                          -- CompCert: none
#eval Floats.Float.toLong (Floats.Float.ofNative 1e30)   -- CompCert: none
#eval Floats.Float.toLongu (Floats.Float.ofNative 1e30)  -- CompCert: none
#eval Floats.Float32.toLongu (Floats.Float32.ofNative 1e30) -- CompCert: none
-- In range for unsigned long, but the port returns 2^63-1:
#eval (Floats.Float.toLongu (Floats.Float.ofNative 1e19)).map (·.toNat)
                                                -- CompCert: some 10000000000000000000

/-! The same wrong results surface through `Cop.semCast`, i.e. in the Clight
semantics itself: `(long) 1e30` gets a value instead of getting stuck. -/

#eval Cop.semCast (.Vfloat (Floats.Float.ofNative 1e30)) tdouble tlong
        Mem.empty                                  -- CompCert: none

/-! ## 2. `Float32.of_long` / `of_longu` round twice

CompCert rounds the integer directly to binary32 (`IEEE754_extra.BofZ 24 128`).
The port rounds to binary64 first and then to binary32.  For
`n = 2^62 + 2^38 + 1` the first rounding lands exactly on a binary32 midpoint
and the second (ties-to-even) goes the wrong way. -/

#eval (Floats.Float32.ofLong (BitVec.ofNat 64 (2^62 + 2^38 + 1))).toNative.toFloat.toUInt64.toNat
                                                -- CompCert: 4611686568183201792 (= 2^62 + 2^39)

/-! ## 3. `Float.abs` / `Float32.abs` keep the sign of `-0.0`

CompCert's `abs` is `Babs`, which clears the sign bit; `fabs(-0.0) = +0.0`.
The port uses `if x < 0 then -x else x`, and `-0.0 < 0.0` is false. -/

#eval (Floats.Float.abs (Floats.Float.ofNative (-0.0))).bits      -- CompCert: 0x0000000000000000
#eval (Floats.Float32.abs (Floats.Float32.ofNative (-0.0))).bits  -- CompCert: 0x00000000

end FloatConvGaps
