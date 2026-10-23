/-
  Float literals — the `from_parsed` part of `lib/Floats.v`
  (`Float.from_parsed`, `Float32.from_parsed`), i.e. `IEEE754_extra.Bparse`
  for binary64 and binary32.

  `from_parsed base intPart expPart` is the value `intPart × base ^ expPart`
  rounded once, to nearest with ties to even (CompCert's `mode_NE`), into the
  format: values beyond the largest finite float give `+∞`, values below the
  smallest subnormal round to `+0.0` or to the smallest subnormal.  The C
  front end (`cfrontend/C2C.ml`) calls it on the decimal or hexadecimal
  digits of a literal.

  As in the rest of `CCLib.lib.Floats`, the rounding is done by the exact
  IEEE-754 model `CCLib.lib.FloatModel` (the backport of Lean core's
  `Float.Model`), not by Flocq:
  * for `expPart ≥ 0` the value is the integer `intPart × base ^ expPart`,
    rounded by the model's `round`;
  * for `expPart < 0` it is the fraction `intPart / base ^ (-expPart)`; the
    model's `divCore` computes enough quotient bits together with the exact
    position of the remainder (`Accuracy`), and `roundWithAccuracy` rounds
    once.  This is the division step of the model's `div`, applied to two
    arbitrary naturals instead of two float mantissas.
-/
import CCLib.lib.Floats
import CCLib.lib.Positive

namespace CC
namespace Floats

open FloatModel FloatModel.UnpackedFloat

namespace Gen

variable (spec : Format)

/-- `IEEE754_extra.Bparse`: `m × base ^ e`, rounded once to nearest even. -/
def parse (base m : Nat) (e : Int) : BitVec spec.numBits :=
  if 0 ≤ e then
    pack spec (round spec .positive (m * base ^ e.toNat) 0)
  else
    let (q, ex, acc) := divCore spec m 0 (base ^ (-e).toNat) 0
    pack spec (roundWithAccuracy spec .positive q ex acc)

end Gen

namespace Float

/-- `Float.from_parsed` (`Bparse 53 1024`). -/
def from_parsed (base intPart : Positive) (expPart : Z) : Float :=
  ⟨Gen.parse Format.binary64 base.toNat intPart.toNat expPart⟩

end Float

namespace Float32

/-- `Float32.from_parsed` (`Bparse 24 128`). -/
def from_parsed (base intPart : Positive) (expPart : Z) : Float32 :=
  ⟨Gen.parse Format.binary32 base.toNat intPart.toNat expPart⟩

end Float32

/-! ### Checks against known bit patterns (evaluated by the kernel) -/

/-- `0.1` -/
example : (Float.from_parsed (Positive.ofNat 10) (Positive.ofNat 1) (-1)).bits.toNat
    = 0x3FB999999999999A := by decide +kernel
/-- `1.5e308` is finite -/
example : (Float.from_parsed (Positive.ofNat 10) (Positive.ofNat 15) 307).bits.toNat
    = 0x7FEAB36D48E1ACF0 := by decide +kernel
/-- `2e308` overflows to `+∞` -/
example : (Float.from_parsed (Positive.ofNat 10) (Positive.ofNat 2) 308).bits.toNat
    = 0x7FF0000000000000 := by decide +kernel
/-- `5e-324` is the smallest subnormal -/
example : (Float.from_parsed (Positive.ofNat 10) (Positive.ofNat 5) (-324)).bits.toNat
    = 1 := by decide +kernel
/-- `2e-324` rounds to `+0.0` -/
example : (Float.from_parsed (Positive.ofNat 10) (Positive.ofNat 2) (-324)).bits.toNat
    = 0 := by decide +kernel
/-- `0x1.8p1 = 3.0` (hexadecimal literal: base 2) -/
example : (Float.from_parsed (Positive.ofNat 2) (Positive.ofNat 3) 0).bits.toNat
    = 0x4008000000000000 := by decide +kernel
/-- `0.1f` -/
example : (Float32.from_parsed (Positive.ofNat 10) (Positive.ofNat 1) (-1)).bits.toNat
    = 0x3DCCCCCD := by decide +kernel

end Floats
end CC
