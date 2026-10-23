/-
  Exact IEEE-754 model — a backport of Lean core's `Float.Model`
  (`Init/Data/Float/Model/**`, Lean ≥ v4.33.0; copyright 2026 Lean FRO, LLC,
  Apache 2.0, author Julia M. Himmel) to the toolchain this project is pinned
  to (v4.32.1), where `Float.Model` does not exist yet.

  The definitions are copied verbatim, except that
  * they live in namespace `CC.FloatModel` instead of `Float.Model`, so the
    file keeps compiling after an upgrade to a toolchain that ships the
    original (at that point this file can be replaced by `Float.Model`), and
  * the `Float.Model`/`Float32.Model` wrapper structures, the `OfScientific`
    parser and the fixed-width `toUInt*`/`ofUInt*` conversions are omitted:
    `CCLib.lib.Floats` works directly on bit patterns and only needs
    `UnpackedFloat` with its rounding, packing and arithmetic.

  The model has a single canonical NaN and no payloads.  CompCert's NaN
  payload rules (`Archi.choose_nan_64/32`, `quiet_nan_64/32`, …) are layered on
  top of it in `CCLib.lib.Floats`.
-/

/-! ### from `Init/Data/Float/Model/Format/Basic.lean` -/

namespace CC.FloatModel

/--
The position of the most significant digit, where the unit digit corresponds to `1`.
So, for example, `1.0b` has total exponent `1`, `0.1b` has total exponent `0`,
`0.01b` has total exponent `-1`, and so on.
-/
def totalExponent (mantissa : Nat) (exponent : Int) :=
  mantissa.log2 + 1 + exponent

/--
A floating point format is specified by two pieces of information: the number
of bits in the mantissa, and the number of bits in the exponent.
-/
structure Format where
  /-- The number of bits in the mantissa, *excluding the implicit bit*. -/
  mantissaBitsWithoutImplicit : Nat
  hm : 0 < mantissaBitsWithoutImplicit := by decide
  /-- The number of bits in the exponent. -/
  exponentBits : Nat
  he : 2 ≤ exponentBits := by decide

namespace Format

/-- Specification corresponding to the IEEE `binary32` format. -/
abbrev binary32 : Format where
  mantissaBitsWithoutImplicit := 23
  exponentBits := 8

/-- Specification corresponding to the IEEE `binary64` format. -/
abbrev binary64 : Format where
  mantissaBitsWithoutImplicit := 52
  exponentBits := 11

/-- The total number of bits in the packed representation. -/
abbrev numBits (spec : Format) : Nat :=
  1 + spec.exponentBits + spec.mantissaBitsWithoutImplicit

/-- The number of bits in the mantissa, *including the implicit bit*. -/
def mantissaBits (spec : Format) : Nat :=
  1 + spec.mantissaBitsWithoutImplicit

/--
The exponent bias. In packed formats, we store the sum of the true exponent and
the bias.
-/
def exponentBias (spec : Format) : Nat :=
  2 ^ (spec.exponentBits - 1) - 1

/--
The smallest exponent possible for a number using the given specification,
including subnormals.
-/
def minExponent (spec : Format) : Int :=
  3 - 2 ^ (spec.exponentBits - 1) - spec.mantissaBits

/--
Suppose we have written a number where `totalExponent` is the position of the
most significant digit, where the unit digit corresponds to `1`. So, for example,
`1.0b` has total exponent `1`, `0.1b` has total exponent `0`, `0.01b` has total
exponent `-1`, and so on. This function computes which exponent that number
should have according to the given `Format`. So, for example, for the number
`0.1b` in `binary64` format, it wants us to use the exponent `-53`, corresponding
to the representation `2^52 * 2^(-53)`, which has a 53-bit mantissa. If the total
exponent gets quite small, then the result exponent eventually gets capped at
`spec.minExponent`, which first forces the result to be a subnormal number and
then, if the total exponent is even smaller, to be zero.
-/
def targetExponent (spec : Format) (totalExponent : Int) : Int :=
  max (totalExponent - spec.mantissaBits) spec.minExponent

end Format

end CC.FloatModel

/-! ### from `Init/Data/Float/Model/Unpacked/Sign.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Inductive with two constructors `negative` and `positive` for representing sign bits in
floating-point models. This is not a general-purpose sign type like mathlib's `SignType`,
which also includes a `zero` case.
-/
inductive Sign where
  /-- Negative (`-`) sign. -/
  | negative : Sign
  /-- Positive (`+`) sign. -/
  | positive : Sign
deriving Repr, DecidableEq

namespace Sign

instance : Mul Sign where
  mul
    | .negative, .negative => .positive
    | .negative, .positive => .negative
    | .positive, .negative => .negative
    | .positive, .positive => .positive

instance : Div Sign where
  div
    | .negative, .negative => .positive
    | .negative, .positive => .negative
    | .positive, .negative => .negative
    | .positive, .positive => .positive

instance : Neg Sign where
  neg
    | .negative => .positive
    | .positive => .negative

instance : Ord Sign where
  compare
    | .negative, .negative => .eq
    | .negative, .positive => .lt
    | .positive, .negative => .gt
    | .positive, .positive => .eq

/--
Apply the given sign to the given integer.
-/
def apply (s : Sign) (n : Int) : Int :=
  match s with
  | .negative => -n
  | .positive => n

/--
Converts the sign to a bitvector, with positive sign denoted by `0`.
-/
def toBitVec : Sign → BitVec 1
  | .negative => 1#1
  | .positive => 0#1

/--
Constructs a sign from a bitvector, with positive sign denoted by `0`.
-/
def ofBitVec (b  : BitVec 1) : Sign :=
  if b = 0#1 then .positive else .negative

end Sign

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Basic.lean` -/

namespace CC.FloatModel

open UnpackedFloat in
/--
An inductive type representing a floating-point number with constructors for signed infinity,
not-a-number without payload, signed zero, and finite floats with a sign, positive natural
mantissa and integral exponent.

Finite floats do not have a unique representation in this format: multiplying the
mantissa by two and decreasing the exponent by one yields a finite float that represents the
same rational number.

For a given `Format`, we say that an unpacked float is in canonical form if the exponent
is equal to the `targetExponent` according to that format. Some operations on `UnpackedFloat`,
such as `compare`, assume that the input(s) are all in canonical form for the same format.

Note that an unpacked float in canonical form for a given format may not actually be
representable in that format as the exponent is too large to fit. In this case, the `pack`
function will overflow the float to infinity.

This type exists solely for the purpose of supporting `Float.Model` and `Float32.Model`. It is not
a goal of this development to serve as the basis for a general-purpose floating-point library or
to have any direct lemmas written about it at all. Rather, users interested in a library about
floating-point numbers should develop such a library completely separately, and users interested in
proving properties of their programs involving `Float` should prove that the operations defined
here are equivalent to the operations defined in the separate library and then transfer lemmas from
the library to the `Float` and `Float32` types.
-/
inductive UnpackedFloat where
  /-- Signed infinity. -/
  | infinity (sign : Sign) : UnpackedFloat
  /-- Not a number. There is no payload attached to a NaN in this format. -/
  | notANumber : UnpackedFloat
  /-- Signed zero. -/
  | zero (sign : Sign) : UnpackedFloat
  /-- Finite floats consisting of a sign bit, a positive natural mantissa and an exponent. -/
  | finite (sign : Sign) (mantissa : Nat) (exponent : Int) (mantissa_pos : 0 < mantissa) : UnpackedFloat
deriving Repr, BEq

end CC.FloatModel

/-! ### from `Init/Data/Float/Model/Unpacked/Round.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Suppose given a real number `x : ℝ` with binary expansion
`x = ± x₀.x₁x₂x₃…`. Truncating the expansion at some point gives an
approximation of `x` as a floating-point number `y`. We can then ask how `y`
is related to `x`. If `y` is exactly `x`, then we say that we are exact.
Otherwise we are inexact, and `y` is slightly smaller than `x`, but `x` is also
smaller than `y + 1ulp`. Together with the information that we are inexact,
we store the information of where `x` is located relative to `y + ½ulp`. This
is sufficient information for rounding `y` according to the various IEEE rounding
rules.
-/
inductive Accuracy where
  /--
  The approximation is exactly equal to the infinitely precise value.
  -/
  | exact
  /--
  The approximation is strictly smaller than the infinitely precise value,
  and the given `Ordering` describes the result of comparing the
  infinitely precise value and the approximation plus half a ulp.
  -/
  | inexact (relativeToPlusOneHalfUlp : Ordering)

namespace Accuracy

/--
Rounds the given mantissa with the given accuracy according to the
round-to-nearest strategy, with ties breaking in favor of even
mantissas.
-/
def roundToNearestEven (mantissa : Nat) : Accuracy → Nat
  | .exact => mantissa
  | .inexact .lt => mantissa
  | .inexact .eq => mantissa + mantissa % 2
  | .inexact .gt => mantissa + 1

end Accuracy

/--
Pairs a mantissa with two residual bits, the 'round bit' and the 'sticky bit',
which carry precisely the required information to compute the `Accuracy` of the
mantissa.
-/
structure ExtendedMantissa where
  /-- The mantissa. -/
  mantissa : Nat
  /-- The next bit after the least significant bit of the mantissa. -/
  roundBit : Bool
  /-- The bitwise `or` of all bits that are even less significant than the round bit.  -/
  stickyBit : Bool

namespace ExtendedMantissa

/-- Extract the accuracy of the mantissa. -/
def accuracy : ExtendedMantissa → Accuracy
  | ⟨_, false, false⟩ => .exact
  | ⟨_, false, true⟩ => .inexact .lt
  | ⟨_, true, false⟩ => .inexact .eq
  | ⟨_, true, true⟩ => .inexact .gt

/--
Extracts the mantissa, rounded according to the data in the residual bits.
-/
def roundedMantissa (em : ExtendedMantissa) : Nat :=
  em.accuracy.roundToNearestEven em.mantissa

/--
Transforms a mantissa and an accuracy into an extended mantissa with the
residual bits initialized to represent the given accuracy.
-/
def ofMantissaAndAccuracy (mantissa : Nat) (accuracy : Accuracy) : ExtendedMantissa :=
  match accuracy with
  | .exact => ⟨mantissa, false, false⟩
  | .inexact .lt => ⟨mantissa, false, true⟩
  | .inexact .eq => ⟨mantissa, true, false⟩
  | .inexact .gt => ⟨mantissa, true, true⟩

/--
Shift the mantissa right by one, propagating information into the residual bits
as required.
-/
def shiftRightOne (em : ExtendedMantissa) : ExtendedMantissa where
  mantissa := em.mantissa / 2
  roundBit := em.mantissa % 2 != 0
  stickyBit := em.roundBit || em.stickyBit

instance : HShiftRight ExtendedMantissa Nat ExtendedMantissa where
  hShiftRight em n := n.repeat shiftRightOne em

end ExtendedMantissa

/--
Shifts the mantissa and exponent and initial accuracy to the target exponent, returning
the new extended mantissa and exponent.

Important: this function will only drop bits from the mantissa and increase the exponent,
not the other way around. The result will only conform to the given specification if
the exponent was not too large to begin with. If this may be the case, you should call
`round` instead.
-/
def shiftToExponent (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (targetExponent : Int) : ExtendedMantissa × Int :=
  let shiftAmount := (targetExponent - exponent).toNat -- negative to 0
  let initialExtendedMantissa := ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy
  (initialExtendedMantissa >>> shiftAmount, exponent + shiftAmount)

/--
Computes the target exponent for the given mantissa and exponent and shifts the
mantissa and exponent and initial accuracy to the target exponent, returning
the new extended mantissa and exponent.

Important: this function will only drop bits from the mantissa and increase the exponent,
not the other way around. The result will only conform to the given specification if
the exponent was not too large to begin with. If this may be the case, you should call
`round` instead.
-/
def shiftToTargetExponent (spec : Format) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) : ExtendedMantissa × Int :=
  let targetExponent := spec.targetExponent (totalExponent mantissa exponent)
  shiftToExponent mantissa exponent accuracy targetExponent

/--
Given a finite float represented by a sign, mantissa and exponent, together with an
`Accuracy` datum, round it to conform to the given `Format`.

Important: this function will only drop bits from the mantissa and increase the exponent,
not the other way around. The result will only conform to the given specification if
the exponent was not too large to begin with. If this may be the case, you should call
`round` instead.
-/
def roundWithAccuracy (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) : UnpackedFloat :=
  -- First shift: this performs the bulk of the shifting
  let (em₁, e₁) := shiftToTargetExponent spec mantissa exponent accuracy
  -- Round mantissa
  let roundedEm₁ := em₁.roundedMantissa
  -- Rounding the mantissa may have overflowed it, causing it to take too many bits, so we shift
  -- once more (no rounding is necessary after this):
  let (finalExtendedMantissa, finalExponent) := shiftToTargetExponent spec roundedEm₁ e₁ .exact
  let finalMantissa := finalExtendedMantissa.mantissa

  if h : finalMantissa = 0 then
    .zero sign
  else
    .finite sign finalMantissa finalExponent (Nat.pos_of_ne_zero h)

/--
If the target exponent is smaller than the given exponent, decreases the exponent of the mantissa to
the target exponent; otherwise does nothing.
-/
def decreaseExponent (mantissa : Nat) (exponent : Int) (targetExponent : Int) : Nat × Int :=
  let shiftAmount := (exponent - targetExponent).toNat -- negative to 0
  (mantissa <<< shiftAmount, exponent - shiftAmount)

/--
Given a finite float represented by a sign, mantissa and exponent,
round it to conform to the given `Format`.

If necessary, this will both decrease and increase the exponent.
-/
def round (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int) : UnpackedFloat :=
  let targetExponent := spec.targetExponent (totalExponent mantissa exponent)
  let (mantissa, exponent) := decreaseExponent mantissa exponent targetExponent
  roundWithAccuracy spec sign mantissa exponent .exact

/--
Given a finite float represented as a signed mantissa and an exponent, round it to conform to the
given `Format`.

If necessary, this will both decrease and increase the exponent.
-/
def normalize (spec : Format) (mantissa : Int) (exponent : Int) (zeroSign : Sign) : UnpackedFloat :=
  match compare mantissa 0 with
  | .lt => round spec .negative (-mantissa).toNat exponent
  | .eq => .zero zeroSign
  | .gt => round spec .positive mantissa.toNat exponent

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Pack/Basic.lean` -/

namespace CC.FloatModel.UnpackedFloat

/-- Creates a packed float from a sign, an exponent and a mantissa. -/
def packComponents (spec : Format) (sign : Sign)
    (exponent : BitVec spec.exponentBits)
    (mantissa : BitVec spec.mantissaBitsWithoutImplicit) : BitVec spec.numBits :=
  sign.toBitVec ++ exponent ++ mantissa

/-- Creates the packed signed infinity representation for the given specification. -/
def packedInfinity (spec : Format) (sign : Sign) : BitVec spec.numBits :=
  packComponents spec sign (-1#_) 0

/-- Creates the canonical packed `NaN` for the given specification. -/
def packedNaN (spec : Format) : BitVec spec.numBits :=
  packComponents spec .positive (-1#_) (1#_ <<< (spec.mantissaBitsWithoutImplicit - 1))

/-- Creates the packed signed zero representation for the given specification. -/
def packedZero (spec : Format) (sign : Sign) : BitVec spec.numBits :=
  packComponents spec sign 0 0

/--
Packs the given float into the format given by the specification.

This function assumes that the float is already correctly rounded for the given specification.
This means that the exponent must be equal to the exponent computed by `spec.targetExponent`.
-/
def pack (spec : Format) : UnpackedFloat → BitVec spec.numBits
  | .notANumber => packedNaN spec
  | .infinity s => packedInfinity spec s
  | .zero s => packedZero spec s
  | .finite s m e _ =>
    let actualMantissaBits := m.log2
    let biasedExponent := (e + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat
    if 2 ^ spec.exponentBits ≤ biasedExponent + 1 then
      packedInfinity spec s
    else if actualMantissaBits + 1 = spec.mantissaBits then
      -- normal
      -- Observe that the transformation of the mantissa clears the implicit bit
      packComponents spec s (BitVec.ofNat _ biasedExponent) (BitVec.ofNat _ m)
    else
      -- subnormal
      packComponents spec s 0#_ (BitVec.ofNat _ m)

/--
Unpacks the mantissa portion of the packed float. If this is a normal number, this
will be missing the implicit bit.
-/
def unpackMantissa {spec : Format} (b : BitVec spec.numBits) :
    BitVec spec.mantissaBitsWithoutImplicit :=
  b.extractLsb' 0 spec.mantissaBitsWithoutImplicit

/--
Unpacks the exponent portion of the packed float.
-/
def unpackExponent {spec : Format} (b : BitVec spec.numBits) :
    BitVec spec.exponentBits :=
  b.extractLsb' spec.mantissaBitsWithoutImplicit spec.exponentBits

/--
Unpacks the sign bit of the packed float.
-/
def unpackSign {spec : Format} (b : BitVec spec.numBits) :
    BitVec 1 :=
  b.extractLsb' (spec.mantissaBitsWithoutImplicit + spec.exponentBits) 1

-- Backport note: these two facts replace `simp` calls that rely on newer core lemmas.
theorem toNat_pos_of_ne_zero' {w : Nat} {v : BitVec w} (h : ¬ v = 0#w) : 0 < v.toNat := by
  apply Nat.pos_of_ne_zero; intro h'; exact h (BitVec.eq_of_toNat_eq (by simp [h']))

theorem one_shiftLeft_or_pos' (n x : Nat) : 0 < 1 <<< n ||| x := by
  have h1 : 0 < 1 <<< n := by
    rw [Nat.shiftLeft_eq]; exact Nat.mul_pos Nat.one_pos (Nat.two_pow_pos n)
  exact Nat.lt_of_lt_of_le h1 Nat.left_le_or

/--
Unpacks the given float according to the given specification.

The resulting float may be assumed to be correctly rounded for the given specification.
-/
def unpack (spec : Format) (b : BitVec spec.numBits) : UnpackedFloat :=
  let mantissaVec := unpackMantissa b
  let exponentVec : BitVec spec.exponentBits :=  unpackExponent b
  let exponent : Int := (exponentVec.toNat : Int) - (spec.exponentBias + spec.mantissaBitsWithoutImplicit)
  let signVec : BitVec 1 := unpackSign b
  let sign := Sign.ofBitVec signVec
  if exponentVec = -1#_ then
    if mantissaVec = 0#_ then
      .infinity sign
    else
      .notANumber
  else if exponentVec = 0#_ then
    if h : mantissaVec = 0#_ then
      .zero sign
    else
      -- subnormal
      .finite sign mantissaVec.toNat (exponent + 1) (toNat_pos_of_ne_zero' h)
  else
    -- normal
    .finite sign (1#1 ++ mantissaVec).toNat exponent (by simp only [BitVec.toNat_append]; exact one_shiftLeft_or_pos' _ _)

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Sign.lean` -/

namespace CC.FloatModel.UnpackedFloat

/-- Negates the given float. -/
def neg : UnpackedFloat → UnpackedFloat
  | .notANumber => .notANumber
  | .infinity s => .infinity (-s)
  | .zero s => .zero (-s)
  | .finite s m e hm => .finite (-s) m e hm

/-- Returns the given float with positive sign. -/
def abs : UnpackedFloat → UnpackedFloat
  | .notANumber => .notANumber
  | .infinity _ => .infinity .positive
  | .zero _ => .zero .positive
  | .finite _ m e hm => .finite .positive m e hm

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Status.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Returns `true` if the float represents a real number, i.e., it is neither infinite nor `NaN`.
-/
def isFinite : UnpackedFloat → Bool
  | .notANumber => false
  | .infinity .. => false
  | .zero .. => true
  | .finite .. => true

/--
Returns `true` if the float is positive or negative infinity.
-/
def isInf : UnpackedFloat → Bool
  | .infinity .. => true
  | _ => false

/--
Returns `true` if the float is `NaN`.
-/
def isNaN : UnpackedFloat → Bool
  | .notANumber => true
  | _ => false

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Add.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Computes the sum of two floating point numbers and rounds the result according to
the given specification.
-/
def add (spec : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity sign₁, .infinity sign₂ =>
    if sign₁ == sign₂ then .infinity sign₁ else .notANumber
  | .infinity s, _ => .infinity s
  | _, .infinity s => .infinity s
  | .zero sign₁, .zero sign₂ =>
    if sign₁ == sign₂ then .zero sign₁ else .zero .positive
  | .zero _, y => y
  | x, .zero _ => x
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    let smallerExponent := min e₁ e₂
    let (m₁, _) := decreaseExponent m₁ e₁ smallerExponent
    let (m₂, _) := decreaseExponent m₂ e₂ smallerExponent
    let mantissa := s₁.apply m₁ + s₂.apply m₂
    normalize spec mantissa smallerExponent .positive

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Sub.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Computes the difference of two floating point numbers and rounds the result according to
the given specification.
-/
def sub (spec : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity sign₁, .infinity sign₂ =>
    if sign₁ == -sign₂ then .infinity sign₁ else .notANumber
  | .infinity s, _ => .infinity s
  | _, .infinity s => .infinity (-s)
  | .zero sign₁, .zero sign₂ =>
    if sign₁ == -sign₂ then .zero sign₁ else .zero .positive
  | .zero _, .finite sign mantissa exponent hm => .finite (-sign) mantissa exponent hm
  | x, .zero _ => x
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    let smallerExponent := min e₁ e₂
    let (m₁, _) := decreaseExponent m₁ e₁ smallerExponent
    let (m₂, _) := decreaseExponent m₂ e₂ smallerExponent
    let mantissa := s₁.apply m₁ - s₂.apply m₂
    normalize spec mantissa smallerExponent .positive

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Mul.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Computes the product of two floating-point numbers and rounds the result according to
the given specification.
-/
def mul (spec : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity sign₁, .infinity sign₂ => .infinity (sign₁ * sign₂)
  | .infinity sign₁, .finite sign₂ .. => .infinity (sign₁ * sign₂)
  | .finite sign₁ .., .infinity sign₂ => .infinity (sign₁ * sign₂)
  | .infinity _, .zero _ => .notANumber
  | .zero _, .infinity _ => .notANumber
  | .finite sign₁ .., .zero sign₂ => .zero (sign₁ * sign₂)
  | .zero sign₁, .finite sign₂ .. => .zero (sign₁ * sign₂)
  | .zero sign₁, .zero sign₂ => .zero (sign₁ * sign₂)
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    roundWithAccuracy spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Div.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Returns the accuracy corresponding to the point `y + (num/den)ulp`.

Assumes `num < den`.
-/
def accuracyOfFraction (num den : Nat) : Accuracy :=
  if num = 0 then
    .exact
  else
    .inexact (compare (2 * num) den)

/--
Computes a `(mantissa, exponent)` pair for the quotient with enough bits to populate the mantissa
for the given specification. Also returns an `Accuracy` stating how the returned pair relates to
the infinitely precise quotient.
-/
def divCore (spec : Format) (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) : Nat × Int × Accuracy :=
  -- Strategy: decrease the exponent here far enough so that we definitely get enough bits in the
  -- quotient `m / m₂`. We take the `min` because we don't want to increase the exponent; this happens
  -- later in the rounding step.
  let targetExponent := min (e₁ - e₂) (spec.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
  let shiftAmount := (e₁ - e₂ - targetExponent).toNat
  let m := m₁ <<< shiftAmount
  (m / m₂, targetExponent, accuracyOfFraction (m % m₂) m₂)

/--
Computes the quotient of two floating point numbers and rounds the result according to
the given specification.
-/
def div (spec : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity _, .infinity _ => .notANumber
  | .infinity sign₁, .finite sign₂ .. => .infinity (sign₁ / sign₂)
  | .finite sign₁ .., .infinity sign₂ => .zero (sign₁ / sign₂)
  | .infinity sign₁, .zero sign₂ => .infinity (sign₁ / sign₂)
  | .zero sign₁, .infinity sign₂ => .zero (sign₁ / sign₂)
  | .finite sign₁ .., .zero sign₂ => .infinity (sign₁ / sign₂)
  | .zero sign₁, .finite sign₂ .. => .zero (sign₁ / sign₂)
  | .zero _, .zero _ => .notANumber
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    let (m, e, acc) := divCore spec m₁ e₁ m₂ e₂
    roundWithAccuracy spec (s₁ / s₂) m e acc

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Sqrt.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Computes a `(mantissa, exponent)` pair for the square root with enough bits to populate the mantissa
for the given specification. Also returns an `Accuracy` stating how the returned pair relates to
the infinitely precise square root.
-/
def sqrtCore (spec : Format) (m : Nat) (e : Int) : Nat × Int × Accuracy :=
  -- Here we shift so that the input is represented as `m * 2 ^ (2 * targetExponent)`, where `m` has
  -- so many bits that `sqrt m` still has enough bits for the specified format.
  let targetExponent := min (e.ediv 2) (spec.targetExponent ((totalExponent m e + 1).ediv 2))
  let shiftAmount := (e - 2 * targetExponent).toNat
  let m := m <<< shiftAmount

  let root := Nat.sqrt m
  let rem := m - root * root

  -- Let x := Real.sqrt m. Then
  -- `x < root + 1/2` ↔ `x^2 < root^2 + root + 1/4` ↔ `rem < root + 1/4` ↔ `rem ≤ root`.
  -- `x = root + 1/2` is impossible.
  let accuracy : Accuracy := if rem = 0 then .exact else .inexact (if rem ≤ root then .lt else .gt)
  (root, targetExponent, accuracy)

/--
Computes the square root of a floating-point number and rounds the result according to the given
specification.
-/
def sqrt (spec : Format) : UnpackedFloat → UnpackedFloat
  | .notANumber => .notANumber
  | .infinity .positive => .infinity .positive
  | .infinity .negative => .notANumber
  | .finite .negative .. => .notANumber
  | .zero sign => .zero sign
  | .finite .positive m e _ =>
    let (m, e, acc) := sqrtCore spec m e
    roundWithAccuracy spec .positive m e acc

end CC.FloatModel.UnpackedFloat

/-! ### from `Init/Data/Float/Model/Unpacked/Operations/Compare.lean` -/

namespace CC.FloatModel.UnpackedFloat

/--
Computes the ordering between the two floats as specificed by IEEE. Returns an
`Option Ordering` to account for the fact that `NaN` is incomparable with everything.
Also, positive and negative zero are equal.

Important: this operation only works correctly if the two inputs are in
canonical form for a common format (see the docstring for `UnpackedFloat` for details.)
-/
protected def compare : UnpackedFloat → UnpackedFloat → Option Ordering
  | .notANumber, _ => none
  | _, .notANumber => none
  | .infinity s₁, .infinity s₂ => some (compare s₁ s₂)
  | .infinity .positive, _ => some .gt
  | .infinity .negative, _ => some .lt
  | _, .infinity .positive => some .lt
  | _, .infinity .negative => some .gt
  | .finite .positive .., .zero _ => some .gt
  | .finite .negative .., .zero _ => some .lt
  | .zero _, .finite .positive .. => some .lt
  | .zero _, .finite .negative .. => some .gt
  | .zero _, .zero _ => some .eq
  | .finite .negative m₁ e₁ _, .finite .negative m₂ e₂ _ =>
    some ((compare e₁ e₂).then (compare m₁ m₂)).swap
  | .finite .negative .., .finite .positive .. => some .lt
  | .finite .positive .., .finite .negative .. => some .gt
  | .finite .positive m₁ e₁ _, .finite .positive m₂ e₂ _ =>
    some ((compare e₁ e₂).then (compare m₁ m₂))

/--
Determines whether `a` is less than or equal to `b` according to IEEE rules.

This is not a total ordering, and `≤` is not reflexive.
-/
protected def le (a b : UnpackedFloat) : Bool :=
  (a.compare b).any (·.isLE)

/--
Determines whether `a` is less than `b` according to IEEE rules.

This is not a total ordering.
-/
protected def lt (a b : UnpackedFloat) : Bool :=
  a.compare b == some .lt

/--
Determines whether `a` is equal to `b` according to IEEE rules.

This is not a reflexive relation.
-/
protected def beq (a b : UnpackedFloat) : Bool :=
  a.compare b == some .eq

end CC.FloatModel.UnpackedFloat

