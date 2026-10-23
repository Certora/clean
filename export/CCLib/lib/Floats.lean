/-
  Floating-point values — port of `lib/Floats.v` (1464 lines), with the parts of
  `lib/IEEE754_extra.v` and Flocq (`Binary.v`, `Bits.v`) that it uses.

  ## Representation and model

  CompCert defines `float := Flocq binary_float 53 1024`.  Here a float is
  **represented by its bit pattern** (`Float.bits : Int64`, `Float32.bits :
  Int`), which is in bijection with Flocq's `binary_float` (`Bits.v`), so
  `of_bits`/`to_bits` are the identity.

  Every operation is computed **exactly, in pure Lean**, from the bit pattern;
  nothing is delegated to the host FPU:

  * The numeric part of every operation is taken from `CCLib.lib.FloatModel`, a
    backport of Lean core's IEEE-754 reference model `Float.Model` (round to
    nearest, ties to even — CompCert's `mode_NE`).  This includes the
    float↔integer conversions: `ZofB` is read off the model's `unpack`, and
    `BofZ` is the model's `normalize` followed by `pack`.
  * NaN results follow CompCert exactly: whenever the model returns NaN the
    result is `binop_nan`/`unop_nan`/`fma_nan`/`of_single_nan`/`to_single_nan`,
    built from the arguments' payloads with the target's `Archi.choose_nan_64/32`
    and `quiet_nan_64/32`, as in `Floats.v`.
  * `neg`/`abs` flip/clear the sign bit (`Bopp`/`Babs` with `neg_nan`/`abs_nan`).

  ## Structure

  Everything is written **once**, generically in the IEEE format, in namespace
  `Gen` (functions on `BitVec spec.numBits`, parameterised by a `NanConfig` for
  the target's NaN rules).  `Float` (binary64) and `Float32` (binary32) are thin
  wrappers that instantiate `Gen` with `Format.binary64`/`Format.binary32` and
  the corresponding `Archi` NaN settings; likewise the lemmas in
  `CCLib.lib.FloatsLemmas` are proved once in `Gen` and restated per format under
  CompCert's names.

  Lean's built-in `Float`/`Float32` cannot be used for the semantics: on the
  pinned toolchain (v4.32.1) their operations are opaque `@[extern]` constants,
  so nothing about them can be proved or evaluated in the kernel, and their NaN
  payloads are those of the host FPU, not CompCert's.  The bridges
  `toNative`/`ofNative` are kept only for printing and testing.

  Names match what the `clightgen -lean` printers emit (`Floats.Float.ofBits`,
  `Floats.Float32.ofBits`), so exported files need no changes.
-/
import CCLib.lib.Integers
import CCLib.aarch64.Archi
import CCLib.lib.FloatModel

namespace CC
namespace Floats

open FloatModel FloatModel.UnpackedFloat

/-! ## Boolean-valued comparisons (`Floats.v`) -/

/-- `cmp_of_comparison` -/
def cmpOfComparison (c : Comparison) (x : Option Ordering) : Bool :=
  match c, x with
  | .Ceq, some .eq => true
  | .Ceq, _ => false
  | .Cne, some .eq => false
  | .Cne, _ => true
  | .Clt, some .lt => true
  | .Clt, _ => false
  | .Cle, some .lt => true
  | .Cle, some .eq => true
  | .Cle, _ => false
  | .Cgt, some .gt => true
  | .Cgt, _ => false
  | .Cge, some .gt => true
  | .Cge, some .eq => true
  | .Cge, _ => false

/-- `ordered_of_comparison` -/
def orderedOfComparison (x : Option Ordering) : Bool := x.isSome

/-! ## Format-generic operations on bit patterns

`spec` is the IEEE format (`Format.binary64` or `Format.binary32`).  A NaN is
described, as in CompCert, by a sign and a payload (`Bool × Nat`). -/
namespace Gen

/-- The target's NaN rules for one format (`Archi.default_nan_64` /
`Archi.choose_nan_64`, resp. the `_32` versions).  Indexed by the format it
applies to, so that the format can be inferred from it. -/
structure NanConfig (spec : Format) where
  /-- `default_nan_*`: sign and payload of the default NaN. -/
  defaultNan : Bool × Nat
  /-- `choose_nan_*`: picks the result NaN from the arguments' NaNs. -/
  chooseNan : List (Bool × Nat) → Bool × Nat

section
variable (spec : Format)

/-- Flocq's `is_nan`. -/
def isNan (b : BitVec spec.numBits) : Bool := (unpack spec b).isNaN

/-- Sign and payload of a NaN (meaningless for other values). -/
def nanOf (b : BitVec spec.numBits) : Bool × Nat :=
  (unpackSign b == 1#1, (unpackMantissa b).toNat)

/-- `quiet_nan_64`/`quiet_nan_32`: the NaN with the given sign and the payload
with its quiet bit set, truncated to the payload width. -/
def quietNan (sp : Bool × Nat) : BitVec spec.numBits :=
  packComponents spec (if sp.1 then .negative else .positive) (-1#_)
    (BitVec.ofNat _ (sp.2 ||| 2 ^ (spec.mantissaBitsWithoutImplicit - 1)))

/-- `cons_pl` -/
def consPl (x : BitVec spec.numBits) (l : List (Bool × Nat)) : List (Bool × Nat) :=
  if isNan spec x then nanOf spec x :: l else l

/-- Pack a model result, replacing a NaN result by the given CompCert NaN. -/
def packOr (nan : BitVec spec.numBits) : UnpackedFloat → BitVec spec.numBits
  | .notANumber => nan
  | r => pack spec r

/-- The sign bit (the most significant bit of the pattern). -/
def signBit : BitVec spec.numBits := BitVec.twoPow _ (spec.numBits - 1)

/-- `Bopp` + `neg_nan`: flip the sign bit, NaNs included. -/
def neg (b : BitVec spec.numBits) : BitVec spec.numBits := b ^^^ signBit spec

/-- `Babs` + `abs_nan`: clear the sign bit, so `abs (-0.0) = +0.0` and NaNs
keep their payload. -/
def abs (b : BitVec spec.numBits) : BitVec spec.numBits := b &&& ~~~signBit spec

/-- `Bcompare`: `none` iff an argument is NaN. -/
def compare (x y : BitVec spec.numBits) : Option Ordering :=
  UnpackedFloat.compare (unpack spec x) (unpack spec y)

/-- `Float.cmp` / `Float32.cmp` -/
def cmp (c : Comparison) (x y : BitVec spec.numBits) : Bool :=
  cmpOfComparison c (compare spec x y)

/-- `Float.ordered` / `Float32.ordered` -/
def ordered (x y : BitVec spec.numBits) : Bool :=
  orderedOfComparison (compare spec x y)

/-- Product of two unpacked floats, *without* rounding (used by `fma`). -/
def mulExact : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity s₁, .infinity s₂ => .infinity (s₁ * s₂)
  | .infinity s₁, .finite s₂ .. => .infinity (s₁ * s₂)
  | .finite s₁ .., .infinity s₂ => .infinity (s₁ * s₂)
  | .infinity _, .zero _ => .notANumber
  | .zero _, .infinity _ => .notANumber
  | .finite s₁ .., .zero s₂ => .zero (s₁ * s₂)
  | .zero s₁, .finite s₂ .. => .zero (s₁ * s₂)
  | .zero s₁, .zero s₂ => .zero (s₁ * s₂)
  | .finite s₁ m₁ e₁ h₁, .finite s₂ m₂ e₂ h₂ =>
    .finite (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) (Nat.mul_pos h₁ h₂)

/-- Flocq's `Bfma` (numeric part): `x * y + z` with a single rounding. -/
def fmaU (x y z : UnpackedFloat) : UnpackedFloat :=
  match mulExact x y with
  | .finite s m e h =>
    match z with
    | .zero _ => round spec s m e
    | _ => add spec (.finite s m e h) z
  | p => add spec p z

/-- `Bconv`: change of format (numeric part), rounding to nearest even. -/
def convU : UnpackedFloat → UnpackedFloat
  | .finite s m e _ => round spec s m e
  | r => r

/-- Flocq's `ZofB`: the value of the float, truncated toward zero, computed
exactly from the model; `none` for infinities and NaNs. -/
def toZ (b : BitVec spec.numBits) : Option Int :=
  match unpack spec b with
  | .zero _ => some 0
  | .finite s m e _ =>
    some (s.apply (if 0 ≤ e then ((m <<< e.toNat : Nat) : Int)
                   else ((m >>> e.natAbs : Nat) : Int)))
  | _ => none

/-- Flocq's `ZofB_range`: `toZ`, but only if the result lies in `[lo, hi]`. -/
def toZRange (b : BitVec spec.numBits) (lo hi : Int) : Option Int :=
  (toZ spec b).filter fun z => decide (lo ≤ z) && decide (z ≤ hi)

/-- `IEEE754_extra.BofZ`: the integer `z` rounded *once*, to nearest with ties
to even, into the format.  `BofZ 0` is `+0.0`; values beyond the largest finite
float round to ±∞. -/
def ofZ (z : Int) : BitVec spec.numBits :=
  pack spec (normalize spec z 0 .positive)

end

/-! ### NaN-propagating operations, parameterised by the target's NaN rules -/

section
variable {spec : Format} (nc : NanConfig spec)

/-- `default_nan_*` -/
def defaultNan : BitVec spec.numBits := quietNan spec nc.defaultNan
/-- `unop_nan` -/
def unopNan (x : BitVec spec.numBits) : BitVec spec.numBits :=
  quietNan spec (nc.chooseNan (consPl spec x []))
/-- `binop_nan` -/
def binopNan (x y : BitVec spec.numBits) : BitVec spec.numBits :=
  quietNan spec (nc.chooseNan (consPl spec x (consPl spec y [])))
/-- `fma_nan_1` -/
def fmaNan1 (x y z : BitVec spec.numBits) : BitVec spec.numBits :=
  let (a, b, c) := Archi.fma_order x y z
  quietNan spec (nc.chooseNan (consPl spec a (consPl spec b (consPl spec c []))))
/-- `fma_nan` -/
def fmaNan (x y z : BitVec spec.numBits) : BitVec spec.numBits :=
  match unpack spec x, unpack spec y with
  | .infinity _, .zero _ | .zero _, .infinity _ =>
    if Archi.fma_invalid_mul_is_nan then
      quietNan spec (nc.chooseNan (nc.defaultNan :: consPl spec z []))
    else fmaNan1 nc x y z
  | _, _ => fmaNan1 nc x y z

/-- `Bplus` + `binop_nan` -/
def add (x y : BitVec spec.numBits) : BitVec spec.numBits :=
  packOr spec (binopNan nc x y) (UnpackedFloat.add spec (unpack spec x) (unpack spec y))
/-- `Bminus` + `binop_nan` -/
def sub (x y : BitVec spec.numBits) : BitVec spec.numBits :=
  packOr spec (binopNan nc x y) (UnpackedFloat.sub spec (unpack spec x) (unpack spec y))
/-- `Bmult` + `binop_nan` -/
def mul (x y : BitVec spec.numBits) : BitVec spec.numBits :=
  packOr spec (binopNan nc x y) (UnpackedFloat.mul spec (unpack spec x) (unpack spec y))
/-- `Bdiv` + `binop_nan` -/
def div (x y : BitVec spec.numBits) : BitVec spec.numBits :=
  packOr spec (binopNan nc x y) (UnpackedFloat.div spec (unpack spec x) (unpack spec y))
/-- `Bsqrt` + `unop_nan` -/
def sqrt (x : BitVec spec.numBits) : BitVec spec.numBits :=
  packOr spec (unopNan nc x) (UnpackedFloat.sqrt spec (unpack spec x))
/-- `Bfma` + `fma_nan`: `x * y + z`, rounded once. -/
def fma (x y z : BitVec spec.numBits) : BitVec spec.numBits :=
  packOr spec (fmaNan nc x y z) (fmaU spec (unpack spec x) (unpack spec y) (unpack spec z))

end

end Gen

/-! ## binary64 (`CompCert Floats.float`) -/

/-- CompCert's `float` (binary64), represented by its 64-bit pattern. -/
structure Float where
  bits : Integers.Int64
  deriving DecidableEq, Repr, Inhabited

namespace Float

/-- The target's binary64 NaN rules. -/
def nanConfig : Gen.NanConfig Format.binary64 := ⟨Archi.default_nan_64, Archi.choose_nan_64⟩

/-- `Float.of_bits` -/
def ofBits (b : Integers.Int64) : Float := ⟨b⟩
/-- `Float.to_bits` -/
def toBits (f : Float) : Integers.Int64 := f.bits
/-- `Float.from_words` -/
def fromWords (hi lo : Integers.Int) : Float := ofBits (Integers.Int64.ofwords hi lo)

/-- Bridge to the native (hardware) binary64 value — for printing and testing
only; no operation below uses it. -/
@[inline] def toNative (f : Float) : _root_.Float :=
  _root_.Float.ofBits f.bits.toNat.toUInt64
/-- Bridge back from a native binary64 value (testing only). -/
@[inline] def ofNative (x : _root_.Float) : Float :=
  ⟨BitVec.ofNat 64 x.toBits.toNat⟩

/-- The value of `f` in the exact IEEE model. -/
def unpack (f : Float) : UnpackedFloat := UnpackedFloat.unpack Format.binary64 f.bits

/-- `Float.zero`: `+0.0`. -/
def zero : Float := ⟨0⟩

/-- `is_nan` -/
def isNaN (f : Float) : Bool := Gen.isNan Format.binary64 f.bits

/-! ### NaN payloads (`Floats.v`, module `Float`) -/

/-- `quiet_nan_64` -/
def quietNan (sp : Bool × Nat) : Float := ⟨Gen.quietNan Format.binary64 sp⟩
/-- `default_nan_64` -/
def defaultNan : Float := ⟨Gen.defaultNan nanConfig⟩
/-- `cons_pl` -/
def consPl (x : Float) (l : List (Bool × Nat)) : List (Bool × Nat) :=
  Gen.consPl Format.binary64 x.bits l
/-- `unop_nan` -/
def unopNan (x : Float) : Float := ⟨Gen.unopNan nanConfig x.bits⟩
/-- `binop_nan` -/
def binopNan (x y : Float) : Float := ⟨Gen.binopNan nanConfig x.bits y.bits⟩
/-- `fma_nan` -/
def fmaNan (x y z : Float) : Float := ⟨Gen.fmaNan nanConfig x.bits y.bits z.bits⟩

/-! ### Arithmetic (round to nearest, ties to even) -/

/-- `Float.neg` (`Bopp` + `neg_nan`): flips the sign bit, NaNs included. -/
def neg (f : Float) : Float := ⟨Gen.neg Format.binary64 f.bits⟩
/-- `Float.abs` (`Babs` + `abs_nan`): clears the sign bit. -/
def abs (f : Float) : Float := ⟨Gen.abs Format.binary64 f.bits⟩
/-- `Float.add` (`Bplus` + `binop_nan`) -/
def add (x y : Float) : Float := ⟨Gen.add nanConfig x.bits y.bits⟩
/-- `Float.sub` (`Bminus` + `binop_nan`) -/
def sub (x y : Float) : Float := ⟨Gen.sub nanConfig x.bits y.bits⟩
/-- `Float.mul` (`Bmult` + `binop_nan`) -/
def mul (x y : Float) : Float := ⟨Gen.mul nanConfig x.bits y.bits⟩
/-- `Float.div` (`Bdiv` + `binop_nan`) -/
def div (x y : Float) : Float := ⟨Gen.div nanConfig x.bits y.bits⟩
/-- `Float.sqrt` (`Bsqrt` + `unop_nan`) -/
def sqrt (x : Float) : Float := ⟨Gen.sqrt nanConfig x.bits⟩
/-- `Float.fma` (`Bfma` + `fma_nan`): `x * y + z`, rounded once. -/
def fma (x y z : Float) : Float := ⟨Gen.fma nanConfig x.bits y.bits z.bits⟩

/-! ### Comparison -/

/-- `Float.compare` (`Bcompare`): `none` iff an argument is NaN. -/
def compare (f1 f2 : Float) : Option Ordering := Gen.compare Format.binary64 f1.bits f2.bits
/-- `Float.cmp` -/
def cmp (c : Comparison) (f1 f2 : Float) : Bool := Gen.cmp Format.binary64 c f1.bits f2.bits
/-- `Float.ordered` -/
def ordered (f1 f2 : Float) : Bool := Gen.ordered Format.binary64 f1.bits f2.bits

/-! ### Conversions to and from integers

CompCert's `to_int`/`to_intu`/`to_long`/`to_longu` return `option` and fail when
the value is NaN, infinite, or truncates outside the target range — the C
standard makes those cases undefined, and `Cop` propagates the `None`
(`Gen.toZRange` = `ZofB_range`).  The `of_*` conversions round the integer once
(`Gen.ofZ` = `BofZ 53 1024`). -/

/-- `Float.to_int` — signed 32-bit, truncating toward zero. -/
def toInt (f : Float) : Option Integers.Int :=
  (Gen.toZRange Format.binary64 f.bits Integers.Int.min_signed
    Integers.Int.max_signed).map Integers.Int.repr
/-- `Float.to_intu` — unsigned 32-bit. -/
def toIntu (f : Float) : Option Integers.Int :=
  (Gen.toZRange Format.binary64 f.bits 0 Integers.Int.max_unsigned).map Integers.Int.repr
/-- `Float.to_long` — signed 64-bit. -/
def toLong (f : Float) : Option Integers.Int64 :=
  (Gen.toZRange Format.binary64 f.bits Integers.Int64.min_signed
    Integers.Int64.max_signed).map Integers.Int64.repr
/-- `Float.to_longu` — unsigned 64-bit. -/
def toLongu (f : Float) : Option Integers.Int64 :=
  (Gen.toZRange Format.binary64 f.bits 0 Integers.Int64.max_unsigned).map
    Integers.Int64.repr

/-- `BofZ 53 1024`, as a `Float`. -/
def ofZ (z : Z) : Float := ⟨Gen.ofZ Format.binary64 z⟩
/-- `Float.of_int` — from a signed 32-bit integer. -/
def ofInt (n : Integers.Int) : Float := ofZ (Integers.Int.signed n)
/-- `Float.of_intu` — from an unsigned 32-bit integer. -/
def ofIntu (n : Integers.Int) : Float := ofZ (Integers.Int.unsigned n)
/-- `Float.of_long` — from a signed 64-bit integer. -/
def ofLong (n : Integers.Int64) : Float := ofZ (Integers.Int64.signed n)
/-- `Float.of_longu` — from an unsigned 64-bit integer. -/
def ofLongu (n : Integers.Int64) : Float := ofZ (Integers.Int64.unsigned n)

end Float

/-! ## binary32 (`CompCert Floats.float32`) -/

/-- CompCert's `float32` (binary32), represented by its 32-bit pattern. -/
structure Float32 where
  bits : Integers.Int
  deriving DecidableEq, Repr, Inhabited

namespace Float32

/-- The target's binary32 NaN rules. -/
def nanConfig : Gen.NanConfig Format.binary32 := ⟨Archi.default_nan_32, Archi.choose_nan_32⟩

/-- `Float32.of_bits` -/
def ofBits (b : Integers.Int) : Float32 := ⟨b⟩
/-- `Float32.to_bits` -/
def toBits (f : Float32) : Integers.Int := f.bits

/-- Bridge to the native binary32 value (printing and testing only). -/
@[inline] def toNative (f : Float32) : _root_.Float32 :=
  _root_.Float32.ofBits f.bits.toNat.toUInt32
/-- Bridge back from a native binary32 value (testing only). -/
@[inline] def ofNative (x : _root_.Float32) : Float32 :=
  ⟨BitVec.ofNat 32 x.toBits.toNat⟩

/-- The value of `f` in the exact IEEE model. -/
def unpack (f : Float32) : UnpackedFloat := UnpackedFloat.unpack Format.binary32 f.bits

/-- `Float32.zero`: `+0.0`. -/
def zero : Float32 := ⟨0⟩

/-- `is_nan` -/
def isNaN (f : Float32) : Bool := Gen.isNan Format.binary32 f.bits

/-- `quiet_nan_32` -/
def quietNan (sp : Bool × Nat) : Float32 := ⟨Gen.quietNan Format.binary32 sp⟩
/-- `default_nan_32` -/
def defaultNan : Float32 := ⟨Gen.defaultNan nanConfig⟩
/-- `cons_pl` -/
def consPl (x : Float32) (l : List (Bool × Nat)) : List (Bool × Nat) :=
  Gen.consPl Format.binary32 x.bits l
/-- `unop_nan` -/
def unopNan (x : Float32) : Float32 := ⟨Gen.unopNan nanConfig x.bits⟩
/-- `binop_nan` -/
def binopNan (x y : Float32) : Float32 := ⟨Gen.binopNan nanConfig x.bits y.bits⟩
/-- `fma_nan` -/
def fmaNan (x y z : Float32) : Float32 := ⟨Gen.fmaNan nanConfig x.bits y.bits z.bits⟩

/-- `Float32.neg`: flips the sign bit, NaNs included. -/
def neg (f : Float32) : Float32 := ⟨Gen.neg Format.binary32 f.bits⟩
/-- `Float32.abs`: clears the sign bit, so `abs (-0.0) = +0.0`. -/
def abs (f : Float32) : Float32 := ⟨Gen.abs Format.binary32 f.bits⟩
/-- `Float32.add` -/
def add (x y : Float32) : Float32 := ⟨Gen.add nanConfig x.bits y.bits⟩
/-- `Float32.sub` -/
def sub (x y : Float32) : Float32 := ⟨Gen.sub nanConfig x.bits y.bits⟩
/-- `Float32.mul` -/
def mul (x y : Float32) : Float32 := ⟨Gen.mul nanConfig x.bits y.bits⟩
/-- `Float32.div` -/
def div (x y : Float32) : Float32 := ⟨Gen.div nanConfig x.bits y.bits⟩
/-- `Float32.sqrt` -/
def sqrt (x : Float32) : Float32 := ⟨Gen.sqrt nanConfig x.bits⟩
/-- `Float32.fma` -/
def fma (x y z : Float32) : Float32 := ⟨Gen.fma nanConfig x.bits y.bits z.bits⟩

/-- `Float32.compare` -/
def compare (f1 f2 : Float32) : Option Ordering := Gen.compare Format.binary32 f1.bits f2.bits
/-- `Float32.cmp` -/
def cmp (c : Comparison) (f1 f2 : Float32) : Bool := Gen.cmp Format.binary32 c f1.bits f2.bits
/-- `Float32.ordered` -/
def ordered (f1 f2 : Float32) : Bool := Gen.ordered Format.binary32 f1.bits f2.bits

/-! ### Conversions to and from integers

As for binary64: exact truncation from the binary32 value (`ZofB_range 24 128`),
and a single rounding of the integer straight to binary32 (`BofZ 24 128`) — not
via binary64, which would round twice. -/

/-- `Float32.to_int` -/
def toInt (f : Float32) : Option Integers.Int :=
  (Gen.toZRange Format.binary32 f.bits Integers.Int.min_signed
    Integers.Int.max_signed).map Integers.Int.repr
/-- `Float32.to_intu` -/
def toIntu (f : Float32) : Option Integers.Int :=
  (Gen.toZRange Format.binary32 f.bits 0 Integers.Int.max_unsigned).map Integers.Int.repr
/-- `Float32.to_long` -/
def toLong (f : Float32) : Option Integers.Int64 :=
  (Gen.toZRange Format.binary32 f.bits Integers.Int64.min_signed
    Integers.Int64.max_signed).map Integers.Int64.repr
/-- `Float32.to_longu` -/
def toLongu (f : Float32) : Option Integers.Int64 :=
  (Gen.toZRange Format.binary32 f.bits 0 Integers.Int64.max_unsigned).map
    Integers.Int64.repr

/-- `BofZ 24 128`, as a `Float32`. -/
def ofZ (z : Z) : Float32 := ⟨Gen.ofZ Format.binary32 z⟩
/-- `Float32.of_int` -/
def ofInt (n : Integers.Int) : Float32 := ofZ (Integers.Int.signed n)
/-- `Float32.of_intu` -/
def ofIntu (n : Integers.Int) : Float32 := ofZ (Integers.Int.unsigned n)
/-- `Float32.of_long` -/
def ofLong (n : Integers.Int64) : Float32 := ofZ (Integers.Int64.signed n)
/-- `Float32.of_longu` -/
def ofLongu (n : Integers.Int64) : Float32 := ofZ (Integers.Int64.unsigned n)

end Float32

/-! ## Conversions between the two formats (`Float.of_single` / `to_single`) -/

/-- `expand_nan_payload`: a binary32 payload shifted into binary64 position. -/
def expandNanPayload (p : Nat) : Nat := p <<< 29
/-- `quiet_nan_64_payload` -/
def quietNan64Payload (p : Nat) : Nat := (p ||| 2 ^ 51) % 2 ^ 52
/-- `reduce_nan_payload` -/
def reduceNanPayload (p : Nat) : Nat := quietNan64Payload p >>> 29

/-- `Float.of_single_nan` -/
def Float.ofSingleNan (f : Float32) : Float :=
  if f.isNaN then
    let (s, p) := Gen.nanOf Format.binary32 f.bits
    if Archi.float_conversion_default_nan then Float.defaultNan
    else if Archi.float_of_single_preserves_sNaN then
      ⟨packComponents Format.binary64 (if s then .negative else .positive) (-1#_)
        (BitVec.ofNat _ (expandNanPayload p))⟩
    else Float.quietNan (s, expandNanPayload p)
  else Float.defaultNan

/-- `Float.to_single_nan` -/
def Float.toSingleNan (f : Float) : Float32 :=
  if f.isNaN then
    let (s, p) := Gen.nanOf Format.binary64 f.bits
    if Archi.float_conversion_default_nan then Float32.defaultNan
    else Float32.quietNan (s, reduceNanPayload p)
  else Float32.defaultNan

/-- `Float.of_single` — widen binary32 to binary64 (exact; `Bconv` +
`of_single_nan`). -/
def Float.ofSingle (f : Float32) : Float :=
  ⟨Gen.packOr Format.binary64 (Float.ofSingleNan f).bits (Gen.convU Format.binary64 f.unpack)⟩
/-- `Float.to_single` — narrow binary64 to binary32, rounding to nearest even
(`Bconv` + `to_single_nan`). -/
def Float.toSingle (f : Float) : Float32 :=
  ⟨Gen.packOr Format.binary32 (Float.toSingleNan f).bits (Gen.convU Format.binary32 f.unpack)⟩

/-- `Float32.of_double` (same as `Float.to_single`) -/
def Float32.ofDouble (f : Float) : Float32 := Float.toSingle f
/-- `Float32.to_double` (same as `Float.of_single`) -/
def Float32.toDouble (f : Float32) : Float := Float.ofSingle f

end Floats
end CC
