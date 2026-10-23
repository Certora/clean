/-
  Target parameters of every CompCert back end — port of `x86_64/Archi.v`,
  `x86_32/Archi.v`, `riscV/Archi.v`, `powerpc/Archi.v`, `arm/Archi.v`
  (and, for comparison, `aarch64/Archi.v`).

  `CCLib/aarch64/Archi.lean` fixes the aarch64 values, which the rest of the port
  (memory model, `Values`, `Floats`, …) is built on.  This file records the
  values of the same knobs for every other target as plain data, so that the
  target-specific modules (`CCLib/x86/…`) can refer to them and so that the
  differences between targets are explicit and checkable.

  Rocq `Parameter`s (chosen by the OCaml driver: `riscV`'s `ptr64`, `arm`'s
  `big_endian`, `powerpc`'s `ppc64`) become explicit arguments here.

  `fma_order` is a polymorphic function in Rocq; every target uses one of
  three permutations of `(x, y, z)`, represented by `FmaOrder`.
-/
import CCLib.aarch64.Archi
import CCLib.lib.Floats

namespace CC
namespace Targets

/-- The three argument orders used by `Archi.fma_order` on the various
targets: `(x, y, z)`, `(x, z, y)` (PowerPC) and `(z, x, y)` (ARM, AArch64). -/
inductive FmaOrder where
  | xyz | xzy | zxy
  deriving DecidableEq, Repr

/-- Apply an `FmaOrder`. -/
def FmaOrder.apply {A : Type} : FmaOrder → A → A → A → A × A × A
  | .xyz, x, y, z => (x, y, z)
  | .xzy, x, y, z => (x, z, y)
  | .zxy, x, y, z => (z, x, y)

/-- All the knobs of `<arch>/Archi.v` that the target-independent semantics
depends on. -/
structure ArchiConfig where
  ptr64 : Bool
  big_endian : Bool
  align_int64 : Nat
  align_float64 : Nat
  splitlong : Bool
  default_nan_64 : Bool × Nat
  default_nan_32 : Bool × Nat
  choose_nan_64 : List (Bool × Nat) → Bool × Nat
  choose_nan_32 : List (Bool × Nat) → Bool × Nat
  fma_order : FmaOrder
  fma_invalid_mul_is_nan : Bool
  float_of_single_preserves_sNaN : Bool
  float_conversion_default_nan : Bool

namespace ArchiConfig

/-- The binary64 NaN rules of a target, in the form used by `CCLib.lib.Floats`. -/
def nan64 (c : ArchiConfig) : Floats.Gen.NanConfig FloatModel.Format.binary64 :=
  ⟨c.default_nan_64, c.choose_nan_64⟩
/-- The binary32 NaN rules of a target, in the form used by `CCLib.lib.Floats`. -/
def nan32 (c : ArchiConfig) : Floats.Gen.NanConfig FloatModel.Format.binary32 :=
  ⟨c.default_nan_32, c.choose_nan_32⟩

/-- `Archi.splitlong_ptr32`: a target that splits 64-bit integer operations
has 32-bit pointers. -/
def SplitlongPtr32 (c : ArchiConfig) : Prop := c.splitlong = true → c.ptr64 = false

/-- `Archi.choose_nan_64_idem` / `choose_nan_32_idem`. -/
def ChooseNanIdem (c : ArchiConfig) : Prop :=
  (∀ n, c.choose_nan_64 [n, n] = c.choose_nan_64 [n]) ∧
  (∀ n, c.choose_nan_32 [n, n] = c.choose_nan_32 [n])

end ArchiConfig

/-- `choose_nan` that returns the first NaN argument (x86, PowerPC). -/
def chooseFirstNan (default : Bool × Nat) : List (Bool × Nat) → Bool × Nat
  | [] => default
  | n :: _ => n

/-- Quiet-NaN payloads: only the quiet bit is set. -/
def quietPayload64 : Nat := 2 ^ 51
def quietPayload32 : Nat := 2 ^ 22

/-! ## The configurations -/

/-- `aarch64/Archi.v`. -/
def aarch64 : ArchiConfig where
  ptr64 := true
  big_endian := false
  align_int64 := 8
  align_float64 := 8
  splitlong := false
  default_nan_64 := (false, quietPayload64)
  default_nan_32 := (false, quietPayload32)
  choose_nan_64 := Archi.choose_nan_64
  choose_nan_32 := Archi.choose_nan_32
  fma_order := .zxy
  fma_invalid_mul_is_nan := true
  float_of_single_preserves_sNaN := false
  float_conversion_default_nan := false

/-- `x86_64/Archi.v`.  The default NaN is negative (x86's "real indefinite"),
and the result NaN of an operation is its first NaN argument. -/
def x86_64 : ArchiConfig where
  ptr64 := true
  big_endian := false
  align_int64 := 8
  align_float64 := 8
  splitlong := false
  default_nan_64 := (true, quietPayload64)
  default_nan_32 := (true, quietPayload32)
  choose_nan_64 := chooseFirstNan (true, quietPayload64)
  choose_nan_32 := chooseFirstNan (true, quietPayload32)
  fma_order := .xyz
  fma_invalid_mul_is_nan := false
  float_of_single_preserves_sNaN := false
  float_conversion_default_nan := false

/-- `x86_32/Archi.v`: as `x86_64` but with 32-bit pointers, 4-byte alignment
of 64-bit quantities and split 64-bit integer operations. -/
def x86_32 : ArchiConfig :=
  { x86_64 with ptr64 := false, align_int64 := 4, align_float64 := 4, splitlong := true }

/-- `riscV/Archi.v`, for the given value of the `ptr64` parameter (RV64 or
RV32).  Every NaN result is the canonical NaN, and conversions between
formats produce the canonical NaN too. -/
def riscV (ptr64 : Bool) : ArchiConfig where
  ptr64 := ptr64
  big_endian := false
  align_int64 := 8
  align_float64 := 8
  splitlong := !ptr64
  default_nan_64 := (false, quietPayload64)
  default_nan_32 := (false, quietPayload32)
  choose_nan_64 := fun _ => (false, quietPayload64)
  choose_nan_32 := fun _ => (false, quietPayload32)
  fma_order := .xyz
  fma_invalid_mul_is_nan := false
  float_of_single_preserves_sNaN := false
  float_conversion_default_nan := true

/-- `powerpc/Archi.v`, for the given value of the `ppc64` parameter (which
only controls whether 64-bit integer operations are split; pointers are
always 32 bits).  Big-endian. -/
def powerpc (ppc64 : Bool) : ArchiConfig where
  ptr64 := false
  big_endian := true
  align_int64 := 8
  align_float64 := 8
  splitlong := !ppc64
  default_nan_64 := (false, quietPayload64)
  default_nan_32 := (false, quietPayload32)
  choose_nan_64 := chooseFirstNan (false, quietPayload64)
  choose_nan_32 := chooseFirstNan (false, quietPayload32)
  fma_order := .xzy
  fma_invalid_mul_is_nan := false
  float_of_single_preserves_sNaN := true
  float_conversion_default_nan := false

/-- `arm/Archi.v`, for the given endianness (a `Parameter` in Rocq).  NaN
selection is the same as on AArch64. -/
def arm (big_endian : Bool) : ArchiConfig where
  ptr64 := false
  big_endian := big_endian
  align_int64 := 8
  align_float64 := 8
  splitlong := true
  default_nan_64 := (false, quietPayload64)
  default_nan_32 := (false, quietPayload32)
  choose_nan_64 := Archi.choose_nan_64
  choose_nan_32 := Archi.choose_nan_32
  fma_order := .zxy
  fma_invalid_mul_is_nan := true
  float_of_single_preserves_sNaN := false
  float_conversion_default_nan := false

/-! ## Facts -/

/-- The aarch64 configuration is the one `CCLib/aarch64/Archi.lean` hard-codes, on
which the whole port is built. -/
theorem aarch64_eq_archi :
    aarch64.ptr64 = Archi.ptr64 ∧ aarch64.big_endian = Archi.big_endian ∧
    aarch64.align_int64 = Archi.align_int64 ∧ aarch64.align_float64 = Archi.align_float64 ∧
    aarch64.splitlong = Archi.splitlong ∧
    aarch64.default_nan_64 = Archi.default_nan_64 ∧
    aarch64.default_nan_32 = Archi.default_nan_32 ∧
    aarch64.choose_nan_64 = Archi.choose_nan_64 ∧
    aarch64.choose_nan_32 = Archi.choose_nan_32 ∧
    (∀ {A : Type} (x y z : A), aarch64.fma_order.apply x y z = Archi.fma_order x y z) ∧
    aarch64.fma_invalid_mul_is_nan = Archi.fma_invalid_mul_is_nan ∧
    aarch64.float_of_single_preserves_sNaN = Archi.float_of_single_preserves_sNaN ∧
    aarch64.float_conversion_default_nan = Archi.float_conversion_default_nan :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

/-- The memory-layout knobs (`ptr64`, `big_endian`, alignments, `splitlong`)
of x86-64 coincide with those of AArch64, so the port's memory model and
value semantics, which use the AArch64 values, are also those of x86-64.
Only the NaN rules differ. -/
theorem x86_64_layout_eq_archi :
    x86_64.ptr64 = Archi.ptr64 ∧ x86_64.big_endian = Archi.big_endian ∧
    x86_64.align_int64 = Archi.align_int64 ∧ x86_64.align_float64 = Archi.align_float64 ∧
    x86_64.splitlong = Archi.splitlong :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The same holds for 64-bit RISC-V. -/
theorem riscV64_layout_eq_archi :
    (riscV true).ptr64 = Archi.ptr64 ∧ (riscV true).big_endian = Archi.big_endian ∧
    (riscV true).align_int64 = Archi.align_int64 ∧
    (riscV true).align_float64 = Archi.align_float64 ∧
    (riscV true).splitlong = Archi.splitlong :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chooseFirstNan_idem (d n : Bool × Nat) :
    chooseFirstNan d [n, n] = chooseFirstNan d [n] := rfl

theorem aarch64_splitlong_ptr32 : aarch64.SplitlongPtr32 := by
  intro h; cases h
theorem x86_64_splitlong_ptr32 : x86_64.SplitlongPtr32 := by
  intro h; cases h
theorem x86_32_splitlong_ptr32 : x86_32.SplitlongPtr32 := fun _ => rfl
theorem riscV_splitlong_ptr32 (p : Bool) : (riscV p).SplitlongPtr32 := by
  cases p <;> simp [ArchiConfig.SplitlongPtr32, riscV]
theorem powerpc_splitlong_ptr32 (p : Bool) : (powerpc p).SplitlongPtr32 := fun _ => rfl
theorem arm_splitlong_ptr32 (b : Bool) : (arm b).SplitlongPtr32 := fun _ => rfl

theorem aarch64_chooseNanIdem : aarch64.ChooseNanIdem :=
  ⟨Archi.choose_nan_64_idem, Archi.choose_nan_32_idem⟩
theorem x86_64_chooseNanIdem : x86_64.ChooseNanIdem := ⟨fun _ => rfl, fun _ => rfl⟩
theorem x86_32_chooseNanIdem : x86_32.ChooseNanIdem := ⟨fun _ => rfl, fun _ => rfl⟩
theorem riscV_chooseNanIdem (p : Bool) : (riscV p).ChooseNanIdem := ⟨fun _ => rfl, fun _ => rfl⟩
theorem powerpc_chooseNanIdem (p : Bool) : (powerpc p).ChooseNanIdem :=
  ⟨fun _ => rfl, fun _ => rfl⟩
theorem arm_chooseNanIdem (b : Bool) : (arm b).ChooseNanIdem :=
  ⟨Archi.choose_nan_64_idem, Archi.choose_nan_32_idem⟩

/-- The default NaNs of x86 and AArch64 differ in sign: the port's float
semantics (which follows AArch64) therefore does not describe x86 NaN
results bit-for-bit. -/
theorem x86_64_default_nan_ne_aarch64 : x86_64.default_nan_64 ≠ aarch64.default_nan_64 := by
  decide

end Targets
end CC
