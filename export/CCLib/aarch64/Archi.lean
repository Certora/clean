/-
  Target parameters — port of `<arch>/Archi.v` (aarch64 defaults).

  In CompCert every one of these is `Global Opaque`, deliberately preventing
  `simpl` from unfolding them so that target-specific facts cannot leak into
  proofs that should be target-independent. Here they are plain `def`s (Lean
  does not enforce the opacity); the discipline is by convention only: do not
  unfold them, e.g. by `simp [Archi.ptr64]`, in lemmas meant to be generic.

  Only these knobs parameterize the whole semantics (measured over CompCert
  3.18): `ptr64`, `big_endian`, `align_int64`, `align_float64`, `splitlong`,
  plus the float NaN-choice knobs (`default_nan_64/32`, `choose_nan_64/32`,
  `float_of_single_preserves_sNaN`, `float_conversion_default_nan`, `fma_order`,
  `fma_invalid_mul_is_nan`).  The NaN knobs are modelled below exactly as in
  `aarch64/Archi.v` and are used by `CCLib.lib.Floats`.  A NaN is described, as in
  CompCert, by its sign and its payload; the payload is a `Nat` here (a
  `positive` in Rocq).
-/
namespace CC
namespace Archi

/-- 64-bit pointers?  (aarch64: yes) -/
def ptr64 : Bool := true

/-- Big-endian target?  (aarch64: no) -/
def big_endian : Bool := false

/-- Are 64-bit integer ops split into 32-bit ones? (only on 32-bit targets) -/
def splitlong : Bool := false

/-- Alignment required for `long long` / `double`. -/
def align_int64 : Nat := 8
def align_float64 : Nat := 8

/-- Word size of `ptrofs`, i.e. of pointer offsets. -/
def ptrWordsize : Nat := if ptr64 then 64 else 32

@[simp] theorem ptrWordsize_eq : ptrWordsize = 64 := rfl

/-! ## NaN knobs (`aarch64/Archi.v`) -/

/-- `default_nan_64`: positive sign, payload `2^51` (the quiet bit only). -/
def default_nan_64 : Bool × Nat := (false, 2 ^ 51)
/-- `default_nan_32`: positive sign, payload `2^22`. -/
def default_nan_32 : Bool × Nat := (false, 2 ^ 22)

/-- `choose_nan`: choose the first signaling NaN, if any; otherwise the first
NaN; otherwise the default NaN. -/
def choose_nan (is_signaling : Nat → Bool) (default : Bool × Nat)
    (l0 : List (Bool × Nat)) : Bool × Nat :=
  let rec choose_snan : List (Bool × Nat) → Bool × Nat
    | [] => match l0 with | n :: _ => n | [] => default
    | ((s, p) :: l1) => if is_signaling p then (s, p) else choose_snan l1
  match l0 with
  | [] => default
  | _ :: _ => choose_snan l0

theorem choose_nan_idem (is_signaling : Nat → Bool) (default : Bool × Nat)
    (n : Bool × Nat) :
    choose_nan is_signaling default [n, n] = choose_nan is_signaling default [n] := by
  obtain ⟨s, p⟩ := n
  simp only [choose_nan, choose_nan.choose_snan]
  cases is_signaling p <;> rfl

/-- `choose_nan_64`: a payload is signaling iff its bit 51 is clear. -/
def choose_nan_64 : List (Bool × Nat) → Bool × Nat :=
  choose_nan (fun p => !p.testBit 51) default_nan_64
/-- `choose_nan_32`: a payload is signaling iff its bit 22 is clear. -/
def choose_nan_32 : List (Bool × Nat) → Bool × Nat :=
  choose_nan (fun p => !p.testBit 22) default_nan_32

theorem choose_nan_64_idem (n : Bool × Nat) : choose_nan_64 [n, n] = choose_nan_64 [n] :=
  choose_nan_idem _ _ n
theorem choose_nan_32_idem (n : Bool × Nat) : choose_nan_32 [n, n] = choose_nan_32 [n] :=
  choose_nan_idem _ _ n

/-- `fma_order`: on ARM, `fma x y z` examines `z` first, then `x`, then `y`. -/
def fma_order {A : Type} (x y z : A) : A × A × A := (z, x, y)

/-- `fma_invalid_mul_is_nan`: `fma 0 ∞ nan` returns the default NaN. -/
def fma_invalid_mul_is_nan : Bool := true
/-- `float_of_single_preserves_sNaN` -/
def float_of_single_preserves_sNaN : Bool := false
/-- `float_conversion_default_nan` -/
def float_conversion_default_nan : Bool := false

end Archi
end CC
