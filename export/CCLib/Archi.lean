/-
  Target parameters — port of `<arch>/Archi.v` (aarch64 defaults).

  In CompCert every one of these is `Global Opaque`, deliberately preventing
  `simpl` from unfolding them so that target-specific facts cannot leak into
  proofs that should be target-independent. We keep the same discipline with
  `@[irreducible]`-style care: unfold them only via the `Archi.*` equations
  below, never by `simp [Archi.ptr64]` in generic lemmas.

  Only these knobs parameterize the whole semantics (measured over CompCert
  3.18): `ptr64`, `big_endian`, `align_int64`, `align_float64`, `splitlong`,
  plus float NaN-choice knobs (handled in `CCLib.Floats`).
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

end Archi
end CC
