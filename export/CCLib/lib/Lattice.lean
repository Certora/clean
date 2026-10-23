/-
  Semi-lattices for dataflow analysis — port of the `SEMILATTICE`
  signature of `lib/Lattice.v` and of its simplest instance `LBoolean`.

  Differences from Rocq: the module type `SEMILATTICE` is a Lean class
  `Semilattice t`; the functors `LPMap`, `LFSet`, `LOption`, `LProd`,
  `LSum` are not ported yet (they are needed by the value and
  liveness analyses, which are not ported).
-/
import CCLib.lib.Positive

namespace CC

/-- `Lattice.SEMILATTICE` -/
class Semilattice (t : Type) where
  eq : t → t → Prop
  eq_refl : ∀ x, eq x x
  eq_sym : ∀ {x y}, eq x y → eq y x
  eq_trans : ∀ {x y z}, eq x y → eq y z → eq x z
  beq : t → t → Bool
  beq_correct : ∀ {x y}, beq x y = true → eq x y
  ge : t → t → Prop
  ge_refl : ∀ {x y}, eq x y → ge x y
  ge_trans : ∀ {x y z}, ge x y → ge y z → ge x z
  bot : t
  ge_bot : ∀ x, ge x bot
  lub : t → t → t
  ge_lub_left : ∀ x y, ge (lub x y) x
  ge_lub_right : ∀ x y, ge (lub x y) y

/-- `Lattice.LBoolean`: booleans ordered by `true ≥ false`. -/
instance LBoolean : Semilattice Bool where
  eq x y := x = y
  eq_refl _ := rfl
  eq_sym h := h.symm
  eq_trans h1 h2 := h1.trans h2
  beq x y := x == y
  beq_correct h := by simpa using h
  ge x y := x = y ∨ x = true
  ge_refl h := .inl h
  ge_trans := by decide
  bot := false
  ge_bot := by decide
  lub x y := x || y
  ge_lub_left := by decide
  ge_lub_right := by decide

end CC
