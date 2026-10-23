/-
  Port of `MenhirLib/Validator_classes.v`.

  Rocq synthesises the executable validators from their specifications with
  type-class instances of `IsValidator P b` (meaning `b = true → P`).  The
  Lean port writes the boolean validators explicitly and proves them sound
  directly; this file keeps the notion and the generic soundness lemmas they
  use.
-/
import CCLib.MenhirLib.Alphabet

namespace CC
namespace MenhirLib

/-- `b` is a sound validator for `P`. -/
def IsValidator (P : Prop) (b : Bool) : Prop := b = true → P

theorem is_validator_true : IsValidator True true := fun _ => trivial

theorem is_validator_eq_true (b : Bool) : IsValidator (b = true) b := id

theorem is_validator_and {P1 P2 : Prop} {b1 b2 : Bool}
    (h1 : IsValidator P1 b1) (h2 : IsValidator P2 b2) : IsValidator (P1 ∧ P2) (b1 && b2) := by
  intro h
  rw [Bool.and_eq_true] at h
  exact ⟨h1 h.1, h2 h.2⟩

/-- Quantification over a finite type is validated by `List.all` over the list
of its elements. -/
theorem is_validator_forall_finite {A : Type} [Alphabet A] {P : A → Prop} {b : A → Bool}
    (h : ∀ x, IsValidator (P x) (b x)) : IsValidator (∀ x, P x) ((all_list : List A).all b) := by
  intro hb x
  exact h x (List.all_eq_true.1 hb x (all_list_forall x))

/-- The same, unfolded: a `List.all` over all the elements of a finite type
gives the property for every element. -/
theorem all_list_all_spec {A : Type} [Alphabet A] {b : A → Bool}
    (h : (all_list : List A).all b = true) (x : A) : b x = true :=
  List.all_eq_true.1 h x (all_list_forall x)

end MenhirLib
end CC
