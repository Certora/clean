/-
  Port of `MenhirLib/Alphabet.v`: finite alphabets.

  Rocq's `Alphabet` bundles a total order (`Comparable`), the fact that the
  order is Leibniz (`ComparableLeibnizEq`) and finiteness (`Finite`).  The
  order is only used by Rocq to build the AVL sets and maps of the
  completeness validator.  The Lean port replaces those by bit masks (see
  `ASet` below), so an alphabet here is an injection into `Nat` (which gives
  decidable equality and the bit-mask sets) together with the list of all its
  elements.  As in Rocq, alphabets are usually built from a `Numbered`
  instance (`NumberedAlphabet`), whose injection is bounded.
-/

namespace CC
namespace MenhirLib

/-- A finite type with an injection into `Nat` (Rocq's `Alphabet`, see the
header for the difference). -/
class Alphabet (A : Type) where
  /-- An injection into `Nat`. -/
  inj : A → Nat
  inj_inj : ∀ x y, inj x = inj y → x = y
  /-- All the elements of the type (Rocq's `Finite.all_list`). -/
  all_list : List A
  all_list_forall : ∀ x, x ∈ all_list

export Alphabet (all_list all_list_forall)

/-- Decidable equality of an alphabet, through its injection. -/
@[reducible] def Alphabet.decEq {A : Type} [Alphabet A] : DecidableEq A := fun x y =>
  if h : Alphabet.inj x = Alphabet.inj y then isTrue (Alphabet.inj_inj x y h)
  else isFalse (fun e => h (e ▸ rfl))

/-- Every alphabet has decidable equality (scoped: other types keep their own
instances). -/
scoped instance (priority := low) instDecEqAlphabet {A : Type} [Alphabet A] : DecidableEq A :=
  Alphabet.decEq

/-- The [Numbered] class provides a convenient way to build [Alphabet]
instances, with a good computational complexity: an injection into `Nat`
bounded by `inj_bound`, with a left inverse `surj`. -/
class Numbered (A : Type) where
  inj : A → Nat
  surj : Nat → A
  surj_inj_compat : ∀ x, surj (inj x) = x
  inj_bound : Nat
  inj_bound_spec : ∀ x, inj x < inj_bound

/-- The alphabet of a numbered type. -/
@[reducible] def NumberedAlphabet {A : Type} (N : Numbered A) : Alphabet A where
  inj := N.inj
  inj_inj x y h := by rw [← N.surj_inj_compat x, ← N.surj_inj_compat y, h]
  all_list := (List.range N.inj_bound).map N.surj
  all_list_forall x := by
    rw [List.mem_map]
    exact ⟨N.inj x, List.mem_range.2 (N.inj_bound_spec x), N.surj_inj_compat x⟩

/-! ## Finite sets of letters as bit masks

These replace the `FSetAVL` sets of terminals used by Rocq's completeness
validator. -/

/-- A finite set of letters of an alphabet, as a bit mask over `Alphabet.inj`. -/
structure ASet (A : Type) [Alphabet A] where
  mask : Nat

namespace ASet
variable {A : Type} [Alphabet A]

def empty : ASet A := ⟨0⟩
def singleton (x : A) : ASet A := ⟨1 <<< Alphabet.inj x⟩
def union (s1 s2 : ASet A) : ASet A := ⟨s1.mask ||| s2.mask⟩
def add (x : A) (s : ASet A) : ASet A := union (singleton x) s
def mem (x : A) (s : ASet A) : Bool := s.mask.testBit (Alphabet.inj x)
def subset (s1 s2 : ASet A) : Bool := s1.mask &&& s2.mask == s1.mask
def ofList (l : List A) : ASet A := l.foldl (fun acc x => add x acc) empty

/-- Membership. -/
def In (x : A) (s : ASet A) : Prop := mem x s = true

/-- Inclusion. -/
def Subset (s1 s2 : ASet A) : Prop := ∀ x, In x s1 → In x s2

theorem not_in_empty (x : A) : ¬ In x (empty : ASet A) := by
  simp [In, mem, empty]

theorem in_singleton_iff (x y : A) : In y (singleton x) ↔ y = x := by
  simp only [In, mem, singleton, Nat.one_shiftLeft, Nat.testBit_two_pow]
  constructor
  · intro h
    have : Alphabet.inj x = Alphabet.inj y := by simpa using h
    exact (Alphabet.inj_inj _ _ this).symm
  · intro h; subst h; simp

theorem in_union_iff (x : A) (s1 s2 : ASet A) : In x (union s1 s2) ↔ In x s1 ∨ In x s2 := by
  simp [In, mem, union, Nat.testBit_or]

theorem in_add_iff (x y : A) (s : ASet A) : In y (add x s) ↔ y = x ∨ In y s := by
  rw [add, in_union_iff, in_singleton_iff]

theorem in_ofList_iff (x : A) (l : List A) : In x (ofList l) ↔ x ∈ l := by
  have key : ∀ (acc : ASet A),
      In x (l.foldl (fun acc x => add x acc) acc) ↔ x ∈ l ∨ In x acc := by
    induction l with
    | nil => intro acc; simp
    | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih, in_add_iff, List.mem_cons, or_assoc]
      exact or_left_comm
  rw [ofList, key]
  exact ⟨fun h => h.elim id (fun h' => absurd h' (not_in_empty x)), Or.inl⟩

theorem subset_spec {s1 s2 : ASet A} (h : subset s1 s2 = true) : Subset s1 s2 := by
  intro x hx
  simp only [subset, beq_iff_eq] at h
  simp only [In, mem] at hx ⊢
  have : (s1.mask &&& s2.mask).testBit (Alphabet.inj x) = true := by rw [h]; exact hx
  rw [Nat.testBit_and] at this
  simp_all

end ASet

end MenhirLib
end CC
