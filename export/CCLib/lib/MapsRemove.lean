/-
  The remaining `PTree` theorems of `lib/Maps.v` about `elements`,
  `remove` and `cardinal`: `elements_extensional`, `elements_remove`, and
  `PTree_Properties.cardinal_set`; and the agreement of the structural
  `cardinal` of `CCLib.lib.MapsProperties` with Rocq's definition
  `length (elements m)`.

  Rocq derives `elements_extensional` from `extensionality` (its trees are
  canonical).  The Lean `PTree` is not canonical (see `CCLib.lib.Maps`), but
  `elements` only depends on the contents, which is what is proved here.
-/
import CCLib.lib.MapsProperties

namespace CC
namespace PTree
variable {A : Type}

/-! ## `elements` depends only on the contents -/

/-- `elemsAux` puts its result in front of the accumulator. -/
theorem elemsAux_acc (m : PTree A) (rp : List Bool) (acc : List (Positive × A)) :
    elemsAux m rp acc = elemsAux m rp [] ++ acc := by
  induction m generalizing rp acc with
  | Leaf => rfl
  | Node l o r ihl ihr =>
    simp only [elemsAux]
    cases o with
    | none => rw [ihl _ (elemsAux r _ acc), ihl _ (elemsAux r _ []), ihr _ acc]; simp
    | some v =>
      rw [ihl _ (_ :: elemsAux r _ acc), ihl _ (_ :: elemsAux r _ []), ihr _ acc]; simp

theorem elemsAux_extensional : ∀ (m n : PTree A), (∀ i, get i m = get i n) →
    ∀ rp acc, elemsAux m rp acc = elemsAux n rp acc
  | .Leaf, n, h, rp, acc =>
    (elemsAux_empty n (fun i => (h i).symm.trans (get_leaf i)) rp acc).symm
  | .Node l o r, .Leaf, h, rp, acc =>
    elemsAux_empty _ (fun i => (h i).trans (get_leaf i)) rp acc
  | .Node l o r, .Node l' o' r', h, rp, acc => by
    have ho : o = o' := h .xH
    subst ho
    simp only [elemsAux]
    rw [elemsAux_extensional r r' (fun i => h (.xI i)),
      elemsAux_extensional l l' (fun i => h (.xO i))]

/-- `PTree.elements_extensional` -/
theorem elements_extensional (m n : PTree A) (h : ∀ i, get i m = get i n) :
    elements m = elements n :=
  elemsAux_extensional m n h [] []

/-! ## `elements` and `remove` -/

theorem elemsAux_remove : ∀ (m : PTree A) (i : Positive) (v : A) (rp : List Bool)
    (acc : List (Positive × A)), get i m = some v →
    ∃ l1 l2, elemsAux m rp acc = l1 ++ (prependPath rp i, v) :: l2
      ∧ elemsAux (remove i m) rp acc = l1 ++ l2
  | .Leaf, i, v, rp, acc, h => by simp at h
  | .Node l o r, .xH, v, rp, acc, h => by
    simp only [get] at h
    subst h
    refine ⟨elemsAux l (false :: rp) [], elemsAux r (true :: rp) acc, ?_, ?_⟩
    · simp only [elemsAux]
      rw [elemsAux_acc]
      rfl
    · simp only [remove, elemsAux]
      rw [elemsAux_acc]
  | .Node l o r, .xO ii, v, rp, acc, h => by
    simp only [get] at h
    obtain ⟨l1, l2, h1, h2⟩ := elemsAux_remove l ii v (false :: rp)
      (match o with
       | some a => (keyOfRevPath rp, a) :: elemsAux r (true :: rp) acc
       | none => elemsAux r (true :: rp) acc) h
    refine ⟨l1, l2, ?_, ?_⟩
    · simp only [elemsAux]; exact h1
    · simp only [remove, elemsAux]; exact h2
  | .Node l o r, .xI ii, v, rp, acc, h => by
    simp only [get] at h
    obtain ⟨l1, l2, h1, h2⟩ := elemsAux_remove r ii v (true :: rp) acc h
    cases o with
    | none =>
      refine ⟨elemsAux l (false :: rp) [] ++ l1, l2, ?_, ?_⟩
      · simp only [elemsAux]
        rw [elemsAux_acc, h1, List.append_assoc]
        rfl
      · simp only [remove, elemsAux]
        rw [elemsAux_acc, h2, List.append_assoc]
    | some a =>
      refine ⟨elemsAux l (false :: rp) [] ++ (keyOfRevPath rp, a) :: l1, l2, ?_, ?_⟩
      · simp only [elemsAux]
        rw [elemsAux_acc, h1, List.append_assoc]
        rfl
      · simp only [remove, elemsAux]
        rw [elemsAux_acc, h2, List.append_assoc]
        rfl

/-- `PTree.elements_remove` -/
theorem elements_remove (i : Positive) (v : A) (m : PTree A) (h : get i m = some v) :
    ∃ l1 l2, elements m = l1 ++ (i, v) :: l2 ∧ elements (remove i m) = l1 ++ l2 :=
  elemsAux_remove m i v [] [] h

/-! ## `cardinal` -/

theorem length_elemsAux (m : PTree A) (rp : List Bool) (acc : List (Positive × A)) :
    (elemsAux m rp acc).length = cardinal m + acc.length := by
  induction m generalizing rp acc with
  | Leaf => simp [elemsAux, cardinal]
  | Node l o r ihl ihr =>
    simp only [elemsAux, cardinal]
    cases o <;> simp [ihl, ihr] <;> omega

/-- The structural `cardinal` is Rocq's `PTree_Properties.cardinal`,
    `length (elements m)`. -/
theorem cardinal_eq_length (m : PTree A) : cardinal m = (elements m).length := by
  simp [elements, length_elemsAux]

/-- Setting an unbound key adds one binding. -/
theorem cardinal_set_none (x : Positive) (y : A) (m : PTree A) (h : get x m = none) :
    cardinal (set x y m) = cardinal m + 1 := by
  induction x generalizing m with
  | xH => cases m <;> simp_all [set, get, cardinal] <;> omega
  | xO ii ih =>
    cases m with
    | Leaf =>
      have := ih Leaf (get_leaf ii)
      simp only [set, cardinal] at this ⊢; simp at this ⊢; omega
    | Node l o r =>
      have := ih l h
      simp only [set, cardinal]; omega
  | xI ii ih =>
    cases m with
    | Leaf =>
      have := ih Leaf (get_leaf ii)
      simp only [set, cardinal] at this ⊢; simp at this ⊢; omega
    | Node l o r =>
      have := ih r h
      simp only [set, cardinal]; omega

/-- `PTree_Properties.cardinal_set` -/
theorem cardinal_set (x : Positive) (y : A) (m : PTree A) (h : get x m = none) :
    cardinal m < cardinal (set x y m) := by
  rw [cardinal_set_none x y m h]; omega

end PTree
end CC
