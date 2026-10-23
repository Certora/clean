/-
  The functional model of `verif_insertionsort`, related to Mathlib's
  insertion sort.

  `insert` of VST's `verif_insertion_sort.v` is Mathlib's
  `List.orderedInsert` for the signed order `Int.cmp Cle` on 32-bit integers,
  and VST's `insertion_sort` (a right fold of `insert`) is
  `List.insertionSort`.  The C loop of `insertionsort` inserts the elements
  from left to right (`isortL`, a left fold); both folds produce a sorted
  permutation of the input, and the order is antisymmetric, so they are equal
  (`isortL_eq_insertionSort`).  This gives `insertionsort` VST's
  specification `insertionsort_spec` (`insertionsort_satisfies`).

  This file imports Mathlib for the theory of sorted lists, so it is kept
  apart from `verif_insertionsort`, which uses only the Lean core.
-/
import VST.progs.verif_insertionsort
import Mathlib.Data.List.Sort

open CC CC.Sep
open Insertionsort

namespace VST.Verif.InsertionSort

/-- The order of `insert`: `Int.cmp Cle x y`, signed `x ≤ y`. -/
def sle (x y : Integers.Int) : Prop := Integers.Int.cmp .Cle x y = true

instance : DecidableRel sle := fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem sle_iff (x y : Integers.Int) : sle x y ↔ x.toInt ≤ y.toInt := by
  show (!Integers.Int.lt y x) = true ↔ _
  have h : Integers.Int.lt y x = true ↔ y.toInt < x.toInt := BitVec.slt_iff_toInt_lt
  cases hh : Integers.Int.lt y x <;> simp_all

instance : Std.Total sle := ⟨fun x y => by simp only [sle_iff]; omega⟩
instance : IsTrans Integers.Int sle := ⟨fun x y z => by simp only [sle_iff]; omega⟩
instance : Std.Antisymm sle :=
  ⟨fun x y h1 h2 => BitVec.toInt_inj.mp (by rw [sle_iff] at h1 h2; omega)⟩

theorem insert_eq_orderedInsert (x : Integers.Int) :
    ∀ l, insert x l = l.orderedInsert sle x
  | [] => rfl
  | h :: t => by
    simp only [insert, List.orderedInsert_cons]
    by_cases hx : sle x h
    · simp [sle] at hx ⊢; simp [hx]
    · have hx' : Integers.Int.cmp .Cle x h = false := by simpa [sle] using hx
      simp [hx', hx, insert_eq_orderedInsert x t]

/-- VST's `insertion_sort` is Mathlib's `List.insertionSort`. -/
theorem insertionSort_eq (xs : List Integers.Int) :
    insertionSort xs = xs.insertionSort sle := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    simp only [insertionSort, List.foldr_cons, List.insertionSort_cons] at ih ⊢
    rw [ih, insert_eq_orderedInsert]

theorem isortL_aux (acc xs : List Integers.Int) (hacc : acc.Pairwise sle) :
    (xs.foldl (fun acc x => insert x acc) acc).Pairwise sle
      ∧ (xs.foldl (fun acc x => insert x acc) acc).Perm (acc ++ xs) := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons a l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (insert a acc) (by
      rw [insert_eq_orderedInsert]; exact hacc.orderedInsert a acc)
    refine ⟨h1, h2.trans ?_⟩
    rw [insert_eq_orderedInsert]
    exact ((List.perm_orderedInsert sle a acc).append_right l).trans
      (by simpa using (List.perm_middle (a := a) (l₁ := acc) (l₂ := l)).symm)

/-- **The list built by the C loop is VST's `insertion_sort`.** -/
theorem isortL_eq_insertionSort (xs : List Integers.Int) : isortL xs = insertionSort xs := by
  obtain ⟨h1, h2⟩ := isortL_aux [] xs List.Pairwise.nil
  have h2' : (isortL xs).Perm xs := by simpa [isortL] using h2
  rw [insertionSort_eq]
  exact List.Perm.eq_of_pairwise' h1 (List.pairwise_insertionSort sle xs)
    (h2'.trans (List.perm_insertionSort sle xs).symm)

/-- `insertionsort_spec` (VST's `insertionsort_spec`). -/
def insertionsortSpec (p : Permission) (contents : List Integers.Int) (x : Val) : Sep.FunSpec where
  tyargs := [tlistp]
  tyres := tlistp
  cc := cc_default
  pre := fun vargs hp => vargs = [x] ∧ listrepL p contents x hp
  post := fun r hp => listrepL p (insertionSort contents) r hp
  measure := fun _ => 0

/-- **`insertionsort` satisfies `insertionsort_spec`** (VST's
    `body_insertionsort`), when the symbol `insert` names `f_insert`. -/
theorem insertionsort_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (hpw : permOrder p .Writable = true) (contents : List Integers.Int)
    (x : Val) (bIns : Block) (hsym : Genv.findSymbol ge.genv_genv _insert = some bIns)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr bIns Integers.Ptrofs.zero)
      = some (.Internal f_insert)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_insertionsort)
      (insertionsortSpec p contents x) [x] := by
  have h := insertionsort_satisfiesL ge hcenv p hpw contents x bIns hsym hfind
  unfold insertionsortSpecL at h
  rw [isortL_eq_insertionSort] at h
  exact h

end VST.Verif.InsertionSort
