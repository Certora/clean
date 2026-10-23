/-
  Port of `lib/Heaps.v`: a heap data structure (splay heaps, following
  C. Okasaki, "Purely functional data structures", section 5.4), with duplicate
  elements eliminated.

  Rocq's functor `SplayHeapSet (E : OrderedType)` becomes the namespace
  `SplayHeapSet`, parameterised by an `OrderedType` instance (see
  `lib/Ordered.lean`).  The raw implementation and its invariant live in
  `SplayHeapSet.R`; the wrapped type `SplayHeapSet.t` is the subtype of binary
  search trees.  `PHeap` is the instantiation over `Positive`.

  Differences from Rocq: element equality is Lean's equality (Rocq's `E.eq`);
  the functional induction schemes are replaced by `fun_induction`.
-/
import CCLib.lib.Ordered

namespace CC
namespace SplayHeapSet

open OrderedType

variable {E : Type _} [OrderedType E]

namespace R

/-- Raw heaps: binary trees; the search-tree invariant is `bst`. -/
inductive heap (E : Type _) : Type _ where
  | Empty : heap E
  | Node (l : heap E) (x : E) (r : heap E) : heap E


def partition (pivot : E) : heap E → heap E × heap E
  | .Empty => (.Empty, .Empty)
  | .Node a x b =>
    match OrderedType.compare x pivot with
    | .eq => (a, b)
    | .lt =>
      match b with
      | .Empty => (.Node a x b, .Empty)
      | .Node b1 y b2 =>
        match OrderedType.compare y pivot with
        | .eq => (.Node a x b1, b2)
        | .lt =>
          let p := partition pivot b2
          (.Node (.Node a x b1) y p.1, p.2)
        | .gt =>
          let p := partition pivot b1
          (.Node a x p.1, .Node p.2 y b2)
    | .gt =>
      match a with
      | .Empty => (.Empty, .Node a x b)
      | .Node a1 y a2 =>
        match OrderedType.compare y pivot with
        | .eq => (a1, .Node a2 x b)
        | .lt =>
          let p := partition pivot a2
          (.Node a1 y p.1, .Node p.2 x b)
        | .gt =>
          let p := partition pivot a1
          (p.1, .Node p.2 y (.Node a2 x b))

def insert (x : E) (h : heap E) : heap E :=
  let p := partition x h
  .Node p.1 x p.2

def findMin : heap E → Option E
  | .Empty => none
  | .Node .Empty x _ => some x
  | .Node a@(.Node _ _ _) _ _ => findMin a

def deleteMin : heap E → heap E
  | .Empty => .Empty
  | .Node .Empty _ b => b
  | .Node (.Node .Empty _ b) y c => .Node b y c
  | .Node (.Node a@(.Node _ _ _) x b) y c => .Node (deleteMin a) x (.Node b y c)

def findMax : heap E → Option E
  | .Empty => none
  | .Node _ x .Empty => some x
  | .Node _ _ b@(.Node _ _ _) => findMax b

def deleteMax : heap E → heap E
  | .Empty => .Empty
  | .Node b _ .Empty => b
  | .Node b x (.Node c _ .Empty) => .Node b x c
  | .Node a x (.Node b y c@(.Node _ _ _)) => .Node (.Node a x b) y (deleteMax c)

/-- Membership (specification). -/
def In (x : E) : heap E → Prop
  | .Empty => False
  | .Node a y b => In x a ∨ x = y ∨ In x b

/-- All elements of `h` are smaller than `x`. -/
def lt_heap : heap E → E → Prop
  | .Empty, _ => True
  | .Node a y b, x => lt_heap a x ∧ lt y x ∧ lt_heap b x

/-- All elements of `h` are greater than `x`. -/
def gt_heap : heap E → E → Prop
  | .Empty, _ => True
  | .Node a y b, x => gt_heap a x ∧ lt x y ∧ gt_heap b x

/-- Binary search tree invariant. -/
def bst : heap E → Prop
  | .Empty => True
  | .Node a x b => bst a ∧ bst b ∧ lt_heap a x ∧ gt_heap b x

def le (x y : E) : Prop := x = y ∨ lt x y

theorem le_lt_trans {x1 x2 x3 : E} (h1 : le x1 x2) (h2 : lt x2 x3) : lt x1 x3 := by
  rcases h1 with e | h
  · subst e; exact h2
  · exact OrderedType.lt_trans _ _ _ h h2

theorem lt_le_trans {x1 x2 x3 : E} (h1 : lt x1 x2) (h2 : le x2 x3) : lt x1 x3 := by
  rcases h2 with e | h
  · subst e; exact h1
  · exact OrderedType.lt_trans _ _ _ h1 h

theorem le_trans {x1 x2 x3 : E} (h1 : le x1 x2) (h2 : le x2 x3) : le x1 x3 := by
  rcases h1 with e | h
  · subst e; exact h2
  · exact .inr (lt_le_trans h h2)

theorem lt_heap_trans {x y : E} (hxy : le x y) : ∀ h : heap E, lt_heap h x → lt_heap h y
  | .Empty, _ => trivial
  | .Node a _ b, ⟨ha, hz, hb⟩ =>
    ⟨lt_heap_trans hxy a ha, lt_le_trans hz hxy, lt_heap_trans hxy b hb⟩

theorem gt_heap_trans {x y : E} (hxy : le y x) : ∀ h : heap E, gt_heap h x → gt_heap h y
  | .Empty, _ => trivial
  | .Node a _ b, ⟨ha, hz, hb⟩ =>
    ⟨gt_heap_trans hxy a ha, le_lt_trans hxy hz, gt_heap_trans hxy b hb⟩

theorem lt_heap_In {x y : E} : ∀ {h : heap E}, lt_heap h x → In y h → lt y x
  | .Node a _ b, ⟨ha, hz, hb⟩, hin => by
    rcases hin with hin | e | hin
    · exact lt_heap_In ha hin
    · subst e; exact hz
    · exact lt_heap_In hb hin

theorem gt_heap_In {x y : E} : ∀ {h : heap E}, gt_heap h x → In y h → lt x y
  | .Node a _ b, ⟨ha, hz, hb⟩, hin => by
    rcases hin with hin | e | hin
    · exact gt_heap_In ha hin
    · subst e; exact hz
    · exact gt_heap_In hb hin

/-! Properties of `partition` -/

theorem compare_cases (x y : E) :
    (OrderedType.compare x y = .lt ∧ lt x y) ∨ (OrderedType.compare x y = .eq ∧ x = y) ∨
    (OrderedType.compare x y = .gt ∧ lt y x) := by
  have := compare_spec x y
  revert this
  cases OrderedType.compare x y <;> simp_all

theorem In_partition (x pivot : E) (hne : x ≠ pivot) (h : heap E) (hb : bst h) :
    In x h ↔ In x (partition pivot h).1 ∨ In x (partition pivot h).2 := by
  fun_induction partition pivot h <;>
    simp only [compare_lt_iff, compare_eq_iff, compare_gt_iff] at * <;>
    simp only [In, bst] at * <;> grind

theorem lt_heap_lt {x y : E} {h : heap E} (hl : lt_heap h x) (hxy : lt x y) : lt_heap h y :=
  lt_heap_trans (.inr hxy) h hl
theorem gt_heap_lt {x y : E} {h : heap E} (hl : gt_heap h x) (hxy : lt y x) : gt_heap h y :=
  gt_heap_trans (.inr hxy) h hl
theorem partition_lt (x pivot : E) (h : heap E) (hl : lt_heap h x) :
    lt_heap (partition pivot h).1 x ∧ lt_heap (partition pivot h).2 x := by
  fun_induction partition pivot h <;> simp only [lt_heap] at * <;> grind
theorem partition_gt (x pivot : E) (h : heap E) (hl : gt_heap h x) :
    gt_heap (partition pivot h).1 x ∧ gt_heap (partition pivot h).2 x := by
  fun_induction partition pivot h <;> simp only [gt_heap] at * <;> grind
theorem partition_split (pivot : E) (h : heap E) (hb : bst h) :
    lt_heap (partition pivot h).1 pivot ∧ gt_heap (partition pivot h).2 pivot := by
  fun_induction partition pivot h <;>
    simp only [compare_lt_iff, compare_eq_iff, compare_gt_iff] at * <;>
    simp only [lt_heap, gt_heap, bst] at * <;> grind [lt_heap_lt, gt_heap_lt]
theorem partition_lt_fst {x pivot : E} {h : heap E} (hl : lt_heap h x) :
    lt_heap (partition pivot h).1 x := (partition_lt x pivot h hl).1
theorem partition_lt_snd {x pivot : E} {h : heap E} (hl : lt_heap h x) :
    lt_heap (partition pivot h).2 x := (partition_lt x pivot h hl).2
theorem partition_gt_fst {x pivot : E} {h : heap E} (hl : gt_heap h x) :
    gt_heap (partition pivot h).1 x := (partition_gt x pivot h hl).1
theorem partition_gt_snd {x pivot : E} {h : heap E} (hl : gt_heap h x) :
    gt_heap (partition pivot h).2 x := (partition_gt x pivot h hl).2
theorem partition_bst (pivot : E) (h : heap E) (hb : bst h) :
    bst (partition pivot h).1 ∧ bst (partition pivot h).2 := by
  fun_induction partition pivot h <;>
    simp only [compare_lt_iff, compare_eq_iff, compare_gt_iff] at * <;>
    simp only [lt_heap, gt_heap, bst] at * <;>
    grind [partition_lt_fst, partition_lt_snd, partition_gt_fst, partition_gt_snd, partition_split, lt_heap_lt, gt_heap_lt]
theorem insert_bst (x : E) (h : heap E) (hb : bst h) : bst (insert x h) := by
  have := partition_bst x h hb
  have := partition_split x h hb
  simp only [insert, bst]; grind

theorem In_insert (x : E) (h : heap E) (y : E) (hb : bst h) :
    In y (insert x h) ↔ y = x ∨ In y h := by
  simp only [insert, In]
  by_cases e : y = x
  · simp [e]
  · rw [In_partition y x e h hb]; grind

theorem deleteMin_lt (x : E) (h : heap E) (hl : lt_heap h x) : lt_heap (deleteMin h) x := by
  fun_induction deleteMin h <;> simp only [lt_heap] at * <;> grind

theorem deleteMin_bst (h : heap E) (hb : bst h) : bst (deleteMin h) := by
  fun_induction deleteMin h <;> simp only [bst] at * <;>
    grind [deleteMin_lt, gt_heap_lt, lt_heap, gt_heap]

omit [OrderedType E] in
theorem In_deleteMin (y x : E) (h : heap E) (hf : findMin h = some x) :
    In y h ↔ y = x ∨ In y (deleteMin h) := by
  fun_induction deleteMin h generalizing x <;> simp only [findMin, In] at * <;> grind

omit [OrderedType E] in
theorem In_findMin {x : E} {h : heap E} (hf : findMin h = some x) : In x h := by
  fun_induction findMin h <;> simp_all [In]

theorem findMin_min : ∀ {x : E} {h : heap E}, findMin h = some x → bst h →
    ∀ y, In y h → le x y
  | _, .Empty, _, _, _, hy => hy.elim
  | x, .Node .Empty x' b, hf, ⟨_, _, _, hgt⟩, y, hy => by
    simp only [findMin, Option.some.injEq] at hf
    subst hf
    rcases hy with hy | e | hy
    · exact hy.elim
    · exact .inl e.symm
    · exact .inr (gt_heap_In hgt hy)
  | x, .Node (.Node a1 z a2) x' b, hf, ⟨ha, _, hlt, hgt⟩, y, hy => by
    simp only [findMin] at hf
    have hxx' := lt_heap_In hlt (In_findMin hf)
    rcases hy with hy | e | hy
    · exact findMin_min hf ha y hy
    · subst e; exact .inr hxx'
    · exact .inr (OrderedType.lt_trans _ _ _ hxx' (gt_heap_In hgt hy))

omit [OrderedType E] in
theorem findMin_empty (h : heap E) (hne : h ≠ .Empty) : findMin h ≠ none := by
  fun_induction findMin h <;> simp_all

theorem deleteMax_gt (x : E) (h : heap E) (hl : gt_heap h x) : gt_heap (deleteMax h) x := by
  fun_induction deleteMax h <;> simp only [gt_heap] at * <;> grind

theorem deleteMax_bst (h : heap E) (hb : bst h) : bst (deleteMax h) := by
  fun_induction deleteMax h <;> simp only [bst] at * <;>
    grind [deleteMax_gt, lt_heap_lt, lt_heap, gt_heap]

omit [OrderedType E] in
theorem In_deleteMax (y x : E) (h : heap E) (hf : findMax h = some x) :
    In y h ↔ y = x ∨ In y (deleteMax h) := by
  fun_induction deleteMax h generalizing x <;> simp only [findMax, In] at * <;> grind

omit [OrderedType E] in
theorem In_findMax {x : E} {h : heap E} (hf : findMax h = some x) : In x h := by
  fun_induction findMax h <;> simp_all [In]

theorem findMax_max : ∀ {x : E} {h : heap E}, findMax h = some x → bst h →
    ∀ y, In y h → le y x
  | _, .Empty, _, _, _, hy => hy.elim
  | x, .Node a x' .Empty, hf, ⟨_, _, hlt, _⟩, y, hy => by
    simp only [findMax, Option.some.injEq] at hf
    subst hf
    rcases hy with hy | e | hy
    · exact .inr (lt_heap_In hlt hy)
    · exact .inl e
    · exact hy.elim
  | x, .Node a x' (.Node b1 z b2), hf, ⟨_, hb, hlt, hgt⟩, y, hy => by
    simp only [findMax] at hf
    have hxx' := gt_heap_In hgt (In_findMax hf)
    rcases hy with hy | e | hy
    · exact .inr (OrderedType.lt_trans _ _ _ (lt_heap_In hlt hy) hxx')
    · subst e; exact .inr hxx'
    · exact findMax_max hf hb y hy

omit [OrderedType E] in
theorem findMax_empty (h : heap E) (hne : h ≠ .Empty) : findMax h ≠ none := by
  fun_induction findMax h <;> simp_all

end R

open R

/-- Heaps: raw heaps satisfying the binary-search-tree invariant. -/
def t (E : Type _) [OrderedType E] := { h : R.heap E // R.bst h }

def empty : t E := ⟨.Empty, trivial⟩

def insert (x : E) (h : t E) : t E := ⟨R.insert x h.1, R.insert_bst x h.1 h.2⟩

def findMin (h : t E) : Option E := R.findMin h.1

def deleteMin (h : t E) : t E := ⟨R.deleteMin h.1, R.deleteMin_bst h.1 h.2⟩

def findMax (h : t E) : Option E := R.findMax h.1

def deleteMax (h : t E) : t E := ⟨R.deleteMax h.1, R.deleteMax_bst h.1 h.2⟩

/-- Membership (for specification). -/
def In (x : E) (h : t E) : Prop := R.In x h.1

theorem In_empty (x : E) : ¬ In x (empty : t E) := id

theorem In_insert (x : E) (h : t E) (y : E) : In y (insert x h) ↔ y = x ∨ In y h :=
  R.In_insert x h.1 y h.2

theorem findMin_empty (h : t E) (y : E) (hf : findMin h = none) : ¬ In y h := by
  intro hin
  cases e : h.1 with
  | Empty => simp only [In, e, R.In] at hin
  | Node a x b => exact R.findMin_empty h.1 (by simp [e]) hf

theorem findMin_min (h : t E) (x y : E) (hf : findMin h = some x) (hin : In y h) :
    x = y ∨ OrderedType.lt x y :=
  R.findMin_min hf h.2 y hin

theorem In_deleteMin (h : t E) (x y : E) (hf : findMin h = some x) :
    In y h ↔ y = x ∨ In y (deleteMin h) :=
  R.In_deleteMin y x h.1 hf

theorem findMax_empty (h : t E) (y : E) (hf : findMax h = none) : ¬ In y h := by
  intro hin
  cases e : h.1 with
  | Empty => simp only [In, e, R.In] at hin
  | Node a x b => exact R.findMax_empty h.1 (by simp [e]) hf

theorem findMax_max (h : t E) (x y : E) (hf : findMax h = some x) (hin : In y h) :
    y = x ∨ OrderedType.lt y x :=
  R.findMax_max hf h.2 y hin

theorem In_deleteMax (h : t E) (x y : E) (hf : findMax h = some x) :
    In y h ↔ y = x ∨ In y (deleteMax h) :=
  R.In_deleteMax y x h.1 hf

end SplayHeapSet

/-- Splay heaps over `Positive` (Rocq's `PHeap`). -/
abbrev PHeap := SplayHeapSet.t Positive

end CC
