/-
  First part of the AVL finite sets (split from `CCLib.lib.FSetAVL`; Rocq standard library `MSetAVL`): the raw trees, membership, the search-tree invariant and the basic operations.
-/
import CCLib.lib.Ordered

namespace CC
namespace FSetAVL

open OrderedType

variable {E : Type _} [OrderedType E]

namespace Raw

/-- `Raw.tree`: binary trees whose nodes carry their height. -/
inductive tree (E : Type _) : Type _ where
  | Leaf : tree E
  | Node (h : Nat) (l : tree E) (x : E) (r : tree E) : tree E
  deriving Inhabited

open tree

/-! ### Membership, search-tree invariant, in-order traversal -/

/-- `Raw.In` -/
inductive In (x : E) : tree E → Prop where
  | IsRoot {h l y r} : x = y → In x (Node h l y r)
  | InLeft {h l y r} : In x l → In x (Node h l y r)
  | InRight {h l y r} : In x r → In x (Node h l y r)

omit [OrderedType E] in
theorem In_node_iff {x : E} {h l y r} :
    In x (Node h l y r) ↔ In x l ∨ x = y ∨ In x r := by
  constructor
  · intro hi; cases hi with
    | IsRoot e => exact .inr (.inl e)
    | InLeft hl => exact .inl hl
    | InRight hr => exact .inr (.inr hr)
  · rintro (hl | e | hr)
    · exact .InLeft hl
    · exact .IsRoot e
    · exact .InRight hr

omit [OrderedType E] in
theorem not_In_Leaf {x : E} : ¬ In x (Leaf : tree E) := fun h => nomatch h

/-- `Raw.lt_tree x s`: all elements of `s` are smaller than `x`. -/
def lt_tree (x : E) (s : tree E) : Prop := ∀ y, In y s → lt y x
/-- `Raw.gt_tree x s`: all elements of `s` are greater than `x`. -/
def gt_tree (x : E) (s : tree E) : Prop := ∀ y, In y s → lt x y

/-- `Raw.bst`: binary search trees (Rocq's `Raw.Ok`). -/
inductive bst : tree E → Prop where
  | leaf : bst Leaf
  | node {h l x r} : bst l → bst r → lt_tree x l → gt_tree x r → bst (Node h l x r)

/-- `Raw.elements`: the in-order list of elements. -/
def elements : tree E → List E
  | Leaf => []
  | Node _ l x r => elements l ++ x :: elements r

omit [OrderedType E] in
theorem In_iff_mem {x : E} : ∀ {s : tree E}, In x s ↔ x ∈ elements s
  | Leaf => by simp [elements, not_In_Leaf]
  | Node _ l y r => by
    rw [In_node_iff, In_iff_mem, In_iff_mem]
    simp [elements, List.mem_append, List.mem_cons]

theorem bst_iff_pairwise : ∀ {s : tree E}, bst s ↔ (elements s).Pairwise lt
  | Leaf => by simp [elements]; exact .leaf
  | Node _ l x r => by
    rw [elements, List.pairwise_append, List.pairwise_cons]
    constructor
    · intro hb
      cases hb with
      | node hl hr ltl gtr =>
        refine ⟨bst_iff_pairwise.1 hl, ⟨fun y hy => gtr y (In_iff_mem.2 hy),
          bst_iff_pairwise.1 hr⟩, ?_⟩
        intro a ha b hb
        have hax := ltl a (In_iff_mem.2 ha)
        simp only [List.mem_cons] at hb
        rcases hb with e | hb
        · subst e; exact hax
        · exact lt_trans _ _ _ hax (gtr b (In_iff_mem.2 hb))
    · rintro ⟨hl, ⟨gtr, hr⟩, cross⟩
      refine .node (bst_iff_pairwise.2 hl) (bst_iff_pairwise.2 hr) ?_ ?_
      · intro y hy; exact cross y (In_iff_mem.1 hy) x (List.mem_cons_self ..)
      · intro y hy; exact gtr y (In_iff_mem.1 hy)

/-- Two trees with the same elements are equally search trees. -/
theorem bst_of_elements_eq {s s' : tree E} (h : elements s' = elements s) (hs : bst s) :
    bst s' := by
  rw [bst_iff_pairwise, h]; exact bst_iff_pairwise.1 hs

omit [OrderedType E] in
theorem In_of_elements_eq {s s' : tree E} (h : elements s' = elements s) {x : E} :
    In x s' ↔ In x s := by
  rw [In_iff_mem, In_iff_mem, h]

theorem bst_node_inv {h l x r} (hb : bst (Node h l x r : tree E)) :
    bst l ∧ bst r ∧ lt_tree x l ∧ gt_tree x r := by
  cases hb with
  | node a b c d => exact ⟨a, b, c, d⟩

/-! ### Basic operations -/

/-- `Raw.height` -/
def height : tree E → Nat
  | Leaf => 0
  | Node h _ _ _ => h

/-- `Raw.cardinal` -/
def cardinal : tree E → Nat
  | Leaf => 0
  | Node _ l _ r => cardinal l + 1 + cardinal r

/-- `Raw.empty` -/
def empty : tree E := Leaf

/-- `Raw.is_empty` -/
def is_empty : tree E → Bool
  | Leaf => true
  | _ => false

/-- `Raw.mem` -/
def mem (x : E) : tree E → Bool
  | Leaf => false
  | Node _ l y r =>
    match compare x y with
    | .lt => mem x l
    | .eq => true
    | .gt => mem x r

/-- `Raw.singleton` -/
def singleton (x : E) : tree E := Node 1 Leaf x Leaf

/-- `Raw.create` -/
def create (l : tree E) (x : E) (r : tree E) : tree E :=
  Node (max (height l) (height r) + 1) l x r

/-- `Raw.bal`: rebalancing (the `assert_false` cases are `create`). -/
def bal (l : tree E) (x : E) (r : tree E) : tree E :=
  let hl := height l
  let hr := height r
  if hl > hr + 2 then
    match l with
    | Leaf => create l x r
    | Node _ ll lx lr =>
      if height ll ≥ height lr then create ll lx (create lr x r)
      else
        match lr with
        | Leaf => create l x r
        | Node _ lrl lrx lrr => create (create ll lx lrl) lrx (create lrr x r)
  else if hr > hl + 2 then
    match r with
    | Leaf => create l x r
    | Node _ rl rx rr =>
      if height rr ≥ height rl then create (create l x rl) rx rr
      else
        match rl with
        | Leaf => create l x r
        | Node _ rll rlx rlr => create (create l x rll) rlx (create rlr rx rr)
  else create l x r

/-- `Raw.add` -/
def add (x : E) : tree E → tree E
  | Leaf => Node 1 Leaf x Leaf
  | Node h l y r =>
    match compare x y with
    | .lt => bal (add x l) y r
    | .eq => Node h l y r
    | .gt => bal l y (add x r)

/-- `Raw.join l x r`: a tree with the elements of `l`, `x` and `r`, assuming
`l < x < r`. -/
def join : tree E → E → tree E → tree E
  | Leaf, x, r => add x r
  | l@(Node lh ll lx lr), x, r =>
    match r with
    | Leaf => add x l
    | Node rh rl rx rr =>
      if lh > rh + 2 then bal ll lx (join lr x (Node rh rl rx rr))
      else if rh > lh + 2 then bal (join l x rl) rx rr
      else create l x (Node rh rl rx rr)
termination_by l _ r => sizeOf l + sizeOf r

/-- `Raw.remove_min l x r`: the tree `Node l x r` without its minimum, and
that minimum. -/
def remove_min : tree E → E → tree E → tree E × E
  | Leaf, x, r => (r, x)
  | Node _ ll lx lr, x, r =>
    let p := remove_min ll lx lr
    (bal p.1 x r, p.2)

/-- `Raw.merge s1 s2`: concatenation of two trees of similar heights,
assuming `s1 < s2`. -/
def merge : tree E → tree E → tree E
  | Leaf, s2 => s2
  | s1, Leaf => s1
  | s1, Node _ l2 x2 r2 =>
    let p := remove_min l2 x2 r2
    bal s1 p.2 p.1

/-- `Raw.remove` -/
def remove (x : E) : tree E → tree E
  | Leaf => Leaf
  | Node _ l y r =>
    match compare x y with
    | .lt => bal (remove x l) y r
    | .eq => merge l r
    | .gt => bal l y (remove x r)

/-- `Raw.min_elt` -/
def min_elt : tree E → Option E
  | Leaf => none
  | Node _ Leaf x _ => some x
  | Node _ l _ _ => min_elt l

/-- `Raw.max_elt` -/
def max_elt : tree E → Option E
  | Leaf => none
  | Node _ _ x Leaf => some x
  | Node _ _ _ r => max_elt r

/-- `Raw.concat s1 s2`: concatenation of two arbitrary trees, assuming
`s1 < s2`. -/
def concat : tree E → tree E → tree E
  | Leaf, s2 => s2
  | s1, Leaf => s1
  | s1, Node _ l2 x2 r2 =>
    let p := remove_min l2 x2 r2
    join s1 p.2 p.1

/-- `Raw.split x s`: the elements of `s` smaller than `x`, whether `x ∈ s`,
and the elements greater than `x`. -/
def split (x : E) : tree E → tree E × Bool × tree E
  | Leaf => (Leaf, false, Leaf)
  | Node _ l y r =>
    match compare x y with
    | .lt =>
      let p := split x l
      (p.1, p.2.1, join p.2.2 y r)
    | .eq => (l, true, r)
    | .gt =>
      let p := split x r
      (join l y p.1, p.2.1, p.2.2)

/-- `Raw.union` -/
def union : tree E → tree E → tree E
  | Leaf, s2 => s2
  | s1@(Node _ _ _ _), Leaf => s1
  | Node _ l1 x1 r1, s2@(Node _ _ _ _) =>
    let p := split x1 s2
    join (union l1 p.1) x1 (union r1 p.2.2)

/-- `Raw.inter` -/
def inter : tree E → tree E → tree E
  | Leaf, _ => Leaf
  | Node _ _ _ _, Leaf => Leaf
  | Node _ l1 x1 r1, s2@(Node _ _ _ _) =>
    let p := split x1 s2
    if p.2.1 then join (inter l1 p.1) x1 (inter r1 p.2.2)
    else concat (inter l1 p.1) (inter r1 p.2.2)

/-- `Raw.diff` -/
def diff : tree E → tree E → tree E
  | Leaf, _ => Leaf
  | s1@(Node _ _ _ _), Leaf => s1
  | Node _ l1 x1 r1, s2@(Node _ _ _ _) =>
    let p := split x1 s2
    if p.2.1 then concat (diff l1 p.1) (diff r1 p.2.2)
    else join (diff l1 p.1) x1 (diff r1 p.2.2)

/-- `Raw.fold` (in increasing order). -/
def fold {A : Type _} (f : E → A → A) : tree E → A → A
  | Leaf, a => a
  | Node _ l x r, a => fold f r (f x (fold f l a))

/-- `Raw.for_all` -/
def for_all (f : E → Bool) : tree E → Bool
  | Leaf => true
  | Node _ l x r => f x && for_all f l && for_all f r

/-- `Raw.exists_` -/
def exists_ (f : E → Bool) : tree E → Bool
  | Leaf => false
  | Node _ l x r => f x || exists_ f l || exists_ f r

/-- `Raw.filter` (Rocq's `filter_acc`, accumulating with `add`). -/
def filter_acc (f : E → Bool) : tree E → tree E → tree E
  | acc, Leaf => acc
  | acc, Node _ l x r =>
    filter_acc f (filter_acc f (if f x then add x acc else acc) l) r

def filter (f : E → Bool) (s : tree E) : tree E := filter_acc f Leaf s

/-- `Raw.subset`, by membership tests. -/
def subset (s1 s2 : tree E) : Bool := for_all (fun x => mem x s2) s1

/-- `Raw.equal` -/
def equal (s1 s2 : tree E) : Bool := subset s1 s2 && subset s2 s1

end Raw
end FSetAVL
end CC
