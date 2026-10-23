/-
  Finite sets as AVL trees: the part of Rocq's standard library
  (`FSetAVL` / `MSetAVL`) that CompCert's `lib/FSetAVLplus.v` includes with
  `Include FSetAVL.Make(X)`.  The Rocq standard library is not available in
  Lean, so it is ported here; `lib/FSetAVLplus.lean` adds CompCert's interval
  operations on top of it.

  * `Raw.tree` with `height`, `create`, `bal`, `add`, `join`, `remove_min`,
    `merge`, `concat`, `remove`, `split`, `union`, `inter`, `diff`, `mem`,
    `elements`, `cardinal`, `fold`, `filter`, `for_all`, `exists_`,
    `min_elt`, `max_elt`, `subset`, `equal`;
  * the membership predicate `Raw.In` and the search-tree invariant `Raw.bst`
    (Rocq's `Raw.Ok`), with the specification of every operation;
  * the set type `FSetAVL.t E`, the subtype of binary search trees (Rocq's
    `MSet.t` record with field `is_ok`), with the `FSetInterface`-style
    specifications (`mem_spec`, `add_spec`, `remove_spec`, `union_spec`,
    `inter_spec`, `diff_spec`, `filter_spec`, `elements_spec1/2`,
    `min_elt_spec1/2/3`, …).

  Differences from Rocq:
  * The functor argument `X` is an `OrderedType` instance (`lib/Ordered.lean`)
    and element equality `X.eq` is Lean's equality.
  * Heights are natural numbers instead of `Int.Z_as_Int` integers.
  * The AVL balance invariant is not needed for correctness and, as in
    `MSetAVL` (where it is proved separately), it is not part of `t`.
  * `join` is defined by well-founded recursion on the sizes of both trees
    instead of a nested `fix`; `subset` is computed by membership tests and
    `filter`/`partition` by insertion.
  * The proofs reason about the in-order list `elements`: rebalancing and
    joining preserve it, and `bst t` is equivalent to `elements t` being
    strictly sorted (`bst_iff_pairwise`).

  The first part of this file is split off into `CCLib.lib.FSetAVLTree`.
-/

import CCLib.lib.FSetAVLTree

namespace CC
namespace FSetAVL
open OrderedType
variable {E : Type _} [OrderedType E]
namespace Raw
open tree

/-! ### Specifications -/

omit [OrderedType E] in
theorem elements_create (l : tree E) x r :
    elements (create l x r) = elements l ++ x :: elements r := rfl

omit [OrderedType E] in
theorem elements_bal (l : tree E) x r : elements (bal l x r) = elements l ++ x :: elements r := by
  unfold bal
  dsimp only
  by_cases h1 : height l > height r + 2
  · rw [if_pos h1]
    cases l with
    | Leaf => rfl
    | Node _ ll lx lr =>
      dsimp only
      by_cases h2 : height ll ≥ height lr
      · rw [if_pos h2]; simp [create, elements]
      · rw [if_neg h2]
        cases lr with
        | Leaf => rfl
        | Node _ lrl lrx lrr => simp [create, elements]
  · rw [if_neg h1]
    by_cases h3 : height r > height l + 2
    · rw [if_pos h3]
      cases r with
      | Leaf => rfl
      | Node _ rl rx rr =>
        dsimp only
        by_cases h2 : height rr ≥ height rl
        · rw [if_pos h2]; simp [create, elements]
        · rw [if_neg h2]
          cases rl with
          | Leaf => rfl
          | Node _ rll rlx rlr => simp [create, elements]
    · rw [if_neg h3]; rfl

omit [OrderedType E] in
theorem In_bal {l : tree E} {x r y} : In y (bal l x r) ↔ In y l ∨ y = x ∨ In y r := by
  rw [In_of_elements_eq (elements_bal l x r) (s := Node 0 l x r), In_node_iff]

theorem bst_bal {l : tree E} {x r} : bst (bal l x r) ↔ bst (Node 0 l x r) :=
  ⟨bst_of_elements_eq (elements_bal l x r).symm, bst_of_elements_eq (elements_bal l x r)⟩

theorem In_add {x y : E} : ∀ {s : tree E}, In y (add x s) ↔ y = x ∨ In y s
  | Leaf => by simp [add, In_node_iff, not_In_Leaf]
  | Node h l z r => by
    unfold add
    have hc := compare_spec x z
    split <;> rename_i heq <;> rw [heq] at hc
    · rw [In_bal, In_add, In_node_iff]; simp only [or_assoc]
    · subst hc
      constructor
      · exact .inr
      · rintro (rfl | hi)
        · exact .IsRoot rfl
        · exact hi
    · rw [In_bal, In_add, In_node_iff]; simp only [or_left_comm]

theorem bst_add {x : E} : ∀ {s : tree E}, bst s → bst (add x s)
  | Leaf, _ => .node .leaf .leaf (fun _ h => absurd h not_In_Leaf) (fun _ h => absurd h not_In_Leaf)
  | Node h l z r, hb => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    unfold add
    have hc := compare_spec x z
    split <;> rename_i heq <;> rw [heq] at hc
    · rw [bst_bal]; refine .node (bst_add hl) hr ?_ gtr
      intro y hy
      rcases In_add.1 hy with rfl | hy
      · exact hc
      · exact ltl y hy
    · exact hb
    · rw [bst_bal]; refine .node hl (bst_add hr) ltl ?_
      intro y hy
      rcases In_add.1 hy with rfl | hy
      · exact hc
      · exact gtr y hy

theorem elements_add_of_gt {x : E} :
    ∀ {s : tree E}, gt_tree x s → elements (add x s) = x :: elements s
  | Leaf, _ => rfl
  | Node h l z r, hg => by
    have hxz : lt x z := hg z (.IsRoot rfl)
    unfold add
    rw [(compare_lt_iff x z).2 hxz]
    dsimp only
    rw [elements_bal, elements_add_of_gt (fun y hy => hg y (.InLeft hy))]
    simp [elements]

theorem elements_add_of_lt {x : E} :
    ∀ {s : tree E}, lt_tree x s → elements (add x s) = elements s ++ [x]
  | Leaf, _ => rfl
  | Node h l z r, hg => by
    have hxz : lt z x := hg z (.IsRoot rfl)
    unfold add
    rw [(compare_gt_iff x z).2 hxz]
    dsimp only
    rw [elements_bal, elements_add_of_lt (fun y hy => hg y (.InRight hy))]
    simp [elements]

theorem In_join {y : E} :
    ∀ (l : tree E) (x : E) (r : tree E), In y (join l x r) ↔ In y l ∨ y = x ∨ In y r
  | Leaf, x, r => by rw [join, In_add]; simp [not_In_Leaf]
  | Node lh ll lx lr, x, Leaf => by
    rw [join, In_add]; simp only [not_In_Leaf, or_false]; exact Or.comm
  | Node lh ll lx lr, x, Node rh rl rx rr => by
    rw [join]
    split
    · rw [In_bal, In_join lr x (Node rh rl rx rr), In_node_iff (l := ll)] <;> simp only [or_assoc]
    · split
      · rw [In_bal, In_join (Node lh ll lx lr) x rl, In_node_iff (l := rl)] <;>
          simp only [or_assoc]
      · exact In_node_iff
termination_by l _ r => sizeOf l + sizeOf r

theorem elements_join :
    ∀ (l : tree E) (x : E) (r : tree E), lt_tree x l → gt_tree x r →
      elements (join l x r) = elements l ++ x :: elements r
  | Leaf, x, r, _, hr => by rw [join, elements_add_of_gt hr]; rfl
  | Node lh ll lx lr, x, Leaf, hl, _ => by rw [join, elements_add_of_lt hl]; rfl
  | Node lh ll lx lr, x, Node rh rl rx rr, hl, hr => by
    rw [join]
    split
    · rw [elements_bal, elements_join lr x (Node rh rl rx rr) (fun y hy => hl y (.InRight hy)) hr]
      simp [elements]
    · split
      · rw [elements_bal, elements_join (Node lh ll lx lr) x rl hl (fun y hy => hr y (.InLeft hy))]
        simp [elements]
      · rfl
termination_by l _ r => sizeOf l + sizeOf r

theorem bst_join {l : tree E} {x r} (hl : bst l) (hr : bst r) (ltl : lt_tree x l)
    (gtr : gt_tree x r) : bst (join l x r) :=
  bst_of_elements_eq (s := Node 0 l x r) (elements_join l x r ltl gtr) (.node hl hr ltl gtr)

omit [OrderedType E] in
theorem elements_remove_min : ∀ (l : tree E) x r,
    (remove_min l x r).2 :: elements (remove_min l x r).1 = elements l ++ x :: elements r
  | Leaf, _, _ => rfl
  | Node _ ll lx lr, x, r => by
    show (remove_min ll lx lr).2 :: elements (bal (remove_min ll lx lr).1 x r) = _
    rw [elements_bal, ← List.cons_append, elements_remove_min ll lx lr]
    simp [elements]

omit [OrderedType E] in
theorem In_remove_min {h} {l : tree E} {x r y} :
    In y (remove_min l x r).1 ∨ y = (remove_min l x r).2 ↔ In y (Node h l x r) := by
  rw [In_iff_mem, In_iff_mem, elements, ← elements_remove_min]
  simp only [List.mem_cons]; exact Or.comm

theorem bst_remove_min {h} {l : tree E} {x r} (hb : bst (Node h l x r)) :
    bst (remove_min l x r).1 ∧ gt_tree (remove_min l x r).2 (remove_min l x r).1 := by
  have := bst_iff_pairwise.1 hb
  rw [elements, ← elements_remove_min, List.pairwise_cons] at this
  exact ⟨bst_iff_pairwise.2 this.2, fun y hy => this.1 y (In_iff_mem.1 hy)⟩

omit [OrderedType E] in
theorem elements_merge : ∀ (s1 s2 : tree E), elements (merge s1 s2) = elements s1 ++ elements s2
  | Leaf, _ => rfl
  | Node _ _ _ _, Leaf => by simp [merge, elements]
  | Node h1 l1 x1 r1, Node _ l2 x2 r2 => by
    show elements (bal _ _ _) = _
    rw [elements_bal, elements_remove_min]; rfl

omit [OrderedType E] in
theorem In_merge {s1 s2 : tree E} {y} : In y (merge s1 s2) ↔ In y s1 ∨ In y s2 := by
  rw [In_iff_mem, In_iff_mem, In_iff_mem, elements_merge, List.mem_append]

/-- `s1 < s2` elementwise. -/
def tree_lt (s1 s2 : tree E) : Prop := ∀ a, In a s1 → ∀ b, In b s2 → lt a b

theorem bst_merge {s1 s2 : tree E} (h1 : bst s1) (h2 : bst s2) (hlt : tree_lt s1 s2) :
    bst (merge s1 s2) := by
  rw [bst_iff_pairwise, elements_merge, List.pairwise_append]
  exact ⟨bst_iff_pairwise.1 h1, bst_iff_pairwise.1 h2,
    fun a ha b hb => hlt a (In_iff_mem.2 ha) b (In_iff_mem.2 hb)⟩

theorem In_concat {s1 s2 : tree E} {y} : In y (concat s1 s2) ↔ In y s1 ∨ In y s2 := by
  match s1, s2 with
  | Leaf, _ => simp [concat, not_In_Leaf]
  | Node _ _ _ _, Leaf => simp [concat, not_In_Leaf]
  | Node h1 l1 x1 r1, Node h2 l2 x2 r2 =>
    show In y (join _ _ _) ↔ _
    rw [In_join, ← In_remove_min (h := h2) (y := y) (l := l2) (x := x2) (r := r2)]
    constructor
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h)

theorem elements_concat {s1 s2 : tree E} (h2 : bst s2) (hlt : tree_lt s1 s2) :
    elements (concat s1 s2) = elements s1 ++ elements s2 := by
  match s1, s2, h2, hlt with
  | Leaf, _, _, _ => rfl
  | Node _ _ _ _, Leaf, _, _ => simp [concat, elements]
  | Node h1 l1 x1 r1, Node h2 l2 x2 r2, h2b, hlt =>
    show elements (join _ _ _) = _
    have hm : In (remove_min l2 x2 r2).2 (Node h2 l2 x2 r2) := by
      exact (In_remove_min (y := (remove_min l2 x2 r2).2) (l := l2) (x := x2) (r := r2)).1
        (.inr rfl)
    rw [elements_join _ _ _ (fun a ha => hlt a ha _ hm) (bst_remove_min h2b).2,
      elements_remove_min]
    rfl

theorem bst_concat {s1 s2 : tree E} (h1 : bst s1) (h2 : bst s2) (hlt : tree_lt s1 s2) :
    bst (concat s1 s2) := by
  rw [bst_iff_pairwise, elements_concat h2 hlt, List.pairwise_append]
  exact ⟨bst_iff_pairwise.1 h1, bst_iff_pairwise.1 h2,
    fun a ha b hb => hlt a (In_iff_mem.2 ha) b (In_iff_mem.2 hb)⟩

theorem remove_sublist (x : E) : ∀ (s : tree E), (elements (remove x s)).Sublist (elements s)
  | Leaf => List.Sublist.refl _
  | Node _ l z r => by
    unfold remove
    split
    · rw [elements_bal, elements]
      exact (remove_sublist x l).append (List.Sublist.refl _)
    · rw [elements_merge, elements]
      exact (List.Sublist.refl _).append (List.sublist_cons_self _ _)
    · rw [elements_bal, elements]
      exact (List.Sublist.refl _).append ((remove_sublist x r).cons_cons _)

theorem bst_remove {x : E} {s : tree E} (hs : bst s) : bst (remove x s) := by
  rw [bst_iff_pairwise] at hs ⊢
  exact hs.sublist (remove_sublist x s)

theorem In_remove {x y : E} : ∀ {s : tree E}, bst s → (In y (remove x s) ↔ In y s ∧ y ≠ x)
  | Leaf, _ => by simp [remove, not_In_Leaf]
  | Node h l z r, hb => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    unfold remove
    have hc := compare_spec x z
    split <;> rename_i heq <;> rw [heq] at hc
    · rw [In_bal, In_remove hl, In_node_iff]
      constructor
      · rintro (⟨h1, h2⟩ | rfl | h1)
        · exact ⟨.inl h1, h2⟩
        · exact ⟨.inr (.inl rfl), fun e => lt_not_eq _ _ hc e.symm⟩
        · exact ⟨.inr (.inr h1), fun e => lt_not_eq _ _ (lt_trans _ _ _ hc (gtr y h1)) e.symm⟩
      · rintro ⟨h1 | h1 | h1, h2⟩
        · exact .inl ⟨h1, h2⟩
        · exact .inr (.inl h1)
        · exact .inr (.inr h1)
    · subst hc
      rw [In_merge, In_node_iff]
      constructor
      · rintro (h1 | h1)
        · exact ⟨.inl h1, lt_not_eq _ _ (ltl y h1)⟩
        · exact ⟨.inr (.inr h1), fun e => lt_not_eq _ _ (gtr y h1) e.symm⟩
      · rintro ⟨h1 | h1 | h1, h2⟩
        · exact .inl h1
        · exact absurd h1 h2
        · exact .inr h1
    · rw [In_bal, In_remove hr, In_node_iff]
      constructor
      · rintro (h1 | rfl | ⟨h1, h2⟩)
        · exact ⟨.inl h1, fun e => lt_not_eq _ _ (lt_trans _ _ _ (ltl y h1) hc) e⟩
        · exact ⟨.inr (.inl rfl), fun e => lt_not_eq _ _ hc e⟩
        · exact ⟨.inr (.inr h1), h2⟩
      · rintro ⟨h1 | h1 | h1, h2⟩
        · exact .inl h1
        · exact .inr (.inl h1)
        · exact .inr (.inr ⟨h1, h2⟩)

theorem mem_spec {x : E} : ∀ {s : tree E}, bst s → (mem x s = true ↔ In x s)
  | Leaf, _ => by simp [mem, not_In_Leaf]
  | Node h l z r, hb => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    unfold mem
    have hc := compare_spec x z
    split <;> rename_i heq <;> rw [heq] at hc
    · rw [mem_spec hl, In_node_iff]
      constructor
      · exact .inl
      · rintro (h1 | rfl | h1)
        · exact h1
        · exact absurd hc (lt_irrefl _)
        · exact absurd (lt_trans _ _ _ hc (gtr x h1)) (lt_irrefl _)
    · subst hc; simp only [true_iff]; exact .IsRoot rfl
    · rw [mem_spec hr, In_node_iff]
      constructor
      · intro h1; exact .inr (.inr h1)
      · rintro (h1 | rfl | h1)
        · exact absurd (lt_trans _ _ _ hc (ltl x h1)) (lt_irrefl _)
        · exact absurd hc (lt_irrefl _)
        · exact h1

theorem split_spec {x : E} : ∀ {s : tree E}, bst s →
    bst (split x s).1 ∧ bst (split x s).2.2 ∧
    (∀ y, In y (split x s).1 ↔ In y s ∧ lt y x) ∧
    ((split x s).2.1 = true ↔ In x s) ∧
    (∀ y, In y (split x s).2.2 ↔ In y s ∧ lt x y)
  | Leaf, _ => by refine ⟨.leaf, .leaf, ?_, ?_, ?_⟩ <;> simp [split, not_In_Leaf]
  | Node h l z r, hb => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    unfold split
    have hc := compare_spec x z
    split <;> rename_i heq <;> rw [heq] at hc
    · obtain ⟨b1, b2, i1, i2, i3⟩ := split_spec (x := x) hl
      refine ⟨b1, bst_join b2 hr (fun y hy => ltl y ((i3 y).1 hy).1) gtr, ?_, ?_, ?_⟩
      · intro y; rw [i1, In_node_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨.inl h1, h2⟩
        · rintro ⟨h1 | rfl | h1, h2⟩
          · exact ⟨h1, h2⟩
          · exact absurd (lt_trans _ _ _ h2 hc) (lt_irrefl _)
          · exact absurd (lt_trans _ _ _ h2 (lt_trans _ _ _ hc (gtr y h1))) (lt_irrefl _)
      · rw [i2, In_node_iff]
        constructor
        · exact .inl
        · rintro (h1 | rfl | h1)
          · exact h1
          · exact absurd hc (lt_irrefl _)
          · exact absurd (lt_trans _ _ _ hc (gtr x h1)) (lt_irrefl _)
      · intro y; rw [In_join, i3, In_node_iff]
        constructor
        · rintro (⟨h1, h2⟩ | rfl | h1)
          · exact ⟨.inl h1, h2⟩
          · exact ⟨.inr (.inl rfl), hc⟩
          · exact ⟨.inr (.inr h1), lt_trans _ _ _ hc (gtr y h1)⟩
        · rintro ⟨h1 | h1 | h1, h2⟩
          · exact .inl ⟨h1, h2⟩
          · exact .inr (.inl h1)
          · exact .inr (.inr h1)
    · subst hc
      refine ⟨hl, hr, ?_, ?_, ?_⟩
      · intro y; rw [In_node_iff]
        constructor
        · intro h1; exact ⟨.inl h1, ltl y h1⟩
        · rintro ⟨h1 | rfl | h1, h2⟩
          · exact h1
          · exact absurd h2 (lt_irrefl _)
          · exact absurd (lt_trans _ _ _ h2 (gtr y h1)) (lt_irrefl _)
      · simp only [true_iff]; exact .IsRoot rfl
      · intro y; rw [In_node_iff]
        constructor
        · intro h1; exact ⟨.inr (.inr h1), gtr y h1⟩
        · rintro ⟨h1 | rfl | h1, h2⟩
          · exact absurd (lt_trans _ _ _ h2 (ltl y h1)) (lt_irrefl _)
          · exact absurd h2 (lt_irrefl _)
          · exact h1
    · obtain ⟨b1, b2, i1, i2, i3⟩ := split_spec (x := x) hr
      refine ⟨bst_join hl b1 ltl (fun y hy => gtr y ((i1 y).1 hy).1), b2, ?_, ?_, ?_⟩
      · intro y; rw [In_join, i1, In_node_iff]
        constructor
        · rintro (h1 | rfl | ⟨h1, h2⟩)
          · exact ⟨.inl h1, lt_trans _ _ _ (ltl y h1) hc⟩
          · exact ⟨.inr (.inl rfl), hc⟩
          · exact ⟨.inr (.inr h1), h2⟩
        · rintro ⟨h1 | h1 | h1, h2⟩
          · exact .inl h1
          · exact .inr (.inl h1)
          · exact .inr (.inr ⟨h1, h2⟩)
      · rw [i2, In_node_iff]
        constructor
        · intro h1; exact .inr (.inr h1)
        · rintro (h1 | rfl | h1)
          · exact absurd (lt_trans _ _ _ hc (ltl x h1)) (lt_irrefl _)
          · exact absurd hc (lt_irrefl _)
          · exact h1
      · intro y; rw [i3, In_node_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨.inr (.inr h1), h2⟩
        · rintro ⟨h1 | rfl | h1, h2⟩
          · exact absurd (lt_trans _ _ _ hc (lt_trans _ _ _ h2 (ltl y h1))) (lt_irrefl _)
          · exact absurd (lt_trans _ _ _ hc h2) (lt_irrefl _)
          · exact ⟨h1, h2⟩

theorem union_spec : ∀ {s1 s2 : tree E}, bst s1 → bst s2 →
    bst (union s1 s2) ∧ ∀ y, In y (union s1 s2) ↔ In y s1 ∨ In y s2
  | Leaf, _, _, h2 => ⟨h2, fun y => by simp [union, not_In_Leaf]⟩
  | Node _ _ _ _, Leaf, h1, _ => ⟨h1, fun y => by simp [union, not_In_Leaf]⟩
  | Node _ l1 x1 r1, Node h2' l2 x2 r2, hb1, hb2 => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb1
    obtain ⟨b1, b2, i1, _, i3⟩ := split_spec (x := x1) hb2
    obtain ⟨u1, iu1⟩ := union_spec hl b1
    obtain ⟨u2, iu2⟩ := union_spec hr b2
    simp only [union]
    refine ⟨bst_join u1 u2 ?_ ?_, ?_⟩
    · intro y hy
      rcases (iu1 y).1 hy with h | h
      · exact ltl y h
      · exact ((i1 y).1 h).2
    · intro y hy
      rcases (iu2 y).1 hy with h | h
      · exact gtr y h
      · exact ((i3 y).1 h).2
    · intro y; rw [In_join, iu1, iu2, i1, i3, In_node_iff (l := l1)]
      constructor
      · rintro ((h | ⟨h, _⟩) | rfl | (h | ⟨h, _⟩))
        · exact .inl (.inl h)
        · exact .inr h
        · exact .inl (.inr (.inl rfl))
        · exact .inl (.inr (.inr h))
        · exact .inr h
      · rintro ((h | rfl | h) | h)
        · exact .inl (.inl h)
        · exact .inr (.inl rfl)
        · exact .inr (.inr (.inl h))
        · have hc := compare_spec y x1
          revert hc
          cases compare y x1 <;> intro hc
          · exact .inl (.inr ⟨h, hc⟩)
          · exact .inr (.inl hc)
          · exact .inr (.inr (.inr ⟨h, hc⟩))

theorem inter_spec : ∀ {s1 s2 : tree E}, bst s1 → bst s2 →
    bst (inter s1 s2) ∧ ∀ y, In y (inter s1 s2) ↔ In y s1 ∧ In y s2
  | Leaf, _, _, _ => ⟨.leaf, fun y => by simp [inter, not_In_Leaf]⟩
  | Node _ _ _ _, Leaf, _, _ => ⟨.leaf, fun y => by simp [inter, not_In_Leaf]⟩
  | Node _ l1 x1 r1, Node h2' l2 x2 r2, hb1, hb2 => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb1
    obtain ⟨b1, b2, i1, i2, i3⟩ := split_spec (x := x1) hb2
    obtain ⟨u1, iu1⟩ := inter_spec hl b1
    obtain ⟨u2, iu2⟩ := inter_spec hr b2
    have lt1 : lt_tree x1 (inter l1 (split x1 (Node h2' l2 x2 r2)).1) :=
      fun y hy => ltl y ((iu1 y).1 hy).1
    have gt2 : gt_tree x1 (inter r1 (split x1 (Node h2' l2 x2 r2)).2.2) :=
      fun y hy => gtr y ((iu2 y).1 hy).1
    simp only [inter]
    split
    · rename_i hx
      refine ⟨bst_join u1 u2 lt1 gt2, fun y => ?_⟩
      rw [In_join, iu1, iu2, i1, i3, In_node_iff (l := l1)]
      constructor
      · rintro (⟨h, h', _⟩ | rfl | ⟨h, h', _⟩)
        · exact ⟨.inl h, h'⟩
        · exact ⟨.inr (.inl rfl), i2.1 hx⟩
        · exact ⟨.inr (.inr h), h'⟩
      · rintro ⟨h | rfl | h, h'⟩
        · exact .inl ⟨h, h', ltl y h⟩
        · exact .inr (.inl rfl)
        · exact .inr (.inr ⟨h, h', gtr y h⟩)
    · rename_i hx
      refine ⟨bst_concat u1 u2 (fun a ha b hb => lt_trans _ _ _ (lt1 a ha) (gt2 b hb)),
        fun y => ?_⟩
      rw [In_concat, iu1, iu2, i1, i3, In_node_iff (l := l1)]
      constructor
      · rintro (⟨h, h', _⟩ | ⟨h, h', _⟩)
        · exact ⟨.inl h, h'⟩
        · exact ⟨.inr (.inr h), h'⟩
      · rintro ⟨h | rfl | h, h'⟩
        · exact .inl ⟨h, h', ltl y h⟩
        · exact absurd (i2.2 h') hx
        · exact .inr ⟨h, h', gtr y h⟩

theorem diff_spec : ∀ {s1 s2 : tree E}, bst s1 → bst s2 →
    bst (diff s1 s2) ∧ ∀ y, In y (diff s1 s2) ↔ In y s1 ∧ ¬ In y s2
  | Leaf, _, _, _ => ⟨.leaf, fun y => by simp [diff, not_In_Leaf]⟩
  | Node _ _ _ _, Leaf, h1, _ => ⟨h1, fun y => by simp [diff, not_In_Leaf]⟩
  | Node _ l1 x1 r1, Node h2' l2 x2 r2, hb1, hb2 => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb1
    obtain ⟨b1, b2, i1, i2, i3⟩ := split_spec (x := x1) hb2
    obtain ⟨u1, iu1⟩ := diff_spec hl b1
    obtain ⟨u2, iu2⟩ := diff_spec hr b2
    have lt1 : lt_tree x1 (diff l1 (split x1 (Node h2' l2 x2 r2)).1) :=
      fun y hy => ltl y ((iu1 y).1 hy).1
    have gt2 : gt_tree x1 (diff r1 (split x1 (Node h2' l2 x2 r2)).2.2) :=
      fun y hy => gtr y ((iu2 y).1 hy).1
    simp only [diff]
    split
    · rename_i hx
      refine ⟨bst_concat u1 u2 (fun a ha b hb => lt_trans _ _ _ (lt1 a ha) (gt2 b hb)),
        fun y => ?_⟩
      rw [In_concat, iu1, iu2, i1, i3, In_node_iff (l := l1)]
      constructor
      · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨.inl h, fun h2 => h' ⟨h2, ltl y h⟩⟩
        · exact ⟨.inr (.inr h), fun h2 => h' ⟨h2, gtr y h⟩⟩
      · rintro ⟨h | rfl | h, h'⟩
        · exact .inl ⟨h, fun h2 => h' h2.1⟩
        · exact absurd (i2.1 hx) h'
        · exact .inr ⟨h, fun h2 => h' h2.1⟩
    · rename_i hx
      refine ⟨bst_join u1 u2 lt1 gt2, fun y => ?_⟩
      rw [In_join, iu1, iu2, i1, i3, In_node_iff (l := l1)]
      constructor
      · rintro (⟨h, h'⟩ | rfl | ⟨h, h'⟩)
        · exact ⟨.inl h, fun h2 => h' ⟨h2, ltl y h⟩⟩
        · exact ⟨.inr (.inl rfl), fun h2 => hx (i2.2 h2)⟩
        · exact ⟨.inr (.inr h), fun h2 => h' ⟨h2, gtr y h⟩⟩
      · rintro ⟨h | rfl | h, h'⟩
        · exact .inl ⟨h, fun h2 => h' h2.1⟩
        · exact .inr (.inl rfl)
        · exact .inr (.inr ⟨h, fun h2 => h' h2.1⟩)

omit [OrderedType E] in
theorem cardinal_eq (s : tree E) : cardinal s = (elements s).length := by
  induction s with
  | Leaf => rfl
  | Node _ l x r ihl ihr => simp [cardinal, elements, ihl, ihr]; omega

omit [OrderedType E] in
theorem fold_eq {A : Type _} (f : E → A → A) :
    ∀ (s : tree E) (a : A), fold f s a = (elements s).foldl (fun a x => f x a) a
  | Leaf, _ => rfl
  | Node _ l x r, a => by simp [fold, elements, List.foldl_append, fold_eq f l, fold_eq f r]

omit [OrderedType E] in
theorem for_all_eq (f : E → Bool) : ∀ (s : tree E), for_all f s = (elements s).all f
  | Leaf => rfl
  | Node _ l x r => by
    simp only [for_all, elements, List.all_append, List.all_cons, for_all_eq f l, for_all_eq f r]
    cases f x <;> cases (elements l).all f <;> rfl

omit [OrderedType E] in
theorem for_all_iff (f : E → Bool) (s : tree E) :
    for_all f s = true ↔ ∀ x, In x s → f x = true := by
  rw [for_all_eq, List.all_eq_true]
  exact ⟨fun h x hx => h x (In_iff_mem.1 hx), fun h x hx => h x (In_iff_mem.2 hx)⟩

omit [OrderedType E] in
theorem exists_eq (f : E → Bool) : ∀ (s : tree E), exists_ f s = (elements s).any f
  | Leaf => rfl
  | Node _ l x r => by
    simp only [exists_, elements, List.any_append, List.any_cons, exists_eq f l, exists_eq f r]
    cases f x <;> cases (elements l).any f <;> rfl

omit [OrderedType E] in
theorem exists_iff (f : E → Bool) (s : tree E) :
    exists_ f s = true ↔ ∃ x, In x s ∧ f x = true := by
  rw [exists_eq, List.any_eq_true]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, In_iff_mem.2 hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, In_iff_mem.1 hx, h⟩⟩

theorem filter_acc_spec (f : E → Bool) : ∀ (s acc : tree E), bst acc →
    bst (filter_acc f acc s) ∧ ∀ y, In y (filter_acc f acc s) ↔ In y acc ∨ (In y s ∧ f y = true)
  | Leaf, acc, h => ⟨h, fun y => by simp [filter_acc, not_In_Leaf]⟩
  | Node _ l x r, acc, h => by
    have h0 : bst (if f x then add x acc else acc) := by
      split
      · exact bst_add h
      · exact h
    obtain ⟨b1, i1⟩ := filter_acc_spec f l _ h0
    obtain ⟨b2, i2⟩ := filter_acc_spec f r _ b1
    refine ⟨b2, fun y => ?_⟩
    simp only [filter_acc]
    rw [i2, i1, In_node_iff]
    have i0 : In y (if f x then add x acc else acc) ↔ In y acc ∨ (y = x ∧ f y = true) := by
      cases hfx : f x
      · simp only [Bool.false_eq_true, if_false]
        constructor
        · exact .inl
        · rintro (h | ⟨rfl, h⟩)
          · exact h
          · rw [hfx] at h; cases h
      · simp only [if_true, In_add]
        constructor
        · rintro (rfl | h)
          · exact .inr ⟨rfl, hfx⟩
          · exact .inl h
        · rintro (h | ⟨rfl, _⟩)
          · exact .inr h
          · exact .inl rfl
    rw [i0]
    constructor
    · rintro (((h | ⟨rfl, h⟩) | ⟨h, h'⟩) | ⟨h, h'⟩)
      · exact .inl h
      · exact .inr ⟨.inr (.inl rfl), h⟩
      · exact .inr ⟨.inl h, h'⟩
      · exact .inr ⟨.inr (.inr h), h'⟩
    · rintro (h | ⟨h | rfl | h, h'⟩)
      · exact .inl (.inl (.inl h))
      · exact .inl (.inr ⟨h, h'⟩)
      · exact .inl (.inl (.inr ⟨rfl, h'⟩))
      · exact .inr ⟨h, h'⟩

theorem filter_spec (f : E → Bool) (s : tree E) :
    bst (filter f s) ∧ ∀ y, In y (filter f s) ↔ In y s ∧ f y = true := by
  obtain ⟨b, i⟩ := filter_acc_spec f s Leaf .leaf
  refine ⟨b, fun y => ?_⟩
  unfold filter; rw [i]
  constructor
  · rintro (h | h)
    · exact absurd h not_In_Leaf
    · exact h
  · exact .inr

omit [OrderedType E] in
theorem min_elt_eq : ∀ (s : tree E), min_elt s = (elements s).head?
  | Leaf => rfl
  | Node _ Leaf x _ => rfl
  | Node _ (Node h ll lx lr) x r => by
    show min_elt (Node h ll lx lr) = _
    rw [min_elt_eq (Node h ll lx lr)]
    simp [elements]

omit [OrderedType E] in
theorem max_elt_eq : ∀ (s : tree E), max_elt s = (elements s).getLast?
  | Leaf => rfl
  | Node _ _ x Leaf => by simp [max_elt, elements]
  | Node _ l x (Node h rl rx rr) => by
    show max_elt (Node h rl rx rr) = _
    rw [max_elt_eq (Node h rl rx rr)]
    have key : ∀ (a : List E) b c, (a ++ b :: c).getLast? = (b :: c).getLast? := by
      intro a b c
      rw [List.getLast?_append]
      cases h : (b :: c).getLast? <;> simp_all
    simp only [elements, key]
    rw [← List.cons_append, key]

omit [OrderedType E] in
theorem is_empty_iff (s : tree E) : is_empty s = true ↔ ∀ y, ¬ In y s := by
  cases s with
  | Leaf => simp [is_empty, not_In_Leaf]
  | Node h l x r => simp only [is_empty, Bool.false_eq_true, false_iff]; intro hn; exact hn x (.IsRoot rfl)

theorem subset_iff {s1 s2 : tree E} (h2 : bst s2) :
    subset s1 s2 = true ↔ ∀ y, In y s1 → In y s2 := by
  unfold subset; rw [for_all_iff]
  exact ⟨fun h y hy => (mem_spec h2).1 (h y hy), fun h y hy => (mem_spec h2).2 (h y hy)⟩

theorem equal_iff {s1 s2 : tree E} (h1 : bst s1) (h2 : bst s2) :
    equal s1 s2 = true ↔ ∀ y, In y s1 ↔ In y s2 := by
  unfold equal; rw [Bool.and_eq_true, subset_iff h2, subset_iff h1]
  exact ⟨fun ⟨a, b⟩ y => ⟨a y, b y⟩, fun h => ⟨fun y => (h y).1, fun y => (h y).2⟩⟩

end Raw

/-- `FSetAVL.t`: finite sets, as binary search trees. -/
def t (E : Type _) [OrderedType E] : Type _ := { s : Raw.tree E // Raw.bst s }

/-- `In x s` -/
def In (x : E) (s : t E) : Prop := Raw.In x s.1
/-- `Equal s s'` -/
def Equal (s s' : t E) : Prop := ∀ a, In a s ↔ In a s'
/-- `Subset s s'` -/
def Subset (s s' : t E) : Prop := ∀ a, In a s → In a s'
/-- `Empty s` -/
def Empty (s : t E) : Prop := ∀ a, ¬ In a s

def empty : t E := ⟨.Leaf, .leaf⟩
def is_empty (s : t E) : Bool := Raw.is_empty s.1
def mem (x : E) (s : t E) : Bool := Raw.mem x s.1
def add (x : E) (s : t E) : t E := ⟨Raw.add x s.1, Raw.bst_add s.2⟩
def singleton (x : E) : t E := add x empty
def remove (x : E) (s : t E) : t E := ⟨Raw.remove x s.1, Raw.bst_remove s.2⟩
def union (s s' : t E) : t E := ⟨Raw.union s.1 s'.1, (Raw.union_spec s.2 s'.2).1⟩
def inter (s s' : t E) : t E := ⟨Raw.inter s.1 s'.1, (Raw.inter_spec s.2 s'.2).1⟩
def diff (s s' : t E) : t E := ⟨Raw.diff s.1 s'.1, (Raw.diff_spec s.2 s'.2).1⟩
def equal (s s' : t E) : Bool := Raw.equal s.1 s'.1
def subset (s s' : t E) : Bool := Raw.subset s.1 s'.1
def fold {A : Type _} (f : E → A → A) (s : t E) (a : A) : A := Raw.fold f s.1 a
def for_all (f : E → Bool) (s : t E) : Bool := Raw.for_all f s.1
def exists_ (f : E → Bool) (s : t E) : Bool := Raw.exists_ f s.1
def filter (f : E → Bool) (s : t E) : t E := ⟨Raw.filter f s.1, (Raw.filter_spec f s.1).1⟩
def partition (f : E → Bool) (s : t E) : t E × t E := (filter f s, filter (fun x => !f x) s)
def cardinal (s : t E) : Nat := Raw.cardinal s.1
def elements (s : t E) : List E := Raw.elements s.1
def min_elt (s : t E) : Option E := Raw.min_elt s.1
def max_elt (s : t E) : Option E := Raw.max_elt s.1
def choose (s : t E) : Option E := min_elt s

theorem empty_spec : Empty (empty : t E) := fun _ h => Raw.not_In_Leaf h

theorem is_empty_spec (s : t E) : is_empty s = true ↔ Empty s := Raw.is_empty_iff s.1

theorem mem_spec {x : E} {s : t E} : mem x s = true ↔ In x s := Raw.mem_spec s.2

theorem add_spec {x y : E} {s : t E} : In y (add x s) ↔ y = x ∨ In y s := Raw.In_add

theorem singleton_spec {x y : E} : In y (singleton x) ↔ y = x := by
  unfold singleton; rw [add_spec]
  exact ⟨fun h => h.elim id (fun h => absurd h Raw.not_In_Leaf), .inl⟩

theorem remove_spec {x y : E} {s : t E} : In y (remove x s) ↔ In y s ∧ y ≠ x :=
  Raw.In_remove s.2

theorem union_spec {s s' : t E} {x : E} : In x (union s s') ↔ In x s ∨ In x s' :=
  (Raw.union_spec s.2 s'.2).2 x

theorem inter_spec {s s' : t E} {x : E} : In x (inter s s') ↔ In x s ∧ In x s' :=
  (Raw.inter_spec s.2 s'.2).2 x

theorem diff_spec {s s' : t E} {x : E} : In x (diff s s') ↔ In x s ∧ ¬ In x s' :=
  (Raw.diff_spec s.2 s'.2).2 x

theorem equal_spec {s s' : t E} : equal s s' = true ↔ Equal s s' := Raw.equal_iff s.2 s'.2

theorem subset_spec {s s' : t E} : subset s s' = true ↔ Subset s s' := Raw.subset_iff s'.2

theorem fold_spec {A : Type _} (f : E → A → A) (s : t E) (a : A) :
    fold f s a = (elements s).foldl (fun a x => f x a) a := Raw.fold_eq f s.1 a

theorem for_all_spec (f : E → Bool) (s : t E) :
    for_all f s = true ↔ ∀ x, In x s → f x = true := Raw.for_all_iff f s.1

theorem exists_spec (f : E → Bool) (s : t E) :
    exists_ f s = true ↔ ∃ x, In x s ∧ f x = true := Raw.exists_iff f s.1

theorem filter_spec (f : E → Bool) {s : t E} {x : E} :
    In x (filter f s) ↔ In x s ∧ f x = true := (Raw.filter_spec f s.1).2 x

theorem partition_spec1 (f : E → Bool) (s : t E) : (partition f s).1 = filter f s := rfl

theorem partition_spec2 (f : E → Bool) (s : t E) :
    (partition f s).2 = filter (fun x => !f x) s := rfl

theorem cardinal_spec (s : t E) : cardinal s = (elements s).length := Raw.cardinal_eq s.1

theorem elements_spec1 {s : t E} {x : E} : x ∈ elements s ↔ In x s := Raw.In_iff_mem.symm

theorem elements_spec2 (s : t E) : (elements s).Pairwise lt := Raw.bst_iff_pairwise.1 s.2

theorem min_elt_spec1 {s : t E} {x : E} (h : min_elt s = some x) : In x s := by
  unfold min_elt at h; rw [Raw.min_elt_eq] at h
  exact Raw.In_iff_mem.2 (List.mem_of_head? h)

theorem min_elt_spec2 {s : t E} {x y : E} (h : min_elt s = some x) (hy : In y s) :
    ¬ lt y x := by
  unfold min_elt at h; rw [Raw.min_elt_eq] at h
  have hp := elements_spec2 s
  have hy' := elements_spec1.2 hy
  unfold elements at hp hy'
  revert h hp hy'
  cases Raw.elements s.1 with
  | nil => intro h; cases h
  | cons a l =>
    intro h hp hy'
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact lt_irrefl _
    · exact lt_asymm (hp.1 y hy')

theorem min_elt_spec3 {s : t E} (h : min_elt s = none) : Empty s := by
  unfold min_elt at h; rw [Raw.min_elt_eq, List.head?_eq_none_iff] at h
  intro a ha
  have := elements_spec1.2 ha
  unfold elements at this; rw [h] at this; cases this

theorem max_elt_spec1 {s : t E} {x : E} (h : max_elt s = some x) : In x s := by
  unfold max_elt at h; rw [Raw.max_elt_eq] at h
  exact Raw.In_iff_mem.2 (List.mem_of_getLast? h)

theorem max_elt_spec2 {s : t E} {x y : E} (h : max_elt s = some x) (hy : In y s) :
    ¬ lt x y := by
  unfold max_elt at h; rw [Raw.max_elt_eq, List.getLast?_eq_some_iff] at h
  obtain ⟨l, hl⟩ := h
  have hp := elements_spec2 s
  have hy' := elements_spec1.2 hy
  unfold elements at hp hy'
  rw [hl] at hp hy'
  rw [List.pairwise_append] at hp
  rcases List.mem_append.1 hy' with hy' | hy'
  · exact lt_asymm (hp.2.2 y hy' x (List.mem_singleton_self _))
  · rw [List.mem_singleton] at hy'; subst hy'; exact lt_irrefl _

theorem max_elt_spec3 {s : t E} (h : max_elt s = none) : Empty s := by
  unfold max_elt at h; rw [Raw.max_elt_eq, List.getLast?_eq_none_iff] at h
  intro a ha
  have := elements_spec1.2 ha
  unfold elements at this; rw [h] at this; cases this

theorem choose_spec1 {s : t E} {x : E} (h : choose s = some x) : In x s := min_elt_spec1 h
theorem choose_spec2 {s : t E} (h : choose s = none) : Empty s := min_elt_spec3 h

end FSetAVL
end CC
