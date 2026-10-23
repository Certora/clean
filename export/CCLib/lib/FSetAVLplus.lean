/-
  Port of `lib/FSetAVLplus.v`: an extension of `FSetAVL` (finite sets as
  balanced binary search trees, `lib/FSetAVL.lean`) with interval-based
  operations, more efficient than the standard ones.

  Rocq's functor `FSetAVLplus.Make (X : OrderedType)` becomes the namespace
  `FSetAVLplus`, parameterised by an `OrderedType` instance; its sets are
  `FSetAVLplus.t E`, which is `FSetAVL.t E` (Rocq's `Include FSetAVL.Make(X)`),
  so every `FSetAVL` operation applies to them.

  Ported, with all the lemmas of the Rocq file:
  * `mem_between` (`raw_mem_between_1/2`, `mem_between_1/2`);
  * `elements_between` (`In_raw_elements_between_1/2/3`,
    `raw_elements_between_ok`, `elements_between_iff`);
  * `for_all_between` (`raw_for_all_between_1/2`, `for_all_between_iff`);
  * `partition_between` (`In_raw_partition_between_1` … `_6`,
    `raw_partition_between_ok`, `partition_between_iff_1/2`).

  Differences from Rocq: the section hypotheses `above_monotone` and
  `below_monotone` are explicit arguments (of types `AboveMonotone` and
  `BelowMonotone`), and only the lemmas that use them take them.
  `pred_compat` is not needed, since element equality is Lean's equality.
-/
import CCLib.lib.FSetAVL

namespace CC
namespace FSetAVLplus

open OrderedType FSetAVL

variable {E : Type _} [OrderedType E]

/-- Monotonicity of a lower-bound test (Rocq's section hypothesis
`above_monotone`). -/
def AboveMonotone (above_low_bound : E → Bool) : Prop :=
  ∀ x1 x2, (x1 = x2 ∨ lt x1 x2) → above_low_bound x1 = true → above_low_bound x2 = true

/-- Monotonicity of an upper-bound test (Rocq's section hypothesis
`below_monotone`). -/
def BelowMonotone (below_high_bound : E → Bool) : Prop :=
  ∀ x1 x2, (x1 = x2 ∨ lt x2 x1) → below_high_bound x1 = true → below_high_bound x2 = true

namespace Raw

open FSetAVL.Raw FSetAVL.Raw.tree

/-! ### `mem_between` -/

/-- `raw_mem_between above below m`: is there an element of `m` in the
interval described by `above` and `below`?  Subtrees lying entirely outside
the interval are not traversed. -/
def raw_mem_between (above_low_bound below_high_bound : E → Bool) : tree E → Bool
  | Leaf => false
  | Node _ l x r =>
    if above_low_bound x then
      if below_high_bound x then true
      else raw_mem_between above_low_bound below_high_bound l
    else raw_mem_between above_low_bound below_high_bound r

omit [OrderedType E] in
theorem raw_mem_between_1 {above_low_bound below_high_bound : E → Bool} :
    ∀ {m : tree E}, raw_mem_between above_low_bound below_high_bound m = true →
      ∃ x, In x m ∧ above_low_bound x = true ∧ below_high_bound x = true
  | Leaf, h => by simp [raw_mem_between] at h
  | Node _ l x r, h => by
    simp only [raw_mem_between] at h
    cases ha : above_low_bound x <;> cases hb : below_high_bound x <;>
      simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at h
    · obtain ⟨y, hy, h1, h2⟩ := raw_mem_between_1 h; exact ⟨y, .InRight hy, h1, h2⟩
    · obtain ⟨y, hy, h1, h2⟩ := raw_mem_between_1 h; exact ⟨y, .InRight hy, h1, h2⟩
    · obtain ⟨y, hy, h1, h2⟩ := raw_mem_between_1 h; exact ⟨y, .InLeft hy, h1, h2⟩
    · exact ⟨x, .IsRoot rfl, ha, hb⟩

theorem raw_mem_between_2 {above_low_bound below_high_bound : E → Bool}
    (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} :
    ∀ {m : tree E}, bst m → In x m → above_low_bound x = true → below_high_bound x = true →
      raw_mem_between above_low_bound below_high_bound m = true
  | Leaf, _, hi, _, _ => absurd hi not_In_Leaf
  | Node _ l x0 r, hb, hi, h1, h2 => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    simp only [raw_mem_between]
    rw [In_node_iff] at hi
    cases ha : above_low_bound x0 <;> cases hb' : below_high_bound x0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact raw_mem_between_2 above_monotone below_monotone hr hi h1 h2
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact raw_mem_between_2 above_monotone below_monotone hr hi h1 h2
    · rcases hi with hi | rfl | hi
      · exact raw_mem_between_2 above_monotone below_monotone hl hi h1 h2
      · rw [h2] at hb'; cases hb'
      · rw [below_monotone _ _ (.inr (gtr x hi)) h2] at hb'; cases hb'

/-! ### `elements_between` -/

/-- `raw_elements_between above below m`: the elements of `m` in the
interval described by `above` and `below`. -/
def raw_elements_between (above_low_bound below_high_bound : E → Bool) : tree E → tree E
  | Leaf => Leaf
  | Node _ l x r =>
    if above_low_bound x then
      if below_high_bound x then
        join (raw_elements_between above_low_bound below_high_bound l) x
          (raw_elements_between above_low_bound below_high_bound r)
      else raw_elements_between above_low_bound below_high_bound l
    else raw_elements_between above_low_bound below_high_bound r

theorem In_raw_elements_between_1 {above_low_bound below_high_bound : E → Bool} {x : E} :
    ∀ {m : tree E}, In x (raw_elements_between above_low_bound below_high_bound m) → In x m
  | Leaf, h => h
  | Node _ l x0 r, h => by
    simp only [raw_elements_between] at h
    cases ha : above_low_bound x0 <;> cases hb : below_high_bound x0 <;>
      simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at h
    · exact .InRight (In_raw_elements_between_1 h)
    · exact .InRight (In_raw_elements_between_1 h)
    · exact .InLeft (In_raw_elements_between_1 h)
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact .InLeft (In_raw_elements_between_1 h)
      · exact .IsRoot rfl
      · exact .InRight (In_raw_elements_between_1 h)

theorem In_raw_elements_between_2 {above_low_bound below_high_bound : E → Bool} {x : E} :
    ∀ {m : tree E}, In x (raw_elements_between above_low_bound below_high_bound m) →
      above_low_bound x = true ∧ below_high_bound x = true
  | Leaf, h => absurd h not_In_Leaf
  | Node _ l x0 r, h => by
    simp only [raw_elements_between] at h
    cases ha : above_low_bound x0 <;> cases hb : below_high_bound x0 <;>
      simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at h
    · exact In_raw_elements_between_2 h
    · exact In_raw_elements_between_2 h
    · exact In_raw_elements_between_2 h
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact In_raw_elements_between_2 h
      · exact ⟨ha, hb⟩
      · exact In_raw_elements_between_2 h

theorem raw_elements_between_ok {above_low_bound below_high_bound : E → Bool} :
    ∀ {m : tree E}, bst m → bst (raw_elements_between above_low_bound below_high_bound m)
  | Leaf, _ => .leaf
  | Node _ l x0 r, hb => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    simp only [raw_elements_between]
    cases above_low_bound x0 <;> cases below_high_bound x0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · exact raw_elements_between_ok hr
    · exact raw_elements_between_ok hr
    · exact raw_elements_between_ok hl
    · exact bst_join (raw_elements_between_ok hl) (raw_elements_between_ok hr)
        (fun y hy => ltl y (In_raw_elements_between_1 hy))
        (fun y hy => gtr y (In_raw_elements_between_1 hy))

theorem In_raw_elements_between_3 {above_low_bound below_high_bound : E → Bool}
    (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} :
    ∀ {m : tree E}, bst m → In x m → above_low_bound x = true → below_high_bound x = true →
      In x (raw_elements_between above_low_bound below_high_bound m)
  | Leaf, _, hi, _, _ => absurd hi not_In_Leaf
  | Node _ l x0 r, hb, hi, h1, h2 => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    simp only [raw_elements_between]
    rw [In_node_iff] at hi
    cases ha : above_low_bound x0 <;> cases hb' : below_high_bound x0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact In_raw_elements_between_3 above_monotone below_monotone hr hi h1 h2
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact In_raw_elements_between_3 above_monotone below_monotone hr hi h1 h2
    · rcases hi with hi | rfl | hi
      · exact In_raw_elements_between_3 above_monotone below_monotone hl hi h1 h2
      · rw [h2] at hb'; cases hb'
      · rw [below_monotone _ _ (.inr (gtr x hi)) h2] at hb'; cases hb'
    · rw [In_join]
      rcases hi with hi | rfl | hi
      · exact .inl (In_raw_elements_between_3 above_monotone below_monotone hl hi h1 h2)
      · exact .inr (.inl rfl)
      · exact .inr (.inr (In_raw_elements_between_3 above_monotone below_monotone hr hi h1 h2))

/-! ### `for_all_between` -/

/-- `raw_for_all_between pred above below m`: do all elements of `m` in the
interval described by `above` and `below` satisfy `pred`? -/
def raw_for_all_between (pred above_low_bound below_high_bound : E → Bool) : tree E → Bool
  | Leaf => true
  | Node _ l x r =>
    if above_low_bound x then
      if below_high_bound x then
        raw_for_all_between pred above_low_bound below_high_bound l && pred x &&
          raw_for_all_between pred above_low_bound below_high_bound r
      else raw_for_all_between pred above_low_bound below_high_bound l
    else raw_for_all_between pred above_low_bound below_high_bound r

theorem raw_for_all_between_1 {pred above_low_bound below_high_bound : E → Bool}
    (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} :
    ∀ {m : tree E}, bst m →
      raw_for_all_between pred above_low_bound below_high_bound m = true →
      In x m → above_low_bound x = true → below_high_bound x = true → pred x = true
  | Leaf, _, _, hi, _, _ => absurd hi not_In_Leaf
  | Node _ l x0 r, hb, h, hi, h1, h2 => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    simp only [raw_for_all_between] at h
    rw [In_node_iff] at hi
    cases ha : above_low_bound x0 <;> cases hb' : below_high_bound x0 <;>
      simp only [ha, hb', Bool.false_eq_true, ↓reduceIte] at h
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact raw_for_all_between_1 above_monotone below_monotone hr h hi h1 h2
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact raw_for_all_between_1 above_monotone below_monotone hr h hi h1 h2
    · rcases hi with hi | rfl | hi
      · exact raw_for_all_between_1 above_monotone below_monotone hl h hi h1 h2
      · rw [h2] at hb'; cases hb'
      · rw [below_monotone _ _ (.inr (gtr x hi)) h2] at hb'; cases hb'
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hl', hx⟩, hr'⟩ := h
      rcases hi with hi | rfl | hi
      · exact raw_for_all_between_1 above_monotone below_monotone hl hl' hi h1 h2
      · exact hx
      · exact raw_for_all_between_1 above_monotone below_monotone hr hr' hi h1 h2

omit [OrderedType E] in
theorem raw_for_all_between_2 {pred above_low_bound below_high_bound : E → Bool} :
    ∀ {m : tree E},
      (∀ x, In x m → above_low_bound x = true → below_high_bound x = true → pred x = true) →
      raw_for_all_between pred above_low_bound below_high_bound m = true
  | Leaf, _ => rfl
  | Node _ l x0 r, h => by
    simp only [raw_for_all_between]
    cases ha : above_low_bound x0 <;> cases hb : below_high_bound x0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · exact raw_for_all_between_2 fun x hx => h x (.InRight hx)
    · exact raw_for_all_between_2 fun x hx => h x (.InRight hx)
    · exact raw_for_all_between_2 fun x hx => h x (.InLeft hx)
    · simp only [Bool.and_eq_true]
      exact ⟨⟨raw_for_all_between_2 fun x hx => h x (.InLeft hx), h x0 (.IsRoot rfl) ha hb⟩,
        raw_for_all_between_2 fun x hx => h x (.InRight hx)⟩

/-! ### `partition_between` -/

/-- `raw_partition_between above below m`: the elements of `m` inside the
interval described by `above` and `below`, and the elements outside. -/
def raw_partition_between (above_low_bound below_high_bound : E → Bool) :
    tree E → tree E × tree E
  | Leaf => (Leaf, Leaf)
  | Node _ l x r =>
    if above_low_bound x then
      if below_high_bound x then
        let pl := raw_partition_between above_low_bound below_high_bound l
        let pr := raw_partition_between above_low_bound below_high_bound r
        (join pl.1 x pr.1, concat pl.2 pr.2)
      else
        let pl := raw_partition_between above_low_bound below_high_bound l
        (pl.1, join pl.2 x r)
    else
      let pr := raw_partition_between above_low_bound below_high_bound r
      (pr.1, join l x pr.2)

theorem In_raw_partition_between_1 {above_low_bound below_high_bound : E → Bool} {x : E} :
    ∀ {m : tree E}, In x (raw_partition_between above_low_bound below_high_bound m).1 → In x m
  | Leaf, h => h
  | Node _ l x0 r, h => by
    simp only [raw_partition_between] at h
    cases ha : above_low_bound x0 <;> cases hb : below_high_bound x0 <;>
      simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at h
    · exact .InRight (In_raw_partition_between_1 h)
    · exact .InRight (In_raw_partition_between_1 h)
    · exact .InLeft (In_raw_partition_between_1 h)
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact .InLeft (In_raw_partition_between_1 h)
      · exact .IsRoot rfl
      · exact .InRight (In_raw_partition_between_1 h)

theorem In_raw_partition_between_2 {above_low_bound below_high_bound : E → Bool} {x : E} :
    ∀ {m : tree E}, In x (raw_partition_between above_low_bound below_high_bound m).2 → In x m
  | Leaf, h => h
  | Node _ l x0 r, h => by
    simp only [raw_partition_between] at h
    cases ha : above_low_bound x0 <;> cases hb : below_high_bound x0 <;>
      simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at h
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact .InLeft h
      · exact .IsRoot rfl
      · exact .InRight (In_raw_partition_between_2 h)
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact .InLeft h
      · exact .IsRoot rfl
      · exact .InRight (In_raw_partition_between_2 h)
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact .InLeft (In_raw_partition_between_2 h)
      · exact .IsRoot rfl
      · exact .InRight h
    · rcases In_concat.1 h with h | h
      · exact .InLeft (In_raw_partition_between_2 h)
      · exact .InRight (In_raw_partition_between_2 h)

theorem raw_partition_between_ok {above_low_bound below_high_bound : E → Bool} :
    ∀ {m : tree E}, bst m →
      bst (raw_partition_between above_low_bound below_high_bound m).1 ∧
      bst (raw_partition_between above_low_bound below_high_bound m).2
  | Leaf, _ => ⟨.leaf, .leaf⟩
  | Node _ l x0 r, hb => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    obtain ⟨l1, l2⟩ := raw_partition_between_ok (above_low_bound := above_low_bound)
      (below_high_bound := below_high_bound) hl
    obtain ⟨r1, r2⟩ := raw_partition_between_ok (above_low_bound := above_low_bound)
      (below_high_bound := below_high_bound) hr
    simp only [raw_partition_between]
    cases above_low_bound x0 <;> cases below_high_bound x0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ⟨r1, bst_join hl r2 ltl (fun y hy => gtr y (In_raw_partition_between_2 hy))⟩
    · exact ⟨r1, bst_join hl r2 ltl (fun y hy => gtr y (In_raw_partition_between_2 hy))⟩
    · exact ⟨l1, bst_join l2 hr (fun y hy => ltl y (In_raw_partition_between_2 hy)) gtr⟩
    · exact ⟨bst_join l1 r1 (fun y hy => ltl y (In_raw_partition_between_1 hy))
          (fun y hy => gtr y (In_raw_partition_between_1 hy)),
        bst_concat l2 r2 (fun a ha b hb => lt_trans _ _ _
          (ltl a (In_raw_partition_between_2 ha)) (gtr b (In_raw_partition_between_2 hb)))⟩

theorem In_raw_partition_between_3 {above_low_bound below_high_bound : E → Bool} {x : E} :
    ∀ {m : tree E}, In x (raw_partition_between above_low_bound below_high_bound m).1 →
      above_low_bound x = true ∧ below_high_bound x = true
  | Leaf, h => absurd h not_In_Leaf
  | Node _ l x0 r, h => by
    simp only [raw_partition_between] at h
    cases ha : above_low_bound x0 <;> cases hb : below_high_bound x0 <;>
      simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at h
    · exact In_raw_partition_between_3 h
    · exact In_raw_partition_between_3 h
    · exact In_raw_partition_between_3 h
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact In_raw_partition_between_3 h
      · exact ⟨ha, hb⟩
      · exact In_raw_partition_between_3 h

theorem In_raw_partition_between_4 {above_low_bound below_high_bound : E → Bool}
    (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} :
    ∀ {m : tree E}, bst m →
      In x (raw_partition_between above_low_bound below_high_bound m).2 →
      above_low_bound x = false ∨ below_high_bound x = false
  | Leaf, _, h => absurd h not_In_Leaf
  | Node _ l x0 r, hb, h => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    simp only [raw_partition_between] at h
    cases ha : above_low_bound x0 <;> cases hb' : below_high_bound x0 <;>
      simp only [ha, hb', Bool.false_eq_true, ↓reduceIte] at h
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · left; cases h1 : above_low_bound x
        · rfl
        · rw [above_monotone _ _ (.inr (ltl x h)) h1] at ha; cases ha
      · exact .inl ha
      · exact In_raw_partition_between_4 above_monotone below_monotone hr h
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · left; cases h1 : above_low_bound x
        · rfl
        · rw [above_monotone _ _ (.inr (ltl x h)) h1] at ha; cases ha
      · exact .inl ha
      · exact In_raw_partition_between_4 above_monotone below_monotone hr h
    · rcases (In_join _ _ _).1 h with h | rfl | h
      · exact In_raw_partition_between_4 above_monotone below_monotone hl h
      · exact .inr hb'
      · right; cases h1 : below_high_bound x
        · rfl
        · rw [below_monotone _ _ (.inr (gtr x h)) h1] at hb'; cases hb'
    · rcases In_concat.1 h with h | h
      · exact In_raw_partition_between_4 above_monotone below_monotone hl h
      · exact In_raw_partition_between_4 above_monotone below_monotone hr h

theorem In_raw_partition_between_5 {above_low_bound below_high_bound : E → Bool}
    (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} :
    ∀ {m : tree E}, bst m → In x m → above_low_bound x = true → below_high_bound x = true →
      In x (raw_partition_between above_low_bound below_high_bound m).1
  | Leaf, _, hi, _, _ => absurd hi not_In_Leaf
  | Node _ l x0 r, hb, hi, h1, h2 => by
    obtain ⟨hl, hr, ltl, gtr⟩ := bst_node_inv hb
    simp only [raw_partition_between]
    rw [In_node_iff] at hi
    cases ha : above_low_bound x0 <;> cases hb' : below_high_bound x0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact In_raw_partition_between_5 above_monotone below_monotone hr hi h1 h2
    · rcases hi with hi | rfl | hi
      · rw [above_monotone _ _ (.inr (ltl x hi)) h1] at ha; cases ha
      · rw [h1] at ha; cases ha
      · exact In_raw_partition_between_5 above_monotone below_monotone hr hi h1 h2
    · rcases hi with hi | rfl | hi
      · exact In_raw_partition_between_5 above_monotone below_monotone hl hi h1 h2
      · rw [h2] at hb'; cases hb'
      · rw [below_monotone _ _ (.inr (gtr x hi)) h2] at hb'; cases hb'
    · rw [In_join]
      rcases hi with hi | rfl | hi
      · exact .inl (In_raw_partition_between_5 above_monotone below_monotone hl hi h1 h2)
      · exact .inr (.inl rfl)
      · exact .inr (.inr (In_raw_partition_between_5 above_monotone below_monotone hr hi h1 h2))

theorem In_raw_partition_between_6 {above_low_bound below_high_bound : E → Bool} {x : E} :
    ∀ {m : tree E}, In x m → (above_low_bound x = false ∨ below_high_bound x = false) →
      In x (raw_partition_between above_low_bound below_high_bound m).2
  | Leaf, hi, _ => absurd hi not_In_Leaf
  | Node _ l x0 r, hi, h => by
    simp only [raw_partition_between]
    rw [In_node_iff] at hi
    cases ha : above_low_bound x0 <;> cases hb : below_high_bound x0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [In_join]
      rcases hi with hi | rfl | hi
      · exact .inl hi
      · exact .inr (.inl rfl)
      · exact .inr (.inr (In_raw_partition_between_6 hi h))
    · rw [In_join]
      rcases hi with hi | rfl | hi
      · exact .inl hi
      · exact .inr (.inl rfl)
      · exact .inr (.inr (In_raw_partition_between_6 hi h))
    · rw [In_join]
      rcases hi with hi | rfl | hi
      · exact .inl (In_raw_partition_between_6 hi h)
      · exact .inr (.inl rfl)
      · exact .inr (.inr hi)
    · rw [In_concat]
      rcases hi with hi | rfl | hi
      · exact .inl (In_raw_partition_between_6 hi h)
      · rw [ha, hb] at h; rcases h with h | h <;> cases h
      · exact .inr (In_raw_partition_between_6 hi h)

end Raw

/-- `FSetAVLplus.t`: the sets of `FSetAVL.Make(X)`. -/
abbrev t (E : Type _) [OrderedType E] : Type _ := FSetAVL.t E

section MEM_BETWEEN

variable (above_low_bound below_high_bound : E → Bool)

/-- `mem_between above below s`: does `s` have an element in the interval
described by `above` and `below`? -/
def mem_between (s : t E) : Bool := Raw.raw_mem_between above_low_bound below_high_bound s.1

variable {above_low_bound below_high_bound}

theorem mem_between_1 {s : t E} (h : mem_between above_low_bound below_high_bound s = true) :
    ∃ x, In x s ∧ above_low_bound x = true ∧ below_high_bound x = true :=
  Raw.raw_mem_between_1 h

theorem mem_between_2 (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} {s : t E}
    (hx : In x s) (h1 : above_low_bound x = true) (h2 : below_high_bound x = true) :
    mem_between above_low_bound below_high_bound s = true :=
  Raw.raw_mem_between_2 above_monotone below_monotone s.2 hx h1 h2

end MEM_BETWEEN

section ELEMENTS_BETWEEN

variable (above_low_bound below_high_bound : E → Bool)

/-- `elements_between above below s`: the set of elements of `s` in the
interval described by `above` and `below`. -/
def elements_between (s : t E) : t E :=
  ⟨Raw.raw_elements_between above_low_bound below_high_bound s.1,
    Raw.raw_elements_between_ok s.2⟩

variable {above_low_bound below_high_bound}

theorem elements_between_iff (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} {s : t E} :
    In x (elements_between above_low_bound below_high_bound s) ↔
      In x s ∧ above_low_bound x = true ∧ below_high_bound x = true :=
  ⟨fun h => ⟨Raw.In_raw_elements_between_1 h, Raw.In_raw_elements_between_2 h⟩,
   fun ⟨h, h1, h2⟩ => Raw.In_raw_elements_between_3 above_monotone below_monotone s.2 h h1 h2⟩

end ELEMENTS_BETWEEN

section FOR_ALL_BETWEEN

variable (pred above_low_bound below_high_bound : E → Bool)

/-- `for_all_between pred above below s`: do all elements of `s` in the
interval described by `above` and `below` satisfy `pred`? -/
def for_all_between (s : t E) : Bool :=
  Raw.raw_for_all_between pred above_low_bound below_high_bound s.1

variable {pred above_low_bound below_high_bound}

theorem for_all_between_iff (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {s : t E} :
    for_all_between pred above_low_bound below_high_bound s = true ↔
      ∀ x, In x s → above_low_bound x = true → below_high_bound x = true → pred x = true :=
  ⟨fun h _ hx h1 h2 => Raw.raw_for_all_between_1 above_monotone below_monotone s.2 h hx h1 h2,
   Raw.raw_for_all_between_2⟩

end FOR_ALL_BETWEEN

section PARTITION_BETWEEN

variable (above_low_bound below_high_bound : E → Bool)

/-- `partition_between above below s`: the elements of `s` inside the
interval described by `above` and `below`, and those outside. -/
def partition_between (s : t E) : t E × t E :=
  (⟨(Raw.raw_partition_between above_low_bound below_high_bound s.1).1,
     (Raw.raw_partition_between_ok s.2).1⟩,
   ⟨(Raw.raw_partition_between above_low_bound below_high_bound s.1).2,
     (Raw.raw_partition_between_ok s.2).2⟩)

variable {above_low_bound below_high_bound}

theorem partition_between_iff_1 (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} {s : t E} :
    In x (partition_between above_low_bound below_high_bound s).1 ↔
      In x s ∧ above_low_bound x = true ∧ below_high_bound x = true :=
  ⟨fun h => ⟨Raw.In_raw_partition_between_1 h, Raw.In_raw_partition_between_3 h⟩,
   fun ⟨h, h1, h2⟩ => Raw.In_raw_partition_between_5 above_monotone below_monotone s.2 h h1 h2⟩

theorem partition_between_iff_2 (above_monotone : AboveMonotone above_low_bound)
    (below_monotone : BelowMonotone below_high_bound) {x : E} {s : t E} :
    In x (partition_between above_low_bound below_high_bound s).2 ↔
      In x s ∧ (above_low_bound x = false ∨ below_high_bound x = false) :=
  ⟨fun h => ⟨Raw.In_raw_partition_between_2 h,
     Raw.In_raw_partition_between_4 above_monotone below_monotone s.2 h⟩,
   fun ⟨h, h'⟩ => Raw.In_raw_partition_between_6 h h'⟩

end PARTITION_BETWEEN

end FSetAVLplus
end CC
