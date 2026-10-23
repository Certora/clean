/-
  Finite sets of integer intervals — port of `lib/IntvSets.v`.

  A set is a list of nonempty semi-open intervals `[lo, hi)`, sorted in
  increasing order and with no overlap nor adjacency.

  Ported: `R.t`, `R.In`, `R.ok`, `R.mem`, `R.contains`, `R.add`,
  `R.remove`, `R.inter`, `R.union`, `R.beq`, and the interface `ISet.t`,
  `In`, `empty`, `interval`, `add`, `remove`, `inter`, `union`, `mem`,
  `contains`, `beq`.

  Proved: the specifications of the representation (`R.mem_In`,
  `R.contains_In`, `R.In_add`, `R.add_ok`, `R.In_remove`, `R.remove_ok`,
  `R.In_inter`, `R.inter_ok`, `R.In_ok_union`, `R.beq_spec` in the form
  `R.beq_eq`) and of the interface (`In_empty`, `In_interval`, `In_add`,
  `In_remove`, `In_inter`, `In_union`, `mem_spec`, `contains_spec`,
  `beq_sound`).  As in Rocq, `ISet.t` is the subtype `{ r | R.ok r }`.
-/
import CCLib.lib.Positive

namespace CC
namespace ISet

namespace R

/-- `ISet.R.t` -/
inductive T where
  | Nil
  | Cons (lo hi : Int) (tl : T)
  deriving DecidableEq, Repr, Inhabited

/-- `ISet.R.In` -/
def In (x : Int) : T → Prop
  | .Nil => False
  | .Cons l h s' => (l ≤ x ∧ x < h) ∨ In x s'

/-- `ISet.R.ok`: sorted, disjoint, non-adjacent, nonempty intervals. -/
inductive Ok : T → Prop where
  | nil : Ok .Nil
  | cons (l h s) : l < h → (∀ x, In x s → h < x) → Ok s → Ok (.Cons l h s)

/-- `ISet.R.mem` -/
def mem (x : Int) : T → Bool
  | .Nil => false
  | .Cons l h s' => if x < h then decide (l ≤ x) else mem x s'

/-- `ISet.R.contains` -/
def contains (L H : Int) : T → Bool
  | .Nil => false
  | .Cons l h s' => (decide (H ≤ h) && decide (l ≤ L)) || contains L H s'

/-- `ISet.R.add` -/
def add (L H : Int) : T → T
  | .Nil => .Cons L H .Nil
  | s@(.Cons l h s') =>
      if h < L then .Cons l h (add L H s')
      else if H < l then .Cons L H s
      else add (min l L) (max h H) s'

/-- `ISet.R.remove` -/
def remove (L H : Int) : T → T
  | .Nil => .Nil
  | s@(.Cons l h s') =>
      if h < L then .Cons l h (remove L H s')
      else if H < l then s
      else if l < L then
        (if H < h then .Cons l L (.Cons H h s') else .Cons l L (remove L H s'))
      else
        (if H < h then .Cons H h s' else remove L H s')

/-- `ISet.R.inter` -/
def inter : T → T → T
  | .Nil, _ => .Nil
  | .Cons _ _ _, .Nil => .Nil
  | .Cons l1 h1 s1', .Cons l2 h2 s2' =>
      if h1 ≤ l2 then inter s1' (.Cons l2 h2 s2')
      else if h2 ≤ l1 then inter (.Cons l1 h1 s1') s2'
      else if l1 ≤ l2 then
        (if h2 ≤ h1 then .Cons l2 h2 (inter (.Cons l1 h1 s1') s2')
         else .Cons l2 h1 (inter s1' (.Cons l2 h2 s2')))
      else
        (if h1 ≤ h2 then .Cons l1 h1 (inter s1' (.Cons l2 h2 s2'))
         else .Cons l1 h2 (inter (.Cons l1 h1 s1') s2'))
termination_by s1 s2 => sizeOf s1 + sizeOf s2

/-- `ISet.R.union` -/
def union : T → T → T
  | .Nil, s2 => s2
  | s1, .Nil => s1
  | .Cons l1 h1 s1', .Cons l2 h2 s2' => add l1 h1 (add l2 h2 (union s1' s2'))

/-- `ISet.R.beq` -/
def beq : T → T → Bool
  | .Nil, .Nil => true
  | .Cons l1 h1 t1, .Cons l2 h2 t2 => decide (l1 = l2) && decide (h1 = h2) && beq t1 t2
  | _, _ => false

/-- `ISet.R.mem_In` -/
theorem mem_In (x : Int) {s : T} (hs : Ok s) : mem x s = true ↔ In x s := by
  induction hs with
  | nil => simp [mem, In]
  | cons l h s hlh hbelow _ ih =>
      by_cases hx : x < h
      · have e : mem x (.Cons l h s) = decide (l ≤ x) := by simp [mem, hx]
        rw [e, decide_eq_true_iff]
        constructor
        · intro hl; exact .inl ⟨hl, hx⟩
        · rintro (⟨hl, _⟩ | hin)
          · exact hl
          · have := hbelow x hin; omega
      · have e : mem x (.Cons l h s) = mem x s := by simp [mem, hx]
        rw [e, ih]
        constructor
        · intro h'; exact .inr h'
        · rintro (⟨_, h'⟩ | h')
          · exact absurd h' hx
          · exact h'

/-- `ISet.R.contains_In` -/
theorem contains_In {L H : Int} (hLH : L < H) {s : T} (hs : Ok s) :
    contains L H s = true ↔ ∀ x, L ≤ x → x < H → In x s := by
  induction hs with
  | nil =>
      simp only [contains, In, Bool.false_eq_true, false_iff, Classical.not_forall]
      exact ⟨L, Int.le_refl _, hLH, id⟩
  | cons l h s hlh hbelow _ ih =>
      simp only [contains, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, In]
      constructor
      · rintro (⟨h1, h2⟩ | hc)
        · intro x hx1 hx2; exact .inl ⟨by omega, by omega⟩
        · intro x hx1 hx2; exact .inr ((ih.1 hc) x hx1 hx2)
      · intro hall
        by_cases hH : H ≤ h
        · by_cases hl : l ≤ L
          · exact .inl ⟨hH, hl⟩
          · rcases hall L (Int.le_refl _) hLH with ⟨h1, _⟩ | hin
            · omega
            · have := hbelow L hin; omega
        · right
          apply ih.2
          intro x hx1 hx2
          rcases hall x hx1 hx2 with ⟨_, h2⟩ | hin
          · exfalso
            rcases hall h (by
                rcases hall L (Int.le_refl _) hLH with ⟨h3, h4⟩ | hin'
                · omega
                · have := hbelow L hin'; omega) (by omega) with ⟨_, h5⟩ | hin''
            · omega
            · have := hbelow h hin''; omega
          · exact hin

/-- `ISet.R.In_add` -/
theorem In_add (x : Int) {s : T} (hs : Ok s) :
    ∀ L H, In x (add L H s) ↔ (L ≤ x ∧ x < H) ∨ In x s := by
  induction hs with
  | nil => intro L H; simp [add, In]
  | cons l h s hlh hbelow hs ih =>
      intro L H
      unfold add
      by_cases c1 : h < L
      · simp only [c1, if_true, In, ih]; exact or_left_comm
      · by_cases c2 : H < l
        · simp only [c1, c2, if_true, if_false, In]
        · simp only [c1, c2, if_false, ih, In]
          constructor
          · rintro (⟨h1, h2⟩ | hin)
            · by_cases hx : L ≤ x ∧ x < H
              · exact .inl hx
              · right; left; omega
            · exact .inr (.inr hin)
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | hin)
            · left; omega
            · left; omega
            · exact .inr hin

/-- `ISet.R.add_ok` -/
theorem add_ok {s : T} (hs : Ok s) : ∀ L H, L < H → Ok (add L H s) := by
  induction hs with
  | nil => intro L H hLH; exact .cons _ _ _ hLH (fun _ h => absurd h id) .nil
  | cons l h s hlh hbelow hs ih =>
      intro L H hLH
      unfold add
      by_cases c1 : h < L
      · simp only [c1, if_true]
        refine .cons _ _ _ hlh ?_ (ih L H hLH)
        intro x hx
        rcases (In_add x hs L H).1 hx with ⟨h1, _⟩ | hin
        · omega
        · exact hbelow x hin
      · by_cases c2 : H < l
        · simp only [c1, c2, if_true, if_false]
          refine .cons _ _ _ hLH ?_ (.cons _ _ _ hlh hbelow hs)
          intro x hx
          rcases hx with ⟨h1, _⟩ | hin
          · omega
          · have := hbelow x hin; omega
        · simp only [c1, c2, if_false]
          exact ih _ _ (by omega)

/-- `ISet.R.In_remove` -/
theorem In_remove (x L H : Int) {s : T} (hs : Ok s) :
    In x (remove L H s) ↔ ¬ (L ≤ x ∧ x < H) ∧ In x s := by
  induction hs with
  | nil => simp [remove, In]
  | cons l h s hlh hbelow hs ih =>
      unfold remove
      by_cases c1 : h < L
      · simp only [c1, if_true, In, ih]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨hn, hin⟩)
          · exact ⟨by omega, .inl ⟨h1, h2⟩⟩
          · exact ⟨hn, .inr hin⟩
        · rintro ⟨hn, ⟨h1, h2⟩ | hin⟩
          · exact .inl ⟨h1, h2⟩
          · exact .inr ⟨hn, hin⟩
      · by_cases c2 : H < l
        · simp only [c1, c2, if_true, if_false, In]
          constructor
          · rintro (⟨h1, h2⟩ | hin)
            · exact ⟨by omega, .inl ⟨h1, h2⟩⟩
            · have := hbelow x hin; exact ⟨by omega, .inr hin⟩
          · exact fun h => h.2
        · by_cases c3 : l < L
          · by_cases c4 : H < h
            · simp only [c1, c2, c3, c4, if_true, if_false, In]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | hin)
                · exact ⟨by omega, .inl ⟨h1, by omega⟩⟩
                · exact ⟨by omega, .inl ⟨by omega, h2⟩⟩
                · have := hbelow x hin; exact ⟨by omega, .inr hin⟩
              · rintro ⟨hn, ⟨h1, h2⟩ | hin⟩
                · by_cases hx : x < L
                  · exact .inl ⟨h1, hx⟩
                  · exact .inr (.inl ⟨by omega, h2⟩)
                · exact .inr (.inr hin)
            · simp only [c1, c2, c3, c4, if_true, if_false, In, ih]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hn, hin⟩)
                · exact ⟨by omega, .inl ⟨h1, by omega⟩⟩
                · exact ⟨hn, .inr hin⟩
              · rintro ⟨hn, ⟨h1, h2⟩ | hin⟩
                · exact .inl ⟨h1, by omega⟩
                · exact .inr ⟨hn, hin⟩
          · by_cases c4 : H < h
            · simp only [c1, c2, c3, c4, if_true, if_false, In]
              constructor
              · rintro (⟨h1, h2⟩ | hin)
                · exact ⟨by omega, .inl ⟨by omega, h2⟩⟩
                · have := hbelow x hin; exact ⟨by omega, .inr hin⟩
              · rintro ⟨hn, ⟨h1, h2⟩ | hin⟩
                · exact .inl ⟨by omega, h2⟩
                · exact .inr hin
            · simp only [c1, c2, c3, c4, if_false, In, ih]
              constructor
              · rintro ⟨hn, hin⟩; exact ⟨hn, .inr hin⟩
              · rintro ⟨hn, ⟨h1, h2⟩ | hin⟩
                · omega
                · exact ⟨hn, hin⟩

/-- `ISet.R.remove_ok` -/
theorem remove_ok {L H : Int} (hLH : L < H) {s : T} (hs : Ok s) : Ok (remove L H s) := by
  induction hs with
  | nil => exact .nil
  | cons l h s hlh hbelow hs ih =>
      unfold remove
      by_cases c1 : h < L
      · simp only [c1, if_true]
        exact .cons _ _ _ hlh (fun x hx => hbelow x ((In_remove x L H hs).1 hx).2) ih
      · by_cases c2 : H < l
        · simp only [c1, c2, if_true, if_false]; exact .cons _ _ _ hlh hbelow hs
        · by_cases c3 : l < L
          · by_cases c4 : H < h
            · simp only [c1, c2, c3, c4, if_true, if_false]
              refine .cons _ _ _ c3 ?_ (.cons _ _ _ c4 hbelow hs)
              intro x hx
              rcases hx with ⟨h1, _⟩ | hin
              · omega
              · have := hbelow x hin; omega
            · simp only [c1, c2, c3, c4, if_true, if_false]
              refine .cons _ _ _ c3 ?_ ih
              intro x hx
              have := (In_remove x L H hs).1 hx
              have := hbelow x this.2; omega
          · by_cases c4 : H < h
            · simp only [c1, c2, c3, c4, if_true, if_false]; exact .cons _ _ _ c4 hbelow hs
            · simp only [c1, c2, c3, c4, if_false]; exact ih

/-- `ISet.R.In_inter` -/
theorem In_inter (x : Int) : ∀ {s1 s2 : T}, Ok s1 → Ok s2 →
    (In x (inter s1 s2) ↔ In x s1 ∧ In x s2) := by
  intro s1 s2
  induction s1, s2 using inter.induct with
  | case1 s2 => intro _ _; simp [inter, In]
  | case2 l1 h1 s1' => intro _ _; simp [inter, In]
  | case3 l1 h1 s1' l2 h2 s2' c1 ih =>
      intro hs1 hs2
      cases hs1 with
      | cons _ _ _ hlh1 hb1 hs1' =>
      rw [inter, if_pos c1, ih hs1' hs2]
      simp only [In]
      constructor
      · rintro ⟨hin, h⟩; exact ⟨.inr hin, h⟩
      · rintro ⟨⟨a1, a2⟩ | hin, ⟨b1, b2⟩ | hin2⟩
        · omega
        · cases hs2 with
          | cons _ _ _ _ hb2 _ => have := hb2 x hin2; omega
        · exact ⟨hin, .inl ⟨b1, b2⟩⟩
        · exact ⟨hin, .inr hin2⟩
  | case4 l1 h1 s1' l2 h2 s2' c1 c2 ih =>
      intro hs1 hs2
      cases hs2 with
      | cons _ _ _ hlh2 hb2 hs2' =>
      rw [inter, if_neg c1, if_pos c2, ih hs1 hs2']
      simp only [In]
      constructor
      · rintro ⟨h, hin⟩; exact ⟨h, .inr hin⟩
      · rintro ⟨⟨a1, a2⟩ | hin, ⟨b1, b2⟩ | hin2⟩
        · omega
        · exact ⟨.inl ⟨a1, a2⟩, hin2⟩
        · cases hs1 with
          | cons _ _ _ _ hb1 _ => have := hb1 x hin; omega
        · exact ⟨.inr hin, hin2⟩
  | case5 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs2 with
      | cons _ _ _ hlh2 hb2 hs2' =>
      rw [inter, if_neg c1, if_neg c2, if_pos c3, if_pos c4]
      simp only [In, ih hs1 hs2']
      constructor
      · rintro (⟨a1, a2⟩ | ⟨h, hin⟩)
        · exact ⟨.inl ⟨by omega, by omega⟩, .inl ⟨a1, a2⟩⟩
        · exact ⟨h, .inr hin⟩
      · rintro ⟨h, ⟨b1, b2⟩ | hin2⟩
        · exact .inl ⟨b1, b2⟩
        · exact .inr ⟨h, hin2⟩
  | case6 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs1 with
      | cons _ _ _ hlh1 hb1 hs1' =>
      rw [inter, if_neg c1, if_neg c2, if_pos c3, if_neg c4]
      simp only [In, ih hs1' hs2]
      constructor
      · rintro (⟨a1, a2⟩ | ⟨hin, h⟩)
        · exact ⟨.inl ⟨by omega, a2⟩, .inl ⟨a1, by omega⟩⟩
        · exact ⟨.inr hin, h⟩
      · rintro ⟨⟨a1, a2⟩ | hin, h⟩
        · rcases h with ⟨b1, b2⟩ | hin2
          · exact .inl ⟨b1, a2⟩
          · cases hs2 with
            | cons _ _ _ _ hb2 _ => have := hb2 x hin2; omega
        · exact .inr ⟨hin, h⟩
  | case7 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs1 with
      | cons _ _ _ hlh1 hb1 hs1' =>
      rw [inter, if_neg c1, if_neg c2, if_neg c3, if_pos c4]
      simp only [In, ih hs1' hs2]
      constructor
      · rintro (⟨a1, a2⟩ | ⟨hin, h⟩)
        · exact ⟨.inl ⟨a1, a2⟩, .inl ⟨by omega, by omega⟩⟩
        · exact ⟨.inr hin, h⟩
      · rintro ⟨⟨a1, a2⟩ | hin, h⟩
        · exact .inl ⟨a1, a2⟩
        · exact .inr ⟨hin, h⟩
  | case8 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs2 with
      | cons _ _ _ hlh2 hb2 hs2' =>
      rw [inter, if_neg c1, if_neg c2, if_neg c3, if_neg c4]
      simp only [In, ih hs1 hs2']
      constructor
      · rintro (⟨a1, a2⟩ | ⟨h, hin⟩)
        · exact ⟨.inl ⟨a1, by omega⟩, .inl ⟨by omega, a2⟩⟩
        · exact ⟨h, .inr hin⟩
      · rintro ⟨h, ⟨b1, b2⟩ | hin2⟩
        · rcases h with ⟨a1, a2⟩ | hin
          · exact .inl ⟨a1, b2⟩
          · cases hs1 with
            | cons _ _ _ _ hb1 _ => have := hb1 x hin; omega
        · exact .inr ⟨h, hin2⟩

/-- `ISet.R.inter_ok` -/
theorem inter_ok : ∀ {s1 s2 : T}, Ok s1 → Ok s2 → Ok (inter s1 s2) := by
  intro s1 s2
  induction s1, s2 using inter.induct with
  | case1 s2 => intro _ _; rw [inter]; exact .nil
  | case2 l1 h1 s1' => intro _ _; rw [inter]; exact .nil
  | case3 l1 h1 s1' l2 h2 s2' c1 ih =>
      intro hs1 hs2
      cases hs1 with
      | cons _ _ _ _ _ hs1' => rw [inter, if_pos c1]; exact ih hs1' hs2
  | case4 l1 h1 s1' l2 h2 s2' c1 c2 ih =>
      intro hs1 hs2
      cases hs2 with
      | cons _ _ _ _ _ hs2' => rw [inter, if_neg c1, if_pos c2]; exact ih hs1 hs2'
  | case5 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs2 with
      | cons _ _ _ hlh2 hb2 hs2' =>
      rw [inter, if_neg c1, if_neg c2, if_pos c3, if_pos c4]
      exact .cons _ _ _ hlh2 (fun x hx => hb2 x ((In_inter x hs1 hs2').1 hx).2) (ih hs1 hs2')
  | case6 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs1 with
      | cons _ _ _ hlh1 hb1 hs1' =>
      rw [inter, if_neg c1, if_neg c2, if_pos c3, if_neg c4]
      exact .cons _ _ _ (by omega) (fun x hx => hb1 x ((In_inter x hs1' hs2).1 hx).1) (ih hs1' hs2)
  | case7 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs1 with
      | cons _ _ _ hlh1 hb1 hs1' =>
      rw [inter, if_neg c1, if_neg c2, if_neg c3, if_pos c4]
      exact .cons _ _ _ hlh1 (fun x hx => hb1 x ((In_inter x hs1' hs2).1 hx).1) (ih hs1' hs2)
  | case8 l1 h1 s1' l2 h2 s2' c1 c2 c3 c4 ih =>
      intro hs1 hs2
      cases hs2 with
      | cons _ _ _ hlh2 hb2 hs2' =>
      rw [inter, if_neg c1, if_neg c2, if_neg c3, if_neg c4]
      exact .cons _ _ _ (by omega) (fun x hx => hb2 x ((In_inter x hs1 hs2').1 hx).2) (ih hs1 hs2')

/-- `ISet.R.In_ok_union` -/
theorem In_ok_union : ∀ {s1 s2 : T}, Ok s1 → Ok s2 →
    Ok (union s1 s2) ∧ ∀ x, (In x s1 ∨ In x s2 ↔ In x (union s1 s2))
  | .Nil, s2, _, h2 => by simp only [union, In, false_or]; exact ⟨h2, fun _ => trivial⟩
  | .Cons l h s, .Nil, h1, _ => by simp only [union, In, or_false]; exact ⟨h1, fun _ => trivial⟩
  | .Cons l1 h1 s1, .Cons l2 h2 s2, hs1, hs2 => by
      cases hs1 with
      | cons _ _ _ hlh1 _ hs1' =>
      cases hs2 with
      | cons _ _ _ hlh2 _ hs2' =>
      obtain ⟨A, B⟩ := In_ok_union hs1' hs2'
      have A2 := add_ok A l2 h2 hlh2
      refine ⟨add_ok A2 l1 h1 hlh1, fun x => ?_⟩
      simp only [union, In, In_add x A2, In_add x A, ← B]
      constructor
      · rintro ((h | h) | (h | h))
        · exact .inl h
        · exact .inr (.inr (.inl h))
        · exact .inr (.inl h)
        · exact .inr (.inr (.inr h))
      · rintro (h | h | h | h)
        · exact .inl (.inl h)
        · exact .inr (.inl h)
        · exact .inl (.inr h)
        · exact .inr (.inr h)

/-- `ISet.R.beq_spec` (the direction used: equal representations). -/
theorem beq_eq : ∀ {s1 s2 : T}, beq s1 s2 = true → s1 = s2
  | .Nil, .Nil, _ => rfl
  | .Cons _ _ _, .Cons _ _ _, h => by
      simp only [beq, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h
      rw [beq_eq h]
  | .Nil, .Cons _ _ _, h => by simp [beq] at h
  | .Cons _ _ _, .Nil, h => by simp [beq] at h

end R

/-- `ISet.t`: the well-formed interval sets. -/
def T : Type := { r : R.T // R.Ok r }

instance : Inhabited T := ⟨⟨.Nil, .nil⟩⟩

/-- `ISet.In` -/
def In (x : Int) (s : T) : Prop := R.In x s.val

/-- `ISet.empty` -/
def empty : T := ⟨.Nil, .nil⟩

/-- `ISet.interval` -/
def interval (l h : Int) : T :=
  if hlh : l < h then ⟨.Cons l h .Nil, .cons _ _ _ hlh (fun _ hx => absurd hx id) .nil⟩ else empty

/-- `ISet.add` -/
def add (l h : Int) (s : T) : T :=
  if hlh : l < h then ⟨R.add l h s.val, R.add_ok s.property l h hlh⟩ else s

/-- `ISet.remove` -/
def remove (l h : Int) (s : T) : T :=
  if hlh : l < h then ⟨R.remove l h s.val, R.remove_ok hlh s.property⟩ else s

/-- `ISet.inter` -/
def inter (s1 s2 : T) : T := ⟨R.inter s1.val s2.val, R.inter_ok s1.property s2.property⟩

/-- `ISet.union` -/
def union (s1 s2 : T) : T :=
  ⟨R.union s1.val s2.val, (R.In_ok_union s1.property s2.property).1⟩

/-- `ISet.mem` -/
def mem (x : Int) (s : T) : Bool := R.mem x s.val

/-- `ISet.contains`: is `[l, h)` contained in `s`? -/
def contains (l h : Int) (s : T) : Bool := if l < h then R.contains l h s.val else true

/-- `ISet.beq` -/
def beq (s1 s2 : T) : Bool := R.beq s1.val s2.val

/-- `ISet.In_empty` -/
theorem In_empty (x : Int) : ¬ In x empty := id

/-- `ISet.In_interval` -/
theorem In_interval (x l h : Int) : In x (interval l h) ↔ l ≤ x ∧ x < h := by
  unfold interval In
  split
  · simp only [R.In, or_false]
  · simp only [empty, R.In, false_iff]; omega

/-- `ISet.In_add` -/
theorem In_add (x l h : Int) (s : T) : In x (add l h s) ↔ (l ≤ x ∧ x < h) ∨ In x s := by
  unfold add In
  split
  · exact R.In_add x s.property l h
  · constructor
    · exact .inr
    · rintro (⟨h1, h2⟩ | hin)
      · omega
      · exact hin

/-- `ISet.In_remove` -/
theorem In_remove (x l h : Int) (s : T) : In x (remove l h s) ↔ ¬ (l ≤ x ∧ x < h) ∧ In x s := by
  unfold remove In
  split
  · exact R.In_remove x l h s.property
  · constructor
    · intro hin; exact ⟨by omega, hin⟩
    · exact fun h => h.2

/-- `ISet.In_inter` -/
theorem In_inter (x : Int) (s1 s2 : T) : In x (inter s1 s2) ↔ In x s1 ∧ In x s2 :=
  R.In_inter x s1.property s2.property

/-- `ISet.In_union` -/
theorem In_union (x : Int) (s1 s2 : T) : In x (union s1 s2) ↔ In x s1 ∨ In x s2 :=
  ((R.In_ok_union s1.property s2.property).2 x).symm

/-- `ISet.mem_spec` -/
theorem mem_spec (x : Int) (s : T) : mem x s = true ↔ In x s := R.mem_In x s.property

/-- `ISet.contains_spec` -/
theorem contains_spec (l h : Int) (s : T) :
    contains l h s = true ↔ ∀ x, l ≤ x → x < h → In x s := by
  unfold contains
  split
  · exact R.contains_In ‹_› s.property
  · simp only [true_iff]; intro x h1 h2; omega

/-- `ISet.beq_spec` (soundness direction). -/
theorem beq_sound {s1 s2 : T} (h : beq s1 s2 = true) (x : Int) : In x s1 ↔ In x s2 := by
  unfold In; rw [R.beq_eq h]

end ISet
end CC
