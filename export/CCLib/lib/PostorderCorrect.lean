/-
  Correctness of the postorder numbering — port of the proofs of
  `lib/Postorder.v` (`invariant`, `postcondition`, `In_sort`,
  `transition_spec`, `initial_state_spec`, `reachable`,
  `postorder_correct`).

  Differences from Rocq: `Plt y next` is `y.toNat < next.toNat`; the
  iteration lemma `WfIter.iterate_prop` is replaced by `iterate_spec`,
  proved by well-founded recursion on the same measure as `iterate`.
-/
import CCLib.lib.Postorder

namespace CC
namespace Postorder

theorem mem_insertSorted {x a : Positive} :
    ∀ {l : List Positive}, x ∈ insertSorted a l ↔ x = a ∨ x ∈ l
  | [] => by simp [insertSorted]
  | y :: l => by
      simp only [insertSorted]
      split
      · simp only [List.mem_cons, mem_insertSorted (l := l)]
        exact ⟨fun h => by rcases h with h | h | h <;> simp [h],
          fun h => by rcases h with h | h | h <;> simp [h]⟩
      · exact List.mem_cons

/-- `Postorder.In_sort` -/
theorem mem_sort {x : Positive} : ∀ {l : List Positive}, x ∈ sort l ↔ x ∈ l
  | [] => by simp [sort]
  | a :: l => by simp only [sort, mem_insertSorted, mem_sort (l := l), List.mem_cons]

section POSTORDER
variable (ginit : Graph) (root : Node)

/-- `Postorder.invariant` -/
structure Invariant (s : State) : Prop where
  sub : ∀ x y, s.gr.get x = some y → ginit.get x = some y
  root : s.gr.get root = none
  below : ∀ x y, s.map.get x = some y → y.toNat < s.next.toNat
  inj : ∀ x1 x2 y, s.map.get x1 = some y → s.map.get x2 = some y → x1 = x2
  rem : ∀ x y, s.gr.get x = some y → s.map.get x = none
  color : ∀ x succs n y, ginit.get x = some succs → s.map.get x = some n →
    y ∈ succs → s.gr.get y = none
  wklist : ∀ x l, (x, l) ∈ s.wrk → s.gr.get x = none ∧
    ∃ l', ginit.get x = some l' ∧ ∀ y, y ∈ l' → y ∉ l → s.gr.get y = none
  grey : ∀ x, ginit.get x ≠ none → s.gr.get x = none → s.map.get x = none →
    ∃ l, (x, l) ∈ s.wrk

/-- `Postorder.postcondition` -/
structure Postcondition (map : PTree Positive) : Prop where
  inj : ∀ x1 x2 y, map.get x1 = some y → map.get x2 = some y → x1 = x2
  root : ginit.get root ≠ none → map.get root ≠ none
  succs : ∀ x succs y, ginit.get x = some succs → map.get x ≠ none → y ∈ succs →
    ginit.get y ≠ none → map.get y ≠ none

/-- `Postorder.transition_spec` -/
theorem transition_spec (s : State) (hi : Invariant ginit root s) :
    match transition s with
    | .inr s' => Invariant ginit root s'
    | .inl m => Postcondition ginit root m := by
  obtain ⟨SUB, ROOT, BELOW, INJ, REM, COLOR, WKLIST, GREY⟩ := hi
  unfold transition
  rcases hw : s.wrk with _ | ⟨⟨x, _ | ⟨y, succsX⟩⟩, l⟩
  · -- finished
    dsimp only
    refine ⟨INJ, fun h hm => ?_, fun x succs y hx hmx hy hgy hmy => ?_⟩
    · have hm' : s.map.get root = none := by simpa using hm
      obtain ⟨l, hl⟩ := GREY root h ROOT hm'
      rw [hw] at hl; cases hl
    · have hmy' : s.map.get y = none := by simpa using hmy
      cases hmx' : s.map.get x with
      | none => exact hmx hmx'
      | some n =>
          have := COLOR x succs n y hx hmx' hy
          obtain ⟨l, hl⟩ := GREY y hgy this hmy'
          rw [hw] at hl; cases hl
  · -- all children of x were traversed
    dsimp only
    obtain ⟨hgx, l', hl', hC⟩ := WKLIST x [] (by rw [hw]; exact List.mem_cons_self ..)
    refine ⟨SUB, ROOT, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x0 y h
      simp only [PTree.gsspec] at h
      split at h
      · cases h; simp
      · have := BELOW x0 y h; simp; omega
    · intro x1 x2 y h1 h2
      simp only [PTree.gsspec] at h1 h2
      split at h1 <;> split at h2
      · subst_vars; rfl
      · cases h1; have := BELOW _ _ h2; omega
      · cases h2; have := BELOW _ _ h1; omega
      · exact INJ _ _ _ h1 h2
    · intro x0 y h
      have hne : x0 ≠ x := by rintro rfl; rw [hgx] at h; cases h
      simp only [PTree.gsspec, hne, if_false]
      exact REM _ _ h
    · intro x0 succs n y hx0 hm hy
      simp only [PTree.gsspec] at hm
      split at hm
      · subst_vars
        rw [hl'] at hx0; cases hx0
        exact hC y hy (by simp)
      · exact COLOR _ _ _ _ hx0 hm hy
    · intro x0 l0 h
      exact WKLIST x0 l0 (by rw [hw]; exact List.mem_cons_of_mem _ h)
    · intro x0 hg hgr hm
      have hne : x0 ≠ x := by rintro rfl; simp at hm
      simp only [PTree.gsspec, hne, if_false] at hm
      obtain ⟨l1, hl1⟩ := GREY x0 hg hgr hm
      rw [hw] at hl1
      rcases List.mem_cons.mp hl1 with h | h
      · cases h; exact absurd rfl hne
      · exact ⟨l1, h⟩
  · obtain ⟨hgx, l', hl', hC⟩ :=
      WKLIST x (y :: succsX) (by rw [hw]; exact List.mem_cons_self ..)
    cases hgy : s.gr.get y with
    | none =>
      -- y is already numbered
      simp only [hgy]
      refine ⟨SUB, ROOT, BELOW, INJ, REM, COLOR, ?_, ?_⟩
      · intro x0 l0 h
        rcases List.mem_cons.mp h with h | h
        · cases h
          refine ⟨hgx, l', hl', fun z hz hnz => ?_⟩
          by_cases e : z = y
          · subst e; exact hgy
          · exact hC z hz (by simp [e, hnz])
        · exact WKLIST x0 l0 (by rw [hw]; exact List.mem_cons_of_mem _ h)
      · intro x0 hg hgr hm
        obtain ⟨l1, hl1⟩ := GREY x0 hg hgr hm
        rw [hw] at hl1
        rcases List.mem_cons.mp hl1 with h | h
        · cases h; exact ⟨succsX, List.mem_cons_self ..⟩
        · exact ⟨l1, List.mem_cons_of_mem _ h⟩
    | some succsY =>
      -- y has to be traversed
      simp only [hgy]
      refine ⟨?_, ?_, BELOW, INJ, ?_, ?_, ?_, ?_⟩
      · intro x0 y0 h
        simp only [PTree.grspec] at h
        split at h
        · cases h
        · exact SUB _ _ h
      · simp only [PTree.grspec]; split
        · rfl
        · exact ROOT
      · intro x0 y0 h
        simp only [PTree.grspec] at h
        split at h
        · cases h
        · exact REM _ _ h
      · intro x0 succs n y0 hx0 hm hy0
        simp only [PTree.grspec]; split
        · rfl
        · exact COLOR _ _ _ _ hx0 hm hy0
      · intro x0 l0 h
        rcases List.mem_cons.mp h with h | h
        · cases h
          refine ⟨by simp, succsY, SUB _ _ hgy, fun z hz hnz => absurd (mem_sort.mpr hz) hnz⟩
        rcases List.mem_cons.mp h with h | h
        · cases h
          refine ⟨?_, l', hl', fun z hz hnz => ?_⟩
          · simp only [PTree.grspec]; split
            · rfl
            · exact hgx
          · simp only [PTree.grspec]; split
            · rfl
            · rename_i e; exact hC z hz (by simp [e, hnz])
        · obtain ⟨hg0, l'', hl'', hC'⟩ :=
            WKLIST x0 l0 (by rw [hw]; exact List.mem_cons_of_mem _ h)
          refine ⟨?_, l'', hl'', fun z hz hnz => ?_⟩
          · simp only [PTree.grspec]; split
            · rfl
            · exact hg0
          · simp only [PTree.grspec]; split
            · rfl
            · exact hC' z hz hnz
      · intro x0 hg hgr hm
        simp only [PTree.grspec] at hgr
        split at hgr
        · subst_vars; exact ⟨sort succsY, List.mem_cons_self ..⟩
        · obtain ⟨l1, hl1⟩ := GREY x0 hg hgr hm
          rw [hw] at hl1
          rcases List.mem_cons.mp hl1 with h | h
          · cases h; exact ⟨succsX, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
          · exact ⟨l1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)⟩

/-- `Postorder.initial_state_spec` -/
theorem initial_state_spec : Invariant ginit root (initState ginit root) := by
  unfold initState
  split
  · rename_i succs hroot
    refine ⟨?_, by simp, by simp, by simp, by simp, by simp, ?_, ?_⟩
    · intro x y h
      simp only [PTree.grspec] at h
      split at h
      · cases h
      · exact h
    · intro x l h
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, succs, hroot, fun z hz hnz => absurd (mem_sort.mpr hz) hnz⟩
    · intro x hg hgr _
      simp only [PTree.grspec] at hgr
      split at hgr
      · subst_vars; exact ⟨_, List.mem_singleton_self _⟩
      · exact absurd hgr hg
  · rename_i hroot
    refine ⟨fun _ _ h => h, hroot, by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro x hg hgr _
    exact absurd hgr hg

/-- `WfIter.iterate_prop` for `iterate`. -/
theorem iterate_spec (s : State) (h : Invariant ginit root s) :
    Postcondition ginit root (iterate s) := by
  have hs := transition_spec ginit root s h
  unfold iterate
  split
  · rename_i m hm
    rw [hm] at hs; exact hs
  · rename_i s' hs'
    rw [hs'] at hs
    exact iterate_spec s' hs
termination_by measure s
decreasing_by exact transition_decreases (by assumption)

end POSTORDER

/-- `Postorder.reachable` -/
inductive Reachable (g : Graph) (root : Positive) : Positive → Prop where
  | root : Reachable g root root
  | succ {x succs y} : Reachable g root x → g.get x = some succs → y ∈ succs →
      Reachable g root y

/-- `Postorder.postorder_correct`: the numbering is injective and numbers
    every reachable node of the graph. -/
theorem postorder_correct (g : Graph) (root : Node) :
    (∀ x1 x2 y, (postorder g root).get x1 = some y → (postorder g root).get x2 = some y →
      x1 = x2) ∧
    (∀ x, Reachable g root x → g.get x ≠ none → (postorder g root).get x ≠ none) := by
  have hp := iterate_spec g root _ (initial_state_spec g root)
  refine ⟨hp.inj, fun x hx => ?_⟩
  induction hx with
  | root => exact hp.root
  | succ hx hg hy ih =>
      intro hgy
      exact hp.succs _ _ _ hg (ih (by rw [hg]; simp)) hy hgy

end Postorder
end CC
