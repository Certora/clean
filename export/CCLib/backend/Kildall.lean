/-
  Kildall's dataflow solvers — port of `backend/Kildall.v` (forward and
  backward solvers).  `PrimIter` (from `lib/Iteration.v`) lives in
  `lib/Iteration.lean`.

  Ported: the `NODE_SET` signature
  (as a class) with `NodeSetForward` / `NodeSetBackward`; `reachable` with
  `reachable_trans` / `reachable_right`; the forward solver
  `Dataflow_Solver` (`propagate_succ`, `propagate_succ_list`, `step`,
  `fixpoint`, `fixpoint_nodeset`, `fixpoint_allnodes`) with its theorems
  `fixpoint_solution`, `fixpoint_entry`, `fixpoint_allnodes_solution`,
  `fixpoint_nodeset_solution` and `fixpoint_invariant`;
  `successors_list`, `add_successors`, `make_predecessors` with
  `make_predecessors_correct_1/2` and `reachable_predecessors`; the
  backward solver `Backward_Dataflow_Solver` (`sequential_node`,
  `exit_points`, `fixpoint`, `fixpoint_allnodes`) with
  `reachable_exit_points(_predecessor)`, `fixpoint_solution` and
  `fixpoint_allnodes_solution`.

  Differences from Rocq:
  * `PrimIter.iterate` is bounded iteration with `num_iterations`
    (10^12) steps of fuel, as Rocq's definition behaves.
  * Node sets are sorted lists (descending for the forward solver, so
    that `pick` returns the largest node like Rocq's `PHeap.findMax`;
    ascending for the backward solver) instead of Rocq's splay heaps
    (`lib/Heaps.v`).
  * The block solver `BBlock_solver` is not ported; of
    `exit_points_charact` only the direction used by the proofs is stated.
-/
import CCLib.lib.Lattice
import CCLib.lib.Iteration
import CCLib.lib.MapsTheory

namespace CC

/-! ## Node sets -/

/-- `Kildall.NODE_SET` -/
class NodeSet (t : Type) where
  empty : t
  add : Positive → t → t
  pick : t → Option (Positive × t)
  allNodes : {A : Type} → PTree A → t
  In : Positive → t → Prop
  empty_spec : ∀ n, ¬ In n empty
  add_spec : ∀ n n' s, In n' (add n s) ↔ n = n' ∨ In n' s
  pick_none : ∀ s n, pick s = none → ¬ In n s
  pick_some : ∀ s n s', pick s = some (n, s') → ∀ n', In n' s ↔ n = n' ∨ In n' s'
  allNodes_spec : ∀ {A : Type} (code : PTree A) n instr, code.get n = some instr → In n (allNodes code)

namespace NodeSetImpl

/-- Insertion in a sorted list without duplicates, for the order `before`. -/
def insert (before : Positive → Positive → Bool) (n : Positive) : List Positive → List Positive
  | [] => [n]
  | x :: l => if n = x then x :: l else if before n x then n :: x :: l else x :: insert before n l

theorem mem_insert (before : Positive → Positive → Bool) (n n' : Positive) :
    ∀ l, n' ∈ insert before n l ↔ n = n' ∨ n' ∈ l
  | [] => by simp [insert, eq_comm]
  | x :: l => by
    simp only [insert]
    split
    · next h => subst h; simp only [List.mem_cons]; constructor
                · intro h; exact .inr h
                · rintro (h | h)
                  · exact .inl h.symm
                  · exact h
    · split
      · simp [eq_comm]
      · simp only [List.mem_cons, mem_insert before n n' l]
        constructor
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inr (.inl h)
          · exact .inl h
          · exact .inr (.inr h)

theorem foldl_insert_mem {A : Type} (before : Positive → Positive → Bool) (n : Positive) :
    ∀ (L : List (Positive × A)) (s : List Positive),
      (n ∈ s ∨ n ∈ L.map Prod.fst) →
      n ∈ L.foldl (fun a p => insert before p.1 a) s
  | [], _, h => by simpa using h
  | (k, _) :: L, s, h => by
    apply foldl_insert_mem before n L
    simp only [List.map_cons, List.mem_cons] at h
    rcases h with h | h | h
    · exact .inl ((mem_insert before k n s).mpr (.inr h))
    · exact .inl ((mem_insert before k n s).mpr (.inl h.symm))
    · exact .inr h

end NodeSetImpl

/-- `Kildall.NodeSetForward`: `pick` returns the largest node. -/
structure NodeSetForward where
  elts : List Positive

/-- `Kildall.NodeSetBackward`: `pick` returns the smallest node. -/
structure NodeSetBackward where
  elts : List Positive

private theorem allNodes_spec_aux (before : Positive → Positive → Bool) {A : Type}
    (code : PTree A) (n : Positive) (instr : A) (h : code.get n = some instr) :
    n ∈ (PTree.elements code).foldl (fun a p => NodeSetImpl.insert before p.1 a) [] :=
  NodeSetImpl.foldl_insert_mem before n _ _
    (.inr (List.mem_map_of_mem (f := Prod.fst) (PTree.elements_correct code n instr h)))

instance : NodeSet NodeSetForward where
  empty := ⟨[]⟩
  add n s := ⟨NodeSetImpl.insert (fun a b => decide (b.toNat < a.toNat)) n s.elts⟩
  pick s := match s.elts with
    | [] => none
    | x :: l => some (x, ⟨l⟩)
  allNodes code := ⟨PTree.fold (fun s pc _ => NodeSetImpl.insert (fun a b => decide (b.toNat < a.toNat)) pc s) code []⟩
  In n s := n ∈ s.elts
  empty_spec _ := by simp
  add_spec n n' s := NodeSetImpl.mem_insert _ n n' s.elts
  pick_none s n h := by
    cases s with | mk elts => cases elts with
      | nil => simp
      | cons => simp at h
  pick_some s n s' h n' := by
    cases s with | mk elts => cases elts with
      | nil => simp at h
      | cons x l =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [eq_comm]
  allNodes_spec code n instr h := allNodes_spec_aux _ code n instr h

instance : NodeSet NodeSetBackward where
  empty := ⟨[]⟩
  add n s := ⟨NodeSetImpl.insert (fun a b => decide (a.toNat < b.toNat)) n s.elts⟩
  pick s := match s.elts with
    | [] => none
    | x :: l => some (x, ⟨l⟩)
  allNodes code := ⟨PTree.fold (fun s pc _ => NodeSetImpl.insert (fun a b => decide (a.toNat < b.toNat)) pc s) code []⟩
  In n s := n ∈ s.elts
  empty_spec _ := by simp
  add_spec n n' s := NodeSetImpl.mem_insert _ n n' s.elts
  pick_none s n h := by
    cases s with | mk elts => cases elts with
      | nil => simp
      | cons => simp at h
  pick_some s n s' h n' := by
    cases s with | mk elts => cases elts with
      | nil => simp at h
      | cons x l =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [eq_comm]
  allNodes_spec code n instr h := allNodes_spec_aux _ code n instr h

/-! ## Reachability -/

namespace Kildall

section REACHABLE
variable {A : Type} (code : PTree A) (successors : A → List Positive)

/-- `Kildall.reachable` -/
inductive Reachable : Positive → Positive → Prop where
  | refl (n) : Reachable n n
  | left (n1 n2 n3 i) : code.get n1 = some i → n2 ∈ successors i → Reachable n2 n3 → Reachable n1 n3

variable {code successors}

/-- `Kildall.reachable_trans` -/
theorem reachable_trans {n1 n2 n3 : Positive} (h1 : Reachable code successors n1 n2)
    (h2 : Reachable code successors n2 n3) : Reachable code successors n1 n3 := by
  induction h1 with
  | refl => exact h2
  | left _ _ _ _ hc hs _ ih => exact .left _ _ _ _ hc hs (ih h2)

/-- `Kildall.reachable_right` -/
theorem reachable_right {n1 n2 n3 : Positive} {i : A} (h : Reachable code successors n1 n2)
    (hc : code.get n2 = some i) (hs : n3 ∈ successors i) : Reachable code successors n1 n3 :=
  reachable_trans h (.left _ _ _ _ hc hs (.refl _))

end REACHABLE

/-! ## The forward solver `Dataflow_Solver` -/

section Kildall
variable {L NS : Type} [Semilattice L] [NodeSet NS]
variable {A : Type} (code : PTree A) (successors : A → List Positive) (transf : Positive → L → L)

open Semilattice NodeSet

/-- `Dataflow_Solver.state` (`visited` is a ghost component). -/
structure State (L NS : Type) where
  aval : PTree L
  worklist : NS
  visited : Positive → Prop

/-- `Dataflow_Solver.abstr_value` -/
def abstrValue (n : Positive) (s : State L NS) : L := (s.aval.get n).getD bot

/-- `Dataflow_Solver.propagate_succ` -/
def propagateSucc (s : State L NS) (out : L) (n : Positive) : State L NS :=
  match s.aval.get n with
  | none => ⟨s.aval.set n out, add n s.worklist, fun p => p = n ∨ s.visited p⟩
  | some oldl =>
      let newl := lub oldl out
      if beq oldl newl then s
      else ⟨s.aval.set n newl, add n s.worklist, fun p => p = n ∨ s.visited p⟩

/-- `Dataflow_Solver.propagate_succ_list` -/
def propagateSuccList (s : State L NS) (out : L) : List Positive → State L NS
  | [] => s
  | n :: rem => propagateSuccList (propagateSucc s out n) out rem

/-- `Dataflow_Solver.step` -/
def step (s : State L NS) : PMap L ⊕ State L NS :=
  match pick s.worklist with
  | none => .inl ⟨bot, s.aval⟩
  | some (n, rem) =>
      match code.get n with
      | none => .inr ⟨s.aval, rem, s.visited⟩
      | some instr =>
          .inr (propagateSuccList ⟨s.aval, rem, s.visited⟩ (transf n (abstrValue n s))
            (successors instr))

/-- `Dataflow_Solver.fixpoint_from` -/
def fixpointFrom (start : State L NS) : Option (PMap L) :=
  PrimIter.iterate (step code successors transf) start

/-- `Dataflow_Solver.start_state` -/
def startState (enode : Positive) (eval : L) : State L NS :=
  ⟨PTree.empty.set enode eval, add enode empty, fun n => n = enode⟩

/-- `Dataflow_Solver.fixpoint` -/
def fixpoint (enode : Positive) (eval : L) : Option (PMap L) :=
  fixpointFrom code successors transf (startState (NS := NS) enode eval)

/-- `Dataflow_Solver.start_state_nodeset` -/
def startStateNodeset (enodes : NS) : State L NS :=
  ⟨PTree.empty, enodes, fun n => In n enodes⟩

/-- `Dataflow_Solver.fixpoint_nodeset` -/
def fixpointNodeset (enodes : NS) : Option (PMap L) :=
  fixpointFrom code successors transf (startStateNodeset enodes)

/-- `Dataflow_Solver.start_state_allnodes` -/
def startStateAllnodes : State L NS :=
  ⟨PTree.empty, allNodes code, fun n => ∃ instr, code.get n = some instr⟩

/-- `Dataflow_Solver.fixpoint_allnodes` -/
def fixpointAllnodes : Option (PMap L) :=
  fixpointFrom (NS := NS) code successors transf (startStateAllnodes code)

/-- `Dataflow_Solver.optge` -/
inductive Optge : Option L → Option L → Prop where
  | some (l l' : L) : ge l l' → Optge (some l) (some l')
  | none (ol : Option L) : Optge ol none

omit [NodeSet NS] in
theorem optge_refl (ol : Option L) : Optge ol ol := by
  cases ol with
  | none => exact .none _
  | some l => exact .some _ _ (ge_refl (eq_refl l))

omit [NodeSet NS] in
theorem optge_trans {ol1 ol2 ol3 : Option L} (h1 : Optge ol1 ol2) (h2 : Optge ol2 ol3) :
    Optge ol1 ol3 := by
  cases h2 with
  | none => exact .none _
  | some _ _ h => cases h1 with
    | some _ _ h' => exact .some _ _ (ge_trans h' h)

omit [NodeSet NS] in
theorem optge_abstrValue {st st' : State L NS} {n : Positive}
    (h : Optge (st.aval.get n) (st'.aval.get n)) : ge (abstrValue n st) (abstrValue n st') := by
  unfold abstrValue
  generalize st.aval.get n = a at h ⊢
  generalize st'.aval.get n = b at h ⊢
  cases h with
  | some _ _ h' => simpa using h'
  | none => exact ge_bot _

omit [NodeSet NS] in
theorem optge_some_inv {o : Option L} {l' : L} (h : Optge o (some l')) :
    ∃ l, o = some l ∧ ge l l' := by
  generalize hl : some l' = o' at h
  cases h with
  | some l _ h => cases hl; exact ⟨l, rfl, h⟩
  | none => cases hl

/-- `Dataflow_Solver.propagate_succ_charact` -/
theorem propagateSucc_charact (st : State L NS) (out : L) (n : Positive) :
    let st' := propagateSucc st out n
    Optge (st'.aval.get n) (some out)
    ∧ (∀ s, n ≠ s → st'.aval.get s = st.aval.get s)
    ∧ (∀ s, Optge (st'.aval.get s) (st.aval.get s))
    ∧ (In n st'.worklist ∨ st'.aval.get n = st.aval.get n)
    ∧ (∀ n', In n' st.worklist → In n' st'.worklist)
    ∧ (∀ n', In n' st'.worklist → n' = n ∨ In n' st.worklist)
    ∧ (∀ n', st.visited n' → st'.visited n')
    ∧ (∀ n', st'.visited n' → In n' st'.worklist ∨ st.visited n')
    ∧ (∀ n', st.aval.get n' = none → st'.aval.get n' ≠ none → st'.visited n') := by
  intro st'
  unfold st' propagateSucc
  cases E : st.aval.get n with
  | none =>
    simp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [PTree.gss]; exact optge_refl _
    · intro s hs; rw [PTree.gso _ _ _ _ hs]
    · intro s
      rw [PTree.gsspec]
      split
      · next h => subst h; rw [E]; exact .none _
      · exact optge_refl _
    · exact .inl ((add_spec _ _ _).mpr (.inl rfl))
    · intro n' h; exact (add_spec _ _ _).mpr (.inr h)
    · intro n' h
      rcases (add_spec _ _ _).mp h with h | h
      · exact .inl h.symm
      · exact .inr h
    · intro n' h; exact .inr h
    · intro n' h
      rcases h with h | h
      · subst h; exact .inl ((add_spec _ _ _).mpr (.inl rfl))
      · exact .inr h
    · intro n' h1 h2
      rw [PTree.gsspec] at h2
      split at h2
      · next h => exact .inl h
      · exact absurd h1 h2
  | some v =>
    simp only
    split
    · next hb =>
      have heq := beq_correct hb
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [E]; exact .some _ _ (ge_trans (ge_refl heq) (ge_lub_right _ _))
      · intro s _; rfl
      · intro s; exact optge_refl _
      · exact .inr E
      · intro n' h; exact h
      · intro n' h; exact .inr h
      · intro n' h; exact h
      · intro n' h; exact .inr h
      · intro n' h1 h2; exact absurd h1 h2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [PTree.gss]; exact .some _ _ (ge_lub_right _ _)
      · intro s hs; rw [PTree.gso _ _ _ _ hs]
      · intro s
        rw [PTree.gsspec]
        split
        · next h => subst h; rw [E]; exact .some _ _ (ge_lub_left _ _)
        · exact optge_refl _
      · exact .inl ((add_spec _ _ _).mpr (.inl rfl))
      · intro n' h; exact (add_spec _ _ _).mpr (.inr h)
      · intro n' h
        rcases (add_spec _ _ _).mp h with h | h
        · exact .inl h.symm
        · exact .inr h
      · intro n' h; exact .inr h
      · intro n' h
        rcases h with h | h
        · subst h; exact .inl ((add_spec _ _ _).mpr (.inl rfl))
        · exact .inr h
      · intro n' h1 h2
        rw [PTree.gsspec] at h2
        split at h2
        · next h => exact .inl h
        · exact absurd h1 h2

/-- `Dataflow_Solver.propagate_succ_list_charact` -/
theorem propagateSuccList_charact (out : L) :
    ∀ (l : List Positive) (st : State L NS),
    let st' := propagateSuccList st out l
    (∀ n, n ∈ l → Optge (st'.aval.get n) (some out))
    ∧ (∀ n, n ∉ l → st'.aval.get n = st.aval.get n)
    ∧ (∀ n, Optge (st'.aval.get n) (st.aval.get n))
    ∧ (∀ n, In n st'.worklist ∨ st'.aval.get n = st.aval.get n)
    ∧ (∀ n', In n' st.worklist → In n' st'.worklist)
    ∧ (∀ n', In n' st'.worklist → n' ∈ l ∨ In n' st.worklist)
    ∧ (∀ n', st.visited n' → st'.visited n')
    ∧ (∀ n', st'.visited n' → In n' st'.worklist ∨ st.visited n')
    ∧ (∀ n', st.aval.get n' = none → st'.aval.get n' ≠ none → st'.visited n')
  | [], st => by
    intro st'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n h; simp at h
    · intro n _; rfl
    · intro n; exact optge_refl _
    · intro n; exact .inr rfl
    · intro n' h; exact h
    · intro n' h; exact .inr h
    · intro n' h; exact h
    · intro n' h; exact .inr h
    · intro n' h1 h2; exact absurd h1 h2
  | a :: l, st => by
    obtain ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9⟩ := propagateSucc_charact st out a
    obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9⟩ := propagateSuccList_charact out l (propagateSucc st out a)
    simp only [propagateSuccList]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact optge_trans (B3 n) A1
      · exact B1 n hn
    · intro n hn
      simp only [List.mem_cons, not_or] at hn
      rw [B2 n hn.2, A2 n (Ne.symm hn.1)]
    · intro n; exact optge_trans (B3 n) (A3 n)
    · intro n
      rcases B4 n with h | h
      · exact .inl h
      · by_cases hna : n = a
        · subst hna
          rcases A4 with h' | h'
          · exact .inl (B5 _ h')
          · exact .inr (h.trans h')
        · exact .inr (h.trans (A2 n (Ne.symm hna)))
    · intro n' h; exact B5 _ (A5 _ h)
    · intro n' h
      rcases B6 n' h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rcases A6 n' h with h | h
        · exact .inl (h ▸ List.mem_cons_self)
        · exact .inr h
    · intro n' h; exact B7 _ (A7 _ h)
    · intro n' h
      rcases B8 n' h with h | h
      · exact .inl h
      · rcases A8 n' h with h | h
        · exact .inl (B5 _ h)
        · exact .inr h
    · intro n' h1 h2
      cases hst1 : (propagateSucc st out a).aval.get n' with
      | some _ => exact B7 _ (A9 _ h1 (by rw [hst1]; simp))
      | none => exact B9 _ hst1 h2

/-- `Dataflow_Solver.steps` -/
inductive Steps : State L NS → State L NS → Prop where
  | base (s) : Steps s s
  | right (s1 s2 s3) : Steps s1 s2 → step code successors transf s2 = .inr s3 → Steps s1 s3

/-- `Dataflow_Solver.fixpoint_from_charact` -/
theorem fixpointFrom_charact (start : State L NS) (res : PMap L)
    (h : fixpointFrom code successors transf start = some res) :
    ∃ st, Steps code successors transf start st ∧ pick st.worklist = none ∧
      res = ⟨bot, st.aval⟩ := by
  refine PrimIter.iterate_prop (step code successors transf)
    (fun st => Steps code successors transf start st)
    (fun res => ∃ st, Steps code successors transf start st ∧ pick st.worklist = none ∧
      res = ⟨bot, st.aval⟩) ?_ start res h (.base _)
  intro a ha
  split
  · next b E =>
    refine ⟨a, ha, ?_⟩
    unfold step at E
    split at E
    · next hp => cases E; exact ⟨hp, rfl⟩
    · split at E <;> cases E
  · next a' E => exact .right _ _ _ ha E

/-- `Dataflow_Solver.step_incr` -/
theorem step_incr (n : Positive) {s1 s2 : State L NS} (h : step code successors transf s1 = .inr s2) :
    Optge (s2.aval.get n) (s1.aval.get n) ∧ (s1.visited n → s2.visited n) := by
  unfold step at h
  split at h
  · cases h
  · next p rem _ =>
    split at h
    · cases h; exact ⟨optge_refl _, id⟩
    · next instr _ =>
      cases h
      obtain ⟨_, _, A3, _, _, _, A7, _, _⟩ := propagateSuccList_charact
        (transf p (abstrValue p s1)) (successors instr) ⟨s1.aval, rem, s1.visited⟩
      exact ⟨A3 n, A7 n⟩

/-- `Dataflow_Solver.steps_incr` -/
theorem steps_incr (n : Positive) {s1 s2 : State L NS} (h : Steps code successors transf s1 s2) :
    Optge (s2.aval.get n) (s1.aval.get n) ∧ (s1.visited n → s2.visited n) := by
  induction h with
  | base => exact ⟨optge_refl _, id⟩
  | right _ _ _ hs ih =>
    obtain ⟨P, Q⟩ := step_incr code successors transf n hs
    exact ⟨optge_trans P ih.1, fun h => Q (ih.2 h)⟩

/-- `Dataflow_Solver.good_state` -/
structure GoodState (st : State L NS) : Prop where
  gs_stable : ∀ n, st.visited n →
    In n st.worklist ∨
    (∀ i s, code.get n = some i → s ∈ successors i →
      Optge (st.aval.get s) (some (transf n (abstrValue n st))))
  gs_defined : ∀ n v, st.aval.get n = some v → st.visited n

/-- `Dataflow_Solver.step_state_good` -/
theorem step_state_good (st : State L NS) (pc : Positive) (rem : NS) (instr : A)
    (hpick : pick st.worklist = some (pc, rem)) (hcode : code.get pc = some instr)
    (hgood : GoodState code successors transf st) :
    GoodState code successors transf
      (propagateSuccList ⟨st.aval, rem, st.visited⟩ (transf pc (abstrValue pc st))
        (successors instr)) := by
  obtain ⟨GOOD1, GOOD2⟩ := hgood
  have PICK2 := pick_some _ _ _ hpick
  obtain ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9⟩ :=
    propagateSuccList_charact (transf pc (abstrValue pc st)) (successors instr)
      ⟨st.aval, rem, st.visited⟩
  constructor
  · intro n hn
    rcases A8 n hn with h | h
    · exact .inl h
    · rcases A4 n with h' | h'
      · exact .inl h'
      · have habs : abstrValue n (propagateSuccList ⟨st.aval, rem, st.visited⟩
            (transf pc (abstrValue pc st)) (successors instr)) = abstrValue n st :=
          congrArg (fun o => Option.getD o bot) h'
        rw [habs]
        rcases GOOD1 n h with P | P
        · rcases (PICK2 n).mp P with P | P
          · subst P
            refine .inr fun i s hi hs => ?_
            rw [hcode] at hi; cases hi
            exact A1 s hs
          · exact .inl (A5 n P)
        · exact .inr fun i s hi hs => optge_trans (A3 s) (P i s hi hs)
  · intro n v hv
    cases hst : st.aval.get n with
    | some v' => exact A7 n (GOOD2 n v' hst)
    | none => exact A9 n hst (by rw [hv]; simp)

/-- `Dataflow_Solver.step_state_good_2` -/
theorem step_state_good_2 (st : State L NS) (pc : Positive) (rem : NS)
    (hgood : GoodState code successors transf st) (hpick : pick st.worklist = some (pc, rem))
    (hcode : code.get pc = none) :
    GoodState code successors transf ⟨st.aval, rem, st.visited⟩ := by
  obtain ⟨GOOD1, GOOD2⟩ := hgood
  have PICK2 := pick_some _ _ _ hpick
  constructor
  · intro n hn
    rcases GOOD1 n hn with P | P
    · rcases (PICK2 n).mp P with P | P
      · subst P; exact .inr fun i s hi _ => by rw [hcode] at hi; cases hi
      · exact .inl P
    · exact .inr P
  · exact GOOD2

/-- `Dataflow_Solver.steps_state_good` -/
theorem steps_state_good {st1 st2 : State L NS} (h : Steps code successors transf st1 st2)
    (hg : GoodState code successors transf st1) : GoodState code successors transf st2 := by
  induction h with
  | base => exact hg
  | right s2 s3 _ e ih =>
    unfold step at e
    split at e
    · cases e
    · next n rem hpick =>
      split at e
      · next hc => cases e; exact step_state_good_2 code successors transf _ _ _ ih hpick hc
      · next instr hc => cases e; exact step_state_good code successors transf _ _ _ _ hpick hc ih

/-- `Dataflow_Solver.start_state_good` -/
theorem startState_good (enode : Positive) (eval : L) :
    GoodState code successors transf (startState (NS := NS) enode eval) := by
  constructor
  · intro n hn
    exact .inl ((add_spec _ _ _).mpr (.inl hn.symm))
  · intro n v hv
    simp only [startState, PTree.gsspec, PTree.gempty] at hv
    split at hv
    · assumption
    · cases hv

/-- `Dataflow_Solver.start_state_nodeset_good` -/
theorem startStateNodeset_good (enodes : NS) :
    GoodState code successors transf (startStateNodeset (L := L) enodes) := by
  constructor
  · intro n hn; exact .inl hn
  · intro n v hv; simp [startStateNodeset] at hv

/-- `Dataflow_Solver.start_state_allnodes_good` -/
theorem startStateAllnodes_good :
    GoodState code successors transf (startStateAllnodes (L := L) (NS := NS) code) := by
  constructor
  · intro n ⟨instr, hc⟩; exact .inl (allNodes_spec code n instr hc)
  · intro n v hv; simp [startStateAllnodes] at hv

/-- `Dataflow_Solver.reachable_visited` -/
theorem reachable_visited (st : State L NS) (hg : GoodState code successors transf st)
    (hpick : pick st.worklist = none) {p q : Positive} (hr : Reachable code successors p q)
    (hp : st.visited p) : st.visited q := by
  obtain ⟨GOOD1, GOOD2⟩ := hg
  induction hr with
  | refl => exact hp
  | left n1 n2 n3 i hc hs _ ih =>
    apply ih
    rcases GOOD1 n1 hp with P | P
    · exact absurd P (pick_none _ _ hpick)
    · have := P i n2 hc hs
      cases h : st.aval.get n2 with
      | none => rw [h] at this; cases this
      | some v => exact GOOD2 n2 v h

/-- `Dataflow_Solver.fixpoint_solution` -/
theorem fixpoint_solution (ep : Positive) (ev : L) (res : PMap L) (n : Positive) (instr : A)
    (s : Positive) (hfix : fixpoint (NS := NS) code successors transf ep ev = some res)
    (hcode : code.get n = some instr) (hs : s ∈ successors instr)
    (hbot : ∀ n, eq (transf n bot) bot) :
    ge (res.get s) (transf n (res.get n)) := by
  obtain ⟨st, STEPS, PICK, RES⟩ := fixpointFrom_charact code successors transf _ _ hfix
  obtain ⟨GOOD1, GOOD2⟩ := steps_state_good code successors transf STEPS
    (startState_good code successors transf ep ev)
  subst RES
  simp only [PMap.get]
  cases STN : st.aval.get n with
  | some v =>
    rcases GOOD1 n (GOOD2 n v STN) with P | P
    · exact absurd P (pick_none _ _ PICK)
    · have := P instr s hcode hs
      unfold abstrValue at this
      rw [STN] at this
      obtain ⟨l, hl, h⟩ := optge_some_inv this
      simpa [hl] using h
  | none =>
    exact ge_trans (ge_bot _) (ge_refl (eq_sym (hbot n)))

/-- `Dataflow_Solver.fixpoint_entry` -/
theorem fixpoint_entry (ep : Positive) (ev : L) (res : PMap L)
    (hfix : fixpoint (NS := NS) code successors transf ep ev = some res) :
    ge (res.get ep) ev := by
  obtain ⟨st, STEPS, _, RES⟩ := fixpointFrom_charact code successors transf _ _ hfix
  obtain ⟨P, _⟩ := steps_incr code successors transf ep STEPS
  simp only [startState, PTree.gss] at P
  subst RES
  simp only [PMap.get]
  obtain ⟨l, hl, h⟩ := optge_some_inv P
  simpa [hl] using h

/-- `Dataflow_Solver.fixpoint_allnodes_solution` -/
theorem fixpointAllnodes_solution (res : PMap L) (n : Positive) (instr : A) (s : Positive)
    (hfix : fixpointAllnodes (NS := NS) code successors transf = some res)
    (hcode : code.get n = some instr) (hs : s ∈ successors instr) :
    ge (res.get s) (transf n (res.get n)) := by
  obtain ⟨st, STEPS, PICK, RES⟩ := fixpointFrom_charact code successors transf _ _ hfix
  obtain ⟨GOOD1, _⟩ := steps_state_good code successors transf STEPS
    (startStateAllnodes_good code successors transf)
  obtain ⟨_, V⟩ := steps_incr code successors transf n STEPS
  rcases GOOD1 n (V ⟨instr, hcode⟩) with P | P
  · exact absurd P (pick_none _ _ PICK)
  · have := P instr s hcode hs
    subst RES
    obtain ⟨l, hl, h⟩ := optge_some_inv this
    simpa [PMap.get, abstrValue, hl] using h

/-- `Dataflow_Solver.fixpoint_nodeset_solution` -/
theorem fixpointNodeset_solution (enodes : NS) (res : PMap L) (e n : Positive) (instr : A)
    (s : Positive) (hfix : fixpointNodeset code successors transf enodes = some res)
    (he : In e enodes) (hr : Reachable code successors e n)
    (hcode : code.get n = some instr) (hs : s ∈ successors instr) :
    ge (res.get s) (transf n (res.get n)) := by
  obtain ⟨st, STEPS, PICK, RES⟩ := fixpointFrom_charact code successors transf _ _ hfix
  have GOOD := steps_state_good code successors transf STEPS
    (startStateNodeset_good code successors transf enodes)
  obtain ⟨_, V⟩ := steps_incr code successors transf e STEPS
  have hv := reachable_visited code successors transf st GOOD PICK hr (V he)
  rcases GOOD.gs_stable n hv with P | P
  · exact absurd P (pick_none _ _ PICK)
  · have := P instr s hcode hs
    subst RES
    obtain ⟨l, hl, h⟩ := optge_some_inv this
    simpa [PMap.get, abstrValue, hl] using h

/-- `Dataflow_Solver.fixpoint_invariant` -/
theorem fixpoint_invariant (ep : Positive) (ev : L) (P : L → Prop) (P_bot : P bot)
    (P_lub : ∀ x y, P x → P y → P (lub x y))
    (P_transf : ∀ pc instr x, code.get pc = some instr → P x → P (transf pc x))
    (P_entrypoint : P ev) (res : PMap L) (pc : Positive)
    (hfix : fixpoint (NS := NS) code successors transf ep ev = some res) : P (res.get pc) := by
  let inv := fun (st : State L NS) => ∀ x, P (abstrValue x st)
  have H0 : inv (startState ep ev) := by
    intro x
    simp only [abstrValue, startState, PTree.gsspec, PTree.gempty]
    split <;> simpa
  have H1 : ∀ st v n, inv st → P v → inv (propagateSucc st v n) := by
    intro st v n hst hv x
    unfold propagateSucc
    cases E : st.aval.get n with
    | none =>
      simp only [abstrValue, PTree.gsspec]
      split
      · simpa
      · exact hst x
    | some oldl =>
      simp only
      split
      · exact hst x
      · simp only [abstrValue, PTree.gsspec]
        split
        · have := hst n
          simp only [abstrValue, E, Option.getD_some] at this
          simpa using P_lub _ _ this hv
        · exact hst x
  have H2 : ∀ l st v, inv st → P v → inv (propagateSuccList st v l) := by
    intro l
    induction l with
    | nil => intro st v h _; exact h
    | cons a l ih => intro st v h hv; exact ih _ _ (H1 _ _ _ h hv) hv
  have H3 : ∀ st1 st2, Steps code successors transf st1 st2 → inv st1 → inv st2 := by
    intro st1 st2 h
    induction h with
    | base => exact id
    | right s2 s3 _ e ih =>
      intro h1
      unfold step at e
      split at e
      · cases e
      · split at e
        · cases e; exact ih h1
        · next instr hc =>
          cases e
          exact H2 _ _ _ (ih h1) (P_transf _ _ _ hc (ih h1 _))
  obtain ⟨st, STEPS, _, RES⟩ := fixpointFrom_charact code successors transf _ _ hfix
  subst RES
  exact H3 _ _ STEPS H0 pc

end Kildall

/-! ## Predecessors -/

/-- `Kildall.successors_list` -/
def successorsList (successors : PTree (List Positive)) (pc : Positive) : List Positive :=
  (successors.get pc).getD []

section Predecessor
variable {A : Type} (code : PTree A) (successors : A → List Positive)

/-- `Kildall.add_successors` -/
def addSuccessors (pred : PTree (List Positive)) (frm : Positive) :
    List Positive → PTree (List Positive)
  | [] => pred
  | to :: rem => addSuccessors (pred.set to (frm :: successorsList pred to)) frm rem

/-- `Kildall.add_successors_correct` -/
theorem addSuccessors_correct :
    ∀ (tolist : List Positive) (frm : Positive) (pred : PTree (List Positive)) (n s : Positive),
      (n ∈ successorsList pred s ∨ (n = frm ∧ s ∈ tolist)) →
      n ∈ successorsList (addSuccessors pred frm tolist) s
  | [], _, _, _, _, h => by simpa [addSuccessors] using h
  | a :: tolist, frm, pred, n, s, h => by
    apply addSuccessors_correct tolist
    unfold successorsList at *
    rw [PTree.gsspec]
    split
    · next hs =>
      subst hs
      simp only [Option.getD_some, List.mem_cons]
      rcases h with h | ⟨rfl, _⟩
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
    · next hs =>
      rcases h with h | ⟨rfl, h⟩
      · exact .inl h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h hs
        · exact .inr ⟨rfl, h⟩

/-- `Kildall.make_predecessors` -/
def makePredecessors : PTree (List Positive) :=
  PTree.fold (fun pred pc instr => addSuccessors pred pc (successors instr)) code PTree.empty

theorem makePredecessors_foldl (n s : Positive) (instr : A) :
    ∀ (L : List (Positive × A)) (pred : PTree (List Positive)),
      (n ∈ successorsList pred s ∨ ((n, instr) ∈ L ∧ s ∈ successors instr)) →
      n ∈ successorsList (L.foldl (fun a p => addSuccessors a p.1 (successors p.2)) pred) s
  | [], _, h => by simpa using h
  | (k, i) :: L, pred, h => by
    apply makePredecessors_foldl n s instr L
    rcases h with h | ⟨hm, hs⟩
    · exact .inl (addSuccessors_correct _ _ _ _ _ (.inl h))
    · rcases List.mem_cons.mp hm with he | hm
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact .inl (addSuccessors_correct _ _ _ _ _ (.inr ⟨rfl, hs⟩))
      · exact .inr ⟨hm, hs⟩

/-- `Kildall.make_predecessors_correct_1` -/
theorem makePredecessors_correct_1 (n : Positive) (instr : A) (s : Positive)
    (hc : code.get n = some instr) (hs : s ∈ successors instr) :
    n ∈ successorsList (makePredecessors code successors) s :=
  makePredecessors_foldl successors n s instr _ _
    (.inr ⟨PTree.elements_correct code n instr hc, hs⟩)

/-- `Kildall.make_predecessors_correct_2` -/
theorem makePredecessors_correct_2 (n : Positive) (instr : A) (s : Positive)
    (hc : code.get n = some instr) (hs : s ∈ successors instr) :
    ∃ l, (makePredecessors code successors).get s = some l ∧ n ∈ l := by
  have := makePredecessors_correct_1 code successors n instr s hc hs
  unfold successorsList at this
  cases h : (makePredecessors code successors).get s with
  | none => rw [h] at this; simp at this
  | some l => rw [h] at this; exact ⟨l, rfl, this⟩

/-- `Kildall.reachable_predecessors` -/
theorem reachable_predecessors {p q : Positive} (h : Reachable code successors p q) :
    Reachable (makePredecessors code successors) (fun l => l) q p := by
  induction h with
  | refl => exact .refl _
  | left n1 n2 n3 i hc hs _ ih =>
    obtain ⟨l, hl, hn⟩ := makePredecessors_correct_2 code successors n1 i n2 hc hs
    exact reachable_right ih hl hn

end Predecessor

/-! ## The backward solver `Backward_Dataflow_Solver` -/

namespace Backward

section
variable {L NS : Type} [Semilattice L] [NodeSet NS]
variable {A : Type} (code : PTree A) (successors : A → List Positive) (transf : Positive → L → L)

open Semilattice NodeSet

/-- `Backward_Dataflow_Solver.sequential_node` -/
def sequentialNode (pc : Positive) (instr : A) : Bool :=
  (successors instr).any (fun s => match code.get s with
    | none => false
    | some _ => decide (s.toNat < pc.toNat))

/-- `Backward_Dataflow_Solver.exit_points` -/
def exitPoints : NS :=
  PTree.fold (fun ep pc instr => if sequentialNode code successors pc instr then ep else add pc ep)
    code empty

/-- `Backward_Dataflow_Solver.fixpoint` -/
def fixpoint : Option (PMap L) :=
  fixpointNodeset (makePredecessors code successors) (fun l => l) transf
    (exitPoints (NS := NS) code successors)

theorem exitPoints_foldl (n : Positive) (i : A) :
    ∀ (L : List (Positive × A)) (ep : NS),
      (In n ep ∨ ((n, i) ∈ L ∧ sequentialNode code successors n i = false)) →
      In n (L.foldl (fun ep p => if sequentialNode code successors p.1 p.2 then ep else add p.1 ep) ep)
  | [], _, h => by
    rcases h with h | ⟨h, _⟩
    · exact h
    · simp at h
  | (k, j) :: L, ep, h => by
    apply exitPoints_foldl n i L
    simp only
    rcases h with h | ⟨hm, hs⟩
    · left; split
      · exact h
      · exact (add_spec _ _ _).mpr (.inr h)
    · rcases List.mem_cons.mp hm with he | hm
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        left; rw [hs]; exact (add_spec _ _ _).mpr (.inl rfl)
      · exact .inr ⟨hm, hs⟩

/-- One direction of `Backward_Dataflow_Solver.exit_points_charact`. -/
theorem exitPoints_charact {n : Positive} {i : A} (hc : code.get n = some i)
    (hs : sequentialNode code successors n i = false) :
    In n (exitPoints (NS := NS) code successors) :=
  exitPoints_foldl code successors n i _ _ (.inr ⟨PTree.elements_correct code n i hc, hs⟩)

/-- `Backward_Dataflow_Solver.reachable_exit_points` -/
theorem reachable_exitPoints (pc : Positive) (i : A) (hc : code.get pc = some i) :
    ∃ x, In x (exitPoints (NS := NS) code successors) ∧ Reachable code successors pc x := by
  induction h : pc.toNat using Nat.strongRecOn generalizing pc i with
  | _ k ih =>
    cases hsn : sequentialNode code successors pc i with
    | true =>
      unfold sequentialNode at hsn
      obtain ⟨s, hs, hq⟩ := List.any_eq_true.mp hsn
      cases hcs : code.get s with
      | none => rw [hcs] at hq; cases hq
      | some i' =>
        rw [hcs] at hq
        have hlt : s.toNat < pc.toNat := of_decide_eq_true hq
        obtain ⟨x, hx, hr⟩ := ih s.toNat (h ▸ hlt) s i' hcs rfl
        exact ⟨x, hx, .left _ _ _ _ hc hs hr⟩
    | false => exact ⟨pc, exitPoints_charact code successors hc hsn, .refl _⟩

/-- `Backward_Dataflow_Solver.reachable_exit_points_predecessor` -/
theorem reachable_exitPoints_predecessor (pc : Positive) (i : A) (hc : code.get pc = some i) :
    ∃ x, In x (exitPoints (NS := NS) code successors) ∧
      Reachable (makePredecessors code successors) (fun l => l) x pc := by
  obtain ⟨x, hx, hr⟩ := reachable_exitPoints (NS := NS) code successors pc i hc
  exact ⟨x, hx, reachable_predecessors code successors hr⟩

/-- `Backward_Dataflow_Solver.fixpoint_solution` -/
theorem fixpoint_solution (res : PMap L) (n : Positive) (instr : A) (s : Positive)
    (hfix : fixpoint (NS := NS) code successors transf = some res)
    (hc : code.get n = some instr) (hs : s ∈ successors instr)
    (hbot : ∀ n a, code.get n = none → eq (transf n a) bot) :
    ge (res.get n) (transf s (res.get s)) := by
  obtain ⟨l, hl, hn⟩ := makePredecessors_correct_2 code successors n instr s hc hs
  cases hcs : code.get s with
  | some instr' =>
    obtain ⟨ep, U, V⟩ := reachable_exitPoints_predecessor (NS := NS) code successors s instr' hcs
    exact Kildall.fixpointNodeset_solution _ _ transf _ res ep s l n hfix U V hl hn
  | none => exact ge_trans (ge_bot _) (ge_refl (eq_sym (hbot s _ hcs)))

/-- `Backward_Dataflow_Solver.fixpoint_allnodes` -/
def fixpointAllnodes : Option (PMap L) :=
  Kildall.fixpointAllnodes (NS := NS) (makePredecessors code successors) (fun l => l) transf

/-- `Backward_Dataflow_Solver.fixpoint_allnodes_solution` -/
theorem fixpointAllnodes_solution (res : PMap L) (n : Positive) (instr : A) (s : Positive)
    (hfix : fixpointAllnodes (NS := NS) code successors transf = some res)
    (hc : code.get n = some instr) (hs : s ∈ successors instr) :
    ge (res.get n) (transf s (res.get s)) := by
  obtain ⟨l, hl, hn⟩ := makePredecessors_correct_2 code successors n instr s hc hs
  exact Kildall.fixpointAllnodes_solution _ _ transf res s l n hfix hl hn

end
end Backward

end Kildall
end CC
