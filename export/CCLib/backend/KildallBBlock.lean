/-
  The "extended basic block" dataflow solver — port of the module
  `BBlock_solver` of `backend/Kildall.v` (definitions).

  Ported: `bbmap`, `result`, `state`, `propagate_successors`, `step`,
  `is_basic_block_head`, `basic_block_map`, `basic_block_list`,
  `fixpoint`, `predecessors`, `state_invariant`.
  Correctness proofs: `predecessors_correct`, `multiple_predecessors`,
  `no_self_loop`, `propagate_successors_charact1/2`,
  `propagate_successors_invariant(_2)`, `initial_state_invariant`,
  `analyze_invariant`, `fixpoint_solution`, `fixpoint_entry`,
  `propagate_successors_P`, `fixpoint_invariant`.

  The solver needs no lattice, only a top element: it is parameterized by
  `top : L` instead of the module type `ORDERED_TYPE_WITH_TOP`.  The
  correctness theorems take the order `ge` of `ORDERED_TYPE_WITH_TOP` and its
  two laws `top_ge`, `refl_ge` as arguments.
-/
import CCLib.backend.Kildall

namespace CC
namespace Kildall
namespace BBlock

section Solver
variable {L A : Type} (top : L) (code : PTree A) (successors : A → List Positive)
  (transf : Positive → L → L) (entrypoint : Positive)

/-- `BBlock_solver.bbmap` -/
abbrev Bbmap := Positive → Bool

/-- `BBlock_solver.result` -/
abbrev Result (L : Type) := PMap L

/-- `BBlock_solver.state` -/
structure State (L : Type) where
  aval : Result L
  worklist : List Positive

/-- `BBlock_solver.propagate_successors` -/
def propagateSuccessors (bb : Bbmap) : List Positive → L → State L → State L
  | [], _, st => st
  | s1 :: sl, l, st =>
      if bb s1 then propagateSuccessors bb sl l st
      else propagateSuccessors bb sl l { aval := st.aval.set s1 l, worklist := s1 :: st.worklist }

/-- `BBlock_solver.step` -/
def step (bb : Bbmap) (st : State L) : Result L ⊕ State L :=
  match st.worklist with
  | [] => .inl st.aval
  | pc :: rem =>
      match code.get pc with
      | none => .inr { aval := st.aval, worklist := rem }
      | some instr =>
          .inr (propagateSuccessors bb (successors instr) (transf pc (st.aval.get pc))
            { aval := st.aval, worklist := rem })

/-- `BBlock_solver.is_basic_block_head`: program points with more than one
    predecessor (or the entry point). -/
def isBasicBlockHead (preds : PTree (List Positive)) (pc : Positive) : Bool :=
  if pc = entrypoint then true
  else
    match successorsList preds pc with
    | [] => false
    | [s] => decide (s = pc)
    | _ :: _ :: _ => true

/-- `BBlock_solver.basic_block_map` -/
def basicBlockMap : Bbmap :=
  isBasicBlockHead entrypoint (makePredecessors code successors)

/-- `BBlock_solver.basic_block_list` -/
def basicBlockList (bb : Bbmap) : List Positive :=
  PTree.fold (fun l pc _ => if bb pc then pc :: l else l) code []

/-- `BBlock_solver.fixpoint` -/
def fixpoint : Option (Result L) :=
  let bb := basicBlockMap code successors entrypoint
  PrimIter.iterate (step code successors transf bb)
    { aval := PMap.init top, worklist := basicBlockList code bb }

/-- `BBlock_solver.predecessors` -/
def predecessors : PTree (List Positive) := makePredecessors code successors

/-- `BBlock_solver.state_invariant`, for a given order `ge` on `L`. -/
def StateInvariant (ge : L → L → Prop) (st : State L) : Prop :=
  (∀ n, basicBlockMap code successors entrypoint n = true → st.aval.get n = top) ∧
  (∀ n, n ∈ st.worklist ∨
    (∀ instr s, code.get n = some instr → s ∈ successors instr →
      ge (st.aval.get s) (transf n (st.aval.get n))))

end Solver

/-! ## Correctness -/

section Correctness
variable {L A : Type} (top : L) (code : PTree A) (successors : A → List Positive)
  (transf : Positive → L → L) (entrypoint : Positive)

/-- `BBlock_solver.predecessors_correct` -/
theorem predecessors_correct {n : Positive} {instr : A} {s : Positive}
    (hc : code.get n = some instr) (hs : s ∈ successors instr) :
    n ∈ successorsList (predecessors code successors) s :=
  makePredecessors_correct_1 code successors n instr s hc hs

/-- `BBlock_solver.multiple_predecessors` -/
theorem multiple_predecessors {s n1 n2 : Positive} {instr1 instr2 : A}
    (h1 : code.get n1 = some instr1) (hs1 : s ∈ successors instr1)
    (h2 : code.get n2 = some instr2) (hs2 : s ∈ successors instr2) (hne : n1 ≠ n2) :
    basicBlockMap code successors entrypoint s = true := by
  have A1 := predecessors_correct code successors h1 hs1
  have A2 := predecessors_correct code successors h2 hs2
  unfold basicBlockMap isBasicBlockHead
  split
  · rfl
  · unfold predecessors at A1 A2
    generalize successorsList (makePredecessors code successors) s = l at A1 A2 ⊢
    match l, A1, A2 with
    | [], A1, _ => cases A1
    | [x], A1, A2 =>
      simp only [List.mem_singleton] at A1 A2
      exact absurd (A1.trans A2.symm) hne
    | _ :: _ :: _, _, _ => rfl

/-- `BBlock_solver.no_self_loop` -/
theorem no_self_loop {n : Positive} {instr : A} (hc : code.get n = some instr)
    (hs : n ∈ successors instr) : basicBlockMap code successors entrypoint n = true := by
  have A1 := predecessors_correct code successors hc hs
  unfold basicBlockMap isBasicBlockHead
  split
  · rfl
  · unfold predecessors at A1
    generalize successorsList (makePredecessors code successors) n = l at A1 ⊢
    match l, A1 with
    | [], A1 => cases A1
    | [x], A1 =>
      simp only [List.mem_singleton] at A1
      subst A1; simp
    | _ :: _ :: _, _ => rfl

/-- `BBlock_solver.propagate_successors_charact1` -/
theorem propagateSuccessors_charact1 (bb : Bbmap) :
    ∀ (succs : List Positive) (l : L) (st : State L),
      ∀ x, x ∈ st.worklist → x ∈ (propagateSuccessors bb succs l st).worklist
  | [], _, _, _, h => h
  | a :: succs, l, st, x, h => by
    simp only [propagateSuccessors]
    split
    · exact propagateSuccessors_charact1 bb succs l st x h
    · exact propagateSuccessors_charact1 bb succs l _ x (List.mem_cons_of_mem _ h)

/-- `BBlock_solver.propagate_successors_charact2` -/
theorem propagateSuccessors_charact2 (bb : Bbmap) :
    ∀ (succs : List Positive) (l : L) (st : State L) (n : Positive),
      (n ∈ succs → bb n = false →
        n ∈ (propagateSuccessors bb succs l st).worklist ∧
        (propagateSuccessors bb succs l st).aval.get n = l) ∧
      (n ∉ succs ∨ bb n = true →
        (propagateSuccessors bb succs l st).aval.get n = st.aval.get n)
  | [], _, _, _ => ⟨fun h => (nomatch h), fun _ => rfl⟩
  | a :: succs, l, st, n => by
    simp only [propagateSuccessors]
    split
    · rename_i hba
      obtain ⟨U, V⟩ := propagateSuccessors_charact2 bb succs l st n
      refine ⟨fun h hb => ?_, fun h => V ?_⟩
      · rcases List.mem_cons.mp h with h | h
        · subst h; rw [hba] at hb; cases hb
        · exact U h hb
      · rcases h with h | h
        · exact .inl fun h' => h (List.mem_cons_of_mem _ h')
        · exact .inr h
    · rename_i hba
      obtain ⟨U, V⟩ := propagateSuccessors_charact2 bb succs l
        { aval := st.aval.set a l, worklist := a :: st.worklist } n
      refine ⟨fun h hb => ?_, fun h => ?_⟩
      · by_cases hn : n = a
        · subst hn
          refine ⟨propagateSuccessors_charact1 bb _ _ _ _ (List.mem_cons_self ..), ?_⟩
          by_cases hin : n ∈ succs
          · exact (U hin hb).2
          · rw [V (.inl hin)]; exact PMap.gss _ _ _
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h hn
          · exact U h hb
      · rw [V ?_]
        · refine PMap.gso _ _ _ _ fun e => ?_
          subst e
          rcases h with h | h
          · exact h (List.mem_cons_self ..)
          · exact absurd h hba
        · rcases h with h | h
          · exact .inl fun h' => h (List.mem_cons_of_mem _ h')
          · exact .inr h

variable (ge : L → L → Prop)

/-- `BBlock_solver.propagate_successors_invariant` -/
theorem propagateSuccessors_invariant {pc : Positive} {instr : A} {res : Result L}
    (top_ge : ∀ x, ge top x) (refl_ge : ∀ x, ge x x)
    {rem : List Positive} (hc : code.get pc = some instr)
    (hinv : StateInvariant top code successors transf entrypoint ge
      { aval := res, worklist := pc :: rem }) :
    StateInvariant top code successors transf entrypoint ge
      (propagateSuccessors (basicBlockMap code successors entrypoint) (successors instr)
        (transf pc (res.get pc)) { aval := res, worklist := rem }) := by
  obtain ⟨INV1, INV2⟩ := hinv
  simp only at INV1 INV2
  have U := propagateSuccessors_charact2 (basicBlockMap code successors entrypoint)
    (successors instr) (transf pc (res.get pc)) { aval := res, worklist := rem }
  have V := propagateSuccessors_charact1 (basicBlockMap code successors entrypoint)
    (successors instr) (transf pc (res.get pc)) { aval := res, worklist := rem }
  generalize propagateSuccessors (basicBlockMap code successors entrypoint) (successors instr)
    (transf pc (res.get pc)) { aval := res, worklist := rem } = st1 at U V ⊢
  simp only at U V
  refine ⟨fun n hn => ?_, fun n => ?_⟩
  · rw [(U n).2 (.inr hn)]; exact INV1 n hn
  · by_cases hpn : pc = n
    · subst hpn
      refine .inr fun instr0 s hc0 hs => ?_
      rw [hc] at hc0; cases hc0
      have E : st1.aval.get pc = res.get pc := by
        refine (U pc).2 ?_
        by_cases hin : pc ∈ successors instr
        · exact .inr (no_self_loop code successors entrypoint hc hin)
        · exact .inl hin
      rw [E]
      cases hbb : basicBlockMap code successors entrypoint s
      · rw [((U s).1 hs hbb).2]; exact refl_ge _
      · rw [(U s).2 (.inr hbb), INV1 s hbb]; exact top_ge _
    · rcases INV2 n with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hpn
        · exact .inl (V n h)
      · have INV3 : ∀ s instr', code.get n = some instr' → s ∈ successors instr' →
            st1.aval.get s = res.get s := by
          intro s instr' hc' hs'
          refine (U s).2 ?_
          by_cases hin : s ∈ successors instr
          · exact .inr (multiple_predecessors code successors entrypoint hc hin hc' hs' hpn)
          · exact .inl hin
        by_cases hin : n ∈ successors instr
        · cases hbb : basicBlockMap code successors entrypoint n
          · exact .inl ((U n).1 hin hbb).1
          · refine .inr fun instr' s hc' hs' => ?_
            rw [(U n).2 (.inr hbb), INV3 s instr' hc' hs']
            exact h instr' s hc' hs'
        · refine .inr fun instr' s hc' hs' => ?_
          rw [(U n).2 (.inl hin), INV3 s instr' hc' hs']
          exact h instr' s hc' hs'

/-- `BBlock_solver.propagate_successors_invariant_2` -/
theorem propagateSuccessors_invariant_2 {pc : Positive} {res : Result L} {rem : List Positive}
    (hc : code.get pc = none)
    (hinv : StateInvariant top code successors transf entrypoint ge
      { aval := res, worklist := pc :: rem }) :
    StateInvariant top code successors transf entrypoint ge { aval := res, worklist := rem } := by
  obtain ⟨INV1, INV2⟩ := hinv
  refine ⟨INV1, fun n => ?_⟩
  rcases INV2 n with h | h
  · rcases List.mem_cons.mp h with h | h
    · subst h; exact .inr fun instr s hc' _ => by rw [hc] at hc'; cases hc'
    · exact .inl h
  · exact .inr h

/-- `BBlock_solver.initial_state_invariant` -/
theorem initial_state_invariant (top_ge : ∀ x, ge top x) :
    StateInvariant top code successors transf entrypoint ge
      { aval := PMap.init top,
        worklist := basicBlockList code (basicBlockMap code successors entrypoint) } :=
  ⟨fun n _ => PMap.gi _ _, fun n => .inr fun _ s _ _ => by simp only [PMap.gi]; exact top_ge _⟩

/-- `BBlock_solver.analyze_invariant` -/
theorem analyze_invariant {res : Result L}
    (top_ge : ∀ x, ge top x) (refl_ge : ∀ x, ge x x)
    (h : fixpoint top code successors transf entrypoint = some res) :
    StateInvariant top code successors transf entrypoint ge { aval := res, worklist := [] } := by
  unfold fixpoint at h
  refine PrimIter.iterate_prop _ (StateInvariant top code successors transf entrypoint ge)
    (fun res => StateInvariant top code successors transf entrypoint ge
      { aval := res, worklist := [] }) ?_ _ _ h
    (initial_state_invariant top code successors transf entrypoint ge top_ge)
  intro st INV
  obtain ⟨stin, stwrk⟩ := st
  simp only [step]
  cases stwrk with
  | nil => exact INV
  | cons pc rem =>
    simp only
    cases hc : code.get pc with
    | none => exact propagateSuccessors_invariant_2 top code successors transf entrypoint ge hc INV
    | some instr =>
      exact propagateSuccessors_invariant top code successors transf entrypoint ge top_ge refl_ge
        hc INV

/-- `BBlock_solver.fixpoint_solution` -/
theorem fixpoint_solution {res : Result L} {n : Positive} {instr : A} {s : Positive}
    (top_ge : ∀ x, ge top x) (refl_ge : ∀ x, ge x x)
    (h : fixpoint top code successors transf entrypoint = some res)
    (hc : code.get n = some instr) (hs : s ∈ successors instr) :
    ge (res.get s) (transf n (res.get n)) := by
  obtain ⟨_, H⟩ := analyze_invariant top code successors transf entrypoint ge top_ge refl_ge h
  rcases H n with h | h
  · cases h
  · exact h instr s hc hs

/-- `BBlock_solver.fixpoint_entry` -/
theorem fixpoint_entry {res : Result L}
    (top_ge : ∀ x, ge top x) (refl_ge : ∀ x, ge x x)
    (h : fixpoint top code successors transf entrypoint = some res) :
    res.get entrypoint = top := by
  obtain ⟨H, _⟩ := analyze_invariant top code successors transf entrypoint ge top_ge refl_ge h
  exact H _ (by simp [basicBlockMap, isBasicBlockHead])

/-- `BBlock_solver.propagate_successors_P` -/
theorem propagateSuccessors_P (P : L → Prop) (bb : Bbmap) {l : L} (hl : P l) :
    ∀ (succs : List Positive) (st : State L), (∀ pc, P (st.aval.get pc)) →
      ∀ pc, P ((propagateSuccessors bb succs l st).aval.get pc)
  | [], _, h => h
  | a :: succs, st, h => by
    simp only [propagateSuccessors]
    split
    · exact propagateSuccessors_P P bb hl succs st h
    · refine propagateSuccessors_P P bb hl succs _ fun pc => ?_
      simp only [PMap.gsspec]
      split
      · exact hl
      · exact h pc

/-- `BBlock_solver.fixpoint_invariant` -/
theorem fixpoint_invariant (P : L → Prop) (Ptop : P top)
    (Ptransf : ∀ pc instr x, code.get pc = some instr → P x → P (transf pc x))
    {res : Result L} (pc : Positive)
    (h : fixpoint top code successors transf entrypoint = some res) : P (res.get pc) := by
  unfold fixpoint at h
  refine PrimIter.iterate_prop _ (fun st : State L => ∀ pc, P (st.aval.get pc))
    (fun res : Result L => P (res.get pc)) ?_ _ _ h (fun pc => by simp only [PMap.gi]; exact Ptop)
  intro st PS
  obtain ⟨aval, wl⟩ := st
  simp only [step]
  cases wl with
  | nil => exact PS pc
  | cons pc' rem =>
    simp only
    cases hc : code.get pc' with
    | none => exact PS
    | some instr => exact propagateSuccessors_P P _ (Ptransf _ _ _ hc (PS pc')) _ _ PS

end Correctness

end BBlock
end Kildall
end CC
