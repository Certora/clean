/-
  [RISC-V instance of `CCLib/backend/TunnelingBranch.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Properties of the branch map computed by tunneling — port of the
  `BRANCH_MAP_CORRECT` section of `backend/Tunnelingproof.v`.

  Main result: `Tunnelingproof.record_gotos_correct`: for every node `pc`
  of the function, either `branch_target pc = pc`, or `pc` starts with a
  branch (resp. a conditional branch whose two targets are tunneled to the
  same node) whose target(s) have the same branch target and a strictly
  smaller `count_gotos` measure.

  Differences from Rocq: the measures, which Rocq builds as the first
  component of a `sig` type, are obtained here as `∃ f, …` and
  `count_gotos` is defined with `Classical.choose`.  The induction over
  `PTree.fold` (Rocq's `PTree_Properties.fold_ind`) is an induction over the
  list `PTree.elements` of the code; the partially processed code is
  represented by the lookup function `restrict P` (the code restricted to
  the already processed nodes `P`).
-/
import CCLib.riscV.Tunneling

namespace CC
namespace RiscV
namespace Tunnelingproof

open LTL Tunneling UnionFind UnionFind.UF

/-- `measure_branch` -/
def measureBranch (u : UF) (pc s : Node) (f : Node → Nat) : Node → Nat := fun x =>
  if u.repr s = pc then f x else if u.repr x = pc then f x + f s + 1 else f x

/-- `measure_cond` -/
def measureCond (u : UF) (pc s1 s2 : Node) (f : Node → Nat) : Node → Nat := fun x =>
  if u.repr s1 = pc then f x
  else if u.repr x = pc then f x + max (f s1) (f s2) + 1 else f x

/-- The property of `branch_map_correct_1` at one node, whose code is `o`. -/
def Bm1 (u : UF) (f : Node → Nat) (pc : Node) : Option Bblock → Prop
  | some (.Lbranch s :: _) => u.repr pc = pc ∨ (u.repr pc = u.repr s ∧ f s < f pc)
  | _ => u.repr pc = pc

/-- `branch_map_correct_1`, for a code given by its lookup function. -/
def BMC1 (c : Node → Option Bblock) (u : UF) (f : Node → Nat) : Prop :=
  ∀ pc, Bm1 u f pc (c pc)

theorem bm1_of_repr {u : UF} {f : Node → Nat} {pc : Node} (h : u.repr pc = pc) :
    ∀ o, Bm1 u f pc o
  | none => h
  | some [] => h
  | some (i :: _) => by cases i <;> first | exact h | exact .inl h

theorem bm1_repr {u : UF} {f : Node → Nat} {pc : Node} {o : Option Bblock}
    (h : Bm1 u f pc o) (hb : ∀ s b, o ≠ some (.Lbranch s :: b)) : u.repr pc = pc := by
  match o, h with
  | none, h => exact h
  | some [], h => exact h
  | some (i :: b), h =>
      cases i
      case Lbranch s => exact absurd rfl (hb s b)
      all_goals exact h

/-- `record_branch_correct` -/
theorem record_branch_correct (c0 c : Node → Option Bblock) (u : UF) (f : Node → Nat)
    (pc : Node) (b : Bblock) (hc0 : ∀ p, p ≠ pc → c0 p = c p) (hc0pc : c0 pc = none)
    (hcpc : c pc = some b) (BMC : BMC1 c0 u f) :
    ∃ f', BMC1 c (recordBranch u pc b) f' := by
  have PC : u.repr pc = pc := by have := BMC pc; rw [hc0pc] at this; exact this
  have DFL : BMC1 c u f := by
    intro p
    by_cases e : p = pc
    · subst e; exact bm1_of_repr PC _
    · rw [← hc0 p e]; exact BMC p
  match b, hcpc with
  | [], _ => exact ⟨f, DFL⟩
  | i :: b', hcpc =>
    cases i
    case Lbranch s =>
      refine ⟨measureBranch u pc s f, fun p => ?_⟩
      simp only [recordBranch]
      by_cases e : p = pc
      · subst e
        rw [hcpc]
        simp only [Bm1]
        rw [repr_union_2 u p s p rfl, repr_union_3]
        by_cases hs : u.repr s = p
        · exact .inl hs
        · refine .inr ⟨rfl, ?_⟩
          simp only [measureBranch, hs, if_false, PC, if_true]
          omega
      · have A : u.repr p = p → (u.union pc s).repr p = p := fun h => by
          rw [repr_union_1 u pc s p (by rw [h, PC]; exact e)]; exact h
        have hb := BMC p
        rw [hc0 p e] at hb
        match hcp : c p, hb with
        | none, hb => exact A hb
        | some [], hb => exact A hb
        | some (i :: bb), hb =>
            cases i
            case Lbranch s0 =>
              simp only [Bm1] at hb ⊢
              rcases hb with hb | ⟨hb1, hb2⟩
              · exact .inl (A hb)
              · refine .inr ⟨sameclass_union_2 u pc s p s0 hb1, ?_⟩
                simp only [measureBranch]
                rw [← hb1]
                split
                · exact hb2
                · split <;> omega
            all_goals exact A hb
    all_goals exact ⟨f, DFL⟩

/-- The code `c` restricted to the nodes in `P`. -/
def restrict (c : LTL.Code) (P : List Node) : Node → Option Bblock := fun p =>
  if p ∈ P then c.get p else none

theorem recordBranches_foldl (c : LTL.Code) :
    ∀ (l : List (Node × Bblock)) (P : List Node) (acc : UF) (f : Node → Nat),
      (P ++ l.map Prod.fst).Nodup → (∀ q ∈ l, c.get q.1 = some q.2) →
      BMC1 (restrict c P) acc f →
      ∃ f', BMC1 (restrict c (P ++ l.map Prod.fst))
        (l.foldl (fun a p => recordBranch a p.1 p.2) acc) f'
  | [], P, acc, f, _, _, h => ⟨f, by simpa using h⟩
  | (pc, b) :: l, P, acc, f, hnd, hl, h => by
      have hpc : pc ∉ P := fun hm => by
        have := List.nodup_append.mp hnd
        exact this.2.2 pc hm pc (by simp) rfl
      obtain ⟨f1, h1⟩ := record_branch_correct (restrict c P) (restrict c (P ++ [pc])) acc f pc b
        (fun p hp => by simp [restrict, hp])
        (by simp [restrict, hpc])
        (by simp [restrict, hl (pc, b) (List.mem_cons_self ..)]) h
      have := recordBranches_foldl c l (P ++ [pc]) _ f1 (by simpa using hnd)
        (fun q hq => hl q (List.mem_cons_of_mem _ hq)) h1
      simpa [List.foldl_cons, List.append_assoc] using this

theorem restrict_elements (c : LTL.Code) (p : Node) :
    restrict c ((PTree.elements c).map Prod.fst) p = c.get p := by
  simp only [restrict]
  split
  · rfl
  · rename_i hn
    cases e : c.get p with
    | none => rfl
    | some v => exact absurd (List.mem_map_of_mem (f := Prod.fst)
        (PTree.elements_correct c p v e)) hn

/-- `record_branches_correct` -/
theorem record_branches_correct (fn : LTL.Function) :
    ∃ f, BMC1 fn.fn_code.get (recordBranches fn) f := by
  obtain ⟨f, hf⟩ := recordBranches_foldl fn.fn_code (PTree.elements fn.fn_code) [] UF.empty
    (fun _ => 0) (by simpa using PTree.elements_keys_norepet fn.fn_code)
    (fun q hq => PTree.elements_complete _ q.1 q.2 hq)
    (fun pc => by simp only [restrict, List.not_mem_nil, if_false]; exact repr_empty pc)
  refine ⟨f, fun pc => ?_⟩
  have := hf pc
  simp only [List.nil_append, restrict_elements] at this
  exact this

section BRANCH_MAP_CORRECT
variable (fn : LTL.Function)

/-- The property of `branch_map_correct_2` at one node. -/
def Bm2 (c : LTL.Code) (u : UF) (f : Node → Nat) (pc : Node) : Option Bblock → Prop
  | some (.Lbranch s :: _) => u.repr pc = pc ∨ (u.repr pc = u.repr s ∧ f s < f pc)
  | some (.Lcond _ _ s1 s2 :: _) =>
      u.repr pc = pc ∨ (c.get pc = none ∧ u.repr pc = u.repr s1 ∧ u.repr pc = u.repr s2 ∧
        f s1 < f pc ∧ f s2 < f pc)
  | _ => u.repr pc = pc

/-- `branch_map_correct_2` -/
def BMC2 (c : LTL.Code) (u : UF) (f : Node → Nat) : Prop :=
  ∀ pc, Bm2 c u f pc (fn.fn_code.get pc)

/-- The property of `branch_map_correct` at one node. -/
def Bm (u : UF) (f : Node → Nat) (pc : Node) : Option Bblock → Prop
  | some (.Lbranch s :: _) => u.repr pc = pc ∨ (u.repr pc = u.repr s ∧ f s < f pc)
  | some (.Lcond _ _ s1 s2 :: _) =>
      u.repr pc = pc ∨ (u.repr pc = u.repr s1 ∧ u.repr pc = u.repr s2 ∧
        f s1 < f pc ∧ f s2 < f pc)
  | _ => u.repr pc = pc

/-- `branch_map_correct` -/
def BMC (u : UF) (f : Node → Nat) : Prop := ∀ pc, Bm u f pc (fn.fn_code.get pc)

theorem bm2_of_bm1 {c : LTL.Code} {u : UF} {f : Node → Nat} {pc : Node} :
    ∀ {o : Option Bblock}, Bm1 u f pc o → Bm2 c u f pc o
  | none, h => h
  | some [], h => h
  | some (i :: _), h => by cases i <;> first | exact h | exact .inl h

theorem bm_of_bm2 {c : LTL.Code} {u : UF} {f : Node → Nat} {pc : Node} :
    ∀ {o : Option Bblock}, Bm2 c u f pc o → Bm u f pc o
  | none, h => h
  | some [], h => h
  | some (i :: _), h => by
      cases i
      case Lcond =>
        rcases h with h | ⟨_, h⟩
        · exact .inl h
        · exact .inr h
      all_goals exact h

/-- `record_cond_correct` -/
theorem record_cond_correct (c : LTL.Code) (u : UF) (changed : Bool) (f : Node → Nat)
    (pc : Node) (b : Bblock) (BMC : BMC2 fn c u f) (GET1 : fn.fn_code.get pc = some b)
    (GET2 : c.get pc ≠ none) :
    ∃ f', BMC2 fn (recordCond (c, u, changed) pc b).1 (recordCond (c, u, changed) pc b).2.1 f' := by
  match b, GET1 with
  | [], _ => exact ⟨f, BMC⟩
  | i :: b', GET1 =>
    cases i
    case Lcond cond args s1 s2 =>
      simp only [recordCond]
      split
      · rename_i e
        have PC : u.repr pc = pc := by
          have := BMC pc
          rw [GET1] at this
          rcases this with h | ⟨h, _⟩
          · exact h
          · exact absurd h GET2
        refine ⟨measureCond u pc s1 s2 f, fun p => ?_⟩
        simp only
        by_cases hp : p = pc
        · subst hp
          rw [GET1]
          simp only [Bm2]
          rw [repr_union_2 u p s1 p rfl]
          by_cases h1 : u.repr s1 = p
          · exact .inl h1
          · refine .inr ⟨PTree.grs _ _, (repr_union_3 u p s1).symm, ?_, ?_, ?_⟩
            · rw [repr_union_1 u p s1 s2 (by rw [← e, PC]; exact h1)]; exact e
            · simp only [measureCond, h1, if_false, PC, if_true]; omega
            · simp only [measureCond, h1, if_false, PC, if_true, ← e]; omega
        · have P : u.repr p = p → (u.union pc s1).repr p = p := fun h => by
            rw [repr_union_1 u pc s1 p (by rw [h, PC]; exact hp)]; exact h
          have hb := BMC p
          match hcp : fn.fn_code.get p, hb with
          | none, hb => exact P hb
          | some [], hb => exact P hb
          | some (j :: bb), hb =>
            cases j
            case Lbranch s0 =>
              simp only [Bm2] at hb ⊢
              rcases hb with hb | ⟨A, B⟩
              · exact .inl (P hb)
              · refine .inr ⟨sameclass_union_2 u pc s1 p s0 A, ?_⟩
                simp only [measureCond]
                rw [← A]
                split
                · exact B
                · split <;> omega
            case Lcond cond' args' s1' s2' =>
              simp only [Bm2] at hb ⊢
              rcases hb with hb | ⟨A, B, C, D, E⟩
              · exact .inl (P hb)
              · refine .inr ⟨by rw [PTree.gro _ _ _ (Ne.symm hp)]; exact A,
                  sameclass_union_2 u pc s1 p s1' B, sameclass_union_2 u pc s1 p s2' C, ?_, ?_⟩
                · simp only [measureCond]
                  rw [← B]
                  split
                  · exact D
                  · split <;> omega
                · simp only [measureCond]
                  rw [← C]
                  split
                  · exact E
                  · split <;> omega
            all_goals exact P hb
      · exact ⟨f, BMC⟩
    all_goals exact ⟨f, BMC⟩

/-- `code_compat` -/
def CodeCompat (c : LTL.Code) : Prop := ∀ pc b, c.get pc = some b → fn.fn_code.get pc = some b

theorem recordCond_fst (st : LTL.Code × UF × Bool) (pc : Node) (b : Bblock) :
    (recordCond st pc b).1 = st.1 ∨ (recordCond st pc b).1 = st.1.remove pc := by
  obtain ⟨c, u, ch⟩ := st
  simp only [recordCond]
  split
  · split
    · exact .inr rfl
    · exact .inl rfl
  · exact .inl rfl

theorem recordConds1_foldl (c0 : LTL.Code) :
    ∀ (l : List (Node × Bblock)) (P : List Node) (st : LTL.Code × UF × Bool),
      (P ++ l.map Prod.fst).Nodup → (∀ q ∈ l, c0.get q.1 = some q.2) →
      CodeCompat fn st.1 → (∀ p, p ∉ P → st.1.get p = c0.get p) →
      (∃ f, BMC2 fn st.1 st.2.1 f) →
      CodeCompat fn (l.foldl (fun a p => recordCond a p.1 p.2) st).1 ∧
        ∃ f, BMC2 fn (l.foldl (fun a p => recordCond a p.1 p.2) st).1
          (l.foldl (fun a p => recordCond a p.1 p.2) st).2.1 f
  | [], _, _, _, _, hc, _, hb => ⟨hc, hb⟩
  | (pc, b) :: l, P, ⟨c, u, ch⟩, hnd, hl, hc, hinv, ⟨f, hb⟩ => by
      have hpc : pc ∉ P := fun hm => by
        have := List.nodup_append.mp hnd
        exact this.2.2 pc hm pc (by simp) rfl
      have GET3 : c.get pc = some b := (hinv pc hpc).trans (hl (pc, b) (List.mem_cons_self ..))
      simp only [List.foldl_cons]
      apply recordConds1_foldl c0 l (P ++ [pc]) _ (by simpa using hnd)
        (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      · intro p b' hp
        rcases recordCond_fst (c, u, ch) pc b with e | e <;> rw [e] at hp
        · exact hc _ _ hp
        · rw [PTree.grspec] at hp
          split at hp
          · cases hp
          · exact hc _ _ hp
      · intro p hp
        have hne : p ≠ pc := fun h => hp (by simp [h])
        have hp' : p ∉ P := fun h => hp (by simp [h])
        rcases recordCond_fst (c, u, ch) pc b with e | e <;> rw [e]
        · exact hinv p hp'
        · rw [PTree.gro _ _ _ (Ne.symm hne)]; exact hinv p hp'
      · exact record_cond_correct fn c u ch f pc b hb (hc _ _ GET3) (by rw [GET3]; simp)

/-- `record_conds_1_correct` -/
theorem record_conds_1_correct (c : LTL.Code) (u : UF) (f : Node → Nat)
    (BMC0 : BMC2 fn c u f) (COMPAT0 : CodeCompat fn c) :
    CodeCompat fn (recordConds1 (c, u)).1 ∧
      ∃ f', BMC2 fn (recordConds1 (c, u)).1 (recordConds1 (c, u)).2.1 f' :=
  recordConds1_foldl fn c (PTree.elements c) [] (c, u, false)
    (by simpa using PTree.elements_keys_norepet c)
    (fun q hq => PTree.elements_complete _ q.1 q.2 hq) COMPAT0 (fun _ _ => rfl) ⟨f, BMC0⟩

/-- `record_conds_correct` -/
theorem record_conds_correct (cu : LTL.Code × UF) (h : ∃ f, BMC2 fn cu.1 cu.2 f)
    (hc : CodeCompat fn cu.1) : ∃ f, BMC fn (recordConds cu) f := by
  rw [recordConds]
  split
  rename_i c' u' changed hrc
  split
  · rename_i hch
    obtain ⟨f, hf⟩ := h
    have := record_conds_1_correct fn cu.1 cu.2 f hf hc
    rw [hrc] at this
    have hdec : PTree.cardinal c' < PTree.cardinal cu.1 :=
      recordConds1_decreases cu (cu' := (c', u')) (by rw [hrc, hch])
    exact record_conds_correct (c', u') this.2 this.1
  · obtain ⟨f, hf⟩ := h
    exact ⟨f, fun pc => bm_of_bm2 (hf pc)⟩
termination_by PTree.cardinal cu.1
decreasing_by all_goals (simp_wf; assumption)

/-- `record_gotos_correct_1` -/
theorem record_gotos_correct_1 : ∃ f, BMC fn (recordGotos fn) f := by
  obtain ⟨f, hf⟩ := record_branches_correct fn
  exact record_conds_correct fn (fn.fn_code, recordBranches fn)
    ⟨f, fun pc => bm2_of_bm1 (hf pc)⟩ (fun _ _ h => h)

/-- `branch_target` -/
def branchTarget (pc : Node) : Node := (recordGotos fn).repr pc

/-- `count_gotos` -/
noncomputable def countGotos : Node → Nat := Classical.choose (record_gotos_correct_1 fn)

/-- `record_gotos_correct`: for every node `pc`, either `branch_target pc = pc`,
    or `pc` starts with `Lbranch s` with `branch_target pc = branch_target s`
    and `count_gotos s < count_gotos pc`, or `pc` starts with
    `Lcond _ _ s1 s2` whose two targets have the branch target of `pc` and a
    smaller `count_gotos`. -/
theorem record_gotos_correct (pc : Node) :
    Bm (recordGotos fn) (countGotos fn) pc (fn.fn_code.get pc) :=
  Classical.choose_spec (record_gotos_correct_1 fn) pc

end BRANCH_MAP_CORRECT

end Tunnelingproof
end RiscV
end CC
