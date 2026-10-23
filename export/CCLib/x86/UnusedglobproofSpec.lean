/-
  [x86-64 instance of `CCLib/backend/UnusedglobproofSpec.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Elimination of unreferenced static definitions: relational specification
  and correctness of the analysis — port of `backend/Unusedglobproof.v`,
  part 1 (lines 1–445): `match_prog_1`, `ref_def`, `valid_used_set`,
  `match_prog`, the workset lemmas, `used_globals_sound`,
  `used_globals_incl`, `used_globals_valid`, the `filter_globdefs` lemmas and
  `transf_program_match`.

  Differences from Rocq: the identifier set `IS.t` is a list (see
  `Unusedglob.lean`), so `IS.In` is list membership.
-/
import CCLib.x86.Unusedglob
import CCLib.lib.MapsTheory
import CCLib.common.ASTTheory

namespace CC
namespace X86
namespace Unusedglob

open RTL

/-! ## Identifier sets -/

theorem IS.mem_iff {x : Ident} {s : IS} : IS.mem x s = true ↔ x ∈ s := by
  simp [IS.mem]

theorem IS.mem_false_iff {x : Ident} {s : IS} : IS.mem x s = false ↔ x ∉ s := by
  rw [← IS.mem_iff]; simp

theorem IS.mem_add {x y : Ident} {s : IS} : y ∈ IS.add x s ↔ y = x ∨ y ∈ s := by
  unfold IS.add
  split
  · next h =>
    rw [IS.mem_iff] at h
    constructor
    · exact .inr
    · rintro (rfl | h'); exact h; exact h'
  · simp

theorem IS.mem_remove {x y : Ident} {s : IS} : y ∈ IS.remove x s ↔ y ∈ s ∧ y ≠ x := by
  simp [IS.remove]

/-! ## Relational specification of the transformation -/

/-- `Unusedglobproof.match_prog_1` -/
structure MatchProg1 (u : IS) (p tp : RTL.Program) : Prop where
  main_eq : tp.prog_main = p.prog_main
  public_eq : tp.prog_public = p.prog_public
  defs : ∀ id, tp.defmap.get id = if IS.mem id u then p.defmap.get id else none
  unique : tp.defsNames.Nodup

/-- `Unusedglobproof.ref_function` -/
def RefFunction (f : RTL.Function) (id : Ident) : Prop :=
  ∃ pc i, f.fn_code.get pc = some i ∧ id ∈ refInstruction i

/-- `Unusedglobproof.ref_fundef` -/
def RefFundef : RTL.Fundef → Ident → Prop
  | .Internal f, id => RefFunction f id
  | .External _, _ => False

/-- `Unusedglobproof.ref_init` -/
def RefInit (il : List InitData) (id : Ident) : Prop :=
  ∃ ofs, InitData.Init_addrof id ofs ∈ il

/-- `Unusedglobproof.ref_def` -/
def RefDef : GlobDef RTL.Fundef Unit → Ident → Prop
  | .Gfun fd, id => RefFundef fd id
  | .Gvar gv, id => RefInit gv.gvar_init id

/-- `Unusedglobproof.valid_used_set` -/
structure ValidUsedSet (p : RTL.Program) (u : IS) : Prop where
  closed : ∀ id gd id', id ∈ u → p.defmap.get id = some gd → RefDef gd id' → id' ∈ u
  main : p.prog_main ∈ u
  publics : ∀ id, id ∈ p.prog_public → id ∈ u
  defined : ∀ id, id ∈ u → id ∈ p.defsNames ∨ id = p.prog_main

/-- `Unusedglobproof.match_prog` -/
def MatchProg (p tp : RTL.Program) : Prop :=
  ∃ u, ValidUsedSet p u ∧ MatchProg1 u p tp

/-! ## Monotonic evolution of the workset -/

/-- `Unusedglobproof.workset_incl` -/
structure WorksetIncl (w1 w2 : Workset) : Prop where
  seen : ∀ id, id ∈ w1.w_seen → id ∈ w2.w_seen
  todo : ∀ id, id ∈ w1.w_todo → id ∈ w2.w_todo
  track : ∀ id, id ∈ w2.w_seen → id ∈ w1.w_seen ∨ id ∈ w2.w_todo

theorem WorksetIncl.refl (w : Workset) : WorksetIncl w w :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => .inl h⟩

theorem WorksetIncl.trans {w1 w2 w3 : Workset} (h1 : WorksetIncl w1 w2) (h2 : WorksetIncl w2 w3) :
    WorksetIncl w1 w3 where
  seen id h := h2.seen id (h1.seen id h)
  todo id h := h2.todo id (h1.todo id h)
  track id h := by
    rcases h2.track id h with h' | h'
    · rcases h1.track id h' with h'' | h''
      · exact .inl h''
      · exact .inr (h2.todo id h'')
    · exact .inr h'

theorem add_workset_incl (id : Ident) (w : Workset) : WorksetIncl w (addWorkset id w) := by
  unfold addWorkset
  split
  · exact WorksetIncl.refl w
  · refine ⟨fun _ h => IS.mem_add.2 (.inr h), fun _ h => List.mem_cons_of_mem _ h, ?_⟩
    intro id0 h
    rcases IS.mem_add.1 h with rfl | h
    · exact .inr List.mem_cons_self
    · exact .inl h

theorem addlist_workset_incl : ∀ (l : List Ident) (w : Workset), WorksetIncl w (addlistWorkset l w)
  | [], w => WorksetIncl.refl w
  | id :: l, w => (add_workset_incl id w).trans (addlist_workset_incl l _)

theorem foldl_addRefInstruction_incl :
    ∀ (l : List (Node × Instruction)) (w : Workset),
      WorksetIncl w (l.foldl (fun a p => addRefInstruction a p.1 p.2) w)
  | [], w => WorksetIncl.refl w
  | p :: l, w => (addlist_workset_incl _ w).trans (foldl_addRefInstruction_incl l _)

theorem add_ref_function_incl (f : RTL.Function) (w : Workset) :
    WorksetIncl w (addRefFunction f w) :=
  foldl_addRefInstruction_incl _ w

theorem add_ref_globvar_incl (gv : GlobVar Unit) (w : Workset) :
    WorksetIncl w (addRefGlobvar gv w) := by
  unfold addRefGlobvar
  generalize gv.gvar_init = l
  induction l generalizing w with
  | nil => exact WorksetIncl.refl w
  | cons a l ih =>
    refine WorksetIncl.trans ?_ (ih _)
    unfold addRefInitData
    split
    · exact add_workset_incl _ _
    · exact WorksetIncl.refl w

theorem add_ref_definition_incl (pm : ProgMap) (id : Ident) (w : Workset) :
    WorksetIncl w (addRefDefinition pm id w) := by
  unfold addRefDefinition
  split
  · exact WorksetIncl.refl w
  · exact add_ref_function_incl _ _
  · exact WorksetIncl.refl w
  · exact add_ref_globvar_incl _ _

/-! ## Soundness of the functions that add identifiers to the workset -/

theorem seen_add_workset (id : Ident) (w : Workset) : id ∈ (addWorkset id w).w_seen := by
  unfold addWorkset
  split
  · next h => exact IS.mem_iff.1 h
  · exact IS.mem_add.2 (.inl rfl)

theorem seen_addlist_workset {id : Ident} :
    ∀ {l : List Ident} (w : Workset), id ∈ l → id ∈ (addlistWorkset l w).w_seen
  | a :: l, w, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (addlist_workset_incl l _).seen _ (seen_add_workset _ w)
    · show id ∈ (addlistWorkset l (addWorkset a w)).w_seen
      exact seen_addlist_workset _ h

theorem seen_foldl_addRefInstruction {id : Ident} {pc : Node} {i : Instruction}
    (hi : id ∈ refInstruction i) :
    ∀ (l : List (Node × Instruction)) (w : Workset), (pc, i) ∈ l →
      id ∈ (l.foldl (fun a p => addRefInstruction a p.1 p.2) w).w_seen
  | q :: l, w, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (foldl_addRefInstruction_incl l _).seen _ (seen_addlist_workset w hi)
    · exact seen_foldl_addRefInstruction hi l _ h

theorem seen_add_ref_function {id : Ident} {f : RTL.Function} (w : Workset)
    (h : RefFunction f id) : id ∈ (addRefFunction f w).w_seen := by
  obtain ⟨pc, i, A, B⟩ := h
  exact seen_foldl_addRefInstruction B _ w (PTree.elements_correct _ _ _ A)

theorem seen_add_ref_definition {pm : ProgMap} {id : Ident} {gd : GlobDef RTL.Fundef Unit}
    {id' : Ident} (w : Workset) (h : pm.get id = some gd) (hr : RefDef gd id') :
    id' ∈ (addRefDefinition pm id w).w_seen := by
  unfold addRefDefinition
  rw [h]
  match gd, hr with
  | .Gfun (.Internal f), hr => exact seen_add_ref_function w hr
  | .Gfun (.External _), hr => exact hr.elim
  | .Gvar gv, hr =>
    obtain ⟨ofs, hin⟩ := hr
    show id' ∈ (addRefGlobvar gv w).w_seen
    unfold addRefGlobvar
    have key : ∀ (l : List InitData) (w : Workset),
        id' ∈ w.w_seen ∨ InitData.Init_addrof id' ofs ∈ l → id' ∈ (l.foldl addRefInitData w).w_seen := by
      intro l
      induction l with
      | nil => intro w h; rcases h with h | h; exact h; simp at h
      | cons a l ih =>
        intro w h
        apply ih
        rcases h with h | h
        · left
          unfold addRefInitData
          split
          · exact (add_workset_incl _ _).seen _ h
          · exact h
        · rcases List.mem_cons.1 h with rfl | h
          · left; exact seen_add_workset _ _
          · exact .inr h
    exact key _ w (.inr hin)

theorem seen_main_initial_workset (p : RTL.Program) : p.prog_main ∈ (initialWorkset p).w_seen :=
  seen_add_workset _ _

theorem seen_public_initial_workset (p : RTL.Program) {id : Ident} (h : id ∈ p.prog_public) :
    id ∈ (initialWorkset p).w_seen := by
  unfold initialWorkset
  refine (add_workset_incl _ _).seen _ ?_
  have key : ∀ (l : List Ident) (w : Workset), id ∈ w.w_seen ∨ id ∈ l →
      id ∈ (l.foldl (fun w id => addWorkset id w) w).w_seen := by
    intro l
    induction l with
    | nil => intro w h; rcases h with h | h; exact h; simp at h
    | cons a l ih =>
      intro w h
      apply ih
      rcases h with h | h
      · exact .inl ((add_workset_incl _ _).seen _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl (seen_add_workset _ _)
        · exact .inr h
  exact key _ _ (.inr h)

theorem initial_workset_incl (p : RTL.Program) :
    WorksetIncl { w_seen := IS.empty, w_todo := [] } (initialWorkset p) := by
  unfold initialWorkset
  refine WorksetIncl.trans ?_ (add_workset_incl _ _)
  generalize ({ w_seen := IS.empty, w_todo := [] } : Workset) = w0
  generalize p.prog_public = l
  induction l generalizing w0 with
  | nil => exact WorksetIncl.refl _
  | cons a l ih => exact (add_workset_incl a w0).trans (ih _)

/-! ## Correctness of the dependency-graph traversal -/

section ANALYSIS
variable (p : RTL.Program)

/-- `Unusedglobproof.workset_invariant` -/
def WorksetInvariant (w : Workset) : Prop :=
  ∀ id gd id', id ∈ w.w_seen → id ∉ w.w_todo → p.defmap.get id = some gd → RefDef gd id' →
    id' ∈ w.w_seen

/-- `Unusedglobproof.used_set_closed` -/
def UsedSetClosed (u : IS) : Prop :=
  ∀ id gd id', id ∈ u → p.defmap.get id = some gd → RefDef gd id' → id' ∈ u

/-- `Unusedglobproof.iter_step_invariant`, first case. -/
theorem iter_step_invariant_inl {w : Workset} (h : WorksetInvariant p w) {u : IS}
    (hs : iterStep p.defmap w = .inl u) : UsedSetClosed p u := by
  unfold iterStep at hs
  cases htodo : w.w_todo with
  | nil =>
    rw [htodo] at hs; cases hs
    intro id gd id' h1 h2 h3
    exact h id gd id' h1 (by rw [htodo]; simp) h2 h3
  | cons id rem => rw [htodo] at hs; cases hs

/-- `Unusedglobproof.iter_step_invariant`, second case. -/
theorem iter_step_invariant_inr {w : Workset} (h : WorksetInvariant p w) {w1 : Workset}
    (hs : iterStep p.defmap w = .inr w1) : WorksetInvariant p w1 := by
  unfold iterStep at hs
  cases htodo : w.w_todo with
  | nil => rw [htodo] at hs; cases hs
  | cons id rem =>
    rw [htodo] at hs; cases hs
    intro id0 gd id' h1 h2 h3 h4
    have I := add_ref_definition_incl p.defmap id { w_seen := w.w_seen, w_todo := rem }
    by_cases e : id = id0
    · subst e; exact seen_add_ref_definition _ h3 h4
    · rcases I.track id0 h1 with A | A
      · refine I.seen _ (h id0 gd id' A ?_ h3 h4)
        rw [htodo]
        intro hm
        rcases List.mem_cons.1 hm with hm | hm
        · exact e hm.symm
        · exact h2 (I.todo _ hm)
      · exact absurd A h2

/-- `Unusedglobproof.used_globals_sound` -/
theorem used_globals_sound {u : IS} (h : usedGlobals p p.defmap = some u) : UsedSetClosed p u := by
  refine PrimIter.iterate_prop (iterStep p.defmap) (WorksetInvariant p) (UsedSetClosed p)
    ?_ _ u h ?_
  · intro w hw
    split
    · next u' hu => exact iter_step_invariant_inl p hw hu
    · next w' hw' => exact iter_step_invariant_inr p hw hw'
  · intro id gd id' h1 h2 _ _
    rcases (initial_workset_incl p).track id h1 with A | A
    · simp [IS.empty] at A
    · exact absurd A h2

/-- `Unusedglobproof.used_globals_incl` -/
theorem used_globals_incl {u : IS} (h : usedGlobals p p.defmap = some u) :
    ∀ id, id ∈ (initialWorkset p).w_seen → id ∈ u := by
  refine PrimIter.iterate_prop (iterStep p.defmap)
    (fun w => ∀ id, id ∈ (initialWorkset p).w_seen → id ∈ w.w_seen)
    (fun u => ∀ id, id ∈ (initialWorkset p).w_seen → id ∈ u) ?_ _ u h (fun _ h => h)
  intro a ha
  split
  · next u' hu =>
    unfold iterStep at hu
    cases htodo : a.w_todo with
    | nil => rw [htodo] at hu; cases hu; exact ha
    | cons id rem => rw [htodo] at hu; cases hu
  · next w' hw' =>
    unfold iterStep at hw'
    cases htodo : a.w_todo with
    | nil => rw [htodo] at hw'; cases hw'
    | cons id rem =>
      rw [htodo] at hw'; cases hw'
      exact fun x hx =>
        (add_ref_definition_incl p.defmap id { w_seen := a.w_seen, w_todo := rem }).seen x (ha x hx)

/-- `Unusedglobproof.used_globals_valid` -/
theorem used_globals_valid {u : IS} (h : usedGlobals p p.defmap = some u)
    (hdef : IS.forAll (globalDefined p p.defmap) u = true) : ValidUsedSet p u where
  closed := used_globals_sound p h
  main := used_globals_incl p h _ (seen_main_initial_workset p)
  publics id hid := used_globals_incl p h _ (seen_public_initial_workset p hid)
  defined id hid := by
    simp only [IS.forAll, List.all_eq_true] at hdef
    have := hdef id hid
    unfold globalDefined at this
    split at this
    · next g hg =>
      left
      exact List.mem_map.2 ⟨(id, g), ASTProgram.in_defmap hg, rfl⟩
    · right; simpa using this

end ANALYSIS

/-! ## Properties of the elimination of unused global definitions -/

/-- `Unusedglobproof.filter_globdefs_accu` -/
theorem filter_globdefs_accu :
    ∀ (defs accu1 accu2 : List (Ident × GlobDef RTL.Fundef Unit)) (u : IS),
      filterGlobdefs u (accu1 ++ accu2) defs = filterGlobdefs u accu1 defs ++ accu2
  | [], _, _, _ => rfl
  | (id, gd) :: defs, accu1, accu2, u => by
    simp only [filterGlobdefs]
    split
    · exact filter_globdefs_accu defs ((id, gd) :: accu1) accu2 _
    · exact filter_globdefs_accu defs accu1 accu2 u

/-- `Unusedglobproof.filter_globdefs_nil` -/
theorem filter_globdefs_nil (u : IS) (accu defs : List (Ident × GlobDef RTL.Fundef Unit)) :
    filterGlobdefs u accu defs = filterGlobdefs u [] defs ++ accu := by
  rw [← filter_globdefs_accu]; rfl

private abbrev addDef (m : ProgMap) (idg : Ident × GlobDef RTL.Fundef Unit) : ProgMap :=
  m.set idg.1 idg.2

/-- `Unusedglobproof.filter_globdefs_map_1` -/
theorem filter_globdefs_map_1 (id : Ident) :
    ∀ (l : List (Ident × GlobDef RTL.Fundef Unit)) (u : IS) (m1 : ProgMap),
      IS.mem id u = false → m1.get id = none →
      ((filterGlobdefs u [] l).foldl addDef m1).get id = none
  | [], _, _, _, h => h
  | (id1, gd1) :: l, u, m1, hu, hm => by
    simp only [filterGlobdefs]
    split
    · next hmem =>
      rw [filter_globdefs_nil, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, addDef]
      have hne : id1 ≠ id := by
        intro e; subst e; rw [hu] at hmem; cases hmem
      rw [PTree.gso _ _ _ _ hne]
      refine filter_globdefs_map_1 id l _ m1 ?_ hm
      rw [IS.mem_false_iff, IS.mem_remove]
      exact fun h => (IS.mem_false_iff.1 hu) h.1
    · exact filter_globdefs_map_1 id l u m1 hu hm

/-- `Unusedglobproof.filter_globdefs_map_2` -/
theorem filter_globdefs_map_2 (id : Ident) :
    ∀ (l : List (Ident × GlobDef RTL.Fundef Unit)) (u : IS) (m1 m2 : ProgMap),
      IS.mem id u = true → m1.get id = m2.get id →
      ((filterGlobdefs u [] l).foldl addDef m1).get id = (l.reverse.foldl addDef m2).get id
  | [], _, _, _, _, h => h
  | (id1, gd1) :: l, u, m1, m2, hu, hm => by
    rw [List.reverse_cons, List.foldl_append]
    simp only [filterGlobdefs, List.foldl_cons, List.foldl_nil]
    split
    · next hmem =>
      rw [filter_globdefs_nil, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, addDef]
      rw [PTree.gsspec, PTree.gsspec]
      split
      · rfl
      · next hne =>
        refine filter_globdefs_map_2 id l _ m1 m2 ?_ hm
        rw [IS.mem_iff, IS.mem_remove]
        exact ⟨IS.mem_iff.1 hu, hne⟩
    · next hmem =>
      simp only [addDef]
      have hne : id1 ≠ id := by
        intro e; subst e; exact hmem hu
      rw [PTree.gso _ _ _ _ hne]
      exact filter_globdefs_map_2 id l u m1 m2 hu hm

/-- `Unusedglobproof.filter_globdefs_map` -/
theorem filter_globdefs_map (id : Ident) (u : IS) (defs : List (Ident × GlobDef RTL.Fundef Unit)) :
    (PTree.ofList (filterGlobdefs u [] defs.reverse)).get id =
      if IS.mem id u then (PTree.ofList defs).get id else none := by
  split
  · next hmem =>
    have := filter_globdefs_map_2 id defs.reverse u PTree.empty PTree.empty hmem rfl
    rw [List.reverse_reverse] at this
    exact this
  · next hmem =>
    exact filter_globdefs_map_1 id _ u PTree.empty (by simpa using hmem) (by simp)

/-- `Unusedglobproof.filter_globdefs_domain` -/
theorem filter_globdefs_domain {id : Ident} :
    ∀ (l : List (Ident × GlobDef RTL.Fundef Unit)) (u : IS),
      id ∈ (filterGlobdefs u [] l).map Prod.fst → id ∈ u ∧ id ∈ l.map Prod.fst
  | [], _, h => by simp [filterGlobdefs] at h
  | (id1, gd1) :: l, u, h => by
    simp only [filterGlobdefs] at h
    split at h
    · next hmem =>
      rw [filter_globdefs_nil, List.map_append, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨A, B⟩ := filter_globdefs_domain l _ h
        rw [IS.mem_remove] at A
        exact ⟨A.1, List.mem_cons_of_mem _ B⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
        subst h
        exact ⟨IS.mem_iff.1 hmem, List.mem_cons_self⟩
    · obtain ⟨A, B⟩ := filter_globdefs_domain l u h
      exact ⟨A, List.mem_cons_of_mem _ B⟩

/-- `Unusedglobproof.filter_globdefs_unique_names` -/
theorem filter_globdefs_unique_names :
    ∀ (l : List (Ident × GlobDef RTL.Fundef Unit)) (u : IS),
      ((filterGlobdefs u [] l).map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | (id1, gd1) :: l, u => by
    simp only [filterGlobdefs]
    split
    · rw [filter_globdefs_nil, List.map_append]
      refine List.nodup_append.2 ⟨filter_globdefs_unique_names l _, by simp, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      intro e; subst e
      have := (filter_globdefs_domain l _ ha).1
      rw [IS.mem_remove] at this
      exact this.2 rfl
    · exact filter_globdefs_unique_names l u

/-- `Unusedglobproof.transf_program_match` -/
theorem transf_program_match {p tp : RTL.Program} (h : transformProgram p = .OK tp) :
    MatchProg p tp := by
  unfold transformProgram at h
  dsimp only at h
  split at h
  · cases h
  · next u hu =>
    split at h
    · next hdef =>
      cases h
      refine ⟨u, used_globals_valid p hu hdef, rfl, rfl, ?_, ?_⟩
      · intro id
        exact filter_globdefs_map id u p.prog_defs
      · exact filter_globdefs_unique_names _ u
    · cases h

end Unusedglob
end X86
end CC
