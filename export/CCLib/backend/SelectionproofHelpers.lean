/-
  Correctness of instruction selection — port of `backend/Selectionproof.v`,
  processing of helper functions: `record_globdefs_sound`,
  `lookup_helper_correct_1`, `lookup_helper_correct`, `get_helpers_correct`.

  These lemmas only mention Cminor programs and the target-independent
  definitions of `Selection.v` (`record_globdefs`, `lookup_helper`,
  `get_helpers`), so they are shared by all targets.  They are not needed on
  aarch64 (whose instruction selection never calls a helper); the x86-64
  proof (`CCLib/x86/SelectionproofMain.lean`) uses them.

  `PTree_Properties.fold_rec` is replaced by induction on the list of
  elements, since `PTree.fold` is defined as a left fold over
  `PTree.elements` in this port.
-/
import CCLib.backend.Selection
import CCLib.backend.SplitLongproof

namespace CC
namespace Selectionproof

open Selection SplitLong SplitLongproof

theorem record_globdefs_fold_sound (id : Ident) (gd : Globdef) :
    ∀ (l : List (Positive × Globdef)) (m : PTree Globdef),
    (l.foldl (fun a p => if globdefOfInterest p.2 then a.set p.1 p.2 else a) m).get id = some gd →
    m.get id = some gd ∨ (id, gd) ∈ l
  | [], m, h => .inl h
  | (k, v) :: l, m, h => by
    rcases record_globdefs_fold_sound id gd l _ h with h' | h'
    · dsimp only at h'
      split at h'
      · rw [PTree.gsspec] at h'
        split at h'
        · next hk => cases h'; subst hk; exact .inr (.head _)
        · exact .inl h'
      · exact .inl h'
    · exact .inr (.tail _ h')

/-- `Selectionproof.record_globdefs_sound` -/
theorem record_globdefs_sound {dm : PTree Globdef} {id : Ident} {gd : Globdef}
    (h : (recordGlobdefs dm).get id = some gd) : dm.get id = some gd := by
  unfold recordGlobdefs at h
  rw [PTree.fold_spec] at h
  rcases record_globdefs_fold_sound id gd _ _ h with h' | h'
  · simp at h'
  · exact PTree.elements_complete _ _ _ h'

theorem lookup_helper_fold_correct (name : String) (sg : Signature) (id : Ident) :
    ∀ (l : List (Positive × Globdef)) (res : Option Ident),
    l.foldl (fun a p => lookupHelperAux name sg a p.1 p.2) res = some id →
    res = some id ∨ (id, GlobDef.Gfun (ASTFundef.External (.EF_runtime name sg))) ∈ l
  | [], res, h => .inl h
  | (k, v) :: l, res, h => by
    rcases lookup_helper_fold_correct name sg id l _ h with h' | h'
    · dsimp only [lookupHelperAux] at h'
      split at h'
      · next name' sg' =>
        split at h'
        · next hc =>
          cases h'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨h1, h2⟩ := hc
          have h1' : name = name' := by simpa using h1
          subst h1' h2
          exact .inr (.head _)
        · exact .inl h'
      · exact .inl h'
    · exact .inr (.tail _ h')

/-- `Selectionproof.lookup_helper_correct_1` -/
theorem lookup_helper_correct_1 {globs : PTree Globdef} {name : String} {sg : Signature}
    {id : Ident} (h : lookupHelper globs name sg = .OK id) :
    globs.get id = some (.Gfun (.External (.EF_runtime name sg))) := by
  unfold lookupHelper at h
  split at h
  · next id' hf =>
    cases h
    rw [PTree.fold_spec] at hf
    rcases lookup_helper_fold_correct name sg id _ _ hf with h' | h'
    · cases h'
    · exact PTree.elements_complete _ _ _ h'
  · cases h

/-- `Selectionproof.lookup_helper_correct` -/
theorem lookup_helper_correct {p : Cminor.Program} {name : String} {sg : Signature} {id : Ident}
    (h : lookupHelper (recordGlobdefs p.defmap) name sg = .OK id) :
    helper_declared p id name sg :=
  record_globdefs_sound (lookup_helper_correct_1 h)

/-- `Selectionproof.get_helpers_correct` -/
theorem get_helpers_correct {p : Cminor.Program} {hf : HelperFunctions}
    (h : getHelpers p.defmap = .OK hf) : helper_functions_declared p hf := by
  have bind_ok : ∀ {A B : Type} {x : Res A} {f : A → Res B} {b : B},
      (x >>= f) = Res.OK b ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
    intro A B x f b; cases x <;> simp [bind, Res.bind]
  simp only [getHelpers, bind_ok] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, _, h5, _, h6, _, h7, _, h8, _, h9, _, h10, _, h11, _, h12,
    _, h13, _, h14, _, h15, h⟩ := h
  cases h
  exact ⟨lookup_helper_correct h1, lookup_helper_correct h2, lookup_helper_correct h3,
    lookup_helper_correct h4, lookup_helper_correct h5, lookup_helper_correct h6,
    lookup_helper_correct h7, lookup_helper_correct h8, lookup_helper_correct h9,
    lookup_helper_correct h10, lookup_helper_correct h11, lookup_helper_correct h12,
    lookup_helper_correct h13, lookup_helper_correct h14, lookup_helper_correct h15⟩

end Selectionproof
end CC
