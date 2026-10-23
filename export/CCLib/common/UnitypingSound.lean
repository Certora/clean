/-
  A solver for unification constraints: soundness and completeness — port of
  the proof part of `common/Unityping.v`: `set_incr`, `set_sound`,
  `set_list_incr`, `set_list_sound`, `move_incr`, `move_sound`,
  `solve_rec_incr`, `solve_rec_sound`, `move_false`, `solve_rec_false`,
  `solve_constraints_incr`, `solve_constraints_sound`, **`solve_sound`**,
  and `set_complete`, `set_list_complete`, `move_complete`,
  `solve_rec_complete`, `solve_constraints_complete`, **`solve_complete`**.
-/
import CCLib.common.Unityping

namespace CC
namespace UniSolver

variable {T : Type} [DecidableEq T]

/-- `UniSolver.set_incr` -/
theorem set_incr {te : Typassign T} {x : Positive} {ty : T} {e e' : Typenv T}
    (h : set e x ty = .OK e') (hs : Satisf te e') : Satisf te e := by
  unfold set at h
  split at h
  · next hx =>
    cases h
    obtain ⟨A, B⟩ := hs
    refine ⟨fun y t hy => A y t ?_, B⟩
    have hne : x ≠ y := by rintro rfl; rw [hx] at hy; cases hy
    show PTree.get y (PTree.set x ty e.te_typ) = some t
    rw [PTree.gso _ _ _ _ hne]; exact hy
  · split at h
    · cases h; exact hs
    · cases h

/-- `UniSolver.set_sound` -/
theorem set_sound {te : Typassign T} {x : Positive} {ty : T} {e e' : Typenv T}
    (h : set e x ty = .OK e') (hs : Satisf te e') : te x = ty := by
  obtain ⟨P, _⟩ := hs
  unfold set at h
  split at h
  · cases h
    exact P x ty (PTree.gss _ _ _)
  · next ty' hx =>
    split at h
    · next heq => cases h; subst heq; exact P x _ hx
    · cases h

/-- `UniSolver.set_list_incr` -/
theorem set_list_incr {te : Typassign T} :
    ∀ {xl : List Positive} {tyl : List T} {e e' : Typenv T},
    setList e xl tyl = .OK e' → Satisf te e' → Satisf te e
  | [], [], _, _, h, hs => by cases h; exact hs
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | x :: xl, ty :: tyl, e, e', h, hs => by
    simp only [setList] at h
    split at h
    · next e1 h1 => exact set_incr h1 (set_list_incr h hs)
    · cases h

/-- `UniSolver.set_list_sound` -/
theorem set_list_sound {te : Typassign T} :
    ∀ {xl : List Positive} {tyl : List T} {e e' : Typenv T},
    setList e xl tyl = .OK e' → Satisf te e' → xl.map te = tyl
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | x :: xl, ty :: tyl, e, e', h, hs => by
    simp only [setList] at h
    split at h
    · next e1 h1 =>
      simp only [List.map_cons]
      rw [set_sound h1 (set_list_incr h hs), set_list_sound h hs]
    · cases h

/-- `UniSolver.move_incr` -/
theorem move_incr {te : Typassign T} {e : Typenv T} {r1 r2 : Positive} {e' : Typenv T}
    {changed : Bool} (h : move e r1 r2 = .OK (changed, e')) (hs : Satisf te e') :
    Satisf te e := by
  obtain ⟨P, Q⟩ := hs
  unfold move at h
  split at h
  · cases h; exact ⟨P, Q⟩
  · next hne =>
    split at h
    · next h1 h2 =>
      cases h
      exact ⟨P, fun x y hxy => Q x y (List.mem_cons_of_mem _ hxy)⟩
    · next ty1 h1 h2 =>
      cases h
      refine ⟨fun x t hx => P x t ?_, Q⟩
      have : r2 ≠ x := by rintro rfl; rw [h2] at hx; cases hx
      show PTree.get x (PTree.set r2 ty1 e.te_typ) = some t
      rw [PTree.gso _ _ _ _ this]; exact hx
    · next ty2 h1 h2 =>
      cases h
      refine ⟨fun x t hx => P x t ?_, Q⟩
      have : r1 ≠ x := by rintro rfl; rw [h1] at hx; cases hx
      show PTree.get x (PTree.set r1 ty2 e.te_typ) = some t
      rw [PTree.gso _ _ _ _ this]; exact hx
    · split at h
      · cases h; exact ⟨P, Q⟩
      · cases h

/-- `UniSolver.move_sound` -/
theorem move_sound {te : Typassign T} {e : Typenv T} {r1 r2 : Positive} {e' : Typenv T}
    {changed : Bool} (h : move e r1 r2 = .OK (changed, e')) (hs : Satisf te e') :
    te r1 = te r2 := by
  obtain ⟨P, Q⟩ := hs
  unfold move at h
  split at h
  · next heq => rw [heq]
  · next hne =>
    split at h
    · cases h; exact Q r1 r2 (List.mem_cons_self ..)
    · next ty1 h1 h2 =>
      cases h
      have hne' : r2 ≠ r1 := Ne.symm hne
      have g1 : PTree.get r1 (PTree.set r2 ty1 e.te_typ) = some ty1 := by
        rw [PTree.gso _ _ _ _ hne']; exact h1
      rw [P r1 ty1 g1, P r2 ty1 (PTree.gss _ _ _)]
    · next ty2 h1 h2 =>
      cases h
      have g2 : PTree.get r2 (PTree.set r1 ty2 e.te_typ) = some ty2 := by
        rw [PTree.gso _ _ _ _ hne]; exact h2
      rw [P r1 ty2 (PTree.gss _ _ _), P r2 ty2 g2]
    · next ty1 ty2 h1 h2 =>
      split at h
      · next heq => cases h; subst heq; rw [P r1 _ h1, P r2 _ h2]
      · cases h

/-- `UniSolver.solve_rec_incr` -/
theorem solveRec_incr {te : Typassign T} :
    ∀ {q : List Constraint} {e : Typenv T} {changed : Bool} {e' : Typenv T} {changed' : Bool},
    solveRec e changed q = .OK (e', changed') → Satisf te e' → Satisf te e
  | [], _, _, _, _, h, hs => by cases h; exact hs
  | (r1, r2) :: q, e, changed, e', changed', h, hs => by
    simp only [solveRec] at h
    split at h
    · next ch1 e1 hm => exact move_incr hm (solveRec_incr h hs)
    · cases h

/-- `UniSolver.solve_rec_sound` -/
theorem solveRec_sound {te : Typassign T} {r1 r2 : Positive} :
    ∀ {q : List Constraint} {e : Typenv T} {changed : Bool} {e' : Typenv T} {changed' : Bool},
    solveRec e changed q = .OK (e', changed') → (r1, r2) ∈ q → Satisf te e' → te r1 = te r2
  | [], _, _, _, _, _, hin, _ => by cases hin
  | (r3, r4) :: q, e, changed, e', changed', h, hin, hs => by
    simp only [solveRec] at h
    split at h
    · next ch1 e1 hm =>
      rcases List.mem_cons.mp hin with heq | hin
      · cases heq; exact move_sound hm (solveRec_incr h hs)
      · exact solveRec_sound h hin hs
    · cases h

/-- `UniSolver.move_false` -/
theorem move_false {e : Typenv T} {r1 r2 : Positive} {e' : Typenv T} (dflt : T)
    (h : move e r1 r2 = .OK (false, e')) :
    e'.te_typ = e.te_typ ∧ makeassign dflt e r1 = makeassign dflt e r2 := by
  unfold move at h
  split at h
  · next heq => cases h; subst heq; exact ⟨rfl, rfl⟩
  · split at h
    · next h1 h2 => cases h; refine ⟨rfl, ?_⟩; simp only [makeassign, h1, h2]
    · cases h
    · cases h
    · next ty1 ty2 h1 h2 =>
      split at h
      · next heq => cases h; subst heq; refine ⟨rfl, ?_⟩; simp only [makeassign, h1, h2]
      · cases h

/-- `UniSolver.solve_rec_false` -/
theorem solveRec_false (dflt : T) {r1 r2 : Positive} :
    ∀ {q : List Constraint} {e : Typenv T} {changed : Bool} {e' : Typenv T},
    solveRec e changed q = .OK (e', false) →
    changed = false ∧ ((r1, r2) ∈ q → makeassign dflt e r1 = makeassign dflt e r2)
  | [], _, _, _, h => by
    simp only [solveRec, Res.OK.injEq, Prod.mk.injEq] at h
    exact ⟨h.2, fun hin => by cases hin⟩
  | (r3, r4) :: q, e, changed, e', h => by
    simp only [solveRec] at h
    split at h
    · next ch1 e1 hm =>
      obtain ⟨P, Q⟩ := solveRec_false dflt h
      have hc : changed = false := by cases changed <;> simp_all
      have hc1 : ch1 = false := by cases ch1 <;> simp_all
      subst hc1
      obtain ⟨U, V⟩ := move_false dflt hm
      refine ⟨hc, fun hin => ?_⟩
      rcases List.mem_cons.mp hin with heq | hin
      · cases heq; exact V
      · have := Q hin
        simp only [makeassign, U] at this ⊢
        exact this
    · cases h

theorem solveConstraints_of_false {e e0 : Typenv T}
    (h : solveRec ⟨e.te_typ, []⟩ false e.te_equ = .OK (e0, false)) :
    solveConstraints e = .OK e := by
  rw [solveConstraints]
  split
  · rfl
  · next heq => rw [h] at heq; cases heq
  · next heq => rw [h] at heq; cases heq

theorem solveConstraints_of_true {e e1 : Typenv T}
    (h : solveRec ⟨e.te_typ, []⟩ false e.te_equ = .OK (e1, true)) :
    solveConstraints e = solveConstraints e1 := by
  rw [solveConstraints]
  split
  · next heq => rw [h] at heq; cases heq
  · next heq => rw [h] at heq; cases heq; rfl
  · next heq => rw [h] at heq; cases heq

theorem solveConstraints_of_error {e : Typenv T} {m : String}
    (h : solveRec ⟨e.te_typ, []⟩ false e.te_equ = .Error m) :
    solveConstraints e = .Error m := by
  rw [solveConstraints]
  split
  · next heq => rw [h] at heq; cases heq
  · next heq => rw [h] at heq; cases heq
  · next heq => rw [h] at heq; cases heq; rfl

/-- `UniSolver.solve_constraints_incr` -/
theorem solveConstraints_incr {te : Typassign T} (e : Typenv T) :
    ∀ {e' : Typenv T}, solveConstraints e = .OK e' → Satisf te e' → Satisf te e := by
  induction e using solveConstraints.induct with
  | case1 e e0 h =>
    intro e' hsc hs
    first | rw [solveConstraints_of_false h] at hsc | rw [solveConstraints_of_true h] at hsc | rw [solveConstraints_of_error h] at hsc
    cases hsc; exact hs
  | case2 e e1 h _ ih =>
    intro e' hsc hs
    first | rw [solveConstraints_of_false h] at hsc | rw [solveConstraints_of_true h] at hsc | rw [solveConstraints_of_error h] at hsc
    have H1 := ih hsc hs
    obtain ⟨A, _⟩ := solveRec_incr h H1
    exact ⟨A, fun x y hxy => solveRec_sound h hxy H1⟩
  | case3 e m h =>
    intro e' hsc _
    first | rw [solveConstraints_of_false h] at hsc | rw [solveConstraints_of_true h] at hsc | rw [solveConstraints_of_error h] at hsc
    cases hsc

/-- `UniSolver.solve_constraints_sound` -/
theorem solveConstraints_sound (dflt : T) (e : Typenv T) :
    ∀ {e' : Typenv T}, solveConstraints e = .OK e' → Satisf (makeassign dflt e') e' := by
  induction e using solveConstraints.induct with
  | case1 e e0 h =>
    intro e' hsc
    first | rw [solveConstraints_of_false h] at hsc | rw [solveConstraints_of_true h] at hsc | rw [solveConstraints_of_error h] at hsc
    cases hsc
    refine ⟨fun x ty hx => by simp only [makeassign, hx], fun x y hxy => ?_⟩
    exact (solveRec_false dflt h).2 hxy
  | case2 e e1 h _ ih =>
    intro e' hsc
    first | rw [solveConstraints_of_false h] at hsc | rw [solveConstraints_of_true h] at hsc | rw [solveConstraints_of_error h] at hsc
    exact ih hsc
  | case3 e m h =>
    intro e' hsc
    first | rw [solveConstraints_of_false h] at hsc | rw [solveConstraints_of_true h] at hsc | rw [solveConstraints_of_error h] at hsc
    cases hsc

/-- `UniSolver.solve_sound` -/
theorem solve_sound {dflt : T} {e : Typenv T} {te : Typassign T} (h : solve dflt e = .OK te) :
    Satisf te e := by
  unfold solve at h
  split at h
  · next e' hsc =>
    cases h
    exact solveConstraints_incr e hsc (solveConstraints_sound dflt e hsc)
  · cases h

/-! ### Completeness -/

/-- `UniSolver.set_complete` -/
theorem set_complete {te : Typassign T} {e : Typenv T} {x : Positive} {ty : T}
    (hs : Satisf te e) (hx : te x = ty) : ∃ e', set e x ty = .OK e' ∧ Satisf te e' := by
  obtain ⟨P, Q⟩ := hs
  unfold set
  split
  · next hget =>
    refine ⟨_, rfl, fun y t hy => ?_, Q⟩
    rw [PTree.gsspec] at hy
    split at hy
    · next heq => cases hy; subst heq; exact hx
    · exact P y t hy
  · next ty1 hget =>
    have : ty = ty1 := hx ▸ P x ty1 hget
    rw [if_pos this]
    exact ⟨e, rfl, P, Q⟩

/-- `UniSolver.set_list_complete` -/
theorem set_list_complete {te : Typassign T} :
    ∀ (xl : List Positive) {e : Typenv T}, Satisf te e →
    ∃ e', setList e xl (xl.map te) = .OK e' ∧ Satisf te e'
  | [], e, hs => ⟨e, rfl, hs⟩
  | x :: xl, e, hs => by
    obtain ⟨e1, P, Q⟩ := set_complete (x := x) hs rfl
    obtain ⟨e2, U, V⟩ := set_list_complete xl Q
    refine ⟨e2, ?_, V⟩
    simp only [List.map_cons, setList, P, U]

/-- `UniSolver.move_complete` -/
theorem move_complete {te : Typassign T} {e : Typenv T} {r1 r2 : Positive}
    (hs : Satisf te e) (h12 : te r1 = te r2) :
    ∃ changed e', move e r1 r2 = .OK (changed, e') ∧ Satisf te e' := by
  obtain ⟨P, Q⟩ := hs
  unfold move
  split
  · exact ⟨_, _, rfl, P, Q⟩
  · split
    · refine ⟨_, _, rfl, P, fun x y hxy => ?_⟩
      rcases List.mem_cons.mp hxy with heq | hxy
      · cases heq; exact h12
      · exact Q x y hxy
    · next ty1 h1 h2 =>
      refine ⟨_, _, rfl, fun x t hx => ?_, Q⟩
      simp only at hx
      rw [PTree.gsspec] at hx
      split at hx
      · next heq => cases hx; subst heq; rw [← h12]; exact P r1 _ h1
      · exact P x t hx
    · next ty2 h1 h2 =>
      refine ⟨_, _, rfl, fun x t hx => ?_, Q⟩
      simp only at hx
      rw [PTree.gsspec] at hx
      split at hx
      · next heq => cases hx; subst heq; rw [h12]; exact P r2 _ h2
      · exact P x t hx
    · next ty1 ty2 h1 h2 =>
      have : ty1 = ty2 := by rw [← P r1 _ h1, ← P r2 _ h2]; exact h12
      rw [if_pos this]
      exact ⟨_, _, rfl, P, Q⟩

/-- `UniSolver.solve_rec_complete` -/
theorem solveRec_complete {te : Typassign T} :
    ∀ (q : List Constraint) {e : Typenv T} (changed : Bool), Satisf te e →
    (∀ r1 r2, (r1, r2) ∈ q → te r1 = te r2) →
    ∃ e' changed', solveRec e changed q = .OK (e', changed') ∧ Satisf te e'
  | [], e, changed, hs, _ => ⟨e, changed, rfl, hs⟩
  | (r1, r2) :: q, e, changed, hs, hq => by
    obtain ⟨ch1, e1, A, B⟩ := move_complete hs (hq r1 r2 (List.mem_cons_self ..))
    obtain ⟨e', ch', C, D⟩ := solveRec_complete q (changed || ch1) B
      (fun x y hxy => hq x y (List.mem_cons_of_mem _ hxy))
    refine ⟨e', ch', ?_, D⟩
    simp only [solveRec, A, C]

/-- `UniSolver.solve_constraints_complete` -/
theorem solveConstraints_complete {te : Typassign T} (e : Typenv T) :
    Satisf te e → ∃ e', solveConstraints e = .OK e' ∧ Satisf te e' := by
  induction e using solveConstraints.induct with
  | case1 e e0 h =>
    intro hs
    exact ⟨e, solveConstraints_of_false h, hs⟩
  | case2 e e1 h _ ih =>
    intro hs
    obtain ⟨P, Q⟩ := hs
    obtain ⟨e1', ch1, R, S⟩ := solveRec_complete e.te_equ (e := ⟨e.te_typ, []⟩) false
      ⟨P, fun _ _ h => by cases h⟩ Q
    rw [h] at R
    cases R
    obtain ⟨e', U, V⟩ := ih S
    exact ⟨e', by rw [solveConstraints_of_true h]; exact U, V⟩
  | case3 e m h =>
    intro hs
    obtain ⟨P, Q⟩ := hs
    obtain ⟨e1', ch1, R, _⟩ := solveRec_complete e.te_equ (e := ⟨e.te_typ, []⟩) false
      ⟨P, fun _ _ h => by cases h⟩ Q
    rw [h] at R
    cases R

/-- `UniSolver.solve_complete` -/
theorem solve_complete (dflt : T) {te : Typassign T} {e : Typenv T} (hs : Satisf te e) :
    ∃ te', solve dflt e = .OK te' := by
  obtain ⟨e', P, _⟩ := solveConstraints_complete e hs
  exact ⟨_, by unfold solve; rw [P]⟩

end UniSolver
end CC
