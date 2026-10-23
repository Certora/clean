/-
  A solver for subtyping constraints — port of `common/Subtyping.v`
  (the `TYPE_ALGEBRA` interface and the `SubSolver` functor).

  The solver handles constraints of the forms `base-type <: T(x)`,
  `T(x) <: base-type` and `T(x) <: T(y)`, where the unknowns are the types
  `T(x)` of identifiers `x`.

  Ported, with the same structure and statements: `bounds`, `constraint`,
  `typenv`, `initial`, `type_def(s)`, `type_use(s)`, `type_move`,
  `solve_rec`, the termination measure (`weight_bounds`, `weight_type_move`,
  `weight_constraints`, `weight_solve_rec`, `weight_typenv`),
  `solve_constraints`, `typassign`, `makeassign`, `solve`, `satisf`,
  `satisf_initial`; the soundness proof (`type_def_sound`, …,
  `solve_sound`) and the completeness proof (`type_def_complete`, …,
  `solve_complete`).

  Differences from Rocq:
  * the module type `TYPE_ALGEBRA` is the class `TypeAlgebra T` and the
    functor `SubSolver` is the namespace `SubSolver`, parameterised by an
    instance;
  * error messages are plain strings (the port's `Res`);
  * `list_forall2` is the port's `ListForall2` (from `LinkingTheory`);
  * `solve_constraints` is defined by well-founded recursion on
    `weight_typenv` with `termination_by` instead of `Function`.
-/
import CCLib.lib.MapsTheory
import CCLib.common.LinkingTheory
import CCLib.cfrontend.Ctypes

namespace CC

/-- `Subtyping.TYPE_ALGEBRA`: base types with subtyping, bounds and a weight. -/
class TypeAlgebra (T : Type) where
  eq : DecidableEq T
  default : T
  sub : T → T → Prop
  sub_refl : ∀ x, sub x x
  sub_trans : ∀ x y z, sub x y → sub y z → sub x z
  sub_dec : ∀ x y, Decidable (sub x y)
  lub : T → T → T
  lub_left : ∀ x y z, sub x z → sub y z → sub x (lub x y)
  lub_right : ∀ x y z, sub x z → sub y z → sub y (lub x y)
  lub_min : ∀ x y z, sub x z → sub y z → sub (lub x y) z
  glb : T → T → T
  glb_left : ∀ x y z, sub z x → sub z y → sub (glb x y) x
  glb_right : ∀ x y z, sub z x → sub z y → sub (glb x y) y
  glb_max : ∀ x y z, sub z x → sub z y → sub z (glb x y)
  low_bound : T → T
  high_bound : T → T
  low_bound_sub : ∀ t, sub (low_bound t) t
  low_bound_minorant : ∀ x y, sub x y → sub (low_bound y) x
  high_bound_sub : ∀ t, sub t (high_bound t)
  high_bound_majorant : ∀ x y, sub x y → sub y (high_bound x)
  weight : T → Nat
  max_weight : Nat
  weight_range : ∀ t, weight t ≤ max_weight
  weight_sub : ∀ x y, sub x y → weight x ≤ weight y
  weight_sub_strict : ∀ x y, sub x y → x ≠ y → weight x < weight y

instance TypeAlgebra.instDecidableEq {T : Type} [h : TypeAlgebra T] : DecidableEq T := h.eq
instance TypeAlgebra.instDecidableSub {T : Type} [h : TypeAlgebra T] (x y : T) :
    Decidable (h.sub x y) := h.sub_dec x y

namespace SubSolver

open TypeAlgebra

variable {T : Type} [TypeAlgebra T]

/-- `SubSolver.bounds`: a low and a high bound, with `lo <: hi`. -/
structure Bounds (T : Type) [TypeAlgebra T] where
  lo : T
  hi : T
  SUB : sub lo hi

/-- `SubSolver.constraint`: `(x, y)` stands for `T(x) <: T(y)`. -/
abbrev Constraint := Positive × Positive

/-- `SubSolver.typenv` -/
structure Typenv (T : Type) [TypeAlgebra T] where
  te_typ : PTree (Bounds T)
  te_sub : List Constraint

/-- `SubSolver.initial` -/
def initial : Typenv T := ⟨PTree.empty, []⟩

/-- `SubSolver.type_def`: add the constraint `ty <: T(x)`. -/
def typeDef (e : Typenv T) (x : Positive) (ty : T) : Res (Typenv T) :=
  match e.te_typ.get x with
  | none => .OK ⟨e.te_typ.set x ⟨ty, high_bound ty, high_bound_sub ty⟩, e.te_sub⟩
  | some ⟨lo, hi, s1⟩ =>
      if s2 : sub ty hi then
        if lo = lub lo ty then .OK e
        else .OK ⟨e.te_typ.set x ⟨lub lo ty, hi, lub_min lo ty hi s1 s2⟩, e.te_sub⟩
      else .Error "bad definition of variable"

/-- `SubSolver.type_defs` -/
def typeDefs : Typenv T → List Positive → List T → Res (Typenv T)
  | e, [], [] => .OK e
  | e, r1 :: rs, ty1 :: tys =>
      match typeDef e r1 ty1 with
      | .OK e1 => typeDefs e1 rs tys
      | .Error m => .Error m
  | _, _, _ => .Error "arity mismatch"

/-- `SubSolver.type_use`: add the constraint `T(x) <: ty`. -/
def typeUse (e : Typenv T) (x : Positive) (ty : T) : Res (Typenv T) :=
  match e.te_typ.get x with
  | none => .OK ⟨e.te_typ.set x ⟨low_bound ty, ty, low_bound_sub ty⟩, e.te_sub⟩
  | some ⟨lo, hi, s1⟩ =>
      if s2 : sub lo ty then
        if hi = glb hi ty then .OK e
        else .OK ⟨e.te_typ.set x ⟨lo, glb hi ty, glb_max hi ty lo s1 s2⟩, e.te_sub⟩
      else .Error "bad use of variable"

/-- `SubSolver.type_uses` -/
def typeUses : Typenv T → List Positive → List T → Res (Typenv T)
  | e, [], [] => .OK e
  | e, r1 :: rs, ty1 :: tys =>
      match typeUse e r1 ty1 with
      | .OK e1 => typeUses e1 rs tys
      | .Error m => .Error m
  | _, _, _ => .Error "arity mismatch"

/-- `SubSolver.type_move`, the case where both variables have bounds. -/
def typeMoveBoth (e : Typenv T) (r1 r2 : Positive) (b1 b2 : Bounds T) : Res (Bool × Typenv T) :=
  if sub b1.hi b2.lo then .OK (false, e)
  else if s : sub b1.lo b2.hi then
    let lo2' := lub b1.lo b2.lo
    let hi1' := glb b1.hi b2.hi
    let nb1 : Bounds T := ⟨b1.lo, hi1', glb_max b1.hi b2.hi b1.lo b1.SUB s⟩
    let nb2 : Bounds T := ⟨lo2', b2.hi, lub_min b1.lo b2.lo b2.hi s b2.SUB⟩
    if b2.lo = lo2' then
      if b1.hi = hi1' then .OK (false, ⟨e.te_typ, (r1, r2) :: e.te_sub⟩)
      else .OK (true, ⟨e.te_typ.set r1 nb1, (r1, r2) :: e.te_sub⟩)
    else
      if b1.hi = hi1' then .OK (true, ⟨e.te_typ.set r2 nb2, (r1, r2) :: e.te_sub⟩)
      else .OK (true, ⟨(e.te_typ.set r1 nb1).set r2 nb2, (r1, r2) :: e.te_sub⟩)
  else .Error "ill-typed move"

/-- `SubSolver.type_move`: add the constraint `T(r1) <: T(r2)`.  The Boolean
is `true` if the bounds of `r1` or `r2` were tightened. -/
def typeMove (e : Typenv T) (r1 r2 : Positive) : Res (Bool × Typenv T) :=
  if r1 = r2 then .OK (false, e) else
  match e.te_typ.get r1, e.te_typ.get r2 with
  | none, none => .OK (false, ⟨e.te_typ, (r1, r2) :: e.te_sub⟩)
  | some b1, none =>
      .OK (true, ⟨e.te_typ.set r2 ⟨b1.lo, high_bound b1.lo, high_bound_sub b1.lo⟩,
                  if sub b1.hi b1.lo then e.te_sub else (r1, r2) :: e.te_sub⟩)
  | none, some b2 =>
      .OK (true, ⟨e.te_typ.set r1 ⟨low_bound b2.hi, b2.hi, low_bound_sub b2.hi⟩,
                  if sub b2.hi b2.lo then e.te_sub else (r1, r2) :: e.te_sub⟩)
  | some b1, some b2 => typeMoveBoth e r1 r2 b1 b2

/-- `SubSolver.solve_rec` -/
def solveRec : Typenv T → Bool → List Constraint → Res (Typenv T × Bool)
  | e, changed, [] => .OK (e, changed)
  | e, changed, (r1, r2) :: q' =>
      match typeMove e r1 r2 with
      | .OK (changed1, e1) => solveRec e1 (changed || changed1) q'
      | .Error m => .Error m

/-! ### Measuring the state -/

/-- `SubSolver.weight_bounds` -/
def weightBounds : Option (Bounds T) → Nat
  | none => max_weight T + 1
  | some b => weight b.hi - weight b.lo

theorem weight_bounds_1 (b : Bounds T) : weightBounds (some b) < weightBounds (none : Option (Bounds T)) := by
  have := weight_range b.hi
  simp only [weightBounds]; omega

theorem weight_bounds_2 (b1 b2 : Bounds T) (h1 : sub b2.lo b1.lo) (h2 : sub b1.hi b2.hi)
    (h : b1.lo ≠ b2.lo ∨ b1.hi ≠ b2.hi) : weightBounds (some b1) < weightBounds (some b2) := by
  have A := weight_sub _ _ b1.SUB
  have B := weight_sub _ _ b2.SUB
  have C := weight_sub _ _ h1
  have D := weight_sub _ _ h2
  simp only [weightBounds]
  rcases h with h | h
  · have := weight_sub_strict _ _ h1 (Ne.symm h); omega
  · have := weight_sub_strict _ _ h2 h; omega

/-- The bounds of a variable after a `set`. -/
theorem weightBounds_set_le (m : PTree (Bounds T)) (x : Positive) (b : Bounds T)
    (hb : weightBounds (some b) ≤ weightBounds (m.get x)) (r : Positive) :
    weightBounds ((m.set x b).get r) ≤ weightBounds (m.get r) := by
  rw [PTree.gsspec]
  split
  · next h => subst h; exact hb
  · exact Nat.le_refl _

theorem weight_type_move_both (e : Typenv T) (r1 r2 : Positive) (b1 b2 : Bounds T)
    (hne : r1 ≠ r2) (E1 : e.te_typ.get r1 = some b1) (E2 : e.te_typ.get r2 = some b2)
    (changed : Bool) (e' : Typenv T) (h : typeMoveBoth e r1 r2 b1 b2 = .OK (changed, e')) :
    (e'.te_sub = e.te_sub ∨ e'.te_sub = (r1, r2) :: e.te_sub) ∧
    (∀ r, weightBounds (e'.te_typ.get r) ≤ weightBounds (e.te_typ.get r)) ∧
    (changed = true →
      weightBounds (e'.te_typ.get r1) + weightBounds (e'.te_typ.get r2) <
        weightBounds (e.te_typ.get r1) + weightBounds (e.te_typ.get r2)) := by
  unfold typeMoveBoth at h
  by_cases hs1 : sub b1.hi b2.lo
  · rw [if_pos hs1] at h; cases h
    exact ⟨.inl rfl, fun _ => Nat.le_refl _, fun h => nomatch h⟩
  rw [if_neg hs1] at h
  have s : sub b1.lo b2.hi := by
    by_cases s : sub b1.lo b2.hi
    · exact s
    · rw [dif_neg s] at h; cases h
  rw [dif_pos s] at h
  simp only at h
  have S1' : sub (glb b1.hi b2.hi) b1.hi := glb_left _ _ _ b1.SUB s
  have S2' : sub b2.lo (lub b1.lo b2.lo) := lub_right _ _ _ s b2.SUB
  have W1 : weightBounds (some (⟨b1.lo, glb b1.hi b2.hi, glb_max b1.hi b2.hi b1.lo b1.SUB s⟩ : Bounds T))
      ≤ weightBounds (some b1) := by
    have := weight_sub _ _ S1'; simp only [weightBounds]; omega
  have W2 : weightBounds (some (⟨lub b1.lo b2.lo, b2.hi, lub_min b1.lo b2.lo b2.hi s b2.SUB⟩ : Bounds T))
      ≤ weightBounds (some b2) := by
    have := weight_sub _ _ S2'; simp only [weightBounds]; omega
  by_cases q1 : b2.lo = lub b1.lo b2.lo <;> by_cases q2 : b1.hi = glb b1.hi b2.hi
  · rw [if_pos q1, if_pos q2] at h
    simp only [Res.OK.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨.inr rfl, fun _ => Nat.le_refl _, fun h => nomatch h⟩
  · rw [if_pos q1, if_neg q2] at h
    simp only [Res.OK.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have L1 := weight_bounds_2 ⟨b1.lo, glb b1.hi b2.hi, glb_max b1.hi b2.hi b1.lo b1.SUB s⟩ b1
      (sub_refl _) S1' (.inr (Ne.symm q2))
    refine ⟨.inr rfl, weightBounds_set_le _ _ _ (by rw [E1]; exact W1), fun _ => ?_⟩
    simp only
    rw [PTree.gss, PTree.gso _ _ _ _ hne, E1, E2]
    omega
  · rw [if_neg q1, if_pos q2] at h
    simp only [Res.OK.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have L2 := weight_bounds_2 ⟨lub b1.lo b2.lo, b2.hi, lub_min b1.lo b2.lo b2.hi s b2.SUB⟩ b2
      S2' (sub_refl _) (.inl (Ne.symm q1))
    refine ⟨.inr rfl, weightBounds_set_le _ _ _ (by rw [E2]; exact W2), fun _ => ?_⟩
    simp only
    rw [PTree.gss, PTree.gso _ _ _ _ (Ne.symm hne), E1, E2]
    omega
  · rw [if_neg q1, if_neg q2] at h
    simp only [Res.OK.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have L1 := weight_bounds_2 ⟨b1.lo, glb b1.hi b2.hi, glb_max b1.hi b2.hi b1.lo b1.SUB s⟩ b1
      (sub_refl _) S1' (.inr (Ne.symm q2))
    have L2 := weight_bounds_2 ⟨lub b1.lo b2.lo, b2.hi, lub_min b1.lo b2.lo b2.hi s b2.SUB⟩ b2
      S2' (sub_refl _) (.inl (Ne.symm q1))
    refine ⟨.inr rfl, fun r => ?_, fun _ => ?_⟩
    · refine Nat.le_trans (weightBounds_set_le _ _ _ ?_ r)
        (weightBounds_set_le _ _ _ (by rw [E1]; exact W1) r)
      rw [PTree.gso _ _ _ _ hne, E2]; exact W2
    · simp only
      rw [PTree.gss, PTree.gso _ _ _ _ (Ne.symm hne), PTree.gss, E1, E2]
      omega

/-- `SubSolver.weight_type_move` -/
theorem weight_type_move (e : Typenv T) (r1 r2 : Positive) (changed : Bool) (e' : Typenv T)
    (h : typeMove e r1 r2 = .OK (changed, e')) :
    (e'.te_sub = e.te_sub ∨ e'.te_sub = (r1, r2) :: e.te_sub) ∧
    (∀ r, weightBounds (e'.te_typ.get r) ≤ weightBounds (e.te_typ.get r)) ∧
    (changed = true →
      weightBounds (e'.te_typ.get r1) + weightBounds (e'.te_typ.get r2) <
        weightBounds (e.te_typ.get r1) + weightBounds (e.te_typ.get r2)) := by
  unfold typeMove at h
  by_cases hne : r1 = r2
  · rw [if_pos hne] at h; cases h
    exact ⟨.inl rfl, fun _ => Nat.le_refl _, fun h => nomatch h⟩
  rw [if_neg hne] at h
  cases E1 : e.te_typ.get r1 with
  | none =>
    cases E2 : e.te_typ.get r2 with
    | none =>
      rw [E1, E2] at h; cases h
      exact ⟨.inr rfl, fun _ => Nat.le_refl _, fun h => nomatch h⟩
    | some b2 =>
      rw [E1, E2] at h; cases h
      have L := weight_bounds_1 (⟨low_bound b2.hi, b2.hi, low_bound_sub b2.hi⟩ : Bounds T)
      refine ⟨?_, weightBounds_set_le _ _ _ (by rw [E1]; exact Nat.le_of_lt L), fun _ => ?_⟩
      · split <;> simp
      · simp only
        rw [PTree.gss, PTree.gso _ _ _ _ hne, E2]
        omega
  | some b1 =>
    cases E2 : e.te_typ.get r2 with
    | none =>
      rw [E1, E2] at h; cases h
      have L := weight_bounds_1 (⟨b1.lo, high_bound b1.lo, high_bound_sub b1.lo⟩ : Bounds T)
      refine ⟨?_, weightBounds_set_le _ _ _ (by rw [E2]; exact Nat.le_of_lt L), fun _ => ?_⟩
      · split <;> simp
      · simp only
        rw [PTree.gss, PTree.gso _ _ _ _ (Ne.symm hne), E1]
        omega
    | some b2 =>
      rw [E1, E2] at h
      have := weight_type_move_both e r1 r2 b1 b2 hne E1 E2 changed e' h
      rwa [E1, E2] at this

/-- `SubSolver.weight_constraints` -/
def weightConstraints (b : PTree (Bounds T)) (cstr : List Constraint) : Nat :=
  cstr.foldr (fun xy n => n + weightBounds (b.get xy.1) + weightBounds (b.get xy.2)) 0

theorem weight_constraints_tighter (b1 b2 : PTree (Bounds T))
    (h : ∀ r, weightBounds (b1.get r) ≤ weightBounds (b2.get r)) (q : List Constraint) :
    weightConstraints b1 q ≤ weightConstraints b2 q := by
  induction q with
  | nil => exact Nat.le_refl _
  | cons a q ih =>
    simp only [weightConstraints, List.foldr_cons] at ih ⊢
    have := h a.1; have := h a.2; omega

@[simp] theorem weightConstraints_nil (b : PTree (Bounds T)) : weightConstraints b [] = 0 := rfl
@[simp] theorem weightConstraints_cons (b : PTree (Bounds T)) (a : Constraint) (q : List Constraint) :
    weightConstraints b (a :: q) =
      weightConstraints b q + weightBounds (b.get a.1) + weightBounds (b.get a.2) := rfl

/-- `SubSolver.weight_solve_rec` -/
theorem weight_solve_rec :
    ∀ (q : List Constraint) (e : Typenv T) (changed : Bool) (e' : Typenv T) (changed' : Bool),
    solveRec e changed q = .OK (e', changed') →
    (∀ r, weightBounds (e'.te_typ.get r) ≤ weightBounds (e.te_typ.get r)) ∧
    weightConstraints e'.te_typ e'.te_sub + (if changed' && !changed then 1 else 0) ≤
      weightConstraints e.te_typ e.te_sub + weightConstraints e.te_typ q
  | [], e, changed, e', changed', h => by
    simp only [solveRec, Res.OK.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun _ => Nat.le_refl _, ?_⟩
    cases changed <;> simp
  | (r1, r2) :: q, e, changed, e', changed', h => by
    simp only [solveRec] at h
    split at h
    · next changed1 e1 hm =>
      obtain ⟨A, B, C⟩ := weight_type_move e r1 r2 changed1 e1 hm
      obtain ⟨D, E⟩ := weight_solve_rec q e1 (changed || changed1) e' changed' h
      refine ⟨fun r => Nat.le_trans (D r) (B r), ?_⟩
      have P := weight_constraints_tighter _ _ B e.te_sub
      have Q : weightConstraints e1.te_typ e1.te_sub ≤
          weightConstraints e1.te_typ e.te_sub +
            weightBounds (e1.te_typ.get r1) + weightBounds (e1.te_typ.get r2) := by
        rcases A with A | A <;> rw [A]
        · omega
        · simp only [weightConstraints_cons]; omega
      have R := weight_constraints_tighter _ _ B q
      simp only [weightConstraints_cons]
      have B1 := B r1
      have B2 := B r2
      cases changed1
      · cases changed <;> cases changed' <;> simp at E ⊢ <;> omega
      · have C' := C rfl
        cases changed <;> cases changed' <;> simp at E ⊢ <;> omega
    · cases h

/-- `SubSolver.weight_typenv` -/
def weightTypenv (e : Typenv T) : Nat := weightConstraints e.te_typ e.te_sub

/-- `SubSolver.solve_constraints`: iterate `solve_rec` until nothing changes. -/
def solveConstraints (e : Typenv T) : Res (Typenv T) :=
  match h : solveRec ⟨e.te_typ, []⟩ false e.te_sub with
  | .OK (_, false) => .OK e
  | .OK (e', true) =>
      have := weight_solve_rec e.te_sub ⟨e.te_typ, []⟩ false e' true h
      solveConstraints e'
  | .Error m => .Error m
termination_by weightTypenv e
decreasing_by
  simp only [weightTypenv]
  simp at this
  omega

/-- `SubSolver.typassign` -/
abbrev Typassign (T : Type) := Positive → T

/-- `SubSolver.makeassign`: each variable gets its low bound. -/
def makeassign (e : Typenv T) : Typassign T :=
  fun x => match e.te_typ.get x with
    | some b => b.lo
    | none => default

/-- `SubSolver.solve` -/
def solve (e : Typenv T) : Res (Typassign T) :=
  match solveConstraints e with
  | .OK e' => .OK (makeassign e')
  | .Error m => .Error m

/-- `SubSolver.satisf`: `te` is a solution of the constraints `e`. -/
def Satisf (te : Typassign T) (e : Typenv T) : Prop :=
  (∀ x b, e.te_typ.get x = some b → sub b.lo (te x) ∧ sub (te x) b.hi) ∧
  (∀ x y, (x, y) ∈ e.te_sub → sub (te x) (te y))

/-- `SubSolver.satisf_initial` -/
theorem satisf_initial (te : Typassign T) : Satisf te (initial : Typenv T) :=
  ⟨fun x b h => by simp [initial] at h, fun _ _ h => by cases h⟩

/-! ### Soundness -/

/-- Tightening the bounds of one variable preserves solutions backwards. -/
theorem satisf_set_incr (te : Typassign T) (m : PTree (Bounds T)) (x : Positive) (b' : Bounds T)
    (l : List Constraint)
    (H : ∀ b, m.get x = some b → sub b.lo b'.lo ∧ sub b'.hi b.hi)
    (h : Satisf te ⟨m.set x b', l⟩) : Satisf te ⟨m, l⟩ := by
  obtain ⟨P, Q⟩ := h
  refine ⟨fun y b hy => ?_, Q⟩
  by_cases hxy : y = x
  · subst hxy
    obtain ⟨A, B⟩ := H b hy
    obtain ⟨C, D⟩ := P y b' (PTree.gss _ _ _)
    exact ⟨sub_trans _ _ _ A C, sub_trans _ _ _ D B⟩
  · exact P y b (by rw [PTree.gso _ _ _ _ (Ne.symm hxy)]; exact hy)

theorem satisf_sub_incr (te : Typassign T) (m : PTree (Bounds T)) (l : List Constraint)
    (c : Constraint) (h : Satisf te ⟨m, c :: l⟩) : Satisf te ⟨m, l⟩ :=
  ⟨h.1, fun x y hm => h.2 x y (List.mem_cons_of_mem _ hm)⟩

/-- `SubSolver.type_def_incr` -/
theorem type_def_incr (te : Typassign T) (x : Positive) (ty : T) (e e' : Typenv T)
    (h : typeDef e x ty = .OK e') (hs : Satisf te e') : Satisf te e := by
  unfold typeDef at h
  cases E : e.te_typ.get x with
  | none =>
    rw [E] at h; cases h
    exact satisf_set_incr te e.te_typ x _ e.te_sub (fun b hb => by rw [E] at hb; cases hb) hs
  | some b =>
    obtain ⟨lo, hi, s1⟩ := b
    rw [E] at h; simp only at h
    by_cases s2 : sub ty hi
    · rw [dif_pos s2] at h
      by_cases q : lo = lub lo ty
      · rw [if_pos q] at h; cases h; exact hs
      · rw [if_neg q] at h; cases h
        refine satisf_set_incr te e.te_typ x _ e.te_sub (fun b hb => ?_) hs
        rw [E] at hb; cases hb
        exact ⟨lub_left _ _ _ s1 s2, sub_refl _⟩
    · rw [dif_neg s2] at h; cases h

/-- `SubSolver.type_def_sound` -/
theorem type_def_sound (te : Typassign T) (x : Positive) (ty : T) (e e' : Typenv T)
    (h : typeDef e x ty = .OK e') (hs : Satisf te e') : sub ty (te x) := by
  obtain ⟨P, _⟩ := hs
  unfold typeDef at h
  cases E : e.te_typ.get x with
  | none =>
    rw [E] at h; cases h
    exact (P x _ (PTree.gss _ _ _)).1
  | some b =>
    obtain ⟨lo, hi, s1⟩ := b
    rw [E] at h; simp only at h
    by_cases s2 : sub ty hi
    · rw [dif_pos s2] at h
      by_cases q : lo = lub lo ty
      · rw [if_pos q] at h; cases h
        refine sub_trans _ lo _ ?_ (P x _ E).1
        rw [q]; exact lub_right _ _ _ s1 s2
      · rw [if_neg q] at h; cases h
        exact sub_trans _ _ _ (lub_right _ _ _ s1 s2) (P x _ (PTree.gss _ _ _)).1
    · rw [dif_neg s2] at h; cases h

/-- `SubSolver.type_defs_incr` -/
theorem type_defs_incr (te : Typassign T) :
    ∀ (xl : List Positive) (tyl : List T) (e e' : Typenv T),
    typeDefs e xl tyl = .OK e' → Satisf te e' → Satisf te e
  | [], [], e, e', h, hs => by simp only [typeDefs, Res.OK.injEq] at h; subst h; exact hs
  | x :: xl, ty :: tyl, e, e', h, hs => by
    simp only [typeDefs] at h
    split at h
    · next e1 h1 => exact type_def_incr te x ty e e1 h1 (type_defs_incr te xl tyl e1 e' h hs)
    · cases h
  | [], _ :: _, _, _, h, _ => by simp [typeDefs] at h
  | _ :: _, [], _, _, h, _ => by simp [typeDefs] at h

/-- `SubSolver.type_defs_sound` -/
theorem type_defs_sound (te : Typassign T) :
    ∀ (xl : List Positive) (tyl : List T) (e e' : Typenv T),
    typeDefs e xl tyl = .OK e' → Satisf te e' → ListForall2 sub tyl (xl.map te)
  | [], [], _, _, _, _ => .nil
  | x :: xl, ty :: tyl, e, e', h, hs => by
    simp only [typeDefs] at h
    split at h
    · next e1 h1 =>
      exact .cons (type_def_sound te x ty e e1 h1 (type_defs_incr te xl tyl e1 e' h hs))
        (type_defs_sound te xl tyl e1 e' h hs)
    · cases h
  | [], _ :: _, _, _, h, _ => by simp [typeDefs] at h
  | _ :: _, [], _, _, h, _ => by simp [typeDefs] at h

/-- `SubSolver.type_use_incr` -/
theorem type_use_incr (te : Typassign T) (x : Positive) (ty : T) (e e' : Typenv T)
    (h : typeUse e x ty = .OK e') (hs : Satisf te e') : Satisf te e := by
  unfold typeUse at h
  cases E : e.te_typ.get x with
  | none =>
    rw [E] at h; cases h
    exact satisf_set_incr te e.te_typ x _ e.te_sub (fun b hb => by rw [E] at hb; cases hb) hs
  | some b =>
    obtain ⟨lo, hi, s1⟩ := b
    rw [E] at h; simp only at h
    by_cases s2 : sub lo ty
    · rw [dif_pos s2] at h
      by_cases q : hi = glb hi ty
      · rw [if_pos q] at h; cases h; exact hs
      · rw [if_neg q] at h; cases h
        refine satisf_set_incr te e.te_typ x _ e.te_sub (fun b hb => ?_) hs
        rw [E] at hb; cases hb
        exact ⟨sub_refl _, glb_left _ _ _ s1 s2⟩
    · rw [dif_neg s2] at h; cases h

/-- `SubSolver.type_use_sound` -/
theorem type_use_sound (te : Typassign T) (x : Positive) (ty : T) (e e' : Typenv T)
    (h : typeUse e x ty = .OK e') (hs : Satisf te e') : sub (te x) ty := by
  obtain ⟨P, _⟩ := hs
  unfold typeUse at h
  cases E : e.te_typ.get x with
  | none =>
    rw [E] at h; cases h
    exact (P x _ (PTree.gss _ _ _)).2
  | some b =>
    obtain ⟨lo, hi, s1⟩ := b
    rw [E] at h; simp only at h
    by_cases s2 : sub lo ty
    · rw [dif_pos s2] at h
      by_cases q : hi = glb hi ty
      · rw [if_pos q] at h; cases h
        refine sub_trans _ hi _ (P x _ E).2 ?_
        rw [q]; exact glb_right _ _ _ s1 s2
      · rw [if_neg q] at h; cases h
        exact sub_trans _ _ _ (P x _ (PTree.gss _ _ _)).2 (glb_right _ _ _ s1 s2)
    · rw [dif_neg s2] at h; cases h

/-- `SubSolver.type_uses_incr` -/
theorem type_uses_incr (te : Typassign T) :
    ∀ (xl : List Positive) (tyl : List T) (e e' : Typenv T),
    typeUses e xl tyl = .OK e' → Satisf te e' → Satisf te e
  | [], [], e, e', h, hs => by simp only [typeUses, Res.OK.injEq] at h; subst h; exact hs
  | x :: xl, ty :: tyl, e, e', h, hs => by
    simp only [typeUses] at h
    split at h
    · next e1 h1 => exact type_use_incr te x ty e e1 h1 (type_uses_incr te xl tyl e1 e' h hs)
    · cases h
  | [], _ :: _, _, _, h, _ => by simp [typeUses] at h
  | _ :: _, [], _, _, h, _ => by simp [typeUses] at h

/-- `SubSolver.type_uses_sound` -/
theorem type_uses_sound (te : Typassign T) :
    ∀ (xl : List Positive) (tyl : List T) (e e' : Typenv T),
    typeUses e xl tyl = .OK e' → Satisf te e' → ListForall2 sub (xl.map te) tyl
  | [], [], _, _, _, _ => .nil
  | x :: xl, ty :: tyl, e, e', h, hs => by
    simp only [typeUses] at h
    split at h
    · next e1 h1 =>
      exact .cons (type_use_sound te x ty e e1 h1 (type_uses_incr te xl tyl e1 e' h hs))
        (type_uses_sound te xl tyl e1 e' h hs)
    · cases h
  | [], _ :: _, _, _, h, _ => by simp [typeUses] at h
  | _ :: _, [], _, _, h, _ => by simp [typeUses] at h

/-- `SubSolver.type_move_incr` -/
theorem type_move_incr (te : Typassign T) (e : Typenv T) (r1 r2 : Positive) (e' : Typenv T)
    (changed : Bool) (h : typeMove e r1 r2 = .OK (changed, e')) (hs : Satisf te e') :
    Satisf te e := by
  unfold typeMove at h
  by_cases hne : r1 = r2
  · rw [if_pos hne] at h; cases h; exact hs
  rw [if_neg hne] at h
  cases E1 : e.te_typ.get r1 with
  | none =>
    cases E2 : e.te_typ.get r2 with
    | none =>
      rw [E1, E2] at h; cases h
      exact satisf_sub_incr te _ _ _ hs
    | some b2 =>
      rw [E1, E2] at h; cases h
      have hs' : Satisf te ⟨e.te_typ.set r1 ⟨low_bound b2.hi, b2.hi, low_bound_sub b2.hi⟩,
          e.te_sub⟩ := by
        split at hs
        · exact hs
        · exact satisf_sub_incr te _ _ _ hs
      exact satisf_set_incr te _ _ _ _ (fun b hb => by rw [E1] at hb; cases hb) hs'
  | some b1 =>
    cases E2 : e.te_typ.get r2 with
    | none =>
      rw [E1, E2] at h; cases h
      have hs' : Satisf te ⟨e.te_typ.set r2 ⟨b1.lo, high_bound b1.lo, high_bound_sub b1.lo⟩,
          e.te_sub⟩ := by
        split at hs
        · exact hs
        · exact satisf_sub_incr te _ _ _ hs
      exact satisf_set_incr te _ _ _ _ (fun b hb => by rw [E2] at hb; cases hb) hs'
    | some b2 =>
      rw [E1, E2] at h
      change typeMoveBoth e r1 r2 b1 b2 = _ at h
      unfold typeMoveBoth at h
      by_cases hs1 : sub b1.hi b2.lo
      · rw [if_pos hs1] at h; cases h; exact hs
      rw [if_neg hs1] at h
      have s : sub b1.lo b2.hi := by
        by_cases s : sub b1.lo b2.hi
        · exact s
        · rw [dif_neg s] at h; cases h
      rw [dif_pos s] at h
      simp only at h
      have H1 : ∀ b, e.te_typ.get r1 = some b →
          sub b.lo b1.lo ∧ sub (glb b1.hi b2.hi) b.hi := fun b hb => by
        rw [E1] at hb; cases hb; exact ⟨sub_refl _, glb_left _ _ _ b1.SUB s⟩
      have H2 : ∀ b, e.te_typ.get r2 = some b →
          sub b.lo (lub b1.lo b2.lo) ∧ sub b2.hi b.hi := fun b hb => by
        rw [E2] at hb; cases hb; exact ⟨lub_right _ _ _ s b2.SUB, sub_refl _⟩
      by_cases q1 : b2.lo = lub b1.lo b2.lo <;> by_cases q2 : b1.hi = glb b1.hi b2.hi
      · rw [if_pos q1, if_pos q2] at h; cases h
        exact satisf_sub_incr te _ _ _ hs
      · rw [if_pos q1, if_neg q2] at h; cases h
        exact satisf_set_incr te _ _ _ _ H1 (satisf_sub_incr te _ _ _ hs)
      · rw [if_neg q1, if_pos q2] at h; cases h
        exact satisf_set_incr te _ _ _ _ H2 (satisf_sub_incr te _ _ _ hs)
      · rw [if_neg q1, if_neg q2] at h; cases h
        refine satisf_set_incr te _ _ _ _ H1 (satisf_set_incr te _ _ _ _ (fun b hb => ?_)
          (satisf_sub_incr te _ _ _ hs))
        rw [PTree.gso _ _ _ _ hne] at hb
        exact H2 b hb

/-- `SubSolver.type_move_sound` -/
theorem type_move_sound (te : Typassign T) (e : Typenv T) (r1 r2 : Positive) (e' : Typenv T)
    (changed : Bool) (h : typeMove e r1 r2 = .OK (changed, e')) (hs : Satisf te e') :
    sub (te r1) (te r2) := by
  obtain ⟨P, Q⟩ := hs
  unfold typeMove at h
  by_cases hne : r1 = r2
  · subst hne; exact sub_refl _
  rw [if_neg hne] at h
  cases E1 : e.te_typ.get r1 with
  | none =>
    cases E2 : e.te_typ.get r2 with
    | none =>
      rw [E1, E2] at h; cases h
      exact Q r1 r2 (by simp)
    | some b2 =>
      rw [E1, E2] at h; cases h
      by_cases hb : sub b2.hi b2.lo
      · have A := (P r1 _ (PTree.gss _ _ _)).2
        have B := (P r2 b2 (by rw [PTree.gso _ _ _ _ hne]; exact E2)).1
        exact sub_trans _ _ _ A (sub_trans _ _ _ hb B)
      · simp only [hb, if_false] at Q
        exact Q r1 r2 (by simp)
  | some b1 =>
    cases E2 : e.te_typ.get r2 with
    | none =>
      rw [E1, E2] at h; cases h
      by_cases hb : sub b1.hi b1.lo
      · have A := (P r1 b1 (by rw [PTree.gso _ _ _ _ (Ne.symm hne)]; exact E1)).2
        have B := (P r2 _ (PTree.gss _ _ _)).1
        exact sub_trans _ _ _ A (sub_trans _ _ _ hb B)
      · simp only [hb, if_false] at Q
        exact Q r1 r2 (by simp)
    | some b2 =>
      rw [E1, E2] at h
      change typeMoveBoth e r1 r2 b1 b2 = _ at h
      unfold typeMoveBoth at h
      by_cases hs1 : sub b1.hi b2.lo
      · rw [if_pos hs1] at h; cases h
        exact sub_trans _ _ _ (P r1 b1 E1).2 (sub_trans _ _ _ hs1 (P r2 b2 E2).1)
      rw [if_neg hs1] at h
      have s : sub b1.lo b2.hi := by
        by_cases s : sub b1.lo b2.hi
        · exact s
        · rw [dif_neg s] at h; cases h
      rw [dif_pos s] at h
      simp only at h
      by_cases q1 : b2.lo = lub b1.lo b2.lo <;> by_cases q2 : b1.hi = glb b1.hi b2.hi
      · rw [if_pos q1, if_pos q2] at h; cases h; exact Q r1 r2 (by simp)
      · rw [if_pos q1, if_neg q2] at h; cases h; exact Q r1 r2 (by simp)
      · rw [if_neg q1, if_pos q2] at h; cases h; exact Q r1 r2 (by simp)
      · rw [if_neg q1, if_neg q2] at h; cases h; exact Q r1 r2 (by simp)

/-- `SubSolver.solve_rec_incr` -/
theorem solve_rec_incr (te : Typassign T) :
    ∀ (q : List Constraint) (e : Typenv T) (changed : Bool) (e' : Typenv T) (changed' : Bool),
    solveRec e changed q = .OK (e', changed') → Satisf te e' → Satisf te e
  | [], e, changed, e', changed', h, hs => by
    simp only [solveRec, Res.OK.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hs
  | (r1, r2) :: q, e, changed, e', changed', h, hs => by
    simp only [solveRec] at h
    split at h
    · next c1 e1 hm =>
      exact type_move_incr te e r1 r2 e1 c1 hm (solve_rec_incr te q e1 _ e' changed' h hs)
    · cases h

/-- `SubSolver.solve_rec_sound` -/
theorem solve_rec_sound (te : Typassign T) (r1 r2 : Positive) :
    ∀ (q : List Constraint) (e : Typenv T) (changed : Bool) (e' : Typenv T) (changed' : Bool),
    solveRec e changed q = .OK (e', changed') → (r1, r2) ∈ q → Satisf te e' →
    sub (te r1) (te r2)
  | [], _, _, _, _, _, hin, _ => by cases hin
  | (r3, r4) :: q, e, changed, e', changed', h, hin, hs => by
    simp only [solveRec] at h
    split at h
    · next c1 e1 hm =>
      rcases List.mem_cons.1 hin with hin | hin
      · cases hin
        exact type_move_sound te e r1 r2 e1 c1 hm (solve_rec_incr te q e1 _ e' changed' h hs)
      · exact solve_rec_sound te r1 r2 q e1 _ e' changed' h hin hs
    · cases h

/-- `SubSolver.type_move_false` -/
theorem type_move_false (e : Typenv T) (r1 r2 : Positive) (e' : Typenv T)
    (h : typeMove e r1 r2 = .OK (false, e')) :
    e'.te_typ = e.te_typ ∧ sub (makeassign e r1) (makeassign e r2) := by
  unfold typeMove at h
  by_cases hne : r1 = r2
  · rw [if_pos hne] at h; cases h; subst hne; exact ⟨rfl, sub_refl _⟩
  rw [if_neg hne] at h
  unfold makeassign
  cases E1 : e.te_typ.get r1 with
  | none =>
    cases E2 : e.te_typ.get r2 with
    | none => rw [E1, E2] at h; cases h; exact ⟨rfl, sub_refl _⟩
    | some b2 => rw [E1, E2] at h; cases h
  | some b1 =>
    cases E2 : e.te_typ.get r2 with
    | none => rw [E1, E2] at h; cases h
    | some b2 =>
      rw [E1, E2] at h
      change typeMoveBoth e r1 r2 b1 b2 = _ at h
      simp only
      unfold typeMoveBoth at h
      by_cases hs1 : sub b1.hi b2.lo
      · rw [if_pos hs1] at h; cases h
        exact ⟨rfl, sub_trans _ _ _ b1.SUB hs1⟩
      rw [if_neg hs1] at h
      have s : sub b1.lo b2.hi := by
        by_cases s : sub b1.lo b2.hi
        · exact s
        · rw [dif_neg s] at h; cases h
      rw [dif_pos s] at h
      simp only at h
      by_cases q1 : b2.lo = lub b1.lo b2.lo <;> by_cases q2 : b1.hi = glb b1.hi b2.hi
      · rw [if_pos q1, if_pos q2] at h; cases h
        refine ⟨rfl, ?_⟩
        rw [q1]; exact lub_left _ _ _ s b2.SUB
      · rw [if_pos q1, if_neg q2] at h; cases h
      · rw [if_neg q1, if_pos q2] at h; cases h
      · rw [if_neg q1, if_neg q2] at h; cases h

/-- `SubSolver.solve_rec_false` -/
theorem solve_rec_false (r1 r2 : Positive) :
    ∀ (q : List Constraint) (e : Typenv T) (changed : Bool) (e' : Typenv T),
    solveRec e changed q = .OK (e', false) →
    changed = false ∧ ((r1, r2) ∈ q → sub (makeassign e r1) (makeassign e r2))
  | [], e, changed, e', h => by
    simp only [solveRec, Res.OK.injEq, Prod.mk.injEq] at h
    exact ⟨h.2, fun hin => nomatch hin⟩
  | (r3, r4) :: q, e, changed, e', h => by
    simp only [solveRec] at h
    split at h
    · next c1 e1 hm =>
      obtain ⟨P, Q⟩ := solve_rec_false r1 r2 q e1 _ e' h
      have hc : changed = false ∧ c1 = false := by
        cases changed <;> cases c1 <;> simp_all
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨U, V⟩ := type_move_false e r3 r4 e1 hm
      refine ⟨rfl, fun hin => ?_⟩
      rcases List.mem_cons.1 hin with hin | hin
      · cases hin; exact V
      · have := Q hin
        unfold makeassign at this ⊢
        rwa [U] at this
    · cases h

/-- `SubSolver.solve_constraints_incr` -/
theorem solve_constraints_incr (te : Typassign T) (e e' : Typenv T)
    (h : solveConstraints e = .OK e') (hs : Satisf te e') : Satisf te e := by
  rw [solveConstraints] at h
  split at h
  · cases h; exact hs
  · next e1 h1 =>
    have := solve_constraints_incr te e1 e' h hs
    obtain ⟨A, _⟩ := solve_rec_incr te _ _ _ _ _ h1 this
    exact ⟨A, fun x y hin => solve_rec_sound te x y _ _ _ _ _ h1 hin this⟩
  · cases h
termination_by weightTypenv e
decreasing_by
  have := weight_solve_rec _ _ _ _ _ ‹solveRec _ _ _ = Res.OK (_, true)›
  simp only [weightTypenv]
  simp at this
  omega

/-- `SubSolver.solve_constraints_sound` -/
theorem solve_constraints_sound (e e' : Typenv T) (h : solveConstraints e = .OK e') :
    Satisf (makeassign e') e' := by
  rw [solveConstraints] at h
  split at h
  · next e1 h1 =>
    cases h
    refine ⟨fun x b hx => ?_, fun x y hin => ?_⟩
    · simp only [makeassign, hx]; exact ⟨sub_refl _, b.SUB⟩
    · exact (solve_rec_false x y _ _ _ _ h1).2 hin
  · next e1 h1 => exact solve_constraints_sound e1 e' h
  · cases h
termination_by weightTypenv e
decreasing_by
  have := weight_solve_rec _ _ _ _ _ ‹solveRec _ _ _ = Res.OK (_, true)›
  simp only [weightTypenv]
  simp at this
  omega

/-- `SubSolver.solve_sound`: the assignment computed by `solve` satisfies the
constraints. -/
theorem solve_sound (e : Typenv T) (te : Typassign T) (h : solve e = .OK te) : Satisf te e := by
  unfold solve at h
  split at h
  · next e' h' =>
    cases h
    exact solve_constraints_incr _ e e' h' (solve_constraints_sound e e' h')
  · cases h

/-! ### Completeness -/

theorem satisf_set (te : Typassign T) (m : PTree (Bounds T)) (l : List Constraint) (x : Positive)
    (b : Bounds T) (h : Satisf te ⟨m, l⟩) (h1 : sub b.lo (te x)) (h2 : sub (te x) b.hi) :
    Satisf te ⟨m.set x b, l⟩ := by
  refine ⟨fun y b' hy => ?_, h.2⟩
  simp only at hy
  rw [PTree.gsspec] at hy
  split at hy
  · next hyx => cases hy; subst hyx; exact ⟨h1, h2⟩
  · exact h.1 y b' hy

theorem satisf_cons (te : Typassign T) (m : PTree (Bounds T)) (l : List Constraint)
    (x y : Positive) (h : Satisf te ⟨m, l⟩) (hxy : sub (te x) (te y)) :
    Satisf te ⟨m, (x, y) :: l⟩ := by
  refine ⟨h.1, fun a b hab => ?_⟩
  rcases List.mem_cons.1 hab with hab | hab
  · cases hab; exact hxy
  · exact h.2 a b hab

/-- `SubSolver.type_def_complete` -/
theorem type_def_complete (te : Typassign T) (e : Typenv T) (x : Positive) (ty : T)
    (hs : Satisf te e) (h : sub ty (te x)) :
    ∃ e', typeDef e x ty = .OK e' ∧ Satisf te e' := by
  unfold typeDef
  cases E : e.te_typ.get x with
  | none =>
    exact ⟨_, rfl, satisf_set te _ _ x _ hs h (high_bound_majorant _ _ h)⟩
  | some b =>
    obtain ⟨lo, hi, s1⟩ := b
    obtain ⟨L, U⟩ := hs.1 x _ E
    have s2 : sub ty hi := sub_trans _ _ _ h U
    simp only
    rw [dif_pos s2]
    by_cases q : lo = lub lo ty
    · rw [if_pos q]; exact ⟨_, rfl, hs⟩
    · rw [if_neg q]
      exact ⟨_, rfl, satisf_set te _ _ x _ hs (lub_min _ _ _ L h) U⟩

/-- `SubSolver.type_defs_complete` -/
theorem type_defs_complete (te : Typassign T) :
    ∀ (xl : List Positive) (tyl : List T) (e : Typenv T),
    Satisf te e → ListForall2 sub tyl (xl.map te) →
    ∃ e', typeDefs e xl tyl = .OK e' ∧ Satisf te e'
  | [], [], e, hs, _ => ⟨e, rfl, hs⟩
  | x :: xl, ty :: tyl, e, hs, hl => by
    cases hl with
    | cons h1 h2 =>
      obtain ⟨e1, P, Q⟩ := type_def_complete te e x ty hs h1
      obtain ⟨e2, U, V⟩ := type_defs_complete te xl tyl e1 Q h2
      exact ⟨e2, by simp only [typeDefs, P, U], V⟩
  | [], _ :: _, _, _, hl => nomatch hl
  | _ :: _, [], _, _, hl => nomatch hl

/-- `SubSolver.type_use_complete` -/
theorem type_use_complete (te : Typassign T) (e : Typenv T) (x : Positive) (ty : T)
    (hs : Satisf te e) (h : sub (te x) ty) :
    ∃ e', typeUse e x ty = .OK e' ∧ Satisf te e' := by
  unfold typeUse
  cases E : e.te_typ.get x with
  | none =>
    exact ⟨_, rfl, satisf_set te _ _ x _ hs (low_bound_minorant _ _ h) h⟩
  | some b =>
    obtain ⟨lo, hi, s1⟩ := b
    obtain ⟨L, U⟩ := hs.1 x _ E
    have s2 : sub lo ty := sub_trans _ _ _ L h
    simp only
    rw [dif_pos s2]
    by_cases q : hi = glb hi ty
    · rw [if_pos q]; exact ⟨_, rfl, hs⟩
    · rw [if_neg q]
      exact ⟨_, rfl, satisf_set te _ _ x _ hs L (glb_max _ _ _ U h)⟩

/-- `SubSolver.type_uses_complete` -/
theorem type_uses_complete (te : Typassign T) :
    ∀ (xl : List Positive) (tyl : List T) (e : Typenv T),
    Satisf te e → ListForall2 sub (xl.map te) tyl →
    ∃ e', typeUses e xl tyl = .OK e' ∧ Satisf te e'
  | [], [], e, hs, _ => ⟨e, rfl, hs⟩
  | x :: xl, ty :: tyl, e, hs, hl => by
    cases hl with
    | cons h1 h2 =>
      obtain ⟨e1, P, Q⟩ := type_use_complete te e x ty hs h1
      obtain ⟨e2, U, V⟩ := type_uses_complete te xl tyl e1 Q h2
      exact ⟨e2, by simp only [typeUses, P, U], V⟩
  | [], _ :: _, _, _, hl => nomatch hl
  | _ :: _, [], _, _, hl => nomatch hl

/-- `SubSolver.type_move_complete` -/
theorem type_move_complete (te : Typassign T) (e : Typenv T) (r1 r2 : Positive)
    (hs : Satisf te e) (h : sub (te r1) (te r2)) :
    ∃ changed e', typeMove e r1 r2 = .OK (changed, e') ∧ Satisf te e' := by
  have hs' : Satisf te ⟨e.te_typ, (r1, r2) :: e.te_sub⟩ := satisf_cons te _ _ _ _ hs h
  unfold typeMove
  by_cases hne : r1 = r2
  · rw [if_pos hne]; exact ⟨_, _, rfl, hs⟩
  rw [if_neg hne]
  cases E1 : e.te_typ.get r1 with
  | none =>
    cases E2 : e.te_typ.get r2 with
    | none => exact ⟨_, _, rfl, hs'⟩
    | some b2 =>
      obtain ⟨L2, U2⟩ := hs.1 r2 b2 E2
      refine ⟨_, _, rfl, ?_⟩
      have A := sub_trans _ _ _ h U2
      split
      · exact satisf_set te _ _ r1 _ hs (low_bound_minorant _ _ A) A
      · exact satisf_set te _ _ r1 _ hs' (low_bound_minorant _ _ A) A
  | some b1 =>
    cases E2 : e.te_typ.get r2 with
    | none =>
      obtain ⟨L1, U1⟩ := hs.1 r1 b1 E1
      refine ⟨_, _, rfl, ?_⟩
      have A := sub_trans _ _ _ L1 h
      split
      · exact satisf_set te _ _ r2 _ hs A (high_bound_majorant _ _ A)
      · exact satisf_set te _ _ r2 _ hs' A (high_bound_majorant _ _ A)
    | some b2 =>
      obtain ⟨L1, U1⟩ := hs.1 r1 b1 E1
      obtain ⟨L2, U2⟩ := hs.1 r2 b2 E2
      change ∃ changed e', typeMoveBoth e r1 r2 b1 b2 = _ ∧ _
      unfold typeMoveBoth
      by_cases hs1 : sub b1.hi b2.lo
      · rw [if_pos hs1]; exact ⟨_, _, rfl, hs⟩
      rw [if_neg hs1]
      have s : sub b1.lo b2.hi := sub_trans _ _ _ L1 (sub_trans _ _ _ h U2)
      rw [dif_pos s]
      simp only
      have N1 : sub (te r1) (glb b1.hi b2.hi) := glb_max _ _ _ U1 (sub_trans _ _ _ h U2)
      have N2 : sub (lub b1.lo b2.lo) (te r2) := lub_min _ _ _ (sub_trans _ _ _ L1 h) L2
      by_cases q1 : b2.lo = lub b1.lo b2.lo <;> by_cases q2 : b1.hi = glb b1.hi b2.hi
      · rw [if_pos q1, if_pos q2]; exact ⟨_, _, rfl, hs'⟩
      · rw [if_pos q1, if_neg q2]
        exact ⟨_, _, rfl, satisf_set te _ _ r1 _ hs' L1 N1⟩
      · rw [if_neg q1, if_pos q2]
        exact ⟨_, _, rfl, satisf_set te _ _ r2 _ hs' N2 U2⟩
      · rw [if_neg q1, if_neg q2]
        exact ⟨_, _, rfl, satisf_set te _ _ r2 _ (satisf_set te _ _ r1 _ hs' L1 N1) N2 U2⟩

/-- `SubSolver.solve_rec_complete` -/
theorem solve_rec_complete (te : Typassign T) :
    ∀ (q : List Constraint) (e : Typenv T) (changed : Bool),
    Satisf te e → (∀ r1 r2, (r1, r2) ∈ q → sub (te r1) (te r2)) →
    ∃ e' changed', solveRec e changed q = .OK (e', changed') ∧ Satisf te e'
  | [], e, changed, hs, _ => ⟨e, changed, rfl, hs⟩
  | (r1, r2) :: q, e, changed, hs, hq => by
    obtain ⟨c1, e1, A, B⟩ := type_move_complete te e r1 r2 hs (hq r1 r2 (by simp))
    obtain ⟨e', c', C, D⟩ := solve_rec_complete te q e1 (changed || c1) B
      (fun a b hab => hq a b (List.mem_cons_of_mem _ hab))
    exact ⟨e', c', by simp only [solveRec, A, C], D⟩

/-- `SubSolver.solve_constraints_complete` -/
theorem solve_constraints_complete (te : Typassign T) (e : Typenv T) (hs : Satisf te e) :
    ∃ e', solveConstraints e = .OK e' ∧ Satisf te e' := by
  obtain ⟨e1, c1, P, Q⟩ := solve_rec_complete te e.te_sub ⟨e.te_typ, []⟩ false
    ⟨hs.1, fun _ _ h => nomatch h⟩ hs.2
  rw [solveConstraints]
  split
  · exact ⟨e, rfl, hs⟩
  · next e2 h2 =>
    rw [P] at h2
    simp only [Res.OK.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact solve_constraints_complete te e1 Q
  · next m h2 => rw [P] at h2; cases h2
termination_by weightTypenv e
decreasing_by
  have := weight_solve_rec _ _ _ _ _ ‹solveRec _ _ _ = Res.OK (_, true)›
  simp only [weightTypenv]
  simp at this
  omega

/-- `SubSolver.solve_complete`: if the constraints have a solution, `solve`
succeeds. -/
theorem solve_complete (te : Typassign T) (e : Typenv T) (hs : Satisf te e) :
    ∃ te', solve e = .OK te' := by
  obtain ⟨e', P, _⟩ := solve_constraints_complete te e hs
  exact ⟨makeassign e', by simp only [solve, P]⟩

end SubSolver
end CC
