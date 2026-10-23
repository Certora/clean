/-
  A solver for unification constraints — port of `common/Unityping.v`
  (the `UniSolver` functor): `constraint`, `typenv`, `initial`, `set`,
  `set_list`, `move`, `solve_rec`, the measure lemmas `length_move` and
  `length_solve_rec`, `solve_constraints` (defined by well-founded
  recursion on the number of pending equations, as in Rocq), `typassign`,
  `makeassign`, `solve`, `satisf`, with `satisf_initial`.

  The soundness and completeness lemmas (`solve_sound`,
  `solve_complete` and their auxiliaries), used by the proofs of the
  passes that call the solver, are in `CCLib.common.UnitypingSound`.

  Differences from Rocq: the module parameter `T : TYPE_ALGEBRA` is a type
  `T` with `DecidableEq` and a default element `dflt`; error messages are
  plain strings.
-/
import CCLib.lib.MapsTheory
import CCLib.cfrontend.Ctypes

namespace CC
namespace UniSolver

variable {T : Type} [DecidableEq T]

/-- `UniSolver.constraint` -/
abbrev Constraint := Positive × Positive

/-- `UniSolver.typenv` -/
structure Typenv (T : Type) where
  te_typ : PTree T
  te_equ : List Constraint

/-- `UniSolver.initial` -/
def initial : Typenv T := ⟨PTree.empty, []⟩

/-- `UniSolver.set`: add the constraint `T(x) = ty`. -/
def set (e : Typenv T) (x : Positive) (ty : T) : Res (Typenv T) :=
  match e.te_typ.get x with
  | none => .OK ⟨e.te_typ.set x ty, e.te_equ⟩
  | some ty' => if ty = ty' then .OK e else .Error "bad definition/use of variable"

/-- `UniSolver.set_list` -/
def setList : Typenv T → List Positive → List T → Res (Typenv T)
  | e, [], [] => .OK e
  | e, r1 :: rs, ty1 :: tys =>
      match set e r1 ty1 with
      | .OK e1 => setList e1 rs tys
      | .Error m => .Error m
  | _, _, _ => .Error "arity mismatch"

/-- `UniSolver.move`: add the constraint `T(r1) = T(r2)`. -/
def move (e : Typenv T) (r1 r2 : Positive) : Res (Bool × Typenv T) :=
  if r1 = r2 then .OK (false, e) else
  match e.te_typ.get r1, e.te_typ.get r2 with
  | none, none => .OK (false, ⟨e.te_typ, (r1, r2) :: e.te_equ⟩)
  | some ty1, none => .OK (true, ⟨e.te_typ.set r2 ty1, e.te_equ⟩)
  | none, some ty2 => .OK (true, ⟨e.te_typ.set r1 ty2, e.te_equ⟩)
  | some ty1, some ty2 =>
      if ty1 = ty2 then .OK (false, e) else .Error "ill-typed move"

/-- `UniSolver.solve_rec` -/
def solveRec : Typenv T → Bool → List Constraint → Res (Typenv T × Bool)
  | e, changed, [] => .OK (e, changed)
  | e, changed, (r1, r2) :: q' =>
      match move e r1 r2 with
      | .OK (changed1, e1) => solveRec e1 (changed || changed1) q'
      | .Error m => .Error m

/-- `UniSolver.length_move` -/
theorem length_move (e : Typenv T) (r1 r2 : Positive) (changed : Bool) (e' : Typenv T)
    (h : move e r1 r2 = .OK (changed, e')) :
    e'.te_equ.length + (if changed then 1 else 0) ≤ e.te_equ.length + 1 := by
  unfold move at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · cases h; simp
    · cases h; simp
    · split at h
      · cases h; simp
      · cases h

/-- `UniSolver.length_solve_rec` -/
theorem length_solveRec :
    ∀ (q : List Constraint) (e : Typenv T) (ch : Bool) (e' : Typenv T) (ch' : Bool),
      solveRec e ch q = .OK (e', ch') →
      e'.te_equ.length + (if ch' && !ch then 1 else 0) ≤ e.te_equ.length + q.length
  | [], e, ch, e', ch', h => by
    simp only [solveRec, Res.OK.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases ch <;> simp
  | (r1, r2) :: q, e, ch, e', ch', h => by
    simp only [solveRec] at h
    split at h
    · next ch0 e0 hm =>
      have A := length_solveRec q e0 (ch || ch0) e' ch' h
      have B := length_move e r1 r2 ch0 e0 hm
      simp only [List.length_cons]
      cases ch' <;> cases ch <;> cases ch0 <;> simp at A B ⊢ <;> omega
    · cases h

/-- `UniSolver.weight_typenv` -/
def weightTypenv (e : Typenv T) : Nat := e.te_equ.length

/-- `UniSolver.solve_constraints` -/
def solveConstraints (e : Typenv T) : Res (Typenv T) :=
  match h : solveRec ⟨e.te_typ, []⟩ false e.te_equ with
  | .OK (_, false) => .OK e
  | .OK (e', true) =>
      have := length_solveRec e.te_equ ⟨e.te_typ, []⟩ false e' true h
      solveConstraints e'
  | .Error m => .Error m
termination_by weightTypenv e
decreasing_by
  simp only [weightTypenv]
  simp at this
  omega

/-- `UniSolver.typassign` -/
abbrev Typassign (T : Type) := Positive → T

/-- `UniSolver.makeassign` -/
def makeassign (dflt : T) (e : Typenv T) : Typassign T :=
  fun x => match e.te_typ.get x with
    | some ty => ty
    | none => dflt

/-- `UniSolver.solve` -/
def solve (dflt : T) (e : Typenv T) : Res (Typassign T) :=
  match solveConstraints e with
  | .OK e' => .OK (makeassign dflt e')
  | .Error m => .Error m

/-- `UniSolver.satisf` -/
def Satisf (te : Typassign T) (e : Typenv T) : Prop :=
  (∀ x ty, e.te_typ.get x = some ty → te x = ty) ∧ (∀ x y, (x, y) ∈ e.te_equ → te x = te y)

omit [DecidableEq T] in
/-- `UniSolver.satisf_initial` -/
theorem satisf_initial (te : Typassign T) : Satisf te (initial : Typenv T) :=
  ⟨fun x ty h => by simp [initial, PTree.empty] at h, fun _ _ h => by cases h⟩

end UniSolver
end CC
