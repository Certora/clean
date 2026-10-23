/-
  Proof automation for the separation logic — Phase 7.6.

  ## What is automated, and how

  The plan expected `Lean.Elab.Tactic` metaprogramming here (no Mathlib to lean
  on).  It turned out mostly unnecessary.  The two jobs are:

  * **Entailment between `∗`-chains.**  Handled by `simp` rather than a custom
    solver: with the *AC trio* — associativity, commutativity and
    left-commutativity as `Eq`s — `simp`'s ordered rewriting sorts a chain into a
    canonical order, so cancellation is `simp only [sep_norm]` followed by
    reflexivity.  That is `sep_cancel` below.  It is far more robust than a
    hand-rolled matcher, and it reorders arbitrarily deep chains.
    The mathematical content is also stated directly, as `sepList_perm`.

  * **Stepping forward over a statement.**  Handled by giving the rules a
    *forward* shape — postcondition computed from the precondition rather than
    guessed — so that `refine` alone makes progress and the intermediate
    assertion of a sequence is fixed by unification.  `triple_set_fwd` is the
    model; `triple_if_true`/`triple_if_false` were already forward-shaped.

  ## What is not automated

  There is no attempt at VST's `forward` in full: no automatic frame inference
  (deciding *which* conjuncts a statement needs), no entailment checking modulo
  pure side conditions, and no `forward_loop` that invents an invariant.  Loop
  invariants and measures are supplied by hand, as they are in VST.  The tactics
  here remove the mechanical bookkeeping, not the thinking.
-/
import CCLib.logic.Funspec

namespace CC

namespace Sep
open HProp

/-! ## Forward-shaped rules

The postcondition is computed, so `refine` can apply these without the caller
supplying the intermediate assertion. -/

/-- Forward form of `triple_set`.  The postcondition records that the temporaries
    are the old ones with `id` updated — no guess required. -/
theorem triple_set_fwd (ge fe f) {P : Assn} {id : Ident} {a : Expr}
    {vf : Env → TempEnv → Val}
    (h : ∀ e le hp m, P e le hp → Heap.Agrees hp m → EvalExpr ge e le m a (vf e le)) :
    Triple ge fe f P (.Sset id a)
      (.only (fun e le hp => ∃ le0, le = le0.set id (vf e le0) ∧ P e le0 hp)) := by
  refine triple_set ge fe f P _ id a (fun e le hp m hP hag => ?_)
  exact ⟨vf e le, h e le hp m hP hag, ⟨le, rfl, hP⟩⟩

/-- Sequencing where the first statement only falls through — the common case,
    packaged so that solving the first premise fixes the intermediate assertion
    by unification. -/
theorem triple_seq_only (ge fe f) {P Q : Assn} {R : ExitConds} {s1 s2 : Stmt}
    (h1 : Triple ge fe f P s1 (.only Q)) (h2 : Triple ge fe f Q s2 R) :
    Triple ge fe f P (.Ssequence s1 s2) R :=
  triple_seq ge fe f P Q R s1 s2
    (triple_conseq ge fe f h1 (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
      (fun _ _ x => False.elim x)) h2

/-- Consequence on the precondition only — the shape a forward step needs when
    the computed postcondition has to be massaged before the next step. -/
theorem triple_pre (ge fe f) {P P' : Assn} {s : Stmt} {R : ExitConds}
    (hP : ∀ e le hp, P' e le hp → P e le hp) (h : Triple ge fe f P s R) :
    Triple ge fe f P' s R :=
  triple_conseq ge fe f h hP (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ x => x) (fun _ _ x => x)

/-- Case split on a disjunctive precondition. -/
theorem triple_or (ge fe f) {P1 P2 : Assn} {s : Stmt} {R : ExitConds}
    (h1 : Triple ge fe f P1 s R) (h2 : Triple ge fe f P2 s R) :
    Triple ge fe f (fun e le hp => P1 e le hp ∨ P2 e le hp) s R := by
  intro k e le hp hf m hd hag hP
  rcases hP with h | h
  · exact h1 k e le hp hf m hd hag h
  · exact h2 k e le hp hf m hd hag h

end Sep

/-! ## Tactics -/

namespace Tactic

-- The AC lemma list.  A `register_simp_attr` set would let users extend this,
-- but it needs `import Lean` in a library file; an explicit list costs nothing
-- and keeps `CCLib` free of the Lean frontend.

/-- Sort both sides of a `∗`-goal into canonical order and close it.  Works on an
    `Eq` between `HProp`s and on an entailment `P ⊢ Q`. -/
macro "sep_cancel" : tactic =>
  `(tactic| (simp only [CC.HProp.sep_assoc_eq, CC.HProp.sep_comm_eq,
                        CC.HProp.sep_left_comm_eq, CC.HProp.sep_emp_eq,
                        CC.HProp.emp_sep_eq];
             first
             | rfl
             | exact CC.HProp.entails_refl _
             | skip))

/-- Normalize `∗`-chains without trying to close the goal. -/
macro "sep_normalize" : tactic =>
  `(tactic| simp only [CC.HProp.sep_assoc_eq, CC.HProp.sep_comm_eq,
                       CC.HProp.sep_left_comm_eq, CC.HProp.sep_emp_eq,
                       CC.HProp.emp_sep_eq])

/-- Step over `Sset` at the head of a sequence, computing the postcondition.

    The assigned value has to be given, because it is exactly what cannot be
    inferred: the intermediate assertion of the sequence is this rule's *output*,
    so there is nothing in the goal to unify it against.  (For a *trailing* `Sset`
    the postcondition is in the goal, so `forward_set_last` needs no argument.) -/
macro "forward_set" v:term : tactic =>
  `(tactic| refine CC.Sep.triple_seq_only _ _ _
              (CC.Sep.triple_set_fwd (vf := $v) _ _ _ ?_) ?_)

/-- Step over a trailing `Sset` (not followed by another statement). -/
macro "forward_set_last" : tactic =>
  `(tactic| refine CC.Sep.triple_set_fwd _ _ _ ?_)

end Tactic
end CC
