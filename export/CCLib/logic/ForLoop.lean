/-
  The counted `for` loop — the rule behind VST's `forward_for_simple_bound`.

  `for (i = …; i < n; i++) body` is compiled by `clightgen` to

      Sloop (Ssequence (Sifthenelse (i < n) Sskip Sbreak) body) incr

  with `i` and `n` `int` temporaries.  `triple_for_lt` proves such a loop from
  an invariant `Inv j` (`j` iterations done, `i = j`, `n = N`): the body takes
  `Inv j` to `Mid j` for `j < N`, the increment takes `Mid j` to `Inv (j+1)`,
  and the loop ends in `Inv N`.  Termination is built in (the measure is
  `N - j`), as everywhere in `CCLib.logic`.
-/
import CCLib.logic.Tactics
import CCLib.logic.HoareArray

namespace CC
namespace Sep

open HProp

/-- The loop guard `i < n` of a counted loop. -/
def forGuard (i n : Ident) : Expr := .Ebinop .Olt (.Etempvar i tint) (.Etempvar n tint) tint

/-- The counted loop `for (; i < n; incr) body`. -/
def forLoop (i n : Ident) (body incr : Stmt) : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse (forGuard i n) .Sskip .Sbreak) body) incr

/-- `i + 1` on an `int` counter. -/
theorem eval_incr {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} (i : Ident) (j : Nat)
    (hi : le.get i = some (.Vint (Integers.Int.repr j))) :
    EvalExpr ge e le m (.Ebinop .Oadd (.Etempvar i tint) (.Econst_int (Integers.Int.repr 1) tint)
      tint) (.Vint (Integers.Int.repr ((j + 1 : Nat) : _root_.Int))) := by
  refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar i tint _ hi)
    (EvalExpr.Econst_int _ tint) ?_
  simp only [typeof]
  rw [semBinop_add_int, repr_add]
  simp

/-- The guard `i < n` of a counted loop, at `i = j ≤ N = n`. -/
theorem eval_forGuard {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} (i n : Ident) (j N : Nat)
    (hN : (N : _root_.Int) < 2147483648) (hj : j ≤ N)
    (hi : le.get i = some (.Vint (Integers.Int.repr j)))
    (hn : le.get n = some (.Vint (Integers.Int.repr N))) :
    EvalExpr ge e le m (forGuard i n) (Val.ofBool (decide (j < N))) := by
  have h : EvalExpr ge e le m (forGuard i n)
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr j) (Integers.Int.repr N))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar i tint _ hi) (EvalExpr.Etempvar n tint _ hn)
      (semBinop_lt_int _ _ _ _)
  rw [lt_repr (j : _root_.Int) (N : _root_.Int) (by omega) (by omega) (by omega) hN] at h
  simpa using h

section
variable (ge : CGenv) (fe : EntryRel) (f : Function)

/-- **A counted loop with any guard.**  `Sloop (Ssequence (if (g) skip else
    break) body) incr`, where the guard `g` (of type `int`) evaluates to
    `j < N` in `Inv j`: `for (i = …; i < n - k; i++)` and the like.  The loop,
    started in `Inv j` (`j ≤ N`), ends in `Inv N`. -/
theorem triple_for_guard (g : Expr) (hgty : typeof g = tint) (N : Nat)
    (Inv Mid : Nat → Assn) (body incr : Stmt) (Ret : Val → HProp)
    (hguard : ∀ j e le hp m, Inv j e le hp → j ≤ N →
      EvalExpr ge e le m g (Val.ofBool (decide (j < N))))
    (hbody : ∀ j, j < N → Triple ge fe f (Inv j) body
      { normal := Mid j, brk := Assn.no, cont := Mid j, ret := Ret })
    (hincr : ∀ j, j < N → Triple ge fe f (Mid j) incr (.only (Inv (j + 1)))) :
    ∀ j, j ≤ N → Triple ge fe f (Inv j)
      (.Sloop (.Ssequence (.Sifthenelse g .Sskip .Sbreak) body) incr)
      { normal := Inv N, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  intro j0 hj0
  let I : Nat → Assn := fun k e le hp => ∃ j, Inv j e le hp ∧ j ≤ N ∧ N - j = k
  let J : Nat → Assn := fun k e le hp => ∃ j, Mid j e le hp ∧ j < N ∧ N - j = k
  refine Sep.triple_conseq ge fe f
    (Sep.triple_loop ge fe f { normal := Inv N, brk := Assn.no, cont := Assn.no, ret := Ret }
      I J _ _ (fun k => ?_) (fun k => ?_) (N - j0))
    (fun e le hp h => ⟨j0, h, hj0, rfl⟩) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ x => x) (fun _ _ x => x)
  · -- the guard, then the body
    refine Sep.triple_seq ge fe f _ (fun e le hp => ∃ j, Inv j e le hp ∧ j < N ∧ N - j = k)
      _ _ _ ?_ ?_
    · refine Sep.triple_exists ge fe f _ _ _ (fun j => ?_)
      by_cases hjN : j < N
      · refine Sep.triple_if_true ge fe f _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
        · obtain ⟨hI, hj, _⟩ := hP
          refine ⟨_, hguard j e le hp m hI hj, ?_⟩
          simpa [hjN, hgty] using boolVal_ofBool_int m true
        · refine Sep.triple_fallthrough ge fe f _ _ _ _ (Sep.triple_skip ge fe f _)
            (fun e le hp h => ?_)
          obtain ⟨hI, _, hk⟩ := h
          exact ⟨j, hI, hjN, hk⟩
      · refine Sep.triple_if_false ge fe f _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
        · obtain ⟨hI, hj, _⟩ := hP
          refine ⟨_, hguard j e le hp m hI hj, ?_⟩
          simpa [hjN, hgty] using boolVal_ofBool_int m false
        · refine Sep.triple_conseq ge fe f (Sep.triple_break ge fe f _) (fun _ _ _ x => x)
            (fun _ _ _ x => x.elim) (fun e le hp h => ?_) (fun _ _ _ x => x.elim)
            (fun _ _ x => x.elim)
          obtain ⟨hI, hj, _⟩ := h
          have : j = N := by omega
          subst this
          exact hI
    · refine Sep.triple_exists ge fe f _ _ _ (fun j => ?_)
      refine Sep.triple_conseq ge fe f (P := fun e le hp => Inv j e le hp ∧ j < N ∧ N - j = k)
        (?_ : Triple ge fe f _ body _) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
      intro kk e le hp hf m hd hag ⟨hI, hj, hk⟩
      obtain ⟨o, hp', hs, hd', hag', hR⟩ := hbody j hj kk e le hp hf m hd hag hI
      refine ⟨o, hp', hs, hd', hag', ?_⟩
      cases o with
      | Normal _ _ _ => exact ⟨j, hR, hj, hk⟩
      | Break _ _ _ => exact hR.elim
      | Continue _ _ _ => exact ⟨j, hR, hj, hk⟩
      | Return _ _ => exact hR
      | Goto _ _ _ _ => exact hR
  · -- the increment
    refine Sep.triple_exists ge fe f _ _ _ (fun j => ?_)
    intro kk e le hp hf m hd hag ⟨hM, hj, hk⟩
    obtain ⟨o, hp', hs, hd', hag', hR⟩ := hincr j hj kk e le hp hf m hd hag hM
    refine ⟨o, hp', hs, hd', hag', ?_⟩
    cases o with
    | Normal _ _ _ => exact ⟨N - (j + 1), by omega, j + 1, hR, by omega, rfl⟩
    | Break _ _ _ => exact hR.elim
    | Continue _ _ _ => exact hR
    | Return _ _ => exact hR.elim
    | Goto _ _ _ _ => exact hR

/-- A pure conjunct of a precondition may be assumed. -/
theorem triple_pure_pre {φ : Prop} {P : Assn} {s : Stmt} {R : ExitConds}
    (h : φ → Triple ge fe f P s R) : Triple ge fe f (fun e le hp => φ ∧ P e le hp) s R := by
  intro k e le hp hf m hd hag hP
  exact h hP.1 k e le hp hf m hd hag hP.2

/-- `triple_for_guard` for a loop whose counter starts at `j0`: the body and
    the increment only need to be correct from `j0` on. -/
theorem triple_for_guard_from (g : Expr) (hgty : typeof g = tint) (j0 N : Nat) (hj0 : j0 ≤ N)
    (Inv Mid : Nat → Assn) (body incr : Stmt) (Ret : Val → HProp)
    (hguard : ∀ j e le hp m, Inv j e le hp → j0 ≤ j → j ≤ N →
      EvalExpr ge e le m g (Val.ofBool (decide (j < N))))
    (hbody : ∀ j, j0 ≤ j → j < N → Triple ge fe f (Inv j) body
      { normal := Mid j, brk := Assn.no, cont := Mid j, ret := Ret })
    (hincr : ∀ j, j0 ≤ j → j < N → Triple ge fe f (Mid j) incr (.only (Inv (j + 1)))) :
    Triple ge fe f (Inv j0)
      (.Sloop (.Ssequence (.Sifthenelse g .Sskip .Sbreak) body) incr)
      { normal := Inv N, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  refine Sep.triple_conseq ge fe f
    (triple_for_guard ge fe f g hgty N (fun j e le hp => j0 ≤ j ∧ Inv j e le hp)
      (fun j e le hp => j0 ≤ j ∧ Mid j e le hp) body incr Ret
      (fun j e le hp m hI hj => hguard j e le hp m hI.2 hI.1 hj)
      (fun j hj => triple_pure_pre ge fe f (fun h0 =>
        Sep.triple_conseq ge fe f (hbody j h0 hj) (fun _ _ _ x => x) (fun _ _ _ x => ⟨h0, x⟩)
          (fun _ _ _ x => x) (fun _ _ _ x => ⟨h0, x⟩) (fun _ _ x => x)))
      (fun j hj => triple_pure_pre ge fe f (fun h0 =>
        Sep.triple_conseq ge fe f (hincr j h0 hj) (fun _ _ _ x => x)
          (fun _ _ _ x => ⟨by omega, x⟩) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)))
      j0 hj0)
    (fun _ _ _ x => ⟨Nat.le_refl _, x⟩) (fun _ _ _ x => x.2) (fun _ _ _ x => x)
    (fun _ _ _ x => x) (fun _ _ x => x)

/-- **The counted `for` loop.**  `Inv j` fixes `i = j` and `n = N`; the loop,
    started in `Inv j` (`j ≤ N`), ends in `Inv N`. -/
theorem triple_for_lt (i n : Ident) (N : Nat) (hN : (N : _root_.Int) < 2147483648)
    (Inv Mid : Nat → Assn) (body incr : Stmt) (Ret : Val → HProp)
    (hi : ∀ j e le hp, Inv j e le hp → le.get i = some (.Vint (Integers.Int.repr j)))
    (hn : ∀ j e le hp, Inv j e le hp → le.get n = some (.Vint (Integers.Int.repr N)))
    (hbody : ∀ j, j < N → Triple ge fe f (Inv j) body
      { normal := Mid j, brk := Assn.no, cont := Mid j, ret := Ret })
    (hincr : ∀ j, j < N → Triple ge fe f (Mid j) incr (.only (Inv (j + 1)))) :
    ∀ j, j ≤ N → Triple ge fe f (Inv j) (forLoop i n body incr)
      { normal := Inv N, brk := Assn.no, cont := Assn.no, ret := Ret } :=
  triple_for_guard ge fe f (forGuard i n) rfl N Inv Mid body incr Ret
    (fun j e le hp _ hI hj => eval_forGuard i n j N hN hj (hi j e le hp hI) (hn j e le hp hI))
    hbody hincr

end

end Sep
end CC
