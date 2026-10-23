/-
  Port of VST's `progs/verif_ptr_compare.v`: the function `f` of
  `vst/progs/ptr_compare.c` (`return (p == q);`) meets its specification.

  VST's specification:

      DECLARE _f
       WITH p: val, q:val, sh: share
       PRE  [ tptr tint, tptr tint]
             PROP (sepalg.nonidentity sh)
             PARAMS (p; q)
             SEP(data_at sh tint (Vint Int.zero) p; data_at sh tint (Vint Int.zero) q)
       POST [ tint ]
              PROP()
              RETURN (Vint (if eq_dec p q then Int.one else Int.zero))
              SEP (data_at sh tint (Vint Int.zero) p; data_at sh tint (Vint Int.zero) q).

  The separation logic of `CCLib.logic` has no fractional shares: a byte has a
  single owner.  VST's precondition, which for `p = q` holds two halves of
  the same cell, is therefore stated as "`p` and `q` point to `int`s, a single
  one when `p = q`" (`TwoInts`).  The permission `perm` of the cells is
  arbitrary (VST's `nonidentity sh`: any non-empty share).

  The comparison is evaluated by `semBinop_eq_ptr` (`CCLib.logic.PtrCompare`):
  Clight compares pointers only when both are valid, which holds because the
  cells they point to are owned.
-/
import VST.progs.ptr_compare
import CCLib
open CC CC.Sep CC.HProp
open Ptr_compare

namespace VST.Verif.PtrCompare

/-- `data_at sh tint (Vint Int.zero) v` -/
def intZeroAt (perm : Permission) : Val → HProp
  | .Vptr b o => mapsto .Mint32 perm b (Integers.Ptrofs.unsigned o) (.Vint Integers.Int.zero)
  | _ => fun _ => False

/-- `data_at sh tint (Vint Int.zero) p * data_at sh tint (Vint Int.zero) q`,
    with a single cell when `p = q`. -/
def TwoInts (perm : Permission) (p q : Val) : HProp :=
  if p = q then intZeroAt perm p else intZeroAt perm p ∗ intZeroAt perm q

/-- `f_spec` -/
def fSpec (p q : Val) (perm : Permission) : Sep.FunSpec where
  tyargs := [tptr tint, tptr tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [p, q] ∧ TwoInts perm p q hp
  post := fun v hp =>
    v = .Vint (if p = q then Integers.Int.one else Integers.Int.zero) ∧ TwoInts perm p q hp
  measure := fun _ => 0

theorem intZeroAt_inv {perm : Permission} {v : Val} {h : Heap} (hv : intZeroAt perm v h) :
    ∃ b o c, v = .Vptr b o ∧ h b (Integers.Ptrofs.unsigned o) = some c := by
  match v, hv with
  | .Vptr b o, hv =>
    obtain ⟨c, hc⟩ := mapsto_owns hv
    exact ⟨b, o, c, rfl, hc⟩

/-- Under `TwoInts`, `p` and `q` are valid pointers. -/
theorem twoInts_valid {perm : Permission} {p q : Val} {hp : Heap} {m : Mem}
    (h : TwoInts perm p q hp) (hag : Heap.Agrees hp m) :
    ∃ b1 o1 b2 o2, p = .Vptr b1 o1 ∧ q = .Vptr b2 o2
      ∧ Mem.validPointer m b1 (Integers.Ptrofs.unsigned o1) = true
      ∧ Mem.validPointer m b2 (Integers.Ptrofs.unsigned o2) = true := by
  unfold TwoInts at h
  split at h
  · rename_i hpq
    subst hpq
    obtain ⟨b, o, c, rfl, hc⟩ := intZeroAt_inv h
    have hv := Heap.agrees_validPointer hag hc
    exact ⟨b, o, b, o, rfl, rfl, hv, hv⟩
  · obtain ⟨h1, h2, _, rfl, hp1, hp2⟩ := h
    obtain ⟨b1, o1, c1, rfl, hc1⟩ := intZeroAt_inv hp1
    obtain ⟨b2, o2, c2, rfl, hc2⟩ := intZeroAt_inv hp2
    obtain ⟨_, hc1'⟩ := Heap.union_owns_left (h2 := h2) hc1
    obtain ⟨_, hc2'⟩ := Heap.union_owns_right (h1 := h1) hc2
    exact ⟨b1, o1, b2, o2, rfl, rfl, Heap.agrees_validPointer hag hc1',
      Heap.agrees_validPointer hag hc2'⟩

/-- **`f` satisfies `f_spec`** (VST's `body_f`). -/
theorem f_satisfies (ge : CGenv) (p q : Val) (perm : Permission) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_f) (fSpec p q perm) [p, q] := by
  let L : TempEnv := ((createUndefTemps f_f.fn_temps).set _p p).set _q q
  refine satisfies_internal_noVars ge _ f_f _ _
    (fun e le hp => e = emptyEnv ∧ le = L ∧ TwoInts perm p q hp)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  refine Sep.triple_return ge _ f_f _ _ _ (fun e le hp m h hag => ?_)
  obtain ⟨rfl, rfl, hP⟩ := h
  obtain ⟨b1, o1, b2, o2, rfl, rfl, hv1, hv2⟩ := twoInts_valid hP hag
  refine ⟨_, _, m, hp,
    EvalExpr.Ebinop _ _ _ _ _ _ _
      (EvalExpr.Etempvar _ _ _ (by
        show PTree.get _p ((PTree.set _p _ _).set _q _) = _
        rw [PTree.gso _ _ _ _ (by decide), PTree.gss]))
      (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _))
      (semBinop_eq_ptr _ m b1 b2 o1 o2 tint tint noattr noattr hv1 hv2),
    semCast_int m _, freeList_emptyEnv _ _, ⟨rfl, hP⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩

end VST.Verif.PtrCompare
