/-
  Divergence of Clight programs, for the program proofs.

  The Hoare triples of `CCLib.logic` are total-correctness triples: they say
  nothing about the runs that never return.  To show that a run diverges, the
  program proofs build a cycle of non-empty silent runs and conclude with
  `Smallstep.forever_silent_of_plus` (`CCLib.common.SmallstepForever`).  The
  runs are written as `Steps (SStep ge fe)` (the silent multi-step relation of
  the triples); the lemmas below turn them into the generic `Star` / `Plus` of
  `CCLib.common.Smallstep`.
-/
import CCLib.logic.Hoare
import CCLib.common.SmallstepForever

namespace CC

/-- A silent multi-step run is a `star` run with the empty trace. -/
theorem steps_star {ge : CGenv} {fe : EntryRel} {s s' : State}
    (h : Steps (SStep ge fe) s s') : Smallstep.Star (Step ge fe) s E0 s' := by
  induction h with
  | refl => exact Smallstep.Star.refl _
  | step _ _ _ h1 _ ih => exact Smallstep.Star.step h1 ih rfl

/-- One silent step followed by a silent run is a `plus` run. -/
theorem steps_plus {ge : CGenv} {fe : EntryRel} {s1 s2 s3 : State}
    (h1 : SStep ge fe s1 s2) (h2 : Steps (SStep ge fe) s2 s3) : Smallstep.Plus (Step ge fe) s1 E0 s3 :=
  Smallstep.Plus.intro h1 (steps_star h2) rfl

end CC
