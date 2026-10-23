/-
  Sanity checks for the big-step semantics (`CCLib/cfrontend/ClightBigstep.lean`): the
  terminating and diverging judgements are inhabited, and a diverging loop
  yields an infinite small-step run (`execinf_stmt_forever`).
-/
import CCLib.cfrontend.ClightBigstep

namespace CC.BigstepCheck

open ClightBigstep Smallstep Outcome

variable (FE : CGenv → Function → List Val → Mem → Env → TempEnv → Mem → Prop) (ge : CGenv)

/-- `skip; break` terminates with outcome `Out_break`. -/
example (e le m) : ExecStmt FE ge e le m (.Ssequence .Sskip .Sbreak) E0 le m Out_break :=
  .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sskip _ _ _) (.exec_Sbreak _ _ _)

/-- `loop { break }` terminates normally. -/
example (e le m) : ExecStmt FE ge e le m (.Sloop .Sbreak .Sskip) E0 le m Out_normal :=
  .exec_Sloop_stop1 _ _ _ _ _ _ _ _ _ _ (.exec_Sbreak _ _ _) .B

/-- The infinite loop `loop { skip }` diverges (coinductively), for any trace. -/
theorem loop_skip_diverges (e le m T) :
    ExecinfStmt FE ge e le m (.Sloop .Sskip .Sskip) T := by
  apply ExecinfStmt.coinduct FE ge (fun _ _ _ s _ => s = .Sloop .Sskip .Sskip)
    (fun _ _ _ _ => False)
  · intro e le m s T hs
    subst hs
    right; right; right; right; right; right; left
    refine ⟨.Sskip, .Sskip, E0, le, m, Out_normal, E0, le, m, T,
      .exec_Sskip _ _ _, .N, .exec_Sskip _ _ _, rfl, rfl, ?_⟩
    simp [Eappinf_E0]
  · intro _ _ _ _ h; exact h.elim
  · rfl

/-- Through `execinf_stmt_forever`, the diverging loop has an infinite
    small-step run. -/
example (f : Function) (k : Cont) (e le m T) :
    Forever (Step ge (FE ge)) (.State f (.Sloop .Sskip .Sskip) k e le m) T :=
  execinf_stmt_forever f k (loop_skip_diverges FE ge e le m T)

end CC.BigstepCheck
