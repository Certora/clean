/-
  Checks for the reference interpreter of CompCert C (`CCLib.cfrontend.Cexec`).
-/
import CCLib.cfrontend.CexecStep

open CC

namespace CexecCheck

/-- A world that answers nothing (every external call / volatile access gets stuck). -/
def silentWorld : World where
  σ := Unit
  st := ()
  io _ _ _ := none
  vload _ _ _ _ := none
  vstore _ _ _ _ _ := none

/-- The interpreter reduces `1 + 2` at the top of an expression state to `3`. -/
example (ge : Csem.CGenv) (f : Csyntax.Function) (k : Csem.Cont) (e : Env) (m : Mem) :
    Cexec.doStep ge .none silentWorld
        (.ExprState f (.Ebinop .Oadd (.Eval (.Vint 1) tint) (.Eval (.Vint 2) tint) tint) k e m) =
      [.TR "red_binop" E0 (.ExprState f (.Eval (.Vint 3) tint) k e m)] := by
  rfl

/-- ... and that transition is a step of the semantics (`do_step_sound`). -/
example (ge : Csem.CGenv) (hinj : Genv.SymbInjective ge.genv_genv) (ox : Cexec.ExtOracle)
    (hS : ox.Sound) (hC : ox.Complete) (w : World) (S S' : Csem.State) (t : Trace) (rule : String)
    (h : Cexec.Transition.TR rule t S' ∈ Cexec.doStep ge ox w S) :
    Csem.Step ge S t S' ∨ (t = E0 ∧ S' = .Stuckstate ∧ Cexec.CanCrashWorld ge w S) :=
  Cexec.do_step_sound ge ox hinj hS hC h

/-- For a whole program, the symbol-injectivity hypothesis is discharged by
    `Genv.symbInjective_globalenv`. -/
example (p : Csyntax.Program) (ox : Cexec.ExtOracle) (hS : ox.Sound) (hC : ox.Complete)
    (w w' : World) (S S' : Csem.State) (t : Trace)
    (hp : PossibleTrace w t w') (h : Csem.Step (Csem.globalenv p) S t S') :
    ∃ rule, Cexec.Transition.TR rule t S' ∈ Cexec.doStep (Csem.globalenv p) ox w S :=
  Cexec.do_step_complete _ ox (Genv.symbInjective_globalenv p.prog_public p.prog_defs) hS hC hp h

/-- A function returning to the empty continuation is a final state with its result. -/
example (m : Mem) : Cexec.atFinalState (.Returnstate (.Vint 42) .Kstop m) = some 42 := rfl

end CexecCheck
