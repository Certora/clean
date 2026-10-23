/-
  Checks for the CompCert C → Clight translation `SimplExpr` (`CCLib.cfrontend.SimplExpr`)
  and its specification (`CCLib.cfrontend.SimplExprspecMain`).
-/
import CCLib.cfrontend.SimplExprspecMain

open CC

namespace SimplExprCheck

/-- `return (1 ? 2 : 3);` in CompCert C. -/
def srcFn : Csyntax.Function where
  fn_return := tint
  fn_callconv := cc_default
  fn_params := []
  fn_vars := []
  fn_body := .Sreturn (some (.Econdition (.Eval (.Vint 1) tint) (.Eval (.Vint 2) tint)
    (.Eval (.Vint 3) tint) tint))

/-- The translation succeeds and introduces exactly one fresh temporary
    (for the value of the conditional expression). -/
example : (match SimplExpr.translFunction PTree.empty (Positive.ofNat 1000) srcFn with
    | .OK tf => tf.fn_temps.length
    | .Error _ => 0) = 1 := by decide

/-- Whatever the translation produces satisfies the relational specification
    `TrFunction` (`SimplExprspec.transl_function_spec`). -/
example (ce : CompositeEnv) (tf : Function)
    (h : SimplExpr.translFunction ce (Positive.ofNat 1000) srcFn = .OK tf) :
    SimplExpr.TrFunction ce srcFn tf :=
  SimplExpr.transl_function_spec ce h

end SimplExprCheck
