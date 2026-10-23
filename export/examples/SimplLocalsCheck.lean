/-
  Checks for the Clight → Clight pass `SimplLocals` (`CCLib.cfrontend.SimplLocals`).
-/
import CCLib.cfrontend.SimplLocals

open CC

namespace SimplLocalsCheck

def x : Ident := Positive.ofNat 1
def y : Ident := Positive.ofNat 2

/-- `int f(void) { int x; int y; x = 1; y = &x != 0; return x + y; }`:
    `x` has its address taken, `y` does not. -/
def srcFn : Function where
  fn_return := tint
  fn_callconv := cc_default
  fn_params := []
  fn_vars := [(x, tint), (y, tint)]
  fn_temps := []
  fn_body :=
    .Ssequence (.Sassign (.Evar x tint) (.Econst_int 1 tint))
      (.Ssequence
        (.Sassign (.Evar y tint)
          (.Ebinop .One (.Eaddrof (.Evar x tint) (.Tpointer tint noattr))
            (.Econst_int 0 tint) tint))
        (.Sreturn (some (.Ebinop .Oadd (.Evar x tint) (.Evar y tint) tint))))

/-- Only `y` is lifted to a temporary. -/
example : SimplLocals.cenvFor srcFn = [y] := by decide

/-- After the pass, `x` stays a memory variable and `y` becomes a temporary. -/
example : (match SimplLocals.transfFunction {} srcFn with
    | .OK tf => (tf.fn_vars.map (·.1), tf.fn_temps.map (·.1))
    | .Error _ => ([], [])) = ([x], [y]) := by decide

end SimplLocalsCheck
