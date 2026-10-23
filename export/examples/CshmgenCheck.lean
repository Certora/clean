/-
  Checks for the Clight → Csharpminor pass `Cshmgen` (`CCLib.cfrontend.Cshmgen`) and
  the Csharpminor → Cminor pass `Cminorgen` (`CCLib.cfrontend.Cminorgen`), run after
  `SimplLocals` on the function of `SimplLocalsCheck`.
-/
import CCLib.cfrontend.Cshmgen
import CCLib.cfrontend.Cminorgen
import SimplLocalsCheck

open CC

namespace CshmgenCheck

/-- The front-end pipeline `SimplLocals` then `Cshmgen` on one function. -/
def pipeline (f : Function) : Res Csharpminor.Function :=
  match SimplLocals.transfFunction {} f with
  | .OK f' => Cshmgen.translFunction (Conventions1.returnValueNeedsNormalization .AAPCS64) PTree.empty f'
  | .Error msg => .Error msg

/-- The translation succeeds: the address-taken `x` stays a 4-byte stack
    variable, `y` is a temporary, and the signature returns an `int`. -/
example : (match pipeline SimplLocalsCheck.srcFn with
    | .OK tf => (tf.fn_vars, tf.fn_temps, tf.fn_sig.sig_res)
    | .Error _ => ([], [], .Xvoid)) =
      ([(SimplLocalsCheck.x, 4)], [SimplLocalsCheck.y], .Xint) := by decide

/-- A cast to `char` of an `int` becomes an 8-bit sign extension. -/
example : (match Cshmgen.makeCast tint tschar (.Evar (Positive.ofNat 1)) with
    | .OK (.Eunop .Ocast8signed (.Evar _)) => true
    | _ => false) = true := by decide

/-- `Cminorgen` then puts `x` in a 4-byte stack frame; the Cminor local
    variables are the former temporaries (`y`). -/
example : (match pipeline SimplLocalsCheck.srcFn with
    | .OK tf =>
      match Cminorgen.translFunction tf with
      | .OK cf => (cf.fn_stackspace, cf.fn_vars)
      | .Error _ => (-1, [])
    | .Error _ => (-1, [])) = (4, [SimplLocalsCheck.y]) := by decide

/-- Stack layout sorts variables by size: a 1-byte, an 8-byte and a 2-byte
    variable get offsets 0, 8 and 2, for a frame of 16 bytes. -/
def layoutFn : Csharpminor.Function :=
  { fn_sig := mksignature [] .Xvoid cc_default, fn_params := [], fn_temps := [],
    fn_body := .Sskip,
    fn_vars := [(Positive.ofNat 1, 1), (Positive.ofNat 2, 8), (Positive.ofNat 3, 2)] }

example : ([1, 2, 3].map (fun n => PTree.get (Positive.ofNat n) (Cminorgen.buildCompilenv layoutFn).1),
    (Cminorgen.buildCompilenv layoutFn).2) = ([some 0, some 8, some 2], 16) := by decide

/-- The variable sort is stable: equal sizes keep their order. -/
example : (Cminorgen.varSort [(Positive.ofNat 1, 4), (Positive.ofNat 2, 1), (Positive.ofNat 3, 4),
    (Positive.ofNat 4, 1)]).map (·.1) = [2, 4, 1, 3].map Positive.ofNat := by decide

end CshmgenCheck
