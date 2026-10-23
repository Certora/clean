/-
  Checks for the CminorSel → RTL pass `RTLgen` (`CCLib.backend.RTLgen`).
-/
import CCLib.backend.RTLgen

open CC CC.Op CC.CminorSel

namespace RTLgenCheck

def x : Ident := Positive.ofNat 1

/-- `int f(int x) { return x + 1; }` after instruction selection. -/
def srcFn : CminorSel.Function :=
  { fn_sig := mksignature [.Xint] .Xint cc_default, fn_params := [x], fn_vars := [],
    fn_stackspace := 0,
    fn_body := .Sreturn (some (.Eop (.Oaddimm (Integers.Int.repr 1)) (.Econs (.Evar x) .Enil))) }

/-- The translation allocates register 1 for `x` and register 2 for the
    result; node 1 is the `return` and node 2 the addition, which is also the
    entry point. -/
example : (match RTLgen.translFunction (fun _ _ _ => false) srcFn with
    | .OK tf =>
      (tf.fn_entrypoint, tf.fn_params,
        match tf.fn_code.get (Positive.ofNat 1), tf.fn_code.get (Positive.ofNat 2) with
        | some (.Ireturn (some r)), some (.Iop (.Oaddimm _) [a] d s) =>
            r == Positive.ofNat 2 && a == Positive.ofNat 1 && d == Positive.ofNat 2 &&
              s == Positive.ofNat 1
        | _, _ => false)
    | .Error _ => (Positive.ofNat 99, [], false)) =
      (Positive.ofNat 2, [Positive.ofNat 1], true) := by decide

/-- An unbound variable is reported as an error. -/
example : (match RTLgen.translFunction (fun _ _ _ => false)
      { srcFn with fn_params := [] } with
    | .OK _ => false
    | .Error _ => true) = true := by decide

end RTLgenCheck
