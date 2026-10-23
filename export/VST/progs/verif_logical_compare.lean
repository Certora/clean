/-
  Port of VST's `progs/verif_logical_compare.v`: `do_or` and `do_and` of
  `vst/progs/logical_compare.c` compute `a || b` and `a && b` on `_Bool`s.

  VST's specifications:

      DECLARE _do_or
       WITH a: int, b : int
       PRE [ tbool, tbool ] PROP () PARAMS (Vint a; Vint b) SEP ()
       POST [ tbool ] PROP() RETURN (Vint (logical_or_result a b)) SEP().

  (and the same for `do_and` with `logical_and_result`).  VST's
  `start_function` knows that a `_Bool` parameter is `0` or `1`; here the
  arguments are given as Lean booleans `a b : Bool` (`boolInt a` is `0` or
  `1`), and the result is `boolInt (a || b)` (resp. `boolInt (a && b)`), which
  is `logical_or_result` (resp. `logical_and_result`) on these values.

  The C code `return a || b;` is compiled by `clightgen` into
  `if (a) t = 1; else t = (_Bool) b; return t;`; VST proves it with the rule
  `semax_shortcut_logical`, here it is plain symbolic execution over an exactly
  known local state (`Sep.At`, `CCLib.logic.ExactTemps`).
-/
import VST.progs.logical_compare
import CCLib
open CC CC.Sep CC.HProp
open Logical_compare

namespace VST.Verif.LogicalCompare

/-- A `_Bool` value: `1` for `true`, `0` for `false`. -/
def boolInt (a : Bool) : Integers.Int :=
  if a then Integers.Int.repr 1 else Integers.Int.repr 0

/-! ## `_Bool` conversions -/

theorem semCast_bool_bool (a : Bool) (m : Mem) :
    Cop.semCast (.Vint (boolInt a)) tbool tbool m = some (.Vint (boolInt a)) := by
  cases a <;> rfl

theorem semCast_int_bool (a : Bool) (m : Mem) :
    Cop.semCast (.Vint (boolInt a)) tint tbool m = some (.Vint (boolInt a)) := by
  cases a <;> rfl

theorem boolVal_bool (a : Bool) (m : Mem) :
    Cop.boolVal (.Vint (boolInt a)) tbool m = some a := by
  cases a <;> rfl

/-! ## The specifications -/

/-- The specification of a binary `_Bool` function computing `op`. -/
def boolSpec (op : Bool → Bool → Bool) (a b : Bool) : Sep.FunSpec where
  tyargs := [tbool, tbool]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint (boolInt a), .Vint (boolInt b)] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (boolInt (op a b)) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- `do_or_spec` -/
abbrev doOrSpec (a b : Bool) : Sep.FunSpec := boolSpec (· || ·) a b
/-- `do_and_spec` -/
abbrev doAndSpec (a b : Bool) : Sep.FunSpec := boolSpec (· && ·) a b

/-! ## The proofs -/

section
variable (ge : CGenv)

/-- The temporaries on entry (both functions have the same parameters and
    temporaries). -/
def le0 (a b : Bool) : TempEnv :=
  (((createUndefTemps f_do_or.fn_temps).set _a (.Vint (boolInt a))).set _b (.Vint (boolInt b)))

/-- `a = (_Bool) a; b = (_Bool) b;`, then the rest. -/
theorem prologue {func : Function} (a b : Bool) (rest : Stmt) (R : Sep.ExitConds)
    (h : Sep.Triple ge (FunctionEntry2 ge) func
      (At ((le0 a b).set _a (.Vint (boolInt a)) |>.set _b (.Vint (boolInt b)))) rest R) :
    Sep.Triple ge (FunctionEntry2 ge) func (At (le0 a b))
      (.Ssequence (.Sset _a (.Ecast (.Etempvar _a tbool) tbool))
        (.Ssequence (.Sset _b (.Ecast (.Etempvar _b tbool) tbool)) rest)) R := by
  refine Sep.triple_seq_only ge _ func (triple_set_at ge _ _ _ _ _ (fun m =>
    EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ tbool _ rfl) (semCast_bool_bool a m))) ?_
  refine Sep.triple_seq_only ge _ func (triple_set_at ge _ _ _ _ _ (fun m =>
    EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ tbool _ ?_) (semCast_bool_bool b m))) h
  exact (PTree.gso _ _ _ _ (by decide)).trans rfl

/-- **`do_or` satisfies `do_or_spec`** (VST's `body_do_or`). -/
theorem do_or_satisfies (a b : Bool) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_do_or) (doOrSpec a b)
      [.Vint (boolInt a), .Vint (boolInt b)] := by
  refine satisfies_at ge f_do_or _ _ (le0 a b) (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) (prologue ge a b _ _ ?_)
  refine Sep.triple_seq_only ge _ f_do_or
    (Q := At (((le0 a b).set _a (.Vint (boolInt a)) |>.set _b (.Vint (boolInt b))).set _t'1
      (.Vint (boolInt (a || b)))))
    (triple_if_at ge _ _ _ _ _ _ _ a
      (fun _ => EvalExpr.Etempvar _ tbool _ rfl) (boolVal_bool a) ?_) ?_
  · cases a
    · exact triple_set_at ge _ _ _ _ _ (fun m =>
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ tbool _ rfl) (semCast_bool_bool b m))
    · exact triple_set_at ge _ _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)
  · exact triple_return_at ge _ _ _ _ _ (fun _ => EvalExpr.Etempvar _ tint _ rfl)
      (semCast_int_bool _)

/-- **`do_and` satisfies `do_and_spec`** (VST's `body_do_and`). -/
theorem do_and_satisfies (a b : Bool) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_do_and) (doAndSpec a b)
      [.Vint (boolInt a), .Vint (boolInt b)] := by
  refine satisfies_at ge f_do_and _ _ (le0 a b) (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) (prologue ge a b _ _ ?_)
  refine Sep.triple_seq_only ge _ f_do_and
    (Q := At (((le0 a b).set _a (.Vint (boolInt a)) |>.set _b (.Vint (boolInt b))).set _t'1
      (.Vint (boolInt (a && b)))))
    (triple_if_at ge _ _ _ _ _ _ _ a
      (fun _ => EvalExpr.Etempvar _ tbool _ rfl) (boolVal_bool a) ?_) ?_
  · cases a
    · exact triple_set_at ge _ _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)
    · exact triple_set_at ge _ _ _ _ _ (fun m =>
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ tbool _ rfl) (semCast_bool_bool b m))
  · exact triple_return_at ge _ _ _ _ _ (fun _ => EvalExpr.Etempvar _ tint _ rfl)
      (semCast_int_bool _)

end

end VST.Verif.LogicalCompare
