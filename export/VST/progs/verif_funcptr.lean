/-
  Port of VST's `progs/verif_funcptr.v`: `myfunc` and `main` of
  `vst/progs/funcptr.c`, where `main` calls `myfunc` through a function
  pointer held in a local.

      int myfunc (int i) { return i+1; }

      int main (void) {
        int (*f)(int);
        int j;
        f = &myfunc;
        j = f(3);
        return j;
      }

  VST's specifications:

      Definition myspec :=
        WITH i: Z
        PRE [ tint ] PROP (Int.min_signed <= i < Int.max_signed)
                     PARAMS (Vint (Int.repr i)) SEP ()
        POST [ tint ] PROP() RETURN (Vint (Int.repr (i+1))) SEP().

      DECLARE _main WITH gv : globals
        PRE  [] main_pre prog tt gv
        POST [ tint ] main_post prog gv.

  `i` is an `Int` and the result is `Int.add i 1` (`= Int.repr (i+1)` under
  VST's range hypothesis, which is then not needed).  `main`'s postcondition
  says it returns `4`.  The call goes through the temporary `f`
  (`eval_callee_temp`), which holds `&myfunc`; `fb` is the block of `myfunc`
  (VST's `make_func_ptr _myfunc`).
-/
import VST.progs.funcptr
import CCLib
open CC CC.Sep CC.HProp
open Funcptr

namespace VST.Verif.Funcptr

/-- `myspec` -/
def mySpec (i : Integers.Int) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint i] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (Integers.Int.add i (Integers.Int.repr 1)) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- `main_spec`: `main` returns `4`. -/
def mainSpec : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (Integers.Int.repr 4) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- **`myfunc` satisfies `myspec`** (VST's `body_myfunc`). -/
theorem myfunc_satisfies (ge : CGenv) (i : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_myfunc) (mySpec i) [.Vint i] :=
  satisfies_at ge f_myfunc _ _ _ (by decide) (by decide) (by decide) rfl rfl (fun _ h => h.2)
    (triple_return_at ge _ _ _ _ _
      (fun _ => EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ rfl)
        (EvalExpr.Econst_int _ tint) (semBinop_add_int _ _ _ _))
      (fun m => semCast_int m _))

/-- **`main` satisfies `main_spec`** (VST's `body_main`), given that the
    symbol `myfunc` is the function `myfunc`. -/
theorem main_satisfies (ge : CGenv) (fb : Block)
    (hsym : Genv.findSymbol ge.genv_genv _myfunc = some fb)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr fb Integers.Ptrofs.zero)
      = some (.Internal f_myfunc)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_main) mainSpec [] := by
  let L : TempEnv := createUndefTemps f_main.fn_temps
  let L1 := L.set _f (.Vptr fb Integers.Ptrofs.zero)
  let v4 : Val := .Vint (Integers.Int.add (Integers.Int.repr 3) (Integers.Int.repr 1))
  refine satisfies_at ge f_main _ _ L (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) ?_
  -- the trailing `return 0;` is unreachable
  refine Sep.triple_seq ge _ f_main _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_main _ _)
  -- `f = &myfunc;`
  refine triple_seq_only ge _ f_main
    (triple_set_at ge _ L _f _ (.Vptr fb Integers.Ptrofs.zero) fun _ =>
      EvalExpr.Eaddrof _ _ fb _ (EvalLvalue.Evar_global _ fb _ (PTree.gempty _) hsym)) ?_
  -- `t'1 = f(3); j = t'1;`
  refine triple_seq_only ge _ f_main (Q := At ((L1.set _t'1 v4).set _j v4)) ?_ ?_
  · refine triple_seq_only ge _ f_main ?_
      (triple_set_at ge _ _ _j _ v4 fun _ => EvalExpr.Etempvar _ tint _ rfl)
    refine Sep.triple_call_at ge _ f_main (mySpec (Integers.Int.repr 3)) _ _ _ _ _ fb _ hfind rfl
      rfl (fun e le hp m hP _ => ?_)
    obtain ⟨rfl, rfl, rfl⟩ := hP
    refine ⟨[.Vint (Integers.Int.repr 3)], Heap.emp, Heap.emp, Heap.disjoint_emp_right _,
      (Heap.union_emp _).symm, eval_callee_temp rfl,
      EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ tint) (semCast_int m _)
        EvalExprlist.nil, ⟨rfl, rfl⟩, myfunc_satisfies ge _, fun v h1' hpost _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := hpost
    exact ⟨rfl, rfl, Heap.union_emp _⟩
  -- `return j;`
  · exact triple_return_at ge _ _ _ v4 v4 (fun _ => EvalExpr.Etempvar _ tint _ rfl)
      (fun m => semCast_int m _)

end VST.Verif.Funcptr
