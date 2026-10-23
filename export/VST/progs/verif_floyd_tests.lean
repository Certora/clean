/-
  Port of VST's `progs/verif_floyd_tests.v`: `test_sizeof` of
  `vst/progs/floyd_tests.c`.

      int test_sizeof(int* p) {
        int a = sizeof(*p);
        int b = 1 + sizeof(*p);
        return a + b;
      }

  VST's specification:

      test_sizeof_spec: WITH p, sh, i
        PRE [ tptr tint ] PROP (readable_share sh; 0 <= i <= Int.max_signed)
          PARAMS (p) SEP (data_at sh tint (Vint (Int.repr i)) p)
        POST [ tint ] PROP () RETURN (Vint (Int.repr 9))
          SEP (data_at sh tint (Vint (Int.repr i)) p)

  `sizeof(*p)` does not read `*p`, so neither the permission nor the range of
  `i` matter: the specification below holds for any permission and any
  `int` content of the cell (VST's side conditions are dropped).
-/
import VST.progs.floyd_tests
import CCLib
open CC CC.Sep CC.HProp
open Floyd_tests

namespace VST.Verif.FloydTests

/-- `test_sizeof_spec` -/
def testSizeofSpec (perm : Permission) (b : Block) (ofs : Integers.Ptrofs) (i : Integers.Int) :
    Sep.FunSpec where
  tyargs := [tptr tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b ofs]
    ∧ mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs) (.Vint i) hp
  post := fun v hp => v = .Vint (Integers.Int.repr 9)
    ∧ mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs) (.Vint i) hp
  measure := fun _ => 0

/-- **`test_sizeof` satisfies `test_sizeof_spec`** (VST's `body_test_sizeof_spec`). -/
theorem test_sizeof_satisfies (ge : CGenv) (perm : Permission) (b : Block)
    (ofs : Integers.Ptrofs) (i : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_test_sizeof)
      (testSizeofSpec perm b ofs i) [.Vptr b ofs] := by
  let L := (createUndefTemps f_test_sizeof.fn_temps).set _p (.Vptr b ofs)
  let H := mapsto .Mint32 perm b (Integers.Ptrofs.unsigned ofs) (.Vint i)
  refine satisfies_internal_noVars ge _ f_test_sizeof _ _ (AtH L H)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  -- `a = (int) sizeof(int);`
  let L1 := L.set _a (.Vint (Integers.Int.repr 4))
  refine Sep.triple_seq_only ge _ f_test_sizeof
    (triple_set_atH ge _ f_test_sizeof L H _ _ _ (fun m _ _ _ =>
      EvalExpr.Ecast _ _ _ _ (EvalExpr.Esizeof _ _) rfl)) ?_
  -- `b = (int) (1 + sizeof(int));`
  let L2 := L1.set _b (.Vint (Integers.Int.repr 5))
  refine Sep.triple_seq_only ge _ f_test_sizeof
    (triple_set_atH ge _ f_test_sizeof L1 H _ _ (.Vint (Integers.Int.repr 5)) (fun m _ _ _ =>
      EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _)
        (EvalExpr.Esizeof _ _) rfl) rfl)) ?_
  -- `return a + b;`
  exact triple_return_atH ge _ f_test_sizeof L2 H _ (.Vint (Integers.Int.repr 9)) _
    (fun m _ _ _ => EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ rfl)
      (EvalExpr.Etempvar _ _ _ rfl) rfl) (fun m => rfl)

end VST.Verif.FloydTests
