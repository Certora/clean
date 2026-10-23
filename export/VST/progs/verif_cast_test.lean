/-
  Port of VST's `progs/verif_cast_test.v`: the functions `test` and
  `issue500` of `vst/progs/cast_test.c` (64-bit arithmetic with implicit
  `int`/`long long`/`unsigned char` conversions) meet their specifications.

  VST's specifications:

      DECLARE _test
       WITH n: Z
       PRE [ tlong ] PROP (0 <= n < Int.max_signed) PARAMS (Vlong (Int64.repr n)) SEP ()
       POST [ tuchar ] PROP () RETURN (Vint (Int.repr 0)) SEP ().

      DECLARE _issue500
       WITH i: Int64.int
       PRE [ tlong ] PROP (Int64.signed i + 2147483648 <= Int64.max_signed)
         PARAMS (Vlong i) SEP()
       POST [ tlong ] PROP() RETURN (Vlong (Int64.add i (Int64.repr 2147483648))) SEP().

  Both results hold for every 64-bit argument, so the preconditions on `n` and
  `i` are not needed: `test` returns `0` because `c << 8` has a zero low byte
  (`shl8_and255`), and `issue500` computes the machine sum.  The bodies are
  straight-line code: each assignment is `triple_set_at` with the evaluation of
  its right-hand side, the operators being computed by reduction (`rfl`).
-/
import VST.progs.cast_test
import CCLib
open CC CC.Sep CC.HProp
open Cast_test

namespace VST.Verif.CastTest

/-- `test_spec` -/
def testSpec (n : Integers.Int64) : Sep.FunSpec where
  tyargs := [tlong]
  tyres := tuchar
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vlong n] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- `issue500_spec` -/
def issue500Spec (i : Integers.Int64) : Sep.FunSpec where
  tyargs := [tlong]
  tyres := tlong
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vlong i] ∧ hp = Heap.emp
  post := fun v hp => v = .Vlong (Integers.Int64.add i (Integers.Int64.repr 2147483648)) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- **`issue500` satisfies `issue500_spec`** (VST's `body_issue500`). -/
theorem issue500_satisfies (ge : CGenv) (i : Integers.Int64) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_issue500) (issue500Spec i) [.Vlong i] := by
  refine satisfies_at ge f_issue500 _ _ _ (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) ?_
  exact Sep.triple_conseq ge _ f_issue500
    (triple_return_at ge _ _ _ _ _ (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ rfl) (EvalExpr.Econst_int _ _) rfl) (fun _ => rfl))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ x => x)

/-- The low byte of a 64-bit value shifted left by 8 is zero. -/
theorem shl8_and255 (x : Integers.Int64) :
    Integers.Int64.and (Integers.Int64.shl x (Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.repr 8))))
      (Cop.castIntLong .Signed (Integers.Int.repr 255)) = Integers.Int64.repr 0 := by
  have h8 : Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.repr 8)) = 8#64 := by decide
  have h255 : Cop.castIntLong .Signed (Integers.Int.repr 255) = 255#64 := by decide
  have h0 : (Integers.Int64.repr 0 : Integers.Int64) = 0#64 := by decide
  rw [h8, h255, h0]
  simp only [Integers.Int64.and, Integers.Int64.shl, Integers.MI.and, Integers.MI.shl]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_zero]
  by_cases h : i < 8
  · simp [h]
  · have : (255#64)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      simp only [BitVec.toNat_ofNat]
      apply Nat.testBit_lt_two_pow
      calc 255 % 2 ^ 64 = 255 := by decide
        _ < 2 ^ 8 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    simp [this]

local macro "tv" : term => `(EvalExpr.Etempvar _ _ _ rfl)
local macro "ci" : term => `(EvalExpr.Econst_int _ _)

/-- **`test` satisfies `test_spec`** (VST's `body_test`): it returns `0` for
    every 64-bit `n`. -/
theorem test_satisfies (ge : CGenv) (n : Integers.Int64) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_test) (testSpec n) [.Vlong n] := by
  refine satisfies_at ge f_test _ _ _ (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ tv ci rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ ci tv rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ tv ci rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ ci rfl) tv rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ tv ci rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ ci tv rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ tv ci rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ebinop _ _ _ _ _ _ _ tv ci rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ tv ci rfl) rfl)) ?_
  refine Sep.triple_seq_only ge _ f_test (triple_set_at ge _ _ _ _ _
    (fun _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ tv tv rfl) rfl)) ?_
  refine Sep.triple_conseq ge _ f_test
    (triple_return_at ge _ _ _ _ (.Vint (Integers.Int.repr 0)) (fun _ => tv) (fun m => ?_))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ x => x)
  rw [shl8_and255]
  have hz : Cop.castIntLong .Unsigned (Cop.castIntInt .I8 .Unsigned
      (Integers.Int.repr (Integers.Int64.unsigned (Integers.Int64.repr 0)))) = 0#64 := by decide
  rw [hz]
  simp only [Integers.Int64.and, Integers.MI.and, BitVec.zero_and]
  rfl

end VST.Verif.CastTest
