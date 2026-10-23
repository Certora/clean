/-
  Port of VST's `progs/verif_stackframe_demo.v`: `iden` of
  `vst/progs/stackframe_demo.c`, whose local `y` has its address taken, so
  it lives in memory (a stack frame) rather than in a temporary.

      int iden (int x) {
        int y = x;
        int * p = & y;
        return * p;
      }

  VST's specification:

      DECLARE _iden
       WITH x : Z
       PRE  [ tint ] PROP () PARAMS (Vint (Int.repr x)) SEP ()
       POST [ tint ] PROP () RETURN (Vint (Int.repr x)) SEP ().

  The entry and exit of the local are `Sep.satisfies_oneLocal` and
  `Sep.triple_return_oneLocal` (`CCLib.logic.OneLocal`): the body owns the
  4 bytes of `y` (VST's `stackframe_of`), and gives them back when `return`
  frees `y`.  `x` is any `Int` (VST's `Int.repr x` for `x : Z`).
-/
import VST.progs.stackframe_demo
import CCLib
open CC CC.Sep CC.HProp
open Stackframe_demo

namespace VST.Verif.StackframeDemo

/-- `iden_spec` -/
def idenSpec (x : Integers.Int) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint x] ∧ emp hp
  post := fun v hp => v = .Vint x ∧ emp hp
  measure := fun _ => 0

theorem sizeof_tint (ce : CompositeEnv) : sizeof ce tint = 4 := by simp [sizeof, tint]

/-- **`iden` satisfies `iden_spec`** (VST's `body_iden`). -/
theorem iden_satisfies (ge : CGenv) (x : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_iden) (idenSpec x) [.Vint x] := by
  let L : TempEnv := (createUndefTemps f_iden.fn_temps).set _x (.Vint x)
  refine satisfies_oneLocal ge f_iden _ _ L _y tint rfl (by decide) (by decide) rfl
    (by rw [sizeof_tint]; decide) fun b => ?_
  let E : Env := emptyEnv.set _y (b, tint)
  -- the 4 undefined bytes of `y` are an undefined `int`
  refine triple_pre ge _ f_iden (P := AtE E L (mapsto .Mint32 .Freeable b 0 .Vundef))
    (fun e le hp ⟨he, hl, hH⟩ => ⟨he, hl, by
      rw [sizeof_tint, show (4 : _root_.Int).toNat = sizeChunkNat .Mint32 from rfl,
        undefBytes_mapsto _ _ _ undefEncoded_Mint32 (by decide)] at hH
      obtain ⟨h1, h2, _, rfl, ⟨_, rfl⟩, hm⟩ := hH
      rwa [Heap.emp_union]⟩) ?_
  -- `y = x;`
  refine triple_seq_only ge _ f_iden
    (triple_assign_atE ge _ f_iden E L _ _ .Mint32 .Freeable b _ 0 _ (.Vint x) (.Vint x) rfl rfl
      rfl (fun _ => eval_lvalue_oneLocal) (fun _ => EvalExpr.Etempvar _ _ _ rfl)
      (fun m => semCast_int m _)) ?_
  -- `p = &y;`
  refine triple_seq_only ge _ f_iden
    (triple_set_atE ge _ f_iden E L _ _ _ _ fun _ _ _ _ => eval_addrof_oneLocal _) ?_
  -- `t'1 = *p;`
  refine triple_seq_only ge _ f_iden
    (triple_set_atE ge _ f_iden E _ _ _ _ (.Vint x) fun m hp hm hag =>
      eval_lvalue_mapsto (chunk := .Mint32) (v := .Vint x) rfl rfl
        (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _))) rfl hm hag) ?_
  -- `return t'1;` frees `y`
  refine triple_pre ge _ f_iden (fun e le hp ⟨he, hl, hH⟩ => ⟨he, hl, by
    rw [emp_sep_eq, ← mapsto_eq_bytes (by decide)]; exact hH⟩)
    (triple_return_oneLocal ge _ f_iden _y tint b _ emp (encodeVal .Mint32 (.Vint x)) _ (.Vint x)
      (.Vint x) (by rw [sizeof_tint]; rfl) (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ (PTree.gss _ _ _))
      (fun m => semCast_int m _))

end VST.Verif.StackframeDemo
