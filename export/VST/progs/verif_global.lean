/-
  Port of VST's `progs/verif_global.v`: `h` and `main` of
  `vst/progs/global.c`, which read the global variable `g`.

  VST's specifications:

      DECLARE _h
       WITH gv: globals
       PRE [ ] PROP () PARAMS() GLOBALS (gv)
               SEP (data_at Ews tint (Vint (Int.repr 7)) (gv _g))
       POST [ tint ] PROP () RETURN (Vint (Int.repr 7))
               SEP (data_at Ews tint (Vint (Int.repr 7)) (gv _g)).

      DECLARE _main
       WITH gv: globals
       PRE  [] main_pre prog tt gv
       POST [ tint ] main_post prog gv.

  Here `gv _g` is the block `gb` that the symbol `g` resolves to
  (`Genv.find_symbol`), `data_at Ews tint (Vint 7) (gv _g)` is the `mapsto`
  of the `int` `7` at offset `0` of `gb` (`gAt`), owned at a readable
  permission `perm`.  `main_pre` gives `main` the initialised globals; of
  those `main` only uses `g`, so its precondition is `gAt`, and its
  postcondition says that it returns `h()`, i.e. `7`.  The global is read with
  `eval_global_mapsto` (`CCLib.logic.Globals`).
-/
import VST.progs.global
import CCLib
open CC CC.Sep CC.HProp
open Global

namespace VST.Verif.Global

/-- `data_at Ews tint (Vint (Int.repr 7)) (gv _g)` -/
def gAt (perm : Permission) (gb : Block) : HProp :=
  mapsto .Mint32 perm gb 0 (.Vint (Integers.Int.repr 7))

/-- `h_spec` -/
def hSpec (perm : Permission) (gb : Block) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ gAt perm gb hp
  post := fun v hp => v = .Vint (Integers.Int.repr 7) ∧ gAt perm gb hp
  measure := fun _ => 0

/-- `main_spec` (with `main_pre`/`main_post` restricted to `g`) -/
def mainSpec (perm : Permission) (gb : Block) : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ gAt perm gb hp
  post := fun v hp => v = .Vint (Integers.Int.repr 7) ∧ gAt perm gb hp
  measure := fun _ => 0

/-- Locals described exactly, and the fragment holding `g`. -/
def AtG (perm : Permission) (gb : Block) (L : TempEnv) : Sep.Assn :=
  Sep.AtH L (gAt perm gb)

section
variable (ge : CGenv) (perm : Permission) (gb : Block)
  (hpr : permOrder perm .Readable = true)
  (hsym_g : Genv.findSymbol ge.genv_genv _g = some gb)
include hpr hsym_g

omit hpr hsym_g in
/-- `return x;` where `x` holds `7`. -/
theorem return7 (f : Function) (hret : f.fn_return = tint) (L : TempEnv) (x : Ident)
    (hx : L.get x = some (.Vint (Integers.Int.repr 7))) :
    Sep.Triple ge (FunctionEntry2 ge) f (AtG perm gb L) (.Sreturn (some (.Etempvar x tint)))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := (hSpec perm gb).post } :=
  Sep.triple_return ge _ f _ _ _ fun e le hp m h _ => by
    obtain ⟨rfl, rfl, hg⟩ := h
    exact ⟨_, _, m, hp, EvalExpr.Etempvar _ tint _ hx, by rw [hret]; exact semCast_int m _,
      freeList_emptyEnv _ _, ⟨rfl, hg⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩

/-- **`h` satisfies `h_spec`** (VST's `body_h`). -/
theorem h_satisfies :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_h) (hSpec perm gb) [] := by
  let L : TempEnv := createUndefTemps f_h.fn_temps
  refine satisfies_internal_noVars ge _ f_h _ _ (AtG perm gb L)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  refine Sep.triple_seq_only ge _ f_h
    (Q := AtG perm gb (L.set _x (.Vint (Integers.Int.repr 7)))) ?_
    (return7 ge perm gb f_h rfl _ _ (PTree.gss _ _ _))
  refine Sep.triple_set ge _ f_h _ _ _ _ fun e le hp m h hag => ?_
  obtain ⟨rfl, rfl, hg⟩ := h
  exact ⟨_, eval_global_mapsto (PTree.gempty _) hsym_g rfl hpr hg hag, rfl, rfl, hg⟩

/-- **`main` satisfies `main_spec`** (VST's `body_main`): it returns `h()`,
    i.e. `7`, given that the global `h` is the function `h`. -/
theorem main_satisfies (hb : Block)
    (hsym_h : Genv.findSymbol ge.genv_genv _h = some hb)
    (hfind_h : Genv.findFunct ge.genv_genv (.Vptr hb Integers.Ptrofs.zero)
      = some (.Internal f_h)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_main) (mainSpec perm gb) [] := by
  let L : TempEnv := createUndefTemps f_main.fn_temps
  let L1 := L.set _t'1 (.Vint (Integers.Int.repr 7))
  refine satisfies_internal_noVars ge _ f_main _ _ (AtG perm gb L)
    (fun _ => ⟨L, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp h => ⟨rfl, rfl, h.2⟩⟩) ?_
  refine Sep.triple_seq ge _ f_main _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_main _ _)
  refine Sep.triple_seq_only ge _ f_main (Q := AtG perm gb (L1.set _y (.Vint (Integers.Int.repr 7))))
    ?_ (return7 ge perm gb f_main rfl _ _ (PTree.gss _ _ _))
  refine Sep.triple_seq_only ge _ f_main (Q := AtG perm gb L1) ?_ ?_
  · refine Sep.triple_call_at ge _ f_main (hSpec perm gb) _ _ _ _ _ hb _ hfind_h rfl rfl
      (fun e le hp m hP _ => ?_)
    obtain ⟨rfl, rfl, hg⟩ := hP
    refine ⟨[], hp, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm,
      eval_callee_global (PTree.gempty _) hsym_h rfl, EvalExprlist.nil, ⟨rfl, hg⟩,
      h_satisfies ge perm gb hpr hsym_g, fun v h1' hpost _ => ?_⟩
    obtain ⟨rfl, hg'⟩ := hpost
    exact ⟨rfl, rfl, by rw [Heap.union_emp]; exact hg'⟩
  · refine Sep.triple_set ge _ f_main _ _ _ _ fun e le hp m h _ => ?_
    obtain ⟨rfl, rfl, hg⟩ := h
    exact ⟨_, EvalExpr.Etempvar _ tint _ (PTree.gss _ _ _), rfl, rfl, hg⟩

end

end VST.Verif.Global
