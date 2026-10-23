/-
  Port of VST's `progs/verif_even.v`: `even` and `main` of `vst/progs/even.c`,
  compiled separately from `odd` (`vst/progs/odd.c`, `verif_odd.lean`).

  The specifications are VST's `verif_evenodd_spec.v`, which are the ones of
  the single-file version: `eoSpec` of `verif_evenodd.lean` (`even_spec` is
  `eoSpec true`, `odd_spec` is `eoSpec false`), and the body proof is the
  shared `body_ok` of that file.  As in VST, where `odd` is an external
  function of `even.c` whose specification is in `Gprog`, the theorems assume
  that whatever the global `odd` resolves to meets `odd_spec`
  (`MeetsSpec`).

  `main` calls `even(42)` and returns its result:

      DECLARE _main
       WITH gv : globals
       PRE  [] main_pre prog tt gv
       POST [ tint ]
         PROP() RETURN (Vint (if Z.even 42 then Int.one else Int.zero)) SEP(has_ext tt).
-/
import VST.progs.even
import VST.progs.verif_evenodd
open CC CC.Sep CC.HProp
open VST.Verif.Evenodd

namespace VST.Verif.Even
open _root_.Even

section
variable (ge : CGenv)

/-- The global `name` resolves to a function `fd` of type
    `int (unsigned)` meeting `eoSpec b` at every argument below `2^32`
    (VST: `name`'s specification is in `Gprog`). -/
def MeetsSpec (name : Ident) (b : Bool) : Prop :=
  ∃ blk fd, Genv.findSymbol ge.genv_genv name = some blk
    ∧ Genv.findFunct ge.genv_genv (.Vptr blk Integers.Ptrofs.zero) = some fd
    ∧ typeOfFundef fd = .Tfunction [tuint] tint cc_default
    ∧ ∀ n : Nat, (n : _root_.Int) < 4294967296 →
        Sep.SatisfiesAt ge (FunctionEntry2 ge) fd (eoSpec b n) [.Vint (Integers.Int.repr n)]

/-- **`even` satisfies `even_spec`** (VST's `body_even`), given that `odd`
    satisfies `odd_spec`. -/
theorem even_satisfies (hodd : MeetsSpec ge _odd false) (n : Nat)
    (hn : (n : _root_.Int) < 4294967296) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_even) (eoSpec true n)
      [.Vint (Integers.Int.repr n)] := by
  obtain ⟨bo, fdo, hsym, hfind, hty, hspec⟩ := hodd
  exact body_ok ge f_even true _odd bo fdo hsym hfind hty rfl rfl rfl rfl rfl n hn
    (fun _ => hspec (n - 1) (by omega))

/-- `main_spec` -/
def mainSpec : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (parityRes true 42) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- **`main` satisfies `main_spec`** (VST's `body_main`): it returns
    `even(42)`, i.e. `1`, given that the global `even` meets `even_spec`. -/
theorem main_satisfies (heven : MeetsSpec ge _even true) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_main) mainSpec [] := by
  obtain ⟨be, fde, hsym, hfind, hty, hspec⟩ := heven
  let L : TempEnv := createUndefTemps f_main.fn_temps
  have hL1 : ∀ v, (L.set _t'1 v).get _t'1 = some v := fun _ => PTree.gss _ _ _
  refine satisfies_at ge f_main _ _ L (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) ?_
  refine Sep.triple_seq ge _ f_main _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_main _ _)
  refine Sep.triple_seq_only ge _ f_main
    (Q := At (L.set _t'1 (.Vint (parityRes true 42)))) ?_ ?_
  · refine Sep.triple_call_at ge _ f_main (eoSpec true 42) _ _ _ _ _ be _ hfind hty rfl
      (fun e le hp m hP _ => ?_)
    obtain ⟨rfl, rfl, rfl⟩ := hP
    refine ⟨_, Heap.emp, Heap.emp, Heap.disjoint_emp_left _, (Heap.emp_union _).symm,
      eval_callee_global (PTree.gempty _) hsym rfl,
      EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ tint) rfl
        EvalExprlist.nil,
      ⟨rfl, rfl⟩, hspec 42 (by decide), fun v _ hpost _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := hpost
    exact ⟨rfl, rfl, Heap.emp_union _⟩
  · exact Sep.triple_conseq ge _ f_main
      (triple_return_at ge _ _ _ _ (.Vint (parityRes true 42))
        (fun _ => EvalExpr.Etempvar _ tint _ (hL1 _)) (fun m => semCast_int m _))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)

end

end VST.Verif.Even
