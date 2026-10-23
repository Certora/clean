/-
  Non-vacuity checks for `CCLib.common.Determinism`.

  A determinism theorem is trivially satisfiable by an empty relation, so
  stating it proves nothing.  Every check below therefore *applies* determinism
  to a step that is actually derivable, in the direction that has content:
  from one exhibited transition, conclude that the relation permits **no other**.

  Three things are pinned here:

  1. the twelve rules with real content in `step_determ` — one representative of
     each shape that can produce a non-trivial obligation, driven off the real
     `f_main` where the AST allows it;
  2. the two facts the rest of the development consumes — `sstep_determ` (the
     silent step relation is a partial function) and `starE0_endpoint_unique`
     (∀-run from ∃-run);
  3. the **axiom set**.  This is the first place in the tree where a theorem may
     legitimately mention an axiom beyond the Lean core three plus the two
     uninterpreted-external `Parameter`s, so the `#print axioms` lines below are
     the guard: `CC.externalFunctionsSemDeterm` and `CC.inlineAssemblySemDeterm`
     are the *only* additions, they appear only where an external call can occur,
     and everything proved before this change still typechecks against the old
     set (`IsSortedSep` is imported for exactly that reason).
-/
import Lean
import GenMain
import IsSortedSep
import CCLib
open CC
open Main   -- the generated module lives in its own namespace

namespace DetermCheck

section Rules
variable (ge : CGenv)
  (fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop)
  (hfe : EntryDeterm fe) (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective)
variable (f : Function) (k : Cont) (e : Env) (le : TempEnv) (m : Mem)
  (s1 s2 : Stmt) (id : Ident)

/-! ### `sd_determ`, applied

Each `example` says: *any* successor of this concrete configuration is the one
named.  That is the content of determinism, and it is unavailable without it —
before this file the only way to know a successor was to be handed it. -/

/-- `Ssequence`, on the body of the real `main`. -/
example (s' : State)
    (h : Step ge fe (.State f_main f_main.fn_body k e le m) E0 s') :
    s' = .State f_main
      (.Sreturn (some (.Econst_int (Integers.Int.repr 0) tint)))
      (.Kseq (.Sreturn (some (.Econst_int (Integers.Int.repr 0) tint))) k) e le m :=
  sstep_determ hfe hinj h (Step.seq _ _ _ _ _ _ _)

/-- `Sset`: the temporary environment after the step is forced. -/
example (s' : State)
    (h : Step ge fe (.State f (.Sset id (.Econst_int (Integers.Int.repr 5) tint))
            k e le m) E0 s') :
    s' = .State f .Sskip k e (le.set id (.Vint (Integers.Int.repr 5))) m :=
  (sstep_determ hfe hinj h
    (Step.set _ _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _)))

/-- `Sifthenelse`: the *branch* is forced.  `CCLib.logic.Hoare`'s `triple_if` takes
    the branch from the caller "to avoid needing determinism of `EvalExpr`"
    (`Hoare.lean:270`); this is the fact that was missing. -/
example (s' : State)
    (h : Step ge fe (.State f (.Sifthenelse (.Econst_int Integers.Int.one tint) s1 s2)
            k e le m) E0 s') :
    s' = .State f s1 k e le m :=
  (sstep_determ hfe hinj h
    (Step.ifthenelse f _ s1 s2 k e le m _ true (EvalExpr.Econst_int _ _) rfl))

/-- `Sskip` under `Kseq` — one of the five `Sskip` rules, which overlap on the
    statement and are separated only by the continuation. -/
example (s' : State) (h : Step ge fe (.State f .Sskip (.Kseq s1 k) e le m) E0 s') :
    s' = .State f s1 k e le m :=
  sstep_determ hfe hinj h (Step.skip_seq _ _ _ _ _ _)

/-- `Sloop`, and `Sbreak` out of it. -/
example (s' : State) (h : Step ge fe (.State f (.Sloop s1 s2) k e le m) E0 s') :
    s' = .State f s1 (.Kloop1 s1 s2 k) e le m :=
  sstep_determ hfe hinj h (Step.loop _ _ _ _ _ _ _)

example (s' : State)
    (h : Step ge fe (.State f .Sbreak (.Kloop1 s1 s2 k) e le m) E0 s') :
    s' = .State f .Sskip k e le m :=
  sstep_determ hfe hinj h (Step.break_loop1 _ _ _ _ _ _ _)

/-- `Slabel`, and returning from a call. -/
example (s' : State) (h : Step ge fe (.State f (.Slabel id s1) k e le m) E0 s') :
    s' = .State f s1 k e le m :=
  sstep_determ hfe hinj h (Step.label _ _ _ _ _ _ _)

example (v : Val) (optid : Option Ident) (s' : State)
    (h : Step ge fe (.Returnstate v (.Kcall optid f e le k) m) E0 s') :
    s' = .State f .Sskip k e (setOpttemp optid v le) m :=
  sstep_determ hfe hinj h (Step.returnstate _ _ _ _ _ _ _)

/-! ### `sd_final_nostep` and `sd_final_determ`, applied -/

/-- A real final state — `main` returning 0 to the empty continuation — takes no
    step at all, for any trace. -/
example (r : Integers.Int) (t : Trace) (s' : State) :
    ¬ Step ge fe (.Returnstate (.Vint r) .Kstop m) t s' :=
  finalState_nostep (FinalState.intro r m)

example (r1 r2 : Integers.Int) (h1 : FinalState (.Returnstate (.Vint r1) .Kstop m) r2) :
    r2 = r1 :=
  finalState_determ h1 (FinalState.intro r1 m)

/-! ### The run-level corollary, applied

`starE0_endpoint_unique` is the ∀-run-from-∃-run step.  Here it is on a concrete
two-step silent run: `Ssequence Sskip Sskip` under `Kstop`.  The exhibited run
ends in a state that cannot step, so *every* silent run from the start ends
there. -/

private def startState (f : Function) (m : Mem) : State :=
  .State f (.Ssequence .Sskip .Sskip) .Kstop emptyEnv PTree.empty m

example (m' : Mem)
    (hfree : Mem.freeList m (blocksOfEnv ge.genv_cenv emptyEnv) = some m')
    (send : State)
    (hrun : StarE0 (Step ge fe) (startState f m) send)
    (hstuck : ∀ t s', ¬ Step ge fe send t s') :
    send = .Returnstate .Vundef .Kstop m' := by
  refine starE0_endpoint_unique hfe hinj hrun ?_ hstuck ?_
  · exact StarE0.step _ _ _ (Step.seq _ _ _ _ _ _ _)
      (StarE0.step _ _ _ (Step.skip_seq _ _ _ _ _ _)
        (StarE0.step _ _ _ (Step.skip_call _ _ _ _ _ _ rfl hfree)
          (StarE0.refl _)))
  · intro t s' hs; cases hs

end Rules

/-! ### The whole-program record, on a real program

`semantics_determinate2 prog` is `Clight.semantics_determinate` for the program
generated from `test/lean/main.c`.  It needs no hypothesis: the symbol-table
injectivity CompCert keeps in its `Genv.t` record is recovered by
`Genv.symbInjective_globalenv`. -/

example : Determinate prog (FunctionEntry2 prog.globalenv) :=
  semantics_determinate2 prog

example : (Genv.toSenv prog.globalenv.genv_genv).SymbolsInjective :=
  program_symbolsInjective prog

/-- And the interpreter agrees with the relation wherever it steps — the
    completeness direction `CCLib.cfrontend.ClightExecSound` left open. -/
example (s s' s2 : State)
    (hi : doStep prog.globalenv s = some (E0, s'))
    (hr : Step prog.globalenv (FunctionEntry2 prog.globalenv) s E0 s2) : s' = s2 :=
  doStep_complete_E0 _ (program_symbolsInjective prog) hi hr

/-! ## Axiom guard, enforced

`#print axioms` only *reports*; this fails the build.  Three claims are checked:

* nothing anywhere depends on an axiom outside the allowed set — which also
  covers `sorryAx`, so this doubles as the no-`sorry` check;
* the two new axioms appear **only** where an external call can occur.  Anything
  that cannot reach `externalCall` — the whole expression layer, memory
  accesses, initial and final states, the recovered `Genv` invariant — must
  still typecheck against the old five;
* work that predates this change is unaffected: `IsSortedSep.is_sorted_satisfies`
  is a Phase-7.7 milestone proof and is held to the old set.

The two new axioms are also asserted to be *present* on `step_determ`, so this
file notices if the proof stops needing them (which would mean the external-call
family had been given semantics, and the axioms should then be removed rather
than left dangling).
-/

section AxiomGuard
open Lean

/-- Lean's own three, plus the two uninterpreted-external `Parameter`s that
    `CCLib.common.Events` has always had. -/
private def oldAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound,
   ``CC.externalFunctionsSem, ``CC.inlineAssemblySem]

private def newAxioms : List Name :=
  [``CC.externalFunctionsSemDeterm, ``CC.inlineAssemblySemDeterm]

/-- `n` depends on no axiom outside `allowed`. -/
private def axiomsWithin (allowed : List Name) (n : Name) : CoreM Unit := do
  let extra := (← collectAxioms n).toList.filter (· ∉ allowed)
  unless extra.isEmpty do
    throwError "{n} depends on unexpected axioms: {extra}"

private def axiomsContain (needed : List Name) (n : Name) : CoreM Unit := do
  let got := (← collectAxioms n).toList
  let missing := needed.filter (· ∉ got)
  unless missing.isEmpty do
    throwError "{n} no longer depends on {missing} — if the external-call \
      family has been given semantics, delete the axioms instead of keeping them"

-- (1) Nothing depends on anything beyond the old five plus the two new ones.
#eval [``CC.step_determ, ``CC.step_traces, ``CC.externalCall_determ,
       ``CC.doStep_complete, ``CC.doStep_complete_E0,
       ``CC.semantics_determinate1, ``CC.semantics_determinate2,
       ``CC.sstep_determ, ``CC.starE0_prefix, ``CC.starE0_endpoint_unique,
       ``CC.determinate_of_entryDeterm].forM (axiomsWithin (oldAxioms ++ newAxioms))

-- (2) The new axioms appear ONLY where an external call can occur.
#eval [``CC.eval_determ, ``CC.evalExpr_determ, ``CC.evalLvalue_determ,
       ``CC.evalExprlist_determ, ``CC.derefLoc_determ, ``CC.assignLoc_determ,
       ``CC.loadBitfield_determ, ``CC.storeBitfield_determ,
       ``CC.allocVariables_determ, ``CC.bindParameters_determ,
       ``CC.functionEntry1_determ, ``CC.functionEntry2_determ,
       ``CC.initialState_determ, ``CC.finalState_nostep, ``CC.finalState_determ,
       ``CC.eventValMatch_determ_1, ``CC.eventValMatch_determ_2,
       ``CC.volatileLoad_determ, ``CC.volatileStore_determ,
       ``CC.Genv.symbInjective_globalenv, ``CC.program_symbolsInjective,
       ``CC.vptrofs_inj,
       ``IsSortedSep.is_sorted_satisfies].forM (axiomsWithin oldAxioms)

-- (3) …and they really are load-bearing where they do appear.
#eval [``CC.step_determ, ``CC.externalCall_determ].forM (axiomsContain newAxioms)

end AxiomGuard

end DetermCheck
