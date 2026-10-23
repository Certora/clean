/-
  A small tactic used by the determinism proofs of the intermediate languages
  (the analogue of the `Determ` Ltac in `backend/Cminor.v` and friends).

  `determ_using [l₁, …, lₙ]` repeatedly looks for two hypotheses `h₁ h₂` such
  that some `lᵢ h₁ h₂ : x = y` typechecks with `x` and `y` different, adds that
  equation and substitutes it.  Each `lᵢ` must have the shape
  `P … v → P … v' → v' = v` (or `v = v'`), e.g. `evalExpr_determ`.
-/
import Lean

namespace CC
open Lean Elab Tactic Meta

/-- One round of `determ_using`: returns `true` if it made progress. -/
private def determRound (lemmas : Array Name) : TacticM Bool := withMainContext do
  let lctx ← getLCtx
  let hs := lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
  for h1 in hs do
    for h2 in hs do
      if h1 == h2 then continue
      for lem in lemmas do
        let r ← observing? do
          let pf ← mkAppM lem #[mkFVar h1, mkFVar h2]
          let ty ← instantiateMVars (← inferType pf)
          if ty.hasExprMVar then throwError "mvars"
          let some (_, l, r) := ty.eq? | throwError "not an equation"
          if l == r then throwError "trivial"
          let g ← getMainGoal
          let (fv, g') ← (← g.assert `hdet ty pf).intro1P
          let g'' ← substCore g' fv (symm := false) (tryToSkip := true) <|>
            substCore g' fv (symm := true) (tryToSkip := true)
          return g''.2
        if let some g := r then
          replaceMainGoal [g]
          return true
  return false

/-- `determ_using [l₁, …]`: see the module docstring. -/
elab "determ_using " "[" ls:ident,* "]" : tactic => do
  let names ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let mut fuel := 50
  while fuel > 0 do
    fuel := fuel - 1
    unless ← determRound names do break

/-- Two `some`-equations with the same left-hand side have equal payloads. -/
theorem some_eq_some_inj {α : Type _} {x : Option α} {a b : α} (h1 : x = some a)
    (h2 : x = some b) : a = b := Option.some.inj (h1.symm.trans h2)

/-- `pair_using t as h`: find two distinct hypotheses `h₁ h₂` such that `t h₁ h₂`
    typechecks without leftover metavariables and add it as hypothesis `h`. -/
elab "pair_using " t:term " as " n:ident : tactic => withMainContext do
  let f ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let lctx ← getLCtx
  let hs := lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
  for h1 in hs do
    for h2 in hs do
      if h1 == h2 then continue
      let r ← observing? do
        let pf0 := mkApp2 f (mkFVar h1) (mkFVar h2)
        Meta.check pf0
        let pf ← instantiateMVars pf0
        let ty ← instantiateMVars (← inferType pf)
        if ty.hasExprMVar || pf.hasExprMVar then throwError "mvars"
        let g ← getMainGoal
        let (_, g') ← (← g.assert n.getId ty pf).intro1P
        return g'
      if let some g := r then
        replaceMainGoal [g]
        return
  throwError "pair_using: no matching pair of hypotheses"

end CC
