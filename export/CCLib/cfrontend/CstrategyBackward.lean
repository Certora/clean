/-
  `cfrontend/Cstrategy.v`, continued: `step_simulation`, `progress` and
  `strategy_simulation` — the deterministic strategy semantics is a backward
  simulation of the nondeterministic CompCert C semantics `Csem.semantics`.
-/
import CCLib.cfrontend.CstrategySimulation
import CCLib.common.BackwardSimulation
namespace CC
namespace Cstrategy

section PROGRESS
variable {ge : Csem.CGenv}

theorem context_notVal {k to C a} (hC : Csem.Context k to C) (ha : NotVal a) : NotVal (C a) := by
  cases hC <;> first | exact ha | trivial

theorem lred_notVal {e a m a' m'} (h : Csem.Lred ge e a m a' m') : NotVal a := by
  cases h <;> trivial

theorem rred_notVal {a m t a' m'} (h : Csem.Rred ge a m t a' m') : NotVal a := by
  cases h <;> trivial

theorem callred_notVal {a m fd args ty} (h : Csem.Callred ge a m fd args ty) : NotVal a := by
  cases h <;> trivial

/-- `Cstrategy.step_simulation` -/
theorem step_simulation {S t S'} (h : Step ge S t S') : Smallstep.Plus (Csem.Step ge) S t S' := by
  rcases h with h | h
  · exact estep_simulation h
  · exact Smallstep.plus_one (.inr h)

/-- `Cstrategy.progress` -/
theorem progress {S} (hs : Safe ge S) :
    (∃ r, Csem.FinalState S r) ∨ (∃ t S', Step ge S t S') := by
  rcases hs S (.refl _) with hf | ⟨t, S', hst⟩
  · exact .inl hf
  right
  rcases hst with h | h
  · have : ∃ t S', Estep ge S t S' := by
      cases h with
      | lred C f a k e m a' m' hr hC => exact can_estep hs (context_notVal hC (lred_notVal hr))
      | rred C f a k e m t a' m' hr hC => exact can_estep hs (context_notVal hC (rred_notVal hr))
      | call C f a k e m fd vargs ty hr hC => exact can_estep hs (context_notVal hC (callred_notVal hr))
      | stuck C f a k e m K hC hn =>
        rcases hs .Stuckstate (Smallstep.star_one (.inl (.stuck C f a k e m K hC hn))) with
          ⟨r, hr⟩ | ⟨t, s'', hst⟩
        · cases hr
        · rcases hst with h | h <;> cases h
    obtain ⟨t', S'', h'⟩ := this
    exact ⟨t', S'', .inl h'⟩
  · exact ⟨t, S', .inr h⟩

end PROGRESS

/-- `Cstrategy.strategy_simulation`: the strategy-restricted semantics is a
    backward simulation of the full CompCert C semantics `Csem.semantics`. -/
theorem strategy_simulation (p : Csyntax.Program) :
    Smallstep.BackwardSimulation (Csem.semantics p) (semantics p) :=
  Smallstep.backward_simulation_plus (L1 := Csem.semantics p) (L2 := semantics p) (fun s1 s2 => s1 = s2)
    (fun _ => rfl)
    (fun s1 h => ⟨s1, h⟩)
    (fun _ s2 _ h2 => ⟨s2, h2, rfl⟩)
    (fun s1 s2 r hm hf => hm ▸ hf)
    (fun s1 s2 hm hs => by subst hm; exact progress hs)
    (fun s2 t s2' hst s1 hm _ => by subst hm; exact ⟨s2', step_simulation hst, rfl⟩)

end Cstrategy
end CC
