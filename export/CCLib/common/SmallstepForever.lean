/-
  Infinite executions — port of the `forever*` part of `common/Smallstep.v`
  (`forever`, `star_forever`, `forever_N`, `forever_plus`, `forever_silent_N`
  and the lemmas reducing them to `forever` / `forever_silent`).

  Rocq's `CoInductive` predicates are Lean `coinductive` predicates (greatest
  fixed points, with a generated `coinduct` principle), so the Rocq `cofix`
  proofs become applications of `coinduct` with the obvious invariant.

  `forever_silent` and `forever_reactive` already live in
  `CCLib.common.Smallstep` (as `ForeverSilent` / `ForeverReactive`, stated
  through an explicit sequence of states); `forever_silent_N_forever` concludes
  that existing `ForeverSilent`, through the coinduction principle
  `foreverSilent_coind`.  `forever_of_plus` (the empty-order case of
  `forever_N`) is what the big-step semantics (`CCLib.common.Bigstep`) uses.
-/
import CCLib.common.Smallstep

namespace CC
namespace Smallstep

variable {σ : Type}

/-! ## `forever`: infinitely many steps, silent or not -/

variable {R : σ → Trace → σ → Prop}

/-- `Smallstep.forever`: an infinite run from `s` with infinite trace `T`. -/
coinductive Forever (R : σ → Trace → σ → Prop) : σ → Traceinf → Prop where
  | intro {s1 t s2 T} : R s1 t s2 → Forever R s2 T → Forever R s1 (Eappinf t T)

/-- Coinduction with `plus` steps (Rocq: `forever_N_forever` instantiated with
    the empty order, together with `forever_N_plus`).  If every state/trace pair
    satisfying `P` can make at least one transition and land in `P` again, then
    `P` implies `Forever`. -/
theorem forever_of_plus (P : σ → Traceinf → Prop)
    (hP : ∀ s T, P s T → ∃ (s' : σ) (t : Trace) (T' : Traceinf),
      Plus R s t s' ∧ P s' T' ∧ T = Eappinf t T') :
    ∀ s T, P s T → Forever R s T := by
  intro s T hsT
  apply Forever.coinduct R
    (fun (s : σ) (T : Traceinf) => ∃ (s' : σ) (t : Trace) (T' : Traceinf),
      Star R s t s' ∧ P s' T' ∧ T = Eappinf t T')
  · intro s T ⟨s', t, T', hst, hP', hT⟩
    cases hst with
    | refl =>
      obtain ⟨s'', t'', T'', hplus, hP'', hT'⟩ := hP _ _ hP'
      cases hplus with
      | intro hr hs heq =>
        refine ⟨_, _, _, hr, ⟨s'', _, T'', hs, hP'', rfl⟩, ?_⟩
        subst heq; rw [hT, Eappinf_E0, hT', Eappinf_assoc]
    | step hr hs heq =>
      refine ⟨_, _, _, hr, ⟨s', _, T', hs, hP', rfl⟩, ?_⟩
      subst heq; rw [hT, Eappinf_assoc]
  · exact ⟨s, E0, T, .refl _, hsT, (Eappinf_E0 T).symm⟩

/-- Rewrite the trace of a run. -/
theorem Star.trace_cast {s1 t s2 t'} (h : Star R s1 t s2) (ht : t = t') : Star R s1 t' s2 :=
  ht ▸ h

/-- Inversion for `forever`. -/
theorem Forever.inv {s T} (h : Forever R s T) :
    ∃ t s' T', R s t s' ∧ Forever R s' T' ∧ T = Eappinf t T' := by
  cases h with
  | intro hr hf => exact ⟨_, _, _, hr, hf, rfl⟩

/-- `Smallstep.star_forever` -/
theorem star_forever {s1 t s2 T} (h1 : Star R s1 t s2) (h2 : Forever R s2 T) :
    Forever R s1 (Eappinf t T) := by
  induction h1 with
  | refl => rw [Eappinf_E0]; exact h2
  | step hr _ heq ih => subst heq; rw [Eappinf_assoc]; exact .intro R hr (ih h2)


/-! ## `forever_N`: steps may be `star` as long as a measure decreases -/

section ForeverN

variable {A : Type} (order : A → A → Prop)

/-- `Smallstep.forever_N`: an alternative definition of `forever` that is
    convenient for coinductive reasoning: each round is either a non-empty run
    (`plus`) or a possibly empty run (`star`) that decreases the measure `a`
    for the order `order`. -/
coinductive ForeverN (R : σ → Trace → σ → Prop) : A → σ → Traceinf → Prop where
  | star {s1 t s2 a1 a2 T1 T2} : Star R s1 t s2 → order a2 a1 → ForeverN R a2 s2 T2 →
      T1 = Eappinf t T2 → ForeverN R a1 s1 T1
  | plus {s1 t s2 a1 a2 T1 T2} : Plus R s1 t s2 → ForeverN R a2 s2 T2 →
      T1 = Eappinf t T2 → ForeverN R a1 s1 T1

variable {order}

/-- `Smallstep.forever_N_inv`: for a well-founded order, some first step can
    always be extracted. -/
theorem forever_N_inv (hwf : WellFounded order) {a s T} (h : ForeverN order R a s T) :
    ∃ t s' a' T', R s t s' ∧ ForeverN order R a' s' T' ∧ T = Eappinf t T' := by
  induction a using hwf.induction generalizing s T with
  | _ a ih =>
  cases h with
  | star hs hord hf hT =>
    cases hs with
    | refl => rw [Eappinf_E0] at hT; subst hT; exact ih _ hord hf
    | step h1 h2 heq =>
      subst heq hT
      exact ⟨_, _, a, _, h1, .star _ _ h2 hord hf rfl, Eappinf_assoc _ _ _⟩
  | @plus _ _ _ _ a2 _ _ hp hf hT =>
    cases hp with
    | intro h1 h2 heq =>
      subst heq hT
      refine ⟨_, _, a2, _, h1, ?_, Eappinf_assoc _ _ _⟩
      cases star_inv h2 with
      | inl h => obtain ⟨rfl, rfl⟩ := h; rw [Eappinf_E0]; exact hf
      | inr h => exact .plus _ _ h hf rfl

/-- `Smallstep.forever_N_forever` -/
theorem forever_N_forever (hwf : WellFounded order) {a s T} (h : ForeverN order R a s T) :
    Forever R s T := by
  refine Forever.coinduct R (fun s T => ∃ a, ForeverN order R a s T) (fun s T hP => ?_) _ _ ⟨a, h⟩
  obtain ⟨a, ha⟩ := hP
  obtain ⟨t, s', a', T', h1, h2, h3⟩ := forever_N_inv hwf ha
  exact ⟨t, s', T', h1, ⟨a', h2⟩, h3⟩

end ForeverN

/-! ## `forever_plus`: infinitely many non-empty runs -/

/-- `Smallstep.forever_plus` -/
coinductive ForeverPlus (R : σ → Trace → σ → Prop) : σ → Traceinf → Prop where
  | intro {s1 t s2 T1 T2} : Plus R s1 t s2 → ForeverPlus R s2 T2 → T1 = Eappinf t T2 →
      ForeverPlus R s1 T1

/-- `Smallstep.forever_plus_inv` -/
theorem forever_plus_inv {s T} (h : ForeverPlus R s T) :
    ∃ s' t T', R s t s' ∧ ForeverPlus R s' T' ∧ T = Eappinf t T' := by
  cases h with
  | intro hp hf hT =>
    cases hp with
    | intro h1 h2 heq =>
      subst heq hT
      refine ⟨_, _, _, h1, ?_, Eappinf_assoc _ _ _⟩
      cases star_inv h2 with
      | inl h => obtain ⟨rfl, rfl⟩ := h; rwa [Eappinf_E0]
      | inr h => exact .intro _ h hf rfl

/-- `Smallstep.forever_plus_forever` -/
theorem forever_plus_forever {s T} (h : ForeverPlus R s T) : Forever R s T := by
  refine Forever.coinduct R (fun s T => ForeverPlus R s T) (fun s T hP => ?_) _ _ h
  obtain ⟨s', t, T', h1, h2, h3⟩ := forever_plus_inv hP
  exact ⟨t, s', T', h1, h2, h3⟩

/-! ## `forever_silent_N` -/

/-- Coinduction principle for `forever_silent`. -/
theorem foreverSilent_coind (P : σ → Prop) (hP : ∀ s, P s → ∃ s', R s E0 s' ∧ P s') :
    ∀ s, P s → ForeverSilent R s := by
  intro s hs
  let next : {x // P x} → {x // P x} := fun x =>
    ⟨Classical.choose (hP x.1 x.2), (Classical.choose_spec (hP x.1 x.2)).2⟩
  let g : Nat → {x // P x} := fun n => Nat.rec ⟨s, hs⟩ (fun _ x => next x) n
  exact ⟨fun n => (g n).1, rfl, fun n => (Classical.choose_spec (hP (g n).1 (g n).2)).1⟩

section ForeverSilentN

variable {A : Type} (order : A → A → Prop)

/-- `Smallstep.forever_silent_N` -/
coinductive ForeverSilentN (R : σ → Trace → σ → Prop) : A → σ → Prop where
  | star {s1 s2 a1 a2} : Star R s1 E0 s2 → order a2 a1 → ForeverSilentN R a2 s2 →
      ForeverSilentN R a1 s1
  | plus {s1 s2 a1 a2} : Plus R s1 E0 s2 → ForeverSilentN R a2 s2 → ForeverSilentN R a1 s1

variable {order}

private theorem Eapp_E0_inv' {t1 t2 : Trace} (h : E0 = Eapp t1 t2) : t1 = E0 ∧ t2 = E0 := by
  simp only [E0, Eapp] at h
  exact List.append_eq_nil_iff.mp h.symm

/-- `Smallstep.forever_silent_N_inv` -/
theorem forever_silent_N_inv (hwf : WellFounded order) {a s}
    (h : ForeverSilentN order R a s) :
    ∃ s' a', R s E0 s' ∧ ForeverSilentN order R a' s' := by
  induction a using hwf.induction generalizing s with
  | _ a ih =>
  cases h with
  | star hs hord hf =>
    cases hs with
    | refl => exact ih _ hord hf
    | step h1 h2 heq =>
      obtain ⟨rfl, rfl⟩ := Eapp_E0_inv' heq
      exact ⟨_, a, h1, .star _ _ h2 hord hf⟩
  | @plus _ _ _ a2 hp hf =>
    cases hp with
    | intro h1 h2 heq =>
      obtain ⟨rfl, rfl⟩ := Eapp_E0_inv' heq
      refine ⟨_, a2, h1, ?_⟩
      cases star_inv h2 with
      | inl h => obtain ⟨rfl, -⟩ := h; exact hf
      | inr h => exact .plus _ _ h hf

/-- `Smallstep.forever_silent_N_forever` -/
theorem forever_silent_N_forever (hwf : WellFounded order) {a s}
    (h : ForeverSilentN order R a s) : ForeverSilent R s := by
  refine foreverSilent_coind (fun s => ∃ a, ForeverSilentN order R a s) (fun s hP => ?_) _ ⟨a, h⟩
  obtain ⟨a, ha⟩ := hP
  obtain ⟨s', a', h1, h2⟩ := forever_silent_N_inv hwf ha
  exact ⟨s', h1, a', h2⟩

end ForeverSilentN

/-- Divergence from a cycle of non-empty silent runs: an invariant that always
    allows one more `plus` silent run gives `forever_silent` (the
    `forever_silent_N_plus` case of `forever_silent_N`, with no measure). -/
theorem forever_silent_of_plus (P : σ → Prop) (hP : ∀ s, P s → ∃ s', Plus R s E0 s' ∧ P s')
    {s} (h : P s) : ForeverSilent R s := by
  have hwf : WellFounded (fun (_ _ : Unit) => False) := ⟨fun _ => Acc.intro _ (fun _ h => h.elim)⟩
  refine forever_silent_N_forever hwf (a := ())
    (ForeverSilentN.coinduct _ _ (fun _ s => P s) (fun _ s hs => ?_) () s h)
  obtain ⟨s', h1, h2⟩ := hP s hs
  exact Or.inr ⟨s', (), h1, h2⟩

/-- A silent infinite run is a `forever` run, for any infinite trace (as in
    Rocq, where `forever_silent` runs satisfy `forever` for every `T`). -/
theorem forever_silent_forever {s} (h : ForeverSilent R s) (T : Traceinf) : Forever R s T := by
  refine Forever.coinduct R (fun s T => ForeverSilent R s) (fun s T hP => ?_) _ _ h
  obtain ⟨s', h1, h2⟩ := hP.inv
  exact ⟨E0, s', T, h1, h2, (Eappinf_E0 T).symm⟩

end Smallstep
end CC
