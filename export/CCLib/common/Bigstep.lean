/-
  Big-step semantics and infinite runs — the parts of `common/Smallstep.v`
  (`forever`, `forever_plus`) and `common/Behaviors.v` (`bigstep_semantics`,
  `bigstep_sound`, `behavior_bigstep_terminates`, `behavior_bigstep_diverges`)
  that `cfrontend/ClightBigstep.v` relies on.

  `Forever` (Rocq's coinductive `forever`) and its coinduction principles
  (`forever_of_plus`, `foreverSilent_coind`) are in `CCLib.common.SmallstepForever`.
-/
import CCLib.common.Behaviors
import CCLib.common.SmallstepForever

namespace CC
namespace Smallstep

variable {σ : Type} {R : σ → Trace → σ → Prop}

/-! ## Silent or reactive (`Behaviors.v`, `forever_silent_or_reactive`) -/

/-- Coinduction principle for `forever_reactive`. -/
theorem foreverReactive_coind (P : σ → Traceinf → Prop)
    (hP : ∀ s T, P s T → ∃ (s' : σ) (t : Trace) (T' : Traceinf),
      Star R s t s' ∧ t ≠ E0 ∧ P s' T' ∧ T = Eappinf t T') :
    ∀ s T, P s T → ForeverReactive R s T := by
  intro s T hsT
  let X := {p : σ × Traceinf // P p.1 p.2}
  let next : X → X := fun x =>
    ⟨(Classical.choose (hP x.1.1 x.1.2 x.2),
      Classical.choose (Classical.choose_spec (Classical.choose_spec (hP x.1.1 x.1.2 x.2)))),
     (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (hP x.1.1 x.1.2 x.2)))).2.2.1⟩
  let tr : X → Trace := fun x => Classical.choose (Classical.choose_spec (hP x.1.1 x.1.2 x.2))
  have hnext : ∀ x : X, Star R x.1.1 (tr x) (next x).1.1 ∧ tr x ≠ E0 ∧
      x.1.2 = Eappinf (tr x) (next x).1.2 := fun x =>
    let h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (hP x.1.1 x.1.2 x.2)))
    ⟨h.1, h.2.1, h.2.2.2⟩
  let g : Nat → X := fun n => Nat.rec ⟨(s, T), hsT⟩ (fun _ x => next x) n
  let ts : Nat → Trace := fun n => tr (g n)
  have hT : ∀ n, T = Eappinf (prefixTrace ts n) (g n).1.2 := by
    intro n
    induction n with
    | zero => exact (Eappinf_E0 T).symm
    | succ n ih =>
      rw [ih, (hnext (g n)).2.2]
      show _ = Eappinf (Eapp (prefixTrace ts n) (ts n)) _
      rw [Eappinf_assoc]
  refine ⟨fun n => (g n).1.1, ts, rfl, fun n => ⟨(hnext (g n)).1, (hnext (g n)).2.1⟩, ?_⟩
  intro n
  rw [hT n]
  exact isPrefix_Eappinf _ _

/-- `Behaviors.forever_silent_or_reactive` (classical): an infinite run either
    reacts forever, or performs a finite trace and then diverges silently. -/
theorem forever_silent_or_reactive {s T} (h : Forever R s T) :
    ForeverReactive R s T ∨
    ∃ t s' T', Star R s t s' ∧ ForeverSilent R s' ∧ T = Eappinf t T' := by
  let A : σ → Traceinf → Prop := fun s T =>
    ∃ t s' T', Star R s t s' ∧ ForeverSilent R s' ∧ T = Eappinf t T'
  by_cases hA : A s T
  · exact Or.inr hA
  · left
    apply foreverReactive_coind (fun s T => Forever R s T ∧ ¬ A s T) _ s T ⟨h, hA⟩
    intro s T ⟨hf, hnA⟩
    apply Classical.byContradiction
    intro hno
    apply hnA
    refine ⟨E0, s, T, .refl _, ?_, (Eappinf_E0 T).symm⟩
    apply foreverSilent_coind (fun x => Star R s E0 x ∧ Forever R x T) _ s ⟨.refl _, hf⟩
    intro x ⟨hsx, hfx⟩
    obtain ⟨t, x', T', hr, hf', hT⟩ := hfx.inv
    by_cases ht : t = E0
    · subst ht
      rw [Eappinf_E0] at hT; subst hT
      exact ⟨x', hr, star_right hsx hr rfl, hf'⟩
    · exfalso
      apply hno
      refine ⟨x', t, T', star_right hsx hr rfl, ht, ⟨hf', ?_⟩, hT⟩
      intro ⟨t2, s2, T2, h2, hs2, hT2⟩
      apply hnA
      refine ⟨Eapp t t2, s2, T2, star_trans (star_right hsx hr rfl) h2 rfl, hs2, ?_⟩
      rw [hT, hT2, Eappinf_assoc]

/-! ## Big-step semantics (`Behaviors.v`) -/

/-- `Behaviors.bigstep_semantics`: a big-step semantics is given by its
    terminating and its diverging executions. -/
structure BigstepSemantics where
  bigstep_terminates : Trace → Integers.Int → Prop
  bigstep_diverges : Traceinf → Prop

/-- `Behaviors.bigstep_sound`: every big-step execution is matched by a run of
    the transition semantics `L`. -/
structure BigstepSound (B : BigstepSemantics) (L : Semantics) : Prop where
  bigstep_terminates_sound : ∀ t r, B.bigstep_terminates t r →
    ∃ s1 s2, L.initial_state s1 ∧ Star L.step s1 t s2 ∧ L.final_state s2 r
  bigstep_diverges_sound : ∀ T, B.bigstep_diverges T →
    ∃ s1, L.initial_state s1 ∧ Forever L.step s1 T

open ProgramBehavior

/-- `Behaviors.behavior_bigstep_terminates` -/
theorem behavior_bigstep_terminates {B : BigstepSemantics} {L : Semantics}
    (hsound : BigstepSound B L) {t r} (h : B.bigstep_terminates t r) :
    ProgramBehaves L (Terminates t r) := by
  obtain ⟨s1, s2, hi, hs, hf⟩ := hsound.bigstep_terminates_sound t r h
  exact .runs hi (.terminates hs hf)

/-- `Behaviors.behavior_bigstep_diverges`: a diverging big-step execution is
    either a reactive behaviour of `L`, or a silent divergence after a finite
    prefix `t` of its trace (`traceinf_prefix t T`). -/
theorem behavior_bigstep_diverges {B : BigstepSemantics} {L : Semantics}
    (hsound : BigstepSound B L) {T} (h : B.bigstep_diverges T) :
    ProgramBehaves L (Reacts T) ∨
    ∃ t, ProgramBehaves L (Diverges t) ∧ ∃ T', T = Eappinf t T' := by
  obtain ⟨s1, hi, hf⟩ := hsound.bigstep_diverges_sound T h
  rcases forever_silent_or_reactive hf with hr | ⟨t, s', T', hs, hsil, hT⟩
  · exact Or.inl (.runs hi (.reacts hr))
  · exact Or.inr ⟨t, .runs hi (.diverges hs hsil), T', hT⟩

end Smallstep
end CC
