/-
  Simulations for determinate languages — port of the sections
  `FORWARD_SIMU_EVENTUALLY`, `DETERMINACY`, `FORWARD_SIMU_DETERM` and
  `FORWARD_SIMU_DETERM_DIAGRAMS` of `common/Smallstep.v`.

  * `forward_simulation_eventually` (and `forward_simulation_eventually_plus`):
    the general "eventually" diagram, with
    an index and a well-founded order (the variants without an index are in
    `SimulationEventually.lean`).  The index of the resulting simulation is
    `index × Nat`, ordered lexicographically (`Prod.Lex`, Lean core).
  * `sd_determ_1`, `sd_determ_2`, `sd_determ_3`, `star_determinacy`.
  * `forward_simulation_determ` and its special cases
    `forward_simulation_determ_star`, `forward_simulation_determ_plus`,
    `forward_simulation_determ_one`: when the source language is determinate,
    the source may take extra silent steps after each simulated step.
-/
import CCLib.common.SimulationEventually

namespace CC
namespace Smallstep

/-! ## `FORWARD_SIMU_EVENTUALLY` -/

section ForwardEventuallyIndex
variable {L1 L2 : Semantics} {index : Type} (order : index → index → Prop)
  (match_states : index → L1.state → L2.state → Prop)

/-- `Smallstep.forward_simulation_eventually` -/
theorem forward_simulation_eventually (hwf : WellFounded order)
    (hinit : ∀ s1, L1.initial_state s1 → ∃ i s2, L2.initial_state s2 ∧ match_states i s1 s2)
    (hfinal : ∀ i s1 s2 r, match_states i s1 s2 → L1.final_state s1 r → L2.final_state s2 r)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ i s2, match_states i s1 s2 →
      ∃ n i' s2', (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ order i' i)) ∧
        Eventually L1.step L1.final_state n s1' (fun s1'' => match_states i' s1'' s2'))
    (hpub : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id) :
    ForwardSimulation L1 L2 := by
  let lex := Prod.lex (⟨order, hwf⟩ : WellFoundedRelation index)
    (⟨Nat.lt, Nat.lt_wfRel.wf⟩ : WellFoundedRelation Nat)
  refine ⟨index × Nat, lex.rel,
    fun i s1 s2 => Eventually L1.step L1.final_state i.2 s1 (fun s1'' => match_states i.1 s1'' s2),
    { order_wf := lex.wf
      initial_states := ?_
      final_states := ?_
      simulation := ?_
      public_preserved := hpub }⟩
  · intro s1 h
    obtain ⟨i, s2, h2, hm⟩ := hinit s1 h
    exact ⟨(i, 0), s2, h2, .now hm⟩
  · rintro ⟨i, n⟩ s1 s2 r hev hf
    cases hev with
    | now hm => exact hfinal _ _ _ _ hm hf
    | later hnf _ _ => exact absurd hf (hnf r)
  · rintro s1 t s1' hst ⟨i, n⟩ s2 hev
    cases hev with
    | now hm =>
      obtain ⟨n', i', s2', A, B⟩ := hsim s1 t s1' hst i s2 hm
      refine ⟨(i', n'), s2', ?_, B⟩
      rcases A with A | ⟨A1, A2⟩
      · exact .inl A
      · exact .inr ⟨A1, Prod.Lex.left _ _ A2⟩
    | later hnf hE0 hst' =>
      rename_i n0
      obtain rfl := hE0 t s1' hst
      exact ⟨(i, n0), s2, .inr ⟨.refl _, Prod.Lex.right _ (Nat.lt_succ_self n0)⟩, hst' _ s1' hst⟩

end ForwardEventuallyIndex

/-- `Smallstep.forward_simulation_eventually_plus` -/
theorem forward_simulation_eventually_plus {L1 L2 : Semantics}
    (match_states : L1.state → L2.state → Prop)
    (hinit : ∀ s1, L1.initial_state s1 → ∃ s2, L2.initial_state s2 ∧ match_states s1 s2)
    (hfinal : ∀ s1 s2 r, match_states s1 s2 → L1.final_state s1 r → L2.final_state s2 r)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      ∃ n s2', Plus L2.step s2 t s2' ∧
        Eventually L1.step L1.final_state n s1' (fun s1'' => match_states s1'' s2'))
    (hpub : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id) :
    ForwardSimulation L1 L2 :=
  forward_simulation_eventually (index := Nat) (· < ·) (fun _ s1 s2 => match_states s1 s2)
    Nat.lt_wfRel.wf
    (fun s1 h => let ⟨s2, A, B⟩ := hinit s1 h; ⟨0, s2, A, B⟩)
    (fun _ s1 s2 r hm hf => hfinal s1 s2 r hm hf)
    (fun s1 t s1' hst _ s2 hm =>
      let ⟨n, s2', A, B⟩ := hsim s1 t s1' hst s2 hm; ⟨n, 0, s2', .inl A, B⟩)
    hpub

/-! ## `DETERMINACY` -/

/-- Two traces of length at most one that match: if one is a prefix of the
    other in a common run, they are equal (the key step of
    `star_determinacy`). -/
private theorem match_single_app {ge : Senv} {t1 t2 t3 t4 : Trace}
    (hm : MatchTraces ge t1 t3) (l1 : t1.length ≤ 1) (l3 : t3.length ≤ 1)
    (heq : Eapp t1 t2 = Eapp t3 t4) : t1 = t3 ∧ t2 = t4 := by
  match t1, t3, l1, l3 with
  | [], [], _, _ => exact ⟨rfl, heq⟩
  | [], [_], _, _ => cases hm
  | [_], [], _, _ => cases hm
  | [a], [b], _, _ =>
    simp only [Eapp, List.singleton_append, List.cons.injEq] at heq
    exact ⟨by rw [heq.1], heq.2⟩


section Determinacy
variable {L : Semantics} (DET : Determinate L)
include DET

/-- `Smallstep.sd_determ_1` -/
theorem sd_determ_1 {s t1 s1 t2 s2} (h1 : L.step s t1 s1) (h2 : L.step s t2 s2) :
    MatchTraces L.symbolenv t1 t2 :=
  (DET.sd_determ s t1 s1 t2 s2 h1 h2).1

/-- `Smallstep.sd_determ_2` -/
theorem sd_determ_2 {s t s1 s2} (h1 : L.step s t s1) (h2 : L.step s t s2) : s1 = s2 :=
  (DET.sd_determ s t s1 t s2 h1 h2).2 rfl

/-- `Smallstep.sd_determ_3` -/
theorem sd_determ_3 {s t s1 s2} (h1 : L.step s t s1) (h2 : L.step s E0 s2) :
    t = E0 ∧ s1 = s2 := by
  have ⟨A, B⟩ := DET.sd_determ s t s1 E0 s2 h1 h2
  have ht : t = E0 := by cases A; rfl
  exact ⟨ht, B ht⟩

/-- `Smallstep.star_determinacy` -/
theorem star_determinacy {s t s'} (h : Star L.step s t s') :
    ∀ {s''}, Star L.step s t s'' → Star L.step s' E0 s'' ∨ Star L.step s'' E0 s' := by
  induction h with
  | refl s => intro s'' h; exact .inl h
  | @step s1 t1 s2 t2 s3 t hst _ heq ih =>
    intro s'' h
    cases h with
    | refl =>
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp heq.symm
      exact .inr (.step hst ‹_› rfl)
    | @step _ t3 s4 t4 _ _ hst' hstar' heq' =>
      have hm := sd_determ_1 DET hst hst'
      obtain ⟨rfl, rfl⟩ := match_single_app hm (DET.sd_traces _ _ _ hst)
        (DET.sd_traces _ _ _ hst') (heq.symm.trans heq')
      obtain rfl := sd_determ_2 DET hst hst'
      exact ih hstar'

end Determinacy

/-! ## `FORWARD_SIMU_DETERM` -/

section ForwardDeterm
variable {L1 L2 : Semantics} (L1det : Determinate L1) {index : Type}
  (order : index → index → Prop) (match_states : index → L1.state → L2.state → Prop)

include L1det in
/-- `Smallstep.star_match_eventually` -/
theorem star_match_eventually {s1 s1'} (h : Star L1.step s1 E0 s1') {i s2}
    (hm : match_states i s1' s2) :
    ∃ n, Eventually L1.step L1.final_state n s1 (fun s1'' => match_states i s1'' s2) := by
  refine star_E0_ind (R := L1.step)
    (fun a b => match_states i b s2 →
      ∃ n, Eventually L1.step L1.final_state n a (fun s1'' => match_states i s1'' s2))
    (fun s hm => ⟨0, .now hm⟩) ?_ h hm
  intro a b c hab ih hm
  obtain ⟨n, hev⟩ := ih hm
  refine ⟨n + 1, .later' (fun r hf => L1det.sd_final_nostep a r hf E0 b hab) ?_⟩
  intro t s' hst
  obtain ⟨rfl, rfl⟩ := sd_determ_3 L1det hst hab
  exact ⟨rfl, hev⟩

include L1det in
/-- `Smallstep.forward_simulation_determ` -/
theorem forward_simulation_determ (hwf : WellFounded order)
    (hinit : ∀ s1, L1.initial_state s1 → ∃ i s2, L2.initial_state s2 ∧ match_states i s1 s2)
    (hfinal : ∀ i s1 s2 r, match_states i s1 s2 → L1.final_state s1 r → L2.final_state s2 r)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ i s2, match_states i s1 s2 →
      ∃ s1'' i' s2', Star L1.step s1' E0 s1'' ∧
        (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ order i' i)) ∧
        match_states i' s1'' s2')
    (hpub : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id) :
    ForwardSimulation L1 L2 := by
  refine forward_simulation_eventually order match_states hwf hinit hfinal ?_ hpub
  intro s1 t s1' hst i s2 hm
  obtain ⟨s1'', i', s2', A, B, C⟩ := hsim s1 t s1' hst i s2 hm
  obtain ⟨n, D⟩ := star_match_eventually L1det match_states A C
  exact ⟨n, i', s2', B, D⟩

end ForwardDeterm

/-! ## `FORWARD_SIMU_DETERM_DIAGRAMS` -/

section ForwardDetermDiagrams
variable {L1 L2 : Semantics} (L1det : Determinate L1)
  (match_states : L1.state → L2.state → Prop)
  (hpub : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id)
  (hinit : ∀ s1, L1.initial_state s1 → ∃ s2, L2.initial_state s2 ∧ match_states s1 s2)
  (hfinal : ∀ s1 s2 r, match_states s1 s2 → L1.final_state s1 r → L2.final_state s2 r)
include L1det hpub hinit hfinal

/-- `Smallstep.forward_simulation_determ_star` -/
theorem forward_simulation_determ_star (measure : L1.state → Nat)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      ∃ s1'' s2', Star L1.step s1' E0 s1'' ∧
        (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ measure s1'' < measure s1)) ∧
        match_states s1'' s2') :
    ForwardSimulation L1 L2 := by
  refine forward_simulation_determ L1det (fun x y => measure x < measure y)
    (fun i s1 s2 => i = s1 ∧ match_states s1 s2) (InvImage.wf measure Nat.lt_wfRel.wf)
    ?_ ?_ ?_ hpub
  · intro s1 h
    obtain ⟨s2, A, B⟩ := hinit s1 h
    exact ⟨s1, s2, A, rfl, B⟩
  · rintro i s1 s2 r ⟨-, hm⟩ hf
    exact hfinal _ _ _ hm hf
  · rintro s1 t s1' hst i s2 ⟨rfl, hm⟩
    obtain ⟨s1'', s2', A, B, C⟩ := hsim i t s1' hst s2 hm
    exact ⟨s1'', s1'', s2', A, B, rfl, C⟩

/-- `Smallstep.forward_simulation_determ_plus` -/
theorem forward_simulation_determ_plus
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      ∃ s1'' s2', Star L1.step s1' E0 s1'' ∧ Plus L2.step s2 t s2' ∧ match_states s1'' s2') :
    ForwardSimulation L1 L2 :=
  forward_simulation_determ_star L1det match_states hpub hinit hfinal (fun _ => 0)
    fun s1 t s1' hst s2 hm =>
      let ⟨s1'', s2', A, B, C⟩ := hsim s1 t s1' hst s2 hm
      ⟨s1'', s2', A, .inl B, C⟩

/-- `Smallstep.forward_simulation_determ_one` -/
theorem forward_simulation_determ_one
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      ∃ s1'' s2', Star L1.step s1' E0 s1'' ∧ L2.step s2 t s2' ∧ match_states s1'' s2') :
    ForwardSimulation L1 L2 :=
  forward_simulation_determ_plus L1det match_states hpub hinit hfinal
    fun s1 t s1' hst s2 hm =>
      let ⟨s1'', s2', A, B, C⟩ := hsim s1 t s1' hst s2 hm
      ⟨s1'', s2', A, plus_one B, C⟩

end ForwardDetermDiagrams

end Smallstep
end CC
