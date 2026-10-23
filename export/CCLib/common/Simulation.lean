/-
  Forward simulations — port of the simulation part of `common/Smallstep.v`
  (`fsim_properties`, `forward_simulation`, the lock-step / plus / star / opt
  constructors, `compose_forward_simulations`) and of the forward-simulation
  half of `common/Behaviors.v` (`forward_simulation_behavior_improves`,
  `forward_simulation_same_safe_behavior`).

  Rocq's `Forward_simulation` record with an existential index type becomes
  `ForwardSimulation L1 L2 : Prop`, an existential over the index type, the
  order and the matching relation.  Rocq's coinductive proofs about
  `forever_silent`/`forever_reactive` become proofs that build the infinite
  run explicitly (`ForeverSilent.coind`, `simulation_forever_reactive`).
-/
import CCLib.common.Behaviors

namespace CC
namespace Smallstep

open ProgramBehavior

/-! ## Auxiliary facts about runs -/

section Runs
variable {σ : Type} {R : σ → Trace → σ → Prop}

/-- Coinduction principle for `forever_silent`: an invariant that always allows
one more silent step yields an infinite silent run. -/
theorem ForeverSilent.coind (P : σ → Prop) (h : ∀ x, P x → ∃ y, R x E0 y ∧ P y)
    {s : σ} (hs : P s) : ForeverSilent R s := by
  have next : ∀ x : {x // P x}, ∃ y : {y // P y}, R x.1 E0 y.1 := by
    intro ⟨x, hx⟩
    obtain ⟨y, hy, hp⟩ := h x hx
    exact ⟨⟨y, hp⟩, hy⟩
  let g : Nat → {x // P x} := fun n =>
    Nat.rec ⟨s, hs⟩ (fun _ x => Classical.choose (next x)) n
  exact ⟨fun n => (g n).1, rfl, fun n => Classical.choose_spec (next (g n))⟩

theorem Eapp_eq_E0 {t1 t2 : Trace} (h : Eapp t1 t2 = E0) : t1 = E0 ∧ t2 = E0 := by
  simp only [Eapp, E0] at h
  exact List.append_eq_nil_iff.mp h

/-- A silent `plus` starts with a silent step. -/
theorem plus_E0_inv {s1 s2 : σ} (h : Plus R s1 E0 s2) :
    ∃ y, R s1 E0 y ∧ Star R y E0 s2 := by
  obtain ⟨hr, hs, ht⟩ := h
  obtain ⟨h1, h2⟩ := Eapp_eq_E0 ht.symm
  subst h1; subst h2
  exact ⟨_, hr, hs⟩

end Runs

/-! ## Forward simulations (`Smallstep.v`) -/

/-- `Smallstep.fsim_properties` -/
structure FSimProperties (L1 L2 : Semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → L1.state → L2.state → Prop) : Prop where
  order_wf : WellFounded order
  initial_states : ∀ s1, L1.initial_state s1 →
    ∃ i s2, L2.initial_state s2 ∧ match_states i s1 s2
  final_states : ∀ i s1 s2 r, match_states i s1 s2 → L1.final_state s1 r → L2.final_state s2 r
  simulation : ∀ s1 t s1', L1.step s1 t s1' → ∀ i s2, match_states i s1 s2 →
    ∃ i' s2', (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ order i' i)) ∧
      match_states i' s1' s2'
  public_preserved : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id

/-- `Smallstep.forward_simulation`: there is an index type, a well-founded
order and a matching relation with the properties above. -/
def ForwardSimulation (L1 L2 : Semantics) : Prop :=
  ∃ (index : Type) (order : index → index → Prop)
    (match_states : index → L1.state → L2.state → Prop),
    FSimProperties L1 L2 index order match_states

section FSim
variable {L1 L2 : Semantics} {index : Type} {order : index → index → Prop}
  {match_states : index → L1.state → L2.state → Prop}
  (S : FSimProperties L1 L2 index order match_states)
include S

/-- `Smallstep.fsim_simulation'` -/
theorem FSimProperties.simulation' {s1 t s1'} (hst : L1.step s1 t s1') {i s2}
    (hm : match_states i s1 s2) :
    (∃ i' s2', Plus L2.step s2 t s2' ∧ match_states i' s1' s2') ∨
    (∃ i', order i' i ∧ t = E0 ∧ match_states i' s1' s2) := by
  obtain ⟨i', s2', hs | ⟨hs, ho⟩, hm'⟩ := S.simulation _ _ _ hst i s2 hm
  · exact Or.inl ⟨i', s2', hs, hm'⟩
  · rcases star_inv hs with ⟨rfl, rfl⟩ | hp
    · exact Or.inr ⟨i', ho, rfl, hm'⟩
    · exact Or.inl ⟨i', s2', hp, hm'⟩

/-- `Smallstep.simulation_star` -/
theorem FSimProperties.simulation_star {s1 t s1'} (hst : Star L1.step s1 t s1') :
    ∀ {i s2}, match_states i s1 s2 → ∃ i' s2', Star L2.step s2 t s2' ∧ match_states i' s1' s2' := by
  induction hst with
  | refl s => intro i s2 hm; exact ⟨i, s2, .refl _, hm⟩
  | step hr _ heq ih =>
    intro i s2 hm
    obtain ⟨i', s2', hs, hm'⟩ := S.simulation _ _ _ hr i s2 hm
    obtain ⟨i'', s2'', hs', hm''⟩ := ih hm'
    rcases hs with hp | ⟨hs, _⟩
    · exact ⟨i'', s2'', star_trans (plus_star hp) hs' heq, hm''⟩
    · exact ⟨i'', s2'', star_trans hs hs' heq, hm''⟩

theorem FSimProperties.simulation_plus_aux {s2_1 t2 s1'} (hs : Star L1.step s2_1 t2 s1') :
    ∀ {s1 t1}, L1.step s1 t1 s2_1 → ∀ {i s2}, match_states i s1 s2 →
    (∃ i' s2', Plus L2.step s2 (Eapp t1 t2) s2' ∧ match_states i' s1' s2') ∨
    (∃ i', Relation.TransGen order i' i ∧ Eapp t1 t2 = E0 ∧ match_states i' s1' s2) := by
  induction hs with
  | refl s =>
    intro s1 t1 hr i s2 hm
    rw [E0_right]
    rcases S.simulation' hr hm with ⟨i', s2', hp', hm'⟩ | ⟨i', ho, rfl, hm'⟩
    · exact Or.inl ⟨i', s2', hp', hm'⟩
    · exact Or.inr ⟨i', .single ho, rfl, hm'⟩
  | step hr2 hs2 heq2 ih =>
    intro s1 t1 hr i s2 hm
    rcases S.simulation' hr hm with ⟨i', s2', hp', hm'⟩ | ⟨i', ho, rfl, hm'⟩
    · obtain ⟨i'', s2'', hs'', hm''⟩ := S.simulation_star (Star.step hr2 hs2 heq2) hm'
      exact Or.inl ⟨i'', s2'', plus_star_trans hp' hs'' rfl, hm''⟩
    · rw [E0_left, heq2]
      rcases ih hr2 hm' with ⟨i'', s2'', hp'', hm''⟩ | ⟨i'', ho', h0, hm''⟩
      · exact Or.inl ⟨i'', s2'', hp'', hm''⟩
      · exact Or.inr ⟨i'', .tail ho' ho, h0, hm''⟩

/-- `Smallstep.simulation_plus` -/
theorem FSimProperties.simulation_plus {s1 t s1'} (hp : Plus L1.step s1 t s1') {i s2}
    (hm : match_states i s1 s2) :
    (∃ i' s2', Plus L2.step s2 t s2' ∧ match_states i' s1' s2') ∨
    (∃ i', Relation.TransGen order i' i ∧ t = E0 ∧ match_states i' s1' s2) := by
  obtain ⟨hr, hs, heq⟩ := hp
  subst heq
  exact S.simulation_plus_aux hs hr hm

/-! ### Divergence is preserved -/

/-- One matched pair of silently diverging / matching states always yields at
least one silent step of `L2` (by well-founded induction on the index). -/
theorem FSimProperties.forever_silent_plus :
    ∀ i s1 s2, ForeverSilent L1.step s1 → match_states i s1 s2 →
      ∃ i' s1' s2', Plus L2.step s2 E0 s2' ∧ ForeverSilent L1.step s1' ∧
        match_states i' s1' s2' := by
  intro i
  induction i using S.order_wf.induction with
  | _ i ih =>
    intro s1 s2 hf hm
    obtain ⟨s1', hr, hf'⟩ := hf.inv
    rcases S.simulation' hr hm with ⟨i', s2', hp, hm'⟩ | ⟨i', ho, _, hm'⟩
    · exact ⟨i', s1', s2', hp, hf', hm'⟩
    · exact ih i' ho s1' s2 hf' hm'

/-- `Smallstep.simulation_forever_silent` -/
theorem FSimProperties.simulation_forever_silent {i s1 s2} (hf : ForeverSilent L1.step s1)
    (hm : match_states i s1 s2) : ForeverSilent L2.step s2 := by
  apply ForeverSilent.coind
    (fun x => ∃ i s1 s2, ForeverSilent L1.step s1 ∧ match_states i s1 s2 ∧ Star L2.step x E0 s2)
  · intro x ⟨i, s1, s2, hf, hm, hx⟩
    obtain ⟨i', s1', s2', hp, hf', hm'⟩ := S.forever_silent_plus i s1 s2 hf hm
    obtain ⟨y, hy, hys⟩ := plus_E0_inv (star_plus_trans hx hp rfl)
    exact ⟨y, hy, i', s1', s2', hf', hm', hys⟩
  · exact ⟨i, s1, s2, hf, hm, .refl _⟩

/-- `Smallstep.simulation_forever_reactive` -/
theorem FSimProperties.simulation_forever_reactive {i s1 s2 T}
    (hf : ForeverReactive L1.step s1 T) (hm : match_states i s1 s2) :
    ForeverReactive L2.step s2 T := by
  obtain ⟨f, ts, hf0, hstep, hT⟩ := hf
  subst hf0
  have next : ∀ n (p : {p : index × L2.state // match_states p.1 (f n) p.2}),
      ∃ q : {q : index × L2.state // match_states q.1 (f (n + 1)) q.2},
        Star L2.step p.1.2 (ts n) q.1.2 := by
    intro n ⟨⟨i, s2⟩, hm⟩
    obtain ⟨i', s2', hs, hm'⟩ := S.simulation_star (hstep n).1 hm
    exact ⟨⟨(i', s2'), hm'⟩, hs⟩
  let g : (n : Nat) → {p : index × L2.state // match_states p.1 (f n) p.2} := fun n =>
    Nat.rec (motive := fun n => {p : index × L2.state // match_states p.1 (f n) p.2})
      ⟨(i, s2), hm⟩ (fun n p => Classical.choose (next n p)) n
  exact ⟨fun n => (g n).1.2, ts, rfl,
    fun n => ⟨Classical.choose_spec (next n (g n)), (hstep n).2⟩, hT⟩

/-! ### Behaviours are improved (`Behaviors.v`) -/

/-- `Behaviors.forward_simulation_state_behaves` -/
theorem FSimProperties.state_behaves {i s1 s2 beh1} (hm : match_states i s1 s2)
    (hb : StateBehaves L1 s1 beh1) :
    ∃ beh2, StateBehaves L2 s2 beh2 ∧ behavior_improves beh1 beh2 := by
  cases hb with
  | terminates hs hfin =>
    obtain ⟨i', s2', hs', hm'⟩ := S.simulation_star hs hm
    exact ⟨_, .terminates hs' (S.final_states _ _ _ _ hm' hfin), behavior_improves_refl _⟩
  | diverges hs hfs =>
    obtain ⟨i', s2', hs', hm'⟩ := S.simulation_star hs hm
    exact ⟨_, .diverges hs' (S.simulation_forever_silent hfs hm'), behavior_improves_refl _⟩
  | reacts hfr =>
    exact ⟨_, .reacts (S.simulation_forever_reactive hfr hm), behavior_improves_refl _⟩
  | @goes_wrong t s1' hs _ _ =>
    obtain ⟨i', s2', hs', hm'⟩ := S.simulation_star hs hm
    obtain ⟨beh', hb'⟩ := state_behaves_exists L2 s2'
    exact ⟨_, state_behaves_app hs' hb', Or.inr ⟨t, rfl, beh', rfl⟩⟩

end FSim

/-- `Behaviors.forward_simulation_behavior_improves`: every behaviour of the
source is improved by some behaviour of the target. -/
theorem forward_simulation_behavior_improves {L1 L2 : Semantics}
    (S : ForwardSimulation L1 L2) {beh1} (hb : ProgramBehaves L1 beh1) :
    ∃ beh2, ProgramBehaves L2 beh2 ∧ behavior_improves beh1 beh2 := by
  obtain ⟨index, order, match_states, S⟩ := S
  cases hb with
  | runs hi hs =>
    obtain ⟨i, s2, hi2, hm⟩ := S.initial_states _ hi
    obtain ⟨beh2, hb2, himp⟩ := S.state_behaves hm hs
    exact ⟨beh2, .runs hi2 hb2, himp⟩
  | goes_initially_wrong _ =>
    obtain ⟨beh2, hb2⟩ := program_behaves_exists L2
    exact ⟨beh2, hb2, behavior_improves_bot _⟩

/-- `Behaviors.forward_simulation_same_safe_behavior`: a behaviour of the source
that does not go wrong is a behaviour of the target. -/
theorem forward_simulation_same_safe_behavior {L1 L2 : Semantics}
    (S : ForwardSimulation L1 L2) {beh} (hb : ProgramBehaves L1 beh) (hnw : beh.not_wrong) :
    ProgramBehaves L2 beh := by
  obtain ⟨beh2, hb2, himp⟩ := forward_simulation_behavior_improves S hb
  rcases himp with rfl | ⟨t, rfl, _⟩
  · exact hb2
  · exact hnw.elim

/-! ## Constructing forward simulations -/

section Constructors
variable {L1 L2 : Semantics} (match_states : L1.state → L2.state → Prop)
  (hpub : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id)
  (hinit : ∀ s1, L1.initial_state s1 → ∃ s2, L2.initial_state s2 ∧ match_states s1 s2)
  (hfinal : ∀ s1 s2 r, match_states s1 s2 → L1.final_state s1 r → L2.final_state s2 r)
include hpub hinit hfinal

/-- `Smallstep.forward_simulation_star_wf`: the general constructor with a
well-founded order on source states. -/
theorem forward_simulation_star_wf (order : L1.state → L1.state → Prop)
    (hwf : WellFounded order)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      ∃ s2', (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ order s1' s1)) ∧
        match_states s1' s2') :
    ForwardSimulation L1 L2 :=
  ⟨L1.state, order, fun i s1 s2 => i = s1 ∧ match_states s1 s2,
    { order_wf := hwf
      initial_states := fun s1 h => by
        obtain ⟨s2, h2, hm⟩ := hinit s1 h
        exact ⟨s1, s2, h2, rfl, hm⟩
      final_states := fun i s1 s2 r ⟨_, hm⟩ hf => hfinal s1 s2 r hm hf
      simulation := fun s1 t s1' hst i s2 ⟨hi, hm⟩ => by
        obtain ⟨s2', hs, hm'⟩ := hsim s1 t s1' hst s2 hm
        exact ⟨s1', s2', by rw [hi]; exact hs, rfl, hm'⟩
      public_preserved := hpub }⟩

/-- `Smallstep.forward_simulation_star`: stuttering steps decrease a measure. -/
theorem forward_simulation_star (measure : L1.state → Nat)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      (∃ s2', Plus L2.step s2 t s2' ∧ match_states s1' s2') ∨
      (measure s1' < measure s1 ∧ t = E0 ∧ match_states s1' s2)) :
    ForwardSimulation L1 L2 :=
  forward_simulation_star_wf match_states hpub hinit hfinal
    (fun x y => measure x < measure y) (InvImage.wf measure Nat.lt_wfRel.wf)
    (fun s1 t s1' hst s2 hm => by
      rcases hsim s1 t s1' hst s2 hm with ⟨s2', hp, hm'⟩ | ⟨hlt, rfl, hm'⟩
      · exact ⟨s2', Or.inl hp, hm'⟩
      · exact ⟨s2, Or.inr ⟨.refl _, hlt⟩, hm'⟩)

/-- `Smallstep.forward_simulation_plus`: each source step is simulated by one
or more target steps. -/
theorem forward_simulation_plus
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      ∃ s2', Plus L2.step s2 t s2' ∧ match_states s1' s2') :
    ForwardSimulation L1 L2 :=
  forward_simulation_star match_states hpub hinit hfinal (fun _ => 0)
    (fun s1 t s1' hst s2 hm => Or.inl (hsim s1 t s1' hst s2 hm))

/-- `Smallstep.forward_simulation_step`: lock-step simulation. -/
theorem forward_simulation_step
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      ∃ s2', L2.step s2 t s2' ∧ match_states s1' s2') :
    ForwardSimulation L1 L2 :=
  forward_simulation_plus match_states hpub hinit hfinal
    (fun s1 t s1' hst s2 hm => by
      obtain ⟨s2', h, hm'⟩ := hsim s1 t s1' hst s2 hm
      exact ⟨s2', plus_one h, hm'⟩)

/-- `Smallstep.forward_simulation_opt`: one target step, or none with a
decreasing measure. -/
theorem forward_simulation_opt (measure : L1.state → Nat)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      (∃ s2', L2.step s2 t s2' ∧ match_states s1' s2') ∨
      (measure s1' < measure s1 ∧ t = E0 ∧ match_states s1' s2)) :
    ForwardSimulation L1 L2 :=
  forward_simulation_star match_states hpub hinit hfinal measure
    (fun s1 t s1' hst s2 hm => by
      rcases hsim s1 t s1' hst s2 hm with ⟨s2', h, hm'⟩ | h
      · exact Or.inl ⟨s2', plus_one h, hm'⟩
      · exact Or.inr h)

end Constructors

/-! ## Composition -/

/-- `Smallstep.compose_forward_simulations` -/
theorem compose_forward_simulations {L1 L2 L3 : Semantics}
    (S12 : ForwardSimulation L1 L2) (S23 : ForwardSimulation L2 L3) :
    ForwardSimulation L1 L3 := by
  obtain ⟨index, order, ms, P⟩ := S12
  obtain ⟨index', order', ms', P'⟩ := S23
  refine ⟨index' × index, Prod.Lex (Relation.TransGen order') order,
    fun i s1 s3 => ∃ s2, ms i.2 s1 s2 ∧ ms' i.1 s2 s3, ?_⟩
  exact
    { order_wf := (Prod.lex ⟨_, P'.order_wf.transGen⟩ ⟨_, P.order_wf⟩).wf
      initial_states := fun s1 h => by
        obtain ⟨i, s2, h2, hm⟩ := P.initial_states s1 h
        obtain ⟨i', s3, h3, hm'⟩ := P'.initial_states s2 h2
        exact ⟨(i', i), s3, h3, s2, hm, hm'⟩
      final_states := fun i s1 s3 r ⟨s2, hm, hm'⟩ hf =>
        P'.final_states _ _ _ _ hm' (P.final_states _ _ _ _ hm hf)
      simulation := fun s1 t s1' hst i s3 ⟨s2, hm, hm'⟩ => by
        obtain ⟨i2, i1⟩ := i
        rcases P.simulation' hst hm with ⟨i1', s2', hp, hm2⟩ | ⟨i1', ho, rfl, hm2⟩
        · rcases P'.simulation_plus hp hm' with ⟨i2', s3', hp3, hm3⟩ | ⟨i2', ho', rfl, hm3⟩
          · exact ⟨(i2', i1'), s3', Or.inl hp3, s2', hm2, hm3⟩
          · exact ⟨(i2', i1'), s3, Or.inr ⟨.refl _, .left _ _ ho'⟩, s2', hm2, hm3⟩
        · exact ⟨(i2, i1'), s3, Or.inr ⟨.refl _, .right _ ho⟩, s2, hm2, hm'⟩
      public_preserved := fun id => (P'.public_preserved id).trans (P.public_preserved id) }

/-- `forward_simulation` is reflexive (identity simulation). -/
theorem forward_simulation_refl (L : Semantics) : ForwardSimulation L L :=
  forward_simulation_step (fun s1 s2 => s1 = s2) (fun _ => rfl)
    (fun s1 h => ⟨s1, h, rfl⟩) (fun _ _ _ h hf => h ▸ hf)
    (fun _ _ s1' hst _ h => ⟨s1', h ▸ hst, rfl⟩)

end Smallstep
end CC
