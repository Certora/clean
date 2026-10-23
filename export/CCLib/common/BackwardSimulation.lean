/-
  Backward simulations — port of the backward-simulation part of
  `common/Smallstep.v` (`bsim_properties`, `backward_simulation`,
  `backward_simulation_plus`, `bsim_E0_star`, `bsim_safe`, `bsim_E0_plus`,
  `star_non_E0_split`) and of the backward half of `common/Behaviors.v`
  (`safe_along_behavior`, `backward_simulation_state_behaves`,
  `backward_simulation_behavior_improves`,
  `backward_simulation_same_safe_behavior`).

  As for forward simulations, Rocq's coinductive arguments are replaced by
  explicit constructions of the infinite runs (`ForeverSilent.coind`,
  `ForeverReactive.coind`).
-/
import CCLib.common.Simulation

namespace CC
namespace Smallstep

open ProgramBehavior

/-! ## A coinduction principle for reactive divergence -/

section Runs
variable {σ : Type} {R : σ → Trace → σ → Prop}

/-- Coinduction principle for `forever_reactive`: an invariant on (state,
infinite trace) pairs that always allows one more non-silent finite run, which
consumes a prefix of the trace, yields a reactive run producing that trace. -/
theorem ForeverReactive.coind (Q : σ → Traceinf → Prop)
    (h : ∀ s T, Q s T → ∃ s' t T', Star R s t s' ∧ t ≠ E0 ∧ Q s' T' ∧ T = Eappinf t T')
    {s : σ} {T : Traceinf} (hs : Q s T) : ForeverReactive R s T := by
  have next : ∀ p : {p : σ × Traceinf // Q p.1 p.2},
      ∃ q : {q : σ × Traceinf // Q q.1 q.2} × Trace,
        Star R p.1.1 q.2 q.1.1.1 ∧ q.2 ≠ E0 ∧ p.1.2 = Eappinf q.2 q.1.1.2 := by
    intro ⟨⟨s, T⟩, hq⟩
    obtain ⟨s', t, T', h1, h2, h3, h4⟩ := h s T hq
    exact ⟨(⟨(s', T'), h3⟩, t), h1, h2, h4⟩
  let g : Nat → {p : σ × Traceinf // Q p.1 p.2} := fun n =>
    Nat.rec ⟨(s, T), hs⟩ (fun _ p => (Classical.choose (next p)).1) n
  let ts : Nat → Trace := fun n => (Classical.choose (next (g n))).2
  have hspec : ∀ n, Star R (g n).1.1 (ts n) (g (n + 1)).1.1 ∧ ts n ≠ E0 ∧
      (g n).1.2 = Eappinf (ts n) (g (n + 1)).1.2 :=
    fun n => Classical.choose_spec (next (g n))
  have hT : ∀ n, T = Eappinf (prefixTrace ts n) (g n).1.2 := by
    intro n
    induction n with
    | zero => exact (Eappinf_E0 _).symm
    | succ n ih =>
      rw [ih, (hspec n).2.2]
      show _ = Eappinf (Eapp (prefixTrace ts n) (ts n)) _
      rw [Eappinf_assoc]
  refine ⟨fun n => (g n).1.1, ts, rfl, fun n => ⟨(hspec n).1, (hspec n).2.1⟩, ?_⟩
  intro n
  rw [hT n]
  exact isPrefix_Eappinf _ _

/-- A silent `star` followed by a silent `plus` invariant yields silent
divergence (coinduction up to `plus`). -/
theorem ForeverSilent.coind_plus (P : σ → Prop) (h : ∀ x, P x → ∃ y, Plus R x E0 y ∧ P y)
    {s : σ} (hs : P s) : ForeverSilent R s := by
  apply ForeverSilent.coind (fun x => ∃ y, Star R x E0 y ∧ P y)
  · intro x ⟨y, hxy, hy⟩
    cases hxy with
    | refl =>
      obtain ⟨z, hz, hpz⟩ := h x hy
      obtain ⟨x', hx', hs'⟩ := plus_E0_inv hz
      exact ⟨x', hx', z, hs', hpz⟩
    | step hr hs' heq =>
      obtain ⟨h1, h2⟩ := Eapp_eq_E0 heq.symm
      subst h1; subst h2
      exact ⟨_, hr, y, hs', hy⟩
  · exact ⟨s, .refl _, hs⟩

end Runs

/-! ## Backward simulations (`Smallstep.v`) -/

/-- `Smallstep.bsim_properties` -/
structure BSimProperties (L1 L2 : Semantics) (index : Type) (order : index → index → Prop)
    (match_states : index → L1.state → L2.state → Prop) : Prop where
  order_wf : WellFounded order
  initial_states_exist : ∀ s1, L1.initial_state s1 → ∃ s2, L2.initial_state s2
  match_initial_states : ∀ s1 s2, L1.initial_state s1 → L2.initial_state s2 →
    ∃ i s1', L1.initial_state s1' ∧ match_states i s1' s2
  match_final_states : ∀ i s1 s2 r, match_states i s1 s2 → Safe L1 s1 →
    L2.final_state s2 r → ∃ s1', Star L1.step s1 E0 s1' ∧ L1.final_state s1' r
  progress : ∀ i s1 s2, match_states i s1 s2 → Safe L1 s1 →
    (∃ r, L2.final_state s2 r) ∨ (∃ t s2', L2.step s2 t s2')
  simulation : ∀ s2 t s2', L2.step s2 t s2' → ∀ i s1, match_states i s1 s2 → Safe L1 s1 →
    ∃ i' s1', (Plus L1.step s1 t s1' ∨ (Star L1.step s1 t s1' ∧ order i' i)) ∧
      match_states i' s1' s2'
  public_preserved : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id

/-- `Smallstep.backward_simulation` -/
def BackwardSimulation (L1 L2 : Semantics) : Prop :=
  ∃ (index : Type) (order : index → index → Prop)
    (match_states : index → L1.state → L2.state → Prop),
    BSimProperties L1 L2 index order match_states

section BSim
variable {L1 L2 : Semantics} {index : Type} {order : index → index → Prop}
  {match_states : index → L1.state → L2.state → Prop}
  (S : BSimProperties L1 L2 index order match_states)
include S

/-- `Smallstep.bsim_simulation'` -/
theorem BSimProperties.simulation' {i s2 t s2'} (hst : L2.step s2 t s2') {s1}
    (hm : match_states i s1 s2) (hs : Safe L1 s1) :
    (∃ i' s1', Plus L1.step s1 t s1' ∧ match_states i' s1' s2') ∨
    (∃ i', order i' i ∧ t = E0 ∧ match_states i' s1 s2') := by
  obtain ⟨i', s1', hp | ⟨hst1, ho⟩, hm'⟩ := S.simulation s2 t s2' hst i s1 hm hs
  · exact Or.inl ⟨i', s1', hp, hm'⟩
  · rcases star_inv hst1 with ⟨rfl, rfl⟩ | hp
    · exact Or.inr ⟨i', ho, rfl, hm'⟩
    · exact Or.inl ⟨i', s1', hp, hm'⟩

/-- `Smallstep.bsim_E0_star` -/
theorem BSimProperties.E0_star {s2 s2'} (hst : Star L2.step s2 E0 s2') :
    ∀ {i s1}, match_states i s1 s2 → Safe L1 s1 →
      ∃ i' s1', Star L1.step s1 E0 s1' ∧ match_states i' s1' s2' := by
  refine star_E0_ind (fun s2 s2' => ∀ {i s1}, match_states i s1 s2 → Safe L1 s1 →
      ∃ i' s1', Star L1.step s1 E0 s1' ∧ match_states i' s1' s2') ?_ ?_ hst
  · intro s i s1 hm _
    exact ⟨i, s1, .refl _, hm⟩
  · intro s1' s2 s3 hr ih i s1 hm hs
    obtain ⟨i', s1'', hor, hm'⟩ := S.simulation _ _ _ hr i s1 hm hs
    have hst' : Star L1.step s1 E0 s1'' := by
      rcases hor with hp | ⟨h, _⟩
      · exact plus_star hp
      · exact h
    obtain ⟨i'', s1''', h3, hm''⟩ := ih hm' (star_safe hst' hs)
    exact ⟨i'', s1''', star_trans hst' h3 rfl, hm''⟩

/-- `Smallstep.bsim_safe` -/
theorem BSimProperties.safe {i s1 s2} (hm : match_states i s1 s2) (hs : Safe L1 s1) :
    Safe L2 s2 := by
  intro s2' hst
  obtain ⟨i', s1', h1, hm'⟩ := S.E0_star hst hm hs
  exact S.progress _ _ _ hm' (star_safe h1 hs)

/-- `Smallstep.bsim_E0_plus` -/
theorem BSimProperties.E0_plus {s2 s2'} (hp : Plus L2.step s2 E0 s2') :
    ∀ {i s1}, match_states i s1 s2 → Safe L1 s1 →
      (∃ i' s1', Plus L1.step s1 E0 s1' ∧ match_states i' s1' s2') ∨
      (∃ i', Relation.TransGen order i' i ∧ match_states i' s1 s2') := by
  obtain ⟨y, hy, hys⟩ := plus_E0_inv hp
  clear hp
  suffices H : Star L2.step y E0 s2' ∧ ∀ {s2}, L2.step s2 E0 y → ∀ {i s1},
      match_states i s1 s2 → Safe L1 s1 →
      (∃ i' s1', Plus L1.step s1 E0 s1' ∧ match_states i' s1' s2') ∨
      (∃ i', Relation.TransGen order i' i ∧ match_states i' s1 s2') from by
    intro i s1 hm hs; exact H.2 hy hm hs
  refine star_E0_ind (fun y s2' => Star L2.step y E0 s2' ∧ ∀ {s2}, L2.step s2 E0 y → ∀ {i s1},
      match_states i s1 s2 → Safe L1 s1 →
      (∃ i' s1', Plus L1.step s1 E0 s1' ∧ match_states i' s1' s2') ∨
      (∃ i', Relation.TransGen order i' i ∧ match_states i' s1 s2')) ?_ ?_ hys
  · intro y
    refine ⟨.refl _, ?_⟩
    intro s2 hy i s1 hm hs
    rcases S.simulation' hy hm hs with ⟨i', s1', hp, hm'⟩ | ⟨i', ho, _, hm'⟩
    · exact Or.inl ⟨i', s1', hp, hm'⟩
    · exact Or.inr ⟨i', .single ho, hm'⟩
  · intro y z w hyz ⟨hzw, ih⟩
    have hyw : Star L2.step y E0 w := star_left hyz hzw rfl
    refine ⟨hyw, ?_⟩
    intro s2 hy i s1 hm hs
    rcases S.simulation' hy hm hs with ⟨i', s1', hp, hm'⟩ | ⟨i', ho, _, hm'⟩
    · obtain ⟨i'', s1'', h2, hm''⟩ := S.E0_star hyw hm' (star_safe (plus_star hp) hs)
      exact Or.inl ⟨i'', s1'', plus_star_trans hp h2 rfl, hm''⟩
    · rcases ih hyz hm' hs with h | ⟨i'', ho', hm''⟩
      · exact Or.inl h
      · exact Or.inr ⟨i'', .tail ho' ho, hm''⟩

end BSim

/-- `Smallstep.star_non_E0_split`: a run producing exactly one event contains
exactly one non-silent step. -/
theorem star_non_E0_split {L : Semantics} {s2 t s2'} (h : Star L.step s2 t s2')
    (hlen : t.length = 1) :
    ∃ s2x s2y, Star L.step s2 E0 s2x ∧ L.step s2x t s2y ∧ Star L.step s2y E0 s2' := by
  induction h with
  | refl => simp [E0] at hlen
  | @step s1 t1 s2 t2 s3 t hr hs heq ih =>
    subst heq
    have hl : t1.length + t2.length = 1 := by simpa [Eapp] using hlen
    by_cases h1 : t1 = E0
    · subst h1
      obtain ⟨x, y, ha, hb, hc⟩ := ih (by simpa [E0] using hl)
      exact ⟨x, y, star_left hr ha rfl, hb, hc⟩
    · have h2 : t2 = E0 := by
        cases t2 with
        | nil => rfl
        | cons _ _ =>
          cases t1 with
          | nil => exact absurd rfl h1
          | cons _ _ => simp at hl; omega
      subst h2
      exact ⟨s1, s2, .refl _, by rw [E0_right]; exact hr, hs⟩

/-! ## Constructing backward simulations -/

section Constructors
variable {L1 L2 : Semantics} (match_states : L1.state → L2.state → Prop)

/-- `Smallstep.backward_simulation_plus`: each target step is matched by one or
more source steps. -/
theorem backward_simulation_plus
    (hpub : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id)
    (hinit_exist : ∀ s1, L1.initial_state s1 → ∃ s2, L2.initial_state s2)
    (hinit : ∀ s1 s2, L1.initial_state s1 → L2.initial_state s2 →
      ∃ s1', L1.initial_state s1' ∧ match_states s1' s2)
    (hfinal : ∀ s1 s2 r, match_states s1 s2 → L2.final_state s2 r → L1.final_state s1 r)
    (hprogress : ∀ s1 s2, match_states s1 s2 → Safe L1 s1 →
      (∃ r, L2.final_state s2 r) ∨ (∃ t s2', L2.step s2 t s2'))
    (hsim : ∀ s2 t s2', L2.step s2 t s2' → ∀ s1, match_states s1 s2 → Safe L1 s1 →
      ∃ s1', Plus L1.step s1 t s1' ∧ match_states s1' s2') :
    BackwardSimulation L1 L2 :=
  ⟨Unit, fun _ _ => False, fun _ s1 s2 => match_states s1 s2,
    { order_wf := ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩
      initial_states_exist := hinit_exist
      match_initial_states := fun s1 s2 h1 h2 => by
        obtain ⟨s1', h, hm⟩ := hinit s1 s2 h1 h2
        exact ⟨(), s1', h, hm⟩
      match_final_states := fun _ s1 s2 r hm _ hf => ⟨s1, .refl _, hfinal s1 s2 r hm hf⟩
      progress := fun _ s1 s2 hm hs => hprogress s1 s2 hm hs
      simulation := fun s2 t s2' hst _ s1 hm hs => by
        obtain ⟨s1', hp, hm'⟩ := hsim s2 t s2' hst s1 hm hs
        exact ⟨(), s1', Or.inl hp, hm'⟩
      public_preserved := hpub }⟩

end Constructors

/-- `backward_simulation` is reflexive. -/
theorem backward_simulation_refl (L : Semantics) : BackwardSimulation L L :=
  backward_simulation_plus (fun s1 s2 => s1 = s2) (fun _ => rfl)
    (fun s1 h => ⟨s1, h⟩) (fun _ s2 _ h2 => ⟨s2, h2, rfl⟩)
    (fun _ _ _ h hf => h ▸ hf)
    (fun s1 s2 h hs => by
      subst h
      rcases hs s1 (.refl _) with hf | hst
      · exact Or.inl hf
      · exact Or.inr hst)
    (fun _ _ s2' hst _ h _ => ⟨s2', h ▸ plus_one hst, rfl⟩)

/-! ## Backward simulations improve behaviours (`Behaviors.v`) -/

section Behaviors
variable {L1 L2 : Semantics} {index : Type} {order : index → index → Prop}
  {match_states : index → L1.state → L2.state → Prop}
  (S : BSimProperties L1 L2 index order match_states)

/-- `Behaviors.safe_along_behavior`: `s` cannot get stuck after any prefix of
`b`. -/
def SafeAlongBehavior (L1 : Semantics) (s : L1.state) (b : ProgramBehavior) : Prop :=
  ∀ t1 s' b2, Star L1.step s t1 s' → b = behavior_app t1 b2 →
    (∃ r, L1.final_state s' r) ∨ (∃ t2 s'', L1.step s' t2 s'')

/-- `Behaviors.safe_along_safe` -/
theorem safeAlong_safe {s : L1.state} {b} (h : SafeAlongBehavior L1 s b) : Safe L1 s :=
  fun s' hst => h E0 s' b hst (behavior_app_E0 b).symm

/-- `Behaviors.star_safe_along` -/
theorem star_safeAlong {s : L1.state} {b t1 s' b2} (h : SafeAlongBehavior L1 s b)
    (hst : Star L1.step s t1 s') (hb : b = behavior_app t1 b2) :
    SafeAlongBehavior L1 s' b2 := by
  intro t2 s'' b3 h2 hb2
  apply h _ _ b3 (star_trans hst h2 rfl)
  rw [hb, hb2, behavior_app_assoc]

/-- `Behaviors.not_safe_along_behavior` -/
theorem not_safeAlong {s : L1.state} {b} (h : ¬ SafeAlongBehavior L1 s b) :
    ∃ t s', behavior_prefix t b ∧ Star L1.step s t s' ∧ Nostep L1.step s' ∧
      ∀ r, ¬ L1.final_state s' r := by
  apply Classical.byContradiction
  intro hc
  apply h
  intro t1 s' b2 hst hb
  apply Classical.byContradiction
  intro hn
  apply hc
  refine ⟨t1, s', ⟨b2, hb⟩, hst, fun t s'' hs => hn (Or.inr ⟨t, s'', hs⟩),
    fun r hr => hn (Or.inl ⟨r, hr⟩)⟩

include S

/-- `Behaviors.backward_simulation_star` -/
theorem BSimProperties.simulation_star {s2 t s2'} (hst : Star L2.step s2 t s2') :
    ∀ {i s1 b}, match_states i s1 s2 → SafeAlongBehavior L1 s1 (behavior_app t b) →
      ∃ i' s1', Star L1.step s1 t s1' ∧ match_states i' s1' s2' := by
  induction hst with
  | refl => intro i s1 _ hm _; exact ⟨i, s1, .refl _, hm⟩
  | @step s2 t1 s3 t2 s4 t hr _ heq ih =>
    intro i s1 b hm hsafe
    obtain ⟨i', s1', hor, hm'⟩ := S.simulation _ _ _ hr i s1 hm (safeAlong_safe hsafe)
    have h1 : Star L1.step s1 t1 s1' := by
      rcases hor with hp | ⟨h, _⟩
      · exact plus_star hp
      · exact h
    have hsafe' : SafeAlongBehavior L1 s1' (behavior_app t2 b) :=
      star_safeAlong hsafe h1 (by rw [heq, behavior_app_assoc])
    obtain ⟨i'', s1'', h2, hm''⟩ := ih hm' hsafe'
    exact ⟨i'', s1'', star_trans h1 h2 heq, hm''⟩

/-- One matched pair of silently diverging target / safe source states always
yields at least one silent source step. -/
theorem BSimProperties.forever_silent_plus :
    ∀ i s1 s2, ForeverSilent L2.step s2 → match_states i s1 s2 → Safe L1 s1 →
      ∃ i' s1' s2', Plus L1.step s1 E0 s1' ∧ ForeverSilent L2.step s2' ∧
        match_states i' s1' s2' := by
  intro i
  induction i using S.order_wf.induction with
  | _ i ih =>
    intro s1 s2 hf hm hs
    obtain ⟨s2', hr, hf'⟩ := hf.inv
    rcases S.simulation' hr hm hs with ⟨i', s1', hp, hm'⟩ | ⟨i', ho, _, hm'⟩
    · exact ⟨i', s1', s2', hp, hf', hm'⟩
    · exact ih i' ho s1 s2' hf' hm' hs

/-- `Behaviors.backward_simulation_forever_silent` -/
theorem BSimProperties.simulation_forever_silent {i s1 s2} (hf : ForeverSilent L2.step s2)
    (hm : match_states i s1 s2) (hs : Safe L1 s1) : ForeverSilent L1.step s1 := by
  apply ForeverSilent.coind_plus
    (fun x => ∃ i s2, ForeverSilent L2.step s2 ∧ match_states i x s2 ∧ Safe L1 x)
  · intro x ⟨i, s2, hf, hm, hs⟩
    obtain ⟨i', s1', s2', hp, hf', hm'⟩ := S.forever_silent_plus i x s2 hf hm hs
    exact ⟨s1', hp, i', s2', hf', hm', star_safe (plus_star hp) hs⟩
  · exact ⟨i, s2, hf, hm, hs⟩

/-- `Behaviors.backward_simulation_forever_reactive` -/
theorem BSimProperties.simulation_forever_reactive {i s1 s2 T}
    (hf : ForeverReactive L2.step s2 T) (hm : match_states i s1 s2)
    (hs : SafeAlongBehavior L1 s1 (Reacts T)) : ForeverReactive L1.step s1 T := by
  apply ForeverReactive.coind (fun x T => ∃ i s2, ForeverReactive L2.step s2 T ∧
    match_states i x s2 ∧ SafeAlongBehavior L1 x (Reacts T))
  · intro x T ⟨i, s2, hf, hm, hs⟩
    obtain ⟨s2', t, T', h2, hne, hf', rfl⟩ := hf.inv
    obtain ⟨i', s1', h1, hm'⟩ := S.simulation_star h2 (b := Reacts T') hm hs
    exact ⟨s1', t, T', h1, hne, ⟨i', s2', hf', hm', star_safeAlong hs h1 rfl⟩, rfl⟩
  · exact ⟨i, s2, hf, hm, hs⟩

/-- `Behaviors.backward_simulation_state_behaves` -/
theorem BSimProperties.state_behaves {i s1 s2 beh2} (hm : match_states i s1 s2)
    (hb : StateBehaves L2 s2 beh2) :
    ∃ beh1, StateBehaves L1 s1 beh1 ∧ behavior_improves beh1 beh2 := by
  by_cases hsafe : SafeAlongBehavior L1 s1 beh2
  · refine ⟨beh2, ?_, behavior_improves_refl _⟩
    cases hb with
    | @terminates t s2' r hst hfin =>
      have he : Terminates t r = behavior_app t (Terminates E0 r) := by
        simp [behavior_app, E0_right]
      rw [he] at hsafe
      obtain ⟨i', s1', h1, hm'⟩ := S.simulation_star hst hm hsafe
      obtain ⟨s1'', h2, hf⟩ := S.match_final_states _ _ _ _ hm'
        (safeAlong_safe (star_safeAlong hsafe h1 rfl)) hfin
      exact .terminates (star_trans h1 h2 (E0_right t).symm) hf
    | @diverges t s2' hst hfs =>
      have he : Diverges t = behavior_app t (Diverges E0) := by
        simp [behavior_app, E0_right]
      rw [he] at hsafe
      obtain ⟨i', s1', h1, hm'⟩ := S.simulation_star hst hm hsafe
      exact .diverges h1 (S.simulation_forever_silent hfs hm'
        (safeAlong_safe (star_safeAlong hsafe h1 rfl)))
    | reacts hfr =>
      exact .reacts (S.simulation_forever_reactive hfr hm hsafe)
    | @goes_wrong t s2' hst hn hnf =>
      have he : Goes_wrong t = behavior_app t (Goes_wrong E0) := by
        simp [behavior_app, E0_right]
      rw [he] at hsafe
      obtain ⟨i', s1', h1, hm'⟩ := S.simulation_star hst hm hsafe
      rcases S.progress _ _ _ hm' (safeAlong_safe (star_safeAlong hsafe h1 rfl)) with
        ⟨r, hr⟩ | ⟨t', s'', hs'⟩
      · exact (hnf r hr).elim
      · exact (hn t' s'' hs').elim
  · obtain ⟨t, s1', hpre, hst, hn, hnf⟩ := not_safeAlong hsafe
    exact ⟨Goes_wrong t, .goes_wrong hst hn hnf, Or.inr ⟨t, rfl, hpre⟩⟩

end Behaviors

/-- `Behaviors.backward_simulation_behavior_improves`: every behaviour of the
target is improved by some behaviour of the source. -/
theorem backward_simulation_behavior_improves {L1 L2 : Semantics}
    (S : BackwardSimulation L1 L2) {beh2} (hb : ProgramBehaves L2 beh2) :
    ∃ beh1, ProgramBehaves L1 beh1 ∧ behavior_improves beh1 beh2 := by
  obtain ⟨index, order, match_states, S⟩ := S
  cases hb with
  | runs hi hs =>
    by_cases h1 : ∃ s1, L1.initial_state s1
    · obtain ⟨s1, hi1⟩ := h1
      obtain ⟨i, s1', hi1', hm⟩ := S.match_initial_states _ _ hi1 hi
      obtain ⟨beh1, hb1, himp⟩ := S.state_behaves hm hs
      exact ⟨beh1, .runs hi1' hb1, himp⟩
    · exact ⟨_, .goes_initially_wrong (fun s h => h1 ⟨s, h⟩), behavior_improves_bot _⟩
  | goes_initially_wrong hn =>
    refine ⟨_, .goes_initially_wrong ?_, behavior_improves_refl _⟩
    intro s1 h
    obtain ⟨s2, h2⟩ := S.initial_states_exist s1 h
    exact hn s2 h2

/-- `Behaviors.backward_simulation_same_safe_behavior`: if no behaviour of the
source goes wrong, every behaviour of the target is a behaviour of the source. -/
theorem backward_simulation_same_safe_behavior {L1 L2 : Semantics}
    (S : BackwardSimulation L1 L2) (hsafe : ∀ beh, ProgramBehaves L1 beh → beh.not_wrong)
    {beh} (hb : ProgramBehaves L2 beh) : ProgramBehaves L1 beh := by
  obtain ⟨beh1, hb1, himp⟩ := backward_simulation_behavior_improves S hb
  rcases himp with rfl | ⟨t, rfl, _⟩
  · exact hb1
  · exact (hsafe _ hb1).elim

/-! ## Composing backward simulations -/

section Compose
variable {L1 L2 L3 : Semantics} (L3_single : SingleEvents L3)
  {index : Type} {order : index → index → Prop}
  {match_states : index → L1.state → L2.state → Prop}
  (S12 : BSimProperties L1 L2 index order match_states)
  {index' : Type} {order' : index' → index' → Prop}
  {match_states' : index' → L2.state → L3.state → Prop}
  (S23 : BSimProperties L2 L3 index' order' match_states')

/-- `Smallstep.bb_order` -/
def bbOrder (order : index → index → Prop) (order' : index' → index' → Prop) :
    index × index' → index × index' → Prop :=
  Prod.Lex (Relation.TransGen order) order'

/-- `Smallstep.bb_match_states` -/
def bbMatchStates (match_states : index → L1.state → L2.state → Prop)
    (match_states' : index' → L2.state → L3.state → Prop)
    (i : index × index') (s1 : L1.state) (s3 : L3.state) : Prop :=
  ∃ s2x s2y, match_states i.1 s1 s2x ∧ Star L2.step s2x E0 s2y ∧ match_states' i.2 s2y s3

theorem bb_match_at {i1 i2 s1 s2 s3} (h1 : match_states i1 s1 s2)
    (h2 : match_states' i2 s2 s3) : bbMatchStates match_states match_states' (i1, i2) s1 s3 :=
  ⟨s2, s2, h1, .refl _, h2⟩

include L3_single S12 S23

/-- `Smallstep.bb_simulation_base` -/
theorem bb_simulation_base {s3 t s3'} (hst : L3.step s3 t s3') {i1 s1 i2 s2}
    (hm1 : match_states i1 s1 s2) (hm2 : match_states' i2 s2 s3) (hs : Safe L1 s1) :
    ∃ i' s1', (Plus L1.step s1 t s1' ∨
        (Star L1.step s1 t s1' ∧ bbOrder order order' i' (i1, i2))) ∧
      bbMatchStates match_states match_states' i' s1' s3' := by
  rcases S23.simulation' hst hm2 (S12.safe hm1 hs) with
    ⟨i2', s2', hp2, hm2'⟩ | ⟨i2', ho2, rfl, hm2'⟩
  · have hlen := L3_single _ _ _ hst
    by_cases ht : t = E0
    · subst ht
      rcases S12.E0_plus hp2 hm1 hs with ⟨i1', s1', hp1, hm1'⟩ | ⟨i1', ho1, hm1'⟩
      · exact ⟨(i1', i2'), s1', Or.inl hp1, bb_match_at hm1' hm2'⟩
      · exact ⟨(i1', i2'), s1, Or.inr ⟨.refl _, .left _ _ ho1⟩, bb_match_at hm1' hm2'⟩
    · have h1 : t.length = 1 := by
        cases t with
        | nil => exact absurd rfl ht
        | cons _ _ => simp at hlen ⊢; omega
      obtain ⟨s2x, s2y, hP, hQ, hR⟩ := star_non_E0_split (plus_star hp2) h1
      obtain ⟨i1', s1x, hX, hY⟩ := S12.E0_star hP hm1 hs
      rcases S12.simulation' hQ hY (star_safe hX hs) with
        ⟨i1'', s1y, hU, hV⟩ | ⟨_, _, hV, _⟩
      · exact ⟨(i1'', i2'), s1y, Or.inl (star_plus_trans hX hU rfl), s2y, s2', hV, hR, hm2'⟩
      · exact absurd hV ht
  · exact ⟨(i1, i2'), s1, Or.inr ⟨.refl _, .right _ ho2⟩, bb_match_at hm1 hm2'⟩

/-- `Smallstep.bb_simulation` -/
theorem bb_simulation {s3 t s3'} (hst : L3.step s3 t s3') {i s1}
    (hm : bbMatchStates match_states match_states' i s1 s3) (hs : Safe L1 s1) :
    ∃ i' s1', (Plus L1.step s1 t s1' ∨ (Star L1.step s1 t s1' ∧ bbOrder order order' i' i)) ∧
      bbMatchStates match_states match_states' i' s1' s3' := by
  obtain ⟨i1, i2⟩ := i
  obtain ⟨s2x, s2y, hm1, hst2, hm2⟩ := hm
  rcases star_inv hst2 with ⟨rfl, -⟩ | hp
  · exact bb_simulation_base L3_single S12 S23 hst hm1 hm2 hs
  · rcases S12.E0_plus hp hm1 hs with ⟨i1', s1', hA, hB⟩ | ⟨i1', hA, hB⟩
    · obtain ⟨i'', s1'', hC, hD⟩ :=
        bb_simulation_base L3_single S12 S23 hst hB hm2 (star_safe (plus_star hA) hs)
      refine ⟨i'', s1'', Or.inl (plus_star_trans hA ?_ rfl), hD⟩
      rcases hC with hP | ⟨hP, _⟩
      · exact plus_star hP
      · exact hP
    · obtain ⟨i'', s1'', hC, hD⟩ := bb_simulation_base L3_single S12 S23 hst hB hm2 hs
      refine ⟨i'', s1'', ?_, hD⟩
      rcases hC with hP | ⟨hP, ho⟩
      · exact Or.inl hP
      · refine Or.inr ⟨hP, ?_⟩
        cases ho with
        | left _ _ h => exact .left _ _ (Relation.TransGen.trans h hA)
        | right _ _ => exact .left _ _ hA

end Compose

/-- `Smallstep.compose_backward_simulation` -/
theorem compose_backward_simulation {L1 L2 L3 : Semantics} (L3_single : SingleEvents L3)
    (S12 : BackwardSimulation L1 L2) (S23 : BackwardSimulation L2 L3) :
    BackwardSimulation L1 L3 := by
  obtain ⟨index, order, ms, P⟩ := S12
  obtain ⟨index', order', ms', P'⟩ := S23
  refine ⟨index × index', bbOrder order order', bbMatchStates ms ms', ?_⟩
  exact
    { order_wf := (Prod.lex ⟨_, P.order_wf.transGen⟩ ⟨_, P'.order_wf⟩).wf
      initial_states_exist := fun s1 h => by
        obtain ⟨s2, h2⟩ := P.initial_states_exist s1 h
        exact P'.initial_states_exist s2 h2
      match_initial_states := fun s1 s3 h1 h3 => by
        obtain ⟨s2, h2⟩ := P.initial_states_exist s1 h1
        obtain ⟨i2, s2', h2', hm2⟩ := P'.match_initial_states s2 s3 h2 h3
        obtain ⟨i1, s1', h1', hm1⟩ := P.match_initial_states s1 s2' h1 h2'
        exact ⟨(i1, i2), s1', h1', bb_match_at hm1 hm2⟩
      match_final_states := fun i s1 s3 r hm hs hf => by
        obtain ⟨s2x, s2y, hm1, hst2, hm2⟩ := hm
        obtain ⟨s2', hA, hB⟩ := P'.match_final_states _ _ _ _ hm2
          (star_safe hst2 (P.safe hm1 hs)) hf
        obtain ⟨i1', s1', hC, hD⟩ := P.E0_star (star_trans hst2 hA rfl) hm1 hs
        obtain ⟨s1'', hP, hQ⟩ := P.match_final_states _ _ _ _ hD (star_safe hC hs) hB
        exact ⟨s1'', star_trans hC hP rfl, hQ⟩
      progress := fun i s1 s3 hm hs => by
        obtain ⟨s2x, s2y, hm1, hst2, hm2⟩ := hm
        exact P'.progress _ _ _ hm2 (star_safe hst2 (P.safe hm1 hs))
      simulation := fun s3 t s3' hst i s1 hm hs => bb_simulation L3_single P P' hst hm hs
      public_preserved := fun id => (P'.public_preserved id).trans (P.public_preserved id) }

end Smallstep
end CC
