/-
  Factoring simulations through `atomic` — the sections
  `FACTOR_FORWARD_SIMULATION` and `FACTOR_BACKWARD_SIMULATION` of
  `common/Smallstep.v`:
  * `factor_forward_simulation`: a forward simulation from `L1` to a
    single-event semantics `L2` gives a forward simulation from `atomic L1`
    to `L2`;
  * `factor_backward_simulation`: a backward simulation from a single-event
    semantics `L1` to a semantics `L2` with well-behaved traces gives a
    backward simulation from `L1` to `atomic L2`.
-/
import CCLib.common.SmallstepAtomic
import CCLib.common.Simulation
import CCLib.common.BackwardSimulation

namespace CC
namespace Smallstep

/-- `Smallstep.star_non_E0_split'`: in a single-event semantics, a run whose
    trace starts with `ev` begins with a run producing exactly `ev`. -/
theorem star_non_E0_split' {L : Semantics} (hs : SingleEvents L) {s2 t s2'}
    (h : Star L.step s2 t s2') :
    ∀ {ev t'}, t = ev :: t' → ∃ s2x, Plus L.step s2 [ev] s2x ∧ Star L.step s2x t' s2' := by
  induction h with
  | refl => intro ev t' he; simp [E0] at he
  | @step s1 t1 s2 t2 s3 t hr hst heq ih =>
    intro ev t' he
    subst heq
    have LEN := hs _ _ _ hr
    match t1, LEN, he with
    | [], _, he =>
      obtain ⟨s2x, A, B⟩ := ih he
      exact ⟨s2x, plus_left hr (plus_star A) rfl, B⟩
    | [e], _, he =>
      simp only [Eapp, List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨s2, plus_one hr, hst⟩

/-! ### Factoring forward simulations -/

section FACTOR_FORWARD_SIMULATION
variable {L1 L2 : Semantics} {index : Type} {order : index → index → Prop}
  {match_states : index → L1.state → L2.state → Prop}

/-- `Smallstep.ffs_match` -/
inductive FfsMatch (match_states : index → L1.state → L2.state → Prop) :
    index → Trace × L1.state → L2.state → Prop where
  | here (i s1 s2) : match_states i s1 s2 → FfsMatch match_states i (E0, s1) s2
  | buffer (i ev t s1 s2 s2') :
      Star L2.step s2 (ev :: t) s2' → match_states i s1 s2' →
      FfsMatch match_states i (ev :: t, s1) s2

/-- `Smallstep.ffs_simulation` -/
theorem ffs_simulation (sim : FSimProperties L1 L2 index order match_states)
    (L2single : SingleEvents L2) {s1 t s1'} (hst : (atomic L1).step s1 t s1') {i s2}
    (hm : FfsMatch match_states i s1 s2) :
    ∃ i' s2', (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ order i' i)) ∧
      FfsMatch match_states i' s1' s2' := by
  cases hst with
  | silent s s' h =>
    cases hm with
    | here _ _ M =>
      obtain ⟨i', s2', A, B⟩ := sim.simulation _ _ _ h i s2 M
      exact ⟨i', s2', A, .here _ _ _ B⟩
  | start s ev t s' h =>
    cases hm with
    | here _ _ M =>
      obtain ⟨i', s2', A, B⟩ := sim.simulation _ _ _ h i s2 M
      cases t with
      | nil => exact ⟨i', s2', A, .here _ _ _ B⟩
      | cons ev' t =>
        have C : Star L2.step s2 (ev :: ev' :: t) s2' := by
          rcases A with A | ⟨A, _⟩
          · exact plus_star A
          · exact A
        obtain ⟨s2x, P, Q⟩ := star_non_E0_split' L2single C rfl
        exact ⟨i', s2x, .inl P, .buffer _ _ _ _ _ _ Q B⟩
  | cont ev t s ho =>
    cases hm with
    | buffer _ _ _ _ s2'' H M =>
      obtain ⟨s2x, P, Q⟩ := star_non_E0_split' L2single H rfl
      cases t with
      | nil => exact ⟨i, s2'', .inl (plus_star_trans P Q rfl), .here _ _ _ M⟩
      | cons e t => exact ⟨i, s2x, .inl P, .buffer _ _ _ _ _ _ Q M⟩

end FACTOR_FORWARD_SIMULATION

/-- `Smallstep.factor_forward_simulation` -/
theorem factor_forward_simulation {L1 L2 : Semantics} (FS : ForwardSimulation L1 L2)
    (L2single : SingleEvents L2) : ForwardSimulation (atomic L1) L2 := by
  obtain ⟨index, order, match_states, sim⟩ := FS
  refine ⟨index, order, FfsMatch match_states, ?_⟩
  exact {
    order_wf := sim.order_wf
    initial_states := by
      rintro ⟨t1, s1⟩ ⟨h, ht⟩
      simp only at h ht
      subst ht
      obtain ⟨i, s2, A, B⟩ := sim.initial_states s1 h
      exact ⟨i, s2, A, .here _ _ _ B⟩
    final_states := by
      rintro i ⟨t1, s1⟩ s2 r hm ⟨hf, ht⟩
      simp only at hf ht
      subst ht
      cases hm with
      | here _ _ M => exact sim.final_states _ _ _ _ M hf
    simulation := fun _ _ _ hst _ _ hm => ffs_simulation sim L2single hst hm
    public_preserved := sim.public_preserved }

/-! ### Factoring backward simulations -/

section FACTOR_BACKWARD_SIMULATION
variable {L1 L2 : Semantics} {index : Type} {order : index → index → Prop}
  {match_states : index → L1.state → L2.state → Prop}

/-- `Smallstep.fbs_match` -/
inductive FbsMatch (match_states : index → L1.state → L2.state → Prop) :
    index → L1.state → Trace × L2.state → Prop where
  | intro (i s1 t s2 s1') :
      Star L1.step s1 t s1' → match_states i s1' s2 → (t = E0 ∨ OutputTrace t) →
      FbsMatch match_states i s1 (t, s2)

/-- `Smallstep.fbs_simulation` -/
theorem fbs_simulation (sim : BSimProperties L1 L2 index order match_states)
    (L1single : SingleEvents L1) (L2wb : WellBehavedTraces L2)
    {s2 t s2'} (hst : (atomic L2).step s2 t s2') {i s1}
    (hm : FbsMatch match_states i s1 s2) (hsafe : Safe L1 s1) :
    ∃ i' s1', (Plus L1.step s1 t s1' ∨ (Star L1.step s1 t s1' ∧ order i' i)) ∧
      FbsMatch match_states i' s1' s2' := by
  cases hst with
  | silent s s' h =>
    cases hm with
    | intro _ _ s1' H0 M _ =>
      obtain ⟨i', s1'', A, B⟩ := sim.simulation _ _ _ h i s1' M (star_safe H0 hsafe)
      refine ⟨i', s1'', ?_, .intro _ _ _ _ _ (.refl _) B (.inl rfl)⟩
      rcases A with P | ⟨P, Q⟩
      · exact .inl (star_plus_trans H0 P rfl)
      · exact .inr ⟨star_trans H0 P rfl, Q⟩
  | start s ev t s' h =>
    cases hm with
    | intro _ _ s1' H0 M _ =>
      obtain ⟨i', s1'', A, B⟩ := sim.simulation _ _ _ h i s1' M (star_safe H0 hsafe)
      have C : Star L1.step s1 (ev :: t) s1'' := by
        refine star_trans H0 ?_ rfl
        rcases A with P | ⟨P, _⟩
        · exact plus_star P
        · exact P
      obtain ⟨s1x, P, Q⟩ := star_non_E0_split' L1single C rfl
      have W : OutputTrace t := L2wb _ _ _ h
      exact ⟨i', s1x, .inl P, .intro _ _ _ _ _ Q B (.inr W)⟩
  | cont ev t s ho =>
    cases hm with
    | intro _ _ s1' H0 M hor =>
      obtain ⟨s1x, P, Q⟩ := star_non_E0_split' L1single H0 rfl
      exact ⟨i, s1x, .inl P, .intro _ _ _ _ _ Q M (.inr ho.2)⟩

/-- `Smallstep.fbs_progress` -/
theorem fbs_progress (sim : BSimProperties L1 L2 index order match_states)
    {i s1 s2} (hm : FbsMatch match_states i s1 s2) (hsafe : Safe L1 s1) :
    (∃ r, (atomic L2).final_state s2 r) ∨ (∃ t s2', (atomic L2).step s2 t s2') := by
  cases hm with
  | intro t s2 s1' H0 M hor =>
    cases t with
    | nil =>
      rcases sim.progress i s1' s2 M (star_safe H0 hsafe) with ⟨r, A⟩ | ⟨t, s2', A⟩
      · exact .inl ⟨r, A, rfl⟩
      · cases t with
        | nil => exact .inr ⟨_, _, .silent _ _ A⟩
        | cons e t => exact .inr ⟨_, _, .start _ _ _ _ A⟩
    | cons e t =>
      rcases hor with h | h
      · simp [E0] at h
      · exact .inr ⟨_, _, .cont _ _ _ h⟩

end FACTOR_BACKWARD_SIMULATION

/-- `Smallstep.factor_backward_simulation` -/
theorem factor_backward_simulation {L1 L2 : Semantics} (BS : BackwardSimulation L1 L2)
    (L1single : SingleEvents L1) (L2wb : WellBehavedTraces L2) :
    BackwardSimulation L1 (atomic L2) := by
  obtain ⟨index, order, match_states, sim⟩ := BS
  refine ⟨index, order, FbsMatch match_states, ?_⟩
  exact {
    order_wf := sim.order_wf
    initial_states_exist := by
      intro s1 h
      obtain ⟨s2, A⟩ := sim.initial_states_exist s1 h
      exact ⟨(E0, s2), A, rfl⟩
    match_initial_states := by
      rintro s1 ⟨t, s2⟩ h1 ⟨h2, ht⟩
      simp only at h2 ht
      subst ht
      obtain ⟨i, s1', A, B⟩ := sim.match_initial_states s1 s2 h1 h2
      exact ⟨i, s1', A, .intro _ _ _ _ _ (.refl _) B (.inl rfl)⟩
    match_final_states := by
      rintro i s1 ⟨t, s2⟩ r hm hsafe ⟨hf, ht⟩
      simp only at hf ht
      subst ht
      cases hm with
      | intro _ _ s1' H0 M _ =>
        obtain ⟨s1'', A, B⟩ := sim.match_final_states i s1' s2 r M (star_safe H0 hsafe) hf
        exact ⟨s1'', star_trans H0 A rfl, B⟩
    progress := fun _ _ _ hm hsafe => fbs_progress sim hm hsafe
    simulation := fun _ _ _ hst _ _ hm hsafe => fbs_simulation sim L1single L2wb hst hm hsafe
    public_preserved := sim.public_preserved }

end Smallstep
end CC
