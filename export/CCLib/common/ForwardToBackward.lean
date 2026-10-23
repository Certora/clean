/-
  From forward to backward simulations — port of the `FORWARD_TO_BACKWARD`
  section of `common/Smallstep.v`: a forward simulation from a receptive
  source semantics to a determinate target semantics can be turned into a
  backward simulation (`forward_to_backward_simulation`).
-/
import CCLib.common.BackwardSimulation

namespace CC
namespace Smallstep

/-! ## Facts about traces -/

/-- `Events.match_traces_preserved` -/
theorem matchTraces_preserved {ge1 ge2 : Senv}
    (h : ∀ id, ge2.public_symbol id = ge1.public_symbol id) {t1 t2 : Trace}
    (hm : MatchTraces ge1 t1 t2) : MatchTraces ge2 t1 t2 := by
  have hv : ∀ ev, EventValValid ge1 ev → EventValValid ge2 ev := by
    intro ev; cases ev <;> simp [EventValValid, h]
  cases hm with
  | nil => exact .nil
  | syscall name args r1 r2 h1 h2 h3 => exact .syscall name args r1 r2 (hv _ h1) (hv _ h2) h3
  | vload chunk id ofs r1 r2 h1 h2 h3 => exact .vload chunk id ofs r1 r2 (hv _ h1) (hv _ h2) h3
  | vstore => exact .vstore _ _ _ _
  | annot => exact .annot _ _

theorem matchTraces_E0_left {ge : Senv} {t : Trace} (h : MatchTraces ge E0 t) : t = E0 := by
  cases h; rfl

theorem matchTraces_E0_right {ge : Senv} {t : Trace} (h : MatchTraces ge t E0) : t = E0 := by
  cases h; rfl

/-- `Smallstep.not_silent_length` -/
theorem not_silent_length {t1 t2 : Trace} (h : (Eapp t1 t2).length ≤ 1) :
    t1 = E0 ∨ t2 = E0 := by
  cases t1 with
  | nil => exact Or.inl rfl
  | cons a l =>
    cases t2 with
    | nil => exact Or.inr rfl
    | cons b l' => simp [Eapp] at h

theorem cons_ne_E0 {a : Event} {l : Trace} : (a :: l : Trace) ≠ E0 := List.cons_ne_nil a l

/-! ## The construction -/

section F2B
variable {L1 L2 : Semantics} {index : Type} {order : index → index → Prop}
  {match_states : index → L1.state → L2.state → Prop}

/-- `Smallstep.f2b_transitions` -/
inductive F2BTransitions (match_states : index → L1.state → L2.state → Prop) :
    L1.state → L2.state → Prop where
  | final {s1 s2 s1' r} : Star L1.step s1 E0 s1' → L1.final_state s1' r →
      L2.final_state s2 r → F2BTransitions match_states s1 s2
  | step {s1 s2 s1' t s1'' s2' i' i''} : Star L1.step s1 E0 s1' → L1.step s1' t s1'' →
      Plus L2.step s2 t s2' → match_states i' s1' s2 → match_states i'' s1'' s2' →
      F2BTransitions match_states s1 s2

/-- `Smallstep.f2b_index` -/
inductive F2BIndex where
  | before (n : Nat)
  | after (n : Nat)

/-- `Smallstep.f2b_order` -/
inductive F2BOrder : F2BIndex → F2BIndex → Prop where
  | before {n n'} : n' < n → F2BOrder (.before n') (.before n)
  | after {n n'} : n' < n → F2BOrder (.after n') (.after n)
  | switch {n n'} : F2BOrder (.before n') (.after n)

/-- `Smallstep.wf_f2b_order` -/
theorem wf_f2b_order : WellFounded F2BOrder := by
  have acc1 : ∀ n, Acc F2BOrder (.before n) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      constructor
      intro y hy
      cases hy with
      | before h => exact ih _ h
  have acc2 : ∀ n, Acc F2BOrder (.after n) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      constructor
      intro y hy
      cases hy with
      | after h => exact ih _ h
      | switch => exact acc1 _
  exact ⟨fun a => by cases a <;> first | exact acc1 _ | exact acc2 _⟩

/-- `Smallstep.f2b_match_states` -/
inductive F2BMatchStates (match_states : index → L1.state → L2.state → Prop) :
    F2BIndex → L1.state → L2.state → Prop where
  | matchAt {i s1 s2} : match_states i s1 s2 → F2BMatchStates match_states (.after 0) s1 s2
  | before {s1 t s1' s2b s2 n s2a i} : L1.step s1 t s1' → t ≠ E0 →
      Star L2.step s2b E0 s2 → StarN L2.step n s2 t s2a → match_states i s1 s2b →
      F2BMatchStates match_states (.before n) s1 s2
  | after {n s2 s2a s1 i} : StarN L2.step (n + 1) s2 E0 s2a → match_states i s1 s2a →
      F2BMatchStates match_states (.after (n + 1)) s1 s2

/-- `Smallstep.f2b_match_after'` -/
theorem f2b_match_after' {n s2 s2a s1 i} (h : StarN L2.step n s2 E0 s2a)
    (hm : match_states i s1 s2a) : F2BMatchStates match_states (.after n) s1 s2 := by
  cases n with
  | zero => cases h; exact .matchAt hm
  | succ n => exact .after h hm

variable (FS : FSimProperties L1 L2 index order match_states)
  (L1_receptive : Receptive L1) (L2_determinate : Determinate L2)

include FS in
/-- `Smallstep.f2b_progress` -/
theorem f2b_progress : ∀ i s1 s2, match_states i s1 s2 → Safe L1 s1 →
    F2BTransitions match_states s1 s2 := by
  intro i
  induction i using FS.order_wf.induction with
  | _ i ih =>
    intro s1 s2 hm hs
    rcases hs s1 (.refl _) with ⟨r, hf⟩ | ⟨t, s1', hst⟩
    · exact .final (.refl _) hf (FS.final_states _ _ _ _ hm hf)
    · rcases FS.simulation' hst hm with ⟨i', s2', hp, hm'⟩ | ⟨i', ho, rfl, hm'⟩
      · exact .step (.refl _) hst hp hm hm'
      · cases ih i' ho s1' s2 hm' (star_safe (star_one hst) hs) with
        | final h1 h2 h3 => exact .final (star_left hst h1 rfl) h2 h3
        | step h1 h2 h3 h4 h5 => exact .step (star_left hst h1 rfl) h2 h3 h4 h5

include FS in
/-- `Smallstep.fsim_simulation_not_E0` -/
theorem fsim_simulation_not_E0 {s1 t s1'} (hst : L1.step s1 t s1') (ht : t ≠ E0)
    {i s2} (hm : match_states i s1 s2) :
    ∃ i' s2', Plus L2.step s2 t s2' ∧ match_states i' s1' s2' := by
  rcases FS.simulation' hst hm with ⟨i', s2', hp, hm'⟩ | ⟨_, _, h, _⟩
  · exact ⟨i', s2', hp, hm'⟩
  · exact absurd h ht

include FS L2_determinate in
/-- `Smallstep.f2b_determinacy_inv` -/
theorem f2b_determinacy_inv {s2 t' s2' t'' s2''} (h1 : L2.step s2 t' s2')
    (h2 : L2.step s2 t'' s2'') :
    (t' = E0 ∧ t'' = E0 ∧ s2' = s2'') ∨
    (t' ≠ E0 ∧ t'' ≠ E0 ∧ MatchTraces L1.symbolenv t' t'') := by
  obtain ⟨hmt, heq⟩ := L2_determinate.sd_determ _ _ _ _ _ h1 h2
  by_cases ht' : t' = E0
  · subst ht'
    have := matchTraces_E0_left hmt
    subst this
    exact Or.inl ⟨rfl, rfl, heq rfl⟩
  · by_cases ht'' : t'' = E0
    · subst ht''
      exact absurd (matchTraces_E0_right hmt) ht'
    · exact Or.inr ⟨ht', ht'',
        matchTraces_preserved (fun id => (FS.public_preserved id).symm) hmt⟩

include FS L2_determinate in
/-- `Smallstep.f2b_determinacy_star` -/
theorem f2b_determinacy_star {s s1} (h : Star L2.step s E0 s1) :
    ∀ {t s2 s3}, L2.step s1 t s2 → t ≠ E0 → Star L2.step s t s3 → Star L2.step s1 t s3 := by
  refine star_E0_ind (fun s s1 => ∀ {t s2 s3}, L2.step s1 t s2 → t ≠ E0 →
    Star L2.step s t s3 → Star L2.step s1 t s3) ?_ ?_ h
  · intro s t s2 s3 _ _ h3; exact h3
  · intro s0 s0' s1 hr ih t s2 s3 h1 ht h3
    cases h3 with
    | refl => exact absurd rfl ht
    | @step _ t' x t'' _ _ hx hxs heq =>
      rcases f2b_determinacy_inv FS L2_determinate hr hx with ⟨_, rfl, rfl⟩ | ⟨h, _, _⟩
      · exact ih h1 ht (by rw [heq]; exact hxs)
      · exact absurd rfl h

/-- First step of a run of `n + 1` steps. -/
theorem starN_succ_inv {σ : Type} {R : σ → Trace → σ → Prop} {n s t s'}
    (h : StarN R (n + 1) s t s') :
    ∃ t1 x t2, R s t1 x ∧ StarN R n x t2 s' ∧ t = Eapp t1 t2 := by
  cases h with
  | step h1 h2 h3 => exact ⟨_, _, _, h1, h2, h3⟩

theorem length_le_one_of_single {L : Semantics} (hs : SingleEvents L) {s t s'}
    (h : L.step s t s') : (Eapp t E0).length ≤ 1 := by
  rw [E0_right]; exact hs _ _ _ h

include FS L1_receptive L2_determinate in
/-- `Smallstep.f2b_simulation_step` -/
theorem f2b_simulation_step {s2 t s2'} (hst2 : L2.step s2 t s2') {i s1}
    (hm : F2BMatchStates match_states i s1 s2) (hs : Safe L1 s1) :
    ∃ i' s1', (Plus L1.step s1 t s1' ∨ (Star L1.step s1 t s1' ∧ F2BOrder i' i)) ∧
      F2BMatchStates match_states i' s1' s2' := by
  have hdet := @f2b_determinacy_inv L1 L2 index order match_states FS L2_determinate
  cases hm with
  | matchAt hm0 =>
    cases f2b_progress FS _ s1 s2 hm0 hs with
    | final _ _ hf2 => exact (L2_determinate.sd_final_nostep _ _ hf2 _ _ hst2).elim
    | @step s1' t1 s1'' s2x i' i'' h1 h2 h3 h4 h5 =>
      obtain ⟨hr3, hs3, heq3⟩ := h3
      rename_i t3 s4 t4
      rcases hdet hr3 hst2 with ⟨rfl, rfl, rfl⟩ | ⟨hn3, hnt, hmt⟩
      · -- L2 made a silent step
        by_cases ht1 : t1 = E0
        · subst ht1
          have : t4 = E0 := (Eapp_eq_E0 heq3.symm).2
          subst this
          obtain ⟨n, hn⟩ := star_starN hs3
          exact ⟨.after n, s1'', Or.inl (plus_right h1 h2 rfl), f2b_match_after' hn h5⟩
        · have : t1 = t4 := heq3
          subst this
          obtain ⟨n, hn⟩ := star_starN hs3
          exact ⟨.before n, s1', Or.inr ⟨h1, .switch⟩,
            .before h2 ht1 (star_one hst2) hn h4⟩
      · -- L2 made a non-silent step, and so does L1
        rcases not_silent_length (heq3 ▸ L1_receptive.sr_traces _ _ _ h2) with h | h
        · exact absurd h hn3
        subst h
        rw [E0_right] at heq3
        subst heq3
        obtain ⟨s1''', hst1⟩ := L1_receptive.sr_receptive _ _ _ _ h2 hmt
        obtain ⟨i3, s2''', hp, hm3⟩ := fsim_simulation_not_E0 FS hst1 hnt h4
        obtain ⟨hr5, hs5, heq5⟩ := hp
        rename_i t5 s5 t6
        rcases not_silent_length (heq5 ▸ L1_receptive.sr_traces _ _ _ hst1) with h | h
        · subst h
          rcases hdet hst2 hr5 with ⟨h', _, _⟩ | ⟨_, h', _⟩
          · exact absurd h' hnt
          · exact absurd rfl h'
        subst h
        rw [E0_right] at heq5
        subst heq5
        rcases hdet hst2 hr5 with ⟨h', _, _⟩ | _
        · exact absurd h' hnt
        have : s5 = s2' := (L2_determinate.sd_determ _ _ _ _ _ hr5 hst2).2 rfl
        subst this
        obtain ⟨n, hn⟩ := star_starN hs5
        exact ⟨.after n, s1''', Or.inl (plus_right h1 hst1 rfl), f2b_match_after' hn hm3⟩
  | before h1 ht1 hs2 hn hm0 =>
    cases hn with
    | refl => exact absurd rfl ht1
    | step hr7 hn7 heq7 =>
      rcases hdet hr7 hst2 with ⟨rfl, rfl, rfl⟩ | ⟨hn7', hnt, hmt⟩
      · exact ⟨.before _, s1, Or.inr ⟨.refl _, .before (Nat.lt_succ_self _)⟩,
          .before h1 ht1 (star_right hs2 hr7 rfl) (by rw [heq7]; exact hn7) hm0⟩
      · rcases not_silent_length (heq7 ▸ L1_receptive.sr_traces _ _ _ h1) with h | h
        · exact absurd h hn7'
        subst h
        rw [E0_right] at heq7
        subst heq7
        obtain ⟨s1''', hst1⟩ := L1_receptive.sr_receptive _ _ _ _ h1 hmt
        obtain ⟨i3, s2''', hp, hm3⟩ := fsim_simulation_not_E0 FS hst1 hnt hm0
        have hR := f2b_determinacy_star FS L2_determinate hs2 hst2 hnt (plus_star hp)
        cases hR with
        | refl => exact absurd rfl hnt
        | @step _ t9 s9 t10 _ _ hr9 hs9 heq9 =>
          rcases not_silent_length (heq9 ▸ L1_receptive.sr_traces _ _ _ hst1) with h | h
          · subst h
            rcases hdet hst2 hr9 with ⟨h', _, _⟩ | ⟨_, h', _⟩
            · exact absurd h' hnt
            · exact absurd rfl h'
          subst h
          rw [E0_right] at heq9
          subst heq9
          have : s9 = s2' := (L2_determinate.sd_determ _ _ _ _ _ hr9 hst2).2 rfl
          subst this
          obtain ⟨n', hn'⟩ := star_starN hs9
          exact ⟨.after n', s1''', Or.inl (plus_one hst1), f2b_match_after' hn' hm3⟩
  | after hn hm0 =>
    obtain ⟨t7, s7, t8, hr7, hn7, heq7⟩ := starN_succ_inv hn
    obtain ⟨rfl, rfl⟩ := Eapp_eq_E0 heq7.symm
    rcases hdet hr7 hst2 with ⟨_, rfl, rfl⟩ | ⟨h, _, _⟩
    · exact ⟨.after _, s1, Or.inr ⟨.refl _, .after (Nat.lt_succ_self _)⟩,
        f2b_match_after' hn7 hm0⟩
    · exact absurd rfl h

end F2B

/-- `Smallstep.forward_to_backward_simulation`: a forward simulation from a
receptive semantics to a determinate one yields a backward simulation. -/
theorem forward_to_backward_simulation {L1 L2 : Semantics} (FS : ForwardSimulation L1 L2)
    (L1_receptive : Receptive L1) (L2_determinate : Determinate L2) :
    BackwardSimulation L1 L2 := by
  obtain ⟨index, order, match_states, FS⟩ := FS
  have first_step : ∀ {n s2 t s2a}, StarN L2.step n s2 t s2a → t ≠ E0 →
      ∃ t' s', L2.step s2 t' s' := by
    intro n s2 t s2a h ht
    cases h with
    | refl => exact absurd rfl ht
    | step h1 _ _ => exact ⟨_, _, h1⟩
  refine ⟨F2BIndex, F2BOrder, F2BMatchStates match_states, ?_⟩
  exact
    { order_wf := wf_f2b_order
      initial_states_exist := fun s1 h => by
        obtain ⟨i, s2, h2, _⟩ := FS.initial_states s1 h
        exact ⟨s2, h2⟩
      match_initial_states := fun s1 s2 h1 h2 => by
        obtain ⟨i, s2', h2', hm⟩ := FS.initial_states s1 h1
        have : s2 = s2' := L2_determinate.sd_initial_determ _ _ h2 h2'
        subst this
        exact ⟨.after 0, s1, h1, .matchAt hm⟩
      match_final_states := fun i s1 s2 r hm hs hf => by
        cases hm with
        | matchAt hm0 =>
          cases f2b_progress FS _ s1 s2 hm0 hs with
          | final h1 hf1 hf2 =>
            exact ⟨_, h1, L2_determinate.sd_final_determ _ _ _ hf2 hf ▸ hf1⟩
          | step _ _ hp _ _ =>
            obtain ⟨hr, _, _⟩ := hp
            exact (L2_determinate.sd_final_nostep _ _ hf _ _ hr).elim
        | before _ ht _ hn _ =>
          obtain ⟨_, _, hst⟩ := first_step hn ht
          exact (L2_determinate.sd_final_nostep _ _ hf _ _ hst).elim
        | after hn _ =>
          obtain ⟨_, _, _, hr, _, _⟩ := starN_succ_inv hn
          exact (L2_determinate.sd_final_nostep _ _ hf _ _ hr).elim
      progress := fun i s1 s2 hm hs => by
        cases hm with
        | matchAt hm0 =>
          cases f2b_progress FS _ s1 s2 hm0 hs with
          | final _ _ hf2 => exact Or.inl ⟨_, hf2⟩
          | step _ _ hp _ _ =>
            obtain ⟨hr, _, _⟩ := hp
            exact Or.inr ⟨_, _, hr⟩
        | before _ ht _ hn _ => exact Or.inr (first_step hn ht)
        | after hn _ =>
          obtain ⟨_, _, _, hr, _, _⟩ := starN_succ_inv hn
          exact Or.inr ⟨_, _, hr⟩
      simulation := fun s2 t s2' hst i s1 hm hs =>
        f2b_simulation_step FS L1_receptive L2_determinate hst hm hs
      public_preserved := FS.public_preserved }

end Smallstep
end CC
