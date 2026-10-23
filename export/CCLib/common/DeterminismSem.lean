/-
  Deterministic semantics — port of the rest of `common/Determinism.v` (the
  worlds themselves are in `CCLib.common.Worlds`):

  * `match_possible_traces`, `possible_traceinf` (+ `_app`, `_app_inv`) and
    `possible_behavior`;
  * the record `sem_deterministic` and section `DETERM_SEM`
    (`star_step_diamond`, `steps_deterministic`, the exclusivity lemmas for
    silent and reactive divergence, `forever_reactive_determ`,
    `state_behaves_deterministic`, `program_behaves_deterministic`);
  * section `WORLD_SEM`: `world_sem` and `world_sem_deterministic`.

  Differences with Rocq:
  * Infinite traces are streams `Nat → Event` (`CCLib.common.Smallstep`), so
    Rocq's bisimilarity `traceinf_sim` is plain equality
    (`CCLib.common.EventsTraceinf.traceinfSim_iff_eq`).  Hence
    `same_behaviors beh1 beh2` is just `beh1 = beh2`, and
    `program_behaves_deterministic` concludes `beh1 = beh2`.
  * `possible_traceinf` is stated with an explicit sequence of worlds instead
    of a `CoInductive`.
  * `possible_traceinf'` (an alternative, unused definition) is not ported.
-/
import CCLib.common.Worlds
import CCLib.common.Behaviors
import CCLib.common.EventsTraceinf

namespace CC
namespace Smallstep

open ProgramBehavior

/-! ## Possible traces -/

/-- `Determinism.match_possible_traces`: two matching traces that are both
    possible from the same world are equal and lead to the same world. -/
theorem match_possible_traces {ge : Senv} {t1 t2 : Trace} {w0 w1 w2 : World}
    (hm : MatchTraces ge t1 t2) (h1 : PossibleTrace w0 t1 w1) (h2 : PossibleTrace w0 t2 w2) :
    t1 = t2 ∧ w1 = w2 := by
  cases hm with
  | nil => exact ⟨rfl, (possibleTrace_E0_inv h1).trans (possibleTrace_E0_inv h2).symm⟩
  | syscall name args res1 res2 =>
    have e1 := possibleTrace_single_inv h1
    have e2 := possibleTrace_single_inv h2
    cases e1 with | syscall _ _ _ _ he1 =>
    cases e2 with | syscall _ _ _ _ he2 =>
    rw [he1] at he2; cases he2; exact ⟨rfl, rfl⟩
  | vload chunk id ofs res1 res2 =>
    have e1 := possibleTrace_single_inv h1
    have e2 := possibleTrace_single_inv h2
    cases e1 with | vload _ _ _ _ _ he1 =>
    cases e2 with | vload _ _ _ _ _ he2 =>
    rw [he1] at he2; cases he2; exact ⟨rfl, rfl⟩
  | vstore chunk id ofs arg =>
    have e1 := possibleTrace_single_inv h1
    have e2 := possibleTrace_single_inv h2
    cases e1 with | vstore _ _ _ _ _ he1 =>
    cases e2 with | vstore _ _ _ _ _ he2 =>
    rw [he1] at he2; cases he2; exact ⟨rfl, rfl⟩
  | annot text args =>
    have e1 := possibleTrace_single_inv h1
    have e2 := possibleTrace_single_inv h2
    cases e1; cases e2; exact ⟨rfl, rfl⟩

/-- `Determinism.possible_traceinf`: every event of the infinite trace `T` is
    accepted, through the worlds `ws 0 = w, ws 1, …`. -/
def PossibleTraceinf (w : World) (T : Traceinf) : Prop :=
  ∃ ws : Nat → World, ws 0 = w ∧ ∀ n, PossibleEvent (ws n) (T n) (ws (n + 1))

/-- The constructor of Rocq's `possible_traceinf`. -/
theorem PossibleTraceinf.cons {w1 ev w2 T} (he : PossibleEvent w1 ev w2)
    (hT : PossibleTraceinf w2 T) : PossibleTraceinf w1 (Econsinf ev T) := by
  obtain ⟨ws, h0, hs⟩ := hT
  refine ⟨fun n => match n with | 0 => w1 | k + 1 => ws k, rfl, fun n => ?_⟩
  cases n with
  | zero => simpa [h0] using he
  | succ n => simpa using hs n

/-- Inversion of Rocq's `possible_traceinf`. -/
theorem PossibleTraceinf.inv {w1 ev T} (h : PossibleTraceinf w1 (Econsinf ev T)) :
    ∃ w2, PossibleEvent w1 ev w2 ∧ PossibleTraceinf w2 T := by
  obtain ⟨ws, h0, hs⟩ := h
  refine ⟨ws 1, ?_, fun n => ws (n + 1), rfl, fun n => ?_⟩
  · have := hs 0; rw [h0] at this; simpa using this
  · simpa using hs (n + 1)

/-- `Determinism.possible_traceinf_app` -/
theorem possibleTraceinf_app {w0 t1 w1 T} (h1 : PossibleTrace w0 t1 w1)
    (h2 : PossibleTraceinf w1 T) : PossibleTraceinf w0 (Eappinf t1 T) := by
  induction h1 with
  | nil => rwa [Eappinf_E0]
  | cons _ _ _ _ _ he _ ih => rw [Eappinf_cons]; exact .cons he (ih h2)

/-- `Determinism.possible_traceinf_app_inv` -/
theorem possibleTraceinf_app_inv {t1 T w0} (h : PossibleTraceinf w0 (Eappinf t1 T)) :
    ∃ w1, PossibleTrace w0 t1 w1 ∧ PossibleTraceinf w1 T := by
  induction t1 generalizing w0 with
  | nil => rw [show ([] : Trace) = E0 from rfl, Eappinf_E0] at h; exact ⟨w0, .nil _, h⟩
  | cons ev t ih =>
    rw [Eappinf_cons] at h
    obtain ⟨w2, he, h2⟩ := h.inv
    obtain ⟨w1, h1, hT⟩ := ih h2
    exact ⟨w1, .cons _ _ _ _ _ he h1, hT⟩

/-- `Determinism.possible_behavior` -/
def PossibleBehavior (w : World) : ProgramBehavior → Prop
  | Terminates t _ => ∃ w', PossibleTrace w t w'
  | Diverges t => ∃ w', PossibleTrace w t w'
  | Reacts T => PossibleTraceinf w T
  | Goes_wrong t => ∃ w', PossibleTrace w t w'

/-! ## Deterministic semantics -/

/-- `Determinism.sem_deterministic` -/
structure SemDeterministic (L : Semantics) : Prop where
  det_step : ∀ s0 t1 s1 t2 s2, L.step s0 t1 s1 → L.step s0 t2 s2 → s1 = s2 ∧ t1 = t2
  det_initial_state : ∀ s1 s2, L.initial_state s1 → L.initial_state s2 → s1 = s2
  det_final_state : ∀ s r1 r2, L.final_state s r1 → L.final_state s r2 → r1 = r2
  det_final_nostep : ∀ s r, L.final_state s r → Nostep L.step s

section DETERM_SEM
variable {L : Semantics} (DET : SemDeterministic L)
include DET

/-- `Determinism.star_step_diamond` -/
theorem star_step_diamond {s0 t1 s1 t2 s2} (h1 : Star L.step s0 t1 s1)
    (h2 : Star L.step s0 t2 s2) :
    ∃ t, (Star L.step s1 t s2 ∧ t2 = Eapp t1 t) ∨ (Star L.step s2 t s1 ∧ t1 = Eapp t2 t) := by
  induction h1 generalizing t2 s2 with
  | refl => exact ⟨t2, Or.inl ⟨h2, rfl⟩⟩
  | step hr hs heq ih =>
    cases h2 with
    | refl => exact ⟨_, Or.inr ⟨.step hr hs heq, rfl⟩⟩
    | step hr' hs' heq' =>
      obtain ⟨rfl, rfl⟩ := DET.det_step _ _ _ _ _ hr hr'
      obtain ⟨t, ⟨hst, rfl⟩ | ⟨hst, rfl⟩⟩ := ih hs'
      · exact ⟨t, Or.inl ⟨hst, by rw [heq', heq, Eapp_assoc]⟩⟩
      · exact ⟨t, Or.inr ⟨hst, by rw [heq', heq, Eapp_assoc]⟩⟩

/-- `Determinism.star_step_triangle` -/
theorem star_step_triangle {s0 t1 s1 t2 s2} (h1 : Star L.step s0 t1 s1)
    (h2 : Star L.step s0 t2 s2) (hno : Nostep L.step s2) :
    ∃ t, Star L.step s1 t s2 ∧ t2 = Eapp t1 t := by
  obtain ⟨t, ⟨hst, rfl⟩ | ⟨hst, rfl⟩⟩ := star_step_diamond DET h1 h2
  · exact ⟨t, hst, rfl⟩
  · cases hst with
    | refl => exact ⟨E0, .refl _, by rw [E0_right, E0_right]⟩
    | step hr _ _ => exact (hno _ _ hr).elim

/-- `Determinism.steps_deterministic` -/
theorem steps_deterministic {s0 t1 s1 t2 s2} (h1 : Star L.step s0 t1 s1)
    (h2 : Star L.step s0 t2 s2) (hno1 : Nostep L.step s1) (hno2 : Nostep L.step s2) :
    t1 = t2 ∧ s1 = s2 := by
  obtain ⟨t, hst, rfl⟩ := star_step_triangle DET h1 h2 hno2
  cases hst with
  | refl => exact ⟨(E0_right _).symm, rfl⟩
  | step hr _ _ => exact (hno1 _ _ hr).elim

/-- `Determinism.terminates_not_goes_wrong` -/
theorem terminates_not_goes_wrong {s t1 s1 r t2 s2} (h1 : Star L.step s t1 s1)
    (hf : L.final_state s1 r) (h2 : Star L.step s t2 s2) (hno : Nostep L.step s2)
    (hnf : ∀ r, ¬ L.final_state s2 r) : False := by
  obtain ⟨_, rfl⟩ := steps_deterministic DET h1 h2 (DET.det_final_nostep _ _ hf) hno
  exact hnf _ hf

/-- `Determinism.star_final_not_forever_silent` -/
theorem star_final_not_forever_silent {s t s'} (h : Star L.step s t s')
    (hno : Nostep L.step s') (hfs : ForeverSilent L.step s) : False := by
  induction h with
  | refl => obtain ⟨s2, hr, _⟩ := hfs.inv; exact hno _ _ hr
  | step hr _ _ ih =>
    obtain ⟨s2, hr', hfs'⟩ := hfs.inv
    obtain ⟨rfl, _⟩ := DET.det_step _ _ _ _ _ hr hr'
    exact ih hno hfs'

/-- `Determinism.star2_final_not_forever_silent` -/
theorem star2_final_not_forever_silent {s t1 s1 t2 s2} (h1 : Star L.step s t1 s1)
    (hno : Nostep L.step s1) (h2 : Star L.step s t2 s2) (hfs : ForeverSilent L.step s2) :
    False := by
  obtain ⟨t, hst, _⟩ := star_step_triangle DET h2 h1 hno
  exact star_final_not_forever_silent DET hst hno hfs

/-- `Determinism.star_final_not_forever_reactive` -/
theorem star_final_not_forever_reactive {s t s'} (h : Star L.step s t s') {T}
    (hno : Nostep L.step s') (hfr : ForeverReactive L.step s T) : False := by
  induction h generalizing T with
  | refl =>
    obtain ⟨s2, t2, _, hst, hne, _⟩ := hfr.inv
    cases hst with
    | refl => exact hne rfl
    | step hr _ _ => exact hno _ _ hr
  | step hr hs _ ih =>
    obtain ⟨s2, t2, T2, hst, hne, hfr2, _⟩ := hfr.inv
    cases hst with
    | refl => exact hne rfl
    | step hr' hs' _ =>
      obtain ⟨rfl, rfl⟩ := DET.det_step _ _ _ _ _ hr hr'
      exact ih hno (star_forever_reactive hs' hfr2)

/-- `Determinism.star_forever_silent_inv` -/
theorem star_forever_silent_inv {s t s'} (h : Star L.step s t s')
    (hfs : ForeverSilent L.step s) : t = E0 ∧ ForeverSilent L.step s' := by
  induction h with
  | refl => exact ⟨rfl, hfs⟩
  | step hr _ heq ih =>
    obtain ⟨s2, hr', hfs'⟩ := hfs.inv
    obtain ⟨rfl, rfl⟩ := DET.det_step _ _ _ _ _ hr hr'
    obtain ⟨rfl, h⟩ := ih hfs'
    exact ⟨heq, h⟩

/-- `Determinism.forever_silent_reactive_exclusive` -/
theorem forever_silent_reactive_exclusive {s T} (hfs : ForeverSilent L.step s)
    (hfr : ForeverReactive L.step s T) : False := by
  obtain ⟨_, _, _, hst, hne, _⟩ := hfr.inv
  exact hne (star_forever_silent_inv DET hst hfs).1

/-- `Determinism.forever_reactive_inv2` -/
theorem forever_reactive_inv2 {s t1 s1} (h1 : Star L.step s t1 s1) {t2 s2 T1 T2}
    (h2 : Star L.step s t2 s2) (hne1 : t1 ≠ E0) (hne2 : t2 ≠ E0)
    (hfr1 : ForeverReactive L.step s1 T1) (hfr2 : ForeverReactive L.step s2 T2) :
    ∃ s' t T1' T2', t ≠ E0 ∧ ForeverReactive L.step s' T1' ∧ ForeverReactive L.step s' T2'
      ∧ Eappinf t1 T1 = Eappinf t T1' ∧ Eappinf t2 T2 = Eappinf t T2' := by
  induction h1 generalizing t2 s2 T2 with
  | refl => exact (hne1 rfl).elim
  | @step _ ta sa tb _ _ hr hs heq ih =>
    cases h2 with
    | refl => exact (hne2 rfl).elim
    | @step _ ta' _ tb' _ _ hr' hs' heq' =>
      obtain ⟨rfl, rfl⟩ := DET.det_step _ _ _ _ _ hr hr'
      subst heq heq'
      cases ta with
      | nil => exact ih hs' hne1 hne2 hfr1 hfr2
      | cons e t3 =>
        exact ⟨sa, e :: t3, Eappinf tb T1, Eappinf tb' T2, List.cons_ne_nil _ _,
          star_forever_reactive hs hfr1, star_forever_reactive hs' hfr2,
          Eappinf_assoc _ _ _, Eappinf_assoc _ _ _⟩

/-- `Determinism.forever_reactive_determ`.  With traces as streams, Rocq's
    `traceinf_sim T1 T2` is `T1 = T2`. -/
theorem forever_reactive_determ {s T1 T2} (hfr1 : ForeverReactive L.step s T1)
    (hfr2 : ForeverReactive L.step s T2) : T1 = T2 := by
  funext n
  induction n using Nat.strongRecOn generalizing s T1 T2 with
  | ind n ih =>
    obtain ⟨s1, t1, T1', hs1, hne1, hfr1', rfl⟩ := hfr1.inv
    obtain ⟨s2, t2, T2', hs2, hne2, hfr2', rfl⟩ := hfr2.inv
    obtain ⟨s', t, U1, U2, hne, hu1, hu2, e1, e2⟩ :=
      forever_reactive_inv2 DET hs1 hs2 hne1 hne2 hfr1' hfr2'
    rw [e1, e2]
    simp only [Eappinf]
    split
    · rfl
    · have : t.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
      exact ih (n - t.length) (by omega) hu1 hu2

/-- `Determinism.star_forever_reactive_inv` -/
theorem star_forever_reactive_inv {s t s'} (h : Star L.step s t s') {T}
    (hfr : ForeverReactive L.step s T) : ∃ T', ForeverReactive L.step s' T' ∧ T = Eappinf t T' := by
  induction h generalizing T with
  | refl => exact ⟨T, hfr, (Eappinf_E0 T).symm⟩
  | step hr hs heq ih =>
    obtain ⟨s2, t2, T2, hst, hne, hfr2, rfl⟩ := hfr.inv
    cases hst with
    | refl => exact (hne rfl).elim
    | step hr' hs' heq' =>
      obtain ⟨rfl, rfl⟩ := DET.det_step _ _ _ _ _ hr hr'
      obtain ⟨T', hT', e⟩ := ih (star_forever_reactive hs' hfr2)
      refine ⟨T', hT', ?_⟩
      rw [heq', heq, Eappinf_assoc, Eappinf_assoc, e]

/-- `Determinism.forever_silent_reactive_exclusive2` -/
theorem forever_silent_reactive_exclusive2 {s t s' T} (h : Star L.step s t s')
    (hfs : ForeverSilent L.step s') (hfr : ForeverReactive L.step s T) : False := by
  obtain ⟨T', hT', _⟩ := star_forever_reactive_inv DET h hfr
  exact forever_silent_reactive_exclusive DET hfs hT'

/-- `Determinism.state_behaves_deterministic`: Rocq's `same_behaviors` is
    equality here (infinite traces are streams). -/
theorem state_behaves_deterministic {s beh1 beh2} (h1 : StateBehaves L s beh1)
    (h2 : StateBehaves L s beh2) : beh1 = beh2 := by
  have dfns := DET.det_final_nostep
  cases h1 with
  | terminates hs1 hf1 =>
    cases h2 with
    | terminates hs2 hf2 =>
      obtain ⟨rfl, rfl⟩ := steps_deterministic DET hs1 hs2 (dfns _ _ hf1) (dfns _ _ hf2)
      rw [DET.det_final_state _ _ _ hf1 hf2]
    | diverges hs2 hfs => exact (star2_final_not_forever_silent DET hs1 (dfns _ _ hf1) hs2 hfs).elim
    | reacts hfr => exact (star_final_not_forever_reactive DET hs1 (dfns _ _ hf1) hfr).elim
    | goes_wrong hs2 hno hnf => exact (terminates_not_goes_wrong DET hs1 hf1 hs2 hno hnf).elim
  | diverges hs1 hfs1 =>
    cases h2 with
    | terminates hs2 hf2 =>
      exact (star2_final_not_forever_silent DET hs2 (dfns _ _ hf2) hs1 hfs1).elim
    | diverges hs2 hfs2 =>
      obtain ⟨t, ⟨hst, rfl⟩ | ⟨hst, rfl⟩⟩ := star_step_diamond DET hs1 hs2
      · rw [(star_forever_silent_inv DET hst hfs1).1, E0_right]
      · rw [(star_forever_silent_inv DET hst hfs2).1, E0_right]
    | reacts hfr => exact (forever_silent_reactive_exclusive2 DET hs1 hfs1 hfr).elim
    | goes_wrong hs2 hno _ => exact (star2_final_not_forever_silent DET hs2 hno hs1 hfs1).elim
  | reacts hfr1 =>
    cases h2 with
    | terminates hs2 hf2 => exact (star_final_not_forever_reactive DET hs2 (dfns _ _ hf2) hfr1).elim
    | diverges hs2 hfs2 => exact (forever_silent_reactive_exclusive2 DET hs2 hfs2 hfr1).elim
    | reacts hfr2 => rw [forever_reactive_determ DET hfr1 hfr2]
    | goes_wrong hs2 hno _ => exact (star_final_not_forever_reactive DET hs2 hno hfr1).elim
  | goes_wrong hs1 hno1 hnf1 =>
    cases h2 with
    | terminates hs2 hf2 => exact (terminates_not_goes_wrong DET hs2 hf2 hs1 hno1 hnf1).elim
    | diverges hs2 hfs2 => exact (star2_final_not_forever_silent DET hs1 hno1 hs2 hfs2).elim
    | reacts hfr => exact (star_final_not_forever_reactive DET hs1 hno1 hfr).elim
    | goes_wrong hs2 hno2 _ =>
      rw [(steps_deterministic DET hs1 hs2 hno1 hno2).1]

/-- **`Determinism.program_behaves_deterministic`**: a deterministic semantics
    has exactly one behaviour. -/
theorem program_behaves_deterministic {beh1 beh2} (h1 : ProgramBehaves L beh1)
    (h2 : ProgramBehaves L beh2) : beh1 = beh2 := by
  cases h1 with
  | runs hi1 hb1 =>
    cases h2 with
    | runs hi2 hb2 =>
      obtain rfl := DET.det_initial_state _ _ hi1 hi2
      exact state_behaves_deterministic DET hb1 hb2
    | goes_initially_wrong hno => exact (hno _ hi1).elim
  | goes_initially_wrong hno =>
    cases h2 with
    | runs hi2 _ => exact (hno _ hi2).elim
    | goes_initially_wrong _ => rfl

end DETERM_SEM

/-! ## Integrating an external world in a semantics (`WORLD_SEM`) -/

/-- `Determinism.world_sem`: the states carry the state of the external world
    `w`, and a step is allowed only if its trace is possible in the current
    world.  (A `World` is a state machine, so the world component of a state is
    a state of that machine: every world reachable from `w` is
    `w.withState s` for some `s`.) -/
def worldSem (L : Semantics) (w : World) : Semantics where
  state := L.state × w.σ
  step := fun s t s' => L.step s.1 t s'.1 ∧ PossibleTrace (w.withState s.2) t (w.withState s'.2)
  initial_state := fun s => L.initial_state s.1 ∧ s.2 = w.st
  final_state := fun s r => L.final_state s.1 r
  symbolenv := L.symbolenv

theorem World.withState_inj {w : World} {a b : w.σ} (h : w.withState a = w.withState b) :
    a = b := by
  have := congrArg (fun x : World => (⟨x.σ, x.st⟩ : Sigma fun T : Type => T)) h
  simp only [World.withState] at this
  exact eq_of_heq (Sigma.mk.inj this).2

/-- **`Determinism.world_sem_deterministic`**: if `L` is determinate, the
    world-aware semantics is deterministic. -/
theorem world_sem_deterministic {L : Semantics} (D : Determinate L) (w : World) :
    SemDeterministic (worldSem L w) where
  det_step := by
    rintro ⟨s0, w0⟩ t1 ⟨s1, w1⟩ t2 ⟨s2, w2⟩ ⟨h1, p1⟩ ⟨h2, p2⟩
    obtain ⟨hm, he⟩ := D.sd_determ _ _ _ _ _ h1 h2
    obtain ⟨rfl, hw⟩ := match_possible_traces hm p1 p2
    obtain rfl := he rfl
    obtain rfl := World.withState_inj hw
    exact ⟨rfl, rfl⟩
  det_initial_state := by
    rintro ⟨s1, w1⟩ ⟨s2, w2⟩ ⟨h1, h1w⟩ ⟨h2, h2w⟩
    simp only at h1w h2w
    subst h1w h2w
    have := D.sd_initial_determ _ _ h1 h2
    simp only at this
    subst this
    rfl
  det_final_state := fun _ _ _ h1 h2 => D.sd_final_determ _ _ _ h1 h2
  det_final_nostep := fun _ _ h _ _ hs => D.sd_final_nostep _ _ h _ _ hs.1

end Smallstep
end CC
