/-
  Program behaviors for the "atomic" construction — the section `ATOMIC` of
  `common/Behaviors.v`: `atomic_finish`, `step_atomic_plus`,
  `star_atomic_star`, `atomic_star_star_gen`, `atomic_star_star`,
  `atomic_forever_silent_forever_silent`, `star_atomic_output_trace`,
  `atomic_forever_reactive_forever_reactive` and **`atomic_behaviors`**: a
  semantics with well-behaved traces and its atomic version have the same
  behaviors.
-/
import CCLib.common.Behaviors
import CCLib.common.SmallstepAtomic
import CCLib.common.BackwardSimulation

namespace CC
namespace Smallstep

open ProgramBehavior

section ATOMIC
variable {L : Semantics}

/-- `Behaviors.atomic_finish` -/
theorem atomic_finish (s : L.state) :
    ∀ (t : Trace), OutputTrace t → Star (atomic L).step (t, s) t (E0, s)
  | [], _ => .refl _
  | ev :: t, ho => star_left (AtomicStep.cont ev t s ho) (atomic_finish s t ho.2) rfl

/-- `Behaviors.step_atomic_plus` -/
theorem step_atomic_plus (Lwb : WellBehavedTraces L) {s1 t s2} (h : L.step s1 t s2) :
    Plus (atomic L).step (E0, s1) t (E0, s2) := by
  cases t with
  | nil => exact plus_one (AtomicStep.silent _ _ h)
  | cons ev t =>
    have ho : OutputTrace t := Lwb _ _ _ h
    exact plus_left (AtomicStep.start _ _ _ _ h) (atomic_finish s2 t ho) rfl

/-- `Behaviors.star_atomic_star` -/
theorem star_atomic_star (Lwb : WellBehavedTraces L) {s1 t s2} (h : Star L.step s1 t s2) :
    Star (atomic L).step (E0, s1) t (E0, s2) := by
  induction h with
  | refl => exact .refl _
  | step hr _ heq ih => exact star_trans (plus_star (step_atomic_plus Lwb hr)) ih heq

/-- `Behaviors.atomic_star_star_gen` -/
theorem atomic_star_star_gen {ts1 t ts2} (h : Star (atomic L).step ts1 t ts2) :
    ∃ t', Star L.step ts1.2 t' ts2.2 ∧ Eapp ts1.1 t' = Eapp t ts2.1 := by
  induction h with
  | refl => exact ⟨E0, .refl _, by simp [Eapp, E0]⟩
  | step hr _ heq ih =>
    obtain ⟨t', A, B⟩ := ih
    subst heq
    cases hr with
    | silent s s' h =>
      exact ⟨t', star_left h A rfl, by simpa [Eapp, E0] using B⟩
    | start s ev t0 s' h =>
      refine ⟨ev :: Eapp t0 t', star_left h A rfl, ?_⟩
      simp only [Eapp, E0, List.nil_append, List.cons_append] at B ⊢
      rw [B]
    | cont ev t0 s _ =>
      refine ⟨t', A, ?_⟩
      simp only [Eapp, List.cons_append, List.append_assoc] at B ⊢
      rw [B, List.nil_append]

/-- `Behaviors.atomic_star_star` -/
theorem atomic_star_star {s1 t s2} (h : Star (atomic L).step (E0, s1) t (E0, s2)) :
    Star L.step s1 t s2 := by
  obtain ⟨t', A, B⟩ := atomic_star_star_gen h
  simp only [Eapp, E0, List.nil_append, List.append_nil] at B
  subst B; exact A

/-- Silent steps of `atomic L` are silent steps of `L`. -/
theorem atomic_step_E0 {ts1 ts2} (h : (atomic L).step ts1 E0 ts2) :
    ts1.1 = E0 ∧ ts2.1 = E0 ∧ L.step ts1.2 E0 ts2.2 := by
  generalize he : (E0 : Trace) = t at h
  cases h with
  | silent s s' h => exact ⟨rfl, rfl, h⟩
  | start => simp [E0] at he
  | cont => simp [E0] at he

/-- `Behaviors.atomic_forever_silent_forever_silent` -/
theorem atomic_forever_silent_forever_silent {s} (h : ForeverSilent (atomic L).step s) :
    ForeverSilent L.step s.2 := by
  obtain ⟨f, hf0, hf⟩ := h
  exact ⟨fun n => (f n).2, congrArg Prod.snd hf0, fun n => (atomic_step_E0 (hf n)).2.2⟩

/-- `Behaviors.star_atomic_output_trace`, generalised. -/
theorem star_atomic_output_trace_gen (Lwb : WellBehavedTraces L) {ts1 t ts2}
    (h : Star (atomic L).step ts1 t ts2) (ho : OutputTrace ts1.1) : OutputTrace ts2.1 := by
  induction h with
  | refl => exact ho
  | step hr _ _ ih =>
    cases hr with
    | silent => exact ih trivial
    | start s ev t s' h => exact ih (Lwb _ _ _ h)
    | cont ev t s ho' => exact ih ho'.2

/-- `Behaviors.star_atomic_output_trace` -/
theorem star_atomic_output_trace (Lwb : WellBehavedTraces L) {s t t' s'}
    (h : Star (atomic L).step (E0, s) t (t', s')) : OutputTrace t' :=
  star_atomic_output_trace_gen Lwb h trivial

/-- Emptying the buffer of a reactive execution of `atomic L`. -/
theorem atomic_forever_reactive_flush :
    ∀ (t : Trace) {s T}, ForeverReactive (atomic L).step (t, s) T →
      ∃ T', ForeverReactive (atomic L).step (E0, s) T' ∧ T = Eappinf t T'
  | [], _, T, h => ⟨T, h, (Eappinf_E0 T).symm⟩
  | ev :: t, s, T, h => by
    obtain ⟨s3, tt, T3, A, hne, B, rfl⟩ := h.inv
    cases A with
    | refl => exact absurd rfl hne
    | step hr hs heq =>
      cases hr with
      | cont _ _ _ ho =>
        subst heq
        obtain ⟨T'', C, D⟩ := atomic_forever_reactive_flush t (star_forever_reactive hs B)
        refine ⟨T'', C, ?_⟩
        show Eappinf (Eapp [ev] _) T3 = Eappinf (Eapp [ev] t) T''
        rw [Eappinf_assoc, Eappinf_assoc]
        exact congrArg _ D

/-- `Behaviors.atomic_forever_reactive_forever_reactive` -/
theorem atomic_forever_reactive_forever_reactive (Lwb : WellBehavedTraces L) {s T}
    (h : ForeverReactive (atomic L).step (E0, s) T) : ForeverReactive L.step s T := by
  refine ForeverReactive.coind (fun s T => ForeverReactive (atomic L).step (E0, s) T) ?_ h
  intro s T hq
  obtain ⟨⟨t2, s2⟩, t, T', A, hne, B, rfl⟩ := hq.inv
  obtain ⟨T'', C, rfl⟩ := atomic_forever_reactive_flush t2 B
  have ho := star_atomic_output_trace Lwb A
  have D : Star (atomic L).step (E0, s) (Eapp t t2) (E0, s2) :=
    star_trans A (atomic_finish s2 t2 ho) rfl
  refine ⟨s2, Eapp t t2, T'', atomic_star_star D, ?_, C, (Eappinf_assoc _ _ _).symm⟩
  intro he
  apply hne
  simp only [Eapp, E0, List.append_eq_nil_iff] at he
  exact he.1

/-- Forward direction of reactive divergence. -/
theorem forever_reactive_atomic (Lwb : WellBehavedTraces L) {s T}
    (h : ForeverReactive L.step s T) : ForeverReactive (atomic L).step (E0, s) T := by
  refine ForeverReactive.coind
    (fun ts T => ts.1 = E0 ∧ ForeverReactive L.step ts.2 T) ?_ ⟨rfl, h⟩
  rintro ⟨t0, s⟩ T ⟨ht0, hq⟩
  simp only at ht0 hq
  subst ht0
  obtain ⟨s2, t, T', A, hne, B, rfl⟩ := hq.inv
  exact ⟨(E0, s2), t, T', star_atomic_star Lwb A, hne, ⟨rfl, B⟩, rfl⟩

/-- `Behaviors.atomic_behaviors`: `L` and `atomic L` have the same behaviors,
    when `L` has well-behaved traces. -/
theorem atomic_behaviors (Lwb : WellBehavedTraces L) (beh : ProgramBehavior) :
    ProgramBehaves L beh ↔ ProgramBehaves (atomic L) beh := by
  constructor
  · intro H
    cases H with
    | @runs s _ hi hb =>
      refine .runs (s := ((E0 : Trace), s)) ⟨hi, rfl⟩ ?_
      cases hb with
      | terminates hst hf => exact .terminates (star_atomic_star Lwb hst) ⟨hf, rfl⟩
      | diverges hst hfs =>
        refine .diverges (star_atomic_star Lwb hst) ?_
        obtain ⟨f, hf0, hf⟩ := hfs
        exact ⟨fun n => (E0, f n), by simp only [hf0], fun n => AtomicStep.silent _ _ (hf n)⟩
      | reacts hfr => exact .reacts (forever_reactive_atomic Lwb hfr)
      | goes_wrong hst hn hnf =>
        refine .goes_wrong (star_atomic_star Lwb hst) ?_ ?_
        · intro t s'' hs
          generalize he : ((E0 : Trace), _) = ts at hs
          cases hs with
          | silent _ _ h => cases he; exact hn _ _ h
          | start _ _ _ _ h => cases he; exact hn _ _ h
          | cont => simp [E0] at he
        · intro r ⟨hf, _⟩; exact hnf r hf
    | goes_initially_wrong hn =>
      exact .goes_initially_wrong (fun s ⟨h, _⟩ => hn s.2 h)
  · intro H
    cases H with
    | @runs ts _ hi hb =>
      obtain ⟨t, s⟩ := ts
      obtain ⟨hi, ht⟩ := hi
      simp only at hi ht
      subst ht
      refine .runs hi ?_
      cases hb with
      | @terminates _ ts' _ hst hf =>
        obtain ⟨t', s'⟩ := ts'
        obtain ⟨hf, ht'⟩ := hf
        simp only at hf ht'
        subst ht'
        exact .terminates (atomic_star_star hst) hf
      | @diverges _ ts' hst hfs =>
        obtain ⟨t', s'⟩ := ts'
        obtain ⟨_, A, _⟩ := hfs.inv
        have ht' := (atomic_step_E0 A).1
        simp only at ht'
        subst ht'
        exact .diverges (atomic_star_star hst) (atomic_forever_silent_forever_silent hfs)
      | reacts hfr => exact .reacts (atomic_forever_reactive_forever_reactive Lwb hfr)
      | @goes_wrong _ ts' hst hn hnf =>
        obtain ⟨t', s'⟩ := ts'
        have ht' : t' = E0 := by
          cases t' with
          | nil => rfl
          | cons ev t'' =>
            exact (hn _ _ (AtomicStep.cont ev t'' s' (star_atomic_output_trace Lwb hst))).elim
        subst ht'
        refine .goes_wrong (atomic_star_star hst) ?_ ?_
        · intro t s'' hs
          cases t with
          | nil => exact hn _ _ (AtomicStep.silent _ _ hs)
          | cons ev t => exact hn _ _ (AtomicStep.start _ _ _ _ hs)
        · intro r hf; exact hnf r ⟨hf, rfl⟩
    | goes_initially_wrong hn =>
      exact .goes_initially_wrong (fun s h => hn (E0, s) ⟨h, rfl⟩)

end ATOMIC

end Smallstep
end CC
