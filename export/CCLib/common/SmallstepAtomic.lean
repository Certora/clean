/-
  Strong receptiveness and the "atomic" transformation of a semantics
  (`common/Smallstep.v`, sections on `well_behaved_traces`, `ATOMIC` and
  `strongly_receptive`), plus `output_event`/`output_trace` from
  `common/Events.v`.

  A step of a strongly receptive semantics may emit several events, but only
  its first event may be an input (a volatile load or a system call); the rest
  must be outputs.  `atomic L` splits such multi-event steps into
  one-event steps, buffering the remaining events in the state, and
  `atomic_receptive` shows the result is receptive.
-/
import CCLib.common.Smallstep

namespace CC

/-- `Events.output_event`: events the outside world cannot influence. -/
def OutputEvent : Event → Prop
  | .Event_syscall _ _ _ => False
  | .Event_vload _ _ _ _ => False
  | .Event_vstore _ _ _ _ => True
  | .Event_annot _ _ => True

/-- `Events.output_trace` -/
def OutputTrace : Trace → Prop
  | [] => True
  | ev :: t => OutputEvent ev ∧ OutputTrace t

namespace Smallstep

/-- `Smallstep.well_behaved_traces`: after the first event of a step, every
    further event is an output. -/
def WellBehavedTraces (L : Semantics) : Prop :=
  ∀ s t s', L.step s t s' →
    match t with
    | [] => True
    | _ :: t' => OutputTrace t'

/-- A semantics emitting at most one event per step has well-behaved traces. -/
theorem SingleEvents.wellBehaved {L : Semantics} (h : SingleEvents L) : WellBehavedTraces L := by
  intro s t s' hs
  have := h s t s' hs
  match t, this with
  | [], _ => trivial
  | [_], _ => trivial

/-- `Smallstep.atomic_step` -/
inductive AtomicStep (L : Semantics) : Trace × L.state → Trace → Trace × L.state → Prop where
  | silent (s s') : L.step s E0 s' → AtomicStep L (E0, s) E0 (E0, s')
  | start (s ev t s') : L.step s (ev :: t) s' → AtomicStep L (E0, s) [ev] (t, s')
  | cont (ev t s) : OutputTrace (ev :: t) → AtomicStep L (ev :: t, s) [ev] (t, s)

/-- `Smallstep.atomic`: the semantics `L` with multi-event steps split into
    single-event steps; the events still to be emitted are kept in the first
    component of the state. -/
def atomic (L : Semantics) : Semantics where
  state := Trace × L.state
  step := AtomicStep L
  initial_state := fun s => L.initial_state s.2 ∧ s.1 = E0
  final_state := fun s r => L.final_state s.2 r ∧ s.1 = E0
  symbolenv := L.symbolenv

/-- `Smallstep.strongly_receptive` -/
structure StronglyReceptive (L : Semantics) : Prop where
  ssr_receptive : ∀ s ev1 t1 s1 ev2,
    L.step s (ev1 :: t1) s1 → MatchTraces L.symbolenv [ev1] [ev2] →
    ∃ s2 t2, L.step s (ev2 :: t2) s2
  ssr_well_behaved : WellBehavedTraces L

private theorem matchTraces_E0' {ge : Senv} {t : Trace} (h : MatchTraces ge E0 t) : t = E0 := by
  generalize he : E0 = t1 at h
  cases h <;> simp_all [E0]

private theorem matchTraces_single_left {ge : Senv} {ev t2} (h : MatchTraces ge [ev] t2) :
    ∃ ev2, t2 = [ev2] := by
  cases h <;> first | exact ⟨_, rfl⟩ | simp_all [E0]

private theorem matchTraces_output {ge : Senv} {ev t2} (ho : OutputEvent ev)
    (h : MatchTraces ge [ev] t2) : t2 = [ev] := by
  generalize he : [ev] = t1 at h
  cases h with
  | nil => simp [E0] at he
  | syscall => simp only [List.cons.injEq, and_true] at he; subst he; exact absurd ho id
  | vload => simp only [List.cons.injEq, and_true] at he; subst he; exact absurd ho id
  | vstore => simp only [List.cons.injEq, and_true] at he; subst he; rfl
  | annot => simp only [List.cons.injEq, and_true] at he; subst he; rfl

/-- `Smallstep.atomic_receptive`: the atomic version of a strongly receptive
    semantics is receptive. -/
theorem atomic_receptive {L : Semantics} (h : StronglyReceptive L) : Receptive (atomic L) where
  sr_receptive := by
    intro s t1 s1 t2 hs hm
    cases hs with
    | silent s s' hst =>
      rw [matchTraces_E0' hm]
      exact ⟨_, .silent s s' hst⟩
    | start s ev t s' hst =>
      obtain ⟨ev2, rfl⟩ := matchTraces_single_left hm
      obtain ⟨s2, t2, h2⟩ := h.ssr_receptive s ev t s' ev2 hst hm
      exact ⟨_, .start s ev2 t2 s2 h2⟩
    | cont ev t s ho =>
      rw [matchTraces_output ho.1 hm]
      exact ⟨_, .cont ev t s ho⟩
  sr_traces := by
    intro s t s' hs
    cases hs <;> simp [E0]

end Smallstep
end CC
