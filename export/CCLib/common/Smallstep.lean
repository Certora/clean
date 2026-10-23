/-
  Generic transition systems — port of the core of `common/Smallstep.v`.

  `Clight.lean` has `Star`/`Plus` specialised to Clight states.  This file
  gives the generic versions (namespace `CC.Smallstep`, over any state type
  `σ` and step relation `R : σ → Trace → σ → Prop`), the `semantics` record,
  `nostep`, `starN`, divergence (`forever_silent`, `forever_reactive`), infinite
  traces, and `safe`.

  Rocq's genv argument is folded into the step relation (`step L (globalenv L)`
  becomes `L.step`).

  ## Infinite traces and coinduction

  Rocq's `traceinf` and the `forever_*` predicates are `CoInductive`.  Here an
  infinite trace is a stream `Nat → Event`, and the coinductive predicates are
  stated through an explicit infinite sequence of states, which is the usual
  equivalent formulation:

  * `ForeverSilent R s` : there are states `s = f 0, f 1, …` with
    `R (f n) E0 (f (n+1))` for all `n` (Rocq: `forever_silent`).
  * `ForeverReactive R s T` : there are states `s = f 0, f 1, …` and non-empty
    traces `ts n` with `Star R (f n) (ts n) (f (n+1))`, and `T` is the
    concatenation `ts 0 ++ ts 1 ++ …` (Rocq: `forever_reactive`).

  The Rocq introduction rules are then theorems
  (`ForeverSilent.intro`, `ForeverReactive.intro`), as are the inversion
  principles (`ForeverSilent.inv`, `ForeverReactive.inv`).
-/
import CCLib.cfrontend.Clight

namespace CC
namespace Smallstep

variable {σ : Type} (R : σ → Trace → σ → Prop)

/-! ## Finite runs -/

/-- `Smallstep.nostep`: `s` cannot take a step. -/
def Nostep (s : σ) : Prop := ∀ t s', ¬ R s t s'

/-- `Smallstep.star` -/
inductive Star : σ → Trace → σ → Prop where
  | refl (s : σ) : Star s E0 s
  | step {s1 t1 s2 t2 s3 t} : R s1 t1 s2 → Star s2 t2 s3 → t = Eapp t1 t2 → Star s1 t s3

/-- `Smallstep.plus` -/
inductive Plus : σ → Trace → σ → Prop where
  | intro {s1 t1 s2 t2 s3 t} : R s1 t1 s2 → Star R s2 t2 s3 → t = Eapp t1 t2 → Plus s1 t s3

/-- `Smallstep.starN`: runs of exactly `n` steps. -/
inductive StarN : Nat → σ → Trace → σ → Prop where
  | refl (s : σ) : StarN 0 s E0 s
  | step {n s1 t1 s2 t2 s3 t} :
      R s1 t1 s2 → StarN n s2 t2 s3 → t = Eapp t1 t2 → StarN (n + 1) s1 t s3

variable {R}

theorem E0_left (t : Trace) : Eapp E0 t = t := rfl
theorem E0_right (t : Trace) : Eapp t E0 = t := List.append_nil t
theorem Eapp_assoc (t1 t2 t3 : Trace) : Eapp (Eapp t1 t2) t3 = Eapp t1 (Eapp t2 t3) :=
  List.append_assoc t1 t2 t3

theorem star_one {s1 t s2} (h : R s1 t s2) : Star R s1 t s2 :=
  .step h (.refl _) (E0_right t).symm

theorem star_two {s1 t1 s2 t2 s3 t} (h1 : R s1 t1 s2) (h2 : R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Star R s1 t s3 :=
  .step h1 (star_one h2) ht

theorem star_trans {s1 t1 s2 t2 s3 t} (h1 : Star R s1 t1 s2) (h2 : Star R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Star R s1 t s3 := by
  subst ht
  induction h1 with
  | refl => exact h2
  | step hr _ heq ih => subst heq; exact .step hr (ih h2) (Eapp_assoc _ _ _)

theorem star_left {s1 t1 s2 t2 s3 t} (h1 : R s1 t1 s2) (h2 : Star R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Star R s1 t s3 := .step h1 h2 ht

theorem star_right {s1 t1 s2 t2 s3 t} (h1 : Star R s1 t1 s2) (h2 : R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Star R s1 t s3 := star_trans h1 (star_one h2) ht

theorem plus_one {s1 t s2} (h : R s1 t s2) : Plus R s1 t s2 :=
  .intro h (.refl _) (E0_right t).symm

theorem plus_star {s1 t s2} (h : Plus R s1 t s2) : Star R s1 t s2 := by
  cases h with | intro hr hs ht => exact .step hr hs ht

theorem plus_left {s1 t1 s2 t2 s3 t} (h1 : R s1 t1 s2) (h2 : Star R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 := .intro h1 h2 ht

theorem plus_right {s1 t1 s2 t2 s3 t} (h1 : Star R s1 t1 s2) (h2 : R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 := by
  subst ht
  cases h1 with
  | refl => exact plus_one h2
  | step hr hs heq => subst heq; exact .intro hr (star_right hs h2 rfl) (Eapp_assoc _ _ _)

theorem plus_star_trans {s1 t1 s2 t2 s3 t} (h1 : Plus R s1 t1 s2) (h2 : Star R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 := by
  cases h1 with
  | intro hr hs heq =>
    subst ht heq; exact .intro hr (star_trans hs h2 rfl) (Eapp_assoc _ _ _)

theorem star_plus_trans {s1 t1 s2 t2 s3 t} (h1 : Star R s1 t1 s2) (h2 : Plus R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 := by
  cases h1 with
  | refl => subst ht; exact h2
  | step hr hs heq =>
    subst ht heq; exact .intro hr (star_trans hs (plus_star h2) rfl) (Eapp_assoc _ _ _)

theorem plus_trans {s1 t1 s2 t2 s3 t} (h1 : Plus R s1 t1 s2) (h2 : Plus R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 := plus_star_trans h1 (plus_star h2) ht

theorem plus_inv {s1 t s2} (h : Plus R s1 t s2) :
    R s1 t s2 ∨ ∃ s' t1 t2, R s1 t1 s' ∧ Plus R s' t2 s2 ∧ t = Eapp t1 t2 := by
  cases h with
  | intro hr hs heq =>
    cases hs with
    | refl => left; rw [heq, E0_right]; exact hr
    | step hr' hs' heq' => right; exact ⟨_, _, _, hr, .intro hr' hs' heq', heq⟩

theorem star_inv {s1 t s2} (h : Star R s1 t s2) : (s2 = s1 ∧ t = E0) ∨ Plus R s1 t s2 := by
  cases h with
  | refl => left; exact ⟨rfl, rfl⟩
  | step hr hs heq => right; exact .intro hr hs heq

theorem star_E0_ind (P : σ → σ → Prop) (hrefl : ∀ s, P s s)
    (hstep : ∀ s1 s2 s3, R s1 E0 s2 → P s2 s3 → P s1 s3) :
    ∀ {s1 s2}, Star R s1 E0 s2 → P s1 s2 := by
  intro s1 s2 h
  generalize hE : (E0 : Trace) = t at h
  induction h with
  | refl => exact hrefl _
  | step hr _ heq ih =>
    subst heq
    have h12 : _ ∧ _ := List.append_eq_nil_iff.mp hE.symm
    rw [h12.1] at hr
    exact hstep _ _ _ hr (ih h12.2.symm)

theorem starN_star {n s1 t s2} (h : StarN R n s1 t s2) : Star R s1 t s2 := by
  induction h with
  | refl => exact .refl _
  | step hr _ heq ih => exact .step hr ih heq

theorem star_starN {s1 t s2} (h : Star R s1 t s2) : ∃ n, StarN R n s1 t s2 := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | step hr _ heq ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step hr hn heq⟩

/-! ## Infinite traces (`Events.traceinf`) -/

/-- `Events.traceinf`, as a stream of events. -/
def Traceinf : Type := Nat → Event

/-- `Events.Eappinf t T` (Rocq notation `t *** T`): prepend a finite trace. -/
def Eappinf (t : Trace) (T : Traceinf) : Traceinf :=
  fun n => if h : n < t.length then t[n] else T (n - t.length)

theorem Eappinf_E0 (T : Traceinf) : Eappinf E0 T = T := by
  funext n; simp [Eappinf, E0]

theorem Eappinf_assoc (t1 t2 : Trace) (T : Traceinf) :
    Eappinf (Eapp t1 t2) T = Eappinf t1 (Eappinf t2 T) := by
  funext n
  simp only [Eappinf, Eapp, List.length_append]
  by_cases h1 : n < t1.length
  · rw [dif_pos (by omega), dif_pos h1, List.getElem_append_left h1]
  · rw [dif_neg h1]
    by_cases h2 : n < t1.length + t2.length
    · rw [dif_pos h2, dif_pos (by omega), List.getElem_append_right (by omega)]
    · rw [dif_neg h2, dif_neg (by omega)]; congr 1; omega

/-- `t` is a prefix of the infinite trace `T`. -/
def IsPrefix (t : Trace) (T : Traceinf) : Prop := ∀ i (h : i < t.length), T i = t[i]

theorem isPrefix_Eappinf (t : Trace) (T : Traceinf) : IsPrefix t (Eappinf t T) := by
  intro i h; simp [Eappinf, h]

/-- The concatenation `ts 0 ++ … ++ ts (n-1)`. -/
def prefixTrace (ts : Nat → Trace) : Nat → Trace
  | 0 => E0
  | n + 1 => Eapp (prefixTrace ts n) (ts n)

theorem prefixTrace_length_ge (ts : Nat → Trace) (hne : ∀ n, ts n ≠ E0) (n : Nat) :
    n ≤ (prefixTrace ts n).length := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [prefixTrace, Eapp, List.length_append]
    have : (ts n).length ≠ 0 := fun h => hne n (List.eq_nil_of_length_eq_zero h)
    omega

theorem prefixTrace_shift (ts : Nat → Trace) (n : Nat) :
    prefixTrace ts (n + 1) = Eapp (ts 0) (prefixTrace (fun k => ts (k + 1)) n) := by
  induction n with
  | zero => simp [prefixTrace, Eapp, E0]
  | succ n ih =>
    rw [prefixTrace, ih]; simp only [prefixTrace, Eapp, List.append_assoc]

/-! ## Divergence -/

/-- Prepend an element to a sequence. -/
def consSeq {α : Type} (a : α) (f : Nat → α) : Nat → α
  | 0 => a
  | n + 1 => f n

@[simp] theorem consSeq_zero {α : Type} (a : α) (f : Nat → α) : consSeq a f 0 = a := rfl
@[simp] theorem consSeq_succ {α : Type} (a : α) (f : Nat → α) (n : Nat) :
    consSeq a f (n + 1) = f n := rfl

/-- `Smallstep.forever_silent`: an infinite sequence of silent steps from `s`. -/
def ForeverSilent (R : σ → Trace → σ → Prop) (s : σ) : Prop :=
  ∃ f : Nat → σ, f 0 = s ∧ ∀ n, R (f n) E0 (f (n + 1))

/-- `Smallstep.forever_reactive`: infinitely many non-silent finite runs from
    `s`, whose traces concatenate to `T`. -/
def ForeverReactive (R : σ → Trace → σ → Prop) (s : σ) (T : Traceinf) : Prop :=
  ∃ (f : Nat → σ) (ts : Nat → Trace), f 0 = s ∧
    (∀ n, Star R (f n) (ts n) (f (n + 1)) ∧ ts n ≠ E0) ∧
    ∀ n, IsPrefix (prefixTrace ts n) T

/-- The introduction rule of Rocq's `forever_silent`. -/
theorem ForeverSilent.intro {s1 s2} (h1 : R s1 E0 s2) (h2 : ForeverSilent R s2) :
    ForeverSilent R s1 := by
  obtain ⟨f, hf0, hf⟩ := h2
  refine ⟨consSeq s1 f, rfl, ?_⟩
  intro n; cases n with
  | zero => rw [← hf0] at h1; exact h1
  | succ n => exact hf n

/-- Inversion for `forever_silent`. -/
theorem ForeverSilent.inv {s1} (h : ForeverSilent R s1) :
    ∃ s2, R s1 E0 s2 ∧ ForeverSilent R s2 := by
  obtain ⟨f, hf0, hf⟩ := h
  exact ⟨f 1, hf0 ▸ hf 0, fun n => f (n + 1), rfl, fun n => hf (n + 1)⟩

/-- The introduction rule of Rocq's `forever_reactive`. -/
theorem ForeverReactive.intro {s1 s2 t T} (h1 : Star R s1 t s2) (hne : t ≠ E0)
    (h2 : ForeverReactive R s2 T) : ForeverReactive R s1 (Eappinf t T) := by
  obtain ⟨f, ts, hf0, hf, hT⟩ := h2
  refine ⟨consSeq s1 f, consSeq t ts, rfl, ?_, ?_⟩
  · intro n; cases n with
    | zero => rw [← hf0] at h1; exact ⟨h1, hne⟩
    | succ n => exact hf n
  · intro n; cases n with
    | zero => intro i h; simp [prefixTrace, E0] at h
    | succ n =>
      rw [prefixTrace_shift]
      simp only [consSeq_zero, consSeq_succ]
      intro i hi
      simp only [Eapp, List.length_append] at hi
      simp only [Eappinf, Eapp]
      by_cases h : i < t.length
      · rw [dif_pos h, List.getElem_append_left h]
      · rw [dif_neg h, List.getElem_append_right (by omega)]
        exact hT n _ _

/-- Inversion for `forever_reactive`. -/
theorem ForeverReactive.inv {s1 T} (h : ForeverReactive R s1 T) :
    ∃ s2 t T', Star R s1 t s2 ∧ t ≠ E0 ∧ ForeverReactive R s2 T' ∧ T = Eappinf t T' := by
  obtain ⟨f, ts, hf0, hf, hT⟩ := h
  refine ⟨f 1, ts 0, fun i => T (i + (ts 0).length), hf0 ▸ (hf 0).1, (hf 0).2,
    ⟨fun n => f (n + 1), fun n => ts (n + 1), rfl, fun n => hf (n + 1), ?_⟩, ?_⟩
  · intro n i hi
    have := hT (n + 1) (i + (ts 0).length)
    rw [prefixTrace_shift] at this
    simp only [Eapp, List.length_append] at this
    show T (i + (ts 0).length) = _
    rw [this (by omega), List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel]
  · funext i
    simp only [Eappinf]
    split
    · rename_i h
      have := hT 1 i
      simp only [prefixTrace, Eapp, E0, List.nil_append] at this
      exact this h
    · congr 1; omega

/-- `Smallstep.star_forever_reactive` -/
theorem star_forever_reactive {s1 t s2 T} (h1 : Star R s1 t s2) (h2 : ForeverReactive R s2 T) :
    ForeverReactive R s1 (Eappinf t T) := by
  by_cases ht : t = E0
  · subst ht; rw [Eappinf_E0]
    obtain ⟨s3, t3, T3, h3, hne, h4, rfl⟩ := h2.inv
    exact ForeverReactive.intro (star_trans h1 h3 rfl) hne h4
  · exact ForeverReactive.intro h1 ht h2

/-! ## The `semantics` record -/

/-- `Smallstep.semantics`: a transition semantics with initial and final
    states.  (Rocq also carries `genvtype`/`globalenv`, here folded into
    `step`, and `symbolenv`.) -/
structure Semantics where
  state : Type
  step : state → Trace → state → Prop
  initial_state : state → Prop
  final_state : state → Integers.Int → Prop
  symbolenv : Senv

/-- `Smallstep.safe`: every state reachable by *silent* steps is final or can
    step (exactly Rocq's definition). -/
def Safe (L : Semantics) (s : L.state) : Prop :=
  ∀ s', Star L.step s E0 s' →
    (∃ r, L.final_state s' r) ∨ (∃ t' s'', L.step s' t' s'')

/-- `Smallstep.star_safe` -/
theorem star_safe {L : Semantics} {s s'} (h : Star L.step s E0 s') (hs : Safe L s) :
    Safe L s' := fun s'' h' => hs s'' (star_trans h h' rfl)

/-- Safety along every run, whatever its trace (stronger than `Safe`). -/
def SafeAlways (L : Semantics) (s : L.state) : Prop :=
  ∀ s' t, Star L.step s t s' →
    (∃ r, L.final_state s' r) ∨ (∃ t' s'', L.step s' t' s'')

theorem SafeAlways.safe {L : Semantics} {s} (h : SafeAlways L s) : Safe L s :=
  fun s' hs => h s' E0 hs

theorem star_safeAlways {L : Semantics} {s s' t} (h : Star L.step s t s')
    (hs : SafeAlways L s) : SafeAlways L s' :=
  fun s'' _ h' => hs s'' _ (star_trans h h' rfl)

/-! ## Receptiveness and determinacy -/

/-- `Smallstep.single_events`: every step emits at most one event. -/
def SingleEvents (L : Semantics) : Prop :=
  ∀ s t s', L.step s t s' → t.length ≤ 1

/-- `Smallstep.receptive` -/
structure Receptive (L : Semantics) : Prop where
  sr_receptive : ∀ s t1 s1 t2, L.step s t1 s1 → MatchTraces L.symbolenv t1 t2 →
    ∃ s2, L.step s t2 s2
  sr_traces : SingleEvents L

/-- `Smallstep.determinate`: the step relation is deterministic up to
    `match_traces`, emits at most one event per step, and initial/final states
    are unique. -/
structure Determinate (L : Semantics) : Prop where
  sd_determ : ∀ s t1 s1 t2 s2, L.step s t1 s1 → L.step s t2 s2 →
    MatchTraces L.symbolenv t1 t2 ∧ (t1 = t2 → s1 = s2)
  sd_traces : SingleEvents L
  sd_initial_determ : ∀ s1 s2, L.initial_state s1 → L.initial_state s2 → s1 = s2
  sd_final_nostep : ∀ s r, L.final_state s r → Nostep L.step s
  sd_final_determ : ∀ s r1 r2, L.final_state s r1 → L.final_state s r2 → r1 = r2

end Smallstep
end CC
