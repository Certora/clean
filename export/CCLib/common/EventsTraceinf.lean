/-
  Infinite traces — port of the `traceinf` part of `common/Events.v`
  (the type itself, `Eappinf` and `Eappinf_assoc` are in
  `CCLib.common.Smallstep`).

  An infinite trace is a stream `Nat → Event`, so:
  * Rocq's `Econsinf e T` is `Eappinf [e] T`;
  * the bisimilarity `traceinf_sim` is equality (`traceinfSim_iff_eq`), and
    `traceinf_sim'` collapses to it as well;
  * `traceinf'` (an infinite sequence of non-empty finite traces) is a
    sequence `ts : Nat → Trace` with `∀ n, ts n ≠ E0`, and
    `traceinf_of_traceinf'` is `traceinfOfSeq`, the stream whose prefixes are
    the concatenations `ts 0 ++ … ++ ts (n-1)` (`traceinfOfSeq_isPrefix`).
    Rocq's `traceinf_traceinf'_app` is `traceinfOfSeq_cons`.
-/
import CCLib.common.Smallstep

namespace CC
namespace Smallstep

/-! ## Basic operations -/

/-- `Events.Econsinf` -/
def Econsinf (e : Event) (T : Traceinf) : Traceinf := Eappinf [e] T

@[simp] theorem Econsinf_zero (e : Event) (T : Traceinf) : Econsinf e T 0 = e := rfl
@[simp] theorem Econsinf_succ (e : Event) (T : Traceinf) (n : Nat) :
    Econsinf e T (n + 1) = T n := rfl

theorem Econsinf_inj {e1 e2 : Event} {T1 T2 : Traceinf} (h : Econsinf e1 T1 = Econsinf e2 T2) :
    e1 = e2 ∧ T1 = T2 :=
  ⟨congrFun h 0, funext fun n => congrFun h (n + 1)⟩

/-- Every infinite trace is an `Econsinf` (Rocq's `unroll_traceinf`). -/
theorem traceinf_eta (T : Traceinf) : T = Econsinf (T 0) (fun n => T (n + 1)) := by
  funext n; cases n <;> rfl

/-- `Events.Eappinf` on a cons (its defining equation in Rocq). -/
theorem Eappinf_cons (e : Event) (t : Trace) (T : Traceinf) :
    Eappinf (e :: t) T = Econsinf e (Eappinf t T) := by
  rw [Econsinf, ← Eappinf_assoc]; rfl

/-- `Events.Eapp_E0_inv` -/
theorem Eapp_E0_inv {t1 t2 : Trace} (h : Eapp t1 t2 = E0) : t1 = E0 ∧ t2 = E0 :=
  List.append_eq_nil_iff.mp h

/-! ## Bisimilarity -/

/-- `Events.traceinf_sim`: two infinite traces with the same events.  For
    streams this is equality (`traceinfSim_iff_eq`). -/
def TraceinfSim (T1 T2 : Traceinf) : Prop := ∀ n, T1 n = T2 n

theorem traceinfSim_iff_eq {T1 T2 : Traceinf} : TraceinfSim T1 T2 ↔ T1 = T2 :=
  ⟨funext, fun h _ => h ▸ rfl⟩

/-- `Events.traceinf_sim_refl` -/
theorem traceinfSim_refl (T : Traceinf) : TraceinfSim T T := fun _ => rfl
/-- `Events.traceinf_sim_sym` -/
theorem traceinfSim_sym {T1 T2 : Traceinf} (h : TraceinfSim T1 T2) : TraceinfSim T2 T1 :=
  fun n => (h n).symm
/-- `Events.traceinf_sim_trans` -/
theorem traceinfSim_trans {T1 T2 T3 : Traceinf} (h1 : TraceinfSim T1 T2)
    (h2 : TraceinfSim T2 T3) : TraceinfSim T1 T3 := fun n => (h1 n).trans (h2 n)

/-- The constructor of Rocq's `traceinf_sim`. -/
theorem traceinfSim_cons (e : Event) {T1 T2 : Traceinf} (h : TraceinfSim T1 T2) :
    TraceinfSim (Econsinf e T1) (Econsinf e T2) := by
  intro n; cases n with
  | zero => rfl
  | succ n => exact h n

/-! ## Prefixes -/

/-- `Events.trace_prefix` -/
def TracePrefix (t1 t2 : Trace) : Prop := ∃ t3, t2 = Eapp t1 t3

/-- `Events.traceinf_prefix` -/
def TraceinfPrefix (t1 : Trace) (T2 : Traceinf) : Prop := ∃ T3, T2 = Eappinf t1 T3

/-- `Events.trace_prefix_app` -/
theorem tracePrefix_app {t1 t2 : Trace} (t : Trace) (h : TracePrefix t1 t2) :
    TracePrefix (Eapp t t1) (Eapp t t2) := by
  obtain ⟨t3, rfl⟩ := h
  exact ⟨t3, (Eapp_assoc _ _ _).symm⟩

/-- `Events.traceinf_prefix_app` -/
theorem traceinfPrefix_app {t1 : Trace} {T2 : Traceinf} (t : Trace) (h : TraceinfPrefix t1 T2) :
    TraceinfPrefix (Eapp t t1) (Eappinf t T2) := by
  obtain ⟨T3, rfl⟩ := h
  exact ⟨T3, (Eappinf_assoc _ _ _).symm⟩

/-- `traceinf_prefix` is the index-wise notion `IsPrefix` used by
    `ForeverReactive`. -/
theorem traceinfPrefix_iff_isPrefix {t : Trace} {T : Traceinf} :
    TraceinfPrefix t T ↔ IsPrefix t T := by
  constructor
  · rintro ⟨T3, rfl⟩; exact isPrefix_Eappinf t T3
  · intro h
    refine ⟨fun i => T (i + t.length), funext fun n => ?_⟩
    simp only [Eappinf]
    split
    · exact h n ‹_›
    · congr 1; omega

/-! ## Infinite traces as sequences of non-empty traces (`traceinf'`) -/

theorem prefixTrace_append (ts : Nat → Trace) (m k : Nat) :
    ∃ rest, prefixTrace ts (m + k) = prefixTrace ts m ++ rest := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨rest, h⟩ := ih
    exact ⟨rest ++ ts (m + k), by
      rw [← Nat.add_assoc, prefixTrace, h]; simp [Eapp, List.append_assoc]⟩

/-- `Events.traceinf_of_traceinf'`: the infinite concatenation
    `ts 0 ++ ts 1 ++ …` of a sequence of non-empty traces.  (Event `i` is read
    off the first `i + 1` traces, which have at least `i + 1` events.) -/
def traceinfOfSeq (ts : Nat → Trace) : Traceinf :=
  fun i => (prefixTrace ts (i + 1)).getD i default

/-- Every finite concatenation `ts 0 ++ … ++ ts (n-1)` is a prefix of
    `traceinfOfSeq ts`. -/
theorem traceinfOfSeq_isPrefix (ts : Nat → Trace) (hne : ∀ n, ts n ≠ E0) (n : Nat) :
    IsPrefix (prefixTrace ts n) (traceinfOfSeq ts) := by
  intro i hi
  show (prefixTrace ts (i + 1)).getD i default = _
  have hlen := prefixTrace_length_ge ts hne (i + 1)
  rw [← List.getElem_eq_getD (h := by omega)]
  by_cases hle : i + 1 ≤ n
  · obtain ⟨rest, hr⟩ := prefixTrace_append ts (i + 1) (n - (i + 1))
    rw [Nat.add_sub_cancel' hle] at hr
    simp only [hr]
    rw [List.getElem_append_left (by omega)]
  · obtain ⟨rest, hr⟩ := prefixTrace_append ts n (i + 1 - n)
    rw [Nat.add_sub_cancel' (by omega)] at hr
    simp only [hr]
    rw [List.getElem_append_left hi]

/-- An infinite trace all of whose finite concatenations are prefixes is
    `traceinfOfSeq`. -/
theorem eq_traceinfOfSeq (ts : Nat → Trace) (hne : ∀ n, ts n ≠ E0) {T : Traceinf}
    (hT : ∀ n, IsPrefix (prefixTrace ts n) T) : T = traceinfOfSeq ts := by
  funext i
  have hlen := prefixTrace_length_ge ts hne (i + 1)
  rw [hT (i + 1) i (by omega), traceinfOfSeq_isPrefix ts hne (i + 1) i (by omega)]

/-- `Events.traceinf_traceinf'_app` -/
theorem traceinfOfSeq_cons (t : Trace) (ts : Nat → Trace) (ht : t ≠ E0) (hne : ∀ n, ts n ≠ E0) :
    traceinfOfSeq (consSeq t ts) = Eappinf t (traceinfOfSeq ts) := by
  have hne' : ∀ n, consSeq t ts n ≠ E0 := fun n => by cases n <;> simp [ht, hne]
  refine (eq_traceinfOfSeq _ hne' fun n => ?_).symm
  cases n with
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
      exact traceinfOfSeq_isPrefix ts hne n _ _

end Smallstep
end CC
