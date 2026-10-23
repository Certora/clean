/-
  Port of `lib/Parmov.v`: translation of parallel moves into sequences of
  individual moves (Rideau, Serpette and Leroy, "Tilting at windmills with
  Coq: formal verification of a compilation algorithm for parallel moves").

  Ported, with the same names and statements:
  * registers, moves and their three semantics (`exec_par`, `exec_seq`,
    `exec_seq_rev`), environment updates (`update_s`, `update_o`, …);
  * the non-deterministic rewriting system (`transition`), well-formedness
    of states (`state_wf`) and its preservation, semantic preservation
    (`transitions_preserve_semantics`) and `transitions_correctness`;
  * the deterministic variant (`dtransition`) and `dtransitions_correctness`;
  * the executable compilation function (`parmove_step`, `parmove_aux`,
    `parmove`, `parmove2`) with `parmove_correctness` and
    `parmove2_correctness`;
  * the syntactic properties (`wf_move`, `parmove_wf_moves`,
    `parmove_initial_reg_or_temp`, `parmove_preserves_register_classes`);
  * the extension to partially overlapping registers
    (`parmove2_correctness_with_overlap`).

  Differences from Rocq:
  * the Rocq `Section` variables `reg`, `reg_eq`, `temp`, `val` become
    implicit/instance arguments (`[DecidableEq reg]`) and an explicit
    argument `temp` for the definitions that mention it;
  * `list_norepet` is `List.Nodup`, `list_disjoint` is spelled out, and
    `clos_refl_trans` is the local inductive `Parmov.Star`;
  * `parmove_aux` is defined by well-founded recursion on `measure` via
    `termination_by` instead of `Function`.

  The first part of this file is split off into `CCLib.lib.ParmovSpec`.
-/

import CCLib.lib.ParmovSpec

namespace CC
namespace Parmov
section PARMOV
variable {reg : Type _}

/-! ## Semantics of moves -/

variable {val : Type _}

/-- Environments map registers to values. -/
abbrev env (reg val : Type _) := reg → val

/-- `Parmov.env_ext` -/
theorem env_ext (e1 e2 : env reg val) (h : ∀ r, e1 r = e2 r) : e1 = e2 := funext h

variable [DecidableEq reg]

/-- Assign `v` to `r`, preserving other registers. -/
def update (r : reg) (v : val) (e : env reg val) : env reg val :=
  fun r' => if r' = r then v else e r'

@[simp] theorem update_s (r : reg) (v : val) (e : env reg val) : update r v e r = v := by
  simp [update]

theorem update_o (r : reg) (v : val) (e : env reg val) (r' : reg) (h : r' ≠ r) :
    update r v e r' = e r' := by
  simp [update, h]

theorem update_ident (r : reg) (e : env reg val) : update r (e r) e = e := by
  funext r'; unfold update; split <;> simp_all

theorem update_commut (r1 : reg) (v1 : val) (r2 : reg) (v2 : val) (e : env reg val)
    (h : r1 ≠ r2) : update r1 v1 (update r2 v2 e) = update r2 v2 (update r1 v1 e) := by
  funext r; unfold update
  by_cases h1 : r = r1 <;> by_cases h2 : r = r2 <;> simp_all

theorem update_twice (r : reg) (v : val) (e : env reg val) :
    update r v (update r v e) = update r v e := by
  funext r'; unfold update; split <;> simp_all

/-- Parallel semantics of moves. -/
def exec_par : moves reg → env reg val → env reg val
  | [], e => e
  | (s, d) :: m', e => update d (e s) (exec_par m' e)

/-- Sequential semantics of moves. -/
def exec_seq : moves reg → env reg val → env reg val
  | [], e => e
  | (s, d) :: m', e => exec_seq m' (update d (e s) e)

/-- Sequential semantics, executing the moves in reverse order. -/
def exec_seq_rev : moves reg → env reg val → env reg val
  | [], e => e
  | (s, d) :: m', e =>
      let e' := exec_seq_rev m' e
      update d (e' s) e'


@[simp] theorem exec_par_nil (e : env reg val) : exec_par [] e = e := rfl
@[simp] theorem exec_par_cons (s d : reg) (m : moves reg) (e : env reg val) :
    exec_par ((s, d) :: m) e = update d (e s) (exec_par m e) := rfl
@[simp] theorem exec_seq_nil (e : env reg val) : exec_seq [] e = e := rfl
@[simp] theorem exec_seq_cons (s d : reg) (m : moves reg) (e : env reg val) :
    exec_seq ((s, d) :: m) e = exec_seq m (update d (e s) e) := rfl
@[simp] theorem exec_seq_rev_nil (e : env reg val) : exec_seq_rev [] e = e := rfl
@[simp] theorem exec_seq_rev_cons (s d : reg) (m : moves reg) (e : env reg val) :
    exec_seq_rev ((s, d) :: m) e = update d (exec_seq_rev m e s) (exec_seq_rev m e) := rfl

/-! ### Transitions preserve semantics -/

/-- Semantics of a state: perform `tau` in reverse sequential order, then
`mu ++ sigma` in parallel. -/
def statemove (st : state reg) (e : env reg val) : env reg val :=
  exec_par (st.mu ++ st.sigma) (exec_seq_rev st.tau e)

theorem exec_par_outside (m : moves reg) (e : env reg val) (r : reg) (h : r ∉ dests m) :
    exec_par m e r = e r := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    obtain ⟨s, d⟩ := a
    simp only [dests_cons, List.mem_cons, not_or] at h
    simp only [exec_par_cons]
    rw [update_o _ _ _ _ h.1, ih h.2]

theorem exec_par_lift (m1 : moves reg) (s d : reg) (m2 : moves reg) (e : env reg val)
    (h : d ∉ dests m1) :
    exec_par (m1 ++ (s, d) :: m2) e = exec_par ((s, d) :: (m1 ++ m2)) e := by
  induction m1 with
  | nil => rfl
  | cons a m1 ih =>
    obtain ⟨s0, d0⟩ := a
    simp only [dests_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, exec_par_cons] at ih ⊢
    rw [ih h.2, update_commut _ _ _ _ _ (Ne.symm h.1)]

theorem exec_par_ident (m1 : moves reg) (r : reg) (m2 : moves reg) (e : env reg val)
    (h : is_mill (m1 ++ (r, r) :: m2)) :
    exec_par (m1 ++ (r, r) :: m2) e = exec_par (m1 ++ m2) e := by
  simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
    List.mem_cons] at h
  have h1 : r ∉ dests m1 := fun hr => h.2.2 r hr r (.inl rfl) rfl
  rw [exec_par_lift _ _ _ _ _ h1, exec_par_cons]
  have : exec_par (m1 ++ m2) e r = e r :=
    exec_par_outside _ _ _ (by simp only [dests_append, List.mem_append, not_or]; exact ⟨h1, h.2.1.1⟩)
  rw [← this, update_ident]

theorem exec_seq_app (m1 m2 : moves reg) (e : env reg val) :
    exec_seq (m1 ++ m2) e = exec_seq m2 (exec_seq m1 e) := by
  induction m1 generalizing e with
  | nil => rfl
  | cons a m1 ih => obtain ⟨s, d⟩ := a; simp [ih]

theorem exec_seq_rev_app (m1 m2 : moves reg) (e : env reg val) :
    exec_seq_rev (m1 ++ m2) e = exec_seq_rev m1 (exec_seq_rev m2 e) := by
  induction m1 with
  | nil => rfl
  | cons a m1 ih => obtain ⟨s, d⟩ := a; simp [ih]

theorem exec_seq_exec_seq_rev (m : moves reg) (e : env reg val) :
    exec_seq_rev m e = exec_seq m.reverse e := by
  induction m with
  | nil => rfl
  | cons a m ih => obtain ⟨s, d⟩ := a; simp [exec_seq_app, ih]

theorem exec_seq_rev_exec_seq (m : moves reg) (e : env reg val) :
    exec_seq m e = exec_seq_rev m.reverse e := by
  rw [exec_seq_exec_seq_rev, List.reverse_reverse]

theorem exec_par_update_no_read (s d : reg) (m : moves reg) (e : env reg val)
    (hnr : no_read m d) (hnd : d ∉ dests m) :
    exec_par m (update d (e s) e) = update d (e s) (exec_par m e) := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    obtain ⟨s0, d0⟩ := a
    simp only [no_read, srcs_cons, List.mem_cons, not_or] at hnr
    simp only [dests_cons, List.mem_cons, not_or] at hnd
    simp only [exec_par_cons]
    rw [ih hnr.2 hnd.2, update_commut _ _ _ _ _ (Ne.symm hnd.1), update_o _ _ _ _ (Ne.symm hnr.1)]

theorem exec_par_append_eq (m1 m2 m3 : moves reg) (e2 e3 : env reg val)
    (h : exec_par m2 e2 = exec_par m3 e3) (hs : ∀ r, r ∈ srcs m1 → e2 r = e3 r) :
    exec_par (m1 ++ m2) e2 = exec_par (m1 ++ m3) e3 := by
  induction m1 with
  | nil => exact h
  | cons a m1 ih =>
    obtain ⟨s, d⟩ := a
    simp only [srcs_cons, List.mem_cons] at hs
    simp only [List.cons_append, exec_par_cons]
    rw [ih (fun r hr => hs r (.inr hr)), hs s (.inl rfl)]

theorem exec_par_combine (e : env reg val) (sl dl : List reg) (hlen : sl.length = dl.length)
    (hnd : dl.Nodup) :
    dl.map (exec_par (sl.zip dl) e) = sl.map e ∧
    ∀ l, l ∉ dl → exec_par (sl.zip dl) e l = e l := by
  induction sl generalizing dl with
  | nil => cases dl <;> simp_all
  | cons a sl ih =>
    cases dl with
    | nil => simp at hlen
    | cons b dl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [List.nodup_cons] at hnd
      obtain ⟨A, B⟩ := ih dl hlen hnd.2
      simp only [List.zip_cons_cons, exec_par_cons, List.map_cons, update_s, List.cons.injEq,
        true_and, List.mem_cons, not_or]
      refine ⟨?_, fun l hl => by rw [update_o _ _ _ _ hl.1, B l hl.2]⟩
      rw [← A]
      apply List.map_congr_left
      intro x hx
      exact update_o _ _ _ _ (fun h => hnd.1 (h ▸ hx))

/-- Two environments agree on all non-temporary registers. -/
def env_equiv (temp : reg → reg) (e1 e2 : env reg val) : Prop :=
  ∀ r, is_not_temp temp r → e1 r = e2 r

omit [DecidableEq reg] in
theorem env_equiv_refl (temp : reg → reg) (e : env reg val) : env_equiv temp e e :=
  fun _ _ => rfl

omit [DecidableEq reg] in
theorem env_equiv_refl' (temp : reg → reg) {e1 e2 : env reg val} (h : e1 = e2) :
    env_equiv temp e1 e2 := h ▸ env_equiv_refl temp e1

omit [DecidableEq reg] in
theorem env_equiv_sym {temp : reg → reg} {e1 e2 : env reg val} (h : env_equiv temp e1 e2) :
    env_equiv temp e2 e1 := fun r hr => (h r hr).symm

omit [DecidableEq reg] in
theorem env_equiv_trans {temp : reg → reg} {e1 e2 e3 : env reg val}
    (h1 : env_equiv temp e1 e2) (h2 : env_equiv temp e2 e3) : env_equiv temp e1 e3 :=
  fun r hr => (h1 r hr).trans (h2 r hr)

theorem exec_par_env_equiv {temp : reg → reg} (m : moves reg) (e1 e2 : env reg val)
    (hm : move_no_temp temp m) (h : env_equiv temp e1 e2) :
    env_equiv temp (exec_par m e1) (exec_par m e2) := by
  induction m with
  | nil => exact h
  | cons a m ih =>
    obtain ⟨s, d⟩ := a
    intro r hr
    simp only [exec_par_cons, update]
    split
    · exact h s (hm s d (by simp)).1
    · exact ih (fun s' d' h' => hm s' d' (by simp [h'])) r hr

theorem transition_preserves_semantics {temp : reg → reg} {st st' : state reg}
    (e : env reg val) (ht : transition temp st st') (hwf : state_wf temp st) :
    env_equiv temp (statemove st' e) (statemove st e) := by
  cases hwf with
  | intro mu sigma tau A B C D =>
  cases ht with
  | tr_nop mu1 r mu2 =>
    apply env_equiv_refl'
    simp only [statemove, List.append_assoc, List.cons_append]
    rw [List.append_assoc, List.cons_append] at A
    exact (exec_par_ident _ _ _ _ A).symm
  | tr_start mu1 s d mu2 =>
    apply env_equiv_refl'
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_cons, List.append_nil] at A
    simp only [statemove, List.append_nil]
    rw [exec_par_lift _ _ _ _ _ (by simp only [dests_append, List.mem_append]; grind),
      exec_par_lift _ _ _ _ _ (by grind)]
    simp
  | tr_push mu1 d r mu2 s sigma =>
    apply env_equiv_refl'
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons] at A
    simp only [statemove, List.append_assoc, List.cons_append]
    generalize exec_seq_rev tau e = E
    have h1 : r ∉ dests (mu1 ++ mu2) := by simp only [dests_append, List.mem_append]; grind
    have h2 : d ∉ dests (mu1 ++ mu2) := by simp only [dests_append, List.mem_append]; grind
    have h3 : r ∉ dests mu1 := by grind
    rw [← List.append_assoc, exec_par_lift _ _ _ _ _ h1, exec_par_cons,
      exec_par_lift _ _ _ _ _ h2, exec_par_lift _ _ _ _ _ h3, exec_par_cons, ← List.append_assoc,
      exec_par_cons, exec_par_lift _ _ _ _ _ h2, exec_par_cons]
  | tr_loop mu sigma s d =>
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_cons] at A
    simp only [statemove, exec_seq_rev_cons]
    generalize exec_seq_rev tau e = e1
    have hd : d ∉ dests (mu ++ sigma) := by simp only [dests_append, List.mem_append]; grind
    rw [← List.append_assoc, ← List.append_assoc, exec_par_lift _ _ _ _ _ hd,
      exec_par_lift _ _ _ _ _ hd]
    simp only [List.append_nil, exec_par_cons]
    have hmnt : move_no_temp temp (mu ++ sigma) := by
      unfold temp_last at C
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append] at C
      exact move_no_temp_append B (move_no_temp_rev C.2)
    have h2 : env_equiv temp (update (temp s) (e1 s) e1) e1 :=
      fun r hr => update_o _ _ _ _ (hr s)
    have h4 := exec_par_env_equiv _ _ _ hmnt h2
    intro r hr
    simp only [update]
    split
    · simp
    · exact h4 r hr
  | tr_pop mu s0 d0 s1 d1 sigma _ hnr hne =>
    apply env_equiv_refl'
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_append, List.mem_cons, List.cons_append] at A
    simp only [statemove, exec_seq_rev_cons]
    generalize exec_seq_rev tau e = e1
    have hnd1 : d1 ∉ dests mu := by grind
    rw [List.cons_append, exec_par_lift _ _ _ _ _ hnd1, exec_par_cons]
    apply exec_par_update_no_read
    · have hp := no_read_path _ _ _ _ hne (is_path_pop D) (by simp only [dests_append,
        List.mem_append, dests_cons, List.mem_cons, dests_nil]; grind)
      simp only [no_read, srcs_append, List.mem_append, not_or] at hp hnr ⊢
      exact ⟨hnr, hp⟩
    · simp only [dests_append, List.mem_append, dests_cons, List.mem_cons, dests_nil]; grind
  | tr_last mu s d _ hnr =>
    apply env_equiv_refl'
    simp only [is_mill, dests_append, dests_cons, List.nodup_append, List.nodup_cons,
      List.mem_cons, dests_nil] at A
    simp only [statemove, exec_seq_rev_cons, List.append_nil]
    generalize exec_seq_rev tau e = e1
    have hnd : d ∉ dests mu := by grind
    rw [exec_par_update_no_read _ _ _ _ hnr hnd, exec_par_lift _ _ _ _ _ hnd]
    simp

theorem transitions_preserve_semantics {temp : reg → reg} {st st' : state reg}
    (e : env reg val) (ht : transitions temp st st') (hwf : state_wf temp st) :
    env_equiv temp (statemove st' e) (statemove st e) := by
  induction ht with
  | refl => exact env_equiv_refl _ _
  | step h hs ih =>
    exact env_equiv_trans (ih (transition_preserves_wf h hwf))
      (transition_preserves_semantics e h hwf)

omit [DecidableEq reg] in
theorem state_wf_start (temp : reg → reg) (mu : moves reg) (h1 : move_no_temp temp mu)
    (h2 : is_mill mu) : state_wf temp ⟨mu, [], []⟩ :=
  .intro _ _ _ (by simpa using h2) h1 trivial .nil

/-- Main correctness result for the non-deterministic system. -/
theorem transitions_correctness (temp : reg → reg) (mu tau : moves reg)
    (h1 : move_no_temp temp mu) (h2 : is_mill mu)
    (ht : transitions temp ⟨mu, [], []⟩ ⟨[], [], tau⟩) (e : env reg val) :
    env_equiv temp (exec_seq tau.reverse e) (exec_par mu e) := by
  have := transitions_preserve_semantics e ht (state_wf_start temp mu h1 h2)
  simp only [statemove, List.append_nil, exec_seq_rev_nil] at this
  rwa [exec_seq_exec_seq_rev] at this

/-! ## Determinisation of the transition relation -/

/-- Deterministic variant of `transition`. -/
inductive dtransition (temp : reg → reg) : state reg → state reg → Prop where
  | dtr_nop (r : reg) (mu tau : moves reg) :
      dtransition temp ⟨(r, r) :: mu, [], tau⟩ ⟨mu, [], tau⟩
  | dtr_start (s d : reg) (mu tau : moves reg) :
      s ≠ d → dtransition temp ⟨(s, d) :: mu, [], tau⟩ ⟨mu, [(s, d)], tau⟩
  | dtr_push (mu1 : moves reg) (d r : reg) (mu2 : moves reg) (s : reg) (sigma tau : moves reg) :
      no_read mu1 d →
      dtransition temp ⟨mu1 ++ (d, r) :: mu2, (s, d) :: sigma, tau⟩
                       ⟨mu1 ++ mu2, (d, r) :: (s, d) :: sigma, tau⟩
  | dtr_loop_pop (mu : moves reg) (s r0 d : reg) (sigma tau : moves reg) :
      no_read mu r0 →
      dtransition temp ⟨mu, (s, r0) :: sigma ++ [(r0, d)], tau⟩
                       ⟨mu, sigma ++ [(temp r0, d)], (s, r0) :: (r0, temp r0) :: tau⟩
  | dtr_pop (mu : moves reg) (s0 d0 s1 d1 : reg) (sigma tau : moves reg) :
      no_read mu d1 → d1 ≠ s0 →
      dtransition temp ⟨mu, (s1, d1) :: sigma ++ [(s0, d0)], tau⟩
                       ⟨mu, sigma ++ [(s0, d0)], (s1, d1) :: tau⟩
  | dtr_last (mu : moves reg) (s d : reg) (tau : moves reg) :
      no_read mu d → dtransition temp ⟨mu, [(s, d)], tau⟩ ⟨mu, [], (s, d) :: tau⟩

/-- Reflexive-transitive closure of `dtransition`. -/
def dtransitions (temp : reg → reg) : state reg → state reg → Prop := Star (dtransition temp)

omit [DecidableEq reg] in
theorem transition_determ {temp : reg → reg} {st st' : state reg}
    (h : dtransition temp st st') (hwf : state_wf temp st) : transitions temp st st' := by
  cases h with
  | dtr_nop r mu tau => exact .single (transition.tr_nop [] r mu [] tau)
  | dtr_start s d mu tau _ => exact .single (transition.tr_start [] s d mu tau)
  | dtr_push mu1 d r mu2 s sigma tau _ => exact .single (transition.tr_push _ _ _ _ _ _ _)
  | dtr_loop_pop mu s r0 d sigma tau hnr =>
    refine .step (transition.tr_loop mu ((s, r0) :: sigma) r0 d tau) (.single ?_)
    refine transition.tr_pop _ _ _ _ _ _ _ hnr ?_
    cases hwf with
    | intro _ _ _ _ _ C _ =>
      unfold temp_last at C
      simp only [List.cons_append, List.reverse_cons, List.reverse_append,
        List.reverse_nil, List.nil_append, List.cons_append] at C
      exact (C.2 s r0 (by simp)).2 r0
  | dtr_pop mu s0 d0 s1 d1 sigma tau h1 h2 => exact .single (transition.tr_pop _ _ _ _ _ _ _ h1 h2)
  | dtr_last mu s d tau h1 => exact .single (transition.tr_last _ _ _ _ h1)

omit [DecidableEq reg] in
theorem transitions_determ {temp : reg → reg} {st st' : state reg}
    (h : dtransitions temp st st') (hwf : state_wf temp st) : transitions temp st st' := by
  induction h with
  | refl => exact .refl _
  | step h1 _ ih =>
    have t1 := transition_determ h1 hwf
    exact t1.trans (ih (transitions_preserve_wf t1 hwf))

theorem dtransitions_correctness (temp : reg → reg) (mu tau : moves reg)
    (h1 : move_no_temp temp mu) (h2 : is_mill mu)
    (ht : dtransitions temp ⟨mu, [], []⟩ ⟨[], [], tau⟩) (e : env reg val) :
    env_equiv temp (exec_seq tau.reverse e) (exec_par mu e) :=
  transitions_correctness temp mu tau h1 h2
    (transitions_determ ht (state_wf_start temp mu h1 h2)) e

/-! ## The compilation function -/

/-- Find the first move whose source is `r`. -/
def split_move : moves reg → reg → Option (moves reg × reg × moves reg)
  | [], _ => none
  | (s, d) :: tl, r =>
      if s = r then some ([], d, tl)
      else match split_move tl r with
        | none => none
        | some (before, d', after) => some ((s, d) :: before, d', after)

/-- Is `r` the source of the last move of `m`? -/
def is_last_source (r : reg) : moves reg → Bool
  | [] => false
  | [(s, _)] => decide (s = r)
  | _ :: tl => is_last_source r tl

/-- Replace the source of the last move of `m` by `r`. -/
def replace_last_source (r : reg) : moves reg → moves reg
  | [] => []
  | [(_, d)] => [(r, d)]
  | s_d :: tl => s_d :: replace_last_source r tl

/-- Final states: `mu` and `sigma` are empty. -/
def final_state (st : state reg) : Bool :=
  match st with
  | ⟨[], [], _⟩ => true
  | _ => false

/-- The case of `parmove_step` where `sigma = (s, d) :: b` and no move of `t`
reads `d`. -/
def parmove_step_pop (temp : reg → reg) (t : moves reg) (s d : reg) (b l : moves reg) :
    state reg :=
  match b with
  | [] => ⟨t, [], (s, d) :: l⟩
  | _ =>
      if is_last_source d b
      then ⟨t, replace_last_source (temp d) b, (s, d) :: (d, temp d) :: l⟩
      else ⟨t, b, (s, d) :: l⟩

/-- The case of `parmove_step` where `sigma = (s, d) :: b`. -/
def parmove_step_sigma (temp : reg → reg) (t : moves reg) (s d : reg) (b l : moves reg) :
    state reg :=
  match split_move t d with
  | some (t1, r, t2) => ⟨t1 ++ t2, (d, r) :: (s, d) :: b, l⟩
  | none => parmove_step_pop temp t s d b l

/-- One step of the deterministic algorithm. -/
def parmove_step (temp : reg → reg) (st : state reg) : state reg :=
  match st with
  | ⟨[], [], _⟩ => st
  | ⟨(s, d) :: tl, [], l⟩ => if s = d then ⟨tl, [], l⟩ else ⟨tl, [(s, d)], l⟩
  | ⟨t, (s, d) :: b, l⟩ => parmove_step_sigma temp t s d b l

theorem split_move_charact (m : moves reg) (r : reg) :
    match split_move m r with
    | some (before, d, after) => m = before ++ (r, d) :: after ∧ no_read before r
    | none => no_read m r := by
  induction m with
  | nil => simp [split_move, no_read]
  | cons a m ih =>
    obtain ⟨s, d⟩ := a
    simp only [split_move]
    by_cases hs : s = r
    · subst hs; simp [no_read]
    · simp only [hs, if_false]
      revert ih
      cases split_move m r with
      | none => intro ih; simp only [no_read, srcs_cons, List.mem_cons, not_or] at ih ⊢; exact ⟨Ne.symm hs, ih⟩
      | some x =>
        obtain ⟨before, d', after⟩ := x
        rintro ⟨rfl, ih⟩
        simp only [no_read, srcs_cons, List.mem_cons, not_or] at ih ⊢
        exact ⟨rfl, Ne.symm hs, ih⟩

theorem is_last_source_charact (r s d : reg) (m : moves reg) :
    if is_last_source r (m ++ [(s, d)]) then s = r else s ≠ r := by
  induction m with
  | nil => by_cases h : s = r <;> simp [is_last_source, h]
  | cons a m ih =>
    rcases hm : m ++ [(s, d)] with _ | ⟨b, tl⟩
    · simp at hm
    · rw [hm] at ih
      simp only [List.cons_append, hm]
      exact ih

omit [DecidableEq reg] in
theorem replace_last_source_charact (s d s' : reg) (m : moves reg) :
    replace_last_source s' (m ++ [(s, d)]) = m ++ [(s', d)] := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    rcases hm : m ++ [(s, d)] with _ | ⟨b, tl⟩
    · simp at hm
    · rw [hm] at ih
      simp only [List.cons_append, hm, replace_last_source, ih]

theorem exists_last_of_ne_nil {α : Type _} {l : List α} (h : l ≠ []) :
    ∃ l' x, l = l' ++ [x] := by
  rcases List.eq_nil_or_concat l with h' | ⟨l', b, h'⟩
  · exact absurd h' h
  · exact ⟨l', b, by simpa using h'⟩

/-- Shared part of `parmove_step_compatible`: the `sigma` non-empty, no
`split_move` case. -/
theorem parmove_step_compatible_pop (temp : reg → reg) (t : moves reg) (s d : reg)
    (b l : moves reg) (hnr : no_read t d) :
    dtransition temp ⟨t, (s, d) :: b, l⟩ (parmove_step_pop temp t s d b l) := by
  unfold parmove_step_pop
  rcases b with _ | ⟨x, b'⟩
  · exact .dtr_last _ _ _ _ hnr
  · obtain ⟨sigma1, ⟨ss1, sd1⟩, heq⟩ := exists_last_of_ne_nil (l := x :: b') (by simp)
    simp only
    rw [heq]
    have hc := is_last_source_charact d ss1 sd1 sigma1
    split at hc
    · next hl =>
      rw [if_pos hl]
      subst hc
      rw [replace_last_source_charact]
      exact .dtr_loop_pop _ _ _ _ _ _ hnr
    · next hl =>
      rw [if_neg hl]
      exact .dtr_pop _ _ _ _ _ _ _ hnr (Ne.symm hc)

theorem parmove_step_compatible (temp : reg → reg) (st : state reg)
    (hnf : final_state st = false) : dtransition temp st (parmove_step temp st) := by
  obtain ⟨mu, sigma, tau⟩ := st
  rcases sigma with _ | ⟨⟨ss, sd⟩, stl⟩
  · rcases mu with _ | ⟨⟨ms, md⟩, mtl⟩
    · simp [final_state] at hnf
    · simp only [parmove_step]
      by_cases h : ms = md
      · subst h; simp only [if_true]; exact .dtr_nop _ _ _
      · simp only [h, if_false]; exact .dtr_start _ _ _ _ h
  · have hstep : parmove_step temp ⟨mu, (ss, sd) :: stl, tau⟩ =
        parmove_step_sigma temp mu ss sd stl tau := by
      rcases mu with _ | ⟨⟨ms, md⟩, mtl⟩ <;> rfl
    rw [hstep]
    unfold parmove_step_sigma
    have hc := split_move_charact mu sd
    revert hc
    cases split_move mu sd with
    | some x =>
      obtain ⟨before, r, after⟩ := x
      rintro ⟨rfl, hnr⟩
      exact .dtr_push _ _ _ _ _ _ _ hnr
    | none =>
      intro hnr
      exact parmove_step_compatible_pop temp mu ss sd stl tau hnr

/-- Termination measure. -/
def measure (st : state reg) : Nat := 2 * st.mu.length + st.sigma.length

omit [DecidableEq reg] in
theorem measure_decreasing_1 {temp : reg → reg} {st st' : state reg}
    (h : dtransition temp st st') : measure st' < measure st := by
  cases h <;> simp [measure] <;> omega

theorem measure_decreasing_2 (temp : reg → reg) (st : state reg)
    (h : final_state st = false) : measure (parmove_step temp st) < measure st :=
  measure_decreasing_1 (parmove_step_compatible temp st h)

/-- Iterate `parmove_step` until a final state is reached. -/
def parmove_aux (temp : reg → reg) (st : state reg) : moves reg :=
  if _ : final_state st = true then st.tau
  else parmove_aux temp (parmove_step temp st)
termination_by measure st
decreasing_by exact measure_decreasing_2 temp st (by simp_all)

theorem parmove_aux_transitions (temp : reg → reg) (st : state reg) :
    dtransitions temp st ⟨[], [], parmove_aux temp st⟩ := by
  rw [parmove_aux]
  split
  · next h =>
    obtain ⟨mu, sigma, tau⟩ := st
    rcases mu with _ | ⟨_, _⟩ <;> rcases sigma with _ | ⟨_, _⟩ <;> simp [final_state] at h
    exact .refl _
  · next h =>
    exact .step (parmove_step_compatible temp st (by simpa using h))
      (parmove_aux_transitions temp (parmove_step temp st))
termination_by measure st
decreasing_by exact measure_decreasing_2 temp st (by simp_all)

/-- The compilation function for parallel moves. -/
def parmove (temp : reg → reg) (mu : moves reg) : moves reg :=
  (parmove_aux temp ⟨mu, [], []⟩).reverse

/-- Main correctness theorem: `parmove mu` is equivalent to the parallel move `mu`
(up to the values of temporaries), provided `mu` is well-formed. -/
theorem parmove_correctness (temp : reg → reg) (mu : moves reg)
    (h1 : move_no_temp temp mu) (h2 : is_mill mu) (e : env reg val) :
    env_equiv temp (exec_seq (parmove temp mu) e) (exec_par mu e) :=
  dtransitions_correctness temp mu _ h1 h2 (parmove_aux_transitions temp _) e

/-- `parmove` on separate lists of sources and destinations. -/
def parmove2 (temp : reg → reg) (sl dl : List reg) : moves reg :=
  parmove temp (sl.zip dl)

theorem parmove2_correctness (temp : reg → reg) (sl dl : List reg)
    (hlen : sl.length = dl.length) (hnd : dl.Nodup)
    (hs : ∀ r, r ∈ sl → is_not_temp temp r) (hd : ∀ r, r ∈ dl → is_not_temp temp r)
    (e : env reg val) :
    dl.map (exec_seq (parmove2 temp sl dl) e) = sl.map e ∧
    ∀ r, r ∉ dl → is_not_temp temp r → exec_seq (parmove2 temp sl dl) e r = e r := by
  obtain ⟨A, B⟩ := srcs_dests_combine sl dl hlen
  have H : env_equiv temp (exec_seq (parmove2 temp sl dl) e) (exec_par (sl.zip dl) e) := by
    apply parmove_correctness
    · intro s d h
      exact ⟨hs s (List.of_mem_zip h).1, hd d (List.of_mem_zip h).2⟩
    · unfold is_mill; rw [B]; exact hnd
  obtain ⟨C, D⟩ := exec_par_combine e sl dl hlen hnd
  refine ⟨?_, fun r hr hnt => (H r hnt).trans (D r hr)⟩
  rw [← C]
  exact List.map_congr_left (fun x hx => H x (hd x hx))

/-! ## Additional syntactic properties -/

section PROPERTIES

variable (temp : reg → reg) (initial_move : moves reg)

/-- Moves that may appear in the output of `parmove initial_move`. -/
inductive wf_move : reg → reg → Prop where
  | same (s d : reg) : (s, d) ∈ initial_move → wf_move s d
  | temp_left (s d : reg) : wf_move s d → wf_move (temp s) d
  | temp_right (s d : reg) : wf_move s d → wf_move s (temp s)

/-- All moves of `m` are `wf_move`. -/
def wf_moves (m : moves reg) : Prop := ∀ s d, (s, d) ∈ m → wf_move temp initial_move s d

omit [DecidableEq reg] in
theorem wf_moves_cons (s d : reg) (m : moves reg) :
    wf_moves temp initial_move ((s, d) :: m) ↔
      wf_move temp initial_move s d ∧ wf_moves temp initial_move m := by
  unfold wf_moves
  constructor
  · intro h; exact ⟨h s d (by simp), fun s' d' h' => h s' d' (by simp [h'])⟩
  · rintro ⟨h1, h2⟩ s' d' h'
    simp only [List.mem_cons, Prod.mk.injEq] at h'
    rcases h' with ⟨rfl, rfl⟩ | h'
    · exact h1
    · exact h2 _ _ h'

omit [DecidableEq reg] in
theorem wf_moves_append (m1 m2 : moves reg) :
    wf_moves temp initial_move (m1 ++ m2) ↔
      wf_moves temp initial_move m1 ∧ wf_moves temp initial_move m2 := by
  unfold wf_moves
  constructor
  · intro h
    exact ⟨fun s d h' => h s d (by simp [h']), fun s d h' => h s d (by simp [h'])⟩
  · rintro ⟨h1, h2⟩ s d h'
    rcases List.mem_append.1 h' with h' | h'
    · exact h1 _ _ h'
    · exact h2 _ _ h'

/-- All three components of a state are `wf_moves`. -/
inductive wf_state : state reg → Prop where
  | intro (mu sigma tau : moves reg) :
      wf_moves temp initial_move mu → wf_moves temp initial_move sigma →
      wf_moves temp initial_move tau → wf_state ⟨mu, sigma, tau⟩

omit [DecidableEq reg] in
theorem dtransition_preserves_wf_state {st st' : state reg}
    (h : dtransition temp st st') (hwf : wf_state temp initial_move st) :
    wf_state temp initial_move st' := by
  cases hwf with
  | intro mu sigma tau A B C =>
  cases h with
  | dtr_nop r mu tau =>
    rw [wf_moves_cons] at A; exact .intro _ _ _ A.2 B C
  | dtr_start s d mu tau _ =>
    rw [wf_moves_cons] at A
    exact .intro _ _ _ A.2 ((wf_moves_cons ..).2 ⟨A.1, fun _ _ h => nomatch h⟩) C
  | dtr_push mu1 d r mu2 s sigma tau _ =>
    rw [wf_moves_append, wf_moves_cons] at A
    exact .intro _ _ _ ((wf_moves_append ..).2 ⟨A.1, A.2.2⟩)
      ((wf_moves_cons ..).2 ⟨A.2.1, B⟩) C
  | dtr_loop_pop mu s r0 d sigma tau _ =>
    rw [wf_moves_append, wf_moves_cons, wf_moves_cons] at B
    refine .intro _ _ _ A ((wf_moves_append ..).2 ⟨B.1.2, (wf_moves_cons ..).2
      ⟨.temp_left _ _ B.2.1, B.2.2⟩⟩) ?_
    rw [wf_moves_cons, wf_moves_cons]
    exact ⟨B.1.1, .temp_right _ _ B.2.1, C⟩
  | dtr_pop mu s0 d0 s1 d1 sigma tau _ _ =>
    rw [wf_moves_append, wf_moves_cons] at B
    exact .intro _ _ _ A ((wf_moves_append ..).2 ⟨B.1.2, B.2⟩)
      ((wf_moves_cons ..).2 ⟨B.1.1, C⟩)
  | dtr_last mu s d tau _ =>
    rw [wf_moves_cons] at B
    exact .intro _ _ _ A (fun _ _ h => nomatch h) ((wf_moves_cons ..).2 ⟨B.1, C⟩)

omit [DecidableEq reg] in
theorem dtransitions_preserve_wf_state {st st' : state reg}
    (h : dtransitions temp st st') (hwf : wf_state temp initial_move st) :
    wf_state temp initial_move st' := by
  induction h with
  | refl => exact hwf
  | step h1 _ ih => exact ih (dtransition_preserves_wf_state temp initial_move h1 hwf)

end PROPERTIES

theorem parmove_wf_moves (temp : reg → reg) (mu : moves reg) :
    wf_moves temp mu (parmove temp mu) := by
  have H : wf_state temp mu ⟨mu, [], []⟩ :=
    .intro _ _ _ (fun s d h => .same _ _ h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
  have := dtransitions_preserve_wf_state temp mu (parmove_aux_transitions temp _) H
  cases this with
  | intro _ _ _ _ _ C =>
    intro s d h
    exact C s d (List.mem_reverse.1 h)

theorem parmove2_wf_moves (temp : reg → reg) (sl dl : List reg) :
    wf_moves temp (sl.zip dl) (parmove2 temp sl dl) :=
  parmove_wf_moves temp _

omit [DecidableEq reg] in
theorem wf_move_initial_reg_or_temp (temp : reg → reg) (mu : moves reg) {s d : reg}
    (h : wf_move temp mu s d) :
    (s ∈ srcs mu ∨ is_temp temp s) ∧ (d ∈ dests mu ∨ is_temp temp d) := by
  induction h with
  | same s d h => exact ⟨.inl (mem_srcs_of_mem h), .inl (mem_dests_of_mem h)⟩
  | temp_left s d _ ih => exact ⟨.inr ⟨s, rfl⟩, ih.2⟩
  | temp_right s d _ ih => exact ⟨ih.1, .inr ⟨s, rfl⟩⟩

theorem parmove_initial_reg_or_temp (temp : reg → reg) (mu : moves reg) (s d : reg)
    (h : (s, d) ∈ parmove temp mu) :
    (s ∈ srcs mu ∨ is_temp temp s) ∧ (d ∈ dests mu ∨ is_temp temp d) :=
  wf_move_initial_reg_or_temp temp mu (parmove_wf_moves temp mu s d h)

omit [DecidableEq reg] in
theorem in_srcs (mu : moves reg) (s : reg) (h : s ∈ srcs mu) : ∃ d, (s, d) ∈ mu := by
  obtain ⟨⟨s', d'⟩, h1, h2⟩ := List.mem_map.1 h
  exact ⟨d', by simpa [← h2] using h1⟩

omit [DecidableEq reg] in
theorem in_dests (mu : moves reg) (d : reg) (h : d ∈ dests mu) : ∃ s, (s, d) ∈ mu := by
  obtain ⟨⟨s', d'⟩, h1, h2⟩ := List.mem_map.1 h
  exact ⟨s', by simpa [← h2] using h1⟩

theorem parmove_srcs_initial_reg_or_temp (temp : reg → reg) (mu : moves reg) (s : reg)
    (h : s ∈ srcs (parmove temp mu)) : s ∈ srcs mu ∨ is_temp temp s := by
  obtain ⟨d, h⟩ := in_srcs _ _ h
  exact (parmove_initial_reg_or_temp temp mu s d h).1

theorem parmove_dests_initial_reg_or_temp (temp : reg → reg) (mu : moves reg) (d : reg)
    (h : d ∈ dests (parmove temp mu)) : d ∈ dests mu ∨ is_temp temp d := by
  obtain ⟨s, h⟩ := in_dests _ _ h
  exact (parmove_initial_reg_or_temp temp mu s d h).2

section REGISTER_CLASSES

variable {cls : Type _} (regclass : reg → cls)

/-- All moves of `mu` stay within one register class. -/
def is_class_compatible (mu : moves reg) : Prop :=
  ∀ s d, (s, d) ∈ mu → regclass s = regclass d

theorem parmove_preserves_register_classes (temp : reg → reg)
    (temp_preserves_class : ∀ r, regclass (temp r) = regclass r)
    (mu : moves reg) (h : is_class_compatible regclass mu) :
    is_class_compatible regclass (parmove temp mu) := by
  have H : ∀ s d, wf_move temp mu s d → regclass s = regclass d := by
    intro s d hw
    induction hw with
    | same s d h' => exact h s d h'
    | temp_left s d _ ih => rw [temp_preserves_class]; exact ih
    | temp_right s d _ _ => rw [temp_preserves_class]
  intro s d hm
  exact H s d (parmove_wf_moves temp mu s d hm)

end REGISTER_CLASSES

/-! ## Extension to partially overlapping registers -/

section OVERLAP_DEFS

variable (disjoint : reg → reg → Prop)

/-- Two registers do not partially overlap: they are equal or disjoint. -/
def no_overlap (r1 r2 : reg) : Prop := r1 = r2 ∨ disjoint r1 r2

omit [DecidableEq reg] in
theorem no_overlap_sym (disjoint_sym : ∀ r1 r2, disjoint r1 r2 → disjoint r2 r1)
    {r1 r2 : reg} (h : no_overlap disjoint r1 r2) : no_overlap disjoint r2 r1 := by
  rcases h with h | h
  · exact .inl h.symm
  · exact .inr (disjoint_sym _ _ h)

/-- Sequential execution with an overlap-aware update. -/
def weak_exec_seq (weak_update : reg → val → env reg val → env reg val) :
    moves reg → env reg val → env reg val
  | [], e => e
  | (s, d) :: m', e => weak_exec_seq weak_update m' (weak_update d (e s) e)

/-- `r` is disjoint from every register of `l`. -/
def disjoint_list (r : reg) (l : List reg) : Prop := ∀ r', r' ∈ l → disjoint r r'

/-- The registers of `l` are pairwise disjoint. -/
inductive pairwise_disjoint : List reg → Prop where
  | nil : pairwise_disjoint []
  | cons (r : reg) (l : List reg) :
      disjoint_list disjoint r l → pairwise_disjoint l → pairwise_disjoint (r :: l)

/-- `r` is disjoint from all temporaries. -/
def disjoint_temps (temp : reg → reg) (r : reg) : Prop := ∀ t, is_temp temp t → disjoint r t

end OVERLAP_DEFS

section OVERLAP

variable {disjoint : reg → reg → Prop}
  (disjoint_sym : ∀ r1 r2, disjoint r1 r2 → disjoint r2 r1)
  (disjoint_not_equal : ∀ r1 r2, disjoint r1 r2 → r1 ≠ r2)

include disjoint_not_equal in
omit [DecidableEq reg] in
theorem disjoint_list_notin {r : reg} {l : List reg} (h : disjoint_list disjoint r l) :
    r ∉ l := fun hr => disjoint_not_equal r r (h r hr) rfl

omit [DecidableEq reg] in
include disjoint_not_equal in
theorem pairwise_disjoint_norepet {l : List reg} (h : pairwise_disjoint disjoint l) :
    l.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | cons r l h1 _ ih => exact List.nodup_cons.2 ⟨disjoint_list_notin disjoint_not_equal h1, ih⟩

include disjoint_not_equal in
omit [DecidableEq reg] in
theorem disjoint_temps_not_temp {temp : reg → reg} {r : reg}
    (h : disjoint_temps disjoint temp r) : is_not_temp temp r :=
  fun d => disjoint_not_equal _ _ (h _ ⟨d, rfl⟩)

include disjoint_sym in
omit [DecidableEq reg] in
theorem no_overlap_pairwise {r1 r2 : reg} {m : List reg} (h : pairwise_disjoint disjoint m)
    (h1 : r1 ∈ m) (h2 : r2 ∈ m) : no_overlap disjoint r1 r2 := by
  induction h with
  | nil => simp at h1
  | cons r l hd _ ih =>
    simp only [List.mem_cons] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · exact .inl rfl
    · exact .inr (hd _ h2)
    · exact .inr (disjoint_sym _ _ (hd _ h1))
    · exact ih h1 h2

variable (temp : reg → reg) (mu : moves reg)

/-- Registers not in the "adherence" of `mu`: they do not partially overlap
any destination or temporary. -/
def no_adherence (r : reg) : Prop :=
  ∀ x, x ∈ dests mu ∨ is_temp temp x → no_overlap disjoint x r

/-- Agreement on all registers outside the adherence of `mu`. -/
def env_match (e1 e2 : env reg val) : Prop :=
  ∀ r, no_adherence (disjoint := disjoint) temp mu r → e1 r = e2 r

variable
  (mu_no_temporaries_src : ∀ s, s ∈ srcs mu → disjoint_temps disjoint temp s)
  (mu_no_temporaries_dst : ∀ d, d ∈ dests mu → disjoint_temps disjoint temp d)
  (mu_dest_pairwise_disjoint : pairwise_disjoint disjoint (dests mu))
  (mu_src_dst_no_overlap : ∀ s d, s ∈ srcs mu → d ∈ dests mu → no_overlap disjoint s d)
  (temps_no_overlap : ∀ t1 t2, is_temp temp t1 → is_temp temp t2 → no_overlap disjoint t1 t2)

omit [DecidableEq reg] in
include disjoint_not_equal mu_dest_pairwise_disjoint in
theorem mu_is_mill : is_mill mu :=
  pairwise_disjoint_norepet disjoint_not_equal mu_dest_pairwise_disjoint

omit [DecidableEq reg] in
include disjoint_not_equal mu_no_temporaries_src mu_no_temporaries_dst in
theorem mu_move_no_temp : move_no_temp temp mu := fun s d h =>
  ⟨disjoint_temps_not_temp disjoint_not_equal (mu_no_temporaries_src s (mem_srcs_of_mem h)),
   disjoint_temps_not_temp disjoint_not_equal (mu_no_temporaries_dst d (mem_dests_of_mem h))⟩

omit [DecidableEq reg] in
include disjoint_sym mu_no_temporaries_dst mu_dest_pairwise_disjoint in
theorem no_adherence_dst (d : reg) (h : d ∈ dests mu) :
    no_adherence (disjoint := disjoint) temp mu d := by
  intro x hx
  rcases hx with hx | hx
  · exact no_overlap_pairwise disjoint_sym mu_dest_pairwise_disjoint hx h
  · exact .inr (disjoint_sym _ _ (mu_no_temporaries_dst d h x hx))

omit [DecidableEq reg] in
include disjoint_sym mu_no_temporaries_src mu_src_dst_no_overlap in
theorem no_adherence_src (s : reg) (h : s ∈ srcs mu) :
    no_adherence (disjoint := disjoint) temp mu s := by
  intro x hx
  rcases hx with hx | hx
  · exact no_overlap_sym disjoint disjoint_sym (mu_src_dst_no_overlap s x h hx)
  · exact .inr (disjoint_sym _ _ (mu_no_temporaries_src s h x hx))

include mu_no_temporaries_dst temps_no_overlap in
omit [DecidableEq reg] in
theorem no_adherence_tmp (t : reg) (h : is_temp temp t) :
    no_adherence (disjoint := disjoint) temp mu t := by
  intro x hx
  rcases hx with hx | hx
  · exact .inr (mu_no_temporaries_dst x hx t h)
  · exact temps_no_overlap x t hx h

variable (weak_update : reg → val → env reg val → env reg val)
  (weak_update_s : ∀ r v e, weak_update r v e r = v)
  (weak_update_d : ∀ r1 v e r2, disjoint r1 r2 → weak_update r1 v e r2 = e r2)

include disjoint_sym disjoint_not_equal mu_no_temporaries_src mu_no_temporaries_dst
  mu_src_dst_no_overlap temps_no_overlap weak_update_s weak_update_d in
theorem weak_update_match (e1 e2 : env reg val) (s d : reg)
    (hs : s ∈ srcs mu ∨ is_temp temp s) (hd : d ∈ dests mu ∨ is_temp temp d)
    (h : env_match (disjoint := disjoint) temp mu e1 e2) :
    env_match (disjoint := disjoint) temp mu (update d (e1 s) e1) (weak_update d (e2 s) e2) := by
  intro r hr
  rcases hr d hd with rfl | hdr
  · rw [update_s, weak_update_s]
    apply h
    rcases hs with hs | hs
    · exact no_adherence_src disjoint_sym temp mu mu_no_temporaries_src mu_src_dst_no_overlap s hs
    · exact no_adherence_tmp temp mu mu_no_temporaries_dst temps_no_overlap s hs
  · rw [update_o _ _ _ _ (Ne.symm (disjoint_not_equal _ _ hdr)), weak_update_d _ _ _ _ hdr]
    exact h r hr

include disjoint_sym disjoint_not_equal mu_no_temporaries_src mu_no_temporaries_dst
  mu_src_dst_no_overlap temps_no_overlap weak_update_s weak_update_d in
theorem weak_exec_seq_match (m : moves reg) (e1 e2 : env reg val)
    (hs : ∀ s, s ∈ srcs m → s ∈ srcs mu ∨ is_temp temp s)
    (hd : ∀ d, d ∈ dests m → d ∈ dests mu ∨ is_temp temp d)
    (h : env_match (disjoint := disjoint) temp mu e1 e2) :
    env_match (disjoint := disjoint) temp mu (exec_seq m e1) (weak_exec_seq weak_update m e2) := by
  induction m generalizing e1 e2 with
  | nil => exact h
  | cons a m ih =>
    obtain ⟨s, d⟩ := a
    simp only [srcs_cons, List.mem_cons, dests_cons] at hs hd
    exact ih _ _ (fun s' h' => hs s' (.inr h')) (fun d' h' => hd d' (.inr h'))
      (weak_update_match disjoint_sym disjoint_not_equal temp mu mu_no_temporaries_src
        mu_no_temporaries_dst mu_src_dst_no_overlap temps_no_overlap weak_update weak_update_s
        weak_update_d e1 e2 s d (hs s (.inl rfl)) (hd d (.inl rfl)) h)

end OVERLAP

/-- Correctness of `parmove2` taking partial register overlap into account. -/
theorem parmove2_correctness_with_overlap {disjoint : reg → reg → Prop}
    (disjoint_sym : ∀ r1 r2, disjoint r1 r2 → disjoint r2 r1)
    (disjoint_not_equal : ∀ r1 r2, disjoint r1 r2 → r1 ≠ r2)
    (temp : reg → reg)
    (weak_update : reg → val → env reg val → env reg val)
    (weak_update_s : ∀ r v e, weak_update r v e r = v)
    (weak_update_d : ∀ r1 v e r2, disjoint r1 r2 → weak_update r1 v e r2 = e r2)
    (sl dl : List reg) (hlen : sl.length = dl.length)
    (hsl : ∀ r, r ∈ sl → disjoint_temps disjoint temp r)
    (hdl : ∀ r, r ∈ dl → disjoint_temps disjoint temp r)
    (hpw : pairwise_disjoint disjoint dl)
    (hov : ∀ s d, s ∈ sl → d ∈ dl → no_overlap disjoint s d)
    (htmp : ∀ t1 t2, is_temp temp t1 → is_temp temp t2 → no_overlap disjoint t1 t2)
    (e : env reg val) :
    dl.map (weak_exec_seq weak_update (parmove2 temp sl dl) e) = sl.map e ∧
    ∀ r, disjoint_list disjoint r dl → disjoint_temps disjoint temp r →
      weak_exec_seq weak_update (parmove2 temp sl dl) e r = e r := by
  have hnd : dl.Nodup := pairwise_disjoint_norepet disjoint_not_equal hpw
  have h5 : ∀ r, r ∈ sl → is_not_temp temp r :=
    fun r h => disjoint_temps_not_temp disjoint_not_equal (hsl r h)
  have h6 : ∀ r, r ∈ dl → is_not_temp temp r :=
    fun r h => disjoint_temps_not_temp disjoint_not_equal (hdl r h)
  obtain ⟨A, B⟩ := parmove2_correctness temp sl dl hlen hnd h5 h6 e
  obtain ⟨C, D⟩ := srcs_dests_combine sl dl hlen
  have H : env_match (disjoint := disjoint) temp (sl.zip dl) (exec_seq (parmove2 temp sl dl) e)
      (weak_exec_seq weak_update (parmove2 temp sl dl) e) := by
    apply weak_exec_seq_match disjoint_sym disjoint_not_equal temp (sl.zip dl)
      (by rw [C]; exact hsl) (by rw [D]; exact hdl)
      (by rw [C, D]; exact hov) htmp weak_update weak_update_s weak_update_d
    · intro s h; rw [C]; rw [← C]; exact parmove_srcs_initial_reg_or_temp temp _ s h
    · intro d h; rw [D]; rw [← D]; exact parmove_dests_initial_reg_or_temp temp _ d h
    · intro _ _; rfl
  refine ⟨?_, fun r h1 h2 => ?_⟩
  · rw [← A]
    apply List.map_congr_left
    intro x hx
    refine (H x ?_).symm
    apply no_adherence_dst disjoint_sym temp _ (by rw [D]; exact hdl) (by rw [D]; exact hpw)
    rw [D]; exact hx
  · rw [← H r ?_]
    · exact B r (disjoint_list_notin disjoint_not_equal h1)
        (disjoint_temps_not_temp disjoint_not_equal h2)
    · intro x hx
      rw [D] at hx
      rcases hx with hx | hx
      · exact .inr (disjoint_sym _ _ (h1 x hx))
      · exact .inr (disjoint_sym _ _ (h2 x hx))

end PARMOV

end Parmov
end CC
