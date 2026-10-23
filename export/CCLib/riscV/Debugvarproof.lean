/-
  [RISC-V instance of `CCLib/backend/Debugvarproof.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness proof for the generation of debugging information for local
  variables — port of `backend/Debugvarproof.v`.

  Main result: `Debugvarproof.transf_program_correct`: if
  `Debugvar.transfProgram prog = .OK tprog`, the Linear semantics of `tprog`
  is a forward simulation of the Linear semantics of `prog`.

  Also ported: the relational characterization of the transformation
  (`match_code`, `transf_code_match`, `match_function`,
  `transf_function_match`, `find_label_match`) and the properties of
  availability sets (`wf_avail`, `set_state_1/2/3`, `wf_set_state`,
  `remove_state_1/2/3`, `wf_remove_state`, `wf_filter`, `join_1`, `join_2`,
  `wf_join`), which Rocq proves for confidence in the analysis although they
  are not used in the preservation proof.

  Differences from Rocq: `Plt` is `<` on `Positive.toNat`; `Senv.equiv` is
  the equality `senv_transf_partial`, so `external_call_symbols_preserved`
  and `eval_builtin_args_preserved` are rewrites.
-/
import CCLib.riscV.Debugvar
import CCLib.riscV.CleanupLabelsproof

namespace CC
namespace RiscV
namespace Debugvarproof

open Linear Debugvar Smallstep

/-! ### Relational characterization of the transformation -/

/-- `match_code` -/
inductive MatchCode : Linear.Code → Linear.Code → Prop where
  | nil : MatchCode [] []
  | cons (i before after c c') : MatchCode c c' →
      MatchCode (i :: c) (i :: addDeltaRanges before after c')

theorem posCompare_refl (v : Positive) : posCompare v v = .eq := by
  simp [posCompare]

/-- `diff_same` -/
theorem diff_same : ∀ s : Avail, diff s s = []
  | [] => rfl
  | (v, i) :: s => by
      simp only [diff, diff2, posCompare_refl, if_true]
      exact diff_same s

/-- `delta_state_same` -/
theorem deltaState_same (s : Option Avail) : deltaState s s = ([], []) := by
  cases s <;> simp [deltaState, diff_same]

theorem addDeltaRanges_same (s : Option Avail) (c : Linear.Code) :
    addDeltaRanges s s c = c := by
  simp [addDeltaRanges, deltaState_same]

/-- `transf_code_match` -/
theorem transf_code_match (lm : Labelmap) (c : Linear.Code) (before : Option Avail) :
    MatchCode c (transfCode lm before c) := by
  match c with
  | [] => simp only [transfCode]; exact .nil
  | i :: c =>
      have DEFAULT : ∀ before after, MatchCode (i :: c)
          (i :: addDeltaRanges before after (transfCode lm after c)) :=
        fun _ _ => .cons _ _ _ _ _ (transf_code_match lm c _)
      cases i with
      | Lgoto l =>
          cases c with
          | nil => simp only [transfCode]; exact DEFAULT _ _
          | cons j c' =>
              cases j with
              | Llabel l0 =>
                  simp only [transfCode]
                  have h := MatchCode.cons (.Llabel l0) before (getLabel l0 lm) c'
                    (transfCode lm (getLabel l0 lm) c') (transf_code_match lm c' _)
                  have h2 := MatchCode.cons (.Lgoto l) before before _ _ h
                  rwa [addDeltaRanges_same] at h2
              | _ => simp only [transfCode]; exact DEFAULT _ _
      | _ => simp only [transfCode]; exact DEFAULT _ _
termination_by c.length
decreasing_by all_goals simp_wf; all_goals omega

/-- `match_function` -/
inductive MatchFunction : Linear.Function → Linear.Function → Prop where
  | intro (f : Linear.Function) (c : Linear.Code) : MatchCode f.fn_code c →
      MatchFunction f ⟨f.fn_sig, f.fn_stacksize, c⟩

/-- `transf_function_match` -/
theorem transf_function_match {f tf : Linear.Function} (h : Debugvar.transfFunction f = .OK tf) :
    MatchFunction f tf := by
  unfold Debugvar.transfFunction at h
  split at h
  · cases h
  · cases h; exact .intro _ _ (transf_code_match _ _ _)

theorem Linear.findLabel_foldr_addEndRange (lbl : Linear.Label) (c : Linear.Code) :
    ∀ l : Avail, Linear.findLabel lbl (l.foldr addEndRange c) = Linear.findLabel lbl c
  | [] => rfl
  | _ :: l => by
      simp only [List.foldr_cons, addEndRange, Linear.findLabel, Linear.isLabel]
      exact Linear.findLabel_foldr_addEndRange lbl c l

theorem Linear.findLabel_foldr_addStartRange (lbl : Linear.Label) (c : Linear.Code) :
    ∀ l : Avail, Linear.findLabel lbl (l.foldr addStartRange c) = Linear.findLabel lbl c
  | [] => rfl
  | _ :: l => by
      simp only [List.foldr_cons, addStartRange, Linear.findLabel, Linear.isLabel]
      exact Linear.findLabel_foldr_addStartRange lbl c l

/-- `find_label_add_delta_ranges` -/
theorem find_label_add_delta_ranges (lbl : Linear.Label) (c : Linear.Code)
    (before after : Option Avail) :
    Linear.findLabel lbl (addDeltaRanges before after c) = Linear.findLabel lbl c := by
  unfold addDeltaRanges
  rw [Linear.findLabel_foldr_addEndRange, Linear.findLabel_foldr_addStartRange]

/-- `find_label_match_rec` -/
theorem find_label_match_rec {lbl : Linear.Label} {c' : Linear.Code} :
    ∀ {c tc : Linear.Code}, MatchCode c tc → Linear.findLabel lbl c = some c' →
      ∃ before after tc', Linear.findLabel lbl tc = some (addDeltaRanges before after tc') ∧
        MatchCode c' tc'
  | _, _, .nil, h => by simp [Linear.findLabel] at h
  | _, _, .cons i before after c tc hm, h => by
      simp only [Linear.findLabel] at h ⊢
      cases e : Linear.isLabel lbl i with
      | true =>
          rw [e] at h; cases h
          exact ⟨before, after, tc, rfl, hm⟩
      | false =>
          rw [e] at h
          simp only [Bool.false_eq_true, if_false]
          rw [find_label_add_delta_ranges]
          exact find_label_match_rec hm h

/-- `find_label_match` -/
theorem find_label_match {f tf : Linear.Function} {lbl : Linear.Label} {c : Linear.Code}
    (hm : MatchFunction f tf) (h : Linear.findLabel lbl f.fn_code = some c) :
    ∃ before after tc, Linear.findLabel lbl tf.fn_code = some (addDeltaRanges before after tc) ∧
      MatchCode c tc := by
  cases hm
  exact find_label_match_rec ‹_› h

/-! ### Properties of availability sets

These are not used in the semantic preservation proof, but establish some
confidence in the availability analysis. -/

/-- `avail_above` -/
def AvailAbove (v : Ident) (s : Avail) : Prop :=
  ∀ v' i', (v', i') ∈ s → v.toNat < v'.toNat

/-- `wf_avail` -/
inductive WfAvail : Avail → Prop where
  | nil : WfAvail []
  | cons (v i s) : AvailAbove v s → WfAvail s → WfAvail ((v, i) :: s)

theorem posCompare_spec (v w : Positive) :
    (posCompare v w = .eq ∧ v = w) ∨ (posCompare v w = .lt ∧ v.toNat < w.toNat) ∨
    (posCompare v w = .gt ∧ w.toNat < v.toNat) := by
  unfold posCompare
  rcases Nat.lt_trichotomy v.toNat w.toNat with h | h | h
  · exact .inr (.inl ⟨Nat.compare_eq_lt.mpr h, h⟩)
  · exact .inl ⟨by simp [h], Positive.toNat_inj h⟩
  · exact .inr (.inr ⟨Nat.compare_eq_gt.mpr h, h⟩)

theorem ne_of_toNat_lt {v w : Positive} (h : v.toNat < w.toNat) : v ≠ w := by
  rintro rfl; omega

/-- `set_state_1` -/
theorem set_state_1 (v : Ident) (i : Debuginfo) : ∀ s, (v, i) ∈ setState v i s
  | [] => by simp [setState]
  | (v', i') :: s => by
      simp only [setState]
      split
      · simp
      · simp
      · exact List.mem_cons_of_mem _ (set_state_1 v i s)

/-- `set_state_2` -/
theorem set_state_2 (v : Ident) (i : Debuginfo) (v' : Ident) (i' : Debuginfo) :
    ∀ s, v' ≠ v → (v', i') ∈ s → (v', i') ∈ setState v i s
  | [], _, h => by simp at h
  | (v1, i1) :: s, hne, h => by
      simp only [setState]
      rcases posCompare_spec v v1 with ⟨e, rfl⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact absurd rfl hne
        · exact List.mem_cons_of_mem _ h
      · exact List.mem_cons_of_mem _ h
      · rcases List.mem_cons.mp h with h | h
        · rw [h]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (set_state_2 v i v' i' s hne h)

/-- `set_state_3` -/
theorem set_state_3 (v : Ident) (i : Debuginfo) (v' : Ident) (i' : Debuginfo) :
    ∀ {s}, WfAvail s → (v', i') ∈ setState v i s →
      (v' = v ∧ i' = i) ∨ (v' ≠ v ∧ (v', i') ∈ s)
  | _, .nil, h => by simp [setState] at h; exact .inl h
  | _, .cons v0 i0 s habove hwf, h => by
      simp only [setState] at h
      rcases posCompare_spec v v0 with ⟨e, rfl⟩ | ⟨e, hlt⟩ | ⟨e, hgt⟩ <;> rw [e] at h
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨(ne_of_toNat_lt (habove _ _ h)).symm, List.mem_cons_of_mem _ h⟩
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact .inl ⟨rfl, rfl⟩
        rcases List.mem_cons.mp h with h | h
        · cases h; exact .inr ⟨(ne_of_toNat_lt hlt).symm, List.mem_cons_self ..⟩
        · exact .inr ⟨(ne_of_toNat_lt (Nat.lt_trans hlt (habove _ _ h))).symm,
            List.mem_cons_of_mem _ h⟩
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact .inr ⟨ne_of_toNat_lt hgt, List.mem_cons_self ..⟩
        · rcases set_state_3 v i v' i' hwf h with h' | ⟨hne, h'⟩
          · exact .inl h'
          · exact .inr ⟨hne, List.mem_cons_of_mem _ h'⟩

/-- `wf_set_state` -/
theorem wf_set_state (v : Ident) (i : Debuginfo) : ∀ {s}, WfAvail s → WfAvail (setState v i s)
  | _, .nil => .cons _ _ _ (fun _ _ h => by simp at h) .nil
  | _, .cons v0 i0 s habove hwf => by
      simp only [setState]
      rcases posCompare_spec v v0 with ⟨e, rfl⟩ | ⟨e, hlt⟩ | ⟨e, hgt⟩ <;> rw [e]
      · exact .cons _ _ _ habove hwf
      · refine .cons _ _ _ (fun v' i' h => ?_) (.cons _ _ _ habove hwf)
        rcases List.mem_cons.mp h with h | h
        · cases h; exact hlt
        · exact Nat.lt_trans hlt (habove _ _ h)
      · refine .cons _ _ _ (fun v' i' h => ?_) (wf_set_state v i hwf)
        rcases set_state_3 v i v' i' hwf h with ⟨rfl, _⟩ | ⟨_, h'⟩
        · exact hgt
        · exact habove _ _ h'

/-- `remove_state_1` -/
theorem remove_state_1 (v : Ident) (i : Debuginfo) :
    ∀ {s}, WfAvail s → (v, i) ∉ removeState v s
  | _, .nil => by simp [removeState]
  | _, .cons v0 i0 s habove hwf => by
      simp only [removeState]
      rcases posCompare_spec v v0 with ⟨e, rfl⟩ | ⟨e, hlt⟩ | ⟨e, hgt⟩ <;> rw [e]
      · intro h; have := habove _ _ h; omega
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h; omega
        · have := habove _ _ h; omega
      · intro h
        rcases List.mem_cons.mp h with h | h
        · cases h; omega
        · exact remove_state_1 v i hwf h

/-- `remove_state_2` -/
theorem remove_state_2 (v v' : Ident) (i' : Debuginfo) :
    ∀ s, v' ≠ v → (v', i') ∈ s → (v', i') ∈ removeState v s
  | [], _, h => h
  | (v1, i1) :: s, hne, h => by
      simp only [removeState]
      rcases posCompare_spec v v1 with ⟨e, rfl⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact absurd rfl hne
        · exact h
      · exact h
      · rcases List.mem_cons.mp h with h | h
        · rw [h]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (remove_state_2 v v' i' s hne h)

/-- `remove_state_3` -/
theorem remove_state_3 (v v' : Ident) (i' : Debuginfo) :
    ∀ {s}, WfAvail s → (v', i') ∈ removeState v s → v' ≠ v ∧ (v', i') ∈ s
  | _, .nil, h => by simp [removeState] at h
  | _, .cons v0 i0 s habove hwf, h => by
      simp only [removeState] at h
      rcases posCompare_spec v v0 with ⟨e, rfl⟩ | ⟨e, hlt⟩ | ⟨e, hgt⟩ <;> rw [e] at h
      · exact ⟨(ne_of_toNat_lt (habove _ _ h)).symm, List.mem_cons_of_mem _ h⟩
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact ⟨(ne_of_toNat_lt hlt).symm, List.mem_cons_self ..⟩
        · exact ⟨(ne_of_toNat_lt (Nat.lt_trans hlt (habove _ _ h))).symm,
            List.mem_cons_of_mem _ h⟩
      · rcases List.mem_cons.mp h with h | h
        · cases h; exact ⟨ne_of_toNat_lt hgt, List.mem_cons_self ..⟩
        · obtain ⟨hne, h'⟩ := remove_state_3 v v' i' hwf h
          exact ⟨hne, List.mem_cons_of_mem _ h'⟩

/-- `wf_remove_state` -/
theorem wf_remove_state (v : Ident) : ∀ {s}, WfAvail s → WfAvail (removeState v s)
  | _, .nil => .nil
  | _, .cons v0 i0 s habove hwf => by
      simp only [removeState]
      rcases posCompare_spec v v0 with ⟨e, rfl⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
      · exact hwf
      · exact .cons _ _ _ habove hwf
      · exact .cons _ _ _ (fun v' i' h => habove _ _ (remove_state_3 v v' i' hwf h).2)
          (wf_remove_state v hwf)

/-- `wf_filter` -/
theorem wf_filter (pred : Ident × Debuginfo → Bool) :
    ∀ {s}, WfAvail s → WfAvail (s.filter pred)
  | _, .nil => .nil
  | _, .cons v i s habove hwf => by
      simp only [List.filter_cons]
      split
      · exact .cons _ _ _ (fun v' i' h => habove _ _ (List.mem_filter.mp h).1) (wf_filter pred hwf)
      · exact wf_filter pred hwf

theorem join_nil_right : ∀ s1 : Avail, join s1 [] = []
  | [] => rfl
  | (_, _) :: _ => rfl

theorem join_eq {v1 v2 : Ident} (i1 i2 : Debuginfo) (s1 s2 : Avail) (e : posCompare v1 v2 = .eq) :
    join ((v1, i1) :: s1) ((v2, i2) :: s2) =
      if i1 = i2 then (v1, i1) :: join s1 s2 else join s1 s2 := by
  show join2 v1 i1 (join s1) ((v2, i2) :: s2) = _
  simp only [join2, e]

theorem join_lt {v1 v2 : Ident} (i1 i2 : Debuginfo) (s1 s2 : Avail) (e : posCompare v1 v2 = .lt) :
    join ((v1, i1) :: s1) ((v2, i2) :: s2) = join s1 ((v2, i2) :: s2) := by
  show join2 v1 i1 (join s1) ((v2, i2) :: s2) = _
  simp only [join2, e]

theorem join_gt {v1 v2 : Ident} (i1 i2 : Debuginfo) (s1 s2 : Avail) (e : posCompare v1 v2 = .gt) :
    join ((v1, i1) :: s1) ((v2, i2) :: s2) = join ((v1, i1) :: s1) s2 := by
  show join2 v1 i1 (join s1) ((v2, i2) :: s2) = _
  simp only [join2, e]
  rfl

/-- `join_2` -/
theorem join_2 (v : Ident) (i : Debuginfo) (s1 s2 : Avail) (hw1 : WfAvail s1) (hw2 : WfAvail s2)
    (h : (v, i) ∈ join s1 s2) : (v, i) ∈ s1 ∧ (v, i) ∈ s2 := by
  match s1, s2, hw1, hw2 with
  | _, _, .nil, _ => simp [join] at h
  | _, _, .cons v1 i1 s1 ha1 hw1, .nil => simp [join_nil_right] at h
  | _, _, .cons v1 i1 s1 ha1 hw1, .cons v2 i2 s2 ha2 hw2 =>
      rcases posCompare_spec v1 v2 with ⟨e, rfl⟩ | ⟨e, hlt⟩ | ⟨e, hgt⟩
      · rw [join_eq _ _ _ _ e] at h
        split at h
        · rename_i hi; subst hi
          rcases List.mem_cons.mp h with h | h
          · rw [h]; exact ⟨List.mem_cons_self .., List.mem_cons_self ..⟩
          · obtain ⟨h1, h2⟩ := join_2 v i s1 s2 hw1 hw2 h
            exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
        · obtain ⟨h1, h2⟩ := join_2 v i s1 s2 hw1 hw2 h
          exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
      · rw [join_lt _ _ _ _ e] at h
        obtain ⟨h1, h2⟩ := join_2 v i s1 _ hw1 (.cons _ _ _ ha2 hw2) h
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rw [join_gt _ _ _ _ e] at h
        have := join_2 v i _ s2 (.cons _ _ _ ha1 hw1) hw2 h
        exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩
termination_by s1.length + s2.length

/-- `join_1` -/
theorem join_1 (v : Ident) (i : Debuginfo) (s1 s2 : Avail) (hw1 : WfAvail s1) (hw2 : WfAvail s2)
    (h1 : (v, i) ∈ s1) (h2 : (v, i) ∈ s2) : (v, i) ∈ join s1 s2 := by
  match s1, s2, hw1, hw2 with
  | _, _, .nil, _ => simp at h1
  | _, _, .cons _ _ _ _ _, .nil => simp at h2
  | _, _, .cons v1 i1 s1 ha1 hw1, .cons v2 i2 s2 ha2 hw2 =>
      rcases posCompare_spec v1 v2 with ⟨e, rfl⟩ | ⟨e, hlt⟩ | ⟨e, hgt⟩
      · rw [join_eq _ _ _ _ e]
        rcases List.mem_cons.mp h1 with e1 | e1 <;> rcases List.mem_cons.mp h2 with e2 | e2
        · cases e1; cases e2; simp
        · cases e1; have := ha2 _ _ e2; omega
        · cases e2; have := ha1 _ _ e1; omega
        · split
          · exact List.mem_cons_of_mem _ (join_1 v i s1 s2 hw1 hw2 e1 e2)
          · exact join_1 v i s1 s2 hw1 hw2 e1 e2
      · rw [join_lt _ _ _ _ e]
        rcases List.mem_cons.mp h1 with e1 | e1
        · cases e1
          rcases List.mem_cons.mp h2 with e2 | e2
          · cases e2; omega
          · have := ha2 _ _ e2; omega
        · exact join_1 v i s1 _ hw1 (.cons _ _ _ ha2 hw2) e1 h2
      · rw [join_gt _ _ _ _ e]
        rcases List.mem_cons.mp h2 with e2 | e2
        · cases e2
          rcases List.mem_cons.mp h1 with e1 | e1
          · cases e1; omega
          · have := ha1 _ _ e1; omega
        · exact join_1 v i _ s2 (.cons _ _ _ ha1 hw1) hw2 h1 e2
termination_by s1.length + s2.length

/-- `wf_join` -/
theorem wf_join (s1 s2 : Avail) (hw1 : WfAvail s1) (hw2 : WfAvail s2) : WfAvail (join s1 s2) := by
  match s1, s2, hw1, hw2 with
  | _, _, .nil, _ => simp only [join]; exact .nil
  | _, _, .cons _ _ _ _ _, .nil => rw [join_nil_right]; exact .nil
  | _, _, .cons v1 i1 s1 ha1 hw1, .cons v2 i2 s2 ha2 hw2 =>
      rcases posCompare_spec v1 v2 with ⟨e, rfl⟩ | ⟨e, hlt⟩ | ⟨e, hgt⟩
      · rw [join_eq _ _ _ _ e]
        split
        · exact .cons _ _ _ (fun v' i' h => ha1 _ _ (join_2 v' i' s1 s2 hw1 hw2 h).1)
            (wf_join s1 s2 hw1 hw2)
        · exact wf_join s1 s2 hw1 hw2
      · rw [join_lt _ _ _ _ e]; exact wf_join s1 _ hw1 (.cons _ _ _ ha2 hw2)
      · rw [join_gt _ _ _ _ e]; exact wf_join _ s2 (.cons _ _ _ ha1 hw1) hw2
termination_by s1.length + s2.length


/-! ### Semantic preservation -/

section PRESERVATION
variable {prog tprog : Linear.Program}
  (TRANSF : Debugvar.transfProgram prog = .OK tprog)
include TRANSF

theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

theorem functions_translated {v : Val} {f : Linear.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧ Debugvar.transfFundef f = .OK tf :=
  find_funct_transf_partial TRANSF h

theorem function_ptr_translated {b : Block} {f : Linear.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧ Debugvar.transfFundef f = .OK tf :=
  find_funct_ptr_transf_partial TRANSF h

omit TRANSF in
/-- `sig_preserved` -/
theorem sig_preserved {f tf : Linear.Fundef} (h : Debugvar.transfFundef f = .OK tf) :
    Linear.funsig tf = Linear.funsig f := by
  cases f with
  | Internal f =>
      simp only [Debugvar.transfFundef, ASTFundef.transfPartial] at h
      split at h
      · rename_i tf' htf; cases h
        cases transf_function_match htf; rfl
      · cases h
  | External ef => cases h; rfl

/-- `find_function_translated` -/
theorem find_function_translated {ros : Sum Mreg Ident} {ls : LTL.Locset} {f : Linear.Fundef}
    (h : Linear.findFunction prog.globalenv ros ls = some f) :
    ∃ tf, Linear.findFunction tprog.globalenv ros ls = some tf ∧ Debugvar.transfFundef f = .OK tf := by
  cases ros with
  | inl r => exact functions_translated TRANSF h
  | inr id =>
      simp only [Linear.findFunction, symbols_preserved TRANSF] at h ⊢
      cases e : Genv.findSymbol prog.globalenv id with
      | none => rw [e] at h; cases h
      | some b => rw [e] at h; exact function_ptr_translated TRANSF h

omit TRANSF in
/-- `can_eval_safe_arg` -/
theorem can_eval_safe_arg (ge : Senv) (rs : LTL.Locset) (sp : Val) (m : Mem) :
    ∀ (a : BuiltinArg Loc), SafeBuiltinArg a → ∃ v, EvalBuiltinArg ge rs sp m a v
  | .BA x, _ => ⟨_, .BA x⟩
  | .BA_int n, _ => ⟨_, .BA_int n⟩
  | .BA_long n, _ => ⟨_, .BA_long n⟩
  | .BA_float n, _ => ⟨_, .BA_float n⟩
  | .BA_single n, _ => ⟨_, .BA_single n⟩
  | .BA_splitlong a1 a2, ⟨h1, h2⟩ => by
      obtain ⟨v1, e1⟩ := can_eval_safe_arg ge rs sp m a1 h1
      obtain ⟨v2, e2⟩ := can_eval_safe_arg ge rs sp m a2 h2
      exact ⟨_, .BA_splitlong _ _ _ _ e1 e2⟩
  | .BA_loadstack .., h => h.elim
  | .BA_addrstack .., h => h.elim
  | .BA_loadglobal .., h => h.elim
  | .BA_addrglobal .., h => h.elim
  | .BA_addptr .., h => h.elim

omit TRANSF in
theorem eval_foldr_addStartRange (ge : Linear.CGenv) (s : List Linear.Stackframe) (f : Linear.Function) (sp : Val) (c : Linear.Code) (rs : LTL.Locset) (m : Mem) :
    ∀ l : Avail, Smallstep.Star (Linear.Step  ge) (.State s f sp (l.foldr addStartRange c) rs m) E0
      (.State s f sp c rs m)
  | [] => .refl _
  | (v, ⟨a, safe⟩) :: l => by
      obtain ⟨v1, e1⟩ := can_eval_safe_arg ge.toSenv rs sp m a safe
      refine .step (.Lbuiltin _ _ _ _ _ _ _ _ _ [v1] E0 .Vundef rs m (.cons e1 .nil)
        (.intro _ _ _) rfl) (eval_foldr_addStartRange ge s f sp c rs m l) rfl

omit TRANSF in
theorem eval_foldr_addEndRange (ge : Linear.CGenv) (s : List Linear.Stackframe) (f : Linear.Function) (sp : Val) (c : Linear.Code) (rs : LTL.Locset) (m : Mem) :
    ∀ l : Avail, Smallstep.Star (Linear.Step  ge) (.State s f sp (l.foldr addEndRange c) rs m) E0
      (.State s f sp c rs m)
  | [] => .refl _
  | _ :: l =>
      .step (.Lbuiltin _ _ _ _ _ _ _ _ _ [] E0 .Vundef rs m .nil (.intro _ _ _) rfl)
        (eval_foldr_addEndRange ge s f sp c rs m l) rfl

omit TRANSF in
/-- `eval_add_delta_ranges` -/
theorem eval_add_delta_ranges (ge : Linear.CGenv) (s : List Linear.Stackframe) (f : Linear.Function) (sp : Val) (c : Linear.Code) (rs : LTL.Locset) (m : Mem)
    (before after : Option Avail) :
    Smallstep.Star (Linear.Step  ge) (.State s f sp (addDeltaRanges before after c) rs m) E0
      (.State s f sp c rs m) := by
  unfold addDeltaRanges
  exact Smallstep.star_trans (eval_foldr_addEndRange  ge s f sp _ rs m _)
    (eval_foldr_addStartRange  ge s f sp c rs m _) rfl

omit TRANSF in
/-- `match_stackframes` -/
inductive MatchStackframes : Linear.Stackframe → Linear.Stackframe → Prop where
  | intro (f sp rs c tf tc before after) : MatchFunction f tf → MatchCode c tc →
      MatchStackframes (.Stackframe f sp rs c)
        (.Stackframe tf sp rs (addDeltaRanges before after tc))

omit TRANSF in
/-- `match_states` -/
inductive MatchStates : Linear.State → Linear.State → Prop where
  | instr (s f sp c rs m tf ts tc) : ListForall2 MatchStackframes s ts →
      MatchFunction f tf → MatchCode c tc →
      MatchStates (.State s f sp c rs m) (.State ts tf sp tc rs m)
  | call (s f rs m tf ts) : ListForall2 MatchStackframes s ts → Debugvar.transfFundef f = .OK tf →
      MatchStates (.Callstate s f rs m) (.Callstate ts tf rs m)
  | ret (s rs m ts) : ListForall2 MatchStackframes s ts →
      MatchStates (.Returnstate s rs m) (.Returnstate ts rs m)

omit TRANSF in
/-- `parent_locset_match` -/
theorem parent_locset_match {s ts : List Linear.Stackframe}
    (h : ListForall2 MatchStackframes s ts) : Linear.parentLocset ts = Linear.parentLocset s := by
  cases h with
  | nil => rfl
  | cons hm _ => cases hm; rfl

omit TRANSF in
theorem matchFunction_stacksize {f tf : Linear.Function} (h : MatchFunction f tf) :
    tf.fn_stacksize = f.fn_stacksize := by cases h; rfl

/-- `transf_step_correct` -/
theorem transf_step_correct {s1 t s2} (hst : Linear.Step  prog.globalenv s1 t s2) {ts1}
    (hm : MatchStates s1 ts1) :
    ∃ ts2, Smallstep.Plus (Linear.Step  tprog.globalenv) ts1 t ts2 ∧ MatchStates s2 ts2 := by
  have hsym := symbols_preserved TRANSF
  have hsenv := senv_preserved TRANSF
  -- the generic case: one step, then the debug annotations
  have adv : ∀ {s f sp i b rs m t rs' m' ts tf before after tc},
      Linear.Step  tprog.globalenv (.State ts tf sp (i :: addDeltaRanges before after tc) rs m)
        t (.State ts tf sp (addDeltaRanges before after tc) rs' m') →
      ListForall2 MatchStackframes s ts → MatchFunction f tf → MatchCode b tc →
      ∃ ts2, Smallstep.Plus (Linear.Step  tprog.globalenv)
        (.State ts tf sp (i :: addDeltaRanges before after tc) rs m) t ts2 ∧
        MatchStates (.State s f sp b rs' m') ts2 := by
    intro s f sp i b rs m t rs' m' ts tf before after tc hstep hs hf hc
    exact ⟨_, .intro hstep (eval_add_delta_ranges  _ _ _ _ _ _ _ _ _) (by simp [E0, Eapp]),
      .instr _ _ _ _ _ _ _ _ _ hs hf hc⟩
  cases hst with
  | Lgetstack s f sp sl ofs ty dst b rs m rs' hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc => exact adv (.Lgetstack _ _ _ _ _ _ _ _ _ _ _ hrs) hs hf hc
  | Lsetstack s f sp src sl ofs ty b rs m rs' hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc => exact adv (.Lsetstack _ _ _ _ _ _ _ _ _ _ _ hrs) hs hf hc
  | Lop s f sp op args res b rs m v rs' hv hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              refine adv (.Lop _ _ _ _ _ _ _ _ _ v _ ?_ hrs) hs hf hc
              rw [Op.evalOperation_preserved prog.globalenv tprog.globalenv hsym]; exact hv
  | Lload s f sp chunk addr args dst b rs m a v rs' ha hv hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              refine adv (.Lload _ _ _ _ _ _ _ _ _ _ a v _ ?_ hv hrs) hs hf hc
              rw [Op.evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact ha
  | Lstore s f sp chunk addr args src b rs m m' a rs' ha hv hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              refine adv (.Lstore _ _ _ _ _ _ _ _ _ _ m' a _ ?_ hv hrs) hs hf hc
              rw [Op.evalAddressing_preserved prog.globalenv tprog.globalenv hsym]; exact ha
  | Lcall s f sp sig ros b rs m f' hf' hsig =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              obtain ⟨tf', h1, h2⟩ := find_function_translated TRANSF hf'
              exact ⟨_, Smallstep.plus_one (.Lcall _ _ _ _ _ _ _ _ _ h1 (by rw [sig_preserved h2]; exact hsig)),
                .call _ _ _ _ _ _ (.cons (.intro _ _ _ _ _ _ _ _ hf hc) hs) h2⟩
  | Ltailcall s f stk sig ros b rs m rs' f' m' hrs hf' hsig hfree =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              obtain ⟨tf', h1, h2⟩ := find_function_translated TRANSF hf'
              refine ⟨_, Smallstep.plus_one (.Ltailcall _ _ _ _ _ _ _ _ rs' _ m'
                (by rw [parent_locset_match hs]; exact hrs) h1
                (by rw [sig_preserved h2]; exact hsig)
                (by rw [matchFunction_stacksize hf]; exact hfree)),
                .call _ _ _ _ _ _ hs h2⟩
  | Lbuiltin s f sp rs m ef args res b vargs t vres rs' m' hargs hec hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              refine ⟨_, .intro (.Lbuiltin _ _ _ _ _ _ _ _ _ vargs t vres _ m' ?_ ?_ hrs)
                (eval_add_delta_ranges  _ _ _ _ _ _ _ _ _) (by simp [E0, Eapp]),
                .instr _ _ _ _ _ _ _ _ _ hs hf hc⟩
              · rw [hsenv]; exact hargs
              · rw [hsenv]; exact hec
  | Llabel s f sp lbl b rs m =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc => exact adv (.Llabel _ _ _ _ _ _ _) hs hf hc
  | Lgoto s f sp lbl b rs m b' hfl =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              obtain ⟨before', after', tc', h1, h2⟩ := find_label_match hf hfl
              exact ⟨_, .intro (.Lgoto _ _ _ _ _ _ _ _ h1)
                (eval_add_delta_ranges  _ _ _ _ _ _ _ _ _) rfl,
                .instr _ _ _ _ _ _ _ _ _ hs hf h2⟩
  | Lcond_true s f sp cond args lbl b rs m rs' b' hc' hrs hfl =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              obtain ⟨before', after', tc', h1, h2⟩ := find_label_match hf hfl
              exact ⟨_, .intro (.Lcond_true _ _ _ _ _ _ _ _ _ _ _ hc' hrs h1)
                (eval_add_delta_ranges  _ _ _ _ _ _ _ _ _) rfl,
                .instr _ _ _ _ _ _ _ _ _ hs hf h2⟩
  | Lcond_false s f sp cond args lbl b rs m rs' hc' hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              exact adv (.Lcond_false _ _ _ _ _ _ _ _ _ _ hc' hrs) hs hf hc
  | Ljumptable s f sp arg tbl b rs m n lbl b' rs' hn hl hfl hrs =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              obtain ⟨before', after', tc', h1, h2⟩ := find_label_match hf hfl
              exact ⟨_, .intro (.Ljumptable _ _ _ _ _ _ _ _ n lbl _ _ hn hl h1 hrs)
                (eval_add_delta_ranges  _ _ _ _ _ _ _ _ _) rfl,
                .instr _ _ _ _ _ _ _ _ _ hs hf h2⟩
  | Lreturn s f stk b rs m m' hfree =>
      cases hm with
      | instr _ _ _ _ _ _ tf ts tc hs hf hc =>
          cases hc with
          | cons _ before after _ tc hc =>
              refine ⟨_, Smallstep.plus_one (.Lreturn _ _ _ _ _ _ _
                (by rw [matchFunction_stacksize hf]; exact hfree)), ?_⟩
              rw [parent_locset_match hs]
              exact .ret _ _ _ _ hs
  | function_internal s f rs m rs' m' stk halloc hrs =>
      cases hm with
      | call _ _ _ _ tf ts hs htf =>
          simp only [Debugvar.transfFundef, ASTFundef.transfPartial] at htf
          split at htf
          · rename_i tf' htf'
            cases htf
            have hmf := transf_function_match htf'
            cases hmf with
            | intro _ hc =>
                exact ⟨_, Smallstep.plus_one (.function_internal _ _ _ _ _ _ _ halloc hrs),
                  .instr _ _ _ _ _ _ _ _ _ hs (.intro _ _ hc) hc⟩
          · cases htf
  | function_external s ef args res rs1 rs2 m t m' hargs hec hrs =>
      cases hm with
      | call _ _ _ _ tf ts hs htf =>
          cases htf
          refine ⟨_, Smallstep.plus_one (.function_external _ _ _ _ _ _ _ _ _ hargs ?_ hrs), .ret _ _ _ _ hs⟩
          rw [hsenv]; exact hec
  | «return» s f sp rs0 c rs m =>
      cases hm with
      | ret _ _ _ ts hs =>
          cases hs with
          | cons hf hs =>
              cases hf with
              | intro _ _ _ _ tf tc before after hmf hmc =>
                  exact ⟨_, .intro (.return _ _ _ _ _ _ _)
                    (eval_add_delta_ranges  _ _ _ _ _ _ _ _ _) rfl,
                    .instr _ _ _ _ _ _ _ _ _ hs hmf hmc⟩

/-- `transf_initial_states` -/
theorem transf_initial_states {st1 : Linear.State} (h : Linear.InitialState prog st1) :
    ∃ st2, Linear.InitialState tprog st2 ∧ MatchStates st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
      obtain ⟨tf, h1, h2⟩ := function_ptr_translated TRANSF hf
      refine ⟨_, .intro b tf m0 ?_ ?_ h1 ?_, .call _ _ _ _ _ _ .nil h2⟩
      · exact (init_mem_transf_partial TRANSF).trans hm
      · rw [(match_transform_partial_program TRANSF).main_eq, symbols_preserved TRANSF]; exact hs
      · rw [sig_preserved h2]; exact hsig

omit TRANSF in
/-- `transf_final_states` -/
theorem transf_final_states {st1 st2 : Linear.State} {r : Integers.Int} (hm : MatchStates st1 st2)
    (h : Linear.FinalState st1 r) : Linear.FinalState st2 r := by
  cases h with
  | intro rs m retcode hr =>
      cases hm with
      | ret _ _ _ ts hs =>
          cases hs
          exact .intro _ _ _ hr

/-- `transf_program_correct`: the generation of debugging information
    preserves the semantics of Linear programs (forward simulation). -/
theorem transf_program_correct :
    Smallstep.ForwardSimulation (Linear.semantics  prog) (Linear.semantics  tprog) :=
  Smallstep.forward_simulation_plus (L1 := Linear.semantics  prog)
    (L2 := Linear.semantics  tprog) MatchStates
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved TRANSF])
    (fun _ h => transf_initial_states TRANSF h)
    (fun _ _ _ hm h => transf_final_states hm h)
    (fun _ _ _ hst _ hm => transf_step_correct  TRANSF hst hm)

end PRESERVATION

end Debugvarproof
end RiscV
end CC
