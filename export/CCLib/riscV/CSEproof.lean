/-
  [RISC-V instance of `CCLib/backend/CSEproof.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness proof for common subexpression elimination — port of
  `backend/CSEproof.v`, part 1: soundness of the basic operations over value
  numberings (`wf_equation_incr`, section `EXTEN`, `valnum_reg_holds`,
  `valnum_regs_holds`, `valnum_builtin_arg(s)_holds`,
  `eval_builtin_args_trivial`, `find_valnum_rhs(')_charact`,
  `find_valnum_num_charact`, `reg_valnum_sound`, `regs_valnums_sound`,
  `find_rhs_sound`, `forget_reg_charact`, `update_reg_charact`,
  `rhs_eval_to_inj`, `add_rhs_holds`, `add_op_holds`, `add_load_holds`,
  `add_builtin_holds`, `set_unknown_holds`, `set_res_unknown_holds`,
  `kill_eqs_charact`, `kill_equations_hold`, `kill_all_loads_hold`,
  `kill_cheap_computations_hold`).

  The remaining parts are in `CSEproofMem.lean` (stores and `memcpy`),
  `CSEproofReduce.lean` (`reduce`, `analysis_correct_*`) and
  `CSEproofStep.lean` (the simulation).
-/
import CCLib.riscV.CSE
import CCLib.riscV.OpTheory

namespace CC
namespace RiscV


/-- `Events.builtin_args_depends_on_memory_correct` -/
theorem builtinArgsDependsOnMemory_correct {A : Type} (m' : Mem) {ge : Senv} {e : A → Val}
    {sp m} : ∀ {al : List (BuiltinArg A)} {vl : List Val}, EvalBuiltinArgs ge e sp m al vl →
    al.any builtinArgDependsOnMemory = false → EvalBuiltinArgs ge e sp m' al vl
  | [], _, .nil, _ => .nil
  | _ :: _, _, .cons h hl, hd => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hd
    exact .cons (builtinArgDependsOnMemory_correct m' h hd.1)
      (builtinArgsDependsOnMemory_correct m' hl hd.2)

namespace CSEproof

open ValueDomain ValueAnalysis RTL CSEdomain CSE Op

/-! ## Value numbers -/

theorem pos_lt_def {p q : Positive} : p < q ↔ p.toNat < q.toNat := Iff.rfl
theorem pos_le_def {p q : Positive} : p ≤ q ↔ p.toNat ≤ q.toNat := Iff.rfl

/-- `CSEproof.wf_equation_incr` -/
theorem wf_equation_incr {next1 next2 : Valnum} {e : Equation} (h : WfEquation next1 e)
    (hle : next1 ≤ next2) : WfEquation next2 e := by
  cases e with
  | Eq l str r =>
    obtain ⟨h1, h2⟩ := h
    rw [pos_le_def] at hle
    exact ⟨by rw [pos_lt_def] at *; omega, fun v hv => by
      have := h2 v hv; rw [pos_lt_def] at *; omega⟩

/-- `CSEproof.valu_agree` -/
def ValuAgree (valu1 valu2 : Valuation) (upto : Valnum) : Prop :=
  ∀ v, v < upto → valu2 v = valu1 v

/-- `CSEproof.valu_agree_refl` -/
theorem valu_agree_refl (valu : Valuation) (upto : Valnum) : ValuAgree valu valu upto :=
  fun _ _ => rfl

section EXTEN
variable {valu1 : Valuation} {upto : Valnum} {valu2 : Valuation}
  (AGREE : ValuAgree valu1 valu2 upto) {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset} {m : Mem}
include AGREE

/-- `CSEproof.valnums_val_exten` -/
theorem valnums_val_exten (vl : List Valnum) (h : ∀ v, v ∈ vl → v < upto) :
    vl.map valu2 = vl.map valu1 :=
  List.map_congr_left fun v hv => AGREE v (h v hv)

/-- `CSEproof.builtin_arg_val_exten` -/
theorem builtin_arg_val_exten {gs : Senv} {a : BuiltinArg Valnum} {v : Val}
    (h : EvalBuiltinArg gs valu1 sp m a v) (hp : ∀ vn, vn ∈ BuiltinArg.params a → vn < upto) :
    EvalBuiltinArg gs valu2 sp m a v := by
  induction h with
  | BA x =>
    rw [← AGREE x (hp x (by simp [BuiltinArg.params]))]; exact .BA x
  | BA_int n => exact .BA_int n
  | BA_long n => exact .BA_long n
  | BA_float n => exact .BA_float n
  | BA_single n => exact .BA_single n
  | BA_loadstack chunk ofs v hl => exact .BA_loadstack _ _ _ hl
  | BA_addrstack ofs => exact .BA_addrstack _
  | BA_loadglobal chunk id ofs v hl => exact .BA_loadglobal _ _ _ _ hl
  | BA_addrglobal id ofs => exact .BA_addrglobal _ _
  | BA_splitlong hi lo vhi vlo _ _ IH1 IH2 =>
    exact .BA_splitlong _ _ _ _ (IH1 fun vn h => hp vn (by simp [BuiltinArg.params, h]))
      (IH2 fun vn h => hp vn (by simp [BuiltinArg.params, h]))
  | BA_addptr a1 a2 v1 v2 _ _ IH1 IH2 =>
    exact .BA_addptr _ _ _ _ (IH1 fun vn h => hp vn (by simp [BuiltinArg.params, h]))
      (IH2 fun vn h => hp vn (by simp [BuiltinArg.params, h]))

/-- `CSEproof.builtin_args_val_exten` -/
theorem builtin_args_val_exten {gs : Senv} :
    ∀ {al : List (BuiltinArg Valnum)} {vl : List Val}, EvalBuiltinArgs gs valu1 sp m al vl →
    (∀ vn, vn ∈ BuiltinArg.paramsList al → vn < upto) → EvalBuiltinArgs gs valu2 sp m al vl
  | [], _, .nil, _ => .nil
  | _ :: _, _, .cons h hl, hp =>
    .cons (builtin_arg_val_exten AGREE h fun vn hv =>
        hp vn (by simp [BuiltinArg.paramsList] at hv ⊢; exact .inl hv))
      (builtin_args_val_exten hl fun vn hv =>
        hp vn (by simp [BuiltinArg.paramsList] at hv ⊢; exact .inr hv))

/-- `CSEproof.rhs_eval_to_exten` -/
theorem rhs_eval_to_exten {r : Rhs} {v : Val} (h : RhsEvalTo valu1 ge sp m r v)
    (hp : ∀ v, v ∈ valnumsRhs r → v < upto) : RhsEvalTo valu2 ge sp m r v := by
  cases h with
  | op_eval_to op vl v he =>
    exact .op_eval_to _ _ _ (by rw [valnums_val_exten AGREE vl hp]; exact he)
  | load_eval_to chunk addr vl a v p ha hl =>
    exact .load_eval_to _ _ _ _ _ _ (by rw [valnums_val_exten AGREE vl hp]; exact ha) hl
  | builtin_eval_to bf args vargs v ha hb =>
    exact .builtin_eval_to _ _ _ _ (builtin_args_val_exten AGREE ha hp) hb

/-- `CSEproof.rhs_valid_exten` -/
theorem rhs_valid_exten {r : Rhs} (h : RhsValid valu1 ge sp r)
    (hp : ∀ v, v ∈ valnumsRhs r → v < upto) : RhsValid valu2 ge sp r := by
  cases h with
  | op_valid => exact .op_valid _ _ _
  | load_valid sp chunk addr vl p b ofs bc ha hpm hg hs =>
    exact .load_valid _ _ _ _ _ _ _ bc (by rw [valnums_val_exten AGREE vl hp]; exact ha) hpm hg hs
  | builtin_valid => exact .builtin_valid _ _ _

/-- `CSEproof.equation_holds_exten` -/
theorem equation_holds_exten {e : Equation} (h : EquationHolds valu1 ge sp m e)
    (hw : WfEquation upto e) : EquationHolds valu2 ge sp m e := by
  cases e with
  | Eq l str r =>
    obtain ⟨hl, hr⟩ := hw
    cases h with
    | eq_holds_strict _ _ he hv =>
      refine .eq_holds_strict _ _ ?_ (rhs_valid_exten AGREE hv hr)
      rw [AGREE l hl]; exact rhs_eval_to_exten AGREE he hr
    | eq_holds_lessdef _ _ v he hld hv =>
      refine .eq_holds_lessdef _ _ v (rhs_eval_to_exten AGREE he hr) ?_ (rhs_valid_exten AGREE hv hr)
      rw [AGREE l hl]; exact hld

/-- `CSEproof.numbering_holds_exten` -/
theorem numbering_holds_exten {n : Numbering} (h : NumberingHolds valu1 ge sp rs m n)
    (hle : n.num_next ≤ upto) : NumberingHolds valu2 ge sp rs m n := by
  obtain ⟨W, E, R⟩ := h
  refine ⟨W, fun eq heq => equation_holds_exten AGREE (E eq heq)
    (wf_equation_incr (W.wf_num_eqs eq heq) hle), fun r v hr => ?_⟩
  rw [R r v hr, AGREE v ?_]
  have := W.wf_num_reg r v hr
  rw [pos_lt_def, pos_le_def] at *; omega

end EXTEN

/-! ### Positive arithmetic -/

theorem pos_ne_of_lt {p q : Positive} (h : p < q) : p ≠ q := fun e => by
  subst e; rw [pos_lt_def] at h; omega
theorem pos_lt_succ_self (p : Positive) : p < p.succ := by
  rw [pos_lt_def, Positive.toNat_succ]; omega
theorem pos_lt_succ_of_lt {p q : Positive} (h : p < q) : p < q.succ := by
  rw [pos_lt_def, Positive.toNat_succ] at *; omega
theorem pos_le_succ (p : Positive) : p ≤ p.succ := by
  rw [pos_le_def, Positive.toNat_succ]; omega
theorem pos_le_refl (p : Positive) : p ≤ p := by rw [pos_le_def]; omega
theorem pos_le_trans {p q r : Positive} (h1 : p ≤ q) (h2 : q ≤ r) : p ≤ r := by
  rw [pos_le_def] at *; omega
theorem pos_lt_of_lt_of_le {p q r : Positive} (h1 : p < q) (h2 : q ≤ r) : p < r := by
  rw [pos_lt_def, pos_le_def] at *; omega

/-! ### Value numbering of registers and builtin arguments -/

section HOLDS
variable {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset} {m : Mem}

/-- `CSEproof.valnum_reg_holds` -/
theorem valnum_reg_holds {valu1 : Valuation} {n : Numbering} {r : Reg} {n' : Numbering}
    {v : Valnum} (h : NumberingHolds valu1 ge sp rs m n) (hv : valnumReg n r = (n', v)) :
    ∃ valu2, NumberingHolds valu2 ge sp rs m n' ∧ rs.get r = valu2 v ∧
      ValuAgree valu1 valu2 n.num_next ∧ v < n'.num_next ∧ n.num_next ≤ n'.num_next := by
  obtain ⟨W, E, R⟩ := h
  unfold valnumReg at hv
  cases hnr : n.num_reg.get r with
  | some v' =>
    rw [hnr] at hv; cases hv
    exact ⟨valu1, ⟨W, E, R⟩, R r _ hnr, valu_agree_refl _ _, W.wf_num_reg r _ hnr, pos_le_refl _⟩
  | none =>
    rw [hnr] at hv; cases hv
    let valu2 : Valuation := fun vn => if vn = n.num_next then rs.get r else valu1 vn
    have AG : ValuAgree valu1 valu2 n.num_next := fun v hv => if_neg (pos_ne_of_lt hv)
    refine ⟨valu2, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, by simp [valu2], AG, pos_lt_succ_self _,
      pos_le_succ _⟩
    · intro e he
      exact wf_equation_incr (W.wf_num_eqs e he) (pos_le_succ _)
    · intro r0 v0 h0
      simp only [PTree.gsspec] at h0
      split at h0
      · cases h0; exact pos_lt_succ_self _
      · exact pos_lt_succ_of_lt (W.wf_num_reg r0 v0 h0)
    · intro r0 v0 h0
      simp only [PMap.gsspec] at h0
      split at h0
      · rename_i hv0
        simp only [List.mem_singleton] at h0
        subst h0 hv0; simp
      · have := W.wf_num_val r0 v0 h0
        have hne : r0 ≠ r := fun e => by subst e; rw [hnr] at this; cases this
        simp only [PTree.gsspec, if_neg hne]; exact this
    · intro eq heq
      exact equation_holds_exten AG (E eq heq) (W.wf_num_eqs eq heq)
    · intro r0 v0 h0
      simp only [PTree.gsspec] at h0
      split at h0
      · rename_i e; cases h0; subst e; simp [valu2]
      · rw [R r0 v0 h0]
        exact (AG v0 (W.wf_num_reg r0 v0 h0)).symm

/-- `CSEproof.valnum_regs_holds` -/
theorem valnum_regs_holds : ∀ (rl : List Reg) {valu1 : Valuation} {n n' : Numbering}
    {vl : List Valnum}, NumberingHolds valu1 ge sp rs m n → valnumRegs n rl = (n', vl) →
    ∃ valu2, NumberingHolds valu2 ge sp rs m n' ∧ rs.getList rl = vl.map valu2 ∧
      ValuAgree valu1 valu2 n.num_next ∧ (∀ v, v ∈ vl → v < n'.num_next) ∧
      n.num_next ≤ n'.num_next
  | [], valu1, n, n', vl, h, hv => by
    simp only [valnumRegs, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨valu1, h, rfl, valu_agree_refl _ _, by simp, pos_le_refl _⟩
  | r :: rl, valu1, n, n', vl, h, hv => by
    simp only [valnumRegs] at hv
    generalize e1 : valnumReg n r = p1 at hv
    obtain ⟨n1, v1⟩ := p1
    generalize e2 : valnumRegs n1 rl = p2 at hv
    obtain ⟨n2, vs⟩ := p2
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨valu2, A, B, C, D, E⟩ := valnum_reg_holds h e1
    obtain ⟨valu3, P, Q, R, S, T⟩ := valnum_regs_holds rl A e2
    refine ⟨valu3, P, ?_, fun v hv => ?_, fun v hv => ?_, pos_le_trans E T⟩
    · simp only [Regmap.getList, List.map_cons] at Q ⊢
      rw [Q, B, R v1 D]
    · rw [R v (pos_lt_of_lt_of_le hv E), C v hv]
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact pos_lt_of_lt_of_le D T
      · exact S v hv

/-- `CSEproof.valnum_builtin_arg_holds` -/
theorem valnum_builtin_arg_holds {a : BuiltinArg Reg} {v : Val}
    (h : EvalBuiltinArg (Genv.toSenv ge) (fun r => rs.get r) sp m a v) :
    ∀ {valu1 : Valuation} {n n' : Numbering} {a' : BuiltinArg Valnum},
    NumberingHolds valu1 ge sp rs m n → valnumBuiltinArg n a = (n', a') →
    ∃ valu2, NumberingHolds valu2 ge sp rs m n' ∧
      EvalBuiltinArg (Genv.toSenv ge) valu2 sp m a' v ∧
      ValuAgree valu1 valu2 n.num_next ∧
      (∀ vn, vn ∈ BuiltinArg.params a' → vn < n'.num_next) ∧ n.num_next ≤ n'.num_next := by
  induction h
  case BA x =>
    intro valu1 n n' a' NH VB
    simp only [valnumBuiltinArg] at VB
    generalize e1 : valnumReg n x = p1 at VB
    obtain ⟨n1, vn⟩ := p1
    simp only [Prod.mk.injEq] at VB
    obtain ⟨rfl, rfl⟩ := VB
    obtain ⟨valu2, A, B, C, D, E⟩ := valnum_reg_holds NH e1
    refine ⟨valu2, A, ?_, C, fun vn' h => ?_, E⟩
    · rw [B]; exact .BA _
    · simp only [BuiltinArg.params, List.mem_singleton] at h; subst h; exact D
  case BA_splitlong hi lo vhi vlo _ _ IH1 IH2 =>
    intro valu1 n n' a' NH VB
    simp only [valnumBuiltinArg] at VB
    generalize e1 : valnumBuiltinArg n hi = p1 at VB
    obtain ⟨n1, hi'⟩ := p1
    generalize e2 : valnumBuiltinArg n1 lo = p2 at VB
    obtain ⟨n2, lo'⟩ := p2
    simp only [Prod.mk.injEq] at VB
    obtain ⟨rfl, rfl⟩ := VB
    obtain ⟨valu2, A, B, C, D, E⟩ := IH1 NH e1
    obtain ⟨valu3, P, Q, R, S, T⟩ := IH2 A e2
    refine ⟨valu3, P, .BA_splitlong _ _ _ _ (builtin_arg_val_exten R B D) Q,
      fun v hv => ?_, fun vn h => ?_, pos_le_trans E T⟩
    · rw [R v (pos_lt_of_lt_of_le hv E), C v hv]
    · simp only [BuiltinArg.params, List.mem_append] at h
      rcases h with h | h
      · exact pos_lt_of_lt_of_le (D vn h) T
      · exact S vn h
  case BA_addptr a1 a2 v1 v2 _ _ IH1 IH2 =>
    intro valu1 n n' a' NH VB
    simp only [valnumBuiltinArg] at VB
    generalize e1 : valnumBuiltinArg n a1 = p1 at VB
    obtain ⟨n1, a1'⟩ := p1
    generalize e2 : valnumBuiltinArg n1 a2 = p2 at VB
    obtain ⟨n2, a2'⟩ := p2
    simp only [Prod.mk.injEq] at VB
    obtain ⟨rfl, rfl⟩ := VB
    obtain ⟨valu2, A, B, C, D, E⟩ := IH1 NH e1
    obtain ⟨valu3, P, Q, R, S, T⟩ := IH2 A e2
    refine ⟨valu3, P, .BA_addptr _ _ _ _ (builtin_arg_val_exten R B D) Q,
      fun v hv => ?_, fun vn h => ?_, pos_le_trans E T⟩
    · rw [R v (pos_lt_of_lt_of_le hv E), C v hv]
    · simp only [BuiltinArg.params, List.mem_append] at h
      rcases h with h | h
      · exact pos_lt_of_lt_of_le (D vn h) T
      · exact S vn h
  all_goals
    intro valu1 n n' a' NH VB
    simp only [valnumBuiltinArg, Prod.mk.injEq] at VB
    obtain ⟨rfl, rfl⟩ := VB
    refine ⟨valu1, NH, ?_, valu_agree_refl _ _, fun vn h => by simp [BuiltinArg.params] at h,
      pos_le_refl _⟩
    constructor <;> assumption

/-- `CSEproof.valnum_builtin_args_holds` -/
theorem valnum_builtin_args_holds :
    ∀ {al : List (BuiltinArg Reg)} {vl : List Val},
    EvalBuiltinArgs (Genv.toSenv ge) (fun r => rs.get r) sp m al vl →
    ∀ {valu1 : Valuation} {n n' : Numbering} {al' : List (BuiltinArg Valnum)},
    NumberingHolds valu1 ge sp rs m n → valnumBuiltinArgs n al = (n', al') →
    ∃ valu2, NumberingHolds valu2 ge sp rs m n' ∧
      EvalBuiltinArgs (Genv.toSenv ge) valu2 sp m al' vl ∧
      ValuAgree valu1 valu2 n.num_next ∧
      (∀ vn, vn ∈ BuiltinArg.paramsList al' → vn < n'.num_next) ∧ n.num_next ≤ n'.num_next
  | [], _, .nil, valu1, n, n', al', NH, VB => by
    simp only [valnumBuiltinArgs, Prod.mk.injEq] at VB
    obtain ⟨rfl, rfl⟩ := VB
    exact ⟨valu1, NH, .nil, valu_agree_refl _ _, by simp [BuiltinArg.paramsList], pos_le_refl _⟩
  | a1 :: al, _, .cons h1 hl, valu1, n, n', al', NH, VB => by
    simp only [valnumBuiltinArgs] at VB
    generalize e1 : valnumBuiltinArg n a1 = p1 at VB
    obtain ⟨n1, a1'⟩ := p1
    generalize e2 : valnumBuiltinArgs n1 al = p2 at VB
    obtain ⟨n2, al''⟩ := p2
    simp only [Prod.mk.injEq] at VB
    obtain ⟨rfl, rfl⟩ := VB
    obtain ⟨valu2, A, B, C, D, E⟩ := valnum_builtin_arg_holds h1 NH e1
    obtain ⟨valu3, P, Q, R, S, T⟩ := valnum_builtin_args_holds hl A e2
    refine ⟨valu3, P, .cons (builtin_arg_val_exten R B D) Q, fun v hv => ?_, fun vn h => ?_,
      pos_le_trans E T⟩
    · rw [R v (pos_lt_of_lt_of_le hv E), C v hv]
    · simp only [BuiltinArg.paramsList, List.flatMap_cons, List.mem_append] at h
      rcases h with h | h
      · exact pos_lt_of_lt_of_le (D vn h) T
      · exact S vn h

/-- `CSEproof.eval_builtin_args_trivial` -/
theorem eval_builtin_args_trivial : ∀ (rl : List Reg),
    EvalBuiltinArgs (Genv.toSenv ge) (fun r => rs.get r) sp m (rl.map .BA) (rs.getList rl)
  | [] => .nil
  | r :: rl => .cons (.BA r) (eval_builtin_args_trivial rl)

end HOLDS

/-! ### Lookups -/

/-- `CSEproof.find_valnum_rhs_charact` -/
theorem find_valnum_rhs_charact (rh : Rhs) (v : Valnum) : ∀ (eqs : List Equation),
    findValnumRhs rh eqs = some v → ∃ rh', Equation.Eq v true rh' ∈ eqs ∧ RhsCompat rh rh'
  | [], h => by cases h
  | .Eq v' str r :: eqs, h => by
    simp only [findValnumRhs] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨rfl, hc2⟩ := hc
      cases h
      exact ⟨r, List.mem_cons_self .., compatRhs_sound hc2⟩
    · obtain ⟨rh', A, B⟩ := find_valnum_rhs_charact rh v eqs h
      exact ⟨rh', List.mem_cons_of_mem _ A, B⟩

/-- `CSEproof.find_valnum_rhs'_charact` -/
theorem find_valnum_rhs'_charact (rh : Rhs) (v : Valnum) : ∀ (eqs : List Equation),
    findValnumRhs' rh eqs = some v →
    ∃ strict rh', Equation.Eq v strict rh' ∈ eqs ∧ RhsCompat rh rh'
  | [], h => by cases h
  | .Eq v' str r :: eqs, h => by
    simp only [findValnumRhs'] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨str, r, List.mem_cons_self .., compatRhs_sound hc⟩
    · obtain ⟨s, rh', A, B⟩ := find_valnum_rhs'_charact rh v eqs h
      exact ⟨s, rh', List.mem_cons_of_mem _ A, B⟩

/-- `CSEproof.find_valnum_num_charact` -/
theorem find_valnum_num_charact (v : Valnum) (r : Rhs) : ∀ (eqs : List Equation),
    findValnumNum v eqs = some r → Equation.Eq v true r ∈ eqs
  | [], h => by cases h
  | .Eq v' str r' :: eqs, h => by
    simp only [findValnumNum] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      cases h; obtain ⟨rfl, rfl⟩ := hc
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (find_valnum_num_charact v r eqs h)

section HOLDS2
variable {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset} {m : Mem}

/-- `CSEproof.reg_valnum_sound` -/
theorem reg_valnum_sound {n : Numbering} {v : Valnum} {r : Reg} {valu : Valuation}
    (h : regValnum n v = some r) (NH : NumberingHolds valu ge sp rs m n) : rs.get r = valu v := by
  unfold regValnum at h
  cases e : n.num_val.get v with
  | nil => rw [e] at h; cases h
  | cons r1 rl =>
    rw [e] at h; cases h
    exact NH.num_holds_reg r v (NH.num_holds_wf.wf_num_val r v (by rw [e]; exact List.mem_cons_self ..))

/-- `CSEproof.regs_valnums_sound` -/
theorem regs_valnums_sound {n : Numbering} {valu : Valuation}
    (NH : NumberingHolds valu ge sp rs m n) : ∀ {vl : List Valnum} {rl : List Reg},
    regsValnums n vl = some rl → rs.getList rl = vl.map valu
  | [], rl, h => by simp only [regsValnums, Option.some.injEq] at h; subst h; rfl
  | a :: vl, rl, h => by
    simp only [regsValnums] at h
    cases e1 : regValnum n a with
    | none => rw [e1] at h; cases h
    | some r1 =>
      cases e2 : regsValnums n vl with
      | none => rw [e1, e2] at h; cases h
      | some rl1 =>
        rw [e1, e2] at h; cases h
        simp only [Regmap.getList, List.map_cons] at *
        rw [reg_valnum_sound e1 NH]
        exact congrArg _ (regs_valnums_sound NH e2)

/-- `CSEdomain.rhs_compat_sym` -/
theorem rhsCompat_symm {r1 r2 : Rhs} (h : RhsCompat r1 r2) : RhsCompat r2 r1 := by
  cases h
  · exact .op _ _
  · exact .load _ _ _ _ _
  · exact .builtin _ _

/-- `CSEproof.find_rhs_sound` -/
theorem find_rhs_sound {n : Numbering} {rh : Rhs} {r : Reg} {valu : Valuation}
    (h : findRhs n rh = some r) (NH : NumberingHolds valu ge sp rs m n) :
    ∃ v, RhsEvalTo valu ge sp m rh v ∧ Val.Lessdef v (rs.get r) := by
  unfold findRhs at h
  cases e : findValnumRhs' rh n.num_eqs with
  | none => rw [e] at h; cases h
  | some vres =>
    rw [e] at h
    obtain ⟨strict, rh', IN, COMPAT⟩ := find_valnum_rhs'_charact rh vres n.num_eqs e
    rw [reg_valnum_sound h NH]
    cases NH.num_holds_eq _ IN with
    | eq_holds_strict _ _ he _ => exact ⟨_, rhsEvalTo_compat he (rhsCompat_symm COMPAT), .refl _⟩
    | eq_holds_lessdef _ _ v he hld _ => exact ⟨v, rhsEvalTo_compat he (rhsCompat_symm COMPAT), hld⟩

/-- `CSEproof.forget_reg_charact` -/
theorem forget_reg_charact {n : Numbering} {rd r : Reg} {v : Valnum} (W : WfNumbering n)
    (h : r ∈ (forgetReg n rd).get v) : r ≠ rd ∧ r ∈ n.num_val.get v := by
  unfold forgetReg at h
  cases hg : n.num_reg.get rd with
  | none =>
    rw [hg] at h
    refine ⟨fun e => ?_, h⟩
    subst e; rw [W.wf_num_val r v h] at hg; cases hg
  | some vd =>
    rw [hg] at h
    rw [PMap.gsspec] at h
    split at h
    · rename_i hv
      subst hv
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at h
      exact ⟨h.2, h.1⟩
    · rename_i hv
      refine ⟨fun e => ?_, h⟩
      subst e; rw [W.wf_num_val r v h] at hg; cases hg; exact hv rfl

/-- `CSEproof.update_reg_charact` -/
theorem update_reg_charact {n : Numbering} {rd : Reg} {vd : Valnum} {r : Reg} {v : Valnum}
    (W : WfNumbering n) (h : r ∈ (updateReg n rd vd).get v) :
    (n.num_reg.set rd vd).get r = some v := by
  unfold updateReg at h
  simp only [PMap.gsspec] at h
  split at h
  · rename_i hv
    subst hv
    rcases List.mem_cons.mp h with h | h
    · subst h; simp
    · obtain ⟨A, B⟩ := forget_reg_charact W h
      rw [PTree.gso _ _ _ _ (Ne.symm A)]; exact W.wf_num_val r _ B
  · obtain ⟨A, B⟩ := forget_reg_charact W h
    rw [PTree.gso _ _ _ _ (Ne.symm A)]; exact W.wf_num_val r _ B

/-- `CSEproof.rhs_eval_to_inj` -/
theorem rhs_eval_to_inj {valu : Valuation} {rh : Rhs} {v1 v2 : Val}
    (h1 : RhsEvalTo valu ge sp m rh v1) (h2 : RhsEvalTo valu ge sp m rh v2) : v1 = v2 := by
  cases h1 with
  | op_eval_to _ _ _ e1 => cases h2 with | op_eval_to _ _ _ e2 => rw [e1] at e2; cases e2; rfl
  | load_eval_to _ _ _ a _ _ a1 l1 =>
    cases h2 with
    | load_eval_to _ _ _ a' _ _ a2 l2 => rw [a1] at a2; cases a2; rw [l1] at l2; cases l2; rfl
  | builtin_eval_to _ _ vargs _ e1 s1 =>
    cases h2 with
    | builtin_eval_to _ _ vargs' _ e2 s2 =>
      rw [evalBuiltinArgs_determ e1 e2] at s2; rw [s1] at s2; cases s2; rfl

end HOLDS2

/-! ### Adding equations -/

section ADD
variable {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset} {m : Mem}

/-- `CSEproof.add_rhs_holds` -/
theorem add_rhs_holds {valu1 : Valuation} {n : Numbering} {rd : Reg} {rh : Rhs}
    {rs' : RTL.Regset} (NH : NumberingHolds valu1 ge sp rs m n) (V : RhsValid valu1 ge sp rh)
    (EV : RhsEvalTo valu1 ge sp m rh (rs'.get rd)) (WF : WfRhs n.num_next rh)
    (OTHER : ∀ r, r ≠ rd → rs'.get r = rs.get r) :
    ∃ valu2, NumberingHolds valu2 ge sp rs' m (addRhs n rd rh) := by
  obtain ⟨W, E, R⟩ := NH
  unfold addRhs
  cases FIND : findValnumRhs rh n.num_eqs with
  | some vres =>
    obtain ⟨rh', IN, COMPAT⟩ := find_valnum_rhs_charact _ _ _ FIND
    have EH := E _ IN
    cases EH with
    | eq_holds_strict _ _ he _ =>
    have X : rs'.get rd = valu1 vres := rhs_eval_to_inj (rhsEvalTo_compat EV COMPAT) he
    refine ⟨valu1, ⟨⟨W.wf_num_eqs, ?_, ?_⟩, E, ?_⟩⟩
    · intro r v h
      simp only [PTree.gsspec] at h
      split at h
      · cases h; exact (W.wf_num_eqs _ IN).1
      · exact W.wf_num_reg r v h
    · intro r v h; exact update_reg_charact W h
    · intro r v h
      simp only [PTree.gsspec] at h
      split at h
      · rename_i e; subst e; cases h; exact X
      · rename_i hne; rw [OTHER r hne]; exact R r v h
  | none =>
    let valu2 : Valuation := fun v => if v = n.num_next then rs'.get rd else valu1 v
    have AG : ValuAgree valu1 valu2 n.num_next := fun v hv => if_neg (pos_ne_of_lt hv)
    refine ⟨valu2, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨pos_lt_succ_self _, fun v hv => pos_lt_succ_of_lt (WF v hv)⟩
      · exact wf_equation_incr (W.wf_num_eqs e he) (pos_le_succ _)
    · intro r v h
      simp only [PTree.gsspec] at h
      split at h
      · cases h; exact pos_lt_succ_self _
      · exact pos_lt_succ_of_lt (W.wf_num_reg r v h)
    · intro r v h; exact update_reg_charact W h
    · intro eq heq
      rcases List.mem_cons.mp heq with rfl | heq
      · refine .eq_holds_strict _ _ ?_ (rhs_valid_exten AG V WF)
        have : valu2 n.num_next = rs'.get rd := if_pos rfl
        rw [this]; exact rhs_eval_to_exten AG EV WF
      · exact equation_holds_exten AG (E eq heq) (W.wf_num_eqs eq heq)
    · intro r v h
      simp only [PTree.gsspec] at h
      split at h
      · rename_i e; subst e; cases h; exact (if_pos rfl).symm
      · rename_i hne
        rw [OTHER r hne, R r v h]
        exact (AG v (W.wf_num_reg r v h)).symm

/-- `CSEproof.add_op_holds` -/
theorem add_op_holds {valu1 : Valuation} {n : Numbering} {op : Operation} {args : List Reg}
    {v : Val} {dst : Reg} (NH : NumberingHolds valu1 ge sp rs m n)
    (EV : evalOperation ge sp op (rs.getList args) m = some v) :
    ∃ valu2, NumberingHolds valu2 ge sp (rs.set dst v) m (addOp n dst op args) := by
  unfold addOp
  cases ISMOVE : isMoveOperation op args with
  | some src =>
    obtain ⟨h1, h2⟩ := Op.isMoveOperation_correct ISMOVE
    subst h1 h2
    have EV' : v = rs.get src := by
      change some (rs.get src) = some v at EV
      cases EV; rfl
    subst EV'
    dsimp only
    generalize e1 : valnumReg n src = p1
    obtain ⟨n1, vsrc⟩ := p1
    obtain ⟨valu2, ⟨W, E, R⟩, B, C, D, F⟩ := valnum_reg_holds NH e1
    refine ⟨valu2, ⟨⟨W.wf_num_eqs, ?_, ?_⟩, E, ?_⟩⟩
    · intro r v h
      simp only [PTree.gsspec] at h
      split at h
      · cases h; exact D
      · exact W.wf_num_reg r v h
    · intro r v h; exact update_reg_charact W h
    · intro r v h
      simp only [PTree.gsspec] at h
      rw [PMap.gsspec]
      split at h
      · rename_i e; cases h; rw [if_pos e]; exact B
      · rename_i hne; rw [if_neg hne]; exact R r v h
  | none =>
    simp only
    generalize e1 : valnumRegs n args = p1
    obtain ⟨n1, vl⟩ := p1
    obtain ⟨valu2, A, B, C, D, F⟩ := valnum_regs_holds args NH e1
    exact add_rhs_holds A (.op_valid _ _ _) (.op_eval_to _ _ _ (by rw [PMap.gss, ← B]; exact EV))
      D (fun r h => PMap.gso _ _ _ _ (Ne.symm h))

/-- `CSEproof.add_load_holds` -/
theorem add_load_holds {valu1 : Valuation} {sp0 : Block} {n : Numbering} {addr : Addressing}
    {args : List Reg} {ap : Aptr} {b : Block} {ofs : Integers.Ptrofs} {chunk : Chunk} {v : Val}
    {dst : Reg} {bc : BlockClassification}
    (NH : NumberingHolds valu1 ge (.Vptr sp0 Integers.Ptrofs.zero) rs m n)
    (EA : evalAddressing ge (.Vptr sp0 Integers.Ptrofs.zero) addr (rs.getList args) =
      some (.Vptr b ofs))
    (LD : Mem.loadv chunk m (.Vptr b ofs) = some v) (PM : Pmatch bc b ofs ap)
    (GM : GenvMatch bc ge) (SP : bc sp0 = .BCstack) :
    ∃ valu2, NumberingHolds valu2 ge (.Vptr sp0 Integers.Ptrofs.zero) (rs.set dst v) m
      (addLoad n dst chunk addr args ap) := by
  unfold addLoad
  generalize e1 : valnumRegs n args = p1
  obtain ⟨n1, vl⟩ := p1
  obtain ⟨valu2, A, B, C, D, F⟩ := valnum_regs_holds args NH e1
  exact add_rhs_holds A (.load_valid _ _ _ _ _ _ _ bc (by rw [← B]; exact EA) PM GM SP)
    (.load_eval_to _ _ _ _ _ _ (by rw [← B]; exact EA) (by rw [PMap.gss]; exact LD))
    D (fun r h => PMap.gso _ _ _ _ (Ne.symm h))

/-- `CSEproof.add_builtin_holds` -/
theorem add_builtin_holds {valu1 : Valuation} {n : Numbering} {bf : Builtins.BuiltinFunction}
    {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {vargs : List Val} {vres : Val}
    (NH : NumberingHolds valu1 ge sp rs m n)
    (EA : EvalBuiltinArgs (Genv.toSenv ge) (fun r => rs.get r) sp m args vargs)
    (BS : (Builtins.builtinFunctionSem bf).sem vargs = some vres) :
    ∃ valu2, NumberingHolds valu2 ge sp (regmapSetres res vres rs) m (addBuiltin n res bf args) := by
  cases res with
  | BR rd =>
    simp only [addBuiltin]
    generalize e1 : valnumBuiltinArgs n args = p1
    obtain ⟨n1, args'⟩ := p1
    obtain ⟨valu2, A, B, C, D, F⟩ := valnum_builtin_args_holds EA NH e1
    exact add_rhs_holds A (.builtin_valid _ _ _)
      (.builtin_eval_to _ _ _ _ B (by simp only [regmapSetres, PMap.gss]; exact BS))
      D (fun r h => PMap.gso _ _ _ _ (Ne.symm h))
  | _ => exact ⟨valu1, NH⟩

/-- `CSEproof.set_unknown_holds` -/
theorem set_unknown_holds {valu : Valuation} {n : Numbering} {r : Reg} {v : Val}
    (NH : NumberingHolds valu ge sp rs m n) :
    NumberingHolds valu ge sp (rs.set r v) m (setUnknown n r) := by
  obtain ⟨W, E, R⟩ := NH
  refine ⟨⟨W.wf_num_eqs, ?_, ?_⟩, E, ?_⟩
  · intro r0 v0 h
    simp only [setUnknown, PTree.grspec] at h
    split at h
    · cases h
    · exact W.wf_num_reg r0 v0 h
  · intro r0 v0 h
    obtain ⟨A, B⟩ := forget_reg_charact W h
    simp only [setUnknown]
    rw [PTree.gro _ _ _ (Ne.symm A)]; exact W.wf_num_val r0 v0 B
  · intro r0 v0 h
    simp only [setUnknown, PTree.grspec] at h
    split at h
    · cases h
    · rename_i hne; rw [PMap.gso _ _ _ _ (Ne.symm hne)]; exact R r0 v0 h

/-- `CSEproof.set_res_unknown_holds` -/
theorem set_res_unknown_holds {valu : Valuation} {n : Numbering} {r : BuiltinRes Reg} {v : Val}
    (NH : NumberingHolds valu ge sp rs m n) :
    NumberingHolds valu ge sp (regmapSetres r v rs) m (setResUnknown n r) := by
  cases r with
  | BR r => exact set_unknown_holds NH
  | _ => exact NH

end ADD

/-! ### Killing equations -/

/-- `CSEproof.kill_eqs_charact` -/
theorem kill_eqs_charact (pred : Rhs → Bool) (l : Valnum) (strict : Bool) (r : Rhs) :
    ∀ (eqs : List Equation), Equation.Eq l strict r ∈ killEqs pred eqs →
    pred r = false ∧ Equation.Eq l strict r ∈ eqs
  | [], h => by cases h
  | .Eq l' s' r' :: eqs, h => by
    simp only [killEqs] at h
    split at h
    · obtain ⟨A, B⟩ := kill_eqs_charact pred l strict r eqs h
      exact ⟨A, List.mem_cons_of_mem _ B⟩
    · rename_i hp
      rcases List.mem_cons.mp h with h | h
      · cases h; exact ⟨by simpa using hp, List.mem_cons_self ..⟩
      · obtain ⟨A, B⟩ := kill_eqs_charact pred l strict r eqs h
        exact ⟨A, List.mem_cons_of_mem _ B⟩

theorem killEqs_subset (pred : Rhs → Bool) {e : Equation} {eqs : List Equation}
    (h : e ∈ killEqs pred eqs) : e ∈ eqs := by
  cases e with
  | Eq l s r => exact (kill_eqs_charact pred l s r eqs h).2

section KILL
variable {ge : RTL.CGenv} {sp : Val} {rs : RTL.Regset} {m : Mem}

/-- `CSEproof.kill_equations_hold` -/
theorem kill_equations_hold {valu : Valuation} {n : Numbering} {pred : Rhs → Bool} {m' : Mem}
    (NH : NumberingHolds valu ge sp rs m n)
    (H : ∀ r v, pred r = false → RhsValid valu ge sp r → RhsEvalTo valu ge sp m r v →
      RhsEvalTo valu ge sp m' r v) :
    NumberingHolds valu ge sp rs m' (killEquations pred n) := by
  obtain ⟨W, E, R⟩ := NH
  refine ⟨⟨fun e he => W.wf_num_eqs e (killEqs_subset pred he), W.wf_num_reg, W.wf_num_val⟩,
    fun eq heq => ?_, R⟩
  cases eq with
  | Eq l s r =>
    obtain ⟨A, B⟩ := kill_eqs_charact pred l s r _ heq
    cases E _ B with
    | eq_holds_strict _ _ he hv => exact .eq_holds_strict _ _ (H _ _ A hv he) hv
    | eq_holds_lessdef _ _ v he hld hv => exact .eq_holds_lessdef _ _ v (H _ _ A hv he) hld hv

/-- `CSEproof.kill_all_loads_hold` -/
theorem kill_all_loads_hold {valu : Valuation} {n : Numbering} {m' : Mem}
    (NH : NumberingHolds valu ge sp rs m n) :
    NumberingHolds valu ge sp rs m' (killAllLoads n) := by
  refine kill_equations_hold NH fun r v hp _ he => ?_
  cases he with
  | op_eval_to op vl v h =>
    exact .op_eval_to _ _ _ (by rw [← opDependsOnMemory_correct ge sp op _ m m' hp]; exact h)
  | load_eval_to => cases hp
  | builtin_eval_to bf args vargs v ha hb =>
    exact .builtin_eval_to _ _ _ _ (builtinArgsDependsOnMemory_correct m' ha hp) hb

/-- `CSEproof.kill_cheap_computations_hold` -/
theorem kill_cheap_computations_hold {valu : Valuation} {n : Numbering}
    (NH : NumberingHolds valu ge sp rs m n) :
    NumberingHolds valu ge sp rs m (killCheapComputations n) :=
  kill_equations_hold NH fun _ _ _ _ he => he

end KILL

end CSEproof
end RiscV
end CC
