/-
  Correctness of strength reduction (aarch64) — port of
  `aarch64/ConstpropOpproof.v`, part 2: `op_strength_reduction_correct` and
  `addr_strength_reduction_correct`.
-/
import CCLib.aarch64.ConstpropOpproof

namespace CC
namespace ConstpropOpproof

open ValueDomain Op ConstpropOp
open Integers (Ptrofs)

section STRENGTH_REDUCTION
variable {F V : Type} {ge : Genv F V} {bc : BlockClassification} {sp : Block} {ae : Aenv}
  {e : RTL.Regset} {m : Mem}

/-- `ConstpropOpproof.op_strength_reduction_correct` -/
theorem op_strength_reduction_correct (o : Options)
    (MATCH : Ematch bc e ae)
    (op : Operation) (args : List Reg) (vl : List Aval) (v : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalOperation ge (.Vptr sp Ptrofs.zero) op (e.getList args) m = some v) :
    OpSim ge sp e m (opStrengthReduction o op args vl) v := by
  unfold opStrengthReduction
  cases op
  all_goals dsimp only
  all_goals first
    | exact ⟨v, hev, .refl _⟩
    | skip
  case Ocmp c =>
    have E : evalOperation ge (.Vptr sp Ptrofs.zero) (.Ocmp c) (e.getList args) m =
        some (Val.ofOptbool (evalCondition c (e.getList args) m)) := by
      generalize e.getList args = l
      rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    rw [E, Option.some.injEq] at hev; subst hev
    exact make_cmp_correct MATCH c args vl hvl
  case Osel c ty =>
    split
    · rename_i r1 r2 args' _ _ vl'
      simp only [List.map_cons, List.cons.injEq] at hvl
      simp only [Regmap.getList, List.map_cons] at hev
      unfold evalOperation at hev
      dsimp only at hev
      simp only [Option.some.injEq] at hev; subst hev
      exact make_select_correct o MATCH c ty r1 r2 args' vl' hvl.2.2
    · exact ⟨v, hev, .refl _⟩
  all_goals split
  all_goals first
    | exact ⟨v, hev, .refl _⟩
    | skip
  all_goals
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl
    simp only [Regmap.getList, List.map_cons, List.map_nil] at hev
    unfold evalOperation at hev
    dsimp only at hev
  all_goals
    first | obtain ⟨h1, h2⟩ := hvl | have h1 := hvl
    try (have H1 := get_I MATCH h1.symm)
    try (have H1 := get_L MATCH h1.symm)
    try (have HF1 := get_F MATCH h1.symm)
    try (have HF1 := get_FS MATCH h1.symm)
    try (have H2 := get_I MATCH h2.symm)
    try (have H2 := get_L MATCH h2.symm)
    try (have HF2 := get_F MATCH h2.symm)
    try (have HF2 := get_FS MATCH h2.symm)
    try (simp only [Option.some.injEq] at hev; subst hev)
    try subst h1
    try subst h2
    try (rw [H1])
    try (rw [H2])
    try simp only [eval_static_shift_correct, eval_static_shiftl_correct,
      eval_static_extend_correct, Val.sub_add_opp, Val.subl_addl_opp, Val.notint, Val.notl]
  all_goals have MATCH' : ∀ r, Vmatch bc (e.get r) (AE.get r ae) := MATCH
  all_goals with_reducible first
    | exact make_addimm_correct _ _
    | (rw [Val.add_commut]; exact make_addimm_correct _ _)
    | exact make_mulimm_correct _ _ _ H2
    | (rw [Val.mul_commut]; exact make_mulimm_correct _ _ _ H1)
    | exact make_divimm_correct _ _ _ hev H2
    | exact make_divuimm_correct _ _ _ hev H2
    | exact make_andimm_correct _ _ (MATCH' _)
    | (rw [Val.and_commut]; exact make_andimm_correct _ _ (MATCH' _))
    | exact make_orimm_correct _ _
    | (rw [Val.or_commut]; exact make_orimm_correct _ _)
    | exact make_xorimm_correct _ _
    | (rw [Val.xor_commut]; exact make_xorimm_correct _ _)
    | exact make_shlimm_correct _ _ _ H2
    | exact make_shrimm_correct _ _ _ H2
    | exact make_shruimm_correct _ _ _ H2
    | exact make_zext_correct _ _ (MATCH' _)
    | exact make_sext_correct _ _ (MATCH' _)
    | exact make_addlimm_correct _ _
    | (rw [Val.addl_commut]; exact make_addlimm_correct _ _)
    | exact make_mullimm_correct _ _ _ H2
    | (rw [Val.mull_commut]; exact make_mullimm_correct _ _ _ H1)
    | exact make_divlimm_correct _ _ _ hev H2
    | exact make_divluimm_correct _ _ _ hev H2
    | exact make_andlimm_correct _ _ _
    | (rw [Val.andl_commut]; exact make_andlimm_correct _ _ _)
    | exact make_orlimm_correct _ _
    | (rw [Val.orl_commut]; exact make_orlimm_correct _ _)
    | exact make_xorlimm_correct _ _
    | (rw [Val.xorl_commut]; exact make_xorlimm_correct _ _)
    | exact make_shllimm_correct _ _ _ H2
    | exact make_shrlimm_correct _ _ _ H2
    | exact make_shrluimm_correct _ _ _ H2
    | exact make_mulfimm_correct _ _ _ HF2
    | exact make_mulfimm_correct_2 _ _ _ HF1
    | exact make_mulfsimm_correct _ _ _ HF2
    | exact make_mulfsimm_correct_2 _ _ _ HF1

theorem shll_amount64 (n : Integers.Int64) (a : Amount64) :
    Val.shll (.Vlong n) (.Vint a.a64_amount) = .Vlong (Integers.Int64.shl' n a.a64_amount) := by
  simp only [Val.shll]
  split
  · simp only [Integers.Int64.shl'_eq]
  · rename_i hc; exact absurd a.a64_range hc

theorem vmatch_of_eq (MATCH : Ematch bc e ae) {r : Reg} {a : Aval} (h : a = AE.get r ae) :
    Vmatch bc (e.get r) a := h ▸ MATCH r

theorem addl_symbol_lessdef {x : Val} {s : Ident} {ofs : Ptrofs} {n : Integers.Int64}
    (h : Val.Lessdef x (Genv.symbolAddress ge s ofs)) :
    Val.Lessdef (Val.addl x (.Vlong n)) (Genv.symbolAddress ge s (Ptrofs.add ofs (Ptrofs.of_int64 n))) := by
  unfold Genv.symbolAddress at h ⊢
  cases hf : Genv.findSymbol ge s <;> simp only [hf] at h ⊢
  · cases h <;> exact .refl _
  · cases h with
    | refl => simp only [Val.addl, Archi.ptr64, ↓reduceIte]; exact .refl _
    | undef => exact .undef _

theorem addl_stk_lessdef_l {x : Val} {ofs : Ptrofs} {n : Integers.Int64}
    (h : Val.Lessdef x (.Vptr sp ofs)) :
    Val.Lessdef (Val.addl x (.Vlong n)) (.Vptr sp (Ptrofs.add ofs (Ptrofs.of_int64 n))) := by
  cases h with
  | refl => simp only [Val.addl, Archi.ptr64, ↓reduceIte]; exact .refl _
  | undef => exact .undef _

theorem addl_stk_lessdef_r {y : Val} {ofs : Ptrofs} {n : Integers.Int64}
    (h : Val.Lessdef y (.Vptr sp ofs)) :
    Val.Lessdef (Val.addl (.Vlong n) y) (.Vptr sp (Ptrofs.add (Ptrofs.of_int64 n) ofs)) := by
  cases h with
  | refl => simp only [Val.addl, Archi.ptr64, ↓reduceIte, Ptrofs.add_commut]; exact .refl _
  | undef => exact .undef _

/-- `ConstpropOpproof.addr_strength_reduction_correct` -/
theorem addr_strength_reduction_correct (o : Options) (GENV : GenvMatch bc ge)
    (STACK : bc sp = .BCstack) (MATCH : Ematch bc e ae)
    (addr : Addressing) (args : List Reg) (vl : List Aval) (res : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalAddressing ge (.Vptr sp Ptrofs.zero) addr (e.getList args) = some res) :
    ∃ res', evalAddressing ge (.Vptr sp Ptrofs.zero) (addrStrengthReduction o addr args vl).1
        (e.getList (addrStrengthReduction o addr args vl).2) = some res' ∧ Val.Lessdef res res' := by
  unfold addrStrengthReduction
  split
  all_goals first
    | exact ⟨res, hev, .refl _⟩
    | skip
  all_goals
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl
    simp only [Regmap.getList, List.map_cons, List.map_nil] at hev
    unfold evalAddressing at hev
    dsimp only at hev
    simp only [Option.some.injEq] at hev
    subst hev
  case h_1 =>
    have h1 := hvl
    split
    · exact ⟨_, rfl, addl_symbol_lessdef (vmatch_ptr_gl GENV (vmatch_of_eq MATCH h1))⟩
    · exact ⟨_, rfl, .refl _⟩
  all_goals
    first | obtain ⟨h1, h2⟩ := hvl | have h1 := hvl
    try (rw [get_L MATCH h1.symm])
    try (rw [get_L MATCH h2.symm])
    try (rw [get_I MATCH h2.symm])
    try simp only [shll_amount64, eval_static_extend_correct]
  all_goals first
    | exact ⟨_, rfl, .refl _⟩
    | (refine ⟨_, rfl, ?_⟩; rw [Val.addl_commut]; exact .refl _)
    | (refine ⟨_, rfl, ?_⟩
       simp only [Val.offsetPtr, Ptrofs.add_zero_l]
       first
         | exact addl_stk_lessdef_l (vmatch_ptr_stk (vmatch_of_eq MATCH h1) STACK)
         | exact addl_stk_lessdef_r (vmatch_ptr_stk (vmatch_of_eq MATCH h2) STACK))

end STRENGTH_REDUCTION

end ConstpropOpproof
end CC
