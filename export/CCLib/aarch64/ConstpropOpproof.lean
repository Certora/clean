/-
  Correctness of strength reduction (aarch64) — port of
  `aarch64/ConstpropOpproof.v`, part 1: `const_for_result_correct`, the
  `eval_static_*_correct` lemmas, `cond_strength_reduction_correct`,
  `make_cmp_correct`, `make_select_correct` and the `make_*imm_correct`
  lemmas.  `op_strength_reduction_correct` and
  `addr_strength_reduction_correct` are in `ConstpropOpproof2.lean`.

  Differences from Rocq: the `let (op, args) := … in ∃ v, …` statements are
  phrased with the predicate `OpSim` below.  Flocq's `Float.mul2_add` and
  `Float32.mul2_add` (`x * 2 = x + x`) come from `CCLib.lib.FloatsArith`.
-/
import CCLib.aarch64.ConstpropOp
import CCLib.aarch64.ValueAOpproof
import CCLib.aarch64.SelectLongproof
import CCLib.backend.ValueDomainProofCmp
import CCLib.lib.FloatsArith

namespace CC
namespace ConstpropOpproof

open ValueDomain Op ConstpropOp
open Integers (Ptrofs)

section STRENGTH_REDUCTION
variable {F V : Type} (ge : Genv F V) {bc : BlockClassification} (sp : Block) (ae : Aenv)
  (e : RTL.Regset) (m : Mem)

/-- `∃ v', eval_operation ge (Vptr sp 0) op e##args m = Some v' ∧ Val.lessdef v v'`
    for the result `(op, args)` of a strength reduction. -/
def OpSim (oa : Operation × List Reg) (v : Val) : Prop :=
  ∃ w, evalOperation ge (.Vptr sp Ptrofs.zero) oa.1 (e.getList oa.2) m = some w ∧ Val.Lessdef v w

variable {ge sp ae e m}

/-- `ConstpropOpproof.const_for_result_correct` -/
theorem const_for_result_correct (o : Options) (GENV : GenvMatch bc ge) (STACK : bc sp = .BCstack)
    {a : Aval} {op : Operation} {v : Val} (h : constForResult o a = some op) (hv : Vmatch bc v a) :
    ∃ v', evalOperation ge (.Vptr sp Ptrofs.zero) op [] m = some v' ∧ Val.Lessdef v v' := by
  cases a with
  | I n => simp only [constForResult, Option.some.injEq] at h; subst h; cases hv; exact ⟨_, rfl, .refl _⟩
  | IU n =>
    simp only [constForResult, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by cases hv <;> constructor⟩
  | L n => simp only [constForResult, Option.some.injEq] at h; subst h; cases hv; exact ⟨_, rfl, .refl _⟩
  | F f =>
    simp only [constForResult] at h
    split at h
    · cases h; cases hv; exact ⟨_, rfl, .refl _⟩
    · cases h
  | FS f =>
    simp only [constForResult] at h
    split at h
    · cases h; cases hv; exact ⟨_, rfl, .refl _⟩
    · cases h
  | Ptr p =>
    cases p with
    | Gl id ofs =>
      simp only [constForResult, Option.some.injEq] at h; subst h
      exact ⟨_, rfl, vmatch_ptr_gl GENV hv⟩
    | Stk ofs =>
      simp only [constForResult, Option.some.injEq] at h; subst h
      refine ⟨_, rfl, ?_⟩
      show Val.Lessdef v (Val.offsetPtr (.Vptr sp Ptrofs.zero) _)
      simp only [Val.offsetPtr, Ptrofs.add_zero_l]
      exact vmatch_ptr_stk hv STACK
    | _ => simp [constForResult] at h
  | _ => simp [constForResult] at h

/-- `ConstpropOpproof.eval_static_shift_correct` -/
theorem eval_static_shift_correct (s : Shift) (v : Integers.Int) (a : Amount32) :
    evalShift s (.Vint v) a = .Vint (evalStaticShift s v a) := by
  cases s <;> simp [evalShift, evalStaticShift, Val.shl, Val.shru, Val.shr, Val.ror, a.a32_range]

/-- `ConstpropOpproof.eval_static_shiftl_correct` -/
theorem eval_static_shiftl_correct (s : Shift) (v : Integers.Int64) (a : Amount64) :
    evalShiftl s (.Vlong v) a = .Vlong (evalStaticShiftl s v a) := by
  cases s <;> simp only [evalShiftl, evalStaticShiftl, Val.shll, Val.shrlu, Val.shrl, Val.rorl]
  all_goals first
    | rfl
    | split
      · simp only [Integers.Int64.shl'_eq, Integers.Int64.shru'_eq, Integers.Int64.shr'_eq]
      · rename_i hc; exact absurd a.a64_range hc

/-- `ConstpropOpproof.eval_static_extend_correct` -/
theorem eval_static_extend_correct (x : Extension) (v : Integers.Int) (a : Amount64) :
    evalExtend x (.Vint v) a = .Vlong (evalStaticExtend x v a) := by
  cases x <;> simp only [evalExtend, evalStaticExtend, Val.shll, Val.longofint, Val.longofintu]
  all_goals split
  all_goals first
    | rename_i hc; exact absurd a.a64_range hc
    | simp only [Integers.Int64.shl'_eq]


/-! ### Reading exact abstract values (Rocq's `SimplVM`) -/

section SIMPLVM
variable {bc : BlockClassification} {ae : Aenv} {e : RTL.Regset}

theorem get_I (MATCH : Ematch bc e ae) {r : Reg} {n : Integers.Int} (h : AE.get r ae = .I n) :
    e.get r = .Vint n := by
  have := MATCH r; rw [h] at this
  generalize hx : PMap.get r e = x at this
  cases this; rfl

theorem get_L (MATCH : Ematch bc e ae) {r : Reg} {n : Integers.Int64} (h : AE.get r ae = .L n) :
    e.get r = .Vlong n := by
  have := MATCH r; rw [h] at this
  generalize hx : PMap.get r e = x at this
  cases this; rfl

theorem get_F (MATCH : Ematch bc e ae) {r : Reg} {n : Floats.Float} (h : AE.get r ae = .F n) :
    e.get r = .Vfloat n := by
  have := MATCH r; rw [h] at this
  generalize hx : PMap.get r e = x at this
  cases this; rfl

theorem get_FS (MATCH : Ematch bc e ae) {r : Reg} {n : Floats.Float32} (h : AE.get r ae = .FS n) :
    e.get r = .Vsingle n := by
  have := MATCH r; rw [h] at this
  generalize hx : PMap.get r e = x at this
  cases this; rfl

end SIMPLVM

theorem cmpf_bool_swap (c : Comparison) (x y : Val) :
    Val.cmpf_bool c.swap x y = Val.cmpf_bool c y x := by
  cases x <;> cases y <;> simp [Val.cmpf_bool, Floats.Float.cmp_swap]

theorem cmpfs_bool_swap (c : Comparison) (x y : Val) :
    Val.cmpfs_bool c.swap x y = Val.cmpfs_bool c y x := by
  cases x <;> cases y <;> simp [Val.cmpfs_bool, Floats.Float32.cmp_swap]

set_option hygiene false in
/-- Rocq's `InvApproxRegs; SimplVM` for two arguments: from the equations
    `hvl` between the abstract values and the registers, rewrite the contents
    of the registers whose abstract value is a constant. -/
macro "simplvm2" MATCH:term "," hvl:ident : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at $hvl:ident
  obtain ⟨h1, h2⟩ := $hvl:ident
  simp only [Regmap.getList, List.map_cons, List.map_nil]
  first
    | simp only [get_I $MATCH h1.symm] | simp only [get_L $MATCH h1.symm]
    | simp only [get_F $MATCH h1.symm] | simp only [get_FS $MATCH h1.symm] | skip
  first
    | simp only [get_I $MATCH h2.symm] | simp only [get_L $MATCH h2.symm]
    | simp only [get_F $MATCH h2.symm] | simp only [get_FS $MATCH h2.symm] | skip))

/-- `ConstpropOpproof.cond_strength_reduction_correct` -/
theorem cond_strength_reduction_correct (MATCH : Ematch bc e ae) (cond : Condition)
    (args : List Reg) (vl : List Aval) (hvl : vl = args.map (fun r => AE.get r ae)) :
    evalCondition (condStrengthReduction cond args vl).1
      (e.getList (condStrengthReduction cond args vl).2) m =
    evalCondition cond (e.getList args) m := by
  unfold condStrengthReduction
  split
  case h_21 => rfl
  all_goals simplvm2 MATCH, hvl
  all_goals (try (split <;> try (subst ‹_ = Floats.Float.zero›)) <;> try (subst ‹_ = Floats.Float32.zero›))
  all_goals (try simp only [evalCondition, List.map_cons, List.map_nil])
  all_goals (try simp only [get_F MATCH h1.symm])
  all_goals (try simp only [get_F MATCH h2.symm])
  all_goals (try simp only [get_FS MATCH h1.symm])
  all_goals (try simp only [get_FS MATCH h2.symm])
  all_goals first
    | exact Val.swap_cmp_bool _ _ _
    | exact Val.swap_cmpu_bool _ _ _ _
    | exact Val.swap_cmpl_bool _ _ _
    | exact Val.swap_cmplu_bool _ _ _ _
    | exact cmpf_bool_swap _ _ _
    | exact cmpfs_bool_swap _ _ _
    | rw [cmpf_bool_swap]
    | rw [cmpfs_bool_swap]
    | rw [eval_static_shift_correct]
    | rw [eval_static_shiftl_correct]
    | rfl


/-- `ConstpropOpproof.make_cmp_base_correct` -/
theorem make_cmp_base_correct (MATCH : Ematch bc e ae) (c : Condition) (args : List Reg)
    (vl : List Aval) (hvl : vl = args.map (fun r => AE.get r ae)) :
    OpSim ge sp e m (makeCmpBase c args vl) (Val.ofOptbool (evalCondition c (e.getList args) m)) := by
  have EQ := cond_strength_reduction_correct (m := m) MATCH c args vl hvl
  unfold makeCmpBase
  generalize condStrengthReduction c args vl = p at EQ ⊢
  obtain ⟨c', args'⟩ := p
  refine ⟨_, rfl, ?_⟩
  simp only at EQ ⊢
  rw [EQ]; exact .refl _

/-- A register whose abstract value is included in `Uns Ptop 1` holds
    `Vundef`, `0` or `1`. -/
theorem uns1_cases (MATCH : Ematch bc e ae) {r : Reg} (h : vincl (AE.get r ae) (.Uns .Ptop 1) = true) :
    e.get r = .Vundef ∨ e.get r = .Vint Integers.Int.zero ∨ e.get r = .Vint Integers.Int.one :=
  vmatch_Uns_1 (vmatch_ge (vincl_ge h) (MATCH r))

/-- The four boolean identities behind `make_cmp_imm_eq` / `make_cmp_imm_ne`
    for a value that is `Vundef`, `0` or `1`. -/
theorem cmp_bool01 (vp : Block → Z → Bool) {x : Val}
    (hx : x = .Vundef ∨ x = .Vint Integers.Int.zero ∨ x = .Vint Integers.Int.one) :
    Val.Lessdef (Val.ofOptbool (Val.cmp_bool .Ceq x (.Vint Integers.Int.one))) x ∧
    Val.Lessdef (Val.ofOptbool (Val.cmpu_bool vp .Ceq x (.Vint Integers.Int.one))) x ∧
    Val.Lessdef (Val.ofOptbool (Val.cmp_bool .Ceq x (.Vint Integers.Int.zero)))
      (Val.xor x (.Vint Integers.Int.one)) ∧
    Val.Lessdef (Val.ofOptbool (Val.cmpu_bool vp .Ceq x (.Vint Integers.Int.zero)))
      (Val.xor x (.Vint Integers.Int.one)) ∧
    Val.Lessdef (Val.ofOptbool (Val.cmp_bool .Cne x (.Vint Integers.Int.zero))) x ∧
    Val.Lessdef (Val.ofOptbool (Val.cmpu_bool vp .Cne x (.Vint Integers.Int.zero))) x ∧
    Val.Lessdef (Val.ofOptbool (Val.cmp_bool .Cne x (.Vint Integers.Int.one)))
      (Val.xor x (.Vint Integers.Int.one)) ∧
    Val.Lessdef (Val.ofOptbool (Val.cmpu_bool vp .Cne x (.Vint Integers.Int.one)))
      (Val.xor x (.Vint Integers.Int.one)) := by
  rcases hx with rfl | rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact .undef _
    | (simp only [Val.cmp_bool, Val.cmpu_bool, Val.ofOptbool, Val.xor]
       first | exact .undef _ | exact .refl _ | decide)


theorem make_cmp_imm_eq_correct (MATCH : Ematch bc e ae) (c : Condition) (r1 : Reg)
    (n : Integers.Int) (hc : c = .Ccompimm .Ceq n ∨ c = .Ccompuimm .Ceq n) :
    OpSim ge sp e m (makeCmpImmEq c [r1] [AE.get r1 ae] n r1 (AE.get r1 ae))
      (Val.ofOptbool (evalCondition c (e.getList [r1]) m)) := by
  unfold makeCmpImmEq
  split
  · rename_i H
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    obtain ⟨rfl, H⟩ := H
    have K := cmp_bool01 (Mem.validPointer m) (uns1_cases MATCH H)
    refine ⟨_, rfl, ?_⟩
    rcases hc with rfl | rfl <;>
      simp only [evalCondition, Regmap.getList, List.map_cons, List.map_nil]
    · exact K.1
    · exact K.2.1
  · split
    · rename_i _ H
      simp only [Bool.and_eq_true, decide_eq_true_eq] at H
      obtain ⟨rfl, H⟩ := H
      have K := cmp_bool01 (Mem.validPointer m) (uns1_cases MATCH H)
      refine ⟨_, rfl, ?_⟩
      rcases hc with rfl | rfl <;>
        simp only [evalCondition, Regmap.getList, List.map_cons, List.map_nil]
      · exact K.2.2.1
      · exact K.2.2.2.1
    · exact make_cmp_base_correct MATCH c [r1] _ rfl

theorem make_cmp_imm_ne_correct (MATCH : Ematch bc e ae) (c : Condition) (r1 : Reg)
    (n : Integers.Int) (hc : c = .Ccompimm .Cne n ∨ c = .Ccompuimm .Cne n) :
    OpSim ge sp e m (makeCmpImmNe c [r1] [AE.get r1 ae] n r1 (AE.get r1 ae))
      (Val.ofOptbool (evalCondition c (e.getList [r1]) m)) := by
  unfold makeCmpImmNe
  split
  · rename_i H
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    obtain ⟨rfl, H⟩ := H
    have K := cmp_bool01 (Mem.validPointer m) (uns1_cases MATCH H)
    refine ⟨_, rfl, ?_⟩
    rcases hc with rfl | rfl <;>
      simp only [evalCondition, Regmap.getList, List.map_cons, List.map_nil]
    · exact K.2.2.2.2.1
    · exact K.2.2.2.2.2.1
  · split
    · rename_i _ H
      simp only [Bool.and_eq_true, decide_eq_true_eq] at H
      obtain ⟨rfl, H⟩ := H
      have K := cmp_bool01 (Mem.validPointer m) (uns1_cases MATCH H)
      refine ⟨_, rfl, ?_⟩
      rcases hc with rfl | rfl <;>
        simp only [evalCondition, Regmap.getList, List.map_cons, List.map_nil]
      · exact K.2.2.2.2.2.2.1
      · exact K.2.2.2.2.2.2.2
    · exact make_cmp_base_correct MATCH c [r1] _ rfl

/-- `ConstpropOpproof.make_cmp_correct` -/
theorem make_cmp_correct (MATCH : Ematch bc e ae) (c : Condition) (args : List Reg)
    (vl : List Aval) (hvl : vl = args.map (fun r => AE.get r ae)) :
    OpSim ge sp e m (makeCmp c args vl) (Val.ofOptbool (evalCondition c (e.getList args) m)) := by
  unfold makeCmp
  split
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl; subst hvl
    exact make_cmp_imm_eq_correct MATCH _ _ _ (.inl rfl)
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl; subst hvl
    exact make_cmp_imm_ne_correct MATCH _ _ _ (.inl rfl)
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl; subst hvl
    exact make_cmp_imm_eq_correct MATCH _ _ _ (.inr rfl)
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl; subst hvl
    exact make_cmp_imm_ne_correct MATCH _ _ _ (.inr rfl)
  · exact make_cmp_base_correct MATCH _ _ _ hvl

theorem vmatch_regs (MATCH : Ematch bc e ae) :
    ∀ (rl : List Reg), ListForall2 (Vmatch bc) (e.getList rl) (rl.map (fun r => AE.get r ae))
  | [] => .nil
  | r :: rl => .cons (MATCH r) (vmatch_regs MATCH rl)

/-- `ConstpropOpproof.make_select_correct` -/
theorem make_select_correct (o : Options) (MATCH : Ematch bc e ae) (c : Condition) (ty : ATyp)
    (r1 r2 : Reg) (args : List Reg) (vl : List Aval) (hvl : vl = args.map (fun r => AE.get r ae)) :
    OpSim ge sp e m (makeSelect o c ty r1 r2 args vl)
      (Val.select (evalCondition c (e.getList args) m) (e.get r1) (e.get r2) ty) := by
  unfold makeSelect
  split
  · rename_i b RB
    refine ⟨if b then e.get r1 else e.get r2, by cases b <;> rfl, ?_⟩
    cases EC : evalCondition c (e.getList args) m with
    | none => exact .undef _
    | some b' =>
      have hb : b = b' := by
        apply resolve_branch_sound _ RB
        rw [← EC]
        subst hvl
        exact ValueAOp.eval_static_condition_sound o.toOptions c m (vmatch_regs MATCH args)
      subst hb
      exact Val.lessdef_normalize _ _
  · have EQ := cond_strength_reduction_correct (m := m) MATCH c args vl hvl
    generalize condStrengthReduction c args vl = p at EQ ⊢
    obtain ⟨c', args'⟩ := p
    refine ⟨_, rfl, ?_⟩
    simp only [Regmap.getList] at EQ ⊢
    rw [EQ]; exact .refl _


/-- Close a `Val.Lessdef` goal that holds by reflexivity or because the left
    side is `Vundef`. -/
macro "ld" : tactic => `(tactic| first | exact Val.Lessdef.refl _ | exact Val.Lessdef.undef _)

theorem int_eq_true {x y : Integers.Int} (h : Integers.Int.eq x y = true) : x = y :=
  (Integers.Int.eq_spec x y).1 h

theorem int64_eq_true {x y : Integers.Int64} (h : Integers.Int64.eq x y = true) : x = y :=
  (Integers.Int64.eq_spec x y).1 h

/-- `ConstpropOpproof.make_addimm_correct` -/
theorem make_addimm_correct (n : Integers.Int) (r : Reg) :
    OpSim ge sp e m (makeAddimm n r) (Val.add (e.get r) (.Vint n)) := by
  unfold makeAddimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · exact ⟨_, rfl, .refl _⟩
  · cases int_eq_true h
    refine ⟨e.get r, rfl, ?_⟩
    generalize e.get r = x
    cases x <;> simp [Val.add, Integers.Int.add_zero, Archi.ptr64] <;> ld

/-- `ConstpropOpproof.make_shlimm_correct` -/
theorem make_shlimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeShlimm n r1 r2) (Val.shl (e.get r1) (.Vint n)) := by
  unfold makeShlimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases L : Integers.Int.ltu n Integers.Int.iwordsize
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (evalShift .Slsl _ (mkAmount32 n))
      simp only [evalShift, SelectOpproof.mkAmount32_eq L]; ld
  · cases int_eq_true h
    refine ⟨e.get r1, rfl, ?_⟩
    generalize e.get r1 = x
    cases x <;> simp [Val.shl, Integers.Int.shl_zero] <;> ld

/-- `ConstpropOpproof.make_shrimm_correct` -/
theorem make_shrimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeShrimm n r1 r2) (Val.shr (e.get r1) (.Vint n)) := by
  unfold makeShrimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases L : Integers.Int.ltu n Integers.Int.iwordsize
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (evalShift .Sasr _ (mkAmount32 n))
      simp only [evalShift, SelectOpproof.mkAmount32_eq L]; ld
  · cases int_eq_true h
    refine ⟨e.get r1, rfl, ?_⟩
    generalize e.get r1 = x
    cases x <;> simp [Val.shr, Integers.Int.shr_zero] <;> ld

/-- `ConstpropOpproof.make_shruimm_correct` -/
theorem make_shruimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeShruimm n r1 r2) (Val.shru (e.get r1) (.Vint n)) := by
  unfold makeShruimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases L : Integers.Int.ltu n Integers.Int.iwordsize
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (evalShift .Slsr _ (mkAmount32 n))
      simp only [evalShift, SelectOpproof.mkAmount32_eq L]; ld
  · cases int_eq_true h
    refine ⟨e.get r1, rfl, ?_⟩
    generalize e.get r1 = x
    cases x <;> simp [Val.shru, Integers.Int.shru_zero] <;> ld

/-- `ConstpropOpproof.make_mulimm_correct` -/
theorem make_mulimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeMulimm n r1 r2) (Val.mul (e.get r1) (.Vint n)) := by
  unfold makeMulimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : Integers.Int.eq n Integers.Int.one
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i l P
        refine ⟨_, rfl, ?_⟩
        show Val.Lessdef _ (evalShift .Slsl _ (mkAmount32 l))
        simp only [evalShift, SelectOpproof.mkAmount32_eq (Integers.Int.is_power2_range P),
          Val.mul_pow2 _ P]; ld
      · refine ⟨_, rfl, ?_⟩
        simp only [H]; ld
    · cases int_eq_true h1
      refine ⟨e.get r1, rfl, ?_⟩
      generalize e.get r1 = x
      cases x <;> simp [Val.mul, Integers.Int.mul_one] <;> ld
  · cases int_eq_true h
    refine ⟨_, rfl, ?_⟩
    generalize e.get r1 = x
    cases x <;> simp [Val.mul, Integers.Int.mul_zero] <;> ld

/-- `ConstpropOpproof.make_divimm_correct` -/
theorem make_divimm_correct (n : Integers.Int) (r1 r2 : Reg) {v : Val}
    (hd : Val.divs (e.get r1) (e.get r2) = some v) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeDivimm n r1 r2) v := by
  unfold makeDivimm
  cases h : Integers.Int.eq n Integers.Int.one
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i l P
      split
      · rename_i L
        refine ⟨v, ?_, .refl _⟩
        rw [H] at hd
        exact Val.divs_pow2 P L hd
      · exact ⟨v, by simp only [Regmap.getList, List.map_cons, List.map_nil]; exact hd, .refl _⟩
    · exact ⟨v, by simp only [Regmap.getList, List.map_cons, List.map_nil]; exact hd, .refl _⟩
  · cases int_eq_true h
    rw [H] at hd
    refine ⟨e.get r1, rfl, ?_⟩
    revert hd
    generalize e.get r1 = x
    intro hd
    cases x <;> simp only [Val.divs, reduceCtorEq] at hd
    split at hd
    · cases hd
    · cases hd; rw [Integers.Int.divs_one]; ld

/-- `ConstpropOpproof.make_divuimm_correct` -/
theorem make_divuimm_correct (n : Integers.Int) (r1 r2 : Reg) {v : Val}
    (hd : Val.divu (e.get r1) (e.get r2) = some v) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeDivuimm n r1 r2) v := by
  unfold makeDivuimm
  cases h : Integers.Int.eq n Integers.Int.one
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i l P
      refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (evalShift .Slsr _ (mkAmount32 l))
      rw [H] at hd
      simp only [evalShift, SelectOpproof.mkAmount32_eq (Integers.Int.is_power2_range P),
        Val.divu_pow2 P hd]; ld
    · exact ⟨v, by simp only [Regmap.getList, List.map_cons, List.map_nil]; exact hd, .refl _⟩
  · cases int_eq_true h
    rw [H] at hd
    refine ⟨e.get r1, rfl, ?_⟩
    revert hd
    generalize e.get r1 = x
    intro hd
    cases x <;> simp only [Val.divu, reduceCtorEq] at hd
    split at hd
    · cases hd
    · cases hd; rw [Integers.Int.divu_one]; ld


local macro "zomega" : tactic => `(tactic| ((try simp only [Z] at *) <;> omega))

/-- `and i n = i` when `i` has no bits at or above `k` and `n` has all bits
    below `k` set. -/
theorem and_uns {k : Z} {i n : Integers.Int} (hu : IsUns k i)
    (hz : Integers.Int.zero_ext k.toNat (Integers.Int.not n) = Integers.Int.zero) :
    Integers.Int.and i n = i := by
  apply Integers.Int.same_bits_eq; intro j hj
  rw [Integers.Int.bits_and]
  by_cases hjk : (j : Z) < k
  · have h1 := congrArg (fun x => Integers.Int.testbit x j) hz
    simp only [Integers.Int.bits_zero_ext, Integers.Int.bits_zero, Integers.Int.bits_not _ hj] at h1
    have : decide (j < k.toNat) = true := by simp; zomega
    rw [this, Bool.true_and, Bool.not_eq_false'] at h1
    rw [h1, Bool.and_true]
  · have hz' : (j : Z) < Integers.Int.zwordsize := by
      have : Integers.Int.zwordsize = 32 := by decide
      rw [this]; zomega
    rw [hu j hz' (by zomega), Bool.false_and]

/-- `ConstpropOpproof.make_andimm_correct` -/
theorem make_andimm_correct (n : Integers.Int) (r : Reg) {x : Aval} (hx : Vmatch bc (e.get r) x) :
    OpSim ge sp e m (makeAndimm n r x) (Val.and (e.get r) (.Vint n)) := by
  unfold makeAndimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : Integers.Int.eq n Integers.Int.mone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases x with
      | Uns p k =>
        simp only
        split
        · rename_i UNS
          refine ⟨e.get r, rfl, ?_⟩
          generalize e.get r = v at hx ⊢
          cases hx with
          | Uns _ i _ _ hu => simp only [Val.and]; rw [and_uns hu (int_eq_true UNS)]; ld
          | Uns_undef => ld
        · exact ⟨_, rfl, .refl _⟩
      | _ => exact ⟨_, rfl, .refl _⟩
    · cases int_eq_true h1
      refine ⟨e.get r, rfl, ?_⟩
      generalize e.get r = v
      cases v <;> simp [Val.and, Integers.Int.and_mone] <;> ld
  · cases int_eq_true h
    refine ⟨_, rfl, ?_⟩
    generalize e.get r = v
    cases v <;> simp [Val.and, Integers.Int.and_zero] <;> ld

/-- `ConstpropOpproof.make_orimm_correct` -/
theorem make_orimm_correct (n : Integers.Int) (r : Reg) :
    OpSim ge sp e m (makeOrimm n r) (Val.or (e.get r) (.Vint n)) := by
  unfold makeOrimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : Integers.Int.eq n Integers.Int.mone
    · exact ⟨_, rfl, .refl _⟩
    · cases int_eq_true h1
      refine ⟨_, rfl, ?_⟩
      generalize e.get r = v
      cases v <;> simp [Val.or, Integers.Int.or_mone] <;> ld
  · cases int_eq_true h
    refine ⟨e.get r, rfl, ?_⟩
    generalize e.get r = v
    cases v <;> simp [Val.or, Integers.Int.or_zero] <;> ld

/-- `ConstpropOpproof.make_xorimm_correct` -/
theorem make_xorimm_correct (n : Integers.Int) (r : Reg) :
    OpSim ge sp e m (makeXorimm n r) (Val.xor (e.get r) (.Vint n)) := by
  unfold makeXorimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · exact ⟨_, rfl, .refl _⟩
  · cases int_eq_true h
    refine ⟨e.get r, rfl, ?_⟩
    generalize e.get r = v
    cases v <;> simp [Val.xor, Integers.Int.xor_zero] <;> ld

/-- `ConstpropOpproof.make_addlimm_correct` -/
theorem make_addlimm_correct (n : Integers.Int64) (r : Reg) :
    OpSim ge sp e m (makeAddlimm n r) (Val.addl (e.get r) (.Vlong n)) := by
  unfold makeAddlimm
  cases h : Integers.Int64.eq n Integers.Int64.zero
  · exact ⟨_, rfl, .refl _⟩
  · cases int64_eq_true h
    refine ⟨e.get r, rfl, ?_⟩
    generalize e.get r = v
    cases v <;> simp [Val.addl, Integers.Int64.add_zero, Archi.ptr64] <;> try ld
    rename_i b ofs
    have : Integers.Ptrofs.of_int64 Integers.Int64.zero = Integers.Ptrofs.zero := by decide
    rw [this, Integers.Ptrofs.add_zero]; ld

theorem ltu64_of_toNat {n : Integers.Int} (h : n.toNat < 64) :
    Integers.Int.ltu n Integers.Int64.iwordsize' = true := by
  have h64 : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq, h64]
  exact h

/-- `ConstpropOpproof.make_shllimm_correct` -/
theorem make_shllimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeShllimm n r1 r2) (Val.shll (e.get r1) (.Vint n)) := by
  unfold makeShllimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases L : Integers.Int.ltu n Integers.Int64.iwordsize'
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (evalShiftl .Slsl _ (mkAmount64 n))
      simp only [evalShiftl, SelectLongproof.mkAmount64_eq L]; ld
  · cases int_eq_true h
    refine ⟨e.get r1, rfl, ?_⟩
    generalize e.get r1 = v
    cases v
    case Vlong a =>
      rw [SelectLongproof.val_shll_long _ (by decide)]
      have : (Integers.Int.zero : Integers.Int).toNat = 0 := by decide
      rw [this, BitVec.shiftLeft_zero]; ld
    all_goals exact .undef _

/-- `ConstpropOpproof.make_shrlimm_correct` -/
theorem make_shrlimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeShrlimm n r1 r2) (Val.shrl (e.get r1) (.Vint n)) := by
  unfold makeShrlimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases L : Integers.Int.ltu n Integers.Int64.iwordsize'
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (evalShiftl .Sasr _ (mkAmount64 n))
      simp only [evalShiftl, SelectLongproof.mkAmount64_eq L]; ld
  · cases int_eq_true h
    refine ⟨e.get r1, rfl, ?_⟩
    generalize e.get r1 = v
    cases v
    case Vlong a =>
      rw [SelectLongproof.val_shrl_long _ (by decide)]
      have : (Integers.Int.zero : Integers.Int).toNat = 0 := by decide
      rw [this, BitVec.sshiftRight_zero]; ld
    all_goals exact .undef _

/-- `ConstpropOpproof.make_shrluimm_correct` -/
theorem make_shrluimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeShrluimm n r1 r2) (Val.shrlu (e.get r1) (.Vint n)) := by
  unfold makeShrluimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases L : Integers.Int.ltu n Integers.Int64.iwordsize'
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (evalShiftl .Slsr _ (mkAmount64 n))
      simp only [evalShiftl, SelectLongproof.mkAmount64_eq L]; ld
  · cases int_eq_true h
    refine ⟨e.get r1, rfl, ?_⟩
    generalize e.get r1 = v
    cases v
    case Vlong a =>
      rw [SelectLongproof.val_shrlu_long _ (by decide)]
      have : (Integers.Int.zero : Integers.Int).toNat = 0 := by decide
      rw [this, BitVec.ushiftRight_zero]; ld
    all_goals exact .undef _

/-- `ConstpropOpproof.make_mullimm_correct` -/
theorem make_mullimm_correct (n : Integers.Int64) (r1 r2 : Reg) (H : e.get r2 = .Vlong n) :
    OpSim ge sp e m (makeMullimm n r1 r2) (Val.mull (e.get r1) (.Vlong n)) := by
  unfold makeMullimm
  cases h : Integers.Int64.eq n Integers.Int64.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : Integers.Int64.eq n Integers.Int64.one
    · simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i l P
        have L := ltu64_of_toNat (Integers.Int64.is_power2'_spec P).1
        refine ⟨_, rfl, ?_⟩
        show Val.Lessdef _ (evalShiftl .Slsl _ (mkAmount64 l))
        simp only [evalShiftl, SelectLongproof.mkAmount64_eq L]
        generalize e.get r1 = v
        cases v
        case Vlong a =>
          rw [SelectLongproof.val_shll_long _ L]
          simp only [Val.mull, Integers.Int64.mul_pow2' _ P]; ld
        all_goals exact .undef _
      · refine ⟨_, rfl, ?_⟩
        simp only [H]; ld
    · cases int64_eq_true h1
      refine ⟨e.get r1, rfl, ?_⟩
      generalize e.get r1 = v
      cases v <;> simp [Val.mull, Integers.Int64.mul_one] <;> ld
  · cases int64_eq_true h
    refine ⟨_, rfl, ?_⟩
    generalize e.get r1 = v
    cases v <;> simp [Val.mull, Integers.Int64.mul_zero] <;> ld

/-- `ConstpropOpproof.make_divlimm_correct` -/
theorem make_divlimm_correct (n : Integers.Int64) (r1 r2 : Reg) {v : Val}
    (hd : Val.divls (e.get r1) (e.get r2) = some v) (H : e.get r2 = .Vlong n) :
    OpSim ge sp e m (makeDivlimm n r1 r2) v := by
  unfold makeDivlimm
  split
  · rename_i l P
    split
    · rename_i L
      refine ⟨v, ?_, .refl _⟩
      rw [H] at hd
      exact Val.divls_pow2 P L hd
    · exact ⟨v, hd, .refl _⟩
  · exact ⟨v, hd, .refl _⟩

/-- `ConstpropOpproof.make_divluimm_correct` -/
theorem make_divluimm_correct (n : Integers.Int64) (r1 r2 : Reg) {v : Val}
    (hd : Val.divlu (e.get r1) (e.get r2) = some v) (H : e.get r2 = .Vlong n) :
    OpSim ge sp e m (makeDivluimm n r1 r2) v := by
  unfold makeDivluimm
  split
  · rename_i l P
    have L := ltu64_of_toNat (Integers.Int64.is_power2'_spec P).1
    refine ⟨_, rfl, ?_⟩
    show Val.Lessdef _ (evalShiftl .Slsr _ (mkAmount64 l))
    rw [H] at hd
    simp only [evalShiftl, SelectLongproof.mkAmount64_eq L, Val.divlu_pow2 P hd]; ld
  · exact ⟨v, hd, .refl _⟩

/-- `ConstpropOpproof.make_andlimm_correct` -/
theorem make_andlimm_correct (n : Integers.Int64) (r : Reg) (x : Aval) :
    OpSim ge sp e m (makeAndlimm n r x) (Val.andl (e.get r) (.Vlong n)) := by
  unfold makeAndlimm
  cases h : Integers.Int64.eq n Integers.Int64.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : Integers.Int64.eq n Integers.Int64.mone
    · exact ⟨_, rfl, .refl _⟩
    · cases int64_eq_true h1
      refine ⟨e.get r, rfl, ?_⟩
      generalize e.get r = v
      cases v <;> simp [Val.andl, Integers.Int64.and_mone] <;> ld
  · cases int64_eq_true h
    refine ⟨_, rfl, ?_⟩
    generalize e.get r = v
    cases v <;> simp [Val.andl, Integers.Int64.and_zero] <;> ld

/-- `ConstpropOpproof.make_orlimm_correct` -/
theorem make_orlimm_correct (n : Integers.Int64) (r : Reg) :
    OpSim ge sp e m (makeOrlimm n r) (Val.orl (e.get r) (.Vlong n)) := by
  unfold makeOrlimm
  cases h : Integers.Int64.eq n Integers.Int64.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : Integers.Int64.eq n Integers.Int64.mone
    · exact ⟨_, rfl, .refl _⟩
    · cases int64_eq_true h1
      refine ⟨_, rfl, ?_⟩
      generalize e.get r = v
      cases v <;> simp [Val.orl, Integers.Int64.or_mone] <;> ld
  · cases int64_eq_true h
    refine ⟨e.get r, rfl, ?_⟩
    generalize e.get r = v
    cases v <;> simp [Val.orl, Integers.Int64.or_zero] <;> ld

/-- `ConstpropOpproof.make_xorlimm_correct` -/
theorem make_xorlimm_correct (n : Integers.Int64) (r : Reg) :
    OpSim ge sp e m (makeXorlimm n r) (Val.xorl (e.get r) (.Vlong n)) := by
  unfold makeXorlimm
  cases h : Integers.Int64.eq n Integers.Int64.zero
  · exact ⟨_, rfl, .refl _⟩
  · cases int64_eq_true h
    refine ⟨e.get r, rfl, ?_⟩
    generalize e.get r = v
    cases v <;> simp [Val.xorl, Integers.Int64.xor_zero] <;> ld


/-- `ConstpropOpproof.make_mulfimm_correct` -/
theorem make_mulfimm_correct (n : Floats.Float) (r1 r2 : Reg)
    (H : e.get r2 = .Vfloat n) :
    OpSim ge sp e m (makeMulfimm n r1 r1 r2) (Val.mulf (e.get r1) (e.get r2)) := by
  unfold makeMulfimm
  split
  · rename_i hn
    refine ⟨_, rfl, ?_⟩
    simp only [H, hn]
    generalize e.get r1 = v
    cases v
    case Vfloat f => simp only [Val.mulf, Val.addf, Floats.Float.mul2_add f]; ld
    all_goals exact .undef _
  · exact ⟨_, rfl, .refl _⟩

/-- `ConstpropOpproof.make_mulfimm_correct_2` -/
theorem make_mulfimm_correct_2 (n : Floats.Float) (r1 r2 : Reg)
    (H : e.get r1 = .Vfloat n) :
    OpSim ge sp e m (makeMulfimm n r2 r1 r2) (Val.mulf (e.get r1) (e.get r2)) := by
  unfold makeMulfimm
  split
  · rename_i hn
    refine ⟨_, rfl, ?_⟩
    simp only [H, hn]
    generalize e.get r2 = v
    cases v
    case Vfloat f =>
      simp only [Val.mulf, Val.addf]
      rw [Floats.Float.mul_commut _ _ (.inl (by decide)), Floats.Float.mul2_add f]; ld
    all_goals exact .undef _
  · exact ⟨_, rfl, .refl _⟩

/-- `ConstpropOpproof.make_mulfsimm_correct` -/
theorem make_mulfsimm_correct (n : Floats.Float32) (r1 r2 : Reg)
    (H : e.get r2 = .Vsingle n) :
    OpSim ge sp e m (makeMulfsimm n r1 r1 r2) (Val.mulfs (e.get r1) (e.get r2)) := by
  unfold makeMulfsimm
  split
  · rename_i hn
    refine ⟨_, rfl, ?_⟩
    simp only [H, hn]
    generalize e.get r1 = v
    cases v
    case Vsingle f => simp only [Val.mulfs, Val.addfs, Floats.Float32.mul2_add f]; ld
    all_goals exact .undef _
  · exact ⟨_, rfl, .refl _⟩

/-- `ConstpropOpproof.make_mulfsimm_correct_2` -/
theorem make_mulfsimm_correct_2 (n : Floats.Float32) (r1 r2 : Reg)
    (H : e.get r1 = .Vsingle n) :
    OpSim ge sp e m (makeMulfsimm n r2 r1 r2) (Val.mulfs (e.get r1) (e.get r2)) := by
  unfold makeMulfsimm
  split
  · rename_i hn
    refine ⟨_, rfl, ?_⟩
    simp only [H, hn]
    generalize e.get r2 = v
    cases v
    case Vsingle f =>
      simp only [Val.mulfs, Val.addfs]
      rw [Floats.Float32.mul_commut _ _ (.inl (by decide)), Floats.Float32.mul2_add f]; ld
    all_goals exact .undef _
  · exact ⟨_, rfl, .refl _⟩

/-- `ConstpropOpproof.make_zext_correct` -/
theorem make_zext_correct (s : Z) (r : Reg) {x : Aval} (hx : Vmatch bc (e.get r) x) :
    OpSim ge sp e m (makeZext s r x) (Val.zeroExt s.toNat (e.get r)) := by
  unfold makeZext
  split
  · rename_i INCL
    refine ⟨e.get r, rfl, ?_⟩
    have V := vmatch_ge (vincl_ge INCL) hx
    generalize e.get r = v at V ⊢
    cases V with
    | Uns _ i _ hk hu => simp only [Val.zeroExt]; rw [(is_uns_zero_ext_Z hk i).1 hu]; ld
    | Uns_undef => ld
  · exact ⟨_, rfl, .refl _⟩

/-- `ConstpropOpproof.make_sext_correct` -/
theorem make_sext_correct (s : Z) (r : Reg) {x : Aval} (hx : Vmatch bc (e.get r) x) :
    OpSim ge sp e m (makeSext s r x) (Val.signExt s.toNat (e.get r)) := by
  unfold makeSext
  split
  · rename_i INCL
    refine ⟨e.get r, rfl, ?_⟩
    have V := vmatch_ge (vincl_ge INCL) hx
    generalize e.get r = v at V ⊢
    cases V with
    | Sgn _ i _ hk hu => simp only [Val.signExt]; rw [(is_sgn_sign_ext_Z hk i).1 hu]; ld
    | Sgn_undef => ld
  · exact ⟨_, rfl, .refl _⟩

end STRENGTH_REDUCTION

end ConstpropOpproof
end CC
