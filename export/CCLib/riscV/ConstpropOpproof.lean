/-
  Correctness of strength reduction for the RISC-V back end — port of
  `riscV/ConstpropOpproof.v`: `match_G`, `match_S`,
  `const_for_result_correct`, `cond_strength_reduction_correct`,
  `make_cmp_base_correct`, `make_cmp_correct`, the `make_*_correct` lemmas
  for the individual operators, `op_strength_reduction_correct` and
  `addr_strength_reduction_correct`.

  Differences from Rocq: as in `CCLib/aarch64/ConstpropOpproof.lean`, the
  `let (op, args) := … in ∃ v, …` statements are phrased with the predicate
  `OpSim`.  The target-independent helpers (reading
  exact abstract values, `cmp_bool01`, …) are reused from the aarch64 file.
-/
import CCLib.riscV.ConstpropOp
import CCLib.aarch64.ConstpropOpproof2

namespace CC
namespace RiscV
namespace ConstpropOpproof

open ValueDomain Op ConstpropOp
open CC.ConstpropOp (Options)
open CC.ConstpropOpproof (get_I get_L get_F get_FS uns1_cases
  cmp_bool01 vmatch_regs int_eq_true int64_eq_true and_uns ltu64_of_toNat vmatch_of_eq)
open Integers (Ptrofs)

section STRENGTH_REDUCTION
variable {F V : Type} (ge : Genv F V) {bc : BlockClassification} (sp : Block) (ae : Aenv)
  (e : RTL.Regset) (m : Mem)

/-- `∃ v', eval_operation ge (Vptr sp 0) op e##args m = Some v' ∧ Val.lessdef v v'`
    for the result `(op, args)` of a strength reduction. -/
def OpSim (oa : Operation × List Reg) (v : Val) : Prop :=
  ∃ w, evalOperation ge (.Vptr sp Ptrofs.zero) oa.1 (e.getList oa.2) m = some w ∧ Val.Lessdef v w

variable {ge sp ae e m}

/-- `ConstpropOpproof.match_G` -/
theorem match_G (GENV : GenvMatch bc ge) (MATCH : Ematch bc e ae) {r : Reg} {id : Ident}
    {ofs : Ptrofs} (h : AE.get r ae = .Ptr (.Gl id ofs)) :
    Val.Lessdef (e.get r) (Genv.symbolAddress ge id ofs) := by
  have := MATCH r; rw [h] at this
  exact vmatch_ptr_gl GENV this

/-- `ConstpropOpproof.match_S` -/
theorem match_S (STACK : bc sp = .BCstack) (MATCH : Ematch bc e ae) {r : Reg} {ofs : Ptrofs}
    (h : AE.get r ae = .Ptr (.Stk ofs)) : Val.Lessdef (e.get r) (.Vptr sp ofs) := by
  have := MATCH r; rw [h] at this
  exact vmatch_ptr_stk this STACK

/-- `ConstpropOpproof.const_for_result_correct` -/
theorem const_for_result_correct (o : Options) (GENV : GenvMatch bc ge) (STACK : bc sp = .BCstack)
    {a : Aval} {op : Operation} {v : Val} (h : constForResult o a = some op) (hv : Vmatch bc v a) :
    ∃ v', evalOperation ge (.Vptr sp Ptrofs.zero) op [] m = some v' ∧ Val.Lessdef v v' := by
  cases a with
  | I n => simp only [constForResult, Option.some.injEq] at h; subst h; cases hv; exact ⟨_, rfl, .refl _⟩
  | IU n =>
    simp only [constForResult, Option.some.injEq] at h; subst h
    exact ⟨_, rfl, by cases hv <;> constructor⟩
  | L n =>
    simp only [constForResult, Archi.ptr64, if_true, Option.some.injEq] at h; subst h; cases hv
    exact ⟨_, rfl, .refl _⟩
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

set_option hygiene false in
/-- Rocq's `InvApproxRegs; SimplVM` for two arguments (integer constants). -/
local macro "simplvm2" MATCH:term "," hvl:ident : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at $hvl:ident
  obtain ⟨h1, h2⟩ := $hvl:ident
  simp only [Regmap.getList, List.map_cons, List.map_nil]
  first
    | simp only [get_I $MATCH h1.symm] | simp only [get_L $MATCH h1.symm] | skip
  first
    | simp only [get_I $MATCH h2.symm] | simp only [get_L $MATCH h2.symm] | skip))

/-- `ConstpropOpproof.cond_strength_reduction_correct` -/
theorem cond_strength_reduction_correct (MATCH : Ematch bc e ae) (cond : Condition)
    (args : List Reg) (vl : List Aval) (hvl : vl = args.map (fun r => AE.get r ae)) :
    evalCondition (condStrengthReduction cond args vl).1
      (e.getList (condStrengthReduction cond args vl).2) m =
    evalCondition cond (e.getList args) m := by
  unfold condStrengthReduction
  split
  case h_9 => rfl
  all_goals simplvm2 MATCH, hvl
  all_goals (try simp only [evalCondition])
  all_goals first
    | exact Val.swap_cmp_bool _ _ _
    | exact Val.swap_cmpu_bool _ _ _ _
    | exact Val.swap_cmpl_bool _ _ _
    | exact Val.swap_cmplu_bool _ _ _ _
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

/-- Close a `Val.Lessdef` goal that holds by reflexivity or because the left
    side is `Vundef`. -/
local macro "ld" : tactic => `(tactic| first | exact Val.Lessdef.refl _ | exact Val.Lessdef.undef _)

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
    cases Integers.Int.ltu n Integers.Int.iwordsize
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · exact ⟨_, rfl, .refl _⟩
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
    cases Integers.Int.ltu n Integers.Int.iwordsize
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · exact ⟨_, rfl, .refl _⟩
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
    cases Integers.Int.ltu n Integers.Int.iwordsize
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · exact ⟨_, rfl, .refl _⟩
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
        rw [Val.mul_pow2 _ P]; ld
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
      rw [H] at hd
      show Val.Lessdef v (Val.shru (e.get r1) (.Vint l))
      rw [Val.divu_pow2 P hd]; ld
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

/-- `ConstpropOpproof.make_moduimm_correct` -/
theorem make_moduimm_correct (n : Integers.Int) (r1 r2 : Reg) {v : Val}
    (hd : Val.modu (e.get r1) (e.get r2) = some v) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeModuimm n r1 r2) v := by
  unfold makeModuimm
  split
  · rename_i l P
    refine ⟨_, rfl, ?_⟩
    rw [H] at hd
    show Val.Lessdef v (Val.and (e.get r1) (.Vint (Integers.Int.sub n Integers.Int.one)))
    rw [Val.modu_pow2 P hd]; ld
  · exact ⟨v, by simp only [Regmap.getList, List.map_cons, List.map_nil]; exact hd, .refl _⟩

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

/-- `ConstpropOpproof.make_shllimm_correct` -/
theorem make_shllimm_correct (n : Integers.Int) (r1 r2 : Reg) (H : e.get r2 = .Vint n) :
    OpSim ge sp e m (makeShllimm n r1 r2) (Val.shll (e.get r1) (.Vint n)) := by
  unfold makeShllimm
  cases h : Integers.Int.eq n Integers.Int.zero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases Integers.Int.ltu n Integers.Int64.iwordsize'
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · exact ⟨_, rfl, .refl _⟩
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
    cases Integers.Int.ltu n Integers.Int64.iwordsize'
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · exact ⟨_, rfl, .refl _⟩
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
    cases Integers.Int.ltu n Integers.Int64.iwordsize'
    · refine ⟨_, rfl, ?_⟩
      simp only [H]; ld
    · exact ⟨_, rfl, .refl _⟩
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
        show Val.Lessdef _ (Val.shll (e.get r1) (.Vint l))
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
    refine ⟨_, rfl, ?_⟩
    show Val.Lessdef _ (Val.shrlu (e.get r1) (.Vint l))
    rw [H] at hd
    rw [Val.divlu_pow2 P hd]; ld
  · exact ⟨v, hd, .refl _⟩

/-- `ConstpropOpproof.make_modluimm_correct` -/
theorem make_modluimm_correct (n : Integers.Int64) (r1 r2 : Reg) {v : Val}
    (hd : Val.modlu (e.get r1) (e.get r2) = some v) (H : e.get r2 = .Vlong n) :
    OpSim ge sp e m (makeModluimm n r1 r2) v := by
  unfold makeModluimm
  split
  · rename_i l P
    refine ⟨_, rfl, ?_⟩
    rw [H] at hd
    show Val.Lessdef v (Val.andl (e.get r1) (.Vlong (Integers.Int64.sub n Integers.Int64.one)))
    rw [Val.modlu_pow2 P hd]; ld
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

/-- Shared proof of the two `make_cast*_correct` lemmas. -/
private theorem make_sext_like {r : Reg} {x : Aval} {k : Nat} {op : Operation} (hk : 0 < k)
    (hx : Vmatch bc (e.get r) x)
    (hop : evalOperation ge (.Vptr sp Ptrofs.zero) op [e.get r] m =
      some (Val.signExt k (e.get r))) :
    OpSim ge sp e m (if vincl x (.Sgn .Ptop k) then (.Omove, [r]) else (op, [r]))
      (Val.signExt k (e.get r)) := by
  split
  · rename_i INCL
    refine ⟨e.get r, rfl, ?_⟩
    have Vm := vmatch_ge (vincl_ge INCL) hx
    generalize e.get r = v at Vm ⊢
    cases Vm with
    | Sgn _ i _ _ hu => simp only [Val.signExt]; rw [(is_sgn_sign_ext hk i).1 hu]; ld
    | Sgn_undef => ld
  · exact ⟨_, hop, .refl _⟩

/-- `ConstpropOpproof.make_cast8signed_correct` -/
theorem make_cast8signed_correct (r : Reg) {x : Aval} (hx : Vmatch bc (e.get r) x) :
    OpSim ge sp e m (makeCast8signed r x) (Val.signExt 8 (e.get r)) :=
  make_sext_like (op := .Ocast8signed) (by decide) hx rfl

/-- `ConstpropOpproof.make_cast16signed_correct` -/
theorem make_cast16signed_correct (r : Reg) {x : Aval} (hx : Vmatch bc (e.get r) x) :
    OpSim ge sp e m (makeCast16signed r x) (Val.signExt 16 (e.get r)) :=
  make_sext_like (op := .Ocast16signed) (by decide) hx rfl

/-- `ConstpropOpproof.op_strength_reduction_correct` -/
theorem op_strength_reduction_correct
    (MATCH : Ematch bc e ae) (op : Operation)
    (args : List Reg) (vl : List Aval) (v : Val)
    (hvl : vl = args.map (fun r => AE.get r ae))
    (hev : evalOperation ge (.Vptr sp Ptrofs.zero) op (e.getList args) m = some v) :
    OpSim ge sp e m (opStrengthReduction op args vl) v := by
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
    try simp only [Val.sub_add_opp, Val.subl_addl_opp]
  all_goals have MATCH' : ∀ r, Vmatch bc (e.get r) (AE.get r ae) := MATCH
  all_goals with_reducible first
    | exact make_cast8signed_correct _ (MATCH' _)
    | exact make_cast16signed_correct _ (MATCH' _)
    | exact make_addimm_correct _ _
    | (rw [Val.add_commut]; exact make_addimm_correct _ _)
    | exact make_mulimm_correct _ _ _ H2
    | (rw [Val.mul_commut]; exact make_mulimm_correct _ _ _ H1)
    | exact make_divimm_correct _ _ _ hev H2
    | exact make_divuimm_correct _ _ _ hev H2
    | exact make_moduimm_correct _ _ _ hev H2
    | exact make_andimm_correct _ _ (MATCH' _)
    | (rw [Val.and_commut]; exact make_andimm_correct _ _ (MATCH' _))
    | exact make_orimm_correct _ _
    | (rw [Val.or_commut]; exact make_orimm_correct _ _)
    | exact make_xorimm_correct _ _
    | (rw [Val.xor_commut]; exact make_xorimm_correct _ _)
    | exact make_shlimm_correct _ _ _ H2
    | exact make_shrimm_correct _ _ _ H2
    | exact make_shruimm_correct _ _ _ H2
    | exact make_addlimm_correct _ _
    | (rw [Val.addl_commut]; exact make_addlimm_correct _ _)
    | exact make_mullimm_correct _ _ _ H2
    | (rw [Val.mull_commut]; exact make_mullimm_correct _ _ _ H1)
    | exact make_divlimm_correct _ _ _ hev H2
    | exact make_divluimm_correct _ _ _ hev H2
    | exact make_modluimm_correct _ _ _ hev H2
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
  case h_3 => exact ⟨res, hev, .refl _⟩
  all_goals
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvl
    simp only [Regmap.getList, List.map_cons, List.map_nil] at hev
    unfold evalAddressing at hev
    simp only [Option.some.injEq] at hev
    subst hev
  · split
    · exact ⟨_, rfl, .refl _⟩
    · refine ⟨_, rfl, ?_⟩
      show Val.Lessdef _ (Genv.symbolAddress ge _ (Ptrofs.add _ _))
      rw [Genv.shift_symbolAddress]
      exact Val.offset_ptr_lessdef _ (vmatch_ptr_gl GENV (vmatch_of_eq MATCH hvl))
  · refine ⟨_, rfl, ?_⟩
    show Val.Lessdef _ (Val.offsetPtr (.Vptr sp Ptrofs.zero) (Ptrofs.add _ _))
    simp only [Val.offsetPtr, Ptrofs.add_zero_l]
    exact Val.offset_ptr_lessdef _ (vmatch_ptr_stk (vmatch_of_eq MATCH hvl) STACK)

end STRENGTH_REDUCTION

end ConstpropOpproof
end RiscV
end CC
