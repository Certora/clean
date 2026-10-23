/-
  Correctness of instruction selection for operators (x86), part 3 — port
  of `x86/SelectOpproof.v`: division and modulus, floating-point operations,
  comparisons, integer casts, conversions, `select`, addressing modes and
  built-in arguments.

  `eval_intuofsingle` and `eval_singleofintu` use `Float32.to_intu_double` /
  `Float32.of_intu_double` from `CCLib.lib.FloatsConv`.
-/
import CCLib.x86.SelectOpproof2
import CCLib.x86.OpTheory
import CCLib.lib.FloatsLemmas
import CCLib.lib.FloatsConv

namespace CC
namespace X86
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `Val.swap_cmpu_bool` -/
theorem val_swap_cmpu_bool (vp : Block → Z → Bool) (c : Comparison) (x y : Val) :
    Val.cmpu_bool vp c.swap x y = Val.cmpu_bool vp c y x := by
  cases x <;> cases y <;> simp [Val.cmpu_bool, Archi.ptr64, Integers.Int.swap_cmpu]

theorem loword_repr (z : _root_.Int) :
    Integers.Int64.loword (Integers.Int64.repr z) = Integers.Int.repr z := by
  show (BitVec.ofInt 64 z).truncate 32 = BitVec.ofInt 32 z
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Integer division and modulus -/

/-- `eval_divs_base` -/
theorem eval_divsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divs x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divsBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_mods_base` -/
theorem eval_modsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.mods x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modsBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_divu_base` -/
theorem eval_divuBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divuBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_modu_base` -/
theorem eval_moduBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (moduBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_shrximm` -/
theorem eval_shrximm {le : Letenv} {a : SelectOp.Expr} {n : Integers.Int} {x z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hz : Val.shrx x (.Vint n) = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (shrximm a n) v ∧ Val.Lessdef z v := by
  unfold shrximm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    refine ⟨x, ha, ?_⟩
    cases x <;> simp [Val.shrx] at hz
    · obtain rfl := hz.2
      rw [Integers.Int.shrx_zero]; ld
  · rw [if_neg h0]
    exact ⟨z, eval_op1 ha hz, .refl _⟩

/-! ### Floating-point operations -/

theorem eval_negf : UnarySound ge sp e m negf Val.negf :=
  fun _ _ _ hx => ⟨_, eval_op1 hx rfl, .refl _⟩
theorem eval_absf : UnarySound ge sp e m absf Val.absf :=
  fun _ _ _ hx => ⟨_, eval_op1 hx rfl, .refl _⟩
theorem eval_addf : BinarySound ge sp e m addf Val.addf :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩
theorem eval_subf : BinarySound ge sp e m subf Val.subf :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩
theorem eval_mulf : BinarySound ge sp e m mulf Val.mulf :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩
theorem eval_negfs : UnarySound ge sp e m negfs Val.negfs :=
  fun _ _ _ hx => ⟨_, eval_op1 hx rfl, .refl _⟩
theorem eval_absfs : UnarySound ge sp e m absfs Val.absfs :=
  fun _ _ _ hx => ⟨_, eval_op1 hx rfl, .refl _⟩
theorem eval_addfs : BinarySound ge sp e m addfs Val.addfs :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩
theorem eval_subfs : BinarySound ge sp e m subfs Val.subfs :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩
theorem eval_mulfs : BinarySound ge sp e m mulfs Val.mulfs :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩

/-- `eval_compf` -/
theorem eval_compf (c : Comparison) : BinarySound ge sp e m (compf c) (Val.cmpf c) :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩

/-- `eval_compfs` -/
theorem eval_compfs (c : Comparison) : BinarySound ge sp e m (compfs c) (Val.cmpfs c) :=
  fun _ _ _ _ _ hx hy => ⟨_, eval_op2 hx hy rfl, .refl _⟩

/-! ### Comparisons against an immediate (`Section COMP_IMM`) -/

section COMP_IMM
variable (default : Comparison → Integers.Int → Condition)
  (intsem : Comparison → Integers.Int → Integers.Int → Bool)
  (vsem : Comparison → Val → Val → Val)

/-- The hypotheses of `Section COMP_IMM`. -/
structure CompImmHyps (m : Mem) : Prop where
  sem_int : ∀ c x y, vsem c (.Vint x) (.Vint y) = Val.ofBool (intsem c x y)
  sem_undef : ∀ c v, vsem c .Vundef v = .Vundef
  sem_eq : ∀ x y, vsem .Ceq (.Vint x) (.Vint y) = Val.ofBool (Integers.Int.eq x y)
  sem_ne : ∀ x y, vsem .Cne (.Vint x) (.Vint y) = Val.ofBool (!Integers.Int.eq x y)
  sem_default : ∀ c v n, vsem c v (.Vint n) = Val.ofOptbool (evalCondition (default c n) [v] m)

variable {default intsem vsem}

theorem int_eq_one_zero : Integers.Int.eq Integers.Int.one Integers.Int.zero = false := by decide
theorem int_eq_zero_one : Integers.Int.eq Integers.Int.zero Integers.Int.one = false := by decide

theorem ofBool_int (b : Bool) :
    Val.ofBool b = .Vint (if b then Integers.Int.one else Integers.Int.zero) := by
  cases b <;> rfl

theorem vsem_ofBool_eq (H : CompImmHyps default intsem vsem m) (b : Bool) (n : Integers.Int) :
    vsem .Ceq (Val.ofBool b) (.Vint n) =
      Val.ofBool (Integers.Int.eq (if b then Integers.Int.one else Integers.Int.zero) n) := by
  rw [ofBool_int, H.sem_eq]

theorem vsem_ofBool_ne (H : CompImmHyps default intsem vsem m) (b : Bool) (n : Integers.Int) :
    vsem .Cne (Val.ofBool b) (.Vint n) =
      Val.ofBool (!Integers.Int.eq (if b then Integers.Int.one else Integers.Int.zero) n) := by
  rw [ofBool_int, H.sem_ne]

theorem compimm_ocmp_eq (H : CompImmHyps default intsem vsem m) (ob : Option Bool) :
    Val.Lessdef (vsem .Ceq (Val.ofOptbool ob) (.Vint Integers.Int.zero))
      (Val.ofOptbool (ob.map (!·))) := by
  cases ob with
  | none => rw [Val.ofOptbool, H.sem_undef]; ld
  | some b =>
    simp only [Val.ofOptbool, Option.map]
    rw [vsem_ofBool_eq H]
    cases b
    · rw [if_neg (by decide), Integers.Int.eq_true]; exact .refl _
    · rw [if_pos rfl, int_eq_one_zero]; exact .refl _

theorem compimm_ocmp_eq1 (H : CompImmHyps default intsem vsem m) (ob : Option Bool) :
    Val.Lessdef (vsem .Ceq (Val.ofOptbool ob) (.Vint Integers.Int.one)) (Val.ofOptbool ob) := by
  cases ob with
  | none => rw [Val.ofOptbool, H.sem_undef]; ld
  | some b =>
    simp only [Val.ofOptbool]
    rw [vsem_ofBool_eq H]
    cases b
    · rw [if_neg (by decide), int_eq_zero_one]; exact .refl _
    · rw [if_pos rfl, Integers.Int.eq_true]; exact .refl _

theorem compimm_ocmp_ne (H : CompImmHyps default intsem vsem m) (ob : Option Bool) :
    Val.Lessdef (vsem .Cne (Val.ofOptbool ob) (.Vint Integers.Int.zero)) (Val.ofOptbool ob) := by
  cases ob with
  | none => rw [Val.ofOptbool, H.sem_undef]; ld
  | some b =>
    simp only [Val.ofOptbool]
    rw [vsem_ofBool_ne H]
    cases b
    · rw [if_neg (by decide), Integers.Int.eq_true]; exact .refl _
    · rw [if_pos rfl, int_eq_one_zero]; exact .refl _

theorem compimm_ocmp_ne1 (H : CompImmHyps default intsem vsem m) (ob : Option Bool) :
    Val.Lessdef (vsem .Cne (Val.ofOptbool ob) (.Vint Integers.Int.one))
      (Val.ofOptbool (ob.map (!·))) := by
  cases ob with
  | none => rw [Val.ofOptbool, H.sem_undef]; ld
  | some b =>
    simp only [Val.ofOptbool, Option.map]
    rw [vsem_ofBool_ne H]
    cases b
    · rw [if_neg (by decide), int_eq_zero_one]; exact .refl _
    · rw [if_pos rfl, Integers.Int.eq_true]; exact .refl _

theorem compimm_ocmp_eq_other (H : CompImmHyps default intsem vsem m) (ob : Option Bool)
    {n : Integers.Int} (hz : n ≠ Integers.Int.zero) (ho : n ≠ Integers.Int.one) :
    Val.Lessdef (vsem .Ceq (Val.ofOptbool ob) (.Vint n)) (.Vint Integers.Int.zero) := by
  cases ob with
  | none => rw [Val.ofOptbool, H.sem_undef]; ld
  | some b =>
    simp only [Val.ofOptbool]
    rw [vsem_ofBool_eq H]
    cases b
    · rw [if_neg (by decide), Integers.Int.eq_false (Ne.symm hz)]; exact .refl _
    · rw [if_pos rfl, Integers.Int.eq_false (Ne.symm ho)]; exact .refl _

theorem compimm_ocmp_ne_other (H : CompImmHyps default intsem vsem m) (ob : Option Bool)
    {n : Integers.Int} (hz : n ≠ Integers.Int.zero) (ho : n ≠ Integers.Int.one) :
    Val.Lessdef (vsem .Cne (Val.ofOptbool ob) (.Vint n)) (.Vint Integers.Int.one) := by
  cases ob with
  | none => rw [Val.ofOptbool, H.sem_undef]; ld
  | some b =>
    simp only [Val.ofOptbool]
    rw [vsem_ofBool_ne H]
    cases b
    · rw [if_neg (by decide), Integers.Int.eq_false (Ne.symm hz)]; exact .refl _
    · rw [if_pos rfl, Integers.Int.eq_false (Ne.symm ho)]; exact .refl _

/-- `eval_compimm` -/
theorem eval_compimm (H : CompImmHyps default intsem vsem m) {le : Letenv} (c : Comparison)
    {a : SelectOp.Expr} (n2 : Integers.Int) {x : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (compimm default intsem c a n2) v ∧
      Val.Lessdef (vsem c x (.Vint n2)) v := by
  unfold compimm
  split
  · obtain rfl := inv_intconst hx
    refine ⟨_, eval_op0 rfl, ?_⟩
    rw [H.sem_int, ofBool_int]; exact .refl _
  · next c0 el =>
    obtain ⟨vl, hl, ho⟩ := inv_op hx
    obtain rfl : Val.ofOptbool (evalCondition c0 vl m) = x := Option.some.inj ho
    by_cases hz : n2 = Integers.Int.zero
    · subst hz
      rw [if_pos rfl]
      refine ⟨_, .Eop _ _ _ _ _ hl rfl, ?_⟩
      show Val.Lessdef _ (Val.ofOptbool (evalCondition (negateCondition c0) vl m))
      rw [Op.eval_negateCondition]
      exact compimm_ocmp_eq H _
    rw [if_neg hz]
    by_cases ho1 : n2 = Integers.Int.one
    · subst ho1
      rw [if_pos rfl]
      exact ⟨_, .Eop _ _ _ _ _ hl rfl, compimm_ocmp_eq1 H _⟩
    rw [if_neg ho1]
    exact ⟨_, eval_op0 rfl, compimm_ocmp_eq_other H _ hz ho1⟩
  · next c0 el =>
    obtain ⟨vl, hl, ho⟩ := inv_op hx
    obtain rfl : Val.ofOptbool (evalCondition c0 vl m) = x := Option.some.inj ho
    by_cases hz : n2 = Integers.Int.zero
    · subst hz
      rw [if_pos rfl]
      exact ⟨_, .Eop _ _ _ _ _ hl rfl, compimm_ocmp_ne H _⟩
    rw [if_neg hz]
    by_cases ho1 : n2 = Integers.Int.one
    · subst ho1
      rw [if_pos rfl]
      refine ⟨_, .Eop _ _ _ _ _ hl rfl, ?_⟩
      show Val.Lessdef _ (Val.ofOptbool (evalCondition (negateCondition c0) vl m))
      rw [Op.eval_negateCondition]
      exact compimm_ocmp_ne1 H _
    rw [if_neg ho1]
    exact ⟨_, eval_op0 rfl, compimm_ocmp_ne_other H _ hz ho1⟩
  · split
    · next hz =>
      subst hz
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      cases v1 <;> simp only [Val.and, H.sem_undef, evalCondition, Val.maskzero_bool,
        Val.ofOptbool] <;> try ld
      rw [H.sem_eq]; exact .refl _
    · exact ⟨_, eval_op1 hx rfl, by rw [H.sem_default]; ld⟩
  · split
    · next hz =>
      subst hz
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      cases v1 <;> simp only [Val.and, H.sem_undef, evalCondition, Val.maskzero_bool,
        Val.ofOptbool, Option.map] <;> try ld
      rw [H.sem_ne]; exact .refl _
    · exact ⟨_, eval_op1 hx rfl, by rw [H.sem_default]; ld⟩
  · exact ⟨_, eval_op1 hx rfl, by rw [H.sem_default]; ld⟩

/-- `eval_compimm_swap` -/
theorem eval_compimm_swap (H : CompImmHyps default intsem vsem m)
    (sem_swap : ∀ c x y, vsem c.swap x y = vsem c y x) {le : Letenv} (c : Comparison)
    {a : SelectOp.Expr} (n2 : Integers.Int) {x : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (compimm default intsem c.swap a n2) v ∧
      Val.Lessdef (vsem c (.Vint n2) x) v := by
  rw [← sem_swap]; exact eval_compimm H c.swap n2 hx

end COMP_IMM

theorem compImmHyps_cmp : CompImmHyps .Ccompimm Integers.Int.cmp Val.cmp m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem compImmHyps_cmpu :
    CompImmHyps .Ccompuimm Integers.Int.cmpu (Val.cmpu (Mem.validPointer m)) m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- `eval_comp` -/
theorem eval_comp (c : Comparison) : BinarySound ge sp e m (comp c) (Val.cmp c) := by
  intro le a x b y hx hy
  unfold comp
  split
  · obtain rfl := inv_intconst hx
    exact eval_compimm_swap compImmHyps_cmp
      (fun c x y => by simp only [Val.cmp, Val.swap_cmp_bool]) c _ hy
  · obtain rfl := inv_intconst hy
    exact eval_compimm compImmHyps_cmp c _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_compu` -/
theorem eval_compu (c : Comparison) :
    BinarySound ge sp e m (compu c) (Val.cmpu (Mem.validPointer m) c) := by
  intro le a x b y hx hy
  unfold compu
  split
  · obtain rfl := inv_intconst hx
    exact eval_compimm_swap compImmHyps_cmpu
      (fun c x y => by simp only [Val.cmpu, val_swap_cmpu_bool]) c _ hy
  · obtain rfl := inv_intconst hy
    exact eval_compimm compImmHyps_cmpu c _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Integer casts -/

/-- `eval_cast8signed` -/
theorem eval_cast8signed : UnarySound ge sp e m cast8signed (Val.signExt 8) := by
  intro le a x hx
  unfold cast8signed
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · exact ⟨_, eval_op1 hx rfl, .refl _⟩

/-- `eval_cast16signed` -/
theorem eval_cast16signed : UnarySound ge sp e m cast16signed (Val.signExt 16) := by
  intro le a x hx
  unfold cast16signed
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · exact ⟨_, eval_op1 hx rfl, .refl _⟩

theorem val_zeroExt_and (v : Val) (k : Nat) (n : Integers.Int) :
    Val.zeroExt k (Val.and v (.Vint n)) =
      Val.and v (.Vint (Integers.Int.and (Integers.Int.repr ((2 : Z) ^ k - 1)) n)) := by
  cases v <;> simp [Val.and, Val.zeroExt]
  rw [Integers.Int.zero_ext_and, Integers.Int.and_assoc, Integers.Int.and_commut n]

/-- `eval_cast8unsigned` -/
theorem eval_cast8unsigned : UnarySound ge sp e m cast8unsigned (Val.zeroExt 8) := by
  intro le a x hx
  unfold cast8unsigned
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · next n t =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    rw [val_zeroExt_and]
    exact eval_andimm _ le _ _ h1
  · exact ⟨_, eval_op1 hx rfl, .refl _⟩

/-- `eval_cast16unsigned` -/
theorem eval_cast16unsigned : UnarySound ge sp e m cast16unsigned (Val.zeroExt 16) := by
  intro le a x hx
  unfold cast16unsigned
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · next n t =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    rw [val_zeroExt_and]
    exact eval_andimm _ le _ _ h1
  · exact ⟨_, eval_op1 hx rfl, .refl _⟩

/-! ### Selection -/

theorem select_negb (ob : Option Bool) (v1 v2 : Val) (ty : ATyp) :
    Val.select (ob.map (!·)) v2 v1 ty = Val.select ob v1 v2 ty := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

/-- `eval_select`.  (Rocq additionally assumes `select_supported ty = true`; the proof does
not need it.) -/
theorem eval_select {le : Letenv} (ty : ATyp) (cond : Condition) {al : SelectOp.Exprlist}
    {vl : List Val} {a1 a2 : SelectOp.Expr} {v1 v2 : Val}
    (hl : CminorSel.EvalExprlist ge sp e m le al vl)
    (h1 : CminorSel.EvalExpr ge sp e m le a1 v1) (h2 : CminorSel.EvalExpr ge sp e m le a2 v2) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (select ty cond al a1 a2) v ∧
      Val.Lessdef (Val.select (evalCondition cond vl m) v1 v2 ty) v := by
  unfold select
  split
  · refine ⟨_, .Eop _ _ _ _ _ (.Econs _ _ _ _ _ h2 (.Econs _ _ _ _ _ h1 hl)) rfl, ?_⟩
    show Val.Lessdef _ (Val.select (evalCondition (negateCondition cond) vl m) v2 v1 ty)
    rw [Op.eval_negateCondition, select_negb]; ld
  · exact ⟨_, .Eop _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 hl)) rfl, .refl _⟩

/-! ### Floating-point conversions -/

/-- `eval_singleoffloat` -/
theorem eval_singleoffloat : UnarySound ge sp e m singleoffloat Val.singleoffloat :=
  fun _ _ _ hx => ⟨_, eval_op1 hx rfl, .refl _⟩

/-- `eval_floatofsingle` -/
theorem eval_floatofsingle : UnarySound ge sp e m floatofsingle Val.floatofsingle :=
  fun _ _ _ hx => ⟨_, eval_op1 hx rfl, .refl _⟩

/-- `eval_intoffloat` -/
theorem eval_intoffloat {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.intoffloat x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (intoffloat a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_intofsingle` -/
theorem eval_intofsingle {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.intofsingle x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (intofsingle a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_floatofint` -/
theorem eval_floatofint {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.floatofint x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (floatofint a) v ∧ Val.Lessdef y v := by
  unfold floatofint
  split
  · obtain rfl := inv_intconst ha
    simp only [Val.floatofint] at hy; cases hy
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · exact ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_singleofint` -/
theorem eval_singleofint {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.singleofint x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (singleofint a) v ∧ Val.Lessdef y v := by
  unfold singleofint
  split
  · obtain rfl := inv_intconst ha
    simp only [Val.singleofint] at hy; cases hy
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · exact ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_intuoffloat` (64-bit configuration: via a conversion to a 64-bit integer). -/
theorem eval_intuoffloat {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.intuoffloat x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (intuoffloat a) v ∧ Val.Lessdef y v := by
  unfold intuoffloat
  simp only [Archi.splitlong, Bool.false_eq_true, if_false]
  cases x with
  | Vfloat f =>
    simp only [Val.intuoffloat] at hy
    cases hf : Floats.Float.toIntu f with
    | none => rw [hf] at hy; cases hy
    | some n =>
      rw [hf] at hy; cases hy
      have hl := Floats.Float.to_intu_to_long f n hf
      refine ⟨_, eval_op1 (eval_op1 ha (v := .Vlong (Integers.Int64.repr (Integers.Int.unsigned n)))
        (by show (Floats.Float.toLong f).map Val.Vlong = _; rw [hl]; rfl)) rfl, ?_⟩
      show Val.Lessdef _ (Val.Vint (Integers.Int64.loword _))
      rw [loword_repr, Integers.Int.repr_unsigned]; ld
  | _ => cases hy

/-- `eval_floatofintu` (64-bit configuration: via a conversion from a 64-bit integer). -/
theorem eval_floatofintu {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.floatofintu x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (floatofintu a) v ∧ Val.Lessdef y v := by
  unfold floatofintu
  split
  · obtain rfl := inv_intconst ha
    simp only [Val.floatofintu] at hy; cases hy
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · simp only [Archi.splitlong, Bool.false_eq_true, if_false]
    cases x with
    | Vint n =>
      simp only [Val.floatofintu] at hy; cases hy
      refine ⟨_, eval_op1 (eval_op1 ha rfl) rfl, ?_⟩
      show Val.Lessdef _ (Val.Vfloat (Floats.Float.ofLong _))
      rw [← Floats.Float.of_intu_of_long]; ld
    | _ => cases hy

/-- `eval_intuofsingle` -/
theorem eval_intuofsingle {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.intuofsingle x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (intuofsingle a) v ∧ Val.Lessdef y v := by
  cases x <;> simp only [Val.intuofsingle, reduceCtorEq] at hy
  rename_i f
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hy
  obtain ⟨v, hv, hl⟩ := eval_floatofsingle _ _ _ ha
  cases hl
  have hd : Floats.Float.toIntu (Floats.Float.ofSingle f) = some n :=
    Floats.Float32.to_intu_double f n hn
  exact eval_intuoffloat hv (by simp [Val.floatofsingle, Val.intuoffloat, hd])

/-- `eval_singleofintu` -/
theorem eval_singleofintu {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.singleofintu x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (singleofintu a) v ∧ Val.Lessdef y v := by
  unfold singleofintu
  split
  · obtain rfl := inv_intconst ha
    simp only [Val.singleofintu] at hy; cases hy
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · cases x <;> simp only [Val.singleofintu, reduceCtorEq] at hy
    rename_i n
    cases hy
    obtain ⟨v, hv, hl⟩ := eval_floatofintu ha (show Val.floatofintu (.Vint n) = some _ from rfl)
    cases hl
    obtain ⟨w, hw, hl2⟩ := eval_singleoffloat _ _ _ hv
    refine ⟨w, hw, ?_⟩
    rw [Floats.Float32.of_intu_double]
    exact hl2

/-! ### Addressing modes -/

/-- `eval_addressing` -/
theorem eval_addressing (chunk : Chunk) {le : Letenv}
    {a : SelectOp.Expr} {v : Val} {b : Block} {ofs : Integers.Ptrofs}
    (ha : CminorSel.EvalExpr ge sp e m le a v) (hv : v = .Vptr b ofs) :
    ∃ vl, CminorSel.EvalExprlist ge sp e m le (addressing chunk a).2 vl ∧
      evalAddressing ge sp (addressing chunk a).1 vl = some v := by
  have default : ∃ vl, CminorSel.EvalExprlist ge sp e m le (a ::: .Enil) vl ∧
      evalAddressing ge sp (.Aindexed 0) vl = some v := by
    refine ⟨[v], .Econs _ _ _ _ _ ha (.Enil _), ?_⟩
    subst hv
    show some (Val.addl _ _) = _
    simp only [Val.addl, Archi.ptr64, if_true]
    rw [show Integers.Ptrofs.of_int64 (Integers.Int64.repr 0) = Integers.Ptrofs.zero by decide,
      Integers.Ptrofs.add_zero]
  unfold addressing
  split
  · simp only [Archi.ptr64, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    exact default
  · split
    · next h =>
      obtain ⟨vl, hl, ho⟩ := inv_op ha
      exact ⟨vl, hl, by simp only [evalAddressing, Archi.ptr64, if_true]; exact ho⟩
    · exact default
  · exact default

/-! ### Arguments of built-ins -/

theorem eval_builtinArgAddr {addr : Addressing} {el : SelectOp.Exprlist} {vl : List Val} {v : Val}
    (hl : CminorSel.EvalExprlist ge sp e m [] el vl)
    (ho : evalAddressing64 ge sp addr vl = some v) :
    CminorSel.EvalBuiltinArg ge sp e m (builtinArgAddr addr el) v := by
  unfold builtinArgAddr
  split
  · cases hl with
    | Econs _ _ _ v1 _ h1 hl =>
      cases hl
      cases ho
      exact .BA_addptr _ _ _ _ (.BA _ _ h1) (.BA_long _)
  · cases hl; cases ho; exact .BA_addrglobal _ _
  · cases hl; cases ho; exact .BA_addrstack _
  · exact .BA _ _ (.Eop _ _ _ _ _ hl ho)

/-- `eval_builtin_arg` -/
theorem eval_builtin_arg {a : SelectOp.Expr} {v : Val}
    (ha : CminorSel.EvalExpr ge sp e m [] a v) :
    CminorSel.EvalBuiltinArg ge sp e m (builtinArg a) v := by
  unfold builtinArg
  split
  · obtain rfl := inv_intconst ha; exact .BA_int _
  · have : some (Val.Vlong _) = some v := inv_op0 ha
    cases this; exact .BA_long _
  · simp only [Archi.ptr64, if_true]; exact .BA _ _ ha
  · simp only [Archi.ptr64, if_true]
    obtain ⟨vl, hl, ho⟩ := inv_op ha
    exact eval_builtinArgAddr hl ho
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    obtain rfl := inv_intconst h1
    obtain rfl := inv_intconst h2
    cases ho; exact .BA_long _
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    cases ho
    exact .BA_splitlong _ _ _ _ h1 h2
  · cases ha with
    | Eload _ _ _ _ vl vaddr _ hl haddr hload =>
      cases hl
      cases haddr
      exact .BA_loadglobal _ _ _ _ hload
  · cases ha with
    | Eload _ _ _ _ vl vaddr _ hl haddr hload =>
      cases hl
      cases haddr
      exact .BA_loadstack _ _ _ hload
  · exact .BA _ _ ha

/-- `eval_platform_builtin` (x86): `__builtin_fmax` and `__builtin_fmin`. -/
theorem eval_platformBuiltinX86 {le : Letenv} (bf : PlatformBuiltinX86)
    {al : SelectOp.Exprlist} {a : SelectOp.Expr} {vl : List Val}
    (h : platformBuiltinX86 bf al = some a) (hl : CminorSel.EvalExprlist ge sp e m le al vl) :
    ∃ v, CminorSel.EvalExpr ge sp e m le a v ∧
      (bf = .BI_fmax → ∃ v1 v2, vl = [v1, v2] ∧ v = Op.maxf v1 v2) ∧
      (bf = .BI_fmin → ∃ v1 v2, vl = [v1, v2] ∧ v = Op.minf v1 v2) := by
  unfold platformBuiltinX86 at h
  split at h
  · cases h
    cases hl with
    | Econs _ _ _ v1 _ h1 hl =>
      cases hl with
      | Econs _ _ _ v2 _ h2 hl =>
        cases hl
        exact ⟨_, eval_op2 h1 h2 rfl, fun _ => ⟨v1, v2, rfl, rfl⟩, fun h => by cases h⟩
  · cases h
    cases hl with
    | Econs _ _ _ v1 _ h1 hl =>
      cases hl with
      | Econs _ _ _ v2 _ h2 hl =>
        cases hl
        exact ⟨_, eval_op2 h1 h2 rfl, (fun h => by cases h), fun _ => ⟨v1, v2, rfl, rfl⟩⟩
  · cases h

end CMCONSTR

end SelectOpproof
end X86
end CC
