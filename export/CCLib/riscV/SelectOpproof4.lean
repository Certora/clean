/-
  Correctness of instruction selection for operators (RISC-V), part 4 —
  port of `riscV/SelectOpproof.v`: integer comparisons, `select`,
  addressing modes and built-in arguments.
-/
import CCLib.riscV.SelectOpproof3
import CCLib.riscV.OpTheory

namespace CC
namespace RiscV
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `Val.swap_cmpu_bool` -/
theorem val_swap_cmpu_bool (vp : Block → Z → Bool) (c : Comparison) (x y : Val) :
    Val.cmpu_bool vp c.swap x y = Val.cmpu_bool vp c y x := by
  cases x <;> cases y <;> simp [Val.cmpu_bool, Archi.ptr64, Integers.Int.swap_cmpu]

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

theorem inv_op {le : Letenv} {op : Operation} {al : SelectOp.Exprlist} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le (.Eop op al) v) :
    ∃ vl, CminorSel.EvalExprlist ge sp e m le al vl ∧ evalOperation ge sp op vl m = some v := by
  cases h with
  | Eop _ _ _ vl _ hl ho => exact ⟨vl, hl, ho⟩

/-! ### Comparisons against an immediate (`Section COMP_IMM`) -/

section COMP_IMM
variable (default : Comparison → Integers.Int → Condition)
  (intsem : Comparison → Integers.Int → Integers.Int → Bool)
  (vsem : Comparison → Val → Val → Val)

/-- The hypotheses of `Section COMP_IMM` relating the value-level comparison `vsem` to the
integer comparison `intsem` and to the default condition `default`. -/
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

/-! ### Integer comparisons -/

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

/-! ### Addressing modes -/

/-- `eval_addressing` -/
theorem eval_addressing (isReloc : Ident → Bool) (chunk : Chunk) {le : Letenv}
    {a : SelectOp.Expr} {v : Val} {b : Block} {ofs : Integers.Ptrofs}
    (ha : CminorSel.EvalExpr ge sp e m le a v) (hv : v = .Vptr b ofs) :
    ∃ vl, CminorSel.EvalExprlist ge sp e m le (addressing isReloc chunk a).2 vl ∧
      evalAddressing ge sp (addressing isReloc chunk a).1 vl = some v := by
  unfold addressing
  split
  · exact ⟨[], .Enil _, inv_op0 ha⟩
  · split
    · refine ⟨[v], .Econs _ _ _ _ _ ha (.Enil _), ?_⟩
      subst hv
      show some (Val.offsetPtr _ _) = _
      simp only [Val.offsetPtr, Integers.Ptrofs.add_zero]
    · exact ⟨[], .Enil _, inv_op0 ha⟩
  · next n e1 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 ha
    cases ho
    exfalso
    cases v1 <;> simp [Val.add, Archi.ptr64] at hv
  · next n e1 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 ha
    cases ho
    refine ⟨[v1], .Econs _ _ _ _ _ h1 (.Enil _), ?_⟩
    show some (Val.offsetPtr v1 _) = some (Val.addl v1 _)
    cases v1 <;> simp [Val.addl, Archi.ptr64] at hv ⊢
    obtain ⟨rfl, rfl⟩ := hv; rfl
  · refine ⟨[v], .Econs _ _ _ _ _ ha (.Enil _), ?_⟩
    subst hv
    show some (Val.offsetPtr _ _) = _
    simp only [Val.offsetPtr, Integers.Ptrofs.add_zero]

/-! ### Arguments of built-ins -/

/-- `eval_builtin_arg` -/
theorem eval_builtin_arg {a : SelectOp.Expr} {v : Val}
    (ha : CminorSel.EvalExpr ge sp e m [] a v) :
    CminorSel.EvalBuiltinArg ge sp e m (builtinArg a) v := by
  unfold builtinArg
  split
  · obtain rfl := inv_intconst ha; exact .BA_int _
  · have : some (Genv.symbolAddress ge _ _) = some v := inv_op0 ha
    cases this; exact .BA_addrglobal _ _
  · have : some (Val.offsetPtr sp _) = some v := inv_op0 ha
    cases this; exact .BA_addrstack _
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
      exact .BA_loadstack _ _ _ hload
  · exact .BA _ _ ha
  · obtain ⟨v1, h1, ho⟩ := inv_op1 ha
    cases ho
    exact .BA_addptr _ _ _ _ (.BA _ _ h1) (.BA_long _)
  · exact .BA _ _ ha

/-- `eval_platform_builtin`: RISC-V has no platform-specific built-ins. -/
theorem eval_platform_builtin {le : Letenv} (bf : Builtins.PlatformBuiltin)
    (al : SelectOp.Exprlist) (a : SelectOp.Expr) (h : platformBuiltin bf al = some a) :
    ∀ v, ∃ v', CminorSel.EvalExpr ge sp e m le a v' ∧ Val.Lessdef v v' := by
  cases h

end CMCONSTR

/-! ### High multiplication -/

namespace SelectDivproofBounds
theorem signed_range32 (x : Integers.Int) :
    (-2 ^ 31 : _root_.Int) ≤ Integers.Int.signed x ∧ (Integers.Int.signed x : _root_.Int) < 2 ^ 31 := by
  have := Integers.Int.signed_range x
  have : @Eq _root_.Int Integers.Int.min_signed (-2^31) := by decide
  have : @Eq _root_.Int Integers.Int.max_signed (2^31 - 1) := by decide
  zomega
end SelectDivproofBounds

theorem loword_repr (z : _root_.Int) : Integers.Int64.loword (Integers.Int64.repr z) = Integers.Int.repr z := by
  show (BitVec.ofInt 64 z).truncate 32 = BitVec.ofInt 32 z
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

theorem mulhs_via_long (i j : Integers.Int) :
    Integers.Int64.loword (Integers.Int64.shr (Integers.Int64.mul (Integers.Int64.repr (Integers.Int.signed i))
      (Integers.Int64.repr (Integers.Int.signed j))) (Integers.Int64.repr 32)) = Integers.Int.mulhs i j := by
  have hi := SelectDivproofBounds.signed_range32 i
  have hj := SelectDivproofBounds.signed_range32 j
  have hp := Int.natAbs_mul (Integers.Int.signed i) (Integers.Int.signed j)
  have hb : (Integers.Int.signed i).natAbs * (Integers.Int.signed j).natAbs ≤ 2 ^ 31 * 2 ^ 31 :=
    Nat.mul_le_mul (by zomega) (by zomega)
  rw [← Integers.Int64.repr_mul, Integers.Int64.shr_div_two_p,
    Integers.Int64.signed_repr (by
      have : @Eq _root_.Int Integers.Int64.min_signed (-2^63) := by decide
      zomega) (by
      have : @Eq _root_.Int Integers.Int64.max_signed (2^63 - 1) := by decide
      zomega),
    show (Integers.Int64.repr 32 : Integers.Int64).toNat = 32 by decide, loword_repr]
  have hm : @Eq _root_.Int Integers.Int.modulus (2 ^ 32) := by decide
  show _ = Integers.Int.repr (Integers.Int.signed i * Integers.Int.signed j / Integers.Int.modulus)
  rw [hm]

theorem mulhu_via_long (i j : Integers.Int) :
    Integers.Int64.loword (Integers.Int64.shru (Integers.Int64.mul (Integers.Int64.repr (Integers.Int.unsigned i))
      (Integers.Int64.repr (Integers.Int.unsigned j))) (Integers.Int64.repr 32)) = Integers.Int.mulhu i j := by
  have hi := Integers.Int.unsigned_range i
  have hj := Integers.Int.unsigned_range j
  have hm : @Eq _root_.Int Integers.Int.modulus (2 ^ 32) := by decide
  have h0 : 0 ≤ Integers.Int.unsigned i * Integers.Int.unsigned j :=
    Int.mul_nonneg hi.1 hj.1
  have h1 : Integers.Int.unsigned i * Integers.Int.unsigned j < 2 ^ 64 := by
    have : Integers.Int.unsigned i * Integers.Int.unsigned j ≤ Integers.Int.unsigned i * (2 ^ 32 - 1) :=
      Int.mul_le_mul_of_nonneg_left (by zomega) hi.1
    have : Integers.Int.unsigned i * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Int.mul_le_mul_of_nonneg_right (by zomega) (by decide)
    zomega
  rw [← Integers.Int64.repr_mul, Integers.Int64.shru_div_two_p,
    Integers.Int64.unsigned_repr h0 (by
      have : @Eq _root_.Int Integers.Int64.max_unsigned (2^64 - 1) := by decide
      zomega),
    show (Integers.Int64.repr 32 : Integers.Int64).toNat = 32 by decide, loword_repr]
  show _ = Integers.Int.repr (Integers.Int.unsigned i * Integers.Int.unsigned j / Integers.Int.modulus)
  rw [hm]

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-- `eval_mulhs` -/
theorem eval_mulhs : BinarySound ge sp e m SelectOp.mulhs Val.mulhs := by
  intro le a x b y hx hy
  unfold SelectOp.mulhs
  simp only [Archi.ptr64, if_true]
  refine ⟨_, eval_op1 (eval_op1 (eval_op2 (eval_op1 hx rfl) (eval_op1 hy rfl) rfl) rfl) rfl, ?_⟩
  cases x <;> cases y <;> try ld
  show Val.Lessdef _ (Val.loword (Val.shrl (Val.mull (Val.longofint _) (Val.longofint _)) _))
  simp only [Val.longofint, Val.mull, Val.shrl, Val.loword, Val.mulhs]
  rw [if_pos (by decide), show Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.repr 32)) =
    Integers.Int64.repr 32 by decide]
  show Val.Lessdef _ (Val.Vint _)
  rw [mulhs_via_long]; ld

/-- `eval_mulhu` -/
theorem eval_mulhu : BinarySound ge sp e m SelectOp.mulhu Val.mulhu := by
  intro le a x b y hx hy
  unfold SelectOp.mulhu
  simp only [Archi.ptr64, if_true]
  refine ⟨_, eval_op1 (eval_op1 (eval_op2 (eval_op1 hx rfl) (eval_op1 hy rfl) rfl) rfl) rfl, ?_⟩
  cases x <;> cases y <;> try ld
  show Val.Lessdef _ (Val.loword (Val.shrlu (Val.mull (Val.longofintu _) (Val.longofintu _)) _))
  simp only [Val.longofintu, Val.mull, Val.shrlu, Val.loword, Val.mulhu]
  rw [if_pos (by decide), show Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.repr 32)) =
    Integers.Int64.repr 32 by decide]
  show Val.Lessdef _ (Val.Vint _)
  rw [mulhu_via_long]; ld

end CMCONSTR

end SelectOpproof
end RiscV
end CC
