/-
  Correctness of instruction selection for operators (aarch64), part 3 —
  continuation of `CCLib.aarch64.SelectOpproof2` (port of `aarch64/SelectOpproof.v`):
  integer comparisons, `select`, addressing modes and built-in arguments.
-/
import CCLib.aarch64.SelectOpproof2
import CCLib.backend.Linearizeproof

namespace CC
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

/-- The four `Ocmp` sub-cases of `eval_compimm`, at the level of values. -/
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
      rw [Linearizeproof.eval_negateCondition]
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
      rw [Linearizeproof.eval_negateCondition]
      exact compimm_ocmp_ne1 H _
    rw [if_neg ho1]
    exact ⟨_, eval_op0 rfl, compimm_ocmp_ne_other H _ hz ho1⟩
  · split
    · next hz =>
      obtain rfl := (Integers.Int.eq_spec _ _).mp hz
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      cases v1 <;> simp only [Val.and, H.sem_undef, evalCondition, Val.cmp_bool, Val.ofOptbool] <;>
        try ld
      rw [H.sem_eq]; exact .refl _
    · exact ⟨_, eval_op1 hx rfl, by rw [H.sem_default]; ld⟩
  · split
    · next hz =>
      obtain rfl := (Integers.Int.eq_spec _ _).mp hz
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      cases v1 <;> simp only [Val.and, H.sem_undef, evalCondition, Val.cmp_bool, Val.ofOptbool] <;>
        try ld
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

/-! ### Integer comparisons -/

/-- The cases of `comp`/`compu` after the first shift case. -/
theorem eval_compRest (shiftcond : Comparison → Shift → Amount32 → Condition)
    (basecond : Comparison → Condition) (vsem : Comparison → Val → Val → Val)
    (hbase : ∀ c x y, vsem c x y = Val.ofOptbool (evalCondition (basecond c) [x, y] m))
    (hshift : ∀ c s a x y,
      vsem c x (evalShift s y a) = Val.ofOptbool (evalCondition (shiftcond c s a) [x, y] m))
    (c : Comparison) : BinarySound ge sp e m (compRest shiftcond basecond c) (vsem c) := by
  intro le a x b y hx hy
  unfold compRest
  split
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    split
    · exact ⟨_, eval_op2 hx h2 rfl, by rw [hshift]; ld⟩
    · exact ⟨_, eval_op2 hx hy rfl, by rw [hbase]; ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by rw [hbase]; ld⟩

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
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    split
    · refine ⟨_, eval_op2 hy h1 rfl, ?_⟩
      show Val.Lessdef _ (Val.ofOptbool (Val.cmp_bool c.swap y _))
      rw [Val.swap_cmp_bool]; ld
    · exact eval_compRest _ _ Val.cmp (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) c le _ _ _ _ hx hy
  · exact eval_compRest _ _ Val.cmp (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) c le _ _ _ _ hx hy

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
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    split
    · refine ⟨_, eval_op2 hy h1 rfl, ?_⟩
      show Val.Lessdef _ (Val.ofOptbool (Val.cmpu_bool (Mem.validPointer m) c.swap y _))
      rw [val_swap_cmpu_bool]; ld
    · exact eval_compRest _ _ (Val.cmpu (Mem.validPointer m)) (fun _ _ _ => rfl)
        (fun _ _ _ _ _ => rfl) c le _ _ _ _ hx hy
  · exact eval_compRest _ _ (Val.cmpu (Mem.validPointer m)) (fun _ _ _ => rfl)
      (fun _ _ _ _ _ => rfl) c le _ _ _ _ hx hy

/-! ### Selection -/

/-- `eval_select`.  (Rocq additionally assumes `select_supported ty = true`; the proof does
not need it.) -/
theorem eval_select {le : Letenv} (ty : ATyp) (cond : Condition) {al : SelectOp.Exprlist}
    {vl : List Val} {a1 a2 : SelectOp.Expr} {v1 v2 : Val}
    (hl : CminorSel.EvalExprlist ge sp e m le al vl)
    (h1 : CminorSel.EvalExpr ge sp e m le a1 v1) (h2 : CminorSel.EvalExpr ge sp e m le a2 v2) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (select ty cond al a1 a2) v ∧
      Val.Lessdef (Val.select (evalCondition cond vl m) v1 v2 ty) v :=
  ⟨_, .Eop _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 hl)) rfl, .refl _⟩

/-! ### Addressing modes -/

theorem ptrofs_of_int64_to_int64 (ofs : Integers.Ptrofs) :
    Integers.Ptrofs.of_int64 (Integers.Ptrofs.to_int64 ofs) = ofs := by
  show BitVec.ofInt 64 ((BitVec.zeroExtend 64 ofs).toNat : _root_.Int) = ofs
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  have := ofs.isLt
  have h2 : (2 : Nat) ^ Archi.ptrWordsize = 2 ^ 64 := rfl
  have h3 : ofs.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h3, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  simp

/-- `eval_addressing` -/
theorem eval_addressing (isReloc : Ident → Bool) (chunk : Chunk) {le : Letenv}
    {a : SelectOp.Expr} {v : Val} {b : Block} {ofs : Integers.Ptrofs}
    (ha : CminorSel.EvalExpr ge sp e m le a v) (hv : v = .Vptr b ofs) :
    ∃ vl, CminorSel.EvalExprlist ge sp e m le (addressing isReloc chunk a).2 vl ∧
      evalAddressing ge sp (addressing isReloc chunk a).1 vl = some v := by
  unfold addressing
  split
  · exact ⟨[], .Enil _, inv_op0 ha⟩
  · next id o =>
    split
    · refine ⟨[Genv.symbolAddress ge id Integers.Ptrofs.zero],
        .Econs _ _ _ _ _ (eval_op0 rfl) (.Enil _), ?_⟩
      obtain rfl : Genv.symbolAddress ge id o = v := Option.some.inj (inv_op0 ha)
      show some (Val.addl (Genv.symbolAddress ge id Integers.Ptrofs.zero)
        (.Vlong (Integers.Ptrofs.to_int64 o))) = some (Genv.symbolAddress ge id o)
      rw [← Genv.shift_symbolAddress_64, ptrofs_of_int64_to_int64, Integers.Ptrofs.add_zero_l]
    · exact ⟨[], .Enil _, inv_op0 ha⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 ha
    exact ⟨[v1], .Econs _ _ _ _ _ h1 (.Enil _), ho⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    exact ⟨[v1, v2], .Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 (.Enil _)), ho⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    exact ⟨[v1, v2], .Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 (.Enil _)), ho⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    exact ⟨[v1, v2], .Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 (.Enil _)), ho⟩
  · refine ⟨[v], .Econs _ _ _ _ _ ha (.Enil _), ?_⟩
    subst hv
    show some (Val.addl _ _) = _
    simp only [Val.addl, Archi.ptr64, if_true]
    rw [show Integers.Ptrofs.of_int64 Integers.Int64.zero = Integers.Ptrofs.zero by decide,
      Integers.Ptrofs.add_zero]

/-! ### Arguments of built-ins -/

/-- `eval_builtin_arg` -/
theorem eval_builtin_arg {a : SelectOp.Expr} {v : Val}
    (ha : CminorSel.EvalExpr ge sp e m [] a v) :
    CminorSel.EvalBuiltinArg ge sp e m (builtinArg a) v := by
  unfold builtinArg
  split
  · obtain rfl := inv_intconst ha; exact .BA_int _
  · have : some (Val.Vlong _) = some v := inv_op0 ha
    cases this; exact .BA_long _
  · have : some (Genv.symbolAddress ge _ _) = some v := inv_op0 ha
    cases this; exact .BA_addrglobal _ _
  · have : some (Val.offsetPtr sp _) = some v := inv_op0 ha
    cases this; exact .BA_addrstack _
  · cases ha with
    | Eload _ _ _ _ vl vaddr _ hl haddr hload =>
      cases hl
      cases haddr
      exact .BA_loadstack _ _ _ hload
  · obtain ⟨v1, h1, ho⟩ := inv_op1 ha
    cases ho
    exact .BA_addptr _ _ _ _ (.BA _ _ h1) (.BA_long _)
  · exact .BA _ _ ha

/-- `eval_platform_builtin`: aarch64 has no platform-specific built-ins. -/
theorem eval_platform_builtin {le : Letenv} (bf : Builtins.PlatformBuiltin)
    (al : SelectOp.Exprlist) (a : SelectOp.Expr) (h : platformBuiltin bf al = some a) :
    ∀ v, ∃ v', CminorSel.EvalExpr ge sp e m le a v' ∧ Val.Lessdef v v' := by
  cases h

end CMCONSTR

end SelectOpproof
end CC
