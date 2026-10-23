/-
  Correctness proof for x86-64 generation: auxiliary results, part 2 —
  port of the "Processor conditions and comparisons" section of
  `x86/Asmgenproof1.v`: `compare_ints_spec`,
  `testcond_for_signed/unsigned_comparison_32_correct`, `compare_longs_spec`,
  `int64_sub_overflow`, `testcond_for_signed/unsigned_comparison_64_correct`,
  `compare_floats_spec`, `compare_floats32_spec`, `eval_extcond`,
  `swap_floats`, `testcond_for_(neg_)float(32)_comparison_correct`,
  `swap_floats_commut`, `compare_floats_inv`, `compare_floats32_inv`,
  `transl_cond_correct`, `eval_testcond_nextinstr`, `eval_testcond_set_ireg`,
  `mk_setcc_base_correct`, `mk_setcc_correct`, `negate_extcond`,
  `negate_testcond_for_condition`, `mk_sel_correct`, `transl_sel_correct`.

  Differences from Rocq: on x86-64 (`Archi.ptr64 = true`) a 32-bit unsigned
  comparison involving a pointer is undefined, so the pointer cases of
  `testcond_for_unsigned_comparison_32_correct` are vacuous.
-/
import CCLib.x86.Asmgenproof1

namespace CC
namespace X86
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1 Op

/-- Unfolding of `Int.cmp` / `Int.cmpu` on each comparison. -/
theorem int_cmp_unfold (x y : Integers.Int) :
    Integers.Int.cmp .Ceq x y = Integers.Int.eq x y ∧ Integers.Int.cmp .Cne x y = !(Integers.Int.eq x y) ∧
    Integers.Int.cmp .Clt x y = Integers.Int.lt x y ∧ Integers.Int.cmp .Cle x y = !(Integers.Int.lt y x) ∧
    Integers.Int.cmp .Cgt x y = Integers.Int.lt y x ∧ Integers.Int.cmp .Cge x y = !(Integers.Int.lt x y) ∧
    Integers.Int.cmpu .Ceq x y = Integers.Int.eq x y ∧ Integers.Int.cmpu .Cne x y = !(Integers.Int.eq x y) ∧
    Integers.Int.cmpu .Clt x y = Integers.Int.ltu x y ∧ Integers.Int.cmpu .Cle x y = !(Integers.Int.ltu y x) ∧
    Integers.Int.cmpu .Cgt x y = Integers.Int.ltu y x ∧ Integers.Int.cmpu .Cge x y = !(Integers.Int.ltu x y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Unfolding of `Int64.cmp` / `Int64.cmpu` on each comparison. -/
theorem int64_cmp_unfold (x y : Integers.Int64) :
    Integers.Int64.cmp .Ceq x y = Integers.Int64.eq x y ∧ Integers.Int64.cmp .Cne x y = !(Integers.Int64.eq x y) ∧
    Integers.Int64.cmp .Clt x y = Integers.Int64.lt x y ∧ Integers.Int64.cmp .Cle x y = !(Integers.Int64.lt y x) ∧
    Integers.Int64.cmp .Cgt x y = Integers.Int64.lt y x ∧ Integers.Int64.cmp .Cge x y = !(Integers.Int64.lt x y) ∧
    Integers.Int64.cmpu .Ceq x y = Integers.Int64.eq x y ∧ Integers.Int64.cmpu .Cne x y = !(Integers.Int64.eq x y) ∧
    Integers.Int64.cmpu .Clt x y = Integers.Int64.ltu x y ∧ Integers.Int64.cmpu .Cle x y = !(Integers.Int64.ltu y x) ∧
    Integers.Int64.cmpu .Cgt x y = Integers.Int64.ltu y x ∧ Integers.Int64.cmpu .Cge x y = !(Integers.Int64.ltu x y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Unfolding of `Ptrofs.cmpu` on each comparison. -/
theorem ptrofs_cmpu_unfold (x y : Integers.Ptrofs) :
    Integers.Ptrofs.cmpu .Ceq x y = Integers.Ptrofs.eq x y ∧ Integers.Ptrofs.cmpu .Cne x y = !(Integers.Ptrofs.eq x y) ∧
    Integers.Ptrofs.cmpu .Clt x y = Integers.Ptrofs.ltu x y ∧ Integers.Ptrofs.cmpu .Cle x y = !(Integers.Ptrofs.ltu y x) ∧
    Integers.Ptrofs.cmpu .Cgt x y = Integers.Ptrofs.ltu y x ∧ Integers.Ptrofs.cmpu .Cge x y = !(Integers.Ptrofs.ltu x y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem int_flag_eqs :
    Integers.Int.eq Integers.Int.one Integers.Int.one = true ∧
    Integers.Int.eq Integers.Int.zero Integers.Int.one = false ∧
    Integers.Int.eq Integers.Int.one Integers.Int.zero = false ∧
    Integers.Int.eq Integers.Int.zero Integers.Int.zero = true := by decide

/-- `Asmgenproof1.compare_ints_spec` -/
theorem compare_ints_spec (rs : Regset) (v1 v2 : Val) (m : Mem) :
    let rs' := nextinstr (compareInts v1 v2 rs m)
    rs' (.CR .ZF) = Val.cmpu (Mem.validPointer m) .Ceq v1 v2 ∧
    rs' (.CR .CF) = Val.cmpu (Mem.validPointer m) .Clt v1 v2 ∧
    rs' (.CR .SF) = Val.negative (Val.sub v1 v2) ∧
    rs' (.CR .OF) = Val.sub_overflow v1 v2 ∧
    ∀ r, dataPreg r = true → rs' r = rs r := by
  refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  cases r <;> simp_all [dataPreg, nextinstr, compareInts, Regset.set]

/-- `Asmgenproof1.compare_longs_spec` -/
theorem compare_longs_spec (rs : Regset) (v1 v2 : Val) (m : Mem) :
    let rs' := nextinstr (compareLongs v1 v2 rs m)
    rs' (.CR .ZF) = Val.maketotal (Val.cmplu (Mem.validPointer m) .Ceq v1 v2) ∧
    rs' (.CR .CF) = Val.maketotal (Val.cmplu (Mem.validPointer m) .Clt v1 v2) ∧
    rs' (.CR .SF) = Val.negativel (Val.subl v1 v2) ∧
    rs' (.CR .OF) = Val.subl_overflow v1 v2 ∧
    ∀ r, dataPreg r = true → rs' r = rs r := by
  refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  cases r <;> simp_all [dataPreg, nextinstr, compareLongs, Regset.set]

/-- `Asmgenproof1.testcond_for_signed_comparison_32_correct` -/
theorem testcond_for_signed_comparison_32_correct (c : Comparison) (v1 v2 : Val) (rs : Regset)
    (m : Mem) (b : Bool) (h : Val.cmp_bool c v1 v2 = some b) :
    evalTestcond (testcondForSignedComparison c) (nextinstr (compareInts v1 v2 rs m)) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmp_bool] at h
  rename_i x y
  subst h
  have hx := Integers.Int.lt_sub_overflow x y
  have hln := Integers.Int.lt_not x y
  cases hl : Integers.Int.lt x y <;> cases he : Integers.Int.eq x y <;> simp only [hl, he] at hx hln <;>
    cases c <;> simp [evalTestcond, testcondForSignedComparison, compareInts, nextinstr, Regset.set,
    Val.cmpu, Val.cmpu_bool, Val.ofOptbool, Val.ofBool, Val.sub_overflow, Val.negative, Val.sub, hx,
    int_cmp_unfold, hln, hl, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]

/-- `Asmgenproof1.testcond_for_unsigned_comparison_32_correct` -/
theorem testcond_for_unsigned_comparison_32_correct (c : Comparison) (v1 v2 : Val) (rs : Regset)
    (m : Mem) (b : Bool) (h : Val.cmpu_bool (Mem.validPointer m) c v1 v2 = some b) :
    evalTestcond (testcondForUnsignedComparison c) (nextinstr (compareInts v1 v2 rs m)) =
      some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpu_bool, Archi.ptr64] at h
  rename_i x y
  subst h
  have hln := Integers.Int.ltu_not x y
  cases hl : Integers.Int.ltu x y <;> cases he : Integers.Int.eq x y <;> simp only [hl, he] at hln <;>
    cases c <;> simp [evalTestcond, testcondForUnsignedComparison, compareInts, nextinstr, Regset.set,
    Val.cmpu, Val.cmpu_bool, Val.ofOptbool, Val.ofBool, int_cmp_unfold, hln, hl, he, Val.Vtrue,
    Val.Vfalse, int_flag_eqs]

/-- `Asmgenproof1.int64_sub_overflow` -/
theorem int64_sub_overflow (x y : Integers.Int64) :
    Integers.Int.xor (Integers.Int.repr (Integers.Int64.unsigned (Integers.Int64.sub_overflow x y Integers.Int64.zero)))
      (Integers.Int.repr (Integers.Int64.unsigned (Integers.Int64.negative (Integers.Int64.sub x y)))) =
    (if Integers.Int64.lt x y then Integers.Int.one else Integers.Int.zero) := by
  have hx := Integers.Int64.lt_sub_overflow x y
  have ha : Integers.Int64.sub_overflow x y Integers.Int64.zero = Integers.Int64.zero ∨
      Integers.Int64.sub_overflow x y Integers.Int64.zero = Integers.Int64.one := by
    unfold Integers.Int64.sub_overflow Integers.MI.sub_overflow; dsimp only
    split <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hb : Integers.Int64.negative (Integers.Int64.sub x y) = Integers.Int64.zero ∨
      Integers.Int64.negative (Integers.Int64.sub x y) = Integers.Int64.one := by
    unfold Integers.Int64.negative Integers.MI.negative; split <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at hx ⊢ <;>
    cases hl : Integers.Int64.lt x y <;> simp only [hl] at hx <;> revert hx <;> decide

/-- `Asmgenproof1.testcond_for_signed_comparison_64_correct` -/
theorem testcond_for_signed_comparison_64_correct (c : Comparison) (v1 v2 : Val) (rs : Regset)
    (m : Mem) (b : Bool) (h : Val.cmpl_bool c v1 v2 = some b) :
    evalTestcond (testcondForSignedComparison c) (nextinstr (compareLongs v1 v2 rs m)) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpl_bool] at h
  rename_i x y
  subst h
  have hx := int64_sub_overflow x y
  have hln := Integers.Int64.lt_not x y
  cases hl : Integers.Int64.lt x y <;> cases he : Integers.Int64.eq x y <;> simp only [hl, he] at hx hln <;>
    cases c <;> simp [evalTestcond, testcondForSignedComparison, compareLongs, nextinstr, Regset.set,
    Val.cmplu, Val.cmplu_bool, Val.maketotal, Val.ofBool, Val.subl_overflow, Val.negativel, Val.subl,
    hx, int64_cmp_unfold, hln, hl, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]

/-- The three possible shapes of a defined 64-bit unsigned comparison. -/
theorem cmplu_bool_shape (vp : Block → Z → Bool) (c : Comparison) (v1 v2 : Val) (b : Bool)
    (h : Val.cmplu_bool vp c v1 v2 = some b) :
    (∃ x y, v1 = .Vlong x ∧ v2 = .Vlong y) ∨
    (∃ p q : Integers.Ptrofs, ∀ c', Val.cmplu_bool vp c' v1 v2 = some (Integers.Ptrofs.cmpu c' p q)) ∨
    (∀ c', Val.cmplu_bool vp c' v1 v2 = Val.cmpDifferentBlocks c') := by
  cases v1 <;> cases v2 <;> simp only [Val.cmplu_bool, Archi.ptr64] at h ⊢ <;> (try contradiction)
  · exact Or.inl ⟨_, _, rfl, rfl⟩
  all_goals simp only [Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
  · split at h
    · rename_i hc; exact Or.inr (Or.inr fun c' => by rw [if_pos hc])
    · contradiction
  · split at h
    · rename_i hc; exact Or.inr (Or.inr fun c' => by rw [if_pos hc])
    · contradiction
  · split at h
    · rename_i hb
      split at h
      · rename_i hc
        exact Or.inr (Or.inl ⟨_, _, fun c' => by rw [if_pos hb, if_pos hc]⟩)
      · contradiction
    · rename_i hb
      split at h
      · rename_i hc; exact Or.inr (Or.inr fun c' => by rw [if_neg hb, if_pos hc])
      · contradiction

/-- `Asmgenproof1.testcond_for_unsigned_comparison_64_correct` -/
theorem testcond_for_unsigned_comparison_64_correct (c : Comparison) (v1 v2 : Val) (rs : Regset)
    (m : Mem) (b : Bool) (h : Val.cmplu_bool (Mem.validPointer m) c v1 v2 = some b) :
    evalTestcond (testcondForUnsignedComparison c) (nextinstr (compareLongs v1 v2 rs m)) =
      some b := by
  rcases cmplu_bool_shape _ c v1 v2 b h with ⟨x, y, rfl, rfl⟩ | ⟨p, q, hall⟩ | hall
  · simp [Val.cmplu_bool] at h
    subst h
    have hln := Integers.Int64.ltu_not x y
    cases hl : Integers.Int64.ltu x y <;> cases he : Integers.Int64.eq x y <;> simp only [hl, he] at hln <;>
      cases c <;> simp [evalTestcond, testcondForUnsignedComparison, compareLongs, nextinstr,
      Regset.set, Val.cmplu, Val.cmplu_bool, Val.maketotal, Val.ofBool, int64_cmp_unfold, hln, hl, he,
      Val.Vtrue, Val.Vfalse, int_flag_eqs]
  · rw [hall] at h
    simp only [Option.some.injEq] at h
    subst h
    have hln := Integers.Ptrofs.ltu_not p q
    simp only [compareLongs, nextinstr, Val.cmplu, hall]
    cases hl : Integers.Ptrofs.ltu p q <;> cases he : Integers.Ptrofs.eq p q <;> simp only [hl, he] at hln <;>
      cases c <;> simp [evalTestcond, testcondForUnsignedComparison, Regset.set,
      Val.maketotal, Val.ofBool, ptrofs_cmpu_unfold, hln, hl, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]
  · rw [hall] at h
    simp only [compareLongs, nextinstr, Val.cmplu, hall]
    cases c <;> simp [Val.cmpDifferentBlocks] at h <;> subst h <;>
      simp [evalTestcond, testcondForUnsignedComparison, Regset.set, Val.cmpDifferentBlocks,
      Val.maketotal, Val.ofBool, Val.Vfalse, int_flag_eqs]

/-- `Asmgenproof1.compare_floats_spec` -/
theorem compare_floats_spec (rs : Regset) (n1 n2 : Floats.Float) :
    let rs' := nextinstr (compareFloats (.Vfloat n1) (.Vfloat n2) rs)
    rs' (.CR .ZF) = Val.ofBool (Floats.Float.cmp .Ceq n1 n2 || !(Floats.Float.ordered n1 n2)) ∧
    rs' (.CR .CF) = Val.ofBool (!(Floats.Float.cmp .Cge n1 n2)) ∧
    rs' (.CR .PF) = Val.ofBool (!(Floats.Float.ordered n1 n2)) ∧
    ∀ r, dataPreg r = true → rs' r = rs r := by
  refine ⟨rfl, rfl, rfl, fun r hr => ?_⟩
  cases r <;> simp_all [dataPreg, nextinstr, compareFloats, Regset.set]

/-- `Asmgenproof1.compare_floats32_spec` -/
theorem compare_floats32_spec (rs : Regset) (n1 n2 : Floats.Float32) :
    let rs' := nextinstr (compareFloats32 (.Vsingle n1) (.Vsingle n2) rs)
    rs' (.CR .ZF) = Val.ofBool (Floats.Float32.cmp .Ceq n1 n2 || !(Floats.Float32.ordered n1 n2)) ∧
    rs' (.CR .CF) = Val.ofBool (!(Floats.Float32.cmp .Cge n1 n2)) ∧
    rs' (.CR .PF) = Val.ofBool (!(Floats.Float32.ordered n1 n2)) ∧
    ∀ r, dataPreg r = true → rs' r = rs r := by
  refine ⟨rfl, rfl, rfl, fun r hr => ?_⟩
  cases r <;> simp_all [dataPreg, nextinstr, compareFloats32, Regset.set]

/-- `Asmgenproof1.eval_extcond` -/
def evalExtcond (xc : Extcond) (rs : Regset) : Option Bool :=
  match xc with
  | .Cond_base c => evalTestcond c rs
  | .Cond_and c1 c2 =>
      match evalTestcond c1 rs, evalTestcond c2 rs with
      | some b1, some b2 => some (b1 && b2)
      | _, _ => none
  | .Cond_or c1 c2 =>
      match evalTestcond c1 rs, evalTestcond c2 rs with
      | some b1, some b2 => some (b1 || b2)
      | _, _ => none

/-- `Asmgenproof1.swap_floats` -/
def swapFloats {A : Type} (c : Comparison) (n1 n2 : A) : A :=
  match c with
  | .Clt | .Cle => n2
  | .Ceq | .Cne | .Cgt | .Cge => n1

theorem float_compare_swap (n1 n2 : Floats.Float) :
    Floats.Gen.compare FloatModel.Format.binary64 n2.bits n1.bits =
      (Floats.Gen.compare FloatModel.Format.binary64 n1.bits n2.bits).map Ordering.swap :=
  Floats.Model.compare_swap _ _

theorem float32_compare_swap (n1 n2 : Floats.Float32) :
    Floats.Gen.compare FloatModel.Format.binary32 n2.bits n1.bits =
      (Floats.Gen.compare FloatModel.Format.binary32 n1.bits n2.bits).map Ordering.swap :=
  Floats.Model.compare_swap _ _

/-- `Asmgenproof1.testcond_for_float_comparison_correct` -/
theorem testcond_for_float_comparison_correct (c : Comparison) (n1 n2 : Floats.Float) (rs : Regset) :
    evalExtcond (testcondForCondition (.Ccompf c))
      (nextinstr (compareFloats (.Vfloat (swapFloats c n1 n2)) (.Vfloat (swapFloats c n2 n1)) rs)) =
    some (Floats.Float.cmp c n1 n2) := by
  cases c <;>
  simp [swapFloats, testcondForCondition, evalExtcond, evalTestcond, compareFloats, nextinstr,
    Regset.set, Floats.Float.cmp, Floats.Float.ordered, Floats.Gen.cmp, Floats.Gen.ordered,
    float_compare_swap n1 n2] <;>
  generalize Floats.Gen.compare FloatModel.Format.binary64 n1.bits n2.bits = o <;>
  rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.testcond_for_neg_float_comparison_correct` -/
theorem testcond_for_neg_float_comparison_correct (c : Comparison) (n1 n2 : Floats.Float) (rs : Regset) :
    evalExtcond (testcondForCondition (.Cnotcompf c))
      (nextinstr (compareFloats (.Vfloat (swapFloats c n1 n2)) (.Vfloat (swapFloats c n2 n1)) rs)) =
    some (!(Floats.Float.cmp c n1 n2)) := by
  cases c <;>
  simp [swapFloats, testcondForCondition, evalExtcond, evalTestcond, compareFloats, nextinstr,
    Regset.set, Floats.Float.cmp, Floats.Float.ordered, Floats.Gen.cmp, Floats.Gen.ordered,
    float_compare_swap n1 n2] <;>
  generalize Floats.Gen.compare FloatModel.Format.binary64 n1.bits n2.bits = o <;>
  rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.testcond_for_float32_comparison_correct` -/
theorem testcond_for_float32_comparison_correct (c : Comparison) (n1 n2 : Floats.Float32) (rs : Regset) :
    evalExtcond (testcondForCondition (.Ccompfs c))
      (nextinstr (compareFloats32 (.Vsingle (swapFloats c n1 n2)) (.Vsingle (swapFloats c n2 n1)) rs)) =
    some (Floats.Float32.cmp c n1 n2) := by
  cases c <;>
  simp [swapFloats, testcondForCondition, evalExtcond, evalTestcond, compareFloats32, nextinstr,
    Regset.set, Floats.Float32.cmp, Floats.Float32.ordered, Floats.Gen.cmp, Floats.Gen.ordered,
    float32_compare_swap n1 n2] <;>
  generalize Floats.Gen.compare FloatModel.Format.binary32 n1.bits n2.bits = o <;>
  rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.testcond_for_neg_float32_comparison_correct` -/
theorem testcond_for_neg_float32_comparison_correct (c : Comparison) (n1 n2 : Floats.Float32) (rs : Regset) :
    evalExtcond (testcondForCondition (.Cnotcompfs c))
      (nextinstr (compareFloats32 (.Vsingle (swapFloats c n1 n2)) (.Vsingle (swapFloats c n2 n1)) rs)) =
    some (!(Floats.Float32.cmp c n1 n2)) := by
  cases c <;>
  simp [swapFloats, testcondForCondition, evalExtcond, evalTestcond, compareFloats32, nextinstr,
    Regset.set, Floats.Float32.cmp, Floats.Float32.ordered, Floats.Gen.cmp, Floats.Gen.ordered,
    float32_compare_swap n1 n2] <;>
  generalize Floats.Gen.compare FloatModel.Format.binary32 n1.bits n2.bits = o <;>
  rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.swap_floats_commut` -/
theorem swap_floats_commut {A B : Type} (c : Comparison) (f : A → B) (x y : A) :
    swapFloats c (f x) (f y) = f (swapFloats c x y) := by
  cases c <;> rfl

/-- `Asmgenproof1.compare_floats_inv` -/
theorem compare_floats_inv (vx vy : Val) (rs : Regset) (r : Preg)
    (h : ∀ c, r ≠ .CR c) : compareFloats vx vy rs r = rs r := by
  have h1 : ∀ c, (r = .CR c) = False := fun c => eq_false (h c)
  unfold compareFloats
  split <;> simp [undefRegs, flagRegs, Regset.set, h1]

/-- `Asmgenproof1.compare_floats32_inv` -/
theorem compare_floats32_inv (vx vy : Val) (rs : Regset) (r : Preg)
    (h : ∀ c, r ≠ .CR c) : compareFloats32 vx vy rs r = rs r := by
  have h1 : ∀ c, (r = .CR c) = False := fun c => eq_false (h c)
  unfold compareFloats32
  split <;> simp [undefRegs, flagRegs, Regset.set, h1]

/-! ## Translation of conditions -/

section TRANSL_COND
variable {ge : Asm.CGenv} {fn : Asm.Function}

theorem compareInts_pc (x y : Val) (rs : Regset) (m : Mem) :
    nextinstr (compareInts x y rs m) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  simp [nextinstr, compareInts, Regset.set]

theorem compareLongs_pc (x y : Val) (rs : Regset) (m : Mem) :
    nextinstr (compareLongs x y rs m) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  simp [nextinstr, compareLongs, Regset.set]

theorem compareFloats_pc (x y : Val) (rs : Regset) :
    nextinstr (compareFloats x y rs) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [nextinstr_pc, compare_floats_inv _ _ _ _ (fun _ => by simp)]

theorem compareFloats32_pc (x y : Val) (rs : Regset) :
    nextinstr (compareFloats32 x y rs) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [nextinstr_pc, compare_floats32_inv _ _ _ _ (fun _ => by simp)]

theorem compareFloats_data (x y : Val) (rs : Regset) {r : Preg} (hr : dataPreg r = true) :
    nextinstr (compareFloats x y rs) r = rs r := by
  rw [nextinstr_inv1 _ hr, compare_floats_inv _ _ _ _ (fun c e => by subst e; simp [dataPreg] at hr)]

theorem compareFloats32_data (x y : Val) (rs : Regset) {r : Preg} (hr : dataPreg r = true) :
    nextinstr (compareFloats32 x y rs) r = rs r := by
  rw [nextinstr_inv1 _ hr, compare_floats32_inv _ _ _ _ (fun c e => by subst e; simp [dataPreg] at hr)]

/-- `Asmgenproof1.transl_cond_correct` -/
theorem transl_cond_correct {cond : Condition} {args : List Mreg} {k c : Code} (rs : Regset)
    (m : Mem) (h : translCond cond args k = .OK c) :
    ∃ rs', ExecStraight ge fn c rs m k rs' m ∧
      (match evalCondition cond ((args.map pregOf).map rs) m with
       | none => True
       | some b => evalExtcond (testcondForCondition cond) rs' = some b ∧
           evalExtcond (testcondForCondition (negateCondition cond)) rs' = some (!b)) ∧
      ∀ r, dataPreg r = true → rs' r = rs r := by
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translCond, res_bind_OK, res_pure_OK] at h <;> (try cases h) <;>
    simp only [evalCondition, List.map]
  · -- Ccomp
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareInts_pc _ _ _ _), ?_, (compare_ints_spec _ _ _ _).2.2.2.2⟩
    cases hb : Val.cmp_bool c0 (rs (.IR r1)) (rs (.IR r2))
    · trivial
    · exact ⟨testcond_for_signed_comparison_32_correct _ _ _ _ _ _ hb, testcond_for_signed_comparison_32_correct _ _ _ _ _ _ (by rw [Val.negate_cmp_bool, hb]; rfl)⟩
  · -- Ccompu
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareInts_pc _ _ _ _), ?_, (compare_ints_spec _ _ _ _).2.2.2.2⟩
    cases hb : Val.cmpu_bool (Mem.validPointer m) c0 (rs (.IR r1)) (rs (.IR r2))
    · trivial
    · exact ⟨testcond_for_unsigned_comparison_32_correct _ _ _ _ _ _ hb, testcond_for_unsigned_comparison_32_correct _ _ _ _ _ _ (by rw [Val.negate_cmpu_bool, hb]; rfl)⟩
  · -- Ccompimm
    rename_i c0 n r1 h; obtain ⟨hr1, rfl⟩ := h
    rw [ireg_of_eq hr1]
    by_cases hn : n = Integers.Int.zero
    · subst hn
      refine ⟨_, .one _ _ _ _ _ _ rfl (compareInts_pc _ _ _ _), ?_, (compare_ints_spec _ _ _ _).2.2.2.2⟩
      cases hv : rs (.IR r1) <;> simp only [Val.cmp_bool] <;> try trivial
      rename_i i
      have hand : Val.and (.Vint i) (.Vint i) = .Vint i := by simp only [Val.and, Integers.Int.and_idem]
      refine ⟨?_, ?_⟩
      · show evalTestcond _ _ = _
        rw [hand]; exact testcond_for_signed_comparison_32_correct _ _ _ _ _ _ rfl
      · show evalTestcond _ _ = _
        rw [hand]; exact testcond_for_signed_comparison_32_correct _ _ _ _ _ _ (by rw [Val.negate_cmp_bool]; rfl)
    · simp only [if_neg hn]
      refine ⟨_, .one _ _ _ _ _ _ rfl (compareInts_pc _ _ _ _), ?_, (compare_ints_spec _ _ _ _).2.2.2.2⟩
      cases hb : Val.cmp_bool c0 (rs (.IR r1)) (.Vint n)
      · trivial
      · exact ⟨testcond_for_signed_comparison_32_correct _ _ _ _ _ _ hb, testcond_for_signed_comparison_32_correct _ _ _ _ _ _ (by rw [Val.negate_cmp_bool, hb]; rfl)⟩
  · -- Ccompuimm
    rename_i c0 n r1 h; obtain ⟨hr1, rfl⟩ := h
    rw [ireg_of_eq hr1]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareInts_pc _ _ _ _), ?_, (compare_ints_spec _ _ _ _).2.2.2.2⟩
    cases hb : Val.cmpu_bool (Mem.validPointer m) c0 (rs (.IR r1)) (.Vint n)
    · trivial
    · exact ⟨testcond_for_unsigned_comparison_32_correct _ _ _ _ _ _ hb, testcond_for_unsigned_comparison_32_correct _ _ _ _ _ _ (by rw [Val.negate_cmpu_bool, hb]; rfl)⟩
  · -- Ccompl
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareLongs_pc _ _ _ _), ?_, (compare_longs_spec _ _ _ _).2.2.2.2⟩
    cases hb : Val.cmpl_bool c0 (rs (.IR r1)) (rs (.IR r2))
    · trivial
    · exact ⟨testcond_for_signed_comparison_64_correct _ _ _ _ _ _ hb, testcond_for_signed_comparison_64_correct _ _ _ _ _ _ (by rw [Val.negate_cmpl_bool, hb]; rfl)⟩
  · -- Ccomplu
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareLongs_pc _ _ _ _), ?_, (compare_longs_spec _ _ _ _).2.2.2.2⟩
    cases hb : Val.cmplu_bool (Mem.validPointer m) c0 (rs (.IR r1)) (rs (.IR r2))
    · trivial
    · exact ⟨testcond_for_unsigned_comparison_64_correct _ _ _ _ _ _ hb, testcond_for_unsigned_comparison_64_correct _ _ _ _ _ _ (by rw [Val.negate_cmplu_bool, hb]; rfl)⟩
  · -- Ccomplimm
    rename_i c0 n r1 h; obtain ⟨hr1, rfl⟩ := h
    rw [ireg_of_eq hr1]
    by_cases hn : n = Integers.Int64.zero
    · subst hn
      refine ⟨_, .one _ _ _ _ _ _ rfl (compareLongs_pc _ _ _ _), ?_, (compare_longs_spec _ _ _ _).2.2.2.2⟩
      cases hv : rs (.IR r1) <;> simp only [Val.cmpl_bool] <;> try trivial
      rename_i i
      have hand : Val.andl (.Vlong i) (.Vlong i) = .Vlong i := by simp only [Val.andl, Integers.Int64.and_idem]
      refine ⟨?_, ?_⟩
      · show evalTestcond _ _ = _
        rw [hand]; exact testcond_for_signed_comparison_64_correct _ _ _ _ _ _ rfl
      · show evalTestcond _ _ = _
        rw [hand]; exact testcond_for_signed_comparison_64_correct _ _ _ _ _ _ (by rw [Val.negate_cmpl_bool]; rfl)
    · simp only [if_neg hn]
      refine ⟨_, .one _ _ _ _ _ _ rfl (compareLongs_pc _ _ _ _), ?_, (compare_longs_spec _ _ _ _).2.2.2.2⟩
      cases hb : Val.cmpl_bool c0 (rs (.IR r1)) (.Vlong n)
      · trivial
      · exact ⟨testcond_for_signed_comparison_64_correct _ _ _ _ _ _ hb, testcond_for_signed_comparison_64_correct _ _ _ _ _ _ (by rw [Val.negate_cmpl_bool, hb]; rfl)⟩
  · -- Ccompluimm
    rename_i c0 n r1 h; obtain ⟨hr1, rfl⟩ := h
    rw [ireg_of_eq hr1]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareLongs_pc _ _ _ _), ?_, (compare_longs_spec _ _ _ _).2.2.2.2⟩
    cases hb : Val.cmplu_bool (Mem.validPointer m) c0 (rs (.IR r1)) (.Vlong n)
    · trivial
    · exact ⟨testcond_for_unsigned_comparison_64_correct _ _ _ _ _ _ hb, testcond_for_unsigned_comparison_64_correct _ _ _ _ _ _ (by rw [Val.negate_cmplu_bool, hb]; rfl)⟩
  · -- Ccompf
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [freg_of_eq hr1, freg_of_eq hr2]
    refine ⟨nextinstr (compareFloats (swapFloats c0 (rs (.FR r1)) (rs (.FR r2)))
      (swapFloats c0 (rs (.FR r2)) (rs (.FR r1))) rs),
      .one _ _ _ _ _ _ (by cases c0 <;> rfl) (compareFloats_pc _ _ _), ?_, fun r hr => compareFloats_data _ _ _ hr⟩
    cases hv1 : rs (.FR r1) <;> cases hv2 : rs (.FR r2) <;> simp only [Val.cmpf_bool] <;>
      try trivial
    rename_i x y
    rw [swap_floats_commut c0 Val.Vfloat x y, swap_floats_commut c0 Val.Vfloat y x]
    exact ⟨testcond_for_float_comparison_correct _ _ _ _, testcond_for_neg_float_comparison_correct _ _ _ _⟩
  · -- Cnotcompf
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [freg_of_eq hr1, freg_of_eq hr2]
    refine ⟨nextinstr (compareFloats (swapFloats c0 (rs (.FR r1)) (rs (.FR r2)))
      (swapFloats c0 (rs (.FR r2)) (rs (.FR r1))) rs),
      .one _ _ _ _ _ _ (by cases c0 <;> rfl) (compareFloats_pc _ _ _), ?_, fun r hr => compareFloats_data _ _ _ hr⟩
    cases hv1 : rs (.FR r1) <;> cases hv2 : rs (.FR r2) <;> simp only [Val.cmpf_bool, Option.map] <;>
      try trivial
    rename_i x y
    rw [swap_floats_commut c0 Val.Vfloat x y, swap_floats_commut c0 Val.Vfloat y x]
    exact ⟨testcond_for_neg_float_comparison_correct _ _ _ _,
      by rw [Bool.not_not]; exact testcond_for_float_comparison_correct _ _ _ _⟩
  · -- Ccompfs
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [freg_of_eq hr1, freg_of_eq hr2]
    refine ⟨nextinstr (compareFloats32 (swapFloats c0 (rs (.FR r1)) (rs (.FR r2)))
      (swapFloats c0 (rs (.FR r2)) (rs (.FR r1))) rs),
      .one _ _ _ _ _ _ (by cases c0 <;> rfl) (compareFloats32_pc _ _ _), ?_, fun r hr => compareFloats32_data _ _ _ hr⟩
    cases hv1 : rs (.FR r1) <;> cases hv2 : rs (.FR r2) <;> simp only [Val.cmpfs_bool] <;>
      try trivial
    rename_i x y
    rw [swap_floats_commut c0 Val.Vsingle x y, swap_floats_commut c0 Val.Vsingle y x]
    exact ⟨testcond_for_float32_comparison_correct _ _ _ _, testcond_for_neg_float32_comparison_correct _ _ _ _⟩
  · -- Cnotcompfs
    rename_i c0 r1 h; obtain ⟨hr1, r2, hr2, rfl⟩ := h
    rw [freg_of_eq hr1, freg_of_eq hr2]
    refine ⟨nextinstr (compareFloats32 (swapFloats c0 (rs (.FR r1)) (rs (.FR r2)))
      (swapFloats c0 (rs (.FR r2)) (rs (.FR r1))) rs),
      .one _ _ _ _ _ _ (by cases c0 <;> rfl) (compareFloats32_pc _ _ _), ?_, fun r hr => compareFloats32_data _ _ _ hr⟩
    cases hv1 : rs (.FR r1) <;> cases hv2 : rs (.FR r2) <;> simp only [Val.cmpfs_bool, Option.map] <;>
      try trivial
    rename_i x y
    rw [swap_floats_commut c0 Val.Vsingle x y, swap_floats_commut c0 Val.Vsingle y x]
    exact ⟨testcond_for_neg_float32_comparison_correct _ _ _ _,
      by rw [Bool.not_not]; exact testcond_for_float32_comparison_correct _ _ _ _⟩
  · -- Cmaskzero
    rename_i n r1 h; obtain ⟨hr1, rfl⟩ := h
    rw [ireg_of_eq hr1]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareInts_pc _ _ _ _), ?_, (compare_ints_spec _ _ _ _).2.2.2.2⟩
    cases hv : rs (.IR r1) <;> simp only [Val.maskzero_bool] <;> try trivial
    rename_i i
    cases he : Integers.Int.eq (Integers.Int.and i n) Integers.Int.zero <;>
      simp [testcondForCondition, negateCondition, evalExtcond, evalTestcond, compareInts, nextinstr,
        Regset.set, Val.and, Val.cmpu, Val.cmpu_bool, Val.ofOptbool, Val.ofBool, Val.Vzero,
        int_cmp_unfold, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]
  · -- Cmasknotzero
    rename_i n r1 h; obtain ⟨hr1, rfl⟩ := h
    rw [ireg_of_eq hr1]
    refine ⟨_, .one _ _ _ _ _ _ rfl (compareInts_pc _ _ _ _), ?_, (compare_ints_spec _ _ _ _).2.2.2.2⟩
    cases hv : rs (.IR r1) <;> simp only [Val.maskzero_bool, Option.map] <;> try trivial
    rename_i i
    cases he : Integers.Int.eq (Integers.Int.and i n) Integers.Int.zero <;>
      simp [testcondForCondition, negateCondition, evalExtcond, evalTestcond, compareInts, nextinstr,
        Regset.set, Val.and, Val.cmpu, Val.cmpu_bool, Val.ofOptbool, Val.ofBool, Val.Vzero,
        int_cmp_unfold, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]

end TRANSL_COND

/-! ## `setcc` and conditional moves -/

section SETCC
variable {ge : Asm.CGenv} {fn : Asm.Function}

/-- `Asmgenproof1.eval_testcond_nextinstr` -/
theorem eval_testcond_nextinstr (c : Testcond) (rs : Regset) :
    evalTestcond c (nextinstr rs) = evalTestcond c rs := by
  cases c <;> simp [evalTestcond, nextinstr, Regset.set]

/-- `Asmgenproof1.eval_testcond_set_ireg` -/
theorem eval_testcond_set_ireg (c : Testcond) (rs : Regset) (r : Ireg) (v : Val) :
    evalTestcond c (rs.set (.IR r) v) = evalTestcond c rs := by
  cases c <;> simp [evalTestcond, Regset.set]

/-- `Asmgenproof1.mk_setcc_base_correct` -/
theorem mk_setcc_base_correct (cond : Extcond) (rd : Ireg) (k : Code) (rs1 : Regset) (m : Mem) :
    ∃ rs2, ExecStraight ge fn (mkSetccBase cond rd k) rs1 m k rs2 m ∧
      rs2 (.IR rd) = Val.ofOptbool (evalExtcond cond rs1) ∧
      ∀ r, dataPreg r = true → r ≠ .IR .RAX ∧ r ≠ .IR .RCX → r ≠ .IR rd → rs2 r = rs1 r := by
  cases cond with
  | Cond_base c =>
    refine ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_pc _), ?_, ?_⟩
    · simp [nextinstr, Regset.set, evalExtcond]
    · intro r hr _ h3
      cases r <;> simp_all [dataPreg, nextinstr, Regset.set]
  | Cond_or c1 c2 =>
    by_cases hrd : rd = .RAX
    · subst hrd
      simp only [mkSetccBase]
      refine ⟨_, exec_straight_three rfl
        (by show nextSet _ _ _ _ = _; rw [eval_testcond_nextinstr, eval_testcond_set_ireg]) (by rfl)
        (by exact nextinstr_pc _) (by exact nextinstr_pc _) (by exact nextinstrNf_pc _), ?_, ?_⟩
      · simp [nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set, evalExtcond] <;>
          generalize evalTestcond c1 rs1 = e1 <;> generalize evalTestcond c2 rs1 = e2 <;>
          rcases e1 with _ | ⟨_ | _⟩ <;> rcases e2 with _ | ⟨_ | _⟩ <;> rfl
      · intro r hr ⟨h1, h2⟩ _
        cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]
    · simp only [mkSetccBase, if_neg hrd]
      refine ⟨_, exec_straight_three rfl
        (by show nextSet _ _ _ _ = _; rw [eval_testcond_nextinstr, eval_testcond_set_ireg]) (by rfl)
        (by exact nextinstr_pc _) (by exact nextinstr_pc _) (by exact nextinstrNf_pc _), ?_, ?_⟩
      · simp [nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set, Ne.symm hrd, evalExtcond] <;>
          generalize evalTestcond c1 rs1 = e1 <;> generalize evalTestcond c2 rs1 = e2 <;>
          rcases e1 with _ | ⟨_ | _⟩ <;> rcases e2 with _ | ⟨_ | _⟩ <;> rfl
      · intro r hr ⟨h1, h2⟩ h3
        cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]
  | Cond_and c1 c2 =>
    by_cases hrd : rd = .RAX
    · subst hrd
      simp only [mkSetccBase]
      refine ⟨_, exec_straight_three rfl
        (by show nextSet _ _ _ _ = _; rw [eval_testcond_nextinstr, eval_testcond_set_ireg]) (by rfl)
        (by exact nextinstr_pc _) (by exact nextinstr_pc _) (by exact nextinstrNf_pc _), ?_, ?_⟩
      · simp [nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set, evalExtcond] <;>
          generalize evalTestcond c1 rs1 = e1 <;> generalize evalTestcond c2 rs1 = e2 <;>
          rcases e1 with _ | ⟨_ | _⟩ <;> rcases e2 with _ | ⟨_ | _⟩ <;> rfl
      · intro r hr ⟨h1, h2⟩ _
        cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]
    · simp only [mkSetccBase, if_neg hrd]
      refine ⟨_, exec_straight_three rfl
        (by show nextSet _ _ _ _ = _; rw [eval_testcond_nextinstr, eval_testcond_set_ireg]) (by rfl)
        (by exact nextinstr_pc _) (by exact nextinstr_pc _) (by exact nextinstrNf_pc _), ?_, ?_⟩
      · simp [nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set, Ne.symm hrd, evalExtcond] <;>
          generalize evalTestcond c1 rs1 = e1 <;> generalize evalTestcond c2 rs1 = e2 <;>
          rcases e1 with _ | ⟨_ | _⟩ <;> rcases e2 with _ | ⟨_ | _⟩ <;> rfl
      · intro r hr ⟨h1, h2⟩ h3
        cases r <;> simp_all [dataPreg, nextinstrNf, nextinstr, undefRegs, flagRegs, Regset.set]

/-- `Asmgenproof1.mk_setcc_correct` -/
theorem mk_setcc_correct (cond : Extcond) (rd : Ireg) (k : Code) (rs1 : Regset) (m : Mem) :
    ∃ rs2, ExecStraight ge fn (mkSetcc cond rd k) rs1 m k rs2 m ∧
      rs2 (.IR rd) = Val.ofOptbool (evalExtcond cond rs1) ∧
      ∀ r, dataPreg r = true → r ≠ .IR .RAX ∧ r ≠ .IR .RCX → r ≠ .IR rd → rs2 r = rs1 r := by
  simp only [mkSetcc, Archi.ptr64, Bool.true_or, if_true]
  exact mk_setcc_base_correct cond rd k rs1 m

/-- `Asmgenproof1.negate_extcond` -/
def negateExtcond (xc : Extcond) : Extcond :=
  match xc with
  | .Cond_base c => .Cond_base (negateTestcond c)
  | .Cond_and c1 c2 => .Cond_or (negateTestcond c1) (negateTestcond c2)
  | .Cond_or c1 c2 => .Cond_and (negateTestcond c1) (negateTestcond c2)

/-- `Asmgenproof1.negate_testcond_for_condition` -/
theorem negate_testcond_for_condition (cond : Condition) :
    negateExtcond (testcondForCondition cond) = testcondForCondition (negateCondition cond) := by
  cases cond <;> first | rfl | (rename_i c; cases c <;> rfl) | (rename_i c _; cases c <;> rfl)

/-- `Asmgenproof1.mk_sel_correct` -/
theorem mk_sel_correct (xc : Extcond) (ty : ATyp) {rd r2 : Ireg} {k c : Code} (ob : Option Bool)
    (rs : Regset) (m : Mem) (h : mkSel xc rd r2 k = .OK c) (hne : rd ≠ r2)
    (hob : match ob with
      | none => True
      | some b => evalExtcond xc rs = some b ∧ evalExtcond (negateExtcond xc) rs = some (!b)) :
    ∃ rs', ExecStraight ge fn c rs m k rs' m ∧
      Val.Lessdef (Val.select ob (rs (.IR rd)) (rs (.IR r2)) ty) (rs' (.IR rd)) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  cases xc with
  | Cond_base c0 =>
    cases h
    refine ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_pc _), ?_, ?_⟩
    · rw [nextinstr_set_same _ _ rfl]
      cases ob with
      | none => exact .undef _
      | some b =>
        have hb : evalTestcond (negateTestcond c0) rs = some (!b) := hob.2
        simp only [hb, Val.select]
        cases b <;> exact Val.lessdef_normalize _ _
    · intro r hr hne'
      exact nextinstr_set_other _ _ hr hne'
  | Cond_and c1 c2 =>
    cases h
    refine ⟨_, exec_straight_two rfl rfl (nextinstr_pc _) (nextinstr_pc _), ?_, ?_⟩
    · rw [nextinstr_set_same _ _ rfl, eval_testcond_nextinstr, eval_testcond_set_ireg]
      cases ob with
      | none => exact .undef _
      | some b =>
        have hb := hob.2
        simp only [negateExtcond, evalExtcond] at hb
        cases h1 : evalTestcond (negateTestcond c1) rs <;>
          cases h2 : evalTestcond (negateTestcond c2) rs <;> simp only [h1, h2] at hb <;> try cases hb
        rename_i b1 b2
        simp only [Option.some.injEq] at hb
        have hrd : (Preg.IR r2) ≠ (Preg.IR rd) := fun e => hne (by cases e; rfl)
        simp only [Val.select, nextinstr_set_same _ _ (show dataPreg (.IR rd) = true from rfl),
          nextinstr_set_other _ _ (show dataPreg (.IR r2) = true from rfl) hrd]
        cases b1 <;> cases b2 <;> cases b <;> simp at hb <;> exact Val.lessdef_normalize _ _
    · intro r hr hne'
      rw [nextinstr_set_other _ _ hr hne', nextinstr_set_other _ _ hr hne']
  | Cond_or c1 c2 => cases h

/-- `Asmgenproof1.transl_sel_correct` -/
theorem transl_sel_correct (ty : ATyp) {cond : Condition} {args : List Mreg} {rd r2 : Ireg}
    {k c : Code} (rs : Regset) (m : Mem) (h : translSel cond args rd r2 k = .OK c) :
    ∃ rs', ExecStraight ge fn c rs m k rs' m ∧
      Val.Lessdef (Val.select (evalCondition cond ((args.map pregOf).map rs) m)
        (rs (.IR rd)) (rs (.IR r2)) ty) (rs' (.IR rd)) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  unfold translSel at h
  by_cases heq : rd = r2
  · subst heq
    rw [if_pos rfl] at h; cases h
    refine ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_pc _), ?_, ?_⟩
    · rw [nextinstr_set_same _ _ rfl]
      cases evalCondition cond ((args.map pregOf).map rs) m with
      | none => exact .undef _
      | some b => cases b <;> exact Val.lessdef_normalize _ _
    · intro r hr hne'
      exact nextinstr_set_other _ _ hr hne'
  · simp only [if_neg heq, res_bind_OK] at h
    obtain ⟨k1, hk1, hc⟩ := h
    obtain ⟨rs1, A, B, C⟩ := transl_cond_correct (ge := ge) (fn := fn) rs m hc
    rw [← negate_testcond_for_condition] at B
    obtain ⟨rs2, D, E, F⟩ := mk_sel_correct _ ty (evalCondition cond ((args.map pregOf).map rs) m) rs1 m hk1 heq B
    refine ⟨rs2, exec_straight_trans A D, ?_, fun r hr hne => by rw [F r hr hne, C r hr]⟩
    rwa [C _ rfl, C _ rfl] at E

end SETCC

end Asmgenproof1
end X86
end CC
