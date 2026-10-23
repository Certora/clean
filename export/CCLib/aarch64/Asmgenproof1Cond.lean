/-
  Correctness of the AArch64 code generator's constructor functions,
  part 3 — port of the "Condition bits" section of `aarch64/Asmgenproof1.v`:
  `compare_int_spec`, `eval_testcond_compare_sint/uint`, `compare_long_spec`,
  `int64_sub_overflow`, `eval_testcond_compare_slong/ulong`,
  `compare_float_spec`, `eval_testcond_compare_(not_)float`,
  `compare_single_spec`, `eval_testcond_compare_(not_)single`,
  `compare_float_inv`, `compare_single_inv`.
-/
import CCLib.aarch64.Asmgenproof1Shift
import CCLib.lib.IntegersOverflow
namespace CC
namespace Asmgenproof1
open Asm Asmgen Asmgenproof0

/-- `Asmgenproof1.compare_int_spec` -/
theorem compare_int_spec (rs : Regset) (v1 v2 : Val) (m : Mem) :
    let rs' := compareInt rs v1 v2 m
    rs' (.CR .CN) = Val.negative (Val.sub v1 v2) ∧
    rs' (.CR .CZ) = Val.cmpu (Mem.validPointer m) .Ceq v1 v2 ∧
    rs' (.CR .CC) = Val.cmpu (Mem.validPointer m) .Cge v1 v2 ∧
    rs' (.CR .CV) = Val.sub_overflow v1 v2 := by
  simp [compareInt, Regset.set]

/-- `Asmgenproof1.compare_long_spec` -/
theorem compare_long_spec (rs : Regset) (v1 v2 : Val) (m : Mem) :
    let rs' := compareLong rs v1 v2 m
    rs' (.CR .CN) = Val.negativel (Val.subl v1 v2) ∧
    rs' (.CR .CZ) = Val.maketotal (Val.cmplu (Mem.validPointer m) .Ceq v1 v2) ∧
    rs' (.CR .CC) = Val.maketotal (Val.cmplu (Mem.validPointer m) .Cge v1 v2) ∧
    rs' (.CR .CV) = Val.subl_overflow v1 v2 := by
  simp [compareLong, Regset.set]

/-- Unfolding of `Int.cmp` / `Int.cmpu` on each comparison. -/
theorem int_cmp_unfold (x y : Integers.Int) :
    Integers.Int.cmp .Ceq x y = Integers.Int.eq x y ∧ Integers.Int.cmp .Cne x y = !(Integers.Int.eq x y) ∧
    Integers.Int.cmp .Clt x y = Integers.Int.lt x y ∧ Integers.Int.cmp .Cle x y = !(Integers.Int.lt y x) ∧
    Integers.Int.cmp .Cgt x y = Integers.Int.lt y x ∧ Integers.Int.cmp .Cge x y = !(Integers.Int.lt x y) ∧
    Integers.Int.cmpu .Ceq x y = Integers.Int.eq x y ∧ Integers.Int.cmpu .Cne x y = !(Integers.Int.eq x y) ∧
    Integers.Int.cmpu .Clt x y = Integers.Int.ltu x y ∧ Integers.Int.cmpu .Cle x y = !(Integers.Int.ltu y x) ∧
    Integers.Int.cmpu .Cgt x y = Integers.Int.ltu y x ∧ Integers.Int.cmpu .Cge x y = !(Integers.Int.ltu x y) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem int_flag_eqs :
    Integers.Int.eq Integers.Int.one Integers.Int.one = true ∧ Integers.Int.eq Integers.Int.zero Integers.Int.one = false ∧
    Integers.Int.eq Integers.Int.one Integers.Int.zero = false ∧ Integers.Int.eq Integers.Int.zero Integers.Int.zero = true := by decide

/-- `Asmgenproof1.eval_testcond_compare_sint` -/
theorem eval_testcond_compare_sint (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset) (m : Mem)
    (h : Val.cmp_bool c v1 v2 = some b) :
    evalTestcond (condForSignedCmp c) (compareInt rs v1 v2 m) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmp_bool] at h
  rename_i x y
  subst h
  have hx := Integers.Int.lt_sub_overflow x y
  have hnl := Integers.Int.not_lt x y
  have hln := Integers.Int.lt_not x y
  cases hl : Integers.Int.lt x y <;> cases he : Integers.Int.eq x y <;> simp only [hl, he] at hx hnl hln <;>
    cases c <;> simp [evalTestcond, condForSignedCmp, compareInt, Regset.set, Val.cmpu, Val.cmpu_bool,
    Val.ofOptbool, Val.ofBool, Val.sub_overflow, Val.negative, Val.sub, hx, int_cmp_unfold, hln, hl, he,
    Val.Vtrue, Val.Vfalse, int_flag_eqs]

/-- `Asmgenproof1.eval_testcond_compare_uint` -/
theorem eval_testcond_compare_uint (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset) (m : Mem)
    (h : Val.cmpu_bool (Mem.validPointer m) c v1 v2 = some b) :
    evalTestcond (condForUnsignedCmp c) (compareInt rs v1 v2 m) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpu_bool, Archi.ptr64] at h
  rename_i x y
  subst h
  have hln := Integers.Int.ltu_not x y
  cases hl : Integers.Int.ltu x y <;> cases he : Integers.Int.eq x y <;> simp only [hl, he] at hln <;>
    cases c <;> simp [evalTestcond, condForUnsignedCmp, compareInt, Regset.set, Val.cmpu, Val.cmpu_bool,
    Val.ofOptbool, Val.ofBool, int_cmp_unfold, hln, hl, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]

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

/-- `Asmgenproof1.int64_sub_overflow` -/
theorem int64_sub_overflow (x y : Integers.Int64) :
    Integers.Int.xor (Integers.Int.repr (Integers.Int64.unsigned (Integers.Int64.sub_overflow x y Integers.Int64.zero)))
      (Integers.Int.repr (Integers.Int64.unsigned (Integers.Int64.negative (Integers.Int64.sub x y)))) =
    (if Integers.Int64.lt x y then Integers.Int.one else Integers.Int.zero) := by
  have hx := Integers.Int64.lt_sub_overflow x y
  have ha : Integers.Int64.sub_overflow x y Integers.Int64.zero = Integers.Int64.zero ∨
      Integers.Int64.sub_overflow x y Integers.Int64.zero = Integers.Int64.one := by
    unfold Integers.Int64.sub_overflow Integers.MI.sub_overflow; dsimp only; split <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hb : Integers.Int64.negative (Integers.Int64.sub x y) = Integers.Int64.zero ∨
      Integers.Int64.negative (Integers.Int64.sub x y) = Integers.Int64.one := by
    unfold Integers.Int64.negative Integers.MI.negative; split <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at hx ⊢ <;>
    cases hl : Integers.Int64.lt x y <;> simp only [hl] at hx <;> revert hx <;> decide

/-- `Asmgenproof1.eval_testcond_compare_slong` -/
theorem eval_testcond_compare_slong (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset) (m : Mem)
    (h : Val.cmpl_bool c v1 v2 = some b) :
    evalTestcond (condForSignedCmp c) (compareLong rs v1 v2 m) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpl_bool] at h
  rename_i x y
  subst h
  have hx := int64_sub_overflow x y
  have hln := Integers.Int64.lt_not x y
  cases hl : Integers.Int64.lt x y <;> cases he : Integers.Int64.eq x y <;> simp only [hl, he] at hx hln <;>
    cases c <;> simp [evalTestcond, condForSignedCmp, compareLong, Regset.set, Val.cmplu, Val.cmplu_bool,
    Val.maketotal, Val.ofBool, Val.subl_overflow, Val.negativel, Val.subl, hx, int64_cmp_unfold, hln, hl, he,
    Val.Vtrue, Val.Vfalse, int_flag_eqs]

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

/-- `Asmgenproof1.eval_testcond_compare_ulong` -/
theorem eval_testcond_compare_ulong (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset) (m : Mem)
    (h : Val.cmplu_bool (Mem.validPointer m) c v1 v2 = some b) :
    evalTestcond (condForUnsignedCmp c) (compareLong rs v1 v2 m) = some b := by
  rcases cmplu_bool_shape _ c v1 v2 b h with ⟨x, y, rfl, rfl⟩ | ⟨p, q, hall⟩ | hall
  · simp [Val.cmplu_bool] at h
    subst h
    have hln := Integers.Int64.ltu_not x y
    cases hl : Integers.Int64.ltu x y <;> cases he : Integers.Int64.eq x y <;> simp only [hl, he] at hln <;>
      cases c <;> simp [evalTestcond, condForUnsignedCmp, compareLong, Regset.set, Val.cmplu, Val.cmplu_bool,
      Val.maketotal, Val.ofBool, int64_cmp_unfold, hln, hl, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]
  · rw [hall] at h
    simp only [Option.some.injEq] at h
    subst h
    have hln := Integers.Ptrofs.ltu_not p q
    simp only [compareLong, Val.cmplu, hall]
    cases hl : Integers.Ptrofs.ltu p q <;> cases he : Integers.Ptrofs.eq p q <;> simp only [hl, he] at hln <;>
      cases c <;> simp [evalTestcond, condForUnsignedCmp, Regset.set,
      Val.maketotal, Val.ofBool, ptrofs_cmpu_unfold, hln, hl, he, Val.Vtrue, Val.Vfalse, int_flag_eqs]
  · rw [hall] at h
    simp only [compareLong, Val.cmplu, hall]
    cases c <;> simp [Val.cmpDifferentBlocks] at h <;> subst h <;>
      simp [evalTestcond, condForUnsignedCmp, Regset.set, Val.cmpDifferentBlocks,
      Val.maketotal, Val.ofBool, Val.Vfalse, int_flag_eqs]

/-- `Asmgenproof1.compare_float_spec` -/
theorem compare_float_spec (rs : Regset) (f1 f2 : Floats.Float) :
    let rs' := compareFloat rs (.Vfloat f1) (.Vfloat f2)
    rs' (.CR .CN) = Val.ofBool (Floats.Float.cmp .Clt f1 f2) ∧
    rs' (.CR .CZ) = Val.ofBool (Floats.Float.cmp .Ceq f1 f2) ∧
    rs' (.CR .CC) = Val.ofBool (!(Floats.Float.cmp .Clt f1 f2)) ∧
    rs' (.CR .CV) = Val.ofBool (!(Floats.Float.ordered f1 f2)) := by
  simp [compareFloat, setFlags, Regset.set]

/-- `Asmgenproof1.eval_testcond_compare_float` -/
theorem eval_testcond_compare_float (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset)
    (h : Val.cmpf_bool c v1 v2 = some b) :
    evalTestcond (condForFloatCmp c) (compareFloat rs v1 v2) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpf_bool] at h
  subst h
  simp only [compareFloat, setFlags, Floats.Float.cmp, Floats.Float.ordered, Floats.Gen.cmp, Floats.Gen.ordered]
  generalize Floats.Gen.compare _ _ _ = o
  cases c <;> rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.eval_testcond_compare_not_float` -/
theorem eval_testcond_compare_not_float (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset)
    (h : Option.map (!·) (Val.cmpf_bool c v1 v2) = some b) :
    evalTestcond (condForFloatNotCmp c) (compareFloat rs v1 v2) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpf_bool] at h
  obtain rfl : b = !(Floats.Float.cmp c _ _) := by rw [h, Bool.not_not]
  simp only [compareFloat, setFlags, Floats.Float.cmp, Floats.Float.ordered, Floats.Gen.cmp, Floats.Gen.ordered]
  generalize Floats.Gen.compare _ _ _ = o
  cases c <;> rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.compare_single_spec` -/
theorem compare_single_spec (rs : Regset) (f1 f2 : Floats.Float32) :
    let rs' := compareSingle rs (.Vsingle f1) (.Vsingle f2)
    rs' (.CR .CN) = Val.ofBool (Floats.Float32.cmp .Clt f1 f2) ∧
    rs' (.CR .CZ) = Val.ofBool (Floats.Float32.cmp .Ceq f1 f2) ∧
    rs' (.CR .CC) = Val.ofBool (!(Floats.Float32.cmp .Clt f1 f2)) ∧
    rs' (.CR .CV) = Val.ofBool (!(Floats.Float32.ordered f1 f2)) := by
  simp [compareSingle, setFlags, Regset.set]

/-- `Asmgenproof1.eval_testcond_compare_single` -/
theorem eval_testcond_compare_single (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset)
    (h : Val.cmpfs_bool c v1 v2 = some b) :
    evalTestcond (condForFloatCmp c) (compareSingle rs v1 v2) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpfs_bool] at h
  subst h
  simp only [compareSingle, setFlags, Floats.Float32.cmp, Floats.Float32.ordered, Floats.Gen.cmp, Floats.Gen.ordered]
  generalize Floats.Gen.compare _ _ _ = o
  cases c <;> rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.eval_testcond_compare_not_single` -/
theorem eval_testcond_compare_not_single (c : Comparison) (v1 v2 : Val) (b : Bool) (rs : Regset)
    (h : Option.map (!·) (Val.cmpfs_bool c v1 v2) = some b) :
    evalTestcond (condForFloatNotCmp c) (compareSingle rs v1 v2) = some b := by
  cases v1 <;> cases v2 <;> simp [Val.cmpfs_bool] at h
  obtain rfl : b = !(Floats.Float32.cmp c _ _) := by rw [h, Bool.not_not]
  simp only [compareSingle, setFlags, Floats.Float32.cmp, Floats.Float32.ordered, Floats.Gen.cmp, Floats.Gen.ordered]
  generalize Floats.Gen.compare _ _ _ = o
  cases c <;> rcases o with _ | ⟨_ | _ | _⟩ <;> rfl

/-- `Asmgenproof1.compare_float_inv` -/
theorem compare_float_inv (rs : Regset) (v1 v2 : Val) (r : Preg) (hr : ∀ c, r ≠ .CR c) :
    nextinstr (compareFloat rs v1 v2) r = nextinstr rs r := by
  have h1 : ∀ c, (r = .CR c) = False := fun c => eq_false (hr c)
  unfold compareFloat
  split <;> simp [nextinstr, setFlags, Regset.set, h1]

/-- `Asmgenproof1.compare_single_inv` -/
theorem compare_single_inv (rs : Regset) (v1 v2 : Val) (r : Preg) (hr : ∀ c, r ≠ .CR c) :
    nextinstr (compareSingle rs v1 v2) r = nextinstr rs r := by
  have h1 : ∀ c, (r = .CR c) = False := fun c => eq_false (hr c)
  unfold compareSingle
  split <;> simp [nextinstr, setFlags, Regset.set, h1]

end Asmgenproof1
end CC
