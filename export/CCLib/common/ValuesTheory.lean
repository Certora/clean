/-
  The remaining theorems of `common/Values.v` (those not already in
  `ValuesLemmas.lean`, `Builtins.lean`, `MemdataInject.lean`,
  `MemoryInjections.lean` or `CopInject.lean`): typing (`has_subtype`,
  `normalize_type`, `load_result_type`, …), booleans (`norm_bool_cases`,
  `bool_of_val_of_optbool`, the `*_optbool` comparison laws), the algebra of
  the 64-bit and backend operations (`addl_assoc`, `mul_pow2`, `divs_pow2`,
  `shl_rolm`, `shrx_carry`, `rolm_rolm`, …), float comparisons
  (`cmpf_le`, …), and the remaining `lessdef` / `inject` compatibility
  lemmas (`cmpu_bool_inject`, `select_inject`, `has_argtype_inject`, …).

  As everywhere in the port, `Archi.ptr64 = true` (aarch64). Rocq proves
  several of these by case analysis on `Archi.ptr64`; here only the 64-bit
  case arises, and the statements are otherwise CompCert's.
-/
import CCLib.common.ValuesOps
import CCLib.lib.IntegersPow2
import CCLib.cfrontend.CopInject

namespace CC
namespace Val

open Integers (Ptrofs)

/-! ## Typing -/

theorem hasTypeP_iff (v : Val) (t : ATyp) : HasType v t ↔ hasType v t = true := Iff.rfl

/-- `Val.Vptr_has_type` -/
theorem Vptr_has_type (b : Block) (ofs : Ptrofs) : HasType (.Vptr b ofs) Tptr := by
  simp [HasType, hasType, Tptr, Archi.ptr64]

/-- `Val.Vnullptr_has_type` -/
theorem Vnullptr_has_type : HasType Vnullptr Tptr := by
  simp [HasType, hasType, Vnullptr, Tptr, Archi.ptr64]

/-- `Val.has_subtype` -/
theorem has_subtype {ty1 ty2 : ATyp} {v : Val} (hs : ATyp.subtype ty1 ty2 = true)
    (h : HasType v ty1) : HasType v ty2 := by
  cases ty1 <;> cases ty2 <;> cases v <;>
    simp_all [ATyp.subtype, HasType, hasType, Archi.ptr64]

/-- `Val.has_subtype_list` -/
theorem has_subtype_list {tyl1 tyl2 : List ATyp} {vl : List Val}
    (hs : ATyp.subtypeList tyl1 tyl2 = true) (h : HasTypeList vl tyl1) :
    HasTypeList vl tyl2 := by
  induction tyl1 generalizing tyl2 vl with
  | nil =>
    cases tyl2 with
    | nil => exact h
    | cons => simp [ATyp.subtypeList] at hs
  | cons t1 l1 ih =>
    cases tyl2 with
    | nil => simp [ATyp.subtypeList] at hs
    | cons t2 l2 =>
      cases vl with
      | nil => exact absurd h (by simp [HasTypeList])
      | cons v vs =>
        simp only [ATyp.subtypeList, Bool.and_eq_true] at hs
        exact ⟨has_subtype hs.1 h.1, ih hs.2 h.2⟩

/-- `Val.has_proj_xtype` -/
theorem has_proj_xtype {v : Val} {t : XType} (h : hasRettype v t) : HasType v t.proj := by
  revert h
  cases t <;> cases v <;> simp [hasRettype, HasType, hasType, XType.proj, Tptr, Archi.ptr64]

/-- `Val.has_inj_type` -/
theorem has_inj_type {v : Val} {t : ATyp} (h : HasType v t) : hasRettype v t.inj := by
  revert h
  cases t <;> cases v <;> simp [hasRettype, HasType, hasType, ATyp.inj, Archi.ptr64]

/-- `Val.normalize_type` -/
theorem normalize_type (v : Val) (ty : ATyp) : HasType (normalize v ty) ty := by
  cases v <;> cases ty <;> simp [normalize, HasType, hasType, Archi.ptr64]

/-- `Val.normalize_idem` -/
theorem normalize_idem {v : Val} {ty : ATyp} (h : HasType v ty) : normalize v ty = v := by
  cases v <;> cases ty <;> simp_all [normalize, HasType, hasType, Archi.ptr64]

/-- `Val.load_result_xtype` -/
theorem load_result_xtype (chunk : Chunk) (v : Val) :
    hasRettype (loadResult chunk v) chunk.xtype := by
  cases chunk <;> cases v <;>
    simp [loadResult, hasRettype, Chunk.xtype, Archi.ptr64, normBool, isBool, Vtrue, Vfalse]
  case Mbool.Vint n =>
    by_cases h : Integers.Int.zero_ext 8 n = Integers.Int.one ∨
        Integers.Int.zero_ext 8 n = Integers.Int.zero
    · rw [if_pos h]; exact h.symm
    · rw [if_neg h]; trivial
  all_goals first
    | exact (Integers.Int.sign_ext_idem (by decide) _).symm
    | exact (Integers.Int.zero_ext_idem _ _).symm

/-- `Val.load_result_type` -/
theorem load_result_type (chunk : Chunk) (v : Val) : HasType (loadResult chunk v) chunk.typ := by
  rw [← Chunk.proj_xtype]; exact has_proj_xtype (load_result_xtype chunk v)

/-- `Val.load_result_same` -/
theorem load_result_same {v : Val} {ty : ATyp} (h : HasType v ty) :
    loadResult (Chunk.ofTyp ty) v = v := by
  cases v <;> cases ty <;> simp_all [loadResult, Chunk.ofTyp, HasType, hasType, Archi.ptr64]

/-! ## Booleans -/

/-- `Val.norm_bool_cases` -/
theorem norm_bool_cases (v : Val) :
    normBool v = .Vundef ∨ normBool v = Vfalse ∨ normBool v = Vtrue := by
  unfold normBool isBool
  by_cases h1 : v = Vtrue
  · subst h1; right; right; rfl
  · by_cases h2 : v = Vfalse
    · subst h2; right; left; rfl
    · left; simp [h1, h2]

/-- `Val.bool_of_val_of_bool` -/
theorem bool_of_val_of_bool {b1 b2 : Bool} (h : BoolOfVal (ofBool b1) b2) : b1 = b2 := by
  cases b1 <;> cases h <;> rfl

/-- `Val.bool_of_val_of_optbool` -/
theorem bool_of_val_of_optbool {ob : Option Bool} {b : Bool} (h : BoolOfVal (ofOptbool ob) b) :
    ob = some b := by
  cases ob with
  | none => cases h
  | some b' => rw [bool_of_val_of_bool h]

/-- `Val.of_bool_is_bool` -/
theorem of_bool_is_bool (b : Bool) : isBool (ofBool b) = true := by cases b <;> decide

/-- `Val.norm_bool_idem` -/
theorem norm_bool_idem (v : Val) : normBool (normBool v) = normBool v := by
  rcases norm_bool_cases v with h | h | h <;> rw [h] <;> decide

/-- `Val.notbool_negb_3` -/
theorem notbool_negb_3 (ob : Option Bool) : ofOptbool (ob.map (!·)) = notbool (ofOptbool ob) :=
  ofOptbool_map_not ob

/-- `Val.not_of_optbool` -/
theorem not_of_optbool (ob : Option Bool) : ofOptbool (ob.map (!·)) = notbool (ofOptbool ob) :=
  ofOptbool_map_not ob

/-- `Val.notbool_idem3` -/
theorem notbool_idem3 (x : Val) : notbool (notbool (notbool x)) = notbool x := by
  cases x with
  | Vint n => cases h : Integers.Int.eq n Integers.Int.zero <;> simp [notbool, h] <;> decide
  | Vptr => rfl
  | _ => rfl

/-- `Val.notbool_idem4` -/
theorem notbool_idem4 (ob : Option Bool) : notbool (notbool (ofOptbool ob)) = ofOptbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> decide

/-! ## Comparisons of boolean results with 0 and 1 -/

/-- `Val.cmp_ne_0_optbool` -/
theorem cmp_ne_0_optbool (ob : Option Bool) :
    cmp .Cne (ofOptbool ob) (.Vint Integers.Int.zero) = ofOptbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> decide

/-- `Val.cmp_eq_1_optbool` -/
theorem cmp_eq_1_optbool (ob : Option Bool) :
    cmp .Ceq (ofOptbool ob) (.Vint Integers.Int.one) = ofOptbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> decide

/-- `Val.cmp_eq_0_optbool` -/
theorem cmp_eq_0_optbool (ob : Option Bool) :
    cmp .Ceq (ofOptbool ob) (.Vint Integers.Int.zero) = ofOptbool (ob.map (!·)) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> decide

/-- `Val.cmp_ne_1_optbool` -/
theorem cmp_ne_1_optbool (ob : Option Bool) :
    cmp .Cne (ofOptbool ob) (.Vint Integers.Int.one) = ofOptbool (ob.map (!·)) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> decide

/-- `Val.cmpu_ne_0_optbool` -/
theorem cmpu_ne_0_optbool (vp : Block → Z → Bool) (ob : Option Bool) :
    cmpu vp .Cne (ofOptbool ob) (.Vint Integers.Int.zero) = ofOptbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

/-- `Val.cmpu_eq_1_optbool` -/
theorem cmpu_eq_1_optbool (vp : Block → Z → Bool) (ob : Option Bool) :
    cmpu vp .Ceq (ofOptbool ob) (.Vint Integers.Int.one) = ofOptbool ob := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

/-- `Val.cmpu_eq_0_optbool` -/
theorem cmpu_eq_0_optbool (vp : Block → Z → Bool) (ob : Option Bool) :
    cmpu vp .Ceq (ofOptbool ob) (.Vint Integers.Int.zero) = ofOptbool (ob.map (!·)) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

/-- `Val.cmpu_ne_1_optbool` -/
theorem cmpu_ne_1_optbool (vp : Block → Z → Bool) (ob : Option Bool) :
    cmpu vp .Cne (ofOptbool ob) (.Vint Integers.Int.one) = ofOptbool (ob.map (!·)) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> rfl

/-! ## Float comparisons -/

/-- `Val.negate_cmpf_eq` -/
theorem negate_cmpf_eq (v1 v2 : Val) : notbool (cmpf .Cne v1 v2) = cmpf .Ceq v1 v2 := by
  cases v1 <;> cases v2 <;> try rfl
  rename_i f1 f2
  simp only [cmpf, cmpf_bool, Floats.Float.cmp_ne_eq]
  cases Floats.Float.cmp .Ceq f1 f2 <;> decide

/-- `Val.negate_cmpf_ne` -/
theorem negate_cmpf_ne (v1 v2 : Val) : notbool (cmpf .Ceq v1 v2) = cmpf .Cne v1 v2 := by
  cases v1 <;> cases v2 <;> try rfl
  rename_i f1 f2
  simp only [cmpf, cmpf_bool, Floats.Float.cmp_ne_eq]
  cases Floats.Float.cmp .Ceq f1 f2 <;> decide

/-- `Val.cmpf_le` -/
theorem cmpf_le (v1 v2 : Val) : cmpf .Cle v1 v2 = or (cmpf .Clt v1 v2) (cmpf .Ceq v1 v2) := by
  cases v1 <;> cases v2 <;> try rfl
  rename_i f1 f2
  simp only [cmpf, cmpf_bool, Floats.Float.cmp_le_lt_eq]
  cases Floats.Float.cmp .Clt f1 f2 <;> cases Floats.Float.cmp .Ceq f1 f2 <;> decide

/-- `Val.cmpf_ge` -/
theorem cmpf_ge (v1 v2 : Val) : cmpf .Cge v1 v2 = or (cmpf .Cgt v1 v2) (cmpf .Ceq v1 v2) := by
  cases v1 <;> cases v2 <;> try rfl
  rename_i f1 f2
  simp only [cmpf, cmpf_bool, Floats.Float.cmp_ge_gt_eq]
  cases Floats.Float.cmp .Cgt f1 f2 <;> cases Floats.Float.cmp .Ceq f1 f2 <;> decide

/-! ## Pointer offsets and 64-bit integers (`Archi.ptr64 = true`) -/

theorem Ptrofs_of_int64_toNat (x : Integers.Int64) : (Ptrofs.of_int64 x).toNat = x.toNat := by
  simp only [Ptrofs.of_int64, Integers.MI.repr, Integers.MI.unsigned, BitVec.toNat_ofInt,
    Archi.ptrWordsize_eq]
  have := x.isLt
  rw [Int.toNat_emod (by omega) (by decide)]
  simp only [Int.toNat_natCast]
  exact Nat.mod_eq_of_lt (by have : ((2 : Z) ^ 64).toNat = 2 ^ 64 := by decide
                             omega)

theorem Ptrofs_to_int64_toNat (x : Ptrofs) : (Ptrofs.to_int64 x).toNat = x.toNat := by
  simp only [Ptrofs.to_int64, BitVec.toNat_setWidth, Archi.ptrWordsize_eq]
  exact Nat.mod_eq_of_lt (by have := x.isLt; simpa using this)

theorem Ptrofs_of_int64_add (a b : Integers.Int64) :
    Ptrofs.of_int64 (Integers.Int64.add a b) = Ptrofs.add (Ptrofs.of_int64 a) (Ptrofs.of_int64 b) := by
  apply BitVec.eq_of_toNat_eq
  rw [Ptrofs_of_int64_toNat]
  simp only [Ptrofs.add, Integers.MI.add, Integers.Int64.add]
  rw [BitVec.toNat_add, BitVec.toNat_add, Ptrofs_of_int64_toNat, Ptrofs_of_int64_toNat]
  rfl

theorem Ptrofs_of_int64_neg (a : Integers.Int64) :
    Ptrofs.of_int64 (Integers.Int64.neg a) = Ptrofs.neg (Ptrofs.of_int64 a) := by
  apply BitVec.eq_of_toNat_eq
  rw [Ptrofs_of_int64_toNat]
  simp only [Ptrofs.neg, Integers.MI.neg, Integers.Int64.neg]
  rw [BitVec.toNat_neg, BitVec.toNat_neg, Ptrofs_of_int64_toNat]
  rfl

theorem Ptrofs_to_int64_add (x : Ptrofs) (i : Integers.Int64) :
    Ptrofs.to_int64 (Ptrofs.add x (Ptrofs.of_int64 i)) =
      Integers.Int64.add (Ptrofs.to_int64 x) i := by
  apply BitVec.eq_of_toNat_eq
  rw [Ptrofs_to_int64_toNat]
  simp only [Ptrofs.add, Integers.MI.add, Integers.Int64.add]
  rw [BitVec.toNat_add, BitVec.toNat_add, Ptrofs_of_int64_toNat, Ptrofs_to_int64_toNat]
  rfl

theorem Ptrofs_to_int64_sub (x : Ptrofs) (i : Integers.Int64) :
    Ptrofs.to_int64 (Ptrofs.sub x (Ptrofs.of_int64 i)) =
      Integers.Int64.sub (Ptrofs.to_int64 x) i := by
  apply BitVec.eq_of_toNat_eq
  rw [Ptrofs_to_int64_toNat]
  simp only [Ptrofs.sub, Integers.MI.sub, Integers.Int64.sub]
  rw [BitVec.toNat_sub, BitVec.toNat_sub, Ptrofs_of_int64_toNat, Ptrofs_to_int64_toNat]
  rfl

/-! ## Arithmetic laws (64-bit) -/

/-- `Val.addl_assoc` -/
theorem addl_assoc (x y z : Val) : addl (addl x y) z = addl x (addl y z) := by
  cases x <;> cases y <;> cases z <;>
    simp [addl, Integers.Int64.add_assoc, Archi.ptr64, Ptrofs_of_int64_add,
      Ptrofs.add_assoc, Ptrofs.add_commut, Ptrofs.add_permut]

/-- `Val.addl_permut` -/
theorem addl_permut (x y z : Val) : addl x (addl y z) = addl y (addl x z) := by
  rw [← addl_assoc, addl_commut x y, addl_assoc]

/-- `Val.addl_permut_4` -/
theorem addl_permut_4 (x y z t : Val) :
    addl (addl x y) (addl z t) = addl (addl x z) (addl y t) := by
  rw [addl_assoc, addl_permut y, ← addl_assoc]

/-- `Val.negl_addl_distr` -/
theorem negl_addl_distr (x y : Val) : negl (addl x y) = addl (negl x) (negl y) := by
  cases x <;> cases y <;> simp [addl, negl, Integers.Int64.neg_add_distr, Archi.ptr64]

/-- `Val.subl_addl_opp` -/
theorem subl_addl_opp (x : Val) (y : Integers.Int64) :
    subl x (.Vlong y) = addl x (.Vlong (Integers.Int64.neg y)) := by
  cases x <;> simp [subl, addl, Integers.Int64.sub_add_opp, Archi.ptr64, Ptrofs_of_int64_neg,
    Ptrofs.sub_add_opp]

/-- `Val.subl_opp_addl` -/
theorem subl_opp_addl (x : Val) (y : Integers.Int64) :
    subl x (.Vlong (Integers.Int64.neg y)) = addl x (.Vlong y) := by
  rw [subl_addl_opp, Integers.Int64.neg_involutive]

/-- `Val.subl_addl_l` -/
theorem subl_addl_l (v1 v2 : Val) (i : Integers.Int64) :
    subl (addl v1 (.Vlong i)) v2 = addl (subl v1 v2) (.Vlong i) := by
  cases v1 with
  | Vlong a =>
    cases v2 with
    | Vlong n => simp only [subl, addl]; rw [Integers.Int64.sub_add_l]
    | _ => rfl
  | Vptr b1 o1 =>
    cases v2 with
    | Vlong n =>
      simp only [subl, addl, Archi.ptr64, if_true]
      rw [Ptrofs.sub_add_l]
    | Vptr b2 o2 =>
      simp only [subl, addl, Archi.ptr64, if_true, Bool.not_true, Bool.false_eq_true, if_false]
      by_cases hb : b1 = b2
      · simp only [hb, if_true]
        rw [Ptrofs.sub_add_l, Ptrofs_to_int64_add]
      · simp only [hb, if_false]
    | _ => rfl
  | _ => cases v2 <;> rfl

/-- `Val.subl_addl_r` -/
theorem subl_addl_r (v1 v2 : Val) (i : Integers.Int64) :
    subl v1 (addl v2 (.Vlong i)) = addl (subl v1 v2) (.Vlong (Integers.Int64.neg i)) := by
  cases v2 with
  | Vlong n =>
    cases v1 with
    | Vlong a =>
      simp only [subl, addl]
      rw [Integers.Int64.add_commut n i, Integers.Int64.sub_add_r]
    | Vptr b o =>
      simp only [subl, addl, Archi.ptr64, if_true]
      rw [Ptrofs_of_int64_neg, Ptrofs_of_int64_add, Ptrofs.add_commut, Ptrofs.sub_add_r]
    | _ => rfl
  | Vptr b2 o2 =>
    cases v1 with
    | Vptr b1 o1 =>
      simp only [subl, addl, Archi.ptr64, if_true, Bool.not_true, Bool.false_eq_true, if_false]
      by_cases hb : b1 = b2
      · simp only [hb, if_true]
        rw [Ptrofs.add_commut, Ptrofs.sub_add_r, ← Ptrofs_of_int64_neg, Ptrofs_to_int64_add]
      · simp only [hb, if_false]
    | _ => rfl
  | _ => cases v1 <;> rfl

/-- `Val.mull_assoc` -/
theorem mull_assoc (x y z : Val) : mull (mull x y) z = mull x (mull y z) := by
  cases x <;> cases y <;> cases z <;> simp [mull, Integers.Int64.mul_assoc]

/-- `Val.mull_addl_distr_l` -/
theorem mull_addl_distr_l (x y z : Val) : mull (addl x y) z = addl (mull x z) (mull y z) := by
  cases x <;> cases y <;> cases z <;>
    simp [mull, addl, Integers.Int64.mul_add_distr_l, Archi.ptr64]

/-- `Val.mull_addl_distr_r` -/
theorem mull_addl_distr_r (x y z : Val) : mull x (addl y z) = addl (mull x y) (mull x z) := by
  cases x <;> cases y <;> cases z <;>
    simp [mull, addl, Integers.Int64.mul_add_distr_r, Archi.ptr64]

/-- `Val.andl_assoc` -/
theorem andl_assoc (x y z : Val) : andl (andl x y) z = andl x (andl y z) := by
  cases x <;> cases y <;> cases z <;> simp [andl, Integers.Int64.and_assoc]

/-- `Val.orl_assoc` -/
theorem orl_assoc (x y z : Val) : orl (orl x y) z = orl x (orl y z) := by
  cases x <;> cases y <;> cases z <;> simp [orl, Integers.Int64.or_assoc]

/-- `Val.xorl_assoc` -/
theorem xorl_assoc (x y z : Val) : xorl (xorl x y) z = xorl x (xorl y z) := by
  cases x <;> cases y <;> cases z <;> simp [xorl, Integers.Int64.xor_assoc]

/-- `Val.notl_xorl` -/
theorem notl_xorl (x : Val) : notl x = xorl x (.Vlong Integers.Int64.mone) := by
  cases x <;> simp [notl, xorl, Integers.Int64.not_eq_xor_mone]

/-! ## Division and remainder -/

/-- `Val.modls_divls` -/
theorem modls_divls {x y z : Val} (h : modls x y = some z) :
    ∃ v, divls x y = some v ∧ z = subl x (mull v y) := by
  cases x <;> cases y <;> simp only [modls, reduceCtorEq] at h
  rename_i a b
  split at h
  · cases h
  · next hc =>
    cases h
    refine ⟨.Vlong (Integers.Int64.divs a b), by simp only [divls, if_neg hc], ?_⟩
    simp [subl, mull, Integers.Int64.mods_divs]

/-- `Val.modlu_divlu` -/
theorem modlu_divlu {x y z : Val} (h : modlu x y = some z) :
    ∃ v, divlu x y = some v ∧ z = subl x (mull v y) := by
  cases x <;> cases y <;> simp only [modlu, reduceCtorEq] at h
  rename_i a b
  split at h
  · cases h
  · next hc =>
    cases h
    refine ⟨.Vlong (Integers.Int64.divu a b), by simp only [divlu, if_neg hc], ?_⟩
    simp [subl, mull, Integers.Int64.modu_divu]

/-- `is_power2 n = some logn` means `n = shl one logn`. -/
theorem Int_is_power2_shl {n logn : Integers.Int} (h : Integers.Int.is_power2 n = some logn) :
    n = Integers.Int.shl Integers.Int.one logn := by
  rw [← Integers.Int.mul_pow2 Integers.Int.one h, Integers.Int.mul_commut, Integers.Int.mul_one]

/-- `Val.mul_pow2` -/
theorem mul_pow2 (x : Val) {n logn : Integers.Int} (h : Integers.Int.is_power2 n = some logn) :
    mul x (.Vint n) = shl x (.Vint logn) := by
  cases x <;> simp only [mul, shl]
  rw [if_pos (Integers.Int.is_power2_range h), Integers.Int.mul_pow2 _ h]

/-- `Val.divs_pow2` -/
theorem divs_pow2 {x y : Val} {n logn : Integers.Int} (h : Integers.Int.is_power2 n = some logn)
    (hl : Integers.Int.ltu logn (Integers.Int.repr 31) = true) (hd : divs x (.Vint n) = some y) :
    shrx x (.Vint logn) = some y := by
  cases x <;> simp only [divs, reduceCtorEq] at hd
  split at hd
  · cases hd
  · cases hd
    simp only [shrx, if_pos hl, Integers.Int.shrx, Integers.MI.shrx]
    rw [Int_is_power2_shl h]; rfl

/-- `Val.divs_one` -/
theorem divs_one (s : Integers.Int) :
    divs (.Vint s) (.Vint Integers.Int.one) = some (.Vint s) := by
  have h1 : Integers.Int.eq Integers.Int.one Integers.Int.zero = false := by decide
  have h2 : Integers.Int.eq Integers.Int.one Integers.Int.mone = false := by decide
  simp only [divs, h1, h2, Bool.and_false, Bool.or_false, Bool.false_eq_true, if_false,
    Integers.Int.divs_one]

/-- `Val.divu_pow2` -/
theorem divu_pow2 {x y : Val} {n logn : Integers.Int} (h : Integers.Int.is_power2 n = some logn)
    (hd : divu x (.Vint n) = some y) : shru x (.Vint logn) = y := by
  cases x <;> simp only [divu, reduceCtorEq] at hd
  split at hd
  · cases hd
  · cases hd
    simp only [shru, if_pos (Integers.Int.is_power2_range h), Integers.Int.divu_pow2 _ h]

/-- `Val.modu_pow2` -/
theorem modu_pow2 {x y : Val} {n logn : Integers.Int} (h : Integers.Int.is_power2 n = some logn)
    (hd : modu x (.Vint n) = some y) : and x (.Vint (Integers.Int.sub n Integers.Int.one)) = y := by
  cases x <;> simp only [modu, reduceCtorEq] at hd
  split at hd
  · cases hd
  · cases hd
    simp only [and, Integers.Int.modu_and _ h]

/-- `Val.divls_one` -/
theorem divls_one (n : Integers.Int64) :
    divls (.Vlong n) (.Vlong Integers.Int64.one) = some (.Vlong n) := by
  have h1 : Integers.Int64.eq Integers.Int64.one Integers.Int64.zero = false := by decide
  have h2 : Integers.Int64.eq Integers.Int64.one Integers.Int64.mone = false := by decide
  simp only [divls, h1, h2, Bool.and_false, Bool.or_false, Bool.false_eq_true, if_false,
    Integers.Int64.divs_one]

/-- `Val.divlu_one` -/
theorem divlu_one (n : Integers.Int64) :
    divlu (.Vlong n) (.Vlong Integers.Int64.one) = some (.Vlong n) := by
  have h1 : Integers.Int64.eq Integers.Int64.one Integers.Int64.zero = false := by decide
  simp only [divlu, h1, Bool.false_eq_true, if_false, Integers.Int64.divu_one]

/-- `Val.divlu_pow2` -/
theorem divlu_pow2 {x y : Val} {n : Integers.Int64} {logn : Integers.Int}
    (h : Integers.Int64.is_power2' n = some logn) (hd : divlu x (.Vlong n) = some y) :
    shrlu x (.Vint logn) = y := by
  cases x <;> simp only [divlu, reduceCtorEq] at hd
  split at hd
  · cases hd
  · cases hd
    have hl := (Integers.Int64.is_power2'_spec h).1
    have hlt : Integers.Int.ltu logn (Integers.Int.repr 64) = true := by
      simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq]
      have : (Integers.Int.repr 64 : Integers.Int).toNat = 64 := by decide
      rw [this]; exact hl
    simp only [shrlu]
    split
    · rw [Integers.Int64.divu_pow2' _ h, Integers.Int64.shru'_eq]
    · next hc => exact absurd hlt hc

/-- `Val.modlu_pow2` -/
theorem modlu_pow2 {x y : Val} {n logn : Integers.Int64}
    (h : Integers.Int64.is_power2 n = some logn) (hd : modlu x (.Vlong n) = some y) :
    andl x (.Vlong (Integers.Int64.sub n Integers.Int64.one)) = y := by
  cases x <;> simp only [modlu, reduceCtorEq] at hd
  split at hd
  · cases hd
  · cases hd
    simp only [andl, Integers.Int64.modu_and _ h]

/-- `Val.divls_pow2` -/
theorem divls_pow2 {x y : Val} {n : Integers.Int64} {logn : Integers.Int}
    (h : Integers.Int64.is_power2' n = some logn)
    (hl : Integers.Int.ltu logn (Integers.Int.repr 63) = true) (hd : divls x (.Vlong n) = some y) :
    shrxl x (.Vint logn) = some y := by
  cases x <;> simp only [divls, reduceCtorEq] at hd
  split at hd
  · cases hd
  · cases hd
    simp only [shrxl, if_pos hl, Integers.Int64.shrx']
    congr 3
    rw [← Integers.Int64.mul_pow2' Integers.Int64.one h, Integers.Int64.mul_commut,
      Integers.Int64.mul_one]

/-! ## Shifts, rotations and masks -/

/-- `Val.rolml_zero` -/
theorem rolml_zero (x : Val) (m : Integers.Int64) :
    rolml x Integers.Int.zero m = andl x (.Vlong m) := by
  cases x <;> simp only [rolml, andl]
  have : (Integers.Int64.repr (Integers.Int.unsigned Integers.Int.zero) : Integers.Int64) =
      Integers.Int64.zero := by decide
  rw [this, Integers.Int64.rolm_zero]

/-- `Val.rolm_zero` -/
theorem rolm_zero (x : Val) (m : Integers.Int) : rolm x Integers.Int.zero m = and x (.Vint m) := by
  cases x <;> simp only [rolm, and, Integers.Int.rolm_zero]

/-- `Val.or_rolm` -/
theorem or_rolm (x : Val) (n m1 m2 : Integers.Int) :
    or (rolm x n m1) (rolm x n m2) = rolm x n (Integers.Int.or m1 m2) := by
  cases x <;> simp only [rolm, or, Integers.Int.or_rolm]

/-- `Val.rolm_rolm` -/
theorem rolm_rolm (x : Val) (n1 m1 n2 m2 : Integers.Int) :
    rolm (rolm x n1 m1) n2 m2 =
      rolm x (Integers.Int.modu (Integers.Int.add n1 n2) Integers.Int.iwordsize)
        (Integers.Int.and (Integers.Int.rol m1 n2) m2) := by
  cases x <;> simp only [rolm, Integers.Int.rolm_rolm]

/-- `Val.cast8unsigned_and` -/
theorem cast8unsigned_and (x : Val) :
    zeroExt 8 x = and x (.Vint (Integers.Int.repr 255)) := by
  cases x <;> simp only [zeroExt, and]
  rw [Integers.Int.zero_ext_and]; rfl

/-- `Val.cast16unsigned_and` -/
theorem cast16unsigned_and (x : Val) :
    zeroExt 16 x = and x (.Vint (Integers.Int.repr 65535)) := by
  cases x <;> simp only [zeroExt, and]
  rw [Integers.Int.zero_ext_and]; rfl

/-- `Val.zero_ext_andl` -/
theorem zero_ext_andl (n : Nat) (v : Val) :
    zero_ext_l n v = andl v (.Vlong (Integers.Int64.repr ((2 : Z) ^ n - 1))) := by
  cases v <;> simp only [zero_ext_l, andl, Integers.Int64.zero_ext_and]

/-- `Val.shl_rolm` -/
theorem shl_rolm (x : Val) {n : Integers.Int} (h : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    shl x (.Vint n) = rolm x n (Integers.Int.shl Integers.Int.mone n) := by
  cases x with
  | Vint a => simp only [shl, rolm, if_pos h]; rw [Integers.Int.shl_rolm _ _ h]
  | _ => rfl

/-- `Val.shru_rolm` -/
theorem shru_rolm (x : Val) {n : Integers.Int} (h : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    shru x (.Vint n) =
      rolm x (Integers.Int.sub Integers.Int.iwordsize n) (Integers.Int.shru Integers.Int.mone n) := by
  cases x with
  | Vint a => simp only [shru, rolm, if_pos h]; rw [Integers.Int.shru_rolm _ _ h]
  | _ => rfl

theorem Int_ltu64_toNat {n : Integers.Int} (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    n.toNat < 64 := by
  have h64 : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq, h64] at h
  exact h

theorem Int64_ltu_repr_unsigned {n : Integers.Int} (h : n.toNat < 64) :
    Integers.Int64.ltu (Integers.Int64.repr (Integers.Int.unsigned n)) Integers.Int64.iwordsize = true := by
  simp only [Integers.Int64.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq,
    Integers.Int64.toNat_repr_unsigned]
  have : (Integers.Int64.iwordsize : Integers.Int64).toNat = 64 := by decide
  rw [this]; exact h

/-- `Val.shll_rolml` -/
theorem shll_rolml (x : Val) {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    shll x (.Vint n) =
      rolml x n (Integers.Int64.shl Integers.Int64.mone (Integers.Int64.repr (Integers.Int.unsigned n))) := by
  cases x <;> simp only [shll, rolml]
  split
  · rw [Integers.Int64.shl_rolm _ _ (Int64_ltu_repr_unsigned (Int_ltu64_toNat h))]
  · next hc => exact absurd h hc

theorem Int64_repr_unsigned_sub64 {n : Integers.Int} (h : n.toNat < 64) :
    (Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.sub Integers.Int64.iwordsize' n)) :
      Integers.Int64) =
      Integers.Int64.sub Integers.Int64.iwordsize (Integers.Int64.repr (Integers.Int.unsigned n)) := by
  have h64 : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [Integers.Int64.toNat_repr_unsigned]
  simp only [Integers.Int.sub, Integers.MI.sub, Integers.Int64.sub]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h64]; omega), h64,
    BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, Integers.Int64.toNat_repr_unsigned]
      have : (Integers.Int64.iwordsize : Integers.Int64).toNat = 64 := by decide
      rw [this]; omega),
    Integers.Int64.toNat_repr_unsigned]
  have : (Integers.Int64.iwordsize : Integers.Int64).toNat = 64 := by decide
  rw [this]

/-- `Val.shrlu_rolml` -/
theorem shrlu_rolml (x : Val) {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    shrlu x (.Vint n) =
      rolml x (Integers.Int.sub Integers.Int64.iwordsize' n)
        (Integers.Int64.shru Integers.Int64.mone (Integers.Int64.repr (Integers.Int.unsigned n))) := by
  cases x <;> simp only [shrlu, rolml]
  split
  · rw [Integers.Int64.shru_rolm _ _ (Int64_ltu_repr_unsigned (Int_ltu64_toNat h)),
      Int64_repr_unsigned_sub64 (Int_ltu64_toNat h)]
  · next hc => exact absurd h hc

theorem Int_ltu31_iwordsize {q : Integers.Int} (h : Integers.Int.ltu q (Integers.Int.repr 31) = true) :
    Integers.Int.ltu q Integers.Int.iwordsize = true := by
  have h31 : (Integers.Int.repr 31 : Integers.Int).toNat = 31 := by decide
  have h32 : (Integers.Int.iwordsize : Integers.Int).toNat = 32 := by decide
  simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq, h31, h32] at h ⊢
  omega

/-- `Val.shrx_carry` -/
theorem shrx_carry {x y z : Val} (h : shrx x y = some z) :
    add (shr x y) (shr_carry x y) = z := by
  cases x <;> cases y <;> simp only [shrx, reduceCtorEq] at h
  rename_i p q
  split at h
  · next hl =>
    cases h
    simp only [shr, shr_carry, if_pos (Int_ltu31_iwordsize hl), add]
    rw [Integers.Int.shrx_carry p q hl]
  · cases h

/-- `Val.shrx_shr` -/
theorem shrx_shr {x y z : Val} (h : shrx x y = some z) :
    ∃ p q, x = .Vint p ∧ y = .Vint q ∧
      z = shr (if Integers.Int.lt p Integers.Int.zero then
                add x (.Vint (Integers.Int.sub (Integers.Int.shl Integers.Int.one q) Integers.Int.one))
               else x) (.Vint q) := by
  cases x <;> cases y <;> simp only [shrx, reduceCtorEq] at h
  rename_i p q
  split at h
  · next hl =>
    cases h
    refine ⟨p, q, rfl, rfl, ?_⟩
    rw [Integers.Int.shrx_shr p q hl]
    split <;> simp only [add, shr, if_pos (Int_ltu31_iwordsize hl)]
  · cases h

/-- `Val.shrx_shr_2` -/
theorem shrx_shr_2 {n : Integers.Int} {x z : Val} (h : shrx x (.Vint n) = some z) :
    z = if Integers.Int.eq n Integers.Int.zero then x else
      shr (add x (shru (shr x (.Vint (Integers.Int.repr 31)))
                       (.Vint (Integers.Int.sub (Integers.Int.repr 32) n))))
          (.Vint n) := by
  cases x <;> simp only [shrx, reduceCtorEq] at h
  rename_i p
  split at h
  · next hl =>
    cases h
    by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
    · rw [if_pos h0, Integers.Int.same_if_eq h0, Integers.Int.shrx_zero]
    · rw [if_neg h0]
      have hn0 : n.toNat ≠ 0 := by
        intro hz; apply h0
        rw [Integers.Int.eq_spec]; exact BitVec.eq_of_toNat_eq (by rw [hz]; rfl)
      have h31 : (Integers.Int.repr 31 : Integers.Int).toNat = 31 := by decide
      have h32 : (Integers.Int.repr 32 : Integers.Int).toNat = 32 := by decide
      have hw : (Integers.Int.iwordsize : Integers.Int).toNat = 32 := by decide
      have hn : n.toNat < 31 := by
        simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq, h31] at hl
        exact hl
      have hr31 : Integers.Int.ltu (Integers.Int.repr 31) Integers.Int.iwordsize = true := by decide
      have hsub : Integers.Int.ltu (Integers.Int.sub (Integers.Int.repr 32) n)
          Integers.Int.iwordsize = true := by
        simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq, hw,
          Integers.Int.sub, Integers.MI.sub]
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h32]; omega), h32]; omega
      simp only [shr, shru, add, if_pos hr31, if_pos hsub, if_pos (Int_ltu31_iwordsize hl)]
      rw [Integers.Int.shrx_shr_2 p n hl]
      rfl
  · cases h

/-- `Val.shrxl_carry` -/
theorem shrxl_carry {x y z : Val} (h : shrxl x y = some z) :
    addl (shrl x y) (shrl_carry x y) = z := by
  cases x <;> cases y <;> simp only [shrxl, reduceCtorEq] at h
  rename_i p q
  split at h
  · next hl =>
    cases h
    have hq : Integers.Int.ltu q Integers.Int64.iwordsize' = true := by
      have := Integers.Int64.ltu63_toNat hl
      have h64 : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
      simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq, h64]; omega
    simp only [shrl, shrl_carry, if_pos hq]
    split
    · simp only [addl]
      rw [Integers.Int64.shrx'_carry p q hl, Integers.Int64.shr'_eq]
    · next hc => exact absurd hq hc
  · cases h

/-- `Val.shrxl_shrl_2` -/
theorem shrxl_shrl_2 {n : Integers.Int} {x z : Val} (h : shrxl x (.Vint n) = some z) :
    z = if Integers.Int.eq n Integers.Int.zero then x else
      shrl (addl x (shrlu (shrl x (.Vint (Integers.Int.repr 63)))
                          (.Vint (Integers.Int.sub (Integers.Int.repr 64) n))))
           (.Vint n) := by
  cases x <;> simp only [shrxl, reduceCtorEq] at h
  rename_i p
  split at h
  · next hl =>
    cases h
    have hn := Integers.Int64.ltu63_toNat hl
    by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
    · rw [if_pos h0, Integers.Int.same_if_eq h0, Integers.Int64.shrx'_eq]
      have : (Integers.Int64.repr (Integers.Int.unsigned Integers.Int.zero) : Integers.Int64) =
          Integers.Int64.zero := by decide
      rw [this]
      exact congrArg Val.Vlong (Integers.MI.shrx_zero p)
    · rw [if_neg h0]
      have hn0 : n.toNat ≠ 0 := by
        intro hz; apply h0
        rw [Integers.Int.eq_spec]; exact BitVec.eq_of_toNat_eq (by rw [hz]; rfl)
      have h64 : (Integers.Int.repr 64 : Integers.Int).toNat = 64 := by decide
      have hlt : ∀ m : Integers.Int, m.toNat < 64 → Integers.Int.ltu m (Integers.Int.repr 64) = true := by
        intro m hm
        simp only [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult, decide_eq_true_eq, h64]; exact hm
      have hsub : (Integers.Int.sub (Integers.Int.repr 64) n).toNat < 64 := by
        simp only [Integers.Int.sub, Integers.MI.sub]
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h64]; omega), h64]; omega
      have h63 : (Integers.Int.repr 63 : Integers.Int).toNat < 64 := by decide
      have e1 : shrl (.Vlong p) (.Vint (Integers.Int.repr 63)) =
          .Vlong (Integers.Int64.shr p (Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.repr 63)))) := by
        simp only [shrl]; exact if_pos (hlt _ h63)
      have e2 : ∀ q : Integers.Int64, shrlu (.Vlong q) (.Vint (Integers.Int.sub (Integers.Int.repr 64) n)) =
          .Vlong (Integers.Int64.shru q (Integers.Int64.repr
            (Integers.Int.unsigned (Integers.Int.sub (Integers.Int.repr 64) n)))) := by
        intro q; simp only [shrlu]; exact if_pos (hlt _ hsub)
      have e3 : ∀ q : Integers.Int64, shrl (.Vlong q) (.Vint n) =
          .Vlong (Integers.Int64.shr q (Integers.Int64.repr (Integers.Int.unsigned n))) := by
        intro q; simp only [shrl]; exact if_pos (hlt _ (by omega))
      rw [e1, e2]
      simp only [addl]
      rw [e3, Integers.Int64.shrx'_shr_2 p n hl, Integers.Int64.shr'_eq, Integers.Int64.shru'_eq,
        Integers.Int64.shr'_eq]
  · cases h

/-- `rolm x 1 1` extracts the sign bit. -/
theorem Int_rolm_one_one (n : Integers.Int) :
    Integers.Int.rolm n Integers.Int.one Integers.Int.one =
      if Integers.Int.lt n Integers.Int.zero then Integers.Int.one else Integers.Int.zero := by
  have hmsb : Integers.Int.lt n Integers.Int.zero = n.msb := by
    simp only [Integers.Int.lt, Integers.Int.zero]
    rw [Integers.MI.lt_def, BitVec.msb_eq_toInt, Integers.MI.signed_zero, Integers.MI.signed]
  rw [hmsb]
  apply Integers.MI.same_bits_eq
  intro i hi
  simp only [Integers.Int.rolm, Integers.MI.rolm, Integers.MI.bits_and]
  rw [Integers.MI.testbit_rol _ _ hi]
  have h1 : (Integers.Int.one : Integers.Int).toNat = 1 := by decide
  rw [h1]
  by_cases hi0 : i = 0
  · subst hi0
    cases hm : n.msb
    · simp [Integers.MI.testbit, Integers.Int.one, Integers.MI.one, Integers.Int.zero,
        Integers.MI.zero, BitVec.msb_eq_getLsbD_last] at hm ⊢; exact hm
    · simp [Integers.MI.testbit, Integers.Int.one, Integers.MI.one,
        BitVec.msb_eq_getLsbD_last] at hm ⊢; exact hm
  · split <;> simp [Integers.MI.testbit, Integers.Int.one, Integers.MI.one, Integers.Int.zero,
      Integers.MI.zero, hi0]

/-- `Val.rolm_lt_zero` -/
theorem rolm_lt_zero (v : Val) :
    rolm v Integers.Int.one Integers.Int.one = cmp .Clt v (.Vint Integers.Int.zero) := by
  cases v <;> try rfl
  rename_i n
  simp only [rolm, cmp, cmp_bool, ofOptbool, Integers.Int.cmp, Integers.MI.cmp, Int_rolm_one_one,
    Integers.Int.lt]
  by_cases hb : Integers.MI.lt n Integers.Int.zero = true
  · rw [if_pos hb, hb]; rfl
  · rw [if_neg hb, Bool.eq_false_iff.mpr hb]; rfl

/-- `Val.rolm_ge_zero` -/
theorem rolm_ge_zero (v : Val) :
    xor (rolm v Integers.Int.one Integers.Int.one) (.Vint Integers.Int.one) =
      cmp .Cge v (.Vint Integers.Int.zero) := by
  cases v <;> try rfl
  rename_i n
  simp only [rolm, xor, cmp, cmp_bool, ofOptbool, Integers.Int.cmp, Integers.MI.cmp, Int_rolm_one_one,
    Integers.Int.lt]
  by_cases hb : Integers.MI.lt n Integers.Int.zero = true
  · rw [if_pos hb, hb]; rfl
  · rw [if_neg hb, Bool.eq_false_iff.mpr hb]; rfl

end Val
end CC
