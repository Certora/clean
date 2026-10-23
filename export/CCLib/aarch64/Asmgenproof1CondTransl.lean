/-
  Correctness of the AArch64 code generator's constructor functions,
  part 4 — port of the "Translation of conditionals" section of
  `aarch64/Asmgenproof1.v`: `transl_cond_correct`,
  `transl_cond_branch_default_correct`, `transl_cond_branch_correct`.
-/
import CCLib.aarch64.Asmgenproof1Cond

namespace CC
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1

/-- Inversion of a successful `Res` bind (`Errors.bind_inversion`). -/
theorem res_bind_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

theorem res_pure_OK {A : Type} {a b : A} : (pure a : Res A) = .OK b ↔ a = b := by
  simp [pure]

theorem compareInt_data (rs : Regset) (v1 v2 : Val) (m : Mem) {r : Preg} (h : dataPreg r = true) :
    nextinstr (compareInt rs v1 v2 m) r = rs r := by
  cases r <;> simp_all [dataPreg, nextinstr, compareInt, Regset.set]

theorem compareLong_data (rs : Regset) (v1 v2 : Val) (m : Mem) {r : Preg} (h : dataPreg r = true) :
    nextinstr (compareLong rs v1 v2 m) r = rs r := by
  cases r <;> simp_all [dataPreg, nextinstr, compareLong, Regset.set]

theorem compareFloat_data (rs : Regset) (v1 v2 : Val) {r : Preg} (h : dataPreg r = true) :
    nextinstr (compareFloat rs v1 v2) r = rs r := by
  rw [compare_float_inv _ _ _ _ (by intro c e; subst e; simp [dataPreg] at h)]
  cases r <;> simp_all [dataPreg, nextinstr, Regset.set]

theorem compareSingle_data (rs : Regset) (v1 v2 : Val) {r : Preg} (h : dataPreg r = true) :
    nextinstr (compareSingle rs v1 v2) r = rs r := by
  rw [compare_single_inv _ _ _ _ (by intro c e; subst e; simp [dataPreg] at h)]
  cases r <;> simp_all [dataPreg, nextinstr, Regset.set]

theorem compareInt_PC (rs : Regset) (v1 v2 : Val) (m : Mem) :
    nextinstr (compareInt rs v1 v2 m) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  simp [nextinstr, compareInt, Regset.set]

theorem compareLong_PC (rs : Regset) (v1 v2 : Val) (m : Mem) :
    nextinstr (compareLong rs v1 v2 m) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  simp [nextinstr, compareLong, Regset.set]

theorem compareFloat_PC (rs : Regset) (v1 v2 : Val) :
    nextinstr (compareFloat rs v1 v2) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [compare_float_inv _ _ _ _ (by intro c e; cases e)]; simp [nextinstr, Regset.set]

theorem compareSingle_PC (rs : Regset) (v1 v2 : Val) :
    nextinstr (compareSingle rs v1 v2) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [compare_single_inv _ _ _ _ (by intro c e; cases e)]; simp [nextinstr, Regset.set]

theorem evalTestcond_nextinstr (c : Testcond) (rs : Regset) :
    evalTestcond c (nextinstr rs) = evalTestcond c rs := by
  cases c <;> simp [evalTestcond, nextinstr, Regset.set]

section CONSTRUCTORS
variable (sym : SymbolSplit) (ge : Asm.CGenv) (fn : Asm.Function)

/-- Common final step of `transl_cond_correct`: an optional prefix that
    preserves the data registers, followed by one flag-setting instruction. -/
theorem cond_step {c1 : Code} {i : Instruction} {k : Code} {rs rs1 rs2 : Regset} {m : Mem}
    {tc : Testcond} {P : Option Bool}
    (hA : ExecStraightOpt sym ge fn c1 rs m (i :: k) rs1 m)
    (hpres : ∀ r, dataPreg r = true → rs1 r = rs r)
    (hi : execInstr sym ge fn i rs1 m = .Next rs2 m)
    (hpc : rs2 .PC = Val.offsetPtr (rs1 .PC) Integers.Ptrofs.one)
    (hdata : ∀ r, dataPreg r = true → rs2 r = rs1 r)
    (ht : ∀ b, P = some b → evalTestcond tc rs2 = some b) :
    ∃ rs', ExecStraight sym ge fn c1 rs m k rs' m ∧ (∀ b, P = some b → evalTestcond tc rs' = some b) ∧
      ∀ r, dataPreg r = true → rs' r = rs r :=
  ⟨rs2, exec_straight_opt_right hA (.one _ _ _ _ _ _ hi hpc), ht,
    fun r hr => (hdata r hr).trans (hpres r hr)⟩

/-- `Asmgenproof1.transl_cond_correct` -/
theorem transl_cond_correct (cond : Op.Condition) (args : List Mreg) (k c : Code) (rs : Regset)
    (m : Mem) (h : translCond cond args k = .OK c) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧
      (∀ b, Op.evalCondition cond ((args.map pregOf).map rs) m = some b →
        evalTestcond (condForCond cond) rs' = some b) ∧
      ∀ r, dataPreg r = true → rs' r = rs r := by
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translCond, res_bind_OK, res_pure_OK] at h <;> (try cases h) <;>
    rename_i r1 h <;> obtain ⟨h1, h⟩ := h
  -- Ccomp
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
      (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_sint _ _ _ _ _ _ hb
  -- Ccompu
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
      (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_uint _ _ _ _ _ _ hb
  -- Ccompimm
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
        (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_sint _ _ _ _ _ _ hb
    · split at h
      · subst h
        refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
          (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr, Integers.Int.repr_unsigned, Integers.Int.neg_involutive]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_sint _ _ _ _ _ _ hb
      · subst h
        rename_i n _ _
        obtain ⟨rs1, A, B, C⟩ := exec_loadimm32 sym ge fn .X16 n _ rs m
        refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
          (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareInt_PC _ _ _ _)
          (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr]
        simp only [ir0w, evalShiftOpInt]
        rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_sint _ _ _ _ _ _ hb
  -- Ccompuimm
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
        (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_uint _ _ _ _ _ _ hb
    · split at h
      · subst h
        refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
          (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr, Integers.Int.repr_unsigned, Integers.Int.neg_involutive]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_uint _ _ _ _ _ _ hb
      · subst h
        rename_i n _ _
        obtain ⟨rs1, A, B, C⟩ := exec_loadimm32 sym ge fn .X16 n _ rs m
        refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
          (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareInt_PC _ _ _ _)
          (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr]
        simp only [ir0w, evalShiftOpInt]
        rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_uint _ _ _ _ _ _ hb
  -- Ccompshift
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
      (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr, transl_eval_shift]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_sint _ _ _ _ _ _ hb
  -- Ccompushift
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
      (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr, transl_eval_shift]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_uint _ _ _ _ _ _ hb
  -- Cmaskzero
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
        (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_sint .Ceq _ _ _ _ _ hb
    · subst h
      rename_i n _
      obtain ⟨rs1, A, B, C⟩ := exec_loadimm32 sym ge fn .X16 n _ rs m
      refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
        (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareInt_PC _ _ _ _)
        (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr]
      simp only [ir0w, evalShiftOpInt]
      rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_sint .Ceq _ _ _ _ _ hb
  -- Cmasknotzero
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareInt_PC _ _ _ _)
        (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_sint .Cne _ _ _ _ _ hb
    · subst h
      rename_i n _
      obtain ⟨rs1, A, B, C⟩ := exec_loadimm32 sym ge fn .X16 n _ rs m
      refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
        (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareInt_PC _ _ _ _)
        (fun _ hr => compareInt_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr]
      simp only [ir0w, evalShiftOpInt]
      rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_sint .Cne _ _ _ _ _ hb
  -- Ccompl
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
      (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_slong _ _ _ _ _ _ hb
  -- Ccomplu
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
      (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_ulong _ _ _ _ _ _ hb
  -- Ccomplimm
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
        (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int64.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_slong _ _ _ _ _ _ hb
    · split at h
      · subst h
        refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
          (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr, Integers.Int64.repr_unsigned, Integers.Int64.neg_involutive]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_slong _ _ _ _ _ _ hb
      · subst h
        rename_i n _ _
        obtain ⟨rs1, A, B, C⟩ := exec_loadimm64 sym ge fn .X16 n _ rs m
        refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
          (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareLong_PC _ _ _ _)
          (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr]
        simp only [ir0x, evalShiftOpLong]
        rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_slong _ _ _ _ _ _ hb
  -- Ccompluimm
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
        (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int64.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_ulong _ _ _ _ _ _ hb
    · split at h
      · subst h
        refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
          (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr, Integers.Int64.repr_unsigned, Integers.Int64.neg_involutive]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_ulong _ _ _ _ _ _ hb
      · subst h
        rename_i n _ _
        obtain ⟨rs1, A, B, C⟩ := exec_loadimm64 sym ge fn .X16 n _ rs m
        refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
          (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareLong_PC _ _ _ _)
          (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
        rw [evalTestcond_nextinstr]
        simp only [ir0x, evalShiftOpLong]
        rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
        simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
        exact eval_testcond_compare_ulong _ _ _ _ _ _ hb
  -- Ccomplshift
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
      (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr, transl_eval_shiftl]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_slong _ _ _ _ _ _ hb
  -- Ccomplushift
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
      (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr, transl_eval_shiftl]
    simp only [List.map, ireg_of_eq h1, ireg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_ulong _ _ _ _ _ _ hb
  -- Cmasklzero
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
        (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int64.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_slong .Ceq _ _ _ _ _ hb
    · subst h
      rename_i n _
      obtain ⟨rs1, A, B, C⟩ := exec_loadimm64 sym ge fn .X16 n _ rs m
      refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
        (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareLong_PC _ _ _ _)
        (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr]
      simp only [ir0x, evalShiftOpLong]
      rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_slong .Ceq _ _ _ _ _ hb
  -- Cmasklnotzero
  · split at h
    · subst h
      refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareLong_PC _ _ _ _)
        (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr, Integers.Int64.repr_unsigned]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_slong .Cne _ _ _ _ _ hb
    · subst h
      rename_i n _
      obtain ⟨rs1, A, B, C⟩ := exec_loadimm64 sym ge fn .X16 n _ rs m
      refine cond_step sym ge fn (.intro _ _ _ _ _ _ A)
        (fun r hr => C r (dataPreg_ne_PC hr) (dataPreg_ne_X16 hr)) rfl (compareLong_PC _ _ _ _)
        (fun _ hr => compareLong_data _ _ _ _ hr) fun b hb => ?_
      rw [evalTestcond_nextinstr]
      simp only [ir0x, evalShiftOpLong]
      rw [B, C _ (by simp) (ireg_of_not_X16' h1)]
      simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hb
      exact eval_testcond_compare_slong .Cne _ _ _ _ _ hb
  -- Ccompf
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareFloat_PC _ _ _)
      (fun _ hr => compareFloat_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, freg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_float _ _ _ _ _ hb
  -- Cnotcompf
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareFloat_PC _ _ _)
      (fun _ hr => compareFloat_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, freg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_not_float _ _ _ _ _ hb
  -- Ccompfzero
  · subst h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareFloat_PC _ _ _)
      (fun _ hr => compareFloat_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, Op.evalCondition] at hb
    exact eval_testcond_compare_float _ _ _ _ _ hb
  -- Cnotcompfzero
  · subst h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareFloat_PC _ _ _)
      (fun _ hr => compareFloat_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, Op.evalCondition] at hb
    exact eval_testcond_compare_not_float _ _ _ _ _ hb
  -- Ccompfs
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareSingle_PC _ _ _)
      (fun _ hr => compareSingle_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, freg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_single _ _ _ _ _ hb
  -- Cnotcompfs
  · obtain ⟨r2, h2, rfl⟩ := h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareSingle_PC _ _ _)
      (fun _ hr => compareSingle_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, freg_of_eq h2, Op.evalCondition] at hb
    exact eval_testcond_compare_not_single _ _ _ _ _ hb
  -- Ccompfszero
  · subst h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareSingle_PC _ _ _)
      (fun _ hr => compareSingle_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, Op.evalCondition] at hb
    exact eval_testcond_compare_single _ _ _ _ _ hb
  -- Cnotcompfszero
  · subst h
    refine cond_step sym ge fn (.refl _ _ _) (fun _ _ => rfl) rfl (compareSingle_PC _ _ _)
      (fun _ hr => compareSingle_data _ _ _ hr) fun b hb => ?_
    rw [evalTestcond_nextinstr]
    simp only [List.map, freg_of_eq h1, Op.evalCondition] at hb
    exact eval_testcond_compare_not_single _ _ _ _ _ hb

theorem exec_Pcbz (sz : Isize) (r : Ireg) (lbl : Label) (rs : Regset) (m : Mem) :
    execInstr sym ge fn (.Pcbz sz r lbl) rs m =
      match evalTestzero sz (rs r) m with
      | some true => gotoLabel fn lbl rs m
      | some false => .Next (nextinstr rs) m
      | none => .Stuck := rfl

theorem exec_Pcbnz (sz : Isize) (r : Ireg) (lbl : Label) (rs : Regset) (m : Mem) :
    execInstr sym ge fn (.Pcbnz sz r lbl) rs m =
      match evalTestzero sz (rs r) m with
      | some true => .Next (nextinstr rs) m
      | some false => gotoLabel fn lbl rs m
      | none => .Stuck := rfl

theorem exec_Ptbz (sz : Isize) (r : Ireg) (n : Integers.Int) (lbl : Label) (rs : Regset) (m : Mem) :
    execInstr sym ge fn (.Ptbz sz r n lbl) rs m =
      match evalTestbit sz (rs r) n with
      | some true => .Next (nextinstr rs) m
      | some false => gotoLabel fn lbl rs m
      | none => .Stuck := rfl

theorem exec_Ptbnz (sz : Isize) (r : Ireg) (n : Integers.Int) (lbl : Label) (rs : Regset) (m : Mem) :
    execInstr sym ge fn (.Ptbnz sz r n lbl) rs m =
      match evalTestbit sz (rs r) n with
      | some true => gotoLabel fn lbl rs m
      | some false => .Next (nextinstr rs) m
      | none => .Stuck := rfl

/-- `Asmgenproof1.transl_cond_branch_default_correct` -/
theorem transl_cond_branch_default_correct (cond : Op.Condition) (args : List Mreg) (lbl : Label)
    (k c : Code) (rs : Regset) (m : Mem) (b : Bool)
    (h : translCondBranchDefault cond args lbl k = .OK c)
    (hev : Op.evalCondition cond ((args.map pregOf).map rs) m = some b) :
    ∃ rs' insn, ExecStraightOpt sym ge fn c rs m (insn :: k) rs' m ∧
      execInstr sym ge fn insn rs' m =
        (if b then gotoLabel fn lbl rs' m else .Next (nextinstr rs') m) ∧
      ∀ r, dataPreg r = true → rs' r = rs r := by
  obtain ⟨rs', A, B, C⟩ := transl_cond_correct sym ge fn cond args _ c rs m h
  refine ⟨rs', .Pbc (condForCond cond) lbl, .intro _ _ _ _ _ _ A, ?_, C⟩
  show (match evalTestcond (condForCond cond) rs' with
    | some true => gotoLabel fn lbl rs' m
    | some false => .Next (nextinstr rs') m
    | none => .Stuck) = _
  rw [B b hev]; cases b <;> rfl

/-- `Asmgenproof1.transl_cond_branch_correct` -/
theorem transl_cond_branch_correct (cond : Op.Condition) (args : List Mreg) (lbl : Label)
    (k c : Code) (rs : Regset) (m : Mem) (b : Bool)
    (h : translCondBranch cond args lbl k = .OK c)
    (hev : Op.evalCondition cond ((args.map pregOf).map rs) m = some b) :
    ∃ rs' insn, ExecStraightOpt sym ge fn c rs m (insn :: k) rs' m ∧
      execInstr sym ge fn insn rs' m =
        (if b then gotoLabel fn lbl rs' m else .Next (nextinstr rs') m) ∧
      ∀ r, dataPreg r = true → rs' r = rs r := by
  have DFL := fun h => transl_cond_branch_default_correct sym ge fn cond args lbl k c rs m b h hev
  rcases args with _ | ⟨a1, _ | ⟨a2, args⟩⟩
  · exact DFL (by simpa [translCondBranch] using h)
  · cases cond <;> (try (rename_i cmp _; cases cmp)) <;> simp only [translCondBranch] at h <;>
      (try exact DFL h)
    all_goals split at h
    all_goals (try exact DFL h)
    all_goals simp only [res_bind_OK, res_pure_OK] at h
    all_goals obtain ⟨r1, h1, rfl⟩ := h
    all_goals refine ⟨rs, _, .refl _ _ _, ?_, fun _ _ => rfl⟩
    all_goals simp only [List.map, ireg_of_eq h1, Op.evalCondition] at hev
    all_goals simp only [exec_Pcbz, exec_Pcbnz, exec_Ptbz, exec_Ptbnz, evalTestzero, evalTestbit]
    · rename_i n hn
      obtain rfl := Integers.Int.same_if_eq hn
      cases hv : rs (.IR r1) <;> simp only [hv, Val.cmp_bool, reduceCtorEq, Option.some.injEq] at hev
      subst hev
      simp only [Val.cmpu_bool, int_cmp_unfold]
      cases Integers.Int.eq _ _ <;> rfl
    · rename_i n hn
      obtain rfl := Integers.Int.same_if_eq hn
      cases hv : rs (.IR r1) <;> simp only [hv, Val.cmp_bool, reduceCtorEq, Option.some.injEq] at hev
      subst hev
      simp only [Val.cmpu_bool, int_cmp_unfold]
      cases Integers.Int.eq _ _ <;> rfl
    · rename_i n hn
      obtain rfl := Integers.Int.same_if_eq hn
      rw [hev]
      cases b <;> rfl
    · rename_i n hn
      obtain rfl := Integers.Int.same_if_eq hn
      rw [show Comparison.Ceq = Comparison.Cne.negate from rfl, Val.negate_cmpu_bool, hev]
      cases b <;> rfl
    · rename_i n _ bit hp
      have hb : Integers.Int.shl Integers.Int.one bit = n := by
        rw [← Integers.Int.mul_pow2 _ hp, Integers.Int.mul_commut, Integers.Int.mul_one]
      rw [hb, show Comparison.Cne = Comparison.Ceq.negate from rfl, Val.negate_cmp_bool, hev]
      cases b <;> rfl
    · rename_i n _ bit hp
      have hb : Integers.Int.shl Integers.Int.one bit = n := by
        rw [← Integers.Int.mul_pow2 _ hp, Integers.Int.mul_commut, Integers.Int.mul_one]
      rw [hb, hev]
      cases b <;> rfl
    · rename_i n hn
      obtain rfl := Integers.Int64.same_if_eq hn
      cases hv : rs (.IR r1) <;> simp only [hv, Val.cmpl_bool, reduceCtorEq, Option.some.injEq] at hev
      subst hev
      simp only [Val.cmplu_bool, int64_cmp_unfold]
      cases Integers.Int64.eq _ _ <;> rfl
    · rename_i n hn
      obtain rfl := Integers.Int64.same_if_eq hn
      cases hv : rs (.IR r1) <;> simp only [hv, Val.cmpl_bool, reduceCtorEq, Option.some.injEq] at hev
      subst hev
      simp only [Val.cmplu_bool, int64_cmp_unfold]
      cases Integers.Int64.eq _ _ <;> rfl
    · rename_i n hn
      obtain rfl := Integers.Int64.same_if_eq hn
      rw [hev]
      cases b <;> rfl
    · rename_i n hn
      obtain rfl := Integers.Int64.same_if_eq hn
      rw [show Comparison.Ceq = Comparison.Cne.negate from rfl, Val.negate_cmplu_bool, hev]
      cases b <;> rfl
    · rename_i n _ bit hp
      have hb : Integers.Int64.shl' Integers.Int64.one bit = n := by
        rw [← Integers.Int64.mul_pow2' _ hp, Integers.Int64.mul_commut, Integers.Int64.mul_one]
      rw [hb, show Comparison.Cne = Comparison.Ceq.negate from rfl, Val.negate_cmpl_bool, hev]
      cases b <;> rfl
    · rename_i n _ bit hp
      have hb : Integers.Int64.shl' Integers.Int64.one bit = n := by
        rw [← Integers.Int64.mul_pow2' _ hp, Integers.Int64.mul_commut, Integers.Int64.mul_one]
      rw [hb, hev]
      cases b <;> rfl
  · exact DFL (by simpa [translCondBranch] using h)

end CONSTRUCTORS

end Asmgenproof1
end CC
