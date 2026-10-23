/-
  Correctness of the AArch64 code generator's constructor functions,
  part 5 — port of the "Translation of arithmetic operations" section of
  `aarch64/Asmgenproof1.v`: `transl_op_correct`.
-/
import CCLib.aarch64.Asmgenproof1CondTransl
import CCLib.lib.IntegersExtMin
import CCLib.lib.IntegersShiftsExtra

namespace CC
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1

/-! ### Inversion of the argument-shape helpers of `transl_op` -/

theorem ii1_inv {res a1 : Mreg} {f : Ireg → Ireg → Code} {c : Code} (h : ii1 res a1 f = .OK c) :
    ∃ rd r1, pregOf res = .IR rd ∧ pregOf a1 = .IR r1 ∧ c = f rd r1 := by
  simp only [ii1, res_bind_OK, res_pure_OK] at h
  obtain ⟨rd, h0, r1, h1, rfl⟩ := h
  exact ⟨rd, r1, ireg_of_eq h0, ireg_of_eq h1, rfl⟩

theorem ii2_inv {res a1 a2 : Mreg} {f : Ireg → Ireg → Ireg → Code} {c : Code}
    (h : ii2 res a1 a2 f = .OK c) :
    ∃ rd r1 r2, pregOf res = .IR rd ∧ pregOf a1 = .IR r1 ∧ pregOf a2 = .IR r2 ∧
      c = f rd r1 r2 := by
  simp only [ii2, res_bind_OK, res_pure_OK] at h
  obtain ⟨rd, h0, r1, h1, r2, h2, rfl⟩ := h
  exact ⟨rd, r1, r2, ireg_of_eq h0, ireg_of_eq h1, ireg_of_eq h2, rfl⟩

theorem ii3_inv {res a1 a2 a3 : Mreg} {f : Ireg → Ireg → Ireg → Ireg → Code} {c : Code}
    (h : ii3 res a1 a2 a3 f = .OK c) :
    ∃ rd r1 r2 r3, pregOf res = .IR rd ∧ pregOf a1 = .IR r1 ∧ pregOf a2 = .IR r2 ∧
      pregOf a3 = .IR r3 ∧ c = f rd r1 r2 r3 := by
  simp only [ii3, res_bind_OK, res_pure_OK] at h
  obtain ⟨rd, h0, r1, h1, r2, h2, r3, h3, rfl⟩ := h
  exact ⟨rd, r1, r2, r3, ireg_of_eq h0, ireg_of_eq h1, ireg_of_eq h2, ireg_of_eq h3, rfl⟩

theorem ff1_inv {res a1 : Mreg} {f : Freg → Freg → Code} {c : Code} (h : ff1 res a1 f = .OK c) :
    ∃ rd r1, pregOf res = .FR rd ∧ pregOf a1 = .FR r1 ∧ c = f rd r1 := by
  simp only [ff1, res_bind_OK, res_pure_OK] at h
  obtain ⟨rd, h0, r1, h1, rfl⟩ := h
  exact ⟨rd, r1, freg_of_eq h0, freg_of_eq h1, rfl⟩

theorem ff2_inv {res a1 a2 : Mreg} {f : Freg → Freg → Freg → Code} {c : Code}
    (h : ff2 res a1 a2 f = .OK c) :
    ∃ rd r1 r2, pregOf res = .FR rd ∧ pregOf a1 = .FR r1 ∧ pregOf a2 = .FR r2 ∧
      c = f rd r1 r2 := by
  simp only [ff2, res_bind_OK, res_pure_OK] at h
  obtain ⟨rd, h0, r1, h1, r2, h2, rfl⟩ := h
  exact ⟨rd, r1, r2, freg_of_eq h0, freg_of_eq h1, freg_of_eq h2, rfl⟩

theorem if1_inv {res a1 : Mreg} {f : Ireg → Freg → Code} {c : Code} (h : if1 res a1 f = .OK c) :
    ∃ rd r1, pregOf res = .IR rd ∧ pregOf a1 = .FR r1 ∧ c = f rd r1 := by
  simp only [if1, res_bind_OK, res_pure_OK] at h
  obtain ⟨rd, h0, r1, h1, rfl⟩ := h
  exact ⟨rd, r1, ireg_of_eq h0, freg_of_eq h1, rfl⟩

theorem fi1_inv {res a1 : Mreg} {f : Freg → Ireg → Code} {c : Code} (h : fi1 res a1 f = .OK c) :
    ∃ rd r1, pregOf res = .FR rd ∧ pregOf a1 = .IR r1 ∧ c = f rd r1 := by
  simp only [fi1, res_bind_OK, res_pure_OK] at h
  obtain ⟨rd, h0, r1, h1, rfl⟩ := h
  exact ⟨rd, r1, freg_of_eq h0, ireg_of_eq h1, rfl⟩

/-! ### Value-level facts used by `transl_op_correct` -/

theorem a32_toNat (a : Op.Amount32) : a.a32_amount.toNat < 32 :=
  Integers.Int.toNat_lt_of_ltu a.a32_range

theorem a64_toNat (a : Op.Amount64) : a.a64_amount.toNat < 64 := by
  have h := a.a64_range
  rw [Integers.Int.ltu_toNat] at h
  have : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  simpa [this] using h

theorem min_toNat32 (s : Z) (a : Integers.Int) :
    (min s (Integers.Int.zwordsize - Integers.Int.unsigned a)).toNat =
      min s.toNat (32 - a.toNat) := by
  have : Integers.Int.unsigned a = (a.toNat : Z) := rfl
  have h2 : Integers.Int.zwordsize = 32 := rfl
  rw [this, h2]; have := a.isLt; omega

theorem min_toNat64 (s : Z) (a : Integers.Int) :
    (min s (Integers.Int64.zwordsize - Integers.Int.unsigned a)).toNat =
      min s.toNat (64 - a.toNat) := by
  have : Integers.Int.unsigned a = (a.toNat : Z) := rfl
  have h2 : Integers.Int64.zwordsize = 64 := rfl
  rw [this, h2]; have := a.isLt; omega

theorem repr64_unsigned_toNat {a : Integers.Int} (h : a.toNat < 64) :
    (Integers.Int64.repr (Integers.Int.unsigned a)).toNat = a.toNat := by
  show (BitVec.ofInt 64 (a.toNat : Z)).toNat = a.toNat
  rw [BitVec.toNat_ofInt]; omega

theorem shl_zeroExt_min (v : Val) (a : Op.Amount32) (s : Z) :
    Val.shl (Val.zeroExt s.toNat v) (.Vint a.a32_amount) =
      Val.shl (Val.zeroExt (min s (Integers.Int.zwordsize -
        Integers.Int.unsigned a.a32_amount)).toNat v) (.Vint a.a32_amount) := by
  cases v <;> simp only [Val.shl, Val.zeroExt]
  split <;> try rfl
  rw [min_toNat32]
  exact congrArg _ (Integers.MI.shl_zero_ext_min _ _ _)

theorem shl_signExt_min (v : Val) (a : Op.Amount32) (s : Z) :
    Val.shl (Val.signExt s.toNat v) (.Vint a.a32_amount) =
      Val.shl (Val.signExt (min s (Integers.Int.zwordsize -
        Integers.Int.unsigned a.a32_amount)).toNat v) (.Vint a.a32_amount) := by
  cases v <;> simp only [Val.shl, Val.signExt]
  split <;> try rfl
  rw [min_toNat32]
  exact congrArg _ (Integers.MI.shl_sign_ext_min _ _ _ (a32_toNat a))

theorem zeroExt_shru_min (v : Val) (a : Op.Amount32) (s : Z) :
    Val.zeroExt s.toNat (Val.shru v (.Vint a.a32_amount)) =
      Val.zeroExt (min s (Integers.Int.zwordsize -
        Integers.Int.unsigned a.a32_amount)).toNat (Val.shru v (.Vint a.a32_amount)) := by
  cases v <;> try rfl
  simp only [Val.shru]
  split <;> try rfl
  simp only [Val.zeroExt]
  rw [min_toNat32]
  exact congrArg _ (Integers.MI.zero_ext_shru_min _ _ _)

theorem signExt_shr_min (v : Val) (a : Op.Amount32) (s : Z) :
    Val.signExt s.toNat (Val.shr v (.Vint a.a32_amount)) =
      Val.signExt (min s (Integers.Int.zwordsize -
        Integers.Int.unsigned a.a32_amount)).toNat (Val.shr v (.Vint a.a32_amount)) := by
  cases v <;> try rfl
  simp only [Val.shr]
  split <;> try rfl
  simp only [Val.signExt]
  rw [min_toNat32]
  exact congrArg _ (Integers.MI.sign_ext_shr_min _ _ _ (a32_toNat a))

theorem shll_zeroExt_min (v : Val) (a : Op.Amount64) (s : Z) :
    Val.shll (Val.zero_ext_l s.toNat v) (.Vint a.a64_amount) =
      Val.shll (Val.zero_ext_l (min s (Integers.Int64.zwordsize -
        Integers.Int.unsigned a.a64_amount)).toNat v) (.Vint a.a64_amount) := by
  cases v <;> simp only [Val.shll, Val.zero_ext_l]
  split <;> try rfl
  have hy := repr64_unsigned_toNat (a64_toNat a)
  generalize Integers.Int64.repr (Integers.Int.unsigned a.a64_amount) = y at hy ⊢
  rw [min_toNat64, ← hy]
  exact congrArg _ (Integers.MI.shl_zero_ext_min _ _ _)

theorem shll_signExt_min (v : Val) (a : Op.Amount64) (s : Z) :
    Val.shll (Val.sign_ext_l s.toNat v) (.Vint a.a64_amount) =
      Val.shll (Val.sign_ext_l (min s (Integers.Int64.zwordsize -
        Integers.Int.unsigned a.a64_amount)).toNat v) (.Vint a.a64_amount) := by
  cases v <;> simp only [Val.shll, Val.sign_ext_l]
  split <;> try rfl
  have h := a64_toNat a
  have hy := repr64_unsigned_toNat h
  generalize Integers.Int64.repr (Integers.Int.unsigned a.a64_amount) = y at hy ⊢
  rw [min_toNat64, ← hy]
  exact congrArg _ (Integers.MI.shl_sign_ext_min _ _ _ (by omega))

theorem zeroExt_shrlu_min (v : Val) (a : Op.Amount64) (s : Z) :
    Val.zero_ext_l s.toNat (Val.shrlu v (.Vint a.a64_amount)) =
      Val.zero_ext_l (min s (Integers.Int64.zwordsize -
        Integers.Int.unsigned a.a64_amount)).toNat (Val.shrlu v (.Vint a.a64_amount)) := by
  cases v <;> try rfl
  simp only [Val.shrlu]
  split <;> try rfl
  simp only [Val.zero_ext_l]
  have hy := repr64_unsigned_toNat (a64_toNat a)
  generalize Integers.Int64.repr (Integers.Int.unsigned a.a64_amount) = y at hy ⊢
  rw [min_toNat64, ← hy]
  exact congrArg _ (Integers.MI.zero_ext_shru_min _ _ _)

theorem signExt_shrl_min (v : Val) (a : Op.Amount64) (s : Z) :
    Val.sign_ext_l s.toNat (Val.shrl v (.Vint a.a64_amount)) =
      Val.sign_ext_l (min s (Integers.Int64.zwordsize -
        Integers.Int.unsigned a.a64_amount)).toNat (Val.shrl v (.Vint a.a64_amount)) := by
  cases v <;> try rfl
  simp only [Val.shrl]
  split <;> try rfl
  simp only [Val.sign_ext_l]
  have h := a64_toNat a
  have hy := repr64_unsigned_toNat h
  generalize Integers.Int64.repr (Integers.Int.unsigned a.a64_amount) = y at hy ⊢
  rw [min_toNat64, ← hy]
  exact congrArg _ (Integers.MI.sign_ext_shr_min _ _ _ (by omega))

theorem neg_lessdef (x : Val) : Val.Lessdef (Val.neg x) (Val.sub (.Vint Integers.Int.zero) x) := by
  cases x <;> simp [Val.neg, Val.sub, Integers.Int.sub_zero_l] <;> constructor

theorem negl_lessdef (x : Val) :
    Val.Lessdef (Val.negl x) (Val.subl (.Vlong Integers.Int64.zero) x) := by
  cases x <;> simp [Val.negl, Val.subl, Integers.Int64.sub_zero_l] <;> constructor

theorem mul_lessdef (x y : Val) :
    Val.Lessdef (Val.mul x y) (Val.add (.Vint Integers.Int.zero) (Val.mul x y)) := by
  cases x <;> cases y <;> simp [Val.mul, Val.add, Integers.Int.add_zero_l] <;> constructor

theorem mull_lessdef (x y : Val) :
    Val.Lessdef (Val.mull x y) (Val.addl (.Vlong Integers.Int64.zero) (Val.mull x y)) := by
  cases x <;> cases y <;> simp [Val.mull, Val.addl, Integers.Int64.add_zero_l] <;> constructor

theorem not_lessdef (x : Val) :
    Val.Lessdef (Val.notint x) (Val.or (.Vint Integers.Int.zero) (Val.notint x)) := by
  cases x <;> simp [Val.notint, Val.or, Integers.Int.or_zero_l] <;> constructor

theorem notl_lessdef (x : Val) :
    Val.Lessdef (Val.notl x) (Val.orl (.Vlong Integers.Int64.zero) (Val.notl x)) := by
  cases x <;> simp [Val.notl, Val.orl, Integers.Int64.or_zero_l] <;> constructor

theorem zext_lessdef (s : Nat) (x : Val) :
    Val.Lessdef (Val.zeroExt s x) (Val.shl (Val.zeroExt s x) (.Vint Integers.Int.zero)) := by
  cases x <;> simp [Val.zeroExt, Val.shl, Integers.Int.shl_zero] <;> constructor

theorem sext_lessdef (s : Nat) (x : Val) :
    Val.Lessdef (Val.signExt s x) (Val.shl (Val.signExt s x) (.Vint Integers.Int.zero)) := by
  cases x <;> simp [Val.signExt, Val.shl, Integers.Int.shl_zero] <;> constructor

theorem zextl_lessdef (s : Nat) (x : Val) :
    Val.Lessdef (Val.zero_ext_l s x) (Val.shll (Val.zero_ext_l s x) (.Vint Integers.Int.zero)) := by
  cases x <;> simp only [Val.zero_ext_l, shll_zero] <;> constructor

theorem sextl_lessdef (s : Nat) (x : Val) :
    Val.Lessdef (Val.sign_ext_l s x) (Val.shll (Val.sign_ext_l s x) (.Vint Integers.Int.zero)) := by
  cases x <;> simp only [Val.sign_ext_l, shll_zero] <;> constructor

theorem maketotal_lessdef {o : Option Val} {v : Val} (h : o = some v) :
    Val.Lessdef v (Val.maketotal o) := by
  subst h; exact .refl _

theorem eval_Ocmp {F V : Type} (ge : Genv F V) (sp : Val) (cond : Op.Condition) (vl : List Val)
    (m : Mem) :
    Op.evalOperation ge sp (.Ocmp cond) vl m = some (Val.ofOptbool (Op.evalCondition cond vl m)) := by
  unfold Op.evalOperation; rfl

theorem eval_Osel {F V : Type} (ge : Genv F V) (sp : Val) (cond : Op.Condition) (ty : ATyp)
    (v1 v2 : Val) (vl : List Val) (m : Mem) :
    Op.evalOperation ge sp (.Osel cond ty) (v1 :: v2 :: vl) m =
      some (Val.select (Op.evalCondition cond vl m) v1 v2 ty) := by
  unfold Op.evalOperation; rfl

theorem translOp_Ocmp (o : Options) (cond : Op.Condition) (args : List Mreg) (res : Mreg)
    (k : Code) :
    translOp o (.Ocmp cond) args res k =
      (do let rd ← iregOf res; translCond cond args (.Pcset rd (condForCond cond) :: k)) := by
  unfold translOp; rfl

attribute [local irreducible] ii1 ii2 ii3 ff1 ff2 if1 fi1

section CONSTRUCTORS
variable (sym : SymbolSplit) (ge : Asm.CGenv) (fn : Asm.Function)

/-- A single instruction that writes one register and advances `PC`. -/
theorem op_single {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Preg} {v v' : Val}
    {P : Preg → Prop}
    (hi : execInstr sym ge fn i rs m = .Next (nextinstr (rs.set rd v')) m) (hrd : rd ≠ .PC)
    (hv : Val.Lessdef v v') :
    ∃ rs', ExecStraight sym ge fn (i :: k) rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  ⟨_, .one _ _ _ _ _ _ hi (nextinstr_set_PC _ _ hrd), by rwa [nextinstr_set_same _ _ hrd],
    fun _ h1 h2 _ => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩

/-- A single instruction that writes one register, clobbers `X16`, and advances `PC`. -/
theorem op_single_X16 {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Preg} {v v' : Val}
    {P : Preg → Prop}
    (hi : execInstr sym ge fn i rs m =
      .Next (nextinstr ((rs.set (.IR .X16) .Vundef).set rd v')) m) (hrd : rd ≠ .PC)
    (hv : Val.Lessdef v v') :
    ∃ rs', ExecStraight sym ge fn (i :: k) rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  ⟨_, .one _ _ _ _ _ _ hi (nextinstr_set_PC _ _ hrd), by rwa [nextinstr_set_same _ _ hrd],
    fun _ h1 h2 _ => by
      rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]
      simp [Regset.set, dataPreg_ne_X16 h1]⟩

/-- A sequence of instructions computing `w` into `rd` and preserving the
    other data registers. -/
theorem op_multi {c k : Code} {rs : Regset} {m : Mem} {rd : Preg} {v w : Val} {P : Preg → Prop}
    (hex : ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' rd = w ∧
      ∀ r, dataPreg r = true → r ≠ rd → rs' r = rs r)
    (hv : Val.Lessdef v w) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  let ⟨rs', A, B, C⟩ := hex
  ⟨rs', A, B ▸ hv, fun r h1 h2 _ => C r h1 h2⟩

/-- Same as `op_multi`, for sequences that preserve every register but `PC`
    and `rd`. -/
theorem op_multi_pc {c k : Code} {rs : Regset} {m : Mem} {rd : Preg} {v w : Val}
    {P : Preg → Prop}
    (hex : ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' rd = w ∧
      ∀ r, r ≠ .PC → r ≠ rd → rs' r = rs r)
    (hv : Val.Lessdef v w) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  let ⟨rs', A, B, C⟩ := hex
  ⟨rs', A, B ▸ hv, fun r h1 h2 _ => C r (dataPreg_ne_PC h1) h2⟩

theorem ne_X16_of {a : Mreg} {r : Ireg} (h : pregOf a = .IR r) : r ≠ .X16 := by
  rintro rfl; exact preg_of_not_X16 a h

theorem addrstack_lessdef (sp : Val) (ofs : Integers.Ptrofs) :
    Val.Lessdef (Val.offsetPtr sp ofs) (Val.addl sp (.Vlong (Integers.Ptrofs.to_int64 ofs))) := by
  cases sp <;> try exact .undef _
  simp only [Val.offsetPtr, Val.addl, ptrofs_of_int64_to_int64]
  exact .refl _

/-- A condition-setting sequence followed by one instruction that writes `rd`. -/
theorem op_after_cond {c1 : Code} {i : Instruction} {k : Code} {rs rs1 : Regset} {m : Mem}
    {rd : Preg} {v w : Val} {P : Preg → Prop}
    (A : ExecStraight sym ge fn c1 rs m (i :: k) rs1 m)
    (C : ∀ r, dataPreg r = true → rs1 r = rs r)
    (hi : execInstr sym ge fn i rs1 m = .Next (nextinstr (rs1.set rd w)) m) (hrd : rd ≠ .PC)
    (hv : Val.Lessdef v w) :
    ∃ rs', ExecStraight sym ge fn c1 rs m k rs' m ∧ Val.Lessdef v (rs' rd) ∧
      ∀ r, dataPreg r = true → r ≠ rd → P r → rs' r = rs r :=
  ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ hi (nextinstr_set_PC _ _ hrd)),
    by rwa [nextinstr_set_same _ _ hrd],
    fun r h1 h2 _ => by rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]; exact C r h1⟩

theorem cmp_lessdef {ob : Option Bool} {tc : Testcond} {rs : Regset}
    (B : ∀ b, ob = some b → evalTestcond tc rs = some b) :
    Val.Lessdef (Val.ofOptbool ob)
      (selectCond tc rs (.Vint Integers.Int.one) (.Vint Integers.Int.zero)) := by
  cases ob with
  | none => exact .undef _
  | some b =>
    simp only [selectCond, B b rfl, Val.ofOptbool, Val.ofBool]
    cases b <;> exact .refl _

theorem select_same_lessdef (ob : Option Bool) (x : Val) (ty : ATyp) :
    Val.Lessdef (Val.select ob x x ty) x := by
  cases ob with
  | none => exact .undef _
  | some b => cases b <;> exact Val.lessdef_normalize _ _

theorem select_lessdef {ob : Option Bool} {tc : Testcond} {rs : Regset} (x y : Val) (ty : ATyp)
    (B : ∀ b, ob = some b → evalTestcond tc rs = some b) :
    Val.Lessdef (Val.select ob x y ty) (selectCond tc rs x y) := by
  cases ob with
  | none => exact .undef _
  | some b =>
    simp only [Val.select, selectCond, B b rfl]
    cases b <;> exact Val.lessdef_normalize _ _

set_option maxHeartbeats 1000000 in
/-- `Asmgenproof1.transl_op_correct` -/
theorem transl_op_correct (o : Options) (op : Op.Operation) (args : List Mreg) (res : Mreg)
    (k : Code) (rs : Regset) (m : Mem) (v : Val) (c : Code)
    (h : translOp o op args res k = .OK c)
    (hev : Op.evalOperation ge (rs .SP) op ((args.map pregOf).map rs) m = some v) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' (pregOf res)) ∧
      ∀ r, dataPreg r = true → r ≠ pregOf res → PregNotin r (destroyedByOp op) →
        rs' r = rs r := by
  cases op
  case Ocmp cond =>
    rw [eval_Ocmp] at hev; cases hev
    rw [translOp_Ocmp] at h
    simp only [res_bind_OK] at h
    obtain ⟨rd, h0, h⟩ := h
    obtain ⟨rs1, A, B, C⟩ := transl_cond_correct sym ge fn cond args _ _ rs m h
    rw [ireg_of_eq h0]
    exact op_after_cond sym ge fn A C rfl (by simp) (cmp_lessdef B)
  case Osel cond ty =>
    rcases args with _ | ⟨a1, _ | ⟨a2, args⟩⟩ <;> unfold translOp at h <;> dsimp only at h <;>
      (try cases h)
    simp only [List.map] at hev
    rw [eval_Osel] at hev; cases hev
    split at h
    · rename_i r e0
      simp only [res_bind_OK] at h
      obtain ⟨r1, h1, r2, h2, h⟩ := h
      have e1 := ireg_of_eq h1
      have e2 := ireg_of_eq h2
      simp only [e0, e1, e2]
      split at h
      · rename_i e; subst e
        simp only [res_pure_OK] at h; subst h
        exact op_single sym ge fn rfl (by simp) (select_same_lessdef _ _ _)
      · obtain ⟨rs1, A, B, C⟩ := transl_cond_correct sym ge fn cond args _ _ rs m h
        refine op_after_cond sym ge fn A C rfl (by simp) ?_
        rw [C _ (by rw [← e1]; exact preg_of_data _), C _ (by rw [← e2]; exact preg_of_data _)]
        exact select_lessdef _ _ _ B
    · rename_i r e0
      simp only [res_bind_OK] at h
      obtain ⟨r1, h1, r2, h2, h⟩ := h
      have e1 := freg_of_eq h1
      have e2 := freg_of_eq h2
      simp only [e0, e1, e2]
      split at h
      · rename_i e; subst e
        simp only [res_pure_OK] at h; subst h
        exact op_single sym ge fn rfl (by simp) (select_same_lessdef _ _ _)
      · obtain ⟨rs1, A, B, C⟩ := transl_cond_correct sym ge fn cond args _ _ rs m h
        refine op_after_cond sym ge fn A C rfl (by simp) ?_
        rw [C _ (by rw [← e1]; exact preg_of_data _), C _ (by rw [← e2]; exact preg_of_data _)]
        exact select_lessdef _ _ _ B
    · cases h
  all_goals (rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, args⟩⟩⟩⟩ <;>
              unfold translOp at h <;> dsimp only at h <;> (try cases h))
  all_goals first
    | (guard_hyp h : ii1 _ _ _ = _
       obtain ⟨rd, r1, e0, e1, rfl⟩ := ii1_inv h
       simp only [List.map, e0, e1] at hev ⊢)
    | (guard_hyp h : ii2 _ _ _ _ = _
       obtain ⟨rd, r1, r2, e0, e1, e2, rfl⟩ := ii2_inv h
       simp only [List.map, e0, e1, e2] at hev ⊢)
    | (guard_hyp h : ii3 _ _ _ _ _ = _
       obtain ⟨rd, r1, r2, r3, e0, e1, e2, e3, rfl⟩ := ii3_inv h
       simp only [List.map, e0, e1, e2, e3] at hev ⊢)
    | (guard_hyp h : ff1 _ _ _ = _
       obtain ⟨rd, r1, e0, e1, rfl⟩ := ff1_inv h
       simp only [List.map, e0, e1] at hev ⊢)
    | (guard_hyp h : ff2 _ _ _ _ = _
       obtain ⟨rd, r1, r2, e0, e1, e2, rfl⟩ := ff2_inv h
       simp only [List.map, e0, e1, e2] at hev ⊢)
    | (guard_hyp h : if1 _ _ _ = _
       obtain ⟨rd, r1, e0, e1, rfl⟩ := if1_inv h
       simp only [List.map, e0, e1] at hev ⊢)
    | (guard_hyp h : fi1 _ _ _ = _
       obtain ⟨rd, r1, e0, e1, rfl⟩ := fi1_inv h
       simp only [List.map, e0, e1] at hev ⊢)
    | skip
  all_goals (try simp only [List.map] at hev)
  all_goals (unfold Op.evalOperation at hev; (try dsimp only at hev))
  all_goals (try (cases hev; exact op_single sym ge fn rfl (by simp) (.refl _)))
  all_goals (try (refine op_single sym ge fn rfl (by simp) ?_))
  all_goals (try (exact maketotal_lessdef hev))
  all_goals (try (
    cases hev
    try simp only [ir0w, ir0x]
    try rw [transl_eval_shift']
    try rw [transl_eval_shiftl']
    try simp only [transl_eval_shift, transl_eval_shiftl]
    try simp only [evalShiftOpInt, evalShiftOpLong]
    first
      | with_reducible exact .refl _
      | exact neg_lessdef _ | exact negl_lessdef _ | exact mul_lessdef _ _
      | exact mull_lessdef _ _ | exact not_lessdef _ | exact notl_lessdef _
      | exact zext_lessdef _ _ | exact sext_lessdef _ _ | exact zextl_lessdef _ _
      | exact sextl_lessdef _ _
      | (rw [shl_zeroExt_min]; exact .refl _) | (rw [shl_signExt_min]; exact .refl _)
      | (rw [zeroExt_shru_min]; exact .refl _) | (rw [signExt_shr_min]; exact .refl _)
      | (rw [shll_zeroExt_min]; exact .refl _) | (rw [shll_signExt_min]; exact .refl _)
      | (rw [zeroExt_shrlu_min]; exact .refl _) | (rw [signExt_shrl_min]; exact .refl _)))
  case Omove.cons.nil =>
    cases hev
    split at h <;> cases h <;> rename_i e0 e1 <;> simp only [e0, e1] <;>
      exact op_single sym ge fn rfl (by simp) (.refl _)
  case Ointconst.nil =>
    cases hev
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨rd, h0, rfl⟩ := h
    rw [ireg_of_eq h0]
    exact op_multi_pc sym ge fn (exec_loadimm32 sym ge fn rd _ k rs m) (.refl _)
  case Olongconst.nil =>
    cases hev
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨rd, h0, rfl⟩ := h
    rw [ireg_of_eq h0]
    exact op_multi_pc sym ge fn (exec_loadimm64 sym ge fn rd _ k rs m) (.refl _)
  case Ofloatconst.nil f =>
    cases hev
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨rd, h0, rfl⟩ := h
    rw [freg_of_eq h0]
    split
    · subst f; exact op_single sym ge fn rfl (by simp) (.refl _)
    · exact op_single_X16 sym ge fn rfl (by simp) (.refl _)
  case Osingleconst.nil f =>
    cases hev
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨rd, h0, rfl⟩ := h
    rw [freg_of_eq h0]
    split
    · subst f; exact op_single sym ge fn rfl (by simp) (.refl _)
    · exact op_single_X16 sym ge fn rfl (by simp) (.refl _)
  case Oaddrsymbol.nil id ofs =>
    cases hev
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨rd, h0, rfl⟩ := h
    rw [ireg_of_eq h0]
    exact op_multi sym ge fn
      (exec_loadsymbol sym ge fn o rd id ofs k rs m (.inl (ireg_of_not_X16 h0))) (.refl _)
  case Oaddrstack.nil ofs =>
    cases hev
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨rd, h0, rfl⟩ := h
    rw [ireg_of_eq h0]
    exact op_multi sym ge fn (exec_addimm64 sym ge fn (.RR1 rd) .XSP _ k rs m (by simp [pregOfIregsp]))
      (addrstack_lessdef _ _)
  case Oaddimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_addimm32 sym ge fn rd r1 n k rs m (ne_X16_of e1)) (.refl _)
  case Oaddlimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_addimm64 sym ge fn (.RR1 rd) (.RR1 r1) n k rs m
      (fun e => ne_X16_of e1 (Preg.IR.inj e))) (.refl _)
  case Oandimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_logicalimm32 sym ge fn (.Pandimm .W) (.Pand .W) Val.and
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 n k rs m (ne_X16_of e1)) (.refl _)
  case Oorimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_logicalimm32 sym ge fn (.Porrimm .W) (.Porr .W) Val.or
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 n k rs m (ne_X16_of e1)) (.refl _)
  case Oxorimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_logicalimm32 sym ge fn (.Peorimm .W) (.Peor .W) Val.xor
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 n k rs m (ne_X16_of e1)) (.refl _)
  case Oandlimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_logicalimm64 sym ge fn (.Pandimm .X) (.Pand .X) Val.andl
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 n k rs m (ne_X16_of e1)) (.refl _)
  case Oorlimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_logicalimm64 sym ge fn (.Porrimm .X) (.Porr .X) Val.orl
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 n k rs m (ne_X16_of e1)) (.refl _)
  case Oxorlimm.cons.nil n =>
    cases hev
    exact op_multi sym ge fn (exec_logicalimm64 sym ge fn (.Peorimm .X) (.Peor .X) Val.xorl
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 n k rs m (ne_X16_of e1)) (.refl _)
  case Oshrximm.cons.nil n =>
    exact op_multi sym ge fn (exec_shrx32 sym ge fn rd r1 n k v rs m hev (ne_X16_of e1)) (.refl _)
  case Oshrlximm.cons.nil n =>
    exact op_multi sym ge fn (exec_shrx64 sym ge fn rd r1 n k v rs m hev (ne_X16_of e1)) (.refl _)
  case Oextend.cons.nil x a =>
    cases hev
    exact op_multi_pc sym ge fn (exec_move_extended sym ge fn rd r1 x a k rs m) (.refl _)
  case Oaddlext.cons.cons.nil x a =>
    cases hev
    exact op_multi sym ge fn (exec_arith_extended sym ge fn Val.addl .Paddext (.Padd .X)
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 r2 x a k rs m (ne_X16_of e1)) (.refl _)
  case Osublext.cons.cons.nil x a =>
    cases hev
    exact op_multi sym ge fn (exec_arith_extended sym ge fn Val.subl .Psubext (.Psub .X)
      (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) rd r1 r2 x a k rs m (ne_X16_of e1)) (.refl _)
  case Olowlong.cons.nil =>
    cases hev
    simp only [res_bind_OK] at h
    obtain ⟨rd, h0, r1, h1, h⟩ := h
    split at h
    · cases h; rename_i e; subst e
      rw [ireg_of_eq h0, ireg_of_eq h1]
      exact op_single sym ge fn rfl (by simp) (.refl _)
    · cases h

end CONSTRUCTORS

end Asmgenproof1
end CC
