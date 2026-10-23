/-
  Correctness proof for RISC-V code generation: auxiliary results, part 2 —
  port of the middle of `riscV/Asmgenproof1.v`: conditional branches
  (`transl_cbranch_correct_1`, `transl_cbranch_correct_true`,
  `transl_cbranch_correct_false`) and condition operators
  (`transl_cond_int32s/32u/64s/64u_correct`,
  `transl_condimm_int32s/32u/64s/64u_correct`, `transl_cond_op_correct`).

  Differences from Rocq: the `ArgsInv` tactic becomes a case analysis on the
  condition and its arguments followed by inversion of the monadic binds;
  `Val.cmpl` and `Val.cmplu` are partial (`Option Val`) as in Rocq, and the
  lemmas relating `maketotal` of them to `Val.ofOptbool` are proved here.
-/
import CCLib.riscV.Asmgenproof1
import CCLib.riscV.OpInject

namespace CC
namespace RiscV
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1 Op

/-- Inversion of a successful `Res` bind (`Errors.bind_inversion`). -/
theorem res_bind_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

theorem res_pure_OK {A : Type} {a b : A} : (pure a : Res A) = .OK b ↔ a = b := by
  simp [pure]

/-! ## Value-level facts -/

theorem xor_ofOptbool_one (ob : Option Bool) :
    Val.xor (Val.ofOptbool ob) (.Vint Integers.Int.one) = Val.ofOptbool (ob.map (!·)) := by
  rcases ob with _ | ⟨_ | _⟩ <;> rfl

theorem maketotal_map_ofBool (ob : Option Bool) :
    Val.maketotal (ob.map Val.ofBool) = Val.ofOptbool ob := by
  rcases ob with _ | ⟨_ | _⟩ <;> rfl

theorem maketotal_cmpl (c : Comparison) (v1 v2 : Val) :
    Val.maketotal (Val.cmpl c v1 v2) = Val.ofOptbool (Val.cmpl_bool c v1 v2) :=
  maketotal_map_ofBool _

theorem maketotal_cmplu (vp : Block → Z → Bool) (c : Comparison) (v1 v2 : Val) :
    Val.maketotal (Val.cmplu vp c v1 v2) = Val.ofOptbool (Val.cmplu_bool vp c v1 v2) :=
  maketotal_map_ofBool _

theorem lessdef_cmp_cmpu {vp : Block → Z → Bool} {c : Comparison} (hc : c = .Ceq ∨ c = .Cne)
    (v1 v2 : Val) : Val.Lessdef (Val.cmp c v1 v2) (Val.cmpu vp c v1 v2) := by
  unfold Val.cmp Val.cmpu
  cases h : Val.cmp_bool c v1 v2
  · exact .undef _
  · rw [cmpu_bool_of_cmp_bool hc h]; exact .refl _

theorem lessdef_cmpl_cmplu {vp : Block → Z → Bool} {c : Comparison} (hc : c = .Ceq ∨ c = .Cne)
    (v1 v2 : Val) :
    Val.Lessdef (Val.maketotal (Val.cmpl c v1 v2)) (Val.maketotal (Val.cmplu vp c v1 v2)) := by
  rw [maketotal_cmpl, maketotal_cmplu]
  cases h : Val.cmpl_bool c v1 v2
  · exact .undef _
  · rw [cmplu_bool_of_cmpl_bool hc h]; exact .refl _

/-! ## Arithmetic facts used by `transl_condimm_*` -/

theorem int_cmp_xor_zero {c : Comparison} (hc : c = .Ceq ∨ c = .Cne) (i n : Integers.Int) :
    Integers.Int.cmp c (Integers.Int.xor i n) Integers.Int.zero = Integers.Int.cmp c i n := by
  rcases hc with rfl | rfl <;>
  simp only [Integers.Int.cmp, Integers.MI.cmp, Integers.Int.xor, Integers.MI.xor, Integers.MI.eq, Integers.Int.zero, Integers.MI.zero] <;> bv_decide
theorem int_cmp_le_max (i : Integers.Int) : Integers.Int.cmp .Cle i (Integers.Int.repr Integers.Int.max_signed) = true := by
  rw [show Integers.Int.repr Integers.Int.max_signed = 0x7fffffff#32 by decide]
  simp only [Integers.Int.cmp, Integers.MI.cmp, Integers.MI.lt]; bv_decide
theorem int_cmp_le_succ (i n : Integers.Int) (h : Integers.Int.eq n (Integers.Int.repr Integers.Int.max_signed) = false) :
    Integers.Int.cmp .Cle i n = Integers.Int.cmp .Clt i (Integers.Int.add n Integers.Int.one) := by
  rw [show Integers.Int.repr Integers.Int.max_signed = 0x7fffffff#32 by decide] at h
  simp only [Integers.Int.eq, Integers.MI.eq] at h
  simp only [Integers.Int.cmp, Integers.MI.cmp, Integers.MI.lt, Integers.Int.add, Integers.MI.add, Integers.Int.one, Integers.MI.one]; bv_decide
theorem int64_cmp_le_succ (i n : Integers.Int64) (h : Integers.Int64.eq n (Integers.Int64.repr Integers.Int64.max_signed) = false) :
    Integers.Int64.cmp .Cle i n = Integers.Int64.cmp .Clt i (Integers.Int64.add n Integers.Int64.one) := by
  rw [show Integers.Int64.repr Integers.Int64.max_signed = 0x7fffffffffffffff#64 by decide] at h
  simp only [Integers.Int64.eq, Integers.MI.eq] at h
  simp only [Integers.Int64.cmp, Integers.MI.cmp, Integers.MI.lt, Integers.Int64.add, Integers.MI.add, Integers.Int64.one, Integers.MI.one]; bv_decide

theorem int64_cmp_xor_zero {c : Comparison} (hc : c = .Ceq ∨ c = .Cne) (i n : Integers.Int64) :
    Integers.Int64.cmp c (Integers.Int64.xor i n) Integers.Int64.zero = Integers.Int64.cmp c i n := by
  rcases hc with rfl | rfl <;>
  simp only [Integers.Int64.cmp, Integers.MI.cmp, Integers.Int64.xor, Integers.MI.xor,
    Integers.MI.eq, Integers.Int64.zero, Integers.MI.zero] <;> bv_decide

theorem int64_cmp_le_max (i : Integers.Int64) :
    Integers.Int64.cmp .Cle i (Integers.Int64.repr Integers.Int64.max_signed) = true := by
  rw [show Integers.Int64.repr Integers.Int64.max_signed = 0x7fffffffffffffff#64 by decide]
  simp only [Integers.Int64.cmp, Integers.MI.cmp, Integers.MI.lt]; bv_decide

theorem int_eq_true {x y : Integers.Int} (h : Integers.Int.eq x y = true) : x = y := by
  simpa [Integers.Int.eq, Integers.MI.eq] using h

theorem int64_eq_true {x y : Integers.Int64} (h : Integers.Int64.eq x y = true) : x = y := by
  simpa [Integers.Int64.eq, Integers.MI.eq] using h

section CONSTRUCTORS
variable {sym : HalfSplit} {ge : Asm.CGenv} {fn : Asm.Function}

/-- A one-instruction sequence setting `rd`. -/
theorem straight_one {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Ireg} {v : Val}
    (h : execInstr sym ge fn i rs m = .Next (nextinstr (rs.set (.IR rd) v)) m) :
    ∃ rs', ExecStraight sym ge fn (i :: k) rs m k rs' m ∧ rs' (.IR rd) = v ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r :=
  ⟨_, exec_straight_set (ir_ne_pc rd) h, nextinstr_set_same _ _ (ir_ne_pc rd),
    fun _ h1 h2 => nextinstr_set_other _ _ h1 h2⟩

/-- An instruction setting `rd`, followed by `xori rd, rd, 1`. -/
theorem straight_two_xor {i : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Ireg}
    {v : Val} (h : execInstr sym ge fn i rs m = .Next (nextinstr (rs.set (.IR rd) v)) m) :
    ∃ rs', ExecStraight sym ge fn (i :: .Pxoriw rd rd Integers.Int.one :: k) rs m k rs' m ∧
      rs' (.IR rd) = Val.xor v (.Vint Integers.Int.one) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  refine ⟨_, .step _ _ _ _ _ _ _ _ _ h (nextinstr_set_pc _ _ (ir_ne_pc rd))
    (exec_straight_set (ir_ne_pc rd) rfl), ?_, fun r h1 h2 => ?_⟩
  · rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
    simp only [get0w]
    rw [nextinstr_set_same _ _ (ir_ne_pc rd)]
  · rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h2]

/-! ## Condition operators -/

/-- `Asmgenproof1.transl_cond_int32s_correct` -/
theorem transl_cond_int32s_correct (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code)
    (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (translCondInt32s cmp rd r1 r2 k) rs m k rs' m ∧
      Val.Lessdef (Val.cmp cmp (get0w rs r1) (get0w rs r2)) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  cases cmp <;> simp only [translCondInt32s]
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Pseqw rd r1 r2) rfl
    exact ⟨rs', A, B ▸ lessdef_cmp_cmpu (.inl rfl) _ _, C⟩
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psnew rd r1 r2) rfl
    exact ⟨rs', A, B ▸ lessdef_cmp_cmpu (.inr rfl) _ _, C⟩
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltw rd r1 r2) rfl
    exact ⟨rs', A, B ▸ .refl _, C⟩
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltw rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B]; unfold Val.cmp
    rw [xor_ofOptbool_one, show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmp_bool,
      show Comparison.Cle = Comparison.Cgt.negate from rfl, Val.negate_cmp_bool]
    exact .refl _
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltw rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B, show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmp]; exact .refl _
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltw rd r1 r2) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B]; unfold Val.cmp
    rw [xor_ofOptbool_one, show Comparison.Cge = Comparison.Clt.negate from rfl,
      Val.negate_cmp_bool]
    exact .refl _

/-- `Asmgenproof1.transl_cond_int32u_correct` -/
theorem transl_cond_int32u_correct (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code)
    (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (translCondInt32u cmp rd r1 r2 k) rs m k rs' m ∧
      rs' (.IR rd) = Val.cmpu (Mem.validPointer m) cmp (get0w rs r1) (get0w rs r2) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  cases cmp <;> simp only [translCondInt32u]
  · exact straight_one rfl
  · exact straight_one rfl
  · exact straight_one rfl
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltuw rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B]; unfold Val.cmpu
    rw [xor_ofOptbool_one, show Comparison.Clt = Comparison.Cgt.swap from rfl,
      Val.swap_cmpu_bool, show Comparison.Cle = Comparison.Cgt.negate from rfl,
      Val.negate_cmpu_bool]
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltuw rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B]; unfold Val.cmpu
    rw [show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmpu_bool]
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltuw rd r1 r2) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B]; unfold Val.cmpu
    rw [xor_ofOptbool_one, show Comparison.Cge = Comparison.Clt.negate from rfl,
      Val.negate_cmpu_bool]

/-- `Asmgenproof1.transl_cond_int64s_correct` -/
theorem transl_cond_int64s_correct (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code)
    (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (translCondInt64s cmp rd r1 r2 k) rs m k rs' m ∧
      Val.Lessdef (Val.maketotal (Val.cmpl cmp (get0l rs r1) (get0l rs r2))) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  cases cmp <;> simp only [translCondInt64s]
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Pseql rd r1 r2) rfl
    exact ⟨rs', A, B ▸ lessdef_cmpl_cmplu (.inl rfl) _ _, C⟩
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psnel rd r1 r2) rfl
    exact ⟨rs', A, B ▸ lessdef_cmpl_cmplu (.inr rfl) _ _, C⟩
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltl rd r1 r2) rfl
    exact ⟨rs', A, B ▸ .refl _, C⟩
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltl rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B, maketotal_cmpl, maketotal_cmpl, xor_ofOptbool_one,
      show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmpl_bool,
      show Comparison.Cle = Comparison.Cgt.negate from rfl, Val.negate_cmpl_bool]
    exact .refl _
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltl rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B, maketotal_cmpl, maketotal_cmpl, show Comparison.Clt = Comparison.Cgt.swap from rfl,
      Val.swap_cmpl_bool]
    exact .refl _
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltl rd r1 r2) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B, maketotal_cmpl, maketotal_cmpl, xor_ofOptbool_one,
      show Comparison.Cge = Comparison.Clt.negate from rfl, Val.negate_cmpl_bool]
    exact .refl _

/-- `Asmgenproof1.transl_cond_int64u_correct` -/
theorem transl_cond_int64u_correct (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code)
    (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (translCondInt64u cmp rd r1 r2 k) rs m k rs' m ∧
      rs' (.IR rd) = Val.maketotal (Val.cmplu (Mem.validPointer m) cmp (get0l rs r1) (get0l rs r2)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  cases cmp <;> simp only [translCondInt64u]
  · exact straight_one rfl
  · exact straight_one rfl
  · exact straight_one rfl
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltul rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B, maketotal_cmplu, maketotal_cmplu, xor_ofOptbool_one,
      show Comparison.Clt = Comparison.Cgt.swap from rfl, Val.swap_cmplu_bool,
      show Comparison.Cle = Comparison.Cgt.negate from rfl, Val.negate_cmplu_bool]
  · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltul rd r2 r1) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B, maketotal_cmplu, maketotal_cmplu, show Comparison.Clt = Comparison.Cgt.swap from rfl,
      Val.swap_cmplu_bool]
  · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
      (i := .Psltul rd r1 r2) rfl
    refine ⟨rs', A, ?_, C⟩
    rw [B, maketotal_cmplu, maketotal_cmplu, xor_ofOptbool_one,
      show Comparison.Cge = Comparison.Clt.negate from rfl, Val.negate_cmplu_bool]

/-- `Asmgenproof1.transl_condimm_int32s_correct` -/
theorem transl_condimm_int32s_correct (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int)
    (k : Code) (rs : Regset) (m : Mem) (h1 : r1 ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (translCondimmInt32s cmp rd r1 n k) rs m k rs' m ∧
      Val.Lessdef (Val.cmp cmp (rs (.IR r1)) (.Vint n)) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  have h1' : Preg.IR r1 ≠ .IR .X31 := fun e => h1 (Preg.IR.inj e)
  unfold translCondimmInt32s
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]; obtain rfl := int_eq_true hz
    obtain ⟨rs', A, B, C⟩ := transl_cond_int32s_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) .X0 k rs m
    exact ⟨rs', A, B, fun r h1 h2 _ => C r h1 h2⟩
  rw [if_neg hz]
  have DFL : ∃ rs', ExecStraight sym ge fn
      (loadimm32 Ireg.X31 n (translCondInt32s cmp rd r1 Ireg.X31 k)) rs m k rs' m ∧
      Val.Lessdef (Val.cmp cmp (rs (.IR r1)) (.Vint n)) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
    obtain ⟨rs1, A1, B1, C1⟩ := loadimm32_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
      (translCondInt32s cmp rd r1 Ireg.X31 k) rs m
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int32s_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) (.X .X31) k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_, fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h3]⟩
    simp only [get0w] at B2; rwa [B1, C1 _ (ir_ne_pc r1) h1'] at B2
  cases cmp <;> dsimp only
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm32_correct (sym := sym) (ge := ge) (fn := fn) .Pxorw .Pxoriw
      Val.xor m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1 n
      (translCondInt32s .Ceq rd rd .X0 k) rs h1
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int32s_correct (sym := sym) (ge := ge) (fn := fn)
      .Ceq rd (.X rd) .X0 k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_, fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h2 h3]⟩
    simp only [get0w] at B2; rw [B1] at B2
    revert B2; cases rs (.IR r1) <;> intro B2 <;> try exact .undef _
    rename_i i
    have E : Val.cmp .Ceq (Val.xor (.Vint i) (.Vint n)) (.Vint Integers.Int.zero) =
        Val.cmp .Ceq (.Vint i) (.Vint n) := by
      show Val.ofBool _ = Val.ofBool _; rw [int_cmp_xor_zero (.inl rfl)]
    rwa [E] at B2
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm32_correct (sym := sym) (ge := ge) (fn := fn) .Pxorw .Pxoriw
      Val.xor m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1 n
      (translCondInt32s .Cne rd rd .X0 k) rs h1
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int32s_correct (sym := sym) (ge := ge) (fn := fn)
      .Cne rd (.X rd) .X0 k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_, fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h2 h3]⟩
    simp only [get0w] at B2; rw [B1] at B2
    revert B2; cases rs (.IR r1) <;> intro B2 <;> try exact .undef _
    rename_i i
    have E : Val.cmp .Cne (Val.xor (.Vint i) (.Vint n)) (.Vint Integers.Int.zero) =
        Val.cmp .Cne (.Vint i) (.Vint n) := by
      show Val.ofBool _ = Val.ofBool _; rw [int_cmp_xor_zero (.inr rfl)]
    rwa [E] at B2
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm32_correct (sym := sym) (ge := ge) (fn := fn) .Psltw .Psltiw
      (Val.cmp .Clt) m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1 n k rs h1
    exact ⟨rs1, A1, B1 ▸ .refl _, C1⟩
  · by_cases hm : Integers.Int.eq n (Integers.Int.repr Integers.Int.max_signed) = true
    · rw [if_pos hm]; obtain rfl := int_eq_true hm
      obtain ⟨rs1, A1, B1, C1⟩ := loadimm32_correct (sym := sym) (ge := ge) (fn := fn) rd
        Integers.Int.one k rs m
      refine ⟨rs1, A1, ?_, fun r h1 h2 _ => C1 r h1 h2⟩
      rw [B1]
      cases rs (.IR r1) <;> try exact .undef _
      rename_i i
      show Val.Lessdef (Val.ofBool _) _
      rw [int_cmp_le_max]; exact .refl _
    · rw [if_neg hm]
      obtain ⟨rs1, A1, B1, C1⟩ := opimm32_correct (sym := sym) (ge := ge) (fn := fn) .Psltw
        .Psltiw (Val.cmp .Clt) m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1
        (Integers.Int.add n Integers.Int.one) k rs h1
      refine ⟨rs1, A1, ?_, C1⟩
      rw [B1]
      cases rs (.IR r1) <;> try exact .undef _
      rename_i i
      show Val.Lessdef (Val.ofBool _) (Val.ofBool _)
      rw [int_cmp_le_succ i n (by simpa using hm)]; exact .refl _
  · exact DFL
  · exact DFL

/-- `Asmgenproof1.transl_condimm_int32u_correct` -/
theorem transl_condimm_int32u_correct (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int)
    (k : Code) (rs : Regset) (m : Mem) (h1 : r1 ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (translCondimmInt32u cmp rd r1 n k) rs m k rs' m ∧
      Val.Lessdef (Val.cmpu (Mem.validPointer m) cmp (rs (.IR r1)) (.Vint n)) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  have h1' : Preg.IR r1 ≠ .IR .X31 := fun e => h1 (Preg.IR.inj e)
  unfold translCondimmInt32u
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]; obtain rfl := int_eq_true hz
    obtain ⟨rs', A, B, C⟩ := transl_cond_int32u_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) .X0 k rs m
    exact ⟨rs', A, B ▸ .refl _, fun r h1 h2 _ => C r h1 h2⟩
  rw [if_neg hz]
  have DFL : ∃ rs', ExecStraight sym ge fn
      (loadimm32 Ireg.X31 n (translCondInt32u cmp rd r1 Ireg.X31 k)) rs m k rs' m ∧
      Val.Lessdef (Val.cmpu (Mem.validPointer m) cmp (rs (.IR r1)) (.Vint n)) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
    obtain ⟨rs1, A1, B1, C1⟩ := loadimm32_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
      (translCondInt32u cmp rd r1 Ireg.X31 k) rs m
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int32u_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) (.X .X31) k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_, fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h3]⟩
    simp only [get0w] at B2; rw [B2, B1, C1 _ (ir_ne_pc r1) h1']; exact .refl _
  cases cmp <;> dsimp only
  · exact DFL
  · exact DFL
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm32_correct (sym := sym) (ge := ge) (fn := fn) .Psltuw
      .Psltiuw (Val.cmpu (Mem.validPointer m) .Clt) m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      rd r1 n k rs h1
    exact ⟨rs1, A1, B1 ▸ .refl _, C1⟩
  · exact DFL
  · exact DFL
  · exact DFL

/-- `Asmgenproof1.transl_condimm_int64s_correct` -/
theorem transl_condimm_int64s_correct (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int64)
    (k : Code) (rs : Regset) (m : Mem) (h1 : r1 ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (translCondimmInt64s cmp rd r1 n k) rs m k rs' m ∧
      Val.Lessdef (Val.maketotal (Val.cmpl cmp (rs (.IR r1)) (.Vlong n))) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  have h1' : Preg.IR r1 ≠ .IR .X31 := fun e => h1 (Preg.IR.inj e)
  unfold translCondimmInt64s
  by_cases hz : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos hz]; obtain rfl := int64_eq_true hz
    obtain ⟨rs', A, B, C⟩ := transl_cond_int64s_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) .X0 k rs m
    exact ⟨rs', A, B, fun r h1 h2 _ => C r h1 h2⟩
  rw [if_neg hz]
  have DFL : ∃ rs', ExecStraight sym ge fn
      (loadimm64 Ireg.X31 n (translCondInt64s cmp rd r1 Ireg.X31 k)) rs m k rs' m ∧
      Val.Lessdef (Val.maketotal (Val.cmpl cmp (rs (.IR r1)) (.Vlong n))) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
    obtain ⟨rs1, A1, B1, C1⟩ := loadimm64_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
      (translCondInt64s cmp rd r1 Ireg.X31 k) rs m
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int64s_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) (.X .X31) k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_,
      fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h3 h3]⟩
    simp only [get0l] at B2; rwa [B1, C1 _ (ir_ne_pc r1) h1' h1'] at B2
  cases cmp <;> dsimp only
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm64_correct (sym := sym) (ge := ge) (fn := fn) .Pxorl .Pxoril
      Val.xorl m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1 n
      (translCondInt64s .Ceq rd rd .X0 k) rs h1
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int64s_correct (sym := sym) (ge := ge) (fn := fn)
      .Ceq rd (.X rd) .X0 k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_, fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h2 h3]⟩
    simp only [get0l] at B2; rw [B1] at B2
    revert B2; cases rs (.IR r1) <;> intro B2 <;> try exact .undef _
    rename_i i
    have E : Val.maketotal (Val.cmpl .Ceq (Val.xorl (.Vlong i) (.Vlong n))
        (.Vlong Integers.Int64.zero)) = Val.maketotal (Val.cmpl .Ceq (.Vlong i) (.Vlong n)) := by
      show Val.ofBool _ = Val.ofBool _; rw [int64_cmp_xor_zero (.inl rfl)]
    rwa [E] at B2
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm64_correct (sym := sym) (ge := ge) (fn := fn) .Pxorl .Pxoril
      Val.xorl m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1 n
      (translCondInt64s .Cne rd rd .X0 k) rs h1
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int64s_correct (sym := sym) (ge := ge) (fn := fn)
      .Cne rd (.X rd) .X0 k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_, fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h2 h3]⟩
    simp only [get0l] at B2; rw [B1] at B2
    revert B2; cases rs (.IR r1) <;> intro B2 <;> try exact .undef _
    rename_i i
    have E : Val.maketotal (Val.cmpl .Cne (Val.xorl (.Vlong i) (.Vlong n))
        (.Vlong Integers.Int64.zero)) = Val.maketotal (Val.cmpl .Cne (.Vlong i) (.Vlong n)) := by
      show Val.ofBool _ = Val.ofBool _; rw [int64_cmp_xor_zero (.inr rfl)]
    rwa [E] at B2
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm64_correct (sym := sym) (ge := ge) (fn := fn) .Psltl .Psltil
      (fun v1 v2 => Val.maketotal (Val.cmpl .Clt v1 v2)) m (fun _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl) rd r1 n k rs h1
    exact ⟨rs1, A1, B1 ▸ .refl _, C1⟩
  · by_cases hm : Integers.Int64.eq n (Integers.Int64.repr Integers.Int64.max_signed) = true
    · rw [if_pos hm]; obtain rfl := int64_eq_true hm
      obtain ⟨rs1, A1, B1, C1⟩ := loadimm32_correct (sym := sym) (ge := ge) (fn := fn) rd
        Integers.Int.one k rs m
      refine ⟨rs1, A1, ?_, fun r h1 h2 _ => C1 r h1 h2⟩
      rw [B1]
      cases rs (.IR r1) <;> try exact .undef _
      rename_i i
      show Val.Lessdef (Val.ofBool _) _
      rw [int64_cmp_le_max]; exact .refl _
    · rw [if_neg hm]
      obtain ⟨rs1, A1, B1, C1⟩ := opimm64_correct (sym := sym) (ge := ge) (fn := fn) .Psltl
        .Psltil (fun v1 v2 => Val.maketotal (Val.cmpl .Clt v1 v2)) m (fun _ _ _ _ => rfl)
        (fun _ _ _ _ => rfl) rd r1 (Integers.Int64.add n Integers.Int64.one) k rs h1
      refine ⟨rs1, A1, ?_, C1⟩
      rw [B1]
      cases rs (.IR r1) <;> try exact .undef _
      rename_i i
      show Val.Lessdef (Val.ofBool _) (Val.ofBool _)
      rw [int64_cmp_le_succ i n (by simpa using hm)]; exact .refl _
  · exact DFL
  · exact DFL

/-- `Asmgenproof1.transl_condimm_int64u_correct` -/
theorem transl_condimm_int64u_correct (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int64)
    (k : Code) (rs : Regset) (m : Mem) (h1 : r1 ≠ .X31) :
    ∃ rs', ExecStraight sym ge fn (translCondimmInt64u cmp rd r1 n k) rs m k rs' m ∧
      Val.Lessdef (Val.maketotal (Val.cmplu (Mem.validPointer m) cmp (rs (.IR r1)) (.Vlong n)))
        (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  have h1' : Preg.IR r1 ≠ .IR .X31 := fun e => h1 (Preg.IR.inj e)
  unfold translCondimmInt64u
  by_cases hz : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos hz]; obtain rfl := int64_eq_true hz
    obtain ⟨rs', A, B, C⟩ := transl_cond_int64u_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) .X0 k rs m
    exact ⟨rs', A, B ▸ .refl _, fun r h1 h2 _ => C r h1 h2⟩
  rw [if_neg hz]
  have DFL : ∃ rs', ExecStraight sym ge fn
      (loadimm64 Ireg.X31 n (translCondInt64u cmp rd r1 Ireg.X31 k)) rs m k rs' m ∧
      Val.Lessdef (Val.maketotal (Val.cmplu (Mem.validPointer m) cmp (rs (.IR r1)) (.Vlong n)))
        (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
    obtain ⟨rs1, A1, B1, C1⟩ := loadimm64_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
      (translCondInt64u cmp rd r1 Ireg.X31 k) rs m
    obtain ⟨rs2, A2, B2, C2⟩ := transl_cond_int64u_correct (sym := sym) (ge := ge) (fn := fn)
      cmp rd (.X r1) (.X .X31) k rs1 m
    refine ⟨rs2, exec_straight_trans A1 A2, ?_,
      fun r h1 h2 h3 => by rw [C2 r h1 h2, C1 r h1 h3 h3]⟩
    simp only [get0l] at B2; rw [B2, B1, C1 _ (ir_ne_pc r1) h1' h1']; exact .refl _
  cases cmp <;> dsimp only
  · exact DFL
  · exact DFL
  · obtain ⟨rs1, A1, B1, C1⟩ := opimm64_correct (sym := sym) (ge := ge) (fn := fn) .Psltul
      .Psltiul (fun v1 v2 => Val.maketotal (Val.cmplu (Mem.validPointer m) .Clt v1 v2)) m
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) rd r1 n k rs h1
    exact ⟨rs1, A1, B1 ▸ .refl _, C1⟩
  · exact DFL
  · exact DFL
  · exact DFL

/-- `branch_on_X31` with the two branch instructions exchanged. -/
theorem branch_on_X31_neg (normal : Bool) (lbl : Label) (rs : Regset) (m : Mem) (b : Bool)
    (h : rs (.IR .X31) = Val.ofBool (xor normal b)) :
    execInstr sym ge fn (if normal then .Pbeqw Ireg.X31 .X0 lbl else .Pbnew Ireg.X31 .X0 lbl) rs m =
      evalBranch fn lbl rs m (some b) := by
  cases normal <;> cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;>
    (show evalBranch fn lbl rs m (Val.cmpu_bool _ _ (rs (.IR .X31)) _) = _) <;>
    rw [h] <;> rfl

/-- `Asmgenproof1.transl_cbranch_correct_1` -/
theorem transl_cbranch_correct_1 {cond : Condition} {args : List Mreg} {lbl : Label}
    {k c : Code} {m : Mem} {ms : Mach.Regset} {b : Bool} {sp : Val} {rs : Regset} {m' : Mem}
    (TRANSL : translCbranch cond args lbl k = .OK c)
    (EVAL : evalCondition cond (args.map ms) m = some b)
    (AG : Agree ms sp rs) (MEXT : Mem.Extends m m') :
    ∃ rs' insn, ExecStraightOpt sym ge fn c rs m' (insn :: k) rs' m' ∧
      execInstr sym ge fn insn rs' m' = evalBranch fn lbl rs' m' (some b) ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  have EVAL' := evalCondition_lessdef (preg_vals AG args) MEXT EVAL
  clear EVAL MEXT AG
  revert TRANSL EVAL'
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;> intro TRANSL EVAL' <;>
    simp only [translCbranch, res_bind_OK, res_pure_OK] at TRANSL <;> (try (cases TRANSL; done)) <;>
    simp only [evalCondition, List.map] at EVAL'
  · -- Ccomp
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1, ireg_of_eq hr2] at EVAL'
    exact ⟨rs, _, .refl _ _ _, transl_cbranch_int32s_correct _ _ _ _ _ _ _ EVAL', fun _ _ _ => rfl⟩
  · -- Ccompu
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1, ireg_of_eq hr2] at EVAL'
    exact ⟨rs, _, .refl _ _ _, transl_cbranch_int32u_correct _ _ _ _ _ _ _ EVAL', fun _ _ _ => rfl⟩
  · -- Ccompimm
    obtain ⟨r1, hr1, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1] at EVAL'
    rename_i c0 n
    by_cases hn : Integers.Int.eq n Integers.Int.zero = true
    · rw [if_pos hn]; obtain rfl := int_eq_true hn
      exact ⟨rs, _, .refl _ _ _, transl_cbranch_int32s_correct _ _ _ _ _ _ _ EVAL',
        fun _ _ _ => rfl⟩
    · rw [if_neg hn]
      obtain ⟨rs1, A, B, C⟩ := loadimm32_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
        (translCbranchInt32s c0 r1 Ireg.X31 lbl :: k) rs m'
      refine ⟨rs1, _, .intro _ _ _ _ _ _ A, transl_cbranch_int32s_correct _ _ _ _ _ _ _ ?_,
        fun r h1 h2 => C r h1 h2⟩
      show Val.cmp_bool _ (rs1 (.IR r1)) (rs1 (.IR .X31)) = _
      rw [B, C _ (ir_ne_pc r1) (ireg_of_not_X31 hr1)]; exact EVAL'
  · -- Ccompuimm
    obtain ⟨r1, hr1, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1] at EVAL'
    rename_i c0 n
    by_cases hn : Integers.Int.eq n Integers.Int.zero = true
    · rw [if_pos hn]; obtain rfl := int_eq_true hn
      exact ⟨rs, _, .refl _ _ _, transl_cbranch_int32u_correct _ _ _ _ _ _ _ EVAL',
        fun _ _ _ => rfl⟩
    · rw [if_neg hn]
      obtain ⟨rs1, A, B, C⟩ := loadimm32_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
        (translCbranchInt32u c0 r1 Ireg.X31 lbl :: k) rs m'
      refine ⟨rs1, _, .intro _ _ _ _ _ _ A, transl_cbranch_int32u_correct _ _ _ _ _ _ _ ?_,
        fun r h1 h2 => C r h1 h2⟩
      show Val.cmpu_bool _ _ (rs1 (.IR r1)) (rs1 (.IR .X31)) = _
      rw [B, C _ (ir_ne_pc r1) (ireg_of_not_X31 hr1)]; exact EVAL'
  · -- Ccompl
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1, ireg_of_eq hr2] at EVAL'
    exact ⟨rs, _, .refl _ _ _, transl_cbranch_int64s_correct _ _ _ _ _ _ _ EVAL', fun _ _ _ => rfl⟩
  · -- Ccomplu
    obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1, ireg_of_eq hr2] at EVAL'
    exact ⟨rs, _, .refl _ _ _, transl_cbranch_int64u_correct _ _ _ _ _ _ _ EVAL', fun _ _ _ => rfl⟩
  · -- Ccomplimm
    obtain ⟨r1, hr1, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1] at EVAL'
    rename_i c0 n
    by_cases hn : Integers.Int64.eq n Integers.Int64.zero = true
    · rw [if_pos hn]; obtain rfl := int64_eq_true hn
      exact ⟨rs, _, .refl _ _ _, transl_cbranch_int64s_correct _ _ _ _ _ _ _ EVAL',
        fun _ _ _ => rfl⟩
    · rw [if_neg hn]
      obtain ⟨rs1, A, B, C⟩ := loadimm64_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
        (translCbranchInt64s c0 r1 Ireg.X31 lbl :: k) rs m'
      refine ⟨rs1, _, .intro _ _ _ _ _ _ A, transl_cbranch_int64s_correct _ _ _ _ _ _ _ ?_,
        fun r h1 h2 => C r h1 h2 h2⟩
      show Val.cmpl_bool _ (rs1 (.IR r1)) (rs1 (.IR .X31)) = _
      rw [B, C _ (ir_ne_pc r1) (ireg_of_not_X31 hr1) (ireg_of_not_X31 hr1)]; exact EVAL'
  · -- Ccompluimm
    obtain ⟨r1, hr1, rfl⟩ := TRANSL
    rw [ireg_of_eq hr1] at EVAL'
    rename_i c0 n
    by_cases hn : Integers.Int64.eq n Integers.Int64.zero = true
    · rw [if_pos hn]; obtain rfl := int64_eq_true hn
      exact ⟨rs, _, .refl _ _ _, transl_cbranch_int64u_correct _ _ _ _ _ _ _ EVAL',
        fun _ _ _ => rfl⟩
    · rw [if_neg hn]
      obtain ⟨rs1, A, B, C⟩ := loadimm64_correct (sym := sym) (ge := ge) (fn := fn) Ireg.X31 n
        (translCbranchInt64u c0 r1 Ireg.X31 lbl :: k) rs m'
      refine ⟨rs1, _, .intro _ _ _ _ _ _ A, transl_cbranch_int64u_correct _ _ _ _ _ _ _ ?_,
        fun r h1 h2 => C r h1 h2 h2⟩
      show Val.cmplu_bool _ _ (rs1 (.IR r1)) (rs1 (.IR .X31)) = _
      rw [B, C _ (ir_ne_pc r1) (ireg_of_not_X31 hr1) (ireg_of_not_X31 hr1)]; exact EVAL'
  · -- Ccompf
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TRANSL
    rw [freg_of_eq hr1, freg_of_eq hr2] at EVAL'
    rename_i c0
    rcases TC : translCondFloat c0 .X31 r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    have V : (if normal then Val.cmpf c0 (rs (.FR r1)) (rs (.FR r2))
        else Val.notbool (Val.cmpf c0 (rs (.FR r1)) (rs (.FR r2)))) = Val.ofBool (normal == b) := by
      unfold Val.cmpf; rw [EVAL']; cases normal <;> cases b <;> rfl
    exact ⟨_, _, .intro _ _ _ _ _ _ (exec_straight_set (ir_ne_pc .X31)
        (transl_cond_float_correct rs m' c0 .X31 r1 r2 insn normal _ TC rfl)),
      branch_on_X31 normal lbl _ m' b (by rw [nextinstr_set_same _ _ (ir_ne_pc .X31), V]),
      fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
  · -- Cnotcompf
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TRANSL
    rw [freg_of_eq hr1, freg_of_eq hr2] at EVAL'
    rename_i c0
    rcases TC : translCondFloat c0 .X31 r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    have EVAL'' : Val.cmpf_bool c0 (rs (.FR r1)) (rs (.FR r2)) = some (!b) := by
      revert EVAL'; cases Val.cmpf_bool c0 (rs (.FR r1)) (rs (.FR r2)) <;> simp
    have V : (if normal then Val.cmpf c0 (rs (.FR r1)) (rs (.FR r2))
        else Val.notbool (Val.cmpf c0 (rs (.FR r1)) (rs (.FR r2)))) = Val.ofBool (xor normal b) := by
      unfold Val.cmpf; rw [EVAL'']; cases normal <;> cases b <;> rfl
    exact ⟨_, _, .intro _ _ _ _ _ _ (exec_straight_set (ir_ne_pc .X31)
        (transl_cond_float_correct rs m' c0 .X31 r1 r2 insn normal _ TC rfl)),
      branch_on_X31_neg normal lbl _ m' b (by rw [nextinstr_set_same _ _ (ir_ne_pc .X31), V]),
      fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
  · -- Ccompfs
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TRANSL
    rw [freg_of_eq hr1, freg_of_eq hr2] at EVAL'
    rename_i c0
    rcases TC : translCondSingle c0 .X31 r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    have V : (if normal then Val.cmpfs c0 (rs (.FR r1)) (rs (.FR r2))
        else Val.notbool (Val.cmpfs c0 (rs (.FR r1)) (rs (.FR r2)))) = Val.ofBool (normal == b) := by
      unfold Val.cmpfs; rw [EVAL']; cases normal <;> cases b <;> rfl
    exact ⟨_, _, .intro _ _ _ _ _ _ (exec_straight_set (ir_ne_pc .X31)
        (transl_cond_single_correct rs m' c0 .X31 r1 r2 insn normal _ TC rfl)),
      branch_on_X31 normal lbl _ m' b (by rw [nextinstr_set_same _ _ (ir_ne_pc .X31), V]),
      fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
  · -- Cnotcompfs
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TRANSL
    rw [freg_of_eq hr1, freg_of_eq hr2] at EVAL'
    rename_i c0
    rcases TC : translCondSingle c0 .X31 r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    have EVAL'' : Val.cmpfs_bool c0 (rs (.FR r1)) (rs (.FR r2)) = some (!b) := by
      revert EVAL'; cases Val.cmpfs_bool c0 (rs (.FR r1)) (rs (.FR r2)) <;> simp
    have V : (if normal then Val.cmpfs c0 (rs (.FR r1)) (rs (.FR r2))
        else Val.notbool (Val.cmpfs c0 (rs (.FR r1)) (rs (.FR r2)))) = Val.ofBool (xor normal b) := by
      unfold Val.cmpfs; rw [EVAL'']; cases normal <;> cases b <;> rfl
    exact ⟨_, _, .intro _ _ _ _ _ _ (exec_straight_set (ir_ne_pc .X31)
        (transl_cond_single_correct rs m' c0 .X31 r1 r2 insn normal _ TC rfl)),
      branch_on_X31_neg normal lbl _ m' b (by rw [nextinstr_set_same _ _ (ir_ne_pc .X31), V]),
      fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩

/-- `Asmgenproof1.transl_cbranch_correct_true` -/
theorem transl_cbranch_correct_true {cond : Condition} {args : List Mreg} {lbl : Label}
    {k c : Code} {m : Mem} {ms : Mach.Regset} {sp : Val} {rs : Regset} {m' : Mem}
    (TRANSL : translCbranch cond args lbl k = .OK c)
    (EVAL : evalCondition cond (args.map ms) m = some true)
    (AG : Agree ms sp rs) (MEXT : Mem.Extends m m') :
    ∃ rs' insn, ExecStraightOpt sym ge fn c rs m' (insn :: k) rs' m' ∧
      execInstr sym ge fn insn rs' m' = gotoLabel fn lbl rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r :=
  transl_cbranch_correct_1 TRANSL EVAL AG MEXT

/-- `Asmgenproof1.transl_cbranch_correct_false` -/
theorem transl_cbranch_correct_false {cond : Condition} {args : List Mreg} {lbl : Label}
    {k c : Code} {m : Mem} {ms : Mach.Regset} {sp : Val} {rs : Regset} {m' : Mem}
    (TRANSL : translCbranch cond args lbl k = .OK c)
    (EVAL : evalCondition cond (args.map ms) m = some false)
    (AG : Agree ms sp rs) (MEXT : Mem.Extends m m') :
    ∃ rs', ExecStraight sym ge fn c rs m' k rs' m' ∧
      ∀ r, r ≠ .PC → r ≠ .IR .X31 → rs' r = rs r := by
  obtain ⟨rs', insn, A, B, C⟩ := transl_cbranch_correct_1 (sym := sym) (ge := ge) (fn := fn)
    TRANSL EVAL AG MEXT
  exact ⟨nextinstr rs', exec_straight_opt_right A (.one _ _ _ _ _ _ B (nextinstr_pc _)),
    fun r h1 h2 => by rw [nextinstr_inv _ h1, C r h1 h2]⟩

theorem lessdef_xor_notbool (ob : Option Bool) :
    Val.Lessdef (Val.ofOptbool ob) (Val.xor (Val.notbool (Val.ofOptbool ob)) (.Vint Integers.Int.one)) := by
  rcases ob with _ | ⟨_ | _⟩
  · exact .undef _
  · exact .refl _
  · exact .refl _

theorem lessdef_notbool_map (ob : Option Bool) :
    Val.Lessdef (Val.ofOptbool (ob.map (!·))) (Val.notbool (Val.ofOptbool ob)) := by
  rcases ob with _ | ⟨_ | _⟩
  · exact .undef _
  · exact .refl _
  · exact .refl _

/-- `Asmgenproof1.transl_cond_op_correct` -/
theorem transl_cond_op_correct {cond : Condition} {rd : Ireg} {args : List Mreg} {k c : Code}
    (rs : Regset) (m : Mem) (TR : translCondOp cond rd args k = .OK c) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧
      Val.Lessdef (Val.ofOptbool (evalCondition cond ((args.map pregOf).map rs) m)) (rs' (.IR rd)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r := by
  revert TR
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;> intro TR <;>
    simp only [translCondOp, res_bind_OK, res_pure_OK] at TR <;> (try (cases TR; done)) <;>
    simp only [evalCondition, List.map]
  · obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TR
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    obtain ⟨rs', A, B, C⟩ := transl_cond_int32s_correct (sym := sym) (ge := ge) (fn := fn)
      _ rd (.X r1) (.X r2) k rs m
    exact ⟨rs', A, B, fun r h1 h2 _ => C r h1 h2⟩
  · obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TR
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    obtain ⟨rs', A, B, C⟩ := transl_cond_int32u_correct (sym := sym) (ge := ge) (fn := fn)
      _ rd (.X r1) (.X r2) k rs m
    exact ⟨rs', A, B ▸ .refl _, fun r h1 h2 _ => C r h1 h2⟩
  · obtain ⟨r1, hr1, rfl⟩ := TR
    rw [ireg_of_eq hr1]
    exact transl_condimm_int32s_correct _ rd r1 _ k rs m (ireg_of_not_X31' hr1)
  · obtain ⟨r1, hr1, rfl⟩ := TR
    rw [ireg_of_eq hr1]
    exact transl_condimm_int32u_correct _ rd r1 _ k rs m (ireg_of_not_X31' hr1)
  · obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TR
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    obtain ⟨rs', A, B, C⟩ := transl_cond_int64s_correct (sym := sym) (ge := ge) (fn := fn)
      _ rd (.X r1) (.X r2) k rs m
    rw [maketotal_cmpl] at B
    exact ⟨rs', A, B, fun r h1 h2 _ => C r h1 h2⟩
  · obtain ⟨r1, hr1, r2, hr2, rfl⟩ := TR
    rw [ireg_of_eq hr1, ireg_of_eq hr2]
    obtain ⟨rs', A, B, C⟩ := transl_cond_int64u_correct (sym := sym) (ge := ge) (fn := fn)
      _ rd (.X r1) (.X r2) k rs m
    rw [maketotal_cmplu] at B
    exact ⟨rs', A, B ▸ .refl _, fun r h1 h2 _ => C r h1 h2⟩
  · obtain ⟨r1, hr1, rfl⟩ := TR
    rw [ireg_of_eq hr1]
    obtain ⟨rs', A, B, C⟩ := transl_condimm_int64s_correct (sym := sym) (ge := ge) (fn := fn)
      _ rd r1 _ k rs m (ireg_of_not_X31' hr1)
    rw [maketotal_cmpl] at B
    exact ⟨rs', A, B, C⟩
  · obtain ⟨r1, hr1, rfl⟩ := TR
    rw [ireg_of_eq hr1]
    obtain ⟨rs', A, B, C⟩ := transl_condimm_int64u_correct (sym := sym) (ge := ge) (fn := fn)
      _ rd r1 _ k rs m (ireg_of_not_X31' hr1)
    rw [maketotal_cmplu] at B
    exact ⟨rs', A, B, C⟩
  · -- Ccompf
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TR
    rw [freg_of_eq hr1, freg_of_eq hr2]
    rename_i c0
    rcases TC : translCondFloat c0 rd r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    cases normal
    · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_float_correct rs m c0 rd r1 r2 insn false _ TC rfl)
      refine ⟨rs', A, ?_, fun r h1 h2 _ => C r h1 h2⟩
      rw [B]; exact lessdef_xor_notbool _
    · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_float_correct rs m c0 rd r1 r2 insn true _ TC rfl)
      exact ⟨rs', A, B ▸ .refl _, fun r h1 h2 _ => C r h1 h2⟩
  · -- Cnotcompf
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TR
    rw [freg_of_eq hr1, freg_of_eq hr2]
    rename_i c0
    rcases TC : translCondFloat c0 rd r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    cases normal
    · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_float_correct rs m c0 rd r1 r2 insn false _ TC rfl)
      refine ⟨rs', A, ?_, fun r h1 h2 _ => C r h1 h2⟩
      rw [B]; exact lessdef_notbool_map _
    · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_float_correct rs m c0 rd r1 r2 insn true _ TC rfl)
      refine ⟨rs', A, ?_, fun r h1 h2 _ => C r h1 h2⟩
      rw [B]; simp only [if_true]; unfold Val.cmpf; rw [xor_ofOptbool_one]; exact .refl _
  · -- Ccompfs
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TR
    rw [freg_of_eq hr1, freg_of_eq hr2]
    rename_i c0
    rcases TC : translCondSingle c0 rd r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    cases normal
    · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_single_correct rs m c0 rd r1 r2 insn false _ TC rfl)
      refine ⟨rs', A, ?_, fun r h1 h2 _ => C r h1 h2⟩
      rw [B]; exact lessdef_xor_notbool _
    · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_single_correct rs m c0 rd r1 r2 insn true _ TC rfl)
      exact ⟨rs', A, B ▸ .refl _, fun r h1 h2 _ => C r h1 h2⟩
  · -- Cnotcompfs
    obtain ⟨r1, hr1, r2, hr2, H⟩ := TR
    rw [freg_of_eq hr1, freg_of_eq hr2]
    rename_i c0
    rcases TC : translCondSingle c0 rd r1 r2 with ⟨insn, normal⟩
    rw [TC] at H; subst H
    cases normal
    · obtain ⟨rs', A, B, C⟩ := straight_one (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_single_correct rs m c0 rd r1 r2 insn false _ TC rfl)
      refine ⟨rs', A, ?_, fun r h1 h2 _ => C r h1 h2⟩
      rw [B]; exact lessdef_notbool_map _
    · obtain ⟨rs', A, B, C⟩ := straight_two_xor (sym := sym) (ge := ge) (fn := fn) (k := k)
        (transl_cond_single_correct rs m c0 rd r1 r2 insn true _ TC rfl)
      refine ⟨rs', A, ?_, fun r h1 h2 _ => C r h1 h2⟩
      rw [B]; simp only [if_true]; unfold Val.cmpfs; rw [xor_ofOptbool_one]; exact .refl _

end CONSTRUCTORS

end Asmgenproof1
end RiscV
end CC
