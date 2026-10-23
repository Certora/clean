/-
  Correctness proof for RISC-V code generation: auxiliary results, part 3 —
  port of `transl_op_correct` from `riscV/Asmgenproof1.v` (with the remark
  `cast32unsigned_from_cast32signed`).

  Differences from Rocq: the `ArgsInv`, `SimplEval` and `TranslOpSimpl`
  tactics become a case analysis on the operation and its arguments, the
  rewriting of `ireg_of`/`freg_of` facts into `preg_of` equations, and a
  generic closing step for the operations translated to a single
  instruction; the remaining cases are handled one by one.  The OCaml
  parameter `symbol_is_relocatable` is a field of the explicit
  `Asmgen.Options` argument `o`.
-/
import CCLib.riscV.Asmgenproof1Cond

namespace CC
namespace RiscV
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1 Op

theorem iregOf_OK {r : Mreg} {x : Ireg} : iregOf r = .OK x ↔ pregOf r = .IR x := by
  unfold iregOf; split <;> simp_all

theorem fregOf_OK {r : Mreg} {x : Freg} : fregOf r = .OK x ↔ pregOf r = .FR x := by
  unfold fregOf; split <;> simp_all

theorem data_ne_pc {r : Preg} (h : dataPreg r = true) : r ≠ .PC := data_diff h rfl
theorem data_ne_x31 {r : Preg} (h : dataPreg r = true) : r ≠ .IR .X31 := data_diff h rfl

/-- `Asmgenproof1.cast32unsigned_from_cast32signed` -/
theorem cast32unsigned_from_cast32signed (i : Integers.Int) :
    Integers.Int64.repr (Integers.Int.unsigned i) =
      Integers.Int64.zero_ext 32 (Integers.Int64.repr (Integers.Int.signed i)) := by
  simp only [Integers.Int64.repr, Integers.Int.unsigned, Integers.Int.signed,
    Integers.Int64.zero_ext, Integers.MI.repr, Integers.MI.unsigned, Integers.MI.signed,
    Integers.MI.zero_ext]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, show BitVec.ofInt 64 i.toInt = i.signExtend 64 from rfl, if_neg (by decide)]
  bv_decide

/-! ### Value-level facts used by `transl_op_correct` -/

theorem lessdef_cast8 (a : Val) :
    Val.Lessdef (Val.signExt 8 a)
      (Val.shr (Val.shl a (.Vint (Integers.Int.repr 24))) (.Vint (Integers.Int.repr 24))) := by
  cases a <;> try exact .undef _
  rename_i i
  simp only [Val.signExt, Val.shl, Val.shr, show Integers.Int.ltu (Integers.Int.repr 24) Integers.Int.iwordsize = true by decide, if_true]
  have : Integers.Int.sign_ext 8 i = Integers.Int.shr (Integers.Int.shl i (Integers.Int.repr 24)) (Integers.Int.repr 24) := by
    rw [show Integers.Int.repr 24 = 24#32 by decide]
    simp only [Integers.Int.sign_ext, Integers.Int.shr, Integers.Int.shl, Integers.MI.sign_ext, Integers.MI.shr, Integers.MI.shl]
    simp
  rw [this]; exact .refl _
theorem shrlu_shll_32 (x : Integers.Int64) :
    Val.shrlu (Val.shll (.Vlong x) (.Vint (Integers.Int.repr 32))) (.Vint (Integers.Int.repr 32)) =
      .Vlong (Integers.Int64.shru (Integers.Int64.shl x (Integers.Int64.repr 32))
        (Integers.Int64.repr 32)) := rfl

theorem lessdef_cast32u (a : Val) :
    Val.Lessdef (Val.longofintu a)
      (Val.shrlu (Val.shll (Val.longofint a) (.Vint (Integers.Int.repr 32))) (.Vint (Integers.Int.repr 32))) := by
  cases a <;> try exact .undef _
  rename_i i
  show Val.Lessdef _ (Val.shrlu (Val.shll (.Vlong _) _) _)
  rw [shrlu_shll_32]
  show Val.Lessdef (.Vlong _) _
  have : Integers.Int64.repr (Integers.Int.unsigned i) = Integers.Int64.shru (Integers.Int64.shl (Integers.Int64.repr (Integers.Int.signed i)) (Integers.Int64.repr 32)) (Integers.Int64.repr 32) := by
    rw [show Integers.Int64.repr 32 = 32#64 by decide]
    simp only [Integers.Int64.repr, Integers.Int.unsigned, Integers.Int.signed, Integers.Int64.shru, Integers.Int64.shl, Integers.MI.repr, Integers.MI.unsigned, Integers.MI.signed, Integers.MI.shru, Integers.MI.shl]
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, show BitVec.ofInt 64 i.toInt = i.signExtend 64 from rfl]
    simp only [show (32#64).toNat = 32 from rfl]
    bv_decide
  rw [this]; exact .refl _
theorem lessdef_neg (a : Val) : Val.Lessdef (Val.neg a) (Val.sub (.Vint Integers.Int.zero) a) := by
  cases a <;> try exact .undef _
  rename_i n
  simp only [Val.neg, Val.sub, Integers.Int.neg, Integers.Int.sub, Integers.MI.neg, Integers.MI.sub, Integers.Int.zero, Integers.MI.zero]
  rw [show (0 : BitVec 32) - n = -n from BitVec.zero_sub n]; exact .refl _
theorem lessdef_negl (a : Val) : Val.Lessdef (Val.negl a) (Val.subl (.Vlong Integers.Int64.zero) a) := by
  cases a <;> try exact .undef _
  rename_i n
  simp only [Val.negl, Val.subl, Integers.Int64.neg, Integers.Int64.sub, Integers.MI.neg, Integers.MI.sub, Integers.Int64.zero, Integers.MI.zero]
  rw [show (0 : BitVec 64) - n = -n from BitVec.zero_sub n]; exact .refl _

theorem lessdef_cast16 (a : Val) :
    Val.Lessdef (Val.signExt 16 a)
      (Val.shr (Val.shl a (.Vint (Integers.Int.repr 16))) (.Vint (Integers.Int.repr 16))) := by
  cases a <;> try exact .undef _
  rename_i i
  simp only [Val.signExt, Val.shl, Val.shr, show Integers.Int.ltu (Integers.Int.repr 16) Integers.Int.iwordsize = true by decide, if_true]
  have : Integers.Int.sign_ext 16 i = Integers.Int.shr (Integers.Int.shl i (Integers.Int.repr 16)) (Integers.Int.repr 16) := by
    rw [show Integers.Int.repr 16 = 16#32 by decide]
    simp only [Integers.Int.sign_ext, Integers.Int.shr, Integers.Int.shl, Integers.MI.sign_ext, Integers.MI.shr, Integers.MI.shl]
    simp
  rw [this]; exact .refl _

theorem ir_not_X31 {a : Mreg} {r : Ireg} (h : pregOf a = .IR r) : r ≠ .X31 :=
  fun e => preg_of_not_X31 a (h.trans (congrArg Preg.IR e))

section CONSTRUCTORS
variable {sym : HalfSplit} {ge : Asm.CGenv} {fn : Asm.Function}

/-- Closing step: a code sequence computing `v'` into `rd`, preserving every
register other than `PC`, `rd` and `X31`. -/
theorem close_X31 {c k : Code} {rs : Regset} {m : Mem} {rd : Ireg} {v v' : Val}
    {P : Preg → Prop}
    (H : ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' (.IR rd) = v' ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r)
    (hv : Val.Lessdef v v') :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' (.IR rd)) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → P r → rs' r = rs r := by
  obtain ⟨rs', A, B, C⟩ := H
  exact ⟨rs', A, B ▸ hv, fun r hd hne _ => C r (data_ne_pc hd) hne (data_ne_x31 hd)⟩

/-- Closing step: as `close_X31`, without clobbering `X31`. -/
theorem close_noX31 {c k : Code} {rs : Regset} {m : Mem} {rd : Ireg} {v v' : Val}
    {P : Preg → Prop}
    (H : ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ rs' (.IR rd) = v' ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r)
    (hv : Val.Lessdef v v') :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' (.IR rd)) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → P r → rs' r = rs r := by
  obtain ⟨rs', A, B, C⟩ := H
  exact ⟨rs', A, B ▸ hv, fun r hd hne _ => C r (data_ne_pc hd) hne⟩

/-- Two instructions, both writing `rd`. -/
theorem straight_two_rd {i1 i2 : Instruction} {k : Code} {rs : Regset} {m : Mem} {rd : Ireg}
    {v1 v2 : Val}
    (h1 : execInstr sym ge fn i1 rs m = .Next (nextinstr (rs.set (.IR rd) v1)) m)
    (h2 : execInstr sym ge fn i2 (nextinstr (rs.set (.IR rd) v1)) m =
      .Next (nextinstr ((nextinstr (rs.set (.IR rd) v1)).set (.IR rd) v2)) m) :
    ∃ rs', ExecStraight sym ge fn (i1 :: i2 :: k) rs m k rs' m ∧ rs' (.IR rd) = v2 ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r :=
  ⟨_, .step _ _ _ _ _ _ _ _ _ h1 (nextinstr_set_pc _ _ (ir_ne_pc rd))
      (exec_straight_set (ir_ne_pc rd) h2),
    nextinstr_set_same _ _ (ir_ne_pc rd),
    fun _ h1 h2 => by rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h2]⟩

/-- Three instructions, all writing `rd`. -/
theorem straight_three_rd {i1 i2 i3 : Instruction} {k : Code} {rs : Regset} {m : Mem}
    {rd : Ireg} {v1 v2 v3 : Val}
    (h1 : execInstr sym ge fn i1 rs m = .Next (nextinstr (rs.set (.IR rd) v1)) m)
    (h2 : execInstr sym ge fn i2 (nextinstr (rs.set (.IR rd) v1)) m =
      .Next (nextinstr ((nextinstr (rs.set (.IR rd) v1)).set (.IR rd) v2)) m)
    (h3 : execInstr sym ge fn i3 (nextinstr ((nextinstr (rs.set (.IR rd) v1)).set (.IR rd) v2)) m =
      .Next (nextinstr ((nextinstr ((nextinstr (rs.set (.IR rd) v1)).set (.IR rd) v2)).set
        (.IR rd) v3)) m) :
    ∃ rs', ExecStraight sym ge fn (i1 :: i2 :: i3 :: k) rs m k rs' m ∧ rs' (.IR rd) = v3 ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r :=
  ⟨_, .step _ _ _ _ _ _ _ _ _ h1 (nextinstr_set_pc _ _ (ir_ne_pc rd))
      (.step _ _ _ _ _ _ _ _ _ h2 (nextinstr_set_pc _ _ (ir_ne_pc rd))
        (exec_straight_set (ir_ne_pc rd) h3)),
    nextinstr_set_same _ _ (ir_ne_pc rd),
    fun _ h1 h2 => by
      rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h2,
        nextinstr_set_other _ _ h1 h2]⟩

/-- The `x31`-based sequence used for `shrx`/`shrxl`: four instructions writing
`X31` three times and then `rd`. -/
theorem straight_four_X31 {i1 i2 i3 i4 : Instruction} {k : Code} {rs : Regset} {m : Mem}
    {rd : Ireg} {v1 v2 v3 v4 : Val}
    (h1 : execInstr sym ge fn i1 rs m = .Next (nextinstr (rs.set (.IR .X31) v1)) m)
    (h2 : execInstr sym ge fn i2 (nextinstr (rs.set (.IR .X31) v1)) m =
      .Next (nextinstr ((nextinstr (rs.set (.IR .X31) v1)).set (.IR .X31) v2)) m)
    (h3 : execInstr sym ge fn i3 (nextinstr ((nextinstr (rs.set (.IR .X31) v1)).set (.IR .X31) v2)) m =
      .Next (nextinstr ((nextinstr ((nextinstr (rs.set (.IR .X31) v1)).set (.IR .X31) v2)).set
        (.IR .X31) v3)) m)
    (h4 : execInstr sym ge fn i4 (nextinstr ((nextinstr ((nextinstr (rs.set (.IR .X31) v1)).set
        (.IR .X31) v2)).set (.IR .X31) v3)) m =
      .Next (nextinstr ((nextinstr ((nextinstr ((nextinstr (rs.set (.IR .X31) v1)).set
        (.IR .X31) v2)).set (.IR .X31) v3)).set (.IR rd) v4)) m) :
    ∃ rs', ExecStraight sym ge fn (i1 :: i2 :: i3 :: i4 :: k) rs m k rs' m ∧ rs' (.IR rd) = v4 ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → r ≠ .IR .X31 → rs' r = rs r :=
  ⟨_, .step _ _ _ _ _ _ _ _ _ h1 (nextinstr_set_pc _ _ (ir_ne_pc _))
      (.step _ _ _ _ _ _ _ _ _ h2 (nextinstr_set_pc _ _ (ir_ne_pc _))
        (.step _ _ _ _ _ _ _ _ _ h3 (nextinstr_set_pc _ _ (ir_ne_pc _))
          (exec_straight_set (ir_ne_pc rd) h4))),
    nextinstr_set_same _ _ (ir_ne_pc rd),
    fun _ h1 h2 h3 => by
      rw [nextinstr_set_other _ _ h1 h2, nextinstr_set_other _ _ h1 h3,
        nextinstr_set_other _ _ h1 h3, nextinstr_set_other _ _ h1 h3]⟩

theorem select_same_lessdef (ob : Option Bool) (v : Val) (ty : ATyp) :
    Val.Lessdef (Val.select ob v v ty) v := by
  cases ob with
  | none => exact .undef _
  | some b => simp only [Val.select, ite_self]; exact Val.lessdef_normalize _ _

/-- The value computed by `Pcsel` after a condition evaluated into `x`. -/
theorem csel_lessdef {ob : Option Bool} {x a b : Val} (ty : ATyp)
    (B : Val.Lessdef (Val.ofOptbool ob) x) :
    Val.Lessdef (Val.select ob a b ty)
      (if x = Val.Vone then a else if x = Val.Vzero then b else .Vundef) := by
  cases ob with
  | none => exact .undef _
  | some bb =>
    cases bb <;> cases B <;>
      simp [Val.select, Val.ofOptbool, Val.ofBool, Val.Vtrue, Val.Vfalse, Val.Vone,
        Val.Vzero] <;> exact Val.lessdef_normalize _ _

set_option maxHeartbeats 4000000 in
/-- `Asmgenproof1.transl_op_correct` -/
theorem transl_op_correct (o : Options) {op : Operation} {args : List Mreg} {res : Mreg}
    {k c : Code} (rs : Regset) (m : Mem) {v : Val}
    (TR : translOp o op args res k = .OK c)
    (EV : evalOperation ge (rs (.IR SP)) op ((args.map pregOf).map rs) m = some v) :
    ∃ rs', ExecStraight sym ge fn c rs m k rs' m ∧ Val.Lessdef v (rs' (pregOf res)) ∧
      ∀ r, dataPreg r = true → r ≠ pregOf res → PregNotin r (destroyedByOp op) → rs' r = rs r := by
  revert TR EV
  cases op <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;> intro TR EV <;>
    unfold translOp at TR <;> dsimp only at TR <;>
    (try simp only [res_bind_OK, res_pure_OK, iregOf_OK, fregOf_OK] at TR) <;>
    (try (cases TR; done)) <;>
    (try simp only [List.map] at EV) <;> (try (unfold evalOperation at EV; dsimp only at EV))
  all_goals (repeat (obtain ⟨_, h, TR⟩ := TR; simp only [h] at EV ⊢))
  all_goals (try subst TR)
  all_goals (try (first
    | (cases EV
       exact ⟨_, exec_straight_set (by simp) rfl,
         by rw [nextinstr_set_same _ _ (by simp)]; exact .refl _,
         fun r hd hne _ => nextinstr_set_other _ _ (data_ne_pc hd) hne⟩)
    | exact ⟨_, exec_straight_set (by simp) rfl,
         by rw [nextinstr_set_same _ _ (by simp)]; simp only [get0w, get0l, EV, Val.maketotal]
            exact .refl _,
         fun r hd hne _ => nextinstr_set_other _ _ (data_ne_pc hd) hne⟩))
  case Ointconst.nil =>
    cases EV
    obtain ⟨rs', A, B, C⟩ := loadimm32_correct (sym := sym) (ge := ge) (fn := fn) _ _ k rs m
    exact close_noX31 ⟨rs', A, B, C⟩ (.refl _)
  case Olongconst.nil =>
    cases EV
    exact close_X31 (loadimm64_correct _ _ k rs m) (.refl _)
  case Oaddrstack.nil =>
    cases EV
    obtain ⟨rs', A, B, C⟩ := addptrofs_correct (sym := sym) (ge := ge) (fn := fn) _ SP _ k rs m
      (by decide)
    exact ⟨rs', A, B, fun r hd hne _ => C r (data_ne_pc hd) hne (data_ne_x31 hd)⟩
  case Ocast8signed.cons.nil =>
    cases EV
    refine close_noX31 (straight_two_rd rfl rfl) ?_
    simp only [get0w]; rw [nextinstr_set_same _ _ (ir_ne_pc _)]; exact lessdef_cast8 _
  case Ocast16signed.cons.nil =>
    cases EV
    refine close_noX31 (straight_two_rd rfl rfl) ?_
    simp only [get0w]; rw [nextinstr_set_same _ _ (ir_ne_pc _)]; exact lessdef_cast16 _
  case Oaddimm.cons.nil =>
    cases EV
    exact close_X31 (opimm32_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oandimm.cons.nil =>
    cases EV
    exact close_X31 (opimm32_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oorimm.cons.nil =>
    cases EV
    exact close_X31 (opimm32_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oxorimm.cons.nil =>
    cases EV
    exact close_X31 (opimm32_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oaddlimm.cons.nil =>
    cases EV
    exact close_X31 (opimm64_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oandlimm.cons.nil =>
    cases EV
    exact close_X31 (opimm64_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oorlimm.cons.nil =>
    cases EV
    exact close_X31 (opimm64_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oxorlimm.cons.nil =>
    cases EV
    exact close_X31 (opimm64_correct _ _ _ m (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) _ _ _ k rs
      (ir_not_X31 h)) (.refl _)
  case Oneg.cons.nil =>
    cases EV
    exact close_noX31 (straight_one rfl) (lessdef_neg _)
  case Onegl.cons.nil =>
    cases EV
    exact close_noX31 (straight_one rfl) (lessdef_negl _)
  case Omove.cons.nil =>
    cases EV
    split at TR <;> cases TR
    · rename_i r a h1 h2
      rw [h1, h2]
      exact close_noX31 (straight_one rfl) (.refl _)
    · rename_i r a h1 h2
      rw [h1, h2]
      exact ⟨_, exec_straight_set (fr_ne_pc _) rfl,
        by rw [nextinstr_set_same _ _ (fr_ne_pc _)]; exact .refl _,
        fun r hd hne _ => nextinstr_set_other _ _ (data_ne_pc hd) hne⟩
  case Ofloatconst.nil =>
    cases EV
    split
    · rename_i hz; subst hz
      have hz : Val.maketotal (Val.floatofint (.Vint Integers.Int.zero)) =
          .Vfloat Floats.Float.zero := by decide
      exact ⟨_, exec_straight_set (fr_ne_pc _) rfl,
        by rw [nextinstr_set_same _ _ (fr_ne_pc _)]; simp only [get0w, hz]; exact .refl _,
        fun r hd hne _ => nextinstr_set_other _ _ (data_ne_pc hd) hne⟩
    · exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (fr_ne_pc _)),
        by rw [nextinstr_set_same _ _ (fr_ne_pc _)]; exact .refl _,
        fun r hd hne _ => by
          rw [nextinstr_set_other _ _ (data_ne_pc hd) hne, Regset.gso _ _ (data_ne_x31 hd)]⟩
  case Osingleconst.nil =>
    cases EV
    split
    · rename_i hz; subst hz
      have hz : Val.maketotal (Val.singleofint (.Vint Integers.Int.zero)) =
          .Vsingle Floats.Float32.zero := by decide
      exact ⟨_, exec_straight_set (fr_ne_pc _) rfl,
        by rw [nextinstr_set_same _ _ (fr_ne_pc _)]; simp only [get0w, hz]; exact .refl _,
        fun r hd hne _ => nextinstr_set_other _ _ (data_ne_pc hd) hne⟩
    · exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (fr_ne_pc _)),
        by rw [nextinstr_set_same _ _ (fr_ne_pc _)]; exact .refl _,
        fun r hd hne _ => by
          rw [nextinstr_set_other _ _ (data_ne_pc hd) hne, Regset.gso _ _ (data_ne_x31 hd)]⟩
  case Oaddrsymbol.nil =>
    cases EV
    rename_i id ofs rd
    split
    · obtain ⟨rs2, A, B, C⟩ := addptrofs_correct (sym := sym) (ge := ge) (fn := fn) rd rd ofs k
        (nextinstr (rs.set (.IR rd) (Genv.symbolAddress ge id Integers.Ptrofs.zero))) m
        (ir_not_X31 h)
      refine ⟨rs2, .step _ _ _ _ _ _ _ _ _ rfl (nextinstr_set_pc _ _ (ir_ne_pc _)) A, ?_,
        fun r hd hne _ => ?_⟩
      · rw [nextinstr_set_same _ _ (ir_ne_pc _), ← Genv.shift_symbolAddress,
          Integers.Ptrofs.add_zero_l] at B
        exact B
      · rw [C r (data_ne_pc hd) hne (data_ne_x31 hd), nextinstr_set_other _ _ (data_ne_pc hd) hne]
    · exact close_noX31 (straight_one rfl) (.refl _)
  case Oshrximm.cons.nil =>
    have E := Val.shrx_shr_2 EV; subst E
    have h31 : Preg.IR _ ≠ .IR .X31 := fun e => ir_not_X31 h (Preg.IR.inj e)
    split
    · exact close_noX31 (straight_one rfl) (.refl _)
    · refine close_X31 (straight_four_X31 rfl rfl rfl rfl) ?_
      simp only [get0w, nextinstr_set_same _ _ (ir_ne_pc _),
        nextinstr_set_other _ _ (ir_ne_pc _) h31]
      exact .refl _
  case Oshrxlimm.cons.nil =>
    have E := Val.shrxl_shrl_2 EV; subst E
    have h31 : Preg.IR _ ≠ .IR .X31 := fun e => ir_not_X31 h (Preg.IR.inj e)
    split
    · exact close_noX31 (straight_one rfl) (.refl _)
    · refine close_X31 (straight_four_X31 rfl rfl rfl rfl) ?_
      simp only [get0l, nextinstr_set_same _ _ (ir_ne_pc _),
        nextinstr_set_other _ _ (ir_ne_pc _) h31]
      exact .refl _
  case Ocast32signed.cons.nil =>
    simp only [assert] at TR
    split at TR
    · rename_i heq; simp only [decide_eq_true_eq] at heq; subst heq
      simp only [res_pure_OK] at TR; subst TR; cases EV
      exact close_noX31 (straight_one rfl) (.refl _)
    · cases TR
  case Ocast32unsigned.cons.nil =>
    simp only [assert] at TR
    split at TR
    · rename_i heq; simp only [decide_eq_true_eq] at heq; subst heq
      simp only [res_pure_OK] at TR; subst TR; cases EV
      refine close_noX31 (straight_three_rd rfl rfl rfl) ?_
      simp only [get0l, nextinstr_set_same _ _ (ir_ne_pc _)]
      exact lessdef_cast32u _
    · cases TR
  case Ocmp.nil =>
    cases EV
    obtain ⟨rs', A, B, C⟩ := transl_cond_op_correct (sym := sym) (ge := ge) (fn := fn) rs m TR
    exact ⟨rs', A, B, fun r hd hne _ => C r (data_ne_pc hd) hne (data_ne_x31 hd)⟩
  case Ocmp.cons.nil =>
    cases EV
    obtain ⟨rs', A, B, C⟩ := transl_cond_op_correct (sym := sym) (ge := ge) (fn := fn) rs m TR
    exact ⟨rs', A, B, fun r hd hne _ => C r (data_ne_pc hd) hne (data_ne_x31 hd)⟩
  case Ocmp.cons.cons.nil =>
    cases EV
    obtain ⟨rs', A, B, C⟩ := transl_cond_op_correct (sym := sym) (ge := ge) (fn := fn) rs m TR
    exact ⟨rs', A, B, fun r hd hne _ => C r (data_ne_pc hd) hne (data_ne_x31 hd)⟩
  case Ocmp.cons.cons.cons =>
    cases EV
    obtain ⟨rs', A, B, C⟩ := transl_cond_op_correct (sym := sym) (ge := ge) (fn := fn) rs m TR
    exact ⟨rs', A, B, fun r hd hne _ => C r (data_ne_pc hd) hne (data_ne_x31 hd)⟩
  all_goals (
    rename_i ty rd hrd r1 hr1 r2
    cases EV
    split at TR
    · rename_i heq; subst heq
      simp only [res_pure_OK] at TR; subst TR
      exact close_noX31 (straight_one rfl) (select_same_lessdef _ _ _)
    · obtain ⟨rs1, A, B, C⟩ := transl_cond_op_correct (sym := sym) (ge := ge) (fn := fn) rs m TR
      have hd31 : Preg.IR rd ≠ .IR .X31 := fun e => ir_not_X31 hrd (Preg.IR.inj e)
      have h1 : Preg.IR r1 ≠ .IR .X31 := fun e => ir_not_X31 hr1 (Preg.IR.inj e)
      have h2 : Preg.IR r2 ≠ .IR .X31 := fun e => ir_not_X31 h (Preg.IR.inj e)
      refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ rfl ?_), ?_, fun r hd hne _ => ?_⟩
      · rw [nextinstr_pc, Regset.gso _ _ (by simp), Regset.gso _ _ (by simp)]
      · rw [nextinstr_inv _ (ir_ne_pc _), Regset.gso _ _ hd31, Regset.gss,
          C _ (ir_ne_pc _) h1 h1, C _ (ir_ne_pc _) h2 h2]
        exact csel_lessdef _ B
      · rw [nextinstr_inv _ (data_ne_pc hd), Regset.gso _ _ (data_ne_x31 hd), Regset.gso _ _ hne,
          C r (data_ne_pc hd) (data_ne_x31 hd) (data_ne_x31 hd)])

end CONSTRUCTORS

end Asmgenproof1
end RiscV
end CC
