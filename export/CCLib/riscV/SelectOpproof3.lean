/-
  Correctness of instruction selection for operators (RISC-V), part 3 —
  port of `riscV/SelectOpproof.v`: bitwise operations, division and
  modulus, floating-point operations, integer casts and conversions.
-/
import CCLib.riscV.SelectOpproof2
import CCLib.lib.IntegersPow2

namespace CC
namespace RiscV
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Conjunction -/

theorem val_and_and (v : Val) (n1 n2 : Integers.Int) :
    Val.and (Val.and v (.Vint n2)) (.Vint n1) = Val.and v (.Vint (Integers.Int.and n1 n2)) := by
  cases v <;> simp [Val.and]
  rw [Integers.Int.and_assoc, Integers.Int.and_commut n2]

/-- `eval_andimm` -/
theorem eval_andimm (n : Integers.Int) :
    UnarySound ge sp e m (andimm n) (fun x => Val.and x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold andimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.and, Integers.Int.and_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int.eq n Integers.Int.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h1
    exact ⟨x, hx, by cases x <;> simp [Val.and, Integers.Int.and_mone] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.and, Integers.Int.and_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    rw [val_and_and]
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_and` -/
theorem eval_and : BinarySound ge sp e m SelectOp.and Val.and := by
  intro le a x b y hx hy
  unfold SelectOp.and
  split
  · obtain rfl := inv_intconst hx
    rw [Val.and_commut]; exact eval_andimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_andimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Disjunction -/

/-- `eval_orimm` -/
theorem eval_orimm (n : Integers.Int) :
    UnarySound ge sp e m (orimm n) (fun x => Val.or x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold orimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.or, Integers.Int.or_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int.eq n Integers.Int.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h1
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.or, Integers.Int.or_mone] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.or, Integers.Int.or_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    cases v1 <;> simp [Val.or] <;> try ld
    rw [Integers.Int.or_assoc, Integers.Int.or_commut _ n]; ld
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_or` -/
theorem eval_or : BinarySound ge sp e m SelectOp.or Val.or := by
  intro le a x b y hx hy
  unfold SelectOp.or
  split
  · obtain rfl := inv_intconst hx
    rw [Val.or_commut]; exact eval_orimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_orimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Exclusive or, negation -/

/-- `eval_xorimm` -/
theorem eval_xorimm (n : Integers.Int) :
    UnarySound ge sp e m (xorimm n) (fun x => Val.xor x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold xorimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.xor, Integers.Int.xor_zero] <;> ld⟩
  rw [if_neg h0]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.xor, Integers.Int.xor_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    have hxx : Val.xor (Val.xor v1 (.Vint n2)) (.Vint n) =
        Val.xor v1 (.Vint (Integers.Int.xor n n2)) := by
      cases v1 <;> simp [Val.xor]
      rw [Integers.Int.xor_assoc, Integers.Int.xor_commut n2]
    dsimp only
    split
    · next hz =>
      obtain hz' := (Integers.Int.eq_spec _ _).mp hz
      refine ⟨v1, h1, ?_⟩
      rw [hxx, hz']
      cases v1 <;> simp [Val.xor, Integers.Int.xor_zero] <;> ld
    · exact ⟨_, eval_op1 h1 rfl, by rw [hxx]; ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_xor` -/
theorem eval_xor : BinarySound ge sp e m SelectOp.xor Val.xor := by
  intro le a x b y hx hy
  unfold SelectOp.xor
  split
  · obtain rfl := inv_intconst hx
    rw [Val.xor_commut]; exact eval_xorimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_xorimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_notint` -/
theorem eval_notint : UnarySound ge sp e m notint Val.notint := by
  intro le a x hx
  obtain ⟨v, hv, hl⟩ := eval_xorimm Integers.Int.mone le a x hx
  refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
  cases x <;> simp [Val.notint, Val.xor, Integers.Int.not_eq_xor_mone] <;> ld

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

/-- `eval_cast8unsigned` -/
theorem eval_cast8unsigned : UnarySound ge sp e m cast8unsigned (Val.zeroExt 8) := by
  intro le a x hx
  obtain ⟨v, hv, hl⟩ := eval_andimm (Integers.Int.repr 255) le a x hx
  refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
  cases x <;> simp [Val.zeroExt, Val.and] <;> try ld

/-- `eval_cast16unsigned` -/
theorem eval_cast16unsigned : UnarySound ge sp e m cast16unsigned (Val.zeroExt 16) := by
  intro le a x hx
  obtain ⟨v, hv, hl⟩ := eval_andimm (Integers.Int.repr 65535) le a x hx
  refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
  cases x <;> simp [Val.zeroExt, Val.and] <;> try ld

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

/-- `eval_intuoffloat` -/
theorem eval_intuoffloat {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.intuoffloat x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (intuoffloat a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_intofsingle` -/
theorem eval_intofsingle {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.intofsingle x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (intofsingle a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_intuofsingle` -/
theorem eval_intuofsingle {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.intuofsingle x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (intuofsingle a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_singleofint` -/
theorem eval_singleofint {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.singleofint x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (singleofint a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_singleofintu` -/
theorem eval_singleofintu {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.singleofintu x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (singleofintu a) v ∧ Val.Lessdef y v :=
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

/-- `eval_floatofintu` -/
theorem eval_floatofintu {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.floatofintu x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (floatofintu a) v ∧ Val.Lessdef y v := by
  unfold floatofintu
  split
  · obtain rfl := inv_intconst ha
    simp only [Val.floatofintu] at hy; cases hy
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · exact ⟨y, eval_op1 ha hy, .refl _⟩

end CMCONSTR

end SelectOpproof
end RiscV
end CC
