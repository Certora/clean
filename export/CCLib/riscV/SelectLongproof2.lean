/-
  Correctness of instruction selection for 64-bit integer operators
  (RISC-V), part 2 — port of `riscV/SelectLongproof.v`: bitwise operations,
  division and modulus, comparisons, floating-point conversions.
-/
import CCLib.riscV.SelectLongproof

namespace CC
namespace RiscV
namespace SelectLongproof

open Op CminorSel SelectOp SelectLong SelectOpproof

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Bitwise operations -/

theorem val_andl_andl (v : Val) (n1 n2 : Integers.Int64) :
    Val.andl (Val.andl v (.Vlong n2)) (.Vlong n1) = Val.andl v (.Vlong (Integers.Int64.and n1 n2)) := by
  cases v <;> simp [Val.andl]
  rw [Integers.Int64.and_assoc, Integers.Int64.and_commut n2]

/-- `eval_andlimm` -/
theorem eval_andlimm (n : Integers.Int64) :
    UnarySound ge sp e m (andlimm n) (fun x => Val.andl x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold andlimm
  by_cases h0 : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h0
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.andl, Integers.Int64.and_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int64.eq n Integers.Int64.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h1
    exact ⟨x, hx, by cases x <;> simp [Val.andl, Integers.Int64.and_mone] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.andl, Integers.Int64.and_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    rw [val_andl_andl]
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_andl` -/
theorem eval_andl : BinarySound ge sp e m andl Val.andl := by
  intro le a x b y hx hy
  unfold andl
  split
  · obtain rfl := inv_longconst hx
    rw [Val.andl_commut]; exact eval_andlimm _ le _ _ hy
  · obtain rfl := inv_longconst hy
    exact eval_andlimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_orlimm` -/
theorem eval_orlimm (n : Integers.Int64) :
    UnarySound ge sp e m (orlimm n) (fun x => Val.orl x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold orlimm
  by_cases h0 : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.orl, Integers.Int64.or_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int64.eq n Integers.Int64.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h1
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.orl, Integers.Int64.or_mone] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.orl, Integers.Int64.or_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    cases v1 <;> simp [Val.orl] <;> try ld
    rw [Integers.Int64.or_assoc, Integers.Int64.or_commut _ n]; ld
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_orl` -/
theorem eval_orl : BinarySound ge sp e m orl Val.orl := by
  intro le a x b y hx hy
  unfold orl
  split
  · obtain rfl := inv_longconst hx
    rw [Val.orl_commut]; exact eval_orlimm _ le _ _ hy
  · obtain rfl := inv_longconst hy
    exact eval_orlimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_xorlimm` -/
theorem eval_xorlimm (n : Integers.Int64) :
    UnarySound ge sp e m (xorlimm n) (fun x => Val.xorl x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold xorlimm
  by_cases h0 : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.xorl, Integers.Int64.xor_zero] <;> ld⟩
  rw [if_neg h0]
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.xorl, Integers.Int64.xor_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    have hxx : Val.xorl (Val.xorl v1 (.Vlong n2)) (.Vlong n) =
        Val.xorl v1 (.Vlong (Integers.Int64.xor n n2)) := by
      cases v1 <;> simp [Val.xorl]
      rw [Integers.Int64.xor_assoc, Integers.Int64.xor_commut n2]
    dsimp only
    split
    · next hz =>
      obtain hz' := (Integers.Int64.eq_spec _ _).mp hz
      refine ⟨v1, h1, ?_⟩
      rw [hxx, hz']
      cases v1 <;> simp [Val.xorl, Integers.Int64.xor_zero] <;> ld
    · exact ⟨_, eval_op1 h1 rfl, by rw [hxx]; ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_xorl` -/
theorem eval_xorl : BinarySound ge sp e m xorl Val.xorl := by
  intro le a x b y hx hy
  unfold xorl
  split
  · obtain rfl := inv_longconst hx
    rw [Val.xorl_commut]; exact eval_xorlimm _ le _ _ hy
  · obtain rfl := inv_longconst hy
    exact eval_xorlimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_notl` -/
theorem eval_notl : UnarySound ge sp e m notl Val.notl := by
  intro le a x hx
  obtain ⟨v, hv, hl⟩ := eval_xorlimm Integers.Int64.mone le a x hx
  refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
  cases x <;> simp [Val.notl, Val.xorl, Integers.Int64.not_eq_xor_mone] <;> ld

/-! ### Division and modulus -/

/-- `eval_divls_base` -/
theorem eval_divlsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divls x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divlsBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_modls_base` -/
theorem eval_modlsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modls x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modlsBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_divlu_base` -/
theorem eval_divluBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divlu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divluBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_modlu_base` -/
theorem eval_modluBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modlu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modluBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_shrxlimm` -/
theorem eval_shrxlimm {le : Letenv} {a : SelectOp.Expr} {n : Integers.Int} {x z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hz : Val.shrxl x (.Vint n) = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (shrxlimm a n) v ∧ Val.Lessdef z v := by
  unfold shrxlimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    refine ⟨x, ha, ?_⟩
    cases x <;> simp [Val.shrxl] at hz
    · obtain rfl := hz.2
      rw [show Integers.Int64.shrx' _ Integers.Int.zero = _ from
        (Integers.Int64.divs_one _ : Integers.Int64.divs _ Integers.Int64.one = _)]; ld
  · rw [if_neg h0]
    exact ⟨z, eval_op1 ha hz, .refl _⟩

/-! ### Comparisons -/

theorem ofOptbool_of_map {ob : Option Bool} {v : Val} (h : ob.map Val.ofBool = some v) :
    Val.ofOptbool ob = v := by
  cases ob with
  | none => cases h
  | some b => cases h; rfl

/-- `eval_cmplu` -/
theorem eval_cmplu (c : Comparison) {le : Letenv} {a b : SelectOp.Expr} {x y v : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hv : Val.cmplu (Mem.validPointer m) c x y = some v) :
    CminorSel.EvalExpr ge sp e m le (cmplu c a b) v := by
  unfold cmplu
  cases h1 : isLongconst a with
  | some n1 =>
    obtain rfl := is_longconst_sound h1 hx
    cases h2 : isLongconst b with
    | some n2 =>
      obtain rfl := is_longconst_sound h2 hy
      cases hv
      refine eval_op0 ?_
      show some (Val.Vint _) = some (Val.ofBool _)
      rw [ofBool_int]
    | none =>
      refine eval_op1 hy ?_
      show some (Val.ofOptbool (Val.cmplu_bool _ c.swap y _)) = _
      unfold Val.cmplu at hv
      rw [Val.swap_cmplu_bool, ofOptbool_of_map hv]
  | none =>
    cases h2 : isLongconst b with
    | some n2 =>
      obtain rfl := is_longconst_sound h2 hy
      exact eval_op1 hx (congrArg some (ofOptbool_of_map hv))
    | none => exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))

/-- `eval_cmpl` -/
theorem eval_cmpl (c : Comparison) {le : Letenv} {a b : SelectOp.Expr} {x y v : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hv : Val.cmpl c x y = some v) :
    CminorSel.EvalExpr ge sp e m le (cmpl c a b) v := by
  unfold cmpl
  cases h1 : isLongconst a with
  | some n1 =>
    obtain rfl := is_longconst_sound h1 hx
    cases h2 : isLongconst b with
    | some n2 =>
      obtain rfl := is_longconst_sound h2 hy
      cases hv
      refine eval_op0 ?_
      show some (Val.Vint _) = some (Val.ofBool _)
      rw [ofBool_int]
    | none =>
      refine eval_op1 hy ?_
      show some (Val.ofOptbool (Val.cmpl_bool c.swap y _)) = _
      unfold Val.cmpl at hv
      rw [Val.swap_cmpl_bool, ofOptbool_of_map hv]
  | none =>
    cases h2 : isLongconst b with
    | some n2 =>
      obtain rfl := is_longconst_sound h2 hy
      exact eval_op1 hx (congrArg some (ofOptbool_of_map hv))
    | none => exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))

/-! ### Floating-point conversions -/

/-- `partial_unary_constructor_sound` -/
def PartialUnarySound (ge : CminorSel.CGenv) (sp : Val) (e : Cminor.Env) (m : Mem)
    (cstr : SelectOp.Expr → SelectOp.Expr) (sem : Val → Option Val) : Prop :=
  ∀ le a x y, CminorSel.EvalExpr ge sp e m le a x → sem x = some y →
    ∃ v, CminorSel.EvalExpr ge sp e m le (cstr a) v ∧ Val.Lessdef y v

theorem eval_longoffloat : PartialUnarySound ge sp e m longoffloat Val.longoffloat :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩
theorem eval_longuoffloat : PartialUnarySound ge sp e m longuoffloat Val.longuoffloat :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩
theorem eval_floatoflong : PartialUnarySound ge sp e m floatoflong Val.floatoflong :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩
theorem eval_floatoflongu : PartialUnarySound ge sp e m floatoflongu Val.floatoflongu :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩
theorem eval_longofsingle : PartialUnarySound ge sp e m longofsingle Val.longofsingle :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩
theorem eval_longuofsingle : PartialUnarySound ge sp e m longuofsingle Val.longuofsingle :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩
theorem eval_singleoflong : PartialUnarySound ge sp e m singleoflong Val.singleoflong :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩
theorem eval_singleoflongu : PartialUnarySound ge sp e m singleoflongu Val.singleoflongu :=
  fun _ _ _ _ hx hy => ⟨_, eval_op1 hx hy, .refl _⟩

end CMCONSTR

end SelectLongproof
end RiscV
end CC
