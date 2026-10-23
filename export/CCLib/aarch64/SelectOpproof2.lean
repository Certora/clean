/-
  Correctness of instruction selection for operators (aarch64), part 2 —
  continuation of `CCLib.aarch64.SelectOpproof` (port of `aarch64/SelectOpproof.v`):
  bitwise operations, general shifts, division bases, floating-point
  operations and conversions.
-/
import CCLib.aarch64.SelectOpproof

namespace CC
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Bitwise negation -/

theorem int_not_bic (a b : Integers.Int) :
    Integers.Int.not (Integers.Int.and a (Integers.Int.not b)) =
      Integers.Int.or b (Integers.Int.not a) := by
  rw [Integers.Int.not_and_or_not, Integers.Int.not_involutive, Integers.Int.or_commut]

theorem int_not_orn (a b : Integers.Int) :
    Integers.Int.not (Integers.Int.or a (Integers.Int.not b)) =
      Integers.Int.and b (Integers.Int.not a) := by
  rw [Integers.Int.not_or_and_not, Integers.Int.not_involutive, Integers.Int.and_commut]

theorem int_not_xor (a b : Integers.Int) :
    Integers.Int.not (Integers.Int.xor a b) = Integers.Int.xor a (Integers.Int.not b) := by
  rw [Integers.Int.not_eq_xor_mone, Integers.Int.not_eq_xor_mone b, Integers.Int.xor_assoc]

theorem int_not_eqv (a b : Integers.Int) :
    Integers.Int.not (Integers.Int.xor a (Integers.Int.not b)) = Integers.Int.xor a b := by
  rw [int_not_xor, Integers.Int.not_involutive]

theorem val_notint_notint (v : Val) : Val.Lessdef (Val.notint (Val.notint v)) v := by
  cases v <;> simp [Val.notint, Integers.Int.not_involutive] <;> ld

/-- `eval_notint` -/
theorem eval_notint : UnarySound ge sp e m notint Val.notint := by
  intro le a x hx
  unfold notint
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, h1, val_notint_notint _⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op1 h1 rfl, val_notint_notint _⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h2 h1 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notint, Val.and, Val.or, int_not_bic] <;> ld
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h2 h1 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notint, Val.and, Val.or, int_not_orn] <;> ld
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notint, Val.xor, int_not_xor] <;> ld
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notint, Val.xor, int_not_eqv] <;> ld
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-! ### Zero and sign extensions -/

theorem unsigned_amount_toNat (a : Amount32) :
    Integers.Int.unsigned a.a32_amount = (a.a32_amount.toNat : _root_.Int) := rfl

/-- `eval_zero_ext` -/
theorem eval_zero_ext (sz : Z) : UnarySound ge sp e m (zeroExt sz) (Val.zeroExt sz.toNat) := by
  intro le a x hx
  unfold zeroExt
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · next am t1 =>
    split
    · next hlt =>
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      rw [unsigned_amount_toNat] at hlt ⊢
      cases v1 <;> simp only [evalShift, Val.shl, Val.zeroExt, am.a32_range, if_true] <;> try ld
      rw [Integers.Int.shl_zero_ext _ _ _ (by zomega),
        show sz.toNat - am.a32_amount.toNat = (sz - (am.a32_amount.toNat : _root_.Int)).toNat by zomega]
      ld
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_sign_ext` -/
theorem eval_sign_ext (sz : Z) : UnarySound ge sp e m (signExt sz) (Val.signExt sz.toNat) := by
  intro le a x hx
  unfold signExt
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · next am t1 =>
    split
    · next hlt =>
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      rw [unsigned_amount_toNat] at hlt ⊢
      cases v1 <;> simp only [evalShift, Val.shl, Val.signExt, am.a32_range, if_true] <;> try ld
      rw [Integers.Int.shl_sign_ext _ _ _ (by zomega),
        show sz.toNat - am.a32_amount.toNat = (sz - (am.a32_amount.toNat : _root_.Int)).toNat by zomega]
      ld
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_cast8signed` -/
theorem eval_cast8signed : UnarySound ge sp e m cast8signed (Val.signExt 8) := eval_sign_ext 8
/-- `eval_cast8unsigned` -/
theorem eval_cast8unsigned : UnarySound ge sp e m cast8unsigned (Val.zeroExt 8) := eval_zero_ext 8
/-- `eval_cast16signed` -/
theorem eval_cast16signed : UnarySound ge sp e m cast16signed (Val.signExt 16) := eval_sign_ext 16
/-- `eval_cast16unsigned` -/
theorem eval_cast16unsigned : UnarySound ge sp e m cast16unsigned (Val.zeroExt 16) :=
  eval_zero_ext 16

/-! ### Conjunction -/

/-- `Z_is_power2m1_sound` (with `Z_is_power2m1_nonneg`). -/
theorem zIsPower2m1_sound {n : Integers.Int} {s : Z}
    (h : zIsPower2m1 (Integers.Int.unsigned n) = some s) :
    n = Integers.Int.repr ((2 : Z) ^ s.toNat - 1) := by
  unfold zIsPower2m1 Integers.Z_is_power2 at h
  split at h
  · next hc =>
    cases h
    have hu : (0 : _root_.Int) ≤ Integers.Int.unsigned n := by
      show (0 : _root_.Int) ≤ (n.toNat : _root_.Int); omega
    have hpos : 0 < (Integers.Int.unsigned n + 1).toNat := by zomega
    have hpow := Integers.nat_eq_two_pow_log2 hpos hc.2
    conv => lhs; rw [← Integers.Int.repr_unsigned n]
    congr 1
    simp only [Int.toNat_natCast]
    have hc' : ((Integers.Int.unsigned n + 1).toNat : _root_.Int) =
        (((2 ^ (Integers.Int.unsigned n + 1).toNat.log2 : Nat)) : _root_.Int) := by
      rw [← hpow]
    rw [Int.natCast_pow, show ((2 : Nat) : _root_.Int) = 2 from rfl] at hc'
    have : ((Integers.Int.unsigned n + 1).toNat : _root_.Int) = Integers.Int.unsigned n + 1 := by
      zomega
    zomega
  · cases h

/-- `eval_andimm_base` -/
theorem eval_andimmBase (n : Integers.Int) :
    UnarySound ge sp e m (andimmBase n) (fun x => Val.and x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold andimmBase
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
  · next s hs =>
    obtain ⟨v, hv, hl⟩ := eval_zero_ext s le a x hx
    refine ⟨v, hv, ?_⟩
    have : Val.and x (.Vint n) = Val.zeroExt s.toNat x := by
      rw [zIsPower2m1_sound hs]
      cases x <;> simp [Val.and, Val.zeroExt, Integers.Int.zero_ext_and]
    rw [this]; exact hl
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

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
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.and, Integers.Int.and_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    rw [val_and_and]
    exact eval_andimmBase _ le _ _ h1
  · next s t2 =>
    split
    · next hs =>
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      have : Val.and (Val.zeroExt s.toNat v1) (.Vint n) =
          Val.and v1 (.Vint (Integers.Int.and n (Integers.Int.repr (twoP s - 1)))) := by
        have ht : twoP s = (2 : Z) ^ s.toNat := by simp [twoP, hs]
        rw [ht]
        cases v1 <;> simp [Val.and, Val.zeroExt, Integers.Int.zero_ext_and]
        rw [Integers.Int.and_assoc, Integers.Int.and_commut n]
      rw [this]
      exact eval_andimmBase _ le _ _ h1
    · exact eval_andimmBase n le _ _ hx
  · exact eval_andimmBase n le _ _ hx

/-- `eval_and` -/
theorem eval_and : BinarySound ge sp e m SelectOp.and Val.and := by
  intro le a x b y hx hy
  unfold SelectOp.and
  split
  · obtain rfl := inv_intconst hx
    rw [Val.and_commut]; exact eval_andimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_andimm _ le _ _ hx
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.and_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.and_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.and_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
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

/-- `same_expr_pure` is sound: two pure-equal expressions evaluate to the same value. -/
theorem sameExprPure_eval {le : Letenv} {t1 t2 : SelectOp.Expr} {v1 v2 : Val}
    (h : sameExprPure t1 t2 = true) (h1 : CminorSel.EvalExpr ge sp e m le t1 v1)
    (h2 : CminorSel.EvalExpr ge sp e m le t2 v2) : v1 = v2 := by
  unfold sameExprPure at h
  split at h
  · next i1 i2 =>
    obtain rfl : i1 = i2 := of_decide_eq_true h
    cases h1 with
    | Evar _ _ _ g1 =>
      cases h2 with
      | Evar _ _ _ g2 => rw [g1] at g2; exact Option.some.inj g2
  · cases h

theorem val_or_ror (v : Val) (a1 a2 : Amount32)
    (h : Integers.Int.add a1.a32_amount a2.a32_amount = Integers.Int.iwordsize) :
    Val.Lessdef (Val.or (Val.shl v (.Vint a1.a32_amount)) (Val.shru v (.Vint a2.a32_amount)))
      (Val.ror v (.Vint a2.a32_amount)) := by
  cases v <;> simp only [Val.or, Val.shl, Val.shru, Val.ror, a1.a32_range, a2.a32_range,
    if_true] <;> try ld
  rw [Integers.Int.or_ror _ _ _ (Integers.Int.toNat_lt_of_ltu a1.a32_range)
    (Integers.Int.toNat_lt_of_ltu a2.a32_range) h]
  ld

/-- `eval_or` -/
theorem eval_or : BinarySound ge sp e m SelectOp.or Val.or := by
  intro le a x b y hx hy
  unfold SelectOp.or
  split
  · obtain rfl := inv_intconst hx
    rw [Val.or_commut]; exact eval_orimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_orimm _ le _ _ hx
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.or_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.or_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain rfl := sameExprPure_eval hc.2 h1 h2
      exact ⟨_, eval_op1 h2 rfl, val_or_ror _ _ _ ((Integers.Int.eq_spec _ _).mp hc.1)⟩
    · exact ⟨_, eval_op2 (eval_op1 h1 rfl) h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain rfl := sameExprPure_eval hc.2 h1 h2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      rw [Val.or_commut]
      exact val_or_ror _ _ _ ((Integers.Int.eq_spec _ _).mp hc.1)
    · exact ⟨_, eval_op2 (eval_op1 h1 rfl) h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.or_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Exclusive or -/

/-- `eval_xorimm_base` -/
theorem eval_xorimmBase (n : Integers.Int) :
    UnarySound ge sp e m (xorimmBase n) (fun x => Val.xor x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold xorimmBase
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.xor, Integers.Int.xor_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int.eq n Integers.Int.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h1
    obtain ⟨v, hv, hl⟩ := eval_notint le a x hx
    refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
    cases x <;> simp [Val.xor, Val.notint, Integers.Int.not_eq_xor_mone] <;> ld
  rw [if_neg h1]
  exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_xorimm` -/
theorem eval_xorimm (n : Integers.Int) :
    UnarySound ge sp e m (xorimm n) (fun x => Val.xor x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold xorimm
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.xor, Integers.Int.xor_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    have : Val.xor (Val.xor v1 (.Vint n2)) (.Vint n) = Val.xor v1 (.Vint (Integers.Int.xor n n2)) := by
      cases v1 <;> simp [Val.xor]
      rw [Integers.Int.xor_assoc, Integers.Int.xor_commut _ n]
    rw [this]
    exact eval_xorimmBase _ le _ _ h1
  · exact eval_xorimmBase n le _ _ hx

/-- `eval_xor` -/
theorem eval_xor : BinarySound ge sp e m SelectOp.xor Val.xor := by
  intro le a x b y hx hy
  unfold SelectOp.xor
  split
  · obtain rfl := inv_intconst hx
    rw [Val.xor_commut]; exact eval_xorimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_xorimm _ le _ _ hx
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.xor_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.xor_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.xor_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Integer division and modulus -/

/-- `eval_divs_base` -/
theorem eval_divsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divs x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divsBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_divu_base` -/
theorem eval_divuBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divuBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_mods_base` -/
theorem eval_modsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.mods x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modsBase a b) v ∧ Val.Lessdef z v := by
  unfold Val.mods at hz
  split at hz
  · next n1 n2 =>
    split at hz
    · cases hz
    · next hc =>
      cases hz
      have hd : Val.divs (.Vint n1) (.Vint n2) = some (.Vint (Integers.Int.divs n1 n2)) := by
        simp only [Val.divs]; rw [if_neg hc]
      have h0 : CminorSel.EvalExpr ge sp e m (.Vint n2 :: .Vint n1 :: le) (.Eletvar 0) (.Vint n2) :=
        .Eletvar _ _ _ rfl
      have h1 : CminorSel.EvalExpr ge sp e m (.Vint n2 :: .Vint n1 :: le) (.Eletvar 1) (.Vint n1) :=
        .Eletvar _ _ _ rfl
      refine ⟨_, .Elet _ _ _ _ _ ha (.Elet _ _ _ _ _ (CminorSel.eval_lift hb)
        (eval_op3 h1 (eval_op2 h1 h0 hd) h0 rfl)), ?_⟩
      simp only [Val.sub, Val.mul, Integers.Int.mods_divs]; ld
  · cases hz

/-- `eval_modu_base` -/
theorem eval_moduBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (moduBase a b) v ∧ Val.Lessdef z v := by
  unfold Val.modu at hz
  split at hz
  · next n1 n2 =>
    split at hz
    · cases hz
    · next hc =>
      cases hz
      have hd : Val.divu (.Vint n1) (.Vint n2) = some (.Vint (Integers.Int.divu n1 n2)) := by
        simp only [Val.divu]; rw [if_neg hc]
      have h0 : CminorSel.EvalExpr ge sp e m (.Vint n2 :: .Vint n1 :: le) (.Eletvar 0) (.Vint n2) :=
        .Eletvar _ _ _ rfl
      have h1 : CminorSel.EvalExpr ge sp e m (.Vint n2 :: .Vint n1 :: le) (.Eletvar 1) (.Vint n1) :=
        .Eletvar _ _ _ rfl
      refine ⟨_, .Elet _ _ _ _ _ ha (.Elet _ _ _ _ _ (CminorSel.eval_lift hb)
        (eval_op3 h1 (eval_op2 h1 h0 hd) h0 rfl)), ?_⟩
      simp only [Val.sub, Val.mul, Integers.Int.modu_divu]; ld
  · cases hz

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

/-! ### General shifts -/

/-- `eval_shl` -/
theorem eval_shl : BinarySound ge sp e m SelectOp.shl Val.shl := by
  intro le a x b y hx hy
  unfold SelectOp.shl
  split
  · obtain rfl := inv_intconst hy
    exact eval_shlimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shr` -/
theorem eval_shr : BinarySound ge sp e m SelectOp.shr Val.shr := by
  intro le a x b y hx hy
  unfold SelectOp.shr
  split
  · obtain rfl := inv_intconst hy
    exact eval_shrimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shru` -/
theorem eval_shru : BinarySound ge sp e m SelectOp.shru Val.shru := by
  intro le a x b y hx hy
  unfold SelectOp.shru
  split
  · obtain rfl := inv_intconst hy
    exact eval_shruimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

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

/-- `eval_singleofint` -/
theorem eval_singleofint {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.singleofint x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (singleofint a) v ∧ Val.Lessdef y v := by
  unfold singleofint
  split
  · obtain rfl := inv_intconst ha
    simp only [Val.singleofint] at hy; cases hy
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · exact ⟨y, eval_op1 ha hy, .refl _⟩

/-- `eval_singleofintu` -/
theorem eval_singleofintu {le : Letenv} {a : SelectOp.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hy : Val.singleofintu x = some y) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (singleofintu a) v ∧ Val.Lessdef y v := by
  unfold singleofintu
  split
  · obtain rfl := inv_intconst ha
    simp only [Val.singleofintu] at hy; cases hy
    exact ⟨_, eval_op0 rfl, .refl _⟩
  · exact ⟨y, eval_op1 ha hy, .refl _⟩

end CMCONSTR

end SelectOpproof
end CC
