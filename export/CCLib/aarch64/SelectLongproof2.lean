/-
  Correctness of instruction selection for 64-bit integer operators
  (aarch64), part 2 — continuation of `CCLib.aarch64.SelectLongproof` (port of
  `aarch64/SelectLongproof.v`): zero extension, bitwise operations,
  division bases, general shifts, comparisons and conversions.
-/
import CCLib.aarch64.SelectLongproof

namespace CC
namespace SelectLongproof

open Op CminorSel SelectOp SelectLong SelectOpproof

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

local macro "ld" : tactic => `(tactic| first | exact Val.Lessdef.refl _ | exact Val.Lessdef.undef _)

/-- `Z_is_power2m1_sound` for 64-bit integers. -/
theorem zIsPower2m1_sound64 {n : Integers.Int64} {s : Z}
    (h : zIsPower2m1 (Integers.Int64.unsigned n) = some s) :
    n = Integers.Int64.repr ((2 : Z) ^ s.toNat - 1) := by
  unfold zIsPower2m1 Integers.Z_is_power2 at h
  split at h
  · next hc =>
    cases h
    have hu : (0 : _root_.Int) ≤ Integers.Int64.unsigned n := by
      show (0 : _root_.Int) ≤ (n.toNat : _root_.Int); omega
    have hpos : 0 < (Integers.Int64.unsigned n + 1).toNat := by zomega
    have hpow := Integers.nat_eq_two_pow_log2 hpos hc.2
    conv => lhs; rw [← Integers.Int64.repr_unsigned n]
    congr 1
    simp only [Int.toNat_natCast]
    have hc' : ((Integers.Int64.unsigned n + 1).toNat : _root_.Int) =
        (((2 ^ (Integers.Int64.unsigned n + 1).toNat.log2 : Nat)) : _root_.Int) := by
      rw [← hpow]
    rw [Int.natCast_pow, show ((2 : Nat) : _root_.Int) = 2 from rfl] at hc'
    have : ((Integers.Int64.unsigned n + 1).toNat : _root_.Int) = Integers.Int64.unsigned n + 1 := by
      zomega
    zomega
  · cases h

theorem int64_not_bic (a b : Integers.Int64) :
    Integers.Int64.not (Integers.Int64.and a (Integers.Int64.not b)) =
      Integers.Int64.or b (Integers.Int64.not a) := by
  rw [Integers.Int64.not_and_or_not, Integers.Int64.not_involutive, Integers.Int64.or_commut]

theorem int64_not_orn (a b : Integers.Int64) :
    Integers.Int64.not (Integers.Int64.or a (Integers.Int64.not b)) =
      Integers.Int64.and b (Integers.Int64.not a) := by
  rw [Integers.Int64.not_or_and_not, Integers.Int64.not_involutive, Integers.Int64.and_commut]

theorem int64_not_xor (a b : Integers.Int64) :
    Integers.Int64.not (Integers.Int64.xor a b) = Integers.Int64.xor a (Integers.Int64.not b) := by
  rw [Integers.Int64.not_eq_xor_mone, Integers.Int64.not_eq_xor_mone b, Integers.Int64.xor_assoc]

theorem int64_not_eqv (a b : Integers.Int64) :
    Integers.Int64.not (Integers.Int64.xor a (Integers.Int64.not b)) = Integers.Int64.xor a b := by
  rw [int64_not_xor, Integers.Int64.not_involutive]

theorem val_notl_notl (v : Val) : Val.Lessdef (Val.notl (Val.notl v)) v := by
  cases v <;> simp [Val.notl, Integers.Int64.not_involutive] <;> ld

theorem val_orl_rorl (v : Val) (a1 a2 : Amount64)
    (h : Integers.Int.add a1.a64_amount a2.a64_amount = Integers.Int64.iwordsize') :
    Val.Lessdef (Val.orl (Val.shll v (.Vint a1.a64_amount)) (Val.shrlu v (.Vint a2.a64_amount)))
      (Val.rorl v (.Vint a2.a64_amount)) := by
  have h1 := a64_toNat a1
  have h2 := a64_toNat a2
  have hs : a1.a64_amount.toNat + a2.a64_amount.toNat = 64 := by
    have := congrArg BitVec.toNat h
    rw [int_add_toNat h1 h2] at this
    rw [this]; decide
  cases v <;> try ld
  rw [val_shll_long _ a1.a64_range, val_shrlu_long _ a2.a64_range]
  simp only [Val.orl, Val.rorl]
  have hr : (Integers.Int64.repr (Integers.Int.unsigned a2.a64_amount) : Integers.Int64).toNat =
      a2.a64_amount.toNat := Integers.Int64.toNat_repr_unsigned _
  rw [Integers.Int64.ror_eq_or_nat _ _ (a := a1.a64_amount.toNat) (by omega) (by omega), hr]
  ld

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Zero extension -/

/-- `eval_zero_ext_l` -/
theorem eval_zero_ext_l (sz : Z) :
    UnarySound ge sp e m (zeroExtL sz) (Val.zero_ext_l sz.toNat) := by
  intro le a x hx
  unfold zeroExtL
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · next am t1 =>
    split
    · next hlt =>
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      rw [unsigned_eq_toNat] at hlt ⊢
      show Val.Lessdef (Val.zero_ext_l _ (Val.shll _ _)) (Val.shll (Val.zero_ext_l _ _) _)
      cases v1 <;> try ld
      simp only [Val.zero_ext_l]
      rw [val_shll_long _ am.a64_range, val_shll_long _ am.a64_range]
      dsimp only
      rw [Integers.Int64.shl_zero_ext_nat _ (by zomega),
        show sz.toNat - am.a64_amount.toNat = (sz - (am.a64_amount.toNat : Z)).toNat by zomega]
      ld
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-! ### Bitwise not, and, or, xor -/

/-- `eval_notl` -/
theorem eval_notl : UnarySound ge sp e m notl Val.notl := by
  intro le a x hx
  unfold notl
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op1 h1 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, h1, val_notl_notl _⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op1 h1 rfl, val_notl_notl _⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h2 h1 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notl, Val.andl, Val.orl, int64_not_bic] <;> ld
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h2 h1 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notl, Val.andl, Val.orl, int64_not_orn] <;> ld
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notl, Val.xorl, int64_not_xor] <;> ld
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx; cases ho
    refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.notl, Val.xorl, int64_not_eqv] <;> ld
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_andlimm_base` -/
theorem eval_andlimmBase (n : Integers.Int64) :
    UnarySound ge sp e m (andlimmBase n) (fun x => Val.andl x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold andlimmBase
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
  · next s hs =>
    obtain ⟨v, hv, hl⟩ := eval_zero_ext_l s le a x hx
    refine ⟨v, hv, ?_⟩
    have : Val.andl x (.Vlong n) = Val.zero_ext_l s.toNat x := by
      rw [zIsPower2m1_sound64 hs]
      cases x <;> simp [Val.andl, Val.zero_ext_l, Integers.Int64.zero_ext_and]
    rw [this]; exact hl
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

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
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.andl, Integers.Int64.and_commut]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    rw [val_andl_andl]
    exact eval_andlimmBase _ le _ _ h1
  · next s t2 =>
    split
    · next hs =>
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      have : Val.andl (Val.zero_ext_l s.toNat v1) (.Vlong n) =
          Val.andl v1 (.Vlong (Integers.Int64.and n (Integers.Int64.repr (twoP s - 1)))) := by
        have ht : twoP s = (2 : Z) ^ s.toNat := by simp [twoP, hs]
        rw [ht]
        cases v1 <;> simp [Val.andl, Val.zero_ext_l, Integers.Int64.zero_ext_and]
        rw [Integers.Int64.and_assoc, Integers.Int64.and_commut n]
      rw [this]
      exact eval_andlimmBase _ le _ _ h1
    · exact eval_andlimmBase n le _ _ hx
  · exact eval_andlimmBase n le _ _ hx

/-- `eval_andl` -/
theorem eval_andl : BinarySound ge sp e m andl Val.andl := by
  intro le a x b y hx hy
  unfold andl
  split
  · obtain rfl := inv_longconst hx
    rw [Val.andl_commut]; exact eval_andlimm _ le _ _ hy
  · obtain rfl := inv_longconst hy
    exact eval_andlimm _ le _ _ hx
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.andl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.andl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.andl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
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
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.orl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.orl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain rfl := sameExprPure_eval hc.2 h1 h2
      exact ⟨_, eval_op1 h2 rfl, val_orl_rorl _ _ _ ((Integers.Int.eq_spec _ _).mp hc.1)⟩
    · exact ⟨_, eval_op2 (eval_op1 h1 rfl) h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain rfl := sameExprPure_eval hc.2 h1 h2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      rw [Val.orl_commut]
      exact val_orl_rorl _ _ _ ((Integers.Int.eq_spec _ _).mp hc.1)
    · exact ⟨_, eval_op2 (eval_op1 h1 rfl) h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.orl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_xorlimm_base` -/
theorem eval_xorlimmBase (n : Integers.Int64) :
    UnarySound ge sp e m (xorlimmBase n) (fun x => Val.xorl x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold xorlimmBase
  by_cases h0 : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h0
    exact ⟨x, hx, by cases x <;> simp [Val.xorl, Integers.Int64.xor_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int64.eq n Integers.Int64.mone = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h1
    obtain ⟨v, hv, hl⟩ := eval_notl le a x hx
    refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
    cases x <;> simp [Val.xorl, Val.notl, Integers.Int64.not_eq_xor_mone] <;> ld
  rw [if_neg h1]
  exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_xorlimm` -/
theorem eval_xorlimm (n : Integers.Int64) :
    UnarySound ge sp e m (xorlimm n) (fun x => Val.xorl x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold xorlimm
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.xorl, Integers.Int64.xor_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    have : Val.xorl (Val.xorl v1 (.Vlong n2)) (.Vlong n) =
        Val.xorl v1 (.Vlong (Integers.Int64.xor n n2)) := by
      cases v1 <;> simp [Val.xorl]
      rw [Integers.Int64.xor_assoc, Integers.Int64.xor_commut _ n]
    rw [this]
    exact eval_xorlimmBase _ le _ _ h1
  · exact eval_xorlimmBase n le _ _ hx

/-- `eval_xorl` -/
theorem eval_xorl : BinarySound ge sp e m xorl Val.xorl := by
  intro le a x b y hx hy
  unfold xorl
  split
  · obtain rfl := inv_longconst hx
    rw [Val.xorl_commut]; exact eval_xorlimm _ le _ _ hy
  · obtain rfl := inv_longconst hy
    exact eval_xorlimm _ le _ _ hx
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.xorl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.xorl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.xorl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Integer division and modulus -/

/-- `eval_divls_base` -/
theorem eval_divlsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divls x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divlsBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_divlu_base` -/
theorem eval_divluBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divlu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divluBase a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_op2 ha hb hz, .refl _⟩

/-- `eval_modls_base` -/
theorem eval_modlsBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modls x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modlsBase a b) v ∧ Val.Lessdef z v := by
  unfold Val.modls at hz
  split at hz
  · next n1 n2 =>
    split at hz
    · cases hz
    · next hc =>
      cases hz
      have hd : Val.divls (.Vlong n1) (.Vlong n2) = some (.Vlong (Integers.Int64.divs n1 n2)) := by
        simp only [Val.divls]; rw [if_neg hc]
      have h0 : CminorSel.EvalExpr ge sp e m (.Vlong n2 :: .Vlong n1 :: le) (.Eletvar 0) (.Vlong n2) :=
        .Eletvar _ _ _ rfl
      have h1 : CminorSel.EvalExpr ge sp e m (.Vlong n2 :: .Vlong n1 :: le) (.Eletvar 1) (.Vlong n1) :=
        .Eletvar _ _ _ rfl
      refine ⟨_, .Elet _ _ _ _ _ ha (.Elet _ _ _ _ _ (CminorSel.eval_lift hb)
        (eval_op3 h1 (eval_op2 h1 h0 hd) h0 rfl)), ?_⟩
      simp only [Val.subl, Val.mull, Integers.Int64.mods_divs]; ld
  · cases hz

/-- `eval_modlu_base` -/
theorem eval_modluBase {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modlu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modluBase a b) v ∧ Val.Lessdef z v := by
  unfold Val.modlu at hz
  split at hz
  · next n1 n2 =>
    split at hz
    · cases hz
    · next hc =>
      cases hz
      have hd : Val.divlu (.Vlong n1) (.Vlong n2) = some (.Vlong (Integers.Int64.divu n1 n2)) := by
        simp only [Val.divlu]; rw [if_neg hc]
      have h0 : CminorSel.EvalExpr ge sp e m (.Vlong n2 :: .Vlong n1 :: le) (.Eletvar 0) (.Vlong n2) :=
        .Eletvar _ _ _ rfl
      have h1 : CminorSel.EvalExpr ge sp e m (.Vlong n2 :: .Vlong n1 :: le) (.Eletvar 1) (.Vlong n1) :=
        .Eletvar _ _ _ rfl
      refine ⟨_, .Elet _ _ _ _ _ ha (.Elet _ _ _ _ _ (CminorSel.eval_lift hb)
        (eval_op3 h1 (eval_op2 h1 h0 hd) h0 rfl)), ?_⟩
      simp only [Val.subl, Val.mull, Integers.Int64.modu_divu]; ld
  · cases hz

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

/-! ### General shifts -/

/-- `eval_shll` -/
theorem eval_shll : BinarySound ge sp e m shll Val.shll := by
  intro le a x b y hx hy
  unfold shll
  split
  · obtain rfl := inv_intconst hy
    exact eval_shllimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shrl` -/
theorem eval_shrl : BinarySound ge sp e m shrl Val.shrl := by
  intro le a x b y hx hy
  unfold shrl
  split
  · obtain rfl := inv_intconst hy
    exact eval_shrlimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shrlu` -/
theorem eval_shrlu : BinarySound ge sp e m shrlu Val.shrlu := by
  intro le a x b y hx hy
  unfold shrlu
  split
  · obtain rfl := inv_intconst hy
    exact eval_shrluimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Comparisons (`Section COMP_IMM`) -/

/-- The hypotheses of `Section COMP_IMM` (64-bit version). -/
structure CompLImmHyps (default : Comparison → Integers.Int64 → Condition)
    (intsem : Comparison → Integers.Int64 → Integers.Int64 → Bool)
    (sem : Comparison → Val → Val → Option Val) (m : Mem) : Prop where
  sem_int : ∀ c x y, sem c (.Vlong x) (.Vlong y) = some (Val.ofBool (intsem c x y))
  sem_undef : ∀ c v, sem c .Vundef v = none
  sem_eq : ∀ x y, sem .Ceq (.Vlong x) (.Vlong y) = some (Val.ofBool (Integers.Int64.eq x y))
  sem_ne : ∀ x y, sem .Cne (.Vlong x) (.Vlong y) = some (Val.ofBool (!Integers.Int64.eq x y))
  sem_default : ∀ c v n, sem c v (.Vlong n) = (evalCondition (default c n) [v] m).map Val.ofBool

theorem ofOptbool_of_map {ob : Option Bool} {v : Val} (h : ob.map Val.ofBool = some v) :
    Val.ofOptbool ob = v := by
  cases ob with
  | none => cases h
  | some b => cases h; rfl

theorem eval_complimm_default {default intsem sem} (H : CompLImmHyps default intsem sem m)
    {le : Letenv} {a : SelectOp.Expr} {x v : Val} {c : Comparison} {n2 : Integers.Int64}
    (hs : sem c x (.Vlong n2) = some v) (hx : CminorSel.EvalExpr ge sp e m le a x) :
    CminorSel.EvalExpr ge sp e m le (.Eop (.Ocmp (default c n2)) (a ::: .Enil)) v := by
  refine eval_op1 hx ?_
  rw [H.sem_default] at hs
  show some (Val.ofOptbool _) = _
  rw [ofOptbool_of_map hs]

/-- `eval_complimm` -/
theorem eval_complimm {default intsem sem} (H : CompLImmHyps default intsem sem m)
    {le : Letenv} (c : Comparison) {a : SelectOp.Expr} (n2 : Integers.Int64) {x v : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hs : sem c x (.Vlong n2) = some v) :
    CminorSel.EvalExpr ge sp e m le (complimm default intsem c a n2) v := by
  unfold complimm
  split
  · obtain rfl := inv_longconst hx
    rw [H.sem_int] at hs; cases hs
    refine eval_op0 ?_
    show some (Val.Vint _) = some (Val.ofBool _)
    rw [ofBool_int]
  · next mk t1 =>
    split
    · next h0 =>
      obtain rfl := (Integers.Int64.eq_spec _ _).mp h0
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine eval_op1 h1 ?_
      cases v1 with
      | Vlong k =>
        simp only [Val.andl] at hs
        rw [H.sem_eq] at hs; cases hs; rfl
      | _ => simp only [Val.andl, H.sem_undef] at hs; cases hs
    · exact eval_complimm_default H hs hx
  · next mk t1 =>
    split
    · next h0 =>
      obtain rfl := (Integers.Int64.eq_spec _ _).mp h0
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine eval_op1 h1 ?_
      cases v1 with
      | Vlong k =>
        simp only [Val.andl] at hs
        rw [H.sem_ne] at hs; cases hs; rfl
      | _ => simp only [Val.andl, H.sem_undef] at hs; cases hs
    · exact eval_complimm_default H hs hx
  · exact eval_complimm_default H hs hx

theorem cmpl_hyps : CompLImmHyps .Ccomplimm Integers.Int64.cmp Val.cmpl m where
  sem_int _ _ _ := rfl
  sem_undef _ _ := rfl
  sem_eq _ _ := rfl
  sem_ne _ _ := rfl
  sem_default c v n := by cases v <;> rfl

theorem cmplu_hyps :
    CompLImmHyps .Ccompluimm Integers.Int64.cmpu (Val.cmplu (Mem.validPointer m)) m where
  sem_int _ _ _ := rfl
  sem_undef _ _ := rfl
  sem_eq _ _ := rfl
  sem_ne _ _ := rfl
  sem_default c v n := by cases v <;> rfl

/-- `eval_cmpl` -/
theorem eval_cmpl (c : Comparison) {le : Letenv} {a b : SelectOp.Expr} {x y v : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hv : Val.cmpl c x y = some v) :
    CminorSel.EvalExpr ge sp e m le (cmpl c a b) v := by
  unfold cmpl
  split
  · obtain rfl := inv_longconst hx
    refine eval_complimm cmpl_hyps c.swap _ hy ?_
    unfold Val.cmpl at hv ⊢; rw [Val.swap_cmpl_bool]; exact hv
  · obtain rfl := inv_longconst hy
    exact eval_complimm cmpl_hyps c _ hx hv
  · next s a1 t1 =>
    split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine eval_op2 hy h1 ?_
      show some (Val.ofOptbool (Val.cmpl_bool c.swap y _)) = _
      rw [Val.swap_cmpl_bool, ofOptbool_of_map hv]
    · unfold cmplRest
      split
      · split
        · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
          exact eval_op2 hx h2 (congrArg some (ofOptbool_of_map hv))
        · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))
      · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))
  · unfold cmplRest
    split
    · split
      · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
        exact eval_op2 hx h2 (congrArg some (ofOptbool_of_map hv))
      · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))
    · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))

/-- `eval_cmplu` -/
theorem eval_cmplu (c : Comparison) {le : Letenv} {a b : SelectOp.Expr} {x y v : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hv : Val.cmplu (Mem.validPointer m) c x y = some v) :
    CminorSel.EvalExpr ge sp e m le (cmplu c a b) v := by
  unfold cmplu
  split
  · obtain rfl := inv_longconst hx
    refine eval_complimm cmplu_hyps c.swap _ hy ?_
    unfold Val.cmplu at hv ⊢; rw [Val.swap_cmplu_bool]; exact hv
  · obtain rfl := inv_longconst hy
    exact eval_complimm cmplu_hyps c _ hx hv
  · next s a1 t1 =>
    split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx; cases ho
      refine eval_op2 hy h1 ?_
      show some (Val.ofOptbool (Val.cmplu_bool _ c.swap y _)) = _
      rw [Val.swap_cmplu_bool, ofOptbool_of_map hv]
    · unfold cmplRest
      split
      · split
        · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
          exact eval_op2 hx h2 (congrArg some (ofOptbool_of_map hv))
        · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))
      · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))
  · unfold cmplRest
    split
    · split
      · obtain ⟨v2, h2, ho⟩ := inv_op1 hy; cases ho
        exact eval_op2 hx h2 (congrArg some (ofOptbool_of_map hv))
      · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))
    · exact eval_op2 hx hy (congrArg some (ofOptbool_of_map hv))

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
end CC
