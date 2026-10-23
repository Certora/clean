/-
  Correctness of instruction selection for operators (aarch64) — port of
  `aarch64/SelectOpproof.v`.

  Every smart constructor of `SelectOp` is shown to compute (an
  approximation, in the sense of `Val.Lessdef`, of) the value of the
  operator it implements: `UnarySound cstr sem` / `BinarySound cstr sem`
  are Rocq's `unary_constructor_sound` / `binary_constructor_sound`.
-/
import CCLib.aarch64.SelectOp
import CCLib.common.ValuesTheory
import CCLib.lib.IntegersShiftsExtra

namespace CC
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- Close a `Val.Lessdef` goal that holds by reflexivity or because the left side is
`Vundef`. -/
macro "ld" : tactic => `(tactic| first | exact Val.Lessdef.refl _ | exact Val.Lessdef.undef _)

namespace SelectDivproofBounds
theorem signed_range32 (x : Integers.Int) :
    (-2 ^ 31 : _root_.Int) ≤ Integers.Int.signed x ∧ (Integers.Int.signed x : _root_.Int) < 2 ^ 31 := by
  have := Integers.Int.signed_range x
  have : @Eq _root_.Int Integers.Int.min_signed (-2^31) := by decide
  have : @Eq _root_.Int Integers.Int.max_signed (2^31 - 1) := by decide
  zomega
end SelectDivproofBounds

section CMCONSTR
variable (ge : CminorSel.CGenv) (sp : Val) (e : Cminor.Env) (m : Mem)

/-- `unary_constructor_sound` -/
def UnarySound (cstr : SelectOp.Expr → SelectOp.Expr) (sem : Val → Val) : Prop :=
  ∀ le a x, CminorSel.EvalExpr ge sp e m le a x →
    ∃ v, CminorSel.EvalExpr ge sp e m le (cstr a) v ∧ Val.Lessdef (sem x) v

/-- `binary_constructor_sound` -/
def BinarySound (cstr : SelectOp.Expr → SelectOp.Expr → SelectOp.Expr)
    (sem : Val → Val → Val) : Prop :=
  ∀ le a x b y, CminorSel.EvalExpr ge sp e m le a x → CminorSel.EvalExpr ge sp e m le b y →
    ∃ v, CminorSel.EvalExpr ge sp e m le (cstr a b) v ∧ Val.Lessdef (sem x y) v

/-! ### Evaluation of operator applications (Rocq's `EvalOp` / `InvEval`) -/

variable {ge sp e m}

theorem eval_op0 {le : Letenv} {op : Operation} {v : Val}
    (h : evalOperation ge sp op [] m = some v) :
    CminorSel.EvalExpr ge sp e m le (.Eop op .Enil) v :=
  .Eop _ _ _ _ _ (.Enil _) h

theorem eval_op1 {le : Letenv} {op : Operation} {a : SelectOp.Expr} {v1 v : Val}
    (h1 : CminorSel.EvalExpr ge sp e m le a v1) (h : evalOperation ge sp op [v1] m = some v) :
    CminorSel.EvalExpr ge sp e m le (.Eop op (a ::: .Enil)) v :=
  .Eop _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Enil _)) h

theorem eval_op2 {le : Letenv} {op : Operation} {a b : SelectOp.Expr} {v1 v2 v : Val}
    (h1 : CminorSel.EvalExpr ge sp e m le a v1) (h2 : CminorSel.EvalExpr ge sp e m le b v2)
    (h : evalOperation ge sp op [v1, v2] m = some v) :
    CminorSel.EvalExpr ge sp e m le (.Eop op (a ::: b ::: .Enil)) v :=
  .Eop _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 (.Enil _))) h

theorem eval_op3 {le : Letenv} {op : Operation} {a b c : SelectOp.Expr} {v1 v2 v3 v : Val}
    (h1 : CminorSel.EvalExpr ge sp e m le a v1) (h2 : CminorSel.EvalExpr ge sp e m le b v2)
    (h3 : CminorSel.EvalExpr ge sp e m le c v3)
    (h : evalOperation ge sp op [v1, v2, v3] m = some v) :
    CminorSel.EvalExpr ge sp e m le (.Eop op (a ::: b ::: c ::: .Enil)) v :=
  .Eop _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2
    (.Econs _ _ _ _ _ h3 (.Enil _)))) h

theorem inv_op0 {le : Letenv} {op : Operation} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le (.Eop op .Enil) v) :
    evalOperation ge sp op [] m = some v := by
  cases h with
  | Eop _ _ _ vl _ hl ho => cases hl; exact ho

theorem inv_op1 {le : Letenv} {op : Operation} {a : SelectOp.Expr} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le (.Eop op (a ::: .Enil)) v) :
    ∃ v1, CminorSel.EvalExpr ge sp e m le a v1 ∧ evalOperation ge sp op [v1] m = some v := by
  cases h with
  | Eop _ _ _ vl _ hl ho =>
    cases hl with
    | Econs _ _ _ v1 _ h1 hl => cases hl; exact ⟨v1, h1, ho⟩

theorem inv_op2 {le : Letenv} {op : Operation} {a b : SelectOp.Expr} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le (.Eop op (a ::: b ::: .Enil)) v) :
    ∃ v1 v2, CminorSel.EvalExpr ge sp e m le a v1 ∧ CminorSel.EvalExpr ge sp e m le b v2 ∧
      evalOperation ge sp op [v1, v2] m = some v := by
  cases h with
  | Eop _ _ _ vl _ hl ho =>
    cases hl with
    | Econs _ _ _ v1 _ h1 hl =>
      cases hl with
      | Econs _ _ _ v2 _ h2 hl => cases hl; exact ⟨v1, v2, h1, h2, ho⟩

theorem inv_intconst {le : Letenv} {n : Integers.Int} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le (.Eop (.Ointconst n) .Enil) v) : v = .Vint n := by
  have : some (Val.Vint n) = some v := inv_op0 h
  exact (Option.some.inj this).symm

/-- A trivially-correct result: the constructor evaluates to exactly `sem x`. -/
theorem lessdef_exists {le : Letenv} {a : SelectOp.Expr} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le a v) : ∃ v', CminorSel.EvalExpr ge sp e m le a v' ∧ Val.Lessdef v v' :=
  ⟨v, h, .refl _⟩

/-! ### Constants -/

/-- `eval_addrsymbol` -/
theorem eval_addrsymbol (le : Letenv) (id : Ident) (ofs : Integers.Ptrofs) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (addrsymbol id ofs) v ∧
      Val.Lessdef (Genv.symbolAddress ge id ofs) v :=
  lessdef_exists (eval_op0 rfl)

/-- `eval_addrstack` -/
theorem eval_addrstack (le : Letenv) (ofs : Integers.Ptrofs) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (addrstack ofs) v ∧ Val.Lessdef (Val.offsetPtr sp ofs) v :=
  lessdef_exists (eval_op0 rfl)

/-! ### Addition, opposite, subtraction -/

/-- `eval_addimm` -/
theorem eval_addimm (n : Integers.Int) :
    UnarySound ge sp e m (addimm n) (fun x => Val.add x (.Vint n)) := by
  intro le a x hx
  unfold addimm
  by_cases hn : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hn]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hn
    refine ⟨x, hx, ?_⟩
    cases x <;> simp [Val.add, Archi.ptr64, Integers.Int.add_zero] <;> ld
  · rw [if_neg hn]
    split
    · rename_i k
      obtain rfl := inv_intconst hx
      exact ⟨_, eval_op0 rfl, by simp [Val.add, Integers.Int.add_commut]; exact .refl _⟩
    · rename_i k t
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.add (Val.add v1 _) _) _
      rw [Val.add_assoc]; simp [Val.add, Integers.Int.add_commut]; ld
    · exact ⟨_, eval_op1 hx rfl, .refl _⟩

theorem eval_addRest2 : BinarySound ge sp e m addRest2 Val.add := by
  intro le a x b y hx hy
  unfold addRest2
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx
    cases ho
    exact ⟨_, eval_op3 hy h1 h2 rfl, by rw [Val.add_commut]; ld⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hy
    cases ho
    exact ⟨_, eval_op3 hx h1 h2 rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

theorem eval_addRest1 : BinarySound ge sp e m addRest1 Val.add := by
  intro le a x b y hx hy
  unfold addRest1
  split
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hy
      cases ho
      exact ⟨_, eval_op2 hx h1 rfl, by ld⟩
    · exact eval_addRest2 le _ _ _ _ hx hy
  · exact eval_addRest2 le _ _ _ _ hx hy

/-- `eval_add` -/
theorem eval_add : BinarySound ge sp e m SelectOp.add Val.add := by
  intro le a x b y hx hy
  unfold SelectOp.add
  split
  · obtain rfl := inv_intconst hx
    rw [Val.add_commut]; exact eval_addimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_addimm _ le _ _ hx
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho1; cases ho2
    rw [Val.add_permut_4]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Oadd) h1 h2 rfl)
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    rw [Val.add_assoc, Val.add_commut (.Vint _) y, ← Val.add_assoc]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Oadd) h1 hy rfl)
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    rw [← Val.add_assoc]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Oadd) hx h2 rfl)
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.add_commut]; ld⟩
    · exact eval_addRest1 le _ _ _ _ hx hy
  · exact eval_addRest1 le _ _ _ _ hx hy

theorem val_sub_zero_neg (v : Val) : Val.Lessdef (Val.sub Val.Vzero v) (Val.neg v) := by
  cases v <;> simp [Val.sub, Val.neg, Val.Vzero, Integers.Int.sub_zero_l] <;> ld

/-- `eval_negint` -/
theorem eval_negint : UnarySound ge sp e m negint (fun v => Val.sub Val.Vzero v) := by
  intro le a x hx
  unfold negint
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by
      simp [Val.sub, Val.Vzero, Integers.Int.sub_zero_l]; ld⟩
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      exact ⟨_, eval_op1 h1 rfl, val_sub_zero_neg _⟩
    · exact ⟨_, eval_op1 hx rfl, val_sub_zero_neg _⟩
  · exact ⟨_, eval_op1 hx rfl, val_sub_zero_neg _⟩

theorem val_sub_add_l (v1 v2 : Val) (i : Integers.Int) :
    Val.sub (Val.add v1 (.Vint i)) v2 = Val.add (Val.sub v1 v2) (.Vint i) := by
  cases v1 <;> cases v2 <;> simp [Val.sub, Val.add, Archi.ptr64, Integers.Int.sub_add_l]

theorem val_sub_add_r (v1 v2 : Val) (i : Integers.Int) :
    Val.sub v1 (Val.add v2 (.Vint i)) = Val.add (Val.sub v1 v2) (.Vint (Integers.Int.neg i)) := by
  cases v1 <;> cases v2 <;> simp [Val.sub, Val.add, Archi.ptr64]
  rw [Integers.Int.add_commut, Integers.Int.sub_add_r]

theorem eval_subRest : BinarySound ge sp e m subRest Val.sub := by
  intro le a x b y hx hy
  unfold subRest
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hy
    cases ho
    exact ⟨_, eval_op3 hx h1 h2 rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_sub` -/
theorem eval_sub : BinarySound ge sp e m SelectOp.sub Val.sub := by
  intro le a x b y hx hy
  unfold SelectOp.sub
  split
  · obtain rfl := inv_intconst hy
    rw [Val.sub_add_opp]; exact eval_addimm _ le _ _ hx
  · rename_i n1 t1 n2 t2
    obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho1; cases ho2
    rw [val_sub_add_l, val_sub_add_r, Val.add_assoc,
      show Val.add (.Vint (Integers.Int.neg n2)) (.Vint n1) = .Vint (Integers.Int.sub n1 n2) by
        simp [Val.add, Integers.Int.add_commut, Integers.Int.sub_add_opp]]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Osub) h1 h2 rfl)
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    rw [val_sub_add_l]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Osub) h1 hy rfl)
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    rw [val_sub_add_r]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Osub) hx h2 rfl)
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hy
      cases ho
      exact ⟨_, eval_op2 hx h1 rfl, by ld⟩
    · exact eval_subRest le _ _ _ _ hx hy
  · exact eval_subRest le _ _ _ _ hx hy

/-! ### Immediate shifts -/

theorem mkAmount32_eq {n : Integers.Int} (h : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    (mkAmount32 n).a32_amount = n :=
  Integers.Int.zero_ext_5_of_ltu h

theorem ltu_add_toNat {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int.iwordsize = true)
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    a.toNat + n.toNat < 2 ^ 32 := by
  have := Integers.Int.toNat_lt_of_ltu ha
  have := Integers.Int.toNat_lt_of_ltu hn
  omega

theorem val_shl_zero (x : Val) : Val.Lessdef (Val.shl x (.Vint Integers.Int.zero)) x := by
  cases x <;> simp [Val.shl] <;> try ld
  rw [if_pos (by decide), Integers.Int.shl_zero]; ld

theorem val_shl_shl (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int.iwordsize = true)
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true)
    (h : Integers.Int.ltu (Integers.Int.add a n) Integers.Int.iwordsize = true) :
    Val.shl (Val.shl v (.Vint a)) (.Vint n) = Val.shl v (.Vint (Integers.Int.add a n)) := by
  cases v <;> simp [Val.shl, ha, hn, h]
  exact Integers.Int.shl_shl _ _ _ (ltu_add_toNat ha hn)

theorem eval_shlimmBase {le : Letenv} {a : SelectOp.Expr} {x : Val} {n : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hn : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    CminorSel.EvalExpr ge sp e m le (shlimmBase a n) (Val.shl x (.Vint n)) := by
  unfold shlimmBase
  refine eval_op1 hx ?_
  show some (Val.shl x (.Vint (mkAmount32 n).a32_amount)) = _
  rw [mkAmount32_eq hn]

/-- `eval_shlimm` -/
theorem eval_shlimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shlimm a n) (fun x => Val.shl x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shlimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shl_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int.iwordsize
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.shl, L]; ld⟩
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_shlimmBase h1 L2, ?_⟩
      show Val.Lessdef (Val.shl (Val.shl v1 _) _) _
      rw [val_shl_shl v1 a0.a32_range L L2]; ld
    · exact ⟨_, eval_shlimmBase hx L, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    show Val.Lessdef _ (Val.shl _ (.Vint (mkAmount32 n).a32_amount))
    rw [mkAmount32_eq L]; ld
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    show Val.Lessdef _ (Val.shl _ (.Vint (mkAmount32 n).a32_amount))
    rw [mkAmount32_eq L]; ld
  · rename_i s0 a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shl (Val.shl _ _) _)
        (Val.shl _ (.Vint (mkAmount32 (Integers.Int.add a0.a32_amount n)).a32_amount))
      rw [mkAmount32_eq L2, val_shl_shl _ a0.a32_range L L2]; ld
    · exact ⟨_, eval_shlimmBase hx L, by ld⟩
  · rename_i s0 a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shl (Val.shl _ _) _)
        (Val.shl _ (.Vint (mkAmount32 (Integers.Int.add a0.a32_amount n)).a32_amount))
      rw [mkAmount32_eq L2, val_shl_shl _ a0.a32_range L L2]; ld
    · exact ⟨_, eval_shlimmBase hx L, by ld⟩
  · exact ⟨_, eval_shlimmBase hx L, by ld⟩

theorem ltu_iw_of_toNat {y : Integers.Int} (h : y.toNat < 32) :
    Integers.Int.ltu y Integers.Int.iwordsize = true := by
  rw [Integers.Int.ltu_toNat]; exact decide_eq_true (by
    show y.toNat < (32 : BitVec 32).toNat; simp; omega)

theorem zw_sub_toNat (a : Integers.Int) :
    (Integers.Int.zwordsize - Integers.Int.unsigned a).toNat = 32 - a.toNat := by
  show ((32 : _root_.Int) - (a.toNat : _root_.Int)).toNat = _; omega

theorem ltu_sub_iw {a n : Integers.Int} (ha : Integers.Int.ltu a Integers.Int.iwordsize = true)
    (h : n.toNat ≤ a.toNat) :
    Integers.Int.ltu (Integers.Int.sub a n) Integers.Int.iwordsize = true := by
  have := Integers.Int.toNat_lt_of_ltu ha
  apply ltu_iw_of_toNat; rw [Integers.Int.sub_toNat h]; omega

theorem val_shru_zero (x : Val) : Val.Lessdef (Val.shru x (.Vint Integers.Int.zero)) x := by
  cases x <;> simp [Val.shru, Integers.Int.shru_zero] <;> first | ld | (rw [if_pos (by decide)]; ld)

theorem val_shru_shru (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int.iwordsize = true)
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true)
    (h : Integers.Int.ltu (Integers.Int.add a n) Integers.Int.iwordsize = true) :
    Val.shru (Val.shru v (.Vint a)) (.Vint n) = Val.shru v (.Vint (Integers.Int.add a n)) := by
  cases v <;> simp [Val.shru, ha, hn, h]
  exact Integers.Int.shru_shru _ _ _ (ltu_add_toNat ha hn)

theorem eval_shruimmBase {le : Letenv} {a : SelectOp.Expr} {x : Val} {n : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hn : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    CminorSel.EvalExpr ge sp e m le (shruimmBase a n) (Val.shru x (.Vint n)) := by
  unfold shruimmBase
  refine eval_op1 hx ?_
  show some (Val.shru x (.Vint (mkAmount32 n).a32_amount)) = _
  rw [mkAmount32_eq hn]

/-- `eval_shruimm` -/
theorem eval_shruimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shruimm a n) (fun x => Val.shru x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shruimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shru_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int.iwordsize
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  have hn' := Integers.Int.toNat_lt_of_ltu L
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.shru, L]; ld⟩
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    have ha' := Integers.Int.toNat_lt_of_ltu a0.a32_range
    split
    · rename_i L2
      have hlt : n.toNat < a0.a32_amount.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      have L3 := ltu_sub_iw a0.a32_range (Nat.le_of_lt hlt)
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shru (Val.shl v1 (.Vint a0.a32_amount)) _)
        (Val.shl (Val.zeroExt (Integers.Int.zwordsize - Integers.Int.unsigned a0.a32_amount).toNat v1)
          (.Vint (mkAmount32 (Integers.Int.sub a0.a32_amount n)).a32_amount))
      rw [mkAmount32_eq L3, zw_sub_toNat]
      cases v1 <;> simp [Val.shru, Val.shl, Val.zeroExt, L, L3, a0.a32_range] <;> try ld
      rw [Integers.Int.shru_shl _ _ _ a0.a32_range L, if_pos L2]; ld
    · rename_i L2
      have hle : a0.a32_amount.toNat ≤ n.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      have L3 := ltu_sub_iw L hle
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shru (Val.shl v1 (.Vint a0.a32_amount)) _)
        (Val.zeroExt (Integers.Int.zwordsize - Integers.Int.unsigned n).toNat
          (Val.shru v1 (.Vint (mkAmount32 (Integers.Int.sub n a0.a32_amount)).a32_amount)))
      rw [mkAmount32_eq L3, zw_sub_toNat]
      cases v1 <;> simp [Val.shru, Val.shl, Val.zeroExt, L, L3, a0.a32_range] <;> try ld
      rw [Integers.Int.shru_shl _ _ _ a0.a32_range L, if_neg (by simpa using L2)]; ld
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_shruimmBase h1 L2, ?_⟩
      show Val.Lessdef (Val.shru (Val.shru v1 _) _) _
      rw [val_shru_shru v1 a0.a32_range L L2]; ld
    · exact ⟨_, eval_shruimmBase hx L, by ld⟩
  · rename_i s0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i hs
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shru (Val.zeroExt s0.toNat v1) _)
        (Val.zeroExt (s0 - Integers.Int.unsigned n).toNat
          (Val.shru v1 (.Vint (mkAmount32 n).a32_amount)))
      rw [mkAmount32_eq L]
      have hs' : s0.toNat = (s0 - Integers.Int.unsigned n).toNat + n.toNat := by
        have : Integers.Int.unsigned n = (n.toNat : _root_.Int) := rfl
        zomega
      cases v1 <;> simp [Val.shru, Val.zeroExt, L] <;> try ld
      rw [hs', Integers.Int.shru_zero_ext]; ld
    · rename_i hs
      refine ⟨_, eval_op0 rfl, ?_⟩
      have hs' : s0.toNat ≤ n.toNat := by
        have : Integers.Int.unsigned n = (n.toNat : _root_.Int) := rfl
        zomega
      cases v1 <;> simp [Val.shru, Val.zeroExt, L] <;> try ld
      rw [Integers.Int.shru_zero_ext_0 _ _ _ hs']; ld
  · exact ⟨_, eval_shruimmBase hx L, by ld⟩

theorem val_shr_zero (x : Val) : Val.Lessdef (Val.shr x (.Vint Integers.Int.zero)) x := by
  cases x <;> simp [Val.shr, Integers.Int.shr_zero] <;> first | ld | (rw [if_pos (by decide)]; ld)

theorem val_shr_shr (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int.iwordsize = true)
    (hn : Integers.Int.ltu n Integers.Int.iwordsize = true)
    (h : Integers.Int.ltu (Integers.Int.add a n) Integers.Int.iwordsize = true) :
    Val.shr (Val.shr v (.Vint a)) (.Vint n) = Val.shr v (.Vint (Integers.Int.add a n)) := by
  cases v <;> simp [Val.shr, ha, hn, h]
  exact Integers.Int.shr_shr _ _ _ (ltu_add_toNat ha hn)

theorem eval_shrimmBase {le : Letenv} {a : SelectOp.Expr} {x : Val} {n : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hn : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    CminorSel.EvalExpr ge sp e m le (shrimmBase a n) (Val.shr x (.Vint n)) := by
  unfold shrimmBase
  refine eval_op1 hx ?_
  show some (Val.shr x (.Vint (mkAmount32 n).a32_amount)) = _
  rw [mkAmount32_eq hn]

/-- `eval_shrimm` -/
theorem eval_shrimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shrimm a n) (fun x => Val.shr x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shrimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shr_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int.iwordsize
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  have hn' := Integers.Int.toNat_lt_of_ltu L
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.shr, L]; ld⟩
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    have ha' := Integers.Int.toNat_lt_of_ltu a0.a32_range
    split
    · rename_i L2
      have hlt : n.toNat < a0.a32_amount.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      have L3 := ltu_sub_iw a0.a32_range (Nat.le_of_lt hlt)
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shr (Val.shl v1 (.Vint a0.a32_amount)) _)
        (Val.shl (Val.signExt (Integers.Int.zwordsize - Integers.Int.unsigned a0.a32_amount).toNat v1)
          (.Vint (mkAmount32 (Integers.Int.sub a0.a32_amount n)).a32_amount))
      rw [mkAmount32_eq L3, zw_sub_toNat]
      cases v1 <;> simp [Val.shr, Val.shl, Val.signExt, L, L3, a0.a32_range] <;> try ld
      rw [Integers.Int.shr_shl _ _ _ a0.a32_range L, if_pos L2]; ld
    · rename_i L2
      have hle : a0.a32_amount.toNat ≤ n.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      have L3 := ltu_sub_iw L hle
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shr (Val.shl v1 (.Vint a0.a32_amount)) _)
        (Val.signExt (Integers.Int.zwordsize - Integers.Int.unsigned n).toNat
          (Val.shr v1 (.Vint (mkAmount32 (Integers.Int.sub n a0.a32_amount)).a32_amount)))
      rw [mkAmount32_eq L3, zw_sub_toNat]
      cases v1 <;> simp [Val.shr, Val.shl, Val.signExt, L, L3, a0.a32_range] <;> try ld
      rw [Integers.Int.shr_shl _ _ _ a0.a32_range L, if_neg (by simpa using L2)]; ld
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_shrimmBase h1 L2, ?_⟩
      show Val.Lessdef (Val.shr (Val.shr v1 _) _) _
      rw [val_shr_shr v1 a0.a32_range L L2]; ld
    · exact ⟨_, eval_shrimmBase hx L, by ld⟩
  · rename_i s0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hs1, hs2⟩ := hs
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shr (Val.signExt s0.toNat v1) _)
        (Val.signExt (s0 - Integers.Int.unsigned n).toNat
          (Val.shr v1 (.Vint (mkAmount32 n).a32_amount)))
      rw [mkAmount32_eq L]
      have hu : Integers.Int.unsigned n = (n.toNat : _root_.Int) := rfl
      have hzw : Integers.Int.zwordsize = (32 : _root_.Int) := rfl
      have hs' : s0.toNat = (s0 - Integers.Int.unsigned n).toNat + n.toNat := by zomega
      cases v1 <;> simp [Val.shr, Val.signExt, L] <;> try ld
      rw [hs', Integers.Int.shr_sign_ext _ _ _ (by zomega) (by zomega)]; ld
    · exact ⟨_, eval_shrimmBase hx L, by ld⟩
  · exact ⟨_, eval_shrimmBase hx L, by ld⟩

/-! ### Multiplication -/

/-- `eval_mulimm_base` -/
theorem eval_mulimmBase (n : Integers.Int) :
    UnarySound ge sp e m (mulimmBase n) (fun x => Val.mul x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold mulimmBase
  split
  · next i h =>
    obtain ⟨hi, hmul⟩ := Integers.Int.one_bits_single h
    obtain ⟨v, hv, hl⟩ := eval_shlimm i le a x hx
    refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
    cases x <;> simp [Val.mul, Val.shl, hi, hmul] <;> ld
  · next i j h =>
    obtain ⟨hi, hj, hmul⟩ := Integers.Int.one_bits_double h
    have hx0 : CminorSel.EvalExpr ge sp e m (x :: le) (.Eletvar 0) x := .Eletvar _ _ _ rfl
    obtain ⟨v1, hv1, hl1⟩ := eval_shlimm i (x :: le) _ x hx0
    obtain ⟨v2, hv2, hl2⟩ := eval_shlimm j (x :: le) _ x hx0
    obtain ⟨v, hv, hl⟩ := eval_add (x :: le) _ _ _ _ hv1 hv2
    refine ⟨v, .Elet _ _ _ _ _ hx hv, Val.lessdef_trans ?_ (Val.lessdef_trans (Val.add_lessdef hl1 hl2) hl)⟩
    cases x <;> simp [Val.mul, Val.shl, Val.add, hi, hj, hmul] <;> ld
  · exact ⟨_, eval_op2 (eval_op0 rfl) hx rfl, by rw [Val.mul_commut]; ld⟩

/-- `eval_mulimm` -/
theorem eval_mulimm (n : Integers.Int) :
    UnarySound ge sp e m (mulimm n) (fun x => Val.mul x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold mulimm
  by_cases h0 : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h0
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.mul, Integers.Int.mul_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int.eq n Integers.Int.one = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int.eq_spec _ _).mp h1
    exact ⟨x, hx, by cases x <;> simp [Val.mul, Integers.Int.mul_one] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.mul, Integers.Int.mul_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1', ho⟩ := inv_op1 hx
    cases ho
    obtain ⟨v', hv', hl'⟩ := eval_mulimmBase n le t2 v1 h1'
    obtain ⟨v'', hv'', hl''⟩ := eval_addimm (Integers.Int.mul n n2) le _ v' hv'
    refine ⟨v'', hv'', Val.lessdef_trans ?_ (Val.lessdef_trans (Val.add_lessdef hl' (.refl _)) hl'')⟩
    rw [Val.mul_add_distr_l]
    simp [Val.mul, Integers.Int.mul_commut]; ld
  · exact eval_mulimmBase n le a x hx

/-- `eval_mul` -/
theorem eval_mul : BinarySound ge sp e m SelectOp.mul Val.mul := by
  intro le a x b y hx hy
  unfold SelectOp.mul
  split
  · obtain rfl := inv_intconst hx
    rw [Val.mul_commut]; exact eval_mulimm _ le _ _ hy
  · obtain rfl := inv_intconst hy
    exact eval_mulimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

theorem loword_repr (z : _root_.Int) : Integers.Int64.loword (Integers.Int64.repr z) = Integers.Int.repr z := by
  show (BitVec.ofInt 64 z).truncate 32 = BitVec.ofInt 32 z
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

theorem val_shll_zero (n : Integers.Int64) :
    Val.shll (.Vlong n) (.Vint (mkAmount64 Integers.Int.zero).a64_amount) = .Vlong n := by
  have : Val.shll (.Vlong n) (.Vint (Integers.Int.zero_ext 6 Integers.Int.zero)) =
      .Vlong (Integers.Int64.shl n (Integers.Int64.repr
        (Integers.Int.unsigned (Integers.Int.zero_ext 6 Integers.Int.zero)))) := rfl
  show Val.shll (.Vlong n) (.Vint (Integers.Int.zero_ext 6 Integers.Int.zero)) = _
  rw [this]
  have h2 : Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.zero_ext 6 Integers.Int.zero)) =
      Integers.Int64.zero := by decide
  rw [h2, Integers.Int64.shl_zero]

theorem val_shrl_32 (n : Integers.Int64) :
    Val.shrl (.Vlong n) (.Vint (mkAmount64 (Integers.Int.repr 32)).a64_amount) =
      .Vlong (Integers.Int64.shr n (Integers.Int64.repr 32)) := by
  have : Val.shrl (.Vlong n) (.Vint (Integers.Int.zero_ext 6 (Integers.Int.repr 32))) =
      .Vlong (Integers.Int64.shr n (Integers.Int64.repr
        (Integers.Int.unsigned (Integers.Int.zero_ext 6 (Integers.Int.repr 32))))) := rfl
  show Val.shrl (.Vlong n) (.Vint (Integers.Int.zero_ext 6 (Integers.Int.repr 32))) = _
  rw [this]
  have h2 : Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.zero_ext 6 (Integers.Int.repr 32))) =
      Integers.Int64.repr 32 := by decide
  rw [h2]

theorem val_shrlu_32 (n : Integers.Int64) :
    Val.shrlu (.Vlong n) (.Vint (mkAmount64 (Integers.Int.repr 32)).a64_amount) =
      .Vlong (Integers.Int64.shru n (Integers.Int64.repr 32)) := by
  have : Val.shrlu (.Vlong n) (.Vint (Integers.Int.zero_ext 6 (Integers.Int.repr 32))) =
      .Vlong (Integers.Int64.shru n (Integers.Int64.repr
        (Integers.Int.unsigned (Integers.Int.zero_ext 6 (Integers.Int.repr 32))))) := rfl
  show Val.shrlu (.Vlong n) (.Vint (Integers.Int.zero_ext 6 (Integers.Int.repr 32))) = _
  rw [this]
  have h2 : Integers.Int64.repr (Integers.Int.unsigned (Integers.Int.zero_ext 6 (Integers.Int.repr 32))) =
      Integers.Int64.repr 32 := by decide
  rw [h2]

theorem mulhs_via_long (i j : Integers.Int) :
    Integers.Int64.loword (Integers.Int64.shr (Integers.Int64.mul (Integers.Int64.repr (Integers.Int.signed i))
      (Integers.Int64.repr (Integers.Int.signed j))) (Integers.Int64.repr 32)) = Integers.Int.mulhs i j := by
  have hi := SelectDivproofBounds.signed_range32 i
  have hj := SelectDivproofBounds.signed_range32 j
  have hp := Int.natAbs_mul (Integers.Int.signed i) (Integers.Int.signed j)
  have hb : (Integers.Int.signed i).natAbs * (Integers.Int.signed j).natAbs ≤ 2 ^ 31 * 2 ^ 31 :=
    Nat.mul_le_mul (by zomega) (by zomega)
  rw [← Integers.Int64.repr_mul, Integers.Int64.shr_div_two_p,
    Integers.Int64.signed_repr (by
      have : @Eq _root_.Int Integers.Int64.min_signed (-2^63) := by decide
      zomega) (by
      have : @Eq _root_.Int Integers.Int64.max_signed (2^63 - 1) := by decide
      zomega),
    show (Integers.Int64.repr 32 : Integers.Int64).toNat = 32 by decide, loword_repr]
  have hm : @Eq _root_.Int Integers.Int.modulus (2 ^ 32) := by decide
  show _ = Integers.Int.repr (Integers.Int.signed i * Integers.Int.signed j / Integers.Int.modulus)
  rw [hm]

theorem mulhu_via_long (i j : Integers.Int) :
    Integers.Int64.loword (Integers.Int64.shru (Integers.Int64.mul (Integers.Int64.repr (Integers.Int.unsigned i))
      (Integers.Int64.repr (Integers.Int.unsigned j))) (Integers.Int64.repr 32)) = Integers.Int.mulhu i j := by
  have hi := Integers.Int.unsigned_range i
  have hj := Integers.Int.unsigned_range j
  have hm : @Eq _root_.Int Integers.Int.modulus (2 ^ 32) := by decide
  have h0 : 0 ≤ Integers.Int.unsigned i * Integers.Int.unsigned j :=
    Int.mul_nonneg hi.1 hj.1
  have h1 : Integers.Int.unsigned i * Integers.Int.unsigned j < 2 ^ 64 := by
    have : Integers.Int.unsigned i * Integers.Int.unsigned j ≤ Integers.Int.unsigned i * (2 ^ 32 - 1) :=
      Int.mul_le_mul_of_nonneg_left (by zomega) hi.1
    have : Integers.Int.unsigned i * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Int.mul_le_mul_of_nonneg_right (by zomega) (by decide)
    zomega
  rw [← Integers.Int64.repr_mul, Integers.Int64.shru_div_two_p,
    Integers.Int64.unsigned_repr h0 (by
      have : @Eq _root_.Int Integers.Int64.max_unsigned (2^64 - 1) := by decide
      zomega),
    show (Integers.Int64.repr 32 : Integers.Int64).toNat = 32 by decide, loword_repr]
  show _ = Integers.Int.repr (Integers.Int.unsigned i * Integers.Int.unsigned j / Integers.Int.modulus)
  rw [hm]

/-- `eval_mulhs` -/
theorem eval_mulhs : BinarySound ge sp e m SelectOp.mulhs Val.mulhs := by
  intro le a x b y hx hy
  refine ⟨_, eval_op1 (eval_op1 (eval_op2 (eval_op1 hx rfl) (eval_op1 hy rfl) rfl) rfl) rfl, ?_⟩
  cases x <;> cases y <;> try ld
  simp only [evalShiftl, evalExtend, Val.longofint]
  rw [val_shll_zero, val_shll_zero]
  simp only [Val.mull]
  rw [val_shrl_32]
  simp only [Val.loword, Val.mulhs]
  rw [mulhs_via_long]; ld

/-- `eval_mulhu` -/
theorem eval_mulhu : BinarySound ge sp e m SelectOp.mulhu Val.mulhu := by
  intro le a x b y hx hy
  refine ⟨_, eval_op1 (eval_op1 (eval_op2 (eval_op1 hx rfl) (eval_op1 hy rfl) rfl) rfl) rfl, ?_⟩
  cases x <;> cases y <;> try ld
  simp only [evalShiftl, evalExtend, Val.longofintu]
  rw [val_shll_zero, val_shll_zero]
  simp only [Val.mull]
  rw [val_shrlu_32]
  simp only [Val.loword, Val.mulhu]
  rw [mulhu_via_long]; ld

end CMCONSTR

end SelectOpproof
end CC
