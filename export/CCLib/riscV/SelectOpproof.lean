/-
  Correctness of instruction selection for operators (RISC-V) — port of
  `riscV/SelectOpproof.v` (constants, addition, subtraction, opposite,
  immediate and general shifts).

  Every smart constructor of `SelectOp` is shown to compute (an
  approximation, in the sense of `Val.Lessdef`, of) the value of the
  operator it implements: `UnarySound cstr sem` / `BinarySound cstr sem`
  are Rocq's `unary_constructor_sound` / `binary_constructor_sound`.
-/
import CCLib.riscV.SelectOp
import CCLib.common.ValuesTheory
import CCLib.lib.IntegersShiftsExtra

namespace CC
namespace RiscV
namespace SelectOpproof

open Op CminorSel SelectOp

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- Close a `Val.Lessdef` goal that holds by reflexivity or because the left side is
`Vundef`. -/
macro "ld" : tactic => `(tactic| first | exact Val.Lessdef.refl _ | exact Val.Lessdef.undef _)

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

theorem lessdef_exists {le : Letenv} {a : SelectOp.Expr} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le a v) :
    ∃ v', CminorSel.EvalExpr ge sp e m le a v' ∧ Val.Lessdef v v' :=
  ⟨v, h, .refl _⟩

/-! ### Constants -/

/-- `eval_addrsymbol` -/
theorem eval_addrsymbol (le : Letenv) (id : Ident) (ofs : Integers.Ptrofs) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (addrsymbol id ofs) v ∧
      Val.Lessdef (Genv.symbolAddress ge id ofs) v :=
  lessdef_exists (eval_op0 rfl)

/-- `eval_addrstack` -/
theorem eval_addrstack (le : Letenv) (ofs : Integers.Ptrofs) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (addrstack ofs) v ∧
      Val.Lessdef (Val.offsetPtr sp ofs) v :=
  lessdef_exists (eval_op0 rfl)

/-! ### Addition, opposite, subtraction -/

/-- On this 64-bit target, adding a 32-bit integer to a pointer is undefined. -/
theorem symbolAddress_add_undef (id : Ident) (ofs : Integers.Ptrofs) (n : Integers.Int) :
    Val.add (Genv.symbolAddress ge id ofs) (.Vint n) = .Vundef := by
  unfold Genv.symbolAddress; split <;> simp [Val.add, Archi.ptr64]

theorem offsetPtr_add_undef (sp : Val) (ofs : Integers.Ptrofs) (n : Integers.Int) :
    Val.add (Val.offsetPtr sp ofs) (.Vint n) = .Vundef := by
  cases sp <;> simp [Val.offsetPtr, Val.add, Archi.ptr64]

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
    · obtain rfl := inv_intconst hx
      exact ⟨_, eval_op0 rfl, by simp [Val.add, Integers.Int.add_commut]; exact .refl _⟩
    · have h0 := inv_op0 hx
      cases h0
      exact ⟨_, eval_op0 rfl, by dsimp only; rw [symbolAddress_add_undef]; ld⟩
    · have h0 := inv_op0 hx
      cases h0
      exact ⟨_, eval_op0 rfl, by dsimp only; rw [offsetPtr_add_undef]; ld⟩
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.add (Val.add v1 _) _) _
      rw [Val.add_assoc]; simp [Val.add, Integers.Int.add_commut]; ld
    · exact ⟨_, eval_op1 hx rfl, .refl _⟩

theorem add_offsetPtr_undef (v1 : Val) (n1 : Integers.Int) (sp : Val) (n2 : Integers.Ptrofs) :
    Val.add (Val.add v1 (.Vint n1)) (Val.offsetPtr sp n2) = .Vundef := by
  cases v1 <;> cases sp <;> simp [Val.offsetPtr, Val.add, Archi.ptr64]

theorem offsetPtr_add_undef' (sp : Val) (n1 : Integers.Ptrofs) (v2 : Val) (n2 : Integers.Int) :
    Val.add (Val.offsetPtr sp n1) (Val.add v2 (.Vint n2)) = .Vundef := by
  cases v2 <;> cases sp <;> simp [Val.offsetPtr, Val.add, Archi.ptr64]

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
    have h0 := inv_op0 hy
    cases ho1; cases h0
    exact ⟨_, eval_op2 (eval_op0 rfl) h1 rfl, by rw [add_offsetPtr_undef]; ld⟩
  · have h0 := inv_op0 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2; cases h0
    exact ⟨_, eval_op2 (eval_op0 rfl) h2 rfl, by rw [offsetPtr_add_undef']; ld⟩
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    rw [Val.add_assoc, Val.add_commut (.Vint _) y, ← Val.add_assoc]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Oadd) h1 hy rfl)
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    rw [← Val.add_assoc]
    exact eval_addimm _ le _ _ (eval_op2 (op := .Oadd) hx h2 rfl)
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

theorem val_sub_add_l (v1 v2 : Val) (i : Integers.Int) :
    Val.sub (Val.add v1 (.Vint i)) v2 = Val.add (Val.sub v1 v2) (.Vint i) := by
  cases v1 <;> cases v2 <;> simp [Val.sub, Val.add, Archi.ptr64, Integers.Int.sub_add_l]

theorem val_sub_add_r (v1 v2 : Val) (i : Integers.Int) :
    Val.sub v1 (Val.add v2 (.Vint i)) = Val.add (Val.sub v1 v2) (.Vint (Integers.Int.neg i)) := by
  cases v1 <;> cases v2 <;> simp [Val.sub, Val.add, Archi.ptr64]
  rw [Integers.Int.add_commut, Integers.Int.sub_add_r]

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
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

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
  · exact ⟨_, eval_op1 hx rfl, val_sub_zero_neg _⟩

end CMCONSTR

end SelectOpproof
end RiscV
end CC
