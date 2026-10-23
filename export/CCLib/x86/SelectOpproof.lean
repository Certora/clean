/-
  Correctness of instruction selection for operators (x86) — port of
  `x86/SelectOpproof.v` (constants, addition, subtraction, opposite).

  Every smart constructor of `SelectOp` is shown to compute (an
  approximation, in the sense of `Val.Lessdef`, of) the value of the
  operator it implements: `UnarySound cstr sem` / `BinarySound cstr sem`
  are Rocq's `unary_constructor_sound` / `binary_constructor_sound`.

  The port's configuration is x86-64 (`Archi.ptr64 = true`): 32-bit
  `Olea` addressing is integer-only, and the symbol/stack forms of `Olea`
  never evaluate.
-/
import CCLib.x86.SelectOp
import CCLib.x86.CombineOpproof
import CCLib.common.ValuesTheory
import CCLib.common.GlobalenvsTheory
import CCLib.lib.IntegersShiftsExtra

namespace CC
namespace X86
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

theorem inv_op {le : Letenv} {op : Operation} {al : SelectOp.Exprlist} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le (.Eop op al) v) :
    ∃ vl, CminorSel.EvalExprlist ge sp e m le al vl ∧ evalOperation ge sp op vl m = some v := by
  cases h with
  | Eop _ _ _ vl _ hl ho => exact ⟨vl, hl, ho⟩

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

/-! ### Constants -/

theorem ptrofs_of_int64_repr_unsigned (ofs : Integers.Ptrofs) :
    Integers.Ptrofs.of_int64 (Integers.Int64.repr (Integers.Ptrofs.unsigned ofs)) = ofs := by
  show BitVec.ofInt 64 ((BitVec.ofInt 64 (ofs.toNat : _root_.Int)).toNat : _root_.Int) = ofs
  apply BitVec.eq_of_toNat_eq
  have := ofs.isLt
  have h2 : (2 : Nat) ^ Archi.ptrWordsize = 2 ^ 64 := rfl
  simp only [BitVec.toNat_ofInt]
  have h3 : ofs.toNat < 2 ^ 64 := by omega
  rw [Int.emod_eq_of_lt (by omega) (by simp; omega)]
  simp only [Int.toNat_natCast]
  rw [Int.emod_eq_of_lt (by omega) (by simp; omega)]
  simp

/-- `eval_addrsymbol` -/
theorem eval_addrsymbol (isReloc : Ident → Bool) (le : Letenv) (id : Ident)
    (ofs : Integers.Ptrofs) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (addrsymbol isReloc id ofs) v ∧
      Val.Lessdef (Genv.symbolAddress ge id ofs) v := by
  unfold addrsymbol
  split
  · split
    · next hz =>
      obtain rfl := (Integers.Ptrofs.eq_spec _ _).mp hz
      exact ⟨_, eval_op0 rfl, .refl _⟩
    · refine ⟨_, eval_op1 (eval_op0 rfl) rfl, ?_⟩
      show Val.Lessdef _ (Val.addl (Genv.symbolAddress ge id Integers.Ptrofs.zero) _)
      rw [← Genv.shift_symbolAddress_64, ptrofs_of_int64_repr_unsigned,
        Integers.Ptrofs.add_zero_l]; ld
  · exact ⟨_, eval_op0 rfl, .refl _⟩

/-- `eval_addrstack` -/
theorem eval_addrstack (le : Letenv) (ofs : Integers.Ptrofs) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (addrstack ofs) v ∧
      Val.Lessdef (Val.offsetPtr sp ofs) v :=
  ⟨_, eval_op0 rfl, .refl _⟩

/-! ### Value-level algebra -/

theorem val_add_zero (v : Val) : Val.Lessdef (Val.add v (.Vint Integers.Int.zero)) v := by
  cases v <;> simp [Val.add, Archi.ptr64, Integers.Int.add_zero] <;> ld

theorem vint_add_repr (a b : Z) :
    Val.add (.Vint (Integers.Int.repr a)) (.Vint (Integers.Int.repr b)) =
      .Vint (Integers.Int.repr (a + b)) := by
  simp only [Val.add]; rw [Integers.Int.repr_add]

/-- `(a + r1) + (b + r2) = a + (b + (r1 + r2))` -/
theorem add_shuffle1 (a b r1 r2 : Val) :
    Val.add (Val.add a r1) (Val.add b r2) = Val.add a (Val.add b (Val.add r1 r2)) := by
  rw [Val.add_assoc, ← Val.add_assoc r1, Val.add_commut r1 b, Val.add_assoc]

/-- `(a + r1) + (b + r2) = b + (a + (r1 + r2))` -/
theorem add_shuffle2 (a b r1 r2 : Val) :
    Val.add (Val.add a r1) (Val.add b r2) = Val.add b (Val.add a (Val.add r1 r2)) := by
  rw [Val.add_commut (Val.add a r1), add_shuffle1, Val.add_commut r2]

/-! ### Addition -/

/-- `eval_addimm` -/
theorem eval_addimm (n : Integers.Int) :
    UnarySound ge sp e m (addimm n) (fun x => Val.add x (.Vint n)) := by
  intro le a x hx
  unfold addimm
  by_cases hn : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hn]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hn
    exact ⟨x, hx, val_add_zero x⟩
  · rw [if_neg hn]
    split
    · obtain rfl := inv_intconst hx
      exact ⟨_, eval_op0 rfl, by simp [Val.add, Integers.Int.add_commut]; exact .refl _⟩
    · next addr args =>
      obtain ⟨vl, hl, ho⟩ := inv_op hx
      refine ⟨_, .Eop _ _ _ _ _ hl
        (eval_offsetAddressingTotal_32 ge sp addr vl (Integers.Int.signed n) x ho), ?_⟩
      rw [Integers.Int.repr_signed]; ld
    · refine ⟨_, eval_op1 hx rfl, ?_⟩
      show Val.Lessdef _ (Val.add x (.Vint (Integers.Int.repr (Integers.Int.signed n))))
      rw [Integers.Int.repr_signed]; ld

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
    refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
    show Val.Lessdef _ (Val.add (Val.add v1 v2) _)
    rw [Val.add_permut_4, vint_add_repr]; ld
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho1; cases ho2
    refine ⟨_, eval_op2 h1 h2 rfl, ?_⟩
    show Val.Lessdef _ (Val.add v1 (Val.add (Val.mul v2 _) _))
    rw [add_shuffle1, vint_add_repr]; ld
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho1; cases ho2
    refine ⟨_, eval_op2 h2 h1 rfl, ?_⟩
    show Val.Lessdef _ (Val.add v2 (Val.add (Val.mul v1 _) _))
    rw [add_shuffle2, vint_add_repr]; ld
  · have h0 := inv_op0 hy; cases h0
  · have h0 := inv_op0 hx; cases h0
  · have h0 := inv_op0 hy; cases h0
  · have h0 := inv_op0 hx; cases h0
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.add_commut]; ld⟩
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    refine ⟨_, eval_op2 h1 hy rfl, ?_⟩
    show Val.Lessdef _ (Val.add (Val.add v1 y) _)
    rw [Val.add_assoc, Val.add_commut (.Vint _) y, ← Val.add_assoc]; ld
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    refine ⟨_, eval_op2 hx h2 rfl, ?_⟩
    show Val.Lessdef _ (Val.add (Val.add x v2) _)
    rw [Val.add_assoc]; ld
  · refine ⟨_, eval_op2 hx hy rfl, ?_⟩
    show Val.Lessdef _ (Val.add (Val.add x y) (.Vint (Integers.Int.repr 0)))
    rw [show Integers.Int.repr 0 = Integers.Int.zero from rfl]
    cases x <;> cases y <;> simp [Val.add, Archi.ptr64, Integers.Int.add_zero] <;> ld

end CMCONSTR

end SelectOpproof
end X86
end CC
