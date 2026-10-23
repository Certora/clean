/-
  Soundness of the recognition of combined operations — port of
  `x86/CombineOpproof.v`: `get_op_sound`, `combine_compimm_ne_0_sound`,
  `combine_compimm_eq_0_sound`, `combine_compimm_eq_1_sound`,
  `combine_compimm_ne_1_sound`, `combine_cond_sound`, `combine_cond'_sound`,
  `combine_addr_32_sound`, `combine_addr_64_sound`, `combine_addr_sound`,
  `combine_op_sound`.

  Also ports the two lemmas of `x86/Op.v` that these proofs use,
  `eval_offset_addressing_total_32` and `eval_offset_addressing_total_64`.

  As in Rocq, everything is stated for a valuation `valu` of value numbers and
  a function `get` that only returns right-hand sides satisfied by `valu`
  (hypothesis `get_sound`).
-/
import CCLib.x86.CombineOp
import CCLib.common.ValuesTheory
import CCLib.common.ValuesInject
import CCLib.common.ValuesLemmas
import CCLib.common.GlobalenvsTheory
import CCLib.x86.OpTheory

namespace CC
namespace X86

namespace Op

private theorem int_repr_add (x y : Z) :
    Integers.Int.add (Integers.Int.repr x) (Integers.Int.repr y) = Integers.Int.repr (x + y) :=
  (Integers.Int.repr_add x y).symm

private theorem int64_repr_add (x y : Z) :
    Integers.Int64.add (Integers.Int64.repr x) (Integers.Int64.repr y) =
      Integers.Int64.repr (x + y) :=
  (Integers.Int64.repr_add x y).symm

/-- `Op.eval_offset_addressing_total_32` -/
theorem eval_offsetAddressingTotal_32 {F V : Type} (ge : Genv F V) (sp : Val)
    (addr : Addressing) (args : List Val) (delta : Z) (v : Val)
    (h : evalAddressing32 ge sp addr args = some v) :
    evalAddressing32 ge sp (offsetAddressingTotal addr delta) args =
      some (Val.add v (.Vint (Integers.Int.repr delta))) := by
  cases addr <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [evalAddressing32, offsetAddressingTotal, Archi.ptr64, if_true] at h ⊢ <;>
    (try cases h) <;>
    simp only [Option.some.injEq, Val.add_assoc] <;>
    first
      | (congr 1; exact (int_repr_add _ _).symm)
      | (congr 2; exact (int_repr_add _ _).symm)
      | (congr 3; exact (int_repr_add _ _).symm)

/-- `Op.eval_offset_addressing_total_64` -/
theorem eval_offsetAddressingTotal_64 {F V : Type} (ge : Genv F V) (sp : Val)
    (addr : Addressing) (args : List Val) (delta : Z) (v : Val)
    (h : evalAddressing64 ge sp addr args = some v) :
    evalAddressing64 ge sp (offsetAddressingTotal addr delta) args =
      some (Val.addl v (.Vlong (Integers.Int64.repr delta))) := by
  have B : Integers.Ptrofs.repr delta = Integers.Ptrofs.of_int64 (Integers.Int64.repr delta) :=
    (Integers.MI.repr_unsigned (w := 64) _).symm
  have L : ∀ a b, Val.addl (.Vlong a) (.Vlong b) = .Vlong (Integers.Int64.add a b) :=
    fun _ _ => rfl
  cases addr <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [evalAddressing64, offsetAddressingTotal, Archi.ptr64, if_true] at h ⊢ <;>
    (try cases h) <;>
    simp only [Option.some.injEq, Val.addl_assoc, L, int64_repr_add]
  · rw [B, Genv.shift_symbolAddress_64]
  · cases sp <;> simp [Val.offsetPtr, Val.addl, Archi.ptr64, Integers.Ptrofs.add_assoc, B]

end Op

namespace CombineOp

open CSEdomain Op
open CC.CSEdomain (Valnum combineComparison combineComparison_cmp_sound
  combineComparison_cmpu_sound combineComparison_cmpl_sound combineComparison_cmplu_sound)

/-- `Int.eq (Int.xor x y) Int.zero = Int.eq x y` (from `Int.xor_is_zero`). -/
private theorem eq_xor_zero (x y : Integers.Int) :
    Integers.Int.eq (Integers.Int.xor x y) Integers.Int.zero = Integers.Int.eq x y := by
  have h := Integers.Int.xor_is_zero x y
  simp only [Integers.Int.eq, Integers.MI.eq] at *
  cases h1 : (Integers.Int.xor x y == Integers.Int.zero) <;>
    cases h2 : (x == y) <;> simp_all

section COMBINE
variable {F V : Type} {ge : Genv F V} {sp : Val} {m : Mem} {get : Valnum → Option Rhs}
  {valu : Valnum → Val}
  (get_sound : ∀ v rhs, get v = some rhs → RhsEvalTo valu ge sp m rhs (valu v))
include get_sound

/-- `CombineOpproof.get_op_sound` -/
theorem get_op_sound {v : Valnum} {op : Operation} {vl : List Valnum}
    (h : get v = some (.Op op vl)) : evalOperation ge sp op (vl.map valu) m = some (valu v) := by
  have := get_sound _ _ h
  cases this
  assumption

/-- `CombineOpproof.combine_compimm_ne_0_sound` -/
theorem combine_compimm_ne_0_sound {x : Valnum} {cond : Condition} {args : List Valnum}
    (h : combineCompimmNe0 get x = some (cond, args)) :
    evalCondition cond (args.map valu) m = Val.cmp_bool .Cne (valu x) (.Vint Integers.Int.zero) ∧
    evalCondition cond (args.map valu) m =
      Val.cmpu_bool (Mem.validPointer m) .Cne (valu x) (.Vint Integers.Int.zero) := by
  unfold combineCompimmNe0 at h
  cases hg : get x with
  | none => rw [hg] at h; cases h
  | some r =>
    rw [hg] at h
    cases r with
    | Load => cases h
    | Builtin => cases h
    | Op op ys =>
      cases op
      all_goals try (cases h; done)
      · -- `Oandimm`
        rename_i n
        cases h
        have E := get_op_sound get_sound hg
        rcases args with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
        change some (Val.and (valu y) (.Vint n)) = some (valu x) at E
        rw [← Option.some.inj E]
        simp only [List.map, evalCondition]
        cases valu y <;> simp [Val.and, Val.maskzero_bool, Val.cmp_bool, Val.cmpu_bool,
          Integers.Int.cmp, Integers.Int.cmpu, Integers.MI.cmp, Integers.MI.cmpu] <;> rfl
      · -- `Oxorimm`
        rename_i n
        cases h
        have E := get_op_sound get_sound hg
        rcases args with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
        change some (Val.xor (valu y) (.Vint n)) = some (valu x) at E
        rw [← Option.some.inj E]
        simp only [List.map, evalCondition]
        cases valu y <;> simp [Val.xor, Val.cmp_bool, Val.cmpu_bool, Integers.Int.cmp,
          Integers.Int.cmpu, Integers.MI.cmp, Integers.MI.cmpu]
        exact (eq_xor_zero _ _).symm
      · -- `Ocmp`
        cases h
        have E := get_op_sound get_sound hg
        change some (Val.ofOptbool (evalCondition cond (args.map valu) m)) = some (valu x) at E
        rw [← Option.some.inj E]
        cases evalCondition cond (args.map valu) m with
        | none => exact ⟨rfl, rfl⟩
        | some b => cases b <;> exact ⟨rfl, rfl⟩

/-- `CombineOpproof.combine_compimm_eq_0_sound` -/
theorem combine_compimm_eq_0_sound {x : Valnum} {cond : Condition} {args : List Valnum}
    (h : combineCompimmEq0 get x = some (cond, args)) :
    evalCondition cond (args.map valu) m = Val.cmp_bool .Ceq (valu x) (.Vint Integers.Int.zero) ∧
    evalCondition cond (args.map valu) m =
      Val.cmpu_bool (Mem.validPointer m) .Ceq (valu x) (.Vint Integers.Int.zero) := by
  unfold combineCompimmEq0 at h
  cases hg : get x with
  | none => rw [hg] at h; cases h
  | some r =>
    rw [hg] at h
    cases r with
    | Load => cases h
    | Builtin => cases h
    | Op op ys =>
      cases op
      all_goals try (cases h; done)
      · -- `Oandimm`
        rename_i n
        cases h
        have E := get_op_sound get_sound hg
        rcases args with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
        change some (Val.and (valu y) (.Vint n)) = some (valu x) at E
        rw [← Option.some.inj E]
        simp only [List.map, evalCondition]
        cases valu y <;> simp [Val.and, Val.maskzero_bool, Val.cmp_bool, Val.cmpu_bool,
          Integers.Int.cmp, Integers.Int.cmpu, Integers.MI.cmp, Integers.MI.cmpu] <;> rfl
      · -- `Oxorimm`
        rename_i n
        cases h
        have E := get_op_sound get_sound hg
        rcases args with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
        change some (Val.xor (valu y) (.Vint n)) = some (valu x) at E
        rw [← Option.some.inj E]
        simp only [List.map, evalCondition]
        cases valu y <;> simp [Val.xor, Val.cmp_bool, Val.cmpu_bool, Integers.Int.cmp,
          Integers.Int.cmpu, Integers.MI.cmp, Integers.MI.cmpu]
        exact (eq_xor_zero _ _).symm
      · -- `Ocmp`
        rename_i c
        have E := get_op_sound get_sound hg
        change some (Val.ofOptbool (evalCondition c (ys.map valu) m)) = some (valu x) at E
        obtain ⟨rfl, rfl⟩ : negateCondition c = cond ∧ ys = args := by
          cases h; exact ⟨rfl, rfl⟩
        rw [← Option.some.inj E, eval_negateCondition]
        generalize evalCondition c _ m = o
        rcases o with _ | _ | _ <;> exact ⟨rfl, rfl⟩

/-- `CombineOpproof.combine_compimm_eq_1_sound` -/
theorem combine_compimm_eq_1_sound {x : Valnum} {cond : Condition} {args : List Valnum}
    (h : combineCompimmEq1 get x = some (cond, args)) :
    evalCondition cond (args.map valu) m = Val.cmp_bool .Ceq (valu x) (.Vint Integers.Int.one) ∧
    evalCondition cond (args.map valu) m =
      Val.cmpu_bool (Mem.validPointer m) .Ceq (valu x) (.Vint Integers.Int.one) := by
  unfold combineCompimmEq1 at h
  cases hg : get x with
  | none => rw [hg] at h; cases h
  | some r =>
    rw [hg] at h
    cases r with
    | Load => cases h
    | Builtin => cases h
    | Op op ys =>
      cases op
      all_goals try (cases h; done)
      · -- `Ocmp`
        rename_i c
        have E := get_op_sound get_sound hg
        change some (Val.ofOptbool (evalCondition c (ys.map valu) m)) = some (valu x) at E
        obtain ⟨rfl, rfl⟩ : c = cond ∧ ys = args := by
          cases h; exact ⟨rfl, rfl⟩
        rw [← Option.some.inj E]
        generalize evalCondition c _ m = o
        rcases o with _ | _ | _ <;> exact ⟨rfl, rfl⟩

/-- `CombineOpproof.combine_compimm_ne_1_sound` -/
theorem combine_compimm_ne_1_sound {x : Valnum} {cond : Condition} {args : List Valnum}
    (h : combineCompimmNe1 get x = some (cond, args)) :
    evalCondition cond (args.map valu) m = Val.cmp_bool .Cne (valu x) (.Vint Integers.Int.one) ∧
    evalCondition cond (args.map valu) m =
      Val.cmpu_bool (Mem.validPointer m) .Cne (valu x) (.Vint Integers.Int.one) := by
  unfold combineCompimmNe1 at h
  cases hg : get x with
  | none => rw [hg] at h; cases h
  | some r =>
    rw [hg] at h
    cases r with
    | Load => cases h
    | Builtin => cases h
    | Op op ys =>
      cases op
      all_goals try (cases h; done)
      · -- `Ocmp`
        rename_i c
        have E := get_op_sound get_sound hg
        change some (Val.ofOptbool (evalCondition c (ys.map valu) m)) = some (valu x) at E
        obtain ⟨rfl, rfl⟩ : negateCondition c = cond ∧ ys = args := by
          cases h; exact ⟨rfl, rfl⟩
        rw [← Option.some.inj E, eval_negateCondition]
        generalize evalCondition c _ m = o
        rcases o with _ | _ | _ <;> exact ⟨rfl, rfl⟩

/-- `CombineOpproof.combine_cond_sound` -/
theorem combine_cond_sound {cond : Condition} {args : List Valnum} {cond' : Condition}
    {args' : List Valnum} (h : combineCond get cond args = some (cond', args')) :
    evalCondition cond' (args'.map valu) m = evalCondition cond (args.map valu) m := by
  have hne : ∀ n x c' a', combineNe get n x = some (c', a') →
      evalCondition c' (a'.map valu) m = Val.cmp_bool .Cne (valu x) (.Vint n) ∧
      evalCondition c' (a'.map valu) m =
        Val.cmpu_bool (Mem.validPointer m) .Cne (valu x) (.Vint n) := by
    intro n x c' a' h
    unfold combineNe at h
    split at h
    · subst n; exact combine_compimm_ne_0_sound get_sound h
    · split at h
      · subst n; exact combine_compimm_ne_1_sound get_sound h
      · cases h
  have heq : ∀ n x c' a', combineEq get n x = some (c', a') →
      evalCondition c' (a'.map valu) m = Val.cmp_bool .Ceq (valu x) (.Vint n) ∧
      evalCondition c' (a'.map valu) m =
        Val.cmpu_bool (Mem.validPointer m) .Ceq (valu x) (.Vint n) := by
    intro n x c' a' h
    unfold combineEq at h
    split at h
    · subst n; exact combine_compimm_eq_0_sound get_sound h
    · split at h
      · subst n; exact combine_compimm_eq_1_sound get_sound h
      · cases h
  cases cond
  all_goals first
    | (cases h; done)
    | (rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> cases h; done)
    | (rename_i c n; cases c <;> rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done))
  · exact (heq n x _ _ h).1
  · exact (hne n x _ _ h).1
  · exact (heq n x _ _ h).2
  · exact (hne n x _ _ h).2

omit get_sound in
/-- `CombineOpproof.combine_cond'_sound` -/
theorem combine_cond'_sound {cond : Condition} {args : List Valnum} {res res' : Bool}
    (h : combineCond' cond args = some res')
    (h2 : evalCondition cond (args.map valu) m = some res) : res = res' := by
  cases cond
  all_goals first
    | (cases h; done)
    | (rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> try (cases h; done))
  · exact combineComparison_cmp_sound valu _ x y res res' h h2
  · exact combineComparison_cmpu_sound valu m _ x y res res' h h2
  · exact combineComparison_cmpl_sound valu _ x y res res' h h2
  · exact combineComparison_cmplu_sound valu m _ x y res res' h h2

/-- `CombineOpproof.combine_addr_32_sound` -/
theorem combine_addr_32_sound {addr : Addressing} {args : List Valnum} {addr' : Addressing}
    {args' : List Valnum} (h : combineAddr32 get addr args = some (addr', args')) :
    evalAddressing32 ge sp addr' (args'.map valu) = evalAddressing32 ge sp addr (args.map valu) := by
  cases addr
  all_goals first
    | (cases h; done)
    | (rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done))
  rename_i n
  simp only [combineAddr32] at h
  split at h
  · rename_i a ys hgx
    split at h
    · rename_i a' hoff
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [offsetAddressing] at hoff
      split at hoff
      · cases hoff
        have E := get_op_sound get_sound hgx
        change evalAddressing32 ge sp a (ys.map valu) = some (valu x) at E
        rw [eval_offsetAddressingTotal_32 ge sp a _ n _ E]
        rfl
      · cases hoff
    · cases h
  · cases h

/-- `CombineOpproof.combine_addr_64_sound` -/
theorem combine_addr_64_sound {addr : Addressing} {args : List Valnum} {addr' : Addressing}
    {args' : List Valnum} (h : combineAddr64 get addr args = some (addr', args')) :
    evalAddressing64 ge sp addr' (args'.map valu) = evalAddressing64 ge sp addr (args.map valu) := by
  cases addr
  all_goals first
    | (cases h; done)
    | (rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done))
  rename_i n
  simp only [combineAddr64] at h
  split at h
  · rename_i a ys hgx
    split at h
    · rename_i a' hoff
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [offsetAddressing] at hoff
      split at hoff
      · cases hoff
        have E := get_op_sound get_sound hgx
        change evalAddressing64 ge sp a (ys.map valu) = some (valu x) at E
        rw [eval_offsetAddressingTotal_64 ge sp a _ n _ E]
        rfl
      · cases hoff
    · cases h
  · cases h

/-- `CombineOpproof.combine_addr_sound` -/
theorem combine_addr_sound {addr : Addressing} {args : List Valnum} {addr' : Addressing}
    {args' : List Valnum} (h : combineAddr get addr args = some (addr', args')) :
    evalAddressing ge sp addr' (args'.map valu) = evalAddressing ge sp addr (args.map valu) := by
  simp only [combineAddr, evalAddressing, Archi.ptr64, if_true] at h ⊢
  exact combine_addr_64_sound get_sound h

/-- `CombineOpproof.combine_op_sound` -/
theorem combine_op_sound {op : Operation} {args : List Valnum} {op' : Operation}
    {args' : List Valnum} {r : Val} (h : combineOp get op args = some (op', args'))
    (h2 : evalOperation ge sp op (args.map valu) m = some r) :
    ∃ r', evalOperation ge sp op' (args'.map valu) m = some r' ∧ Val.Lessdef r r' := by
  cases op
  all_goals try (cases h; done)
  case Olea addr =>
    simp only [combineOp] at h
    split at h
    · rename_i a2 args2 hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨r, ?_, .refl _⟩
      rw [← h2]
      exact combine_addr_32_sound get_sound hc
    · cases h
  case Oleal addr =>
    simp only [combineOp] at h
    split at h
    · rename_i a2 args2 hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨r, ?_, .refl _⟩
      rw [← h2]
      exact combine_addr_64_sound get_sound hc
    · cases h
  case Oandimm n =>
    rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done)
    simp only [combineOp] at h
    split at h
    · rename_i mm ys hgx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have E := get_op_sound get_sound hgx
      rcases ys with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
      change some (Val.and (valu y) (.Vint mm)) = some (valu x) at E
      change some (Val.and (valu x) (.Vint n)) = some r at h2
      refine ⟨Val.and (valu y) (.Vint (Integers.Int.and mm n)), rfl, ?_⟩
      rw [← Option.some.inj h2, ← Option.some.inj E, Val.and_assoc]
      exact .refl _
    · cases h
  case Oorimm n =>
    rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done)
    simp only [combineOp] at h
    split at h
    · rename_i mm ys hgx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have E := get_op_sound get_sound hgx
      rcases ys with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
      change some (Val.or (valu y) (.Vint mm)) = some (valu x) at E
      change some (Val.or (valu x) (.Vint n)) = some r at h2
      refine ⟨Val.or (valu y) (.Vint (Integers.Int.or mm n)), rfl, ?_⟩
      rw [← Option.some.inj h2, ← Option.some.inj E, Val.or_assoc]
      exact .refl _
    · cases h
  case Oxorimm n =>
    rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done)
    simp only [combineOp] at h
    split at h
    · rename_i mm ys hgx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have E := get_op_sound get_sound hgx
      rcases ys with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
      change some (Val.xor (valu y) (.Vint mm)) = some (valu x) at E
      change some (Val.xor (valu x) (.Vint n)) = some r at h2
      refine ⟨Val.xor (valu y) (.Vint (Integers.Int.xor mm n)), rfl, ?_⟩
      rw [← Option.some.inj h2, ← Option.some.inj E, Val.xor_assoc]
      exact .refl _
    · cases h
  case Oandlimm n =>
    rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done)
    simp only [combineOp] at h
    split at h
    · rename_i mm ys hgx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have E := get_op_sound get_sound hgx
      rcases ys with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
      change some (Val.andl (valu y) (.Vlong mm)) = some (valu x) at E
      change some (Val.andl (valu x) (.Vlong n)) = some r at h2
      refine ⟨Val.andl (valu y) (.Vlong (Integers.Int64.and mm n)), rfl, ?_⟩
      rw [← Option.some.inj h2, ← Option.some.inj E, Val.andl_assoc]
      exact .refl _
    · cases h
  case Oorlimm n =>
    rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done)
    simp only [combineOp] at h
    split at h
    · rename_i mm ys hgx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have E := get_op_sound get_sound hgx
      rcases ys with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
      change some (Val.orl (valu y) (.Vlong mm)) = some (valu x) at E
      change some (Val.orl (valu x) (.Vlong n)) = some r at h2
      refine ⟨Val.orl (valu y) (.Vlong (Integers.Int64.or mm n)), rfl, ?_⟩
      rw [← Option.some.inj h2, ← Option.some.inj E, Val.orl_assoc]
      exact .refl _
    · cases h
  case Oxorlimm n =>
    rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> try (cases h; done)
    simp only [combineOp] at h
    split at h
    · rename_i mm ys hgx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have E := get_op_sound get_sound hgx
      rcases ys with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try cases E
      change some (Val.xorl (valu y) (.Vlong mm)) = some (valu x) at E
      change some (Val.xorl (valu x) (.Vlong n)) = some r at h2
      refine ⟨Val.xorl (valu y) (.Vlong (Integers.Int64.xor mm n)), rfl, ?_⟩
      rw [← Option.some.inj h2, ← Option.some.inj E, Val.xorl_assoc]
      exact .refl _
    · cases h
  case Ocmp cond =>
    simp only [combineOp] at h
    change some (Val.ofOptbool (evalCondition cond (args.map valu) m)) = some r at h2
    rw [← Option.some.inj h2]
    split at h
    · rename_i b hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases he : evalCondition cond (args.map valu) m with
      | none => cases b <;> exact ⟨_, rfl, .undef _⟩
      | some res =>
        have := combine_cond'_sound hb he
        subst this
        cases res <;> exact ⟨_, rfl, .refl _⟩
    · split at h
      · rename_i c2 a2 hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨_, rfl, ?_⟩
        rw [combine_cond_sound get_sound hc]
        exact .refl _
      · cases h
  case Osel cond ty =>
    rcases args with _ | ⟨x, _ | ⟨y, args⟩⟩ <;> try (cases h; done)
    simp only [combineOp] at h
    change some (Val.select (evalCondition cond (args.map valu) m) (valu x) (valu y) ty) =
      some r at h2
    rw [← Option.some.inj h2]
    split at h
    · rename_i b hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨_, rfl, ?_⟩
      cases he : evalCondition cond (args.map valu) m with
      | none => exact .undef _
      | some res =>
        have := combine_cond'_sound hb he
        subst this
        cases res <;> exact Val.lessdef_normalize _ _
    · split at h
      · rename_i hxy
        subst hxy
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨_, rfl, ?_⟩
        cases evalCondition cond (args.map valu) m with
        | none => exact .undef _
        | some b => cases b <;> exact Val.lessdef_normalize _ _
      · split at h
        · rename_i c2 a2 hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨_, rfl, ?_⟩
          rw [combine_cond_sound get_sound hc]
          exact .refl _
        · cases h

end COMBINE

end CombineOp
end X86
end CC
