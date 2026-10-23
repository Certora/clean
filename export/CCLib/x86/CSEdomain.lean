/-
  [x86-64 instance of `CCLib/backend/CSEdomain.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  The abstract domain for value numbering (common subexpression
  elimination) — port of `backend/CSEdomain.v` (whole file): `valnum`,
  `rhs`, `equation`, `rhs_compat`, `compat_rhs`, `numbering`,
  `empty_numbering`, `valnums_rhs`, `wf_rhs`, `wf_equation`, `wf_numbering`,
  `valuation`, the satisfiability relations `rhs_eval_to`, `rhs_valid`,
  `equation_holds`, `numbering_holds` with `rhs_eval_to_compat` and
  `empty_numbering_holds`, and `combine_comparison` with its four soundness
  lemmas.

  The x86-64 right-hand sides `Rhs` and their evaluation `RhsEvalTo` are
  defined in `CCLib/x86/CombineOp.lean` (namespace `CC.X86.CSEdomain`);
  `Valnum` and `combine_comparison` with its soundness lemmas are shared
  with `CCLib/backend/CSEdomain.lean`.
-/
import CCLib.backend.ValueDomain
import CCLib.x86.Op
import CCLib.x86.RTL
import CCLib.common.Builtins
import CCLib.x86.CombineOp

namespace CC
namespace X86


namespace CSEdomain

open ValueDomain Op
export CC.CSEdomain (Valnum combineComparison combineComparison_cmp_sound
  combineComparison_cmpu_sound combineComparison_cmpl_sound combineComparison_cmplu_sound)

deriving instance DecidableEq for Rhs

/-- `CSEdomain.equation`: `v = r` (if `strict`) or `v ≥ r` (otherwise). -/
inductive Equation where
  | Eq (v : Valnum) (strict : Bool) (r : Rhs)
  deriving DecidableEq

/-- `CSEdomain.rhs_compat`: equality up to the regions of `Load`s. -/
inductive RhsCompat : Rhs → Rhs → Prop where
  | op (op vl) : RhsCompat (.Op op vl) (.Op op vl)
  | load (chunk addr vl p1 p2) : RhsCompat (.Load chunk addr vl p1) (.Load chunk addr vl p2)
  | builtin (bf args) : RhsCompat (.Builtin bf args) (.Builtin bf args)

/-- `CSEdomain.compat_rhs` -/
def compatRhs (r1 r2 : Rhs) : Bool :=
  match r1, r2 with
  | .Op op1 vl1, .Op op2 vl2 => decide (op1 = op2) && decide (vl1 = vl2)
  | .Load chunk1 addr1 vl1 _, .Load chunk2 addr2 vl2 _ =>
      decide (chunk1 = chunk2) && decide (addr1 = addr2) && decide (vl1 = vl2)
  | .Builtin bf1 args1, .Builtin bf2 args2 => decide (bf1 = bf2) && decide (args1 = args2)
  | _, _ => false

theorem compatRhs_sound {r1 r2 : Rhs} (h : compatRhs r1 r2 = true) : RhsCompat r1 r2 := by
  cases r1 <;> cases r2 <;> simp [compatRhs] at h
  · obtain ⟨rfl, rfl⟩ := h; exact .op _ _
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact .load _ _ _ _ _
  · obtain ⟨rfl, rfl⟩ := h; exact .builtin _ _

/-- `CSEdomain.numbering` -/
structure Numbering where
  /-- first unused value number -/
  num_next : Valnum
  /-- valid equations -/
  num_eqs : List Equation
  /-- mapping register to valnum -/
  num_reg : PTree Valnum
  /-- reverse mapping valnum to registers containing it -/
  num_val : PMap (List Reg)

instance : Inhabited Numbering := ⟨⟨.xH, [], .Leaf, PMap.init []⟩⟩

/-- `CSEdomain.empty_numbering` -/
def emptyNumbering : Numbering :=
  { num_next := .xH, num_eqs := [], num_reg := PTree.empty, num_val := PMap.init [] }

/-- `CSEdomain.valnums_rhs` -/
def valnumsRhs (r : Rhs) : List Valnum :=
  match r with
  | .Op _ vl => vl
  | .Load _ _ vl _ => vl
  | .Builtin _ args => BuiltinArg.paramsList args

/-- `CSEdomain.wf_rhs` -/
def WfRhs (next : Valnum) (r : Rhs) : Prop := ∀ v, v ∈ valnumsRhs r → v < next

/-- `CSEdomain.wf_equation` -/
def WfEquation (next : Valnum) (e : Equation) : Prop :=
  match e with
  | .Eq l _ r => l < next ∧ WfRhs next r

/-- `CSEdomain.wf_numbering` -/
structure WfNumbering (n : Numbering) : Prop where
  wf_num_eqs : ∀ e, e ∈ n.num_eqs → WfEquation n.num_next e
  wf_num_reg : ∀ r v, n.num_reg.get r = some v → v < n.num_next
  wf_num_val : ∀ r v, r ∈ n.num_val.get v → n.num_reg.get r = some v

/-- `CSEdomain.valuation` -/
abbrev Valuation := Valnum → Val


/-- `CSEdomain.rhs_eval_to_compat` -/
theorem rhsEvalTo_compat {valu : Valuation} {ge : RTL.CGenv} {sp : Val} {m : Mem} {rh rh' : Rhs}
    {v : Val} (h : RhsEvalTo valu ge sp m rh v) (hc : RhsCompat rh rh') :
    RhsEvalTo valu ge sp m rh' v := by
  cases h <;> cases hc
  · exact .op_eval_to _ _ _ ‹_›
  · exact .load_eval_to _ _ _ _ _ _ ‹_› ‹_›
  · exact .builtin_eval_to _ _ _ _ ‹_› ‹_›

/-- `CSEdomain.rhs_valid`: the address read by a `Load` equation belongs to
    its region. -/
inductive RhsValid (valu : Valuation) (ge : RTL.CGenv) : Val → Rhs → Prop where
  | op_valid (sp op vl) : RhsValid valu ge sp (.Op op vl)
  | load_valid (sp chunk addr vl p b ofs) (bc : BlockClassification) :
      evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) addr (vl.map valu) = some (.Vptr b ofs) →
      Pmatch bc b ofs p → GenvMatch bc ge → bc sp = .BCstack →
      RhsValid valu ge (.Vptr sp Integers.Ptrofs.zero) (.Load chunk addr vl p)
  | builtin_valid (sp bf args) : RhsValid valu ge sp (.Builtin bf args)

/-- `CSEdomain.equation_holds` -/
inductive EquationHolds (valu : Valuation) (ge : RTL.CGenv) (sp : Val) (m : Mem) :
    Equation → Prop where
  | eq_holds_strict (l r) : RhsEvalTo valu ge sp m r (valu l) → RhsValid valu ge sp r →
      EquationHolds valu ge sp m (.Eq l true r)
  | eq_holds_lessdef (l r v) : RhsEvalTo valu ge sp m r v → Val.Lessdef v (valu l) →
      RhsValid valu ge sp r → EquationHolds valu ge sp m (.Eq l false r)

/-- `CSEdomain.numbering_holds` -/
structure NumberingHolds (valu : Valuation) (ge : RTL.CGenv) (sp : Val) (rs : RTL.Regset)
    (m : Mem) (n : Numbering) : Prop where
  num_holds_wf : WfNumbering n
  num_holds_eq : ∀ eq, eq ∈ n.num_eqs → EquationHolds valu ge sp m eq
  num_holds_reg : ∀ r v, n.num_reg.get r = some v → rs.get r = valu v

/-- `CSEdomain.empty_numbering_holds` -/
theorem empty_numbering_holds (valu : Valuation) (ge : RTL.CGenv) (sp : Val) (rs : RTL.Regset)
    (m : Mem) : NumberingHolds valu ge sp rs m emptyNumbering := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> intros <;> simp_all [emptyNumbering]

end CSEdomain

end X86
end CC
