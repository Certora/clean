/-
  Neededness analysis for RISC-V operators — port of `riscV/NeedOp.v`.

  Ported: `op1`, `op2`, `needs_of_condition`, `needs_of_operation`,
  `operation_is_redundant`, and section `SOUNDNESS`:
  `needs_of_condition_sound`, `needs_of_operation_sound`,
  `operation_is_redundant_sound`.

  Differences from Rocq: the generic lemmas `default_needs_of_condition_sound`
  and `default_needs_of_operation_sound` of `NeedDomain.v` are stated over the
  aarch64 operators in `CCLib/backend/NeedDomainProof2.lean`; their RISC-V
  instances are proved here from `Op.eval_condition_lessdef` /
  `Op.eval_operation_lessdef` (`CCLib/riscV/OpInject.lean`).
-/
import CCLib.riscV.OpInject
import CCLib.backend.NeedDomainProof2

namespace CC
namespace RiscV
namespace NeedOp

open NeedDomain Op

/-- `NeedOp.op1` -/
def op1 (nv : Nval) : List Nval := [nv]
/-- `NeedOp.op2` -/
def op2 (nv : Nval) : List Nval := [nv, nv]

/-- `needs_of_condition` (RISC-V) -/
def needsOfCondition (_cond : Condition) : List Nval := []

/-- `needs_of_operation` (RISC-V) -/
def needsOfOperation (op : Operation) (nv : Nval) : List Nval :=
  match op with
  | .Omove => op1 nv
  | .Ointconst _ | .Olongconst _ | .Ofloatconst _ | .Osingleconst _
  | .Oaddrsymbol _ _ | .Oaddrstack _ => []
  | .Ocast8signed => op1 (signExt 8 nv)
  | .Ocast16signed => op1 (signExt 16 nv)
  | .Oadd => op2 (modarith nv)
  | .Oaddimm _ => op1 (modarith nv)
  | .Oneg => op1 (modarith nv)
  | .Osub => op2 (default nv)
  | .Omul => op2 (modarith nv)
  | .Omulhs | .Omulhu | .Odiv | .Odivu | .Omod | .Omodu => op2 (default nv)
  | .Oand => op2 (bitwise nv)
  | .Oandimm n => op1 (andimm nv n)
  | .Oor => op2 (bitwise nv)
  | .Oorimm n => op1 (orimm nv n)
  | .Oxor => op2 (bitwise nv)
  | .Oxorimm _ => op1 (bitwise nv)
  | .Oshl | .Oshr | .Oshru => op2 (default nv)
  | .Oshlimm n => op1 (shlimm nv n)
  | .Oshrimm n => op1 (shrimm nv n)
  | .Oshruimm n => op1 (shruimm nv n)
  | .Oshrximm _ => op1 (default nv)
  | .Omakelong => [makelongHi nv, makelongLo nv]
  | .Olowlong => op1 (loword nv)
  | .Ohighlong => op1 (hiword nv)
  | .Ocast32signed => op1 (longofint nv)
  | .Ocast32unsigned => op1 (longofintu nv)
  | .Oaddl => op2 (modarith nv)
  | .Oaddlimm _ => op1 (modarith nv)
  | .Onegl => op1 (modarith nv)
  | .Osubl => op2 (default nv)
  | .Omull => op2 (modarith nv)
  | .Omullhs | .Omullhu | .Odivl | .Odivlu | .Omodl | .Omodlu => op2 (default nv)
  | .Oandl => op2 (bitwise nv)
  | .Oandlimm n => op1 (andlimm nv n)
  | .Oorl => op2 (bitwise nv)
  | .Oorlimm n => op1 (orlimm nv n)
  | .Oxorl => op2 (bitwise nv)
  | .Oxorlimm _ => op1 (bitwise nv)
  | .Oshll | .Oshrl | .Oshrlu => op2 (default nv)
  | .Oshllimm n => op1 (shllimm nv n)
  | .Oshrlimm n => op1 (shrlimm nv n)
  | .Oshrluimm n => op1 (shrluimm nv n)
  | .Oshrxlimm _ => op1 (default nv)
  | .Onegf | .Oabsf => op1 (default nv)
  | .Oaddf | .Osubf | .Omulf | .Odivf => op2 (default nv)
  | .Onegfs | .Oabsfs => op1 (default nv)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => op2 (default nv)
  | .Ofloatofsingle | .Osingleoffloat => op1 (default nv)
  | .Ointoffloat | .Ointuoffloat | .Ofloatofint | .Ofloatofintu => op1 (default nv)
  | .Olongoffloat | .Olonguoffloat | .Ofloatoflong | .Ofloatoflongu => op1 (default nv)
  | .Ointofsingle | .Ointuofsingle | .Osingleofint | .Osingleofintu => op1 (default nv)
  | .Olongofsingle | .Olonguofsingle | .Osingleoflong | .Osingleoflongu => op1 (default nv)
  | .Ocmp c => needsOfCondition c
  | .Osel c _ => nv :: nv :: needsOfCondition c

/-- `operation_is_redundant` (RISC-V) -/
def operationIsRedundant (op : Operation) (nv : Nval) : Bool :=
  match op with
  | .Ocast8signed => signExtRedundant 8 nv
  | .Ocast16signed => signExtRedundant 16 nv
  | .Oandimm n => andimmRedundant nv n
  | .Oorimm n => orimmRedundant nv n
  | .Oandlimm n => andlimmRedundant nv n
  | .Oorlimm n => orlimmRedundant nv n
  | _ => false

/-! ## Soundness -/

private theorem vagreeList_1 {a : Val} {w : List Val} {n1 : Nval}
    (h : VagreeList [a] w [n1]) : ∃ b, w = [b] ∧ vagree a b n1 := by
  cases h with
  | cons h1 h2 => cases h2; exact ⟨_, rfl, h1⟩

private theorem vagreeList_2 {a1 a2 : Val} {w : List Val} {n1 n2 : Nval}
    (h : VagreeList [a1, a2] w [n1, n2]) :
    ∃ b1 b2, w = [b1, b2] ∧ vagree a1 b1 n1 ∧ vagree a2 b2 n2 := by
  cases h with
  | cons h1 h2 => cases h2 with
    | cons h3 h4 => cases h4; exact ⟨_, _, rfl, h1, h3⟩

section SOUNDNESS

variable {F V : Type} (ge : Genv F V) (sp : Block) {m m' : Mem}
  (PERM : ∀ b ofs k p, Mem.perm m b ofs k p = true → Mem.perm m' b ofs k p = true)
include PERM

/-- `needs_of_condition_sound` (RISC-V) -/
theorem needs_of_condition_sound {cond : Condition} {args args' : List Val} {b : Bool}
    (h : evalCondition cond args m = some b) (hl : VagreeList args args' (needsOfCondition cond)) :
    evalCondition cond args' m' = some b :=
  evalCondition_lessdef_vp (lessdef_vagree_list hl) (fun b ofs hv => PERM b ofs _ _ hv) h

/-- The default abstraction, for RISC-V operators. -/
private theorem default_sound' {op : Operation} {args args' : List Val} {v : Val} {nv : Nval}
    {l : List Nval}
    (h : evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args m = some v)
    (hl : VagreeList args args' l)
    (hlen : l = [] ∨ l = [default nv] ∨ l = [default nv, default nv]) (hnv : nv ≠ .Nothing) :
    ∃ v', evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args' m' = some v' ∧
      vagree v v' nv := by
  have LD : Val.LessdefList args args' := by
    rcases hlen with rfl | rfl | rfl
    · exact vagreeList_default_lessdef hnv (Or.inl hl)
    · exact vagreeList_default_lessdef hnv (Or.inr (Or.inl hl))
    · exact vagreeList_default_lessdef hnv (Or.inr (Or.inr (Or.inl hl)))
  obtain ⟨v2, h2, hl2⟩ := evalOperation_lessdef_vp ge _ op LD
    (fun b ofs hv => PERM b ofs _ _ hv) h
  exact ⟨v2, h2, vagree_lessdef _ hl2⟩

/-- `needs_of_operation_sound` (RISC-V) -/
theorem needs_of_operation_sound {op : Operation} {args args' : List Val} {v : Val} {nv : Nval}
    (h : evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args m = some v)
    (hl : VagreeList args args' (needsOfOperation op nv)) (hnv : nv ≠ .Nothing) :
    ∃ v', evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args' m' = some v' ∧
      vagree v v' nv := by
  cases op
  case Osel c ty =>
    rcases args with _ | ⟨v1, _ | ⟨v2, vl⟩⟩ <;> cases h
    simp only [needsOfOperation, needsOfCondition] at hl
    cases hl with
    | cons h1 h2 => cases h2 with
      | cons h3 h4 =>
        refine ⟨_, rfl, ?_⟩
        cases hc : evalCondition c vl m with
        | some b =>
            rw [needs_of_condition_sound PERM hc h4]
            exact select_sound ty h1 h3
        | none => exact vagree_lessdef _ (.undef _)
  all_goals first
    | (refine default_sound' ge sp PERM h hl ?_ hnv
       simp only [needsOfOperation, op1, op2, needsOfCondition, true_or, or_true]
       done)
    | skip
  all_goals
    rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩ <;> cases h <;>
      simp only [needsOfOperation, op1, op2] at hl <;>
      first
        | obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
        | obtain ⟨b1, b2, rfl, h1, h2⟩ := vagreeList_2 hl
  all_goals refine ⟨_, rfl, ?_⟩
  case Omove => exact h1
  case Ocast8signed => exact sign_ext_sound (n := 8) (by decide) h1
  case Ocast16signed => exact sign_ext_sound (n := 16) (by decide) h1
  case Oadd => exact add_sound h1 h2
  case Oaddimm => exact add_sound h1 (vagree_same _ _)
  case Oneg => exact neg_sound h1
  case Omul => exact mul_sound h1 h2
  case Oand => exact and_sound h1 h2
  case Oandimm => exact andimm_sound h1
  case Oor => exact or_sound h1 h2
  case Oorimm => exact orimm_sound h1
  case Oxor => exact xor_sound h1 h2
  case Oxorimm => exact xor_sound h1 (vagree_same _ _)
  case Oshlimm => exact shlimm_sound h1
  case Oshrimm => exact shrimm_sound h1
  case Oshruimm => exact shruimm_sound h1
  case Omakelong => exact makelong_sound h1 h2
  case Olowlong => exact loword_sound h1
  case Ohighlong => exact hiword_sound h1
  case Ocast32signed => exact longofint_sound h1
  case Ocast32unsigned => exact longofintu_sound h1
  case Oaddl => exact addl_sound h1 h2
  case Oaddlimm => exact addl_sound h1 (vagree_same _ _)
  case Onegl => exact negl_sound h1
  case Omull => exact mull_sound h1 h2
  case Oandl => exact andl_sound h1 h2
  case Oandlimm => exact andlimm_sound h1
  case Oorl => exact orl_sound h1 h2
  case Oorlimm => exact orlimm_sound h1
  case Oxorl => exact xorl_sound h1 h2
  case Oxorlimm => exact xorl_sound h1 (vagree_same _ _)
  case Oshllimm => exact shllimm_sound h1
  case Oshrlimm => exact shrlimm_sound h1
  case Oshrluimm => exact shrluimm_sound h1

omit PERM in
/-- `operation_is_redundant_sound` (RISC-V) -/
theorem operation_is_redundant_sound {op : Operation} {nv : Nval} {arg1 arg1' : Val}
    {args args' : List Val} {v : Val}
    (hr : operationIsRedundant op nv = true)
    (h : evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op (arg1 :: args) m = some v)
    (hl : VagreeList (arg1 :: args) (arg1' :: args') (needsOfOperation op nv)) :
    vagree v arg1' nv := by
  cases op <;> try (simp only [operationIsRedundant, reduceCtorEq] at hr; done)
  all_goals
    simp only [needsOfOperation, op1] at hl
    rcases hl with _ | _ | ⟨h1, _⟩
    rcases args with _ | ⟨_, _⟩ <;> cases h
  case Oandimm => exact andimm_redundant_sound hr h1
  case Oorimm => exact orimm_redundant_sound hr h1
  case Oandlimm => exact andlimm_redundant_sound hr h1
  case Oorlimm => exact orlimm_redundant_sound hr h1
  case Ocast8signed => exact sign_ext_redundant_sound (n := 8) (by decide) hr h1
  case Ocast16signed => exact sign_ext_redundant_sound (n := 16) (by decide) hr h1

end SOUNDNESS

end NeedOp
end RiscV
end CC
