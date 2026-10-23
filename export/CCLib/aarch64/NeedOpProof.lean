/-
  Neededness analysis for AArch64 operators — port of `aarch64/NeedOp.v`
  (soundness part): `shift_sound`, `shiftl_sound`, `extend_sound`,
  `zero_ext'_sound`, `sign_ext'_sound`, `needs_of_condition_sound`,
  `needs_of_operation_sound`, `operation_is_redundant_sound`.
-/
import CCLib.aarch64.NeedOp
import CCLib.backend.NeedDomainProof2

namespace CC
namespace NeedOp

open NeedDomain Op

theorem shift_sound {v w : Val} {s : Shift} {a : Amount32} {x : Nval}
    (h : vagree v w (needsOfShift s a x)) :
    vagree (evalShift s v a) (evalShift s w a) x := by
  cases s
  · exact shlimm_sound h
  · exact shruimm_sound h
  · exact shrimm_sound h
  · exact ror_sound h

theorem shiftl_sound {v w : Val} {s : Shift} {a : Amount64} {x : Nval}
    (h : vagree v w (needsOfShiftl s a x)) :
    vagree (evalShiftl s v a) (evalShiftl s w a) x := by
  cases s
  · exact shllimm_sound h
  · exact shrluimm_sound h
  · exact shrlimm_sound h
  · exact rorl_sound h

theorem extend_sound {v w : Val} {ext : Extension} {a : Amount64} {x : Nval}
    (h : vagree v w (needsOfExtend ext a x)) :
    vagree (evalExtend ext v a) (evalExtend ext w a) x := by
  cases ext
  · exact shllimm_sound (longofint_sound h)
  · exact shllimm_sound (longofintu_sound h)

private theorem default_cases {v w : Val} {x : Nval} (h : vagree v w (default x)) :
    x = .Nothing ∨ Val.Lessdef v w := by
  cases x
  · exact Or.inl rfl
  all_goals exact Or.inr (lessdef_vagree h)

/-- `zero_ext'_sound` -/
theorem zero_ext'_sound {v w : Val} {x : Nval} {n : Z} (h : vagree v w (zeroExt' n x)) :
    vagree (Val.zeroExt n.toNat v) (Val.zeroExt n.toNat w) x := by
  unfold zeroExt' at h
  split at h
  · exact zero_ext_sound n h
  · rcases default_cases h with rfl | hl
    · trivial
    · exact vagree_lessdef _ (Val.zero_ext_lessdef _ hl)

/-- `sign_ext'_sound` -/
theorem sign_ext'_sound {v w : Val} {x : Nval} {n : Z} (h : vagree v w (signExt' n x)) :
    vagree (Val.signExt n.toNat v) (Val.signExt n.toNat w) x := by
  unfold signExt' at h
  split at h
  · exact sign_ext_sound ‹_› h
  · rcases default_cases h with rfl | hl
    · trivial
    · exact vagree_lessdef _ (Val.sign_ext_lessdef _ hl)

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

private theorem vagreeList_3 {a1 a2 a3 : Val} {w : List Val} {n1 n2 n3 : Nval}
    (h : VagreeList [a1, a2, a3] w [n1, n2, n3]) :
    ∃ b1 b2 b3, w = [b1, b2, b3] ∧ vagree a1 b1 n1 ∧ vagree a2 b2 n2 ∧ vagree a3 b3 n3 := by
  cases h with
  | cons h1 h2 => cases h2 with
    | cons h3 h4 => cases h4 with
      | cons h5 h6 => cases h6; exact ⟨_, _, _, rfl, h1, h3, h5⟩

section SOUNDNESS

variable {F V : Type} (ge : Genv F V) (sp : Block) {m m' : Mem}
  (PERM : ∀ b ofs k p, Mem.perm m b ofs k p = true → Mem.perm m' b ofs k p = true)
include PERM

/-- `needs_of_condition_sound` -/
theorem needs_of_condition_sound {cond : Condition} {args args' : List Val} {b : Bool}
    (h : evalCondition cond args m = some b) (hl : VagreeList args args' (needsOfCondition cond)) :
    evalCondition cond args' m' = some b :=
  default_needs_of_condition_sound PERM h hl

private theorem default_sound' {op : Operation} {args args' : List Val} {v : Val} {nv : Nval}
    {l : List Nval}
    (h : evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args m = some v)
    (hl : VagreeList args args' l)
    (hlen : l = [] ∨ l = [default nv] ∨ l = [default nv, default nv] ∨
      l = [default nv, default nv, default nv]) (hnv : nv ≠ .Nothing) :
    ∃ v', evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args' m' = some v' ∧
      vagree v v' nv := by
  rcases hlen with rfl | rfl | rfl | rfl
  · exact default_needs_of_operation_sound ge sp PERM h (Or.inl hl) hnv
  · exact default_needs_of_operation_sound ge sp PERM h (Or.inr (Or.inl hl)) hnv
  · exact default_needs_of_operation_sound ge sp PERM h (Or.inr (Or.inr (Or.inl hl))) hnv
  · exact default_needs_of_operation_sound ge sp PERM h (Or.inr (Or.inr (Or.inr hl))) hnv

/-- `needs_of_operation_sound` -/
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
    rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, l⟩⟩⟩⟩ <;> cases h <;>
      simp only [needsOfOperation, op1, op2, op1shift, op1shiftl, op2shift, op2shiftl,
        op2extl] at hl <;>
      first
        | obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
        | obtain ⟨b1, b2, rfl, h1, h2⟩ := vagreeList_2 hl
        | obtain ⟨b1, b2, b3, rfl, h1, h2, h3⟩ := vagreeList_3 hl
  all_goals refine ⟨_, rfl, ?_⟩
  case Omove => exact h1
  case Oshift => exact shift_sound h1
  case Oadd => exact add_sound h1 h2
  case Oaddshift => exact add_sound h1 (shift_sound h2)
  case Oaddimm => exact add_sound h1 (vagree_same _ _)
  case Oneg => exact neg_sound h1
  case Onegshift => exact neg_sound (shift_sound h1)
  case Osub => exact sub_sound h1 h2
  case Osubshift => exact sub_sound h1 (shift_sound h2)
  case Omul => exact mul_sound h1 h2
  case Omuladd => exact add_sound h1 (mul_sound (by rw [modarith_idem]; exact h2) (by rw [modarith_idem]; exact h3))
  case Omulsub => exact sub_sound h1 (mul_sound (by rw [modarith_idem]; exact h2) (by rw [modarith_idem]; exact h3))
  case Oand => exact and_sound h1 h2
  case Oandshift => exact and_sound h1 (shift_sound h2)
  case Oandimm => exact andimm_sound h1
  case Oor => exact or_sound h1 h2
  case Oorshift => exact or_sound h1 (shift_sound h2)
  case Oorimm => exact orimm_sound h1
  case Oxor => exact xor_sound h1 h2
  case Oxorshift => exact xor_sound h1 (shift_sound h2)
  case Oxorimm => exact xor_sound h1 (vagree_same _ _)
  case Onot => exact notint_sound h1
  case Onotshift => exact notint_sound (shift_sound h1)
  case Obic => exact and_sound h1 (notint_sound h2)
  case Obicshift => exact and_sound h1 (notint_sound (shift_sound h2))
  case Oorn => exact or_sound h1 (notint_sound h2)
  case Oornshift => exact or_sound h1 (notint_sound (shift_sound h2))
  case Oeqv => exact xor_sound h1 (notint_sound h2)
  case Oeqvshift => exact xor_sound h1 (notint_sound (shift_sound h2))
  case Ozext => exact zero_ext'_sound h1
  case Osext => exact sign_ext'_sound h1
  case Oshlzext => exact shlimm_sound (zero_ext'_sound h1)
  case Oshlsext => exact shlimm_sound (sign_ext'_sound h1)
  case Ozextshr => exact zero_ext'_sound (shruimm_sound h1)
  case Osextshr => exact sign_ext'_sound (shrimm_sound h1)
  case Oshiftl => exact shiftl_sound h1
  case Oextend => exact extend_sound h1
  case Omakelong => exact makelong_sound h1 h2
  case Olowlong => exact loword_sound h1
  case Ohighlong => exact hiword_sound h1
  case Oaddl => exact addl_sound h1 h2
  case Oaddlshift => exact addl_sound h1 (shiftl_sound h2)
  case Oaddlext => exact addl_sound h1 (extend_sound h2)
  case Oaddlimm => exact addl_sound h1 (vagree_same _ _)
  case Onegl => exact negl_sound h1
  case Oneglshift => exact negl_sound (shiftl_sound h1)
  case Omull => exact mull_sound h1 h2
  case Omulladd => exact addl_sound h1 (mull_sound (by rw [modarith_idem]; exact h2) (by rw [modarith_idem]; exact h3))
  case Oandl => exact andl_sound h1 h2
  case Oorl => exact orl_sound h1 h2
  case Oxorl => exact xorl_sound h1 h2
  case Obicl => exact andl_sound h1 (notl_sound h2)
  case Oornl => exact orl_sound h1 (notl_sound h2)
  case Oeqvl => exact xorl_sound h1 (notl_sound h2)
  case Oandlshift => exact andl_sound h1 (shiftl_sound h2)
  case Oorlshift => exact orl_sound h1 (shiftl_sound h2)
  case Oxorlshift => exact xorl_sound h1 (shiftl_sound h2)
  case Obiclshift => exact andl_sound h1 (notl_sound (shiftl_sound h2))
  case Oornlshift => exact orl_sound h1 (notl_sound (shiftl_sound h2))
  case Oeqvlshift => exact xorl_sound h1 (notl_sound (shiftl_sound h2))
  case Oandlimm => exact andlimm_sound h1
  case Oorlimm => exact orlimm_sound h1
  case Oxorlimm => exact xorl_sound h1 (vagree_same _ _)
  case Onotl => exact notl_sound h1
  case Onotlshift => exact notl_sound (shiftl_sound h1)

omit PERM in
/-- `operation_is_redundant_sound` -/
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
  case Ozext =>
    simp only [operationIsRedundant, Bool.and_eq_true, decide_eq_true_eq] at hr
    unfold zeroExt' at h1; rw [if_pos hr.1] at h1
    exact zero_ext_redundant_sound hr.2 h1
  case Osext =>
    simp only [operationIsRedundant, Bool.and_eq_true, decide_eq_true_eq] at hr
    unfold signExt' at h1; rw [if_pos hr.1] at h1
    exact sign_ext_redundant_sound hr.1 hr.2 h1

end SOUNDNESS

end NeedOp
end CC
