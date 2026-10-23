/-
  Neededness analysis for x86-64 operators — port of `x86/NeedOp.v`.

  Ported: `op1`, `op2`, `needs_of_condition`, `needs_of_addressing`,
  `needs_of_operation`, `operation_is_redundant`, and section `SOUNDNESS`:
  `needs_of_condition_sound`, `needs_of_addressing_32_sound`,
  `needs_of_addressing_64_sound`, `needs_of_operation_sound`,
  `operation_is_redundant_sound`.

  Differences from Rocq: the generic lemmas `default_needs_of_condition_sound`
  and `default_needs_of_operation_sound` of `NeedDomain.v` are stated over the
  aarch64 operators in `CCLib/backend/NeedDomainProof2.lean`; their x86
  instances are proved here from `Op.eval_condition_lessdef` /
  `Op.eval_operation_lessdef` (`CCLib/x86/OpInject.lean`).
-/
import CCLib.x86.OpInject
import CCLib.backend.NeedDomainProof2

namespace CC
namespace X86
namespace NeedOp

open NeedDomain Op

/-- `NeedOp.op1` -/
def op1 (nv : Nval) : List Nval := [nv]
/-- `NeedOp.op2` -/
def op2 (nv : Nval) : List Nval := [nv, nv]

/-- `needs_of_condition` (x86) -/
def needsOfCondition (cond : Condition) : List Nval :=
  match cond with
  | .Cmaskzero n | .Cmasknotzero n => op1 (maskzero n)
  | _ => []

/-- `needs_of_addressing` (x86) -/
def needsOfAddressing (addr : Addressing) (nv : Nval) : List Nval :=
  match addr with
  | .Aindexed _ => op1 (modarith nv)
  | .Aindexed2 _ => op2 (modarith nv)
  | .Ascaled _ _ => op1 (modarith (modarith nv))
  | .Aindexed2scaled _ _ => op2 (modarith nv)
  | .Aglobal _ _ => []
  | .Abased _ _ => op1 (modarith nv)
  | .Abasedscaled _ _ _ => op1 (modarith (modarith nv))
  | .Ainstack _ => []

/-- `needs_of_operation` (x86) -/
def needsOfOperation (op : Operation) (nv : Nval) : List Nval :=
  match op with
  | .Omove => op1 nv
  | .Ointconst _ | .Olongconst _ | .Ofloatconst _ | .Osingleconst _
  | .Oindirectsymbol _ => []
  | .Ocast8signed => op1 (signExt 8 nv)
  | .Ocast8unsigned => op1 (zeroExt 8 nv)
  | .Ocast16signed => op1 (signExt 16 nv)
  | .Ocast16unsigned => op1 (zeroExt 16 nv)
  | .Oneg => op1 (modarith nv)
  | .Osub => op2 (default nv)
  | .Omul => op2 (modarith nv)
  | .Omulimm _ => op1 (modarith nv)
  | .Omulhs | .Omulhu | .Odiv | .Odivu | .Omod | .Omodu => op2 (default nv)
  | .Oand => op2 (bitwise nv)
  | .Oandimm n => op1 (andimm nv n)
  | .Oor => op2 (bitwise nv)
  | .Oorimm n => op1 (orimm nv n)
  | .Oxor => op2 (bitwise nv)
  | .Oxorimm _ => op1 (bitwise nv)
  | .Onot => op1 (bitwise nv)
  | .Oshl => op2 (default nv)
  | .Oshlimm n => op1 (shlimm nv n)
  | .Oshr => op2 (default nv)
  | .Oshrimm n => op1 (shrimm nv n)
  | .Oshrximm _ => op1 (default nv)
  | .Oshru => op2 (default nv)
  | .Oshruimm n => op1 (shruimm nv n)
  | .Ororimm n => op1 (ror nv n)
  | .Oshldimm _ => op1 (default nv)
  | .Olea addr => needsOfAddressing addr nv
  | .Omakelong => [makelongHi nv, makelongLo nv]
  | .Olowlong => op1 (loword nv)
  | .Ohighlong => op1 (hiword nv)
  | .Ocast32signed => op1 (longofint nv)
  | .Ocast32unsigned => op1 (longofintu nv)
  | .Onegl => op1 (modarith nv)
  | .Oaddlimm _ => op1 (modarith nv)
  | .Osubl => op2 (default nv)
  | .Omull => op2 (modarith nv)
  | .Omullimm _ => op1 (modarith nv)
  | .Omullhs | .Omullhu | .Odivl | .Odivlu | .Omodl | .Omodlu => op2 (default nv)
  | .Oandl => op2 (bitwise nv)
  | .Oandlimm n => op1 (andlimm nv n)
  | .Oorl => op2 (bitwise nv)
  | .Oorlimm n => op1 (orlimm nv n)
  | .Oxorl => op2 (bitwise nv)
  | .Oxorlimm _ => op1 (bitwise nv)
  | .Onotl => op1 (bitwise nv)
  | .Oshll => op2 (default nv)
  | .Oshllimm n => op1 (shllimm nv n)
  | .Oshrl => op2 (default nv)
  | .Oshrlimm n => op1 (shrlimm nv n)
  | .Oshrxlimm _ => op1 (default nv)
  | .Oshrlu => op2 (default nv)
  | .Oshrluimm n => op1 (shrluimm nv n)
  | .Ororlimm n => op1 (rorl nv n)
  | .Oleal addr => needsOfAddressing addr nv
  | .Onegf | .Oabsf => op1 (default nv)
  | .Oaddf | .Osubf | .Omulf | .Odivf | .Omaxf | .Ominf => op2 (default nv)
  | .Onegfs | .Oabsfs => op1 (default nv)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => op2 (default nv)
  | .Osingleoffloat | .Ofloatofsingle => op1 (default nv)
  | .Ointoffloat | .Ofloatofint | .Ointofsingle | .Osingleofint => op1 (default nv)
  | .Olongoffloat | .Ofloatoflong | .Olongofsingle | .Osingleoflong => op1 (default nv)
  | .Ocmp c => needsOfCondition c
  | .Osel c _ => nv :: nv :: needsOfCondition c

/-- `operation_is_redundant` (x86) -/
def operationIsRedundant (op : Operation) (nv : Nval) : Bool :=
  match op with
  | .Ocast8signed => signExtRedundant 8 nv
  | .Ocast8unsigned => zeroExtRedundant 8 nv
  | .Ocast16signed => signExtRedundant 16 nv
  | .Ocast16unsigned => zeroExtRedundant 16 nv
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

/-- `needs_of_condition_sound` (x86) -/
theorem needs_of_condition_sound {cond : Condition} {args args' : List Val} {b : Bool}
    (h : evalCondition cond args m = some b) (hl : VagreeList args args' (needsOfCondition cond)) :
    evalCondition cond args' m' = some b := by
  have hvp : ∀ b ofs, Mem.validPointer m b ofs = true → Mem.validPointer m' b ofs = true :=
    fun b ofs hv => PERM b ofs _ _ hv
  cases cond
  case Cmaskzero n =>
    rcases args with _ | ⟨a1, _ | ⟨a2, l⟩⟩ <;> try (cases h; done)
    simp only [needsOfCondition, op1] at hl
    obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
    exact maskzero_sound h1 h
  case Cmasknotzero n =>
    rcases args with _ | ⟨a1, _ | ⟨a2, l⟩⟩ <;> try (cases h; done)
    simp only [needsOfCondition, op1] at hl
    obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
    simp only [evalCondition] at h ⊢
    cases e : Val.maskzero_bool a1 n with
    | none => rw [e] at h; cases h
    | some b' => rw [e] at h; rw [maskzero_sound h1 e]; exact h
  all_goals exact evalCondition_lessdef_vp (lessdef_vagree_list hl) hvp h

omit PERM in
/-- `needs_of_addressing_32_sound` -/
theorem needs_of_addressing_32_sound {addr : Addressing} {args args' : List Val} {v : Val}
    {nv : Nval} (h : evalAddressing32 ge (.Vptr sp Integers.Ptrofs.zero) addr args = some v)
    (hl : VagreeList args args' (needsOfAddressing addr nv)) :
    ∃ v', evalAddressing32 ge (.Vptr sp Integers.Ptrofs.zero) addr args' = some v' ∧
      vagree v v' nv := by
  cases addr <;> simp only [needsOfAddressing, op1, op2] at hl <;>
    rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩ <;>
    simp only [evalAddressing32, Archi.ptr64, if_true, reduceCtorEq, Option.some.injEq] at h <;>
    subst h
  · obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
    exact ⟨_, rfl, add_sound h1 (vagree_same _ _)⟩
  · obtain ⟨b1, b2, rfl, h1, h2⟩ := vagreeList_2 hl
    exact ⟨_, rfl, add_sound (add_sound (by rw [modarith_idem]; exact h1)
      (by rw [modarith_idem]; exact h2)) (vagree_same _ _)⟩
  · obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
    exact ⟨_, rfl, add_sound (mul_sound h1 (vagree_same _ _)) (vagree_same _ _)⟩
  · obtain ⟨b1, b2, rfl, h1, h2⟩ := vagreeList_2 hl
    exact ⟨_, rfl, add_sound h1 (add_sound (mul_sound (by rw [modarith_idem, modarith_idem]; exact h2)
      (vagree_same _ _)) (vagree_same _ _))⟩

omit PERM in
/-- `needs_of_addressing_64_sound` -/
theorem needs_of_addressing_64_sound {addr : Addressing} {args args' : List Val} {v : Val}
    {nv : Nval} (h : evalAddressing64 ge (.Vptr sp Integers.Ptrofs.zero) addr args = some v)
    (hl : VagreeList args args' (needsOfAddressing addr nv)) :
    ∃ v', evalAddressing64 ge (.Vptr sp Integers.Ptrofs.zero) addr args' = some v' ∧
      vagree v v' nv := by
  cases addr <;> simp only [needsOfAddressing, op1, op2] at hl <;>
    rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩ <;>
    simp only [evalAddressing64, Archi.ptr64, if_true, reduceCtorEq, Option.some.injEq] at h <;>
    subst h
  · obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
    exact ⟨_, rfl, addl_sound h1 (vagree_same _ _)⟩
  · obtain ⟨b1, b2, rfl, h1, h2⟩ := vagreeList_2 hl
    exact ⟨_, rfl, addl_sound (addl_sound (by rw [modarith_idem]; exact h1)
      (by rw [modarith_idem]; exact h2)) (vagree_same _ _)⟩
  · obtain ⟨b1, rfl, h1⟩ := vagreeList_1 hl
    exact ⟨_, rfl, addl_sound (mull_sound h1 (vagree_same _ _)) (vagree_same _ _)⟩
  · obtain ⟨b1, b2, rfl, h1, h2⟩ := vagreeList_2 hl
    exact ⟨_, rfl, addl_sound h1 (addl_sound (mull_sound
      (by rw [modarith_idem, modarith_idem]; exact h2) (vagree_same _ _)) (vagree_same _ _))⟩
  · cases hl; exact ⟨_, rfl, vagree_same _ _⟩
  · cases hl; exact ⟨_, rfl, vagree_same _ _⟩

/-- The default abstraction, for x86 operators. -/
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

/-- `needs_of_operation_sound` (x86) -/
theorem needs_of_operation_sound {op : Operation} {args args' : List Val} {v : Val} {nv : Nval}
    (h : evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args m = some v)
    (hl : VagreeList args args' (needsOfOperation op nv)) (hnv : nv ≠ .Nothing) :
    ∃ v', evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op args' m' = some v' ∧
      vagree v v' nv := by
  cases op
  case Olea addr =>
    have e : ∀ l, evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (.Olea addr) l m =
        evalAddressing32 ge (.Vptr sp Integers.Ptrofs.zero) addr l := by
      intro l; rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    have e' : ∀ l, evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (.Olea addr) l m' =
        evalAddressing32 ge (.Vptr sp Integers.Ptrofs.zero) addr l := by
      intro l; rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; rw [e']
    exact needs_of_addressing_32_sound ge sp h hl
  case Oleal addr =>
    have e : ∀ l, evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (.Oleal addr) l m =
        evalAddressing64 ge (.Vptr sp Integers.Ptrofs.zero) addr l := by
      intro l; rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    have e' : ∀ l, evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (.Oleal addr) l m' =
        evalAddressing64 ge (.Vptr sp Integers.Ptrofs.zero) addr l := by
      intro l; rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; rw [e']
    exact needs_of_addressing_64_sound ge sp h hl
  case Ocmp c =>
    have e : ∀ l mm, evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (.Ocmp c) l mm =
        some (Val.ofOptbool (evalCondition c l mm)) := by
      intro l mm; rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h ⊢; cases h
    refine ⟨_, rfl, ?_⟩
    cases ec : evalCondition c args m with
    | none => exact vagree_lessdef _ (.undef _)
    | some b =>
      rw [needs_of_condition_sound PERM ec hl]
      exact vagree_same _ _
  case Osel c ty =>
    rcases args with _ | ⟨v1, _ | ⟨v2, vl⟩⟩ <;> cases h
    simp only [needsOfOperation] at hl
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
       simp only [needsOfOperation, op1, op2, true_or, or_true]
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
  case Ocast8unsigned => exact zero_ext_sound (8 : Z) h1
  case Ocast16signed => exact sign_ext_sound (n := 16) (by decide) h1
  case Ocast16unsigned => exact zero_ext_sound (16 : Z) h1
  case Oneg => exact neg_sound h1
  case Omul => exact mul_sound h1 h2
  case Omulimm => exact mul_sound h1 (vagree_same _ _)
  case Oand => exact and_sound h1 h2
  case Oandimm => exact andimm_sound h1
  case Oor => exact or_sound h1 h2
  case Oorimm => exact orimm_sound h1
  case Oxor => exact xor_sound h1 h2
  case Oxorimm => exact xor_sound h1 (vagree_same _ _)
  case Onot => exact notint_sound h1
  case Oshlimm => exact shlimm_sound h1
  case Oshrimm => exact shrimm_sound h1
  case Oshruimm => exact shruimm_sound h1
  case Ororimm => exact ror_sound h1
  case Omakelong => exact makelong_sound h1 h2
  case Olowlong => exact loword_sound h1
  case Ohighlong => exact hiword_sound h1
  case Ocast32signed => exact longofint_sound h1
  case Ocast32unsigned => exact longofintu_sound h1
  case Onegl => exact negl_sound h1
  case Oaddlimm => exact addl_sound h1 (vagree_same _ _)
  case Omull => exact mull_sound h1 h2
  case Omullimm => exact mull_sound h1 (vagree_same _ _)
  case Oandl => exact andl_sound h1 h2
  case Oandlimm => exact andlimm_sound h1
  case Oorl => exact orl_sound h1 h2
  case Oorlimm => exact orlimm_sound h1
  case Oxorl => exact xorl_sound h1 h2
  case Oxorlimm => exact xorl_sound h1 (vagree_same _ _)
  case Onotl => exact notl_sound h1
  case Oshllimm => exact shllimm_sound h1
  case Oshrlimm => exact shrlimm_sound h1
  case Oshrluimm => exact shrluimm_sound h1
  case Ororlimm => exact rorl_sound h1

omit PERM in
/-- `operation_is_redundant_sound` (x86) -/
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
  case Ocast8unsigned => exact zero_ext_redundant_sound (n := 8) hr h1
  case Ocast16signed => exact sign_ext_redundant_sound (n := 16) (by decide) hr h1
  case Ocast16unsigned => exact zero_ext_redundant_sound (n := 16) hr h1

end SOUNDNESS

end NeedOp
end X86
end CC
