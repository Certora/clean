/-
  Correctness of the validator of comparison trees — port of the proof part
  of `common/Switch.v` (`wf_comptree`, `validate_wf`, `split_eq_prop`,
  `split_lt_prop`, `split_between_prop`, `validate_jumptable_correct_rec`,
  `validate_jumptable_correct`, `validate_correct_rec`, `table_tree_agree`,
  `validate_switch_correct`).
-/
import CCLib.common.Switch
import CCLib.lib.MapsLemmas
import CCLib.lib.IntegersLemmas

namespace CC
namespace Switch

section COMPTREE
variable (modulus : Z)

/-- `Switch.wf_comptree` -/
inductive WfComptree : Comptree → Prop where
  | action (act : Nat) : WfComptree (.CTaction act)
  | ifeq (key : Z) (act : Nat) (cne : Comptree) :
      0 ≤ key → key < modulus → WfComptree cne → WfComptree (.CTifeq key act cne)
  | iflt (key : Z) (clt cge : Comptree) :
      0 ≤ key → key < modulus → WfComptree clt → WfComptree cge → WfComptree (.CTiflt key clt cge)
  | jumptable (ofs sz : Z) (acts : List Nat) (cother : Comptree) :
      0 ≤ ofs → ofs < modulus → 0 ≤ sz → sz < modulus → WfComptree cother →
      WfComptree (.CTjumptable ofs sz acts cother)

/-- `Switch.validate_wf` -/
theorem validate_wf (default : Nat) (t : Comptree) :
    ∀ cases lo hi, validate modulus default cases t lo hi = true → WfComptree modulus t := by
  induction t with
  | CTaction act => intros; exact .action act
  | CTifeq key act t' ih =>
    intro cases lo hi h
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    split at h2
    · cases h2
    · simp only [Bool.and_eq_true] at h2
      exact .ifeq _ _ _ h0 h1 (ih _ _ _ h2.2)
  | CTiflt key t1 t2 ih1 ih2 =>
    intro cases lo hi h
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    exact .iflt _ _ _ h0 h1 (ih1 _ _ _ h2.1) (ih2 _ _ _ h2.2)
  | CTjumptable ofs sz tbl t' ih =>
    intro cases lo hi h
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, _⟩, _⟩, _⟩, h4⟩ := h
    exact .jumptable _ _ _ _ h0 h1 h2 h3 (ih _ _ _ h4.2)

/-- `Switch.split_eq_prop` -/
theorem splitEq_prop (v : Z) (default : Nat) (n : Z) :
    ∀ (cases : Table) (optact : Option Nat) (cases' : Table),
    splitEq n cases = (optact, cases') →
    switchTarget v default cases =
      (if v = n then optact.getD default else switchTarget v default cases') := by
  intro cases
  induction cases with
  | nil =>
    intro optact cases' h
    simp only [splitEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [switchTarget]
  | cons kv rem ih =>
    obtain ⟨key, act⟩ := kv
    intro optact cases' h
    rcases hs : splitEq n rem with ⟨same, others⟩
    have ih' := ih same others hs
    simp only [splitEq, hs] at h
    simp only [switchTarget, ih']
    by_cases hk : key = n
    · simp only [hk, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hk
      by_cases hv : v = key <;> simp [hv]
    · simp only [hk, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hv : v = key
      · subst hv; simp [hk, switchTarget]
      · simp [hv, switchTarget]

/-- `Switch.split_lt_prop` -/
theorem splitLt_prop (v : Z) (default : Nat) (n : Z) :
    ∀ (cases lcases rcases : Table),
    splitLt n cases = (lcases, rcases) →
    switchTarget v default cases =
      (if v < n then switchTarget v default lcases else switchTarget v default rcases) := by
  intro cases
  induction cases with
  | nil =>
    intro lcases rcases h
    simp only [splitLt, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [switchTarget]
  | cons kv rem ih =>
    obtain ⟨key, act⟩ := kv
    intro lcases rcases h
    rcases hs : splitLt n rem with ⟨lc, rc⟩
    have ih' := ih lc rc hs
    simp only [splitLt, hs] at h
    simp only [switchTarget, ih']
    by_cases hk : key < n
    · simp only [hk, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hv : v = key
      · subst hv; simp [hk, switchTarget]
      · simp [hv, switchTarget]
    · simp only [hk, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hv : v = key
      · subst hv; simp [hk, switchTarget]
      · simp [hv, switchTarget]

/-- `Switch.split_between_prop` -/
theorem splitBetween_prop (v : Z) (default : Nat) (ofs sz : Z) :
    ∀ (cases : Table) (inside : ZMap Nat) (outside : Table),
    splitBetween modulus default ofs sz cases = (inside, outside) →
    switchTarget v default cases =
      (if (v - ofs) % modulus < sz then ZMap.get v inside
       else switchTarget v default outside) := by
  intro cases
  induction cases with
  | nil =>
    intro inside outside h
    simp only [splitBetween, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [switchTarget]
  | cons kv rem ih =>
    obtain ⟨key, act⟩ := kv
    intro inside outside h
    rcases hs : splitBetween modulus default ofs sz rem with ⟨ins, outs⟩
    have ih' := ih ins outs hs
    simp only [splitBetween, hs] at h
    simp only [switchTarget, ih']
    by_cases hk : (key - ofs) % modulus < sz
    · simp only [hk, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hv : v = key
      · subst hv; simp [hk]
      · rw [ZMap.gso _ _ _ _ (Ne.symm hv)]; simp [hv]
    · simp only [hk, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hv : v = key
      · subst hv; simp [hk, switchTarget]
      · simp [hv, switchTarget]

/-- `Switch.validate_jumptable_correct_rec` -/
theorem validateJumptable_correct_rec (cases : ZMap Nat) :
    ∀ (tbl : List Nat) (base v : Z),
    validateJumptable cases tbl base = true → 0 ≤ v → v < (tbl.length : Z) →
    listNthZ tbl v = some (ZMap.get (base + v) cases) := by
  intro tbl
  induction tbl with
  | nil => intro base v _ h1 h2; simp at h2; zomega
  | cons act rem ih =>
    intro base v h h1 h2
    simp only [validateJumptable, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨ha, hr⟩ := h
    simp only [listNthZ]
    by_cases hv : v = 0
    · subst hv; simp [ha]
    · simp only [hv, if_false]
      have := ih (base + 1) (v - 1) hr (by zomega) (by simp at h2; zomega)
      rw [this]
      congr 2
      zomega

/-- `Switch.validate_jumptable_correct` -/
theorem validateJumptable_correct (hmod : modulus > 0) (cases : ZMap Nat) (tbl : List Nat)
    (ofs v sz : Z) (h : validateJumptable cases tbl ofs = true)
    (h1 : (v - ofs) % modulus < sz) (h3 : 0 ≤ ofs) (h4 : ofs + sz ≤ modulus)
    (h5 : 0 ≤ v) (h6 : v < modulus) (h7 : sz ≤ (tbl.length : Z)) :
    listNthZ tbl ((v - ofs) % modulus) = some (ZMap.get v cases) := by
  have hm0 : 0 ≤ (v - ofs) % modulus := Int.emod_nonneg _ (by zomega)
  rw [validateJumptable_correct_rec cases tbl ofs _ h hm0 (by zomega)]
  congr 2
  -- `(v - ofs) mod modulus = v - ofs`
  by_cases hle : ofs ≤ v
  · rw [Int.emod_eq_of_lt (by zomega) (by zomega)]; zomega
  · exfalso
    have : (v - ofs) % modulus = v - ofs + modulus := by
      rw [← Int.add_mul_emod_self_right (v - ofs) 1 modulus]
      rw [Int.emod_eq_of_lt (by zomega) (by zomega)]; zomega
    zomega

/-- `Switch.validate_correct_rec` -/
theorem validate_correct_rec (hmod : modulus > 0) (default : Nat) (v : Z) (hv0 : 0 ≤ v)
    (hv1 : v < modulus) (t : Comptree) :
    ∀ cases lo hi, validate modulus default cases t lo hi = true → lo ≤ v → v ≤ hi →
    comptreeMatch modulus v t = some (switchTarget v default cases) := by
  induction t with
  | CTaction act =>
    intro cases lo hi h hlo hhi
    cases cases with
    | nil =>
      simp only [validate, beq_iff_eq] at h
      subst h; rfl
    | cons kv rem =>
      obtain ⟨key1, act1⟩ := kv
      simp only [validate, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      subst h3
      have : v = key1 := by zomega
      simp [comptreeMatch, switchTarget, this]
  | CTifeq key act t' ih =>
    intro cases lo hi h hlo hhi
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨_, h2⟩ := h
    rcases hs : splitEq key cases with ⟨optact, others⟩
    rw [hs] at h2
    cases optact with
    | none => cases h2
    | some act1 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨rfl, h3⟩ := h2
      rw [splitEq_prop v default key cases _ _ hs]
      simp only [comptreeMatch]
      by_cases hk : v = key
      · simp [hk]
      · simp only [hk, if_false]
        refine ih _ _ _ h3 ?_ ?_
        · unfold refineLowBound; split <;> zomega
        · unfold refineHighBound; split <;> zomega
  | CTiflt key t1 t2 ih1 ih2 =>
    intro cases lo hi h hlo hhi
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨_, h2⟩ := h
    rcases hs : splitLt key cases with ⟨lc, rc⟩
    rw [hs] at h2
    rw [splitLt_prop v default key cases _ _ hs]
    simp only [comptreeMatch]
    by_cases hk : v < key
    · simp only [hk, if_true]; exact ih1 _ _ _ h2.1 hlo (by zomega)
    · simp only [hk, if_false]; exact ih2 _ _ _ h2.2 (by zomega) hhi
  | CTjumptable ofs sz tbl t' ih =>
    intro cases lo hi h hlo hhi
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, _⟩, _⟩, _⟩, h4⟩, h5⟩, _⟩, h7⟩ := h
    rcases hs : splitBetween modulus default ofs sz cases with ⟨ins, outs⟩
    rw [hs] at h7
    rw [splitBetween_prop modulus v default ofs sz cases _ _ hs]
    simp only [comptreeMatch]
    have hm0 : 0 ≤ (v - ofs) % modulus := Int.emod_nonneg _ (by zomega)
    by_cases hk : (v - ofs) % modulus < sz
    · simp only [hk, if_true]
      rw [Int.emod_eq_of_lt hm0 (by zomega)]
      exact validateJumptable_correct modulus hmod ins tbl ofs v sz h7.1 hk h0 h4 hv0 hv1 h5
    · simp only [hk, if_false]; exact ih _ _ _ h7.2 hlo hhi

/-- `Switch.table_tree_agree` -/
def TableTreeAgree (default : Nat) (cases : Table) (t : Comptree) : Prop :=
  ∀ v, 0 ≤ v → v < modulus → comptreeMatch modulus v t = some (switchTarget v default cases)

/-- `Switch.validate_switch_correct` -/
theorem validateSwitch_correct (hmod : modulus > 0) (default : Nat) (t : Comptree)
    (cases : Table) (h : validateSwitch modulus default cases t = true) :
    WfComptree modulus t ∧ TableTreeAgree modulus default cases t :=
  ⟨validate_wf modulus default t _ _ _ h,
   fun v hv0 hv1 => validate_correct_rec modulus hmod default v hv0 hv1 t _ _ _ h hv0 (by zomega)⟩

end COMPTREE

end Switch
end CC
