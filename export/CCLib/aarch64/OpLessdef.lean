/-
  Evaluation of operators is monotone with respect to `Val.lessdef` and
  memory extensions — port of the `EVAL_LESSDEF` section of `aarch64/Op.v`
  (`eval_condition_lessdef`, `eval_operation_lessdef`,
  `eval_addressing_lessdef`).

  Differences from Rocq: proved directly (by case analysis on the operator
  and on the `lessdef` hypotheses) instead of being derived from the
  injection lemmas of `EVAL_COMPAT`.
-/
import CCLib.aarch64.Op
import CCLib.common.MemoryExtends
import CCLib.common.ValuesInject
import CCLib.common.EventsBuiltinArgs

namespace CC
namespace Op

open Val

section UndefLemmas

@[simp] theorem cmp_bool_undef_l (c : Comparison) (v : Val) : cmp_bool c .Vundef v = none := rfl
@[simp] theorem cmp_bool_undef_r (c : Comparison) (v : Val) : cmp_bool c v .Vundef = none := by
  cases v <;> rfl
@[simp] theorem cmpl_bool_undef_l (c : Comparison) (v : Val) : cmpl_bool c .Vundef v = none := rfl
@[simp] theorem cmpl_bool_undef_r (c : Comparison) (v : Val) : cmpl_bool c v .Vundef = none := by
  cases v <;> rfl
@[simp] theorem cmpf_bool_undef_l (c : Comparison) (v : Val) : cmpf_bool c .Vundef v = none := rfl
@[simp] theorem cmpf_bool_undef_r (c : Comparison) (v : Val) : cmpf_bool c v .Vundef = none := by
  cases v <;> rfl
@[simp] theorem cmpfs_bool_undef_l (c : Comparison) (v : Val) : cmpfs_bool c .Vundef v = none := rfl
@[simp] theorem cmpfs_bool_undef_r (c : Comparison) (v : Val) : cmpfs_bool c v .Vundef = none := by
  cases v <;> rfl
@[simp] theorem evalShift_undef (s : Shift) (a : Amount32) : evalShift s .Vundef a = .Vundef := by
  cases s <;> rfl
@[simp] theorem evalShiftl_undef (s : Shift) (a : Amount64) : evalShiftl s .Vundef a = .Vundef := by
  cases s <;> rfl
@[simp] theorem evalExtend_undef (x : Extension) (a : Amount64) :
    evalExtend x .Vundef a = .Vundef := by
  cases x <;> rfl
@[simp] theorem and_undef_l (v : Val) : Val.and .Vundef v = .Vundef := rfl
@[simp] theorem andl_undef_l (v : Val) : Val.andl .Vundef v = .Vundef := rfl

end UndefLemmas

theorem evalShift_lessdef (s : Shift) (a : Amount32) {v v' : Val} (h : Lessdef v v') :
    Lessdef (evalShift s v a) (evalShift s v' a) := by
  cases h
  · exact .refl _
  · rw [evalShift_undef]; exact .undef _

theorem evalShiftl_lessdef (s : Shift) (a : Amount64) {v v' : Val} (h : Lessdef v v') :
    Lessdef (evalShiftl s v a) (evalShiftl s v' a) := by
  cases h
  · exact .refl _
  · rw [evalShiftl_undef]; exact .undef _

theorem evalExtend_lessdef (x : Extension) (a : Amount64) {v v' : Val} (h : Lessdef v v') :
    Lessdef (evalExtend x v a) (evalExtend x v' a) := by
  cases h
  · exact .refl _
  · rw [evalExtend_undef]; exact .undef _

/-- `Op.eval_condition_lessdef`, for any pair of memories where valid pointers
    stay valid (used with `Mem.Extends` and with the memory agreement of
    `Deadcodeproof`). -/
theorem evalCondition_lessdef_vp {cond : Condition} {vl1 vl2 : List Val} {b : Bool} {m1 m2 : Mem}
    (hl : Val.LessdefList vl1 vl2)
    (hvp : ∀ b ofs, Mem.validPointer m1 b ofs = true → Mem.validPointer m2 b ofs = true)
    (h : evalCondition cond vl1 m1 = some b) : evalCondition cond vl2 m2 = some b := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals cases cond
  all_goals simp only [evalCondition] at h ⊢
  all_goals first
    | exact cmpu_bool_lessdef hvp h1 h2 h
    | exact cmpu_bool_lessdef hvp h1 (.refl _) h
    | exact cmplu_bool_lessdef hvp h1 h2 h
    | exact cmplu_bool_lessdef hvp h1 (.refl _) h
    | exact cmpu_bool_lessdef hvp h1 (evalShift_lessdef _ _ h2) h
    | exact cmplu_bool_lessdef hvp h1 (evalShiftl_lessdef _ _ h2) h
    | (simp at h; done)
    | (cases h1 <;> (try cases h2) <;> first | exact h | (simp at h; done))

/-- `Op.eval_condition_lessdef` -/
theorem evalCondition_lessdef {cond : Condition} {vl1 vl2 : List Val} {b : Bool} {m1 m2 : Mem}
    (hl : Val.LessdefList vl1 vl2) (hm : Mem.Extends m1 m2)
    (h : evalCondition cond vl1 m1 = some b) : evalCondition cond vl2 m2 = some b :=
  evalCondition_lessdef_vp hl (fun _ _ hv => Mem.validPointer_extends hm hv) h


section ValUndef

/-! Strictness of the value operators: an undefined argument gives an
undefined result (or no result). -/

theorem add_undef_l (v : Val) : Val.add .Vundef v = .Vundef := by cases v <;> rfl
theorem add_undef_r (v : Val) : Val.add v .Vundef = .Vundef := by cases v <;> rfl
theorem sub_undef_l (v : Val) : Val.sub .Vundef v = .Vundef := by cases v <;> rfl
theorem sub_undef_r (v : Val) : Val.sub v .Vundef = .Vundef := by cases v <;> rfl
theorem mul_undef_l (v : Val) : Val.mul .Vundef v = .Vundef := by cases v <;> rfl
theorem mul_undef_r (v : Val) : Val.mul v .Vundef = .Vundef := by cases v <;> rfl
theorem and_undef_r (v : Val) : Val.and v .Vundef = .Vundef := by cases v <;> rfl
theorem or_undef_l (v : Val) : Val.or .Vundef v = .Vundef := by cases v <;> rfl
theorem or_undef_r (v : Val) : Val.or v .Vundef = .Vundef := by cases v <;> rfl
theorem xor_undef_l (v : Val) : Val.xor .Vundef v = .Vundef := by cases v <;> rfl
theorem xor_undef_r (v : Val) : Val.xor v .Vundef = .Vundef := by cases v <;> rfl
theorem shl_undef_l (v : Val) : Val.shl .Vundef v = .Vundef := by cases v <;> rfl
theorem shl_undef_r (v : Val) : Val.shl v .Vundef = .Vundef := by cases v <;> rfl
theorem shr_undef_l (v : Val) : Val.shr .Vundef v = .Vundef := by cases v <;> rfl
theorem shr_undef_r (v : Val) : Val.shr v .Vundef = .Vundef := by cases v <;> rfl
theorem shru_undef_l (v : Val) : Val.shru .Vundef v = .Vundef := by cases v <;> rfl
theorem shru_undef_r (v : Val) : Val.shru v .Vundef = .Vundef := by cases v <;> rfl
theorem ror_undef_l (v : Val) : Val.ror .Vundef v = .Vundef := by cases v <;> rfl
theorem ror_undef_r (v : Val) : Val.ror v .Vundef = .Vundef := by cases v <;> rfl
theorem longofwords_undef_l (v : Val) : Val.longofwords .Vundef v = .Vundef := by cases v <;> rfl
theorem longofwords_undef_r (v : Val) : Val.longofwords v .Vundef = .Vundef := by cases v <;> rfl
theorem addl_undef_l (v : Val) : Val.addl .Vundef v = .Vundef := by cases v <;> rfl
theorem addl_undef_r (v : Val) : Val.addl v .Vundef = .Vundef := by cases v <;> rfl
theorem subl_undef_l (v : Val) : Val.subl .Vundef v = .Vundef := by cases v <;> rfl
theorem subl_undef_r (v : Val) : Val.subl v .Vundef = .Vundef := by cases v <;> rfl
theorem mull_undef_l (v : Val) : Val.mull .Vundef v = .Vundef := by cases v <;> rfl
theorem mull_undef_r (v : Val) : Val.mull v .Vundef = .Vundef := by cases v <;> rfl
theorem mullhs_undef_l (v : Val) : Val.mullhs .Vundef v = .Vundef := by cases v <;> rfl
theorem mullhs_undef_r (v : Val) : Val.mullhs v .Vundef = .Vundef := by cases v <;> rfl
theorem mullhu_undef_l (v : Val) : Val.mullhu .Vundef v = .Vundef := by cases v <;> rfl
theorem mullhu_undef_r (v : Val) : Val.mullhu v .Vundef = .Vundef := by cases v <;> rfl
theorem andl_undef_r (v : Val) : Val.andl v .Vundef = .Vundef := by cases v <;> rfl
theorem orl_undef_l (v : Val) : Val.orl .Vundef v = .Vundef := by cases v <;> rfl
theorem orl_undef_r (v : Val) : Val.orl v .Vundef = .Vundef := by cases v <;> rfl
theorem xorl_undef_l (v : Val) : Val.xorl .Vundef v = .Vundef := by cases v <;> rfl
theorem xorl_undef_r (v : Val) : Val.xorl v .Vundef = .Vundef := by cases v <;> rfl
theorem shll_undef_l (v : Val) : Val.shll .Vundef v = .Vundef := by cases v <;> rfl
theorem shll_undef_r (v : Val) : Val.shll v .Vundef = .Vundef := by cases v <;> rfl
theorem shrl_undef_l (v : Val) : Val.shrl .Vundef v = .Vundef := by cases v <;> rfl
theorem shrl_undef_r (v : Val) : Val.shrl v .Vundef = .Vundef := by cases v <;> rfl
theorem shrlu_undef_l (v : Val) : Val.shrlu .Vundef v = .Vundef := by cases v <;> rfl
theorem shrlu_undef_r (v : Val) : Val.shrlu v .Vundef = .Vundef := by cases v <;> rfl
theorem rorl_undef_l (v : Val) : Val.rorl .Vundef v = .Vundef := by cases v <;> rfl
theorem rorl_undef_r (v : Val) : Val.rorl v .Vundef = .Vundef := by cases v <;> rfl
theorem addf_undef_l (v : Val) : Val.addf .Vundef v = .Vundef := by cases v <;> rfl
theorem addf_undef_r (v : Val) : Val.addf v .Vundef = .Vundef := by cases v <;> rfl
theorem subf_undef_l (v : Val) : Val.subf .Vundef v = .Vundef := by cases v <;> rfl
theorem subf_undef_r (v : Val) : Val.subf v .Vundef = .Vundef := by cases v <;> rfl
theorem mulf_undef_l (v : Val) : Val.mulf .Vundef v = .Vundef := by cases v <;> rfl
theorem mulf_undef_r (v : Val) : Val.mulf v .Vundef = .Vundef := by cases v <;> rfl
theorem divf_undef_l (v : Val) : Val.divf .Vundef v = .Vundef := by cases v <;> rfl
theorem divf_undef_r (v : Val) : Val.divf v .Vundef = .Vundef := by cases v <;> rfl
theorem addfs_undef_l (v : Val) : Val.addfs .Vundef v = .Vundef := by cases v <;> rfl
theorem addfs_undef_r (v : Val) : Val.addfs v .Vundef = .Vundef := by cases v <;> rfl
theorem subfs_undef_l (v : Val) : Val.subfs .Vundef v = .Vundef := by cases v <;> rfl
theorem subfs_undef_r (v : Val) : Val.subfs v .Vundef = .Vundef := by cases v <;> rfl
theorem mulfs_undef_l (v : Val) : Val.mulfs .Vundef v = .Vundef := by cases v <;> rfl
theorem mulfs_undef_r (v : Val) : Val.mulfs v .Vundef = .Vundef := by cases v <;> rfl
theorem divfs_undef_l (v : Val) : Val.divfs .Vundef v = .Vundef := by cases v <;> rfl
theorem divfs_undef_r (v : Val) : Val.divfs v .Vundef = .Vundef := by cases v <;> rfl
theorem neg_undef : Val.neg .Vundef = .Vundef := rfl
theorem notint_undef : Val.notint .Vundef = .Vundef := rfl
theorem negl_undef : Val.negl .Vundef = .Vundef := rfl
theorem notl_undef : Val.notl .Vundef = .Vundef := rfl
theorem negf_undef : Val.negf .Vundef = .Vundef := rfl
theorem absf_undef : Val.absf .Vundef = .Vundef := rfl
theorem negfs_undef : Val.negfs .Vundef = .Vundef := rfl
theorem absfs_undef : Val.absfs .Vundef = .Vundef := rfl
theorem singleoffloat_undef : Val.singleoffloat .Vundef = .Vundef := rfl
theorem floatofsingle_undef : Val.floatofsingle .Vundef = .Vundef := rfl
theorem loword_undef : Val.loword .Vundef = .Vundef := rfl
theorem hiword_undef : Val.hiword .Vundef = .Vundef := rfl
theorem longofint_undef : Val.longofint .Vundef = .Vundef := rfl
theorem longofintu_undef : Val.longofintu .Vundef = .Vundef := rfl
theorem zeroExt_undef (n : Nat) : Val.zeroExt n .Vundef = .Vundef := rfl
theorem signExt_undef (n : Nat) : Val.signExt n .Vundef = .Vundef := rfl
theorem zero_ext_l_undef (n : Nat) : Val.zero_ext_l n .Vundef = .Vundef := rfl
theorem sign_ext_l_undef (n : Nat) : Val.sign_ext_l n .Vundef = .Vundef := rfl
theorem divs_undef_l (v : Val) : Val.divs .Vundef v = none := by cases v <;> rfl
theorem divs_undef_r (v : Val) : Val.divs v .Vundef = none := by cases v <;> rfl
theorem divu_undef_l (v : Val) : Val.divu .Vundef v = none := by cases v <;> rfl
theorem divu_undef_r (v : Val) : Val.divu v .Vundef = none := by cases v <;> rfl
theorem divls_undef_l (v : Val) : Val.divls .Vundef v = none := by cases v <;> rfl
theorem divls_undef_r (v : Val) : Val.divls v .Vundef = none := by cases v <;> rfl
theorem divlu_undef_l (v : Val) : Val.divlu .Vundef v = none := by cases v <;> rfl
theorem divlu_undef_r (v : Val) : Val.divlu v .Vundef = none := by cases v <;> rfl
theorem shrx_undef_l (v : Val) : Val.shrx .Vundef v = none := by cases v <;> rfl
theorem shrxl_undef_l (v : Val) : Val.shrxl .Vundef v = none := by cases v <;> rfl
theorem intoffloat_undef : Val.intoffloat .Vundef = none := rfl
theorem intuoffloat_undef : Val.intuoffloat .Vundef = none := rfl
theorem floatofint_undef : Val.floatofint .Vundef = none := rfl
theorem floatofintu_undef : Val.floatofintu .Vundef = none := rfl
theorem intofsingle_undef : Val.intofsingle .Vundef = none := rfl
theorem intuofsingle_undef : Val.intuofsingle .Vundef = none := rfl
theorem singleofint_undef : Val.singleofint .Vundef = none := rfl
theorem singleofintu_undef : Val.singleofintu .Vundef = none := rfl
theorem longoffloat_undef : Val.longoffloat .Vundef = none := rfl
theorem longuoffloat_undef : Val.longuoffloat .Vundef = none := rfl
theorem floatoflong_undef : Val.floatoflong .Vundef = none := rfl
theorem floatoflongu_undef : Val.floatoflongu .Vundef = none := rfl
theorem longofsingle_undef : Val.longofsingle .Vundef = none := rfl
theorem longuofsingle_undef : Val.longuofsingle .Vundef = none := rfl
theorem singleoflong_undef : Val.singleoflong .Vundef = none := rfl
theorem singleoflongu_undef : Val.singleoflongu .Vundef = none := rfl

end ValUndef

/-- Rewrites an operator applied to an undefined argument. -/
macro "val_undef_simp" : tactic => `(tactic| simp only [add_undef_l, add_undef_r, sub_undef_l, sub_undef_r, mul_undef_l, mul_undef_r, and_undef_l, and_undef_r, or_undef_l, or_undef_r, xor_undef_l, xor_undef_r, shl_undef_l, shl_undef_r, shr_undef_l, shr_undef_r, shru_undef_l, shru_undef_r, ror_undef_l, ror_undef_r, longofwords_undef_l, longofwords_undef_r, addl_undef_l, addl_undef_r, subl_undef_l, subl_undef_r, mull_undef_l, mull_undef_r, mullhs_undef_l, mullhs_undef_r, mullhu_undef_l, mullhu_undef_r, andl_undef_l, andl_undef_r, orl_undef_l, orl_undef_r, xorl_undef_l, xorl_undef_r, shll_undef_l, shll_undef_r, shrl_undef_l, shrl_undef_r, shrlu_undef_l, shrlu_undef_r, rorl_undef_l, rorl_undef_r, addf_undef_l, addf_undef_r, subf_undef_l, subf_undef_r, mulf_undef_l, mulf_undef_r, divf_undef_l, divf_undef_r, addfs_undef_l, addfs_undef_r, subfs_undef_l, subfs_undef_r, mulfs_undef_l, mulfs_undef_r, divfs_undef_l, divfs_undef_r, neg_undef, notint_undef, negl_undef, notl_undef, negf_undef, absf_undef, negfs_undef, absfs_undef, singleoffloat_undef, floatofsingle_undef, loword_undef, hiword_undef, longofint_undef, longofintu_undef, zeroExt_undef, signExt_undef, zero_ext_l_undef, sign_ext_l_undef, divs_undef_l, divs_undef_r, divu_undef_l, divu_undef_r, divls_undef_l, divls_undef_r, divlu_undef_l, divlu_undef_r, shrx_undef_l, shrxl_undef_l, intoffloat_undef, intuoffloat_undef, floatofint_undef, floatofintu_undef, intofsingle_undef, intuofsingle_undef, singleofint_undef, singleofintu_undef, longoffloat_undef, longuoffloat_undef, floatoflong_undef, floatoflongu_undef, longofsingle_undef, longuofsingle_undef, singleoflong_undef, singleoflongu_undef, evalShift_undef, evalShiftl_undef, evalExtend_undef])
macro "val_undef_simp" "at" h:ident : tactic => `(tactic| simp only [add_undef_l, add_undef_r, sub_undef_l, sub_undef_r, mul_undef_l, mul_undef_r, and_undef_l, and_undef_r, or_undef_l, or_undef_r, xor_undef_l, xor_undef_r, shl_undef_l, shl_undef_r, shr_undef_l, shr_undef_r, shru_undef_l, shru_undef_r, ror_undef_l, ror_undef_r, longofwords_undef_l, longofwords_undef_r, addl_undef_l, addl_undef_r, subl_undef_l, subl_undef_r, mull_undef_l, mull_undef_r, mullhs_undef_l, mullhs_undef_r, mullhu_undef_l, mullhu_undef_r, andl_undef_l, andl_undef_r, orl_undef_l, orl_undef_r, xorl_undef_l, xorl_undef_r, shll_undef_l, shll_undef_r, shrl_undef_l, shrl_undef_r, shrlu_undef_l, shrlu_undef_r, rorl_undef_l, rorl_undef_r, addf_undef_l, addf_undef_r, subf_undef_l, subf_undef_r, mulf_undef_l, mulf_undef_r, divf_undef_l, divf_undef_r, addfs_undef_l, addfs_undef_r, subfs_undef_l, subfs_undef_r, mulfs_undef_l, mulfs_undef_r, divfs_undef_l, divfs_undef_r, neg_undef, notint_undef, negl_undef, notl_undef, negf_undef, absf_undef, negfs_undef, absfs_undef, singleoffloat_undef, floatofsingle_undef, loword_undef, hiword_undef, longofint_undef, longofintu_undef, zeroExt_undef, signExt_undef, zero_ext_l_undef, sign_ext_l_undef, divs_undef_l, divs_undef_r, divu_undef_l, divu_undef_r, divls_undef_l, divls_undef_r, divlu_undef_l, divlu_undef_r, shrx_undef_l, shrxl_undef_l, intoffloat_undef, intuoffloat_undef, floatofint_undef, floatofintu_undef, intofsingle_undef, intuofsingle_undef, singleofint_undef, singleofintu_undef, longoffloat_undef, longuoffloat_undef, floatoflong_undef, floatoflongu_undef, longofsingle_undef, longuofsingle_undef, singleoflong_undef, singleoflongu_undef, evalShift_undef, evalShiftl_undef, evalExtend_undef] at $h:ident)

/-- `Op.eval_operation_lessdef`, for any pair of memories where valid pointers
    stay valid. -/
theorem evalOperation_lessdef_vp {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    {vl1 vl2 : List Val} {v1 : Val} {m1 m2 : Mem}
    (hl : Val.LessdefList vl1 vl2)
    (hm : ∀ b ofs, Mem.validPointer m1 b ofs = true → Mem.validPointer m2 b ofs = true)
    (h : evalOperation ge sp op vl1 m1 = some v1) :
    ∃ v2, evalOperation ge sp op vl2 m2 = some v2 ∧ Val.Lessdef v1 v2 := by
  cases op
  case Ocmp c =>
    have e : evalOperation ge sp (.Ocmp c) vl1 m1 =
        some (Val.ofOptbool (evalCondition c vl1 m1)) := by
      rcases vl1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    have e2 : evalOperation ge sp (.Ocmp c) vl2 m2 =
        some (Val.ofOptbool (evalCondition c vl2 m2)) := by
      rcases vl2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h
    exact ⟨_, e2, of_optbool_lessdef (fun b hb => evalCondition_lessdef_vp hl hm hb)⟩
  case Osel c ty =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, hl⟩⟩
    · cases h
    · cases h
    · cases h
      refine ⟨_, rfl, select_lessdef ty ?_ h1 h2⟩
      cases e : evalCondition c _ m1 with
      | none => exact .inl rfl
      | some b => exact .inr (evalCondition_lessdef_vp hl hm e).symm
  all_goals
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, hl⟩⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; refine ⟨_, rfl, ?_⟩;
       (try cases h1) <;> (try cases h2) <;> (try cases h3) <;>
       first
        | with_reducible exact .refl _
        | exact .undef _
        | (val_undef_simp; exact .undef _))
    | ((try cases h1) <;> (try cases h2) <;> first
        | exact ⟨_, h, .refl _⟩
        | (exfalso; unfold evalOperation at h; dsimp only at h; val_undef_simp at h; cases h))

/-- `Op.eval_operation_lessdef` -/
theorem evalOperation_lessdef {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    {vl1 vl2 : List Val} {v1 : Val} {m1 m2 : Mem}
    (hl : Val.LessdefList vl1 vl2) (hm : Mem.Extends m1 m2)
    (h : evalOperation ge sp op vl1 m1 = some v1) :
    ∃ v2, evalOperation ge sp op vl2 m2 = some v2 ∧ Val.Lessdef v1 v2 :=
  evalOperation_lessdef_vp ge sp op hl (fun _ _ hv => Mem.validPointer_extends hm hv) h

/-- `Op.eval_addressing_lessdef` -/
theorem evalAddressing_lessdef {F V : Type} (ge : Genv F V) (sp : Val) (addr : Addressing)
    {vl1 vl2 : List Val} {v1 : Val} (hl : Val.LessdefList vl1 vl2)
    (h : evalAddressing ge sp addr vl1 = some v1) :
    ∃ v2, evalAddressing ge sp addr vl2 = some v2 ∧ Val.Lessdef v1 v2 := by
  cases addr <;> rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; refine ⟨_, rfl, ?_⟩;
       (try cases h1) <;> (try cases h2) <;>
       first
        | with_reducible exact .refl _
        | exact .undef _
        | (val_undef_simp; exact .undef _))

/-- Monotonicity of a binary operator that is undefined as soon as one of
    its arguments is. -/
theorem lessdef_binop {g : Val → Val → Val} (hl : ∀ y, g .Vundef y = .Vundef)
    (hr : ∀ x, g x .Vundef = .Vundef) {a a' b b' : Val} (ha : Lessdef a a') (hb : Lessdef b b') :
    Lessdef (g a b) (g a' b') := by
  cases ha <;> cases hb
  · exact .refl _
  · rw [hr]; exact .undef _
  · rw [hl]; exact .undef _
  · rw [hl]; exact .undef _

end Op

/-- `Events.eval_builtin_arg_lessdef` -/
theorem evalBuiltinArg_lessdef {A : Type} {ge : Senv} {e1 e2 : A → Val} {sp : Val} {m1 m2 : Mem}
    (he : ∀ x, Val.Lessdef (e1 x) (e2 x)) (hm : Mem.Extends m1 m2) {a : BuiltinArg A} {v1 : Val}
    (h : EvalBuiltinArg ge e1 sp m1 a v1) :
    ∃ v2, EvalBuiltinArg ge e2 sp m2 a v2 ∧ Val.Lessdef v1 v2 := by
  induction h with
  | BA x => exact ⟨_, .BA x, he x⟩
  | BA_int n => exact ⟨_, .BA_int n, .refl _⟩
  | BA_long n => exact ⟨_, .BA_long n, .refl _⟩
  | BA_float n => exact ⟨_, .BA_float n, .refl _⟩
  | BA_single n => exact ⟨_, .BA_single n, .refl _⟩
  | BA_loadstack chunk ofs v hl =>
      obtain ⟨v2, h2, hv⟩ := Mem.loadv_extends hm hl (.refl _)
      exact ⟨v2, .BA_loadstack _ _ _ h2, hv⟩
  | BA_addrstack ofs => exact ⟨_, .BA_addrstack ofs, .refl _⟩
  | BA_loadglobal chunk id ofs v hl =>
      obtain ⟨v2, h2, hv⟩ := Mem.loadv_extends hm hl (.refl _)
      exact ⟨v2, .BA_loadglobal _ _ _ _ h2, hv⟩
  | BA_addrglobal id ofs => exact ⟨_, .BA_addrglobal id ofs, .refl _⟩
  | BA_splitlong hi lo vhi vlo _ _ ih1 ih2 =>
      obtain ⟨v1', e1', l1⟩ := ih1
      obtain ⟨v2', e2', l2⟩ := ih2
      exact ⟨_, .BA_splitlong _ _ _ _ e1' e2',
        Op.lessdef_binop Op.longofwords_undef_l Op.longofwords_undef_r l1 l2⟩
  | BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 =>
      obtain ⟨v1', e1', l1⟩ := ih1
      obtain ⟨v2', e2', l2⟩ := ih2
      refine ⟨_, .BA_addptr _ _ _ _ e1' e2', ?_⟩
      cases hp : Archi.ptr64
      · simp only [Bool.false_eq_true, if_false]
        exact Op.lessdef_binop Op.add_undef_l Op.add_undef_r l1 l2
      · simp only [if_true]
        exact Op.lessdef_binop Op.addl_undef_l Op.addl_undef_r l1 l2

/-- `Events.eval_builtin_args_lessdef` -/
theorem evalBuiltinArgs_lessdef {A : Type} {ge : Senv} {e1 e2 : A → Val} {sp : Val}
    {m1 m2 : Mem} (he : ∀ x, Val.Lessdef (e1 x) (e2 x)) (hm : Mem.Extends m1 m2) :
    ∀ {al : List (BuiltinArg A)} {vl1 : List Val}, EvalBuiltinArgs ge e1 sp m1 al vl1 →
      ∃ vl2, EvalBuiltinArgs ge e2 sp m2 al vl2 ∧ Val.LessdefList vl1 vl2
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons h hl => by
      obtain ⟨v2, h2, l2⟩ := evalBuiltinArg_lessdef he hm h
      obtain ⟨vl2, hl2, ll2⟩ := evalBuiltinArgs_lessdef he hm hl
      exact ⟨v2 :: vl2, .cons h2 hl2, .cons l2 ll2⟩

end CC
