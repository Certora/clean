/-
  Evaluation of operators commutes with memory injections — port of the
  `EVAL_COMPAT` / `EVAL_INJECT` sections of `aarch64/Op.v`
  (`eval_condition_inj`, `eval_operation_inj`, `eval_addressing_inj`,
  `eval_shift_stack_operation`, `eval_shift_stack_addressing`) and
  `Events.eval_builtin_arg(s)_inject`.
-/
import CCLib.aarch64.OpLessdef
import CCLib.cfrontend.CopInject

namespace CC
namespace Op

open Val

/-- Closes `Val.Inject f x x` when `x` is built from non-pointer values. -/
syntax "inj_self" : tactic
macro_rules
  | `(tactic| inj_self) => `(tactic| first
      | exact .int _ | exact .long _ | exact .float _ | exact .single _ | exact .undef _
      | (split <;> inj_self))


/-- Closes `e = some v → Val.Inject f v v` when `e` is built from non-pointer values. -/
syntax "inj_opt" : tactic
macro_rules
  | `(tactic| inj_opt) => `(tactic| first
      | (intro h; cases h; inj_self)
      | (intro h; simp at h; done)
      | (intro h; simp only [Option.map] at h; revert h; inj_opt)
      | (split <;> inj_opt))

section
variable {f : Meminj}
theorem neg_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.neg v) (Val.neg v') := by
  cases h <;> simp only [Val.neg] <;> inj_self

theorem notint_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.notint v) (Val.notint v') := by
  cases h <;> simp only [Val.notint] <;> inj_self

theorem negl_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.negl v) (Val.negl v') := by
  cases h <;> simp only [Val.negl] <;> inj_self

theorem notl_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.notl v) (Val.notl v') := by
  cases h <;> simp only [Val.notl] <;> inj_self

theorem negf_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.negf v) (Val.negf v') := by
  cases h <;> simp only [Val.negf] <;> inj_self

theorem absf_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.absf v) (Val.absf v') := by
  cases h <;> simp only [Val.absf] <;> inj_self

theorem negfs_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.negfs v) (Val.negfs v') := by
  cases h <;> simp only [Val.negfs] <;> inj_self

theorem absfs_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.absfs v) (Val.absfs v') := by
  cases h <;> simp only [Val.absfs] <;> inj_self

theorem singleoffloat_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.singleoffloat v) (Val.singleoffloat v') := by
  cases h <;> simp only [Val.singleoffloat] <;> inj_self

theorem floatofsingle_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.floatofsingle v) (Val.floatofsingle v') := by
  cases h <;> simp only [Val.floatofsingle] <;> inj_self

theorem longofint_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.longofint v) (Val.longofint v') := by
  cases h <;> simp only [Val.longofint] <;> inj_self

theorem longofintu_inject {v v' : Val} (h : Inject f v v') : Inject f (Val.longofintu v) (Val.longofintu v') := by
  cases h <;> simp only [Val.longofintu] <;> inj_self

theorem zeroExt_inject (n : Nat) {v v' : Val} (h : Inject f v v') :
    Inject f (Val.zeroExt n v) (Val.zeroExt n v') := by
  cases h <;> simp only [Val.zeroExt] <;> inj_self

theorem signExt_inject (n : Nat) {v v' : Val} (h : Inject f v v') :
    Inject f (Val.signExt n v) (Val.signExt n v') := by
  cases h <;> simp only [Val.signExt] <;> inj_self

theorem zero_ext_l_inject (n : Nat) {v v' : Val} (h : Inject f v v') :
    Inject f (Val.zero_ext_l n v) (Val.zero_ext_l n v') := by
  cases h <;> simp only [Val.zero_ext_l] <;> inj_self

theorem sign_ext_l_inject (n : Nat) {v v' : Val} (h : Inject f v v') :
    Inject f (Val.sign_ext_l n v) (Val.sign_ext_l n v') := by
  cases h <;> simp only [Val.sign_ext_l] <;> inj_self

theorem mul_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mul a b) (Val.mul a' b') := by
  cases ha <;> cases hb <;> simp only [Val.mul] <;> inj_self

theorem and_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.and a b) (Val.and a' b') := by
  cases ha <;> cases hb <;> simp only [Val.and] <;> inj_self

theorem or_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.or a b) (Val.or a' b') := by
  cases ha <;> cases hb <;> simp only [Val.or] <;> inj_self

theorem xor_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.xor a b) (Val.xor a' b') := by
  cases ha <;> cases hb <;> simp only [Val.xor] <;> inj_self

theorem shl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.shl a b) (Val.shl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shl] <;> inj_self

theorem shr_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.shr a b) (Val.shr a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shr] <;> inj_self

theorem shru_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.shru a b) (Val.shru a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shru] <;> inj_self

theorem ror_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.ror a b) (Val.ror a' b') := by
  cases ha <;> cases hb <;> simp only [Val.ror] <;> inj_self

theorem mull_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mull a b) (Val.mull a' b') := by
  cases ha <;> cases hb <;> simp only [Val.mull] <;> inj_self

theorem mullhs_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mullhs a b) (Val.mullhs a' b') := by
  cases ha <;> cases hb <;> simp only [Val.mullhs] <;> inj_self

theorem mullhu_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mullhu a b) (Val.mullhu a' b') := by
  cases ha <;> cases hb <;> simp only [Val.mullhu] <;> inj_self

theorem andl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.andl a b) (Val.andl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.andl] <;> inj_self

theorem orl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.orl a b) (Val.orl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.orl] <;> inj_self

theorem xorl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.xorl a b) (Val.xorl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.xorl] <;> inj_self

theorem shll_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.shll a b) (Val.shll a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shll] <;> inj_self

theorem shrl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.shrl a b) (Val.shrl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shrl] <;> inj_self

theorem shrlu_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.shrlu a b) (Val.shrlu a' b') := by
  cases ha <;> cases hb <;> simp only [Val.shrlu] <;> inj_self

theorem rorl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.rorl a b) (Val.rorl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.rorl] <;> inj_self

theorem addf_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.addf a b) (Val.addf a' b') := by
  cases ha <;> cases hb <;> simp only [Val.addf] <;> inj_self

theorem subf_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.subf a b) (Val.subf a' b') := by
  cases ha <;> cases hb <;> simp only [Val.subf] <;> inj_self

theorem mulf_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mulf a b) (Val.mulf a' b') := by
  cases ha <;> cases hb <;> simp only [Val.mulf] <;> inj_self

theorem divf_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.divf a b) (Val.divf a' b') := by
  cases ha <;> cases hb <;> simp only [Val.divf] <;> inj_self

theorem addfs_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.addfs a b) (Val.addfs a' b') := by
  cases ha <;> cases hb <;> simp only [Val.addfs] <;> inj_self

theorem subfs_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.subfs a b) (Val.subfs a' b') := by
  cases ha <;> cases hb <;> simp only [Val.subfs] <;> inj_self

theorem mulfs_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.mulfs a b) (Val.mulfs a' b') := by
  cases ha <;> cases hb <;> simp only [Val.mulfs] <;> inj_self

theorem divfs_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.divfs a b) (Val.divfs a' b') := by
  cases ha <;> cases hb <;> simp only [Val.divfs] <;> inj_self

theorem divs_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.divs a b = some v) : ∃ v', Val.divs a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.divs] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem divu_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.divu a b = some v) : ∃ v', Val.divu a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.divu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem shrx_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.shrx a b = some v) : ∃ v', Val.shrx a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.shrx] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem divls_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.divls a b = some v) : ∃ v', Val.divls a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.divls] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem divlu_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.divlu a b = some v) : ∃ v', Val.divlu a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.divlu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem shrxl_inject {a a' b b' v : Val} (ha : Inject f a a') (hb : Inject f b b')
    (h : Val.shrxl a b = some v) : ∃ v', Val.shrxl a' b' = some v' ∧ Inject f v v' := by
  cases ha <;> cases hb <;> simp only [Val.shrxl] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem intoffloat_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.intoffloat a = some v) : ∃ v', Val.intoffloat a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.intoffloat] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem intuoffloat_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.intuoffloat a = some v) : ∃ v', Val.intuoffloat a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.intuoffloat] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem floatofint_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.floatofint a = some v) : ∃ v', Val.floatofint a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.floatofint] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem floatofintu_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.floatofintu a = some v) : ∃ v', Val.floatofintu a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.floatofintu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem intofsingle_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.intofsingle a = some v) : ∃ v', Val.intofsingle a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.intofsingle] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem intuofsingle_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.intuofsingle a = some v) : ∃ v', Val.intuofsingle a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.intuofsingle] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem singleofint_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.singleofint a = some v) : ∃ v', Val.singleofint a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.singleofint] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem singleofintu_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.singleofintu a = some v) : ∃ v', Val.singleofintu a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.singleofintu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem longoffloat_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.longoffloat a = some v) : ∃ v', Val.longoffloat a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.longoffloat] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem longuoffloat_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.longuoffloat a = some v) : ∃ v', Val.longuoffloat a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.longuoffloat] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem floatoflong_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.floatoflong a = some v) : ∃ v', Val.floatoflong a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.floatoflong] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem floatoflongu_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.floatoflongu a = some v) : ∃ v', Val.floatoflongu a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.floatoflongu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem longofsingle_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.longofsingle a = some v) : ∃ v', Val.longofsingle a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.longofsingle] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem longuofsingle_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.longuofsingle a = some v) : ∃ v', Val.longuofsingle a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.longuofsingle] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem singleoflong_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.singleoflong a = some v) : ∃ v', Val.singleoflong a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.singleoflong] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)

theorem singleoflongu_inject {a a' v : Val} (ha : Inject f a a')
    (h : Val.singleoflongu a = some v) : ∃ v', Val.singleoflongu a' = some v' ∧ Inject f v v' := by
  cases ha <;> simp only [Val.singleoflongu] at h ⊢ <;>
    first | (cases h; done) | (refine ⟨v, h, ?_⟩; revert h; inj_opt)


theorem evalShift_inject (s : Shift) (a : Amount32) {v v' : Val} (h : Inject f v v') :
    Inject f (evalShift s v a) (evalShift s v' a) := by
  cases h <;> cases s <;>
    simp only [evalShift, Val.shl, Val.shru, Val.shr, Val.ror] <;> inj_self

theorem evalShiftl_inject (s : Shift) (a : Amount64) {v v' : Val} (h : Inject f v v') :
    Inject f (evalShiftl s v a) (evalShiftl s v' a) := by
  cases h <;> cases s <;>
    simp only [evalShiftl, Val.shll, Val.shrlu, Val.shrl, Val.rorl] <;> inj_self

theorem evalExtend_inject (x : Extension) (a : Amount64) {v v' : Val} (h : Inject f v v') :
    Inject f (evalExtend x v a) (evalExtend x v' a) := by
  cases h <;> cases x <;>
    simp only [evalExtend, Val.shll, Val.longofint, Val.longofintu] <;> inj_self

open Integers in
theorem addl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.addl a b) (Val.addl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.addl, Archi.ptr64, if_true] <;> try inj_self
  all_goals
    refine .ptr _ ‹_› ?_
    subst_vars
    rw [Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr _)]

open Integers in
theorem subl_inject {a a' b b' : Val} (ha : Inject f a a') (hb : Inject f b b') :
    Inject f (Val.subl a b) (Val.subl a' b') := by
  cases ha <;> cases hb <;> simp only [Val.subl, Archi.ptr64, if_true, Bool.not_true,
    Bool.false_eq_true, if_false] <;> try inj_self
  · refine .ptr _ ‹_› ?_
    subst_vars
    rw [Ptrofs.sub_add_l]
  · rename_i b1 _ _ _ delta1 hf1 ho1 b3 _ _ _ delta2 hf2 ho2
    split
    · next e =>
      subst e
      rw [hf1] at hf2; cases hf2
      rw [if_pos rfl, ho1, ho2, Ptrofs.sub_shifted]; exact .long _
    · exact .undef _

/-- Proves `Val.Inject f e e'` for operator expressions `e`, `e'` built
    from injected arguments. -/
syntax "inj_comp" : tactic
macro_rules
  | `(tactic| inj_comp) => `(tactic| first
      | assumption | exact .int _ | exact .long _ | exact .float _ | exact .single _
      | exact .undef _
      | (with_reducible apply neg_inject <;> inj_comp) | (with_reducible apply notint_inject <;> inj_comp) | (with_reducible apply negl_inject <;> inj_comp) | (with_reducible apply notl_inject <;> inj_comp) | (with_reducible apply negf_inject <;> inj_comp) | (with_reducible apply absf_inject <;> inj_comp) | (with_reducible apply negfs_inject <;> inj_comp) | (with_reducible apply absfs_inject <;> inj_comp) | (with_reducible apply singleoffloat_inject <;> inj_comp) | (with_reducible apply floatofsingle_inject <;> inj_comp) | (with_reducible apply longofint_inject <;> inj_comp) | (with_reducible apply longofintu_inject <;> inj_comp) | (with_reducible apply zeroExt_inject <;> inj_comp) | (with_reducible apply signExt_inject <;> inj_comp) | (with_reducible apply zero_ext_l_inject <;> inj_comp) | (with_reducible apply sign_ext_l_inject <;> inj_comp) | (with_reducible apply mul_inject <;> inj_comp) | (with_reducible apply and_inject <;> inj_comp) | (with_reducible apply or_inject <;> inj_comp) | (with_reducible apply xor_inject <;> inj_comp) | (with_reducible apply shl_inject <;> inj_comp) | (with_reducible apply shr_inject <;> inj_comp) | (with_reducible apply shru_inject <;> inj_comp) | (with_reducible apply ror_inject <;> inj_comp) | (with_reducible apply mull_inject <;> inj_comp) | (with_reducible apply mullhs_inject <;> inj_comp) | (with_reducible apply mullhu_inject <;> inj_comp) | (with_reducible apply andl_inject <;> inj_comp) | (with_reducible apply orl_inject <;> inj_comp) | (with_reducible apply xorl_inject <;> inj_comp) | (with_reducible apply shll_inject <;> inj_comp) | (with_reducible apply shrl_inject <;> inj_comp) | (with_reducible apply shrlu_inject <;> inj_comp) | (with_reducible apply rorl_inject <;> inj_comp) | (with_reducible apply addf_inject <;> inj_comp) | (with_reducible apply subf_inject <;> inj_comp) | (with_reducible apply mulf_inject <;> inj_comp) | (with_reducible apply divf_inject <;> inj_comp) | (with_reducible apply addfs_inject <;> inj_comp) | (with_reducible apply subfs_inject <;> inj_comp) | (with_reducible apply mulfs_inject <;> inj_comp) | (with_reducible apply divfs_inject <;> inj_comp) | (with_reducible apply addl_inject <;> inj_comp) | (with_reducible apply subl_inject <;> inj_comp) | (with_reducible apply evalShift_inject <;> inj_comp) | (with_reducible apply evalShiftl_inject <;> inj_comp) | (with_reducible apply evalExtend_inject <;> inj_comp) | (with_reducible apply Val.add_inject <;> inj_comp) | (with_reducible apply Val.sub_inject <;> inj_comp) | (with_reducible apply Val.longofwords_inject <;> inj_comp) | (with_reducible apply Val.loword_inject <;> inj_comp) | (with_reducible apply Val.hiword_inject <;> inj_comp) | (with_reducible apply Val.offset_ptr_inject <;> inj_comp))

/-- Closes an `Option`-valued operator case. -/
macro "inj_optop" : tactic => `(tactic| first | exact shrx_inject ‹_› (.int _) ‹_› | exact shrxl_inject ‹_› (.int _) ‹_› | exact divs_inject ‹_› ‹_› ‹_› | exact divu_inject ‹_› ‹_› ‹_› | exact shrx_inject ‹_› ‹_› ‹_› | exact divls_inject ‹_› ‹_› ‹_› | exact divlu_inject ‹_› ‹_› ‹_› | exact shrxl_inject ‹_› ‹_› ‹_› | exact intoffloat_inject ‹_› ‹_› | exact intuoffloat_inject ‹_› ‹_› | exact floatofint_inject ‹_› ‹_› | exact floatofintu_inject ‹_› ‹_› | exact intofsingle_inject ‹_› ‹_› | exact intuofsingle_inject ‹_› ‹_› | exact singleofint_inject ‹_› ‹_› | exact singleofintu_inject ‹_› ‹_› | exact longoffloat_inject ‹_› ‹_› | exact longuoffloat_inject ‹_› ‹_› | exact floatoflong_inject ‹_› ‹_› | exact floatoflongu_inject ‹_› ‹_› | exact longofsingle_inject ‹_› ‹_› | exact longuofsingle_inject ‹_› ‹_› | exact singleoflong_inject ‹_› ‹_› | exact singleoflongu_inject ‹_› ‹_›)

theorem cmpl_bool_inject (c : Comparison) {v1 v1' v2 v2' : Val} {b : Bool}
    (h1 : Inject f v1 v1') (h2 : Inject f v2 v2') (h : cmpl_bool c v1 v2 = some b) :
    cmpl_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;> simp_all [cmpl_bool]

theorem cmpf_bool_inject (c : Comparison) {v1 v1' v2 v2' : Val} {b : Bool}
    (h1 : Inject f v1 v1') (h2 : Inject f v2 v2') (h : cmpf_bool c v1 v2 = some b) :
    cmpf_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;> simp_all [cmpf_bool]

theorem cmpfs_bool_inject (c : Comparison) {v1 v1' v2 v2' : Val} {b : Bool}
    (h1 : Inject f v1 v1') (h2 : Inject f v2 v2') (h : cmpfs_bool c v1 v2 = some b) :
    cmpfs_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;> simp_all [cmpfs_bool]

theorem map_not_inject {o o' : Option Bool} {b : Bool} (hi : ∀ b, o = some b → o' = some b)
    (h : Option.map not o = some b) : Option.map not o' = some b := by
  cases o with
  | none => cases h
  | some x => rw [hi x rfl]; exact h

/-- `Op.eval_condition_inj` (for a memory injection). -/
theorem evalCondition_inject {cond : Condition} {vl1 vl2 : List Val} {b : Bool} {m1 m2 : Mem}
    (hl : InjectList f vl1 vl2) (hm : Mem.Inject f m1 m2)
    (h : evalCondition cond vl1 m1 = some b) : evalCondition cond vl2 m2 = some b := by
  have H := Cop.copInjHyps_of_inject hm
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals cases cond
  all_goals simp only [evalCondition] at h ⊢
  all_goals first
    | (simp at h; done)
    | exact cmp_bool_inject _ h1 h2 h
    | exact cmp_bool_inject _ h1 (.int _) h
    | exact cmp_bool_inject _ h1 (evalShift_inject _ _ h2) h
    | exact cmp_bool_inject _ (and_inject h1 (.int _)) (.int _) h
    | exact cmpl_bool_inject _ h1 h2 h
    | exact cmpl_bool_inject _ h1 (.long _) h
    | exact cmpl_bool_inject _ h1 (evalShiftl_inject _ _ h2) h
    | exact cmpl_bool_inject _ (andl_inject h1 (.long _)) (.long _) h
    | exact cmpf_bool_inject _ h1 h2 h
    | exact cmpf_bool_inject _ h1 (.float _) h
    | exact cmpfs_bool_inject _ h1 h2 h
    | exact cmpfs_bool_inject _ h1 (.single _) h
    | exact map_not_inject (fun _ => cmpf_bool_inject _ h1 h2) h
    | exact map_not_inject (fun _ => cmpf_bool_inject _ h1 (.float _)) h
    | exact map_not_inject (fun _ => cmpfs_bool_inject _ h1 h2) h
    | exact map_not_inject (fun _ => cmpfs_bool_inject _ h1 (.single _)) h
    | exact Val.cmpu_bool_inject H h1 h2 h
    | exact Val.cmpu_bool_inject H h1 (.int _) h
    | exact Val.cmpu_bool_inject H h1 (evalShift_inject _ _ h2) h
    | exact Cop.cmplu_bool_inject H h1 h2 h
    | exact Cop.cmplu_bool_inject H h1 (.long _) h
    | exact Cop.cmplu_bool_inject H h1 (evalShiftl_inject _ _ h2) h

theorem ofOptbool_inject {ob ob' : Option Bool} (hi : ∀ b, ob = some b → ob' = some b) :
    Inject f (Val.ofOptbool ob) (Val.ofOptbool ob') := by
  cases ob with
  | none => exact .undef _
  | some b => rw [hi b rfl]; cases b <;> exact .int _

set_option maxHeartbeats 4000000 in
/-- `Op.eval_operation_inj` (for a memory injection; the stack pointers are
    arbitrary injected values). -/
theorem evalOperation_inject {F V : Type} (ge : Genv F V)
    (hsym : ∀ id ofs, Inject f (Genv.symbolAddress ge id ofs) (Genv.symbolAddress ge id ofs))
    {sp1 sp2 : Val} (hsp : Inject f sp1 sp2) {op : Operation}
    {vl1 vl2 : List Val} {v1 : Val} {m1 m2 : Mem}
    (hl : InjectList f vl1 vl2) (hm : Mem.Inject f m1 m2)
    (h : evalOperation ge sp1 op vl1 m1 = some v1) :
    ∃ v2, evalOperation ge sp2 op vl2 m2 = some v2 ∧ Inject f v1 v2 := by
  cases op
  case Ocmp c =>
    have e : evalOperation ge sp1 (.Ocmp c) vl1 m1 =
        some (Val.ofOptbool (evalCondition c vl1 m1)) := by
      rcases vl1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    have e2 : evalOperation ge sp2 (.Ocmp c) vl2 m2 =
        some (Val.ofOptbool (evalCondition c vl2 m2)) := by
      rcases vl2 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h
    exact ⟨_, e2, ofOptbool_inject (fun b hb => evalCondition_inject hl hm hb)⟩
  case Osel c ty =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, hl⟩⟩
    · cases h
    · cases h
    · cases h
      refine ⟨_, rfl, Val.select_inject ty ?_ h1 h2⟩
      cases e : evalCondition c _ m1 with
      | none => exact .inl rfl
      | some b => exact .inr (evalCondition_inject hl hm e).symm
  all_goals
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, hl⟩⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, rfl, by inj_comp⟩)
    | (cases h; exact ⟨_, rfl, hsym _ _⟩)
    | inj_optop

/-- `Op.eval_addressing_inj` -/
theorem evalAddressing_inject {F V : Type} (ge : Genv F V)
    (hsym : ∀ id ofs, Inject f (Genv.symbolAddress ge id ofs) (Genv.symbolAddress ge id ofs))
    {sp1 sp2 : Val} (hsp : Inject f sp1 sp2) {addr : Addressing}
    {vl1 vl2 : List Val} {v1 : Val} (hl : InjectList f vl1 vl2)
    (h : evalAddressing ge sp1 addr vl1 = some v1) :
    ∃ v2, evalAddressing ge sp2 addr vl2 = some v2 ∧ Inject f v1 v2 := by
  cases addr <;> rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨_, rfl, by inj_comp⟩)
    | (cases h; exact ⟨_, rfl, hsym _ _⟩)

theorem evalOperation_sp_irrel {F V : Type} (ge : Genv F V) (sp1 sp2 : Val) (op : Operation)
    (hop : ∀ ofs, op ≠ .Oaddrstack ofs) (vl : List Val) (m : Mem) :
    evalOperation ge sp1 op vl m = evalOperation ge sp2 op vl m := by
  cases op
  case Oaddrstack ofs => exact absurd rfl (hop ofs)
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

theorem evalAddressing_sp_irrel {F V : Type} (ge : Genv F V) (sp1 sp2 : Val) (addr : Addressing)
    (ha : ∀ ofs, addr ≠ .Ainstack ofs) (vl : List Val) :
    evalAddressing ge sp1 addr vl = evalAddressing ge sp2 addr vl := by
  cases addr
  case Ainstack ofs => exact absurd rfl (ha ofs)
  all_goals rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-- `Op.eval_shift_stack_operation` -/
theorem evalOperation_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (delta : Z)
    (op : Operation) (vl : List Val) (m : Mem) :
    evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackOperation delta op) vl m =
      evalOperation ge (.Vptr sp (Integers.Ptrofs.repr delta)) op vl m := by
  by_cases hop : ∃ ofs, op = .Oaddrstack ofs
  · obtain ⟨ofs, rfl⟩ := hop
    rcases vl with _ | ⟨_, _⟩
    · show some (Val.offsetPtr _ _) = some (Val.offsetPtr _ _)
      simp only [Val.offsetPtr]
      rw [Integers.Ptrofs.add_commut Integers.Ptrofs.zero, Integers.Ptrofs.add_zero,
        Integers.Ptrofs.add_commut]
    · rfl
  · have hop' : ∀ ofs, op ≠ .Oaddrstack ofs := fun ofs e => hop ⟨ofs, e⟩
    have e : shiftStackOperation delta op = op := by
      cases op <;> first | rfl | exact absurd rfl (hop' _)
    rw [e]; exact evalOperation_sp_irrel ge _ _ op hop' vl m

/-- `Op.eval_shift_stack_addressing` -/
theorem evalAddressing_shiftStack {F V : Type} (ge : Genv F V) (sp : Block) (delta : Z)
    (addr : Addressing) (vl : List Val) :
    evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) (shiftStackAddressing delta addr) vl =
      evalAddressing ge (.Vptr sp (Integers.Ptrofs.repr delta)) addr vl := by
  by_cases ha : ∃ ofs, addr = .Ainstack ofs
  · obtain ⟨ofs, rfl⟩ := ha
    rcases vl with _ | ⟨_, _⟩
    · show some (Val.offsetPtr _ _) = some (Val.offsetPtr _ _)
      simp only [Val.offsetPtr]
      rw [Integers.Ptrofs.add_commut Integers.Ptrofs.zero, Integers.Ptrofs.add_zero,
        Integers.Ptrofs.add_commut]
    · rfl
  · have ha' : ∀ ofs, addr ≠ .Ainstack ofs := fun ofs e => ha ⟨ofs, e⟩
    have e : shiftStackAddressing delta addr = addr := by
      cases addr <;> first | rfl | exact absurd rfl (ha' _)
    rw [e]; exact evalAddressing_sp_irrel ge _ _ addr ha' vl

end

end Op

/-- `Events.eval_builtin_arg_inject`, generalised to two symbol environments
    and arbitrary register maps and stack pointers related by `f`. -/
theorem evalBuiltinArg_inject {A B : Type} {f : Val.Meminj} {ge1 ge2 : Senv}
    {e1 : A → Val} {e2 : B → Val} {sp1 sp2 : Val} {m1 m2 : Mem} (tr : A → B)
    (hsym : ∀ id ofs, Val.Inject f (ge1.symbolAddress id ofs) (ge2.symbolAddress id ofs))
    (hsp : Val.Inject f sp1 sp2) (he : ∀ x, Val.Inject f (e1 x) (e2 (tr x)))
    (hm : Mem.Inject f m1 m2) {a : BuiltinArg A} {v1 : Val}
    (h : EvalBuiltinArg ge1 e1 sp1 m1 a v1) :
    ∃ v2, EvalBuiltinArg ge2 e2 sp2 m2 (a.map tr) v2 ∧ Val.Inject f v1 v2 := by
  induction h with
  | BA x => exact ⟨_, .BA (tr x), he x⟩
  | BA_int n => exact ⟨_, .BA_int n, .int _⟩
  | BA_long n => exact ⟨_, .BA_long n, .long _⟩
  | BA_float n => exact ⟨_, .BA_float n, .float _⟩
  | BA_single n => exact ⟨_, .BA_single n, .single _⟩
  | BA_loadstack chunk ofs v hl =>
      obtain ⟨v2, h2, hv⟩ := Mem.loadv_inject hm hl (Val.offset_ptr_inject ofs hsp)
      exact ⟨v2, .BA_loadstack _ _ _ h2, hv⟩
  | BA_addrstack ofs => exact ⟨_, .BA_addrstack ofs, Val.offset_ptr_inject ofs hsp⟩
  | BA_loadglobal chunk id ofs v hl =>
      obtain ⟨v2, h2, hv⟩ := Mem.loadv_inject hm hl (hsym id ofs)
      exact ⟨v2, .BA_loadglobal _ _ _ _ h2, hv⟩
  | BA_addrglobal id ofs => exact ⟨_, .BA_addrglobal id ofs, hsym id ofs⟩
  | BA_splitlong hi lo vhi vlo _ _ ih1 ih2 =>
      obtain ⟨v1', e1', l1⟩ := ih1
      obtain ⟨v2', e2', l2⟩ := ih2
      exact ⟨_, .BA_splitlong _ _ _ _ e1' e2', Val.longofwords_inject l1 l2⟩
  | BA_addptr a1 a2 v1 v2 _ _ ih1 ih2 =>
      obtain ⟨v1', e1', l1⟩ := ih1
      obtain ⟨v2', e2', l2⟩ := ih2
      refine ⟨_, .BA_addptr _ _ _ _ e1' e2', ?_⟩
      simp only [Archi.ptr64, if_true]
      exact Op.addl_inject l1 l2

/-- `Events.eval_builtin_args_inject` (generalised as `evalBuiltinArg_inject`). -/
theorem evalBuiltinArgs_inject {A B : Type} {f : Val.Meminj} {ge1 ge2 : Senv}
    {e1 : A → Val} {e2 : B → Val} {sp1 sp2 : Val} {m1 m2 : Mem} (tr : A → B)
    (hsym : ∀ id ofs, Val.Inject f (ge1.symbolAddress id ofs) (ge2.symbolAddress id ofs))
    (hsp : Val.Inject f sp1 sp2) (he : ∀ x, Val.Inject f (e1 x) (e2 (tr x)))
    (hm : Mem.Inject f m1 m2) :
    ∀ {al : List (BuiltinArg A)} {vl1 : List Val}, EvalBuiltinArgs ge1 e1 sp1 m1 al vl1 →
      ∃ vl2, EvalBuiltinArgs ge2 e2 sp2 m2 (al.map (BuiltinArg.map tr)) vl2 ∧
        Val.InjectList f vl1 vl2
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons h hl => by
      obtain ⟨v2, h2, l2⟩ := evalBuiltinArg_inject tr hsym hsp he hm h
      obtain ⟨vl2, hl2, ll2⟩ := evalBuiltinArgs_inject tr hsym hsp he hm hl
      exact ⟨v2 :: vl2, .cons h2 hl2, .cons l2 ll2⟩

end CC
