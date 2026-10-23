/-
  Soundness of the abstract interpretation of aarch64 operators — port of
  section `SOUNDNESS` of `aarch64/ValueAOp.v`.

  Ported: `eval_static_shift_sound`, `eval_static_shiftl_sound`,
  `eval_static_extend_sound`, `eval_static_condition_sound`,
  `symbol_address_sound`, `symbol_address_sound_2`,
  `eval_static_addressing_sound`, `eval_static_operation_sound`.
-/
import CCLib.aarch64.ValueAOp
import CCLib.backend.ValueDomainEnv
import CCLib.common.LinkingTheory

namespace CC
namespace ValueAOp

open ValueDomain Op

section SOUNDNESS
variable {bc : BlockClassification}

/-- `ValueAOp.eval_static_shift_sound` -/
theorem eval_static_shift_sound {v : Val} {av : Aval} (s : Shift) (n : Amount32)
    (h : Vmatch bc v av) : Vmatch bc (evalShift s v n) (evalStaticShift s av n) := by
  cases s
  · exact shl_sound h (.i _)
  · exact shru_sound h (.i _)
  · exact shr_sound h (.i _)
  · exact ror_sound h (.i _)

/-- `ValueAOp.eval_static_shiftl_sound` -/
theorem eval_static_shiftl_sound {v : Val} {av : Aval} (s : Shift) (n : Amount64)
    (h : Vmatch bc v av) : Vmatch bc (evalShiftl s v n) (evalStaticShiftl s av n) := by
  cases s
  · exact shll_sound h (.i _)
  · exact shrlu_sound h (.i _)
  · exact shrl_sound h (.i _)
  · exact rorl_sound h (.i _)

/-- `ValueAOp.eval_static_extend_sound` -/
theorem eval_static_extend_sound {v : Val} {av : Aval} (x : Extension) (n : Amount64)
    (h : Vmatch bc v av) : Vmatch bc (evalExtend x v n) (evalStaticExtend x av n) := by
  cases x
  · exact shll_sound (longofint_sound h) (.i _)
  · exact shll_sound (longofintu_sound h) (.i _)

theorem maskzero_eq (v : Val) (n : Integers.Int) :
    Val.cmp_bool .Ceq (Val.and v (.Vint n)) (.Vint Integers.Int.zero) = Val.maskzero_bool v n := by
  cases v <;> rfl

theorem masknotzero_eq (v : Val) (n : Integers.Int) :
    Val.cmp_bool .Cne (Val.and v (.Vint n)) (.Vint Integers.Int.zero) =
      (Val.maskzero_bool v n).map not := by
  cases v <;> rfl

/-- `ValueAOp.eval_static_condition_sound` -/
theorem eval_static_condition_sound (o : Options) (cond : Condition) {vargs : List Val} (m : Mem)
    {aargs : List Aval} (hl : ListForall2 (Vmatch bc) vargs aargs) :
    Cmatch (evalCondition cond vargs m) (evalStaticCondition o cond aargs) := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩ <;> cases cond <;>
    simp only [evalCondition, evalStaticCondition] <;> try exact .none
  all_goals first
    | exact cmp_bool_sound _ h1 h2
    | exact cmpu_bool_sound _ _ _ h1 h2
    | exact cmp_bool_sound _ h1 (.i _)
    | exact cmpu_bool_sound _ _ _ h1 (.i _)
    | exact cmp_bool_sound _ h1 (eval_static_shift_sound _ _ h2)
    | exact cmpu_bool_sound _ _ _ h1 (eval_static_shift_sound _ _ h2)
    | (rw [maskzero_eq]; exact maskzero_sound _ h1)
    | (rw [masknotzero_eq]; exact cnot_sound (maskzero_sound _ h1))
    | exact cmpl_bool_sound _ h1 h2
    | exact cmplu_bool_sound _ _ _ h1 h2
    | exact cmpl_bool_sound _ h1 (.l _)
    | exact cmplu_bool_sound _ _ _ h1 (.l _)
    | exact cmpl_bool_sound _ h1 (eval_static_shiftl_sound _ _ h2)
    | exact cmplu_bool_sound _ _ _ h1 (eval_static_shiftl_sound _ _ h2)
    | exact cmpl_bool_sound _ (andl_sound h1 (.l _)) (.l _)
    | exact cmpf_bool_sound _ h1 h2
    | exact cnot_sound (cmpf_bool_sound _ h1 h2)
    | exact cmpf_bool_sound _ h1 (.f _)
    | exact cnot_sound (cmpf_bool_sound _ h1 (.f _))
    | exact cmpfs_bool_sound _ h1 h2
    | exact cnot_sound (cmpfs_bool_sound _ h1 h2)
    | exact cmpfs_bool_sound _ h1 (.s _)
    | exact cnot_sound (cmpfs_bool_sound _ h1 (.s _))

/-- `ValueAOp.symbol_address_sound_2` -/
theorem symbol_address_sound_2 {F V : Type} {ge : Genv F V} (hge : GenvMatch bc ge) (id : Ident)
    (ofs : Integers.Ptrofs) : Vmatch bc (Genv.symbolAddress ge id ofs) (.Ifptr (.Gl id ofs)) := by
  unfold Genv.symbolAddress
  cases hf : Genv.findSymbol ge id with
  | none => exact .ifptr_undef _
  | some b => exact .ifptr_p _ _ _ (.gl _ ((hge.1 id b).1 hf))

theorem addrstack_sound {sp : Block} (hsp : bc sp = .BCstack) (ofs : Integers.Ptrofs) :
    Vmatch bc (Val.offsetPtr (.Vptr sp Integers.Ptrofs.zero) ofs) (.Ptr (.Stk ofs)) := by
  simp only [Val.offsetPtr, Integers.Ptrofs.add_zero_l]
  exact .ptr _ _ _ (.stk hsp)

/-- `ValueAOp.eval_static_addressing_sound` -/
theorem eval_static_addressing_sound {F V : Type} {ge : Genv F V} (hge : GenvMatch bc ge)
    {sp : Block} (hsp : bc sp = .BCstack) (addr : Addressing) {vargs : List Val} {vres : Val}
    {aargs : List Aval}
    (h : evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) addr vargs = some vres)
    (hl : ListForall2 (Vmatch bc) vargs aargs) :
    Vmatch bc vres (evalStaticAddressing addr aargs) := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩ <;> cases addr <;>
    simp only [evalAddressing, evalStaticAddressing, reduceCtorEq, Option.some.injEq] at h ⊢ <;>
    subst h
  · exact symbol_address_sound _ _ hge
  · exact addrstack_sound hsp _
  · exact addl_sound h1 (.l _)
  · exact addl_sound h1 h2
  · exact addl_sound h1 (shll_sound h2 (.i _))
  · exact addl_sound h1 (eval_static_extend_sound _ _ h2)

/-- Repeatedly apply the soundness lemmas of the abstract operators. -/
macro "va_auto" : tactic => `(tactic| repeat' first
  | assumption
  | exact Vmatch.i _ | exact Vmatch.l _ | exact Vmatch.f _ | exact Vmatch.s _
  | apply eval_static_shift_sound | apply eval_static_shiftl_sound
  | apply eval_static_extend_sound
  | apply add_sound | apply sub_sound | apply neg_sound | apply mul_sound
  | apply divs_sound | apply divu_sound
  | apply and_sound | apply or_sound | apply xor_sound | apply notint_sound
  | apply shl_sound | apply shr_sound | apply shru_sound | apply shrx_sound
  | apply zero_ext_sound | apply sign_ext_sound
  | apply longofwords_sound | apply loword_sound | apply hiword_sound
  | apply addl_sound | apply subl_sound | apply negl_sound | apply mull_sound
  | apply mullhs_sound | apply mullhu_sound | apply divls_sound | apply divlu_sound
  | apply andl_sound | apply orl_sound | apply xorl_sound | apply notl_sound
  | apply shll_sound | apply shrl_sound | apply shrlu_sound | apply shrxl_sound
  | apply zero_ext_l_sound | apply sign_ext_l_sound
  | apply negf_sound | apply absf_sound | apply addf_sound | apply subf_sound
  | apply mulf_sound | apply divf_sound
  | apply negfs_sound | apply absfs_sound | apply addfs_sound | apply subfs_sound
  | apply mulfs_sound | apply divfs_sound
  | apply singleoffloat_sound | apply floatofsingle_sound
  | apply intoffloat_sound | apply intuoffloat_sound | apply floatofint_sound
  | apply floatofintu_sound | apply intofsingle_sound | apply intuofsingle_sound
  | apply singleofint_sound | apply singleofintu_sound
  | apply longoffloat_sound | apply longuoffloat_sound | apply floatoflong_sound
  | apply floatoflongu_sound | apply longofsingle_sound | apply longuofsingle_sound
  | apply singleoflong_sound | apply singleoflongu_sound)

/-- `ValueAOp.eval_static_operation_sound` -/
theorem eval_static_operation_sound (o : Options) {F V : Type} {ge : Genv F V}
    (hge : GenvMatch bc ge) {sp : Block} (hsp : bc sp = .BCstack) (op : Operation)
    {vargs : List Val} {m : Mem} {vres : Val} {aargs : List Aval}
    (h : evalOperation ge (.Vptr sp Integers.Ptrofs.zero) op vargs m = some vres)
    (hl : ListForall2 (Vmatch bc) vargs aargs) :
    Vmatch bc vres (evalStaticOperation o op aargs) := by
  cases op
  case Ocmp c =>
    have e : evalOperation ge (.Vptr sp Integers.Ptrofs.zero) (.Ocmp c) vargs m =
        some (Val.ofOptbool (evalCondition c vargs m)) := by
      rcases vargs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    have e2 : evalStaticOperation o (.Ocmp c) aargs = ofOptbool (evalStaticCondition o c aargs) := by
      rcases aargs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h; rw [e2]
    exact of_optbool_sound (eval_static_condition_sound o c m hl)
  case Osel c ty =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, hl⟩⟩
    · cases h
    · cases h
    · cases h
      exact select_sound _ ty (eval_static_condition_sound o c m hl) h1 h2
  all_goals
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, hl⟩⟩⟩⟩
  all_goals first
    | (cases h; done)
    | (cases h
       first
        | (exact symbol_address_sound _ _ hge)
        | (exact addrstack_sound hsp _)
        | (va_auto; done)
        | (dsimp only [evalStaticOperation]; split <;> constructor)
        | exact shl_sound (zero_ext_sound _ h1) (.i _)
        | exact shl_sound (sign_ext_sound _ h1) (.i _))
    | (va_auto; done)

end SOUNDNESS

end ValueAOp
end CC
