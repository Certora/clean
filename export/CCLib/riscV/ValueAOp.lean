/-
  Value analysis for RISC-V operators — port of `riscV/ValueAOp.v`
  (definitions and section `SOUNDNESS`).

  Ported: `eval_static_condition`, `eval_static_addressing`,
  `eval_static_operation`, `eval_static_condition_sound`,
  `symbol_address_sound`, `symbol_address_sound_2`,
  `eval_static_addressing_sound`, `eval_static_operation_sound`.

  Differences from Rocq: as in `CCLib/aarch64/ValueAOp.lean`, the OCaml
  parameters `Compopts.va_strict` and `Compopts.propagate_float_constants`
  are the fields of an explicit `ValueAOp.Options` argument (the structure
  is shared with the aarch64 port).  `symbol_address_sound` and
  `symbol_address_sound_2` are the target-independent lemmas of
  `CCLib/backend/ValueDomainProof.lean` and `CCLib/aarch64/ValueAOpproof.lean`.
-/
import CCLib.riscV.Op
import CCLib.aarch64.ValueAOpproof

namespace CC
namespace RiscV
namespace ValueAOp

open ValueDomain Op
open CC.ValueAOp (Options)

section
variable (o : Options)

/-- `ValueAOp.eval_static_condition` (RISC-V) -/
def evalStaticCondition (cond : Condition) (vl : List Aval) : Abool :=
  match cond, vl with
  | .Ccomp c, [v1, v2] => cmpBool c v1 v2
  | .Ccompu c, [v1, v2] => cmpuBool o.strict c v1 v2
  | .Ccompimm c n, [v1] => cmpBool c v1 (.I n)
  | .Ccompuimm c n, [v1] => cmpuBool o.strict c v1 (.I n)
  | .Ccompl c, [v1, v2] => cmplBool c v1 v2
  | .Ccomplu c, [v1, v2] => cmpluBool o.strict c v1 v2
  | .Ccomplimm c n, [v1] => cmplBool c v1 (.L n)
  | .Ccompluimm c n, [v1] => cmpluBool o.strict c v1 (.L n)
  | .Ccompf c, [v1, v2] => cmpfBool c v1 v2
  | .Cnotcompf c, [v1, v2] => cnot (cmpfBool c v1 v2)
  | .Ccompfs c, [v1, v2] => cmpfsBool c v1 v2
  | .Cnotcompfs c, [v1, v2] => cnot (cmpfsBool c v1 v2)
  | _, _ => .Bnone

end

/-- `ValueAOp.eval_static_addressing` (RISC-V) -/
def evalStaticAddressing (addr : Addressing) (vl : List Aval) : Aval :=
  match addr, vl with
  | .Aindexed n, [v1] => offsetPtr v1 n
  | .Aglobal s ofs, [] => .Ptr (.Gl s ofs)
  | .Ainstack ofs, [] => .Ptr (.Stk ofs)
  | _, _ => .Vbot

section
variable (o : Options)

/-- `ValueAOp.eval_static_operation` (RISC-V) -/
def evalStaticOperation (op : Operation) (vl : List Aval) : Aval :=
  match op, vl with
  | .Omove, [v1] => v1
  | .Ointconst n, [] => .I n
  | .Olongconst n, [] => .L n
  | .Ofloatconst n, [] => if o.propagateFloatConstants then .F n else ntop
  | .Osingleconst n, [] => if o.propagateFloatConstants then .FS n else ntop
  | .Oaddrsymbol id ofs, [] => .Ptr (.Gl id ofs)
  | .Oaddrstack ofs, [] => .Ptr (.Stk ofs)
  | .Ocast8signed, [v1] => signExt 8 v1
  | .Ocast16signed, [v1] => signExt 16 v1
  | .Oadd, [v1, v2] => add v1 v2
  | .Oaddimm n, [v1] => add v1 (.I n)
  | .Oneg, [v1] => neg v1
  | .Osub, [v1, v2] => sub v1 v2
  | .Omul, [v1, v2] => mul v1 v2
  | .Omulhs, [v1, v2] => mulhs v1 v2
  | .Omulhu, [v1, v2] => mulhu v1 v2
  | .Odiv, [v1, v2] => divs o.strict v1 v2
  | .Odivu, [v1, v2] => divu o.strict v1 v2
  | .Omod, [v1, v2] => mods o.strict v1 v2
  | .Omodu, [v1, v2] => modu o.strict v1 v2
  | .Oand, [v1, v2] => and v1 v2
  | .Oandimm n, [v1] => and v1 (.I n)
  | .Oor, [v1, v2] => or v1 v2
  | .Oorimm n, [v1] => or v1 (.I n)
  | .Oxor, [v1, v2] => xor v1 v2
  | .Oxorimm n, [v1] => xor v1 (.I n)
  | .Oshl, [v1, v2] => shl v1 v2
  | .Oshlimm n, [v1] => shl v1 (.I n)
  | .Oshr, [v1, v2] => shr v1 v2
  | .Oshrimm n, [v1] => shr v1 (.I n)
  | .Oshru, [v1, v2] => shru v1 v2
  | .Oshruimm n, [v1] => shru v1 (.I n)
  | .Oshrximm n, [v1] => shrx v1 (.I n)
  | .Omakelong, [v1, v2] => longofwords v1 v2
  | .Olowlong, [v1] => loword v1
  | .Ohighlong, [v1] => hiword v1
  | .Ocast32signed, [v1] => longofint v1
  | .Ocast32unsigned, [v1] => longofintu v1
  | .Oaddl, [v1, v2] => addl v1 v2
  | .Oaddlimm n, [v1] => addl v1 (.L n)
  | .Onegl, [v1] => negl v1
  | .Osubl, [v1, v2] => subl v1 v2
  | .Omull, [v1, v2] => mull v1 v2
  | .Omullhs, [v1, v2] => mullhs v1 v2
  | .Omullhu, [v1, v2] => mullhu v1 v2
  | .Odivl, [v1, v2] => divls o.strict v1 v2
  | .Odivlu, [v1, v2] => divlu o.strict v1 v2
  | .Omodl, [v1, v2] => modls o.strict v1 v2
  | .Omodlu, [v1, v2] => modlu o.strict v1 v2
  | .Oandl, [v1, v2] => andl v1 v2
  | .Oandlimm n, [v1] => andl v1 (.L n)
  | .Oorl, [v1, v2] => orl v1 v2
  | .Oorlimm n, [v1] => orl v1 (.L n)
  | .Oxorl, [v1, v2] => xorl v1 v2
  | .Oxorlimm n, [v1] => xorl v1 (.L n)
  | .Oshll, [v1, v2] => shll v1 v2
  | .Oshllimm n, [v1] => shll v1 (.I n)
  | .Oshrl, [v1, v2] => shrl v1 v2
  | .Oshrlimm n, [v1] => shrl v1 (.I n)
  | .Oshrlu, [v1, v2] => shrlu v1 v2
  | .Oshrluimm n, [v1] => shrlu v1 (.I n)
  | .Oshrxlimm n, [v1] => shrxl v1 (.I n)
  | .Onegf, [v1] => negf v1
  | .Oabsf, [v1] => absf v1
  | .Oaddf, [v1, v2] => addf v1 v2
  | .Osubf, [v1, v2] => subf v1 v2
  | .Omulf, [v1, v2] => mulf v1 v2
  | .Odivf, [v1, v2] => divf v1 v2
  | .Onegfs, [v1] => negfs v1
  | .Oabsfs, [v1] => absfs v1
  | .Oaddfs, [v1, v2] => addfs v1 v2
  | .Osubfs, [v1, v2] => subfs v1 v2
  | .Omulfs, [v1, v2] => mulfs v1 v2
  | .Odivfs, [v1, v2] => divfs v1 v2
  | .Osingleoffloat, [v1] => singleoffloat v1
  | .Ofloatofsingle, [v1] => floatofsingle v1
  | .Ointoffloat, [v1] => intoffloat o.strict v1
  | .Ointuoffloat, [v1] => intuoffloat o.strict v1
  | .Ofloatofint, [v1] => floatofint v1
  | .Ofloatofintu, [v1] => floatofintu v1
  | .Ointofsingle, [v1] => intofsingle o.strict v1
  | .Ointuofsingle, [v1] => intuofsingle o.strict v1
  | .Osingleofint, [v1] => singleofint v1
  | .Osingleofintu, [v1] => singleofintu v1
  | .Olongoffloat, [v1] => longoffloat o.strict v1
  | .Olonguoffloat, [v1] => longuoffloat o.strict v1
  | .Ofloatoflong, [v1] => floatoflong v1
  | .Ofloatoflongu, [v1] => floatoflongu v1
  | .Olongofsingle, [v1] => longofsingle o.strict v1
  | .Olonguofsingle, [v1] => longuofsingle o.strict v1
  | .Osingleoflong, [v1] => singleoflong v1
  | .Osingleoflongu, [v1] => singleoflongu v1
  | .Ocmp c, _ => ofOptbool (evalStaticCondition o c vl)
  | .Osel c ty, v1 :: v2 :: vl => select o.strict (evalStaticCondition o c vl) v1 v2 ty
  | _, _ => .Vbot

end

/-! ## Soundness -/

section SOUNDNESS
variable {bc : BlockClassification}

/-- `ValueAOp.eval_static_condition_sound` (RISC-V) -/
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
    | exact cmpl_bool_sound _ h1 h2
    | exact cmplu_bool_sound _ _ _ h1 h2
    | exact cmpl_bool_sound _ h1 (.l _)
    | exact cmplu_bool_sound _ _ _ h1 (.l _)
    | exact cmpf_bool_sound _ h1 h2
    | exact cnot_sound (cmpf_bool_sound _ h1 h2)
    | exact cmpfs_bool_sound _ h1 h2
    | exact cnot_sound (cmpfs_bool_sound _ h1 h2)

/-- `ValueAOp.eval_static_addressing_sound` (RISC-V) -/
theorem eval_static_addressing_sound {F V : Type} {ge : Genv F V} (hge : GenvMatch bc ge)
    {sp : Block} (hsp : bc sp = .BCstack) (addr : Addressing) {vargs : List Val} {vres : Val}
    {aargs : List Aval}
    (h : evalAddressing ge (.Vptr sp Integers.Ptrofs.zero) addr vargs = some vres)
    (hl : ListForall2 (Vmatch bc) vargs aargs) :
    Vmatch bc vres (evalStaticAddressing addr aargs) := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩ <;> cases addr <;>
    simp only [evalAddressing, evalStaticAddressing, reduceCtorEq,
      Option.some.injEq] at h ⊢ <;>
    subst h
  · exact symbol_address_sound _ _ hge
  · exact CC.ValueAOp.addrstack_sound hsp _
  · exact offset_ptr_sound _ h1

/-- Repeatedly apply the soundness lemmas of the abstract operators. -/
macro "va_auto_riscv" : tactic => `(tactic| repeat' first
  | assumption
  | exact Vmatch.i _ | exact Vmatch.l _ | exact Vmatch.f _ | exact Vmatch.s _
  | apply add_sound | apply sub_sound | apply neg_sound | apply mul_sound
  | apply mulhs_sound | apply mulhu_sound
  | apply divs_sound | apply divu_sound | apply mods_sound | apply modu_sound
  | apply and_sound | apply or_sound | apply xor_sound
  | apply shl_sound | apply shr_sound | apply shru_sound | apply shrx_sound
  | apply longofwords_sound | apply loword_sound | apply hiword_sound
  | apply longofint_sound | apply longofintu_sound
  | apply addl_sound | apply subl_sound | apply negl_sound | apply mull_sound
  | apply mullhs_sound | apply mullhu_sound | apply divls_sound | apply divlu_sound
  | apply modls_sound | apply modlu_sound
  | apply andl_sound | apply orl_sound | apply xorl_sound
  | apply shll_sound | apply shrl_sound | apply shrlu_sound | apply shrxl_sound
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

/-- `ValueAOp.eval_static_operation_sound` (RISC-V) -/
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
    have e2 : evalStaticOperation o (.Ocmp c) aargs =
        ofOptbool (evalStaticCondition o c aargs) := by
      rcases aargs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h; rw [e2]
    exact of_optbool_sound (eval_static_condition_sound o c m hl)
  case Osel c ty =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, hl⟩⟩
    · cases h
    · cases h
    · cases h
      exact select_sound _ ty (eval_static_condition_sound o c m hl) h1 h2
  case Ocast8signed =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩ <;>
      unfold evalOperation at h <;> dsimp only at h <;> unfold evalStaticOperation <;>
      dsimp only <;> cases h
    exact sign_ext_sound 8 h1
  case Ocast16signed =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩ <;>
      unfold evalOperation at h <;> dsimp only at h <;> unfold evalStaticOperation <;>
      dsimp only <;> cases h
    exact sign_ext_sound 16 h1
  all_goals
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩ <;>
      unfold evalOperation at h <;> dsimp only at h <;> unfold evalStaticOperation <;>
      dsimp only
  all_goals first
    | (cases h; done)
    | (cases h
       first
        | exact symbol_address_sound _ _ hge
        | exact CC.ValueAOp.addrstack_sound hsp _
        | (split <;> constructor)
        | (va_auto_riscv; done))
    | (va_auto_riscv; done)

end SOUNDNESS

end ValueAOp
end RiscV
end CC
