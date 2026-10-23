/-
  Weak type soundness of the x86 operators — the `SOUNDNESS` section of
  `x86/Op.v` (`type_of_addressing32_sound`, `type_of_addressing64_sound`,
  `type_of_operation_sound`): a defined result of `eval_operation` has the
  type predicted by `type_of_operation`.
-/
import CCLib.x86.Op
import CCLib.backend.CminortypingSubject

namespace CC
namespace X86
namespace Op

open Cminortyping in
private theorem hasType_select (c : Option Bool) (v1 v2 : Val) (ty : ATyp) :
    Val.HasType (Val.select c v1 v2 ty) ty := by
  cases c with
  | none => exact Cminortyping.hasType_undef ty
  | some b => exact Val.normalize_type _ _

private theorem hasType_symbolAddress {F V : Type} (ge : Genv F V) (id : Ident)
    (ofs : Integers.Ptrofs) : Val.HasType (Genv.symbolAddress ge id ofs) Tptr := by
  unfold Genv.symbolAddress
  split
  · exact Val.Vptr_has_type _ _
  · exact Cminortyping.hasType_undef _

private theorem hasType_offsetPtr (sp : Val) (ofs : Integers.Ptrofs) :
    Val.HasType (Val.offsetPtr sp ofs) Tptr := by
  unfold Val.offsetPtr
  split
  · exact Val.Vptr_has_type _ _
  · exact Cminortyping.hasType_undef _

/-- `Op.type_of_addressing32_sound` -/
theorem type_of_addressing32_sound {F V : Type} (ge : Genv F V) (sp : Val) (addr : Addressing)
    (vl : List Val) (v : Val) (h : evalAddressing32 ge sp addr vl = some v) :
    Val.HasType v .Tint := by
  cases addr <;> rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;>
    simp only [evalAddressing32, Archi.ptr64, if_true, Option.some.injEq,
      reduceCtorEq] at h <;> subst h <;>
    (try cases a) <;> (try cases b) <;>
    simp [Val.HasType, Val.hasType, Val.add, Val.mul, Archi.ptr64]

/-- `Op.type_of_addressing64_sound` -/
theorem type_of_addressing64_sound {F V : Type} (ge : Genv F V) (sp : Val) (addr : Addressing)
    (vl : List Val) (v : Val) (h : evalAddressing64 ge sp addr vl = some v) :
    Val.HasType v .Tlong := by
  cases addr <;> rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;>
    simp only [evalAddressing64, Archi.ptr64, if_true, Option.some.injEq,
      reduceCtorEq] at h <;> (try subst h)
  case Aglobal.nil => exact hasType_symbolAddress ge _ _
  case Ainstack.nil => exact hasType_offsetPtr sp _
  all_goals
    (cases a <;> (try cases b) <;>
      simp [Val.HasType, Val.hasType, Val.addl, Val.mull, Archi.ptr64])

private theorem ty_divs {a b v : Val} (h : Val.divs a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.divs, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_divu {a b v : Val} (h : Val.divu a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.divu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_mods {a b v : Val} (h : Val.mods a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.mods, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_modu {a b v : Val} (h : Val.modu a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.modu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_divls {a b v : Val} (h : Val.divls a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.divls, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_divlu {a b v : Val} (h : Val.divlu a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.divlu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_modls {a b v : Val} (h : Val.modls a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.modls, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_modlu {a b v : Val} (h : Val.modlu a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.modlu, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_shrx {a b v : Val} (h : Val.shrx a b = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.shrx, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_shrxl {a b v : Val} (h : Val.shrxl a b = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.shrxl, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_intoffloat {a v : Val} (h : Val.intoffloat a = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.intoffloat, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_intofsingle {a v : Val} (h : Val.intofsingle a = some v) : Val.HasType v .Tint := by
  cases a <;> (try cases b) <;> simp only [Val.intofsingle, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_floatofint {a v : Val} (h : Val.floatofint a = some v) : Val.HasType v .Tfloat := by
  cases a <;> (try cases b) <;> simp only [Val.floatofint, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_floatoflong {a v : Val} (h : Val.floatoflong a = some v) : Val.HasType v .Tfloat := by
  cases a <;> (try cases b) <;> simp only [Val.floatoflong, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_singleofint {a v : Val} (h : Val.singleofint a = some v) : Val.HasType v .Tsingle := by
  cases a <;> (try cases b) <;> simp only [Val.singleofint, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_singleoflong {a v : Val} (h : Val.singleoflong a = some v) : Val.HasType v .Tsingle := by
  cases a <;> (try cases b) <;> simp only [Val.singleoflong, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_longoffloat {a v : Val} (h : Val.longoffloat a = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.longoffloat, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl
private theorem ty_longofsingle {a v : Val} (h : Val.longofsingle a = some v) : Val.HasType v .Tlong := by
  cases a <;> (try cases b) <;> simp only [Val.longofsingle, reduceCtorEq] at h <;> (try split at h) <;>
    (try cases h) <;> (try simp at h) <;> (try obtain ⟨_, _, rfl⟩ := h) <;> rfl

set_option maxHeartbeats 1000000 in
/-- `Op.type_of_operation_sound` -/
theorem type_of_operation_sound {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    (vl : List Val) (m : Mem) (v : Val) (hop : op ≠ .Omove)
    (h : evalOperation ge sp op vl m = some v) :
    Val.HasType v (typeOfOperation op).2 := by
  cases op
  case Omove => exact absurd rfl hop
  case Olea a => exact type_of_addressing32_sound ge sp a vl v h
  case Oleal a => exact type_of_addressing64_sound ge sp a vl v h
  case Ocmp c =>
    have e : evalOperation ge sp (.Ocmp c) vl m =
        some (Val.ofOptbool (evalCondition c vl m)) := by
      rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h; exact Cminortyping.hasType_ofOptbool _
  case Osel c ty =>
    rcases vl with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> try cases h
    exact hasType_select _ _ _ _
  case Oindirectsymbol id =>
    rcases vl with _ | ⟨_, _⟩ <;> cases h; exact hasType_symbolAddress ge _ _
  case Oshldimm n =>
    rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> cases h
    generalize Val.shl a _ = x; generalize Val.shru b _ = y
    cases x <;> cases y <;> rfl
  all_goals
    rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> (try cases h) <;>
    first
      | exact ty_divs h
      | exact ty_divu h
      | exact ty_mods h
      | exact ty_modu h
      | exact ty_divls h
      | exact ty_divlu h
      | exact ty_modls h
      | exact ty_modlu h
      | exact ty_shrx h
      | exact ty_shrxl h
      | exact ty_intoffloat h
      | exact ty_intofsingle h
      | exact ty_floatofint h
      | exact ty_floatoflong h
      | exact ty_singleofint h
      | exact ty_singleoflong h
      | exact ty_longoffloat h
      | exact ty_longofsingle h
      | ((try cases a) <;> (try cases b) <;>
         simp [typeOfOperation, Val.HasType, Val.hasType, Val.signExt, Val.zeroExt, Val.neg,
          Val.sub, Val.mul, Val.mulhs, Val.mulhu, Val.and, Val.or, Val.xor, Val.notint, Val.shl,
          Val.shr, Val.shru, Val.ror, Val.longofwords, Val.loword, Val.hiword, Val.longofint,
          Val.longofintu, Val.negl, Val.addl, Val.subl, Val.mull, Val.mullhs, Val.mullhu,
          Val.andl, Val.orl, Val.xorl, Val.notl, Val.shll, Val.shrl, Val.shrlu, Val.rorl,
          Val.negf, Val.absf, Val.addf, Val.subf, Val.mulf, Val.divf, maxf, minf, Val.negfs,
          Val.absfs, Val.addfs, Val.subfs, Val.mulfs, Val.divfs, Val.singleoffloat,
          Val.floatofsingle, Archi.ptr64] <;>
         first | rfl | (apply Cminortyping.hasType_ite <;> rfl))

end Op
end X86
end CC
