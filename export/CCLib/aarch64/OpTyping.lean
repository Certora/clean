/-
  Weak type soundness of the aarch64 operators — the `SOUNDNESS` section of
  `aarch64/Op.v` (`type_of_addressing_sound`, `type_of_operation_sound`),
  plus `is_move_operation_correct`: a defined result of `eval_operation`
  has the type predicted by `type_of_operation`.
-/
import CCLib.aarch64.Op
import CCLib.backend.CminortypingSubject

namespace CC
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

/-- `Op.is_move_operation_correct` -/
theorem isMoveOperation_correct {A : Type} {op : Operation} {args : List A} {a : A}
    (h : isMoveOperation op args = some a) : op = .Omove ∧ args = [a] := by
  cases op <;> rcases args with _ | ⟨x, _ | ⟨y, l⟩⟩ <;> simp [isMoveOperation] at h ⊢
  exact h

private theorem ty_shift (s : Shift) (v : Val) (a : Amount32) :
    Val.HasType (evalShift s v a) .Tint := by
  cases s <;> cases v <;> simp only [evalShift, Val.shl, Val.shru, Val.shr, Val.ror] <;>
    (try split) <;> rfl

private theorem ty_shiftl (s : Shift) (v : Val) (a : Amount64) :
    Val.HasType (evalShiftl s v a) .Tlong := by
  cases s <;> cases v <;> simp only [evalShiftl, Val.shll, Val.shrlu, Val.shrl, Val.rorl] <;>
    (try split) <;> rfl

private theorem ty_extend (x : Extension) (v : Val) (a : Amount64) :
    Val.HasType (evalExtend x v a) .Tlong := by
  cases x <;> cases v <;> simp only [evalExtend, Val.shll, Val.longofint, Val.longofintu] <;>
    (try split) <;> rfl


/-! ### Result types of the value operators -/

private theorem ty_neg (a : Val) : Val.HasType (Val.neg a) .Tint := by
  cases a <;> simp only [Val.neg] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_notint (a : Val) : Val.HasType (Val.notint a) .Tint := by
  cases a <;> simp only [Val.notint] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_loword (a : Val) : Val.HasType (Val.loword a) .Tint := by
  cases a <;> simp only [Val.loword] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_hiword (a : Val) : Val.HasType (Val.hiword a) .Tint := by
  cases a <;> simp only [Val.hiword] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_negl (a : Val) : Val.HasType (Val.negl a) .Tlong := by
  cases a <;> simp only [Val.negl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_notl (a : Val) : Val.HasType (Val.notl a) .Tlong := by
  cases a <;> simp only [Val.notl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_negf (a : Val) : Val.HasType (Val.negf a) .Tfloat := by
  cases a <;> simp only [Val.negf] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_absf (a : Val) : Val.HasType (Val.absf a) .Tfloat := by
  cases a <;> simp only [Val.absf] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_negfs (a : Val) : Val.HasType (Val.negfs a) .Tsingle := by
  cases a <;> simp only [Val.negfs] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_absfs (a : Val) : Val.HasType (Val.absfs a) .Tsingle := by
  cases a <;> simp only [Val.absfs] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_singleoffloat (a : Val) : Val.HasType (Val.singleoffloat a) .Tsingle := by
  cases a <;> simp only [Val.singleoffloat] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_floatofsingle (a : Val) : Val.HasType (Val.floatofsingle a) .Tfloat := by
  cases a <;> simp only [Val.floatofsingle] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_longofint (a : Val) : Val.HasType (Val.longofint a) .Tlong := by
  cases a <;> simp only [Val.longofint] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_longofintu (a : Val) : Val.HasType (Val.longofintu a) .Tlong := by
  cases a <;> simp only [Val.longofintu] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_zeroExt (k : Nat) (a : Val) : Val.HasType (Val.zeroExt k a) .Tint := by
  cases a <;> simp only [Val.zeroExt] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_signExt (k : Nat) (a : Val) : Val.HasType (Val.signExt k a) .Tint := by
  cases a <;> simp only [Val.signExt] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_zero_ext_l (k : Nat) (a : Val) : Val.HasType (Val.zero_ext_l k a) .Tlong := by
  cases a <;> simp only [Val.zero_ext_l] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_sign_ext_l (k : Nat) (a : Val) : Val.HasType (Val.sign_ext_l k a) .Tlong := by
  cases a <;> simp only [Val.sign_ext_l] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_add (a b : Val) : Val.HasType (Val.add a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.add] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_sub (a b : Val) : Val.HasType (Val.sub a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.sub] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_mul (a b : Val) : Val.HasType (Val.mul a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.mul] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_and (a b : Val) : Val.HasType (Val.and a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.and] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_or (a b : Val) : Val.HasType (Val.or a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.or] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_xor (a b : Val) : Val.HasType (Val.xor a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.xor] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_shl (a b : Val) : Val.HasType (Val.shl a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.shl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_shr (a b : Val) : Val.HasType (Val.shr a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.shr] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_shru (a b : Val) : Val.HasType (Val.shru a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.shru] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_ror (a b : Val) : Val.HasType (Val.ror a b) .Tint := by
  cases a <;> cases b <;> simp only [Val.ror] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_longofwords (a b : Val) : Val.HasType (Val.longofwords a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.longofwords] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_addl (a b : Val) : Val.HasType (Val.addl a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.addl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_subl (a b : Val) : Val.HasType (Val.subl a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.subl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_mull (a b : Val) : Val.HasType (Val.mull a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.mull] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_mullhs (a b : Val) : Val.HasType (Val.mullhs a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.mullhs] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_mullhu (a b : Val) : Val.HasType (Val.mullhu a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.mullhu] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_andl (a b : Val) : Val.HasType (Val.andl a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.andl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_orl (a b : Val) : Val.HasType (Val.orl a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.orl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_xorl (a b : Val) : Val.HasType (Val.xorl a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.xorl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_shll (a b : Val) : Val.HasType (Val.shll a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.shll] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_shrl (a b : Val) : Val.HasType (Val.shrl a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.shrl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_shrlu (a b : Val) : Val.HasType (Val.shrlu a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.shrlu] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_rorl (a b : Val) : Val.HasType (Val.rorl a b) .Tlong := by
  cases a <;> cases b <;> simp only [Val.rorl] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_addf (a b : Val) : Val.HasType (Val.addf a b) .Tfloat := by
  cases a <;> cases b <;> simp only [Val.addf] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_subf (a b : Val) : Val.HasType (Val.subf a b) .Tfloat := by
  cases a <;> cases b <;> simp only [Val.subf] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_mulf (a b : Val) : Val.HasType (Val.mulf a b) .Tfloat := by
  cases a <;> cases b <;> simp only [Val.mulf] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_divf (a b : Val) : Val.HasType (Val.divf a b) .Tfloat := by
  cases a <;> cases b <;> simp only [Val.divf] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_addfs (a b : Val) : Val.HasType (Val.addfs a b) .Tsingle := by
  cases a <;> cases b <;> simp only [Val.addfs] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_subfs (a b : Val) : Val.HasType (Val.subfs a b) .Tsingle := by
  cases a <;> cases b <;> simp only [Val.subfs] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_mulfs (a b : Val) : Val.HasType (Val.mulfs a b) .Tsingle := by
  cases a <;> cases b <;> simp only [Val.mulfs] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_divfs (a b : Val) : Val.HasType (Val.divfs a b) .Tsingle := by
  cases a <;> cases b <;> simp only [Val.divfs] <;>
  first | rfl | (simp only [Val.HasType, Val.hasType, Archi.ptr64]; done) | (repeat' split) <;> first | rfl | simp [Val.HasType, Val.hasType, Archi.ptr64] | skip

private theorem ty_divs {a b v : Val} (h : Val.divs a b = some v) : Val.HasType v .Tint := by
  cases a <;> cases b <;> simp only [Val.divs, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_divu {a b v : Val} (h : Val.divu a b = some v) : Val.HasType v .Tint := by
  cases a <;> cases b <;> simp only [Val.divu, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_divls {a b v : Val} (h : Val.divls a b = some v) : Val.HasType v .Tlong := by
  cases a <;> cases b <;> simp only [Val.divls, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_divlu {a b v : Val} (h : Val.divlu a b = some v) : Val.HasType v .Tlong := by
  cases a <;> cases b <;> simp only [Val.divlu, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_shrx {a b v : Val} (h : Val.shrx a b = some v) : Val.HasType v .Tint := by
  cases a <;> cases b <;> simp only [Val.shrx, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_shrxl {a b v : Val} (h : Val.shrxl a b = some v) : Val.HasType v .Tlong := by
  cases a <;> cases b <;> simp only [Val.shrxl, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_intoffloat {a v : Val} (h : Val.intoffloat a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intoffloat, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_intuoffloat {a v : Val} (h : Val.intuoffloat a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intuoffloat, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_floatofint {a v : Val} (h : Val.floatofint a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatofint, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_floatofintu {a v : Val} (h : Val.floatofintu a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatofintu, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_intofsingle {a v : Val} (h : Val.intofsingle a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intofsingle, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_intuofsingle {a v : Val} (h : Val.intuofsingle a = some v) : Val.HasType v .Tint := by
  cases a <;> simp only [Val.intuofsingle, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_singleofint {a v : Val} (h : Val.singleofint a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleofint, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_singleofintu {a v : Val} (h : Val.singleofintu a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleofintu, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_longoffloat {a v : Val} (h : Val.longoffloat a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longoffloat, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_longuoffloat {a v : Val} (h : Val.longuoffloat a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longuoffloat, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_floatoflong {a v : Val} (h : Val.floatoflong a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatoflong, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_floatoflongu {a v : Val} (h : Val.floatoflongu a = some v) : Val.HasType v .Tfloat := by
  cases a <;> simp only [Val.floatoflongu, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_longofsingle {a v : Val} (h : Val.longofsingle a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longofsingle, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_longuofsingle {a v : Val} (h : Val.longuofsingle a = some v) : Val.HasType v .Tlong := by
  cases a <;> simp only [Val.longuofsingle, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_singleoflong {a v : Val} (h : Val.singleoflong a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleoflong, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

private theorem ty_singleoflongu {a v : Val} (h : Val.singleoflongu a = some v) : Val.HasType v .Tsingle := by
  cases a <;> simp only [Val.singleoflongu, reduceCtorEq] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> (try simp at h) <;>
    (try obtain ⟨_, _, rfl⟩ := h) <;> (try obtain ⟨_, rfl⟩ := h) <;> rfl

/-- `Op.type_of_addressing_sound` -/
theorem type_of_addressing_sound {F V : Type} (ge : Genv F V) (sp : Val) (addr : Addressing)
    (vl : List Val) (v : Val) (h : evalAddressing ge sp addr vl = some v) :
    Val.HasType v Tptr := by
  cases addr <;> rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;>
    simp only [evalAddressing, Option.some.injEq, reduceCtorEq] at h <;> subst h
  case Aglobal.nil => exact hasType_symbolAddress ge _ _
  case Ainstack.nil => exact hasType_offsetPtr sp _
  all_goals exact ty_addl _ _

set_option maxHeartbeats 1000000 in
/-- `Op.type_of_operation_sound` -/
theorem type_of_operation_sound {F V : Type} (ge : Genv F V) (sp : Val) (op : Operation)
    (vl : List Val) (m : Mem) (v : Val) (hop : op ≠ .Omove)
    (h : evalOperation ge sp op vl m = some v) :
    Val.HasType v (typeOfOperation op).2 := by
  cases op
  case Omove => exact absurd rfl hop
  case Ocmp c =>
    have e : evalOperation ge sp (.Ocmp c) vl m =
        some (Val.ofOptbool (evalCondition c vl m)) := by
      rcases vl with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [e] at h; cases h; exact Cminortyping.hasType_ofOptbool _
  case Osel c ty =>
    rcases vl with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> try cases h
    exact hasType_select _ _ _ _
  case Oaddrsymbol id ofs =>
    rcases vl with _ | ⟨_, _⟩ <;> cases h; exact hasType_symbolAddress ge _ _
  case Oaddrstack ofs =>
    rcases vl with _ | ⟨_, _⟩ <;> cases h; exact hasType_offsetPtr sp _
  all_goals
    rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _⟩⟩⟩⟩ <;> (try cases h) <;>
    first
      | rfl
      | exact ty_divs h | exact ty_divu h | exact ty_divls h | exact ty_divlu h
      | exact ty_shrx h | exact ty_shrxl h
      | exact ty_intoffloat h | exact ty_intuoffloat h | exact ty_floatofint h
      | exact ty_floatofintu h | exact ty_intofsingle h | exact ty_intuofsingle h
      | exact ty_singleofint h | exact ty_singleofintu h | exact ty_longoffloat h
      | exact ty_longuoffloat h | exact ty_floatoflong h | exact ty_floatoflongu h
      | exact ty_longofsingle h | exact ty_longuofsingle h | exact ty_singleoflong h
      | exact ty_singleoflongu h
      | exact ty_shift _ _ _ | exact ty_shiftl _ _ _ | exact ty_extend _ _ _
      | exact ty_neg _ | exact ty_notint _ | exact ty_loword _ | exact ty_hiword _
      | exact ty_negl _ | exact ty_notl _ | exact ty_negf _ | exact ty_absf _
      | exact ty_negfs _ | exact ty_absfs _ | exact ty_singleoffloat _
      | exact ty_floatofsingle _
      | exact ty_zeroExt _ _ | exact ty_signExt _ _ | exact ty_zero_ext_l _ _
      | exact ty_sign_ext_l _ _
      | exact ty_add _ _ | exact ty_sub _ _ | exact ty_mul _ _ | exact ty_and _ _
      | exact ty_or _ _ | exact ty_xor _ _ | exact ty_shl _ _ | exact ty_shr _ _
      | exact ty_shru _ _ | exact ty_longofwords _ _ | exact ty_addl _ _
      | exact ty_subl _ _ | exact ty_mull _ _ | exact ty_mullhs _ _ | exact ty_mullhu _ _
      | exact ty_andl _ _ | exact ty_orl _ _ | exact ty_xorl _ _ | exact ty_shll _ _
      | exact ty_shrl _ _ | exact ty_shrlu _ _ | exact ty_addf _ _ | exact ty_subf _ _
      | exact ty_mulf _ _ | exact ty_divf _ _ | exact ty_addfs _ _ | exact ty_subfs _ _
      | exact ty_mulfs _ _ | exact ty_divfs _ _

end Op
end CC
