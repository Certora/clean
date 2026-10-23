/-
  The remaining `lessdef` / `inject` lemmas of `common/Values.v`:
  `lessdef_list_inv`, `cmpu_bool_lessdef`, `cmplu_bool_lessdef`,
  `select_lessdef`, `has_argtype_lessdef`, `sub_inject`,
  `offset_ptr_inject`, `cmpu_bool_inject`, `select_inject`,
  `has_argtype_inject`, `val_inject_lessdef`, `val_inject_id`, …

  The pointer-validity hypotheses of Rocq's `Section VAL_INJ_OPS` are the
  structure `Cop.PtrInjHyps` (already used for `cmplu_bool_inject`).
-/
import CCLib.common.ValuesTheory

namespace CC
namespace Val

open Integers (Ptrofs)

/-! ## `lessdef` -/

/-- `Val.lessdef_same` -/
theorem lessdef_same {v1 v2 : Val} (h : v1 = v2) : Lessdef v1 v2 := h ▸ .refl v1

/-- `Val.lessdef_list_inv` -/
theorem lessdef_list_inv {vl1 vl2 : List Val} (h : LessdefList vl1 vl2) :
    vl1 = vl2 ∨ Val.Vundef ∈ vl1 := by
  induction h with
  | nil => left; rfl
  | cons hv _ ih =>
    cases hv with
    | refl =>
      rcases ih with rfl | hin
      · left; rfl
      · right; exact List.mem_cons_of_mem _ hin
    | undef => right; exact List.mem_cons_self

/-- `Val.lessdef_list_trans` -/
theorem lessdef_list_trans {vl1 vl2 vl3 : List Val} (h1 : LessdefList vl1 vl2)
    (h2 : LessdefList vl2 vl3) : LessdefList vl1 vl3 := by
  induction h1 generalizing vl3 with
  | nil => exact h2
  | cons hv _ ih =>
    cases h2 with
    | cons hv' hl' => exact .cons (lessdef_trans hv hv') (ih hl')

/-- `Val.norm_bool_is_lessdef` -/
theorem norm_bool_is_lessdef (v : Val) : Lessdef (normBool v) v := by
  unfold normBool
  split
  · exact .refl v
  · exact .undef v

/-- `Val.norm_bool_lessdef` -/
theorem norm_bool_lessdef {v1 v2 : Val} (h : Lessdef v1 v2) : Lessdef (normBool v1) (normBool v2) := by
  cases h with
  | refl => exact .refl _
  | undef => exact .undef _

/-- `Val.singleoffloat_lessdef` -/
theorem singleoffloat_lessdef {v1 v2 : Val} (h : Lessdef v1 v2) :
    Lessdef (singleoffloat v1) (singleoffloat v2) := by
  cases h with
  | refl => exact .refl _
  | undef => exact .undef _

/-- `Val.cmpu_bool_lessdef` -/
theorem cmpu_bool_lessdef {vp vp' : Block → Z → Bool} {c : Comparison} {v1 v1' v2 v2' : Val}
    {b : Bool} (_hv : ∀ b ofs, vp b ofs = true → vp' b ofs = true) (h1 : Lessdef v1 v1')
    (h2 : Lessdef v2 v2') (h : cmpu_bool vp c v1 v2 = some b) : cmpu_bool vp' c v1' v2' = some b := by
  cases h1 <;> cases h2 <;> (try simp [cmpu_bool] at h)
  cases v1 <;> cases v2 <;> simp_all [cmpu_bool]

/-- Monotone validity predicates satisfy the injection hypotheses for the
    identity injection. -/
theorem ptrInjHyps_inject_id {vp vp' : Block → Z → Bool}
    (hv : ∀ b ofs, vp b ofs = true → vp' b ofs = true) : Cop.PtrInjHyps inject_id vp vp' where
  valid_pointer_inj b1 ofs b2 delta hf h := by
    simp only [inject_id, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rw [Ptrofs.repr_zero, Ptrofs.add_zero]; exact hv _ _ h
  weak_valid_pointer_inj b1 ofs b2 delta hf h := by
    simp only [inject_id, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rw [Ptrofs.repr_zero, Ptrofs.add_zero]
    simp only [weakValidPtr, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hv _ _ h)
    · exact Or.inr (hv _ _ h)
  weak_valid_pointer_no_overflow b1 ofs b2 delta hf _ := by
    simp only [inject_id, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rw [Ptrofs.repr_zero, Ptrofs.unsigned_zero]
    have := Ptrofs.unsigned_range_2 ofs
    constructor <;> zomega
  valid_different_pointers_inj b1 ofs1 b2 ofs2 b1' delta1 b2' delta2 hne _ _ hf1 hf2 := by
    simp only [inject_id, Option.some.injEq, Prod.mk.injEq] at hf1 hf2
    obtain ⟨rfl, rfl⟩ := hf1
    obtain ⟨rfl, rfl⟩ := hf2
    exact Or.inl hne

/-- `Val.cmplu_bool_lessdef` -/
theorem cmplu_bool_lessdef {vp vp' : Block → Z → Bool} {c : Comparison} {v1 v1' v2 v2' : Val}
    {b : Bool} (hv : ∀ b ofs, vp b ofs = true → vp' b ofs = true) (h1 : Lessdef v1 v1')
    (h2 : Lessdef v2 v2') (h : cmplu_bool vp c v1 v2 = some b) :
    cmplu_bool vp' c v1' v2' = some b :=
  Cop.cmplu_bool_inject (ptrInjHyps_inject_id hv) (lessdef_inject_id.mp h1)
    (lessdef_inject_id.mp h2) h

/-- `Val.of_optbool_lessdef` -/
theorem of_optbool_lessdef {ob ob' : Option Bool} (h : ∀ b, ob = some b → ob' = some b) :
    Lessdef (ofOptbool ob) (ofOptbool ob') := by
  cases ob with
  | none => exact .undef _
  | some b => rw [h b rfl]; exact .refl _

/-- `Val.longofwords_lessdef` -/
theorem longofwords_lessdef {v1 v2 v1' v2' : Val} (h1 : Lessdef v1 v1') (h2 : Lessdef v2 v2') :
    Lessdef (longofwords v1 v2) (longofwords v1' v2') := by
  cases h1 with
  | refl => cases h2 with
    | refl => exact .refl _
    | undef => cases v1 <;> exact .undef _
  | undef => exact .undef _

/-- `Val.loword_lessdef` -/
theorem loword_lessdef {v v' : Val} (h : Lessdef v v') : Lessdef (loword v) (loword v') := by
  cases h with
  | refl => exact .refl _
  | undef => exact .undef _

/-- `Val.hiword_lessdef` -/
theorem hiword_lessdef {v v' : Val} (h : Lessdef v v') : Lessdef (hiword v) (hiword v') := by
  cases h with
  | refl => exact .refl _
  | undef => exact .undef _

/-- `Val.offset_ptr_zero` -/
theorem offset_ptr_zero (v : Val) : Lessdef (offsetPtr v Ptrofs.zero) v := by
  cases v with
  | Vptr b ofs => simp only [offsetPtr, Ptrofs.add_zero]; exact .refl _
  | _ => exact .undef _

/-- `Val.offset_ptr_assoc` -/
theorem offset_ptr_assoc (v : Val) (d1 d2 : Ptrofs) :
    offsetPtr (offsetPtr v d1) d2 = offsetPtr v (Ptrofs.add d1 d2) := by
  cases v <;> simp [offsetPtr, Ptrofs.add_assoc]

/-- `Val.lessdef_normalize` -/
theorem lessdef_normalize (v : Val) (ty : ATyp) : Lessdef (normalize v ty) v := by
  cases v <;> cases ty <;> simp only [normalize, Archi.ptr64, if_true] <;>
    first | exact .refl _ | exact .undef _

/-- `Val.normalize_lessdef` -/
theorem normalize_lessdef {v v' : Val} (ty : ATyp) (h : Lessdef v v') :
    Lessdef (normalize v ty) (normalize v' ty) := by
  cases h with
  | refl => exact .refl _
  | undef => exact .undef _

/-- `Val.select_lessdef` -/
theorem select_lessdef {ob ob' : Option Bool} {v1 v1' v2 v2' : Val} (ty : ATyp)
    (hob : ob = none ∨ ob = ob') (h1 : Lessdef v1 v1') (h2 : Lessdef v2 v2') :
    Lessdef (select ob v1 v2 ty) (select ob' v1' v2' ty) := by
  rcases hob with rfl | rfl
  · exact .undef _
  · cases ob with
    | none => exact .undef _
    | some b => cases b <;> exact normalize_lessdef ty ‹_›

/-- `Val.has_argtype_lessdef` -/
theorem has_argtype_lessdef {v v' : Val} {r : XType} (h : HasArgtype v r) (hl : Lessdef v v') :
    HasArgtype v' r := by
  cases hl with
  | refl => exact h
  | undef => cases r <;> cases v' <;> simp_all [HasArgtype]

/-- `Val.has_argtype_list_lessdef` -/
theorem has_argtype_list_lessdef {vl vl' : List Val} {rl : List XType} (h : HasArgtypeList vl rl)
    (hl : LessdefList vl vl') : HasArgtypeList vl' rl := by
  induction hl generalizing rl with
  | nil => exact h
  | cons hv _ ih =>
    cases rl with
    | nil => exact absurd h (by simp [HasArgtypeList])
    | cons r rs => exact ⟨has_argtype_lessdef h.1 hv, ih h.2⟩

/-! ## `inject` -/

section Inject

variable {f : Meminj}

/-- `Val.inject_ptrofs` -/
theorem inject_ptrofs (mi : Meminj) (i : Ptrofs) : Inject mi (Vptrofs i) (Vptrofs i) := by
  simp only [Vptrofs, Archi.ptr64, if_true]; exact .long _

/-- `Val.sub_inject` -/
theorem sub_inject {v1 v1' v2 v2' : Val} (h1 : Inject f v1 v1') (h2 : Inject f v2 v2') :
    Inject f (sub v1 v2) (sub v1' v2') := by
  cases h1 <;> cases h2 <;> simp [sub, Archi.ptr64] <;> first | exact .int _ | exact .undef _

/-- `Val.offset_ptr_inject` -/
theorem offset_ptr_inject {v v' : Val} (ofs : Ptrofs) (h : Inject f v v') :
    Inject f (offsetPtr v ofs) (offsetPtr v' ofs) := by
  cases h with
  | ptr delta hf ho =>
    simp only [offsetPtr]
    refine .ptr delta hf ?_
    rw [ho, Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut ofs]
  | undef => exact .undef _
  | _ => exact .undef _

/-- `Val.cmpu_bool_inject` -/
theorem cmpu_bool_inject {vp1 vp2 : Block → Z → Bool} (_H : Cop.PtrInjHyps f vp1 vp2)
    {c : Comparison} {v1 v2 v1' v2' : Val} {b : Bool} (h1 : Inject f v1 v1') (h2 : Inject f v2 v2')
    (h : cmpu_bool vp1 c v1 v2 = some b) : cmpu_bool vp2 c v1' v2' = some b := by
  cases h1 <;> cases h2 <;> simp_all [cmpu_bool, Archi.ptr64]

/-- `Val.longofwords_inject` -/
theorem longofwords_inject {v1 v2 v1' v2' : Val} (h1 : Inject f v1 v1') (h2 : Inject f v2 v2') :
    Inject f (longofwords v1 v2) (longofwords v1' v2') := by
  cases h1 <;> cases h2 <;> simp only [longofwords] <;> first | exact .long _ | exact .undef _

/-- `Val.loword_inject` -/
theorem loword_inject {v v' : Val} (h : Inject f v v') : Inject f (loword v) (loword v') := by
  cases h <;> simp only [loword] <;> first | exact .int _ | exact .undef _

/-- `Val.hiword_inject` -/
theorem hiword_inject {v v' : Val} (h : Inject f v v') : Inject f (hiword v) (hiword v') := by
  cases h <;> simp only [hiword] <;> first | exact .int _ | exact .undef _

/-- `Val.select_inject` -/
theorem select_inject {ob ob' : Option Bool} {v1 v1' v2 v2' : Val} (ty : ATyp)
    (hob : ob = none ∨ ob = ob') (h1 : Inject f v1 v1') (h2 : Inject f v2 v2') :
    Inject f (select ob v1 v2 ty) (select ob' v1' v2' ty) := by
  rcases hob with rfl | rfl
  · exact .undef _
  · cases ob with
    | none => exact .undef _
    | some b => cases b <;> exact Builtins.normalize_inject ‹_› ty

/-- `Val.has_argtype_inject` -/
theorem has_argtype_inject {v v' : Val} {r : XType} (h : HasArgtype v r) (hi : Inject f v v') :
    HasArgtype v' r := by
  cases hi with
  | undef => cases r <;> cases v' <;> simp_all [HasArgtype]
  | ptr => cases r <;> simp_all [HasArgtype]
  | _ => exact h

/-- `Val.has_argtype_list_inject` -/
theorem has_argtype_list_inject {vl vl' : List Val} {rl : List XType} (h : HasArgtypeList vl rl)
    (hi : InjectList f vl vl') : HasArgtypeList vl' rl := by
  induction hi generalizing rl with
  | nil => exact h
  | cons hv _ ih =>
    cases rl with
    | nil => exact absurd h (by simp [HasArgtypeList])
    | cons r rs => exact ⟨has_argtype_inject h.1 hv, ih h.2⟩

end Inject

/-- `Val.val_inject_lessdef` -/
theorem val_inject_lessdef {v1 v2 : Val} :
    Lessdef v1 v2 ↔ Inject (fun b => some (b, 0)) v1 v2 := lessdef_inject_id

/-- `Val.val_inject_list_lessdef` -/
theorem val_inject_list_lessdef {vl1 vl2 : List Val} :
    LessdefList vl1 vl2 ↔ InjectList (fun b => some (b, 0)) vl1 vl2 := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hv _ ih => exact .cons (lessdef_inject_id.mp hv) ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons hv _ ih => exact .cons (lessdef_inject_id.mpr hv) ih

/-- `Val.val_inject_id` -/
theorem val_inject_id {v1 v2 : Val} : Inject inject_id v1 v2 ↔ Lessdef v1 v2 :=
  lessdef_inject_id.symm

end Val
end CC
