/-
  The `GENERIC_INJECTION` section of `cfrontend/Cop.v`: the C operators
  commute with memory injections.  As in CompCert, the generic lemmas are
  stated under four hypotheses about pointer validity (`CopInjHyps`), and the
  `*_inject` corollaries discharge them from a full memory injection
  (`Mem.Inject`).
-/
import CCLib.cfrontend.Cop
import CCLib.common.MemoryInjections

namespace CC
namespace Cop

open Integers (Ptrofs)

/-- The four hypotheses of `Values.COMPARISONS` / `Cop.GENERIC_INJECTION`,
for validity predicates `vp1` (source) and `vp2` (target). -/
structure PtrInjHyps (f : Val.Meminj) (vp1 vp2 : Block → Z → Bool) : Prop where
  valid_pointer_inj : ∀ b1 ofs b2 delta, f b1 = some (b2, delta) →
    vp1 b1 (Ptrofs.unsigned ofs) = true →
    vp2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true
  weak_valid_pointer_inj : ∀ b1 ofs b2 delta, f b1 = some (b2, delta) →
    Val.weakValidPtr vp1 b1 (Ptrofs.unsigned ofs) = true →
    Val.weakValidPtr vp2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true
  weak_valid_pointer_no_overflow : ∀ b1 ofs b2 delta, f b1 = some (b2, delta) →
    Val.weakValidPtr vp1 b1 (Ptrofs.unsigned ofs) = true →
    0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned
  valid_different_pointers_inj : ∀ b1 ofs1 b2 ofs2 b1' delta1 b2' delta2, b1 ≠ b2 →
    vp1 b1 (Ptrofs.unsigned ofs1) = true →
    vp1 b2 (Ptrofs.unsigned ofs2) = true →
    f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
    b1' ≠ b2' ∨ Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
      Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))

/-- The hypotheses of `Cop.GENERIC_INJECTION` for memories `m` and `m'`. -/
abbrev CopInjHyps (f : Val.Meminj) (m m' : Mem) : Prop :=
  PtrInjHyps f (Mem.validPointer m) (Mem.validPointer m')

/-- `Values.cmplu_bool_inject` -/
theorem cmplu_bool_inject {f : Val.Meminj} {vp1 vp2 : Block → Z → Bool} (H : PtrInjHyps f vp1 vp2)
    {c : Comparison} {v1 v2 v1' v2' : Val} {b : Bool} (h1 : Val.Inject f v1 v1')
    (h2 : Val.Inject f v2 v2') (h : Val.cmplu_bool vp1 c v1 v2 = some b) :
    Val.cmplu_bool vp2 c v1' v2' = some b := by
  cases h1 <;> cases h2 <;> simp only [Val.cmplu_bool, Archi.ptr64] at h ⊢ <;> try cases h
  · rfl
  · subst_vars
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
    split at h
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hc.1, H.weak_valid_pointer_inj _ _ _ _ ‹_› hc.2⟩)]
      exact h
    · cases h
  · subst_vars
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
    split at h
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hc.1, H.weak_valid_pointer_inj _ _ _ _ ‹_› hc.2⟩)]
      exact h
    · cases h
  · next b1 o1 b1' o1' d1 hf1 ho1 b2 o2 b2' o2' d2 hf2 ho2 =>
    subst ho1 ho2
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
    by_cases hb : b1 = b2
    · subst hb
      rw [hf1] at hf2; cases hf2
      rw [if_pos rfl] at h ⊢
      split at h
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        have hw1 := H.weak_valid_pointer_inj _ _ _ _ hf1 hc.1
        have hw2 := H.weak_valid_pointer_inj _ _ _ _ hf1 hc.2
        have hn1 := H.weak_valid_pointer_no_overflow _ _ _ _ hf1 hc.1
        have hn2 := H.weak_valid_pointer_no_overflow _ _ _ _ hf1 hc.2
        rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hw1, hw2⟩)]
        rw [Ptrofs.translate_cmpu c hn1.2 hn2.2]
        exact h
      · cases h
    · rw [if_neg hb] at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        have hwv : ∀ b o, vp1 b o = true → Val.weakValidPtr vp1 b o = true := by
          intro b o hv; simp [Val.weakValidPtr, hv]
        by_cases hb' : b1' = b2'
        · subst hb'
          rw [if_pos rfl]
          have hw1 := H.weak_valid_pointer_inj _ _ _ _ hf1 (hwv _ _ hc.1)
          have hw2 := H.weak_valid_pointer_inj _ _ _ _ hf2 (hwv _ _ hc.2)
          rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hw1, hw2⟩)]
          rcases H.valid_different_pointers_inj _ _ _ _ _ _ _ _ hb hc.1 hc.2 hf1 hf2 with hne | hne
          · exact absurd rfl hne
          · have hne' : Ptrofs.add o1 (Ptrofs.repr d1) ≠ Ptrofs.add o2 (Ptrofs.repr d2) :=
              fun he => hne (by rw [he])
            have hq : Ptrofs.eq (Ptrofs.add o1 (Ptrofs.repr d1)) (Ptrofs.add o2 (Ptrofs.repr d2)) =
                false := Ptrofs.eq_false hne'
            cases c <;> simp only [Val.cmpDifferentBlocks] at h <;> cases h
            · show some (Ptrofs.eq _ _) = some false
              rw [hq]
            · show some (!Ptrofs.eq _ _) = some true
              rw [hq]; rfl
        · rw [if_neg hb']
          rw [if_pos (by simp only [Bool.and_eq_true]; exact
            ⟨H.valid_pointer_inj _ _ _ _ hf1 hc.1, H.valid_pointer_inj _ _ _ _ hf2 hc.2⟩)]
          exact h
      · cases h

section Generic
variable {f : Val.Meminj} {m m' : Mem}

/-- `Cop.sem_cast_inj` -/
theorem semCast_inj (H : CopInjHyps f m m') {v1 : Val} {ty1 ty : Ty} {v tv1 : Val}
    (h : semCast v1 ty1 ty m = some v) (hi : Val.Inject f v1 tv1) :
    ∃ tv, semCast tv1 ty1 ty m' = some tv ∧ Val.Inject f v tv := by
  unfold semCast at h ⊢
  generalize classifyCast ty1 ty = c at h ⊢
  cases c <;> cases hi <;> simp [Archi.ptr64] at h ⊢ <;> (try subst_vars) <;>
    first
    | exact .int _ | exact .long _ | exact .float _ | exact .single _ | exact .undef _
    | exact .ptr _ ‹_› rfl
    | (obtain ⟨h1, rfl⟩ := h; exact ⟨_, ⟨h1, rfl⟩, .ptr _ ‹_› rfl⟩)
    | (obtain ⟨h1, rfl⟩ := h
       exact ⟨_, ⟨H.weak_valid_pointer_inj _ _ _ _ ‹_› h1, rfl⟩, .int _⟩)
    | (revert h; split <;> intro h <;> simp at h ⊢ <;> subst h <;>
       first | exact .int _ | exact .long _)

/-- `Cop.bool_val_inj` -/
theorem boolVal_inj (H : CopInjHyps f m m') {v : Val} {ty : Ty} {b : Bool} {tv : Val}
    (h : boolVal v ty m = some b) (hi : Val.Inject f v tv) : boolVal tv ty m' = some b := by
  unfold boolVal at h ⊢
  generalize classifyBool ty = c at h ⊢
  cases c <;> cases hi <;> simp [Archi.ptr64] at h ⊢ <;> (try subst_vars) <;> (try rfl) <;>
    first
    | exact h
    | (obtain ⟨h1, rfl⟩ := h; exact ⟨H.weak_valid_pointer_inj _ _ _ _ ‹_› h1, rfl⟩)

/-- `Cop.sem_unary_operation_inj` -/
theorem semUnaryOperation_inj (H : CopInjHyps f m m') {op : Unop} {v1 : Val} {ty : Ty}
    {v tv1 : Val} (h : semUnaryOperation op v1 ty m = some v) (hi : Val.Inject f v1 tv1) :
    ∃ tv, semUnaryOperation op tv1 ty m' = some tv ∧ Val.Inject f v tv := by
  cases op with
  | Onotbool =>
    simp only [semUnaryOperation, semNotbool] at h ⊢
    cases hb : boolVal v1 ty m with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      rw [boolVal_inj H hb hi]
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      subst h
      refine ⟨_, rfl, ?_⟩
      cases b <;> exact .int _
  | Onotint =>
    simp only [semUnaryOperation, semNotint] at h ⊢
    generalize classifyNotint ty = c at h ⊢
    cases c <;> cases hi <;> simp at h ⊢ <;> subst_vars <;> first | exact .int _ | exact .long _
  | Oneg =>
    simp only [semUnaryOperation, semNeg] at h ⊢
    generalize classifyNeg ty = c at h ⊢
    cases c <;> cases hi <;> simp at h ⊢ <;> subst_vars <;>
      first | exact .int _ | exact .long _ | exact .float _ | exact .single _
  | Oabsfloat =>
    simp only [semUnaryOperation, semAbsfloat] at h ⊢
    generalize classifyNeg ty = c at h ⊢
    cases c <;> cases hi <;> simp at h ⊢ <;> subst_vars <;> exact .float _

/-- `Cop.optval_self_injects` -/
def OptvalSelfInjects : Option Val → Prop
  | some (.Vptr _ _) => False
  | _ => True

theorem self_inject_of {ov : Option Val} {v : Val} (he : ov = some v) (hs : OptvalSelfInjects ov) :
    Val.Inject f v v := by
  subst he
  cases v with
  | Vptr b o => exact hs.elim
  | Vundef => exact .undef _
  | Vint i => exact .int _
  | Vlong i => exact .long _
  | Vfloat x => exact .float _
  | Vsingle x => exact .single _

/-- `Cop.sem_binarith_inject` -/
theorem semBinarith_inject (H : CopInjHyps f m m')
    {semInt : Signedness → Integers.Int → Integers.Int → Option Val}
    {semLong : Signedness → Integers.Int64 → Integers.Int64 → Option Val}
    {semFloat : Floats.Float → Floats.Float → Option Val}
    {semSingle : Floats.Float32 → Floats.Float32 → Option Val}
    {v1 : Val} {t1 : Ty} {v2 : Val} {t2 : Ty} {v v1' v2' : Val}
    (h : semBinarith semInt semLong semFloat semSingle v1 t1 v2 t2 m = some v)
    (hi1 : Val.Inject f v1 v1') (hi2 : Val.Inject f v2 v2')
    (hsi : ∀ sg n1 n2, OptvalSelfInjects (semInt sg n1 n2))
    (hsl : ∀ sg n1 n2, OptvalSelfInjects (semLong sg n1 n2))
    (hsf : ∀ n1 n2, OptvalSelfInjects (semFloat n1 n2))
    (hss : ∀ n1 n2, OptvalSelfInjects (semSingle n1 n2)) :
    ∃ v', semBinarith semInt semLong semFloat semSingle v1' t1 v2' t2 m' = some v' ∧
      Val.Inject f v v' := by
  unfold semBinarith at h ⊢
  simp only at h ⊢
  cases hc1 : semCast v1 t1 (binarithType (classifyBinarith t1 t2)) m with
  | none => rw [hc1] at h; cases h
  | some w1 =>
    rw [hc1] at h
    cases hc2 : semCast v2 t2 (binarithType (classifyBinarith t1 t2)) m with
    | none => rw [hc2] at h; cases h
    | some w2 =>
      rw [hc2] at h
      obtain ⟨w1', hc1', hw1⟩ := semCast_inj H hc1 hi1
      obtain ⟨w2', hc2', hw2⟩ := semCast_inj H hc2 hi2
      rw [hc1', hc2']
      simp only
      generalize classifyBinarith t1 t2 = c at h ⊢
      cases c <;> cases hw1 <;> cases hw2 <;> simp only at h ⊢ <;> (try cases h) <;>
        exact ⟨v, h, self_inject_of h (by
          first
          | exact hsi _ _ _
          | exact hsl _ _ _
          | exact hsf _ _
          | exact hss _ _)⟩

/-- `Cop.sem_shift_inject` -/
theorem semShift_inject
    {semInt : Signedness → Integers.Int → Integers.Int → Integers.Int}
    {semLong : Signedness → Integers.Int64 → Integers.Int64 → Integers.Int64}
    {v1 : Val} {t1 : Ty} {v2 : Val} {t2 : Ty} {v v1' v2' : Val}
    (h : semShift semInt semLong v1 t1 v2 t2 = some v)
    (hi1 : Val.Inject f v1 v1') (hi2 : Val.Inject f v2 v2') :
    ∃ v', semShift semInt semLong v1' t1 v2' t2 = some v' ∧ Val.Inject f v v' := by
  refine ⟨v, ?_, ?_⟩
  · unfold semShift at h ⊢
    generalize classifyShift t1 t2 = c at h ⊢
    cases c <;> cases hi1 <;> cases hi2 <;> simp only at h ⊢ <;> first | exact h | cases h
  · unfold semShift at h
    generalize classifyShift t1 t2 = c at h
    cases c <;> cases hi1 <;> cases hi2 <;> simp only at h <;> (try cases h) <;>
      (split at h <;> cases h) <;> first | exact .int _ | exact .long _

/-- `Cop.sem_cmp_ptr_inj` -/
theorem cmpPtr_inj (H : CopInjHyps f m m') {c : Comparison} {v1 v2 v tv1 tv2 : Val}
    (h : cmpPtr m c v1 v2 = some v) (hi1 : Val.Inject f v1 tv1) (hi2 : Val.Inject f v2 tv2) :
    ∃ tv, cmpPtr m' c tv1 tv2 = some tv ∧ Val.Inject f v tv := by
  unfold cmpPtr at h ⊢
  simp only [Archi.ptr64, if_true] at h ⊢
  cases hb : Val.cmplu_bool (Mem.validPointer m) c v1 v2 with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    rw [cmplu_bool_inject H hi1 hi2 hb]
    simp only [Option.map_some, Option.some.injEq] at h ⊢
    subst h
    refine ⟨_, rfl, ?_⟩
    cases b <;> exact .int _

theorem selfInjects_ofBool (b : Bool) : OptvalSelfInjects (some (Val.ofBool b)) := by
  cases b <;> trivial

theorem vptrofs_inject (n : Ptrofs) : Val.Inject f (Val.Vptrofs n) (Val.Vptrofs n) := by
  simp only [Val.Vptrofs, Archi.ptr64, if_true]; exact .long _

/-- `Cop.sem_cmp_inj` -/
theorem semCmp_inj (H : CopInjHyps f m m') {c : Comparison} {v1 tv1 : Val} {ty1 : Ty}
    {v2 tv2 : Val} {ty2 : Ty} {v : Val} (h : semCmp c v1 ty1 v2 ty2 m = some v)
    (hi1 : Val.Inject f v1 tv1) (hi2 : Val.Inject f v2 tv2) :
    ∃ tv, semCmp c tv1 ty1 tv2 ty2 m' = some tv ∧ Val.Inject f v tv := by
  unfold semCmp at h ⊢
  generalize classifyCmp ty1 ty2 = cc at h ⊢
  cases cc with
  | pp => exact cmpPtr_inj H h hi1 hi2
  | pi si =>
    cases hi2 <;> simp only [Archi.ptr64, if_true] at h ⊢ <;> try cases h
    exact cmpPtr_inj H h hi1 (vptrofs_inject _)
  | ip si =>
    cases hi1 <;> simp only [Archi.ptr64, if_true] at h ⊢ <;> try cases h
    exact cmpPtr_inj H h (vptrofs_inject _) hi2
  | pl =>
    cases hi2 <;> simp only [Archi.ptr64, if_true] at h ⊢ <;> try cases h
    · exact cmpPtr_inj H h hi1 (vptrofs_inject _)
    · exact cmpPtr_inj H h hi1 (.ptr _ ‹_› ‹_›)
  | lp =>
    cases hi1 <;> simp only [Archi.ptr64, if_true] at h ⊢ <;> try cases h
    · exact cmpPtr_inj H h (vptrofs_inject _) hi2
    · exact cmpPtr_inj H h (.ptr _ ‹_› ‹_›) hi2
  | default =>
    exact semBinarith_inject H h hi1 hi2 (fun _ _ _ => selfInjects_ofBool _)
      (fun _ _ _ => selfInjects_ofBool _) (fun _ _ => selfInjects_ofBool _)
      (fun _ _ => selfInjects_ofBool _)

theorem semAddPtrInt_inj {cenv : CompositeEnv} {ty : Ty} {si : Signedness} {v1 v2 tv1 tv2 v : Val}
    (hi1 : Val.Inject f v1 tv1) (hi2 : Val.Inject f v2 tv2)
    (h : semAddPtrInt cenv ty si v1 v2 = some v) :
    ∃ tv, semAddPtrInt cenv ty si tv1 tv2 = some tv ∧ Val.Inject f v tv := by
  cases hi1 <;> cases hi2 <;> simp [semAddPtrInt, Archi.ptr64] at h ⊢ <;> subst_vars
  · exact .long _
  · refine .ptr _ ‹_› ?_
    rw [Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr _)]

theorem semAddPtrLong_inj {cenv : CompositeEnv} {ty : Ty} {v1 v2 tv1 tv2 v : Val}
    (hi1 : Val.Inject f v1 tv1) (hi2 : Val.Inject f v2 tv2)
    (h : semAddPtrLong cenv ty v1 v2 = some v) :
    ∃ tv, semAddPtrLong cenv ty tv1 tv2 = some tv ∧ Val.Inject f v tv := by
  cases hi1 <;> cases hi2 <;> simp [semAddPtrLong, Archi.ptr64] at h ⊢ <;> subst_vars
  · exact .long _
  · refine .ptr _ ‹_› ?_
    rw [Ptrofs.add_assoc, Ptrofs.add_assoc, Ptrofs.add_commut (Ptrofs.repr _)]

/-- `Cop.sem_binary_operation_inj` -/
theorem semBinaryOperation_inj (H : CopInjHyps f m m') {cenv : CompositeEnv} {op : Binop}
    {v1 : Val} {ty1 : Ty} {v2 : Val} {ty2 : Ty} {v tv1 tv2 : Val}
    (h : semBinaryOperation cenv op v1 ty1 v2 ty2 m = some v)
    (hi1 : Val.Inject f v1 tv1) (hi2 : Val.Inject f v2 tv2) :
    ∃ tv, semBinaryOperation cenv op tv1 ty1 tv2 ty2 m' = some tv ∧ Val.Inject f v tv := by
  cases op with
  | Oadd =>
    simp only [semBinaryOperation, semAdd] at h ⊢
    generalize classifyAdd ty1 ty2 = c at h ⊢
    cases c with
    | pi ty si => exact semAddPtrInt_inj hi1 hi2 h
    | pl ty => exact semAddPtrLong_inj hi1 hi2 h
    | ip si ty => exact semAddPtrInt_inj hi2 hi1 h
    | lp ty => exact semAddPtrLong_inj hi2 hi1 h
    | default =>
      exact semBinarith_inject H h hi1 hi2 (fun _ _ _ => trivial) (fun _ _ _ => trivial)
        (fun _ _ => trivial) (fun _ _ => trivial)
  | Osub =>
    simp only [semBinaryOperation, semSub] at h ⊢
    generalize classifySub ty1 ty2 = c at h ⊢
    cases c with
    | pi ty si =>
      cases hi1 <;> cases hi2 <;> simp [Archi.ptr64] at h ⊢ <;> subst_vars
      · exact .long _
      · refine .ptr _ ‹_› ?_
        rw [Ptrofs.sub_add_l]
    | pl ty =>
      cases hi1 <;> cases hi2 <;> simp [Archi.ptr64] at h ⊢ <;> subst_vars
      · exact .long _
      · refine .ptr _ ‹_› ?_
        rw [Ptrofs.sub_add_l]
    | pp ty =>
      cases hi1 <;> cases hi2 <;> simp only at h ⊢ <;> try cases h
      next b1 o1 b1' o1' d1 hf1 ho1 b2 o2 b2' o2' d2 hf2 ho2 =>
        subst ho1 ho2
        by_cases hb : b1 = b2
        · subst hb
          rw [hf1] at hf2; cases hf2
          rw [if_pos rfl] at h ⊢
          rw [Ptrofs.sub_shifted]
          refine ⟨v, h, ?_⟩
          split at h
          · cases h; exact vptrofs_inject _
          · cases h
        · rw [if_neg hb] at h; cases h
    | default =>
      exact semBinarith_inject H h hi1 hi2 (fun _ _ _ => trivial) (fun _ _ _ => trivial)
        (fun _ _ => trivial) (fun _ _ => trivial)
  | Omul =>
    exact semBinarith_inject H h hi1 hi2 (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ _ => trivial) (fun _ _ => trivial)
  | Odiv =>
    refine semBinarith_inject H h hi1 hi2 ?_ ?_ (fun _ _ => trivial) (fun _ _ => trivial) <;>
      intro sg n1 n2 <;> cases sg <;> simp only <;> split <;> trivial
  | Omod =>
    refine semBinarith_inject H h hi1 hi2 ?_ ?_ (fun _ _ => trivial) (fun _ _ => trivial) <;>
      intro sg n1 n2 <;> cases sg <;> simp only <;> split <;> trivial
  | Oand =>
    exact semBinarith_inject H h hi1 hi2 (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ _ => trivial) (fun _ _ => trivial)
  | Oor =>
    exact semBinarith_inject H h hi1 hi2 (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ _ => trivial) (fun _ _ => trivial)
  | Oxor =>
    exact semBinarith_inject H h hi1 hi2 (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun _ _ => trivial) (fun _ _ => trivial)
  | Oshl => exact semShift_inject h hi1 hi2
  | Oshr =>
    simp only [semBinaryOperation, semShr] at h ⊢
    exact semShift_inject h hi1 hi2
  | Oeq => exact semCmp_inj H h hi1 hi2
  | One => exact semCmp_inj H h hi1 hi2
  | Olt => exact semCmp_inj H h hi1 hi2
  | Ogt => exact semCmp_inj H h hi1 hi2
  | Ole => exact semCmp_inj H h hi1 hi2
  | Oge => exact semCmp_inj H h hi1 hi2

end Generic

/-! ## Corollaries for memory injections -/

/-- `Memory.weak_valid_pointer_inject_no_overflow` -/
theorem _root_.CC.Mem.weakValidPointer_inject_no_overflow {f : Val.Meminj} {m1 m2 : Mem}
    (h : Mem.Inject f m1 m2) {b : Block} {ofs : Ptrofs} {b' : Block} {delta : _root_.Int}
    (hv : Mem.weakValidPointer m1 b (Ptrofs.unsigned ofs) = true) (hf : f b = some (b', delta)) :
    0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned := by
  simp only [Mem.weakValidPointer, Mem.validPointer, Bool.or_eq_true] at hv
  obtain ⟨hA, hB, hC⟩ := h.representable _ _ _ ofs hf
    (hv.imp Mem.perm_cur_max Mem.perm_cur_max)
  have hr : (0 : _root_.Int) ≤ (Ptrofs.unsigned ofs : _root_.Int) := (Ptrofs.unsigned_range_2 ofs).1
  have hA' : (0 : _root_.Int) ≤ delta := hA
  rw [Ptrofs.unsigned_repr (z := delta) hA'
    (Int.le_trans (Int.le_add_of_nonneg_left hr) hC)]
  exact ⟨hB, hC⟩

/-- A memory injection provides the four hypotheses of `GENERIC_INJECTION`. -/
theorem copInjHyps_of_inject {f : Val.Meminj} {m m' : Mem} (h : Mem.Inject f m m') :
    CopInjHyps f m m' where
  valid_pointer_inj := fun _ _ _ _ hf hv => Mem.validPointer_inject_val h hv (.ptr _ hf rfl)
  weak_valid_pointer_inj := fun _ _ _ _ hf hv => Mem.weakValidPointer_inject_val h hv (.ptr _ hf rfl)
  weak_valid_pointer_no_overflow := fun _ _ _ _ hf hv => Mem.weakValidPointer_inject_no_overflow h hv hf
  valid_different_pointers_inj := fun _ _ _ _ _ _ _ _ hne hv1 hv2 hf1 hf2 =>
    Mem.different_pointers_inject h hne hv1 hv2 hf1 hf2

/-- `Cop.sem_cast_inject` -/
theorem semCast_inject {f : Val.Meminj} {v1 : Val} {ty1 ty : Ty} {m : Mem} {v tv1 : Val} {tm : Mem}
    (h : semCast v1 ty1 ty m = some v) (hi : Val.Inject f v1 tv1) (hm : Mem.Inject f m tm) :
    ∃ tv, semCast tv1 ty1 ty tm = some tv ∧ Val.Inject f v tv :=
  semCast_inj (copInjHyps_of_inject hm) h hi

/-- `Cop.sem_unary_operation_inject` -/
theorem semUnaryOperation_inject {f : Val.Meminj} {m m' : Mem} {op : Unop} {v1 : Val} {ty1 : Ty}
    {v tv1 : Val} (h : semUnaryOperation op v1 ty1 m = some v) (hi : Val.Inject f v1 tv1)
    (hm : Mem.Inject f m m') :
    ∃ tv, semUnaryOperation op tv1 ty1 m' = some tv ∧ Val.Inject f v tv :=
  semUnaryOperation_inj (copInjHyps_of_inject hm) h hi

/-- `Cop.sem_binary_operation_inject` -/
theorem semBinaryOperation_inject {f : Val.Meminj} {m m' : Mem} {cenv : CompositeEnv}
    {op : Binop} {v1 : Val} {ty1 : Ty} {v2 : Val} {ty2 : Ty} {v tv1 tv2 : Val}
    (h : semBinaryOperation cenv op v1 ty1 v2 ty2 m = some v)
    (hi1 : Val.Inject f v1 tv1) (hi2 : Val.Inject f v2 tv2) (hm : Mem.Inject f m m') :
    ∃ tv, semBinaryOperation cenv op tv1 ty1 tv2 ty2 m' = some tv ∧ Val.Inject f v tv :=
  semBinaryOperation_inj (copInjHyps_of_inject hm) h hi1 hi2

/-- `Cop.bool_val_inject` -/
theorem boolVal_inject {f : Val.Meminj} {m m' : Mem} {v : Val} {ty : Ty} {b : Bool} {tv : Val}
    (h : boolVal v ty m = some b) (hi : Val.Inject f v tv) (hm : Mem.Inject f m m') :
    boolVal tv ty m' = some b :=
  boolVal_inj (copInjHyps_of_inject hm) h hi

end Cop
end CC
