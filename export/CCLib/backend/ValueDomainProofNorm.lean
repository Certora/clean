/-
  Soundness of `maskzero`, of the normalization operators (`vnormalize_type`,
  `select`, `vnormalize`) and of the conversions between concrete and
  abstract values (`backend/ValueDomain.v`, from `maskzero_sound` to
  `of_xtype_arg_sound`).  Continues `ValueDomainProofCmp.lean`.
-/
import CCLib.backend.ValueDomainProofCmp
import CCLib.common.ValuesInject
import CCLib.common.ValuesTheory

namespace CC
namespace ValueDomain

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

section
variable {bc : BlockClassification}

/-! ## `maskzero` -/

/-- `ValueDomain.maskzero_sound` -/
theorem maskzero_sound (mask : Integers.Int) {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Cmatch (Val.maskzero_bool v mask) (maskzero x mask) := by
  cases h <;> simp only [Val.maskzero_bool, maskzero] <;> try constructor
  all_goals split <;> try constructor
  rename_i p i n hn hu hz
  have e : Integers.Int.and i mask = Integers.Int.zero := by
    have hz' := Integers.Int.same_if_eq hz
    apply Integers.Int.same_bits_eq
    intro k hk
    rw [Integers.Int.bits_and, Integers.Int.bits_zero]
    by_cases hkn : (k : Z) < n
    · have := congrArg (fun z => Integers.Int.testbit z k) hz'
      simp only [Integers.Int.bits_zero_ext, Integers.Int.bits_zero] at this
      have hk' : k < n.toNat := by zomega
      simp only [hk', decide_true, Bool.true_and] at this
      simp [this]
    · rw [hu k (by zomega) (by zomega)]; rfl
  rw [e, Integers.Int.eq_true]; constructor

/-! ## Normalization -/

/-- `ValueDomain.vnormalize_type_sound` -/
theorem vnormalize_type_sound {v : Val} {x : Aval} (ty : ATyp) (h : Vmatch bc v x) :
    Vmatch bc (Val.normalize v ty) (vnormalizeType ty x) := by
  cases h <;> cases ty <;>
    simp only [Val.normalize, vnormalizeType, addUndef, Archi.ptr64, if_true, ntop] <;>
    first | assumption | (constructor <;> assumption) | (constructor; done)

/-- `ValueDomain.select_sound` -/
theorem select_sound (strict : Bool) {ob : Option Bool} {v w : Val} {ab : Abool} {x y : Aval}
    (ty : ATyp) (hc : Cmatch ob ab) (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.select ob v w ty) (select strict ab x y ty) := by
  cases hc <;> simp only [Val.select, select]
  · exact .num_undef _
  · rename_i b; cases b <;> exact vnormalize_type_sound ty ‹_›
  · exact add_undef_undef _
  · rename_i b; cases b <;> exact add_undef_sound (vnormalize_type_sound ty ‹_›)
  · cases ob with
    | none => exact add_undef_undef _
    | some b =>
      apply add_undef_sound; apply vnormalize_type_sound
      cases b
      · exact vmatch_lub_r strict _ h2
      · exact vmatch_lub_l strict _ h1

theorem zext_uns (k : Nat) (i : Integers.Int) : IsUns k (Integers.Int.zero_ext k i) :=
  is_zero_ext_uns i k k (.inr (Int.le_refl _))

theorem sext_sgn {k : Nat} (hk : 0 < k) (i : Integers.Int) : IsSgn k (Integers.Int.sign_ext k i) :=
  is_sign_ext_sgn i k k hk (.inr (Int.le_refl _))

theorem zext_uns_min (k : Nat) {n : Z} {i : Integers.Int} (hu : IsUns n i) :
    IsUns (min n k) (Integers.Int.zero_ext k i) := by
  by_cases h : n ≤ k
  · rw [Int.min_eq_left h]; exact is_zero_ext_uns i k n (.inl hu)
  · rw [Int.min_eq_right (by zomega)]; exact zext_uns k i

theorem sext_sgn_min {k : Nat} (hk : 0 < k) {n : Z} {i : Integers.Int} (hs : IsSgn n i) :
    IsSgn (min n k) (Integers.Int.sign_ext k i) := by
  by_cases h : n ≤ k
  · rw [Int.min_eq_left h]; exact is_sign_ext_sgn i k n hk (.inl hs)
  · rw [Int.min_eq_right (by zomega)]; exact sext_sgn hk i

local macro "norm_close" : tactic =>
  `(tactic| first
    | (constructor; done)
    | (constructor <;> assumption)
    | exact .Uns _ _ _ (by decide) (zext_uns _ _)
    | exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _)
    | exact .Uns _ _ _ (by zomega) (zext_uns_min _ ‹_›)
    | exact .Sgn _ _ _ (by zomega) (sext_sgn_min (by decide) ‹_›)
    | (split
       · exact .Uns _ _ _ ‹_› (is_sign_ext_uns _ _ _ ‹_› (by zomega) ‹_›)
       · exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _))
    | (split <;> first | (constructor; done) | (constructor <;> assumption)))

theorem isUns1_zero_or_one {j : Integers.Int} (h : j = Integers.Int.one ∨ j = Integers.Int.zero) :
    IsUns 1 j := by
  rcases h with e | e <;> subst e
  · exact fun m h1 h2 => by rw [bits_one]; simp only [decide_eq_false_iff_not]; zomega
  · exact fun m _ _ => Integers.Int.bits_zero m

theorem normBool_vint (j : Integers.Int) :
    Val.normBool (.Vint j) =
      if j = Integers.Int.one ∨ j = Integers.Int.zero then .Vint j else .Vundef := by
  simp only [Val.normBool, Val.isBool, Val.Vtrue, Val.Vfalse, Bool.or_eq_true, beq_iff_eq,
    Val.Vint.injEq]

theorem eq01_iff (j : Integers.Int) :
    (Integers.Int.eq j Integers.Int.zero || Integers.Int.eq j Integers.Int.one) = true ↔
      (j = Integers.Int.one ∨ j = Integers.Int.zero) := by
  rw [Bool.or_eq_true, Integers.Int.eq_spec, Integers.Int.eq_spec, or_comm]

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mbool {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mbool v) (vnormalize .Mbool x) := by
  have NB : ∀ p i, Vmatch bc (Val.normBool (.Vint (Integers.Int.zero_ext 8 i))) (.Uns p 1) := by
    intro p i
    rw [normBool_vint]; split
    · exact .Uns _ _ _ (by decide) (isUns1_zero_or_one ‹_›)
    · exact .Uns_undef _ _
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, provenance] <;>
    first
    | exact NB _ _
    | exact .Uns_undef _ _
    | (rw [normBool_vint]
       by_cases hc : (Integers.Int.zero_ext 8 ‹_› = Integers.Int.one ∨
          Integers.Int.zero_ext 8 ‹_› = Integers.Int.zero)
       · rw [if_pos hc, if_pos ((eq01_iff _).2 hc)]; constructor
       · rw [if_neg hc, if_neg (fun e => hc ((eq01_iff _).1 e))]; constructor)
    | (split <;> constructor)

local macro "sext_close" : tactic =>
  `(tactic| first
    | (constructor; done)
    | exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _)
    | exact .Sgn _ _ _ (by zomega) (sext_sgn_min (by decide) ‹_›)
    | (split
       · exact .Uns _ _ _ ‹_› (is_sign_ext_uns _ _ _ ‹_› (by zomega) ‹_›)
       · exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _))
    | (split <;> constructor))

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mint8signed {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mint8signed v) (vnormalize .Mint8signed x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try sext_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mint8unsigned {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mint8unsigned v) (vnormalize .Mint8unsigned x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mint16signed {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mint16signed v) (vnormalize .Mint16signed x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try sext_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mint16unsigned {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mint16unsigned v) (vnormalize .Mint16unsigned x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mint32 {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mint32 v) (vnormalize .Mint32 x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mint64 {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mint64 v) (vnormalize .Mint64 x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mfloat32 {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mfloat32 v) (vnormalize .Mfloat32 x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Mfloat64 {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Mfloat64 v) (vnormalize .Mfloat64 x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Many32 {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Many32 v) (vnormalize .Many32 x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

set_option maxHeartbeats 1000000 in
theorem vnormalize_sound_Many64 {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult .Many64 v) (vnormalize .Many64 x) := by
  cases h <;> delta vnormalize <;> dsimp only <;>
    simp only [Val.loadResult, Archi.ptr64, if_true, provenance] <;>
    try norm_close

/-- `ValueDomain.vnormalize_sound` -/
theorem vnormalize_sound (chunk : Chunk) {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loadResult chunk v) (vnormalize chunk x) := by
  cases chunk
  · exact vnormalize_sound_Mbool h
  · exact vnormalize_sound_Mint8signed h
  · exact vnormalize_sound_Mint8unsigned h
  · exact vnormalize_sound_Mint16signed h
  · exact vnormalize_sound_Mint16unsigned h
  · exact vnormalize_sound_Mint32 h
  · exact vnormalize_sound_Mint64 h
  · exact vnormalize_sound_Mfloat32 h
  · exact vnormalize_sound_Mfloat64 h
  · exact vnormalize_sound_Many32 h
  · exact vnormalize_sound_Many64 h

/-! ## Concrete and abstract values -/

/-- `ValueDomain.val_of_aval_sound` -/
theorem val_of_aval_sound {v : Val} {a : Aval} (h : Vmatch bc v a) : Val.Lessdef (valOfAval a) v := by
  cases h <;> simp only [valOfAval] <;> constructor

/-- `ValueDomain.aval_of_val_sound` -/
theorem aval_of_val_sound {v : Val} {a : Aval} (h : avalOfVal v = some a) : Vmatch bc v a := by
  cases v <;> simp only [avalOfVal, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> constructor

local macro "xt_undef" : tactic =>
  `(tactic| first | exact .Uns_undef _ _ | exact .Sgn_undef _ _ | exact ht.elim)

/-- `ValueDomain.of_xtype_arg_sound` -/
theorem of_xtype_arg_sound {v : Val} (x : XType) (p : Aptr) (ht : Val.HasArgtype v x)
    (h : Vmatch bc v (.Ifptr p)) : Vmatch bc v (ofXtype x p) := by
  cases x <;> simp only [ofXtype] <;> try exact h
  all_goals cases v <;> simp only [Val.HasArgtype] at ht <;> try xt_undef
  · rename_i n
    refine .Uns _ _ _ (by decide) ?_
    rcases ht with e | e <;> subst e
    · exact fun m _ _ => Integers.Int.bits_zero m
    · exact fun m h1 h2 => by rw [bits_one]; simp only [decide_eq_false_iff_not]; zomega
  · rw [ht]; exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _)
  · rw [ht]; exact .Uns _ _ _ (by decide) (zext_uns _ _)
  · rw [ht]; exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _)
  · rw [ht]; exact .Uns _ _ _ (by decide) (zext_uns _ _)

end

end ValueDomain
end CC
