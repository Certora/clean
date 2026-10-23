/-
  Monotonicity of `vnormalize` — port of `poffset_ge`, `poffset_monotone`,
  `provenance_monotone`, `provenance_ifptr_ge` and `vnormalize_monotone` from
  `backend/ValueDomain.v`.
-/
import CCLib.backend.ValueDomainProofNorm

namespace CC
namespace ValueDomain

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

/-- `ValueDomain.poffset_ge` -/
theorem poffset_ge (p : Aptr) : Pge (poffset p) p := by
  cases p <;> constructor

/-- `ValueDomain.poffset_monotone` -/
theorem poffset_monotone {p q : Aptr} (h : Pge p q) : Pge (poffset p) (poffset q) := by
  cases h <;> simp only [poffset] <;> first | constructor | (cases ‹Aptr› <;> constructor)

/-- `ValueDomain.provenance_monotone` -/
theorem provenance_monotone {x y : Aval} (h : Vge x y) : Pge (provenance x) (provenance y) := by
  cases h <;> simp only [provenance] <;>
    first
    | constructor
    | assumption
    | exact poffset_monotone ‹_›
    | exact pge_trans (poffset_ge _) ‹_›

/-- `ValueDomain.provenance_ifptr_ge` -/
theorem provenance_ifptr_ge {p q : Aptr} (h : Pge p q) : Pge (provenance (.Ifptr p)) q :=
  pge_trans (poffset_ge p) h

theorem vge_bool_I (p : Aptr) (j : Integers.Int) :
    Vge (.Uns p 1) (if (Integers.Int.eq j Integers.Int.zero || Integers.Int.eq j Integers.Int.one)
      then .I j else .Uns .Pbot 1) := by
  split
  · exact .uns_i _ _ _ (by decide) (isUns1_zero_or_one ((eq01_iff _).1 ‹_›))
  · exact .uns_uns _ _ _ _ (by decide) (.bot _)

theorem vge_bool_IU (p : Aptr) (j : Integers.Int) :
    Vge (.Uns p 1) (if (Integers.Int.eq j Integers.Int.zero || Integers.Int.eq j Integers.Int.one)
      then .IU j else .Uns .Pbot 1) := by
  split
  · exact .uns_iu _ _ _ (by decide) (isUns1_zero_or_one ((eq01_iff _).1 ‹_›))
  · exact .uns_uns _ _ _ _ (by decide) (.bot _)

theorem vge_bool_IU_I (j : Integers.Int) :
    Vge (if (Integers.Int.eq j Integers.Int.zero || Integers.Int.eq j Integers.Int.one)
      then .IU j else .Uns .Pbot 1)
      (if (Integers.Int.eq j Integers.Int.zero || Integers.Int.eq j Integers.Int.one)
      then .I j else .Uns .Pbot 1) := by
  split
  · exact .iu_i _
  · exact .uns_uns _ _ _ _ (by decide) (.refl _)

local macro "mono_close" : tactic =>
  `(tactic| first
    | (constructor; done)
    | exact vge_bool_I _ _
    | exact vge_bool_IU _ _
    | exact vge_bool_IU_I _
    | exact .sgn_i _ _ _ (by decide) (sext_sgn (by decide) _)
    | exact .sgn_iu _ _ _ (by decide) (sext_sgn (by decide) _)
    | exact .uns_i _ _ _ (by decide) (zext_uns _ _)
    | exact .uns_iu _ _ _ (by decide) (zext_uns _ _)
    | exact .sgn_i _ _ _ (by zomega) (sext_sgn_min (by decide) ‹_›)
    | exact .sgn_iu _ _ _ (by zomega) (sext_sgn_min (by decide) ‹_›)
    | exact .uns_i _ _ _ (by zomega) (zext_uns_min _ ‹_›)
    | exact .uns_iu _ _ _ (by zomega) (zext_uns_min _ ‹_›)
    | exact .uns_i _ _ _ ‹_› (is_sign_ext_uns _ _ _ ‹_› (by zomega) ‹_›)
    | exact .uns_iu _ _ _ ‹_› (is_sign_ext_uns _ _ _ ‹_› (by zomega) ‹_›)
    | (constructor <;> first | exact ‹Pge _ _› | zomega)
    | (constructor <;> simp only [provenance] <;> first | assumption | constructor)
    | (exfalso; zomega))

local macro "mono_tac" : tactic =>
  `(tactic| (cases ‹Vge _ _› <;> delta vnormalize <;> dsimp only <;>
    (try simp only [Archi.ptr64, if_true]) <;> (try split) <;> (try split) <;> mono_close))

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mbool {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mbool x) (vnormalize .Mbool y) := by
  have hp := provenance_monotone h
  cases h <;> delta vnormalize <;> dsimp only <;>
    first
    | (constructor; done)
    | exact vge_bool_I _ _
    | exact vge_bool_IU _ _
    | exact vge_bool_IU_I _
    | exact .uns_uns _ _ _ _ (Int.le_refl _) hp
    | exact vge_refl _

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mint8signed {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mint8signed x) (vnormalize .Mint8signed y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mint8unsigned {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mint8unsigned x) (vnormalize .Mint8unsigned y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mint16signed {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mint16signed x) (vnormalize .Mint16signed y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mint16unsigned {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mint16unsigned x) (vnormalize .Mint16unsigned y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mint32 {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mint32 x) (vnormalize .Mint32 y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mint64 {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mint64 x) (vnormalize .Mint64 y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mfloat32 {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mfloat32 x) (vnormalize .Mfloat32 y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Mfloat64 {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Mfloat64 x) (vnormalize .Mfloat64 y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Many32 {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Many32 x) (vnormalize .Many32 y) := by
  have hp := provenance_monotone h
  mono_tac

set_option maxHeartbeats 1000000 in
theorem vnormalize_monotone_Many64 {x y : Aval} (h : Vge x y) :
    Vge (vnormalize .Many64 x) (vnormalize .Many64 y) := by
  have hp := provenance_monotone h
  mono_tac

/-- `ValueDomain.vnormalize_monotone` -/
theorem vnormalize_monotone (chunk : Chunk) {x y : Aval} (h : Vge x y) :
    Vge (vnormalize chunk x) (vnormalize chunk y) := by
  cases chunk
  · exact vnormalize_monotone_Mbool h
  · exact vnormalize_monotone_Mint8signed h
  · exact vnormalize_monotone_Mint8unsigned h
  · exact vnormalize_monotone_Mint16signed h
  · exact vnormalize_monotone_Mint16unsigned h
  · exact vnormalize_monotone_Mint32 h
  · exact vnormalize_monotone_Mint64 h
  · exact vnormalize_monotone_Mfloat32 h
  · exact vnormalize_monotone_Mfloat64 h
  · exact vnormalize_monotone_Many32 h
  · exact vnormalize_monotone_Many64 h

end ValueDomain
end CC
