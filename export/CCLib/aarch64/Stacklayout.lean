/-
  Layout of activation records — port of `aarch64/Stacklayout.v`:
  `make_env`, `frame_env_separated`, `frame_env_range`, `frame_env_aligned`.

  Differences from Rocq: `fe_ofs_arg` is `Stacklayout.feOfsArg`, defined in
  `CCLib/backend/Mach.lean` (the Mach semantics needs it);
  `frame_env_aligned_size` additionally records that the frame size is a
  multiple of 16.
-/
import CCLib.backend.Bounds
import CCLib.backend.Mach
import CCLib.common.Separation

namespace CC

open Bounds Separation Mem

namespace Stacklayout

/-- `Stacklayout.make_env` (aarch64) -/
def makeEnv (b : Bounds) : FrameEnv :=
  let olink := align (4 * b.bound_outgoing) 8
  let oretaddr := olink + 8
  let ocs := oretaddr + 8
  let ol := align (sizeCalleeSaveArea b ocs) 8
  let ostkdata := align (ol + 4 * b.bound_local) 8
  let sz := align (ostkdata + b.bound_stack_data) 16
  { fe_size := sz, fe_ofs_link := olink, fe_ofs_retaddr := oretaddr, fe_ofs_local := ol,
    fe_ofs_callee_save := ocs, fe_stack_data := ostkdata,
    fe_used_callee_save := b.used_callee_save }

private theorem frame_arith (bo bl bsd e g f h i : Int) (h1 : 0 ≤ bl) (h2 : 0 ≤ bo)
    (a1 : 4 * bo ≤ e) (a2 : e + 8 + 8 ≤ g) (a3 : g ≤ f) (a4 : f + 4 * bl ≤ h)
    (a5 : h + bsd ≤ i) : 0 ≤ h ∧ h + bsd ≤ i := by omega

/-- `Stacklayout.frame_env_range` -/
theorem frame_env_range (b : Bounds) :
    0 ≤ (makeEnv b).fe_stack_data ∧
      (makeEnv b).fe_stack_data + b.bound_stack_data ≤ (makeEnv b).fe_size := by
  have h1 : (0 : Int) ≤ b.bound_local := b.bound_local_pos
  have h2 : (0 : Int) ≤ b.bound_outgoing := b.bound_outgoing_pos
  have a1 := align_le (4 * b.bound_outgoing) 8 (by decide)
  have a2 : (align (4 * b.bound_outgoing) 8 + 8 + 8 : Int) ≤
      sizeCalleeSaveArea b (align (4 * b.bound_outgoing) 8 + 8 + 8) :=
    sizeCalleeSaveArea_incr b (align (4 * b.bound_outgoing) 8 + 8 + 8)
  have a3 := align_le (sizeCalleeSaveArea b (align (4 * b.bound_outgoing) 8 + 8 + 8)) 8 (by decide)
  have a4 := align_le (align (sizeCalleeSaveArea b (align (4 * b.bound_outgoing) 8 + 8 + 8)) 8
    + 4 * b.bound_local) 8 (by decide)
  have a5 := align_le (align (align (sizeCalleeSaveArea b (align (4 * b.bound_outgoing) 8 + 8 + 8)) 8
    + 4 * b.bound_local) 8 + b.bound_stack_data) 16 (by decide)
  simp only [makeEnv]
  exact frame_arith _ _ _ _ _ _ _ _ h1 h2 a1 a2 a3 a4 a5

/-- `Stacklayout.frame_env_aligned` -/
theorem frame_env_aligned (b : Bounds) :
    (8 : Z) ∣ feOfsArg ∧ (8 : Z) ∣ (makeEnv b).fe_ofs_local ∧ (8 : Z) ∣ (makeEnv b).fe_stack_data ∧
      alignChunk Mptr ∣ (makeEnv b).fe_ofs_link ∧ alignChunk Mptr ∣ (makeEnv b).fe_ofs_retaddr :=
  ⟨⟨0, rfl⟩, align_divides _ _, align_divides _ _, align_divides _ _,
   Int.dvd_add (align_divides _ _) ⟨1, rfl⟩⟩

/-- The frame size and the back-link offset are aligned too (used to keep the
stack pointer 16-aligned). -/
theorem frame_env_aligned_size (b : Bounds) :
    (8 : Z) ∣ (makeEnv b).fe_ofs_link ∧ (8 : Z) ∣ (makeEnv b).fe_ofs_local ∧
      (8 : Z) ∣ (makeEnv b).fe_stack_data ∧ (16 : Z) ∣ (makeEnv b).fe_size :=
  ⟨align_divides _ _, align_divides _ _, align_divides _ _, align_divides _ _⟩


private theorem frame_env_separated_aux {m : Mem} {sp : Block} {P Q : MAssert}
    {bo bl olink scs ol ostk : _root_.Int} (hbo : 0 ≤ bo) (hbl : 0 ≤ bl)
    (holink : olink = align (4 * bo) 8) (hscs : olink + 8 + 8 ≤ scs) (hol : ol = align scs 8)
    (hostk : ol + 4 * bl ≤ ostk) (h : m ⊨ range sp 0 ostk ** Q ** P) :
    m ⊨ range sp ol (ol + 4 * bl) ** range sp 0 (0 + 4 * bo) ** range sp olink (olink + 8) **
      range sp (olink + 8) (olink + 8 + 8) ** range sp (olink + 8 + 8) scs ** P := by
  have a1 : 4 * bo ≤ olink := holink ▸ align_le _ _ (by decide)
  have a2 : scs ≤ ol := hol ▸ align_le _ _ (by decide)
  have h1 := range_drop_right (mid := ol + 4 * bl) (by omega) (by omega) (sep_drop2 h)
  have h2 := range_split_2 (mid := scs) (al := 8) (by rw [← hol]; show @LE.le _root_.Int _ _ _; omega) (by rw [← hol]; show @LE.le _root_.Int _ _ _; omega)
    (by decide) h1
  rw [← hol] at h2
  have h3 := range_split (mid := olink + 8 + 8) (by omega) (by omega) h2
  have h4 := range_split (mid := olink + 8) (by omega) (by omega) h3
  have h5 := range_split_2 (mid := 4 * bo) (al := 8) (by rw [← holink]; show @LE.le _root_.Int _ _ _; omega)
    (by rw [← holink]; show @LE.le _root_.Int _ _ _; omega) (by decide) h4
  rw [← holink] at h5
  rw [Int.zero_add]
  exact ((sep_swap12 _ _ _).trans ((sep_swap23 _ _ _ _).trans ((sep_swap34 _ _ _ _ _).trans
    (sep_swap45 _ _ _ _ _ _)))).2.1 _ h5

/-- `Stacklayout.frame_env_separated` -/
theorem frame_env_separated (b : Bounds) (sp : Block) (m : Mem) (P : MAssert)
    (h : m ⊨ range sp 0 (makeEnv b).fe_stack_data **
      range sp ((makeEnv b).fe_stack_data + b.bound_stack_data) (makeEnv b).fe_size ** P) :
    m ⊨ range sp (makeEnv b).fe_ofs_local ((makeEnv b).fe_ofs_local + 4 * b.bound_local) **
      range sp feOfsArg (feOfsArg + 4 * b.bound_outgoing) **
      range sp (makeEnv b).fe_ofs_link ((makeEnv b).fe_ofs_link + sizeChunk Mptr) **
      range sp (makeEnv b).fe_ofs_retaddr ((makeEnv b).fe_ofs_retaddr + sizeChunk Mptr) **
      range sp (makeEnv b).fe_ofs_callee_save
        (sizeCalleeSaveArea b (makeEnv b).fe_ofs_callee_save) ** P := by
  have hbo : (0 : _root_.Int) ≤ b.bound_outgoing := b.bound_outgoing_pos
  have hbl : (0 : _root_.Int) ≤ b.bound_local := b.bound_local_pos
  exact frame_env_separated_aux hbo hbl rfl
    (sizeCalleeSaveArea_incr b (align (4 * b.bound_outgoing) 8 + 8 + 8)) rfl
    (align_le _ 8 (by decide)) h

end Stacklayout

end CC
