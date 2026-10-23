/-
  Layout of activation records for the x86 back end — port of
  `x86/Stacklayout.v`: `fe_ofs_arg`, `make_env`, `frame_env_separated`,
  `frame_env_range`, `frame_env_aligned`.

  The frame is laid out as follows (from the stack pointer upwards):
  - for the Win64 ABI, 32 reserved bytes;
  - the outgoing arguments of function calls;
  - the back link to the parent frame;
  - the saved callee-save registers used by the function;
  - the local stack slots;
  - the stack-allocated data declared in Cminor;
  - the return address.

  Differences from Rocq: `Archi.win64` (a Rocq `Parameter`) is an explicit
  argument `win64`; the bounds record is the x86 instance
  `CCLib/x86/Bounds.lean`.  `Archi.ptr64` is `true` in this port, so the
  word size `w` is 8.
-/
import CCLib.x86.Bounds
import CCLib.common.Separation

namespace CC
namespace X86

open Separation Mem
open X86.Bounds (Bounds FrameEnv sizeCalleeSaveArea sizeCalleeSaveArea_incr)

namespace Stacklayout

/-- `Stacklayout.fe_ofs_arg` -/
def feOfsArg (win64 : Bool) : Z := if win64 then 32 else 0

/-- The word size `if Archi.ptr64 then 8 else 4` of `make_env`. -/
def wordSize : Z := if Archi.ptr64 then 8 else 4

theorem wordSize_eq : wordSize = 8 := rfl

/-- `Stacklayout.make_env` (x86) -/
def makeEnv {win64 : Bool} (b : Bounds win64) : FrameEnv :=
  let w := wordSize
  let olink := align (feOfsArg win64 + 4 * b.bound_outgoing) w
  let ocs := olink + w
  let ol := align (sizeCalleeSaveArea b ocs) 8
  let ostkdata := align (ol + 4 * b.bound_local) 8
  let oretaddr := align (ostkdata + b.bound_stack_data) w
  let sz := oretaddr + w
  { fe_size := sz, fe_ofs_link := olink, fe_ofs_retaddr := oretaddr, fe_ofs_local := ol,
    fe_ofs_callee_save := ocs, fe_stack_data := ostkdata,
    fe_used_callee_save := b.used_callee_save }

theorem feOfsArg_nonneg (win64 : Bool) : 0 ≤ feOfsArg win64 := by
  cases win64 <;> decide

private theorem frame_arith (arg bo bl bsd e g f h i : _root_.Int) (h0 : 0 ≤ arg) (h1 : 0 ≤ bl)
    (h2 : 0 ≤ bo) (a1 : arg + 4 * bo ≤ e) (a2 : e + 8 ≤ g) (a3 : g ≤ f) (a4 : f + 4 * bl ≤ h)
    (a5 : h + bsd ≤ i) : 0 ≤ h ∧ h + bsd ≤ i + 8 := by omega

/-- `Stacklayout.frame_env_range` -/
theorem frame_env_range {win64 : Bool} (b : Bounds win64) :
    0 ≤ (makeEnv b).fe_stack_data ∧
      (makeEnv b).fe_stack_data + b.bound_stack_data ≤ (makeEnv b).fe_size := by
  have h1 : (0 : Int) ≤ b.bound_local := b.bound_local_pos
  have h2 : (0 : Int) ≤ b.bound_outgoing := b.bound_outgoing_pos
  have h0 := feOfsArg_nonneg win64
  have a1 := align_le (feOfsArg win64 + 4 * b.bound_outgoing) 8 (by decide)
  have a2 : (align (feOfsArg win64 + 4 * b.bound_outgoing) 8 + 8 : Int) ≤
      sizeCalleeSaveArea b (align (feOfsArg win64 + 4 * b.bound_outgoing) 8 + 8) :=
    sizeCalleeSaveArea_incr b _
  have a3 := align_le (sizeCalleeSaveArea b
    (align (feOfsArg win64 + 4 * b.bound_outgoing) 8 + 8)) 8 (by decide)
  have a4 := align_le (align (sizeCalleeSaveArea b
    (align (feOfsArg win64 + 4 * b.bound_outgoing) 8 + 8)) 8 + 4 * b.bound_local) 8 (by decide)
  have a5 := align_le (align (align (sizeCalleeSaveArea b
    (align (feOfsArg win64 + 4 * b.bound_outgoing) 8 + 8)) 8 + 4 * b.bound_local) 8 +
      b.bound_stack_data) 8 (by decide)
  simp only [makeEnv, wordSize_eq]
  exact frame_arith _ _ _ _ _ _ _ _ _ h0 h1 h2 a1 a2 a3 a4 a5

/-- `Stacklayout.frame_env_aligned` -/
theorem frame_env_aligned {win64 : Bool} (b : Bounds win64) :
    (8 : Z) ∣ feOfsArg win64 ∧ (8 : Z) ∣ (makeEnv b).fe_ofs_local ∧
      (8 : Z) ∣ (makeEnv b).fe_stack_data ∧
      alignChunk Mptr ∣ (makeEnv b).fe_ofs_link ∧ alignChunk Mptr ∣ (makeEnv b).fe_ofs_retaddr :=
  ⟨by cases win64 <;> decide, align_divides _ _, align_divides _ _, align_divides _ _,
   align_divides _ _⟩

private theorem frame_env_separated_aux {m : Mem} {sp : Block} {P : MAssert}
    {arg bo bl bsd olink ocs scs ol ostk oret : _root_.Int} (harg : 0 ≤ arg) (hbo : 0 ≤ bo)
    (hbl : 0 ≤ bl)
    (holink : olink = align (arg + 4 * bo) 8) (hocs : ocs = olink + 8) (hscs : ocs ≤ scs)
    (hol : ol = align scs 8) (hostk : ol + 4 * bl ≤ ostk)
    (horet : oret = align (ostk + bsd) 8)
    (h : m ⊨ range sp 0 ostk ** range sp (ostk + bsd) (oret + 8) ** P) :
    m ⊨ range sp ol (ol + 4 * bl) ** range sp arg (arg + 4 * bo) **
      range sp olink (olink + 8) ** range sp oret (oret + 8) ** range sp ocs scs ** P := by
  subst hocs
  have a1 : arg + 4 * bo ≤ olink := holink ▸ align_le _ _ (by decide)
  have a2 : scs ≤ ol := hol ▸ align_le _ _ (by decide)
  have a3 : ostk + bsd ≤ oret := horet ▸ align_le _ _ (by decide)
  have h1 := (sep_swap _ _ _).1.pred h
  have h2 := range_drop_left (mid := oret) a3 (by omega) h1
  have h3 := (sep_swap _ _ _).1.pred h2
  have h4 := range_drop_right (mid := ol + 4 * bl) (by omega) hostk h3
  have h5 := range_split_2 (mid := scs) (al := 8) (by rw [← hol]; show @LE.le _root_.Int _ _ _; omega)
    (by rw [← hol]; show @LE.le _root_.Int _ _ _; omega) (by decide) h4
  rw [← hol] at h5
  have h6 := range_split (mid := olink + 8) (by omega) hscs h5
  have h7 := range_split_2 (mid := arg + 4 * bo) (al := 8)
    (by rw [← holink]; show @LE.le _root_.Int _ _ _; omega)
    (by rw [← holink]; show @LE.le _root_.Int _ _ _; omega) (by decide) h6
  rw [← holink] at h7
  have h8 := range_drop_left (mid := arg) harg (by omega) h7
  exact (sep_swap12 _ _ _).1.pred ((sep_swap23 _ _ _ _).1.pred
    ((sep_swap45 _ _ _ _ _ _).1.pred ((sep_swap34 _ _ _ _ _).1.pred h8)))

/-- `Stacklayout.frame_env_separated` -/
theorem frame_env_separated {win64 : Bool} (b : Bounds win64) (sp : Block) (m : Mem)
    (P : MAssert)
    (h : m ⊨ range sp 0 (makeEnv b).fe_stack_data **
      range sp ((makeEnv b).fe_stack_data + b.bound_stack_data) (makeEnv b).fe_size ** P) :
    m ⊨ range sp (makeEnv b).fe_ofs_local ((makeEnv b).fe_ofs_local + 4 * b.bound_local) **
      range sp (feOfsArg win64) (feOfsArg win64 + 4 * b.bound_outgoing) **
      range sp (makeEnv b).fe_ofs_link ((makeEnv b).fe_ofs_link + sizeChunk Mptr) **
      range sp (makeEnv b).fe_ofs_retaddr ((makeEnv b).fe_ofs_retaddr + sizeChunk Mptr) **
      range sp (makeEnv b).fe_ofs_callee_save
        (sizeCalleeSaveArea b (makeEnv b).fe_ofs_callee_save) ** P := by
  have hbo : (0 : _root_.Int) ≤ b.bound_outgoing := b.bound_outgoing_pos
  have hbl : (0 : _root_.Int) ≤ b.bound_local := b.bound_local_pos
  exact frame_env_separated_aux (feOfsArg_nonneg win64) hbo hbl rfl rfl
    (sizeCalleeSaveArea_incr b _) rfl (align_le _ 8 (by decide)) rfl h

end Stacklayout
end X86
end CC
