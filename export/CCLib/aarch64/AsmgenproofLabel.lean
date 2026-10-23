/-
  Correctness proof for AArch64 code generation, part 1 — port of the
  `TRANSL_LABEL` section of `aarch64/Asmgenproof.v`: the Asm constructor
  functions do not introduce labels, so that the translation commutes with
  label lookup (`transl_code_label`, `transl_find_label`).
-/
import CCLib.aarch64.Asmgenproof1Mem

namespace CC
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1

/-- Peel off non-label instructions until the continuation is reached. -/
macro "tnl" : tactic =>
  `(tactic| repeat' (first | exact tail_nolabel_refl _ | refine tail_nolabel_cons (by trivial) ?_))

theorem loadimmK_label (sz : Isize) (rd : Ireg) (l : List (Z × Z)) (k : Code) :
    TailNolabel k (loadimmK sz rd l k) := by
  induction l with
  | nil => exact tail_nolabel_refl _
  | cons np l ih => exact tail_nolabel_cons (by trivial) ih

theorem loadimmZ_label (sz : Isize) (rd : Ireg) (l : List (Z × Z)) (k : Code) :
    TailNolabel k (loadimmZ sz rd l k) := by
  unfold loadimmZ; split
  · tnl
  · exact tail_nolabel_cons (by trivial) (loadimmK_label _ _ _ _)

theorem loadimmN_label (sz : Isize) (rd : Ireg) (l : List (Z × Z)) (k : Code) :
    TailNolabel k (loadimmN sz rd l k) := by
  unfold loadimmN; split
  · tnl
  · exact tail_nolabel_cons (by trivial) (loadimmK_label _ _ _ _)

theorem loadimm_label (sz : Isize) (rd : Ireg) (n : Z) (k : Code) :
    TailNolabel k (loadimm sz rd n k) := by
  unfold loadimm
  cases sz <;> dsimp only <;> split <;>
    first | exact loadimmZ_label _ _ _ _ | exact loadimmN_label _ _ _ _

theorem loadimm32_label (rd : Ireg) (n : Integers.Int) (k : Code) :
    TailNolabel k (loadimm32 rd n k) := by
  unfold loadimm32; split
  · tnl
  · exact loadimm_label _ _ _ _

theorem loadimm64_label (rd : Ireg) (n : Integers.Int64) (k : Code) :
    TailNolabel k (loadimm64 rd n k) := by
  unfold loadimm64; split
  · tnl
  · exact loadimm_label _ _ _ _

theorem addimmAux_label (insn : Iregsp → Iregsp → Z → Instruction)
    (hi : ∀ rd r1 n, Nolabel (insn rd r1 n)) (rd r1 : Iregsp) (n : Z) (k : Code) :
    TailNolabel k (addimmAux insn rd r1 n k) := by
  unfold addimmAux; dsimp only
  split
  · exact tail_nolabel_cons (hi _ _ _) (tail_nolabel_refl _)
  split
  · exact tail_nolabel_cons (hi _ _ _) (tail_nolabel_refl _)
  · exact tail_nolabel_cons (hi _ _ _) (tail_nolabel_cons (hi _ _ _) (tail_nolabel_refl _))

theorem addimm32_label (rd r1 : Ireg) (n : Integers.Int) (k : Code) :
    TailNolabel k (addimm32 rd r1 n k) := by
  unfold addimm32; dsimp only
  split
  · exact addimmAux_label _ (fun _ _ _ => by trivial) _ _ _ _
  split
  · exact addimmAux_label _ (fun _ _ _ => by trivial) _ _ _ _
  split
  · exact tail_nolabel_trans (loadimm32_label _ _ _)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))
  · exact tail_nolabel_trans (loadimm32_label _ _ _)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))

theorem addimm64_label (rd r1 : Iregsp) (n : Integers.Int64) (k : Code) :
    TailNolabel k (addimm64 rd r1 n k) := by
  unfold addimm64; dsimp only
  split
  · exact addimmAux_label _ (fun _ _ _ => by trivial) _ _ _ _
  split
  · exact addimmAux_label _ (fun _ _ _ => by trivial) _ _ _ _
  split
  · exact tail_nolabel_trans (loadimm64_label _ _ _)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))
  · exact tail_nolabel_trans (loadimm64_label _ _ _)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))

theorem logicalimm32_label (insn1 : Ireg → Ireg0 → Z → Instruction)
    (insn2 : Ireg → Ireg0 → Ireg → ShiftOp → Instruction)
    (h1 : ∀ rd r1 n, Nolabel (insn1 rd r1 n)) (h2 : ∀ rd r1 r2 s, Nolabel (insn2 rd r1 r2 s))
    (rd r1 : Ireg) (n : Integers.Int) (k : Code) :
    TailNolabel k (logicalimm32 insn1 insn2 rd r1 n k) := by
  unfold logicalimm32; split
  · exact tail_nolabel_cons (h1 _ _ _) (tail_nolabel_refl _)
  · exact tail_nolabel_trans (loadimm32_label _ _ _)
      (tail_nolabel_cons (h2 _ _ _ _) (tail_nolabel_refl _))

theorem logicalimm64_label (insn1 : Ireg → Ireg0 → Z → Instruction)
    (insn2 : Ireg → Ireg0 → Ireg → ShiftOp → Instruction)
    (h1 : ∀ rd r1 n, Nolabel (insn1 rd r1 n)) (h2 : ∀ rd r1 r2 s, Nolabel (insn2 rd r1 r2 s))
    (rd r1 : Ireg) (n : Integers.Int64) (k : Code) :
    TailNolabel k (logicalimm64 insn1 insn2 rd r1 n k) := by
  unfold logicalimm64; split
  · exact tail_nolabel_cons (h1 _ _ _) (tail_nolabel_refl _)
  · exact tail_nolabel_trans (loadimm64_label _ _ _)
      (tail_nolabel_cons (h2 _ _ _ _) (tail_nolabel_refl _))

theorem moveExtendedBase_label (rd r1 : Ireg) (ex : Op.Extension) (k : Code) :
    TailNolabel k (moveExtendedBase rd r1 ex k) := by
  unfold moveExtendedBase; split <;> tnl

theorem moveExtended_label (rd r1 : Ireg) (ex : Op.Extension) (a : Integers.Int) (k : Code) :
    TailNolabel k (moveExtended rd r1 ex a k) := by
  unfold moveExtended; split
  · exact moveExtendedBase_label _ _ _ _
  · exact tail_nolabel_trans (moveExtendedBase_label _ _ _ _)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))

theorem arithExtended_label (insnX : Iregsp → Iregsp → Ireg → ExtendOp → Instruction)
    (insnS : Ireg → Ireg0 → Ireg → ShiftOp → Instruction)
    (hX : ∀ rd r1 r2 x, Nolabel (insnX rd r1 r2 x)) (hS : ∀ rd r1 r2 s, Nolabel (insnS rd r1 r2 s))
    (rd r1 r2 : Ireg) (ex : Op.Extension) (a : Integers.Int) (k : Code) :
    TailNolabel k (arithExtended insnX insnS rd r1 r2 ex a k) := by
  unfold arithExtended; split
  · exact tail_nolabel_cons (hX _ _ _ _) (tail_nolabel_refl _)
  · exact tail_nolabel_trans (moveExtendedBase_label _ _ _ _)
      (tail_nolabel_cons (hS _ _ _ _) (tail_nolabel_refl _))

theorem shrx32_label (rd r1 : Ireg) (n : Integers.Int) (k : Code) :
    TailNolabel k (shrx32 rd r1 n k) := by
  unfold shrx32; split <;> tnl

theorem shrx64_label (rd r1 : Ireg) (n : Integers.Int) (k : Code) :
    TailNolabel k (shrx64 rd r1 n k) := by
  unfold shrx64; split <;> tnl

theorem loadsymbol_label (o : Options) (rd : Ireg) (id : Ident) (ofs : Integers.Ptrofs)
    (k : Code) : TailNolabel k (loadsymbol o rd id ofs k) := by
  unfold loadsymbol; split
  · split
    · tnl
    · exact tail_nolabel_cons (by trivial) (addimm64_label _ _ _ _)
  · tnl

theorem nolabel_of_isLabel {i : Instruction} (h : ∀ lbl, isLabel lbl i = false) : Nolabel i := by
  cases i <;> simp_all [Nolabel, isLabel]

/-- Peel off non-label instructions and the constructor functions above. -/
macro "tnl_auto" : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact tail_nolabel_refl _
    | with_reducible refine tail_nolabel_cons (nolabel_of_isLabel fun _ => rfl) ?_
    | with_reducible refine tail_nolabel_trans (loadimm32_label _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (loadimm64_label _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (addimm32_label _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (addimm64_label _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (logicalimm32_label _ _
        (fun _ _ _ => nolabel_of_isLabel fun _ => rfl)
        (fun _ _ _ _ => nolabel_of_isLabel fun _ => rfl) _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (logicalimm64_label _ _
        (fun _ _ _ => nolabel_of_isLabel fun _ => rfl)
        (fun _ _ _ _ => nolabel_of_isLabel fun _ => rfl) _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (moveExtended_label _ _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (arithExtended_label _ _
        (fun _ _ _ _ => nolabel_of_isLabel fun _ => rfl)
        (fun _ _ _ _ => nolabel_of_isLabel fun _ => rfl) _ _ _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (shrx32_label _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (shrx64_label _ _ _ _) ?_
    | with_reducible refine tail_nolabel_trans (loadsymbol_label _ _ _ _ _) ?_
    | split))

set_option maxHeartbeats 2000000 in
/-- `Asmgenproof.transl_cond_label` -/
theorem transl_cond_label (cond : Op.Condition) (args : List Mreg) (k c : Code)
    (h : translCond cond args k = .OK c) : TailNolabel k c := by
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translCond, res_bind_OK, res_pure_OK, reduceCtorEq] at h <;>
    first
    | (obtain ⟨_, _, _, _, rfl⟩ := h; tnl_auto)
    | (obtain ⟨_, _, rfl⟩ := h; tnl_auto)

/-- `Asmgenproof.transl_cond_branch_default_label` -/
theorem transl_cond_branch_default_label (cond : Op.Condition) (args : List Mreg) (lbl : Label)
    (k c : Code) (h : translCondBranchDefault cond args lbl k = .OK c) : TailNolabel k c :=
  tail_nolabel_trans (transl_cond_label _ _ _ _ h) (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))

set_option maxHeartbeats 1000000 in
/-- `Asmgenproof.transl_cond_branch_label` -/
theorem transl_cond_branch_label (cond : Op.Condition) (args : List Mreg) (lbl : Label)
    (k c : Code) (h : translCondBranch cond args lbl k = .OK c) : TailNolabel k c := by
  unfold translCondBranch at h
  repeat' split at h
  all_goals first
    | exact transl_cond_branch_default_label _ _ _ _ _ h
    | (simp only [res_bind_OK, res_pure_OK] at h
       obtain ⟨_, _, rfl⟩ := h
       tnl_auto)

attribute [local irreducible] ii1 ii2 ii3 ff1 ff2 if1 fi1

set_option maxHeartbeats 2000000 in
/-- `Asmgenproof.transl_op_label` -/
theorem transl_op_label (o : Options) (op : Op.Operation) (args : List Mreg) (r : Mreg)
    (k c : Code) (h : translOp o op args r k = .OK c) : TailNolabel k c := by
  cases op
  case Ocmp cond =>
    rw [translOp_Ocmp] at h
    simp only [res_bind_OK] at h
    obtain ⟨_, _, h⟩ := h
    exact tail_nolabel_trans (transl_cond_label _ _ _ _ h)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))
  case Osel cond ty =>
    rcases args with _ | ⟨a1, _ | ⟨a2, args⟩⟩ <;> unfold translOp at h <;> dsimp only at h <;>
      (try cases h)
    split at h
    all_goals first
      | cases h
      | (simp only [res_bind_OK] at h
         obtain ⟨_, _, _, _, h⟩ := h
         split at h
         · simp only [res_pure_OK] at h; subst h; tnl_auto
         · exact tail_nolabel_trans (transl_cond_label _ _ _ _ h)
             (tail_nolabel_cons (by trivial) (tail_nolabel_refl _)))
  all_goals (rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, args⟩⟩⟩⟩ <;>
              unfold translOp at h <;> dsimp only at h <;> (try cases h))
  all_goals first
    | (guard_hyp h : ii1 _ _ _ = _
       obtain ⟨_, _, _, _, rfl⟩ := ii1_inv h)
    | (guard_hyp h : ii2 _ _ _ _ = _
       obtain ⟨_, _, _, _, _, _, rfl⟩ := ii2_inv h)
    | (guard_hyp h : ii3 _ _ _ _ _ = _
       obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := ii3_inv h)
    | (guard_hyp h : ff1 _ _ _ = _
       obtain ⟨_, _, _, _, rfl⟩ := ff1_inv h)
    | (guard_hyp h : ff2 _ _ _ _ = _
       obtain ⟨_, _, _, _, _, _, rfl⟩ := ff2_inv h)
    | (guard_hyp h : if1 _ _ _ = _
       obtain ⟨_, _, _, _, rfl⟩ := if1_inv h)
    | (guard_hyp h : fi1 _ _ _ = _
       obtain ⟨_, _, _, _, rfl⟩ := fi1_inv h)
    | (simp only [res_bind_OK, res_pure_OK] at h
       obtain ⟨_, _, rfl⟩ := h)
    | (simp only [res_bind_OK] at h
       obtain ⟨_, _, _, _, h⟩ := h
       split at h <;> cases h)
    | (split at h <;> cases h)
  all_goals tnl_auto

/-- `Asmgenproof.transl_addressing_label` -/
theorem transl_addressing_label (o : Options) (sz : Z) (addr : Op.Addressing) (args : List Mreg)
    (insn : Asm.Addressing → Instruction) (k c : Code)
    (hi : ∀ ad, Nolabel (insn ad)) (h : translAddressing o sz addr args insn k = .OK c) :
    TailNolabel k c := by
  cases addr <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;>
    simp only [translAddressing, res_bind_OK, reduceCtorEq] at h
  all_goals first
    | (obtain ⟨_, _, _, _, h⟩ := h
       repeat' split at h
       all_goals (simp only [res_pure_OK] at h; subst h))
    | (obtain ⟨_, _, h⟩ := h
       repeat' split at h
       all_goals (simp only [res_pure_OK] at h; subst h))
    | (repeat' split at h
       all_goals (cases h))
  all_goals first
    | exact tail_nolabel_cons (hi _) (tail_nolabel_refl _)
    | exact tail_nolabel_cons (by trivial) (tail_nolabel_cons (hi _) (tail_nolabel_refl _))
    | exact tail_nolabel_trans (loadimm64_label _ _ _) (tail_nolabel_cons (hi _) (tail_nolabel_refl _))
    | exact tail_nolabel_trans (loadsymbol_label _ _ _ _ _)
        (tail_nolabel_cons (hi _) (tail_nolabel_refl _))
    | exact tail_nolabel_trans (arithExtended_label _ _ (fun _ _ _ _ => by trivial)
        (fun _ _ _ _ => by trivial) _ _ _ _ _ _) (tail_nolabel_cons (hi _) (tail_nolabel_refl _))

/-- `Asmgenproof.transl_load_label` -/
theorem transl_load_label (o : Options) (chunk : Chunk) (addr : Op.Addressing) (args : List Mreg)
    (dst : Mreg) (k c : Code) (h : translLoad o chunk addr args dst k = .OK c) :
    TailNolabel k c := by
  cases chunk <;> simp only [translLoad, res_bind_OK, reduceCtorEq] at h <;>
    obtain ⟨_, _, h⟩ := h <;>
    exact transl_addressing_label _ _ _ _ _ _ _ (fun _ => by trivial) h

/-- `Asmgenproof.transl_store_label` -/
theorem transl_store_label (o : Options) (chunk : Chunk) (addr : Op.Addressing)
    (args : List Mreg) (src : Mreg) (k c : Code) (h : translStore o chunk addr args src k = .OK c) :
    TailNolabel k c := by
  cases chunk <;> simp only [translStore, res_bind_OK, reduceCtorEq] at h <;>
    obtain ⟨_, _, h⟩ := h <;>
    exact transl_addressing_label _ _ _ _ _ _ _ (fun _ => by trivial) h

/-- `Asmgenproof.indexed_memory_access_label` -/
theorem indexed_memory_access_label (insn : Asm.Addressing → Instruction) (sz : Z)
    (base : Iregsp) (ofs : Integers.Ptrofs) (k : Code) (hi : ∀ ad, Nolabel (insn ad)) :
    TailNolabel k (indexedMemoryAccess insn sz base ofs k) := by
  unfold indexedMemoryAccess; dsimp only; split
  · exact tail_nolabel_cons (hi _) (tail_nolabel_refl _)
  · exact tail_nolabel_trans (loadimm64_label _ _ _) (tail_nolabel_cons (hi _) (tail_nolabel_refl _))

/-- `Asmgenproof.loadind_label` -/
theorem loadind_label (base : Iregsp) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg)
    (k c : Code) (h : loadind base ofs ty dst k = .OK c) : TailNolabel k c := by
  unfold loadind at h
  split at h <;> cases h <;> exact indexed_memory_access_label _ _ _ _ _ (fun _ => trivial)

/-- `Asmgenproof.storeind_label` -/
theorem storeind_label (src : Mreg) (base : Iregsp) (ofs : Integers.Ptrofs) (ty : ATyp)
    (k c : Code) (h : storeind src base ofs ty k = .OK c) : TailNolabel k c := by
  unfold storeind at h
  split at h <;> cases h <;> exact indexed_memory_access_label _ _ _ _ _ (fun _ => trivial)

/-- `Asmgenproof.loadptr_label` -/
theorem loadptr_label (base : Iregsp) (ofs : Integers.Ptrofs) (dst : Ireg) (k : Code) :
    TailNolabel k (loadptr base ofs dst k) :=
  indexed_memory_access_label _ _ _ _ _ (fun _ => trivial)

/-- `Asmgenproof.storeptr_label` -/
theorem storeptr_label (src : Ireg) (base : Iregsp) (ofs : Integers.Ptrofs) (k : Code) :
    TailNolabel k (storeptr src base ofs k) :=
  indexed_memory_access_label _ _ _ _ _ (fun _ => trivial)

/-- `Asmgenproof.make_epilogue_label` -/
theorem make_epilogue_label (f : Mach.Function) (k : Code) :
    TailNolabel k (makeEpilogue f k) :=
  tail_nolabel_trans (loadptr_label _ _ _ _) (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))

/-- The conclusion of `Asmgenproof.transl_instr_label`. -/
def InstrLabelSpec (i : Mach.Instruction) (k c : Code) : Prop :=
  match i with
  | .Mlabel lbl => c = .Plabel lbl :: k
  | _ => TailNolabel k c

/-- `Asmgenproof.transl_instr_label` -/
theorem transl_instr_label (o : Options) (f : Mach.Function) (i : Mach.Instruction) (ep : Bool)
    (k c : Code) (h : translInstr o f i ep k = .OK c) : InstrLabelSpec i k c := by
  cases i <;> simp only [translInstr] at h <;> simp only [InstrLabelSpec]
  case Mgetstack => exact loadind_label _ _ _ _ _ _ h
  case Msetstack => exact storeind_label _ _ _ _ _ _ h
  case Mgetparam =>
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨c1, h1, rfl⟩ := h
    split
    · exact loadind_label _ _ _ _ _ _ h1
    · exact tail_nolabel_trans (loadptr_label _ _ _ _) (loadind_label _ _ _ _ _ _ h1)
  case Mop => exact transl_op_label _ _ _ _ _ _ h
  case Mload => exact transl_load_label _ _ _ _ _ _ _ h
  case Mstore => exact transl_store_label _ _ _ _ _ _ _ h
  case Mcall sig ros =>
    cases ros <;> simp only [res_bind_OK, res_pure_OK, Res.OK.injEq] at h
    · obtain ⟨_, _, rfl⟩ := h; tnl
    · subst h; tnl
  case Mtailcall sig ros =>
    cases ros <;> simp only [res_bind_OK, res_pure_OK, Res.OK.injEq] at h
    · obtain ⟨_, _, rfl⟩ := h
      exact tail_nolabel_trans (make_epilogue_label _ _)
        (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))
    · subst h
      exact tail_nolabel_trans (make_epilogue_label _ _)
        (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))
  case Mbuiltin => cases h; tnl
  case Mlabel => cases h; rfl
  case Mgoto => cases h; tnl
  case Mcond => exact transl_cond_branch_label _ _ _ _ _ h
  case Mjumptable =>
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨_, _, rfl⟩ := h; tnl
  case Mreturn =>
    cases h
    exact tail_nolabel_trans (make_epilogue_label _ _)
      (tail_nolabel_cons (by trivial) (tail_nolabel_refl _))

/-- `Asmgenproof.transl_instr_label'` -/
theorem transl_instr_label' (lbl : Label) (o : Options) (f : Mach.Function) (i : Mach.Instruction)
    (ep : Bool) (k c : Code) (h : translInstr o f i ep k = .OK c) :
    Asmgenproof0.findLabel lbl c = if Mach.isLabel lbl i then some k else Asmgenproof0.findLabel lbl k := by
  have A := transl_instr_label o f i ep k c h
  cases i <;> simp only [InstrLabelSpec] at A <;> try exact A.2 lbl
  subst A
  simp [Asmgenproof0.findLabel, isLabel, Mach.isLabel]

/-- `Asmgenproof.transl_code_label` -/
theorem transl_code_label (lbl : Label) (o : Options) (f : Mach.Function) :
    ∀ (c : Mach.Code) (ep : Bool) (tc : Code), translCode o f c ep = .OK tc →
    match Mach.findLabel lbl c with
    | none => Asmgenproof0.findLabel lbl tc = none
    | some c' => ∃ tc', Asmgenproof0.findLabel lbl tc = some tc' ∧ translCode o f c' false = .OK tc'
  | [], _, tc, h => by cases h; rfl
  | a :: c, ep, tc, h => by
    simp only [translCode, res_bind_OK] at h
    obtain ⟨k, hk, h⟩ := h
    simp only [Mach.findLabel]
    rw [transl_instr_label' lbl _ _ _ _ _ _ h]
    have C := Mach.isLabel_correct lbl a
    by_cases hl : Mach.isLabel lbl a = true
    · rw [if_pos hl] at C; subst C
      simp only [Mach.isLabel, decide_true, if_true]
      exact ⟨k, rfl, hk⟩
    · simp only [hl, Bool.false_eq_true, if_false]
      exact transl_code_label lbl o f c _ k hk

/-- `Asmgenproof.transl_find_label` -/
theorem transl_find_label (lbl : Label) (o : Options) (f : Mach.Function) (tf : Asm.Function)
    (h : transfFunction o f = .OK tf) :
    match Mach.findLabel lbl f.fn_code with
    | none => Asmgenproof0.findLabel lbl tf.fn_code = none
    | some c => ∃ tc, Asmgenproof0.findLabel lbl tf.fn_code = some tc ∧ translCode o f c false = .OK tc := by
  simp only [transfFunction, res_bind_OK] at h
  obtain ⟨tf', h1, h2⟩ := h
  split at h2
  · cases h2
  simp only [res_pure_OK] at h2; subst h2
  simp only [translFunction, res_bind_OK, res_pure_OK] at h1
  obtain ⟨c, hc, rfl⟩ := h1
  rw [transl_code'_transl_code] at hc
  have := transl_code_label lbl o f _ _ _ hc
  simp only [Asmgenproof0.findLabel, isLabel]
  exact this

end Asmgenproof
end CC
