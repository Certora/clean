/-
  Correctness proof for RISC-V code generation, part 1 — port of the
  `TRANSL_LABEL` section of `riscV/Asmgenproof.v`: the Asm constructor
  functions do not introduce labels, so that the translation commutes with
  label lookup (`transl_code_label`, `transl_find_label`).
-/
import CCLib.riscV.Asmgenproof1Mem

namespace CC
namespace RiscV
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Op

/-- Peel off non-label instructions until the continuation is reached. -/
macro "tnl" : tactic =>
  `(tactic| repeat' (first | exact tail_nolabel_refl _ | (refine tail_nolabel_cons ?_ ?_; trivial)))

theorem nolabel_cbranch_int32s (c : Comparison) (r1 r2 : Ireg0) (l : Label) :
    Nolabel (translCbranchInt32s c r1 r2 l) := by cases c <;> trivial
theorem nolabel_cbranch_int32u (c : Comparison) (r1 r2 : Ireg0) (l : Label) :
    Nolabel (translCbranchInt32u c r1 r2 l) := by cases c <;> trivial
theorem nolabel_cbranch_int64s (c : Comparison) (r1 r2 : Ireg0) (l : Label) :
    Nolabel (translCbranchInt64s c r1 r2 l) := by cases c <;> trivial
theorem nolabel_cbranch_int64u (c : Comparison) (r1 r2 : Ireg0) (l : Label) :
    Nolabel (translCbranchInt64u c r1 r2 l) := by cases c <;> trivial

/-- `Asmgenproof.transl_cond_float_nolabel` -/
theorem transl_cond_float_nolabel (c : Comparison) (rd : Ireg) (f1 f2 : Freg) :
    Nolabel (translCondFloat c rd f1 f2).1 := by cases c <;> trivial

/-- `Asmgenproof.transl_cond_single_nolabel` -/
theorem transl_cond_single_nolabel (c : Comparison) (rd : Ireg) (f1 f2 : Freg) :
    Nolabel (translCondSingle c rd f1 f2).1 := by cases c <;> trivial

/-- `Asmgenproof.loadimm32_label` -/
theorem loadimm32_label (r : Ireg) (n : Integers.Int) (k : Code) :
    TailNolabel k (loadimm32 r n k) := by
  unfold loadimm32 loadHilo32; split <;> (try split) <;> tnl

/-- `Asmgenproof.opimm32_label` -/
theorem opimm32_label (op : Ireg → Ireg0 → Ireg0 → Instruction)
    (opimm : Ireg → Ireg0 → Integers.Int → Instruction) (r1 r2 : Ireg) (n : Integers.Int)
    (k : Code) (h1 : ∀ r1 r2 r3, Nolabel (op r1 r2 r3)) (h2 : ∀ r1 r2 n, Nolabel (opimm r1 r2 n)) :
    TailNolabel k (opimm32 op opimm r1 r2 n k) := by
  unfold opimm32 loadHilo32; split
  · exact tail_nolabel_cons (h2 _ _ _) (tail_nolabel_refl _)
  · split <;> tnl <;> exact tail_nolabel_cons (h1 _ _ _) (tail_nolabel_refl _)

/-- `Asmgenproof.loadimm64_label` -/
theorem loadimm64_label (r : Ireg) (n : Integers.Int64) (k : Code) :
    TailNolabel k (loadimm64 r n k) := by
  unfold loadimm64 loadHilo64; split <;> (try split) <;> tnl

/-- `Asmgenproof.opimm64_label` -/
theorem opimm64_label (op : Ireg → Ireg0 → Ireg0 → Instruction)
    (opimm : Ireg → Ireg0 → Integers.Int64 → Instruction) (r1 r2 : Ireg) (n : Integers.Int64)
    (k : Code) (h1 : ∀ r1 r2 r3, Nolabel (op r1 r2 r3)) (h2 : ∀ r1 r2 n, Nolabel (opimm r1 r2 n)) :
    TailNolabel k (opimm64 op opimm r1 r2 n k) := by
  unfold opimm64 loadHilo64; split
  · exact tail_nolabel_cons (h2 _ _ _) (tail_nolabel_refl _)
  · split <;> tnl <;> exact tail_nolabel_cons (h1 _ _ _) (tail_nolabel_refl _)
  · tnl; exact tail_nolabel_cons (h1 _ _ _) (tail_nolabel_refl _)

/-- `Asmgenproof.addptrofs_label` -/
theorem addptrofs_label (r1 r2 : Ireg) (n : Integers.Ptrofs) (k : Code) :
    TailNolabel k (addptrofs r1 r2 n k) := by
  unfold addptrofs; split
  · tnl
  · split
    · exact opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · exact opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)

/-- Instructions and code fragments without labels (the `TailNoLabel` tactic
of Rocq, extended with the lemmas above). -/
macro "tnl2" : tactic =>
  `(tactic| repeat' (first
    | exact tail_nolabel_refl _
    | exact loadimm32_label _ _ _
    | exact loadimm64_label _ _ _
    | exact addptrofs_label _ _ _ _
    | exact opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    | exact opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    | refine tail_nolabel_trans (loadimm32_label _ _ _) ?_
    | refine tail_nolabel_trans (loadimm64_label _ _ _) ?_
    | refine tail_nolabel_trans (opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial)
        (fun _ _ _ => trivial)) ?_
    | refine tail_nolabel_trans (opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial)
        (fun _ _ _ => trivial)) ?_
    | refine tail_nolabel_trans (addptrofs_label _ _ _ _) ?_
    | (refine tail_nolabel_cons ?_ ?_
       first
        | trivial
        | exact nolabel_cbranch_int32s _ _ _ _
        | exact nolabel_cbranch_int32u _ _ _ _
        | exact nolabel_cbranch_int64s _ _ _ _
        | exact nolabel_cbranch_int64u _ _ _ _
        | exact transl_cond_float_nolabel _ _ _ _
        | exact transl_cond_single_nolabel _ _ _ _)
    | split))

/-- `Asmgenproof.transl_cbranch_label` -/
theorem transl_cbranch_label {cond : Condition} {args : List Mreg} {lbl : Label} {k c : Code}
    (h : translCbranch cond args lbl k = .OK c) : TailNolabel k c := by
  revert h
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;> intro h <;>
    simp only [translCbranch, res_bind_OK, res_pure_OK] at h <;> (try (cases h; done))
  all_goals first
    | (obtain ⟨_, _, _, _, rfl⟩ := h; tnl2)
    | (obtain ⟨_, _, rfl⟩ := h; tnl2)

theorem transl_cond_int32s_label (c : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) :
    TailNolabel k (translCondInt32s c rd r1 r2 k) := by cases c <;> tnl
theorem transl_cond_int32u_label (c : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) :
    TailNolabel k (translCondInt32u c rd r1 r2 k) := by cases c <;> tnl
theorem transl_cond_int64s_label (c : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) :
    TailNolabel k (translCondInt64s c rd r1 r2 k) := by cases c <;> tnl
theorem transl_cond_int64u_label (c : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) :
    TailNolabel k (translCondInt64u c rd r1 r2 k) := by cases c <;> tnl

theorem transl_condimm_int32s_label (c : Comparison) (rd r1 : Ireg) (n : Integers.Int)
    (k : Code) : TailNolabel k (translCondimmInt32s c rd r1 n k) := by
  unfold translCondimmInt32s; split
  · exact transl_cond_int32s_label _ _ _ _ _
  · split
    · exact tail_nolabel_trans (opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial))
        (transl_cond_int32s_label _ _ _ _ _)
    · exact tail_nolabel_trans (opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial))
        (transl_cond_int32s_label _ _ _ _ _)
    · exact opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · split
      · exact loadimm32_label _ _ _
      · exact opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · exact tail_nolabel_trans (loadimm32_label _ _ _)
        (transl_cond_int32s_label _ _ _ _ _)

theorem transl_condimm_int32u_label (c : Comparison) (rd r1 : Ireg) (n : Integers.Int)
    (k : Code) : TailNolabel k (translCondimmInt32u c rd r1 n k) := by
  unfold translCondimmInt32u; split
  · exact transl_cond_int32u_label _ _ _ _ _
  · split
    · exact opimm32_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · exact tail_nolabel_trans (loadimm32_label _ _ _)
        (transl_cond_int32u_label _ _ _ _ _)

theorem transl_condimm_int64s_label (c : Comparison) (rd r1 : Ireg) (n : Integers.Int64)
    (k : Code) : TailNolabel k (translCondimmInt64s c rd r1 n k) := by
  unfold translCondimmInt64s; split
  · exact transl_cond_int64s_label _ _ _ _ _
  · split
    · exact tail_nolabel_trans (opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial))
        (transl_cond_int64s_label _ _ _ _ _)
    · exact tail_nolabel_trans (opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial))
        (transl_cond_int64s_label _ _ _ _ _)
    · exact opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · split
      · exact loadimm32_label _ _ _
      · exact opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · exact tail_nolabel_trans (loadimm64_label _ _ _)
        (transl_cond_int64s_label _ _ _ _ _)

theorem transl_condimm_int64u_label (c : Comparison) (rd r1 : Ireg) (n : Integers.Int64)
    (k : Code) : TailNolabel k (translCondimmInt64u c rd r1 n k) := by
  unfold translCondimmInt64u; split
  · exact transl_cond_int64u_label _ _ _ _ _
  · split
    · exact opimm64_label _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · exact tail_nolabel_trans (loadimm64_label _ _ _)
        (transl_cond_int64u_label _ _ _ _ _)

/-- `Asmgenproof.transl_cond_op_label` -/
theorem transl_cond_op_label {cond : Condition} {rd : Ireg} {args : List Mreg} {k c : Code}
    (h : translCondOp cond rd args k = .OK c) : TailNolabel k c := by
  revert h
  cases cond <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;> intro h <;>
    simp only [translCondOp, res_bind_OK, res_pure_OK] at h <;> (try (cases h; done))
  all_goals first
    | (obtain ⟨_, _, _, _, rfl⟩ := h
       first
         | exact transl_cond_int32s_label _ _ _ _ _
         | exact transl_cond_int32u_label _ _ _ _ _
         | exact transl_cond_int64s_label _ _ _ _ _
         | exact transl_cond_int64u_label _ _ _ _ _
         | (tnl2; done))
    | (obtain ⟨_, _, rfl⟩ := h
       first
         | exact transl_condimm_int32s_label _ _ _ _ _
         | exact transl_condimm_int32u_label _ _ _ _ _
         | exact transl_condimm_int64s_label _ _ _ _ _
         | exact transl_condimm_int64u_label _ _ _ _ _)

set_option maxHeartbeats 4000000 in
/-- `Asmgenproof.transl_op_label` -/
theorem transl_op_label {o : Options} {op : Operation} {args : List Mreg} {r : Mreg} {k c : Code}
    (h : translOp o op args r k = .OK c) : TailNolabel k c := by
  revert h
  cases op <;> rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, args⟩⟩⟩ <;> intro h <;>
    unfold translOp at h <;> dsimp only at h <;>
    (try simp only [res_bind_OK, res_pure_OK, assert] at h) <;> (try (cases h; done))
  all_goals (repeat (obtain ⟨_, _, h⟩ := h))
  all_goals (try (tnl2; done))
  all_goals first
    | exact transl_cond_op_label h
    | (split at h <;>
        first
          | (cases h; done)
          | (simp only [res_pure_OK, Res.OK.injEq] at h; subst h; tnl2; done)
          | exact tail_nolabel_trans (transl_cond_op_label h)
              (tail_nolabel_cons (by trivial) (tail_nolabel_refl _)))

/-- `Asmgenproof.indexed_memory_access_label` -/
theorem indexed_memory_access_label (mk : Ireg → Offset → Instruction) (base : Ireg)
    (ofs : Integers.Ptrofs) (k : Code) (h : ∀ r o, Nolabel (mk r o)) :
    TailNolabel k (indexedMemoryAccess mk base ofs k) := by
  unfold indexedMemoryAccess
  split <;> split <;> tnl <;> exact tail_nolabel_cons (h _ _) (tail_nolabel_refl _)

/-- `Asmgenproof.loadind_label` -/
theorem loadind_label {base : Ireg} {ofs : Integers.Ptrofs} {ty : ATyp} {dst : Mreg}
    {k c : Code} (h : loadind base ofs ty dst k = .OK c) : TailNolabel k c := by
  unfold loadind at h
  split at h <;> cases h <;> exact indexed_memory_access_label _ _ _ _ (fun _ _ => trivial)

/-- `Asmgenproof.storeind_label` -/
theorem storeind_label {src : Mreg} {base : Ireg} {ofs : Integers.Ptrofs} {ty : ATyp}
    {k c : Code} (h : storeind src base ofs ty k = .OK c) : TailNolabel k c := by
  unfold storeind at h
  split at h <;> cases h <;> exact indexed_memory_access_label _ _ _ _ (fun _ _ => trivial)

/-- `Asmgenproof.loadind_ptr_label` -/
theorem loadind_ptr_label (base : Ireg) (ofs : Integers.Ptrofs) (dst : Ireg) (k : Code) :
    TailNolabel k (loadindPtr base ofs dst k) :=
  indexed_memory_access_label _ _ _ _ (fun _ _ => by unfold Nolabel; split <;> trivial)

/-- `Asmgenproof.storeind_ptr_label` -/
theorem storeind_ptr_label (src base : Ireg) (ofs : Integers.Ptrofs) (k : Code) :
    TailNolabel k (storeindPtr src base ofs k) :=
  indexed_memory_access_label _ _ _ _ (fun _ _ => by unfold Nolabel; split <;> trivial)

/-- `Asmgenproof.transl_memory_access_label` -/
theorem transl_memory_access_label {mk : Ireg → Offset → Instruction} {addr : Addressing}
    {args : List Mreg} {k c : Code} (h : translMemoryAccess mk addr args k = .OK c)
    (hmk : ∀ r o, Nolabel (mk r o)) : TailNolabel k c := by
  revert h
  cases addr <;> rcases args with _ | ⟨a1, _ | ⟨a2, args⟩⟩ <;> intro h <;>
    simp only [translMemoryAccess, res_bind_OK, res_pure_OK, Res.OK.injEq] at h <;>
    (try (cases h; done))
  · obtain ⟨_, _, rfl⟩ := h; exact indexed_memory_access_label _ _ _ _ hmk
  · subst h; exact tail_nolabel_cons trivial (tail_nolabel_cons (hmk _ _) (tail_nolabel_refl _))
  · subst h; exact indexed_memory_access_label _ _ _ _ hmk

/-- `Asmgenproof.make_epilogue_label` -/
theorem make_epilogue_label (f : Mach.Function) (k : Code) :
    TailNolabel k (makeEpilogue f k) :=
  tail_nolabel_trans (loadind_ptr_label _ _ _ _) (tail_nolabel_cons trivial (tail_nolabel_refl _))

/-- `Asmgenproof.transl_load_label` (part of `transl_instr_label` in Rocq). -/
theorem transl_load_label {chunk : Chunk} {addr : Addressing} {args : List Mreg} {dst : Mreg}
    {k c : Code} (h : translLoad chunk addr args dst k = .OK c) : TailNolabel k c := by
  cases chunk <;> simp only [translLoad, res_bind_OK] at h <;> (try (cases h; done)) <;>
    obtain ⟨_, _, h⟩ := h <;> exact transl_memory_access_label h (fun _ _ => trivial)

/-- `Asmgenproof.transl_store_label` (part of `transl_instr_label` in Rocq). -/
theorem transl_store_label {chunk : Chunk} {addr : Addressing} {args : List Mreg} {src : Mreg}
    {k c : Code} (h : translStore chunk addr args src k = .OK c) : TailNolabel k c := by
  cases chunk <;> simp only [translStore, res_bind_OK] at h <;> (try (cases h; done)) <;>
    obtain ⟨_, _, h⟩ := h <;> exact transl_memory_access_label h (fun _ _ => trivial)

/-- The conclusion of `Asmgenproof.transl_instr_label`. -/
def InstrLabelSpec (i : Mach.Instruction) (k c : Code) : Prop :=
  match i with
  | .Mlabel lbl => c = .Plabel lbl :: k
  | _ => TailNolabel k c

/-- `Asmgenproof.transl_instr_label` -/
theorem transl_instr_label (o : Options) (f : Mach.Function) (i : Mach.Instruction) (ep : Bool)
    (k c : Code) (h : translInstr o f i ep k = .OK c) : InstrLabelSpec i k c := by
  cases i <;> simp only [translInstr] at h <;> simp only [InstrLabelSpec]
  case Mgetstack => exact loadind_label h
  case Msetstack => exact storeind_label h
  case Mgetparam =>
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨c1, h1, rfl⟩ := h
    split
    · exact loadind_label h1
    · exact tail_nolabel_trans (loadind_ptr_label _ _ _ _) (loadind_label h1)
  case Mop => exact transl_op_label h
  case Mload => exact transl_load_label h
  case Mstore => exact transl_store_label h
  case Mcall sig ros =>
    cases ros <;> simp only [res_bind_OK, res_pure_OK, Res.OK.injEq] at h
    · obtain ⟨_, _, rfl⟩ := h; tnl
    · subst h; tnl
  case Mtailcall sig ros =>
    cases ros <;> simp only [res_bind_OK, res_pure_OK, Res.OK.injEq] at h
    · obtain ⟨_, _, rfl⟩ := h
      exact tail_nolabel_trans (make_epilogue_label _ _) (tail_nolabel_cons trivial
        (tail_nolabel_refl _))
    · subst h
      exact tail_nolabel_trans (make_epilogue_label _ _) (tail_nolabel_cons trivial
        (tail_nolabel_refl _))
  case Mbuiltin => cases h; tnl
  case Mlabel => cases h; rfl
  case Mgoto => cases h; tnl
  case Mcond => exact transl_cbranch_label h
  case Mjumptable =>
    simp only [res_bind_OK, res_pure_OK] at h
    obtain ⟨_, _, rfl⟩ := h; tnl
  case Mreturn =>
    cases h
    exact tail_nolabel_trans (make_epilogue_label _ _) (tail_nolabel_cons trivial
      (tail_nolabel_refl _))

/-- `Asmgenproof.transl_instr_label'` -/
theorem transl_instr_label' (lbl : Label) (o : Options) (f : Mach.Function)
    (i : Mach.Instruction) (ep : Bool) (k c : Code) (h : translInstr o f i ep k = .OK c) :
    Asmgenproof0.findLabel lbl c =
      if Mach.isLabel lbl i then some k else Asmgenproof0.findLabel lbl k := by
  have A := transl_instr_label o f i ep k c h
  cases i <;> simp only [InstrLabelSpec] at A <;> try exact A.2 lbl
  subst A
  simp [Asmgenproof0.findLabel, isLabel, Mach.isLabel]

/-- `Asmgenproof.transl_code_label` -/
theorem transl_code_label (lbl : Label) (o : Options) (f : Mach.Function) :
    ∀ (c : Mach.Code) (ep : Bool) (tc : Code), translCode o f c ep = .OK tc →
    match Mach.findLabel lbl c with
    | none => Asmgenproof0.findLabel lbl tc = none
    | some c' => ∃ tc', Asmgenproof0.findLabel lbl tc = some tc' ∧
        translCode o f c' false = .OK tc'
  | [], _, tc, h => by cases h; rfl
  | a :: c, ep, tc, h => by
    simp only [translCode, res_bind_OK] at h
    obtain ⟨k, hk, h⟩ := h
    simp only [Mach.findLabel]
    rw [transl_instr_label' lbl _ _ _ _ _ _ h]
    by_cases hl : Mach.isLabel lbl a = true
    · have C : a = .Mlabel lbl := by cases a <;> simp_all [Mach.isLabel]
      subst C
      simp only [Mach.isLabel, decide_true, if_true]
      exact ⟨k, rfl, hk⟩
    · simp only [hl, Bool.false_eq_true, if_false]
      exact transl_code_label lbl o f c _ k hk

/-- `Asmgenproof.transl_find_label` -/
theorem transl_find_label (lbl : Label) (o : Options) (f : Mach.Function) (tf : Asm.Function)
    (h : transfFunction o f = .OK tf) :
    match Mach.findLabel lbl f.fn_code with
    | none => Asmgenproof0.findLabel lbl tf.fn_code = none
    | some c => ∃ tc, Asmgenproof0.findLabel lbl tf.fn_code = some tc ∧
        translCode o f c false = .OK tc := by
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
  rw [(storeind_ptr_label _ _ _ _).2 lbl]
  simp only [Asmgenproof0.findLabel, isLabel]
  exact this

end Asmgenproof
end RiscV
end CC
