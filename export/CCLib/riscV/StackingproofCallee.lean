/-
  [RISC-V instance of `CCLib/backend/StackingproofCallee.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness proof for the layout of activation records, part 3 — port of
  the "Correctness of saving and restoring of callee-save registers" part of
  `backend/Stackingproof.v`: `save_callee_save_rec_correct`,
  `save_callee_save_correct`, `function_prologue_correct`,
  `restore_callee_save_rec_correct`, `restore_callee_save_correct` and
  `function_epilogue_correct`.

  Differences from Rocq: on aarch64 `destroyed_by_setstack` is empty and every
  machine register has type `Tany64`, so the section hypotheses
  `ls_temp_undef` and `wt_ls` of Rocq's `Section SAVE_CALLEE_SAVE` hold
  trivially and are omitted.
-/
import CCLib.riscV.StackingproofAgree

namespace CC
namespace RiscV
namespace Stackingproof

open Linear Mach Conventions1 Conventions Stacklayout Stacking Bounds Separation
open Lineartyping Smallstep

section CALLEE_SAVE
variable (rao : Mach.Function → Mach.Code → Integers.Ptrofs → Prop)
  (tge : Mach.CGenv)

/-- `Stackingproof.save_callee_save_rec_correct` -/
theorem save_callee_save_rec_correct (j : Val.Meminj) (cs : List Mach.Stackframe) (fb : Block)
    (sp : Block) (ls : LTL.Locset) (k : Mach.Code) :
    ∀ (l : List Mreg) (pos : Z) (rs : Regset) (m : Mem) (P : MAssert),
      m ⊨ range sp pos (sizeCalleeSaveAreaRec l pos) ** P →
      AgreeRegs j ls rs →
      ∃ rs' m',
        Smallstep.Star (Mach.Step  rao tge)
          (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) (saveCalleeSaveRec l pos k) rs m)
          E0 (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) k rs' m') ∧
        m' ⊨ containsCalleeSaves j sp pos l ls ** P ∧
        (∀ ofs k p, Mem.perm m sp ofs k p = true → Mem.perm m' sp ofs k p = true) ∧
        AgreeRegs j ls rs'
  | [], pos, rs, m, P, SEP, AG =>
    ⟨rs, m, .refl _, (sep_pure True P m).2 ⟨trivial, sep_drop SEP⟩, fun _ _ _ h => h, AG⟩
  | r :: l, pos, rs, m, P, SEP, AG => by
    simp only [containsCalleeSaves, saveCalleeSaveRec]
    simp only [sizeCalleeSaveAreaRec] at SEP
    have SZPOS : (0 : Z) < (Mreg.type r).size := by rw [Mreg.type_eq_any64]; decide
    have POS1 := align_le pos (Mreg.type r).size SZPOS
    have AL1 : alignChunk (Chunk.ofTyp (Mreg.type r)) ∣ align pos (Mreg.type r).size := by
      rw [Mreg.type_eq_any64]; exact Int.dvd_trans (show alignChunk (Chunk.ofTyp .Tany64) ∣ ATyp.size .Tany64 by decide)
        (align_divides _ _)
    generalize align pos (Mreg.type r).size = pos1 at *
    have SZREC := sizeCalleeSaveAreaRec_incr l (pos1 + (Mreg.type r).size)
    have SEP1 := range_drop_left (mid := pos1) POS1 (by zomega) SEP
    have SEP2 := range_split (mid := pos1 + (Mreg.type r).size) (by zomega) SZREC SEP1
    have SEP2' : m ⊨ range sp pos1 (pos1 + sizeChunk (Chunk.ofTyp (Mreg.type r))) **
        (range sp (pos1 + (Mreg.type r).size) (sizeCalleeSaveAreaRec l
          (pos1 + (Mreg.type r).size)) ** P) := by
      rw [size_type_chunk]; exact SEP2
    have SEP3 := range_contains SEP2' AL1
    obtain ⟨m1, STORE, SEP4⟩ := contains_set_stack (spec := fun v' => Val.Inject j (ls (.R r)) v')
      (rs r) SEP3 (load_result_inject (AG r) (hasType_mreg _ _))
    have SEP5 := (sep_swap _ _ _).pred.1 SEP4
    obtain ⟨rs2, m2, A, B, C, D⟩ :=
      save_callee_save_rec_correct j cs fb sp ls k l _ rs m1 _ SEP5 AG
    refine ⟨rs2, m2, ?_, ?_, ?_, D⟩
    · exact star_left (Mach.Step.Msetstack _ _ _ _ _ _ _ _ _ _ _ STORE rfl) A rfl
    · exact (sep_assoc _ _ _).pred.2 ((sep_swap _ _ _).pred.1 B)
    · intro ofs k' p hp
      apply C
      have hst := STORE
      rw [storeStack_eq _ _ _ _ _ (by have := SEP.1.1; zomega) (by
        have := (sep_proj1 SEP3).2.1; zomega)] at hst
      rw [Mem.perm_store hst]; exact hp

end CALLEE_SAVE

/-! ## Properties of the translated function (`Section FRAME_PROPERTIES`) -/

section FRAME_PROPERTIES
variable {f : Linear.Function} {tf : Mach.Function}

/-- `Stackingproof.unfold_transf_function` -/
theorem unfold_transf_function (h : transfFunction  f = .OK tf) :
    tf = { fn_sig := f.fn_sig, fn_code := translBody f (fenv  f),
           fn_stacksize := (fenv  f).fe_size,
           fn_link_ofs := Integers.Ptrofs.repr (fenv  f).fe_ofs_link,
           fn_retaddr_ofs := Integers.Ptrofs.repr (fenv  f).fe_ofs_retaddr } := by
  unfold transfFunction at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h; rfl

/-- `Stackingproof.transf_function_well_typed` -/
theorem transf_function_well_typed (h : transfFunction  f = .OK tf) :
    wtFunction  f = true := by
  unfold transfFunction at h
  split at h
  · cases h
  · rename_i hw; simpa using hw

/-- `Stackingproof.size_no_overflow` -/
theorem size_no_overflow (h : transfFunction  f = .OK tf) :
    (fenv  f).fe_size ≤ Integers.Ptrofs.max_unsigned := by
  unfold transfFunction at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · rename_i hlt; exact Int.not_lt.mp hlt

/-- `Stackingproof.bound_stack_data_stacksize` -/
theorem bound_stack_data_stacksize : f.fn_stacksize ≤ (bnds  f).bound_stack_data :=
  Int.le_max_left _ _

end FRAME_PROPERTIES

/-! ## Remarks on `LTL.undef_regs` -/

/-- `Stackingproof.LTL_undef_regs_same` -/
theorem LTL_undef_regs_same {r : Mreg} : ∀ {rl : List Mreg} (ls : LTL.Locset), r ∈ rl →
    LTL.undefRegs rl ls (.R r) = .Vundef
  | [], _, h => absurd h List.not_mem_nil
  | a :: rl, ls, h => by
    simp only [LTL.undefRegs]
    by_cases e : a = r
    · subst e; exact Locmap.gss_reg _ _ _
    · rcases List.mem_cons.mp h with e' | h'
      · exact absurd e'.symm e
      · rw [Locmap.gso (by simp [Loc.diff]; exact e)]; exact LTL_undef_regs_same ls h'

/-- `Stackingproof.LTL_undef_regs_others` -/
theorem LTL_undef_regs_others {r : Mreg} : ∀ {rl : List Mreg} (ls : LTL.Locset), r ∉ rl →
    LTL.undefRegs rl ls (.R r) = ls (.R r)
  | [], _, _ => rfl
  | a :: rl, ls, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [LTL.undefRegs]
    rw [Locmap.gso (by simp [Loc.diff]; exact Ne.symm h.1)]
    exact LTL_undef_regs_others ls h.2

/-- `Stackingproof.LTL_undef_regs_slot` -/
theorem LTL_undef_regs_slot (sl : Slot) (ofs : Z) (ty : ATyp) :
    ∀ (rl : List Mreg) (ls : LTL.Locset), LTL.undefRegs rl ls (.S sl ofs ty) = ls (.S sl ofs ty)
  | [], _ => rfl
  | a :: rl, ls => by
    simp only [LTL.undefRegs]
    rw [Locmap.gso (by simp [Loc.diff])]
    exact LTL_undef_regs_slot sl ofs ty rl ls

section CALLEE_SAVE2
variable (rao : Mach.Function → Mach.Code → Integers.Ptrofs → Prop)
  (tge : Mach.CGenv)

/-- `Stackingproof.save_callee_save_correct` -/
theorem save_callee_save_correct (f : Linear.Function) (j : Val.Meminj) (ls ls0 : LTL.Locset)
    (rs : Regset) (sp : Block) (cs : List Mach.Stackframe) (fb : Block) (k : Mach.Code)
    (m : Mem) (P : MAssert)
    (SEP : m ⊨ range sp (fenv  f).fe_ofs_callee_save
      (sizeCalleeSaveArea (bnds  f) (fenv  f).fe_ofs_callee_save) ** P)
    (AGCS : AgreeCalleeSave ls ls0) (AG : AgreeRegs j ls rs) :
    ∃ rs' m',
      Smallstep.Star (Mach.Step  rao tge)
        (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) (saveCalleeSave (fenv  f) k)
          (Mach.undefRegs destroyedAtFunctionEntry rs) m)
        E0 (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) k rs' m') ∧
      m' ⊨ containsCalleeSaves j sp (fenv  f).fe_ofs_callee_save
        (bnds  f).used_callee_save ls0 ** P ∧
      (∀ ofs k p, Mem.perm m sp ofs k p = true → Mem.perm m' sp ofs k p = true) ∧
      AgreeRegs j (LTL.undefRegs destroyedAtFunctionEntry (LTL.callRegs ls)) rs' := by
  obtain ⟨rs', m', EXEC, SEP', PERMS, AG'⟩ :=
    save_callee_save_rec_correct  rao tge j cs fb sp
      (LTL.undefRegs destroyedAtFunctionEntry (LTL.callRegs ls)) k _ _ _ m P SEP
      (agree_regs_undef_regs _ (agree_regs_call_regs AG))
  refine ⟨rs', m', EXEC, ?_, PERMS, AG'⟩
  refine (sepconj_eqv (contains_callee_saves_exten _ _ _ _ _ _ ?_) (.refl P)).pred.1 SEP'
  intro r hr
  have hcs := (bnds  f).used_callee_save_prop r hr
  rw [LTL_undef_regs_others _ (fun h => by
    have := destroyed_at_function_entry_caller_save
    simp only [NoCalleeSaves] at this
    rw [List.any_eq_false] at this
    exact this r h (by simp [hcs]))]
  exact (AGCS (.R r) hcs).symm

end CALLEE_SAVE2

/-- Stores to the stack frame preserve permissions. -/
theorem storeStack_perm {m : Mem} {a : Val} {ty : ATyp} {ofs : Integers.Ptrofs} {v : Val}
    {m' : Mem} (h : storeStack m a ty ofs v = some m') (b : Block) (i : Z) (k : PermKind)
    (p : Permission) : Mem.perm m' b i k p = Mem.perm m b i k p := by
  unfold storeStack Mem.storev at h
  split at h
  · split at h
    · exact Mem.perm_store h b i k p
    · cases h
  · cases h

private theorem assoc5 {A B C D E R : MAssert} {m : Mem} :
    (m ⊨ (A ** B ** C ** D ** E) ** R) ↔ (m ⊨ A ** B ** C ** D ** E ** R) := by
  refine (sep_assoc _ _ _).pred.trans ?_
  refine (sepconj_eqv (.refl A) (sep_assoc _ _ _)).pred.trans ?_
  refine (sepconj_eqv (.refl A) (sepconj_eqv (.refl B) (sep_assoc _ _ _))).pred.trans ?_
  exact (sepconj_eqv (.refl A) (sepconj_eqv (.refl B) (sepconj_eqv (.refl C)
    (sep_assoc _ _ _)))).pred

section PROLOGUE
variable (rao : Mach.Function → Mach.Code → Integers.Ptrofs → Prop)
  (tge : Mach.CGenv)

/-- `Stackingproof.function_prologue_correct` -/
theorem function_prologue_correct {F V : Type} (ge : Genv F V) {f : Linear.Function}
    {tf : Mach.Function} (TRANSF_F : transfFunction  f = .OK tf)
    (j : Val.Meminj) (ls ls0 ls1 : LTL.Locset) (rs rs1 : Regset) (m1 m1' m2 : Mem) (sp : Block)
    (parent ra : Val) (cs : List Mach.Stackframe) (fb : Block) (k : Mach.Code) (P : MAssert)
    (AGREGS : AgreeRegs j ls rs) (AGCS : AgreeCalleeSave ls ls0)
    (AGARGS : AgreeOutgoingArguments  f.fn_sig ls ls0)
    (LS1 : ls1 = LTL.undefRegs destroyedAtFunctionEntry (LTL.callRegs ls))
    (RS1 : rs1 = Mach.undefRegs destroyedAtFunctionEntry rs)
    (ALLOC : Mem.alloc m1 0 f.fn_stacksize = (m2, sp))
    (TYPAR : Val.HasType parent Tptr) (TYRA : Val.HasType ra Tptr)
    (SEP : m1' ⊨ minjection j m1 ** globalenvInject ge j ** P) :
    ∃ j' rs' m2' sp' m3' m4' m5',
      Mem.alloc m1' 0 tf.fn_stacksize = (m2', sp') ∧
      storeStack m2' (.Vptr sp' Integers.Ptrofs.zero) Tptr tf.fn_link_ofs parent = some m3' ∧
      storeStack m3' (.Vptr sp' Integers.Ptrofs.zero) Tptr tf.fn_retaddr_ofs ra = some m4' ∧
      Smallstep.Star (Mach.Step  rao tge)
        (Mach.State.State cs fb (.Vptr sp' Integers.Ptrofs.zero)
          (saveCalleeSave (fenv  f) k) rs1 m4')
        E0 (Mach.State.State cs fb (.Vptr sp' Integers.Ptrofs.zero) k rs' m5') ∧
      AgreeRegs j' ls1 rs' ∧ AgreeLocs  f ls1 ls0 ∧
      (m5' ⊨ frameContents  f j' sp' ls1 ls0 parent ra ** minjection j' m2 **
        globalenvInject ge j' ** P) ∧
      j' sp = some (sp', (fenv  f).fe_stack_data) ∧ Val.inject_incr j j' := by
  subst LS1 RS1
  have NOOV := size_no_overflow TRANSF_F
  have e := unfold_transf_function TRANSF_F
  subst e
  have LAYOUT1 := frame_env_range (bnds  f)
  have LAYOUT2 := frame_env_aligned (bnds  f)
  have BSD := (bnds  f).bound_stack_data_pos
  rcases hA : Mem.alloc m1' 0 (fenv  f).fe_size with ⟨m2', sp'⟩
  obtain ⟨j', SEP, INCR, SAME⟩ := alloc_parallel_rule_2 (delta := (fenv  f).fe_stack_data)
    (hi := (fenv  f).fe_stack_data + (bnds  f).bound_stack_data)
    SEP ALLOC hA LAYOUT2.2.2.1 rfl (by rw [Int.max_comm]; rfl)
    ⟨by show 0 ≤ (makeEnv (bnds  f)).fe_size; zomega, NOOV⟩ LAYOUT1.1 LAYOUT1.2
  have SEPCONJ := mconj_intro ((sep_assoc _ _ _).pred.2 SEP) ((sep_assoc _ _ _).pred.2 SEP)
  have SEPa := frame_env_separated (bnds  f) sp' m2' _ SEP
  -- store of the parent pointer
  have S1 := (sep_swap3 _ _ _ _).pred.1 SEPa
  have S2 := range_contains (chunk := Mptr) S1 LAYOUT2.2.2.2.1
  obtain ⟨m3', STORE_PARENT, S3⟩ := contains_set_stack (spec := fun v' => v' = parent)
    (ty := Tptr) parent S2 (Val.load_result_same TYPAR)
  have S4 := (sep_swap3 _ _ _ _).pred.2 S3
  -- store of the return address
  have S5 := (sep_swap4 _ _ _ _ _).pred.1 S4
  have S6 := range_contains (chunk := Mptr) S5 LAYOUT2.2.2.2.2
  obtain ⟨m4', STORE_RETADDR, S7⟩ := contains_set_stack (spec := fun v' => v' = ra)
    (ty := Tptr) ra S6 (Val.load_result_same TYRA)
  have S8 := (sep_swap4 _ _ _ _ _).pred.2 S7
  -- saving the callee-save registers
  have S9 := (sep_swap5 _ _ _ _ _ _).pred.1 S8
  obtain ⟨rs2, m5', SAVE_CS, S10, PERMS, AGREGS'⟩ :=
    save_callee_save_correct  rao tge f j' ls ls0 rs sp' cs fb k m4' _ S9 AGCS
      (agree_regs_inject_incr AGREGS INCR)
  have S11 := (sep_swap5 _ _ _ _ _ _).pred.2 S10
  -- materializing the Local and Outgoing locations
  have S12 := initial_locations j' sp' _ _ _ .Local
    (LTL.undefRegs destroyedAtFunctionEntry (LTL.callRegs ls)) m5' S11 LAYOUT2.2.1
    (fun ofs ty => by rw [LTL_undef_regs_slot]; rfl)
  have S13 := (sep_swap _ _ _).pred.1 S12
  have S14 := initial_locations j' sp' _ _ _ .Outgoing
    (LTL.undefRegs destroyedAtFunctionEntry (LTL.callRegs ls)) m5' S13 LAYOUT2.1
    (fun ofs ty => by rw [LTL_undef_regs_slot]; rfl)
  have S15 := (sep_swap _ _ _).pred.1 S14
  have PERM25 : ∀ i k p, Mem.perm m2' sp' i k p = true → Mem.perm m5' sp' i k p = true := by
    intro i k p hp
    apply PERMS
    rw [storeStack_perm STORE_RETADDR, storeStack_perm STORE_PARENT]
    exact hp
  have SEPFINAL : m5' ⊨ frameContents  f j' sp'
      (LTL.undefRegs destroyedAtFunctionEntry (LTL.callRegs ls)) ls0 parent ra **
      minjection j' m2 ** globalenvInject ge j' ** P :=
    frame_mconj SEPCONJ (assoc5.2 S15)
      (sep_preserved (sep_proj1 (mconj_proj2 SEPCONJ))
        (fun h => range_preserved h fun i k p _ _ => PERM25 i k p)
        (fun h => range_preserved h fun i k p _ _ => PERM25 i k p))
  refine ⟨j', rs2, m2', sp', m3', m4', m5', rfl, STORE_PARENT, STORE_RETADDR, SAVE_CS, AGREGS',
    ?_, SEPFINAL, SAME, INCR⟩
  refine agree_locs_undef_locs _ ⟨fun r hr => ?_, fun ofs ty hin => ?_⟩ rfl
  · have hcs : isCalleeSave r = true := by
      cases e : isCalleeSave r
      · exact absurd (caller_save_reg_within_bounds e) hr
      · rfl
    exact AGCS (.R r) hcs
  · exact AGARGS ty ofs (incoming_slot_in_parameters  ofs ty f.fn_sig hin)

end PROLOGUE

section RESTORE_CALLEE_SAVE
variable (rao : Mach.Function → Mach.Code → Integers.Ptrofs → Prop)
  (tge : Mach.CGenv)

/-- `Stackingproof.agree_unused` -/
def AgreeUnused (f : Linear.Function) (j : Val.Meminj) (ls0 : LTL.Locset) (rs : Regset) : Prop :=
  ∀ r, ¬ MregWithinBounds (bnds  f) r → Val.Inject j (ls0 (.R r)) (rs r)

/-- `Stackingproof.restore_callee_save_rec_correct` -/
theorem restore_callee_save_rec_correct (f : Linear.Function) (j : Val.Meminj)
    (cs : List Mach.Stackframe) (fb : Block) (sp : Block) (ls0 : LTL.Locset) (m : Mem) :
    ∀ (l : List Mreg) (ofs : Z) (rs : Regset) (k : Mach.Code),
      m ⊨ containsCalleeSaves j sp ofs l ls0 →
      AgreeUnused  f j ls0 rs →
      (∀ r, r ∈ l → MregWithinBounds (bnds  f) r) →
      ∃ rs',
        Smallstep.Star (Mach.Step  rao tge)
          (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) (restoreCalleeSaveRec l ofs k)
            rs m)
          E0 (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) k rs' m) ∧
        (∀ r, r ∈ l → Val.Inject j (ls0 (.R r)) (rs' r)) ∧
        (∀ r, r ∉ l → rs' r = rs r) ∧
        AgreeUnused  f j ls0 rs'
  | [], _, rs, _, _, AU, _ => ⟨rs, .refl _, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, AU⟩
  | r :: l, ofs, rs, k, h, AU, WB => by
    simp only [containsCalleeSaves] at h
    simp only [restoreCalleeSaveRec]
    have BOUND := WB r List.mem_cons_self
    obtain ⟨v, LOAD, SPEC⟩ := contains_get_stack (sep_proj1 h)
    obtain ⟨rs', A, B, C, D⟩ := restore_callee_save_rec_correct f j cs fb sp ls0 m l _
      (Regset.set r v rs) k (sep_proj2 h)
      (fun r0 hr0 => by
        have hne : r0 ≠ r := fun e => hr0 (e ▸ BOUND)
        rw [Regset.gso _ _ hne]; exact AU r0 hr0)
      (fun r0 hr0 => WB r0 (List.mem_cons_of_mem _ hr0))
    refine ⟨rs', star_left (Mach.Step.Mgetstack _ _ _ _ _ _ _ _ _ _ LOAD) A rfl, ?_, ?_, D⟩
    · intro r0 hr0
      by_cases hl : r0 ∈ l
      · exact B r0 hl
      · have e : r0 = r := by
          rcases List.mem_cons.mp hr0 with e | e
          · exact e
          · exact absurd e hl
        subst e
        rw [C _ hl, Regset.gss]; exact SPEC
    · intro r0 hr0
      simp only [List.mem_cons, not_or] at hr0
      rw [C _ hr0.2, Regset.gso _ _ hr0.1]

/-- `Stackingproof.restore_callee_save_correct` -/
theorem restore_callee_save_correct (f : Linear.Function) (m : Mem) (j : Val.Meminj) (sp : Block)
    (ls ls0 : LTL.Locset) (pa ra : Val) (P : MAssert) (rs : Regset) (k : Mach.Code)
    (cs : List Mach.Stackframe) (fb : Block)
    (h : m ⊨ frameContents  f j sp ls ls0 pa ra ** P) (AU : AgreeUnused  f j ls0 rs) :
    ∃ rs',
      Smallstep.Star (Mach.Step  rao tge)
        (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) (restoreCalleeSave (fenv  f) k)
          rs m)
        E0 (Mach.State.State cs fb (.Vptr sp Integers.Ptrofs.zero) k rs' m) ∧
      (∀ r, isCalleeSave r = true → Val.Inject j (ls0 (.R r)) (rs' r)) ∧
      (∀ r, isCalleeSave r = false → rs' r = rs r) := by
  have h1 := sep_drop (sep_drop (sep_drop (sep_drop (sep_proj1 (mconj_proj1 h)))))
  obtain ⟨rs', A, B, C, _⟩ := restore_callee_save_rec_correct  rao tge f j cs fb sp ls0 m
    (bnds  f).used_callee_save _ rs k h1 AU (fun r hr _ => hr)
  refine ⟨rs', A, fun r hr => ?_, fun r hr => C r fun hin => ?_⟩
  · by_cases hin : r ∈ (bnds  f).used_callee_save
    · exact B r hin
    · rw [C r hin]; exact AU r fun hw => hin (hw hr)
  · have := (bnds  f).used_callee_save_prop r hin
    rw [hr] at this; cases this

/-- `Stackingproof.function_epilogue_correct` -/
theorem function_epilogue_correct {f : Linear.Function} {tf : Mach.Function}
    (TRANSF_F : transfFunction  f = .OK tf) (m' : Mem) (j : Val.Meminj) (sp' : Block)
    (ls ls0 : LTL.Locset) (pa ra : Val) (P : MAssert) (m : Mem) (rs : Regset) (sp : Block)
    (m1 : Mem) (k : Mach.Code) (cs : List Mach.Stackframe) (fb : Block)
    (SEP : m' ⊨ frameContents  f j sp' ls ls0 pa ra ** minjection j m ** P)
    (AGR : AgreeRegs j ls rs) (AGL : AgreeLocs  f ls ls0)
    (INJ : j sp = some (sp', (fenv  f).fe_stack_data))
    (FREE : Mem.free m sp 0 f.fn_stacksize = some m1) :
    ∃ rs1 m1',
      loadStack m' (.Vptr sp' Integers.Ptrofs.zero) Tptr tf.fn_link_ofs = some pa ∧
      loadStack m' (.Vptr sp' Integers.Ptrofs.zero) Tptr tf.fn_retaddr_ofs = some ra ∧
      Mem.free m' sp' 0 tf.fn_stacksize = some m1' ∧
      Smallstep.Star (Mach.Step  rao tge)
        (Mach.State.State cs fb (.Vptr sp' Integers.Ptrofs.zero)
          (restoreCalleeSave (fenv  f) k) rs m')
        E0 (Mach.State.State cs fb (.Vptr sp' Integers.Ptrofs.zero) k rs1 m') ∧
      AgreeRegs j (LTL.returnRegs ls0 ls) rs1 ∧
      AgreeCalleeSave (LTL.returnRegs ls0 ls) ls0 ∧
      m1' ⊨ minjection j m1 ** P := by
  have e := unfold_transf_function TRANSF_F
  subst e
  obtain ⟨m1', FREE', SEP'⟩ := free_parallel_rule ((sep_assoc _ _ _).pred.1 (mconj_proj2 SEP))
    FREE INJ rfl (by rw [Int.max_comm]; rfl)
  obtain ⟨rs', LOAD_CS, CS, NCS⟩ := restore_callee_save_correct  rao tge f m' j sp' ls ls0
    pa ra _ rs k cs fb SEP (fun r hr => by rw [← AGL.agree_unused_reg r hr]; exact AGR r)
  refine ⟨rs', m1', frame_get_parent SEP, frame_get_retaddr SEP, FREE', LOAD_CS, ?_, ?_, SEP'⟩
  · intro r
    simp only [LTL.returnRegs]
    cases hc : isCalleeSave r
    · simp only [Bool.false_eq_true, if_false]; rw [NCS r hc]; exact AGR r
    · simp only [if_true]; exact CS r hc
  · intro l hl
    cases l with
    | R r => simp only [CalleeSaveLoc] at hl; simp [LTL.returnRegs, hl]
    | S sl ofs ty => cases sl <;> simp_all [CalleeSaveLoc, LTL.returnRegs]

end RESTORE_CALLEE_SAVE

end Stackingproof
end RiscV
end CC
