/-
  [x86-64 instance of `CCLib/backend/ValueAnalysisSoundBC.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Soundness of the value analysis, part 2 — port of the constructions of
  block classifications in `backend/ValueAnalysis.v`.

  Ported: `allocate_stack` (construction 1), `anonymize_stack`
  (construction 2), `hide_stack` (construction 3),
  `return_from_public_call` (construction 4), `return_from_private_call`
  (construction 5).

  The block classifications are built with `bcUpdate bc sp c`, which
  reclassifies the single block `sp` (Rocq builds the record `BC f F_stack
  F_glob` by hand each time).
-/
import CCLib.x86.ValueAnalysisSoundBasic

namespace CC
namespace X86
namespace ValueAnalysis

open ValueDomain RTL

/-! ## Reclassifying one block -/

/-- `bc` with block `sp` reclassified as `c` (which is not a global). -/
def bcUpdate (bc : BlockClassification) (sp : Block) (c : BlockClass)
    (hc : ∀ id, c ≠ .BCglob id) (hs : c = .BCstack → ∀ b, b ≠ sp → bc b ≠ .BCstack) :
    BlockClassification where
  bc_img b := if b = sp then c else bc b
  bc_stack b1 b2 h1 h2 := by
    by_cases e1 : b1 = sp <;> by_cases e2 : b2 = sp <;>
      simp only [e1, e2, if_true, if_false] at h1 h2
    · rw [e1, e2]
    · exact absurd h2 (hs h1 b2 e2)
    · exact absurd h1 (hs h2 b1 e1)
    · exact bc.bc_stack b1 b2 h1 h2
  bc_glob b1 b2 id h1 h2 := by
    by_cases e1 : b1 = sp <;> by_cases e2 : b2 = sp <;>
      simp only [e1, e2, if_true, if_false] at h1 h2
    · rw [e1, e2]
    · exact absurd h1 (hc id)
    · exact absurd h2 (hc id)
    · exact bc.bc_glob b1 b2 id h1 h2

section
variable {bc : BlockClassification} {sp : Block} {c : BlockClass} {hc : ∀ id, c ≠ .BCglob id}
  {hs : c = .BCstack → ∀ b, b ≠ sp → bc b ≠ .BCstack}

@[simp] theorem bcUpdate_same : bcUpdate bc sp c hc hs sp = c := by
  show (if sp = sp then c else bc sp) = c
  simp

theorem bcUpdate_other {b : Block} (h : b ≠ sp) : bcUpdate bc sp c hc hs b = bc b := by
  show (if b = sp then c else bc b) = bc b
  simp [h]

end

/-- A pointer matching anything matches `Ptop`. -/
theorem vmatch_ptr_top {bc : BlockClassification} {b : Block} {ofs : Integers.Ptrofs} {x : Aval}
    (h : Vmatch bc (.Vptr b ofs) x) : Pmatch bc b ofs .Ptop := by
  have := vmatch_top h
  cases this
  assumption

/-- Loads from a fresh block read `Undef` bytes. -/
theorem loadbytes_alloc_same {m : Mem} {lo hi : Z} {m' : Mem} {b : Block}
    (ha : Mem.alloc m lo hi = (m', b)) {ofs n : Z} {bytes : List MemVal}
    (hl : Mem.loadbytes m' b ofs n = some bytes) : bytes = List.replicate n.toNat .Undef := by
  have e1 : (Mem.alloc m lo hi).1 = m' := by rw [ha]
  have e2 : (Mem.alloc m lo hi).2 = b := by rw [ha]
  rw [Mem.alloc_result] at e2
  subst e1 e2
  unfold Mem.loadbytes at hl
  split at hl
  · cases hl; exact Mem.getN_alloc_same m lo hi _ _
  · cases hl

/-! ## Construction 1: allocating the stack frame at function entry -/

/-- `ValueAnalysis.allocate_stack` -/
theorem allocate_stack {F V : Type} {m : Mem} {sz : Z} {m' : Mem} {sp : Block}
    {bc : BlockClassification} {ge : Genv F V} {rm : Romem} {am : Amem}
    (ALLOC : Mem.alloc m 0 sz = (m', sp)) (GENV : GenvMatch bc ge) (RO : Romatch bc m rm)
    (MM : Mmatch bc m am) (NOSTACK : BcNostack bc) :
    ∃ bc', bcIncr bc bc' ∧ bc' sp = .BCstack ∧ GenvMatch bc' ge ∧ Romatch bc' m' rm ∧
      Mmatch bc' m' mfunctionEntry ∧ (∀ b, b < sp → bc' b = bc b) ∧
      (∀ v x, Vmatch bc v x → Vmatch bc' v (.Ifptr .Nonstack)) := by
  have e1 : (Mem.alloc m 0 sz).1 = m' := by rw [ALLOC]
  have SP : sp = m.nextblock := by
    have : (Mem.alloc m 0 sz).2 = sp := by rw [ALLOC]
    rw [← this]; rfl
  have NB : m'.nextblock = m.nextblock.succ := by rw [← e1]; rfl
  have VALID : ∀ b, bc b ≠ .BCinvalid → Mem.validBlock m b = true := fun b h =>
    (Mem.validBlock_iff m b).2 (MM.mmatch_below b h)
  have SPINVALID : bc sp = .BCinvalid := by
    apply Classical.byContradiction; intro h
    have := MM.mmatch_below sp h
    rw [SP] at this; exact Nat.lt_irrefl _ this
  let bc' := bcUpdate bc sp .BCstack (by simp) (fun _ b _ => NOSTACK b)
  have BC'EQ : ∀ b, bc b ≠ .BCinvalid → bc' b = bc b := fun b h =>
    bcUpdate_other (by intro e; subst e; exact h SPINVALID)
  have INCR : bcIncr bc bc' := BC'EQ
  have SM : ∀ b p, bc b ≠ .BCinvalid → Smatch bc m b p → Smatch bc' m' b .Nonstack :=
    fun b p hb h => smatch_incr INCR (smatch_inv (smatch_no_stack NOSTACK h)
      (fun ofs n _ => Mem.loadbytes_alloc_unchanged ALLOC (VALID b hb) ofs n))
  have SMSTACK : Smatch bc' m' sp .Pbot := by
    refine ⟨fun chunk ofs v hl => ?_, fun ofs b' ofs' q i hl => ?_⟩
    · obtain ⟨bytes, hb, rfl⟩ := Mem.load_loadbytes hl
      rw [loadbytes_alloc_same ALLOC hb]
      have hpos := sizeChunk_pos chunk
      obtain ⟨k, hk⟩ : ∃ k, (sizeChunk chunk).toNat = k + 1 := ⟨(sizeChunk chunk).toNat - 1, by omega⟩
      rw [hk, List.replicate_succ, decodeVal_undef_cons]
      exact .ifptr_undef _
    · have := loadbytes_alloc_same ALLOC hl
      simp at this
  refine ⟨bc', INCR, bcUpdate_same, ?_, ?_, ?_, ?_, ?_⟩
  · refine genv_match_exten GENV (fun b id => ?_) (fun b h => ?_)
    · by_cases e : b = sp
      · subst e; rw [SPINVALID, bcUpdate_same]; simp
      · rw [bcUpdate_other e]
    · rw [bcUpdate_other (by intro e; subst e; rw [SPINVALID] at h; cases h)]; exact h
  · refine romatch_exten (romatch_alloc ALLOC MM.mmatch_below RO) (fun b id => ?_)
    by_cases e : b = sp
    · subst e; rw [SPINVALID, bcUpdate_same]; simp
    · rw [bcUpdate_other e]
  · refine ⟨fun b hb => ?_, fun id ab b _ hg => ?_, fun b h1 h2 => ?_, fun b hb => ?_, ?_⟩
    · by_cases e : b = sp
      · subst e; exact ablock_init_sound SMSTACK
      · rw [bcUpdate_other e] at hb; exact absurd hb (NOSTACK b)
    · simp [mfunctionEntry] at hg
    · have e : b ≠ sp := by intro e; subst e; exact h1 bcUpdate_same
      rw [bcUpdate_other e] at h1 h2
      exact SM b _ h2 (MM.mmatch_nonstack b h1 h2)
    · by_cases e : b = sp
      · subst e; exact smatch_ge SMSTACK (.bot _)
      · rw [bcUpdate_other e] at hb
        exact SM b _ hb (MM.mmatch_top b hb)
    · intro b hb
      show b.toNat < m'.nextblock.toNat
      rw [NB, Positive.toNat_succ]
      by_cases e : b = sp
      · subst e; rw [SP]; exact Nat.lt_succ_self _
      · rw [bcUpdate_other e] at hb
        exact Nat.lt_succ_of_lt (MM.mmatch_below b hb)
  · intro b hb
    exact bcUpdate_other (by intro e; subst e; exact Nat.lt_irrefl _ hb)
  · intro v x h
    exact vmatch_incr INCR (vmatch_no_stack NOSTACK h)

/-! ## Construction 2: turn the stack into an "other" block -/

/-- `ValueAnalysis.anonymize_stack` -/
theorem anonymize_stack {F V : Type} {m : Mem} {sp : Block} {bc : BlockClassification}
    {ge : Genv F V} {rm : Romem} {am : Amem}
    (GENV : GenvMatch bc ge) (RO : Romatch bc m rm) (MM : Mmatch bc m am)
    (SP : bc sp = .BCstack) :
    ∃ bc', BcNostack bc' ∧ bc' sp = .BCother ∧ (∀ b, b ≠ sp → bc' b = bc b) ∧
      (∀ v x, Vmatch bc v x → Vmatch bc' v Vtop) ∧ GenvMatch bc' ge ∧ Romatch bc' m rm ∧
      Mmatch bc' m mtop := by
  let bc' := bcUpdate bc sp .BCother (by simp) (by simp)
  have NOSTACK : BcNostack bc' := by
    intro b hb
    by_cases e : b = sp
    · subst e; rw [bcUpdate_same] at hb; cases hb
    · rw [bcUpdate_other e] at hb; exact e (bc.bc_stack b sp hb SP)
  have PM : ∀ b ofs p, Pmatch bc b ofs p → Pmatch bc' b ofs .Ptop := by
    intro b ofs p h
    have h' := pmatch_top' h
    cases h' with
    | top hb =>
      refine .top ?_
      by_cases e : b = sp
      · subst e; rw [bcUpdate_same]; simp
      · rw [bcUpdate_other e]; exact hb
  have VM : ∀ v x, Vmatch bc v x → Vmatch bc' v Vtop := fun v x h =>
    vmatch_ifptr _ _ (fun b ofs he => by subst he; exact PM _ _ _ (vmatch_ptr_top h))
  have SM : ∀ b p, Smatch bc m b p → Smatch bc' m b .Ptop := fun b p h =>
    ⟨fun chunk ofs v hl => VM _ _ (h.1 chunk ofs v hl),
     fun ofs b' ofs' q i hl => PM _ _ _ (h.2 ofs b' ofs' q i hl)⟩
  refine ⟨bc', NOSTACK, bcUpdate_same, fun b e => bcUpdate_other e, VM, ?_, ?_, ?_⟩
  · refine genv_match_exten GENV (fun b id => ?_) (fun b h => ?_)
    · by_cases e : b = sp
      · subst e; rw [SP, bcUpdate_same]; simp
      · rw [bcUpdate_other e]
    · by_cases e : b = sp
      · subst e; exact bcUpdate_same
      · rw [bcUpdate_other e]; exact h
  · refine romatch_exten RO (fun b id => ?_)
    by_cases e : b = sp
    · subst e; rw [SP, bcUpdate_same]; simp
    · rw [bcUpdate_other e]
  · refine ⟨fun b hb => absurd hb (NOSTACK b), fun id ab b _ hg => ?_, fun b h1 h2 => ?_,
      fun b hb => ?_, ?_⟩
    · simp [mtop, minit] at hg
    · by_cases e : b = sp
      · subst e; exact SM _ _ (MM.mmatch_stack _ SP).1
      · rw [bcUpdate_other e] at h1 h2
        exact SM _ _ (MM.mmatch_nonstack b h1 h2)
    · by_cases e : b = sp
      · subst e; exact SM _ _ (MM.mmatch_stack _ SP).1
      · rw [bcUpdate_other e] at hb
        exact SM _ _ (MM.mmatch_top b hb)
    · intro b hb
      by_cases e : b = sp
      · subst e; exact MM.mmatch_below _ (by rw [SP]; simp)
      · rw [bcUpdate_other e] at hb; exact MM.mmatch_below b hb

/-! ## Construction 3: turn the stack into an invalid block -/

/-- `ValueAnalysis.hide_stack` -/
theorem hide_stack {F V : Type} {m : Mem} {sp : Block} {bc : BlockClassification}
    {ge : Genv F V} {rm : Romem} {am : Amem}
    (GENV : GenvMatch bc ge) (RO : Romatch bc m rm) (MM : Mmatch bc m am)
    (SP : bc sp = .BCstack) (NOLEAK : Pge .Nonstack am.am_nonstack) :
    ∃ bc', BcNostack bc' ∧ bc' sp = .BCinvalid ∧ (∀ b, b ≠ sp → bc' b = bc b) ∧
      (∀ v x, Vge (.Ifptr .Nonstack) x → Vmatch bc v x → Vmatch bc' v Vtop) ∧
      GenvMatch bc' ge ∧ Romatch bc' m rm ∧ Mmatch bc' m mtop := by
  let bc' := bcUpdate bc sp .BCinvalid (by simp) (by simp)
  have NOSTACK : BcNostack bc' := by
    intro b hb
    by_cases e : b = sp
    · subst e; rw [bcUpdate_same] at hb; cases hb
    · rw [bcUpdate_other e] at hb; exact e (bc.bc_stack b sp hb SP)
  have PM' : ∀ b ofs, Pmatch bc b ofs .Nonstack → Pmatch bc' b ofs .Ptop := by
    intro b ofs h
    cases h with
    | nonstack h1 h2 =>
      have e : b ≠ sp := by intro e; subst e; exact h1 SP
      exact .top (by rw [bcUpdate_other e]; exact h2)
  have PM : ∀ b ofs p, Pge .Nonstack p → Pmatch bc b ofs p → Pmatch bc' b ofs .Ptop :=
    fun b ofs p hp h => PM' b ofs (pmatch_ge hp h)
  have VM : ∀ v x, Vge (.Ifptr .Nonstack) x → Vmatch bc v x → Vmatch bc' v Vtop := by
    intro v x hx h
    have h' := vmatch_ge hx h
    refine vmatch_ifptr _ _ (fun b ofs he => ?_)
    subst he
    cases h' with
    | ifptr_p _ _ _ hp => exact PM' _ _ hp
  have SM : ∀ b p, Pge .Nonstack p → Smatch bc m b p → Smatch bc' m b .Ptop := fun b p hp h =>
    ⟨fun chunk ofs v hl => VM _ (.Ifptr p) (.ip_ip _ _ hp) (h.1 chunk ofs v hl),
     fun ofs b' ofs' q i hl => PM _ _ _ hp (h.2 ofs b' ofs' q i hl)⟩
  refine ⟨bc', NOSTACK, bcUpdate_same, fun b e => bcUpdate_other e, VM, ?_, ?_, ?_⟩
  · refine genv_match_exten GENV (fun b id => ?_) (fun b h => ?_)
    · by_cases e : b = sp
      · subst e; rw [SP, bcUpdate_same]; simp
      · rw [bcUpdate_other e]
    · have e : b ≠ sp := by intro e; subst e; rw [SP] at h; cases h
      rw [bcUpdate_other e]; exact h
  · refine romatch_exten RO (fun b id => ?_)
    by_cases e : b = sp
    · subst e; rw [SP, bcUpdate_same]; simp
    · rw [bcUpdate_other e]
  · refine ⟨fun b hb => absurd hb (NOSTACK b), fun id ab b _ hg => ?_, fun b h1 h2 => ?_,
      fun b hb => ?_, ?_⟩
    · simp [mtop, minit] at hg
    · have e : b ≠ sp := by intro e; subst e; exact h2 bcUpdate_same
      rw [bcUpdate_other e] at h1 h2
      exact SM _ _ NOLEAK (MM.mmatch_nonstack b h1 h2)
    · have e : b ≠ sp := by intro e; subst e; exact hb bcUpdate_same
      rw [bcUpdate_other e] at hb
      exact SM _ _ NOLEAK (MM.mmatch_nonstack b (fun h => e (bc.bc_stack b sp h SP)) hb)
    · intro b hb
      have e : b ≠ sp := by intro e; subst e; exact hb bcUpdate_same
      rw [bcUpdate_other e] at hb; exact MM.mmatch_below b hb

/-! ## Construction 4: restore the stack after a public call -/

/-- `ValueAnalysis.return_from_public_call` -/
theorem return_from_public_call {F V : Type} {caller callee : BlockClassification} {bound sp : Block}
    {ge : Genv F V} {e : RTL.Regset} {ae : Aenv} {v : Val} {m : Mem} {rm : Romem}
    (BELOW : bcBelow caller bound) (SP1 : callee sp = .BCother) (SP2 : caller sp = .BCstack)
    (SAME : ∀ b, b < bound → b ≠ sp → caller b = callee b) (GE1 : GenvMatch caller ge)
    (EM : Ematch caller e ae) (RESM : Vmatch callee v Vtop)
    (RM : Romatch callee m rm) (MM : Mmatch callee m mtop) (GE2 : GenvMatch callee ge)
    (NOSTACK : BcNostack callee) :
    ∃ bc, Vmatch bc v Vtop ∧ Ematch bc e ae ∧ Romatch bc m rm ∧
      Mmatch bc m mafterPublicCall ∧ GenvMatch bc ge ∧ bc sp = .BCstack ∧
      (∀ b, b < sp → bc b = caller b) := by
  let bc := bcUpdate callee sp .BCstack (by simp) (fun _ b _ => NOSTACK b)
  have INCR : bcIncr caller bc := by
    intro b hb
    by_cases e : b = sp
    · subst e; rw [bcUpdate_same, SP2]
    · rw [bcUpdate_other e]; exact (SAME b (BELOW b hb) e).symm
  have PM : ∀ b ofs p, Pmatch callee b ofs p → Pmatch bc b ofs .Ptop := by
    intro b ofs p h
    cases pmatch_top' h with
    | top hb =>
      refine .top ?_
      by_cases e : b = sp
      · subst e; rw [bcUpdate_same]; simp
      · rw [bcUpdate_other e]; exact hb
  have VM : ∀ v x, Vmatch callee v x → Vmatch bc v Vtop := fun v x h =>
    vmatch_ifptr _ _ (fun b ofs he => by subst he; exact PM _ _ _ (vmatch_ptr_top h))
  have SM : ∀ b p, Smatch callee m b p → Smatch bc m b .Ptop := fun b p h =>
    ⟨fun chunk ofs v hl => VM _ _ (h.1 chunk ofs v hl),
     fun ofs b' ofs' q i hl => PM _ _ _ (h.2 ofs b' ofs' q i hl)⟩
  have SPB : sp < bound := BELOW sp (by rw [SP2]; simp)
  refine ⟨bc, VM _ _ RESM, ematch_incr EM INCR, ?_, ?_, ?_, bcUpdate_same, ?_⟩
  · refine romatch_exten RM (fun b id => ?_)
    by_cases e : b = sp
    · subst e; rw [SP1, bcUpdate_same]; simp
    · rw [bcUpdate_other e]
  · refine ⟨fun b hb => ?_, fun id ab b _ hg => ?_, fun b h1 h2 => ?_, fun b hb => ?_, ?_⟩
    · by_cases e : b = sp
      · subst e
        exact ablock_init_sound (SM _ _ (MM.mmatch_nonstack _ (by rw [SP1]; simp) (by rw [SP1]; simp)))
      · rw [bcUpdate_other e] at hb; exact absurd hb (NOSTACK b)
    · simp [mafterPublicCall, mtop, minit] at hg
    · have e : b ≠ sp := by intro e; subst e; exact h1 bcUpdate_same
      rw [bcUpdate_other e] at h1 h2
      exact SM _ _ (MM.mmatch_nonstack b h1 h2)
    · refine SM _ _ (MM.mmatch_top b ?_)
      by_cases e : b = sp
      · subst e; rw [SP1]; simp
      · rw [bcUpdate_other e] at hb; exact hb
    · intro b hb
      by_cases e : b = sp
      · subst e; exact MM.mmatch_below _ (by rw [SP1]; simp)
      · rw [bcUpdate_other e] at hb; exact MM.mmatch_below b hb
  · refine genv_match_exten GE1 (fun b id => ?_) (fun b h => ?_)
    · by_cases e : b = sp
      · subst e; rw [SP2, bcUpdate_same]
      · rw [bcUpdate_other e]
        constructor
        · intro h
          rw [← SAME b (BELOW b (by rw [h]; simp)) e]; exact h
        · intro h
          exact (GE1.1 id b).1 ((GE2.1 id b).2 h)
    · have e : b ≠ sp := by intro e; subst e; rw [SP2] at h; cases h
      rw [bcUpdate_other e, ← SAME b (BELOW b (by rw [h]; simp)) e]; exact h
  · intro b hb
    have e : b ≠ sp := by intro e; subst e; exact Nat.lt_irrefl _ hb
    rw [bcUpdate_other e]
    exact (SAME b (Nat.lt_trans hb SPB) e).symm

/-! ## Construction 5: restore the stack after a private call -/

/-- `ValueAnalysis.return_from_private_call` -/
theorem return_from_private_call {F V : Type} {caller callee : BlockClassification}
    {bound sp : Block} {ge : Genv F V} {e : RTL.Regset} {ae : Aenv} {v : Val} {m : Mem}
    {rm : Romem} {am : Amem}
    (BELOW : bcBelow caller bound) (SP1 : callee sp = .BCinvalid) (SP2 : caller sp = .BCstack)
    (SAME : ∀ b, b < bound → b ≠ sp → caller b = callee b)
    (EM : Ematch caller e ae) (CONTENTS : Bmatch caller m sp am.am_stack)
    (BOUND : bound ≤ m.nextblock) (RESM : Vmatch callee v Vtop)
    (RM : Romatch callee m rm) (MM : Mmatch callee m mtop) (GE2 : GenvMatch callee ge)
    (NOSTACK : BcNostack callee) :
    ∃ bc, Vmatch bc v (.Ifptr .Nonstack) ∧ Ematch bc e ae ∧ Romatch bc m rm ∧
      Mmatch bc m (mafterPrivateCall am) ∧ GenvMatch bc ge ∧ bc sp = .BCstack ∧
      (∀ b, b < sp → bc b = caller b) := by
  let bc := bcUpdate callee sp .BCstack (by simp) (fun _ b _ => NOSTACK b)
  have INCR1 : bcIncr caller bc := by
    intro b hb
    by_cases e : b = sp
    · subst e; rw [bcUpdate_same, SP2]
    · rw [bcUpdate_other e]; exact (SAME b (BELOW b hb) e).symm
  have INCR2 : bcIncr callee bc := by
    intro b hb
    have e : b ≠ sp := by intro e; subst e; exact hb SP1
    exact bcUpdate_other e
  have PM : ∀ b ofs p, Pmatch callee b ofs p → Pmatch bc b ofs .Nonstack := by
    intro b ofs p h
    cases pmatch_top' h with
    | top hb =>
      have e : b ≠ sp := by intro e; subst e; exact hb SP1
      exact .nonstack (by rw [bcUpdate_other e]; exact NOSTACK b) (by rw [bcUpdate_other e]; exact hb)
  have VM : ∀ v x, Vmatch callee v x → Vmatch bc v (.Ifptr .Nonstack) := fun v x h =>
    vmatch_ifptr _ _ (fun b ofs he => by subst he; exact PM _ _ _ (vmatch_ptr_top h))
  have SM : ∀ b p, Smatch callee m b p → Smatch bc m b .Nonstack := fun b p h =>
    ⟨fun chunk ofs v hl => VM _ _ (h.1 chunk ofs v hl),
     fun ofs b' ofs' q i hl => PM _ _ _ (h.2 ofs b' ofs' q i hl)⟩
  have BSTK : Bmatch bc m sp am.am_stack := bmatch_incr INCR1 CONTENTS
  have SPB : sp < bound := BELOW sp (by rw [SP2]; simp)
  refine ⟨bc, VM _ _ RESM, ematch_incr EM INCR1, ?_, ?_, ?_, bcUpdate_same, ?_⟩
  · refine romatch_exten RM (fun b id => ?_)
    by_cases e : b = sp
    · subst e; rw [SP1, bcUpdate_same]; simp
    · rw [bcUpdate_other e]
  · refine ⟨fun b hb => ?_, fun id ab b _ hg => ?_, fun b h1 h2 => ?_, fun b hb => ?_, ?_⟩
    · by_cases e : b = sp
      · subst e; exact BSTK
      · rw [bcUpdate_other e] at hb; exact absurd hb (NOSTACK b)
    · simp [mafterPrivateCall] at hg
    · have e : b ≠ sp := by intro e; subst e; exact h1 bcUpdate_same
      rw [bcUpdate_other e] at h1 h2
      exact SM _ _ (MM.mmatch_nonstack b h1 h2)
    · by_cases e : b = sp
      · subst e; exact smatch_ge BSTK.1 (pge_lub_l _ _)
      · rw [bcUpdate_other e] at hb
        exact smatch_ge (SM _ _ (MM.mmatch_top b hb)) (pge_lub_r _ _)
    · intro b hb
      by_cases e : b = sp
      · subst e; exact Nat.lt_of_lt_of_le SPB BOUND
      · rw [bcUpdate_other e] at hb; exact MM.mmatch_below b hb
  · refine genv_match_exten GE2 (fun b id => ?_) (fun b h => ?_)
    · by_cases e : b = sp
      · subst e; rw [SP1, bcUpdate_same]; simp
      · rw [bcUpdate_other e]
    · have e : b ≠ sp := by intro e; subst e; rw [SP1] at h; cases h
      rw [bcUpdate_other e]; exact h
  · intro b hb
    have e : b ≠ sp := by intro e; subst e; exact Nat.lt_irrefl _ hb
    rw [bcUpdate_other e]
    exact (SAME b (Nat.lt_trans hb SPB) e).symm

end ValueAnalysis
end X86
end CC
