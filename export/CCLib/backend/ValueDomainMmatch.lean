/-
  Soundness of the abstract memory states of the value analysis — port of
  the `romatch` / `mmatch` part of `backend/ValueDomain.v` (from
  `romatch_store` to the end of section `MATCH`, plus the nonaliasing test
  `pdisjoint`, the `bc_incr` lemmas and `ematch`).

  Ported: `romatch_store`, `romatch_storebytes`, `romatch_ext`,
  `romatch_free`, `romatch_alloc`, `load_sound`, `loadv_sound`,
  `store_sound`, `storev_sound`, `loadbytes_sound`, `storebytes_sound`,
  `mmatch_ext`, `mmatch_free`, `mmatch_top'`, `mbeq_sound`, `mmatch_lub_l`,
  `mmatch_lub_r`.

  From `common/Memory.v`: `loadbytes_store_other`, `loadbytes_free_2`,
  `loadbytes_alloc_unchanged`.
-/
import CCLib.backend.ValueDomainMemProof
import CCLib.common.MemoryUnchanged

namespace CC

namespace Mem

/-- `Mem.loadbytes_store_other` -/
theorem loadbytes_store_other {chunk : Chunk} {m : Mem} {b : Block} {ofs : _root_.Int} {v : Val}
    {m' : Mem} (h : store chunk m b ofs v = some m') (b' : Block) (ofs' n : _root_.Int)
    (hdisj : b' ≠ b ∨ n ≤ 0 ∨ ofs' + n ≤ ofs ∨ ofs + sizeChunk chunk ≤ ofs') :
    loadbytes m' b' ofs' n = loadbytes m b' ofs' n := by
  have hs := store_storebytes h
  rcases hdisj with h1 | h1 | h1
  · exact loadbytes_storebytes_other hs b' ofs' n (.inl h1)
  · unfold loadbytes
    have e : n.toNat = 0 := by omega
    rw [e]
    have r1 : rangePerm m' b' ofs' (ofs' + n) .Cur .Readable = true :=
      rangePerm_intro _ _ _ _ _ _ (fun o h2 h3 => by omega)
    have r2 : rangePerm m b' ofs' (ofs' + n) .Cur .Readable = true :=
      rangePerm_intro _ _ _ _ _ _ (fun o h2 h3 => by omega)
    rw [if_pos r1, if_pos r2]; rfl
  · refine loadbytes_storebytes_other hs b' ofs' n (.inr ?_)
    rw [length_encodeVal, sizeChunkNat_cast]; exact h1

/-- `Mem.loadbytes_free_2` -/
theorem loadbytes_free_2 {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (h : free m b lo hi = some m') {b' : Block} {ofs n : _root_.Int} {bytes : List MemVal}
    (hl : loadbytes m' b' ofs n = some bytes) : loadbytes m b' ofs n = some bytes := by
  rw [free_result h] at hl
  unfold loadbytes at hl ⊢
  split at hl
  · rename_i hr
    rw [if_pos (rangePerm_intro _ _ _ _ _ _ (fun o h1 h2 =>
      perm_free_3 (rangePerm_perm _ _ _ _ _ _ hr o h1 h2)))]
    exact hl
  · cases hl

/-- `Mem.loadbytes_alloc_unchanged` -/
theorem loadbytes_alloc_unchanged {m : Mem} {lo hi : Z} {m' : Mem} {b : Block}
    (ha : alloc m lo hi = (m', b)) {b' : Block} (hv : validBlock m b' = true)
    (ofs n : _root_.Int) : loadbytes m' b' ofs n = loadbytes m b' ofs n := by
  have U : UnchangedOn (fun _ _ => True) m m' := alloc_unchangedOn ha
  by_cases hl : ∃ bytes, loadbytes m b' ofs n = some bytes
  · obtain ⟨bytes, hl⟩ := hl
    rw [hl, U.loadbytes (fun _ _ _ => trivial) hl]
  · have e : loadbytes m b' ofs n = none := by
      cases h : loadbytes m b' ofs n
      · rfl
      · exact absurd ⟨_, h⟩ hl
    rw [e, U.loadbytes_1 hv (fun _ _ _ => trivial), e]

end Mem

namespace ValueDomain

variable {bc : BlockClassification}

/-! ## Read-only memory -/

/-- `ValueDomain.romatch_store` -/
theorem romatch_store {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    {rm : Romem} (hs : Mem.store chunk m b ofs v = some m') (hr : Romatch bc m rm) :
    Romatch bc m' rm := by
  intro b0 id ab hb0 hrm
  obtain ⟨A, B, C⟩ := hr b0 id ab hb0 hrm
  have hne : b0 ≠ b := by
    intro he; subst he
    have hva := Mem.store_valid_access_3 hs
    simp only [Mem.validAccess, Bool.and_eq_true] at hva
    have hp := Mem.rangePerm_perm _ _ _ _ _ _ hva.1 ofs (Int.le_refl _)
      (by have := sizeChunk_pos chunk; omega)
    have := C ofs
    rw [Mem.perm_cur_max hp] at this; cases this
  refine ⟨A, bmatch_inv B (fun o n _ => Mem.loadbytes_store_other hs _ _ _ (.inl hne)), ?_⟩
  intro o
  rw [Mem.perm_store hs]; exact C o

/-- `ValueDomain.romatch_storebytes` -/
theorem romatch_storebytes {m : Mem} {b : Block} {ofs : _root_.Int} {bytes : List MemVal} {m' : Mem}
    {rm : Romem} (hs : Mem.storebytes m b ofs bytes = some m') (hr : Romatch bc m rm) :
    Romatch bc m' rm := by
  intro b0 id ab hb0 hrm
  obtain ⟨A, B, C⟩ := hr b0 id ab hb0 hrm
  refine ⟨A, bmatch_inv B (fun o n _ => ?_), fun o => by rw [Mem.perm_storebytes hs]; exact C o⟩
  by_cases hne : b0 = b
  · subst hne
    by_cases hlen : bytes.length = 0
    · have U := Mem.storebytes_unchangedOn (P := fun _ _ => True) hs (fun i h1 h2 => by omega)
      cases hl : Mem.loadbytes m b0 o n with
      | some bytes' => exact U.loadbytes (fun _ _ _ => trivial) hl
      | none =>
        unfold Mem.loadbytes at hl ⊢
        rw [Mem.rangePerm_congr (fun o => Mem.perm_storebytes hs _ o .Cur .Readable)]
        split at hl <;> simp_all
    · have hr := Mem.storebytes_range_perm hs
      have hp := Mem.rangePerm_perm _ _ _ _ _ _ hr ofs (Int.le_refl _)
        (by have h0 : (0 : _root_.Int) < bytes.length := by exact_mod_cast Nat.pos_of_ne_zero hlen
            exact Int.lt_add_of_pos_right _ h0)
      have := C ofs
      rw [Mem.perm_cur_max hp] at this; cases this
  · exact Mem.loadbytes_storebytes_other hs _ _ _ (.inl hne)

/-- `ValueDomain.romatch_ext` -/
theorem romatch_ext {m : Mem} {rm : Romem} {m' : Mem} (hr : Romatch bc m rm)
    (H1 : ∀ b id ofs n bytes, bc b = .BCglob id → Mem.loadbytes m' b ofs n = some bytes →
      Mem.loadbytes m b ofs n = some bytes)
    (H2 : ∀ b id ofs p, bc b = .BCglob id → Mem.perm m' b ofs .Max p = true →
      Mem.perm m b ofs .Max p = true) :
    Romatch bc m' rm := by
  intro b id ab hb hrm
  obtain ⟨A, B, C⟩ := hr b id ab hb hrm
  refine ⟨A, bmatch_ext B (fun ofs n bytes hl _ => H1 b id ofs n bytes hb hl), fun ofs => ?_⟩
  cases hp : Mem.perm m' b ofs .Max .Writable
  · rfl
  · have := H2 b id ofs _ hb hp
    rw [C ofs] at this; cases this

/-- `ValueDomain.romatch_free` -/
theorem romatch_free {m : Mem} {b : Block} {lo hi : Z} {m' : Mem} {rm : Romem}
    (hf : Mem.free m b lo hi = some m') (hr : Romatch bc m rm) : Romatch bc m' rm :=
  romatch_ext hr (fun _ _ _ _ _ _ hl => Mem.loadbytes_free_2 hf hl)
    (fun _ _ _ _ _ hp => by rw [Mem.free_result hf] at hp; exact Mem.perm_free_3 hp)

/-- `ValueDomain.romatch_alloc` -/
theorem romatch_alloc {m : Mem} {lo hi : Z} {m' : Mem} {b : Block} {rm : Romem}
    (ha : Mem.alloc m lo hi = (m', b)) (hbelow : bcBelow bc m.nextblock)
    (hr : Romatch bc m rm) : Romatch bc m' rm := by
  have e1 : (Mem.alloc m lo hi).1 = m' := by rw [ha]
  have hvalid : ∀ b0 id, bc b0 = .BCglob id → Mem.validBlock m b0 = true := by
    intro b0 id h
    have := hbelow b0 (by rw [h]; simp)
    simpa [Mem.validBlock] using this
  refine romatch_ext hr (fun b0 id ofs n bytes hb hl => ?_) (fun b0 id ofs p hb hp => ?_)
  · rw [← hl]; exact (Mem.loadbytes_alloc_unchanged ha (hvalid b0 id hb) ofs n).symm
  · have hne : b0 ≠ m.nextblock := by
      intro he; have := hvalid b0 id hb; subst he
      simp [Mem.validBlock, Positive.lt_iff] at this
    rw [← e1, Mem.perm_alloc_other m lo hi b0 hne] at hp; exact hp

/-! ## Abstract loads and stores -/

/-- `ValueDomain.load_sound` -/
theorem load_sound (strict : Bool) {chunk : Chunk} {m : Mem} {b : Block} {ofs : Integers.Ptrofs}
    {v : Val} {rm : Romem} {am : Amem} {p : Aptr}
    (hl : Mem.load chunk m b (Integers.Ptrofs.unsigned ofs) = some v)
    (hr : Romatch bc m rm) (hm : Mmatch bc m am) (hp : Pmatch bc b ofs p) :
    Vmatch bc v (load strict chunk rm am p) := by
  cases hp with
  | gl id h =>
    have NS := hm.mmatch_nonstack b (by rw [h]; simp) (by rw [h]; simp)
    simp only [load]
    split
    · rename_i ab hrm; exact ablock_load_sound hl (hr b id ab h hrm).2.1
    · split
      · rename_i ab hg; exact ablock_load_sound hl (hm.mmatch_glob id ab b h hg)
      · exact vnormalize_cast hl (NS.1 _ _ _ hl)
  | glo id h =>
    have NS := hm.mmatch_nonstack b (by rw [h]; simp) (by rw [h]; simp)
    simp only [load]
    split
    · rename_i ab hrm; exact ablock_load_anywhere_sound hl (hr b id ab h hrm).2.1
    · split
      · rename_i ab hg; exact ablock_load_anywhere_sound hl (hm.mmatch_glob id ab b h hg)
      · exact vnormalize_cast hl (NS.1 _ _ _ hl)
  | glob id h =>
    have NS := hm.mmatch_nonstack b (by rw [h]; simp) (by rw [h]; simp)
    exact vnormalize_cast hl (NS.1 _ _ _ hl)
  | stk h => exact ablock_load_sound hl (hm.mmatch_stack b h)
  | stack h => exact ablock_load_anywhere_sound hl (hm.mmatch_stack b h)
  | nonstack h1 h2 => exact vnormalize_cast hl ((hm.mmatch_nonstack b h1 h2).1 _ _ _ hl)
  | top h => exact vnormalize_cast hl ((hm.mmatch_top b h).1 _ _ _ hl)

/-- `ValueDomain.loadv_sound` -/
theorem loadv_sound (strict : Bool) {chunk : Chunk} {m : Mem} {addr v : Val} {rm : Romem}
    {am : Amem} {aaddr : Aval} (hl : Mem.loadv chunk m addr = some v)
    (hr : Romatch bc m rm) (hm : Mmatch bc m am) (ha : Vmatch bc addr aaddr) :
    Vmatch bc v (loadv strict chunk rm am aaddr) := by
  cases addr with
  | Vptr b ofs =>
    simp only [Mem.loadv] at hl
    split at hl
    · exact load_sound strict hl hr hm (match_aptr_of_aval strict ha)
    · cases hl
  | _ => cases hl

theorem bmatch_globBlock {m : Mem} {am : Amem} {b : Block} {id : Ident} (hm : Mmatch bc m am)
    (h : bc b = .BCglob id) : Bmatch bc m b (globBlock am id) := by
  unfold globBlock
  split
  · rename_i ab hg; exact hm.mmatch_glob id ab b h hg
  · exact ablock_init_sound (hm.mmatch_nonstack b (by rw [h]; simp) (by rw [h]; simp))

/-- `ValueDomain.store_sound` -/
theorem store_sound {chunk : Chunk} {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {v : Val}
    {m' : Mem} {am : Amem} {p : Aptr} {av : Aval}
    (hs : Mem.store chunk m b (Integers.Ptrofs.unsigned ofs) v = some m')
    (hm : Mmatch bc m am) (hp : Pmatch bc b ofs p) (hv : Vmatch bc v av) :
    Mmatch bc m' (store chunk am p av) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b0 hb0
    have DFL : bc b ≠ .BCstack → Bmatch bc m' b0 am.am_stack := fun hne =>
      bmatch_inv (hm.mmatch_stack b0 hb0) (fun o n _ =>
        Mem.loadbytes_store_other hs _ _ _ (.inl (by intro e; subst e; exact hne hb0)))
    cases hp with
    | stk h =>
      have := bc.bc_stack b0 b hb0 h; subst this
      exact ablock_store_sound hs (hm.mmatch_stack _ hb0) hv
    | stack h =>
      have := bc.bc_stack b0 b hb0 h; subst this
      exact ablock_store_anywhere_sound hs (hm.mmatch_stack _ hb0) hv
    | top h => exact ablock_store_anywhere_sound hs (hm.mmatch_stack _ hb0) hv
    | gl id h => exact DFL (by rw [h]; simp)
    | glo id h => exact DFL (by rw [h]; simp)
    | glob id h => exact DFL (by rw [h]; simp)
    | nonstack h1 h2 => exact DFL h1
  · intro id ab b' hb' hg
    have DFL : bc b ≠ .BCglob id → am.am_glob.get id = some ab → Bmatch bc m' b' ab :=
      fun hne hg' => bmatch_inv (hm.mmatch_glob id ab b' hb' hg') (fun o n _ =>
        Mem.loadbytes_store_other hs _ _ _ (.inl (by intro e; subst e; exact hne hb')))
    cases hp with
    | gl id0 h =>
      dsimp only [store] at hg
      rw [PTree.gsspec] at hg
      split at hg
      · rename_i he; subst he; cases hg
        have := bc.bc_glob b' b id hb' h; subst this
        exact ablock_store_sound hs (bmatch_globBlock hm h) hv
      · rename_i hne; exact DFL (by rw [h]; simp [Ne.symm hne]) hg
    | glo id0 h =>
      dsimp only [store] at hg
      rw [PTree.gsspec] at hg
      split at hg
      · rename_i he; subst he; cases hg
        have := bc.bc_glob b' b id hb' h; subst this
        exact ablock_store_anywhere_sound hs (bmatch_globBlock hm h) hv
      · rename_i hne; exact DFL (by rw [h]; simp [Ne.symm hne]) hg
    | glob id0 h => dsimp only [store] at hg; rw [PTree.gempty] at hg; cases hg
    | nonstack h1 h2 => dsimp only [store] at hg; rw [PTree.gempty] at hg; cases hg
    | top h => dsimp only [store] at hg; rw [PTree.gempty] at hg; cases hg
    | stk h => exact DFL (by rw [h]; simp) hg
    | stack h => exact DFL (by rw [h]; simp) hg
  · intro b0 h1 h2
    have DFL : Smatch bc m' b0 (vplub av am.am_nonstack) :=
      smatch_store hs (hm.mmatch_nonstack b0 h1 h2) hv
    have STK : bc b = .BCstack → Smatch bc m' b0 am.am_nonstack := fun hb =>
      smatch_inv (hm.mmatch_nonstack b0 h1 h2) (fun o n _ =>
        Mem.loadbytes_store_other hs _ _ _ (.inl (by intro e; subst e; exact h1 hb)))
    cases hp <;> first | exact DFL | (apply STK; assumption)
  · intro b0 h
    exact smatch_store hs (hm.mmatch_top b0 h) hv
  · show bcBelow bc m'.nextblock
    rw [Mem.store_nextblock hs]; exact hm.mmatch_below

/-- `ValueDomain.storev_sound` -/
theorem storev_sound (strict : Bool) {chunk : Chunk} {m : Mem} {addr v : Val} {m' : Mem}
    {am : Amem} {aaddr av : Aval} (hs : Mem.storev chunk m addr v = some m')
    (hm : Mmatch bc m am) (ha : Vmatch bc addr aaddr) (hv : Vmatch bc v av) :
    Mmatch bc m' (storev strict chunk am aaddr av) := by
  cases addr with
  | Vptr b ofs =>
    simp only [Mem.storev] at hs
    split at hs
    · exact store_sound hs hm (match_aptr_of_aval strict ha) hv
    · cases hs
  | _ => cases hs

/-- `ValueDomain.loadbytes_sound` -/
theorem loadbytes_sound (strict : Bool) {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {sz : Z}
    {bytes : List MemVal} {am : Amem} {rm : Romem} {p : Aptr}
    (hl : Mem.loadbytes m b (Integers.Ptrofs.unsigned ofs) sz = some bytes)
    (hr : Romatch bc m rm) (hm : Mmatch bc m am) (hp : Pmatch bc b ofs p) :
    ∀ b' ofs' q i, MemVal.Fragment (.Vptr b' ofs') q i ∈ bytes →
      Pmatch bc b' ofs' (loadbytes strict am rm p) := by
  intro b' ofs' q i hin
  cases hp with
  | gl id h =>
    have NS := hm.mmatch_nonstack b (by rw [h]; simp) (by rw [h]; simp)
    simp only [loadbytes]
    split
    · rename_i ab hrm; exact ablock_loadbytes_sound hl (hr b id ab h hrm).2.1 hin
    · split
      · rename_i ab hg; exact ablock_loadbytes_sound hl (hm.mmatch_glob id ab b h hg) hin
      · exact smatch_loadbytes hl NS hin
  | glo id h =>
    have NS := hm.mmatch_nonstack b (by rw [h]; simp) (by rw [h]; simp)
    simp only [loadbytes]
    split
    · rename_i ab hrm; exact ablock_loadbytes_sound hl (hr b id ab h hrm).2.1 hin
    · split
      · rename_i ab hg; exact ablock_loadbytes_sound hl (hm.mmatch_glob id ab b h hg) hin
      · exact smatch_loadbytes hl NS hin
  | glob id h =>
    exact smatch_loadbytes hl (hm.mmatch_nonstack b (by rw [h]; simp) (by rw [h]; simp)) hin
  | stk h => exact ablock_loadbytes_sound hl (hm.mmatch_stack b h) hin
  | stack h => exact ablock_loadbytes_sound hl (hm.mmatch_stack b h) hin
  | nonstack h1 h2 => exact smatch_loadbytes hl (hm.mmatch_nonstack b h1 h2) hin
  | top h => exact smatch_loadbytes hl (hm.mmatch_top b h) hin

/-- `ValueDomain.storebytes_sound` -/
theorem storebytes_sound {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {bytes : List MemVal}
    {m' : Mem} {am : Amem} {p : Aptr} {sz : Z} {q : Aptr}
    (hs : Mem.storebytes m b (Integers.Ptrofs.unsigned ofs) bytes = some m')
    (hm : Mmatch bc m am) (hp : Pmatch bc b ofs p) (hlen : bytes.length = sz.toNat)
    (hc : ∀ b' ofs' qt i, MemVal.Fragment (.Vptr b' ofs') qt i ∈ bytes → Pmatch bc b' ofs' q) :
    Mmatch bc m' (storebytes am p sz q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b0 hb0
    have DFL : bc b ≠ .BCstack → Bmatch bc m' b0 am.am_stack := fun hne =>
      bmatch_inv (hm.mmatch_stack b0 hb0) (fun o n _ =>
        Mem.loadbytes_storebytes_other hs _ _ _ (.inl (by intro e; subst e; exact hne hb0)))
    cases hp with
    | stk h =>
      have := bc.bc_stack b0 b hb0 h; subst this
      exact ablock_storebytes_sound hs hlen hc (hm.mmatch_stack _ hb0)
    | stack h =>
      have := bc.bc_stack b0 b hb0 h; subst this
      exact ablock_storebytes_anywhere_sound hs hc (hm.mmatch_stack _ hb0)
    | top h => exact ablock_storebytes_anywhere_sound hs hc (hm.mmatch_stack _ hb0)
    | gl id h => exact DFL (by rw [h]; simp)
    | glo id h => exact DFL (by rw [h]; simp)
    | glob id h => exact DFL (by rw [h]; simp)
    | nonstack h1 h2 => exact DFL h1
  · intro id ab b' hb' hg
    have DFL : bc b ≠ .BCglob id → am.am_glob.get id = some ab → Bmatch bc m' b' ab :=
      fun hne hg' => bmatch_inv (hm.mmatch_glob id ab b' hb' hg') (fun o n _ =>
        Mem.loadbytes_storebytes_other hs _ _ _ (.inl (by intro e; subst e; exact hne hb')))
    cases hp with
    | gl id0 h =>
      dsimp only [storebytes] at hg
      rw [PTree.gsspec] at hg
      split at hg
      · rename_i he; subst he; cases hg
        have := bc.bc_glob b' b id hb' h; subst this
        exact ablock_storebytes_sound hs hlen hc (bmatch_globBlock hm h)
      · rename_i hne; exact DFL (by rw [h]; simp [Ne.symm hne]) hg
    | glo id0 h =>
      dsimp only [storebytes] at hg
      rw [PTree.gsspec] at hg
      split at hg
      · rename_i he; subst he; cases hg
        have := bc.bc_glob b' b id hb' h; subst this
        exact ablock_storebytes_anywhere_sound hs hc (bmatch_globBlock hm h)
      · rename_i hne; exact DFL (by rw [h]; simp [Ne.symm hne]) hg
    | glob id0 h => dsimp only [storebytes] at hg; rw [PTree.gempty] at hg; cases hg
    | nonstack h1 h2 => dsimp only [storebytes] at hg; rw [PTree.gempty] at hg; cases hg
    | top h => dsimp only [storebytes] at hg; rw [PTree.gempty] at hg; cases hg
    | stk h => exact DFL (by rw [h]; simp) hg
    | stack h => exact DFL (by rw [h]; simp) hg
  · intro b0 h1 h2
    have DFL : Smatch bc m' b0 (plub q am.am_nonstack) :=
      smatch_storebytes hs (hm.mmatch_nonstack b0 h1 h2) hc
    have STK : bc b = .BCstack → Smatch bc m' b0 am.am_nonstack := fun hb =>
      smatch_inv (hm.mmatch_nonstack b0 h1 h2) (fun o n _ =>
        Mem.loadbytes_storebytes_other hs _ _ _ (.inl (by intro e; subst e; exact h1 hb)))
    cases hp <;> first | exact DFL | (apply STK; assumption)
  · intro b0 h
    exact smatch_storebytes hs (hm.mmatch_top b0 h) hc
  · show bcBelow bc m'.nextblock
    rw [Mem.storebytes_nextblock hs]; exact hm.mmatch_below

/-- `ValueDomain.mmatch_ext` -/
theorem mmatch_ext {m : Mem} {am : Amem} {m' : Mem} (hm : Mmatch bc m am)
    (H : ∀ b ofs n bytes, bc b ≠ .BCinvalid → n ≥ 0 → Mem.loadbytes m' b ofs n = some bytes →
      Mem.loadbytes m b ofs n = some bytes)
    (hnb : m.nextblock ≤ m'.nextblock) : Mmatch bc m' am := by
  refine ⟨fun b h => ?_, fun id ab b h hg => ?_, fun b h1 h2 => ?_, fun b h => ?_, ?_⟩
  · exact bmatch_ext (hm.mmatch_stack b h)
      (fun ofs n bytes hl hn => H b ofs n bytes (by rw [h]; simp) hn hl)
  · exact bmatch_ext (hm.mmatch_glob id ab b h hg)
      (fun ofs n bytes hl hn => H b ofs n bytes (by rw [h]; simp) hn hl)
  · exact smatch_ext (hm.mmatch_nonstack b h1 h2)
      (fun ofs n bytes hl hn => H b ofs n bytes h2 hn hl)
  · exact smatch_ext (hm.mmatch_top b h)
      (fun ofs n bytes hl hn => H b ofs n bytes h hn hl)
  · intro b h
    have := hm.mmatch_below b h
    exact Nat.lt_of_lt_of_le this hnb

/-- `ValueDomain.mmatch_free` -/
theorem mmatch_free {m : Mem} {b : Block} {lo hi : Z} {m' : Mem} {am : Amem}
    (hf : Mem.free m b lo hi = some m') (hm : Mmatch bc m am) : Mmatch bc m' am :=
  mmatch_ext hm (fun _ _ _ _ _ _ hl => Mem.loadbytes_free_2 hf hl)
    (by rw [Mem.nextblock_free hf]; exact Nat.le_refl _)

/-- `ValueDomain.mmatch_top'` -/
theorem mmatch_top' {m : Mem} {am : Amem} (hm : Mmatch bc m am) : Mmatch bc m mtop := by
  refine ⟨fun b h => ?_, fun id ab b _ hg => ?_, fun b h1 h2 => ?_, fun b h => ?_, hm.mmatch_below⟩
  · exact ablock_init_sound (smatch_ge (hm.mmatch_stack b h).1 (.top _))
  · simp [mtop, minit] at hg
  · exact smatch_ge (hm.mmatch_nonstack b h1 h2) (.top _)
  · exact smatch_ge (hm.mmatch_top b h) (.top _)

/-- `PTree.beq_correct` (the direction used by `mbeq_sound`). -/
theorem ptreeBeq_correct {A : Type} (cmp : A → A → Bool) :
    ∀ (t1 t2 : PTree A), ptreeBeq cmp t1 t2 = true → ∀ i,
      (PTree.get i t1 = none ∧ PTree.get i t2 = none) ∨
      ∃ x y, PTree.get i t1 = some x ∧ PTree.get i t2 = some y ∧ cmp x y = true
  | .Leaf, t2, h, i => .inl ⟨PTree.get_leaf i, ptreeBeq_leaf_l _ t2 h i⟩
  | .Node l o r, .Leaf, h, i => .inl ⟨ptreeBeq_leaf_r _ _ h i, PTree.get_leaf i⟩
  | .Node l1 o1 r1, .Node l2 o2 r2, h, i => by
    unfold ptreeBeq at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ho, hl⟩, hr⟩ := h
    cases i with
    | xH =>
      show (o1 = none ∧ o2 = none) ∨ ∃ x y, o1 = some x ∧ o2 = some y ∧ cmp x y = true
      cases o1 <;> cases o2 <;> simp_all
    | xO i => exact ptreeBeq_correct cmp l1 l2 hl i
    | xI i => exact ptreeBeq_correct cmp r1 r2 hr i

/-- `ValueDomain.mbeq_sound` -/
theorem mbeq_sound {m1 m2 : Amem} (h : mbeq m1 m2 = true) (m : Mem) :
    Mmatch bc m m1 ↔ Mmatch bc m m2 := by
  simp only [mbeq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ht, hn⟩, hs⟩, hg⟩ := h
  have G := ptreeBeq_correct bbeq _ _ hg
  constructor
  · intro M
    refine ⟨fun b hb => (bbeq_sound hs m b).1 (M.mmatch_stack b hb), fun id ab b hb hab => ?_,
      fun b h1 h2 => hn ▸ M.mmatch_nonstack b h1 h2, fun b h => ht ▸ M.mmatch_top b h,
      M.mmatch_below⟩
    rcases G id with ⟨_, e⟩ | ⟨x, y, e1, e2, e3⟩
    · rw [e] at hab; cases hab
    · rw [e2] at hab; cases hab
      exact (bbeq_sound e3 m b).1 (M.mmatch_glob id x b hb e1)
  · intro M
    refine ⟨fun b hb => (bbeq_sound hs m b).2 (M.mmatch_stack b hb), fun id ab b hb hab => ?_,
      fun b h1 h2 => hn ▸ M.mmatch_nonstack b h1 h2, fun b h => ht ▸ M.mmatch_top b h,
      M.mmatch_below⟩
    rcases G id with ⟨e, _⟩ | ⟨x, y, e1, e2, e3⟩
    · rw [e] at hab; cases hab
    · rw [e1] at hab; cases hab
      exact (bbeq_sound e3 m b).2 (M.mmatch_glob id y b hb e2)

/-- `ValueDomain.mmatch_lub_l` -/
theorem mmatch_lub_l (strict : Bool) {m : Mem} {x : Amem} (y : Amem) (hm : Mmatch bc m x) :
    Mmatch bc m (mlub strict x y) := by
  refine ⟨fun b h => bmatch_lub_l strict _ (hm.mmatch_stack b h), fun id ab b h hg => ?_,
    fun b h1 h2 => smatch_lub_l _ (hm.mmatch_nonstack b h1 h2),
    fun b h => smatch_lub_l _ (hm.mmatch_top b h), hm.mmatch_below⟩
  dsimp only [mlub] at hg
  rw [PTree.gcombine _ rfl] at hg
  unfold combineAblock at hg
  split at hg
  · rename_i b1 b2 e1 e2; cases hg
    exact bmatch_lub_l strict _ (hm.mmatch_glob id b1 b h e1)
  · cases hg

/-- `ValueDomain.mmatch_lub_r` -/
theorem mmatch_lub_r (strict : Bool) {m : Mem} (x : Amem) {y : Amem} (hm : Mmatch bc m y) :
    Mmatch bc m (mlub strict x y) := by
  refine ⟨fun b h => bmatch_lub_r strict _ (hm.mmatch_stack b h), fun id ab b h hg => ?_,
    fun b h1 h2 => smatch_lub_r _ (hm.mmatch_nonstack b h1 h2),
    fun b h => smatch_lub_r _ (hm.mmatch_top b h), hm.mmatch_below⟩
  dsimp only [mlub] at hg
  rw [PTree.gcombine _ rfl] at hg
  unfold combineAblock at hg
  split at hg
  · rename_i b1 b2 e1 e2; cases hg
    exact bmatch_lub_r strict _ (hm.mmatch_glob id b2 b h e2)
  · cases hg

/-! ## Nonaliasing tests -/

/-- `ValueDomain.pdisjoint_sound` -/
theorem pdisjoint_sound {sz1 : Z} {b1 : Block} {ofs1 : Integers.Ptrofs} {p1 : Aptr} {sz2 : Z}
    {b2 : Block} {ofs2 : Integers.Ptrofs} {p2 : Aptr}
    (hd : pdisjoint p1 sz1 p2 sz2 = true) (h1 : Pmatch bc b1 ofs1 p1) (h2 : Pmatch bc b2 ofs2 p2) :
    b1 ≠ b2 ∨ Integers.Ptrofs.unsigned ofs1 + sz1 ≤ Integers.Ptrofs.unsigned ofs2 ∨
      Integers.Ptrofs.unsigned ofs2 + sz2 ≤ Integers.Ptrofs.unsigned ofs1 := by
  cases h1 <;> cases h2 <;> dsimp only [pdisjoint] at hd <;> (try cases hd)
  all_goals first
    | (left; intro he; subst he; simp_all; done)
    | skip
  all_goals (try (simp only [Bool.or_eq_true, decide_eq_true_eq] at hd; exact .inr hd))
  rename_i id1 h1 id2 h2
  by_cases hid : id1 = id2
  · rw [if_pos hid] at hd
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hd
    exact .inr hd
  · left; intro he; subst he
    rw [h1] at h2
    injection h2 with h2
    exact hid h2

/-- `ValueDomain.pdisjoint_sound_strong`: nonaliasing even when the two
    pointers are matched against different, compatible block classifications. -/
theorem pdisjoint_sound_strong {F V : Type} {sz1 : Z} {b1 : Block} {ofs1 : Integers.Ptrofs}
    {bc1 : BlockClassification} {p1 : Aptr} {sz2 : Z} {b2 : Block} {ofs2 : Integers.Ptrofs}
    {bc2 : BlockClassification} {p2 : Aptr} {ge : Genv F V} {sp : Block}
    (hd : pdisjoint p1 sz1 p2 sz2 = true) (h1 : Pmatch bc1 b1 ofs1 p1) (h2 : Pmatch bc2 b2 ofs2 p2)
    (hge1 : GenvMatch bc1 ge) (hsp1 : bc1 sp = .BCstack)
    (hge2 : GenvMatch bc2 ge) (hsp2 : bc2 sp = .BCstack) :
    b1 ≠ b2 ∨ Integers.Ptrofs.unsigned ofs1 + sz1 ≤ Integers.Ptrofs.unsigned ofs2 ∨
      Integers.Ptrofs.unsigned ofs2 + sz2 ≤ Integers.Ptrofs.unsigned ofs1 := by
  -- a global of `bc1` is the same global in `bc2`, and conversely
  have G12 : ∀ b id, bc1 b = .BCglob id → bc2 b = .BCglob id := fun b id h =>
    (hge2.1 id b).1 ((hge1.1 id b).2 h)
  have G21 : ∀ b id, bc2 b = .BCglob id → bc1 b = .BCglob id := fun b id h =>
    (hge1.1 id b).1 ((hge2.1 id b).2 h)
  -- the stack block is the same in both classifications
  have S12 : ∀ b, bc1 b = .BCstack → bc2 b = .BCstack := fun b h => by
    rw [bc1.bc_stack b sp h hsp1]; exact hsp2
  have S21 : ∀ b, bc2 b = .BCstack → bc1 b = .BCstack := fun b h => by
    rw [bc2.bc_stack b sp h hsp2]; exact hsp1
  cases h1 <;> cases h2 <;> dsimp only [pdisjoint] at hd <;> (try cases hd)
  all_goals first
    | (left; intro he; subst he
       first
       | (have := G12 _ _ ‹bc1 _ = .BCglob _›; simp_all; done)
       | (have := S12 _ ‹bc1 _ = .BCstack›; simp_all; done)
       | (simp_all; done))
    | skip
  all_goals (try (simp only [Bool.or_eq_true, decide_eq_true_eq] at hd; exact .inr hd))
  rename_i id1 h1 id2 h2
  by_cases hid : id1 = id2
  · rw [if_pos hid] at hd
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hd
    exact .inr hd
  · left; intro he; subst he
    rw [G12 _ _ h1] at h2
    injection h2 with h2
    exact hid h2

/-! ## Monotonicity properties when the block classification changes -/

/-- `ValueDomain.genv_match_exten` -/
theorem genv_match_exten {F V : Type} {ge : Genv F V} {bc1 bc2 : BlockClassification}
    (hg : GenvMatch bc1 ge) (H1 : ∀ b id, bc1 b = .BCglob id ↔ bc2 b = .BCglob id)
    (H2 : ∀ b, bc1 b = .BCother → bc2 b = .BCother) : GenvMatch bc2 ge := by
  obtain ⟨A, B⟩ := hg
  refine ⟨fun id b => (A id b).trans (H1 b id), fun b hb => ?_⟩
  obtain ⟨B1, B2⟩ := B b hb
  cases h : bc1 b with
  | BCinvalid => exact absurd h B1
  | BCstack => exact absurd h B2
  | BCglob id => rw [(H1 b id).1 h]; simp
  | BCother => rw [H2 b h]; simp

/-- `ValueDomain.romatch_exten` -/
theorem romatch_exten {bc1 bc2 : BlockClassification} {m : Mem} {rm : Romem}
    (hr : Romatch bc1 m rm) (H : ∀ b id, bc2 b = .BCglob id ↔ bc1 b = .BCglob id) :
    Romatch bc2 m rm := by
  intro b id ab hb hrm
  obtain ⟨A, B, C⟩ := hr b id ab ((H b id).1 hb) hrm
  refine ⟨A, ?_, C⟩
  have PM : ∀ b ofs p, Pmatch bc1 b ofs p → Pmatch bc1 b ofs ab.ab_summary → Pmatch bc2 b ofs p := by
    intro b0 ofs p h1 h2
    have hg : Pmatch bc1 b0 ofs .Glob := pmatch_ge A h2
    cases hg with
    | glob id0 hid0 =>
      have e2 : bc2 b0 = .BCglob id0 := (H b0 id0).2 hid0
      cases h1 with
      | gl id1 h => rw [hid0] at h; cases h; exact .gl _ e2
      | glo id1 h => rw [hid0] at h; cases h; exact .glo _ e2
      | glob id1 h => rw [hid0] at h; cases h; exact .glob _ e2
      | stk h => rw [hid0] at h; cases h
      | stack h => rw [hid0] at h; cases h
      | nonstack _ _ => exact .nonstack (by rw [e2]; simp) (by rw [e2]; simp)
      | top _ => exact .top (by rw [e2]; simp)
  have VM : ∀ v x, Vmatch bc1 v x → Vmatch bc1 v (.Ifptr ab.ab_summary) → Vmatch bc2 v x := by
    intro v x h1 h2
    cases h1 <;> (try (constructor <;> assumption)) <;> (try constructor)
    all_goals (cases h2; apply PM <;> assumption)
  obtain ⟨⟨B1, B2⟩, B3⟩ := B
  exact ⟨⟨fun chunk ofs v hl => VM _ _ (B1 _ _ _ hl) (B1 _ _ _ hl),
    fun ofs b' ofs' q i hl => PM _ _ _ (B2 _ _ _ _ _ hl) (B2 _ _ _ _ _ hl)⟩,
    fun chunk ofs v hl => VM _ _ (B3 _ _ _ hl) (B1 _ _ _ hl)⟩

section MATCH_INCR
variable {bc1 bc2 : BlockClassification} (INCR : bcIncr bc1 bc2)
include INCR

/-- `ValueDomain.pmatch_incr` -/
theorem pmatch_incr {b : Block} {ofs : Integers.Ptrofs} {p : Aptr} (h : Pmatch bc1 b ofs p) :
    Pmatch bc2 b ofs p := by
  cases h with
  | gl id h' => exact .gl _ (by rw [INCR b (by rw [h']; simp)]; exact h')
  | glo id h' => exact .glo _ (by rw [INCR b (by rw [h']; simp)]; exact h')
  | glob id h' => exact .glob _ (by rw [INCR b (by rw [h']; simp)]; exact h')
  | stk h' => exact .stk (by rw [INCR b (by rw [h']; simp)]; exact h')
  | stack h' => exact .stack (by rw [INCR b (by rw [h']; simp)]; exact h')
  | nonstack h1 h2 => exact .nonstack (by rw [INCR b h2]; exact h1) (by rw [INCR b h2]; exact h2)
  | top h' => exact .top (by rw [INCR b h']; exact h')

/-- `ValueDomain.vmatch_incr` -/
theorem vmatch_incr {v : Val} {x : Aval} (h : Vmatch bc1 v x) : Vmatch bc2 v x := by
  cases h <;> (try (constructor <;> assumption)) <;> (try constructor)
  all_goals (apply pmatch_incr INCR; assumption)

/-- `ValueDomain.smatch_incr` -/
theorem smatch_incr {m : Mem} {b : Block} {p : Aptr} (h : Smatch bc1 m b p) : Smatch bc2 m b p :=
  ⟨fun chunk ofs v hl => vmatch_incr INCR (h.1 chunk ofs v hl),
   fun ofs b' ofs' q i hl => pmatch_incr INCR (h.2 ofs b' ofs' q i hl)⟩

/-- `ValueDomain.bmatch_incr` -/
theorem bmatch_incr {m : Mem} {b : Block} {ab : Ablock} (h : Bmatch bc1 m b ab) :
    Bmatch bc2 m b ab :=
  ⟨smatch_incr INCR h.1, fun chunk ofs v hl => vmatch_incr INCR (h.2 chunk ofs v hl)⟩

end MATCH_INCR

end ValueDomain
end CC
