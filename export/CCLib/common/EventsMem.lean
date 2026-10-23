/-
  Memory-related fields of CompCert's `extcall_properties` (`common/Events.v`)
  for the external calls whose semantics the port defines: `ec_valid_block`,
  `ec_max_perm`, `ec_readonly` and `ec_trace_length`.  `ec_mem_extends` is in
  `CCLib.common.EventsExtends`, `ec_mem_inject` in `CCLib.common.EventsInject`,
  `ec_symbols_preserved`/`ec_well_typed` in `CCLib.common.EventsProps`, and
  `ec_receptive` in `CCLib.common.EventsReceptive`.

  The uninterpreted externals (`externalFunctionsSem`, `inlineAssemblySem`) are
  not covered: in CompCert their properties are axioms, and this file adds no
  axioms.  For them `ExtcallMemProps` is an assumption a client has to supply.
-/
import CCLib.common.Events
import CCLib.common.MemoryUnchanged
import CCLib.common.MemoryInject

namespace CC

/-- `Events.loc_not_writable`: locations without `Max`/`Writable` permission. -/
def locNotWritable (m : Mem) (b : Block) (ofs : Z) : Prop :=
  ¬ Mem.perm m b ofs .Max .Writable = true

/-- The memory fields of `Events.extcall_properties` (`ec_valid_block`,
    `ec_max_perm`, `ec_readonly`) together with `ec_trace_length`. -/
structure ExtcallMemProps (sem : ExtcallSem) (ge : Senv) : Prop where
  /-- `ec_valid_block` -/
  validBlock : ∀ vargs m t vres m' b, sem ge vargs m t vres m' →
    Mem.validBlock m b = true → Mem.validBlock m' b = true
  /-- `ec_max_perm` -/
  maxPerm : ∀ vargs m t vres m' b ofs p, sem ge vargs m t vres m' →
    Mem.validBlock m b = true → Mem.perm m' b ofs .Max p = true → Mem.perm m b ofs .Max p = true
  /-- `ec_readonly` -/
  readonly : ∀ vargs m t vres m', sem ge vargs m t vres m' →
    Mem.UnchangedOn (locNotWritable m) m m'
  /-- `ec_trace_length` -/
  traceLength : ∀ vargs m t vres m', sem ge vargs m t vres m' → t.length ≤ 1

namespace EventsMem

/-- A semantics that leaves memory untouched and emits at most one event has
    all the memory properties. -/
theorem of_mem_eq {sem : ExtcallSem} {ge : Senv}
    (h : ∀ vargs m t vres m', sem ge vargs m t vres m' → m' = m ∧ t.length ≤ 1) :
    ExtcallMemProps sem ge where
  validBlock := fun _ _ _ _ _ _ hs hb => by rw [(h _ _ _ _ _ hs).1]; exact hb
  maxPerm := fun _ _ _ _ _ _ _ _ hs _ hp => by rwa [(h _ _ _ _ _ hs).1] at hp
  readonly := fun _ _ _ _ _ hs => by rw [(h _ _ _ _ _ hs).1]; exact Mem.unchangedOn_refl _
  traceLength := fun _ _ _ _ _ hs => (h _ _ _ _ _ hs).2

/-- Writable `Cur` permission rules out `locNotWritable`. -/
theorem not_locNotWritable_of_cur {m : Mem} {b : Block} {ofs : Z} {p : Permission}
    (h : Mem.perm m b ofs .Cur p = true) (hp : permOrder p .Writable = true) :
    ¬ locNotWritable m b ofs :=
  fun hn => hn (Mem.perm_implies (Mem.perm_cur_max h) hp)

theorem store_readonly {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (hs : Mem.store chunk m b ofs v = some m') : Mem.UnchangedOn (locNotWritable m) m m' :=
  Mem.store_unchangedOn hs fun i h1 h2 =>
    not_locNotWritable_of_cur
      (Mem.rangePerm_perm m b _ _ _ _
        (by have := Mem.store_valid_access hs
            simp only [Mem.validAccess, Bool.and_eq_true] at this; exact this.1) i h1 h2)
      rfl

theorem storebytes_readonly {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    (hs : Mem.storebytes m b ofs bytes = some m') : Mem.UnchangedOn (locNotWritable m) m m' :=
  Mem.storebytes_unchangedOn hs fun i h1 h2 =>
    not_locNotWritable_of_cur
      (Mem.rangePerm_perm m b _ _ _ _ (Mem.storebytes_rangePerm hs) i h1 h2) rfl

theorem free_readonly {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (hf : Mem.free m b lo hi = some m') : Mem.UnchangedOn (locNotWritable m) m m' :=
  Mem.free_unchangedOn hf fun i h1 h2 =>
    not_locNotWritable_of_cur
      (Mem.rangePerm_perm m b _ _ _ _ (Mem.free_range_perm hf) i h1 h2) rfl

theorem free_maxPerm {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (hf : Mem.free m b lo hi = some m') {b' : Block} {ofs : Z} {k : PermKind} {p : Permission}
    (h : Mem.perm m' b' ofs k p = true) : Mem.perm m b' ofs k p = true := by
  rw [Mem.free_result hf] at h; exact Mem.perm_free_3 h

theorem alloc_store_valid {m : Mem} {lo hi : Z} {m1 m2 : Mem} {b : Block} {chunk : Chunk}
    {ofs : Z} {v : Val} (ha : Mem.alloc m lo hi = (m1, b))
    (hs : Mem.store chunk m1 b ofs v = some m2) {b' : Block}
    (hb : Mem.validBlock m b' = true) : Mem.validBlock m2 b' = true := by
  have e1 : (Mem.alloc m lo hi).1 = m1 := by rw [ha]
  subst e1
  exact Mem.valid_block_store_1 hs (Mem.valid_block_alloc m lo hi hb)

theorem alloc_store_maxPerm {m : Mem} {lo hi : Z} {m1 m2 : Mem} {b : Block} {chunk : Chunk}
    {ofs : Z} {v : Val} (ha : Mem.alloc m lo hi = (m1, b))
    (hs : Mem.store chunk m1 b ofs v = some m2) {b' : Block} {ofs' : Z} {p : Permission}
    (hb : Mem.validBlock m b' = true) (hp : Mem.perm m2 b' ofs' .Max p = true) :
    Mem.perm m b' ofs' .Max p = true := by
  have e1 : (Mem.alloc m lo hi).1 = m1 := by rw [ha]
  subst e1
  rw [Mem.perm_store hs] at hp
  have hne : b' ≠ m.nextblock := by
    intro he; subst he; rw [Mem.fresh_block_alloc] at hb; cases hb
  rwa [Mem.perm_alloc_other m lo hi b' hne] at hp

theorem alloc_store_readonly {m : Mem} {lo hi : Z} {m1 m2 : Mem} {b : Block} {chunk : Chunk}
    {ofs : Z} {v : Val} (ha : Mem.alloc m lo hi = (m1, b))
    (hs : Mem.store chunk m1 b ofs v = some m2) :
    Mem.UnchangedOn (locNotWritable m) m m2 := by
  have hb : b = m.nextblock := by
    have : (Mem.alloc m lo hi).2 = b := by rw [ha]
    rw [← this]; rfl
  have h1 : Mem.UnchangedOn (fun b' ofs' => locNotWritable m b' ofs' ∧ Mem.validBlock m b' = true)
      m m1 := Mem.alloc_unchangedOn ha
  have h2 : Mem.UnchangedOn (fun b' ofs' => locNotWritable m b' ofs' ∧ Mem.validBlock m b' = true)
      m1 m2 := Mem.store_unchangedOn hs fun _ _ _ hq => by
        subst hb; rw [Mem.fresh_block_alloc] at hq; cases hq.2
  exact (h1.trans h2).implies fun _ _ hq hv => ⟨hq, hv⟩

/-! ## The builtins with a defined semantics -/

theorem volatileLoadSem_memProps (chunk : Chunk) (ge : Senv) :
    ExtcallMemProps (VolatileLoadSem chunk) ge :=
  of_mem_eq fun _ _ _ _ _ hs => by
    cases hs
    rename_i hl
    exact ⟨rfl, by cases hl <;> simp [E0]⟩

theorem volatileStoreSem_memProps (chunk : Chunk) (ge : Senv) :
    ExtcallMemProps (VolatileStoreSem chunk) ge where
  validBlock := fun _ _ _ _ _ _ hs hb => by
    cases hs with
    | intro _ _ _ _ _ _ _ hst =>
      cases hst with
      | vol => exact hb
      | nonvol _ _ _ hs => exact Mem.valid_block_store_1 hs hb
  maxPerm := fun _ _ _ _ _ _ _ _ hs _ hp => by
    cases hs with
    | intro _ _ _ _ _ _ _ hst =>
      cases hst with
      | vol => exact hp
      | nonvol _ _ _ hs => rwa [Mem.perm_store hs] at hp
  readonly := fun _ _ _ _ _ hs => by
    cases hs with
    | intro _ _ _ _ _ _ _ hst =>
      cases hst with
      | vol => exact Mem.unchangedOn_refl _
      | nonvol _ _ _ hs => exact store_readonly hs
  traceLength := fun _ _ _ _ _ hs => by
    cases hs with
    | intro _ _ _ _ _ _ _ hst => cases hst <;> simp [E0]

theorem extcallMallocSem_memProps (ge : Senv) : ExtcallMemProps ExtcallMallocSem ge where
  validBlock := fun _ _ _ _ _ _ hs hb => by
    cases hs with
    | intro _ _ _ _ _ _ ha hst => exact alloc_store_valid ha hst hb
  maxPerm := fun _ _ _ _ _ _ _ _ hs hb hp => by
    cases hs with
    | intro _ _ _ _ _ _ ha hst => exact alloc_store_maxPerm ha hst hb hp
  readonly := fun _ _ _ _ _ hs => by
    cases hs with
    | intro _ _ _ _ _ _ ha hst => exact alloc_store_readonly ha hst
  traceLength := fun _ _ _ _ _ hs => by cases hs; simp [E0]

theorem extcallFreeSem_memProps (ge : Senv) : ExtcallMemProps ExtcallFreeSem ge where
  validBlock := fun _ _ _ _ _ _ hs hb => by
    cases hs with
    | ptr _ _ _ _ _ _ _ hf => exact Mem.valid_block_free_1 hf hb
    | null => exact hb
  maxPerm := fun _ _ _ _ _ _ _ _ hs _ hp => by
    cases hs with
    | ptr _ _ _ _ _ _ _ hf => exact free_maxPerm hf hp
    | null => exact hp
  readonly := fun _ _ _ _ _ hs => by
    cases hs with
    | ptr _ _ _ _ _ _ _ hf => exact free_readonly hf
    | null => exact Mem.unchangedOn_refl _
  traceLength := fun _ _ _ _ _ hs => by cases hs <;> simp [E0]

theorem extcallMemcpySem_memProps (sz al : Z) (ge : Senv) :
    ExtcallMemProps (ExtcallMemcpySem sz al) ge where
  validBlock := fun _ _ _ _ _ _ hs hb => by
    cases hs with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsb => exact Mem.valid_block_storebytes_1 hsb hb
  maxPerm := fun _ _ _ _ _ _ _ _ hs _ hp => by
    cases hs with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsb => rwa [Mem.perm_storebytes hsb] at hp
  readonly := fun _ _ _ _ _ hs => by
    cases hs with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsb => exact storebytes_readonly hsb
  traceLength := fun _ _ _ _ _ hs => by cases hs; simp [E0]

theorem extcallAnnotSem_memProps (text : String) (targs : List ATyp) (ge : Senv) :
    ExtcallMemProps (ExtcallAnnotSem text targs) ge :=
  of_mem_eq fun _ _ _ _ _ hs => by cases hs; exact ⟨rfl, by simp⟩

theorem extcallAnnotValSem_memProps (text : String) (targ : ATyp) (ge : Senv) :
    ExtcallMemProps (ExtcallAnnotValSem text targ) ge :=
  of_mem_eq fun _ _ _ _ _ hs => by cases hs; exact ⟨rfl, by simp⟩

theorem extcallDebugSem_memProps (ge : Senv) : ExtcallMemProps ExtcallDebugSem ge :=
  of_mem_eq fun _ _ _ _ _ hs => by cases hs; exact ⟨rfl, by simp [E0]⟩

theorem knownBuiltinSem_memProps (bf : Builtins.BuiltinFunction) (ge : Senv) :
    ExtcallMemProps (KnownBuiltinSem bf) ge :=
  of_mem_eq fun _ _ _ _ _ hs => by cases hs; exact ⟨rfl, by simp [E0]⟩

end EventsMem

/-- `Events.external_call_spec`, memory fields: every external call whose
    semantics the port defines satisfies `ec_valid_block`, `ec_max_perm`,
    `ec_readonly` and `ec_trace_length`.  `EF_external`, `EF_inline_asm` and
    `EF_builtin`/`EF_runtime` names that are not known builtins are
    uninterpreted; for those the properties are a hypothesis (`hext`), exactly
    as CompCert assumes them by axiom. -/
theorem externalCall_memProps (ef : ExtFun) (ge : Senv)
    (hext : ∀ name sg, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ExtcallMemProps (externalCall ef) ge := by
  cases ef with
  | EF_external name sg => exact hext name sg
  | EF_builtin name sg =>
    show ExtcallMemProps (builtinOrExternalSem name sg) ge
    unfold builtinOrExternalSem
    split
    · exact EventsMem.knownBuiltinSem_memProps _ ge
    · exact hext name sg
  | EF_runtime name sg =>
    show ExtcallMemProps (builtinOrExternalSem name sg) ge
    unfold builtinOrExternalSem
    split
    · exact EventsMem.knownBuiltinSem_memProps _ ge
    · exact hext name sg
  | EF_vload chunk => exact EventsMem.volatileLoadSem_memProps chunk ge
  | EF_vstore chunk => exact EventsMem.volatileStoreSem_memProps chunk ge
  | EF_malloc => exact EventsMem.extcallMallocSem_memProps ge
  | EF_free => exact EventsMem.extcallFreeSem_memProps ge
  | EF_memcpy sz al => exact EventsMem.extcallMemcpySem_memProps sz al ge
  | EF_annot _ txt targs => exact EventsMem.extcallAnnotSem_memProps txt targs ge
  | EF_annot_val _ txt targ => exact EventsMem.extcallAnnotValSem_memProps txt targ ge
  | EF_inline_asm txt sg _ => exact hasm txt sg
  | EF_debug _ _ _ => exact EventsMem.extcallDebugSem_memProps ge

end CC
