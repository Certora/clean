/-
  `ec_mem_extends` from CompCert's `extcall_properties` (`common/Events.v`):
  running an external call on a less-defined argument list in a memory that is
  extended by another one can be matched, in the extending memory, by a run
  that produces a more-defined result, an extending final memory, and leaves
  the out-of-bounds locations of the original memory untouched.

  Proved for every external call whose semantics the port defines; for the
  uninterpreted ones (which CompCert constrains by axiom) the property is a
  hypothesis.
-/
import CCLib.common.EventsMem
import CCLib.common.MemoryExtends

namespace CC

/-- `Events.loc_out_of_bounds`: locations with no `Max`/`Nonempty` permission. -/
def locOutOfBounds (m : Mem) (b : Block) (ofs : Z) : Prop :=
  ¬ Mem.perm m b ofs .Max .Nonempty = true

/-- `ec_mem_extends` -/
def ExtcallMemExtends (sem : ExtcallSem) (ge : Senv) : Prop :=
  ∀ vargs m1 t vres m2 m1' vargs',
    sem ge vargs m1 t vres m2 → Mem.Extends m1 m1' → Val.LessdefList vargs vargs' →
    ∃ vres' m2', sem ge vargs' m1' t vres' m2' ∧ Val.Lessdef vres vres' ∧
      Mem.Extends m2 m2' ∧ Mem.UnchangedOn (locOutOfBounds m1) m1' m2'

namespace EventsExtends

theorem lessdef_defined {v v' : Val} (h : Val.Lessdef v v') (hv : v ≠ .Vundef) : v' = v := by
  cases h with
  | refl => rfl
  | undef => exact absurd rfl hv

theorem eventValMatch_ne_undef {ge : Senv} {ev : EventVal} {ty : ATyp} {v : Val}
    (h : EventValMatch ge ev ty v) : v ≠ .Vundef := by
  cases h <;> simp

theorem eventValMatch_lessdef {ge : Senv} {ev : EventVal} {ty : ATyp} {v v' : Val}
    (h : EventValMatch ge ev ty v) (hl : Val.Lessdef v v') : EventValMatch ge ev ty v' := by
  rw [lessdef_defined hl (eventValMatch_ne_undef h)]; exact h

theorem eventValListMatch_lessdef {ge : Senv} {evl : List EventVal} {tyl : List ATyp}
    {vl vl' : List Val} (h : EventValListMatch ge evl tyl vl) (hl : Val.LessdefList vl vl') :
    EventValListMatch ge evl tyl vl' := by
  induction h generalizing vl' with
  | evl_match_nil => cases hl; exact .evl_match_nil
  | evl_match_cons _ _ _ _ _ _ h1 _ ih =>
    cases hl with
    | cons hv hl' => exact .evl_match_cons _ _ _ _ _ _ (eventValMatch_lessdef h1 hv) (ih hl')

theorem loadResult_undef (chunk : Chunk) : Val.loadResult chunk .Vundef = .Vundef := by
  cases chunk <;> rfl

theorem vptrofs_ne_undef (n : Integers.Ptrofs) : Val.Vptrofs n ≠ .Vundef := by
  simp [Val.Vptrofs, Archi.ptr64]

theorem vnullptr_ne_undef : Val.Vnullptr ≠ .Vundef := by
  simp [Val.Vnullptr, Archi.ptr64]

/-- A memory that is not changed by the call satisfies the conclusion. -/
theorem unchanged_trivial {m1 m1' : Mem} (h : Mem.Extends m1 m1') :
    Mem.Extends m1 m1' ∧ Mem.UnchangedOn (locOutOfBounds m1) m1' m1' :=
  ⟨h, Mem.unchangedOn_refl _⟩

theorem perm_nonempty_of_cur {m : Mem} {b : Block} {ofs : Z} {p : Permission}
    (h : Mem.perm m b ofs .Cur p = true) : ¬ locOutOfBounds m b ofs :=
  fun hn => hn (Mem.perm_implies (Mem.perm_cur_max h) (by cases p <;> rfl))

/-! ## The builtins with a defined semantics -/

theorem volatileLoadSem_extends (chunk : Chunk) (ge : Senv) :
    ExtcallMemExtends (VolatileLoadSem chunk) ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | intro _ b ofs _ _ _ hvl =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      rw [lessdef_defined hv (by simp)]
      cases hvl with
      | vol id ev v hvol hfs hm =>
        exact ⟨_, m1', .intro _ _ _ _ _ _ (VolatileLoad.vol _ _ _ _ id ev v hvol hfs hm), .refl _,
          unchanged_trivial hx⟩
      | nonvol _ hvol hld =>
        obtain ⟨v2, hld2, hv2⟩ := Mem.load_extends hx hld
        exact ⟨v2, m1', .intro _ _ _ _ _ _ (VolatileLoad.nonvol _ _ _ _ _ hvol hld2), hv2,
          unchanged_trivial hx⟩

theorem volatileStoreSem_extends (chunk : Chunk) (ge : Senv) :
    ExtcallMemExtends (VolatileStoreSem chunk) ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | intro _ b ofs _ v _ _ hvs =>
    cases hl with
    | cons hp hl' =>
      cases hl' with
      | cons hv hl'' =>
        cases hl''
        rw [lessdef_defined hp (by simp)]
        rename_i v'
        cases hvs with
        | vol id ev _ hvol hfs hm =>
          have hm' : EventValMatch ge ev (Chunk.typ chunk) (Val.loadResult chunk v') := by
            cases hv with
            | refl => exact hm
            | undef => rw [loadResult_undef] at hm; exact absurd rfl (eventValMatch_ne_undef hm)
          exact ⟨_, m1', .intro _ _ _ _ _ _ _ (VolatileStore.vol _ _ _ _ id ev _ hvol hfs hm'), .refl _,
            unchanged_trivial hx⟩
        | nonvol _ m2 hvol hst =>
          obtain ⟨m2', hst2, hx2⟩ := Mem.store_within_extends hx hst hv
          refine ⟨_, m2', .intro _ _ _ _ _ _ _ (VolatileStore.nonvol _ _ _ _ _ _ hvol hst2), .refl _, hx2, ?_⟩
          exact Mem.store_unchangedOn hst2 fun i h1 h2 =>
            fun hn => hn (Mem.validAccess_perm_nonempty (Mem.store_valid_access hst) h1 h2)

theorem extcallMallocSem_extends (ge : Senv) : ExtcallMemExtends ExtcallMallocSem ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | intro _ sz _ mA b _ ha hst =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      rw [lessdef_defined hv (vptrofs_ne_undef sz)]
      obtain ⟨mA', ha', hxA⟩ := Mem.alloc_extends hx ha (Int.le_refl _) (Int.le_refl _)
      obtain ⟨m2', hst', hx2⟩ := Mem.store_within_extends hxA hst (.refl _)
      refine ⟨_, m2', .intro _ _ _ _ _ _ ha' hst', .refl _, hx2, ?_⟩
      have hb : b = m1'.nextblock := (Mem.alloc_eq ha').2
      have h1 : Mem.UnchangedOn
          (fun b' ofs' => locOutOfBounds m1 b' ofs' ∧ Mem.validBlock m1' b' = true) m1' mA' :=
        Mem.alloc_unchangedOn ha'
      have h2 : Mem.UnchangedOn
          (fun b' ofs' => locOutOfBounds m1 b' ofs' ∧ Mem.validBlock m1' b' = true) mA' m2' :=
        Mem.store_unchangedOn hst' fun _ _ _ hq => by
          subst hb; rw [Mem.fresh_block_alloc] at hq; cases hq.2
      exact (h1.trans h2).implies fun _ _ hq hv => ⟨hq, hv⟩

theorem extcallFreeSem_extends (ge : Senv) : ExtcallMemExtends ExtcallFreeSem ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | ptr _ b lo sz _ _ hld hf =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      rw [lessdef_defined hv (by simp)]
      obtain ⟨v2, hld2, hv2⟩ := Mem.load_extends hx hld
      rw [lessdef_defined hv2 (vptrofs_ne_undef sz)] at hld2
      obtain ⟨m2', hf2, hx2⟩ := Mem.free_parallel_extends hx hf
      refine ⟨_, m2', .ptr _ _ _ _ _ _ hld2 hf2, .refl _, hx2, ?_⟩
      exact Mem.free_unchangedOn hf2 fun i h1 h2 =>
        perm_nonempty_of_cur (Mem.rangePerm_perm m1 b _ _ _ _ (Mem.free_range_perm hf) i h1 h2)
  | null =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      rw [lessdef_defined hv vnullptr_ne_undef]
      exact ⟨_, m1', .null _ _, .refl _, unchanged_trivial hx⟩

theorem extcallMemcpySem_extends (sz al : Z) (ge : Senv) :
    ExtcallMemExtends (ExtcallMemcpySem sz al) ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | intro _ bdst odst bsrc osrc _ bytes _ hal hsz hmod hsa hda hov hlb hsb =>
    cases hl with
    | cons hv1 hl' =>
      cases hl' with
      | cons hv2 hl'' =>
        cases hl''
        rw [lessdef_defined hv1 (by simp), lessdef_defined hv2 (by simp)]
        obtain ⟨bytes2, hlb2, hbi⟩ := Mem.loadbytes_extends hx hlb
        obtain ⟨m2', hsb2, hx2⟩ := Mem.storebytes_within_extends hx hsb hbi
        refine ⟨_, m2', .intro _ _ _ _ _ _ _ _ hal hsz hmod hsa hda hov hlb2 hsb2, .refl _,
          hx2, ?_⟩
        have hlen := Mem.memvalInjectList_length_eq hbi
        exact Mem.storebytes_unchangedOn hsb2 fun i h1 h2 =>
          perm_nonempty_of_cur (Mem.rangePerm_perm m1 bdst _ _ _ _
            (Mem.storebytes_rangePerm hsb) i h1 (by rw [hlen]; exact h2))

theorem extcallAnnotSem_extends (text : String) (targs : List ATyp) (ge : Senv) :
    ExtcallMemExtends (ExtcallAnnotSem text targs) ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | intro _ _ _ args hm =>
    exact ⟨_, m1', .intro _ _ _ _ (eventValListMatch_lessdef hm hl), .refl _,
      unchanged_trivial hx⟩

theorem extcallAnnotValSem_extends (text : String) (targ : ATyp) (ge : Senv) :
    ExtcallMemExtends (ExtcallAnnotValSem text targ) ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | intro _ v _ arg hm =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      exact ⟨_, m1', .intro _ _ _ _ (eventValMatch_lessdef hm hv), hv, unchanged_trivial hx⟩

theorem extcallDebugSem_extends (ge : Senv) : ExtcallMemExtends ExtcallDebugSem ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx _
  cases hs
  exact ⟨_, m1', .intro _ _ _, .refl _, unchanged_trivial hx⟩

theorem knownBuiltinSem_extends (bf : Builtins.BuiltinFunction) (ge : Senv) :
    ExtcallMemExtends (KnownBuiltinSem bf) ge := by
  intro vargs m1 t vres m2 m1' vargs' hs hx hl
  cases hs with
  | intro _ _ _ _ hsem =>
    obtain ⟨v', hsem', hv⟩ := Builtins.builtinFunctionSem_lessdef bf hsem hl
    exact ⟨v', m1', .intro _ _ _ _ hsem', hv, unchanged_trivial hx⟩

end EventsExtends

/-- `ec_mem_extends` for every external call (CompCert's `external_call_mem_extends`):
    proved for every external call whose semantics the port defines; the
    uninterpreted externals contribute it as hypotheses `hext`/`hasm`, as CompCert
    assumes it by axiom. -/
theorem externalCall_memExtends (ef : ExtFun) (ge : Senv)
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) ge) :
    ExtcallMemExtends (externalCall ef) ge := by
  cases ef with
  | EF_external name sg => exact hext name sg
  | EF_builtin name sg =>
    show ExtcallMemExtends (builtinOrExternalSem name sg) ge
    unfold builtinOrExternalSem
    split
    · exact EventsExtends.knownBuiltinSem_extends _ ge
    · exact hext name sg
  | EF_runtime name sg =>
    show ExtcallMemExtends (builtinOrExternalSem name sg) ge
    unfold builtinOrExternalSem
    split
    · exact EventsExtends.knownBuiltinSem_extends _ ge
    · exact hext name sg
  | EF_vload chunk => exact EventsExtends.volatileLoadSem_extends chunk ge
  | EF_vstore chunk => exact EventsExtends.volatileStoreSem_extends chunk ge
  | EF_malloc => exact EventsExtends.extcallMallocSem_extends ge
  | EF_free => exact EventsExtends.extcallFreeSem_extends ge
  | EF_memcpy sz al => exact EventsExtends.extcallMemcpySem_extends sz al ge
  | EF_annot _ txt targs => exact EventsExtends.extcallAnnotSem_extends txt targs ge
  | EF_annot_val _ txt targ => exact EventsExtends.extcallAnnotValSem_extends txt targ ge
  | EF_inline_asm txt sg _ => exact hasm txt sg
  | EF_debug _ _ _ => exact EventsExtends.extcallDebugSem_extends ge

end CC
