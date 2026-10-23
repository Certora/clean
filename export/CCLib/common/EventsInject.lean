/-
  `ec_mem_inject` from CompCert's `extcall_properties` (`common/Events.v`),
  with the definitions it is phrased in: `symbols_inject`, `loc_unmapped`,
  `loc_out_of_reach` and `inject_separated`.

  Proved for every external call whose semantics the port defines; for the
  uninterpreted ones (which CompCert constrains by axiom) the property is a
  hypothesis.
-/
import CCLib.common.EventsExtends
import CCLib.common.MemoryInjections
import CCLib.common.MemoryDrop

namespace CC

open Integers

/-- `Events.symbols_inject` -/
structure SymbolsInject (f : Val.Meminj) (ge1 ge2 : Senv) : Prop where
  public_eq : ∀ id, ge2.public_symbol id = ge1.public_symbol id
  find_mapped : ∀ id b1 b2 delta, f b1 = some (b2, delta) → ge1.find_symbol id = some b1 →
    delta = 0 ∧ ge2.find_symbol id = some b2
  find_public : ∀ id b1, ge1.public_symbol id = true → ge1.find_symbol id = some b1 →
    ∃ b2, f b1 = some (b2, 0) ∧ ge2.find_symbol id = some b2
  volatile_eq : ∀ b1 b2 delta, f b1 = some (b2, delta) →
    ge2.block_is_volatile b2 = ge1.block_is_volatile b1

/-- `Events.loc_unmapped` -/
def locUnmapped (f : Val.Meminj) (b : Block) (_ofs : Z) : Prop := f b = none

/-- `Events.loc_out_of_reach` -/
def locOutOfReach (f : Val.Meminj) (m : Mem) (b : Block) (ofs : Z) : Prop :=
  ∀ b0 delta, f b0 = some (b, delta) → ¬ Mem.perm m b0 (ofs - delta) .Max .Nonempty = true

/-- `Events.inject_separated` -/
def InjectSeparated (f f' : Val.Meminj) (m1 m2 : Mem) : Prop :=
  ∀ b1 b2 delta, f b1 = none → f' b1 = some (b2, delta) →
    Mem.validBlock m1 b1 = false ∧ Mem.validBlock m2 b2 = false

/-- `ec_mem_inject` -/
def ExtcallMemInject (sem : ExtcallSem) : Prop :=
  ∀ ge1 ge2 vargs m1 t vres m2 f m1' vargs',
    SymbolsInject f ge1 ge2 → sem ge1 vargs m1 t vres m2 → Mem.Inject f m1 m1' →
    Val.InjectList f vargs vargs' →
    ∃ f' vres' m2', sem ge2 vargs' m1' t vres' m2' ∧ Val.Inject f' vres vres' ∧
      Mem.Inject f' m2 m2' ∧ Mem.UnchangedOn (locUnmapped f) m1 m2 ∧
      Mem.UnchangedOn (locOutOfReach f m1) m1' m2' ∧ Val.inject_incr f f' ∧
      InjectSeparated f f' m1 m1'

namespace EventsInject

theorem injectSeparated_refl (f : Val.Meminj) (m1 m2 : Mem) : InjectSeparated f f m1 m2 :=
  fun _ _ _ h1 h2 => by rw [h1] at h2; cases h2

theorem ptrofs_add_repr_zero (ofs : Ptrofs) : Ptrofs.add ofs (Ptrofs.repr 0) = ofs :=
  Ptrofs.add_zero ofs

/-- `Events.eventval_match_inject` -/
theorem eventValMatch_inject {f : Val.Meminj} {ge1 ge2 : Senv} (hs : SymbolsInject f ge1 ge2)
    {ev : EventVal} {ty : ATyp} {v1 v2 : Val} (hm : EventValMatch ge1 ev ty v1)
    (hi : Val.Inject f v1 v2) : EventValMatch ge2 ev ty v2 := by
  cases hm with
  | ev_match_int => cases hi; exact .ev_match_int _
  | ev_match_long => cases hi; exact .ev_match_long _
  | ev_match_float => cases hi; exact .ev_match_float _
  | ev_match_single => cases hi; exact .ev_match_single _
  | ev_match_ptr id b ofs hp hf =>
    cases hi with
    | ptr delta hfb ho =>
      obtain ⟨rfl, hf2⟩ := hs.find_mapped _ _ _ _ hfb hf
      rw [ho, ptrofs_add_repr_zero]
      exact .ev_match_ptr _ _ _ (by rw [hs.public_eq]; exact hp) hf2

/-- `Events.eventval_match_inject_2` -/
theorem eventValMatch_inject_2 {f : Val.Meminj} {ge1 ge2 : Senv} (hs : SymbolsInject f ge1 ge2)
    {ev : EventVal} {ty : ATyp} {v1 : Val} (hm : EventValMatch ge1 ev ty v1) :
    ∃ v2, EventValMatch ge2 ev ty v2 ∧ Val.Inject f v1 v2 := by
  cases hm with
  | ev_match_int i => exact ⟨_, .ev_match_int i, .int i⟩
  | ev_match_long i => exact ⟨_, .ev_match_long i, .long i⟩
  | ev_match_float x => exact ⟨_, .ev_match_float x, .float x⟩
  | ev_match_single x => exact ⟨_, .ev_match_single x, .single x⟩
  | ev_match_ptr id b ofs hp hf =>
    obtain ⟨b2, hfb, hf2⟩ := hs.find_public _ _ hp hf
    exact ⟨_, .ev_match_ptr _ _ _ (by rw [hs.public_eq]; exact hp) hf2,
      .ptr 0 hfb (ptrofs_add_repr_zero ofs).symm⟩

/-- `Events.eventval_list_match_inject` -/
theorem eventValListMatch_inject {f : Val.Meminj} {ge1 ge2 : Senv}
    (hs : SymbolsInject f ge1 ge2) {evl : List EventVal} {tyl : List ATyp} {vl1 vl2 : List Val}
    (hm : EventValListMatch ge1 evl tyl vl1) (hi : Val.InjectList f vl1 vl2) :
    EventValListMatch ge2 evl tyl vl2 := by
  induction hm generalizing vl2 with
  | evl_match_nil => cases hi; exact .evl_match_nil
  | evl_match_cons _ _ _ _ _ _ h1 _ ih =>
    cases hi with
    | cons hv hl => exact .evl_match_cons _ _ _ _ _ _ (eventValMatch_inject hs h1 hv) (ih hl)

/-- The conclusion for a call that changes neither memory. -/
theorem unchanged_both {f : Val.Meminj} {m1 m1' : Mem} :
    Mem.UnchangedOn (locUnmapped f) m1 m1 ∧ Mem.UnchangedOn (locOutOfReach f m1) m1' m1' ∧
      Val.inject_incr f f ∧ InjectSeparated f f m1 m1' :=
  ⟨Mem.unchangedOn_refl _, Mem.unchangedOn_refl _, Val.inject_incr_refl f,
    injectSeparated_refl f m1 m1'⟩

theorem inject_vptrofs {f : Val.Meminj} {n : Ptrofs} {v : Val}
    (h : Val.Inject f (Val.Vptrofs n) v) : v = Val.Vptrofs n := by
  simp only [Val.Vptrofs, Archi.ptr64, if_true] at h ⊢
  cases h; rfl

theorem inject_vnullptr {f : Val.Meminj} {v : Val} (h : Val.Inject f Val.Vnullptr v) :
    v = Val.Vnullptr := by
  simp only [Val.Vnullptr, Archi.ptr64, if_true] at h ⊢
  cases h; rfl

/-- A location in the image of a `Max`/`Nonempty` location is reachable. -/
theorem not_outOfReach {f : Val.Meminj} {m : Mem} {b b' : Block} {delta i : Z}
    (hf : f b = some (b', delta)) (hp : Mem.perm m b (i - delta) .Max .Nonempty = true) :
    ¬ locOutOfReach f m b' i :=
  fun hn => hn b delta hf hp

theorem not_unmapped {f : Val.Meminj} {b b' : Block} {delta i : Z}
    (hf : f b = some (b', delta)) : ¬ locUnmapped f b i := by
  unfold locUnmapped; rw [hf]; simp

theorem perm_nonempty_max_of_cur {m : Mem} {b : Block} {ofs : Z} {p : Permission}
    (h : Mem.perm m b ofs .Cur p = true) : Mem.perm m b ofs .Max .Nonempty = true :=
  Mem.perm_implies (Mem.perm_cur_max h) (by cases p <;> rfl)

theorem loadbytes_length {m : Mem} {b : Block} {ofs n : Z} {bytes : List MemVal}
    (h : Mem.loadbytes m b ofs n = some bytes) : bytes.length = n.toNat := by
  rw [Mem.loadbytes_result (Mem.loadbytes_range_perm h)] at h
  cases h
  generalize n.toNat = k
  induction k generalizing ofs with
  | zero => rfl
  | succ k ih => simp [Mem.getN, ih]

theorem loadbytes_zero (m : Mem) (b : Block) (ofs : Z) : Mem.loadbytes m b ofs 0 = some [] := by
  have : Mem.rangePerm m b ofs (ofs + 0) .Cur .Readable = true :=
    Mem.rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => by omega
  rw [Mem.loadbytes_result this]; rfl

theorem storebytes_nil_exists (m : Mem) (b : Block) (ofs : Z) :
    ∃ m', Mem.storebytes m b ofs [] = some m' :=
  Mem.storebytes_isSome (Mem.rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => by simp at h2; omega)

/-! ## The builtins with a defined semantics -/

theorem volatileLoadSem_inject (chunk : Chunk) : ExtcallMemInject (VolatileLoadSem chunk) := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hs hsem hi hl
  cases hsem with
  | intro _ b ofs _ _ _ hvl =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      cases hv with
      | ptr delta hfb ho =>
        subst ho
        cases hvl with
        | vol id ev v hvol hfs hm =>
          obtain ⟨rfl, hf2⟩ := hs.find_mapped _ _ _ _ hfb hfs
          obtain ⟨v2, hm2, hv2⟩ := eventValMatch_inject_2 hs hm
          have hvol2 := (hs.volatile_eq _ _ _ hfb).trans hvol
          refine ⟨f, _, m1', ?_, Val.loadResult_inject chunk hv2, hi, unchanged_both⟩
          rw [ptrofs_add_repr_zero]
          exact .intro _ _ _ _ _ _ (VolatileLoad.vol _ _ _ _ id ev v2 hvol2 hf2 hm2)
        | nonvol _ hvol hld =>
          have hvol2 := (hs.volatile_eq _ _ _ hfb).trans hvol
          obtain ⟨v2, hld2, hv2⟩ := Mem.load_inject hi hld hfb
          rw [← Mem.address_inject' hi (Mem.load_valid_access hld) hfb] at hld2
          exact ⟨f, v2, m1', .intro _ _ _ _ _ _ (VolatileLoad.nonvol _ _ _ _ _ hvol2 hld2), hv2,
            hi, unchanged_both⟩

theorem volatileStoreSem_inject (chunk : Chunk) : ExtcallMemInject (VolatileStoreSem chunk) := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hs hsem hi hl
  cases hsem with
  | intro _ b ofs _ v _ _ hvs =>
    cases hl with
    | cons hp hl' =>
      cases hl' with
      | cons hv hl'' =>
        cases hl''
        cases hp with
        | ptr delta hfb ho =>
          subst ho
          have hvol2 := hs.volatile_eq _ _ _ hfb
          cases hvs with
          | vol id ev _ hvol hfs hm =>
            obtain ⟨rfl, hf2⟩ := hs.find_mapped _ _ _ _ hfb hfs
            have hm2 := eventValMatch_inject hs hm (Val.loadResult_inject chunk hv)
            refine ⟨f, Val.Vundef, m1', ?_, .undef _, hi, unchanged_both⟩
            rw [ptrofs_add_repr_zero]
            exact .intro _ _ _ _ _ _ _
              (VolatileStore.vol _ _ _ _ id ev _ (hvol2.trans hvol) hf2 hm2)
          | nonvol _ m2 hvol hst =>
            obtain ⟨m2', hst2, hi2⟩ := Mem.store_mapped_inject hi hst hfb hv
            have hva := Mem.store_valid_access hst
            refine ⟨f, Val.Vundef, m2', ?_, .undef _, hi2,
              Mem.store_unchangedOn hst fun _ _ _ => not_unmapped hfb,
              Mem.store_unchangedOn hst2 fun i h1 h2 =>
                not_outOfReach hfb (Mem.validAccess_perm_nonempty hva (by omega) (by omega)),
              Val.inject_incr_refl f, injectSeparated_refl f m1 m1'⟩
            rw [← Mem.address_inject' hi hva hfb] at hst2
            exact .intro _ _ _ _ _ _ _
              (VolatileStore.nonvol _ _ _ _ _ _ (hvol2.trans hvol) hst2)

theorem extcallMallocSem_inject : ExtcallMemInject ExtcallMallocSem := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hs hsem hi hl
  cases hsem with
  | intro _ sz _ mA b _ ha hst =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      rw [inject_vptrofs hv]
      obtain ⟨f', mA', b2, ha', hiA, hincr, hfb, hother⟩ :=
        Mem.alloc_parallel_inject hi ha (Int.le_refl _) (Int.le_refl _)
      have hvi : Val.Inject f' (Val.Vptrofs sz) (Val.Vptrofs sz) := by
        simp only [Val.Vptrofs, Archi.ptr64, if_true]; exact .long _
      obtain ⟨m2', hst', hi2⟩ := Mem.store_mapped_inject hiA hst hfb hvi
      rw [Int.add_zero] at hst'
      have hb : b = m1.nextblock := (Mem.alloc_eq ha).2
      have hb2 : b2 = m1'.nextblock := (Mem.alloc_eq ha').2
      refine ⟨f', _, m2', .intro _ _ _ _ _ _ ha' hst',
        .ptr 0 hfb (ptrofs_add_repr_zero _).symm, hi2, ?_, ?_, hincr, ?_⟩
      · have h1 : Mem.UnchangedOn
            (fun b' ofs' => locUnmapped f b' ofs' ∧ Mem.validBlock m1 b' = true) m1 mA :=
          Mem.alloc_unchangedOn ha
        have h2 : Mem.UnchangedOn
            (fun b' ofs' => locUnmapped f b' ofs' ∧ Mem.validBlock m1 b' = true) mA m2 :=
          Mem.store_unchangedOn hst fun _ _ _ hq => by
            subst hb; rw [Mem.fresh_block_alloc] at hq; cases hq.2
        exact (h1.trans h2).implies fun _ _ hq hv => ⟨hq, hv⟩
      · have h1 : Mem.UnchangedOn
            (fun b' ofs' => locOutOfReach f m1 b' ofs' ∧ Mem.validBlock m1' b' = true) m1' mA' :=
          Mem.alloc_unchangedOn ha'
        have h2 : Mem.UnchangedOn
            (fun b' ofs' => locOutOfReach f m1 b' ofs' ∧ Mem.validBlock m1' b' = true) mA' m2' :=
          Mem.store_unchangedOn hst' fun _ _ _ hq => by
            subst hb2; rw [Mem.fresh_block_alloc] at hq; cases hq.2
        exact (h1.trans h2).implies fun _ _ hq hv => ⟨hq, hv⟩
      · intro b0 b0' d hnone hsome
        by_cases he : b0 = b
        · subst he
          rw [hfb] at hsome; cases hsome
          subst hb; subst hb2
          exact ⟨Mem.fresh_block_alloc m1, Mem.fresh_block_alloc m1'⟩
        · rw [hother b0 he, hnone] at hsome; cases hsome

theorem extcallFreeSem_inject : ExtcallMemInject ExtcallFreeSem := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hs hsem hi hl
  cases hsem with
  | ptr _ b lo sz _ _ hld hf =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      cases hv with
      | ptr delta hfb ho =>
        subst ho
        obtain ⟨v2, hld2, hv2⟩ := Mem.load_inject hi hld hfb
        rw [inject_vptrofs hv2] at hld2
        obtain ⟨m2', hf2, hi2⟩ := Mem.free_parallel_inject hi hf hfb
        have hr := Mem.free_range_perm hf
        have hsz := sizeChunk_pos Mptr
        have hus : (0 : _root_.Int) ≤ (Ptrofs.unsigned sz : _root_.Int) := (Ptrofs.unsigned_range_2 sz).1
        have hp : Mem.perm m1 b (Ptrofs.unsigned lo - 1) .Cur .Freeable = true :=
          Mem.rangePerm_perm _ _ _ _ _ _ hr _ (by zomega) (by zomega)
        have ha := Mem.address_inject_1 hi hp hfb
        refine ⟨f, Val.Vundef, m2', ?_, .undef _, hi2,
          Mem.free_unchangedOn hf fun _ _ _ => not_unmapped hfb,
          Mem.free_unchangedOn hf2 fun i h1 h2 =>
            not_outOfReach hfb (perm_nonempty_max_of_cur
              (Mem.rangePerm_perm _ _ _ _ _ _ hr (i - delta) (by omega) (by omega))),
          Val.inject_incr_refl f, injectSeparated_refl f m1 m1'⟩
        have e1 : Ptrofs.unsigned (Ptrofs.add lo (Ptrofs.repr delta)) - sizeChunk Mptr =
            Ptrofs.unsigned lo - sizeChunk Mptr + delta := by rw [ha]; zomega
        have e2 : Ptrofs.unsigned (Ptrofs.add lo (Ptrofs.repr delta)) + Ptrofs.unsigned sz =
            Ptrofs.unsigned lo + Ptrofs.unsigned sz + delta := by rw [ha]; zomega
        refine .ptr _ _ _ sz _ _ ?_ ?_
        · rw [e1]; exact hld2
        · rw [e1, e2]; exact hf2
  | null =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      rw [inject_vnullptr hv]
      exact ⟨f, _, m1', .null _ _, .undef _, hi, unchanged_both⟩

theorem extcallMemcpySem_inject (sz al : Z) : ExtcallMemInject (ExtcallMemcpySem sz al) := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hs hsem hi hl
  cases hsem with
  | intro _ bdst odst bsrc osrc _ bytes m2 hal hsz hmod hsa hda hov hlb hsb =>
    cases hl with
    | cons hv1 hl' =>
      cases hl' with
      | cons hv2 hl'' =>
        cases hl''
        cases hv1 with
        | ptr dd hfd hod =>
          cases hv2 with
          | ptr ds hfs hos =>
            subst hod hos
            have hlen := loadbytes_length hlb
            by_cases hz : sz = 0
            · subst hz
              have hb : bytes = [] := by
                cases bytes with
                | nil => rfl
                | cons _ _ => simp at hlen
              subst hb
              obtain ⟨m2', hsb2⟩ := storebytes_nil_exists m1' _
                (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr dd)))
              refine ⟨f, Val.Vundef, m2', .intro _ _ _ _ _ _ _ _ hal hsz hmod
                (fun h => absurd h (Int.lt_irrefl 0)) (fun h => absurd h (Int.lt_irrefl 0))
                (by zomega) (loadbytes_zero _ _ _) hsb2, .undef _,
                Mem.storebytes_empty_inject hi hsb hsb2,
                Mem.storebytes_unchangedOn hsb fun _ h1 h2 => by simp at h2; omega,
                Mem.storebytes_unchangedOn hsb2 fun _ h1 h2 => by simp at h2; omega,
                Val.inject_incr_refl f, injectSeparated_refl f m1 m1'⟩
            · have hpos : sz > 0 := by zomega
              have hlenZ : (bytes.length : _root_.Int) = sz := by rw [hlen]; zomega
              have hrs := Mem.loadbytes_range_perm hlb
              have hrd := Mem.storebytes_rangePerm hsb
              rw [hlenZ] at hrd
              have ps := Mem.rangePerm_perm _ _ _ _ _ _ hrs (Ptrofs.unsigned osrc)
                (Int.le_refl _) (by zomega)
              have pd := Mem.rangePerm_perm _ _ _ _ _ _ hrd (Ptrofs.unsigned odst)
                (Int.le_refl _) (by zomega)
              have e1 := Mem.address_inject hi ps hfs
              have e2 := Mem.address_inject hi pd hfd
              obtain ⟨bytes2, hlb2, hbi⟩ := Mem.loadbytes_inject hi hlb hfs
              obtain ⟨m2', hsb2, hi2⟩ := Mem.storebytes_mapped_inject hi hsb hfd hbi
              have hlen2 := Mem.memvalInjectList_length_eq hbi
              have hrsN := Mem.rangePerm_implies hrs (show permOrder .Readable .Nonempty = true from rfl)
              have hrdN := Mem.rangePerm_implies hrd (show permOrder .Writable .Nonempty = true from rfl)
              have hdsz : al ∣ sz := Int.dvd_of_emod_eq_zero hmod
              have hov' := Mem.disjoint_or_equal_inject hi hfs hfd (Mem.rangePerm_max hrsN)
                (Mem.rangePerm_max hrdN) hpos hov
              refine ⟨f, Val.Vundef, m2', ?_, .undef _, hi2,
                Mem.storebytes_unchangedOn hsb fun _ _ _ => not_unmapped hfd,
                Mem.storebytes_unchangedOn hsb2 fun i h1 h2 =>
                  not_outOfReach hfd (Mem.rangePerm_perm _ _ _ _ _ _ (Mem.rangePerm_max hrdN)
                    (i - dd) (by omega) (by rw [← hlen2, hlenZ] at h2; omega)),
                Val.inject_incr_refl f, injectSeparated_refl f m1 m1'⟩
              refine .intro _ _ _ _ _ _ bytes2 _ hal hsz hmod ?_ ?_ ?_ ?_ ?_
              · intro _
                rw [e1]
                exact Int.emod_eq_zero_of_dvd (Mem.aligned_area_inject hi hal hpos hdsz hrsN
                  (Int.dvd_of_emod_eq_zero (hsa hpos)) hfs)
              · intro _
                rw [e2]
                exact Int.emod_eq_zero_of_dvd (Mem.aligned_area_inject hi hal hpos hdsz hrdN
                  (Int.dvd_of_emod_eq_zero (hda hpos)) hfd)
              · rw [e1, e2]; exact hov'
              · rw [e1]; exact hlb2
              · rw [e2]; exact hsb2

theorem extcallAnnotSem_inject (text : String) (targs : List ATyp) :
    ExtcallMemInject (ExtcallAnnotSem text targs) := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hs hsem hi hl
  cases hsem with
  | intro _ _ _ args hm =>
    exact ⟨f, _, m1', .intro _ _ _ _ (eventValListMatch_inject hs hm hl), .undef _, hi,
      unchanged_both⟩

theorem extcallAnnotValSem_inject (text : String) (targ : ATyp) :
    ExtcallMemInject (ExtcallAnnotValSem text targ) := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' hs hsem hi hl
  cases hsem with
  | intro _ v _ arg hm =>
    cases hl with
    | cons hv hl' =>
      cases hl'
      exact ⟨f, _, m1', .intro _ _ _ _ (eventValMatch_inject hs hm hv), hv, hi, unchanged_both⟩

theorem extcallDebugSem_inject : ExtcallMemInject ExtcallDebugSem := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' _ hsem hi _
  cases hsem
  exact ⟨f, _, m1', .intro _ _ _, .undef _, hi, unchanged_both⟩

theorem knownBuiltinSem_inject (bf : Builtins.BuiltinFunction) :
    ExtcallMemInject (KnownBuiltinSem bf) := by
  intro ge1 ge2 vargs m1 t vres m2 f m1' vargs' _ hsem hi hl
  cases hsem with
  | intro _ _ _ _ hsem =>
    obtain ⟨v', hsem', hv⟩ := Builtins.builtinFunctionSem_inject bf hsem hl
    exact ⟨f, v', m1', .intro _ _ _ _ hsem', hv, hi, unchanged_both⟩

end EventsInject

/-- `ec_mem_inject` for every external call (CompCert's `external_call_mem_inject_gen`):
    proved for every external call whose semantics the port defines; the
    uninterpreted externals contribute it as hypotheses `hext`/`hasm`, as CompCert
    assumes it by axiom. -/
theorem externalCall_memInject (ef : ExtFun)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg)) :
    ExtcallMemInject (externalCall ef) := by
  cases ef with
  | EF_external name sg => exact hext name sg
  | EF_builtin name sg =>
    show ExtcallMemInject (builtinOrExternalSem name sg)
    unfold builtinOrExternalSem
    split
    · exact EventsInject.knownBuiltinSem_inject _
    · exact hext name sg
  | EF_runtime name sg =>
    show ExtcallMemInject (builtinOrExternalSem name sg)
    unfold builtinOrExternalSem
    split
    · exact EventsInject.knownBuiltinSem_inject _
    · exact hext name sg
  | EF_vload chunk => exact EventsInject.volatileLoadSem_inject chunk
  | EF_vstore chunk => exact EventsInject.volatileStoreSem_inject chunk
  | EF_malloc => exact EventsInject.extcallMallocSem_inject
  | EF_free => exact EventsInject.extcallFreeSem_inject
  | EF_memcpy sz al => exact EventsInject.extcallMemcpySem_inject sz al
  | EF_annot _ txt targs => exact EventsInject.extcallAnnotSem_inject txt targs
  | EF_annot_val _ txt targ => exact EventsInject.extcallAnnotValSem_inject txt targ
  | EF_inline_asm txt sg _ => exact hasm txt sg
  | EF_debug _ _ _ => exact EventsInject.extcallDebugSem_inject

end CC
