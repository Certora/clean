/-
  Generic memory injections — port of the `MEM_INJ` section of
  `common/Memory.v` (`mem_inj`, `perm_inj`, `range_perm_inj`,
  `valid_access_inj`, `getN_inj`, `load_inj`, `loadbytes_inj`, `setN_inj`,
  `store_mapped_inj`, `store_unmapped_inj`, `store_outside_inj`) together with
  `Memdata.min_safe_alignment`.

  `MemInj f m1 m2` is the part of a memory injection shared by memory
  extensions (`CCLib.common.MemoryExtends`) and full injections
  (`CCLib.common.MemoryInjections`): permissions are preserved, the offsets are
  suitably aligned, and readable contents are related by `memval_inject`.

  Numeric binders are spelled `_root_.Int` rather than `Z` so `omega` sees them
  (see the note in `CCLib/common/Memory.lean`).
-/
import CCLib.common.MemoryUnchanged
import CCLib.common.MemdataInject

namespace CC

/-- `Memdata.min_safe_alignment`: the alignment a block of size `sz` must
have so that every access inside it is aligned. -/
def minSafeAlignment (sz : _root_.Int) : _root_.Int :=
  if sz < 2 then 1 else if sz < 4 then 2 else if sz < 8 then 4 else 8

/-- `Memdata.min_safe_alignment_pos` -/
theorem minSafeAlignment_pos (sz : Z) : minSafeAlignment sz > 0 := by
  unfold minSafeAlignment; split <;> (try split) <;> (try split) <;> decide

/-- `Memdata.min_safe_alignment_sound` -/
theorem minSafeAlignment_sound (sz : _root_.Int) (chunk : Chunk) (h : sizeChunk chunk ≤ sz) :
    alignChunk chunk ∣ minSafeAlignment sz := by
  unfold minSafeAlignment
  cases chunk <;> simp only [alignChunk] <;>
    first
    | (have h' : (1 : _root_.Int) ≤ sz := h; (repeat' split) <;> first | decide | omega)
    | (have h' : (2 : _root_.Int) ≤ sz := h; (repeat' split) <;> first | decide | omega)
    | (have h' : (4 : _root_.Int) ≤ sz := h; (repeat' split) <;> first | decide | omega)
    | (have h' : (8 : _root_.Int) ≤ sz := h; (repeat' split) <;> first | decide | omega)

/-- `Memdata.min_safe_alignment_8` -/
theorem minSafeAlignment_dvd_8 (sz : Z) : minSafeAlignment sz ∣ 8 := by
  unfold minSafeAlignment; (repeat' split) <;> decide

/-- `Memdata.min_safe_alignment_mono` -/
theorem minSafeAlignment_mono {sz1 sz2 : _root_.Int} (h : sz1 ≤ sz2) :
    minSafeAlignment sz1 ∣ minSafeAlignment sz2 := by
  unfold minSafeAlignment; (repeat' split) <;> first | decide | omega

namespace Mem

/-- `Memory.mem_inj` -/
structure MemInj (f : Val.Meminj) (m1 m2 : Mem) : Prop where
  perm : ∀ b1 b2 delta ofs k p, f b1 = some (b2, delta) →
    Mem.perm m1 b1 ofs k p = true → Mem.perm m2 b2 (ofs + delta) k p = true
  align : ∀ b1 b2 delta (ofs sz : _root_.Int) p, f b1 = some (b2, delta) → sz > 0 →
    rangePerm m1 b1 ofs (ofs + sz) .Max p = true → minSafeAlignment sz ∣ delta
  memval : ∀ b1 ofs b2 delta, f b1 = some (b2, delta) →
    Mem.perm m1 b1 ofs .Cur .Readable = true →
    MemvalInject f (ZMap.get ofs (PMap.get b1 m1.contents))
      (ZMap.get (ofs + delta) (PMap.get b2 m2.contents))

section MemInj
variable {f : Val.Meminj} {m1 m2 : Mem}

/-- `Memory.perm_inj` -/
theorem perm_inj (h : MemInj f m1 m2) {b1 b2 : Block} {delta ofs : Z} {k : PermKind}
    {p : Permission} (hp : perm m1 b1 ofs k p = true) (hf : f b1 = some (b2, delta)) :
    perm m2 b2 (ofs + delta) k p = true :=
  h.perm _ _ _ _ _ _ hf hp

/-- `Memory.range_perm_inj` -/
theorem rangePerm_inj (h : MemInj f m1 m2) {b1 b2 : Block} {delta lo hi : _root_.Int}
    {k : PermKind} {p : Permission} (hp : rangePerm m1 b1 lo hi k p = true)
    (hf : f b1 = some (b2, delta)) :
    rangePerm m2 b2 (lo + delta) (hi + delta) k p = true := by
  apply rangePerm_intro
  intro ofs h1 h2
  have := perm_inj h (rangePerm_perm m1 b1 lo hi k p hp (ofs - delta) (by omega) (by omega)) hf
  rwa [show ofs - delta + delta = ofs by omega] at this

/-- Alignment of `delta` for an access of `chunk` inside the source block. -/
theorem align_inj (h : MemInj f m1 m2) {b1 b2 : Block} {delta ofs : _root_.Int}
    {chunk : Chunk} {p : Permission}
    (hp : rangePerm m1 b1 ofs (ofs + sizeChunk chunk) .Max p = true)
    (hf : f b1 = some (b2, delta)) : alignChunk chunk ∣ delta :=
  Int.dvd_trans (minSafeAlignment_sound _ chunk (Int.le_refl _))
    (h.align _ _ _ _ _ _ hf (sizeChunk_pos chunk) hp)

/-- `Memory.perm_cur_max` -/
theorem perm_cur_max {m : Mem} {b : Block} {ofs : Z} {p : Permission}
    (h : perm m b ofs .Cur p = true) : perm m b ofs .Max p = true := by
  have hm := m.access_max b ofs
  unfold perm at h ⊢
  generalize PMap.get b m.access ofs .Max = mx at hm ⊢
  generalize PMap.get b m.access ofs .Cur = cu at hm h
  cases mx <;> cases cu <;> simp_all [permOrder'', permOrder']
  exact permOrder_trans hm h

/-- `Memory.perm_cur` -/
theorem perm_cur {m : Mem} {b : Block} {ofs : Z} {k : PermKind} {p : Permission}
    (h : perm m b ofs .Cur p = true) : perm m b ofs k p = true := by
  cases k
  · exact perm_cur_max h
  · exact h

/-- `Memory.perm_max` -/
theorem perm_max {m : Mem} {b : Block} {ofs : Z} {k : PermKind} {p : Permission}
    (h : perm m b ofs k p = true) : perm m b ofs .Max p = true := by
  cases k
  · exact h
  · exact perm_cur_max h

/-- `Memory.range_perm_cur` / `range_perm_max` -/
theorem rangePerm_max {m : Mem} {b : Block} {lo hi : _root_.Int} {k : PermKind}
    {p : Permission} (h : rangePerm m b lo hi k p = true) :
    rangePerm m b lo hi .Max p = true :=
  rangePerm_intro m b lo hi .Max p (fun ofs h1 h2 => perm_max (rangePerm_perm m b lo hi k p h ofs h1 h2))

/-- `validAccess` gives the `Max` range permission as well. -/
theorem validAccess_rangePerm_max {m : Mem} {chunk : Chunk} {b : Block} {ofs : _root_.Int}
    {p : Permission} (h : validAccess m chunk b ofs p = true) :
    rangePerm m b ofs (ofs + sizeChunk chunk) .Max p = true := by
  simp only [validAccess, Bool.and_eq_true] at h
  exact rangePerm_max h.1

/-- `Memory.valid_access_inj` -/
theorem validAccess_inj (h : MemInj f m1 m2) {chunk : Chunk} {b1 b2 : Block}
    {delta ofs : _root_.Int} {p : Permission} (hf : f b1 = some (b2, delta))
    (hv : validAccess m1 chunk b1 ofs p = true) :
    validAccess m2 chunk b2 (ofs + delta) p = true := by
  have hal := align_inj h (validAccess_rangePerm_max hv) hf
  simp only [validAccess, Bool.and_eq_true, beq_iff_eq] at hv ⊢
  refine ⟨?_, ?_⟩
  · have := rangePerm_inj h hv.1 hf
    rwa [show ofs + sizeChunk chunk + delta = ofs + delta + sizeChunk chunk by omega] at this
  · exact Int.emod_eq_zero_of_dvd (Int.dvd_add (Int.dvd_of_emod_eq_zero hv.2) hal)

/-- `Memory.getN_inj` -/
theorem getN_inj (h : MemInj f m1 m2) {b1 b2 : Block} {delta : _root_.Int}
    (hf : f b1 = some (b2, delta)) :
    ∀ (n : Nat) (ofs : _root_.Int),
      rangePerm m1 b1 ofs (ofs + n) .Cur .Readable = true →
      MemvalInjectList f (getN n ofs (PMap.get b1 m1.contents))
        (getN n (ofs + delta) (PMap.get b2 m2.contents)) := by
  intro n
  induction n with
  | zero => intro _ _; exact .nil
  | succ n ih =>
    intro ofs hr
    have hc : ((n + 1 : Nat) : _root_.Int) = (n : _root_.Int) + 1 := Int.natCast_succ n
    rw [hc] at hr
    refine .cons (h.memval _ _ _ _ hf
      (rangePerm_perm m1 b1 _ _ _ _ hr ofs (Int.le_refl _) (by omega))) ?_
    rw [show ofs + delta + 1 = (ofs + 1) + delta by omega]
    apply ih
    apply rangePerm_intro
    intro i h1 h2
    exact rangePerm_perm m1 b1 _ _ _ _ hr i (by omega) (by omega)

/-- `Memory.load_inj` -/
theorem load_inj (h : MemInj f m1 m2) {chunk : Chunk} {b1 b2 : Block} {delta ofs : _root_.Int}
    {v1 : Val} (hl : load chunk m1 b1 ofs = some v1) (hf : f b1 = some (b2, delta)) :
    ∃ v2, load chunk m2 b2 (ofs + delta) = some v2 ∧ Val.Inject f v1 v2 := by
  unfold load at hl ⊢
  split at hl
  · next hv =>
    cases hl
    rw [if_pos (validAccess_inj h hf hv)]
    refine ⟨_, rfl, decodeVal_inject chunk (getN_inj h hf _ _ ?_)⟩
    simp only [validAccess, Bool.and_eq_true] at hv
    rw [sizeChunkNat_cast]; exact hv.1
  · cases hl

/-- `Memory.loadbytes_inj` -/
theorem loadbytes_inj (h : MemInj f m1 m2) {len : _root_.Int} {b1 b2 : Block}
    {delta ofs : _root_.Int} {bytes1 : List MemVal}
    (hl : loadbytes m1 b1 ofs len = some bytes1) (hf : f b1 = some (b2, delta)) :
    ∃ bytes2, loadbytes m2 b2 (ofs + delta) len = some bytes2 ∧
      MemvalInjectList f bytes1 bytes2 := by
  unfold loadbytes at hl ⊢
  split at hl
  · next hr =>
    cases hl
    have hr2 := rangePerm_inj h hr hf
    rw [show ofs + len + delta = ofs + delta + len by omega] at hr2
    rw [if_pos hr2]
    refine ⟨_, rfl, ?_⟩
    by_cases hlen : 0 ≤ len
    · apply getN_inj h hf
      rwa [Int.toNat_of_nonneg hlen]
    · rw [show len.toNat = 0 by omega]; exact .nil
  · cases hl

/-! ### Stores -/

/-- `Memory.setN_inj` -/
theorem setN_inj (access : _root_.Int → Prop) (delta : _root_.Int) {vl1 vl2 : List MemVal}
    (hv : MemvalInjectList f vl1 vl2) :
    ∀ (p : _root_.Int) (c1 c2 : ZMap MemVal),
      (∀ q, access q → MemvalInject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) →
      ∀ q, access q → MemvalInject f (ZMap.get q (setN vl1 p c1))
        (ZMap.get (q + delta) (setN vl2 (p + delta) c2)) := by
  induction hv with
  | nil => intro p c1 c2 h; exact h
  | @cons a b _ _ ha _ ih =>
    intro p c1 c2 h
    show ∀ q, access q → MemvalInject f (ZMap.get q (setN _ (p + 1) (ZMap.set p a c1)))
      (ZMap.get (q + delta) (setN _ (p + delta + 1) (ZMap.set (p + delta) b c2)))
    rw [show p + delta + 1 = (p + 1) + delta by omega]
    apply ih
    intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [ZMap.gss, ZMap.gss]; exact ha
    · rw [ZMap.gso p q _ _ (Ne.symm hqp), ZMap.gso (p + delta) (q + delta) _ _ (by omega)]
      exact h q hq

/-- `Memory.meminj_no_overlap` -/
def MeminjNoOverlap (f : Val.Meminj) (m : Mem) : Prop :=
  ∀ (b1 b1' : Block) (delta1 : _root_.Int) (b2 b2' : Block) (delta2 ofs1 ofs2 : _root_.Int),
    b1 ≠ b2 → f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
    perm m b1 ofs1 .Max .Nonempty = true → perm m b2 ofs2 .Max .Nonempty = true →
    b1' ≠ b2' ∨ ofs1 + delta1 ≠ ofs2 + delta2

/-- A writable chunk carries `Max`/`Nonempty` permission at each of its bytes. -/
theorem validAccess_perm_nonempty {m : Mem} {chunk : Chunk} {b : Block} {ofs : _root_.Int}
    {p : Permission} (hv : validAccess m chunk b ofs p = true) {i : _root_.Int}
    (h1 : ofs ≤ i) (h2 : i < ofs + sizeChunk chunk) : perm m b i .Max .Nonempty = true := by
  have := rangePerm_perm m b _ _ _ _ (validAccess_rangePerm_max hv) i h1 h2
  exact perm_implies this (by cases p <;> rfl)

/-- `Memory.store_mapped_inj` -/
theorem store_mapped_inj (h : MemInj f m1 m2) {chunk : Chunk} {b1 b2 : Block}
    {ofs delta : _root_.Int} {v1 v2 : Val} {n1 : Mem}
    (hs : store chunk m1 b1 ofs v1 = some n1) (hno : MeminjNoOverlap f m1)
    (hf : f b1 = some (b2, delta)) (hv : Val.Inject f v1 v2) :
    ∃ n2, store chunk m2 b2 (ofs + delta) v2 = some n2 ∧ MemInj f n1 n2 := by
  have hva1 := store_valid_access hs
  obtain ⟨n2, hs2⟩ := valid_access_store v2 (validAccess_inj h hf hva1)
  refine ⟨n2, hs2, ⟨?_, ?_, ?_⟩⟩
  · intro b b' d o k p hfb hp
    rw [perm_store hs] at hp
    rw [perm_store hs2]
    exact h.perm _ _ _ _ _ _ hfb hp
  · intro b b' d o sz p hfb hsz hr
    rw [rangePerm_store_eq hs] at hr
    exact h.align _ _ _ _ _ _ hfb hsz hr
  · intro b0 o b3 d0 hfb hp
    rw [perm_store hs] at hp
    rw [store_contents hs, store_contents hs2, PMap.gsspec, PMap.gsspec]
    by_cases hb0 : b0 = b1
    · subst hb0
      rw [hf] at hfb
      cases hfb
      rw [if_pos rfl, if_pos rfl]
      exact setN_inj (fun o => perm m1 b0 o .Cur .Readable = true) delta
        (encodeVal_inject chunk hv) ofs _ _ (fun q hq => h.memval _ _ _ _ hf hq) o hp
    · rw [if_neg hb0]
      by_cases hb3 : b3 = b2
      · subst hb3
        rw [if_pos rfl, setN_outside]
        · exact h.memval _ _ _ _ hfb hp
        · rw [length_encodeVal, sizeChunkNat_cast]
          rcases Int.lt_or_le (o + d0) (ofs + delta) with hlt | hge
          · exact Or.inl hlt
          rcases Int.lt_or_le (o + d0) (ofs + delta + sizeChunk chunk) with hlt2 | hge2
          · exfalso
            have hr := hno b0 b3 d0 b1 b3 delta o (o + d0 - delta) hb0 hfb hf
              (perm_max (perm_implies hp (by rfl)))
              (validAccess_perm_nonempty hva1 (by omega) (by omega))
            rcases hr with hr | hr
            · exact hr rfl
            · exact hr (by omega)
          · exact Or.inr hge2
      · rw [if_neg hb3]
        exact h.memval _ _ _ _ hfb hp

/-- `Memory.store_unmapped_inj` -/
theorem store_unmapped_inj (h : MemInj f m1 m2) {chunk : Chunk} {b1 : Block} {ofs : _root_.Int}
    {v1 : Val} {n1 : Mem} (hs : store chunk m1 b1 ofs v1 = some n1) (hf : f b1 = none) :
    MemInj f n1 m2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro b b' d o k p hfb hp
    rw [perm_store hs] at hp
    exact h.perm _ _ _ _ _ _ hfb hp
  · intro b b' d o sz p hfb hsz hr
    rw [rangePerm_store_eq hs] at hr
    exact h.align _ _ _ _ _ _ hfb hsz hr
  · intro b0 o b3 d0 hfb hp
    rw [perm_store hs] at hp
    rw [store_contents hs, PMap.gso]
    · exact h.memval _ _ _ _ hfb hp
    · intro he; subst he; rw [hf] at hfb; cases hfb

/-- `Memory.store_outside_inj` -/
theorem store_outside_inj (h : MemInj f m1 m2) {chunk : Chunk} {b : Block} {ofs : _root_.Int}
    {v : Val} {m2' : Mem}
    (hout : ∀ b' delta (ofs' : _root_.Int), f b' = some (b, delta) →
      perm m1 b' ofs' .Cur .Readable = true → ofs ≤ ofs' + delta →
      ofs' + delta < ofs + sizeChunk chunk → False)
    (hs : store chunk m2 b ofs v = some m2') : MemInj f m1 m2' := by
  refine ⟨?_, h.align, ?_⟩
  · intro b1 b' d o k p hfb hp
    rw [perm_store hs]
    exact h.perm _ _ _ _ _ _ hfb hp
  · intro b0 o b3 d0 hfb hp
    rw [store_contents hs, PMap.gsspec]
    by_cases hb : b3 = b
    · subst hb
      rw [if_pos rfl, setN_outside]
      · exact h.memval _ _ _ _ hfb hp
      · rw [length_encodeVal, sizeChunkNat_cast]
        rcases Int.lt_or_le (o + d0) ofs with hlt | hge
        · exact Or.inl hlt
        rcases Int.lt_or_le (o + d0) (ofs + sizeChunk chunk) with hlt2 | hge2
        · exact (hout b0 d0 o hfb hp hge hlt2).elim
        · exact Or.inr hge2
    · rw [if_neg hb]
      exact h.memval _ _ _ _ hfb hp

/-! ### Allocation and freeing -/

/-- A block carrying a permission is not the next fresh block. -/
theorem ne_nextblock_of_perm {m : Mem} {b : Block} {ofs : Z} {k : PermKind} {p : Permission}
    (h : perm m b ofs k p = true) : b ≠ m.nextblock := by
  intro he
  have := perm_valid_block m b ofs k p h
  rw [he, Positive.lt_iff] at this
  exact Nat.lt_irrefl _ this

/-- `Memory.perm_alloc_1` -/
theorem perm_alloc_1 {m : Mem} {lo hi : Z} {b : Block} {ofs : Z} {k : PermKind}
    {p : Permission} (h : perm m b ofs k p = true) : perm (alloc m lo hi).1 b ofs k p = true := by
  rw [perm_alloc_other m lo hi b (ne_nextblock_of_perm h)]; exact h

/-- `Memory.perm_alloc_inv` -/
theorem perm_alloc_inv {m : Mem} {lo hi : _root_.Int} {b : Block} {ofs : _root_.Int}
    {k : PermKind} {p : Permission} (h : perm (alloc m lo hi).1 b ofs k p = true) :
    if b = m.nextblock then lo ≤ ofs ∧ ofs < hi else perm m b ofs k p = true := by
  split
  · next he =>
    subst he
    rcases Int.lt_or_le ofs lo with h1 | h1
    · rw [perm_alloc_outside m lo hi ofs k p (Or.inl h1)] at h; cases h
    rcases Int.lt_or_le ofs hi with h2 | h2
    · exact ⟨h1, h2⟩
    · rw [perm_alloc_outside m lo hi ofs k p (Or.inr h2)] at h; cases h
  · next hne => rwa [perm_alloc_other m lo hi b hne] at h

/-- `Memory.perm_free_3` -/
theorem perm_free_3 {m : Mem} {b : Block} {lo hi : _root_.Int} {b' : Block} {ofs : _root_.Int}
    {k : PermKind} {p : Permission} (h : perm (uncheckedFree m b lo hi) b' ofs k p = true) :
    perm m b' ofs k p = true := by
  by_cases hb : b' = b
  · subst hb
    rcases Int.lt_or_le ofs lo with h1 | h1
    · rwa [perm_free_outside m b' lo hi ofs k p (Or.inl h1)] at h
    rcases Int.lt_or_le ofs hi with h2 | h2
    · rw [perm_free_inside m b' lo hi ofs k p h1 h2] at h; cases h
    · rwa [perm_free_outside m b' lo hi ofs k p (Or.inr h2)] at h
  · rwa [perm_free_other m b lo hi b' hb] at h

/-- `Memory.perm_free_1` -/
theorem perm_free_1 {m : Mem} {b : Block} {lo hi : _root_.Int} {b' : Block} {ofs : _root_.Int}
    {k : PermKind} {p : Permission} (hout : b' ≠ b ∨ ofs < lo ∨ hi ≤ ofs)
    (h : perm m b' ofs k p = true) : perm (uncheckedFree m b lo hi) b' ofs k p = true := by
  rcases hout with hb | hr
  · rwa [perm_free_other m b lo hi b' hb]
  · by_cases hb : b' = b
    · subst hb; rwa [perm_free_outside m b' lo hi ofs k p hr]
    · rwa [perm_free_other m b lo hi b' hb]

theorem alloc_eq {m : Mem} {lo hi : Z} {m' : Mem} {b : Block} (h : alloc m lo hi = (m', b)) :
    m' = (alloc m lo hi).1 ∧ b = m.nextblock := by
  rw [h]; exact ⟨rfl, (congrArg Prod.snd h).symm⟩

/-- `Memory.alloc_right_inj` -/
theorem alloc_right_inj (h : MemInj f m1 m2) {lo hi : Z} {b2 : Block} {m2' : Mem}
    (ha : alloc m2 lo hi = (m2', b2)) : MemInj f m1 m2' := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  refine ⟨fun b1 b2 d o k p hf hp => perm_alloc_1 (h.perm _ _ _ _ _ _ hf hp), h.align, ?_⟩
  intro b1 o b3 d hf hp
  have hp2 := h.perm _ _ _ _ _ _ hf hp
  rw [alloc_contents, PMap.gso _ _ _ _ (Ne.symm (ne_nextblock_of_perm hp2))]
  exact h.memval _ _ _ _ hf hp

/-- `Memory.alloc_left_unmapped_inj` -/
theorem alloc_left_unmapped_inj (h : MemInj f m1 m2) {lo hi : Z} {b1 : Block} {m1' : Mem}
    (ha : alloc m1 lo hi = (m1', b1)) (hf : f b1 = none) : MemInj f m1' m2 := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  have hother : ∀ {b b' d}, f b = some (b', d) → b ≠ m1.nextblock := by
    intro b b' d hfb he; subst he; rw [hf] at hfb; cases hfb
  refine ⟨?_, ?_, ?_⟩
  · intro b b' d o k p hfb hp
    rw [perm_alloc_other m1 lo hi b (hother hfb)] at hp
    exact h.perm _ _ _ _ _ _ hfb hp
  · intro b b' d o sz p hfb hsz hr
    rw [rangePerm_congr (fun o => perm_alloc_other m1 lo hi b (hother hfb) o .Max p)] at hr
    exact h.align _ _ _ _ _ _ hfb hsz hr
  · intro b o b' d hfb hp
    rw [perm_alloc_other m1 lo hi b (hother hfb)] at hp
    rw [alloc_contents, PMap.gso _ _ _ _ (Ne.symm (hother hfb))]
    exact h.memval _ _ _ _ hfb hp

/-- `Memory.alloc_left_mapped_inj` -/
theorem alloc_left_mapped_inj (h : MemInj f m1 m2) {lo hi : _root_.Int} {b1 b2 : Block}
    {delta : _root_.Int} {m1' : Mem}
    (ha : alloc m1 lo hi = (m1', b1))
    (hal : minSafeAlignment (hi - lo) ∣ delta)
    (hperm : ∀ (ofs : _root_.Int) k p, lo ≤ ofs → ofs < hi → perm m2 b2 (ofs + delta) k p = true)
    (hf : f b1 = some (b2, delta)) : MemInj f m1' m2 := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  refine ⟨?_, ?_, ?_⟩
  · intro b b' d o k p hfb hp
    have hi := perm_alloc_inv hp
    split at hi
    · next he => subst he; rw [hf] at hfb; cases hfb; exact hperm o k p hi.1 hi.2
    · exact h.perm _ _ _ _ _ _ hfb hi
  · intro b b' d o sz p hfb hsz hr
    by_cases he : b = m1.nextblock
    · subst he
      rw [hf] at hfb; cases hfb
      have hA := perm_alloc_inv (rangePerm_perm _ _ _ _ _ _ hr o (Int.le_refl _) (by omega))
      have hB := perm_alloc_inv (rangePerm_perm _ _ _ _ _ _ hr (o + sz - 1) (by omega) (by omega))
      rw [if_pos rfl] at hA hB
      exact Int.dvd_trans (minSafeAlignment_mono (by omega)) hal
    · rw [rangePerm_congr (fun o => perm_alloc_other m1 lo hi b he o .Max p)] at hr
      exact h.align _ _ _ _ _ _ hfb hsz hr
  · intro b o b' d hfb hp
    have hi := perm_alloc_inv hp
    rw [alloc_contents, PMap.gsspec]
    split at hi
    · next he => rw [if_pos he, ZMap.gi]; exact .undef _
    · next he => rw [if_neg he]; exact h.memval _ _ _ _ hfb hi

/-- `Memory.free_left_inj` -/
theorem free_left_inj (h : MemInj f m1 m2) {b : Block} {lo hi : _root_.Int} {m1' : Mem}
    (hfr : free m1 b lo hi = some m1') : MemInj f m1' m2 := by
  rw [free_result hfr]
  refine ⟨fun b1 b2 d o k p hf hp => h.perm _ _ _ _ _ _ hf (perm_free_3 hp), ?_,
    fun b1 o b2 d hf hp => h.memval _ _ _ _ hf (perm_free_3 hp)⟩
  intro b1 b2 d o sz p hf hsz hr
  exact h.align _ _ _ _ _ _ hf hsz
    (rangePerm_intro _ _ _ _ _ _ fun i h1 h2 => perm_free_3 (rangePerm_perm _ _ _ _ _ _ hr i h1 h2))

/-- `Memory.free_right_inj` -/
theorem free_right_inj (h : MemInj f m1 m2) {b : Block} {lo hi : _root_.Int} {m2' : Mem}
    (hfr : free m2 b lo hi = some m2')
    (hout : ∀ b' delta (ofs : _root_.Int) k p, f b' = some (b, delta) →
      perm m1 b' ofs k p = true → lo ≤ ofs + delta → ofs + delta < hi → False) :
    MemInj f m1 m2' := by
  rw [free_result hfr]
  have hperm : ∀ b1 b2 d (o : _root_.Int) k p, f b1 = some (b2, d) → perm m1 b1 o k p = true →
      perm (uncheckedFree m2 b lo hi) b2 (o + d) k p = true := by
    intro b1 b2 d o k p hf hp
    apply perm_free_1 _ (h.perm _ _ _ _ _ _ hf hp)
    by_cases hb : b2 = b
    · subst hb
      right
      rcases Int.lt_or_le (o + d) lo with h1 | h1
      · exact Or.inl h1
      rcases Int.lt_or_le (o + d) hi with h2 | h2
      · exact (hout b1 d o k p hf hp h1 h2).elim
      · exact Or.inr h2
    · exact Or.inl hb
  exact ⟨hperm, h.align, fun b1 o b2 d hf hp => h.memval _ _ _ _ hf hp⟩

/-! ### Composition -/

/-- `Memory.mem_inj_compose` -/
theorem memInj_compose {f f' : Val.Meminj} {m1 m2 m3 : Mem} (h12 : MemInj f m1 m2)
    (h23 : MemInj f' m2 m3) : MemInj (Val.compose_meminj f f') m1 m3 := by
  have dec : ∀ {b1 b3 d}, Val.compose_meminj f f' b1 = some (b3, d) →
      ∃ b2 d1 d2, f b1 = some (b2, d1) ∧ f' b2 = some (b3, d2) ∧ d = d1 + d2 := by
    intro b1 b3 d hc
    simp only [Val.compose_meminj] at hc
    split at hc
    · cases hc
    · next b2 d1 hf =>
      split at hc
      · cases hc
      · next b3' d2 hf' =>
        cases hc
        exact ⟨b2, d1, d2, hf, hf', rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro b1 b3 d o k p hc hp
    obtain ⟨b2, d1, d2, hf, hf', rfl⟩ := dec hc
    have := h23.perm _ _ _ _ _ _ hf' (h12.perm _ _ _ _ _ _ hf hp)
    rwa [Int.add_assoc] at this
  · intro b1 b3 d o sz p hc hsz hr
    obtain ⟨b2, d1, d2, hf, hf', rfl⟩ := dec hc
    have hr2 := rangePerm_inj h12 hr hf
    rw [show o + sz + d1 = (o + d1) + sz by omega] at hr2
    exact Int.dvd_add (h12.align _ _ _ _ _ _ hf hsz hr)
      (h23.align _ _ _ _ _ _ hf' hsz hr2)
  · intro b1 o b3 d hc hp
    obtain ⟨b2, d1, d2, hf, hf', rfl⟩ := dec hc
    have := h23.memval _ _ _ _ hf' (h12.perm _ _ _ _ _ _ hf hp)
    rw [Int.add_assoc] at this
    exact MemvalInject.compose (h12.memval _ _ _ _ hf hp) this

/-! ### `storebytes` -/

theorem memvalInjectList_length_eq {vl1 vl2 : List MemVal} (h : MemvalInjectList f vl1 vl2) :
    vl1.length = vl2.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- `Memory.storebytes_range_perm` -/
theorem storebytes_rangePerm {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    (h : storebytes m b ofs bytes = some m') :
    rangePerm m b ofs (ofs + (bytes.length : Z)) .Cur .Writable = true := by
  unfold storebytes at h
  split at h
  · assumption
  · cases h

/-- `Memory.storebytes_mapped_inj` -/
theorem storebytes_mapped_inj (h : MemInj f m1 m2) {b1 b2 : Block} {ofs delta : _root_.Int}
    {bytes1 bytes2 : List MemVal} {n1 : Mem}
    (hs : storebytes m1 b1 ofs bytes1 = some n1) (hno : MeminjNoOverlap f m1)
    (hf : f b1 = some (b2, delta)) (hv : MemvalInjectList f bytes1 bytes2) :
    ∃ n2, storebytes m2 b2 (ofs + delta) bytes2 = some n2 ∧ MemInj f n1 n2 := by
  have hr1 := storebytes_rangePerm hs
  have hlen := memvalInjectList_length_eq hv
  have hr2 := rangePerm_inj h hr1 hf
  rw [show ofs + (bytes1.length : _root_.Int) + delta = ofs + delta + (bytes2.length : _root_.Int)
    by omega] at hr2
  obtain ⟨n2, hs2⟩ := storebytes_isSome hr2
  refine ⟨n2, hs2, ⟨?_, ?_, ?_⟩⟩
  · intro b b' d o k p hfb hp
    rw [perm_storebytes hs] at hp
    rw [perm_storebytes hs2]
    exact h.perm _ _ _ _ _ _ hfb hp
  · intro b b' d o sz p hfb hsz hr
    rw [rangePerm_congr (fun o => perm_storebytes hs b o .Max p)] at hr
    exact h.align _ _ _ _ _ _ hfb hsz hr
  · intro b0 o b3 d0 hfb hp
    rw [perm_storebytes hs] at hp
    rw [storebytes_contents hs, storebytes_contents hs2, PMap.gsspec, PMap.gsspec]
    by_cases hb0 : b0 = b1
    · subst hb0
      rw [hf] at hfb
      cases hfb
      rw [if_pos rfl, if_pos rfl]
      exact setN_inj (fun o => perm m1 b0 o .Cur .Readable = true) delta hv ofs _ _
        (fun q hq => h.memval _ _ _ _ hf hq) o hp
    · rw [if_neg hb0]
      by_cases hb3 : b3 = b2
      · subst hb3
        rw [if_pos rfl, setN_outside]
        · exact h.memval _ _ _ _ hfb hp
        · rcases Int.lt_or_le (o + d0) (ofs + delta) with hlt | hge
          · exact Or.inl hlt
          rcases Int.lt_or_le (o + d0) (ofs + delta + (bytes2.length : _root_.Int)) with hlt2 | hge2
          · exfalso
            have hq := perm_cur_max (perm_implies
              (rangePerm_perm _ _ _ _ _ _ hr1 (o + d0 - delta) (by omega) (by omega))
              (show permOrder .Writable .Nonempty = true by rfl))
            rcases hno b0 b3 d0 b1 b3 delta o (o + d0 - delta) hb0 hfb hf
              (perm_max (perm_implies hp (by rfl))) hq with hr | hr
            · exact hr rfl
            · exact hr (by omega)
          · exact Or.inr hge2
      · rw [if_neg hb3]
        exact h.memval _ _ _ _ hfb hp

/-- `Memory.storebytes_unmapped_inj` -/
theorem storebytes_unmapped_inj (h : MemInj f m1 m2) {b1 : Block} {ofs : _root_.Int}
    {bytes1 : List MemVal} {n1 : Mem} (hs : storebytes m1 b1 ofs bytes1 = some n1)
    (hf : f b1 = none) : MemInj f n1 m2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro b b' d o k p hfb hp
    rw [perm_storebytes hs] at hp
    exact h.perm _ _ _ _ _ _ hfb hp
  · intro b b' d o sz p hfb hsz hr
    rw [rangePerm_congr (fun o => perm_storebytes hs b o .Max p)] at hr
    exact h.align _ _ _ _ _ _ hfb hsz hr
  · intro b0 o b3 d0 hfb hp
    rw [perm_storebytes hs] at hp
    rw [storebytes_contents hs, PMap.gso]
    · exact h.memval _ _ _ _ hfb hp
    · intro he; subst he; rw [hf] at hfb; cases hfb

/-- `Memory.storebytes_outside_inj` -/
theorem storebytes_outside_inj (h : MemInj f m1 m2) {b : Block} {ofs : _root_.Int}
    {bytes2 : List MemVal} {m2' : Mem}
    (hout : ∀ b' delta (ofs' : _root_.Int), f b' = some (b, delta) →
      perm m1 b' ofs' .Cur .Readable = true → ofs ≤ ofs' + delta →
      ofs' + delta < ofs + (bytes2.length : _root_.Int) → False)
    (hs : storebytes m2 b ofs bytes2 = some m2') : MemInj f m1 m2' := by
  refine ⟨?_, h.align, ?_⟩
  · intro b1 b' d o k p hfb hp
    rw [perm_storebytes hs]
    exact h.perm _ _ _ _ _ _ hfb hp
  · intro b0 o b3 d0 hfb hp
    rw [storebytes_contents hs, PMap.gsspec]
    by_cases hb : b3 = b
    · subst hb
      rw [if_pos rfl, setN_outside]
      · exact h.memval _ _ _ _ hfb hp
      · rcases Int.lt_or_le (o + d0) ofs with hlt | hge
        · exact Or.inl hlt
        rcases Int.lt_or_le (o + d0) (ofs + (bytes2.length : _root_.Int)) with hlt2 | hge2
        · exact (hout b0 d0 o hfb hp hge hlt2).elim
        · exact Or.inr hge2
    · rw [if_neg hb]
      exact h.memval _ _ _ _ hfb hp

end MemInj

end Mem
end CC
