/-
  Memory extensions — port of the `EXTENDS` section of `common/Memory.v`.

  `Extends m1 m2` says that `m2` has the same blocks as `m1`, at least the same
  permissions, and contents that are at least as defined (`memval_lessdef`).
  It is the memory relation of the compiler passes that do not change the
  block structure (e.g. `Selection`, `Tailcall`, constant propagation), and it
  is what `Mem.inject` reduces to for the identity injection.
-/
import CCLib.common.MemoryInject

namespace CC
namespace Mem

/-- `Memory.extends` -/
structure Extends (m1 m2 : Mem) : Prop where
  next : m1.nextblock = m2.nextblock
  inj : MemInj Val.inject_id m1 m2
  perm_inv : ∀ b ofs k p, perm m2 b ofs k p = true →
    perm m1 b ofs k p = true ∨ perm m1 b ofs .Max .Nonempty = false

section
variable {m1 m2 : Mem}

theorem inject_id_eq {b b' : Block} {d : Z} (h : Val.inject_id b = some (b', d)) :
    b' = b ∧ d = 0 := by
  simp only [Val.inject_id, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- The identity injection never maps two different blocks to the same one. -/
theorem inject_id_noOverlap (m : Mem) : MeminjNoOverlap Val.inject_id m := by
  intro b1 b1' d1 b2 b2' d2 o1 o2 hne h1 h2 _ _
  obtain ⟨rfl, rfl⟩ := inject_id_eq h1
  obtain ⟨rfl, rfl⟩ := inject_id_eq h2
  exact Or.inl hne

/-- `Memory.extends_refl` -/
theorem extends_refl (m : Mem) : Extends m m := by
  refine ⟨rfl, ⟨?_, ?_, ?_⟩, fun _ _ _ _ h => Or.inl h⟩
  · intro b1 b2 d o k p hf hp
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    rwa [Int.add_zero]
  · intro b1 b2 d o sz p hf _ _
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    exact Int.dvd_zero _
  · intro b1 o b2 d hf _
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    rw [Int.add_zero]
    exact memvalLessdef_refl _

/-- `Memory.load_extends` -/
theorem load_extends (h : Extends m1 m2) {chunk : Chunk} {b : Block} {ofs : _root_.Int}
    {v1 : Val} (hl : load chunk m1 b ofs = some v1) :
    ∃ v2, load chunk m2 b ofs = some v2 ∧ Val.Lessdef v1 v2 := by
  obtain ⟨v2, hl2, hv⟩ := load_inj h.inj hl (rfl : Val.inject_id b = some (b, 0))
  rw [Int.add_zero] at hl2
  exact ⟨v2, hl2, Val.lessdef_inject_id.mpr hv⟩

/-- `Memory.loadv_extends` -/
theorem loadv_extends (h : Extends m1 m2) {chunk : Chunk} {addr1 addr2 v1 : Val}
    (hl : loadv chunk m1 addr1 = some v1) (ha : Val.Lessdef addr1 addr2) :
    ∃ v2, loadv chunk m2 addr2 = some v2 ∧ Val.Lessdef v1 v2 := by
  cases ha with
  | refl =>
    cases addr1 <;> simp only [loadv] at hl ⊢ <;> try cases hl
    split at hl
    · next hc => rw [if_pos hc]; exact load_extends h hl
    · cases hl
  | undef => simp [loadv] at hl

/-- `Memory.loadbytes_extends` -/
theorem loadbytes_extends (h : Extends m1 m2) {b : Block} {ofs len : _root_.Int}
    {bytes1 : List MemVal} (hl : loadbytes m1 b ofs len = some bytes1) :
    ∃ bytes2, loadbytes m2 b ofs len = some bytes2 ∧
      MemvalInjectList Val.inject_id bytes1 bytes2 := by
  have := loadbytes_inj h.inj hl (rfl : Val.inject_id b = some (b, 0))
  rwa [Int.add_zero] at this

/-- `Memory.store_within_extends` -/
theorem store_within_extends (h : Extends m1 m2) {chunk : Chunk} {b : Block}
    {ofs : _root_.Int} {v1 v2 : Val} {m1' : Mem}
    (hs : store chunk m1 b ofs v1 = some m1') (hv : Val.Lessdef v1 v2) :
    ∃ m2', store chunk m2 b ofs v2 = some m2' ∧ Extends m1' m2' := by
  obtain ⟨m2', hs2, hinj⟩ := store_mapped_inj h.inj hs (inject_id_noOverlap m1)
    (rfl : Val.inject_id b = some (b, 0)) (Val.lessdef_inject_id.mp hv)
  rw [Int.add_zero] at hs2
  refine ⟨m2', hs2, ⟨?_, hinj, ?_⟩⟩
  · rw [store_nextblock hs, store_nextblock hs2]; exact h.next
  · intro b' o k p hp
    rw [perm_store hs2] at hp
    rw [perm_store hs, perm_store hs]
    exact h.perm_inv _ _ _ _ hp

/-- `Memory.store_outside_extends` -/
theorem store_outside_extends (h : Extends m1 m2) {chunk : Chunk} {b : Block}
    {ofs : _root_.Int} {v : Val} {m2' : Mem} (hs : store chunk m2 b ofs v = some m2')
    (hout : ∀ ofs' : _root_.Int, perm m1 b ofs' .Cur .Readable = true → ofs ≤ ofs' →
      ofs' < ofs + sizeChunk chunk → False) : Extends m1 m2' := by
  refine ⟨?_, store_outside_inj h.inj ?_ hs, ?_⟩
  · rw [store_nextblock hs]; exact h.next
  · intro b' d o hf hp h1 h2
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    rw [Int.add_zero] at h1 h2
    exact hout o hp h1 h2
  · intro b' o k p hp
    rw [perm_store hs] at hp
    exact h.perm_inv _ _ _ _ hp

/-- `Memory.storev_extends` -/
theorem storev_extends (h : Extends m1 m2) {chunk : Chunk} {addr1 addr2 v1 v2 : Val}
    {m1' : Mem} (hs : storev chunk m1 addr1 v1 = some m1') (ha : Val.Lessdef addr1 addr2)
    (hv : Val.Lessdef v1 v2) :
    ∃ m2', storev chunk m2 addr2 v2 = some m2' ∧ Extends m1' m2' := by
  cases ha with
  | refl =>
    cases addr1 <;> simp only [storev] at hs ⊢ <;> try cases hs
    split at hs
    · next hc => rw [if_pos hc]; exact store_within_extends h hs hv
    · cases hs
  | undef => simp [storev] at hs

/-- `Memory.alloc_extends` -/
theorem alloc_extends (h : Extends m1 m2) {lo1 hi1 lo2 hi2 : _root_.Int} {b : Block}
    {m1' : Mem} (ha : alloc m1 lo1 hi1 = (m1', b)) (hlo : lo2 ≤ lo1) (hhi : hi1 ≤ hi2) :
    ∃ m2', alloc m2 lo2 hi2 = (m2', b) ∧ Extends m1' m2' := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  have hn := h.next
  refine ⟨(alloc m2 lo2 hi2).1, ?_, ⟨?_, ?_, ?_⟩⟩
  · show ((alloc m2 lo2 hi2).1, m2.nextblock) = _
    rw [hn]
  · show m1.nextblock.succ = m2.nextblock.succ
    rw [hn]
  · refine alloc_left_mapped_inj (alloc_right_inj h.inj (b2 := m2.nextblock) rfl)
      (rfl : alloc m1 lo1 hi1 = ((alloc m1 lo1 hi1).1, m1.nextblock)) (Int.dvd_zero _) ?_
      (rfl : Val.inject_id m1.nextblock = some (m1.nextblock, 0))
    intro o k p h1 h2
    rw [hn, Int.add_zero]
    exact perm_implies (perm_alloc_same m2 lo2 hi2 o k (by omega) (by omega)) (by cases p <;> rfl)
  · intro b' o k p hp
    have hi := perm_alloc_inv hp
    split at hi
    · next he =>
      subst he
      rw [← hn]
      rcases Int.lt_or_le o lo1 with h1 | h1
      · exact Or.inr (perm_alloc_outside m1 lo1 hi1 o .Max .Nonempty (Or.inl h1))
      rcases Int.lt_or_le o hi1 with h2 | h2
      · exact Or.inl (perm_implies (perm_alloc_same m1 lo1 hi1 o k h1 h2) (by cases p <;> rfl))
      · exact Or.inr (perm_alloc_outside m1 lo1 hi1 o .Max .Nonempty (Or.inr h2))
    · next he =>
      have he1 : b' ≠ m1.nextblock := by rw [hn]; exact he
      rw [perm_alloc_other m1 lo1 hi1 b' he1, perm_alloc_other m1 lo1 hi1 b' he1]
      exact h.perm_inv _ _ _ _ hi

/-- `Memory.perm_free_inv`, in the form used below. -/
theorem perm_free_cases {m : Mem} {b : Block} {lo hi : _root_.Int} {b' : Block}
    {ofs : _root_.Int} {k : PermKind} {p : Permission} (h : perm m b' ofs k p = true) :
    (b' = b ∧ lo ≤ ofs ∧ ofs < hi) ∨ perm (uncheckedFree m b lo hi) b' ofs k p = true := by
  by_cases hb : b' = b
  · subst hb
    rcases Int.lt_or_le ofs lo with h1 | h1
    · exact Or.inr (perm_free_1 (Or.inr (Or.inl h1)) h)
    rcases Int.lt_or_le ofs hi with h2 | h2
    · exact Or.inl ⟨rfl, h1, h2⟩
    · exact Or.inr (perm_free_1 (Or.inr (Or.inr h2)) h)
  · exact Or.inr (perm_free_1 (Or.inl hb) h)

theorem perm_free_false {m : Mem} {b : Block} {lo hi : _root_.Int} {b' : Block}
    {ofs : _root_.Int} {k : PermKind} {p : Permission} (h : perm m b' ofs k p = false) :
    perm (uncheckedFree m b lo hi) b' ofs k p = false := by
  cases hc : perm (uncheckedFree m b lo hi) b' ofs k p
  · rfl
  · rw [perm_free_3 hc] at h; cases h

/-- Shared `perm_inv` argument of `free_left_extends` / `free_parallel_extends`. -/
theorem free_perm_inv {m : Mem} {b : Block} {lo hi : _root_.Int} {b' : Block}
    {ofs : _root_.Int} {k : PermKind} {p : Permission}
    (h : perm m b' ofs k p = true ∨ perm m b' ofs .Max .Nonempty = false) :
    perm (uncheckedFree m b lo hi) b' ofs k p = true ∨
      perm (uncheckedFree m b lo hi) b' ofs .Max .Nonempty = false := by
  rcases h with h | h
  · rcases perm_free_cases (b := b) (lo := lo) (hi := hi) h with ⟨rfl, h1, h2⟩ | h
    · exact Or.inr (perm_free_inside m b' lo hi ofs .Max .Nonempty h1 h2)
    · exact Or.inl h
  · exact Or.inr (perm_free_false h)

/-- `Memory.free_left_extends` -/
theorem free_left_extends (h : Extends m1 m2) {b : Block} {lo hi : _root_.Int} {m1' : Mem}
    (hf : free m1 b lo hi = some m1') : Extends m1' m2 := by
  refine ⟨?_, free_left_inj h.inj hf, ?_⟩
  · rw [free_result hf]; exact h.next
  · intro b' o k p hp
    rw [free_result hf]
    exact free_perm_inv (h.perm_inv _ _ _ _ hp)

/-- `Memory.free_right_extends` -/
theorem free_right_extends (h : Extends m1 m2) {b : Block} {lo hi : _root_.Int} {m2' : Mem}
    (hf : free m2 b lo hi = some m2')
    (hout : ∀ (ofs : _root_.Int) k p, perm m1 b ofs k p = true → lo ≤ ofs → ofs < hi → False) :
    Extends m1 m2' := by
  refine ⟨?_, free_right_inj h.inj hf ?_, ?_⟩
  · rw [free_result hf]; exact h.next
  · intro b' d o k p hfb hp h1 h2
    obtain ⟨rfl, rfl⟩ := inject_id_eq hfb
    rw [Int.add_zero] at h1 h2
    exact hout o k p hp h1 h2
  · intro b' o k p hp
    rw [free_result hf] at hp
    exact h.perm_inv _ _ _ _ (perm_free_3 hp)

/-- `Memory.free_parallel_extends` -/
theorem free_parallel_extends (h : Extends m1 m2) {b : Block} {lo hi : _root_.Int} {m1' : Mem}
    (hf : free m1 b lo hi = some m1') :
    ∃ m2', free m2 b lo hi = some m2' ∧ Extends m1' m2' := by
  have hr : rangePerm m2 b lo hi .Cur .Freeable = true := by
    have := rangePerm_inj h.inj (free_rangePerm hf) (rfl : Val.inject_id b = some (b, 0))
    rwa [Int.add_zero, Int.add_zero] at this
  refine ⟨_, free_isSome hr, ⟨?_, ?_, ?_⟩⟩
  · rw [free_result hf]; exact h.next
  · refine free_right_inj (free_left_inj h.inj hf) (free_isSome hr) ?_
    intro b' d o k p hfb hp h1 h2
    obtain ⟨rfl, rfl⟩ := inject_id_eq hfb
    rw [Int.add_zero] at h1 h2
    rw [free_result hf, perm_free_inside m1 _ lo hi o k p h1 h2] at hp
    cases hp
  · intro b' o k p hp
    rw [free_result hf]
    exact free_perm_inv (h.perm_inv _ _ _ _ (perm_free_3 hp))

/-- `Memory.valid_block_extends` -/
theorem validBlock_extends (h : Extends m1 m2) (b : Block) :
    validBlock m1 b = validBlock m2 b := by
  simp only [validBlock, h.next]

/-- `Memory.perm_extends` -/
theorem perm_extends (h : Extends m1 m2) {b : Block} {ofs : _root_.Int} {k : PermKind}
    {p : Permission} (hp : perm m1 b ofs k p = true) : perm m2 b ofs k p = true := by
  have := perm_inj h.inj hp (rfl : Val.inject_id b = some (b, 0))
  rwa [Int.add_zero] at this

/-- `Memory.perm_extends_inv` -/
theorem perm_extends_inv (h : Extends m1 m2) {b : Block} {ofs : _root_.Int} {k : PermKind}
    {p : Permission} (hp : perm m2 b ofs k p = true) :
    perm m1 b ofs k p = true ∨ perm m1 b ofs .Max .Nonempty = false :=
  h.perm_inv _ _ _ _ hp

/-- `Memory.valid_access_extends` -/
theorem validAccess_extends (h : Extends m1 m2) {chunk : Chunk} {b : Block}
    {ofs : _root_.Int} {p : Permission} (hv : validAccess m1 chunk b ofs p = true) :
    validAccess m2 chunk b ofs p = true := by
  have := validAccess_inj h.inj (rfl : Val.inject_id b = some (b, 0)) hv
  rwa [Int.add_zero] at this

/-- `Memory.valid_pointer_extends` -/
theorem validPointer_extends (h : Extends m1 m2) {b : Block} {ofs : _root_.Int}
    (hv : validPointer m1 b ofs = true) : validPointer m2 b ofs = true :=
  perm_extends h hv

/-- `Memory.weak_valid_pointer_extends` -/
theorem weakValidPointer_extends (h : Extends m1 m2) {b : Block} {ofs : _root_.Int}
    (hv : weakValidPointer m1 b ofs = true) : weakValidPointer m2 b ofs = true := by
  simp only [weakValidPointer, Bool.or_eq_true] at hv ⊢
  rcases hv with hv | hv
  · exact Or.inl (validPointer_extends h hv)
  · exact Or.inr (validPointer_extends h hv)

theorem compose_inject_id : Val.compose_meminj Val.inject_id Val.inject_id = Val.inject_id := by
  funext b
  simp [Val.compose_meminj, Val.inject_id]

/-- `Memory.extends_extends_compose` -/
theorem extends_extends_compose {m3 : Mem} (h12 : Extends m1 m2) (h23 : Extends m2 m3) :
    Extends m1 m3 := by
  refine ⟨h12.next.trans h23.next, ?_, ?_⟩
  · have := memInj_compose h12.inj h23.inj
    rwa [compose_inject_id] at this
  · intro b o k p hp
    rcases h23.perm_inv _ _ _ _ hp with hp2 | hp2
    · exact h12.perm_inv _ _ _ _ hp2
    · right
      cases hc : perm m1 b o .Max .Nonempty
      · rfl
      · rw [perm_extends h12 hc] at hp2; cases hp2

/-- `Memory.storebytes_within_extends` -/
theorem storebytes_within_extends (h : Extends m1 m2) {b : Block} {ofs : _root_.Int}
    {bytes1 bytes2 : List MemVal} {m1' : Mem} (hs : storebytes m1 b ofs bytes1 = some m1')
    (hv : MemvalInjectList Val.inject_id bytes1 bytes2) :
    ∃ m2', storebytes m2 b ofs bytes2 = some m2' ∧ Extends m1' m2' := by
  obtain ⟨m2', hs2, hinj⟩ := storebytes_mapped_inj h.inj hs (inject_id_noOverlap m1)
    (rfl : Val.inject_id b = some (b, 0)) hv
  rw [Int.add_zero] at hs2
  refine ⟨m2', hs2, ⟨?_, hinj, ?_⟩⟩
  · rw [storebytes_nextblock hs, storebytes_nextblock hs2]; exact h.next
  · intro b' o k p hp
    rw [perm_storebytes hs2] at hp
    rw [perm_storebytes hs, perm_storebytes hs]
    exact h.perm_inv _ _ _ _ hp

/-- `Memory.storebytes_outside_extends` -/
theorem storebytes_outside_extends (h : Extends m1 m2) {b : Block} {ofs : _root_.Int}
    {bytes2 : List MemVal} {m2' : Mem} (hs : storebytes m2 b ofs bytes2 = some m2')
    (hout : ∀ ofs' : _root_.Int, perm m1 b ofs' .Cur .Readable = true → ofs ≤ ofs' →
      ofs' < ofs + (bytes2.length : _root_.Int) → False) : Extends m1 m2' := by
  refine ⟨?_, storebytes_outside_inj h.inj ?_ hs, ?_⟩
  · rw [storebytes_nextblock hs]; exact h.next
  · intro b' d o hf hp h1 h2
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    rw [Int.add_zero] at h1 h2
    exact hout o hp h1 h2
  · intro b' o k p hp
    rw [perm_storebytes hs] at hp
    exact h.perm_inv _ _ _ _ hp

end

end Mem
end CC
