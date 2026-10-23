/-
  More theorems of `common/Memory.v`: block validity and `nextblock` across
  every operation, the success conditions of `load`/`store`/`free`/
  `dropPerm`, the `loadv`/`storev` wrappers, and `free_list`.
-/
import CCLib.common.MemoryLemmas
import CCLib.lib.IntegersPtrofs

namespace CC

namespace Positive

/-- `toNat` is injective. -/
theorem toNat_inj : ∀ {p q : Positive}, p.toNat = q.toNat → p = q
  | .xH, .xH, _ => rfl
  | .xH, .xO q, h => by have := toNat_pos q; simp only [toNat] at h; omega
  | .xH, .xI q, h => by have := toNat_pos q; simp only [toNat] at h; omega
  | .xO p, .xH, h => by have := toNat_pos p; simp only [toNat] at h; omega
  | .xI p, .xH, h => by have := toNat_pos p; simp only [toNat] at h; omega
  | .xO p, .xO q, h => by
      simp only [toNat] at h; rw [toNat_inj (show p.toNat = q.toNat by omega)]
  | .xI p, .xI q, h => by
      simp only [toNat] at h; rw [toNat_inj (show p.toNat = q.toNat by omega)]
  | .xO p, .xI q, h => by simp only [toNat] at h; omega
  | .xI p, .xO q, h => by simp only [toNat] at h; omega

end Positive

namespace Mem

/-! ## Validity of blocks -/

theorem validBlock_iff (m : Mem) (b : Block) : validBlock m b = true ↔ b.toNat < m.nextblock.toNat := by
  simp [validBlock, Positive.lt_iff]

/-! ## `alloc` -/

/-- `Mem.nextblock_alloc` -/
theorem nextblock_alloc (m : Mem) (lo hi : Z) : (alloc m lo hi).1.nextblock = m.nextblock.succ := rfl

/-- `Mem.valid_block_alloc` -/
theorem valid_block_alloc (m : Mem) (lo hi : Z) {b : Block} (h : validBlock m b = true) :
    validBlock (alloc m lo hi).1 b = true := by
  rw [validBlock_iff] at *; rw [nextblock_alloc, Positive.toNat_succ]; omega

/-- `Mem.valid_new_block` -/
theorem valid_new_block (m : Mem) (lo hi : Z) :
    validBlock (alloc m lo hi).1 (alloc m lo hi).2 = true := by
  rw [validBlock_iff, nextblock_alloc, alloc_result, Positive.toNat_succ]; omega

/-- `Mem.valid_block_alloc_inv` -/
theorem valid_block_alloc_inv (m : Mem) (lo hi : Z) {b : Block}
    (h : validBlock (alloc m lo hi).1 b = true) : b = m.nextblock ∨ validBlock m b = true := by
  rw [validBlock_iff, nextblock_alloc, Positive.toNat_succ] at h
  by_cases hb : b.toNat < m.nextblock.toNat
  · exact Or.inr ((validBlock_iff m b).mpr hb)
  · left
    have : b.toNat = m.nextblock.toNat := by omega
    exact Positive.toNat_inj this

/-! ## `store` / `storebytes` -/

/-- `Mem.store_valid_access_3`: a successful store had write permission. -/
theorem store_valid_access_3 {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (h : store chunk m b ofs v = some m') : validAccess m chunk b ofs .Writable = true :=
  store_valid_access h

/-- `Mem.valid_access_store`: write permission is enough for `store` to succeed. -/
theorem valid_access_store {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} (v : Val)
    (h : validAccess m chunk b ofs .Writable = true) : ∃ m', store chunk m b ofs v = some m' := by
  unfold store; rw [if_pos h]; exact ⟨_, rfl⟩

/-- `Mem.valid_block_store_1` -/
theorem valid_block_store_1 {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (h : store chunk m b ofs v = some m') {b' : Block} (hb : validBlock m b' = true) :
    validBlock m' b' = true := by
  simp only [validBlock] at *; rw [store_nextblock h]; exact hb

/-- `Mem.valid_block_store_2` -/
theorem valid_block_store_2 {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (h : store chunk m b ofs v = some m') {b' : Block} (hb : validBlock m' b' = true) :
    validBlock m b' = true := by
  simp only [validBlock] at *; rw [store_nextblock h] at hb; exact hb

/-- `Mem.perm_store_1`/`perm_store_2`: stores do not change permissions. -/
theorem perm_store_eq {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (h : store chunk m b ofs v = some m') (b' : Block) (ofs' : Z) (k : PermKind) (p : Permission) :
    perm m' b' ofs' k p = perm m b' ofs' k p := by
  simp only [perm, store_access h]

/-- `Mem.valid_block_storebytes_1` -/
theorem valid_block_storebytes_1 {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    (h : storebytes m b ofs bytes = some m') {b' : Block} (hb : validBlock m b' = true) :
    validBlock m' b' = true := by
  simp only [validBlock] at *; rw [storebytes_nextblock h]; exact hb

/-- `Mem.valid_block_storebytes_2` -/
theorem valid_block_storebytes_2 {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    (h : storebytes m b ofs bytes = some m') {b' : Block} (hb : validBlock m' b' = true) :
    validBlock m b' = true := by
  simp only [validBlock] at *; rw [storebytes_nextblock h] at hb; exact hb

/-! ## `load` / `loadbytes` -/

/-- `Mem.load_valid_access` -/
theorem load_valid_access {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val}
    (h : load chunk m b ofs = some v) : validAccess m chunk b ofs .Readable = true := by
  unfold load at h; split at h
  · assumption
  · cases h

/-- `Mem.valid_access_load` -/
theorem valid_access_load {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    (h : validAccess m chunk b ofs .Readable = true) : ∃ v, load chunk m b ofs = some v := by
  unfold load; rw [if_pos h]; exact ⟨_, rfl⟩

/-- `Mem.loadbytes_range_perm` -/
theorem loadbytes_range_perm {m : Mem} {b : Block} {ofs n : Z} {bytes : List MemVal}
    (h : loadbytes m b ofs n = some bytes) : rangePerm m b ofs (ofs + n) .Cur .Readable = true := by
  unfold loadbytes at h; split at h
  · assumption
  · cases h

/-- `Mem.range_perm_loadbytes` -/
theorem range_perm_loadbytes {m : Mem} {b : Block} {ofs n : Z}
    (h : rangePerm m b ofs (ofs + n) .Cur .Readable = true) :
    ∃ bytes, loadbytes m b ofs n = some bytes := by
  unfold loadbytes; rw [if_pos h]; exact ⟨_, rfl⟩

/-! ## `loadv` / `storev` -/

/-- The no-wrap-around side condition of `loadv`/`storev` at offset `o`, or a
chunk whose alignment already rules wrapping out (every chunk except
`Mfloat64`/`Many64`, which are 8 bytes but only 4-byte aligned). -/
def ChunkNoWrap (chunk : Chunk) (o : Z) : Prop :=
  alignChunk chunk = sizeChunk chunk ∨ o + sizeChunk chunk ≤ Integers.Ptrofs.modulus

theorem ptrofs_modulus_eq : (Integers.Ptrofs.modulus : _root_.Int) = 18446744073709551616 := rfl

/-- An aligned access at an in-range offset never wraps around, provided the
chunk's alignment equals its size. -/
theorem noWrap_of_aligned (chunk : Chunk) (o : _root_.Int) (h0 : 0 ≤ o)
    (hlt : o < Integers.Ptrofs.modulus) (hal : o % alignChunk chunk = 0)
    (hw : ChunkNoWrap chunk o) : o + sizeChunk chunk ≤ Integers.Ptrofs.modulus := by
  rcases hw with hc | hb
  · rw [ptrofs_modulus_eq] at hlt ⊢
    cases chunk <;> simp only [alignChunk, sizeChunk] at hc hal ⊢ <;>
      first
      | (have : o % 1 = 0 := hal; omega)
      | (have : o % 2 = 0 := hal; omega)
      | (have : o % 4 = 0 := hal; omega)
      | (have : o % 8 = 0 := hal; omega)
      | cases hc
  · exact hb

/-- `Mem.loadv` on a pointer is `load` at its unsigned offset, when the access
cannot wrap around (always the case except for 4-aligned 8-byte chunks). -/
theorem loadv_ptr (chunk : Chunk) (m : Mem) (b : Block) (ofs : Integers.Ptrofs)
    (hw : ChunkNoWrap chunk (Integers.Ptrofs.unsigned ofs)) :
    loadv chunk m (.Vptr b ofs) = load chunk m b (Integers.Ptrofs.unsigned ofs) := by
  simp only [loadv]
  split
  · rfl
  · next hn =>
    cases hl : load chunk m b (Integers.Ptrofs.unsigned ofs) with
    | none => rfl
    | some v =>
      have hv := load_valid_access hl
      simp only [validAccess, Bool.and_eq_true, beq_iff_eq] at hv
      have hr := Integers.Ptrofs.unsigned_range ofs
      exact absurd (noWrap_of_aligned chunk _ hr.1 hr.2 hv.2 hw) hn

/-- `Mem.storev` on a pointer is `store` at its unsigned offset, under the same
condition as `loadv_ptr`. -/
theorem storev_ptr (chunk : Chunk) (m : Mem) (b : Block) (ofs : Integers.Ptrofs) (v : Val)
    (hw : ChunkNoWrap chunk (Integers.Ptrofs.unsigned ofs)) :
    storev chunk m (.Vptr b ofs) v = store chunk m b (Integers.Ptrofs.unsigned ofs) v := by
  simp only [storev]
  split
  · rfl
  · next hn =>
    cases hs : store chunk m b (Integers.Ptrofs.unsigned ofs) v with
    | none => rfl
    | some m' =>
      have hv := store_valid_access hs
      simp only [validAccess, Bool.and_eq_true, beq_iff_eq] at hv
      have hr := Integers.Ptrofs.unsigned_range ofs
      exact absurd (noWrap_of_aligned chunk _ hr.1 hr.2 hv.2 hw) hn

/-- A successful `loadv` is a successful `load`. -/
theorem loadv_load {chunk : Chunk} {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {v : Val}
    (h : loadv chunk m (.Vptr b ofs) = some v) :
    load chunk m b (Integers.Ptrofs.unsigned ofs) = some v := by
  simp only [loadv] at h
  split at h
  · exact h
  · cases h

/-- A successful `storev` is a successful `store`. -/
theorem storev_store {chunk : Chunk} {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {v : Val}
    {m' : Mem} (h : storev chunk m (.Vptr b ofs) v = some m') :
    store chunk m b (Integers.Ptrofs.unsigned ofs) v = some m' := by
  simp only [storev] at h
  split at h
  · exact h
  · cases h

/-- `Mem.loadv_storev_same` -/
theorem loadv_storev_same {chunk : Chunk} {m : Mem} {addr v : Val} {m' : Mem}
    (h : storev chunk m addr v = some m') : loadv chunk m' addr = some (Val.loadResult chunk v) := by
  cases addr with
  | Vptr b ofs =>
    simp only [storev] at h
    simp only [loadv]
    split at h
    · next hc => rw [if_pos hc]; exact load_store_same h
    · cases h
  | _ => cases h

/-- `Mem.storev_nextblock` -/
theorem storev_nextblock {chunk : Chunk} {m : Mem} {addr v : Val} {m' : Mem}
    (h : storev chunk m addr v = some m') : m'.nextblock = m.nextblock := by
  cases addr with
  | Vptr b ofs => exact store_nextblock (storev_store h)
  | _ => cases h

/-! ## `free` / `free_list` / `drop_perm` -/

/-- `Mem.nextblock_free` -/
theorem nextblock_free {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (h : free m b lo hi = some m') : m'.nextblock = m.nextblock := by
  rw [free_result h]; rfl

/-- `Mem.valid_block_free_1` -/
theorem valid_block_free_1 {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (h : free m b lo hi = some m') {b' : Block} (hb : validBlock m b' = true) :
    validBlock m' b' = true := by
  simp only [validBlock] at *; rw [nextblock_free h]; exact hb

/-- `Mem.valid_block_free_2` -/
theorem valid_block_free_2 {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (h : free m b lo hi = some m') {b' : Block} (hb : validBlock m' b' = true) :
    validBlock m b' = true := by
  simp only [validBlock] at *; rw [nextblock_free h] at hb; exact hb

/-- `Mem.free_range_perm` -/
theorem free_range_perm {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (h : free m b lo hi = some m') : rangePerm m b lo hi .Cur .Freeable = true := by
  unfold free at h; split at h
  · assumption
  · cases h

/-- `Mem.range_perm_free` -/
theorem range_perm_free {m : Mem} {b : Block} {lo hi : Z}
    (h : rangePerm m b lo hi .Cur .Freeable = true) : ∃ m', free m b lo hi = some m' :=
  ⟨_, free_isSome h⟩

/-- `Mem.nextblock_freelist` -/
theorem nextblock_freeList {m : Mem} {l : List (Block × Z × Z)} {m' : Mem}
    (h : freeList m l = some m') : m'.nextblock = m.nextblock := by
  induction l generalizing m with
  | nil => simp only [freeList, Option.some.injEq] at h; rw [h]
  | cons e l ih =>
    obtain ⟨b, lo, hi⟩ := e
    simp only [freeList] at h
    split at h
    · cases h
    · rename_i m1 hm1
      rw [ih h, nextblock_free hm1]

/-- `Mem.valid_block_freelist` -/
theorem valid_block_freeList {m : Mem} {l : List (Block × Z × Z)} {m' : Mem}
    (h : freeList m l = some m') (b : Block) : validBlock m' b = validBlock m b := by
  simp only [validBlock, nextblock_freeList h]

/-- `Mem.nextblock_drop` -/
theorem nextblock_drop {m : Mem} {b : Block} {lo hi : Z} {p : Permission} {m' : Mem}
    (h : dropPerm m b lo hi p = some m') : m'.nextblock = m.nextblock := by
  unfold dropPerm at h; split at h
  · cases h; rfl
  · cases h

/-- `Mem.range_perm_drop_1` -/
theorem range_perm_drop_1 {m : Mem} {b : Block} {lo hi : Z} {p : Permission} {m' : Mem}
    (h : dropPerm m b lo hi p = some m') : rangePerm m b lo hi .Cur .Freeable = true := by
  unfold dropPerm at h; split at h
  · assumption
  · cases h

/-- `Mem.perm_drop_1`: inside the range, the new permission is `p`. -/
theorem perm_drop_1 {m : Mem} {b : Block} {lo hi : Z} {p : Permission} {m' : Mem}
    (h : dropPerm m b lo hi p = some m') {ofs : Z} (k : PermKind) (h1 : lo ≤ ofs) (h2 : ofs < hi) :
    perm m' b ofs k p = true := by
  unfold dropPerm at h; split at h
  · cases h
    simp only [perm, PMap.gss]
    rw [if_pos ⟨h1, h2⟩]
    simp [permOrder', permOrder]
  · cases h

/-- `Mem.perm_drop_3`: outside the range, permissions are unchanged. -/
theorem perm_drop_3 {m : Mem} {b : Block} {lo hi : Z} {p : Permission} {m' : Mem}
    (h : dropPerm m b lo hi p = some m') (b' : Block) (ofs : Z) (k : PermKind) (p' : Permission)
    (hout : b' ≠ b ∨ ofs < lo ∨ hi ≤ ofs) : perm m' b' ofs k p' = perm m b' ofs k p' := by
  unfold dropPerm at h; split at h
  · cases h
    simp only [perm]
    rw [PMap.gsspec]
    split
    · rename_i hb
      subst hb
      have : ¬ (lo ≤ ofs ∧ ofs < hi) := by
        rcases hout with hb | hb
        · exact absurd rfl hb
        · intro ⟨h1, h2⟩; rcases hb with hb | hb
          · exact absurd h1 (by simp only [CC.Z] at *; omega)
          · exact absurd h2 (by simp only [CC.Z] at *; omega)
      simp only [this, if_false]
    · rfl
  · cases h

/-- `Mem.valid_block_drop_1` / `valid_block_drop_2` -/
theorem valid_block_drop {m : Mem} {b : Block} {lo hi : Z} {p : Permission} {m' : Mem}
    (h : dropPerm m b lo hi p = some m') (b' : Block) : validBlock m' b' = validBlock m b' := by
  simp only [validBlock, nextblock_drop h]

end Mem
end CC
