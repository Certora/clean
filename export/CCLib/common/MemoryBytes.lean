/-
  Byte-level `loadbytes` lemmas — the part of `common/Memory.v` needed by the
  correctness proof of initializers (`cfrontend/Initializersproof.v`):

  * `loadbytes_length`, `loadbytes_empty`, `loadbytes_concat`,
    `loadbytes_split`: `loadbytes` over adjacent ranges;
  * `loadbytes_load`: a `load` can be computed from the bytes it reads;
  * `loadbytes_store_same`: a `store` writes exactly `encode_val`;
  * `store_signed_unsigned_8`, `store_signed_unsigned_16`,
    `store_bool_unsigned_8`: chunks of equal size and encoding store the same
    bytes.

  Binders are `_root_.Int` rather than `Z` where `omega` has to see them (see
  the header of `CCLib/common/MemdataLemmas.lean`).
-/
import CCLib.common.MemoryUnchanged

namespace CC
namespace Mem

/-- `getN` over two adjacent ranges. -/
theorem getN_append (n1 n2 : Nat) (p : _root_.Int) (c : ZMap MemVal) :
    getN (n1 + n2) p c = getN n1 p c ++ getN n2 (p + (n1 : _root_.Int)) c := by
  induction n1 generalizing p with
  | zero => simp [getN]
  | succ n ih =>
    rw [Nat.add_right_comm]
    show ZMap.get p c :: getN (n + n2) (p + 1) c = (ZMap.get p c :: getN n (p + 1) c) ++ _
    rw [ih, List.cons_append]
    congr 3
    rw [Int.natCast_add, Int.add_assoc, Int.add_comm 1]
    rfl

theorem length_getN (n : Nat) (p : _root_.Int) (c : ZMap MemVal) : (getN n p c).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [getN, ih]

/-- `Mem.loadbytes_length` -/
theorem loadbytes_length {m : Mem} {b : Block} {ofs n : _root_.Int} {bytes : List MemVal}
    (h : loadbytes m b ofs n = some bytes) : bytes.length = n.toNat := by
  unfold loadbytes at h
  split at h
  · cases h; exact length_getN _ _ _
  · cases h

/-- `Mem.loadbytes_empty` -/
theorem loadbytes_empty (m : Mem) (b : Block) (ofs : _root_.Int) {n : _root_.Int} (hn : n ≤ 0) :
    loadbytes m b ofs n = some [] := by
  unfold loadbytes
  rw [if_pos (rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => by omega)]
  rw [show n.toNat = 0 by omega]
  rfl

/-- `Mem.loadbytes_concat` -/
theorem loadbytes_concat {m : Mem} {b : Block} {ofs n1 n2 : _root_.Int} {bytes1 bytes2 : List MemVal}
    (h1 : loadbytes m b ofs n1 = some bytes1) (h2 : loadbytes m b (ofs + n1) n2 = some bytes2)
    (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2) :
    loadbytes m b ofs (n1 + n2) = some (bytes1 ++ bytes2) := by
  have r1 := loadbytes_range_perm h1
  have r2 := loadbytes_range_perm h2
  unfold loadbytes at h1 h2 ⊢
  rw [if_pos r1] at h1
  rw [if_pos r2] at h2
  cases h1; cases h2
  rw [if_pos (by rw [← Int.add_assoc]; exact rangePerm_append r1 r2)]
  rw [show (n1 + n2).toNat = n1.toNat + n2.toNat by omega, getN_append,
    show ofs + (n1.toNat : _root_.Int) = ofs + n1 by omega]

/-- `Mem.loadbytes_split` -/
theorem loadbytes_split {m : Mem} {b : Block} {ofs n1 n2 : _root_.Int} {bytes : List MemVal}
    (h : loadbytes m b ofs (n1 + n2) = some bytes) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2) :
    ∃ bytes1 bytes2, loadbytes m b ofs n1 = some bytes1 ∧
      loadbytes m b (ofs + n1) n2 = some bytes2 ∧ bytes = bytes1 ++ bytes2 := by
  have r := loadbytes_range_perm h
  unfold loadbytes at h ⊢
  rw [if_pos r] at h
  cases h
  refine ⟨_, _, if_pos (rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
      rangePerm_perm _ _ _ _ _ _ r o h1 (by omega)),
    if_pos (rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
      rangePerm_perm _ _ _ _ _ _ r o (by omega) (by omega)), ?_⟩
  rw [show (n1 + n2).toNat = n1.toNat + n2.toNat by omega, getN_append,
    show ofs + (n1.toNat : _root_.Int) = ofs + n1 by omega]

/-- `Mem.loadbytes_load` -/
theorem loadbytes_load {chunk : Chunk} {m : Mem} {b : Block} {ofs : _root_.Int} {bytes : List MemVal}
    (h : loadbytes m b ofs (sizeChunk chunk) = some bytes) (hal : alignChunk chunk ∣ ofs) :
    load chunk m b ofs = some (decodeVal chunk bytes) := by
  have r := loadbytes_range_perm h
  unfold loadbytes at h
  rw [if_pos r] at h
  cases h
  unfold load
  rw [if_pos (by
    simp only [validAccess, Bool.and_eq_true, beq_iff_eq]
    exact ⟨r, Int.emod_eq_zero_of_dvd hal⟩)]
  rfl

/-- `Mem.loadbytes_store_same` -/
theorem loadbytes_store_same {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (h : store chunk m b ofs v = some m') :
    loadbytes m' b ofs (sizeChunk chunk) = some (encodeVal chunk v) := by
  have hva := store_valid_access h
  simp only [validAccess, Bool.and_eq_true] at hva
  have hr : rangePerm m' b ofs (ofs + sizeChunk chunk) .Cur .Readable = true := by
    rw [rangePerm_store_eq h]; exact rangePerm_implies hva.1 (by decide)
  rw [loadbytes_result hr, store_contents h, PMap.gss]
  rw [show (sizeChunk chunk).toNat = (encodeVal chunk v).length by
        rw [length_encodeVal]; rfl,
      getN_setN_same]

/-- Two chunks that have the same size and write the same bytes give the same
    `store`. -/
theorem store_same_encoding {chunk1 chunk2 : Chunk} (m : Mem) (b : Block) (ofs : Z) (v : Val)
    (hs : sizeChunk chunk1 = sizeChunk chunk2) (ha : alignChunk chunk1 = alignChunk chunk2)
    (he : encodeVal chunk1 v = encodeVal chunk2 v) :
    store chunk1 m b ofs v = store chunk2 m b ofs v := by
  unfold store validAccess
  rw [hs, ha]
  simp only [he]

/-- `Mem.store_signed_unsigned_8` -/
theorem store_signed_unsigned_8 (m : Mem) (b : Block) (ofs : Z) (v : Val) :
    store .Mint8signed m b ofs v = store .Mint8unsigned m b ofs v :=
  store_same_encoding m b ofs v rfl rfl (by cases v <;> rfl)

/-- `Mem.store_signed_unsigned_16` -/
theorem store_signed_unsigned_16 (m : Mem) (b : Block) (ofs : Z) (v : Val) :
    store .Mint16signed m b ofs v = store .Mint16unsigned m b ofs v :=
  store_same_encoding m b ofs v rfl rfl (by cases v <;> rfl)

/-- `Mem.store_bool_unsigned_8` -/
theorem store_bool_unsigned_8 (m : Mem) (b : Block) (ofs : Z) (v : Val) :
    store .Mbool m b ofs v = store .Mint8unsigned m b ofs v :=
  store_same_encoding m b ofs v rfl rfl (by cases v <;> rfl)

end Mem
end CC
