/-
  `Mem.unchanged_on` — port of the `UNCHANGED_ON` section of `common/Memory.v`.

  `UnchangedOn P m m'` says that, on the locations satisfying `P`, the
  permissions of blocks valid in `m` and the contents of readable locations are
  the same in `m'`, and that `m'` has at least the blocks of `m`.  It is the
  frame property external calls and compiler passes rely on.
-/
import CCLib.common.MemoryTheory

namespace CC
namespace Mem

/-- `Mem.unchanged_on` -/
structure UnchangedOn (P : Block → Z → Prop) (m1 m2 : Mem) : Prop where
  nextblock_le : m1.nextblock ≤ m2.nextblock
  perm_iff : ∀ b ofs k p, P b ofs → validBlock m1 b = true →
    (Mem.perm m1 b ofs k p = true ↔ Mem.perm m2 b ofs k p = true)
  contents_eq : ∀ b ofs, P b ofs → Mem.perm m1 b ofs .Cur .Readable = true →
    ZMap.get ofs (PMap.get b m2.contents) = ZMap.get ofs (PMap.get b m1.contents)

/-! ## Auxiliary facts -/

theorem validBlock_of_perm {m : Mem} {b : Block} {ofs : Z} {k : PermKind} {p : Permission}
    (h : perm m b ofs k p = true) : validBlock m b = true := by
  simp only [validBlock, decide_eq_true_eq]
  exact perm_valid_block m b ofs k p h

/-- `getN` only depends on the cells it reads. -/
theorem getN_congr (c1 c2 : ZMap MemVal) :
    ∀ (n : Nat) (ofs : _root_.Int),
      (∀ i : _root_.Int, ofs ≤ i → i < ofs + n → ZMap.get i c1 = ZMap.get i c2) →
      getN n ofs c1 = getN n ofs c2 := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro ofs h
    simp only [getN]
    rw [h ofs (Int.le_refl _) (by omega), ih (ofs + 1) (fun i h1 h2 => h i (by omega) (by omega))]

private theorem toNat_bound (ofs n i : _root_.Int) (h1 : ofs ≤ i) (h2 : i < ofs + (n.toNat : Nat)) :
    i < ofs + n := by omega

private theorem in_of_not_out (ofs lo hi : _root_.Int) (h : ¬(ofs < lo ∨ hi ≤ ofs)) :
    lo ≤ ofs ∧ ofs < hi := by omega

private theorem sizeChunkNat_cast (chunk : Chunk) : ((sizeChunkNat chunk : Nat) : _root_.Int) = sizeChunk chunk := by
  cases chunk <;> rfl

section
variable {P : Block → Z → Prop}

/-! ## Basic properties -/

/-- `Mem.unchanged_on_refl` -/
theorem unchangedOn_refl (m : Mem) : UnchangedOn P m m :=
  ⟨Nat.le_refl _, fun _ _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => rfl⟩

/-- `Mem.valid_block_unchanged_on` -/
theorem UnchangedOn.valid_block {m m' : Mem} (h : UnchangedOn P m m') {b : Block}
    (hb : validBlock m b = true) : validBlock m' b = true := by
  simp only [Mem.validBlock, decide_eq_true_eq] at *
  exact Nat.lt_of_lt_of_le hb h.nextblock_le

/-- `Mem.perm_unchanged_on` -/
theorem UnchangedOn.perm_1 {m m' : Mem} (h : UnchangedOn P m m') {b ofs k p}
    (hP : P b ofs) (hp : perm m b ofs k p = true) : perm m' b ofs k p = true :=
  (h.perm_iff b ofs k p hP (validBlock_of_perm hp)).mp hp

/-- `Mem.perm_unchanged_on_2` -/
theorem UnchangedOn.perm_2 {m m' : Mem} (h : UnchangedOn P m m') {b ofs k p}
    (hP : P b ofs) (hv : validBlock m b = true) (hp : perm m' b ofs k p = true) :
    perm m b ofs k p = true :=
  (h.perm_iff b ofs k p hP hv).mpr hp

/-- `Mem.unchanged_on_trans` -/
theorem UnchangedOn.trans {m1 m2 m3 : Mem} (h12 : UnchangedOn P m1 m2)
    (h23 : UnchangedOn P m2 m3) : UnchangedOn P m1 m3 where
  nextblock_le := Nat.le_trans h12.nextblock_le h23.nextblock_le
  perm_iff := fun b ofs k p hP hv =>
    (h12.perm_iff b ofs k p hP hv).trans (h23.perm_iff b ofs k p hP (h12.valid_block hv))
  contents_eq := fun b ofs hP hp => by
    rw [h23.contents_eq b ofs hP (h12.perm_1 hP hp), h12.contents_eq b ofs hP hp]

/-- `Mem.unchanged_on_implies` -/
theorem UnchangedOn.implies {Q : Block → Z → Prop} {m m' : Mem} (h : UnchangedOn P m m')
    (hQ : ∀ b ofs, Q b ofs → validBlock m b = true → P b ofs) : UnchangedOn Q m m' where
  nextblock_le := h.nextblock_le
  perm_iff := fun b ofs k p hq hv => h.perm_iff b ofs k p (hQ b ofs hq hv) hv
  contents_eq := fun b ofs hq hp =>
    h.contents_eq b ofs (hQ b ofs hq (validBlock_of_perm hp)) hp

/-! ## Loads -/

theorem UnchangedOn.rangePerm {m m' : Mem} (h : UnchangedOn P m m') {b : Block}
    {lo hi : _root_.Int} {k : PermKind} {p : Permission}
    (hP : ∀ i : _root_.Int, lo ≤ i → i < hi → P b i)
    (hr : Mem.rangePerm m b lo hi k p = true) : Mem.rangePerm m' b lo hi k p = true :=
  rangePerm_intro m' b lo hi k p fun i h1 h2 =>
    h.perm_1 (hP i h1 h2) (rangePerm_perm m b lo hi k p hr i h1 h2)

theorem UnchangedOn.rangePerm_2 {m m' : Mem} (h : UnchangedOn P m m') {b : Block}
    (hv : Mem.validBlock m b = true) {lo hi : _root_.Int} {k : PermKind} {p : Permission}
    (hP : ∀ i : _root_.Int, lo ≤ i → i < hi → P b i)
    (hr : Mem.rangePerm m' b lo hi k p = true) : Mem.rangePerm m b lo hi k p = true :=
  rangePerm_intro m b lo hi k p fun i h1 h2 =>
    h.perm_2 (hP i h1 h2) hv (rangePerm_perm m' b lo hi k p hr i h1 h2)

theorem UnchangedOn.getN {m m' : Mem} (h : UnchangedOn P m m') {b : Block} {n : Nat}
    {ofs : _root_.Int} (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + n → P b i)
    (hr : ∀ i : _root_.Int, ofs ≤ i → i < ofs + n → perm m b i .Cur .Readable = true) :
    Mem.getN n ofs (PMap.get b m'.contents) = Mem.getN n ofs (PMap.get b m.contents) :=
  getN_congr _ _ n ofs fun i h1 h2 => h.contents_eq b i (hP i h1 h2) (hr i h1 h2)

/-- `Mem.loadbytes_unchanged_on_1` -/
theorem UnchangedOn.loadbytes_1 {m m' : Mem} (h : UnchangedOn P m m') {b : Block}
    {ofs n : _root_.Int} (hv : Mem.validBlock m b = true)
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + n → P b i) :
    loadbytes m' b ofs n = loadbytes m b ofs n := by
  unfold loadbytes
  by_cases hr : Mem.rangePerm m b ofs (ofs + n) .Cur .Readable = true
  · rw [if_pos (h.rangePerm hP hr), if_pos hr,
      h.getN (fun i h1 h2 => hP i h1 (toNat_bound ofs n i h1 h2))
        (fun i h1 h2 => rangePerm_perm m b _ _ _ _ hr i h1 (toNat_bound ofs n i h1 h2))]
  · have hr' : ¬ Mem.rangePerm m' b ofs (ofs + n) .Cur .Readable = true :=
      fun h' => hr (h.rangePerm_2 hv hP h')
    rw [if_neg hr, if_neg hr']

/-- `Mem.loadbytes_unchanged_on` -/
theorem UnchangedOn.loadbytes {m m' : Mem} (h : UnchangedOn P m m') {b : Block}
    {ofs n : _root_.Int} {bytes : List MemVal}
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + n → P b i)
    (hl : Mem.loadbytes m b ofs n = some bytes) : Mem.loadbytes m' b ofs n = some bytes := by
  unfold Mem.loadbytes at *
  by_cases hr : Mem.rangePerm m b ofs (ofs + n) .Cur .Readable = true
  · rw [if_pos hr] at hl
    rw [if_pos (h.rangePerm hP hr), ← hl,
      h.getN (fun i h1 h2 => hP i h1 (toNat_bound ofs n i h1 h2))
        (fun i h1 h2 => rangePerm_perm m b _ _ _ _ hr i h1 (toNat_bound ofs n i h1 h2))]
  · rw [if_neg hr] at hl; cases hl

/-- `Mem.load_unchanged_on_1` -/
theorem UnchangedOn.load_1 {m m' : Mem} (h : UnchangedOn P m m') {chunk : Chunk}
    {b : Block} {ofs : _root_.Int} (hv : Mem.validBlock m b = true)
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + sizeChunk chunk → P b i) :
    load chunk m' b ofs = load chunk m b ofs := by
  unfold load validAccess
  by_cases hr : Mem.rangePerm m b ofs (ofs + sizeChunk chunk) .Cur .Readable = true
  · have hr' := h.rangePerm hP hr
    simp only [hr, hr', Bool.true_and]
    split
    · rw [h.getN (fun i h1 h2 => hP i h1 (by rw [sizeChunkNat_cast] at h2; exact h2))
        (fun i h1 h2 => rangePerm_perm m b _ _ _ _ hr i h1
          (by rw [sizeChunkNat_cast] at h2; exact h2))]
    · rfl
  · have hr' : ¬ Mem.rangePerm m' b ofs (ofs + sizeChunk chunk) .Cur .Readable = true :=
      fun h' => hr (h.rangePerm_2 hv hP h')
    simp only [Bool.not_eq_true] at hr hr'
    simp [hr, hr']

/-- `Mem.load_unchanged_on` -/
theorem UnchangedOn.load {m m' : Mem} (h : UnchangedOn P m m') {chunk : Chunk}
    {b : Block} {ofs : _root_.Int} {v : Val}
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + sizeChunk chunk → P b i)
    (hl : Mem.load chunk m b ofs = some v) : Mem.load chunk m' b ofs = some v := by
  have hva : validAccess m chunk b ofs .Readable = true := by
    unfold Mem.load at hl; split at hl
    · assumption
    · cases hl
  have hr : Mem.rangePerm m b ofs (ofs + sizeChunk chunk) .Cur .Readable = true := by
    simp only [validAccess, Bool.and_eq_true] at hva; exact hva.1
  have hpos : (0 : _root_.Int) < sizeChunk chunk := by cases chunk <;> decide
  have hv : Mem.validBlock m b = true :=
    validBlock_of_perm (rangePerm_perm m b _ _ _ _ hr ofs (Int.le_refl _) (by omega))
  rw [h.load_1 hv hP]; exact hl

/-! ## Operations that leave other locations unchanged -/

/-- `Mem.store_unchanged_on` -/
theorem store_unchangedOn {chunk : Chunk} {m : Mem} {b : Block} {ofs : _root_.Int} {v : Val}
    {m' : Mem} (hs : store chunk m b ofs v = some m')
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + sizeChunk chunk → ¬ P b i) :
    UnchangedOn P m m' where
  nextblock_le := by rw [store_nextblock hs]; exact Nat.le_refl _
  perm_iff := fun b' ofs' k p _ _ => by rw [perm_store hs]
  contents_eq := fun b' ofs' hp _ => by
    rw [store_contents hs, PMap.gsspec]
    split
    · rename_i he
      subst he
      apply setN_outside
      rw [length_encodeVal, sizeChunkNat_cast]
      apply Classical.byContradiction
      intro hc
      exact hP ofs' (by omega) (by omega) hp
    · rfl

/-- `Mem.storebytes_unchanged_on` -/
theorem storebytes_unchangedOn {m : Mem} {b : Block} {ofs : _root_.Int} {bytes : List MemVal}
    {m' : Mem} (hs : storebytes m b ofs bytes = some m')
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + (bytes.length : _root_.Int) → ¬ P b i) :
    UnchangedOn P m m' where
  nextblock_le := by rw [storebytes_nextblock hs]; exact Nat.le_refl _
  perm_iff := fun b' ofs' k p _ _ => by rw [perm_storebytes hs]
  contents_eq := fun b' ofs' hp _ => by
    rw [storebytes_contents hs, PMap.gsspec]
    split
    · rename_i he
      subst he
      apply setN_outside
      apply Classical.byContradiction
      intro hc
      exact hP ofs' (by omega) (by omega) hp
    · rfl

/-- `Mem.alloc_unchanged_on` -/
theorem alloc_unchangedOn {m : Mem} {lo hi : Z} {m' : Mem} {b : Block}
    (ha : alloc m lo hi = (m', b)) : UnchangedOn P m m' := by
  have e1 : (alloc m lo hi).1 = m' := by rw [ha]
  subst e1
  refine ⟨?_, ?_, ?_⟩
  · show m.nextblock.toNat ≤ m.nextblock.succ.toNat
    rw [Positive.toNat_succ]; exact Nat.le_succ _
  · intro b' ofs k p _ hv
    have hne : b' ≠ m.nextblock := by
      intro he; subst he; simp [Mem.validBlock, Positive.lt_iff] at hv
    rw [perm_alloc_other m lo hi b' hne]
  · intro b' ofs _ hp
    have hne : b' ≠ m.nextblock := by
      intro he; subst he
      have := validBlock_of_perm hp
      simp [Mem.validBlock, Positive.lt_iff] at this
    show ZMap.get ofs (PMap.get b' (PMap.set m.nextblock _ m.contents)) = _
    rw [PMap.gso _ _ _ _ (Ne.symm hne)]

/-- `Mem.free_unchanged_on` -/
theorem free_unchangedOn {m : Mem} {b : Block} {lo hi : _root_.Int} {m' : Mem}
    (hf : free m b lo hi = some m') (hP : ∀ i : _root_.Int, lo ≤ i → i < hi → ¬ P b i) :
    UnchangedOn P m m' := by
  rw [free_result hf]
  refine ⟨Nat.le_refl _, ?_, fun _ _ _ _ => rfl⟩
  intro b' ofs k p hp _
  by_cases hb : b' = b
  · subst hb
    have hout : ofs < lo ∨ hi ≤ ofs := by
      apply Classical.byContradiction
      intro hc
      exact hP ofs (in_of_not_out _ _ _ hc).1 (in_of_not_out _ _ _ hc).2 hp
    rw [perm_free_outside m b' lo hi ofs k p hout]
  · rw [perm_free_other m b lo hi b' hb]

/-- `Mem.drop_perm_unchanged_on` -/
theorem dropPerm_unchangedOn {m : Mem} {b : Block} {lo hi : _root_.Int} {p : Permission}
    {m' : Mem} (hd : dropPerm m b lo hi p = some m')
    (hP : ∀ i : _root_.Int, lo ≤ i → i < hi → ¬ P b i) : UnchangedOn P m m' := by
  have hc : m'.contents = m.contents := by
    unfold dropPerm at hd; split at hd
    · cases hd; rfl
    · cases hd
  refine ⟨by rw [nextblock_drop hd]; exact Nat.le_refl _, ?_, ?_⟩
  · intro b' ofs k p' hp _
    have hout : b' ≠ b ∨ ofs < lo ∨ hi ≤ ofs := by
      by_cases hb : b' = b
      · subst hb
        right
        apply Classical.byContradiction
        intro hc
        exact hP ofs (in_of_not_out _ _ _ hc).1 (in_of_not_out _ _ _ hc).2 hp
      · exact Or.inl hb
    rw [perm_drop_3 hd b' ofs k p' hout]
  · intro b' ofs _ _; rw [hc]

end

end Mem
end CC
