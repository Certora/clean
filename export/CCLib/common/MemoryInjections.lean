/-
  Memory injections — port of the `INJECT` section of `common/Memory.v`
  (`Mem.inject` and its main theorems) and of `Mem.inject_neutral`.

  `Inject f m1 m2` is the memory relation used by every CompCert pass that
  changes the block structure (`SimplLocals`, `Cminorgen`, `Inlining`,
  `Stacking`, …): blocks of `m1` are mapped by `f` into blocks of `m2` at an
  offset, without overlap, with the contents of `m1` related to those of `m2`
  by `memval_inject f`.
-/
import CCLib.common.MemoryExtends
import CCLib.lib.IntegersPtrofs

namespace CC
namespace Mem

open Integers (Ptrofs)

/-- `Memory.inject` -/
structure Inject (f : Val.Meminj) (m1 m2 : Mem) : Prop where
  inj : MemInj f m1 m2
  freeblocks : ∀ b, validBlock m1 b = false → f b = none
  mappedblocks : ∀ b b' delta, f b = some (b', delta) → validBlock m2 b' = true
  no_overlap : MeminjNoOverlap f m1
  representable : ∀ b b' (delta : _root_.Int) (ofs : Ptrofs), f b = some (b', delta) →
    (perm m1 b (Ptrofs.unsigned ofs) .Max .Nonempty = true ∨
      perm m1 b (Ptrofs.unsigned ofs - 1) .Max .Nonempty = true) →
    delta ≥ 0 ∧ 0 ≤ Ptrofs.unsigned ofs + delta ∧ Ptrofs.unsigned ofs + delta ≤ Ptrofs.max_unsigned
  perm_inv : ∀ b1 (ofs : _root_.Int) b2 delta k p, f b1 = some (b2, delta) →
    perm m2 b2 (ofs + delta) k p = true →
    perm m1 b1 ofs k p = true ∨ perm m1 b1 ofs .Max .Nonempty = false
  metadata : ∀ b b' (delta ofs : _root_.Int), f b = some (b', delta) →
    perm m1 b ofs .Max .Nonempty = true → ofs < 0 → delta = 0

section
variable {f : Val.Meminj} {m1 m2 : Mem}

/-! ## Validity, permissions, accesses -/

/-- `Memory.valid_block_inject_1` -/
theorem validBlock_inject_1 {b1 b2 : Block} {delta : Z} (hf : f b1 = some (b2, delta))
    (h : Inject f m1 m2) : validBlock m1 b1 = true := by
  cases hv : validBlock m1 b1
  · rw [h.freeblocks b1 hv] at hf; cases hf
  · rfl

/-- `Memory.valid_block_inject_2` -/
theorem validBlock_inject_2 {b1 b2 : Block} {delta : Z} (hf : f b1 = some (b2, delta))
    (h : Inject f m1 m2) : validBlock m2 b2 = true :=
  h.mappedblocks _ _ _ hf

/-- `Memory.perm_inject` -/
theorem perm_inject {b1 b2 : Block} {delta ofs : _root_.Int} {k : PermKind} {p : Permission}
    (hf : f b1 = some (b2, delta)) (h : Inject f m1 m2) (hp : perm m1 b1 ofs k p = true) :
    perm m2 b2 (ofs + delta) k p = true :=
  perm_inj h.inj hp hf

/-- `Memory.perm_inject_inv` -/
theorem perm_inject_inv (h : Inject f m1 m2) {b1 b2 : Block} {delta ofs : _root_.Int}
    {k : PermKind} {p : Permission} (hf : f b1 = some (b2, delta))
    (hp : perm m2 b2 (ofs + delta) k p = true) :
    perm m1 b1 ofs k p = true ∨ perm m1 b1 ofs .Max .Nonempty = false :=
  h.perm_inv _ _ _ _ _ _ hf hp

/-- `Memory.range_perm_inject` -/
theorem rangePerm_inject {b1 b2 : Block} {delta lo hi : _root_.Int} {k : PermKind}
    {p : Permission} (hf : f b1 = some (b2, delta)) (h : Inject f m1 m2)
    (hp : rangePerm m1 b1 lo hi k p = true) :
    rangePerm m2 b2 (lo + delta) (hi + delta) k p = true :=
  rangePerm_inj h.inj hp hf

/-- `Memory.valid_access_inject` -/
theorem validAccess_inject {chunk : Chunk} {b1 b2 : Block} {delta ofs : _root_.Int}
    {p : Permission} (hf : f b1 = some (b2, delta)) (h : Inject f m1 m2)
    (hv : validAccess m1 chunk b1 ofs p = true) :
    validAccess m2 chunk b2 (ofs + delta) p = true :=
  validAccess_inj h.inj hf hv

/-- `Memory.valid_pointer_inject` -/
theorem validPointer_inject {b1 b2 : Block} {delta ofs : _root_.Int}
    (hf : f b1 = some (b2, delta)) (h : Inject f m1 m2)
    (hv : validPointer m1 b1 ofs = true) : validPointer m2 b2 (ofs + delta) = true :=
  perm_inject hf h hv

/-- `Memory.weak_valid_pointer_inject` -/
theorem weakValidPointer_inject {b1 b2 : Block} {delta ofs : _root_.Int}
    (hf : f b1 = some (b2, delta)) (h : Inject f m1 m2)
    (hv : weakValidPointer m1 b1 ofs = true) : weakValidPointer m2 b2 (ofs + delta) = true := by
  simp only [weakValidPointer, Bool.or_eq_true] at hv ⊢
  rcases hv with hv | hv
  · exact Or.inl (validPointer_inject hf h hv)
  · right
    have := validPointer_inject hf h hv
    rwa [show ofs - 1 + delta = ofs + delta - 1 by omega] at this

/-! ## Absence of overflow in address computations -/

theorem max_unsigned_eq : Ptrofs.max_unsigned = Ptrofs.modulus - 1 := rfl

/-- `Memory.address_inject_gen` -/
theorem address_inject_gen (h : Inject f m1 m2) {b1 b2 : Block} {ofs1 : Ptrofs}
    {delta : _root_.Int} {p : Permission}
    (hp : perm m1 b1 (Ptrofs.unsigned ofs1) .Cur p = true ∨
      perm m1 b1 (Ptrofs.unsigned ofs1 - 1) .Cur p = true)
    (hf : f b1 = some (b2, delta)) :
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta := by
  have hne : perm m1 b1 (Ptrofs.unsigned ofs1) .Max .Nonempty = true ∨
      perm m1 b1 (Ptrofs.unsigned ofs1 - 1) .Max .Nonempty = true := by
    rcases hp with hp | hp
    · exact Or.inl (perm_cur_max (perm_implies hp (by cases p <;> rfl)))
    · exact Or.inr (perm_cur_max (perm_implies hp (by cases p <;> rfl)))
  obtain ⟨hA, hB, hC⟩ := h.representable _ _ _ ofs1 hf hne
  have hr : (0 : _root_.Int) ≤ (Ptrofs.unsigned ofs1 : _root_.Int) := (Ptrofs.unsigned_range_2 ofs1).1
  have hA' : (0 : _root_.Int) ≤ delta := hA
  rw [Ptrofs.add_unsigned, Ptrofs.unsigned_repr (z := delta) hA'
    (Int.le_trans (Int.le_add_of_nonneg_left hr) hC)]
  exact Ptrofs.unsigned_repr hB hC

/-- `Memory.address_inject` -/
theorem address_inject (h : Inject f m1 m2) {b1 b2 : Block} {ofs1 : Ptrofs}
    {delta : _root_.Int} {p : Permission}
    (hp : perm m1 b1 (Ptrofs.unsigned ofs1) .Cur p = true) (hf : f b1 = some (b2, delta)) :
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta :=
  address_inject_gen h (Or.inl hp) hf

/-- `Memory.address_inject_1` -/
theorem address_inject_1 (h : Inject f m1 m2) {b1 b2 : Block} {ofs1 : Ptrofs}
    {delta : _root_.Int} {p : Permission}
    (hp : perm m1 b1 (Ptrofs.unsigned ofs1 - 1) .Cur p = true) (hf : f b1 = some (b2, delta)) :
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta :=
  address_inject_gen h (Or.inr hp) hf

/-- `Memory.address_inject'` -/
theorem address_inject' (h : Inject f m1 m2) {chunk : Chunk} {b1 b2 : Block} {ofs1 : Ptrofs}
    {delta : _root_.Int} {p : Permission}
    (hv : validAccess m1 chunk b1 (Ptrofs.unsigned ofs1) p = true)
    (hf : f b1 = some (b2, delta)) :
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta := by
  simp only [validAccess, Bool.and_eq_true] at hv
  exact address_inject h (rangePerm_perm _ _ _ _ _ _ hv.1 _ (Int.le_refl _)
    (by have := sizeChunk_pos chunk; omega)) hf

/-- `Memory.valid_pointer_inject_no_overflow` -/
theorem validPointer_inject_no_overflow (h : Inject f m1 m2) {b : Block} {ofs : Ptrofs}
    {b' : Block} {delta : _root_.Int}
    (hv : validPointer m1 b (Ptrofs.unsigned ofs) = true) (hf : f b = some (b', delta)) :
    0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned := by
  obtain ⟨hA, hB, hC⟩ := h.representable _ _ _ ofs hf (Or.inl (perm_cur_max hv))
  have hr : (0 : _root_.Int) ≤ (Ptrofs.unsigned ofs : _root_.Int) := (Ptrofs.unsigned_range_2 ofs).1
  have hA' : (0 : _root_.Int) ≤ delta := hA
  rw [Ptrofs.unsigned_repr (z := delta) hA'
    (Int.le_trans (Int.le_add_of_nonneg_left hr) hC)]
  exact ⟨hB, hC⟩

/-- `Memory.valid_pointer_inject_val` -/
theorem validPointer_inject_val (h : Inject f m1 m2) {b : Block} {ofs : Ptrofs} {b' : Block}
    {ofs' : Ptrofs} (hv : validPointer m1 b (Ptrofs.unsigned ofs) = true)
    (hi : Val.Inject f (.Vptr b ofs) (.Vptr b' ofs')) :
    validPointer m2 b' (Ptrofs.unsigned ofs') = true := by
  cases hi with
  | ptr delta hf ho =>
    subst ho
    rw [address_inject h hv hf]
    exact validPointer_inject hf h hv

/-- `Memory.weak_valid_pointer_inject_val` -/
theorem weakValidPointer_inject_val (h : Inject f m1 m2) {b : Block} {ofs : Ptrofs}
    {b' : Block} {ofs' : Ptrofs} (hv : weakValidPointer m1 b (Ptrofs.unsigned ofs) = true)
    (hi : Val.Inject f (.Vptr b ofs) (.Vptr b' ofs')) :
    weakValidPointer m2 b' (Ptrofs.unsigned ofs') = true := by
  cases hi with
  | ptr delta hf ho =>
    subst ho
    have hv' := hv
    simp only [weakValidPointer, Bool.or_eq_true] at hv'
    rw [address_inject_gen h hv' hf]
    exact weakValidPointer_inject hf h hv

private theorem below_arith_1 (u s : _root_.Int) (hs : 0 < s) (hr : 0 ≤ u) : 0 ≤ u + s - 1 := by omega

private theorem below_arith_2 (u s M : _root_.Int) (hb : u + s ≤ M) : u + s - 1 ≤ M - 1 := by omega

private theorem below_arith_3 (u s d M : _root_.Int) (hrep : u + s - 1 + d ≤ M - 1) :
    u + d + s ≤ M := by omega

/-- `Memory.address_inject_below` -/
theorem address_inject_below (h : Inject f m1 m2) {chunk : Chunk} {b1 b2 : Block}
    {ofs1 : Ptrofs} {delta : _root_.Int} {p : Permission}
    (hv : validAccess m1 chunk b1 (Ptrofs.unsigned ofs1) p = true)
    (hb : Ptrofs.unsigned ofs1 + sizeChunk chunk ≤ Ptrofs.modulus)
    (hf : f b1 = some (b2, delta)) :
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) + sizeChunk chunk ≤ Ptrofs.modulus := by
  rw [address_inject' h hv hf]
  have hs := sizeChunk_pos chunk
  have hr := (Ptrofs.unsigned_range_2 ofs1).1
  have hB : Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs1 + sizeChunk chunk - 1)) =
      Ptrofs.unsigned ofs1 + sizeChunk chunk - 1 :=
    Ptrofs.unsigned_repr (below_arith_1 _ _ hs hr) (below_arith_2 _ _ _ hb)
  have hp : perm m1 b1 (Ptrofs.unsigned ofs1 + sizeChunk chunk - 1) .Cur p = true := by
    simp only [validAccess, Bool.and_eq_true] at hv
    exact rangePerm_perm _ _ _ _ _ _ hv.1 _ (by omega) (by omega)
  rw [← hB] at hp
  have := (h.representable _ _ _ _ hf
    (Or.inl (perm_cur_max (perm_implies hp (by cases p <;> rfl))))).2.2
  rw [hB] at this
  exact below_arith_3 _ _ _ _ this

/-- `Memory.inject_no_overlap` -/
theorem inject_no_overlap (h : Inject f m1 m2) {b1 b2 b1' b2' : Block}
    {delta1 delta2 ofs1 ofs2 : _root_.Int} (hne : b1 ≠ b2)
    (hf1 : f b1 = some (b1', delta1)) (hf2 : f b2 = some (b2', delta2))
    (hp1 : perm m1 b1 ofs1 .Max .Nonempty = true) (hp2 : perm m1 b2 ofs2 .Max .Nonempty = true) :
    b1' ≠ b2' ∨ ofs1 + delta1 ≠ ofs2 + delta2 :=
  h.no_overlap _ _ _ _ _ _ _ _ hne hf1 hf2 hp1 hp2

/-- `Memory.different_pointers_inject` -/
theorem different_pointers_inject (h : Inject f m1 m2) {b1 b2 b1' b2' : Block}
    {ofs1 ofs2 : Ptrofs} {delta1 delta2 : _root_.Int} (hne : b1 ≠ b2)
    (hv1 : validPointer m1 b1 (Ptrofs.unsigned ofs1) = true)
    (hv2 : validPointer m1 b2 (Ptrofs.unsigned ofs2) = true)
    (hf1 : f b1 = some (b1', delta1)) (hf2 : f b2 = some (b2', delta2)) :
    b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)) := by
  rw [address_inject h hv1 hf1, address_inject h hv2 hf2]
  exact inject_no_overlap h hne hf1 hf2 (perm_cur_max hv1) (perm_cur_max hv2)

/-! ## Loads -/

/-- `Memory.load_inject` -/
theorem load_inject (h : Inject f m1 m2) {chunk : Chunk} {b1 b2 : Block}
    {delta ofs : _root_.Int} {v1 : Val} (hl : load chunk m1 b1 ofs = some v1)
    (hf : f b1 = some (b2, delta)) :
    ∃ v2, load chunk m2 b2 (ofs + delta) = some v2 ∧ Val.Inject f v1 v2 :=
  load_inj h.inj hl hf

/-- `Memory.loadv_inject` -/
theorem loadv_inject (h : Inject f m1 m2) {chunk : Chunk} {a1 a2 v1 : Val}
    (hl : loadv chunk m1 a1 = some v1) (ha : Val.Inject f a1 a2) :
    ∃ v2, loadv chunk m2 a2 = some v2 ∧ Val.Inject f v1 v2 := by
  cases ha with
  | ptr delta hf ho =>
    subst ho
    simp only [loadv] at hl ⊢
    split at hl
    · next hc =>
      rw [if_pos (address_inject_below h (load_valid_access hl) hc hf),
        address_inject' h (load_valid_access hl) hf]
      exact load_inject h hl hf
    · cases hl
  | _ => simp [loadv] at hl

/-- `Memory.loadbytes_inject` -/
theorem loadbytes_inject (h : Inject f m1 m2) {b1 b2 : Block} {delta ofs len : _root_.Int}
    {bytes1 : List MemVal} (hl : loadbytes m1 b1 ofs len = some bytes1)
    (hf : f b1 = some (b2, delta)) :
    ∃ bytes2, loadbytes m2 b2 (ofs + delta) len = some bytes2 ∧
      MemvalInjectList f bytes1 bytes2 :=
  loadbytes_inj h.inj hl hf

/-! ## Stores -/

/-- An `Inject` is preserved when both memories keep their permissions and
`nextblock`, and the contents stay related. -/
theorem Inject.of_perm_eq (h : Inject f m1 m2) {n1 n2 : Mem} (hi : MemInj f n1 n2)
    (hn1 : n1.nextblock = m1.nextblock) (hn2 : n2.nextblock = m2.nextblock)
    (hp1 : ∀ b ofs k p, perm n1 b ofs k p = perm m1 b ofs k p)
    (hp2 : ∀ b ofs k p, perm n2 b ofs k p = perm m2 b ofs k p) : Inject f n1 n2 := by
  refine ⟨hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb; exact h.freeblocks b (by simpa [validBlock, hn1] using hb)
  · intro b b' d hf; simpa [validBlock, hn2] using h.mappedblocks b b' d hf
  · intro b1 b1' d1 b2 b2' d2 o1 o2 hne hf1 hf2 hq1 hq2
    rw [hp1] at hq1 hq2
    exact h.no_overlap _ _ _ _ _ _ _ _ hne hf1 hf2 hq1 hq2
  · intro b b' d o hf hq
    rw [hp1, hp1] at hq
    exact h.representable _ _ _ _ hf hq
  · intro b1 o b2 d k p hf hq
    rw [hp2] at hq
    rw [hp1, hp1]
    exact h.perm_inv _ _ _ _ _ _ hf hq
  · intro b b' d o hf hq
    rw [hp1] at hq
    exact h.metadata _ _ _ _ hf hq

/-- `Memory.store_mapped_inject` -/
theorem store_mapped_inject (h : Inject f m1 m2) {chunk : Chunk} {b1 b2 : Block}
    {ofs delta : _root_.Int} {v1 v2 : Val} {n1 : Mem}
    (hs : store chunk m1 b1 ofs v1 = some n1) (hf : f b1 = some (b2, delta))
    (hv : Val.Inject f v1 v2) :
    ∃ n2, store chunk m2 b2 (ofs + delta) v2 = some n2 ∧ Inject f n1 n2 := by
  obtain ⟨n2, hs2, hi⟩ := store_mapped_inj h.inj hs h.no_overlap hf hv
  exact ⟨n2, hs2, h.of_perm_eq hi (store_nextblock hs) (store_nextblock hs2)
    (fun b o k p => perm_store hs b o k p) (fun b o k p => perm_store hs2 b o k p)⟩

/-- `Memory.store_unmapped_inject` -/
theorem store_unmapped_inject (h : Inject f m1 m2) {chunk : Chunk} {b1 : Block}
    {ofs : _root_.Int} {v1 : Val} {n1 : Mem} (hs : store chunk m1 b1 ofs v1 = some n1)
    (hf : f b1 = none) : Inject f n1 m2 :=
  h.of_perm_eq (store_unmapped_inj h.inj hs hf) (store_nextblock hs) rfl
    (fun b o k p => perm_store hs b o k p) (fun _ _ _ _ => rfl)

/-- `Memory.store_outside_inject` -/
theorem store_outside_inject (h : Inject f m1 m2) {chunk : Chunk} {b : Block}
    {ofs : _root_.Int} {v : Val} {m2' : Mem}
    (hout : ∀ b' delta (ofs' : _root_.Int), f b' = some (b, delta) →
      perm m1 b' ofs' .Cur .Readable = true → ofs ≤ ofs' + delta →
      ofs' + delta < ofs + sizeChunk chunk → False)
    (hs : store chunk m2 b ofs v = some m2') : Inject f m1 m2' :=
  h.of_perm_eq (store_outside_inj h.inj hout hs) rfl (store_nextblock hs)
    (fun _ _ _ _ => rfl) (fun b o k p => perm_store hs b o k p)

/-- `Memory.storebytes_mapped_inject` -/
theorem storebytes_mapped_inject (h : Inject f m1 m2) {b1 b2 : Block} {ofs delta : _root_.Int}
    {bytes1 bytes2 : List MemVal} {n1 : Mem} (hs : storebytes m1 b1 ofs bytes1 = some n1)
    (hf : f b1 = some (b2, delta)) (hv : MemvalInjectList f bytes1 bytes2) :
    ∃ n2, storebytes m2 b2 (ofs + delta) bytes2 = some n2 ∧ Inject f n1 n2 := by
  obtain ⟨n2, hs2, hi⟩ := storebytes_mapped_inj h.inj hs h.no_overlap hf hv
  exact ⟨n2, hs2, h.of_perm_eq hi (storebytes_nextblock hs) (storebytes_nextblock hs2)
    (fun b o k p => perm_storebytes hs b o k p) (fun b o k p => perm_storebytes hs2 b o k p)⟩

/-- `Memory.storebytes_unmapped_inject` -/
theorem storebytes_unmapped_inject (h : Inject f m1 m2) {b1 : Block} {ofs : _root_.Int}
    {bytes1 : List MemVal} {n1 : Mem} (hs : storebytes m1 b1 ofs bytes1 = some n1)
    (hf : f b1 = none) : Inject f n1 m2 :=
  h.of_perm_eq (storebytes_unmapped_inj h.inj hs hf) (storebytes_nextblock hs) rfl
    (fun b o k p => perm_storebytes hs b o k p) (fun _ _ _ _ => rfl)

/-- `Memory.storebytes_outside_inject` -/
theorem storebytes_outside_inject (h : Inject f m1 m2) {b : Block} {ofs : _root_.Int}
    {bytes2 : List MemVal} {m2' : Mem}
    (hout : ∀ b' delta (ofs' : _root_.Int), f b' = some (b, delta) →
      perm m1 b' ofs' .Cur .Readable = true → ofs ≤ ofs' + delta →
      ofs' + delta < ofs + (bytes2.length : _root_.Int) → False)
    (hs : storebytes m2 b ofs bytes2 = some m2') : Inject f m1 m2' :=
  h.of_perm_eq (storebytes_outside_inj h.inj hout hs) rfl (storebytes_nextblock hs)
    (fun _ _ _ _ => rfl) (fun b o k p => perm_storebytes hs b o k p)

/-- `Memory.storev_mapped_inject` -/
theorem storev_mapped_inject (h : Inject f m1 m2) {chunk : Chunk} {a1 a2 v1 v2 : Val}
    {n1 : Mem} (hs : storev chunk m1 a1 v1 = some n1) (ha : Val.Inject f a1 a2)
    (hv : Val.Inject f v1 v2) : ∃ n2, storev chunk m2 a2 v2 = some n2 ∧ Inject f n1 n2 := by
  cases ha with
  | ptr delta hf ho =>
    subst ho
    simp only [storev] at hs ⊢
    split at hs
    · next hc =>
      rw [if_pos (address_inject_below h (store_valid_access hs) hc hf),
        address_inject' h (store_valid_access hs) hf]
      exact store_mapped_inject h hs hf hv
    · cases hs
  | _ => simp [storev] at hs

/-! ## Allocation and freeing -/

/-- `Memory.alloc_right_inject` -/
theorem alloc_right_inject (h : Inject f m1 m2) {lo hi : Z} {b2 : Block} {m2' : Mem}
    (ha : alloc m2 lo hi = (m2', b2)) : Inject f m1 m2' := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  refine ⟨alloc_right_inj h.inj (rfl : alloc m2 lo hi = (_, m2.nextblock)), h.freeblocks,
    fun b b' d hf => valid_block_alloc m2 lo hi (h.mappedblocks b b' d hf), h.no_overlap,
    h.representable, ?_, h.metadata⟩
  intro b1 o b2 d k p hf hp
  have hi := perm_alloc_inv hp
  split at hi
  · next he =>
    have hv := h.mappedblocks _ _ _ hf
    rw [he, fresh_block_alloc] at hv
    cases hv
  · exact h.perm_inv _ _ _ _ _ _ hf hi

/-- `Memory.alloc_left_unmapped_inject` -/
theorem alloc_left_unmapped_inject (h : Inject f m1 m2) {lo hi : Z} {b1 : Block} {m1' : Mem}
    (ha : alloc m1 lo hi = (m1', b1)) :
    ∃ f', Inject f' m1' m2 ∧ Val.inject_incr f f' ∧ f' b1 = none ∧
      ∀ b, b ≠ b1 → f' b = f b := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  have hnone : f m1.nextblock = none := h.freeblocks _ (fresh_block_alloc m1)
  have hne : ∀ {b b' d}, f b = some (b', d) → b ≠ m1.nextblock := by
    intro b b' d hfb he; subst he; rw [hnone] at hfb; cases hfb
  refine ⟨f, ⟨alloc_left_unmapped_inj h.inj (rfl : alloc m1 lo hi = (_, m1.nextblock)) hnone,
    ?_, h.mappedblocks, ?_, ?_, ?_, ?_⟩, Val.inject_incr_refl f, hnone, fun _ _ => rfl⟩
  · intro b hb
    cases hv : validBlock m1 b
    · exact h.freeblocks b hv
    · rw [valid_block_alloc m1 lo hi hv] at hb; cases hb
  · intro b1 b1' d1 b2 b2' d2 o1 o2 hne' hf1 hf2 hp1 hp2
    rw [perm_alloc_other m1 lo hi _ (hne hf1)] at hp1
    rw [perm_alloc_other m1 lo hi _ (hne hf2)] at hp2
    exact h.no_overlap _ _ _ _ _ _ _ _ hne' hf1 hf2 hp1 hp2
  · intro b b' d o hf hp
    rw [perm_alloc_other m1 lo hi _ (hne hf), perm_alloc_other m1 lo hi _ (hne hf)] at hp
    exact h.representable _ _ _ _ hf hp
  · intro b o b' d k p hf hp
    rw [perm_alloc_other m1 lo hi _ (hne hf), perm_alloc_other m1 lo hi _ (hne hf)]
    exact h.perm_inv _ _ _ _ _ _ hf hp
  · intro b b' d o hf hp
    rw [perm_alloc_other m1 lo hi _ (hne hf)] at hp
    exact h.metadata _ _ _ _ hf hp

/-- `Memory.free_left_inject` -/
theorem free_left_inject (h : Inject f m1 m2) {b : Block} {lo hi : _root_.Int} {m1' : Mem}
    (hfr : free m1 b lo hi = some m1') : Inject f m1' m2 := by
  have hinj := free_left_inj h.inj hfr
  rw [free_result hfr] at hinj ⊢
  refine ⟨hinj, fun b' hb => h.freeblocks b' (by simpa [validBlock] using hb), h.mappedblocks,
    ?_, ?_, ?_, ?_⟩
  · intro b1 b1' d1 b2 b2' d2 o1 o2 hne hf1 hf2 hp1 hp2
    exact h.no_overlap _ _ _ _ _ _ _ _ hne hf1 hf2 (perm_free_3 hp1) (perm_free_3 hp2)
  · intro b' b'' d o hf hp
    refine h.representable _ _ _ _ hf ?_
    rcases hp with hp | hp
    · exact Or.inl (perm_free_3 hp)
    · exact Or.inr (perm_free_3 hp)
  · intro b1 o b2 d k p hf hp
    exact free_perm_inv (h.perm_inv _ _ _ _ _ _ hf hp)
  · intro b' b'' d o hf hp
    exact h.metadata _ _ _ _ hf (perm_free_3 hp)

/-- `Memory.free_list_left_inject` -/
theorem freeList_left_inject {m2 : Mem} :
    ∀ (l : List (Block × Z × Z)) {m1 m1' : Mem}, Inject f m1 m2 → freeList m1 l = some m1' →
      Inject f m1' m2
  | [], _, _, h, hl => by simp only [freeList, Option.some.injEq] at hl; subst hl; exact h
  | (b, lo, hi) :: l, m1, m1', h, hl => by
    simp only [freeList] at hl
    split at hl
    · cases hl
    · next m11 hfr => exact freeList_left_inject l (free_left_inject h hfr) hl

/-- `Memory.free_right_inject` -/
theorem free_right_inject (h : Inject f m1 m2) {b : Block} {lo hi : _root_.Int} {m2' : Mem}
    (hfr : free m2 b lo hi = some m2')
    (hout : ∀ b1 delta (ofs : _root_.Int) k p, f b1 = some (b, delta) →
      perm m1 b1 ofs k p = true → lo ≤ ofs + delta → ofs + delta < hi → False) :
    Inject f m1 m2' := by
  have hinj := free_right_inj h.inj hfr hout
  rw [free_result hfr] at hinj ⊢
  refine ⟨hinj, h.freeblocks, fun b1 b' d hf => by simpa [validBlock] using h.mappedblocks _ _ _ hf,
    h.no_overlap, h.representable, ?_, h.metadata⟩
  intro b1 o b2 d k p hf hp
  exact h.perm_inv _ _ _ _ _ _ hf (perm_free_3 hp)

/-- `Memory.free_parallel_inject` -/
theorem free_parallel_inject (h : Inject f m1 m2) {b b' : Block} {lo hi delta : _root_.Int}
    {m1' : Mem} (hfr : free m1 b lo hi = some m1') (hf : f b = some (b', delta)) :
    ∃ m2', free m2 b' (lo + delta) (hi + delta) = some m2' ∧ Inject f m1' m2' := by
  have hr1 := free_rangePerm hfr
  have hr := rangePerm_inject hf h hr1
  refine ⟨_, free_isSome hr, free_right_inject (free_left_inject h hfr) (free_isSome hr) ?_⟩
  intro b1 d o k p hf1 hp h1 h2
  rw [free_result hfr] at hp
  by_cases hb : b1 = b
  · subst hb
    rw [hf] at hf1; cases hf1
    rw [perm_free_inside m1 _ lo hi o k p (by omega) (by omega)] at hp
    cases hp
  · have hq := perm_cur_max (perm_implies (rangePerm_perm _ _ _ _ _ _ hr1 (o + d - delta)
      (by omega) (by omega)) (show permOrder .Freeable .Nonempty = true by rfl))
    rcases h.no_overlap _ _ _ _ _ _ _ _ hb hf1 hf
      (perm_max (perm_implies (perm_free_3 hp) (by cases p <;> rfl))) hq with hc | hc
    · exact hc rfl
    · exact hc (by omega)

/-! ## Composition -/

theorem compose_meminj_some {f f' : Val.Meminj} {b1 b3 : Block} {d : Z}
    (hc : Val.compose_meminj f f' b1 = some (b3, d)) :
    ∃ b2 d1 d2, f b1 = some (b2, d1) ∧ f' b2 = some (b3, d2) ∧ d = d1 + d2 := by
  simp only [Val.compose_meminj] at hc
  split at hc
  · cases hc
  · next b2 d1 hf =>
    split at hc
    · cases hc
    · next b3' d2 hf' =>
      cases hc
      exact ⟨b2, d1, d2, hf, hf', rfl⟩

theorem compose_meminj_none {f f' : Val.Meminj} {b : Block} (h : f b = none) :
    Val.compose_meminj f f' b = none := by
  simp [Val.compose_meminj, h]

theorem compose_inject_id_left (f : Val.Meminj) : Val.compose_meminj Val.inject_id f = f := by
  funext b
  simp only [Val.compose_meminj, Val.inject_id]
  cases f b with
  | none => rfl
  | some p => rcases p with ⟨b', d⟩; simp only [Int.zero_add]

theorem compose_inject_id_right (f : Val.Meminj) : Val.compose_meminj f Val.inject_id = f := by
  funext b
  simp only [Val.compose_meminj, Val.inject_id]
  cases f b with
  | none => rfl
  | some p => rcases p with ⟨b', d⟩; simp only [Int.add_zero]

private theorem compose_arith_0 (u d : _root_.Int) : u - 1 + d = u + d - 1 := by omega

private theorem compose_arith_1 (u d1 d2 M : _root_.Int) (hA : d1 ≥ 0) (hA' : d2 ≥ 0)
    (hC : u + d1 + d2 ≤ M) (hB : 0 ≤ u + d1 + d2) :
    d1 + d2 ≥ 0 ∧ 0 ≤ u + (d1 + d2) ∧ u + (d1 + d2) ≤ M := by omega

private theorem compose_arith_2 (o1 o2 d1 d2 e : _root_.Int) (h : o1 + d1 ≠ o2 + d2) :
    o1 + (d1 + e) ≠ o2 + (d2 + e) := by omega

private theorem compose_arith_3 (o1 o2 d1 d2 e1 e2 : _root_.Int)
    (h : o1 + d1 + e1 ≠ o2 + d2 + e2) : o1 + (d1 + e1) ≠ o2 + (d2 + e2) := by omega

/-- `Memory.inject_compose` -/
theorem inject_compose {f f' : Val.Meminj} {m3 : Mem} (h12 : Inject f m1 m2)
    (h23 : Inject f' m2 m3) : Inject (Val.compose_meminj f f') m1 m3 := by
  refine ⟨memInj_compose h12.inj h23.inj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact compose_meminj_none (h12.freeblocks b hb)
  · intro b b' d hc
    obtain ⟨b2, d1, d2, _, hf', _⟩ := compose_meminj_some hc
    exact h23.mappedblocks _ _ _ hf'
  · intro b1 b1' d1 b2 b2' d2 o1 o2 hne hc1 hc2 hp1 hp2
    obtain ⟨b1x, d1x, d1y, hf1, hf1', rfl⟩ := compose_meminj_some hc1
    obtain ⟨b2x, d2x, d2y, hf2, hf2', rfl⟩ := compose_meminj_some hc2
    have A := h12.no_overlap _ _ _ _ _ _ _ _ hne hf1 hf2 hp1 hp2
    by_cases hx : b1x = b2x
    · subst hx
      rw [hf1'] at hf2'; cases hf2'
      rcases A with A | A
      · exact absurd rfl A
      · exact Or.inr (compose_arith_2 _ _ _ _ _ A)
    · rcases h23.no_overlap _ _ _ _ _ _ _ _ hx hf1' hf2' (perm_inj h12.inj hp1 hf1)
        (perm_inj h12.inj hp2 hf2) with B | B
      · exact Or.inl B
      · exact Or.inr (compose_arith_3 _ _ _ _ _ _ B)
  · intro b b' d ofs hc hp
    obtain ⟨b1, d1, d2, hf, hf', rfl⟩ := compose_meminj_some hc
    obtain ⟨hA, hB, hC⟩ := h12.representable _ _ _ _ hf hp
    have hU : Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs + d1)) =
        Ptrofs.unsigned ofs + d1 := Ptrofs.unsigned_repr hB hC
    have hp2 : perm m2 b1 (Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs + d1))) .Max
          .Nonempty = true ∨
        perm m2 b1 (Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs + d1)) - 1) .Max
          .Nonempty = true := by
      rw [hU]
      rcases hp with hp | hp
      · exact Or.inl (perm_inj h12.inj hp hf)
      · right
        have := perm_inj h12.inj hp hf
        rwa [compose_arith_0] at this
    obtain ⟨hA', hB', hC'⟩ := h23.representable _ _ _ _ hf' hp2
    rw [hU] at hB' hC'
    exact compose_arith_1 _ _ _ _ hA hA' hC' hB'
  · intro b1 o b3 d k p hc hp
    obtain ⟨b2, d1, d2, hf, hf', rfl⟩ := compose_meminj_some hc
    rw [← Int.add_assoc] at hp
    rcases h23.perm_inv _ _ _ _ _ _ hf' hp with A | A
    · exact h12.perm_inv _ _ _ _ _ _ hf A
    · right
      cases hq : perm m1 b1 o .Max .Nonempty
      · rfl
      · rw [perm_inj h12.inj hq hf] at A; cases A
  · intro b b' d o hc hp hlt
    obtain ⟨b1, d1, d2, hf, hf', rfl⟩ := compose_meminj_some hc
    have h1 := h12.metadata _ _ _ _ hf hp hlt
    have hp2 := perm_inj h12.inj hp hf
    rw [h1, Int.add_zero] at hp2
    rw [h1, h23.metadata _ _ _ _ hf' hp2 hlt]
    rfl

/-- `Memory.val_lessdef_inject_compose` -/
theorem val_lessdef_inject_compose {v1 v2 v3 : Val} (h1 : Val.Lessdef v1 v2)
    (h2 : Val.Inject f v2 v3) : Val.Inject f v1 v3 := by
  cases h1 with
  | refl => exact h2
  | undef => exact .undef _

/-- `Memory.val_inject_lessdef_compose` -/
theorem val_inject_lessdef_compose {v1 v2 v3 : Val} (h1 : Val.Inject f v1 v2)
    (h2 : Val.Lessdef v2 v3) : Val.Inject f v1 v3 := by
  cases h2 with
  | refl => exact h1
  | undef => cases h1; exact .undef _

/-- `Memory.extends_inject_compose` -/
theorem extends_inject_compose {m3 : Mem} (h12 : Extends m1 m2) (h23 : Inject f m2 m3) :
    Inject f m1 m3 := by
  refine ⟨?_, ?_, h23.mappedblocks, ?_, ?_, ?_, ?_⟩
  · have := memInj_compose h12.inj h23.inj
    rwa [compose_inject_id_left] at this
  · intro b hb
    exact h23.freeblocks b (by rw [← validBlock_extends h12]; exact hb)
  · intro b1 b1' d1 b2 b2' d2 o1 o2 hne hf1 hf2 hp1 hp2
    exact h23.no_overlap _ _ _ _ _ _ _ _ hne hf1 hf2 (perm_extends h12 hp1) (perm_extends h12 hp2)
  · intro b b' d o hf hp
    refine h23.representable _ _ _ _ hf ?_
    rcases hp with hp | hp
    · exact Or.inl (perm_extends h12 hp)
    · exact Or.inr (perm_extends h12 hp)
  · intro b1 o b2 d k p hf hp
    rcases h23.perm_inv _ _ _ _ _ _ hf hp with A | A
    · exact h12.perm_inv _ _ _ _ A
    · right
      cases hq : perm m1 b1 o .Max .Nonempty
      · rfl
      · rw [perm_extends h12 hq] at A; cases A
  · intro b b' d o hf hp hlt
    exact h23.metadata _ _ _ _ hf (perm_extends h12 hp) hlt

/-- `Memory.inject_extends_compose` -/
theorem inject_extends_compose {m3 : Mem} (h12 : Inject f m1 m2) (h23 : Extends m2 m3) :
    Inject f m1 m3 := by
  refine ⟨?_, h12.freeblocks, ?_, h12.no_overlap, h12.representable, ?_, h12.metadata⟩
  · have := memInj_compose h12.inj h23.inj
    rwa [compose_inject_id_right] at this
  · intro b b' d hf
    rw [← validBlock_extends h23]; exact h12.mappedblocks _ _ _ hf
  · intro b1 o b2 d k p hf hp
    rcases h23.perm_inv _ _ _ _ hp with A | A
    · exact h12.perm_inv _ _ _ _ _ _ hf A
    · right
      cases hq : perm m1 b1 o .Max .Nonempty
      · rfl
      · rw [perm_inj h12.inj hq hf] at A; cases A

/-! ## Allocation mapped into an existing block -/

private theorem amap_arith_1 (u d M : _root_.Int) (hu : 0 ≤ u) (huM : u ≤ M) (hd0 : 0 ≤ d)
    (h : d = 0 ∨ 0 ≤ u + d ∧ u + d < M) : d ≥ 0 ∧ 0 ≤ u + d ∧ u + d ≤ M := by omega

private theorem amap_arith_2 (u d M : _root_.Int) (hu : 0 ≤ u) (huM : u ≤ M) (hd0 : 0 ≤ d)
    (h : d = 0 ∨ 0 ≤ u - 1 + d ∧ u - 1 + d < M) : d ≥ 0 ∧ 0 ≤ u + d ∧ u + d ≤ M := by omega

/-- `Memory.alloc_left_mapped_inject` -/
theorem alloc_left_mapped_inject (h : Inject f m1 m2) {lo hi : _root_.Int} {b1 b2 : Block}
    {m1' : Mem} {delta : _root_.Int} (ha : alloc m1 lo hi = (m1', b1))
    (hvalid : validBlock m2 b2 = true)
    (hr1 : 0 ≤ delta ∧ delta ≤ Ptrofs.max_unsigned)
    (hr2 : delta = 0 ∨ 0 ≤ lo)
    (hr3 : ∀ (ofs : _root_.Int) k p, perm m2 b2 ofs k p = true →
      delta = 0 ∨ (0 ≤ ofs ∧ ofs < Ptrofs.max_unsigned))
    (hperm : ∀ (ofs : _root_.Int) k p, lo ≤ ofs → ofs < hi → perm m2 b2 (ofs + delta) k p = true)
    (hal : minSafeAlignment (hi - lo) ∣ delta)
    (hsep : ∀ b (delta' ofs : _root_.Int) k p, f b = some (b2, delta') →
      perm m1 b ofs k p = true → lo + delta ≤ ofs + delta' → ofs + delta' < hi + delta → False) :
    ∃ f', Inject f' m1' m2 ∧ Val.inject_incr f f' ∧ f' b1 = some (b2, delta) ∧
      ∀ b, b ≠ b1 → f' b = f b := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  have hnone : f m1.nextblock = none := h.freeblocks _ (fresh_block_alloc m1)
  let f' : Val.Meminj := fun b => if b = m1.nextblock then some (b2, delta) else f b
  have hf'1 : f' m1.nextblock = some (b2, delta) := if_pos rfl
  have hf'2 : ∀ b, b ≠ m1.nextblock → f' b = f b := fun b hb => if_neg hb
  have hincr : Val.inject_incr f f' := by
    intro b b' d hfb
    by_cases hb : b = m1.nextblock
    · subst hb; rw [hnone] at hfb; cases hfb
    · rw [hf'2 b hb]; exact hfb
  -- `f'` and `f` agree on every block carrying a permission in `m1`
  have hagree : ∀ {b o k p}, perm m1 b o k p = true → f' b = f b :=
    fun hp => hf'2 _ (ne_nextblock_of_perm hp)
  have hinj0 : MemInj f' m1 m2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro b b' d o k p hfb hp
      rw [hagree hp] at hfb
      exact h.inj.perm _ _ _ _ _ _ hfb hp
    · intro b b' d o sz p hfb hsz hr
      have hp := rangePerm_perm _ _ _ _ _ _ hr o (Int.le_refl _) (by omega)
      rw [hagree hp] at hfb
      exact h.inj.align _ _ _ _ _ _ hfb hsz hr
    · intro b o b' d hfb hp
      rw [hagree hp] at hfb
      exact (h.inj.memval _ _ _ _ hfb hp).incr hincr
  have hrange := Ptrofs.unsigned_range_2
  refine ⟨f', ⟨alloc_left_mapped_inj hinj0 (rfl : alloc m1 lo hi = (_, m1.nextblock)) hal
      hperm hf'1, ?_, ?_, ?_, ?_, ?_, ?_⟩, hincr, hf'1, hf'2⟩
  · -- freeblocks
    intro b hb
    have hne : b ≠ m1.nextblock := by
      intro he; subst he
      have hv : validBlock (alloc m1 lo hi).1 m1.nextblock = true := valid_new_block m1 lo hi
      rw [hv] at hb; cases hb
    rw [hf'2 b hne]
    cases hv : validBlock m1 b
    · exact h.freeblocks b hv
    · rw [valid_block_alloc m1 lo hi hv] at hb; cases hb
  · -- mappedblocks
    intro b b' d hfb
    by_cases hb : b = m1.nextblock
    · subst hb; rw [hf'1] at hfb; cases hfb; exact hvalid
    · rw [hf'2 b hb] at hfb; exact h.mappedblocks _ _ _ hfb
  · -- no overlap
    intro x1 y1 d1 x2 y2 d2 o1 o2 hne hf1 hf2 hp1 hp2
    have P1 := perm_alloc_inv hp1
    have P2 := perm_alloc_inv hp2
    by_cases hx1 : x1 = m1.nextblock
    · subst hx1
      have hx2 : x2 ≠ m1.nextblock := fun he => hne he.symm
      rw [if_pos rfl] at P1
      rw [if_neg hx2] at P2
      rw [hf'1] at hf1; cases hf1
      rw [hf'2 _ hx2] at hf2
      by_cases hy : b2 = y2
      · subst hy
        exact Or.inr (fun heq => hsep _ _ _ _ _ hf2 P2 (by omega) (by omega))
      · exact Or.inl hy
    · rw [if_neg hx1] at P1
      rw [hf'2 _ hx1] at hf1
      by_cases hx2 : x2 = m1.nextblock
      · subst hx2
        rw [if_pos rfl] at P2
        rw [hf'1] at hf2; cases hf2
        by_cases hy : y1 = b2
        · subst hy
          exact Or.inr (fun heq => hsep _ _ _ _ _ hf1 P1 (by omega) (by omega))
        · exact Or.inl hy
      · rw [if_neg hx2] at P2
        rw [hf'2 _ hx2] at hf2
        exact h.no_overlap _ _ _ _ _ _ _ _ hne hf1 hf2 P1 P2
  · -- representable
    intro b b' d ofs hfb hp
    by_cases hb : b = m1.nextblock
    · subst hb
      rw [hf'1] at hfb; cases hfb
      have hu := hrange ofs
      rcases hp with hp | hp
      · have P := perm_alloc_inv hp
        rw [if_pos rfl] at P
        exact amap_arith_1 _ _ _ hu.1 hu.2 hr1.1 (hr3 _ _ _ (hperm _ .Max .Nonempty P.1 P.2))
      · have P := perm_alloc_inv hp
        rw [if_pos rfl] at P
        exact amap_arith_2 _ _ _ hu.1 hu.2 hr1.1 (hr3 _ _ _ (hperm _ .Max .Nonempty P.1 P.2))
    · rw [hf'2 b hb] at hfb
      rw [perm_alloc_other m1 lo hi b hb, perm_alloc_other m1 lo hi b hb] at hp
      exact h.representable _ _ _ _ hfb hp
  · -- perm inv
    intro b o b' d k p hfb hp
    by_cases hb : b = m1.nextblock
    · subst hb
      rcases Int.lt_or_le o lo with h1 | h1
      · exact Or.inr (perm_alloc_outside m1 lo hi o .Max .Nonempty (Or.inl h1))
      rcases Int.lt_or_le o hi with h2 | h2
      · exact Or.inl (perm_implies (perm_alloc_same m1 lo hi o k h1 h2) (by cases p <;> rfl))
      · exact Or.inr (perm_alloc_outside m1 lo hi o .Max .Nonempty (Or.inr h2))
    · rw [hf'2 b hb] at hfb
      rw [perm_alloc_other m1 lo hi b hb, perm_alloc_other m1 lo hi b hb]
      exact h.perm_inv _ _ _ _ _ _ hfb hp
  · -- metadata
    intro b b' d o hfb hp hlt
    by_cases hb : b = m1.nextblock
    · subst hb
      rw [hf'1] at hfb; cases hfb
      have P := perm_alloc_inv hp
      rw [if_pos rfl] at P
      rcases hr2 with hr2 | hr2
      · exact hr2
      · omega
    · rw [hf'2 b hb] at hfb
      rw [perm_alloc_other m1 lo hi b hb] at hp
      exact h.metadata _ _ _ _ hfb hp hlt

/-- `Memory.alloc_parallel_inject` -/
theorem alloc_parallel_inject (h : Inject f m1 m2) {lo1 hi1 lo2 hi2 : _root_.Int} {b1 : Block}
    {m1' : Mem} (ha : alloc m1 lo1 hi1 = (m1', b1)) (hlo : lo2 ≤ lo1) (hhi : hi1 ≤ hi2) :
    ∃ f' m2' b2, alloc m2 lo2 hi2 = (m2', b2) ∧ Inject f' m1' m2' ∧ Val.inject_incr f f' ∧
      f' b1 = some (b2, 0) ∧ ∀ b, b ≠ b1 → f' b = f b := by
  have h2 := alloc_right_inject h (rfl : alloc m2 lo2 hi2 = (_, m2.nextblock))
  obtain ⟨f', hi, hincr, hb1, hother⟩ := alloc_left_mapped_inject (delta := 0) (b2 := m2.nextblock)
    h2 ha (valid_new_block m2 lo2 hi2)
    ⟨Int.le_refl _, by decide⟩ (Or.inl rfl) (fun _ _ _ _ => Or.inl rfl)
    (fun o k p h1 h2 => by
      rw [Int.add_zero]
      exact perm_implies (perm_alloc_same m2 lo2 hi2 o k (by omega) (by omega)) (by cases p <;> rfl))
    (Int.dvd_zero _)
    (fun b d o k p hfb _ _ _ => by
      have hv := h.mappedblocks _ _ _ hfb
      rw [fresh_block_alloc] at hv; cases hv)
  exact ⟨f', _, _, rfl, hi, hincr, hb1, hother⟩

/-! ## Neutral injections -/

/-- `Memory.flat_inj`: the identity on blocks below `thr`, undefined above. -/
def flatInj (thr : Block) : Val.Meminj := fun b => if b < thr then some (b, 0) else none

/-- `Memory.inject_neutral` -/
def InjectNeutral (thr : Block) (m : Mem) : Prop := MemInj (flatInj thr) m m

theorem flatInj_some {thr b b' : Block} {d : Z} (h : flatInj thr b = some (b', d)) :
    b' = b ∧ d = 0 ∧ b < thr := by
  simp only [flatInj] at h
  split at h
  · next hlt => cases h; exact ⟨rfl, rfl, hlt⟩
  · cases h

/-- `Memory.flat_inj_no_overlap` -/
theorem flatInj_no_overlap (thr : Block) (m : Mem) : MeminjNoOverlap (flatInj thr) m := by
  intro b1 b1' d1 b2 b2' d2 o1 o2 hne hf1 hf2 _ _
  obtain ⟨rfl, rfl, _⟩ := flatInj_some hf1
  obtain ⟨rfl, rfl, _⟩ := flatInj_some hf2
  exact Or.inl hne

/-- `Memory.neutral_inject` -/
theorem neutral_inject {m : Mem} (h : InjectNeutral m.nextblock m) :
    Inject (flatInj m.nextblock) m m := by
  refine ⟨h, ?_, ?_, flatInj_no_overlap _ m, ?_, ?_, ?_⟩
  · intro b hb
    simp only [validBlock, decide_eq_false_iff_not] at hb
    simp only [flatInj, if_neg hb]
  · intro b b' d hf
    obtain ⟨rfl, rfl, hlt⟩ := flatInj_some hf
    simpa [validBlock] using hlt
  · intro b b' d ofs hf _
    obtain ⟨rfl, rfl, _⟩ := flatInj_some hf
    have hr := Ptrofs.unsigned_range_2 ofs
    rw [Int.add_zero]
    exact ⟨Int.le_refl _, hr.1, hr.2⟩
  · intro b1 o b2 d k p hf hp
    obtain ⟨rfl, rfl, _⟩ := flatInj_some hf
    rw [Int.add_zero] at hp
    exact Or.inl hp
  · intro b b' d o hf _ _
    exact (flatInj_some hf).2.1

/-- `Memory.empty_inject_neutral` -/
theorem empty_inject_neutral (thr : Block) : InjectNeutral thr empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro b1 b2 d o k p _ hp
    simp [perm, empty, PMap.gi, permOrder'] at hp
  · intro b1 b2 d o sz p _ hsz hr
    have hp := rangePerm_perm _ _ _ _ _ _ hr o (Int.le_refl _) (by omega)
    simp [perm, empty, PMap.gi, permOrder'] at hp
  · intro b1 o b2 d _ hp
    simp [perm, empty, PMap.gi, permOrder'] at hp

/-- `Memory.alloc_inject_neutral` -/
theorem alloc_inject_neutral {thr : Block} {m : Mem} {lo hi : _root_.Int} {b : Block}
    {m' : Mem} (ha : alloc m lo hi = (m', b)) (h : InjectNeutral thr m)
    (hlt : m.nextblock < thr) : InjectNeutral thr m' := by
  obtain ⟨rfl, rfl⟩ := alloc_eq ha
  refine alloc_left_mapped_inj (b2 := m.nextblock)
    (alloc_right_inj h (rfl : alloc m lo hi = (_, m.nextblock)))
    (rfl : alloc m lo hi = (_, m.nextblock)) (Int.dvd_zero _) ?_ ?_
  · intro o k p h1 h2
    rw [Int.add_zero]
    exact perm_implies (perm_alloc_same m lo hi o k h1 h2) (by cases p <;> rfl)
  · simp only [flatInj, if_pos hlt]

/-- `Memory.store_inject_neutral` -/
theorem store_inject_neutral {thr : Block} {chunk : Chunk} {m : Mem} {b : Block}
    {ofs : _root_.Int} {v : Val} {m' : Mem} (hs : store chunk m b ofs v = some m')
    (h : InjectNeutral thr m) (hlt : b < thr) (hv : Val.Inject (flatInj thr) v v) :
    InjectNeutral thr m' := by
  obtain ⟨n2, hs2, hi⟩ := store_mapped_inj h hs (flatInj_no_overlap thr m)
    (show flatInj thr b = some (b, 0) by simp only [flatInj, if_pos hlt]) hv
  rw [Int.add_zero, hs] at hs2
  cases hs2
  exact hi

end

end Mem
end CC
