/-
  Elimination of unneeded computations over RTL: correctness proof — port of
  `backend/Deadcodeproof.v`, part 1: the `magree` relation between memory
  states (`magree_monotone`, `mextends_agree`, `magree_extends`,
  `magree_loadbytes`, `magree_load`, `magree_loadv`,
  `magree_storebytes_parallel`, `magree_store_parallel`,
  `magree_storev_parallel`, `magree_storebytes_left`, `magree_store_left`,
  `magree_free`, `magree_valid_access`).

  `magree m1 m2 P` is a variant of `Mem.extends` in which the contents of the
  two memory states may differ arbitrarily outside the locations satisfying
  `P`.
-/
import CCLib.common.MemoryExtends
import CCLib.common.MemoryLemmas
import CCLib.common.MemoryBytes
import CCLib.common.MemoryTheory
import CCLib.common.MemoryInject
import CCLib.backend.ValueDomainMemProof
import CCLib.backend.NeedDomainProof2

namespace CC
namespace Deadcodeproof

open Mem

/-- `Deadcodeproof.locset` -/
abbrev Locset := Block → Z → Prop

/-- `Deadcodeproof.magree` -/
structure Magree (m1 m2 : Mem) (P : Locset) : Prop where
  ma_perm : ∀ b ofs k p, Mem.perm m1 b ofs k p = true → Mem.perm m2 b ofs k p = true
  ma_perm_inv : ∀ b ofs k p, Mem.perm m2 b ofs k p = true →
    Mem.perm m1 b ofs k p = true ∨ Mem.perm m1 b ofs .Max .Nonempty = false
  ma_memval : ∀ b ofs, Mem.perm m1 b ofs .Cur .Readable = true → P b ofs →
    MemvalInject Val.inject_id (ZMap.get ofs (PMap.get b m1.contents))
      (ZMap.get ofs (PMap.get b m2.contents))
  ma_nextblock : m2.nextblock = m1.nextblock

variable {m1 m2 : Mem} {P Q : Locset}

/-- `Deadcodeproof.magree_monotone` -/
theorem magree_monotone (h : Magree m1 m2 P) (hq : ∀ b ofs, Q b ofs → P b ofs) :
    Magree m1 m2 Q :=
  ⟨h.ma_perm, h.ma_perm_inv, fun b ofs hp hQ => h.ma_memval b ofs hp (hq b ofs hQ),
    h.ma_nextblock⟩

/-- `Deadcodeproof.mextends_agree` -/
theorem mextends_agree (h : Mem.Extends m1 m2) (P : Locset) : Magree m1 m2 P := by
  refine ⟨fun b ofs k p hp => ?_, h.perm_inv, fun b ofs hp _ => ?_, h.next.symm⟩
  · have := h.inj.perm b b 0 ofs k p rfl hp
    rwa [Int.add_zero] at this
  · have := h.inj.memval b ofs b 0 rfl hp
    rwa [Int.add_zero] at this

/-- `Deadcodeproof.magree_extends` -/
theorem magree_extends (hP : ∀ b ofs, P b ofs) (h : Magree m1 m2 P) : Mem.Extends m1 m2 := by
  refine ⟨h.ma_nextblock.symm, ⟨?_, ?_, ?_⟩, h.ma_perm_inv⟩
  · intro b1 b2 d o k p hf hp
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    rw [Int.add_zero]; exact h.ma_perm _ _ _ _ hp
  · intro b1 b2 d o sz p hf _ _
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    exact Int.dvd_zero _
  · intro b1 o b2 d hf hp
    obtain ⟨rfl, rfl⟩ := inject_id_eq hf
    rw [Int.add_zero]
    exact h.ma_memval _ _ hp (hP _ _)

private theorem getN_lessdef (c1 c2 : ZMap MemVal) :
    ∀ (n : Nat) (ofs : _root_.Int),
    (∀ i : _root_.Int, ofs ≤ i → i < ofs + n →
      MemvalInject Val.inject_id (ZMap.get i c1) (ZMap.get i c2)) →
    MemvalInjectList Val.inject_id (getN n ofs c1) (getN n ofs c2)
  | 0, _, _ => .nil
  | n + 1, ofs, h =>
    .cons (h ofs (Int.le_refl _) (by omega))
      (getN_lessdef c1 c2 n (ofs + 1) fun i h1 h2 => h i (by omega) (by omega))

/-- `Deadcodeproof.magree_loadbytes` -/
theorem magree_loadbytes {b : Block} {ofs n : _root_.Int} {bytes : List MemVal}
    (h : Magree m1 m2 P) (hl : loadbytes m1 b ofs n = some bytes)
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + n → P b i) :
    ∃ bytes', loadbytes m2 b ofs n = some bytes' ∧
      MemvalInjectList Val.inject_id bytes bytes' := by
  have r := loadbytes_range_perm hl
  rw [loadbytes_result r] at hl
  cases hl
  have r2 : rangePerm m2 b ofs (ofs + n) .Cur .Readable = true :=
    rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
      h.ma_perm _ _ _ _ (rangePerm_perm _ _ _ _ _ _ r o h1 h2)
  refine ⟨_, loadbytes_result r2, getN_lessdef _ _ _ _ fun i h1 h2 => ?_⟩
  have h2' : i < ofs + n := by omega
  exact h.ma_memval _ _ (rangePerm_perm _ _ _ _ _ _ r i h1 h2') (hP i h1 h2')

/-- `Deadcodeproof.magree_load` -/
theorem magree_load {chunk : Chunk} {b : Block} {ofs : _root_.Int} {v : Val}
    (h : Magree m1 m2 P) (hl : load chunk m1 b ofs = some v)
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + sizeChunk chunk → P b i) :
    ∃ v', load chunk m2 b ofs = some v' ∧ Val.Lessdef v v' := by
  have hva := load_valid_access hl
  obtain ⟨bytes, LB, rfl⟩ := load_loadbytes hl
  obtain ⟨bytes', LB', INJ⟩ := magree_loadbytes h LB hP
  simp only [validAccess, Bool.and_eq_true, beq_iff_eq] at hva
  refine ⟨_, loadbytes_load LB' (Int.dvd_of_emod_eq_zero hva.2), ?_⟩
  exact Val.val_inject_id.1 (decodeVal_inject chunk INJ)

/-- `Deadcodeproof.magree_loadv` -/
theorem magree_loadv {chunk : Chunk} {b : Block} {ofs : Integers.Ptrofs} {v : Val}
    (h : Magree m1 m2 P) (hl : loadv chunk m1 (.Vptr b ofs) = some v)
    (hP : ∀ i : _root_.Int, Integers.Ptrofs.unsigned ofs ≤ i →
      i < Integers.Ptrofs.unsigned ofs + sizeChunk chunk → P b i) :
    ∃ v', loadv chunk m2 (.Vptr b ofs) = some v' ∧ Val.Lessdef v v' := by
  simp only [loadv] at hl ⊢
  split at hl
  · obtain ⟨v', A, B⟩ := magree_load h hl hP
    exact ⟨v', by rw [if_pos ‹_›]; exact A, B⟩
  · cases hl

private theorem setN_lessdef (access : _root_.Int → Prop) :
    ∀ {bytes1 bytes2 : List MemVal}, MemvalInjectList Val.inject_id bytes1 bytes2 →
    ∀ (p : _root_.Int) (c1 c2 : ZMap MemVal),
    (∀ i, access i → i < p ∨ p + (bytes1.length : _root_.Int) ≤ i →
      MemvalInject Val.inject_id (ZMap.get i c1) (ZMap.get i c2)) →
    ∀ q, access q →
      MemvalInject Val.inject_id (ZMap.get q (setN bytes1 p c1)) (ZMap.get q (setN bytes2 p c2))
  | _, _, .nil, p, c1, c2, h, q, hq => h q hq (by have := Int.lt_or_le q p; simpa using this)
  | _ :: _, _ :: _, .cons hv hl, p, c1, c2, h, q, hq => by
    simp only [setN]
    refine setN_lessdef access hl (p + 1) _ _ (fun i hi hr => ?_) q hq
    by_cases hip : i = p
    · subst hip; rw [ZMap.gss, ZMap.gss]; exact hv
    · rw [ZMap.gso _ _ _ _ (Ne.symm hip), ZMap.gso _ _ _ _ (Ne.symm hip)]
      refine h i hi ?_
      simp only [List.length_cons] at hr ⊢
      omega

/-- `Deadcodeproof.magree_storebytes_parallel` -/
theorem magree_storebytes_parallel {b : Block} {ofs : _root_.Int} {bytes1 bytes2 : List MemVal}
    {m1' : Mem} (h : Magree m1 m2 P) (hs : storebytes m1 b ofs bytes1 = some m1')
    (hPQ : ∀ b' (i : _root_.Int), Q b' i →
      b' ≠ b ∨ i < ofs ∨ ofs + (bytes1.length : _root_.Int) ≤ i → P b' i)
    (hl : MemvalInjectList Val.inject_id bytes1 bytes2) :
    ∃ m2', storebytes m2 b ofs bytes2 = some m2' ∧ Magree m1' m2' Q := by
  have hlen : bytes1.length = bytes2.length := by
    clear hs hPQ
    induction hl with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  have r1 : rangePerm m1 b ofs (ofs + (bytes1.length : Z)) .Cur .Writable = true := by
    unfold storebytes at hs; split at hs
    · assumption
    · cases hs
  obtain ⟨m2', ST2⟩ := storebytes_isSome (m := m2) (b := b) (ofs := ofs) (bytes := bytes2)
    (rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
      h.ma_perm _ _ _ _ (rangePerm_perm _ _ _ _ _ _ r1 o h1 (by rw [hlen]; exact h2)))
  refine ⟨m2', ST2, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro b' (o : _root_.Int) k p hp
    rw [perm_storebytes ST2]; rw [perm_storebytes hs] at hp
    exact h.ma_perm _ _ _ _ hp
  · intro b' (o : _root_.Int) k p hp
    rw [perm_storebytes ST2] at hp
    rw [perm_storebytes hs, perm_storebytes hs]
    exact h.ma_perm_inv _ _ _ _ hp
  · intro b' (o : _root_.Int) hp hq
    rw [storebytes_contents hs, storebytes_contents ST2]
    rw [perm_storebytes hs] at hp
    by_cases hb : b' = b
    · subst hb
      rw [PMap.gss, PMap.gss]
      exact setN_lessdef (fun o => Mem.perm m1 b' o .Cur .Readable = true ∧ Q b' o) hl ofs _ _
        (fun i hi hr => h.ma_memval _ _ hi.1 (hPQ _ _ hi.2 (.inr hr))) o ⟨hp, hq⟩
    · rw [PMap.gso _ _ _ _ (Ne.symm hb), PMap.gso _ _ _ _ (Ne.symm hb)]
      exact h.ma_memval _ _ hp (hPQ _ _ hq (.inl hb))
  · rw [storebytes_nextblock hs, storebytes_nextblock ST2]; exact h.ma_nextblock

/-- `Deadcodeproof.magree_store_parallel` -/
theorem magree_store_parallel {chunk : Chunk} {b : Block} {ofs : _root_.Int} {v1 v2 : Val}
    {m1' : Mem} (h : Magree m1 m2 P) (hs : store chunk m1 b ofs v1 = some m1')
    (hv : NeedDomain.vagree v1 v2 (NeedDomain.storeArgument chunk))
    (hPQ : ∀ b' (i : _root_.Int), Q b' i →
      b' ≠ b ∨ i < ofs ∨ ofs + sizeChunk chunk ≤ i → P b' i) :
    ∃ m2', store chunk m2 b ofs v2 = some m2' ∧ Magree m1' m2' Q := by
  have hva := store_valid_access hs
  have SB1 := store_storebytes hs
  obtain ⟨m2', SB2, AG⟩ := magree_storebytes_parallel h SB1
    (fun b' i hq hr => hPQ b' i hq (by
      rw [length_encodeVal, sizeChunkNat_cast] at hr; exact hr))
    (NeedDomain.store_argument_sound chunk hv)
  refine ⟨m2', ?_, AG⟩
  unfold store
  have hva2 : validAccess m2 chunk b ofs .Writable = true := by
    simp only [validAccess, Bool.and_eq_true] at hva ⊢
    exact ⟨rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
      h.ma_perm _ _ _ _ (rangePerm_perm _ _ _ _ _ _ hva.1 o h1 h2), hva.2⟩
  rw [if_pos hva2]
  unfold storebytes at SB2
  split at SB2
  · cases SB2; rfl
  · cases SB2

/-- `Deadcodeproof.magree_storev_parallel` -/
theorem magree_storev_parallel {chunk : Chunk} {b : Block} {ofs : Integers.Ptrofs} {v1 v2 : Val}
    {m1' : Mem} (h : Magree m1 m2 P) (hs : storev chunk m1 (.Vptr b ofs) v1 = some m1')
    (hv : NeedDomain.vagree v1 v2 (NeedDomain.storeArgument chunk))
    (hPQ : ∀ b' (i : _root_.Int), Q b' i →
      b' ≠ b ∨ i < Integers.Ptrofs.unsigned ofs ∨
        Integers.Ptrofs.unsigned ofs + sizeChunk chunk ≤ i → P b' i) :
    ∃ m2', storev chunk m2 (.Vptr b ofs) v2 = some m2' ∧ Magree m1' m2' Q := by
  simp only [storev] at hs ⊢
  split at hs
  · obtain ⟨m2', A, B⟩ := magree_store_parallel h hs hv hPQ
    exact ⟨m2', by rw [if_pos ‹_›]; exact A, B⟩
  · cases hs

/-- `Deadcodeproof.magree_storebytes_left` -/
theorem magree_storebytes_left {b : Block} {ofs : _root_.Int} {bytes1 : List MemVal} {m1' : Mem}
    (h : Magree m1 m2 P) (hs : storebytes m1 b ofs bytes1 = some m1')
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + (bytes1.length : _root_.Int) → ¬ P b i) :
    Magree m1' m2 P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b' (o : _root_.Int) k p hp
    rw [perm_storebytes hs] at hp
    exact h.ma_perm _ _ _ _ hp
  · intro b' (o : _root_.Int) k p hp
    rw [perm_storebytes hs, perm_storebytes hs]
    exact h.ma_perm_inv _ _ _ _ hp
  · intro b' (o : _root_.Int) hp hq
    rw [perm_storebytes hs] at hp
    rw [storebytes_contents hs]
    by_cases hb : b' = b
    · subst hb
      rw [PMap.gss, setN_outside]
      · exact h.ma_memval _ _ hp hq
      · by_cases h1 : o < ofs
        · exact .inl h1
        · by_cases h2 : ofs + (bytes1.length : _root_.Int) ≤ o
          · exact .inr h2
          · exact absurd hq (hP o (by omega) (by omega))
    · rw [PMap.gso _ _ _ _ (Ne.symm hb)]
      exact h.ma_memval _ _ hp hq
  · rw [storebytes_nextblock hs]; exact h.ma_nextblock

/-- `Deadcodeproof.magree_store_left` -/
theorem magree_store_left {chunk : Chunk} {b : Block} {ofs : _root_.Int} {v1 : Val} {m1' : Mem}
    (h : Magree m1 m2 P) (hs : store chunk m1 b ofs v1 = some m1')
    (hP : ∀ i : _root_.Int, ofs ≤ i → i < ofs + sizeChunk chunk → ¬ P b i) :
    Magree m1' m2 P :=
  magree_storebytes_left h (store_storebytes hs) (fun i h1 h2 => hP i h1 (by
    rw [length_encodeVal, sizeChunkNat_cast] at h2; exact h2))

/-- `Deadcodeproof.magree_free` -/
theorem magree_free {b : Block} {lo hi : _root_.Int} {m1' : Mem}
    (h : Magree m1 m2 P) (hf : free m1 b lo hi = some m1')
    (hPQ : ∀ b' (i : _root_.Int), Q b' i → b' ≠ b ∨ ¬ (lo ≤ i ∧ i < hi) → P b' i) :
    ∃ m2', free m2 b lo hi = some m2' ∧ Magree m1' m2' Q := by
  have r := free_rangePerm hf
  have r2 : rangePerm m2 b lo hi .Cur .Freeable = true :=
    rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
      h.ma_perm _ _ _ _ (rangePerm_perm _ _ _ _ _ _ r o h1 h2)
  refine ⟨_, free_isSome r2, ?_⟩
  rw [free_result hf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b' (o : _root_.Int) k p hp
    have hp2 := h.ma_perm _ _ _ _ (perm_free_3 hp)
    by_cases hin : b' = b ∧ lo ≤ o ∧ o < hi
    · obtain ⟨rfl, h1, h2⟩ := hin
      rw [perm_free_inside _ _ _ _ _ _ _ h1 h2] at hp; cases hp
    · refine perm_free_1 ?_ hp2
      by_cases hb : b' = b
      · refine .inr ?_
        by_cases h1 : lo ≤ o
        · by_cases h2 : o < hi
          · exact absurd ⟨hb, h1, h2⟩ hin
          · omega
        · omega
      · exact .inl hb
  · intro b' (o : _root_.Int) k p hp
    rcases h.ma_perm_inv _ _ _ _ (perm_free_3 hp) with A | A
    · by_cases hin : b' = b ∧ lo ≤ o ∧ o < hi
      · obtain ⟨rfl, h1, h2⟩ := hin
        exact .inr (perm_free_inside _ _ _ _ _ _ _ h1 h2)
      · refine .inl (perm_free_1 ?_ A)
        by_cases hb : b' = b
        · refine .inr ?_
          by_cases h1 : lo ≤ o
          · by_cases h2 : o < hi
            · exact absurd ⟨hb, h1, h2⟩ hin
            · omega
          · omega
        · exact .inl hb
    · right
      cases e : Mem.perm (uncheckedFree m1 b lo hi) b' o .Max .Nonempty with
      | false => rfl
      | true => rw [perm_free_3 e] at A; cases A
  · intro b' (o : _root_.Int) hp hq
    simp only [uncheckedFree_contents]
    refine h.ma_memval _ _ (perm_free_3 hp) (hPQ _ _ hq ?_)
    by_cases hb : b' = b
    · subst hb
      right
      intro ⟨h1, h2⟩
      rw [perm_free_inside _ _ _ _ _ _ _ h1 h2] at hp; cases hp
    · exact .inl hb
  · simp only [uncheckedFree_nextblock]; exact h.ma_nextblock

/-- `Deadcodeproof.magree_valid_access` -/
theorem magree_valid_access {chunk : Chunk} {b : Block} {ofs : Z} {p : Permission}
    (h : Magree m1 m2 P) (hv : validAccess m1 chunk b ofs p = true) :
    validAccess m2 chunk b ofs p = true := by
  simp only [validAccess, Bool.and_eq_true] at hv ⊢
  exact ⟨rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
    h.ma_perm _ _ _ _ (rangePerm_perm _ _ _ _ _ _ hv.1 o h1 h2), hv.2⟩

end Deadcodeproof
end CC
