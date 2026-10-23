/-
  The `Memory.v` lemma slice the separation logic needs — Phase 7.1.

  `CCLib/common/Memory.lean` shipped the operations plus two permission lemmas.  A
  points-to predicate needs the store/load algebra on top of that: what a store
  changes (`store_contents`), what it leaves alone (`store_access`,
  `store_nextblock`), and the two round-trip theorems `load_store_same` and
  `load_store_other`.

  `withContents` is `private` in `Memory.lean`, so it cannot be named here.  That
  is not an obstacle: it produces a structure literal, so its projections reduce,
  and the lemmas below are stated purely in terms of `store` and the public
  fields.
-/
import CCLib.lib.MapsLemmas
import CCLib.common.MemdataLemmas
import CCLib.common.Memory

namespace CC
namespace Mem

/-! ## `getN` / `setN` algebra

Binders are spelled `_root_.Int` rather than `Z` so that `omega` sees its own
arithmetic instances — see the header of `CCLib/common/MemdataLemmas.lean`. -/

/-- `Memory.setN_outside` — a byte outside the written range is untouched. -/
theorem setN_outside (vl : List MemVal) (p q : _root_.Int) (c : ZMap MemVal)
    (h : q < p ∨ p + (vl.length : _root_.Int) ≤ q) :
    ZMap.get q (setN vl p c) = ZMap.get q c := by
  induction vl generalizing p c with
  | nil => rfl
  | cons v vl' ih =>
      have hne : p ≠ q := by
        simp only [List.length_cons] at h
        omega
      have hrec : q < p + 1 ∨ (p + 1) + (vl'.length : _root_.Int) ≤ q := by
        simp only [List.length_cons] at h
        omega
      show ZMap.get q (setN vl' (p + 1) (ZMap.set p v c)) = ZMap.get q c
      rw [ih (p + 1) (ZMap.set p v c) hrec]
      exact ZMap.gso p q v c hne

/-- `Memory.getN_setN_same` — reading back exactly what was written. -/
theorem getN_setN_same (vl : List MemVal) (p : _root_.Int) (c : ZMap MemVal) :
    getN vl.length p (setN vl p c) = vl := by
  induction vl generalizing p c with
  | nil => rfl
  | cons v vl' ih =>
      show ZMap.get p (setN vl' (p + 1) (ZMap.set p v c))
             :: getN vl'.length (p + 1) (setN vl' (p + 1) (ZMap.set p v c)) = v :: vl'
      rw [ih (p + 1) (ZMap.set p v c),
          setN_outside vl' (p + 1) p (ZMap.set p v c) (by omega),
          ZMap.gss]

/-- Pointwise dual of `getN_setN_same`: an individual written byte reads back.
    `Heap.Agrees` is a pointwise predicate, so the list-shaped lemma is not
    enough for the separation-logic store rule. -/
theorem setN_inside : ∀ (vl : List MemVal) (p : _root_.Int) (c : ZMap MemVal) (i : Nat),
    i < vl.length → ZMap.get (p + (i : _root_.Int)) (setN vl p c) = vl[i]! := by
  intro vl
  induction vl with
  | nil => intro _ _ i hi; simp at hi
  | cons v vl' ih =>
      intro p c i hi
      cases i with
      | zero =>
          show ZMap.get (p + (0 : _root_.Int)) (setN vl' (p + 1) (ZMap.set p v c)) = v
          rw [show p + (0 : _root_.Int) = p from by omega,
              setN_outside vl' (p + 1) p (ZMap.set p v c) (by omega), ZMap.gss]
      | succ j =>
          have hj : j < vl'.length := by simp only [List.length_cons] at hi; omega
          show ZMap.get (p + ((j + 1 : Nat) : _root_.Int))
                 (setN vl' (p + 1) (ZMap.set p v c)) = _
          rw [show p + ((j + 1 : Nat) : _root_.Int) = (p + 1) + (j : _root_.Int) from by
                push_cast; omega,
              ih (p + 1) (ZMap.set p v c) j hj]
          simp

/-- `Memory.getN_setN_outside` — a read entirely outside the written range sees
    the old contents. -/
theorem getN_setN_outside (vl : List MemVal) (n : Nat) (p q : _root_.Int)
    (c : ZMap MemVal) (h : q + (n : _root_.Int) ≤ p ∨ p + (vl.length : _root_.Int) ≤ q) :
    getN n q (setN vl p c) = getN n q c := by
  induction n generalizing q with
  | zero => rfl
  | succ k ih =>
      show ZMap.get q (setN vl p c) :: getN k (q + 1) (setN vl p c)
             = ZMap.get q c :: getN k (q + 1) c
      rw [setN_outside vl p q c (by omega), ih (q + 1) (by omega)]

/-! ## What a store does and does not change -/

theorem store_valid_access {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m') :
    validAccess m chunk b ofs .Writable = true := by
  unfold store at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem store_contents {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m') :
    m'.contents
      = PMap.set b (setN (encodeVal chunk v) ofs (PMap.get b m.contents)) m.contents := by
  unfold store at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

theorem store_access {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m') :
    m'.access = m.access := by
  unfold store at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

theorem store_nextblock {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m') :
    m'.nextblock = m.nextblock := by
  unfold store at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-- Permissions are unaffected by a store, in both directions. -/
theorem perm_store {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m')
    (b' : Block) (ofs' : Z) (k : PermKind) (p : Permission) :
    perm m' b' ofs' k p = perm m b' ofs' k p := by
  simp [perm, store_access h]

/-! ## Permission monotonicity -/

theorem permOrder_trans {p q r : Permission} (h1 : permOrder p q = true)
    (h2 : permOrder q r = true) : permOrder p r = true := by
  simp only [permOrder, decide_eq_true_eq] at *; omega

theorem perm_implies {m : Mem} {b : Block} {ofs : Z} {k : PermKind} {p q : Permission}
    (h : perm m b ofs k p = true) (hpq : permOrder p q = true) :
    perm m b ofs k q = true := by
  unfold perm at h ⊢
  generalize hg : PMap.get b m.access ofs k = o at h ⊢
  cases o with
  | none => simp [permOrder'] at h
  | some p' => simp only [permOrder'] at h ⊢; exact permOrder_trans h hpq

theorem rangePerm_implies {m : Mem} {b : Block} {lo hi : _root_.Int} {k : PermKind}
    {p q : Permission} (h : rangePerm m b lo hi k p = true) (hpq : permOrder p q = true) :
    rangePerm m b lo hi k q = true :=
  rangePerm_intro m b lo hi k q
    (fun ofs h1 h2 => perm_implies (rangePerm_perm m b lo hi k p h ofs h1 h2) hpq)

/-- A store leaves every `rangePerm` intact, because it does not touch `access`. -/
theorem rangePerm_store {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m')
    (b' : Block) (lo hi : _root_.Int) (k : PermKind) (p : Permission)
    (hrp : rangePerm m b' lo hi k p = true) :
    rangePerm m' b' lo hi k p = true :=
  rangePerm_intro m' b' lo hi k p
    (fun o h1 h2 => by
      rw [perm_store h b' o k p]
      exact rangePerm_perm m b' lo hi k p hrp o h1 h2)

theorem validAccess_implies {m : Mem} {chunk : Chunk} {b : Block} {ofs : Z}
    {p q : Permission} (h : validAccess m chunk b ofs p = true)
    (hpq : permOrder p q = true) : validAccess m chunk b ofs q = true := by
  simp only [validAccess, Bool.and_eq_true] at h ⊢
  exact ⟨rangePerm_implies h.1 hpq, h.2⟩

/-- Two adjacent permitted ranges join into one.  `malloc` hands out a header and
    a payload separately; `free` needs them as a single range. -/
theorem rangePerm_append {m : Mem} {b : Block} {lo mid hi : _root_.Int} {k : PermKind}
    {p : Permission} (h1 : rangePerm m b lo mid k p = true)
    (h2 : rangePerm m b mid hi k p = true) : rangePerm m b lo hi k p = true := by
  refine rangePerm_intro m b lo hi k p (fun ofs g1 g2 => ?_)
  by_cases hc : ofs < mid
  · exact rangePerm_perm m b lo mid k p h1 ofs g1 hc
  · exact rangePerm_perm m b mid hi k p h2 ofs (by omega) g2

/-! ## The load/store round trip -/

/-- `Memory.load_store_same` — reading back a stored value yields it, normalized
    by the chunk (`Val.load_result`). -/
theorem load_store_same {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m') :
    load chunk m' b ofs = some (Val.loadResult chunk v) := by
  have hvaW : validAccess m chunk b ofs .Writable = true := store_valid_access h
  have hva : validAccess m' chunk b ofs .Readable = true := by
    simp only [validAccess, Bool.and_eq_true] at hvaW ⊢
    exact ⟨rangePerm_store h b ofs (ofs + sizeChunk chunk) .Cur .Readable
             (rangePerm_implies hvaW.1 (by decide)), hvaW.2⟩
  unfold load
  rw [hva, store_contents h, PMap.gss]
  simp only [if_true]
  congr 1
  rw [show sizeChunkNat chunk = (encodeVal chunk v).length from
        (length_encodeVal chunk v).symm,
      getN_setN_same]
  exact decodeVal_encodeVal chunk v

/-- Two memories agreeing on `perm` throughout a block agree on `rangePerm`
    there.  The workhorse behind every "operation X preserves permissions"
    lemma: `rangePerm`'s body uses the `private` `rangePermAux`, so the only way
    to reason about it from outside is through the
    `rangePerm_intro` / `rangePerm_perm` pair. -/
theorem rangePerm_congr {m1 m2 : Mem} {b : Block} {lo hi : _root_.Int}
    {k : PermKind} {p : Permission}
    (h : ∀ ofs : _root_.Int, perm m1 b ofs k p = perm m2 b ofs k p) :
    rangePerm m1 b lo hi k p = rangePerm m2 b lo hi k p := by
  cases h2 : rangePerm m2 b lo hi k p
  · cases h1 : rangePerm m1 b lo hi k p
    · rfl
    · exact absurd (rangePerm_intro m2 b lo hi k p (fun o ha hb => by
        rw [← h o]; exact rangePerm_perm m1 b lo hi k p h1 o ha hb)) (by simp [h2])
  · exact rangePerm_intro m1 b lo hi k p (fun o ha hb => by
      rw [h o]; exact rangePerm_perm m2 b lo hi k p h2 o ha hb)

theorem validAccess_congr {m1 m2 : Mem} {chunk : Chunk} {b : Block} {ofs : Z}
    {p : Permission} (h : ∀ o : _root_.Int, perm m1 b o .Cur p = perm m2 b o .Cur p) :
    validAccess m1 chunk b ofs p = validAccess m2 chunk b ofs p := by
  simp only [validAccess, rangePerm_congr h]

/-- Permissions are *exactly* preserved by a store, as a `Bool` equality. -/
theorem rangePerm_store_eq {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m')
    (b' : Block) (lo hi : _root_.Int) (k : PermKind) (p : Permission) :
    rangePerm m' b' lo hi k p = rangePerm m b' lo hi k p :=
  rangePerm_congr (fun o => perm_store h b' o k p)

theorem validAccess_store_eq {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m')
    (chunk' : Chunk) (b' : Block) (ofs' : Z) (p : Permission) :
    validAccess m' chunk' b' ofs' p = validAccess m chunk' b' ofs' p := by
  simp only [validAccess, rangePerm_store_eq h]

/-- `Memory.load_store_other` — a load disjoint from the store sees the old
    memory.  This is the half the frame rule needs. -/
theorem load_store_other {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z}
    {v : Val} {m' : Mem} (h : store chunk m b ofs v = some m')
    (chunk' : Chunk) (b' : Block) (ofs' : _root_.Int)
    (hdisj : b' ≠ b ∨ ofs' + sizeChunk chunk' ≤ ofs ∨ ofs + sizeChunk chunk ≤ ofs') :
    load chunk' m' b' ofs' = load chunk' m b' ofs' := by
  unfold load
  rw [validAccess_store_eq h]
  cases hva : validAccess m chunk' b' ofs' .Readable
  · simp
  · simp only [if_true]
    congr 2
    rw [store_contents h]
    rcases hdisj with hb | hr
    · -- a different block: the write is invisible
      exact congrArg _ (PMap.gso b b' _ m.contents (fun heq => hb heq.symm))
    · -- same block, disjoint offset ranges
      by_cases hb : b' = b
      · subst hb
        rw [PMap.gss]
        refine getN_setN_outside (encodeVal chunk v) (sizeChunkNat chunk') ofs ofs'
          (PMap.get b' m.contents) ?_
        rw [length_encodeVal]
        simp only [sizeChunkNat]
        -- the `have … := h` steps re-elaborate the hypotheses at `_root_.Int`;
        -- as they stand their instances sit at `CC.Z` and `omega` cannot see them
        -- `rw [hc]` rather than `omega`: the goal's arithmetic instances sit at
        -- `CC.Z` while a re-typed hypothesis would sit at `Int`, and `omega`
        -- matches instances syntactically.  Rewriting the cast away makes the
        -- goal literally the hypothesis.
        rcases hr with h1 | h2
        · left
          have hc : ((sizeChunk chunk').toNat : Z) = sizeChunk chunk' := by
            cases chunk' <;> simp [sizeChunk]
          rw [hc]; exact h1
        · right
          have hc : ((sizeChunk chunk).toNat : Z) = sizeChunk chunk := by
            cases chunk <;> simp [sizeChunk]
          rw [hc]; exact h2
      · exact congrArg _ (PMap.gso b b' _ m.contents (fun heq => hb heq.symm))

/-! ## Allocation

`alloc` never fails and returns a structure literal, so its projections are
`rfl`.  What the program logic needs from it: the fresh block is `Freeable` and
`Undef` throughout `[lo, hi)`, and nothing else in memory moves — that second
part is what turns a function entry into new separation-logic resources without
disturbing the caller's. -/

@[simp] theorem alloc_result (m : Mem) (lo hi : Z) : (alloc m lo hi).2 = m.nextblock := rfl

@[simp] theorem alloc_nextblock (m : Mem) (lo hi : Z) :
    (alloc m lo hi).1.nextblock = m.nextblock.succ := rfl

@[simp] theorem alloc_access (m : Mem) (lo hi : Z) :
    (alloc m lo hi).1.access
      = PMap.set m.nextblock
          (fun ofs _ => if lo ≤ ofs ∧ ofs < hi then some .Freeable else none) m.access := rfl

@[simp] theorem alloc_contents (m : Mem) (lo hi : Z) :
    (alloc m lo hi).1.contents = PMap.set m.nextblock (ZMap.init MemVal.Undef) m.contents := rfl

/-- The freshly allocated block is `Freeable` on `[lo, hi)`. -/
theorem perm_alloc_same (m : Mem) (lo hi : _root_.Int) (ofs : _root_.Int) (k : PermKind)
    (h1 : lo ≤ ofs) (h2 : ofs < hi) :
    perm (alloc m lo hi).1 m.nextblock ofs k .Freeable = true := by
  simp [perm, PMap.gss, h1, h2, permOrder', permOrder, Permission.rank]

/-- ... and carries no permission outside it. -/
theorem perm_alloc_outside (m : Mem) (lo hi : _root_.Int) (ofs : _root_.Int) (k : PermKind)
    (p : Permission) (h : ofs < lo ∨ hi ≤ ofs) :
    perm (alloc m lo hi).1 m.nextblock ofs k p = false := by
  have hno : ¬ (lo ≤ ofs ∧ ofs < hi) := by omega
  simp [perm, PMap.gss, hno, permOrder']

/-- Allocation does not disturb any existing block. -/
theorem perm_alloc_other (m : Mem) (lo hi : Z) (b' : Block) (hb : b' ≠ m.nextblock)
    (ofs : Z) (k : PermKind) (p : Permission) :
    perm (alloc m lo hi).1 b' ofs k p = perm m b' ofs k p := by
  simp [perm, PMap.gso _ _ _ _ (Ne.symm hb)]

/-- The fresh block reads as `Undef` everywhere. -/
theorem getN_alloc_same (m : Mem) (lo hi : Z) (n : Nat) (ofs : _root_.Int) :
    getN n ofs (PMap.get m.nextblock (alloc m lo hi).1.contents)
      = List.replicate n MemVal.Undef := by
  rw [alloc_contents, PMap.gss]
  induction n generalizing ofs with
  | zero => rfl
  | succ k ih => simp only [getN, ZMap.gi, List.replicate, ih (ofs + 1)]

/-- Loads from other blocks are unaffected by an allocation. -/
theorem load_alloc_other (m : Mem) (lo hi : Z) (chunk : Chunk) (b' : Block)
    (hb : b' ≠ m.nextblock) (ofs : Z) :
    load chunk (alloc m lo hi).1 b' ofs = load chunk m b' ofs := by
  unfold load
  rw [validAccess_congr (m1 := (alloc m lo hi).1) (m2 := m) (chunk := chunk)
        (b := b') (ofs := ofs) (p := .Readable)
        (fun o => perm_alloc_other m lo hi b' hb o .Cur .Readable),
      alloc_contents, PMap.gso _ _ _ _ (Ne.symm hb)]

/-- The allocated block was not valid before. -/
theorem fresh_block_alloc (m : Mem) : validBlock m m.nextblock = false := by
  simp [validBlock, Positive.lt_iff]

/-! ## Freeing

`free` only clears permissions — `unchecked_free` keeps `contents` and
`nextblock` — so the bytes of a freed block are still there, just unreachable.
The program logic uses this at function exit: the locals' resources are consumed,
and everything else is untouched. -/

theorem free_rangePerm {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (h : free m b lo hi = some m') : rangePerm m b lo hi .Cur .Freeable = true := by
  unfold free at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem free_result {m : Mem} {b : Block} {lo hi : Z} {m' : Mem}
    (h : free m b lo hi = some m') : m' = uncheckedFree m b lo hi := by
  unfold free at h
  split at h
  · injection h with h; exact h.symm
  · exact absurd h (by simp)

/-- `free` succeeds exactly when the range is `Freeable`. -/
theorem free_isSome {m : Mem} {b : Block} {lo hi : Z}
    (h : rangePerm m b lo hi .Cur .Freeable = true) :
    free m b lo hi = some (uncheckedFree m b lo hi) := by
  unfold free; rw [h]; simp

@[simp] theorem uncheckedFree_contents (m : Mem) (b : Block) (lo hi : Z) :
    (uncheckedFree m b lo hi).contents = m.contents := rfl

@[simp] theorem uncheckedFree_nextblock (m : Mem) (b : Block) (lo hi : Z) :
    (uncheckedFree m b lo hi).nextblock = m.nextblock := rfl

theorem perm_free_other (m : Mem) (b : Block) (lo hi : Z) (b' : Block) (hb : b' ≠ b)
    (ofs : Z) (k : PermKind) (p : Permission) :
    perm (uncheckedFree m b lo hi) b' ofs k p = perm m b' ofs k p := by
  simp [perm, uncheckedFree, PMap.gso _ _ _ _ (Ne.symm hb)]

theorem perm_free_outside (m : Mem) (b : Block) (lo hi : _root_.Int) (ofs : _root_.Int)
    (k : PermKind) (p : Permission) (h : ofs < lo ∨ hi ≤ ofs) :
    perm (uncheckedFree m b lo hi) b ofs k p = perm m b ofs k p := by
  have hno : ¬ (lo ≤ ofs ∧ ofs < hi) := by omega
  simp [perm, uncheckedFree, PMap.gss, hno]

/-- Inside the freed range nothing is permitted any more. -/
theorem perm_free_inside (m : Mem) (b : Block) (lo hi : _root_.Int) (ofs : _root_.Int)
    (k : PermKind) (p : Permission) (h1 : lo ≤ ofs) (h2 : ofs < hi) :
    perm (uncheckedFree m b lo hi) b ofs k p = false := by
  simp [perm, uncheckedFree, PMap.gss, h1, h2, permOrder']

/-- Loads from a different block survive a free. -/
theorem load_free_other (m : Mem) (b : Block) (lo hi : Z) (chunk : Chunk) (b' : Block)
    (hb : b' ≠ b) (ofs : Z) :
    load chunk (uncheckedFree m b lo hi) b' ofs = load chunk m b' ofs := by
  unfold load
  rw [validAccess_congr (m1 := uncheckedFree m b lo hi) (m2 := m) (chunk := chunk)
        (b := b') (ofs := ofs) (p := .Readable)
        (fun o => perm_free_other m b lo hi b' hb o .Cur .Readable),
      uncheckedFree_contents]

/-- A `getN` is determined pointwise: knowing each byte pins the whole list.
    `Heap.Agrees` is pointwise, so this is the bridge from a fragment to
    `loadbytes`.

    Binders are `_root_.Int`, not `Z`: the offset arithmetic below is driven by
    `omega`, which is blind to `CC.Z`-elaborated operators (the standing hazard). -/
theorem getN_eq_of_agree : ∀ (vl : List MemVal) (ofs : _root_.Int) (c : ZMap MemVal),
    (∀ i : Nat, i < vl.length → ZMap.get (ofs + (i : _root_.Int)) c = vl[i]!) →
    getN vl.length ofs c = vl := by
  intro vl
  induction vl with
  | nil => intro _ _ _; rfl
  | cons v vl' ih =>
      intro ofs c hpt
      show ZMap.get ofs c :: getN vl'.length (ofs + 1) c = v :: vl'
      have h0 : ZMap.get ofs c = v := by
        have := hpt 0 (by simp)
        simpa using this
      rw [h0]
      refine congrArg _ (ih (ofs + 1) c (fun i hi => ?_))
      have hi1 := hpt (i + 1) (Nat.succ_lt_succ hi)
      rw [show ofs + ((i + 1 : Nat) : _root_.Int) = (ofs + 1) + (i : _root_.Int) from by
        push_cast; omega] at hi1
      simpa using hi1

/-! ## `storebytes` and `loadbytes`

`memcpy` is the one library external zlib actually calls, and its semantics
(`Events.ExtcallMemcpySem`) is stated in terms of `loadbytes`/`storebytes` rather
than `load`/`store`.  These mirror the `store_*` lemmas above; `storebytes`
shares `withContents` with `store`, so the proofs mirror too. -/

theorem storebytes_contents {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    {m' : Mem} (h : storebytes m b ofs bytes = some m') :
    m'.contents = PMap.set b (setN bytes ofs (PMap.get b m.contents)) m.contents := by
  unfold storebytes at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

theorem storebytes_access {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    {m' : Mem} (h : storebytes m b ofs bytes = some m') : m'.access = m.access := by
  unfold storebytes at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

theorem storebytes_nextblock {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    {m' : Mem} (h : storebytes m b ofs bytes = some m') :
    m'.nextblock = m.nextblock := by
  unfold storebytes at h
  split at h
  · injection h with h; subst h; rfl
  · exact absurd h (by simp)

/-- Permissions are unaffected by a `storebytes`, in both directions. -/
theorem perm_storebytes {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    {m' : Mem} (h : storebytes m b ofs bytes = some m')
    (b' : Block) (ofs' : Z) (k : PermKind) (p : Permission) :
    perm m' b' ofs' k p = perm m b' ofs' k p := by
  simp [perm, storebytes_access h]

/-- `storebytes` succeeds exactly when the range is writable. -/
theorem storebytes_isSome {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    (hrp : rangePerm m b ofs (ofs + (bytes.length : Z)) .Cur .Writable = true) :
    ∃ m', storebytes m b ofs bytes = some m' := by
  unfold storebytes
  rw [hrp]
  exact ⟨_, rfl⟩

/-- `loadbytes` succeeds exactly when the range is readable, and returns the
    contents verbatim. -/
theorem loadbytes_result {m : Mem} {b : Block} {ofs n : Z}
    (hrp : rangePerm m b ofs (ofs + n) .Cur .Readable = true) :
    loadbytes m b ofs n = some (getN n.toNat ofs (PMap.get b m.contents)) := by
  unfold loadbytes; rw [hrp]; rfl

/-- The bytes just written read back. -/
theorem loadbytes_storebytes_same {m : Mem} {b : Block} {ofs : Z}
    {bytes : List MemVal} {m' : Mem} (h : storebytes m b ofs bytes = some m')
    (hrp : rangePerm m' b ofs (ofs + (bytes.length : Z)) .Cur .Readable = true) :
    loadbytes m' b ofs (bytes.length : Z) = some bytes := by
  rw [loadbytes_result hrp, storebytes_contents h, PMap.gss,
      show ((bytes.length : Z)).toNat = bytes.length from by omega,
      getN_setN_same]

/-- Bytes outside the written range are untouched — the pointwise form
    `Heap.Agrees` needs. -/
theorem getN_storebytes_outside {m : Mem} {b : Block} {ofs : Z}
    {bytes : List MemVal} {m' : Mem} (h : storebytes m b ofs bytes = some m')
    (ofs' : Z) (hout : ofs' < ofs ∨ ofs + (bytes.length : Z) ≤ ofs') :
    ZMap.get ofs' (PMap.get b m'.contents) = ZMap.get ofs' (PMap.get b m.contents) := by
  rw [storebytes_contents h, PMap.gss, setN_outside bytes ofs ofs' _ hout]

end Mem
end CC
