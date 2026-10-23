/-
  The heap resource algebra — Phase 7.2 of the separation-logic plan.

  A `Heap` is a *fragment* of a `Mem`: a partial map from (block, offset) to a
  permission and a byte.  Separating conjunction will be disjoint union of
  fragments, and `Agrees` is the erasure that connects a fragment back to a
  concrete CompCert memory.

  ## One permission per cell

  CompCert's `Mem.access` carries a `Cur` and a `Max` permission per byte, but
  every operation in `CCLib/common/Memory.lean` keeps them equal: `alloc` sets both,
  `uncheckedFree` zeroes both (its range branch ignores the `PermKind`),
  `store`/`storebytes` leave `access` untouched, and `dropPerm` sets both.  So
  `Cur = Max` is invariant for any program that does not call `dropPerm` mid-run —
  only `Genv.allocGlobals` does — and a cell can carry a single `Permission`.

  This is a *stated restriction*, not a theorem about CompCert: memories where
  `Cur < Max` are expressible in the model and are not described by any `Heap`.

  ## Unique ownership

  There are no fractional permissions: disjointness is disjointness of domains,
  so a byte has at most one owner.  For sequential code this is not a real
  limitation — a caller lends a buffer to a callee and gets it back in the
  postcondition — and it avoids needing a share algebra.

  ## Fragments do not describe all of memory

  `Agrees h m` constrains only the cells `h` owns.  Un-owned memory (other stack
  frames, globals nobody mentions) is simply not described.  That is what makes
  the frame rule fall out in Phase 7.4, and it means no leak-freedom is claimed.
-/
import CCLib.common.MemoryLemmas

namespace CC

/-- One byte of owned memory: its permission (`Cur` = `Max`) and its contents. -/
structure Cell where
  perm : Permission
  val : MemVal
  deriving DecidableEq, Repr

/-- A fragment of memory.  `none` means "not owned by this fragment". -/
def Heap : Type := Block → Z → Option Cell

namespace Heap

/-- The empty fragment, owning nothing. -/
def emp : Heap := fun _ _ => none

/-- The fragment owning exactly one byte. -/
def single (b : Block) (ofs : Z) (c : Cell) : Heap :=
  fun b' ofs' => if b' = b ∧ ofs' = ofs then some c else none

/-- Two fragments own disjoint sets of bytes. -/
def disjoint (h1 h2 : Heap) : Prop :=
  ∀ b ofs, h1 b ofs = none ∨ h2 b ofs = none

/-- Union of fragments.  Left-biased, so it is total; on *disjoint* fragments the
    bias is invisible and the operation is commutative (`union_comm`). -/
def union (h1 h2 : Heap) : Heap :=
  fun b ofs => match h1 b ofs with
               | some c => some c
               | none => h2 b ofs

/-! ## Extensionality -/

theorem ext {h1 h2 : Heap} (h : ∀ b ofs, h1 b ofs = h2 b ofs) : h1 = h2 := by
  funext b ofs; exact h b ofs

/-! ## Lookup -/

@[simp] theorem emp_apply (b : Block) (ofs : Z) : emp b ofs = none := rfl

@[simp] theorem single_same (b : Block) (ofs : Z) (c : Cell) :
    single b ofs c b ofs = some c := by simp [single]

theorem single_other (b : Block) (ofs : Z) (c : Cell) (b' : Block) (ofs' : Z)
    (h : ¬ (b' = b ∧ ofs' = ofs)) : single b ofs c b' ofs' = none := by
  simp [single, h]

@[simp] theorem union_apply (h1 h2 : Heap) (b : Block) (ofs : Z) :
    union h1 h2 b ofs = match h1 b ofs with | some c => some c | none => h2 b ofs := rfl

/-- Looking up in a union, resolved by which side owns the byte. -/
theorem union_of_left {h1 h2 : Heap} {b : Block} {ofs : Z} {c : Cell}
    (h : h1 b ofs = some c) : union h1 h2 b ofs = some c := by
  simp [union, h]

theorem union_of_right {h1 h2 : Heap} {b : Block} {ofs : Z}
    (h : h1 b ofs = none) : union h1 h2 b ofs = h2 b ofs := by
  simp [union, h]

/-- Dual of `union_of_right`: if the *right* side is empty here, the union is the
    left side. -/
theorem union_right_none {h1 h2 : Heap} {b : Block} {ofs : Z}
    (h : h2 b ofs = none) : union h1 h2 b ofs = h1 b ofs := by
  cases h1b : h1 b ofs <;> simp [union, h1b, h]

/-! ## The partial commutative monoid laws -/

@[simp] theorem union_emp (h : Heap) : union h emp = h := by
  refine ext (fun b ofs => ?_)
  cases hb : h b ofs <;> simp [union, hb]

@[simp] theorem emp_union (h : Heap) : union emp h = h := by
  refine ext (fun b ofs => ?_); rfl

/-- Associativity holds unconditionally, thanks to the left bias. -/
theorem union_assoc (h1 h2 h3 : Heap) :
    union (union h1 h2) h3 = union h1 (union h2 h3) := by
  refine ext (fun b ofs => ?_)
  cases h1b : h1 b ofs <;> cases h2b : h2 b ofs <;> simp [union, h1b, h2b]

theorem disjoint_comm {h1 h2 : Heap} (h : disjoint h1 h2) : disjoint h2 h1 :=
  fun b ofs => (h b ofs).symm

@[simp] theorem disjoint_emp_right (h : Heap) : disjoint h emp := fun _ _ => Or.inr rfl
@[simp] theorem disjoint_emp_left (h : Heap) : disjoint emp h := fun _ _ => Or.inl rfl

/-- On disjoint fragments, union is commutative. -/
theorem union_comm {h1 h2 : Heap} (hd : disjoint h1 h2) : union h1 h2 = union h2 h1 := by
  refine ext (fun b ofs => ?_)
  rcases hd b ofs with h | h <;> cases h1b : h1 b ofs <;> cases h2b : h2 b ofs <;>
    simp_all [union]

/-- Swap the first two summands of a right-nested union.  Needed whenever a rule
    lends the *second* of two owned fragments to an operation and the first has to
    join the frame (`memcpy` does exactly this with its destination). -/
theorem union_left_comm {h1 h2 h3 : Heap} (hd : disjoint h1 h2) :
    union h1 (union h2 h3) = union h2 (union h1 h3) := by
  rw [← union_assoc, ← union_assoc, union_comm hd]

theorem disjoint_union_left {h1 h2 h3 : Heap} :
    disjoint (union h1 h2) h3 ↔ disjoint h1 h3 ∧ disjoint h2 h3 := by
  constructor
  · intro h
    refine ⟨fun b ofs => ?_, fun b ofs => ?_⟩
    · rcases h b ofs with hu | h3n
      · cases h1b : h1 b ofs with
        | none => exact Or.inl rfl
        | some c => rw [union_of_left h1b] at hu; exact absurd hu (by simp)
      · exact Or.inr h3n
    · rcases h b ofs with hu | h3n
      · cases h1b : h1 b ofs with
        | none => rw [union_of_right h1b] at hu; exact Or.inl hu
        | some c =>
            cases h2b : h2 b ofs with
            | none => exact Or.inl rfl
            | some c2 => rw [union_of_left h1b] at hu; exact absurd hu (by simp)
      · exact Or.inr h3n
  · intro ⟨ha, hb⟩ b ofs
    rcases ha b ofs with h1n | h3n
    · rcases hb b ofs with h2n | h3n'
      · exact Or.inl (by rw [union_of_right h1n]; exact h2n)
      · exact Or.inr h3n'
    · exact Or.inr h3n

theorem disjoint_union_right {h1 h2 h3 : Heap} :
    disjoint h1 (union h2 h3) ↔ disjoint h1 h2 ∧ disjoint h1 h3 := by
  constructor
  · intro h
    exact ⟨disjoint_comm ((disjoint_union_left.mp (disjoint_comm h)).1),
           disjoint_comm ((disjoint_union_left.mp (disjoint_comm h)).2)⟩
  · intro ⟨ha, hb⟩
    exact disjoint_comm (disjoint_union_left.mpr ⟨disjoint_comm ha, disjoint_comm hb⟩)

/-- Cancellation: a fragment is determined by its union with a disjoint one. -/
theorem union_cancel {h1 h2 h : Heap} (hd1 : disjoint h1 h) (hd2 : disjoint h2 h)
    (heq : union h1 h = union h2 h) : h1 = h2 := by
  refine ext (fun b ofs => ?_)
  have h' := congrFun (congrFun heq b) ofs
  rcases hd1 b ofs with h1n | hn
  · rcases hd2 b ofs with h2n | hn2
    · rw [h1n, h2n]
    · rw [h1n]
      cases h2b : h2 b ofs with
      | none => rfl
      | some c => rw [union_of_left h2b, union_of_right h1n] at h'
                  rw [hn2] at h'; exact absurd h'.symm (by simp)
  · rw [union_right_none hn, union_right_none hn] at h'
    exact h'

end Heap

/-! ## Erasure onto a concrete memory -/

/-- `Agrees h m`: every byte the fragment `h` owns really is in `m`, with that
    permission (as both `Cur` and `Max`) and those contents.

    Nothing is said about bytes `h` does not own — see the header. -/
def Heap.Agrees (h : Heap) (m : Mem) : Prop :=
  ∀ b ofs c, h b ofs = some c →
      PMap.get b m.access ofs .Cur = some c.perm
    ∧ PMap.get b m.access ofs .Max = some c.perm
    ∧ ZMap.get ofs (PMap.get b m.contents) = c.val

namespace Heap

theorem Agrees_perm {h : Heap} {m : Mem} (hag : Agrees h m) {b : Block} {ofs : Z}
    {c : Cell} (hc : h b ofs = some c) (k : PermKind) :
    Mem.perm m b ofs k c.perm = true := by
  obtain ⟨hcur, hmax, _⟩ := hag b ofs c hc
  cases k with
  | Max => simp [Mem.perm, hmax, permOrder', permOrder]
  | Cur => simp [Mem.perm, hcur, permOrder', permOrder]

theorem Agrees_val {h : Heap} {m : Mem} (hag : Agrees h m) {b : Block} {ofs : Z}
    {c : Cell} (hc : h b ofs = some c) :
    ZMap.get ofs (PMap.get b m.contents) = c.val := (hag b ofs c hc).2.2

/-- An owned byte lives in an allocated block.  Follows from `Mem`'s own
    `nextblock_noaccess` invariant, so it needs no extra hypothesis. -/
theorem Agrees_validBlock {h : Heap} {m : Mem} (hag : Agrees h m) {b : Block} {ofs : Z}
    {c : Cell} (hc : h b ofs = some c) : b < m.nextblock := by
  obtain ⟨hcur, _, _⟩ := hag b ofs c hc
  by_cases hb : b < m.nextblock
  · exact hb
  · rw [m.nextblock_noaccess b ofs .Cur hb] at hcur
    exact absurd hcur (by simp)

/-! ## `Agrees` and union -/

theorem Agrees_union_left {h1 h2 : Heap} {m : Mem} (hag : Agrees (union h1 h2) m) :
    Agrees h1 m := fun b ofs c hc => hag b ofs c (union_of_left hc)

theorem Agrees_union_right {h1 h2 : Heap} {m : Mem} (hd : disjoint h1 h2)
    (hag : Agrees (union h1 h2) m) : Agrees h2 m := by
  intro b ofs c hc
  refine hag b ofs c ?_
  rcases hd b ofs with h1n | h2n
  · rw [union_of_right h1n]; exact hc
  · rw [h2n] at hc; exact absurd hc (by simp)

theorem Agrees_union {h1 h2 : Heap} {m : Mem} (hag1 : Agrees h1 m) (hag2 : Agrees h2 m) :
    Agrees (union h1 h2) m := by
  intro b ofs c hc
  cases h1b : h1 b ofs with
  | some c1 => rw [union_of_left h1b] at hc; injection hc with hc; subst hc
               exact hag1 b ofs c1 h1b
  | none => rw [union_of_right h1b] at hc; exact hag2 b ofs c hc

/-- Nobody owns anything in a *fresh* block: an owned byte lives in an allocated
    block, and `m.nextblock` is by definition not allocated. -/
theorem Agrees_fresh_none {h : Heap} {m : Mem} (hag : Agrees h m) (ofs : Z) :
    h m.nextblock ofs = none := by
  cases hc : h m.nextblock ofs with
  | none => rfl
  | some c =>
      exact absurd (Agrees_validBlock hag hc) (by simp [Positive.lt_iff])

/-! ## Owning a contiguous range

The bridge from single-byte ownership to CompCert's chunk-sized `load`/`store`,
and hence what Phase 7.3's `mapsto` will be defined over. -/

/-- `h` owns the `vl.length` bytes at `b + ofs`, each with permission `p`. -/
def ownsRange (h : Heap) (b : Block) (ofs : Z) (p : Permission) (vl : List MemVal) : Prop :=
  ∀ i : Nat, i < vl.length → h b (ofs + (i : Z)) = some ⟨p, vl[i]!⟩

theorem ownsRange_tail {h : Heap} {b : Block} {ofs : _root_.Int} {p : Permission}
    {v : MemVal} {vl : List MemVal} (ho : ownsRange h b ofs p (v :: vl)) :
    ownsRange h b (ofs + 1) p vl := by
  intro i hi
  have := ho (i + 1) (by simp only [List.length_cons]; omega)
  rw [show ofs + ((i + 1 : Nat) : _root_.Int) = (ofs + 1) + (i : _root_.Int) from by
    push_cast; omega] at this
  simpa using this

/-- A fragment that owns nothing in `[ofs, ofs+n)` owns nothing at any offset in
    that window — restated as the disjointness form the memory lemmas want. -/
theorem outside_of_unowned {h : Heap} {b : Block} {ofs : _root_.Int} {n : Nat}
    (hno : ∀ i : Nat, i < n → h b (ofs + (i : _root_.Int)) = none)
    {ofs' : _root_.Int} {c : Cell} (hc : h b ofs' = some c) :
    ofs' < ofs ∨ ofs + (n : _root_.Int) ≤ ofs' := by
  by_cases h1 : ofs ≤ ofs'
  · by_cases h2 : ofs' < ofs + (n : _root_.Int)
    · exfalso
      have hlt : (ofs' - ofs).toNat < n := by omega
      have hn := hno (ofs' - ofs).toNat hlt
      rw [show ofs + (((ofs' - ofs).toNat : Nat) : _root_.Int) = ofs' from by omega] at hn
      rw [hn] at hc; exact absurd hc (by simp)
    · exact Or.inr (by omega)
  · exact Or.inl (by omega)

/-- Reading an owned range out of the concrete memory gives exactly the owned
    bytes.  With `Agrees_rangePerm` this is what makes `Mem.load` succeed. -/
theorem Agrees_getN {h : Heap} {m : Mem} {b : Block} {p : Permission}
    (hag : Agrees h m) : ∀ (vl : List MemVal) (ofs : _root_.Int),
      ownsRange h b ofs p vl → Mem.getN vl.length ofs (PMap.get b m.contents) = vl := by
  intro vl
  induction vl with
  | nil => intro _ _; rfl
  | cons v vl' ih =>
      intro ofs ho
      have hhead : h b ofs = some ⟨p, v⟩ := by
        have := ho 0 (by simp)
        simpa using this
      show ZMap.get ofs (PMap.get b m.contents)
             :: Mem.getN vl'.length (ofs + 1) (PMap.get b m.contents) = v :: vl'
      rw [Agrees_val hag hhead, ih (ofs + 1) (ownsRange_tail ho)]

/-- An owned range carries its permission throughout, as a `rangePerm`. -/
theorem Agrees_rangePerm {h : Heap} {m : Mem} {b : Block} {p : Permission}
    {vl : List MemVal} {ofs : _root_.Int} (hag : Agrees h m)
    (ho : ownsRange h b ofs p vl) (k : PermKind) :
    Mem.rangePerm m b ofs (ofs + (vl.length : _root_.Int)) k p = true := by
  refine Mem.rangePerm_intro m b ofs (ofs + (vl.length : _root_.Int)) k p (fun o h1 h2 => ?_)
  have hlt : (o - ofs).toNat < vl.length := by omega
  have hc := ho (o - ofs).toNat hlt
  rw [show ofs + (((o - ofs).toNat : Nat) : _root_.Int) = o from by omega] at hc
  exact Agrees_perm hag hc k

/-- **Disjoint fragments occupy disjoint address ranges.**  Two `∗`-separated
    equal-length windows in the same block cannot overlap, which is precisely the
    non-overlap side condition `Events.ExtcallMemcpySem` demands.  So a caller
    that owns source and destination separately never has to *prove* non-overlap
    — `∗` already said it.

    (At `n = 0` the conclusion is a tautology, which is why no positivity
    hypothesis is needed.) -/
theorem disjoint_ranges_nonoverlap {h1 h2 : Heap} {b : Block}
    {o1 o2 : _root_.Int} {n : Nat} {p1 p2 : Permission} {vl1 vl2 : List MemVal}
    (hd : disjoint h1 h2)
    (hl1 : vl1.length = n) (hl2 : vl2.length = n)
    (ho1 : ownsRange h1 b o1 p1 vl1) (ho2 : ownsRange h2 b o2 p2 vl2) :
    o1 + (n : _root_.Int) ≤ o2 ∨ o2 + (n : _root_.Int) ≤ o1 := by
  by_cases hle : o1 ≤ o2
  · by_cases hlt : o2 < o1 + (n : _root_.Int)
    · -- the windows overlap at `o2`, which both fragments would then own
      exfalso
      have hk : (o2 - o1).toNat < n := by omega
      have e1 : h1 b o2 = some ⟨p1, vl1[(o2 - o1).toNat]!⟩ := by
        have h := ho1 (o2 - o1).toNat (by rw [hl1]; exact hk)
        rwa [show o1 + (((o2 - o1).toNat : Nat) : _root_.Int) = o2 from by omega] at h
      have e2 : h2 b o2 = some ⟨p2, vl2[0]!⟩ := by
        have h := ho2 0 (by rw [hl2]; omega)
        simpa using h
      rcases hd b o2 with hn | hn
      · rw [e1] at hn; exact absurd hn (by simp)
      · rw [e2] at hn; exact absurd hn (by simp)
    · exact Or.inl (by omega)
  · by_cases hlt : o1 < o2 + (n : _root_.Int)
    · exfalso
      have hk : (o1 - o2).toNat < n := by omega
      have e1 : h1 b o1 = some ⟨p1, vl1[0]!⟩ := by
        have h := ho1 0 (by rw [hl1]; omega)
        simpa using h
      have e2 : h2 b o1 = some ⟨p2, vl2[(o1 - o2).toNat]!⟩ := by
        have h := ho2 (o1 - o2).toNat (by rw [hl2]; exact hk)
        rwa [show o2 + (((o1 - o2).toNat : Nat) : _root_.Int) = o1 from by omega] at h
      rcases hd b o1 with hn | hn
      · rw [e1] at hn; exact absurd hn (by simp)
      · rw [e2] at hn; exact absurd hn (by simp)
    · exact Or.inr (by omega)

/-! ## `Agrees` under the memory operations

These are what let Phase 7.4 thread a frame through a step: the frame keeps
agreeing, so its bytes are provably unchanged. -/

/-- A store inside a region the fragment does not own leaves it agreeing. -/
theorem Agrees_store_frame {hf : Heap} {m m' : Mem} {chunk : Chunk} {b : Block}
    {ofs : _root_.Int} {v : Val} (hst : Mem.store chunk m b ofs v = some m')
    (hag : Agrees hf m)
    (hno : ∀ i : Nat, i < sizeChunkNat chunk → hf b (ofs + (i : _root_.Int)) = none) :
    Agrees hf m' := by
  intro b' ofs' c hc
  obtain ⟨hcur, hmax, hval⟩ := hag b' ofs' c hc
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.store_access hst]; exact hcur
  · rw [Mem.store_access hst]; exact hmax
  · rw [Mem.store_contents hst]
    by_cases hb : b' = b
    · subst hb
      rw [PMap.gss]
      rw [Mem.setN_outside (encodeVal chunk v) ofs ofs' _ ?_]
      · exact hval
      · rw [length_encodeVal]
        exact outside_of_unowned hno hc
    · rw [PMap.gso _ _ _ _ (fun heq => hb heq.symm)]; exact hval

/-- The `storebytes` analogue: a fragment owning nothing in the written range
    survives.  This is what `memcpy` needs — its semantics is stated over
    `loadbytes`/`storebytes`, not `load`/`store`. -/
theorem Agrees_storebytes_frame {hf : Heap} {m m' : Mem} {b : Block}
    {ofs : _root_.Int} {bytes : List MemVal}
    (hst : Mem.storebytes m b ofs bytes = some m')
    (hag : Agrees hf m)
    (hno : ∀ i : Nat, i < bytes.length → hf b (ofs + (i : _root_.Int)) = none) :
    Agrees hf m' := by
  intro b' ofs' c hc
  obtain ⟨hcur, hmax, hval⟩ := hag b' ofs' c hc
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.storebytes_access hst]; exact hcur
  · rw [Mem.storebytes_access hst]; exact hmax
  · rw [Mem.storebytes_contents hst]
    by_cases hb : b' = b
    · subst hb
      rw [PMap.gss, Mem.setN_outside bytes ofs ofs' _ (outside_of_unowned hno hc)]
      exact hval
    · rw [PMap.gso _ _ _ _ (fun heq => hb heq.symm)]; exact hval

/-- Allocation preserves every fragment: an owned byte is in an already-valid
    block, and `alloc` only touches the fresh one. -/
theorem Agrees_alloc {h : Heap} {m : Mem} {lo hi : Z} (hag : Agrees h m) :
    Agrees h (Mem.alloc m lo hi).1 := by
  intro b ofs c hc
  have hvb : b < m.nextblock := Agrees_validBlock hag hc
  have hbne : b ≠ m.nextblock := by
    intro heq; rw [heq] at hvb; exact absurd hvb (by simp [Positive.lt_iff])
  obtain ⟨hcur, hmax, hval⟩ := hag b ofs c hc
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.alloc_access, PMap.gso _ _ _ _ (Ne.symm hbne)]; exact hcur
  · rw [Mem.alloc_access, PMap.gso _ _ _ _ (Ne.symm hbne)]; exact hmax
  · rw [Mem.alloc_contents, PMap.gso _ _ _ _ (Ne.symm hbne)]; exact hval

/-- Freeing a range the fragment does not own leaves it agreeing.  Note `contents`
    survive a free — `uncheckedFree` only clears permissions. -/
theorem Agrees_free_frame {h : Heap} {m : Mem} {b : Block} {lo hi : _root_.Int}
    (hag : Agrees h m)
    (hno : ∀ ofs : _root_.Int, lo ≤ ofs → ofs < hi → h b ofs = none) :
    Agrees h (Mem.uncheckedFree m b lo hi) := by
  intro b' ofs' c hc
  obtain ⟨hcur, hmax, hval⟩ := hag b' ofs' c hc
  have hacc : PMap.get b' (Mem.uncheckedFree m b lo hi).access ofs'
              = PMap.get b' m.access ofs' := by
    by_cases hb : b' = b
    · subst hb
      have hout : ¬ (lo ≤ ofs' ∧ ofs' < hi) := by
        intro ⟨h1, h2⟩
        rw [hno ofs' h1 h2] at hc; exact absurd hc (by simp)
      funext k
      simp [Mem.uncheckedFree, PMap.gss, hout]
    · simp [Mem.uncheckedFree, PMap.gso _ _ _ _ (fun heq => hb heq.symm)]
  exact ⟨by rw [hacc]; exact hcur, by rw [hacc]; exact hmax, hval⟩

end Heap
end CC
