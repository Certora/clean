/-
  **Phase 9, Wave B — generic aggregate predicates: arrays with split/join.**

  Until this file, the logic could *read* an array element (`arrayU32_load`,
  `arrayU8_load`) but could not *write* one: there was no way to take an array
  apart into "element `i`" ∗ "everything else" and put it back together with the
  element changed.  trees.c does `s->dyn_ltree[k].Freq++` constantly, so this was
  the single blocker for all of zlib's data-structure code.

  Design:

  * `arrayFrom elt lo n` is the index-structural core: `elt lo ∗ … ∗ elt (lo+n-1)`,
    where each `elt i : HProp` already knows its own absolute offset.  Keeping the
    offsets *inside* the element closure means every lemma about `arrayFrom` is
    pure index arithmetic — no `stride * i` terms in the inductions.
  * `arrayOf elt stride ofs n` lays `elt i (ofs + stride*i)` out every `stride`
    bytes.  Generic over the element predicate *and* the stride, so arrays of
    structs and 2-D arrays come out by nesting.
  * **`arrayOf_split` is an equality**, so the same lemma joins; and
    **`arrayOf_update`** is the write pattern — the array with element `i`
    replaced, its rest stated at the *old* elements, which is exactly what a
    store through `triple_assign` leaves in hand.
  * `arrayU16` (`bl_count`, and every `ct_data` member) as the first instance,
    with load/split/update; `arrayU8`/`arrayU32` are proved *equal* to their
    `arrayOf` forms, so they inherit split/update without touching their
    existing definitions or the proofs built on them.
  * `anyBytes` (a run of owned bytes with unknown contents) and `unionAt`
    (a union owning its **whole** footprint, not just the active member) —
    Phase 9 Step 3.

  Everything is footprint-checked (`_none`) and satisfiability-checked
  (`_satisfiable`): a predicate nothing can satisfy is worse than no predicate.

  **`CC.Z` note, hardened.**  Offsets and strides below are declared at
  `_root_.Int`, not at the (definitionally equal) `Z` alias: a goal whose
  arithmetic is *elaborated at `Z`* is opaque to `omega` — not just `Z`-typed
  hypotheses, as the standing note said, but goals too (measured on
  `(ofs + 1) + 1 * ↑j = ofs + 1 * (↑j + 1)`, which `omega` refuses with `ofs : Z`
  and proves instantly with `ofs : _root_.Int`).  Since `Z := _root_.Int` is an
  abbrev, every `Z`-typed call site still unifies.
-/
import CCLib.logic.HoareLong

namespace CC
open HProp

/-! ## `arrayFrom` — the index-structural core -/

/-- `elt lo ∗ elt (lo+1) ∗ … ∗ elt (lo+n-1)`.  Each element carries its own
    absolute offset; `arrayFrom` only supplies the index. -/
def arrayFrom (elt : Nat → HProp) : Nat → Nat → HProp
  | _, 0 => emp
  | lo, n + 1 => elt lo ∗ arrayFrom elt (lo + 1) n

/-- An `arrayFrom` depends only on the elements it actually uses. -/
theorem arrayFrom_congr {elt elt' : Nat → HProp} :
    ∀ (n lo : Nat), (∀ j, lo ≤ j → j < lo + n → elt j = elt' j) →
      arrayFrom elt lo n = arrayFrom elt' lo n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ k ih =>
      intro lo hj
      show elt lo ∗ arrayFrom elt (lo + 1) k = elt' lo ∗ arrayFrom elt' (lo + 1) k
      rw [hj lo (Nat.le_refl _) (by omega),
          ih (lo + 1) (fun j h1 h2 => hj j (by omega) (by omega))]

/-- Reindexing: starting `d` later is the same as shifting the element function. -/
theorem arrayFrom_reindex (elt : Nat → HProp) (d : Nat) :
    ∀ (n lo : Nat), arrayFrom elt (lo + d) n = arrayFrom (fun i => elt (i + d)) lo n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
      intro lo
      show elt (lo + d) ∗ arrayFrom elt (lo + d + 1) k
        = elt (lo + d) ∗ arrayFrom (fun i => elt (i + d)) (lo + 1) k
      rw [show lo + d + 1 = (lo + 1) + d from by omega, ih (lo + 1)]

/-- Concatenation, as an equality. -/
theorem arrayFrom_append (elt : Nat → HProp) :
    ∀ (a lo b : Nat),
      arrayFrom elt lo (a + b) = arrayFrom elt lo a ∗ arrayFrom elt (lo + a) b := by
  intro a
  induction a with
  | zero =>
      intro lo b
      show arrayFrom elt lo (0 + b) = arrayFrom elt lo 0 ∗ arrayFrom elt (lo + 0) b
      rw [Nat.zero_add, Nat.add_zero, show arrayFrom elt lo 0 = emp from rfl, emp_sep_eq]
  | succ k ih =>
      intro lo b
      have h1 : (k + 1) + b = (k + b) + 1 := by omega
      rw [h1]
      show elt lo ∗ arrayFrom elt (lo + 1) (k + b)
        = (elt lo ∗ arrayFrom elt (lo + 1) k) ∗ arrayFrom elt (lo + (k + 1)) b
      rw [ih (lo + 1) b, sep_assoc_eq, show lo + 1 + k = lo + (k + 1) from by omega]

/-- **Split at index `i`** — an equality, so the same lemma joins.  The element
    comes out in front; the prefix and suffix stay behind as the frame. -/
theorem arrayFrom_split (elt : Nat → HProp) (lo n i : Nat) (hi : i < n) :
    arrayFrom elt lo n
      = elt (lo + i)
          ∗ (arrayFrom elt lo i ∗ arrayFrom elt (lo + i + 1) (n - i - 1)) := by
  have hn : n = i + (1 + (n - i - 1)) := by omega
  conv => lhs; rw [hn]
  rw [arrayFrom_append elt i lo (1 + (n - i - 1)), Nat.add_comm 1 (n - i - 1)]
  show arrayFrom elt lo i ∗ (elt (lo + i) ∗ arrayFrom elt (lo + i + 1) (n - i - 1)) = _
  rw [sep_left_comm_eq]

/-! ## `arrayOf` — base + stride -/

/-- `arrayOf elt stride ofs n`: elements `0 … n-1`, where `elt i off` describes
    the `i`-th element at absolute byte offset `off`, laid out every `stride`
    bytes starting at `ofs`.  Arrays of structs = a compound `elt`; 2-D arrays =
    a nested `arrayOf`. -/
def arrayOf (elt : Nat → _root_.Int → HProp) (stride ofs : _root_.Int) (n : Nat) : HProp :=
  arrayFrom (fun i => elt i (ofs + stride * (i : _root_.Int))) 0 n

/-- Everything but element `i` — the frame a read or write of one element leaves. -/
def arrayOfRest (elt : Nat → _root_.Int → HProp) (stride ofs : _root_.Int)
    (n i : Nat) : HProp :=
  arrayFrom (fun j => elt j (ofs + stride * (j : _root_.Int))) 0 i
    ∗ arrayFrom (fun j => elt j (ofs + stride * (j : _root_.Int))) (i + 1) (n - i - 1)

/-- **Extract element `i`.**  An equality: read right-to-left, it is the join. -/
theorem arrayOf_split (elt : Nat → _root_.Int → HProp) (stride ofs : _root_.Int)
    (n i : Nat) (hi : i < n) :
    arrayOf elt stride ofs n
      = elt i (ofs + stride * (i : _root_.Int)) ∗ arrayOfRest elt stride ofs n i := by
  have h := arrayFrom_split (fun j => elt j (ofs + stride * (j : _root_.Int))) 0 n i hi
  simpa [arrayOf, arrayOfRest, Nat.zero_add] using h

/-- An `arrayOf` depends only on the element predicates it uses. -/
theorem arrayOf_congr {elt elt' : Nat → _root_.Int → HProp} (stride ofs : _root_.Int)
    (n : Nat) (h : ∀ j, j < n → elt j = elt' j) :
    arrayOf elt stride ofs n = arrayOf elt' stride ofs n :=
  arrayFrom_congr n 0 (fun j _ hj => congrFun (h j (by omega)) _)

/-- **The write pattern.**  After a store to element `i`, the fragment in hand is
    `elt' i` at its offset ∗ the old rest; this rebuilds the array at the updated
    element function.  `elt'` must agree with `elt` off `i` — for a pointwise
    update `fun j => if j = i then … else elt j` that is `simp`. -/
theorem arrayOf_update (elt elt' : Nat → _root_.Int → HProp) (stride ofs : _root_.Int)
    (n i : Nat) (hi : i < n) (hagree : ∀ j, j < n → j ≠ i → elt' j = elt j) :
    arrayOf elt' stride ofs n
      = elt' i (ofs + stride * (i : _root_.Int)) ∗ arrayOfRest elt stride ofs n i := by
  rw [arrayOf_split elt' stride ofs n i hi]
  unfold arrayOfRest
  rw [arrayFrom_congr (elt := fun j => elt' j (ofs + stride * (j : _root_.Int)))
        i 0 (fun j _ hj => congrFun (hagree j (by omega) (by omega)) _),
      arrayFrom_congr (elt := fun j => elt' j (ofs + stride * (j : _root_.Int)))
        (n - i - 1) (i + 1) (fun j hj1 hj2 => congrFun (hagree j (by omega) (by omega)) _)]

/-! ## Footprint and satisfiability, generically

Stated over a per-index *window function* `win`, so that the inductions never
mention `stride * i` products — the instances discharge `win j = ofs + stride*j`
with one `Int.mul_add` rewrite. -/

/-- If every element owns only bytes of block `b` inside its own window
    `[win j, win j + esz)`, the array owns nothing outside all the windows. -/
theorem arrayFrom_none {b : Block} {win : Nat → _root_.Int} {esz : _root_.Int}
    {elt : Nat → HProp}
    (helt : ∀ j h', elt j h' → ∀ b' o',
        (b' ≠ b ∨ o' < win j ∨ win j + esz ≤ o') → h' b' o' = none) :
    ∀ (n lo : Nat) (h : Heap), arrayFrom elt lo n h →
      ∀ b' o',
        (∀ j, lo ≤ j → j < lo + n → (b' ≠ b ∨ o' < win j ∨ win j + esz ≤ o')) →
        h b' o' = none := by
  intro n
  induction n with
  | zero => intro _ h hh _ _ _; rw [show h = Heap.emp from hh]; rfl
  | succ k ih =>
      intro lo h hh b' o' hout
      obtain ⟨h1, h2, _, heq, hhead, htail⟩ := hh
      subst heq
      have e1 : h1 b' o' = none :=
        helt lo h1 hhead b' o' (hout lo (Nat.le_refl _) (by omega))
      have e2 : h2 b' o' = none :=
        ih (lo + 1) h2 htail b' o' (fun j hj1 hj2 => hout j (by omega) (by omega))
      simp [Heap.union, e1, e2]

/-- Windows in increasing order stay apart: `win j + esz ≤ win (j + d + 1)`. -/
private theorem win_chain {win : Nat → _root_.Int} {esz : _root_.Int}
    (hmono : ∀ j, win j + esz ≤ win (j + 1)) (hesz : 0 ≤ esz) :
    ∀ (d j : Nat), win j + esz ≤ win (j + (d + 1)) := by
  intro d
  induction d with
  | zero => intro j; simpa using hmono j
  | succ e ih =>
      intro j
      have h1 := ih j
      have h2 := hmono (j + (e + 1))
      rw [show j + (e + 1 + 1) = (j + (e + 1)) + 1 from by omega]
      omega

/-- An `arrayFrom` of separated, individually-satisfiable, footprint-bounded
    elements is satisfiable. -/
theorem arrayFrom_satisfiable {b : Block} {win : Nat → _root_.Int} {esz : _root_.Int}
    {elt : Nat → HProp}
    (helt : ∀ j h', elt j h' → ∀ b' o',
        (b' ≠ b ∨ o' < win j ∨ win j + esz ≤ o') → h' b' o' = none)
    (hmono : ∀ j, win j + esz ≤ win (j + 1)) (hesz : 0 ≤ esz)
    (hsat : ∀ j, ∃ h', elt j h') :
    ∀ (n lo : Nat), ∃ h, arrayFrom elt lo n h := by
  intro n
  induction n with
  | zero => intro _; exact ⟨Heap.emp, rfl⟩
  | succ k ih =>
      intro lo
      obtain ⟨h2, hh2⟩ := ih (lo + 1)
      obtain ⟨h1, hh1⟩ := hsat lo
      refine ⟨Heap.union h1 h2, h1, h2, ?_, rfl, hh1, hh2⟩
      intro b' o'
      by_cases hcase : h1 b' o' = none
      · exact Or.inl hcase
      · -- h1 owns (b', o'), so o' sits inside window `lo`; every later window
        -- starts past it, so the tail owns nothing there.  No case on the block
        -- is needed: the window disjuncts carry the argument.
        refine Or.inr (arrayFrom_none helt k (lo + 1) h2 hh2 b' o' ?_)
        intro j hj1 hj2
        have hlt : o' < win lo + esz := by
          by_cases hx : o' < win lo + esz
          · exact hx
          · exact absurd (helt lo h1 hh1 b' o' (Or.inr (Or.inr (Int.not_lt.mp hx)))) hcase
        have hchain : win lo + esz ≤ win j := by
          have hd : j = lo + ((j - lo - 1) + 1) := by omega
          rw [hd]; exact win_chain hmono hesz (j - lo - 1) lo
        exact Or.inr (Or.inl (Int.lt_of_lt_of_le hlt hchain))

/-- The one fact connecting consecutive windows at stride layout:
    `ofs + stride*j + esz ≤ ofs + stride*(j+1)` when `esz ≤ stride`. -/
private theorem stride_window_mono {stride ofs esz : _root_.Int}
    (hstr : esz ≤ stride) (j : Nat) :
    (ofs + stride * (j : _root_.Int)) + esz
      ≤ ofs + stride * (((j + 1 : Nat)) : _root_.Int) := by
  have hc : (((j + 1 : Nat)) : _root_.Int) = (j : _root_.Int) + 1 := by push_cast; omega
  rw [hc, Int.mul_add, Int.mul_one]
  omega

/-- `arrayOf` is satisfiable whenever each element is satisfiable at its own
    offset, owns at most `esz` bytes there, and `esz ≤ stride`. -/
theorem arrayOf_satisfiable {b : Block} {esz : _root_.Int}
    (elt : Nat → _root_.Int → HProp) (stride ofs : _root_.Int) (n : Nat)
    (helt : ∀ j off h', elt j off h' → ∀ b' o',
        (b' ≠ b ∨ o' < off ∨ off + esz ≤ o') → h' b' o' = none)
    (hesz : 0 ≤ esz) (hstr : esz ≤ stride)
    (hsat : ∀ j, ∃ h', elt j (ofs + stride * (j : _root_.Int)) h') :
    ∃ h, arrayOf elt stride ofs n h :=
  arrayFrom_satisfiable (win := fun j => ofs + stride * (j : _root_.Int))
    (fun j h' hj => helt j _ h' hj)
    (fun j => stride_window_mono hstr j) hesz hsat n 0

/-- `arrayOf` owns nothing outside `b × [ofs, ofs + stride*n)`, provided each
    element owns at most `esz ≤ stride` bytes at its own offset. -/
theorem arrayOf_none {b : Block} {esz : _root_.Int}
    {elt : Nat → _root_.Int → HProp} {stride ofs : _root_.Int} {n : Nat}
    (helt : ∀ j off h', elt j off h' → ∀ b' o',
        (b' ≠ b ∨ o' < off ∨ off + esz ≤ o') → h' b' o' = none)
    (hesz : 0 ≤ esz) (hstr : esz ≤ stride)
    {h : Heap} (hh : arrayOf elt stride ofs n h) :
    ∀ b' o',
      (b' ≠ b ∨ o' < ofs ∨ ofs + stride * (n : _root_.Int) ≤ o') → h b' o' = none := by
  intro b' o' hout
  refine arrayFrom_none (win := fun j => ofs + stride * (j : _root_.Int))
    (fun j h' hj => helt j _ h' hj) n 0 h hh b' o' ?_
  intro j _ hj2
  show b' ≠ b ∨ o' < ofs + stride * (j : _root_.Int)
       ∨ (ofs + stride * (j : _root_.Int)) + esz ≤ o'
  rcases hout with hb | hlt | hge
  · exact Or.inl hb
  · refine Or.inr (Or.inl ?_)
    have hnn : 0 ≤ stride * (j : _root_.Int) := Int.mul_nonneg (by omega) (by omega)
    omega
  · refine Or.inr (Or.inr ?_)
    have hstep := stride_window_mono (ofs := ofs) (esz := esz) hstr j
    have hle : (((j + 1 : Nat)) : _root_.Int) ≤ (n : _root_.Int) := by push_cast; omega
    have hmul : stride * (((j + 1 : Nat)) : _root_.Int) ≤ stride * (n : _root_.Int) :=
      Int.mul_le_mul_of_nonneg_left hle (by omega)
    omega

/-! ## `arrayU16` — the first instance

`bl_count[16]` is `ushort[16]`, and both members of every `ct_data` union are
`ushort`, so 16-bit arrays are the commonest array shape in zlib's tables.
Elements are `Nat`s below 65536, following `arrayU8`'s convention: that is what
makes the load lemma state `f i` and not `zero_ext 16 (f i)`. -/

/-- Zero-extending a value already below 2¹⁶ does nothing. -/
theorem zero_ext16_repr (c : Nat) (h : c < 65536) :
    Integers.Int.zero_ext 16 (Integers.Int.repr ((c : _root_.Int)))
      = Integers.Int.repr ((c : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int.zero_ext, Integers.MI.zero_ext, ge_iff_le,
             show ¬ (32 ≤ 16) from by omega, if_false]
  rw [BitVec.toNat_and, u32_toNat_repr]
  show _ &&& (BitVec.allOnes 32 >>> (32 - 16)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_allOnes]
  rw [Nat.mod_eq_of_lt (by omega : c < 4294967296),
      show ((2 ^ 32 - 1 : Nat) >>> (32 - 16)) = 2 ^ 16 - 1 from by rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : c < 2 ^ 16)]

/-- A `mapsto` exists at any aligned offset. -/
theorem mapsto_exists (chunk : Chunk) (p : Permission) (b : Block)
    (ofs : _root_.Int) (v : Val) (halign : ofs % alignChunk chunk = 0) :
    ∃ h, mapsto chunk p b ofs v h := by
  obtain ⟨h, hm⟩ := bytesPtsTo_exists b p (encodeVal chunk v) ofs
  exact ⟨h, pure_sep_intro halign hm⟩

/-- The element predicate of `arrayU16`. -/
def u16elt (p : Permission) (b : Block) (f : Nat → Nat) : Nat → _root_.Int → HProp :=
  fun i off => mapsto .Mint16unsigned p b off (.Vint (Integers.Int.repr ((f i : Nat))))

/-- `n` owned `unsigned short`s at `b + ofs`, holding `f 0 … f (n-1)`. -/
def arrayU16 (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) : HProp :=
  arrayOf (u16elt p b f) 2 ofs n

/-- The footprint bound `arrayOf_none`/`_satisfiable` want, for `u16elt`. -/
theorem u16elt_none (p : Permission) (b : Block) (f : Nat → Nat) :
    ∀ j off h', u16elt p b f j off h' → ∀ b' o',
      (b' ≠ b ∨ o' < off ∨ off + (2 : _root_.Int) ≤ o') → h' b' o' = none := by
  intro j off h' hm b' o' hout
  refine mapsto_none hm b' o' ?_
  rcases hout with hb | hlt | hge
  · exact Or.inl hb
  · exact Or.inr (Or.inl hlt)
  · refine Or.inr (Or.inr ?_)
    show off + ((sizeChunkNat .Mint16unsigned : Nat) : _root_.Int) ≤ o'
    have hsz : ((sizeChunkNat .Mint16unsigned : Nat) : _root_.Int) = 2 := rfl
    omega

/-- `arrayU16` is satisfiable at any even base. -/
theorem arrayU16_satisfiable (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) (halign : ofs % 2 = 0) :
    ∃ h, arrayU16 p b ofs n f h := by
  refine arrayOf_satisfiable (esz := 2) (u16elt p b f) 2 ofs n
    (u16elt_none p b f) (by omega) (by omega) ?_
  intro j
  refine mapsto_exists .Mint16unsigned p b _ _ ?_
  show (ofs + 2 * ((j : Nat) : _root_.Int)) % alignChunk .Mint16unsigned = 0
  have ha : alignChunk .Mint16unsigned = 2 := rfl
  rw [ha]
  omega

/-- `arrayU16` owns exactly its `2 * n` bytes. -/
theorem arrayU16_none (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) (h : Heap) (hh : arrayU16 p b ofs n f h) :
    ∀ b' o', (b' ≠ b ∨ o' < ofs ∨ ofs + 2 * (n : _root_.Int) ≤ o') → h b' o' = none :=
  arrayOf_none (esz := 2) (u16elt_none p b f) (by omega) (by omega) hh

/-- **Split**, packaged: the element in front as a bare `mapsto`, the rest behind. -/
theorem arrayU16_split (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) (i : Nat) (hi : i < n) :
    arrayU16 p b ofs n f
      = mapsto .Mint16unsigned p b (ofs + 2 * (i : _root_.Int))
          (.Vint (Integers.Int.repr ((f i : Nat))))
        ∗ arrayOfRest (u16elt p b f) 2 ofs n i :=
  arrayOf_split (u16elt p b f) 2 ofs n i hi

/-- **Join after a write**: the updated element in front, the *old* rest behind —
    exactly the fragment a store leaves — equals the array at the updated
    element function. -/
theorem arrayU16_update (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) (i : Nat) (v : Nat) (hi : i < n) :
    arrayU16 p b ofs n (fun j => if j = i then v else f j)
      = mapsto .Mint16unsigned p b (ofs + 2 * (i : _root_.Int))
          (.Vint (Integers.Int.repr ((v : Nat))))
        ∗ arrayOfRest (u16elt p b f) 2 ofs n i := by
  have h := arrayOf_update (u16elt p b f)
    (u16elt p b (fun j => if j = i then v else f j)) 2 ofs n i hi
    (fun j _ hne => by funext off; simp [u16elt, hne])
  rw [arrayU16, h]
  simp [u16elt]

/-- **Append one element at the end** — an equality, so it also peels the last
    one off.  The dual of `arrayOf_split`, which extracts from the middle. -/
theorem arrayOf_snoc (elt : Nat → _root_.Int → HProp) (stride ofs : _root_.Int)
    (n : Nat) :
    arrayOf elt stride ofs (n + 1)
      = arrayOf elt stride ofs n ∗ elt n (ofs + stride * (n : _root_.Int)) := by
  show arrayFrom (fun i => elt i (ofs + stride * (i : _root_.Int))) 0 (n + 1) = _
  rw [arrayFrom_append (fun i => elt i (ofs + stride * (i : _root_.Int))) n 0 1,
      Nat.zero_add]
  show arrayOf elt stride ofs n
        ∗ (elt n (ofs + stride * (n : _root_.Int))
           ∗ arrayFrom (fun i => elt i (ofs + stride * (i : _root_.Int))) (n + 1) 0) = _
  rw [show arrayFrom (fun i => elt i (ofs + stride * (i : _root_.Int))) (n + 1) 0
         = emp from rfl, sep_emp_eq]

/-- **Reading element `i`.**  Owning the array is enough; the rest is absorbed
    into `mapsto_load`'s frame. -/
theorem arrayU16_load (p : Permission) (b : Block)
    (hpr : permOrder p .Readable = true) (n : Nat) (f : Nat → Nat) (i : Nat)
    (hi : i < n) (hb : ∀ j, f j < 65536) (ofs : _root_.Int) (h : Heap) (m : Mem)
    (harr : arrayU16 p b ofs n f h) (hag : Heap.Agrees h m) :
    Mem.load .Mint16unsigned m b (ofs + 2 * (i : _root_.Int))
      = some (.Vint (Integers.Int.repr ((f i : Nat)))) := by
  rw [arrayU16_split p b ofs n f i hi] at harr
  obtain ⟨h1, h2, _, heq, hel, _⟩ := harr
  subst heq
  have hl := mapsto_load hpr hel (Heap.Agrees_union_left hag)
  simpa [Val.loadResult, zero_ext16_repr (f i) (hb i)] using hl

/-- **Grow the initialized prefix by one.**  The zeroing-loop invariant in
    `inflate_table` (inftrees.c:116-117) is "initialized prefix ∗ undefined
    suffix", and this is the step that moves one cell across the boundary.

    The element function is oriented as `arrayU16_update`'s is
    (`if j = n then v else f j`) so client rewrites compose without `funext`. -/
theorem arrayU16_snoc (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) (v : Nat) :
    arrayU16 p b ofs n f
      ∗ mapsto .Mint16unsigned p b (ofs + 2 * (n : _root_.Int))
          (.Vint (Integers.Int.repr ((v : Nat))))
      = arrayU16 p b ofs (n + 1) (fun j => if j = n then v else f j) := by
  show _ = arrayOf (u16elt p b (fun j => if j = n then v else f j)) 2 ofs (n + 1)
  rw [arrayOf_snoc,
      arrayOf_congr (elt' := u16elt p b f) 2 ofs n
        (fun j hj => by funext off; simp [u16elt, show j ≠ n from by omega])]
  simp [u16elt, arrayU16]

/-! ### Indexing a `u16` array

`eval_index_lvalue` (`CCLib.logic.SepHoare`) already derives the address at any element
type; this adds the load.  Every indexed array in `inflate_table` — the `lens[]`
and `work[]` parameters, the `count[16]`/`offs[16]` locals — is `unsigned short`,
and none of them could be read before. -/

/-- `sizeof cenv tushort = 2`, in any composite environment: `tushort` is a base
    type, so this needs no `decide` against a particular program. -/
theorem sizeof_tushort (cenv : CompositeEnv) : sizeof cenv tushort = 2 := by
  simp [sizeof, tushort]

/-- The `haddr` obligation of `eval_index_u16`, discharged.  Clients supply the
    index bound and the no-wrap bound; the stride is settled here. -/
theorem u16Ofs_unsigned (cenv : CompositeEnv) (si : Signedness)
    (ofs0 : Integers.Ptrofs) (i : Nat)
    (hi : (i : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 2 * (i : _root_.Int)
             < 18446744073709551616) :
    Integers.Ptrofs.unsigned
        (Sep.idxOfs cenv tushort si ofs0 (Integers.Int.repr ((i : _root_.Int))))
      = Integers.Ptrofs.unsigned ofs0 + 2 * (i : _root_.Int) := by
  -- the only gap is the `Nat`-to-`Int` cast on the stride; `omega` is blind to
  -- `Ptrofs.unsigned`, which sits at `CC.Z`, so close it by rewriting the cast
  -- rather than by arithmetic
  have h2 : ((2 : Nat) : _root_.Int) = 2 := rfl
  have h := Sep.idxOfs_unsigned cenv tushort si ofs0 i 2
    (by rw [sizeof_tushort]; rfl) (by decide) hi (by rw [h2]; exact hno)
  rw [h2] at h
  exact h

/-- **Reading `base[idx]` out of an owned `u16` array.**

    The index's signedness is a parameter (`hcls`, `rfl` at every site), because
    `inflate_table` indexes with `tuint` temporaries as often as with `tint`.
    `hb` is where `arrayU16_load`'s `zero_ext16_repr` comes from — the client's
    arrays satisfy it structurally. -/
theorem eval_index_u16 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Nat} {h : Heap} {base idx : Expr} {i : Nat} {si : Signedness}
    (hpr : permOrder p .Readable = true)
    (harr : arrayU16 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n) (hb : ∀ j, f j < 65536)
    (hptr : EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr ((i : _root_.Int)))))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx) = .pi tushort si)
    (haddr : Integers.Ptrofs.unsigned
               (Sep.idxOfs ge.genv_cenv tushort si ofs0
                 (Integers.Int.repr ((i : _root_.Int))))
             = Integers.Ptrofs.unsigned ofs0 + 2 * (i : _root_.Int)) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd base idx (tptr tushort)) tushort)
      (.Vint (Integers.Int.repr ((f i : Nat)))) := by
  refine EvalExpr.Elvalue _ b
    (Sep.idxOfs ge.genv_cenv tushort si ofs0 (Integers.Int.repr ((i : _root_.Int))))
    .Full _ (Sep.eval_index_lvalue hptr hidx hcls) ?_
  refine DerefLoc.value .Mint16unsigned _ rfl ?_
  rw [Mem.loadv_ptr _ _ _ _ (Or.inl rfl), haddr]
  exact arrayU16_load p b hpr n f i hi hb _ h m harr hag

/-! ## `arrayU8` and `arrayU32` are instances

Proved *equal* to their `arrayOf` forms, so split/update transfer through the
equalities and every existing proof built on the old definitions stands. -/

/-- The element predicate of `arrayU8`. -/
def u8elt (p : Permission) (b : Block) (f : Nat → Nat) : Nat → _root_.Int → HProp :=
  fun i off => mapsto .Mint8unsigned p b off (.Vint (Integers.Int.repr ((f i : Nat))))

/-- The element predicate of `arrayU32`. -/
def u32elt (p : Permission) (b : Block) (f : Nat → Integers.Int) :
    Nat → _root_.Int → HProp :=
  fun i off => mapsto .Mint32 p b off (.Vint (f i))

theorem arrayU8_eq_arrayOf (p : Permission) (b : Block) :
    ∀ (n : Nat) (f : Nat → Nat) (ofs : _root_.Int),
      arrayU8 p b ofs n f = arrayOf (u8elt p b f) 1 ofs n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ k ih =>
      intro f ofs
      show mapsto .Mint8unsigned p b ofs (.Vint (Integers.Int.repr ((f 0 : Nat))))
             ∗ arrayU8 p b (ofs + 1) k (fun i => f (i + 1)) = _
      rw [ih (fun i => f (i + 1)) (ofs + 1)]
      show _ = arrayFrom (fun i => u8elt p b f i (ofs + 1 * (i : _root_.Int))) 0 (k + 1)
      rw [show arrayFrom (fun i => u8elt p b f i (ofs + 1 * (i : _root_.Int))) 0 (k + 1)
            = u8elt p b f 0 (ofs + 1 * ((0 : Nat) : _root_.Int))
              ∗ arrayFrom (fun i => u8elt p b f i (ofs + 1 * (i : _root_.Int))) (0 + 1) k
          from rfl,
          arrayFrom_reindex (fun i => u8elt p b f i (ofs + 1 * (i : _root_.Int))) 1 k 0]
      have hhead : u8elt p b f 0 (ofs + 1 * ((0 : Nat) : _root_.Int))
          = mapsto .Mint8unsigned p b ofs (.Vint (Integers.Int.repr ((f 0 : Nat)))) := by
        simp [u8elt]
      rw [hhead]
      refine congrArg _ ?_
      show arrayOf (u8elt p b (fun i => f (i + 1))) 1 (ofs + 1) k
         = arrayFrom (fun i => u8elt p b f (i + 1) (ofs + 1 * ((i + 1 : Nat) : _root_.Int))) 0 k
      unfold arrayOf
      refine arrayFrom_congr k 0 (fun j _ hj => ?_)
      show u8elt p b (fun i => f (i + 1)) j ((ofs + 1) + 1 * (j : _root_.Int))
         = u8elt p b f (j + 1) (ofs + 1 * ((j + 1 : Nat) : _root_.Int))
      simp only [u8elt]
      rw [show (ofs + 1) + 1 * (j : _root_.Int)
            = ofs + 1 * ((j + 1 : Nat) : _root_.Int) from by push_cast; omega]

theorem arrayU32_eq_arrayOf (p : Permission) (b : Block) :
    ∀ (n : Nat) (f : Nat → Integers.Int) (ofs : _root_.Int),
      arrayU32 p b ofs n f = arrayOf (u32elt p b f) 4 ofs n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ k ih =>
      intro f ofs
      show mapsto .Mint32 p b ofs (.Vint (f 0))
             ∗ arrayU32 p b (ofs + 4) k (fun i => f (i + 1)) = _
      rw [ih (fun i => f (i + 1)) (ofs + 4)]
      show _ = arrayFrom (fun i => u32elt p b f i (ofs + 4 * (i : _root_.Int))) 0 (k + 1)
      rw [show arrayFrom (fun i => u32elt p b f i (ofs + 4 * (i : _root_.Int))) 0 (k + 1)
            = u32elt p b f 0 (ofs + 4 * ((0 : Nat) : _root_.Int))
              ∗ arrayFrom (fun i => u32elt p b f i (ofs + 4 * (i : _root_.Int))) (0 + 1) k
          from rfl,
          arrayFrom_reindex (fun i => u32elt p b f i (ofs + 4 * (i : _root_.Int))) 1 k 0]
      have hhead : u32elt p b f 0 (ofs + 4 * ((0 : Nat) : _root_.Int))
          = mapsto .Mint32 p b ofs (.Vint (f 0)) := by
        simp [u32elt]
      rw [hhead]
      refine congrArg _ ?_
      show arrayOf (u32elt p b (fun i => f (i + 1))) 4 (ofs + 4) k
         = arrayFrom (fun i => u32elt p b f (i + 1) (ofs + 4 * ((i + 1 : Nat) : _root_.Int))) 0 k
      unfold arrayOf
      refine arrayFrom_congr k 0 (fun j _ hj => ?_)
      show u32elt p b (fun i => f (i + 1)) j ((ofs + 4) + 4 * (j : _root_.Int))
         = u32elt p b f (j + 1) (ofs + 4 * ((j + 1 : Nat) : _root_.Int))
      simp only [u32elt]
      rw [show (ofs + 4) + 4 * (j : _root_.Int)
            = ofs + 4 * ((j + 1 : Nat) : _root_.Int) from by push_cast; omega]

/-- **Split for `arrayU32`** — the write path for zlib's `heap[573]` (`int`). -/
theorem arrayU32_split (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Integers.Int) (i : Nat) (hi : i < n) :
    arrayU32 p b ofs n f
      = mapsto .Mint32 p b (ofs + 4 * (i : _root_.Int)) (.Vint (f i))
        ∗ arrayOfRest (u32elt p b f) 4 ofs n i := by
  rw [arrayU32_eq_arrayOf, arrayOf_split (u32elt p b f) 4 ofs n i hi]
  rfl

/-- **Join after a write, `arrayU32`.** -/
theorem arrayU32_update (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Integers.Int) (i : Nat) (v : Integers.Int) (hi : i < n) :
    arrayU32 p b ofs n (fun j => if j = i then v else f j)
      = mapsto .Mint32 p b (ofs + 4 * (i : _root_.Int)) (.Vint v)
        ∗ arrayOfRest (u32elt p b f) 4 ofs n i := by
  rw [arrayU32_eq_arrayOf]
  have h := arrayOf_update (u32elt p b f)
    (u32elt p b (fun j => if j = i then v else f j)) 4 ofs n i hi
    (fun j _ hne => by funext off; simp [u32elt, hne])
  rw [h]
  simp [u32elt]

/-- **Split for `arrayU8`** — the write path for zlib's `depth[573]` (`uchar`). -/
theorem arrayU8_split (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) (i : Nat) (hi : i < n) :
    arrayU8 p b ofs n f
      = mapsto .Mint8unsigned p b (ofs + 1 * (i : _root_.Int))
          (.Vint (Integers.Int.repr ((f i : Nat))))
        ∗ arrayOfRest (u8elt p b f) 1 ofs n i := by
  rw [arrayU8_eq_arrayOf, arrayOf_split (u8elt p b f) 1 ofs n i hi]
  rfl

/-- **Join after a write, `arrayU8`.** -/
theorem arrayU8_update (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Nat) (i : Nat) (v : Nat) (hi : i < n) :
    arrayU8 p b ofs n (fun j => if j = i then v else f j)
      = mapsto .Mint8unsigned p b (ofs + 1 * (i : _root_.Int))
          (.Vint (Integers.Int.repr ((v : Nat))))
        ∗ arrayOfRest (u8elt p b f) 1 ofs n i := by
  rw [arrayU8_eq_arrayOf]
  have h := arrayOf_update (u8elt p b f)
    (u8elt p b (fun j => if j = i then v else f j)) 1 ofs n i hi
    (fun j _ hne => by funext off; simp [u8elt, hne])
  rw [h]
  simp [u8elt]

/-! ## Unions — Phase 9 Step 3

`unionAt` owns the union's **whole** footprint (`co_sizeof`), not just the
active member: otherwise switching the variant is unprovable in general.  For
zlib's `ct_data` the member *is* the whole footprint (both `ushort`, union size
2), so the padding run is empty — that is a hypothesis the layout discharges,
not an assumption baked in here. -/

/-- `n` owned bytes with unknown contents. -/
def anyBytes (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat) : HProp :=
  hexists (fun bytes : List MemVal => ⌜bytes.length = n⌝ ∗ bytesPtsTo b p ofs bytes)

theorem anyBytes_zero (p : Permission) (b : Block) (ofs : _root_.Int) :
    anyBytes p b ofs 0 = emp := by
  funext h
  refine propext ⟨fun ⟨bytes, hb⟩ => ?_, fun hh => ⟨[], pure_sep_intro rfl hh⟩⟩
  obtain ⟨hlen, hbytes⟩ := pure_sep_elim hb
  rw [List.length_eq_zero_iff] at hlen
  subst hlen
  exact hbytes

theorem anyBytes_exists (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat) :
    ∃ h, anyBytes p b ofs n h := by
  obtain ⟨h, hm⟩ := bytesPtsTo_exists b p (List.replicate n .Undef) ofs
  exact ⟨h, List.replicate n .Undef, pure_sep_intro (List.length_replicate) hm⟩

theorem anyBytes_none {p : Permission} {b : Block} {ofs : _root_.Int} {n : Nat}
    {h : Heap} (hh : anyBytes p b ofs n h) :
    ∀ b' o', (b' ≠ b ∨ o' < ofs ∨ ofs + (n : _root_.Int) ≤ o') → h b' o' = none := by
  obtain ⟨bytes, hb⟩ := hh
  obtain ⟨hlen, hbytes⟩ := pure_sep_elim hb
  intro b' o' hout
  refine bytesPtsTo_none b p bytes ofs h hbytes b' o' ?_
  rw [hlen]
  exact hout

/-- Any concrete byte run is an `anyBytes` — the join after writing through it. -/
theorem anyBytes_intro {p : Permission} {b : Block} {ofs : _root_.Int}
    {bytes : List MemVal} {h : Heap} (hbytes : bytesPtsTo b p ofs bytes h) :
    anyBytes p b ofs bytes.length h :=
  ⟨bytes, pure_sep_intro rfl hbytes⟩

/-- A union at `b + ofs`, with active variant `variant` of chunk `chunk` holding
    `v`, owning the **whole** `co_sizeof` footprint.  The trailing padding run is
    `anyBytes`; for zlib's `ct_data` unions it is empty. -/
def unionAt (cenv : CompositeEnv) (uid : Ident) (pm : Permission) (b : Block)
    (ofs : _root_.Int) (variant : Ident) (chunk : Chunk) (v : Val) : HProp :=
  match cenv.get uid with
  | some co =>
      ⌜unionFieldOffset cenv variant co.co_members = .OK (0, .Full)
        ∧ sizeChunk chunk ≤ co.co_sizeof⌝
      ∗ mapsto chunk pm b ofs v
      ∗ anyBytes pm b (ofs + sizeChunk chunk) (co.co_sizeof - sizeChunk chunk).toNat
  | none => ⌜False⌝

/-- Dropping a true pure conjunct. -/
theorem pure_sep_eq {φ : Prop} (hφ : φ) (P : HProp) : (⌜φ⌝ ∗ P) = P := by
  funext h
  exact propext ⟨fun hs => (pure_sep_elim hs).2, fun hp => pure_sep_intro hφ hp⟩

/-- Unfold `unionAt` at a use site, given the composite and the variant facts
    (both `decide` at a concrete union). -/
theorem unionAt_eq {cenv : CompositeEnv} {uid : Ident} {co : Composite}
    {pm : Permission} {b : Block} {ofs : _root_.Int} {variant : Ident}
    {chunk : Chunk} {v : Val}
    (hco : cenv.get uid = some co)
    (hvar : unionFieldOffset cenv variant co.co_members = .OK (0, .Full))
    (hsz : sizeChunk chunk ≤ co.co_sizeof) :
    unionAt cenv uid pm b ofs variant chunk v
      = mapsto chunk pm b ofs v
        ∗ anyBytes pm b (ofs + sizeChunk chunk) (co.co_sizeof - sizeChunk chunk).toNat := by
  unfold unionAt
  rw [hco]
  exact pure_sep_eq ⟨hvar, hsz⟩ _

/-- **Switching the active variant** (equal-size members, which covers every
    union in zlib): the footprint of the old variant, with the new member stored
    through its `mapsto`, is the union at the new variant. -/
theorem unionAt_switch {cenv : CompositeEnv} {uid : Ident} {co : Composite}
    {pm : Permission} {b : Block} {ofs : _root_.Int} {variant' : Ident}
    {chunk chunk' : Chunk} {v' : Val}
    (hco : cenv.get uid = some co)
    (hvar' : unionFieldOffset cenv variant' co.co_members = .OK (0, .Full))
    (hsz : sizeChunk chunk ≤ co.co_sizeof)
    (hszeq : sizeChunk chunk' = sizeChunk chunk) :
    unionAt cenv uid pm b ofs variant' chunk' v'
      = mapsto chunk' pm b ofs v'
        ∗ anyBytes pm b (ofs + sizeChunk chunk) (co.co_sizeof - sizeChunk chunk).toNat := by
  rw [unionAt_eq hco hvar' (by rw [hszeq]; exact hsz), hszeq]

/-- `unionAt` is satisfiable whenever the member fits and the base is aligned. -/
theorem unionAt_satisfiable (cenv : CompositeEnv) (uid : Ident) (co : Composite)
    (pm : Permission) (b : Block) (ofs : _root_.Int) (variant : Ident)
    (chunk : Chunk) (v : Val)
    (hco : cenv.get uid = some co)
    (hvar : unionFieldOffset cenv variant co.co_members = .OK (0, .Full))
    (hsz : sizeChunk chunk ≤ co.co_sizeof)
    (halign : ofs % alignChunk chunk = 0) :
    ∃ h, unionAt cenv uid pm b ofs variant chunk v h := by
  rw [unionAt_eq hco hvar hsz]
  obtain ⟨h1, hh1⟩ := mapsto_exists chunk pm b ofs v halign
  obtain ⟨h2, hh2⟩ := anyBytes_exists pm b (ofs + sizeChunk chunk)
    (co.co_sizeof - sizeChunk chunk).toNat
  refine ⟨Heap.union h1 h2, h1, h2, ?_, rfl, hh1, hh2⟩
  intro b' o'
  by_cases hcase : h1 b' o' = none
  · exact Or.inl hcase
  · refine Or.inr (anyBytes_none hh2 b' o' ?_)
    refine Or.inr (Or.inl ?_)
    show o' < ofs + sizeChunk chunk
    rw [← sizeChunkNat_cast chunk]
    by_cases hx : o' < ofs + ((sizeChunkNat chunk : Nat) : _root_.Int)
    · exact hx
    · exact absurd (mapsto_none hh1 b' o' (Or.inr (Or.inr (Int.not_lt.mp hx)))) hcase

end CC
