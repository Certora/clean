/-
  Non-vacuity checks for the Phase-7.1 memory lemma library
  (`CCLib/common/MemoryLemmas.lean`).

  Every lemma there is proved, so it is *true*.  That is not the same as being
  *useful*: if `store` never succeeded, `load_store_same` would hold vacuously and
  the separation logic built on it would be worthless.  So each headline lemma is
  instantiated here at a concrete memory and the conclusion is computed.

  Everything is discharged by `decide`, not `native_decide` — the Lean memory
  model reduces in the kernel, so these checks add no axioms at all.  (Rocq
  cannot run the same checks: `Mem.store`/`load` are not evaluable there, because
  `range_perm_dec` recurses on an opaque accessibility proof.)
-/
import CCLib
open CC

namespace MemCheck

/-! ## A concrete memory: one 8-byte block -/

def blk : Mem × Block := Mem.alloc Mem.empty 0 8
def m0 : Mem := blk.1
def b0 : Block := blk.2

/-! ## Allocation gives `Freeable`, `Undef` cells -/

/-- `perm_alloc_same` is not vacuous. -/
theorem fresh_is_freeable : Mem.perm m0 b0 3 .Cur .Freeable = true :=
  Mem.perm_alloc_same Mem.empty 0 8 3 .Cur (by decide) (by decide)

/-- `perm_alloc_outside` is not vacuous. -/
theorem outside_is_unpermitted : Mem.perm m0 b0 9 .Cur .Nonempty = false :=
  Mem.perm_alloc_outside Mem.empty 0 8 9 .Cur .Nonempty (by decide)

/-- `getN_alloc_same` is not vacuous: a fresh block really reads as `Undef`. -/
theorem fresh_is_undef :
    Mem.getN 4 0 (PMap.get b0 m0.contents) = List.replicate 4 MemVal.Undef :=
  Mem.getN_alloc_same Mem.empty 0 8 4 0

/-! ## Store then load -/

theorem s1_isSome :
    (Mem.store .Mint32 m0 b0 0 (.Vint (Integers.Int.repr 42))).isSome = true := by decide

def m1 : Mem := (Mem.store .Mint32 m0 b0 0 (.Vint (Integers.Int.repr 42))).get s1_isSome

theorem s1_eq : Mem.store .Mint32 m0 b0 0 (.Vint (Integers.Int.repr 42)) = some m1 :=
  (Option.some_get s1_isSome).symm

/-- **`load_store_same` is not vacuous.**  A real store succeeds and the value
    comes back. -/
theorem load_after_store : Mem.load .Mint32 m1 b0 0 = some (.Vint (Integers.Int.repr 42)) := by
  have h := Mem.load_store_same s1_eq
  simpa [Val.loadResult] using h

/-! ## A second, disjoint store leaves the first alone -/

theorem s2_isSome :
    (Mem.store .Mint32 m1 b0 4 (.Vint (Integers.Int.repr 7))).isSome = true := by decide

def m2 : Mem := (Mem.store .Mint32 m1 b0 4 (.Vint (Integers.Int.repr 7))).get s2_isSome

theorem s2_eq : Mem.store .Mint32 m1 b0 4 (.Vint (Integers.Int.repr 7)) = some m2 :=
  (Option.some_get s2_isSome).symm

/-- **`load_store_other` is not vacuous** — and this is the lemma the frame rule
    will rest on: writing at offset 4 provably does not disturb offset 0. -/
theorem frame_preserved : Mem.load .Mint32 m2 b0 0 = some (.Vint (Integers.Int.repr 42)) := by
  rw [Mem.load_store_other s2_eq .Mint32 b0 0 (by right; left; decide)]
  exact load_after_store

/-- The second store did land, so the check above is not passing by accident. -/
theorem second_store_landed :
    Mem.load .Mint32 m2 b0 4 = some (.Vint (Integers.Int.repr 7)) := by
  have h := Mem.load_store_same s2_eq
  simpa [Val.loadResult] using h

/-! ## Freeing -/

/-- `free_isSome` is not vacuous: the block really is `Freeable`. -/
theorem free_ok : Mem.free m2 b0 0 8 = some (Mem.uncheckedFree m2 b0 0 8) :=
  Mem.free_isSome (by decide)

/-- `perm_free_inside` is not vacuous. -/
theorem after_free_unpermitted :
    Mem.perm (Mem.uncheckedFree m2 b0 0 8) b0 3 .Cur .Readable = false :=
  Mem.perm_free_inside m2 b0 0 8 3 .Cur .Readable (by decide) (by decide)

/-! ## The heap algebra, and the frame property end to end (Phase 7.2)

The point of `Heap`/`Agrees` is that a fragment disjoint from a write keeps
agreeing with memory afterwards — that is what the frame rule will be built from.
Here it is exercised on concrete data: a fragment owning bytes 0-3 survives a
store at offset 4. -/

/-- A fragment owning the four bytes of the first `int`, at `Freeable`. -/
def hf : Heap := fun b ofs =>
  if b = b0 ∧ 0 ≤ ofs ∧ ofs < 4
  then some ⟨.Freeable, ZMap.get ofs (PMap.get b0 m1.contents)⟩
  else none

/-- The block is `Freeable` throughout `[0, 8)` in `m1` — allocation set it, and
    the store did not touch `access`. -/
theorem b0_eq : b0 = Mem.empty.nextblock := rfl

-- Arithmetic side conditions, stated over fresh `_root_.Int` binders.  A type
-- *ascription* on an existing `Z`-typed variable does not help: the term is
-- unchanged, so `inferType` still says `CC.Z` and the operator elaborates there.
-- Passing a `Z`-typed hypothesis into an `Int`-typed binder is fine — `exact`
-- bridges the two by definitional equality.
private theorem lt4_lt8 (x : _root_.Int) (h : x < 4) : x < 8 := by omega
private theorem not_lt4_eq4 (x : _root_.Int) (h1 : x < 4) (h2 : x = 4) : False := by omega
private theorem not_off_lo (x : _root_.Int) (h : 4 + x < 4) (h0 : 0 ≤ x) : False := by omega

theorem m1_freeable (ofs : Int) (h1 : 0 ≤ ofs) (h2 : ofs < 8) (k : PermKind) :
    PMap.get b0 m1.access ofs k = some .Freeable := by
  have hacc : m1.access = m0.access := Mem.store_access s1_eq
  rw [hacc]
  show PMap.get b0 (Mem.alloc Mem.empty 0 8).1.access ofs k = _
  rw [b0_eq, Mem.alloc_access, PMap.gss]
  simp [h1, h2]

theorem hf_agrees_m1 : Heap.Agrees hf m1 := by
  intro b ofs c hc
  by_cases hcond : b = b0 ∧ 0 ≤ ofs ∧ ofs < 4
  · obtain ⟨hb, h1, h2⟩ := hcond
    subst hb
    have hcv : c = ⟨.Freeable, ZMap.get ofs (PMap.get b0 m1.contents)⟩ := by
      simpa [hf, h1, h2] using hc.symm
    subst hcv
    have h8 : ofs < 8 := lt4_lt8 ofs h2
    exact ⟨m1_freeable ofs h1 h8 .Cur, m1_freeable ofs h1 h8 .Max, rfl⟩
  · rw [show hf b ofs = none from by simp [hf, hcond]] at hc
    exact absurd hc (by simp)

/-- **The frame property, concretely.**  `hf` owns bytes 0-3; the store at offset
    4 is disjoint from it; so `hf` still agrees with the memory afterwards. -/
theorem hf_agrees_m2 : Heap.Agrees hf m2 :=
  Heap.Agrees_store_frame s2_eq hf_agrees_m1
    (fun i hi => by
      have hne : ¬ (b0 = b0 ∧ (0:Z) ≤ 4 + (i : Z) ∧ 4 + (i : Z) < 4) := by
        intro hc
        exact not_off_lo (i : Z) hc.2.2 (Int.natCast_nonneg i)
      show (if b0 = b0 ∧ (0:Z) ≤ 4 + (i:Z) ∧ 4 + (i:Z) < 4 then _ else none) = none
      rw [if_neg hne])

/-- And therefore the framed bytes are literally unchanged: byte 0 of the first
    `int` reads the same in `m2` as the fragment recorded from `m1`. -/
theorem framed_byte_unchanged :
    ZMap.get 0 (PMap.get b0 m2.contents) = ZMap.get 0 (PMap.get b0 m1.contents) := by
  have hc : hf b0 0 = some ⟨.Freeable, ZMap.get 0 (PMap.get b0 m1.contents)⟩ := by
    simp [hf]
  exact Heap.Agrees_val hf_agrees_m2 hc

/-! ## The monoid laws are not vacuous either -/

theorem disjoint_example : Heap.disjoint hf (Heap.single b0 4 ⟨.Freeable, .Undef⟩) := by
  intro b ofs
  by_cases hcond : b = b0 ∧ 0 ≤ ofs ∧ ofs < 4
  · refine Or.inr (Heap.single_other _ _ _ _ _ ?_)
    intro heq
    exact not_lt4_eq4 ofs hcond.2.2 heq.2
  · exact Or.inl (by simp [hf, hcond])

/-! ## The assertion layer (Phase 7.3)

A weaker check than the ones above, and deliberately so: it establishes that
`mapsto` and `arrayU32` are *satisfiable* — ruling out the vacuous-predicate
failure mode — but does not pair a fragment with a concrete `Agrees`.  Building a
hand-rolled heap and proving it equals the singleton chain `mapsto` unfolds to
costs a great deal for little extra assurance, and Phase 7.7 exercises the whole
path for real when `is_sorted` is re-proved: the program itself constructs exactly
such a state. -/

/-- `mapsto` is satisfiable. -/
theorem mapsto_satisfiable :
    ∃ h, mapsto .Mint32 .Freeable b0 0 (.Vint (Integers.Int.repr 42)) h := by
  obtain ⟨h, hh⟩ :=
    bytesPtsTo_exists b0 .Freeable (encodeVal .Mint32 (.Vint (Integers.Int.repr 42))) 0
  exact ⟨h, HProp.pure_sep_intro (by decide) hh⟩

def arr2 : Nat → Integers.Int :=
  fun i => if i = 0 then Integers.Int.repr 42 else Integers.Int.repr 7

/-- `arrayU32` is satisfiable — a two-element array of `unsigned int`. -/
theorem array_satisfiable : ∃ h, arrayU32 .Freeable b0 0 2 arr2 h :=
  arrayU32_satisfiable .Freeable b0 2 arr2 0 (by decide)

end MemCheck
