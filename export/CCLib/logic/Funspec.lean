/-
  Function specifications, the call rule, and the whole-program closure theorem —
  Phase 7.5.

  ## Why a measure, and not step-indexing

  VST proves its `semax_func` by step-indexing, which works because `semax` is a
  *safety* property: "does not go wrong within `n` steps" composes without ever
  producing an execution.  The triple here is **total correctness** — it asserts a
  terminating execution exists — so `∀ n, Satisfies_n f S` yields nothing, and the
  step-indexed induction does not close.

  The adaptation: every spec carries a well-founded **measure on its arguments**,
  the call rule may only invoke a callee whose measure at the *actual* arguments is
  strictly smaller, and `closure` is induction on that measure.  Mutual recursion
  works because the measure is global rather than per-function, and the discipline
  matches the loop rule, which already carries a `Nat` measure.

  ## Scope

  No function pointers: the callee is resolved through `Genv.findFunct` at a
  pointer with offset zero, which is what `EvalLvalue.Evar_global` produces.
  `Sbuiltin` and external calls are out of scope — `externalCall` is an axiom (as
  it is in Rocq's `Events.v`), so `malloc`/`free`/`memcpy` would need axiomatized
  specs of their own.

  The first part of this file is split off into `CCLib.logic.FunspecCall`.
-/

import CCLib.logic.FunspecCall
import CCLib.logic.Locals

namespace CC
namespace Sep
open HProp

/-! ## `malloc` and `free`

These are **not** axiomatized: `Events.extcall_malloc_sem` / `extcall_free_sem`
are real inductive relations in `CCLib/common/Events.lean`, ported from CompCert, and
both produce the empty trace.  So the rules below are proved, and calls to
`malloc`/`free` go through the ordinary `triple_call` — no bespoke call rule.

`malloc(sz)` allocates `[-sizeof(Mptr), sz)` and stashes `sz` just below the
returned pointer, which is how `free` recovers the size.  The caller therefore
receives *two* resources: the payload, and a **token** for the header.  The token
is what `free` consumes — exactly VST's `malloc_token`. -/

/-- The header cell `malloc` writes below the returned pointer.  Holding it is
    what entitles a caller to `free` the block. -/
def mallocToken (b : Block) (sz : Integers.Ptrofs) : HProp :=
  mapsto Mptr .Freeable b (- sizeChunk Mptr) (Val.Vptrofs sz)

/-- The payload: `sz` bytes of uninitialised, freeable memory at `b + 0`. -/
def mallocPayload (b : Block) (sz : Integers.Ptrofs) : HProp :=
  bytesPtsTo b .Freeable 0
    (List.replicate (Integers.Ptrofs.unsigned sz).toNat MemVal.Undef)

/-- `malloc`'s specification: consumes nothing, produces the token and payload. -/
def mallocSpec (sz : Integers.Ptrofs) : FunSpec where
  tyargs := [tulong]
  tyres := tptr tvoid
  cc := cc_default
  pre := fun vargs => ⌜vargs = [Val.Vptrofs sz]⌝
  post := fun v => hexists (fun b : Block =>
    ⌜v = .Vptr b Integers.Ptrofs.zero⌝ ∗ (mallocToken b sz ∗ mallocPayload b sz))
  measure := fun _ => 0

/-! ### The three facts a `malloc` rule needs about its post-state

Stated and proved here; assembling them into `SatisfiesAt (.External .EF_malloc)`
is the remaining step (it must build the post-fragment from `bytesPtsTo_exists`
and re-establish `Agrees`, following the pattern of `mapsto_store`). -/

-- The header store always succeeds on a freshly allocated block.
theorem malloc_store_ok (m : Mem) (sz : Integers.Ptrofs) :
    ∃ m'', Mem.store Mptr (Mem.alloc m (- sizeChunk Mptr)
             (Integers.Ptrofs.unsigned sz)).1
             (Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz)).2
             (- sizeChunk Mptr) (Val.Vptrofs sz) = some m'' := by
  have hva : Mem.validAccess (Mem.alloc m (- sizeChunk Mptr)
      (Integers.Ptrofs.unsigned sz)).1 Mptr
      (Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz)).2
      (- sizeChunk Mptr) .Writable = true := by
    simp only [Mem.validAccess, Bool.and_eq_true]
    refine ⟨?_, by simp [Mptr, Archi.ptr64, sizeChunk, alignChunk]⟩
    refine Mem.rangePerm_intro _ _ _ _ _ _ (fun ofs h1 h2 => ?_)
    rw [Mem.alloc_result]
    refine Mem.perm_implies (p := .Freeable) ?_ (by decide)
    refine Mem.perm_alloc_same m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz) ofs .Cur h1 ?_
    have hnn : (0 : _root_.Int) ≤ Integers.Ptrofs.unsigned sz := by
      show (0 : _root_.Int) ≤ ((_ : Nat) : _root_.Int); omega
    have hs8 : sizeChunk Mptr = 8 := by simp [Mptr, Archi.ptr64, sizeChunk]
    rw [hs8] at h2
    omega
  unfold Mem.store
  rw [hva]
  exact ⟨_, rfl⟩

-- Step 2: what the post-state holds.

/-- The header bytes read back as what was stored. -/
theorem malloc_header_contents (m' m'' : Mem) (sz : Integers.Ptrofs) (b : Block)
    (hstore : Mem.store Mptr m' b (- sizeChunk Mptr) (Val.Vptrofs sz) = some m'')
    (i : Nat) (hi : i < (encodeVal Mptr (Val.Vptrofs sz)).length) :
    ZMap.get ((- sizeChunk Mptr) + (i : _root_.Int)) (PMap.get b m''.contents)
      = (encodeVal Mptr (Val.Vptrofs sz))[i]! := by
  rw [Mem.store_contents hstore, PMap.gss]
  exact Mem.setN_inside _ _ _ i hi

/-- The payload reads back as `Undef`: `alloc` initialises it, and the header
    store is disjoint from it. -/
theorem malloc_payload_contents (m m' m'' : Mem) (sz : Integers.Ptrofs) (b : Block)
    (halloc : Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz) = (m', b))
    (hstore : Mem.store Mptr m' b (- sizeChunk Mptr) (Val.Vptrofs sz) = some m'')
    (j : _root_.Int) (h0 : 0 ≤ j) :
    ZMap.get j (PMap.get b m''.contents) = MemVal.Undef := by
  have hs8 : sizeChunk Mptr = 8 := by simp [Mptr, Archi.ptr64, sizeChunk]
  have hout : j < (- sizeChunk Mptr) ∨
      (- sizeChunk Mptr) + ((encodeVal Mptr (Val.Vptrofs sz)).length : _root_.Int) ≤ j := by
    right
    rw [length_encodeVal]
    -- fresh `_root_.Int` binders: the goal sits at `CC.Z`, where omega is blind
    have hj : (-(8 : _root_.Int)) + (8 : _root_.Int) ≤ j := by omega
    exact hj
  rw [Mem.store_contents hstore, PMap.gss, Mem.setN_outside _ _ _ _ hout]
  have hm' : m' = (Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz)).1 := by
    rw [halloc]
  have hb : b = m.nextblock := by
    rw [← Mem.alloc_result m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz), halloc]
  rw [hm', hb, Mem.alloc_contents, PMap.gss, ZMap.gi]

-- All the offset arithmetic of the `malloc` rule, over fresh binders.  The goals
-- themselves sit at `CC.Z` (`sizeChunk`, `Ptrofs.unsigned`), where `omega` is
-- blind; `exact`/`apply` bridge by definitional equality.
private theorem hdr_lo (i : Nat) : (-8 : _root_.Int) ≤ (-8) + (i : _root_.Int) := by omega
private theorem hdr_hi (S : _root_.Int) (hS : 0 ≤ S) (i : Nat) (hi : i < 8) :
    (-8 : _root_.Int) + (i : _root_.Int) < S := by omega
private theorem hdr_neg (i : Nat) (hi : i < 8) :
    (-8 : _root_.Int) + (i : _root_.Int) < 0 := by omega
private theorem pay_lo (i : Nat) : (-8 : _root_.Int) ≤ (0 : _root_.Int) + (i : _root_.Int) := by
  omega
private theorem pay_nn (i : Nat) : (0 : _root_.Int) ≤ (0 : _root_.Int) + (i : _root_.Int) := by
  omega
private theorem pay_hi (S : _root_.Int) (i : Nat) (hi : (i : _root_.Int) < S) :
    (0 : _root_.Int) + (i : _root_.Int) < S := by omega
private theorem pay_ge8 (i : Nat) :
    (-8 : _root_.Int) + (8 : _root_.Int) ≤ (0 : _root_.Int) + (i : _root_.Int) := by omega
private theorem toNat_lt (S : _root_.Int) (hS : 0 ≤ S) (i : Nat) (hi : i < S.toNat) :
    (i : _root_.Int) < S := by omega

/-- The whole allocated range — header *and* payload — is `Freeable` afterwards. -/
theorem malloc_access (m m' m'' : Mem) (sz : Integers.Ptrofs) (b : Block)
    (halloc : Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz) = (m', b))
    (hstore : Mem.store Mptr m' b (- sizeChunk Mptr) (Val.Vptrofs sz) = some m'')
    (ofs : _root_.Int) (kk : PermKind)
    (h1 : - sizeChunk Mptr ≤ ofs) (h2 : ofs < Integers.Ptrofs.unsigned sz) :
    PMap.get b m''.access ofs kk = some .Freeable := by
  rw [Mem.store_access hstore]
  have hb : b = m.nextblock := by
    rw [← Mem.alloc_result m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz), halloc]
  have hm' : m' = (Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz)).1 := by
    rw [halloc]
  rw [hm', hb, Mem.alloc_access, PMap.gss]
  simp [h1, h2]

/-- **`malloc` meets its specification.**  Proved from CompCert's own
    `extcall_malloc_sem`, so this costs no axioms.  The caller hands over nothing
    and receives the token and the payload; any frame `hf` is carried through,
    which is sound because the block is *fresh* and therefore owned by nobody. -/
theorem malloc_satisfies (ge : CGenv) (fe : EntryRel) (sz : Integers.Ptrofs)
    (targs : List Ty) (tres : Ty) (cc : CallConv) :
    SatisfiesAt ge fe (.External .EF_malloc targs tres cc) (mallocSpec sz)
      [Val.Vptrofs sz] := by
  intro k m hp hf hk hpre hd hag
  -- the precondition is pure, so the caller's fragment is empty
  obtain ⟨-, hemp⟩ := hpre
  subst hemp
  rw [Heap.emp_union] at hag
  obtain ⟨m', b, halloc⟩ :
      ∃ m' b, Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz) = (m', b) :=
    ⟨_, _, rfl⟩
  obtain ⟨m'', hstore⟩ := malloc_store_ok m sz
  rw [halloc] at hstore
  have hbfresh : b = m.nextblock := by
    rw [← Mem.alloc_result m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz), halloc]
  have hsznn : (0 : _root_.Int) ≤ Integers.Ptrofs.unsigned sz := by
    show (0 : _root_.Int) ≤ ((_ : Nat) : _root_.Int); omega
  have hs8 : sizeChunk Mptr = 8 := by simp [Mptr, Archi.ptr64, sizeChunk]
  -- the two produced fragments
  obtain ⟨hH, hHm⟩ :=
    bytesPtsTo_exists b .Freeable (encodeVal Mptr (Val.Vptrofs sz)) (- sizeChunk Mptr)
  obtain ⟨hP, hPm⟩ :=
    bytesPtsTo_exists b .Freeable
      (List.replicate (Integers.Ptrofs.unsigned sz).toNat MemVal.Undef) 0
  have hownH := bytesPtsTo_ownsRange b .Freeable _ _ hH hHm
  have hownP := bytesPtsTo_ownsRange b .Freeable _ _ hP hPm
  have hlenH : (encodeVal Mptr (Val.Vptrofs sz)).length = 8 := by
    rw [length_encodeVal]; simp [sizeChunkNat, hs8]
  have hlenP : (List.replicate (Integers.Ptrofs.unsigned sz).toNat MemVal.Undef).length
             = (Integers.Ptrofs.unsigned sz).toNat := by simp
  -- `hf` owns nothing in the fresh block
  have hfnone : ∀ o : _root_.Int, hf b o = none := by
    intro o; rw [hbfresh]; exact Heap.Agrees_fresh_none hag o
  -- each fragment agrees with the post-state
  have hagH : Heap.Agrees hH m'' := by
    intro bb oo c hc
    by_cases hb : bb = b
    · rw [hb] at hc ⊢
      rcases window_split (- sizeChunk Mptr) oo 8 with ⟨i, hi, hoo⟩ | hout
      · subst hoo
        rw [hownH i (by rw [hlenH]; exact hi)] at hc
        injection hc with hc; subst hc
        exact ⟨malloc_access m m' m'' sz b halloc hstore _ _ (hdr_lo i)
                 (hdr_hi _ hsznn i hi),
               malloc_access m m' m'' sz b halloc hstore _ _ (hdr_lo i)
                 (hdr_hi _ hsznn i hi),
               malloc_header_contents m' m'' sz b hstore i (by rw [hlenH]; exact hi)⟩
      · rw [bytesPtsTo_none b .Freeable _ _ hH hHm b oo
              (by rw [hlenH]; exact Or.inr hout)] at hc
        exact absurd hc (by simp)
    · rw [bytesPtsTo_none b .Freeable _ _ hH hHm bb oo (Or.inl hb)] at hc
      exact absurd hc (by simp)
  have hagP : Heap.Agrees hP m'' := by
    intro bb oo c hc
    by_cases hb : bb = b
    · rw [hb] at hc ⊢
      rcases window_split 0 oo (Integers.Ptrofs.unsigned sz).toNat with ⟨i, hi, hoo⟩ | hout
      · subst hoo
        rw [hownP i (by rw [hlenP]; exact hi)] at hc
        injection hc with hc; subst hc
        have hiS : ((i : Nat) : _root_.Int) < Integers.Ptrofs.unsigned sz :=
          toNat_lt _ hsznn i hi
        refine ⟨malloc_access m m' m'' sz b halloc hstore _ _ (pay_lo i) (pay_hi _ i hiS),
                malloc_access m m' m'' sz b halloc hstore _ _ (pay_lo i) (pay_hi _ i hiS), ?_⟩
        rw [malloc_payload_contents m m' m'' sz b halloc hstore _ (pay_nn i)]
        simp [hi]
      · rw [bytesPtsTo_none b .Freeable _ _ hP hPm b oo
              (by rw [hlenP]; exact Or.inr hout)] at hc
        exact absurd hc (by simp)
    · rw [bytesPtsTo_none b .Freeable _ _ hP hPm bb oo (Or.inl hb)] at hc
      exact absurd hc (by simp)
  -- header and payload are disjoint from each other, and both from `hf`
  have hdHP : Heap.disjoint hH hP := by
    intro bb oo
    by_cases hb : bb = b
    · rw [hb]
      rcases window_split (- sizeChunk Mptr) oo 8 with ⟨i, hi, hoo⟩ | hout
      · subst hoo
        refine Or.inr (bytesPtsTo_none b .Freeable _ _ hP hPm b _ ?_)
        exact Or.inr (Or.inl (hdr_neg i hi))
      · exact Or.inl (bytesPtsTo_none b .Freeable _ _ hH hHm b oo
          (by rw [hlenH]; exact Or.inr hout))
    · exact Or.inl (bytesPtsTo_none b .Freeable _ _ hH hHm bb oo (Or.inl hb))
  have hdUf : Heap.disjoint (Heap.union hH hP) hf := by
    rw [Heap.disjoint_union_left]
    constructor
    · intro bb oo
      by_cases hb : bb = b
      · exact Or.inr (by rw [hb]; exact hfnone oo)
      · exact Or.inl (bytesPtsTo_none b .Freeable _ _ hH hHm bb oo (Or.inl hb))
    · intro bb oo
      by_cases hb : bb = b
      · exact Or.inr (by rw [hb]; exact hfnone oo)
      · exact Or.inl (bytesPtsTo_none b .Freeable _ _ hP hPm bb oo (Or.inl hb))
  -- `hf` survives the allocation and the header store
  have hagf : Heap.Agrees hf m'' := by
    refine Heap.Agrees_store_frame hstore ?_ (fun i _ => hfnone _)
    have : m' = (Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz)).1 := by
      rw [halloc]
    rw [this]; exact Heap.Agrees_alloc hag
  refine ⟨.Vptr b Integers.Ptrofs.zero, m'', Heap.union hH hP, ?_, ?_, hdUf, ?_⟩
  · exact Steps.one (Step.external_function .EF_malloc targs tres cc
      [Val.Vptrofs sz] k m (.Vptr b Integers.Ptrofs.zero) E0 m''
      (ExtcallMallocSem.intro _ sz m m' b m'' halloc hstore))
  · exact ⟨b, pure_sep_intro rfl ⟨hH, hP, hdHP, rfl,
      pure_sep_intro (by simp [Mptr, Archi.ptr64, sizeChunk, alignChunk]) hHm, hPm⟩⟩
  · exact Heap.Agrees_union (Heap.Agrees_union hagH hagP) hagf

/-! ### `free`

The interesting direction: `free` *consumes* the token and the payload.  Holding
the token is what proves the header is there, which is what lets `free` recover
the size — so the token is not bookkeeping, it is the precondition that makes the
call safe. -/

def freeSpec (b : Block) (sz : Integers.Ptrofs) : FunSpec where
  tyargs := [tptr tvoid]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs => ⌜vargs = [Val.Vptr b Integers.Ptrofs.zero]⌝
                      ∗ (mallocToken b sz
                         ∗ anyBytes .Freeable b 0 (Integers.Ptrofs.unsigned sz).toNat)
  post := fun v => ⌜v = Val.Vundef⌝
  measure := fun _ => 0

/-- **`free` meets its specification.**  It *consumes* the token and the payload.
    Holding the token is what proves the header is present, which is what lets
    `free` recover the size — so the token is not bookkeeping, it is the
    precondition that makes the call safe.

    Written `Nat`-first: `Ptrofs.unsigned` returns `CC.Z`, so naming the size as a
    `Nat` before stating any bound is what keeps every bound below `Int`-typed and
    therefore visible to `omega`. -/
theorem free_satisfies (ge : CGenv) (fe : EntryRel) (b : Block) (sz : Integers.Ptrofs)
    (targs : List Ty) (tres : Ty) (cc : CallConv) :
    SatisfiesAt ge fe (.External .EF_free targs tres cc) (freeSpec b sz)
      [Val.Vptr b Integers.Ptrofs.zero] := by
  intro k m hp hf hk hpre hd hag
  obtain ⟨-, hres⟩ := pure_sep_elim hpre
  obtain ⟨hH, hP, hdHP, heq, hHm, hPm⟩ := hres
  subst heq
  -- ── everything numeric gets an `Int`-typed name up front ──────────────────
  obtain ⟨szN, hszN⟩ : ∃ n : Nat, Integers.Ptrofs.unsigned sz = (n : _root_.Int) :=
    ⟨sz.toNat, rfl⟩
  have hs8 : sizeChunk Mptr = 8 := by simp [Mptr, Archi.ptr64, sizeChunk]
  have hz0 : Integers.Ptrofs.unsigned Integers.Ptrofs.zero = 0 := by
    simp [Integers.Ptrofs.unsigned, Integers.Ptrofs.zero, Integers.MI.unsigned,
          Integers.MI.zero]
  have hlo : Integers.Ptrofs.unsigned Integers.Ptrofs.zero - sizeChunk Mptr
           = (-8 : _root_.Int) := by rw [hz0, hs8]; decide
  have hhi : Integers.Ptrofs.unsigned Integers.Ptrofs.zero + Integers.Ptrofs.unsigned sz
           = (szN : _root_.Int) := by rw [hz0, hszN]; simp
  -- ── the two owned ranges, in index form over `Int` ────────────────────────
  have hagHP : Heap.Agrees (Heap.union hH hP) m := Heap.Agrees_union_left hag
  have hagH : Heap.Agrees hH m := Heap.Agrees_union_left hagHP
  have hagP : Heap.Agrees hP m := Heap.Agrees_union_right hdHP hagHP
  have hownH : ∀ i : Nat, i < 8 →
      hH b ((-8 : _root_.Int) + (i : _root_.Int))
        = some ⟨.Freeable, (encodeVal Mptr (Val.Vptrofs sz))[i]!⟩ := by
    intro i hi
    have h := bytesPtsTo_ownsRange b .Freeable _ _ hH (pure_sep_elim hHm).2 i
      (by rw [length_encodeVal]; simp only [sizeChunkNat, hs8]; omega)
    rwa [hs8] at h
  -- rewrite `Ptrofs.unsigned sz` *out* of the payload predicate: carrying the
  -- bridge fact does not help, because that fact is itself `Z`-typed
  obtain ⟨bytes, hPm⟩ := hPm
  obtain ⟨hlenP, hPm⟩ := pure_sep_elim hPm
  rw [hszN] at hlenP
  simp only [Int.toNat_natCast] at hlenP
  have hownP : ∀ i : Nat, i < szN →
      hP b ((0 : _root_.Int) + (i : _root_.Int)) = some ⟨.Freeable, bytes[i]!⟩ := by
    intro i hi
    exact bytesPtsTo_ownsRange b .Freeable _ _ hP hPm i (by omega)
  -- ── the whole block is Freeable: header range ∪ payload range ─────────────
  have hrpH : Mem.rangePerm m b (-8 : _root_.Int) 0 .Cur .Freeable = true := by
    refine Mem.rangePerm_intro _ _ _ _ _ _ (fun ofs g1 g2 => ?_)
    obtain ⟨i, hi, hoo⟩ : ∃ i : Nat, i < 8 ∧ ofs = (-8 : _root_.Int) + (i : _root_.Int) :=
      ⟨(ofs + 8).toNat, by omega, by omega⟩
    rw [hoo]
    exact Heap.Agrees_perm hagH (hownH i hi) .Cur
  have hrpP : Mem.rangePerm m b (0 : _root_.Int) (szN : _root_.Int) .Cur .Freeable = true := by
    refine Mem.rangePerm_intro _ _ _ _ _ _ (fun ofs g1 g2 => ?_)
    obtain ⟨i, hi, hoo⟩ : ∃ i : Nat, i < szN ∧ ofs = (0 : _root_.Int) + (i : _root_.Int) :=
      ⟨ofs.toNat, by omega, by omega⟩
    rw [hoo]
    exact Heap.Agrees_perm hagP (hownP i hi) .Cur
  have hrp : Mem.rangePerm m b (-8 : _root_.Int) (szN : _root_.Int) .Cur .Freeable = true :=
    Mem.rangePerm_append hrpH hrpP
  -- ── the header load and the free both succeed ─────────────────────────────
  have hload : Mem.load Mptr m b
      (Integers.Ptrofs.unsigned Integers.Ptrofs.zero - sizeChunk Mptr)
      = some (Val.Vptrofs sz) := by
    rw [hlo]
    have hl := mapsto_load (p := .Freeable) (by decide) hHm hagH
    rw [hs8] at hl
    rwa [show Val.loadResult Mptr (Val.Vptrofs sz) = Val.Vptrofs sz from by
          simp [Mptr, Archi.ptr64, Val.Vptrofs, Val.loadResult]] at hl
  have hfree : Mem.free m b
      (Integers.Ptrofs.unsigned Integers.Ptrofs.zero - sizeChunk Mptr)
      (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + Integers.Ptrofs.unsigned sz)
      = some (Mem.uncheckedFree m b
        (Integers.Ptrofs.unsigned Integers.Ptrofs.zero - sizeChunk Mptr)
        (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + Integers.Ptrofs.unsigned sz)) := by
    refine Mem.free_isSome ?_
    rw [hlo, hhi]; exact hrp
  -- ── the frame owns nothing in the freed range ─────────────────────────────
  have hfnone : ∀ ofs : _root_.Int, (-8 : _root_.Int) ≤ ofs → ofs < (szN : _root_.Int) →
      hf b ofs = none := by
    intro ofs g1 g2
    rcases Heap.disjoint_union_left.mp hd with ⟨hdH, hdP⟩
    by_cases hneg : ofs < 0
    · rcases hdH b ofs with hn | hn
      · obtain ⟨i, hi, hoo⟩ : ∃ i : Nat, i < 8 ∧ ofs = (-8 : _root_.Int) + (i : _root_.Int) :=
          ⟨(ofs + 8).toNat, by omega, by omega⟩
        rw [hoo, hownH i hi] at hn
        exact absurd hn (by simp)
      · exact hn
    · rcases hdP b ofs with hn | hn
      · obtain ⟨i, hi, hoo⟩ : ∃ i : Nat, i < szN ∧ ofs = (0 : _root_.Int) + (i : _root_.Int) :=
          ⟨ofs.toNat, by omega, by omega⟩
        rw [hoo, hownP i hi] at hn
        exact absurd hn (by simp)
      · exact hn
  refine ⟨.Vundef, Mem.uncheckedFree m b
      (Integers.Ptrofs.unsigned Integers.Ptrofs.zero - sizeChunk Mptr)
      (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + Integers.Ptrofs.unsigned sz),
    Heap.emp, ?_, ⟨rfl, rfl⟩, Heap.disjoint_emp_left hf, ?_⟩
  · exact Steps.one (Step.external_function .EF_free targs tres cc
      [Val.Vptr b Integers.Ptrofs.zero] k m .Vundef E0 _
      (ExtcallFreeSem.ptr ge.genv_genv.toSenv b Integers.Ptrofs.zero sz m _ hload hfree))
  · rw [Heap.emp_union, Mem.free_result hfree]
    refine Heap.Agrees_free_frame (Heap.Agrees_union_right hd hag) (fun ofs g1 g2 => ?_)
    · rw [hlo] at g1
      rw [hhi] at g2
      exact hfnone ofs g1 g2

/-! ## `memcpy`

The one library external zlib actually calls (`Sbuiltin` is 0 in the whole
round-trip set, so `memcpy` arrives as an ordinary `Scall` to
`EF_memcpy sz al`).  `Events.ExtcallMemcpySem` is a *real* inductive relation, so
this needs no new axiom — the same situation as `malloc`/`free`.

The pleasant part: `ExtcallMemcpySem` demands that source and destination be
non-overlapping, and a precondition that owns them *separately* already says so.
`Heap.disjoint_ranges_nonoverlap` extracts it, so the caller never proves
non-overlap by hand.  Alignment is *not* implied by ownership and stays a
hypothesis. -/

-- fresh-binder bridges: `ExtcallMemcpySem`'s numeric premises sit at `CC.Z`,
-- where `omega` is blind (the standing hazard)
private theorem cast_nonneg (n : Nat) : (0 : _root_.Int) ≤ ((n : Nat) : _root_.Int) := by omega
private theorem pos_of_cast_pos (n : Nat) (h : (0 : _root_.Int) < ((n : Nat) : _root_.Int)) :
    0 < n := by omega

/-- `memcpy`'s specification: the source is read, the destination is overwritten
    with it, and both are handed back.  `old` is whatever the destination held
    before — its *length* is what the caller must match.

    Note the alignment parameter `al` is deliberately **absent**: it constrains
    the call, not the resource, so it lives in the call site's `EF_memcpy sz al`
    and in `memcpy_satisfies`'s hypotheses. -/
def memcpySpec (bsrc : Block) (osrc : Integers.Ptrofs) (psrc : Permission)
    (bdst : Block) (odst : Integers.Ptrofs) (pdst : Permission)
    (src old : List MemVal) : FunSpec where
  tyargs := [tptr tvoid, tptr tvoid]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs =>
    ⌜vargs = [Val.Vptr bdst odst, Val.Vptr bsrc osrc]⌝
    ∗ (bytesPtsTo bsrc psrc (Integers.Ptrofs.unsigned osrc) src
        ∗ bytesPtsTo bdst pdst (Integers.Ptrofs.unsigned odst) old)
  post := fun v =>
    ⌜v = Val.Vundef⌝
    ∗ (bytesPtsTo bsrc psrc (Integers.Ptrofs.unsigned osrc) src
        ∗ bytesPtsTo bdst pdst (Integers.Ptrofs.unsigned odst) src)
  measure := fun _ => 0

/-- **`memcpy` meets its specification.**  Non-overlap comes from the `∗` in the
    precondition; only the alignment conditions are hypotheses, because ownership
    says nothing about alignment. -/
theorem memcpy_satisfies (ge : CGenv) (fe : EntryRel) (al : Z)
    (bsrc : Block) (osrc : Integers.Ptrofs) (psrc : Permission)
    (bdst : Block) (odst : Integers.Ptrofs) (pdst : Permission)
    (src old : List MemVal)
    (targs : List Ty) (tres : Ty) (cc : CallConv)
    (hpr : permOrder psrc .Readable = true)
    (hpw : permOrder pdst .Writable = true)
    (hlen : old.length = src.length)
    (hal : al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8)
    (hszal : ((src.length : Nat) : _root_.Int) % al = 0)
    (halsrc : 0 < src.length → Integers.Ptrofs.unsigned osrc % al = 0)
    (haldst : 0 < src.length → Integers.Ptrofs.unsigned odst % al = 0) :
    SatisfiesAt ge fe
      (.External (.EF_memcpy ((src.length : Nat) : _root_.Int) al) targs tres cc)
      (memcpySpec bsrc osrc psrc bdst odst pdst src old)
      [Val.Vptr bdst odst, Val.Vptr bsrc osrc] := by
  intro k m hp hf hk hpre hd hag
  obtain ⟨-, hres⟩ := pure_sep_elim hpre
  obtain ⟨h1, h2, hd12, heq, hsrcm, hdstm⟩ := hres
  subst heq
  -- ── rearrange so the *destination* is the operated-on fragment ────────────
  rw [Heap.disjoint_union_left] at hd
  have hd2f : Heap.disjoint h2 (Heap.union h1 hf) := by
    rw [Heap.disjoint_union_right]; exact ⟨Heap.disjoint_comm hd12, hd.2⟩
  have hag2 : Heap.Agrees (Heap.union h2 (Heap.union h1 hf)) m := by
    rw [← Heap.union_left_comm hd12, ← Heap.union_assoc]; exact hag
  have hag1 : Heap.Agrees h1 m := Heap.Agrees_union_left (Heap.Agrees_union_left hag)
  -- ── the load, the store, and non-overlap ─────────────────────────────────
  have hload := bytesPtsTo_loadbytes hpr hsrcm hag1
  obtain ⟨m', h2', hstore, h2'm, hd2'f, hag2'⟩ :=
    bytesPtsTo_storebytes hpw hlen.symm hdstm hd2f hag2
  -- non-overlap is *not* a hypothesis: the `∗` in the precondition already
  -- separated the two windows, and `disjoint_ranges_nonoverlap` reads it off
  have hno : bsrc ≠ bdst
             ∨ Integers.Ptrofs.unsigned osrc = Integers.Ptrofs.unsigned odst
             ∨ Integers.Ptrofs.unsigned osrc + ((src.length : Nat) : _root_.Int)
                 ≤ Integers.Ptrofs.unsigned odst
             ∨ Integers.Ptrofs.unsigned odst + ((src.length : Nat) : _root_.Int)
                 ≤ Integers.Ptrofs.unsigned osrc := by
    by_cases hb : bsrc = bdst
    · subst hb
      rcases Heap.disjoint_ranges_nonoverlap hd12 rfl hlen
          (bytesPtsTo_ownsRange _ psrc src _ h1 hsrcm)
          (bytesPtsTo_ownsRange _ pdst old _ h2 hdstm) with hx | hx
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx))
    · exact Or.inl hb
  -- ── put the two fragments back together ──────────────────────────────────
  rw [Heap.disjoint_union_right] at hd2'f
  have hd12' : Heap.disjoint h1 h2' := Heap.disjoint_comm hd2'f.1
  refine ⟨Val.Vundef, m', Heap.union h1 h2', ?_,
          pure_sep_intro rfl ⟨h1, h2', hd12', rfl, hsrcm, h2'm⟩,
          ?_, ?_⟩
  · refine Steps.one (Step.external_function
      (.EF_memcpy ((src.length : Nat) : _root_.Int) al) targs tres cc
      [Val.Vptr bdst odst, Val.Vptr bsrc osrc] k m .Vundef E0 m' ?_)
    exact ExtcallMemcpySem.intro ge.genv_genv.toSenv bdst odst bsrc osrc m src m'
      hal (cast_nonneg _) hszal
      (fun h => halsrc (pos_of_cast_pos _ h)) (fun h => haldst (pos_of_cast_pos _ h))
      hno hload hstore
  · rw [Heap.disjoint_union_left]; exact ⟨hd.1, hd2'f.2⟩
  · rw [Heap.union_assoc, Heap.union_left_comm hd12']
    exact hag2'

end Sep
end CC
