/-
  **Phase 9, Wave D — entry/exit resource transfer: the resource side.**

  Phase 7.4 delivered *frame preservation* for function entry and exit
  (`Agrees_allocVariables`, `Agrees_freeList`): a fragment the callee does not own
  survives.  What was missing is *transfer* — the fragment the callee **gains**
  when `AllocVariables` allocates its `fn_vars`, and gives back when
  `return`/`skip_call` frees them.

  Measured scope: 10 of the linked program's 95 functions have `fn_vars`, with at
  most 3 locals each and footprints of 4-112 bytes.  Two of the 112-byte ones are
  `z_stream stream;` in `compress2`/`uncompress2` — the round-trip entry points —
  so this is on the critical path, not a nicety.

  ## The predicate: all-Undef bytes, not `anyBytes`

  Wave B's `anyBytes` says "some byte list of this length", which is right for
  union padding but **too weak for a fresh local**: to carve a `mapsto` out of a
  region you need to know what the bytes *are*, and an arbitrary byte list is not
  in the image of `encodeVal`.

  A fresh block is stronger than that.  `Mem.alloc` sets `contents` to
  `ZMap.init Undef` (`CCLib/common/Memory.lean:226`) and `Mem.getN_alloc_same` already
  proves a read back is `List.replicate n Undef`.  And for every chunk except
  `Many32`/`Many64`,

      encodeVal chunk .Vundef = List.replicate (sizeChunkNat chunk) .Undef

  holds **by `rfl`** (verified for Mint8unsigned/Mint16unsigned/Mint32/Mint64/
  Mptr; `Many64` is the exception, and `UndefEncoded` below excludes it).  So a
  chunk-aligned, chunk-sized window of Undef bytes *is* `mapsto chunk p b off
  .Vundef`, exactly.  That is what makes `undefBytes_split` true, and it is why
  this file introduces `undefBytes` rather than reusing `anyBytes`.

  ## The missing primitive

  Everything here rests on `bytesPtsTo_append` — a `bytesPtsTo` over `l1 ++ l2`
  is the `∗` of its halves.  `CCLib/logic/SepLogic.lean` never had it, and without it
  no region can be cut in two.  Stated as an **equality**, so it splits and joins.
-/
import CCLib.logic.Aggregate

namespace CC
open HProp

/-! ## Byte runs split and join -/

/-- **The missing primitive**: a byte run over `l1 ++ l2` is the `∗` of the run
    over `l1` and the run over `l2`, the latter starting `l1.length` further on.
    An equality, so the same lemma cuts and re-joins. -/
theorem bytesPtsTo_append (b : Block) (p : Permission) :
    ∀ (l1 l2 : List MemVal) (ofs : _root_.Int),
      bytesPtsTo b p ofs (l1 ++ l2)
        = bytesPtsTo b p ofs l1 ∗ bytesPtsTo b p (ofs + (l1.length : _root_.Int)) l2 := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 ofs
      show bytesPtsTo b p ofs l2 = emp ∗ bytesPtsTo b p (ofs + ((0 : Nat) : _root_.Int)) l2
      rw [emp_sep_eq, show ofs + ((0 : Nat) : _root_.Int) = ofs from by omega]
  | cons v l1' ih =>
      intro l2 ofs
      show bytePtsTo b ofs p v ∗ bytesPtsTo b p (ofs + 1) (l1' ++ l2)
        = (bytePtsTo b ofs p v ∗ bytesPtsTo b p (ofs + 1) l1')
          ∗ bytesPtsTo b p (ofs + ((l1'.length + 1 : Nat) : _root_.Int)) l2
      rw [ih l2 (ofs + 1), sep_assoc_eq,
          show (ofs + 1) + ((l1'.length : Nat) : _root_.Int)
             = ofs + ((l1'.length + 1 : Nat) : _root_.Int) from by push_cast; omega]

/-- **Carving a window out of an unknown-contents region.**  The companion to
    `bytesPtsTo_append` at the `anyBytes` level, and an equality, so it also
    re-joins.

    This is what a client needs to write one `struct code` slot into a table
    region: split `anyBytes … (4 * cap)` at the slot, hand the 4-byte window to
    `triple_assign_copy`, and join the result back.  The result comes back as
    `bytesPtsTo … srcBytes`, which weakens into `anyBytes` by supplying the
    witness — one line, since `anyBytes` is exactly that existential. -/
theorem anyBytes_split (p : Permission) (b : Block) (ofs : _root_.Int)
    (n₁ n₂ : Nat) :
    anyBytes p b ofs (n₁ + n₂)
      = anyBytes p b ofs n₁ ∗ anyBytes p b (ofs + (n₁ : _root_.Int)) n₂ := by
  funext h
  refine propext ⟨fun hall => ?_, fun hsp => ?_⟩
  · obtain ⟨bytes, hb⟩ := hall
    obtain ⟨hlen, hbytes⟩ := pure_sep_elim hb
    have hl1 : (bytes.take n₁).length = n₁ := by
      rw [List.length_take]; omega
    have hl2 : (bytes.drop n₁).length = n₂ := by
      rw [List.length_drop]; omega
    rw [show bytes = bytes.take n₁ ++ bytes.drop n₁ from
          (List.take_append_drop n₁ bytes).symm,
        bytesPtsTo_append, hl1] at hbytes
    obtain ⟨h1, h2, hd, heq, hb1, hb2⟩ := hbytes
    exact ⟨h1, h2, hd, heq, ⟨_, pure_sep_intro hl1 hb1⟩,
           ⟨_, pure_sep_intro hl2 hb2⟩⟩
  · obtain ⟨h1, h2, hd, heq, ha1, ha2⟩ := hsp
    obtain ⟨bytes1, hb1⟩ := ha1
    obtain ⟨bytes2, hb2⟩ := ha2
    obtain ⟨hl1, hp1⟩ := pure_sep_elim hb1
    obtain ⟨hl2, hp2⟩ := pure_sep_elim hb2
    refine ⟨bytes1 ++ bytes2,
      pure_sep_intro (by rw [List.length_append]; omega) ?_⟩
    rw [bytesPtsTo_append, hl1]
    exact ⟨h1, h2, hd, heq, hp1, hp2⟩

/-- **Writing into an `anyBytes` window.**  The `anyBytes` form of
    `mapsto_store`: the old contents are forgotten, so no assumption about them
    is needed, and what comes back is a `mapsto` for the value just written. -/
theorem anyBytes_store {chunk : Chunk} {p : Permission} {b : Block}
    {ofs : _root_.Int} {v' : Val} {h hf : Heap} {m : Mem}
    (hpw : permOrder p .Writable = true)
    (hal : ofs % alignChunk chunk = 0)
    (hm : anyBytes p b ofs (sizeChunkNat chunk) h)
    (hd : Heap.disjoint h hf)
    (hag : Heap.Agrees (Heap.union h hf) m) :
    ∃ m' h', Mem.store chunk m b ofs v' = some m'
           ∧ mapsto chunk p b ofs v' h'
           ∧ Heap.disjoint h' hf
           ∧ Heap.Agrees (Heap.union h' hf) m' := by
  obtain ⟨bytes, hbb⟩ := hm
  obtain ⟨hlen, hb⟩ := pure_sep_elim hbb
  exact bytesPtsTo_store hpw hal hlen hb hd hag

namespace Sep

/-- **`*p = a2;` into a window the caller lent as raw bytes.**  `triple_assign`
    wants the target to be a `mapsto`, i.e. to already hold the encoding of some
    value; `inflate`'s output buffer is only `anyBytes` (the caller promises the
    bytes are writable, nothing about their contents), and a general `MemVal` run
    is not the encoding of anything.  The store never reads the old bytes, so the
    weaker footprint suffices. -/
theorem triple_assign_any (ge fe f) (P Q : Assn) (a1 a2 : Expr) (chunk : Chunk)
    (p : Permission) (b : Block) (ofs : Integers.Ptrofs)
    (hpw : permOrder p .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (hsplit : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
        ∃ vnew h1 h2,
          Heap.disjoint h1 h2 ∧ hp = Heap.union h1 h2
          ∧ anyBytes p b (Integers.Ptrofs.unsigned ofs) (sizeChunkNat chunk) h1
          ∧ Integers.Ptrofs.unsigned ofs % alignChunk chunk = 0
          ∧ EvalLvalue ge e le m a1 b ofs .Full
          ∧ (∃ v2, EvalExpr ge e le m a2 v2
                   ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew)
          ∧ (∀ h1', mapsto chunk p b (Integers.Ptrofs.unsigned ofs) vnew h1' →
                Heap.disjoint h1' h2 → Q e le (Heap.union h1' h2)))
    (hw : Mem.ChunkNoWrap chunk (Integers.Ptrofs.unsigned ofs) := by exact Or.inl rfl) :
    Triple ge fe f P (.Sassign a1 a2) (.only Q) := by
  intro k e le hp hf m hd hag hP
  obtain ⟨vnew, h1, h2, hd12, heq, hany, hal, hlv, ⟨v2, hev2, hcast⟩, hQ⟩ :=
    hsplit e le hp m hP (Heap.Agrees_union_left hag)
  subst heq
  rw [Heap.disjoint_union_left] at hd
  have hd1 : Heap.disjoint h1 (Heap.union h2 hf) := by
    rw [Heap.disjoint_union_right]; exact ⟨hd12, hd.1⟩
  have hag1 : Heap.Agrees (Heap.union h1 (Heap.union h2 hf)) m := by
    rw [← Heap.union_assoc]; exact hag
  obtain ⟨m', h1', hstore, hm1', hd1', hag1'⟩ :=
    anyBytes_store (v' := vnew) hpw hal hany hd1 hag1
  rw [Heap.disjoint_union_right] at hd1'
  refine ⟨.Normal e le m', Heap.union h1' h2, ?_, ?_, ?_, ?_⟩
  · exact Steps.one (Step.assign f a1 a2 k e le m b ofs .Full v2 vnew m' hlv hev2 hcast
      (AssignLoc.value vnew chunk m' hacc (by
        rw [Mem.storev_ptr _ _ _ _ _ hw]
        exact hstore)))
  · rw [Heap.disjoint_union_left]; exact ⟨hd1'.2, hd.2⟩
  · show Heap.Agrees (Heap.union (Heap.union h1' h2) hf) m'
    rw [Heap.union_assoc]; exact hag1'
  · exact hQ h1' hm1' hd1'.1

end Sep

/-- The direction a use site needs after the copy: concrete bytes weaken into
    `anyBytes`.  Just supplying the witness. -/
theorem anyBytes_of_bytesPtsTo {p : Permission} {b : Block} {ofs : _root_.Int}
    {bytes : List MemVal} {h : Heap} (hb : bytesPtsTo b p ofs bytes h) :
    anyBytes p b ofs bytes.length h :=
  ⟨bytes, pure_sep_intro rfl hb⟩

/-! ## Fresh locals: runs of `Undef` -/

/-- `n` owned bytes at `b + ofs`, all `Undef` — exactly what `Mem.alloc` leaves
    behind.  Stronger than `anyBytes` (which allows any contents), and the extra
    strength is what lets a `mapsto` be carved out. -/
def undefBytes (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat) : HProp :=
  bytesPtsTo b p ofs (List.replicate n .Undef)

/-- A run of Undef bytes is in particular *some* run of bytes. -/
theorem undefBytes_anyBytes {p : Permission} {b : Block} {ofs : _root_.Int}
    {n : Nat} {h : Heap} (hu : undefBytes p b ofs n h) : anyBytes p b ofs n h :=
  ⟨List.replicate n .Undef, pure_sep_intro (List.length_replicate) hu⟩

theorem undefBytes_zero (p : Permission) (b : Block) (ofs : _root_.Int) :
    undefBytes p b ofs 0 = emp := rfl

/-- Splitting a run in two, at any point. -/
theorem undefBytes_append (p : Permission) (b : Block) (ofs : _root_.Int)
    (i j : Nat) :
    undefBytes p b ofs (i + j)
      = undefBytes p b ofs i ∗ undefBytes p b (ofs + (i : _root_.Int)) j := by
  unfold undefBytes
  rw [← List.replicate_append_replicate,
      bytesPtsTo_append b p (List.replicate i .Undef)
        (List.replicate j .Undef) ofs, List.length_replicate]

theorem undefBytes_exists (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat) :
    ∃ h, undefBytes p b ofs n h :=
  bytesPtsTo_exists b p (List.replicate n .Undef) ofs

theorem undefBytes_none {p : Permission} {b : Block} {ofs : _root_.Int} {n : Nat}
    {h : Heap} (hu : undefBytes p b ofs n h) :
    ∀ b' o', (b' ≠ b ∨ o' < ofs ∨ ofs + (n : _root_.Int) ≤ o') → h b' o' = none := by
  intro b' o' hout
  refine bytesPtsTo_none b p (List.replicate n .Undef) ofs h hu b' o' ?_
  rw [List.length_replicate]
  exact hout

/-! ## Turning undef bytes into a `mapsto`

`UndefEncoded chunk` is the side condition that an undef value of that chunk
really is a run of Undef bytes.  It holds by `rfl` for every chunk a C program
uses; only `Many32`/`Many64` (CompCert's "any 32/64-bit value" chunks, which
Clight never produces for a scalar access) fail it. -/

/-- `encodeVal chunk .Vundef` is a run of `Undef`.  `rfl` at every concrete
    chunk except `Many32`/`Many64`. -/
def UndefEncoded (chunk : Chunk) : Prop :=
  encodeVal chunk .Vundef = List.replicate (sizeChunkNat chunk) .Undef

theorem undefEncoded_Mint8unsigned : UndefEncoded .Mint8unsigned := rfl
theorem undefEncoded_Mint8signed : UndefEncoded .Mint8signed := rfl
theorem undefEncoded_Mint16unsigned : UndefEncoded .Mint16unsigned := rfl
theorem undefEncoded_Mint16signed : UndefEncoded .Mint16signed := rfl
theorem undefEncoded_Mint32 : UndefEncoded .Mint32 := rfl
theorem undefEncoded_Mint64 : UndefEncoded .Mint64 := rfl
theorem undefEncoded_Mfloat32 : UndefEncoded .Mfloat32 := rfl
theorem undefEncoded_Mfloat64 : UndefEncoded .Mfloat64 := rfl
theorem undefEncoded_Mbool : UndefEncoded .Mbool := rfl

/-- **A chunk-sized run of Undef bytes IS an undef `mapsto`**, given alignment.
    An equality, so it converts in both directions. -/
theorem undefBytes_mapsto {chunk : Chunk} (p : Permission) (b : Block)
    (ofs : _root_.Int) (henc : UndefEncoded chunk)
    (halign : ofs % alignChunk chunk = 0) :
    undefBytes p b ofs (sizeChunkNat chunk) = mapsto chunk p b ofs .Vundef := by
  unfold undefBytes mapsto
  rw [← henc, pure_sep_eq halign]

/-- **D1 — carve one field slot out of a local.**  A local's undef footprint
    yields the `mapsto` at byte offset `d`, with the bytes before and after left
    as undef runs.  This is the entry-side analogue of `arrayOf_split`, and it is
    what makes a *write* to a fresh local possible: `triple_assign` needs a
    `mapsto` for the old value, and after entry all one has is undef bytes. -/
theorem undefBytes_split {chunk : Chunk} (p : Permission) (b : Block)
    (ofs : _root_.Int) (n d : Nat)
    (henc : UndefEncoded chunk)
    (halign : (ofs + (d : _root_.Int)) % alignChunk chunk = 0)
    (hfit : d + sizeChunkNat chunk ≤ n) :
    undefBytes p b ofs n
      = mapsto chunk p b (ofs + (d : _root_.Int)) .Vundef
        ∗ (undefBytes p b ofs d
           ∗ undefBytes p b (ofs + (d : _root_.Int) + (sizeChunkNat chunk : _root_.Int))
               (n - d - sizeChunkNat chunk)) := by
  have hn : n = d + (sizeChunkNat chunk + (n - d - sizeChunkNat chunk)) := by omega
  conv => lhs; rw [hn]
  rw [undefBytes_append p b ofs d (sizeChunkNat chunk + (n - d - sizeChunkNat chunk)),
      undefBytes_append p b (ofs + (d : _root_.Int)) (sizeChunkNat chunk)
        (n - d - sizeChunkNat chunk),
      undefBytes_mapsto p b (ofs + (d : _root_.Int)) henc halign,
      ← sep_assoc_eq, sep_comm_eq (undefBytes p b ofs d), sep_assoc_eq]

/-- **Peel one undefined `u16` cell off the front.**

    `arrayU16`'s element predicate cannot express an undefined element, so the
    zeroing-loop invariant of `inflate_table` (inftrees.c:116-117) has to be
    "initialized `arrayU16` prefix ∗ `undefBytes` suffix".  This is the lemma that
    moves the boundary: it turns the first two bytes of the suffix into the
    `mapsto` a store can go through.

    The alignment hypothesis is genuine, not bookkeeping: `undefBytes` carries no
    alignment and `mapsto` does.  Clients use this at `ofs = 2 * len`, where it is
    `omega`. -/
theorem undefBytes_uncons_u16 (p : Permission) (b : Block) (ofs : _root_.Int)
    (n : Nat) (hal : ofs % 2 = 0) :
    undefBytes p b ofs (2 * (n + 1))
      = mapsto .Mint16unsigned p b ofs .Vundef
        ∗ undefBytes p b (ofs + 2) (2 * n) := by
  rw [undefBytes_split (chunk := .Mint16unsigned) p b ofs (2 * (n + 1)) 0
        undefEncoded_Mint16unsigned
        (by show (ofs + ((0 : Nat) : _root_.Int)) % 2 = 0
            omega)
        (by show 0 + sizeChunkNat .Mint16unsigned ≤ 2 * (n + 1)
            show 0 + 2 ≤ 2 * (n + 1)
            omega),
      -- compound offset first: collapsing `ofs + ↑0` early destroys the pattern
      show ofs + ((0 : Nat) : _root_.Int)
             + ((sizeChunkNat .Mint16unsigned : Nat) : _root_.Int) = ofs + 2 from by
        show ofs + ((0 : Nat) : _root_.Int) + ((2 : Nat) : _root_.Int) = ofs + 2
        omega,
      show ofs + ((0 : Nat) : _root_.Int) = ofs from by omega,
      show 2 * (n + 1) - 0 - sizeChunkNat .Mint16unsigned = 2 * n from by
        show 2 * (n + 1) - 0 - 2 = 2 * n
        omega,
      undefBytes_zero, emp_sep_eq]

/-! ## The fresh block a local lives in

`Mem.alloc` produces `Freeable` permission over `[0, n)` and `Undef` contents, so
the canonical undef fragment for the fresh block is realized by the post-alloc
memory.  This is the per-local half of the entry rule. -/

/-- A `bytesPtsTo` fragment is *exactly* its range: owning a cell forces the
    block and offset to be inside, and pins the cell's contents. -/
theorem undefBytes_inv {p : Permission} {b : Block} {n : Nat} {h : Heap}
    (hu : undefBytes p b 0 n h) :
    ∀ b' (o' : _root_.Int) c, h b' o' = some c →
      b' = b ∧ 0 ≤ o' ∧ o' < (n : _root_.Int) ∧ c = ⟨p, MemVal.Undef⟩ := by
  intro b' o' c hc
  have hown := bytesPtsTo_ownsRange b p (List.replicate n .Undef) 0 h hu
  -- `window_split` rather than a raw `by_cases`: its statement is at `_root_.Int`,
  -- so the facts it produces are omega-visible (the standing `CC.Z` note).
  by_cases hb : b' = b
  · subst hb
    rcases window_split 0 o' n with ⟨i, hi, hoo⟩ | hout
    · -- take the bounds out *before* rewriting, while `hoo` is still oriented
      have h0 : 0 ≤ o' := by omega
      have hlt' : o' < (n : _root_.Int) := by omega
      have hlen : i < (List.replicate n (MemVal.Undef)).length := by
        rw [List.length_replicate]; exact hi
      have hcell := hown i hlen
      rw [← hoo] at hcell
      rw [hcell] at hc
      injection hc with hc
      refine ⟨rfl, h0, hlt', ?_⟩
      rw [← hc]
      refine congrArg (fun v => (⟨p, v⟩ : Cell)) ?_
      show (List.replicate n (MemVal.Undef))[i]! = MemVal.Undef
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
      simp [hi]
    · rw [undefBytes_none hu b' o' (Or.inr hout)] at hc
      exact absurd hc (by simp)
  · rw [undefBytes_none hu b' o' (Or.inl hb)] at hc
    exact absurd hc (by simp)

/-- **The fresh block's fragment is realized by the memory `alloc` produced.** -/
theorem undefBytes_agrees_alloc (m : Mem) (n : Nat) {h : Heap}
    (hu : undefBytes .Freeable m.nextblock 0 n h) :
    Heap.Agrees h (Mem.alloc m 0 (n : _root_.Int)).1 := by
  intro b' o' c hc
  obtain ⟨hb, hlo, hhi, hcv⟩ := undefBytes_inv hu b' o' c hc
  subst hb
  subst hcv
  refine ⟨?_, ?_, ?_⟩
  · show PMap.get m.nextblock (Mem.alloc m 0 (n : _root_.Int)).1.access o' .Cur = _
    rw [Mem.alloc_access, PMap.gss]
    exact if_pos ⟨hlo, hhi⟩
  · show PMap.get m.nextblock (Mem.alloc m 0 (n : _root_.Int)).1.access o' .Max = _
    rw [Mem.alloc_access, PMap.gss]
    exact if_pos ⟨hlo, hhi⟩
  · show ZMap.get o' (PMap.get m.nextblock (Mem.alloc m 0 (n : _root_.Int)).1.contents) = _
    rw [Mem.alloc_contents, PMap.gss]
    simp [ZMap.get, ZMap.init, PMap.get, PMap.init, PTree.empty, PTree.get]


/-- `Int.toNat` round-trips on a nonnegative integer.  Stated over a fresh
    `_root_.Int` binder because `sizeof` returns `CC.Z`, where `omega` cannot see
    a nonnegativity hypothesis (the standing `CC.Z` note). -/
theorem toNat_cast_of_nonneg (x : _root_.Int) (h : 0 ≤ x) :
    ((x.toNat : Nat) : _root_.Int) = x := by omega

/-! ## D3 — the resource a function entry produces

`AllocVariables` allocates one fresh block per local.  What the callee gains is
the `∗`-chain of those blocks' undef footprints, together with the environment
bindings that name them. -/

/-- The locals of a function, as the callee sees them after entry: one fresh
    block per `(id, ty)`, owning `sizeof ce ty` undef bytes at `Freeable`, named
    by the environment. -/
def localsAt (ce : CompositeEnv) (e : Env) : List (Ident × Ty) → HProp
  | [] => emp
  | (id, ty) :: rest =>
      hexists (fun b : Block =>
        ⌜e.get id = some (b, ty)⌝ ∗ undefBytes .Freeable b 0 (sizeof ce ty).toNat)
      ∗ localsAt ce e rest

/-- Allocating variables other than `id` leaves `id`'s binding alone.  This is
    where `listNorepet (varNames f.fn_vars)` — which `FunctionEntry2` supplies —
    earns its keep: without it a later local could shadow an earlier one. -/
theorem allocVariables_env_other {ce : CompositeEnv} {id : Ident} :
    ∀ {vars : List (Ident × Ty)} {e m e' m'},
      AllocVariables ce e m vars e' m' → id ∉ varNames vars →
      e'.get id = e.get id := by
  intro vars e m e' m' hav
  induction hav with
  | nil _ _ => intro _; rfl
  | cons e0 m0 id0 ty0 vars0 m1 b1 m2 e2 _ hrest ih =>
      intro hni
      simp only [varNames, List.map_cons, List.mem_cons] at hni
      rw [ih (by simp only [varNames]; exact fun hm => hni (Or.inr hm))]
      exact PTree.gso id0 id (b1, ty0) e0 (fun hc => hni (Or.inl hc.symm))

/-- **D3 — entry transfers resources in.**  After `AllocVariables`, the caller's
    fragment `h` is intact and the callee additionally owns one fresh undef block
    per local.  The fresh blocks are automatically disjoint from `h` and from each
    other: each is `m.nextblock` at its own allocation step, and `Agrees` forbids
    owning a byte of a not-yet-allocated block (`Heap.Agrees_fresh_none`).

    `hsz` is a genuine side condition, not an oversight: the Lean port of
    `Ctypes.composite` dropped CompCert's `co_sizeof_pos` `Prop` field (see the
    header of `CCLib/cfrontend/Ctypes.lean`), so `0 ≤ sizeof ce ty` does **not** hold for an
    arbitrary composite environment — only for one `buildCompositeEnv` produced.
    At a concrete program it is `decide`. -/
theorem allocVariables_resources {ce : CompositeEnv} :
    ∀ {vars : List (Ident × Ty)} {e0 m e' m'},
      AllocVariables ce e0 m vars e' m' →
      listNorepet (varNames vars) →
      (∀ v ∈ vars, 0 ≤ sizeof ce v.2) →
      ∀ h : Heap, Heap.Agrees h m →
      ∃ hl, Heap.disjoint h hl
            ∧ Heap.Agrees (Heap.union h hl) m'
            ∧ localsAt ce e' vars hl := by
  intro vars e0 m e' m' hav
  induction hav with
  | nil e m =>
      intro _ _ h hag
      exact ⟨Heap.emp, Heap.disjoint_emp_right h, by rw [Heap.union_emp]; exact hag, rfl⟩
  | cons e00 m0 id ty vars0 m1 b1 m2 e2 halloc hrest ih =>
      intro hnr hsz h hag
      have hnr' : id ∉ varNames vars0 ∧ listNorepet (varNames vars0) := by
        simpa [listNorepet, varNames, List.nodup_cons] using hnr
      -- the fresh block is `m0.nextblock`, and `h` owns nothing there
      have hb1 : b1 = m0.nextblock := by rw [← Mem.alloc_result m0 0 (sizeof ce ty), halloc]
      have hm1 : m1 = (Mem.alloc m0 0 (sizeof ce ty)).1 := by rw [halloc]
      obtain ⟨h1, hh1⟩ := undefBytes_exists .Freeable b1 0 (sizeof ce ty).toNat
      have hszcast : ((sizeof ce ty).toNat : _root_.Int) = sizeof ce ty :=
        toNat_cast_of_nonneg _ (hsz (id, ty) List.mem_cons_self)
      have hag1 : Heap.Agrees h1 m1 := by
        rw [hm1, ← hszcast]
        exact undefBytes_agrees_alloc m0 (sizeof ce ty).toNat (by rw [hb1] at hh1; exact hh1)
      have hd1 : Heap.disjoint h h1 := by
        intro bb oo
        by_cases hbb : bb = b1
        · exact Or.inl (by rw [hbb, hb1]; exact Heap.Agrees_fresh_none hag oo)
        · exact Or.inr (undefBytes_none hh1 bb oo (Or.inl hbb))
      have hagu : Heap.Agrees (Heap.union h h1) m1 := by
        refine Heap.Agrees_union ?_ hag1
        rw [hm1]; exact Heap.Agrees_alloc hag
      obtain ⟨hl', hd', hag', hloc'⟩ :=
        ih hnr'.2 (fun v hv => hsz v (List.mem_cons_of_mem _ hv)) (Heap.union h h1) hagu
      have hdsplit := Heap.disjoint_union_left.mp hd'
      refine ⟨Heap.union h1 hl', ?_, ?_, ?_⟩
      · rw [Heap.disjoint_union_right]; exact ⟨hd1, hdsplit.1⟩
      · rw [← Heap.union_assoc]; exact hag'
      · refine ⟨h1, hl', hdsplit.2, rfl, ⟨b1, ?_⟩, hloc'⟩
        refine pure_sep_intro ?_ hh1
        rw [allocVariables_env_other hrest hnr'.1]
        exact PTree.gss id (b1, ty) e00

/-! ## D4 — the exit side: freeing succeeds

`return` and `skip_call` free every block of `blocksOfEnv`, and `Mem.free`
returns `none` unless the whole range is `Freeable`.  Owning the range at
`Freeable` is exactly what makes it succeed — so the callee's own locals pay for
their deallocation, and a proof never has to assume the free works. -/

/-- Freeing one block leaves every *other* block's permissions alone, so a
    `rangePerm` for a different block survives.  This is what makes the list
    induction go through. -/
theorem rangePerm_free_other {m : Mem} {b b' : Block} {lo hi lo' hi' : Z}
    {m' : Mem} (hne : b' ≠ b) (hfree : Mem.free m b lo hi = some m')
    (hrp : Mem.rangePerm m b' lo' hi' .Cur .Freeable = true) :
    Mem.rangePerm m' b' lo' hi' .Cur .Freeable = true := by
  rw [Mem.free_result hfree]
  refine Mem.rangePerm_intro _ _ _ _ _ _ (fun o h1 h2 => ?_)
  rw [Mem.perm_free_other m b lo hi b' hne o .Cur .Freeable]
  exact Mem.rangePerm_perm m b' lo' hi' .Cur .Freeable hrp o h1 h2

/-- **D4 — freeing a list of owned blocks succeeds.**  Given `Freeable` over
    every block's range, and the blocks pairwise distinct, `freeList` returns a
    memory.  Distinctness is needed because freeing a block twice fails: the
    second `free` finds no permission. -/
theorem freeList_isSome_of_rangePerm :
    ∀ (l : List (Block × Z × Z)) (m : Mem),
      (∀ blk ∈ l, Mem.rangePerm m blk.1 blk.2.1 blk.2.2 .Cur .Freeable = true) →
      l.Pairwise (fun a b => a.1 ≠ b.1) →
      ∃ m', Mem.freeList m l = some m' := by
  intro l
  induction l with
  | nil => intro m _ _; exact ⟨m, rfl⟩
  | cons blk l' ih =>
      intro m hrp hpw
      obtain ⟨b, lo, hi⟩ := blk
      have hfree := Mem.free_isSome (hrp (b, lo, hi) List.mem_cons_self)
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
      refine ⟨?_, ?_⟩
      case refine_1 =>
        exact (ih (Mem.uncheckedFree m b lo hi) (fun blk' hb' =>
          rangePerm_free_other (Ne.symm (hhead blk' hb')) hfree
            (hrp blk' (List.mem_cons_of_mem _ hb'))
          ) htail).choose
      case refine_2 =>
        rw [Mem.freeList, hfree]
        exact (ih (Mem.uncheckedFree m b lo hi) (fun blk' hb' =>
          rangePerm_free_other (Ne.symm (hhead blk' hb')) hfree
            (hrp blk' (List.mem_cons_of_mem _ hb'))
          ) htail).choose_spec

/-- Ownership of a local's footprint gives the `Freeable` range its
    deallocation needs — the bridge from the resource to `Mem.free`. -/
theorem undefBytes_rangePerm {b : Block} {n : Nat} {h : Heap} {m : Mem}
    (hu : undefBytes .Freeable b 0 n h) (hag : Heap.Agrees h m) :
    Mem.rangePerm m b 0 (n : _root_.Int) .Cur .Freeable = true := by
  have hown := bytesPtsTo_ownsRange b .Freeable (List.replicate n .Undef) 0 h hu
  have hrp := Heap.Agrees_rangePerm hag hown .Cur
  rw [List.length_replicate] at hrp
  simpa using hrp

/-! ### Freeing a block whose contents are no longer `undef`

`undefBytes_rangePerm` above is too specialized for a real return: by then
`count`/`offs` are fully-written `arrayU16`s and `here` is three field `mapsto`s,
none of which is `undefBytes` any more.

The generalization is one line, because `Heap.Agrees_rangePerm` is already stated
over `ownsRange` and `bytesPtsTo_ownsRange` already bridges to it.  So rather than
a new "owned block" predicate, everything reduces to *getting the fragment into
`bytesPtsTo` form* — and the three lemmas that do that (`mapsto_eq_bytes`,
`bytesPtsTo_append`, `arrayU16_bytes` below) already exist or are added here. -/

/-- **The workhorse.**  Any owned byte run gives the `rangePerm` a free needs, at
    whatever permission it is held. -/
theorem bytesPtsTo_rangePerm {p : Permission} {b : Block} {ofs : _root_.Int}
    {vl : List MemVal} {h : Heap} {m : Mem}
    (hb : bytesPtsTo b p ofs vl h) (hag : Heap.Agrees h m) :
    Mem.rangePerm m b ofs (ofs + (vl.length : _root_.Int)) .Cur p = true :=
  Heap.Agrees_rangePerm hag (bytesPtsTo_ownsRange b p vl ofs h hb) .Cur

/-- The bytes an `arrayU16` holds, front to back. -/
def u16Bytes (f : Nat → Nat) : Nat → List MemVal
  | 0 => []
  | n + 1 => u16Bytes f n
             ++ encodeVal .Mint16unsigned (.Vint (Integers.Int.repr ((f n : Nat))))

theorem u16Bytes_length (f : Nat → Nat) : ∀ n, (u16Bytes f n).length = 2 * n
  | 0 => rfl
  | n + 1 => by
      show (u16Bytes f n
             ++ encodeVal .Mint16unsigned
                  (.Vint (Integers.Int.repr ((f n : Nat))))).length = 2 * (n + 1)
      rw [List.length_append, u16Bytes_length f n, length_encodeVal]
      show 2 * n + sizeChunkNat .Mint16unsigned = 2 * (n + 1)
      show 2 * n + 2 = 2 * (n + 1)
      omega

/-- **An `arrayU16` *is* a byte run.**  Proved with `arrayOf_snoc` and
    `bytesPtsTo_append`, one element at a time.  This is what lets a
    fully-initialized local be freed at return, and it is also the bridge a
    functional proof needs when it has to look at `count`/`offs` as memory. -/
theorem arrayU16_bytes (p : Permission) (b : Block) (ofs : _root_.Int)
    (f : Nat → Nat) (hal : ofs % 2 = 0) :
    ∀ n, arrayU16 p b ofs n f = bytesPtsTo b p ofs (u16Bytes f n)
  | 0 => rfl
  | n + 1 => by
      show arrayOf (u16elt p b f) 2 ofs (n + 1) = _
      rw [arrayOf_snoc]
      show arrayU16 p b ofs n f
            ∗ u16elt p b f n (ofs + 2 * (n : _root_.Int)) = _
      rw [arrayU16_bytes p b ofs f hal n]
      show bytesPtsTo b p ofs (u16Bytes f n)
            ∗ mapsto .Mint16unsigned p b (ofs + 2 * (n : _root_.Int))
                (.Vint (Integers.Int.repr ((f n : Nat)))) = _
      rw [mapsto_eq_bytes (chunk := .Mint16unsigned)
            (by show (ofs + 2 * (n : _root_.Int)) % 2 = 0
                omega)]
      show _ = bytesPtsTo b p ofs
                (u16Bytes f n
                 ++ encodeVal .Mint16unsigned (.Vint (Integers.Int.repr ((f n : Nat)))))
      rw [bytesPtsTo_append, u16Bytes_length f n]
      show _ = bytesPtsTo b p ofs (u16Bytes f n)
                ∗ bytesPtsTo b p (ofs + ((2 * n : Nat) : _root_.Int)) _
      rw [show ofs + ((2 * n : Nat) : _root_.Int) = ofs + 2 * (n : _root_.Int) from by
            omega]

/-- The corollary a return site wants: a fully-written `u16` local is
    `Freeable` over its whole extent. -/
theorem arrayU16_rangePerm {b : Block} {n : Nat} {f : Nat → Nat}
    {h : Heap} {m : Mem}
    (ha : arrayU16 .Freeable b 0 n f h) (hag : Heap.Agrees h m) :
    Mem.rangePerm m b 0 ((2 * n : Nat) : _root_.Int) .Cur .Freeable = true := by
  rw [arrayU16_bytes .Freeable b 0 f (by omega) n] at ha
  have h1 := bytesPtsTo_rangePerm ha hag
  rw [u16Bytes_length f n] at h1
  simpa using h1

/-! ## D2 — a fresh local as a struct

`z_stream stream;` gives 112 undef bytes; the code then writes `stream.zalloc`,
`stream.zfree`, … so each field must become a `mapsto` at its own offset.

**No new lemma is needed for this.**  `undefBytes_split` leaves the bytes after
the carved slot as *another* `undefBytes` run, so splitting again at the next
field is the same lemma applied to the residual — the field list is peeled off
front to back.  `two_fields` below proves that composition rather than asserting
it, since "it should compose" is exactly the kind of claim this project has
learned to check.

**The alignment obligation is real and does not vanish.**  Wave B's `∗` gives
non-overlap for free (Step 5's finding), but nothing gives alignment.  Here it is
cheap for a different reason: a fresh block starts at offset 0, so a field at
`delta` needs `delta % alignChunk chunk = 0` — a *layout* fact about the struct,
`decide` at a concrete composite. -/

/-- **Two fields carved out of one fresh local**, at offsets `d₁ < d₂`, with the
    padding before, between and after left owned.  The proof is
    `undefBytes_split` twice: the second application lands on the residual run
    the first one produced.  Generalises to any number of fields by iterating. -/
theorem two_fields (p : Permission) (b : Block) (ofs : _root_.Int)
    (n d1 d2 : Nat) {c1 c2 : Chunk}
    (he1 : UndefEncoded c1) (he2 : UndefEncoded c2)
    (ha1 : (ofs + (d1 : _root_.Int)) % alignChunk c1 = 0)
    (ha2 : (ofs + (d2 : _root_.Int)) % alignChunk c2 = 0)
    (hord : d1 + sizeChunkNat c1 ≤ d2)
    (hfit : d2 + sizeChunkNat c2 ≤ n) :
    undefBytes p b ofs n
      = mapsto c1 p b (ofs + (d1 : _root_.Int)) .Vundef
        ∗ (undefBytes p b ofs d1
           ∗ (mapsto c2 p b (ofs + (d2 : _root_.Int)) .Vundef
              ∗ (undefBytes p b (ofs + (d1 : _root_.Int) + (sizeChunkNat c1 : _root_.Int))
                   (d2 - d1 - sizeChunkNat c1)
                 ∗ undefBytes p b (ofs + (d2 : _root_.Int) + (sizeChunkNat c2 : _root_.Int))
                     (n - d2 - sizeChunkNat c2)))) := by
  -- first field
  rw [undefBytes_split p b ofs n d1 he1 ha1 (by omega)]
  -- second field, out of the residual run that the first split left behind
  have hbase : ofs + (d1 : _root_.Int) + (sizeChunkNat c1 : _root_.Int)
      = ofs + ((d1 + sizeChunkNat c1 : Nat) : _root_.Int) := by push_cast; omega
  rw [hbase,
      undefBytes_split p b (ofs + ((d1 + sizeChunkNat c1 : Nat) : _root_.Int))
        (n - d1 - sizeChunkNat c1) (d2 - d1 - sizeChunkNat c1) he2
        (by rw [show ofs + ((d1 + sizeChunkNat c1 : Nat) : _root_.Int)
                    + ((d2 - d1 - sizeChunkNat c1 : Nat) : _root_.Int)
                  = ofs + (d2 : _root_.Int) from by push_cast; omega]
            exact ha2)
        (by omega)]
  -- line the residual offsets and counts up with the statement
  rw [show ofs + ((d1 + sizeChunkNat c1 : Nat) : _root_.Int)
           + ((d2 - d1 - sizeChunkNat c1 : Nat) : _root_.Int)
         = ofs + (d2 : _root_.Int) from by push_cast; omega,
      show ofs + (d2 : _root_.Int) + (sizeChunkNat c2 : _root_.Int)
         = ofs + (d2 : _root_.Int) + (sizeChunkNat c2 : _root_.Int) from rfl,
      show n - d1 - sizeChunkNat c1 - (d2 - d1 - sizeChunkNat c1) - sizeChunkNat c2
         = n - d2 - sizeChunkNat c2 from by omega,
      show ofs + ((d1 + sizeChunkNat c1 : Nat) : _root_.Int)
         = ofs + (d1 : _root_.Int) + (sizeChunkNat c1 : _root_.Int) from by push_cast; omega]

end CC
