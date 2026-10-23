/-
  Soundness of the abstract memory of the value analysis — port of the
  `smatch` / `bmatch` part of `backend/ValueDomain.v` (from `vnormalize_cast`
  on).

  Ported: `vnormalize_cast`, `loadbytes_load_ext`, `smatch_ext`, `smatch_inv`,
  `smatch_ge`, `In_loadbytes`, `smatch_loadbytes`, `loadbytes_provenance`,
  `storebytes_provenance`, `store_provenance`, `smatch_store`,
  `smatch_storebytes`, `bmatch_ext`, `bmatch_inv`, `ablock_load_sound`,
  `ablock_load_anywhere_sound`, `ablock_init_sound`,
  `ablock_store_anywhere_sound`, `ablock_loadbytes_sound`,
  `ablock_storebytes_anywhere_sound`, `inval_after_contents`,
  `inval_before_outside`, `inval_before_contents_1`, `max_size_chunk`,
  `inval_before_contents`, `ablock_store_contents`, `chunk_compat_true`,
  `ablock_store_sound`, `ablock_storebytes_contents`,
  `ablock_storebytes_sound`, `bbeq_load`, `bbeq_sound`, `smatch_lub_l`,
  `smatch_lub_r`, `bmatch_lub_l`, `bmatch_lub_r`; `PTree.beq_sound` (for
  `ptreeBeq` with boolean equality of values).

  From `common/Memory.v` (for the concrete memory model): `load_loadbytes`,
  `storebytes_range_perm`, `loadbytes_storebytes_other`, `store_storebytes`,
  `load_store_similar_2`, `load_storebytes_other`.

  Difference from Rocq: `smatch_store` / `smatch_storebytes` derive the
  "loaded pointer" half from the byte-level half (`load_ptr_fragment`: a load
  returning a pointer reads a fragment of that pointer at its first byte)
  instead of using `Mem.load_pointer_store`.
-/
import CCLib.backend.ValueDomainMem
import CCLib.backend.ValueDomainProofNormMono
import CCLib.common.MemoryBytes
import CCLib.common.MemdataEncode

namespace CC

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

namespace Mem

/-- `Mem.storebytes_range_perm` -/
theorem storebytes_range_perm {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    (h : storebytes m b ofs bytes = some m') :
    rangePerm m b ofs (ofs + (bytes.length : Z)) .Cur .Writable = true := by
  unfold storebytes at h
  split at h
  · assumption
  · cases h

/-- `Mem.load_loadbytes` -/
theorem load_loadbytes {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val}
    (h : load chunk m b ofs = some v) :
    ∃ bytes, loadbytes m b ofs (sizeChunk chunk) = some bytes ∧ v = decodeVal chunk bytes := by
  have hva := load_valid_access h
  unfold load at h
  rw [if_pos hva] at h
  cases h
  simp only [validAccess, Bool.and_eq_true] at hva
  exact ⟨_, loadbytes_result hva.1, rfl⟩

/-- `Mem.loadbytes_storebytes_other` -/
theorem loadbytes_storebytes_other {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    {m' : Mem} (h : storebytes m b ofs bytes = some m') (b' : Block) (ofs' n : _root_.Int)
    (hdisj : b' ≠ b ∨ ofs' + n ≤ ofs ∨ ofs + (bytes.length : _root_.Int) ≤ ofs') :
    loadbytes m' b' ofs' n = loadbytes m b' ofs' n := by
  unfold loadbytes
  rw [rangePerm_congr (fun o => perm_storebytes h b' o .Cur .Readable)]
  split
  · congr 1
    apply getN_congr
    intro i h1 h2
    rw [storebytes_contents h, PMap.gsspec]
    split
    · rename_i he
      subst he
      apply setN_outside
      rcases hdisj with hb | hr
      · exact absurd rfl hb
      · zomega
    · rfl
  · rfl

/-- `Mem.store_storebytes` -/
theorem store_storebytes {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (h : store chunk m b ofs v = some m') : storebytes m b ofs (encodeVal chunk v) = some m' := by
  unfold store at h
  split at h
  · rename_i hva
    cases h
    unfold storebytes
    simp only [validAccess, Bool.and_eq_true] at hva
    rw [if_pos (by rw [length_encodeVal, sizeChunkNat_cast]; exact hva.1)]
  · cases h

/-- `Mem.load_store_similar_2` -/
theorem load_store_similar_2 {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    (h : store chunk m b ofs v = some m') {chunk' : Chunk}
    (hsz : sizeChunk chunk' = sizeChunk chunk) (hal : alignChunk chunk' ≤ alignChunk chunk)
    (hty : chunk'.typ = chunk.typ) :
    load chunk' m' b ofs = some (Val.loadResult chunk' v) := by
  have hvaW : validAccess m chunk b ofs .Writable = true := store_valid_access h
  have hva : validAccess m' chunk' b ofs .Readable = true := by
    simp only [validAccess, Bool.and_eq_true, beq_iff_eq] at hvaW ⊢
    refine ⟨?_, ?_⟩
    · rw [hsz]
      exact rangePerm_store h b ofs (ofs + sizeChunk chunk) .Cur .Readable
        (rangePerm_implies hvaW.1 (by decide))
    · have h2 := hvaW.2
      cases chunk <;> cases chunk' <;> simp only [alignChunk] at hal h2 ⊢ <;> zomega
  unfold load
  rw [hva, store_contents h, PMap.gss]
  simp only [if_true]
  congr 1
  rw [show sizeChunkNat chunk' = (encodeVal chunk v).length by
        rw [length_encodeVal]; simp only [sizeChunkNat, hsz],
      getN_setN_same]
  exact decodeEncodeVal_similar hty.symm hsz.symm (decodeEncodeVal_general v chunk chunk')

/-- `Mem.load_storebytes_other` -/
theorem load_storebytes_other {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    (h : storebytes m b ofs bytes = some m') (chunk : Chunk) (b' : Block) (ofs' : _root_.Int)
    (hdisj : b' ≠ b ∨ ofs' + sizeChunk chunk ≤ ofs ∨ ofs + (bytes.length : _root_.Int) ≤ ofs') :
    load chunk m' b' ofs' = load chunk m b' ofs' := by
  unfold load validAccess
  rw [rangePerm_congr (fun o => perm_storebytes h b' o .Cur .Readable)]
  split
  · congr 2
    apply getN_congr
    intro i h1 h2
    rw [storebytes_contents h, PMap.gsspec]
    split
    · rename_i he
      subst he
      apply setN_outside
      have hc := sizeChunkNat_cast chunk
      rcases hdisj with hb | hr
      · exact absurd rfl hb
      · zomega
    · rfl
  · rfl

end Mem

namespace ValueDomain

variable {bc : BlockClassification}

/-- `ValueDomain.loadbytes_load_ext` -/
theorem loadbytes_load_ext {b : Block} {m m' : Mem}
    (H : ∀ ofs n bytes, Mem.loadbytes m' b ofs n = some bytes → n ≥ 0 →
      Mem.loadbytes m b ofs n = some bytes) :
    ∀ chunk ofs v, Mem.load chunk m' b ofs = some v → Mem.load chunk m b ofs = some v := by
  intro chunk ofs v hl
  obtain ⟨bytes, hb, rfl⟩ := Mem.load_loadbytes hl
  have hva := Mem.load_valid_access hl
  simp only [Mem.validAccess, Bool.and_eq_true, beq_iff_eq] at hva
  have hpos := sizeChunk_pos chunk
  exact Mem.loadbytes_load (H _ _ _ hb (Int.le_of_lt hpos)) (Int.dvd_of_emod_eq_zero hva.2)

/-- `ValueDomain.smatch_ext` -/
theorem smatch_ext {m : Mem} {b : Block} {p : Aptr} {m' : Mem} (hs : Smatch bc m b p)
    (H : ∀ ofs n bytes, Mem.loadbytes m' b ofs n = some bytes → n ≥ 0 →
      Mem.loadbytes m b ofs n = some bytes) : Smatch bc m' b p :=
  ⟨fun chunk ofs v hl => hs.1 chunk ofs v (loadbytes_load_ext H chunk ofs v hl),
   fun ofs b' ofs' q i hl => hs.2 ofs b' ofs' q i (H _ _ _ hl (by decide))⟩

/-- `ValueDomain.smatch_inv` -/
theorem smatch_inv {m : Mem} {b : Block} {p : Aptr} {m' : Mem} (hs : Smatch bc m b p)
    (H : ∀ ofs n, n ≥ 0 → Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) :
    Smatch bc m' b p :=
  smatch_ext hs fun ofs n bytes hl hn => by rw [← H ofs n hn]; exact hl

/-- `ValueDomain.smatch_ge` -/
theorem smatch_ge {m : Mem} {b : Block} {p q : Aptr} (hs : Smatch bc m b p) (hge : Pge q p) :
    Smatch bc m b q :=
  ⟨fun chunk ofs v hl => vmatch_ge (.ip_ip _ _ hge) (hs.1 chunk ofs v hl),
   fun ofs b' ofs' q' i hl => pmatch_ge hge (hs.2 ofs b' ofs' q' i hl)⟩

/-- `ValueDomain.In_loadbytes` -/
theorem In_loadbytes {m : Mem} {b : Block} {byte : MemVal} :
    ∀ (k : Nat) (n ofs : _root_.Int) (bytes : List MemVal), n.toNat = k →
    Mem.loadbytes m b ofs n = some bytes → byte ∈ bytes →
    ∃ ofs', ofs ≤ ofs' ∧ ofs' < ofs + n ∧ Mem.loadbytes m b ofs' 1 = some [byte] := by
  intro k
  induction k with
  | zero =>
    intro n ofs bytes hk hl hin
    rw [Mem.loadbytes_empty m b ofs (by omega)] at hl
    cases hl; cases hin
  | succ k ih =>
    intro n ofs bytes hk hl hin
    obtain ⟨b1, b2, h1, h2, rfl⟩ :=
      Mem.loadbytes_split (n1 := 1) (n2 := n - 1) (by rw [show 1 + (n - 1) = n by omega]; exact hl)
        (by decide) (by omega)
    have hlen := Mem.loadbytes_length h1
    rcases List.mem_append.mp hin with hin | hin
    · match b1, hlen, hin with
      | [x], _, hin =>
        cases List.mem_singleton.mp hin
        exact ⟨ofs, Int.le_refl _, by omega, h1⟩
    · obtain ⟨o, ho1, ho2, ho3⟩ := ih (n - 1) (ofs + 1) b2 (by omega) h2 hin
      exact ⟨o, by omega, by omega, ho3⟩

/-- `ValueDomain.smatch_loadbytes` -/
theorem smatch_loadbytes {m : Mem} {b : Block} {p : Aptr} {b' : Block} {ofs' : Integers.Ptrofs}
    {q : Quantity} {i : Nat} {n ofs : Z} {bytes : List MemVal}
    (hl : Mem.loadbytes m b ofs n = some bytes) (hs : Smatch bc m b p)
    (hin : MemVal.Fragment (.Vptr b' ofs') q i ∈ bytes) : Pmatch bc b' ofs' p := by
  obtain ⟨o, _, _, ho⟩ := In_loadbytes _ n ofs bytes rfl hl hin
  exact hs.2 o b' ofs' q i ho

/-- `ValueDomain.vnormalize_cast` -/
theorem vnormalize_cast {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {p : Aptr}
    (hl : Mem.load chunk m b ofs = some v) (hv : Vmatch bc v (.Ifptr p)) :
    Vmatch bc v (vnormalize chunk (.Ifptr p)) := by
  obtain ⟨bytes, _, rfl⟩ := Mem.load_loadbytes hl
  have hc := decodeVal_cast chunk bytes
  have ht := decodeVal_type chunk bytes
  cases chunk <;> simp only at hc
  · rw [hc]
    show Vmatch bc _ (.Uns _ 1)
    generalize decodeVal _ bytes = w
    cases w
    case Vint i =>
      rw [normBool_vint]; split
      · exact .Uns _ _ _ (by decide) (isUns1_zero_or_one ‹_›)
      · exact .Uns_undef _ _
    all_goals exact .Uns_undef _ _
  · rw [hc]; show Vmatch bc _ (.Sgn _ 8)
    generalize decodeVal _ bytes = w
    cases w <;> simp only [Val.signExt]
    case Vint i => exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _)
    all_goals exact .Sgn_undef _ _
  · rw [hc]; show Vmatch bc _ (.Uns _ 8)
    generalize decodeVal _ bytes = w
    cases w <;> simp only [Val.zeroExt]
    case Vint i => exact .Uns _ _ _ (by decide) (zext_uns _ _)
    all_goals exact .Uns_undef _ _
  · rw [hc]; show Vmatch bc _ (.Sgn _ 16)
    generalize decodeVal _ bytes = w
    cases w <;> simp only [Val.signExt]
    case Vint i => exact .Sgn _ _ _ (by decide) (sext_sgn (by decide) _)
    all_goals exact .Sgn_undef _ _
  · rw [hc]; show Vmatch bc _ (.Uns _ 16)
    generalize decodeVal _ bytes = w
    cases w <;> simp only [Val.zeroExt]
    case Vint i => exact .Uns _ _ _ (by decide) (zext_uns _ _)
    all_goals exact .Uns_undef _ _
  · show Vmatch bc _ (.Num _)
    generalize decodeVal _ bytes = w at ht
    cases w <;> simp [Val.HasType, Val.hasType, Chunk.typ] at ht <;> constructor
  · exact hv
  · show Vmatch bc _ (.Num _)
    generalize decodeVal _ bytes = w at ht
    cases w <;> simp [Val.HasType, Val.hasType, Chunk.typ] at ht <;> constructor
  · show Vmatch bc _ (.Num _)
    generalize decodeVal _ bytes = w at ht
    cases w <;> simp [Val.HasType, Val.hasType, Chunk.typ] at ht <;> constructor
  · show Vmatch bc _ (.Num _)
    generalize decodeVal _ bytes = w at ht
    cases w <;> simp [Val.HasType, Val.hasType, Chunk.typ, Archi.ptr64] at ht <;> constructor
  · exact hv

/-- `ValueDomain.loadbytes_provenance` -/
theorem loadbytes_provenance {m : Mem} {b : Block} {ofs' : _root_.Int} {byte : MemVal} :
    ∀ (k : Nat) (n ofs : _root_.Int) (bytes : List MemVal), n.toNat = k →
    Mem.loadbytes m b ofs n = some bytes → Mem.loadbytes m b ofs' 1 = some [byte] →
    ofs ≤ ofs' → ofs' < ofs + n → byte ∈ bytes := by
  intro k
  induction k with
  | zero => intro n ofs bytes hk _ _ h1 h2; omega
  | succ k ih =>
    intro n ofs bytes hk hl h1 hlo hhi
    obtain ⟨b1, b2, l1, l2, rfl⟩ :=
      Mem.loadbytes_split (n1 := 1) (n2 := n - 1) (by rw [show 1 + (n - 1) = n by omega]; exact hl)
        (by decide) (by omega)
    rw [List.mem_append]
    by_cases he : ofs = ofs'
    · subst he
      rw [h1] at l1; cases l1
      exact .inl (List.mem_singleton.mpr rfl)
    · exact .inr (ih (n - 1) (ofs + 1) b2 (by omega) l2 h1 (by omega) (by omega))

/-- `ValueDomain.storebytes_provenance` -/
theorem storebytes_provenance {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    {b' : Block} {ofs' : Z} {b'' : Block} {ofs'' : Integers.Ptrofs} {q : Quantity} {i : Nat}
    (hs : Mem.storebytes m b ofs bytes = some m')
    (hl : Mem.loadbytes m' b' ofs' 1 = some [.Fragment (.Vptr b'' ofs'') q i]) :
    MemVal.Fragment (.Vptr b'' ofs'') q i ∈ bytes ∨
    Mem.loadbytes m b' ofs' 1 = some [.Fragment (.Vptr b'' ofs'') q i] := by
  by_cases hin : b' = b ∧ ofs ≤ ofs' ∧ ofs' < ofs + (bytes.length : _root_.Int)
  · obtain ⟨rfl, h1, h2⟩ := hin
    left
    have hrp : Mem.rangePerm m' b' ofs (ofs + (bytes.length : Z)) .Cur .Readable = true := by
      rw [Mem.rangePerm_congr (fun o => Mem.perm_storebytes hs b' o .Cur .Readable)]
      exact Mem.rangePerm_implies (Mem.storebytes_range_perm hs) (by decide)
    exact loadbytes_provenance _ _ ofs bytes rfl (Mem.loadbytes_storebytes_same hs hrp) hl h1 h2
  · right
    rw [← hl, Mem.loadbytes_storebytes_other hs b' ofs' 1 (by
      by_cases hb : b' = b
      · subst hb
        have : ¬(ofs ≤ ofs' ∧ ofs' < ofs + (bytes.length : _root_.Int)) := fun h => hin ⟨rfl, h⟩
        exact .inr (by zomega)
      · exact .inl hb)]

theorem loadResult_ptr {chunk : Chunk} {v : Val} {bx : Block} {ox : Integers.Ptrofs}
    (h : Val.loadResult chunk v = .Vptr bx ox) : v = .Vptr bx ox := by
  cases chunk <;> cases v <;>
    simp [Val.loadResult, Archi.ptr64, Val.normBool, Val.isBool] at h ⊢ <;>
    first | exact h | (split at h <;> cases h)

/-- A load that returns a pointer reads, at its first byte, a fragment of
    that pointer. -/
theorem load_ptr_fragment {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {bx : Block}
    {ox : Integers.Ptrofs} (hl : Mem.load chunk m b ofs = some (.Vptr bx ox)) :
    ∃ q i, Mem.loadbytes m b ofs 1 = some [.Fragment (.Vptr bx ox) q i] := by
  obtain ⟨bytes, hb, he⟩ := Mem.load_loadbytes hl
  have hpos := sizeChunk_pos chunk
  obtain ⟨b1, b2, l1, _, rfl⟩ := Mem.loadbytes_split (n1 := 1) (n2 := sizeChunk chunk - 1)
    (by rw [show (1 : _root_.Int) + (sizeChunk chunk - 1) = sizeChunk chunk by omega]; exact hb)
    (by decide) (by omega)
  have hlen := Mem.loadbytes_length l1
  match b1, hlen, l1, he with
  | [x], _, l1, he =>
    have hs := decodeVal_shape chunk x b2
    simp only [List.singleton_append] at he
    generalize decodeVal chunk (x :: b2) = w at hs he
    cases hs with
    | f v q i mvl _ _ _ _ =>
      rw [loadResult_ptr he.symm] at l1
      exact ⟨q, i, l1⟩
    | b _ _ _ hnp _ => subst he; exact hnp.elim
    | u _ => cases he

/-- `ValueDomain.store_provenance` -/
theorem store_provenance {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    {b' : Block} {ofs' : Z} {b'' : Block} {ofs'' : Integers.Ptrofs} {q : Quantity} {i : Nat}
    (hs : Mem.store chunk m b ofs v = some m')
    (hl : Mem.loadbytes m' b' ofs' 1 = some [.Fragment (.Vptr b'' ofs'') q i]) :
    (v = .Vptr b'' ofs'' ∧
      (chunk = .Mint32 ∨ chunk = .Many32 ∨ chunk = .Mint64 ∨ chunk = .Many64)) ∨
    Mem.loadbytes m b' ofs' 1 = some [.Fragment (.Vptr b'' ofs'') q i] := by
  rcases storebytes_provenance (Mem.store_storebytes hs) hl with A | A
  · left
    have ENC := encodeVal_shape chunk v
    generalize encodeVal chunk v = l at ENC A
    cases ENC with
    | f q' i' mvl hc _ _ hall =>
      rcases List.mem_cons.mp A with e | e
      · cases e; exact ⟨rfl, hc⟩
      · obtain ⟨j, e', _⟩ := hall _ e
        cases e'; exact ⟨rfl, hc⟩
    | b byte mvl _ hall =>
      rcases List.mem_cons.mp A with e | e
      · cases e
      · obtain ⟨_, e'⟩ := hall _ e; cases e'
    | u mvl hall =>
      rcases List.mem_cons.mp A with e | e
      · cases e
      · cases hall _ e
  · exact .inr A

/-- `ValueDomain.smatch_store` -/
theorem smatch_store {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    {b' : Block} {p : Aptr} {av : Aval}
    (hs : Mem.store chunk m b ofs v = some m') (hsm : Smatch bc m b' p) (hv : Vmatch bc v av) :
    Smatch bc m' b' (vplub av p) := by
  have B : ∀ o b'' o'' q i, Mem.loadbytes m' b' o 1 = some [.Fragment (.Vptr b'' o'') q i] →
      Pmatch bc b'' o'' (vplub av p) := by
    intro o b'' o'' q i hl
    rcases store_provenance hs hl with ⟨rfl, _⟩ | h
    · have V := vmatch_vplub_l p hv
      cases V with | ifptr_p _ _ _ hp => exact hp
    · exact pmatch_vplub av (hsm.2 _ _ _ _ _ h)
  refine ⟨fun chunk' o v' hl => vmatch_ifptr _ _ (fun bx ox he => ?_), B⟩
  subst he
  obtain ⟨q, i, h1⟩ := load_ptr_fragment hl
  exact B _ _ _ _ _ h1

/-- `ValueDomain.smatch_storebytes` -/
theorem smatch_storebytes {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    {b' : Block} {p p' : Aptr}
    (hs : Mem.storebytes m b ofs bytes = some m') (hsm : Smatch bc m b' p)
    (hc : ∀ b' ofs' q i, MemVal.Fragment (.Vptr b' ofs') q i ∈ bytes → Pmatch bc b' ofs' p') :
    Smatch bc m' b' (plub p' p) := by
  have B : ∀ o b'' o'' q i, Mem.loadbytes m' b' o 1 = some [.Fragment (.Vptr b'' o'') q i] →
      Pmatch bc b'' o'' (plub p' p) := by
    intro o b'' o'' q i hl
    rcases storebytes_provenance hs hl with h | h
    · exact pmatch_lub_l _ (hc _ _ _ _ h)
    · exact pmatch_lub_r _ (hsm.2 _ _ _ _ _ h)
  refine ⟨fun chunk' o v' hl => vmatch_ifptr _ _ (fun bx ox he => ?_), B⟩
  subst he
  obtain ⟨q, i, h1⟩ := load_ptr_fragment hl
  exact B _ _ _ _ _ h1

/-- `ValueDomain.bmatch_ext` -/
theorem bmatch_ext {m : Mem} {b : Block} {ab : Ablock} {m' : Mem} (hb : Bmatch bc m b ab)
    (H : ∀ ofs n bytes, Mem.loadbytes m' b ofs n = some bytes → n ≥ 0 →
      Mem.loadbytes m b ofs n = some bytes) : Bmatch bc m' b ab :=
  ⟨smatch_ext hb.1 H, fun chunk ofs v hl => hb.2 chunk ofs v (loadbytes_load_ext H chunk ofs v hl)⟩

/-- `ValueDomain.bmatch_inv` -/
theorem bmatch_inv {m : Mem} {b : Block} {ab : Ablock} {m' : Mem} (hb : Bmatch bc m b ab)
    (H : ∀ ofs n, n ≥ 0 → Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) :
    Bmatch bc m' b ab :=
  bmatch_ext hb fun ofs n bytes hl hn => by rw [← H ofs n hn]; exact hl

/-- `ValueDomain.ablock_load_sound` -/
theorem ablock_load_sound {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {ab : Ablock}
    (hl : Mem.load chunk m b ofs = some v) (hb : Bmatch bc m b ab) :
    Vmatch bc v (ablockLoad chunk ab ofs) :=
  hb.2 _ _ _ hl

/-- `ValueDomain.ablock_load_anywhere_sound` -/
theorem ablock_load_anywhere_sound {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val}
    {ab : Ablock} (hl : Mem.load chunk m b ofs = some v) (hb : Bmatch bc m b ab) :
    Vmatch bc v (ablockLoadAnywhere chunk ab) :=
  vnormalize_cast hl (hb.1.1 _ _ _ hl)

/-- `ValueDomain.ablock_init_sound` -/
theorem ablock_init_sound {m : Mem} {b : Block} {p : Aptr} (hs : Smatch bc m b p) :
    Bmatch bc m b (ablockInit p) := by
  refine ⟨hs, fun chunk ofs v hl => ?_⟩
  simp only [ablockLoad, ablockInit, ZTree.get, ZTree.empty, PTree.gempty]
  exact vnormalize_cast hl (hs.1 _ _ _ hl)

/-- `ValueDomain.ablock_store_anywhere_sound` -/
theorem ablock_store_anywhere_sound {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val}
    {m' : Mem} {b' : Block} {ab : Ablock} {av : Aval}
    (hs : Mem.store chunk m b ofs v = some m') (hb : Bmatch bc m b' ab) (hv : Vmatch bc v av) :
    Bmatch bc m' b' (ablockStoreAnywhere chunk ab av) :=
  ablock_init_sound (smatch_store hs hb.1 hv)

/-- `ValueDomain.ablock_loadbytes_sound` -/
theorem ablock_loadbytes_sound {m : Mem} {b : Block} {ab : Ablock} {b' : Block}
    {ofs' : Integers.Ptrofs} {q : Quantity} {i : Nat} {n ofs : Z} {bytes : List MemVal}
    (hl : Mem.loadbytes m b ofs n = some bytes) (hb : Bmatch bc m b ab)
    (hin : MemVal.Fragment (.Vptr b' ofs') q i ∈ bytes) :
    Pmatch bc b' ofs' (ablockLoadbytes ab) :=
  smatch_loadbytes hl hb.1 hin

/-- `ValueDomain.ablock_storebytes_anywhere_sound` -/
theorem ablock_storebytes_anywhere_sound {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal}
    {p : Aptr} {m' : Mem} {b' : Block} {ab : Ablock}
    (hs : Mem.storebytes m b ofs bytes = some m')
    (hc : ∀ b' ofs' q i, MemVal.Fragment (.Vptr b' ofs') q i ∈ bytes → Pmatch bc b' ofs' p)
    (hb : Bmatch bc m b' ab) : Bmatch bc m' b' (ablockStorebytesAnywhere ab p) :=
  ablock_init_sound (smatch_storebytes hs hb.1 hc)

/-! ## Contents of abstract blocks after stores -/

theorem ZTree.gss' {A : Type} (i : Z) (v : A) (m : ZTree A) : ZTree.get i (ZTree.set i v m) = some v := by
  simp [ZTree.get, ZTree.set]

theorem ZTree.gso' {A : Type} {i j : Z} (v : A) (m : ZTree A) (h : i ≠ j) :
    ZTree.get j (ZTree.set i v m) = ZTree.get j m :=
  PTree.gso _ _ _ _ (fun e => h (ZIndexed.index_inj e))

theorem ZTree.gro' {A : Type} {i j : Z} (m : ZTree A) (h : i ≠ j) :
    ZTree.get j (ZTree.remove i m) = ZTree.get j m :=
  PTree.gro _ _ _ (fun e => h (ZIndexed.index_inj e))

theorem ZTree.grs' {A : Type} (i : Z) (m : ZTree A) : ZTree.get i (ZTree.remove i m) = none :=
  PTree.grs _ _

private theorem invalAfter_go {i : Z} {x : Acontent} :
    ∀ (n : Nat) (lo : Z) (c : ZTree Acontent),
    ZTree.get i (countedUp.go (fun i c => ZTree.remove i c) n lo c) = some x →
    ZTree.get i c = some x ∧ (i < lo ∨ i ≥ lo + n) := by
  intro n
  induction n with
  | zero => intro lo c h; exact ⟨h, by zomega⟩
  | succ n ih =>
    intro lo c h
    obtain ⟨h1, h2⟩ := ih (lo + 1) _ h
    by_cases he : lo = i
    · subst he; rw [ZTree.grs'] at h1; cases h1
    · rw [ZTree.gro' _ he] at h1
      exact ⟨h1, by zomega⟩

/-- `ValueDomain.inval_after_contents` -/
theorem inval_after_contents {chunk : Chunk} {av : Aval} {i lo hi : Z} {c : ZTree Acontent}
    (h : ZTree.get i (invalAfter lo hi c) = some (.ACval chunk av)) :
    ZTree.get i c = some (.ACval chunk av) ∧ (i < lo ∨ i ≥ hi) := by
  obtain ⟨h1, h2⟩ := invalAfter_go _ _ _ h
  exact ⟨h1, by zomega⟩

theorem invalIf_other {hi lo j : Z} {c : ZTree Acontent} (h : j ≠ lo) :
    ZTree.get j (invalIf hi lo c) = ZTree.get j c := by
  unfold invalIf
  split
  · rfl
  · split
    · rfl
    · exact ZTree.gro' _ (Ne.symm h)

theorem invalIf_same {hi lo : Z} {c : ZTree Acontent} {chunk : Chunk} {av : Aval}
    (h : ZTree.get lo (invalIf hi lo c) = some (.ACval chunk av)) :
    ZTree.get lo c = some (.ACval chunk av) ∧ lo + sizeChunk chunk ≤ hi := by
  unfold invalIf at h
  split at h
  · rename_i hn; rw [hn] at h; cases h
  · rename_i ch av' hc
    split at h
    · rw [hc] at h ⊢; cases h; exact ⟨rfl, ‹_›⟩
    · rw [ZTree.grs'] at h; cases h

private theorem invalBefore_go_outside {i hi : Z} :
    ∀ (n : Nat) (lo : Z) (c : ZTree Acontent), (i < lo ∨ i ≥ lo + n) →
    ZTree.get i (countedUp.go (invalIf hi) n lo c) = ZTree.get i c := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro lo c h
    show ZTree.get i (countedUp.go (invalIf hi) n (lo + 1) (invalIf hi lo c)) = _
    rw [ih (lo + 1) _ (by zomega), invalIf_other (by zomega)]

/-- `ValueDomain.inval_before_outside` -/
theorem inval_before_outside {i hi lo : Z} {c : ZTree Acontent} (h : i < lo ∨ i ≥ hi) :
    ZTree.get i (invalBefore hi lo c) = ZTree.get i c :=
  invalBefore_go_outside _ _ _ (by zomega)

private theorem invalBefore_go_contents {i hi : Z} {chunk : Chunk} {av : Aval} :
    ∀ (n : Nat) (lo : Z) (c : ZTree Acontent),
    ZTree.get i (countedUp.go (invalIf hi) n lo c) = some (.ACval chunk av) →
    ZTree.get i c = some (.ACval chunk av) ∧ (lo ≤ i → i < lo + n → i + sizeChunk chunk ≤ hi) := by
  intro n
  induction n with
  | zero => intro lo c h; exact ⟨h, fun h1 h2 => by zomega⟩
  | succ n ih =>
    intro lo c h
    obtain ⟨h1, h2⟩ := ih (lo + 1) _ h
    by_cases he : i = lo
    · subst he
      obtain ⟨h3, h4⟩ := invalIf_same h1
      exact ⟨h3, fun _ _ => h4⟩
    · rw [invalIf_other he] at h1
      exact ⟨h1, fun a b => h2 (by zomega) (by zomega)⟩

/-- `ValueDomain.inval_before_contents_1` -/
theorem inval_before_contents_1 {i : Z} {chunk : Chunk} {av : Aval} {lo hi : Z}
    {c : ZTree Acontent} (hr : lo ≤ i ∧ i < hi)
    (h : ZTree.get i (invalBefore hi lo c) = some (.ACval chunk av)) :
    ZTree.get i c = some (.ACval chunk av) ∧ i + sizeChunk chunk ≤ hi := by
  obtain ⟨h1, h2⟩ := invalBefore_go_contents _ _ _ h
  exact ⟨h1, h2 hr.1 (by zomega)⟩

/-- `ValueDomain.max_size_chunk` -/
theorem max_size_chunk (chunk : Chunk) : sizeChunk chunk ≤ 8 := by
  cases chunk <;> decide

/-- `ValueDomain.inval_before_contents` -/
theorem inval_before_contents {i : Z} {c : ZTree Acontent} {chunk' : Chunk} {av' : Aval} {j : Z}
    (h : ZTree.get j (invalBefore i (i - 7) c) = some (.ACval chunk' av')) :
    ZTree.get j c = some (.ACval chunk' av') ∧ (j + sizeChunk chunk' ≤ i ∨ i ≤ j) := by
  have hm := max_size_chunk chunk'
  by_cases h1 : j < i - 7
  · rw [inval_before_outside (.inl h1)] at h
    exact ⟨h, .inl (by zomega)⟩
  · by_cases h2 : j < i
    · obtain ⟨h3, h4⟩ := inval_before_contents_1 ⟨by zomega, h2⟩ h
      exact ⟨h3, .inl h4⟩
    · rw [inval_before_outside (.inr (by zomega))] at h
      exact ⟨h, .inr (by zomega)⟩

/-- `ValueDomain.ablock_store_contents` -/
theorem ablock_store_contents {chunk : Chunk} {ab : Ablock} {i : Z} {av : Aval} {j : Z}
    {chunk' : Chunk} {av' : Aval}
    (h : ZTree.get j (ablockStore chunk ab i av).ab_contents = some (.ACval chunk' av')) :
    (i = j ∧ chunk' = chunk ∧ av' = av) ∨
    (ZTree.get j ab.ab_contents = some (.ACval chunk' av') ∧
      (j + sizeChunk chunk' ≤ i ∨ i + sizeChunk chunk ≤ j)) := by
  simp only [ablockStore] at h
  by_cases he : i = j
  · subst he
    rw [ZTree.gss'] at h
    cases h
    exact .inl ⟨rfl, rfl, rfl⟩
  · right
    rw [ZTree.gso' _ _ he] at h
    obtain ⟨A, B⟩ := inval_before_contents h
    obtain ⟨C, D⟩ := inval_after_contents A
    exact ⟨C, by zomega⟩

/-- `ValueDomain.chunk_compat_true` -/
theorem chunk_compat_true {c c' : Chunk} (h : chunkCompat c c' = true) :
    sizeChunk c = sizeChunk c' ∧ alignChunk c ≤ alignChunk c' ∧ c.typ = c'.typ := by
  cases c <;> cases c' <;> simp [chunkCompat] at h <;> decide

/-- `ValueDomain.ablock_store_sound` -/
theorem ablock_store_sound {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val} {m' : Mem}
    {ab : Ablock} {av : Aval}
    (hs : Mem.store chunk m b ofs v = some m') (hb : Bmatch bc m b ab) (hv : Vmatch bc v av) :
    Bmatch bc m' b (ablockStore chunk ab ofs av) := by
  have SM := smatch_store hs hb.1 hv
  refine ⟨SM, fun chunk' ofs' v' hl => ?_⟩
  have SUMMARY : Vmatch bc v' (vnormalize chunk' (.Ifptr (vplub av ab.ab_summary))) :=
    vnormalize_cast hl (SM.1 _ _ _ hl)
  unfold ablockLoad
  split
  · exact SUMMARY
  · rename_i chunk1 av1 C
    split
    · rename_i COMPAT
      obtain ⟨U, V, W⟩ := chunk_compat_true COMPAT
      rcases ablock_store_contents C with ⟨rfl, rfl, rfl⟩ | ⟨P, Q⟩
      · rw [Mem.load_store_similar_2 hs U V W] at hl
        cases hl
        exact vnormalize_sound _ hv
      · have hl' : Mem.load chunk' m b ofs' = some v' := by
          rw [← hl]
          exact (Mem.load_store_other hs chunk' b ofs' (.inr (by rw [U]; exact Q))).symm
        have := hb.2 _ _ _ hl'
        unfold ablockLoad at this
        rw [P] at this
        simp only [COMPAT, if_true] at this
        exact this
    · exact SUMMARY

/-- `ValueDomain.ablock_storebytes_contents` -/
theorem ablock_storebytes_contents {ab : Ablock} {p : Aptr} {i sz j : Z} {chunk' : Chunk}
    {av' : Aval}
    (h : ZTree.get j (ablockStorebytes ab p i sz).ab_contents = some (.ACval chunk' av')) :
    ZTree.get j ab.ab_contents = some (.ACval chunk' av') ∧
      (j + sizeChunk chunk' ≤ i ∨ i + max sz 0 ≤ j) := by
  simp only [ablockStorebytes] at h
  obtain ⟨A, B⟩ := inval_before_contents h
  obtain ⟨C, D⟩ := inval_after_contents A
  refine ⟨C, ?_⟩
  rcases B with B | B
  · exact .inl B
  · right
    have : max sz 0 = sz ∨ max sz 0 = 0 := by
      simp only [Z] at *; omega
    zomega

/-- `ValueDomain.ablock_storebytes_sound` -/
theorem ablock_storebytes_sound {m : Mem} {b : Block} {ofs : Z} {bytes : List MemVal} {m' : Mem}
    {p : Aptr} {ab : Ablock} {sz : Z}
    (hs : Mem.storebytes m b ofs bytes = some m') (hlen : bytes.length = sz.toNat)
    (hc : ∀ b' ofs' q i, MemVal.Fragment (.Vptr b' ofs') q i ∈ bytes → Pmatch bc b' ofs' p)
    (hb : Bmatch bc m b ab) : Bmatch bc m' b (ablockStorebytes ab p ofs sz) := by
  have SM := smatch_storebytes hs hb.1 hc
  refine ⟨SM, fun chunk' ofs' v' hl => ?_⟩
  have SUMMARY : Vmatch bc v' (vnormalize chunk' (.Ifptr (plub p ab.ab_summary))) :=
    vnormalize_cast hl (SM.1 _ _ _ hl)
  unfold ablockLoad
  split
  · exact SUMMARY
  · rename_i chunk1 av1 C
    split
    · rename_i COMPAT
      obtain ⟨U, _, _⟩ := chunk_compat_true COMPAT
      obtain ⟨A, B⟩ := ablock_storebytes_contents C
      have hl' : Mem.load chunk' m b ofs' = some v' := by
        rw [← hl]
        refine (Mem.load_storebytes_other hs chunk' b ofs' (.inr ?_)).symm
        rw [U, hlen]
        have : max sz 0 = sz ∨ max sz 0 = 0 := by simp only [Z] at *; omega
        zomega
      have := hb.2 _ _ _ hl'
      unfold ablockLoad at this
      rw [A] at this
      simp only [COMPAT, if_true] at this
      exact this
    · exact SUMMARY

/-- `ValueDomain.smatch_lub_l` -/
theorem smatch_lub_l {m : Mem} {b : Block} {p : Aptr} (q : Aptr) (hs : Smatch bc m b p) :
    Smatch bc m b (plub p q) :=
  smatch_ge hs (pge_lub_l p q)

/-- `ValueDomain.smatch_lub_r` -/
theorem smatch_lub_r {m : Mem} {b : Block} (p : Aptr) {q : Aptr} (hs : Smatch bc m b q) :
    Smatch bc m b (plub p q) :=
  smatch_ge hs (pge_lub_r p q)

theorem ptreeBeq_leaf_l {A : Type} (cmp : A → A → Bool) :
    ∀ (t : PTree A), ptreeBeq cmp .Leaf t = true → ∀ i, PTree.get i t = none
  | .Leaf, _, i => PTree.get_leaf i
  | .Node l o r, h, i => by
    simp only [ptreeBeq, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨ho, hl⟩, hr⟩ := h
    cases i with
    | xH => exact ho
    | xO i => exact ptreeBeq_leaf_l cmp l hl i
    | xI i => exact ptreeBeq_leaf_l cmp r hr i

theorem ptreeBeq_leaf_r {A : Type} (cmp : A → A → Bool) :
    ∀ (t : PTree A), ptreeBeq cmp t .Leaf = true → ∀ i, PTree.get i t = none
  | .Leaf, _, i => PTree.get_leaf i
  | .Node l o r, h, i => by
    simp only [ptreeBeq, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨ho, hl⟩, hr⟩ := h
    cases i with
    | xH => exact ho
    | xO i => exact ptreeBeq_leaf_r cmp l hl i
    | xI i => exact ptreeBeq_leaf_r cmp r hr i

/-- `PTree.beq_sound`, for the boolean equality of values. -/
theorem ptreeBeq_eq {A : Type} [DecidableEq A] :
    ∀ (t1 t2 : PTree A), ptreeBeq (fun a b => decide (a = b)) t1 t2 = true →
    ∀ i, PTree.get i t1 = PTree.get i t2
  | .Leaf, t2, h, i => by rw [PTree.get_leaf, ptreeBeq_leaf_l _ t2 h i]
  | .Node l o r, .Leaf, h, i => by rw [PTree.get_leaf, ptreeBeq_leaf_r _ _ h i]
  | .Node l1 o1 r1, .Node l2 o2 r2, h, i => by
    unfold ptreeBeq at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ho, hl⟩, hr⟩ := h
    cases i with
    | xH =>
      show o1 = o2
      cases o1 <;> cases o2 <;> simp_all
    | xO i => exact ptreeBeq_eq l1 l2 hl i
    | xI i => exact ptreeBeq_eq r1 r2 hr i

/-- `ValueDomain.bbeq_load` -/
theorem bbeq_load {ab1 ab2 : Ablock} (h : bbeq ab1 ab2 = true) :
    ab1.ab_summary = ab2.ab_summary ∧ ∀ chunk i, ablockLoad chunk ab1 i = ablockLoad chunk ab2 i := by
  simp only [bbeq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, hc⟩ := h
  refine ⟨hs, fun chunk i => ?_⟩
  unfold ablockLoad
  rw [show ZTree.get i ab1.ab_contents = ZTree.get i ab2.ab_contents from
    ptreeBeq_eq _ _ hc _, hs]

/-- `ValueDomain.bbeq_sound` -/
theorem bbeq_sound {ab1 ab2 : Ablock} (h : bbeq ab1 ab2 = true) (m : Mem) (b : Block) :
    Bmatch bc m b ab1 ↔ Bmatch bc m b ab2 := by
  obtain ⟨A, B⟩ := bbeq_load h
  unfold Bmatch
  rw [A]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun chunk ofs v hl => B chunk ofs ▸ h2 chunk ofs v hl⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun chunk ofs v hl => (B chunk ofs).symm ▸ h2 chunk ofs v hl⟩

/-- `ValueDomain.bmatch_lub_l` -/
theorem bmatch_lub_l (strict : Bool) {m : Mem} {b : Block} {x : Ablock} (y : Ablock)
    (hb : Bmatch bc m b x) : Bmatch bc m b (blub strict x y) := by
  refine ⟨smatch_lub_l _ hb.1, fun chunk ofs v hl => ?_⟩
  have SUMMARY : Vmatch bc v (vnormalize chunk (.Ifptr (plub x.ab_summary y.ab_summary))) :=
    vnormalize_cast hl ((smatch_lub_l y.ab_summary hb.1).1 _ _ _ hl)
  have H := hb.2 _ _ _ hl
  unfold ablockLoad at H ⊢
  simp only [blub, ZTree.get] at H ⊢
  rw [PTree.gcombine _ rfl]
  generalize PTree.get (ZIndexed.index ofs) x.ab_contents = cx at H ⊢
  generalize PTree.get (ZIndexed.index ofs) y.ab_contents = cy
  rcases cx with _ | ⟨chx, avx⟩ <;> rcases cy with _ | ⟨chy, avy⟩ <;>
    simp only [combineAcontents] <;> try exact SUMMARY
  by_cases he : chx = chy
  · subst he
    simp only [if_true]
    dsimp only at H ⊢
    split
    · rename_i COMPAT
      simp only [COMPAT, if_true] at H
      exact vmatch_ge (vnormalize_monotone _ (vge_lub_l _ _ _)) H
    · exact SUMMARY
  · simp only [he, if_false]
    exact SUMMARY

/-- `ValueDomain.bmatch_lub_r` -/
theorem bmatch_lub_r (strict : Bool) {m : Mem} {b : Block} (x : Ablock) {y : Ablock}
    (hb : Bmatch bc m b y) : Bmatch bc m b (blub strict x y) := by
  refine ⟨smatch_lub_r _ hb.1, fun chunk ofs v hl => ?_⟩
  have SUMMARY : Vmatch bc v (vnormalize chunk (.Ifptr (plub x.ab_summary y.ab_summary))) :=
    vnormalize_cast hl ((smatch_lub_r x.ab_summary hb.1).1 _ _ _ hl)
  have H := hb.2 _ _ _ hl
  unfold ablockLoad at H ⊢
  simp only [blub, ZTree.get] at H ⊢
  rw [PTree.gcombine _ rfl]
  generalize PTree.get (ZIndexed.index ofs) y.ab_contents = cy at H ⊢
  generalize PTree.get (ZIndexed.index ofs) x.ab_contents = cx
  rcases cx with _ | ⟨chx, avx⟩ <;> rcases cy with _ | ⟨chy, avy⟩ <;>
    simp only [combineAcontents] <;> try exact SUMMARY
  by_cases he : chx = chy
  · subst he
    simp only [if_true]
    dsimp only at H ⊢
    split
    · rename_i COMPAT
      simp only [COMPAT, if_true] at H
      exact vmatch_ge (vnormalize_monotone _ (vge_lub_r _ _ _)) H
    · exact SUMMARY
  · simp only [he, if_false]
    exact SUMMARY

end ValueDomain
end CC
