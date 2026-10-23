/-
  `common/Memdata.v`, lines 511–806: what can be said about reading back a value
  with a *different* chunk than it was stored with (`decode_encode_val`),
  typing and cast properties of `decode_val`, and the "pointers cannot be
  forged" shape lemmas.
-/
import CCLib.common.MemdataTheory

namespace CC

/-- `Memdata.decode_encode_val`: the relation between a value `v1` stored with
    `chunk1` and the value `v2` read back with `chunk2`.  Where nothing
    meaningful can be said the relation is `True`. -/
def decodeEncodeVal (v1 : Val) (chunk1 chunk2 : Chunk) (v2 : Val) : Prop :=
  match v1, chunk1, chunk2 with
  | .Vundef, _, _ => v2 = .Vundef
  | .Vint n, .Mbool, .Mint8signed | .Vint n, .Mint8signed, .Mint8signed
  | .Vint n, .Mint8unsigned, .Mint8signed => v2 = .Vint (Integers.Int.sign_ext 8 n)
  | .Vint n, .Mbool, .Mint8unsigned | .Vint n, .Mint8signed, .Mint8unsigned
  | .Vint n, .Mint8unsigned, .Mint8unsigned => v2 = .Vint (Integers.Int.zero_ext 8 n)
  | .Vint n, .Mbool, .Mbool | .Vint n, .Mint8signed, .Mbool
  | .Vint n, .Mint8unsigned, .Mbool => v2 = Val.normBool (.Vint (Integers.Int.zero_ext 8 n))
  | .Vint n, .Mint16signed, .Mint16signed => v2 = .Vint (Integers.Int.sign_ext 16 n)
  | .Vint n, .Mint16unsigned, .Mint16signed => v2 = .Vint (Integers.Int.sign_ext 16 n)
  | .Vint n, .Mint16signed, .Mint16unsigned => v2 = .Vint (Integers.Int.zero_ext 16 n)
  | .Vint n, .Mint16unsigned, .Mint16unsigned => v2 = .Vint (Integers.Int.zero_ext 16 n)
  | .Vint n, .Mint32, .Mint32 => v2 = .Vint n
  | .Vint n, .Many32, .Many32 => v2 = .Vint n
  | .Vint n, .Mint32, .Mfloat32 => v2 = .Vsingle (Floats.Float32.ofBits n)
  | .Vint n, .Many64, .Many64 => v2 = .Vint n
  | .Vint _, .Mint64, _ | .Vint _, .Mfloat32, _ | .Vint _, .Mfloat64, _
  | .Vint _, .Many64, _ => v2 = .Vundef
  | .Vint _, _, _ => True
  | .Vptr b ofs, .Mint32, .Mint32 | .Vptr b ofs, .Mint32, .Many32
  | .Vptr b ofs, .Many32, .Mint32 | .Vptr b ofs, .Many32, .Many32 =>
      v2 = if Archi.ptr64 then .Vundef else .Vptr b ofs
  | .Vptr b ofs, .Mint64, .Mint64 | .Vptr b ofs, .Mint64, .Many64 =>
      v2 = if Archi.ptr64 then .Vptr b ofs else .Vundef
  | .Vptr b ofs, .Many64, .Many64 => v2 = .Vptr b ofs
  | .Vptr b ofs, .Many64, .Mint64 => v2 = if Archi.ptr64 then .Vptr b ofs else .Vundef
  | .Vptr _ _, _, _ => v2 = .Vundef
  | .Vlong n, .Mint64, .Mint64 => v2 = .Vlong n
  | .Vlong n, .Mint64, .Mfloat64 => v2 = .Vfloat (Floats.Float.ofBits n)
  | .Vlong n, .Many64, .Many64 => v2 = .Vlong n
  | .Vlong _, .Mbool, _ | .Vlong _, .Mint8signed, _ | .Vlong _, .Mint8unsigned, _
  | .Vlong _, .Mint16signed, _ | .Vlong _, .Mint16unsigned, _ | .Vlong _, .Mint32, _
  | .Vlong _, .Mfloat32, _ | .Vlong _, .Mfloat64, _ | .Vlong _, .Many32, _ => v2 = .Vundef
  | .Vlong _, _, _ => True
  | .Vfloat f, .Mfloat64, .Mfloat64 => v2 = .Vfloat f
  | .Vfloat f, .Mfloat64, .Mint64 => v2 = .Vlong (Floats.Float.toBits f)
  | .Vfloat f, .Many64, .Many64 => v2 = .Vfloat f
  | .Vfloat _, .Mbool, _ | .Vfloat _, .Mint8signed, _ | .Vfloat _, .Mint8unsigned, _
  | .Vfloat _, .Mint16signed, _ | .Vfloat _, .Mint16unsigned, _ | .Vfloat _, .Mint32, _
  | .Vfloat _, .Mfloat32, _ | .Vfloat _, .Mint64, _ | .Vfloat _, .Many32, _ => v2 = .Vundef
  | .Vfloat _, _, _ => True
  | .Vsingle f, .Mfloat32, .Mfloat32 => v2 = .Vsingle f
  | .Vsingle f, .Mfloat32, .Mint32 => v2 = .Vint (Floats.Float32.toBits f)
  | .Vsingle f, .Many32, .Many32 => v2 = .Vsingle f
  | .Vsingle f, .Many64, .Many64 => v2 = .Vsingle f
  | .Vsingle _, .Mbool, _ | .Vsingle _, .Mint8signed, _ | .Vsingle _, .Mint8unsigned, _
  | .Vsingle _, .Mint16signed, _ | .Vsingle _, .Mint16unsigned, _ | .Vsingle _, .Mint32, _
  | .Vsingle _, .Mint64, _ | .Vsingle _, .Mfloat64, _ | .Vsingle _, .Many64, _ => v2 = .Vundef
  | .Vsingle _, _, _ => True

private theorem sign_ext_zero_ext_8 (n : Integers.Int) :
    Integers.Int.sign_ext 8 (Integers.Int.zero_ext 8 n) = Integers.Int.sign_ext 8 n :=
  Integers.Int.sign_ext_zero_ext (by decide) (Nat.le_refl 8) n

private theorem sign_ext_zero_ext_16 (n : Integers.Int) :
    Integers.Int.sign_ext 16 (Integers.Int.zero_ext 16 n) = Integers.Int.sign_ext 16 n :=
  Integers.Int.sign_ext_zero_ext (by decide) (Nat.le_refl 16) n

private theorem zero_ext_idem' (k : Nat) (n : Integers.Int) :
    Integers.Int.zero_ext k (Integers.Int.zero_ext k n) = Integers.Int.zero_ext k n := Integers.Int.zero_ext_idem k n

/-- `Memdata.decode_encode_val_general` -/
theorem decodeEncodeVal_general (v : Val) (chunk1 chunk2 : Chunk) :
    decodeEncodeVal v chunk1 chunk2 (decodeVal chunk2 (encodeVal chunk1 v)) := by
  cases v <;> cases chunk1 <;> cases chunk2 <;>
    simp [decodeEncodeVal, decodeVal, encodeVal, Val.loadResult, sizeChunkNat, sizeChunk,
      decode_encode_int_1, decode_encode_int_2, decode_encode_int_4, decode_encode_int_8,
      sign_ext_zero_ext_8, sign_ext_zero_ext_16, zero_ext_idem',
      projValue_injValue_mismatch]

/-- `Memdata.decode_encode_val_similar` -/
theorem decodeEncodeVal_similar {v1 : Val} {chunk1 chunk2 : Chunk} {v2 : Val}
    (hty : chunk1.typ = chunk2.typ) (hsz : sizeChunk chunk1 = sizeChunk chunk2)
    (h : decodeEncodeVal v1 chunk1 chunk2 v2) : v2 = Val.loadResult chunk2 v1 := by
  cases chunk1 <;> cases chunk2 <;> simp [Chunk.typ, sizeChunk] at hty hsz <;>
    cases v1 <;> simpa [decodeEncodeVal, Val.loadResult] using h

/-- `Memdata.decode_val_xtype` -/
theorem decodeVal_xtype (chunk : Chunk) (cl : List MemVal) :
    Val.hasRettype (decodeVal chunk cl) chunk.xtype :=
  EventsProps.decodeVal_hasRettype chunk cl

/-- `Memdata.decode_val_type` -/
theorem decodeVal_type (chunk : Chunk) (cl : List MemVal) :
    Val.HasType (decodeVal chunk cl) chunk.typ := by
  rw [← Chunk.proj_xtype]; exact Val.has_proj_xtype (EventsProps.decodeVal_hasRettype chunk cl)

/-- `Memdata.encode_val_int8_signed_unsigned` -/
theorem encodeVal_int8_signed_unsigned (v : Val) :
    encodeVal .Mint8signed v = encodeVal .Mint8unsigned v := by
  cases v <;> rfl

/-- `Memdata.encode_val_int16_signed_unsigned` -/
theorem encodeVal_int16_signed_unsigned (v : Val) :
    encodeVal .Mint16signed v = encodeVal .Mint16unsigned v := by
  cases v <;> rfl

private theorem unsigned_zero_ext_8 (n : Integers.Int) :
    Integers.Int.unsigned (Integers.Int.zero_ext 8 n) % 256 = Integers.Int.unsigned n % 256 := by
  rw [Integers.Int.zero_ext_mod]; exact _root_.Int.emod_emod_of_dvd _ (_root_.Int.dvd_refl _)

private theorem unsigned_zero_ext_16 (n : Integers.Int) :
    Integers.Int.unsigned (Integers.Int.zero_ext 16 n) % 65536 = Integers.Int.unsigned n % 65536 := by
  rw [Integers.Int.zero_ext_mod]; exact _root_.Int.emod_emod_of_dvd _ (_root_.Int.dvd_refl _)

private theorem unsigned_sign_ext_8 (n : Integers.Int) :
    Integers.Int.unsigned (Integers.Int.sign_ext 8 n) % 256 = Integers.Int.unsigned n % 256 := by
  have h := congrArg Integers.Int.unsigned (Integers.Int.zero_ext_sign_ext (n := 8) (n' := 8)
    (by decide) (Nat.le_refl 8) n)
  rw [Integers.Int.zero_ext_mod, Integers.Int.zero_ext_mod] at h
  exact h

private theorem unsigned_sign_ext_16 (n : Integers.Int) :
    Integers.Int.unsigned (Integers.Int.sign_ext 16 n) % 65536 = Integers.Int.unsigned n % 65536 := by
  have h := congrArg Integers.Int.unsigned (Integers.Int.zero_ext_sign_ext (n := 16) (n' := 16)
    (by decide) (Nat.le_refl 16) n)
  rw [Integers.Int.zero_ext_mod, Integers.Int.zero_ext_mod] at h
  exact h

/-- `Memdata.encode_val_int8_zero_ext` -/
theorem encodeVal_int8_zero_ext (n : Integers.Int) :
    encodeVal .Mint8unsigned (.Vint (Integers.Int.zero_ext 8 n)) = encodeVal .Mint8unsigned (.Vint n) := by
  simp only [encodeVal]; rw [encodeInt_8_mod _ _ (unsigned_zero_ext_8 n)]

/-- `Memdata.encode_val_int8_sign_ext` -/
theorem encodeVal_int8_sign_ext (n : Integers.Int) :
    encodeVal .Mint8signed (.Vint (Integers.Int.sign_ext 8 n)) = encodeVal .Mint8signed (.Vint n) := by
  simp only [encodeVal]; rw [encodeInt_8_mod _ _ (unsigned_sign_ext_8 n)]

/-- `Memdata.encode_val_int16_zero_ext` -/
theorem encodeVal_int16_zero_ext (n : Integers.Int) :
    encodeVal .Mint16unsigned (.Vint (Integers.Int.zero_ext 16 n))
      = encodeVal .Mint16unsigned (.Vint n) := by
  simp only [encodeVal]; rw [encodeInt_16_mod _ _ (unsigned_zero_ext_16 n)]

/-- `Memdata.encode_val_int16_sign_ext` -/
theorem encodeVal_int16_sign_ext (n : Integers.Int) :
    encodeVal .Mint16signed (.Vint (Integers.Int.sign_ext 16 n)) = encodeVal .Mint16signed (.Vint n) := by
  simp only [encodeVal]; rw [encodeInt_16_mod _ _ (unsigned_sign_ext_16 n)]

private theorem signExt_idem_of {k : Nat} (hk : 0 < k) {v : Val}
    (h : v = .Vundef ∨ ∃ x, v = .Vint (Integers.Int.sign_ext k x)) : v = Val.signExt k v := by
  rcases h with rfl | ⟨x, rfl⟩
  · rfl
  · simp only [Val.signExt]; rw [Integers.Int.sign_ext_idem hk]

private theorem zeroExt_idem_of {k : Nat} {v : Val}
    (h : v = .Vundef ∨ ∃ x, v = .Vint (Integers.Int.zero_ext k x)) : v = Val.zeroExt k v := by
  rcases h with rfl | ⟨x, rfl⟩
  · rfl
  · simp only [Val.zeroExt]; rw [Integers.Int.zero_ext_idem]

/-- `Memdata.decode_val_cast`: small-integer loads are already normalised. -/
theorem decodeVal_cast (chunk : Chunk) (l : List MemVal) :
    match chunk with
    | .Mbool => decodeVal chunk l = Val.normBool (decodeVal chunk l)
    | .Mint8signed => decodeVal chunk l = Val.signExt 8 (decodeVal chunk l)
    | .Mint8unsigned => decodeVal chunk l = Val.zeroExt 8 (decodeVal chunk l)
    | .Mint16signed => decodeVal chunk l = Val.signExt 16 (decodeVal chunk l)
    | .Mint16unsigned => decodeVal chunk l = Val.zeroExt 16 (decodeVal chunk l)
    | _ => True := by
  cases chunk
  case Mbool =>
    show decodeVal .Mbool l = Val.normBool (decodeVal .Mbool l)
    unfold decodeVal
    split
    · rw [Val.norm_bool_idem]
    · rfl
  case Mint8signed =>
    apply signExt_idem_of (by decide)
    unfold decodeVal; split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  case Mint8unsigned =>
    apply zeroExt_idem_of
    unfold decodeVal; split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  case Mint16signed =>
    apply signExt_idem_of (by decide)
    unfold decodeVal; split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  case Mint16unsigned =>
    apply zeroExt_idem_of
    unfold decodeVal; split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  all_goals trivial

/-! ## Pointers cannot be forged -/

/-- `Memdata.shape_encoding`: the shape of the bytes `encode_val chunk v`. -/
inductive ShapeEncoding (chunk : Chunk) (v : Val) : List MemVal → Prop where
  | f (q : Quantity) (i : Nat) (mvl : List MemVal) :
      (chunk = .Mint32 ∨ chunk = .Many32 ∨ chunk = .Mint64 ∨ chunk = .Many64) →
      q = quantityChunk chunk →
      i + 1 = sizeQuantityNat q →
      (∀ mv ∈ mvl, ∃ j, mv = .Fragment v q j ∧ j + 1 ≠ sizeQuantityNat q) →
      ShapeEncoding chunk v (.Fragment v q i :: mvl)
  | b (b : Byte) (mvl : List MemVal) :
      (match v with
        | .Vint _ | .Vlong _ | .Vfloat _ | .Vsingle _ => True
        | _ => False) →
      (∀ mv ∈ mvl, ∃ b', mv = .Byte b') →
      ShapeEncoding chunk v (.Byte b :: mvl)
  | u (mvl : List MemVal) :
      (∀ mv ∈ mvl, mv = .Undef) →
      ShapeEncoding chunk v (.Undef :: mvl)

private theorem mem_injValueRec_lt {v : Val} {q : Quantity} {mv : MemVal} :
    ∀ n, n < sizeQuantityNat q → mv ∈ injValueRec n v q →
      ∃ j, mv = .Fragment v q j ∧ j + 1 ≠ sizeQuantityNat q
  | 0, _, h => by cases h
  | n + 1, hn, h => by
      simp only [injValueRec, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨n, h, by omega⟩
      · exact mem_injValueRec_lt n (by omega) h

private theorem shapeEncoding_injValue {chunk : Chunk} {v : Val} {q : Quantity}
    (hq : q = quantityChunk chunk)
    (hc : chunk = .Mint32 ∨ chunk = .Many32 ∨ chunk = .Mint64 ∨ chunk = .Many64) :
    ShapeEncoding chunk v (injValue q v) := by
  obtain ⟨n, hn⟩ := sizeQuantityNat_pos q
  unfold injValue
  rw [hn, injValueRec]
  exact .f q n _ hc hq hn.symm
    (fun mv h => mem_injValueRec_lt n (by omega) h)

private theorem shapeEncoding_injBytes {chunk : Chunk} {v : Val} {bl : List Byte}
    (hv : match v with
      | .Vint _ | .Vlong _ | .Vfloat _ | .Vsingle _ => True
      | _ => False)
    (hl : bl.length ≠ 0) : ShapeEncoding chunk v (injBytes bl) := by
  cases bl with
  | nil => exact absurd rfl hl
  | cons b bl =>
      refine .b b _ hv ?_
      intro mv h
      simp only [List.mem_map] at h
      obtain ⟨b', _, rfl⟩ := h
      exact ⟨b', rfl⟩

private theorem shapeEncoding_undef {chunk : Chunk} {v : Val} (n : Nat) :
    ShapeEncoding chunk v (List.replicate (n + 1) .Undef) :=
  .u _ (fun _ h => List.eq_of_mem_replicate h)

/-- `Memdata.encode_val_shape` -/
theorem encodeVal_shape (chunk : Chunk) (v : Val) : ShapeEncoding chunk v (encodeVal chunk v) := by
  cases v <;> cases chunk <;>
    simp only [encodeVal, Archi.ptr64_eq, if_true, sizeChunkNat, sizeChunk] <;>
    first
      | exact shapeEncoding_injValue rfl (by simp)
      | exact shapeEncoding_injBytes trivial (by simp)
      | exact shapeEncoding_undef _

/-- `Memdata.shape_decoding`: the shape of the bytes a value is decoded from. -/
inductive ShapeDecoding (chunk : Chunk) : List MemVal → Val → Prop where
  | f (v : Val) (q : Quantity) (i : Nat) (mvl : List MemVal) :
      (chunk = .Mint32 ∨ chunk = .Many32 ∨ chunk = .Mint64 ∨ chunk = .Many64) →
      q = quantityChunk chunk →
      i + 1 = sizeQuantityNat q →
      (∀ mv ∈ mvl, ∃ j, mv = .Fragment v q j ∧ j + 1 ≠ sizeQuantityNat q) →
      ShapeDecoding chunk (.Fragment v q i :: mvl) (Val.loadResult chunk v)
  | b (b : Byte) (mvl : List MemVal) (v : Val) :
      (match v with | .Vptr _ _ => False | _ => True) →
      (∀ mv ∈ mvl, ∃ b', mv = .Byte b') →
      ShapeDecoding chunk (.Byte b :: mvl) v
  | u (mvl : List MemVal) : ShapeDecoding chunk mvl .Vundef

private theorem checkValue_mem {v : Val} {q : Quantity} {mv : MemVal} :
    ∀ (n : Nat) (mvs : List MemVal), checkValue n v q mvs = true → mv ∈ mvs →
      n < sizeQuantityNat q → ∃ j, mv = .Fragment v q j ∧ j + 1 ≠ sizeQuantityNat q
  | 0, [], _, h, _ => by cases h
  | n + 1, .Fragment v' q' m' :: mvs, hc, hm, hn => by
      simp only [checkValue, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hc⟩ := hc
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨n, rfl, by omega⟩
      · exact checkValue_mem n mvs hc hm (by omega)
  | 0, _ :: _, hc, _, _ => by simp [checkValue] at hc
  | n + 1, [], hc, _, _ => by simp [checkValue] at hc
  | n + 1, .Undef :: _, hc, _, _ => by simp [checkValue] at hc
  | n + 1, .Byte _ :: _, hc, _, _ => by simp [checkValue] at hc

private theorem loadResult_undef (chunk : Chunk) : Val.loadResult chunk .Vundef = .Vundef := by
  cases chunk <;> rfl

private theorem shapeDecoding_projValue {chunk : Chunk} {q : Quantity} (mv1 : MemVal)
    (mvl : List MemVal) (hq : sizeQuantityNat q = sizeChunkNat chunk)
    (hc : chunk = .Mint32 ∨ chunk = .Many32 ∨ chunk = .Mint64 ∨ chunk = .Many64) :
    ShapeDecoding chunk (mv1 :: mvl) (Val.loadResult chunk (projValue q (mv1 :: mvl))) := by
  cases mv1 with
  | Fragment v q' i =>
      obtain ⟨n, hn⟩ := sizeQuantityNat_pos q
      simp only [projValue]
      split
      · rename_i hcv
        rw [hn] at hcv
        simp only [checkValue, Bool.and_eq_true, beq_iff_eq] at hcv
        obtain ⟨⟨⟨_, rfl⟩, rfl⟩, hcv⟩ := hcv
        refine .f v q n mvl hc ?_ hn.symm
          (fun mv h => checkValue_mem n mvl hcv h (by omega))
        rcases hc with rfl | rfl | rfl | rfl <;> cases q <;>
          first | rfl | (simp [sizeQuantityNat, sizeChunkNat, sizeChunk] at hq)
      · rw [loadResult_undef]; exact .u _
  | _ => simp only [projValue]; rw [loadResult_undef]; exact .u _

/-- `Memdata.decode_val_shape` -/
theorem decodeVal_shape (chunk : Chunk) (mv1 : MemVal) (mvl : List MemVal) :
    ShapeDecoding chunk (mv1 :: mvl) (decodeVal chunk (mv1 :: mvl)) := by
  unfold decodeVal
  split
  · rename_i bl hpb
    have heq := injBytes_projBytes hpb
    cases bl with
    | nil => cases heq
    | cons b bl =>
        simp only [injBytes, List.map_cons, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hall : ∀ mv ∈ List.map MemVal.Byte bl, ∃ b', mv = .Byte b' := by
          intro mv h
          simp only [List.mem_map] at h
          obtain ⟨b', _, rfl⟩ := h
          exact ⟨b', rfl⟩
        cases chunk
        case Mbool =>
          refine .b b _ _ ?_ hall
          generalize Integers.Int.zero_ext 8 _ = x
          unfold Val.normBool
          cases Val.isBool (.Vint x) <;> simp
        all_goals exact .b b _ _ trivial hall
  · cases chunk <;> simp only [Archi.ptr64_eq, if_true] <;>
      first
        | exact .u _
        | exact shapeDecoding_projValue mv1 mvl rfl (by simp)
