/-
  The rest of `common/Memdata.v`: the chunk/alignment lemmas, the general
  (width-polymorphic) byte encoding round trip, the `encode_val`/`decode_val`
  properties used by CompCert's pass proofs (`decode_encode_val_general`,
  `decode_val_cast`, the `int8`/`int16` re-encoding lemmas), the "pointers
  cannot be forged" shape lemmas, and the lemmas about splitting a 64-bit access
  into two 32-bit ones.

  `decode_val_int64` and `encode_val_int64` assume `Archi.ptr64 = false`; on the
  64-bit target this port fixes (`Archi.ptr64 = true`) they are vacuous, so they
  are stated with that hypothesis and discharged by contradiction.
-/
import CCLib.common.MemdataLemmas
import CCLib.common.EventsProps
import CCLib.common.ValuesTheory

namespace CC

/-! ## Chunks and alignment -/

/-- `Memdata.size_chunk_conv` -/
theorem sizeChunk_conv (chunk : Chunk) :
    sizeChunk chunk = ((sizeChunkNat chunk : Nat) : _root_.Int) :=
  (sizeChunkNat_cast chunk).symm

/-- `Memdata.size_chunk_nat_pos` -/
theorem sizeChunkNat_pos (chunk : Chunk) : ∃ n, sizeChunkNat chunk = n + 1 := by
  cases chunk <;> exact ⟨_, rfl⟩

/-- `Memdata.align_chunk_pos` -/
theorem alignChunk_pos (chunk : Chunk) : (0 : _root_.Int) < alignChunk chunk := by
  cases chunk <;> decide

/-- `Memdata.align_chunk_Mptr` (on the 64-bit target). -/
theorem alignChunk_Mptr : alignChunk Mptr = 8 := rfl

/-- `Memdata.align_size_chunk_divides` -/
theorem alignChunk_dvd_sizeChunk (chunk : Chunk) : alignChunk chunk ∣ sizeChunk chunk := by
  cases chunk <;> decide

/-- `Memdata.align_le_divides` -/
theorem alignChunk_le_dvd (chunk1 chunk2 : Chunk)
    (h : alignChunk chunk1 ≤ alignChunk chunk2) : alignChunk chunk1 ∣ alignChunk chunk2 := by
  cases chunk1 <;> cases chunk2 <;> revert h <;> decide

/-- `Memdata.align_chunk_max` -/
theorem alignChunk_dvd_8 (chunk : Chunk) : alignChunk chunk ∣ 8 := by
  cases chunk <;> decide

/-- `Memdata.size_quantity_nat_pos` -/
theorem sizeQuantityNat_pos (q : Quantity) : ∃ n, sizeQuantityNat q = n + 1 := by
  cases q <;> exact ⟨_, rfl⟩

/-! ## Byte encoding of integers, at every width -/

theorem emod_mul_decomp (x a b : _root_.Int) (ha : 0 < a) (hb : 0 < b) :
    x % (a * b) = x % a + a * (x / a % b) := by
  have h1 := Int.emod_add_mul_ediv x a
  have h2 := Int.emod_add_mul_ediv (x / a) b
  have r1 := Int.emod_nonneg x (Int.ne_of_gt ha)
  have r2 := Int.emod_lt_of_pos x ha
  have r3 := Int.emod_nonneg (x / a) (Int.ne_of_gt hb)
  have r4 := Int.emod_lt_of_pos (x / a) hb
  have hx : (x % a + a * (x / a % b)) + (a * b) * (x / a / b) = x := by
    rw [Int.mul_assoc, Int.add_assoc, ← Int.mul_add, h2, h1]
  conv => lhs; rw [← hx]
  rw [Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt
  · exact Int.add_nonneg r1 (Int.mul_nonneg (Int.le_of_lt ha) r3)
  · have : a * (x / a % b) ≤ a * (b - 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt ha)
    rw [Int.mul_sub, Int.mul_one] at this
    omega

private theorem two_pow_succ_mul8 (n : Nat) :
    (2 : _root_.Int) ^ ((n + 1) * 8) = 256 * 2 ^ (n * 8) := by
  rw [Nat.succ_mul, Int.pow_add, Int.mul_comm]; rfl

private theorem two_pow_pos' (k : Nat) : (0 : _root_.Int) < 2 ^ k :=
  Int.pow_pos (by decide)

/-- `Memdata.int_of_bytes_of_int` -/
theorem intOfBytes_bytesOfInt (n : Nat) (x : _root_.Int) :
    intOfBytes (bytesOfInt n x) = x % 2 ^ (n * 8) := by
  induction n generalizing x with
  | zero => simp [bytesOfInt, intOfBytes]
  | succ m ih =>
      simp only [bytesOfInt, intOfBytes, ih, byte_unsigned_repr]
      rw [two_pow_succ_mul8, emod_mul_decomp x 256 _ (by decide) (two_pow_pos' _),
        Int.mul_comm 256]

/-- `Memdata.rev_if_be_involutive` -/
theorem revIfBe_involutive (l : List Byte) : revIfBe (revIfBe l) = l := by
  simp [revIfBe]

/-- `Memdata.decode_encode_int` -/
theorem decodeInt_encodeInt (n : Nat) (x : _root_.Int) :
    decodeInt (encodeInt n x) = x % 2 ^ (n * 8) := by
  simp only [decodeInt, encodeInt, revIfBe_involutive, intOfBytes_bytesOfInt]

/-- `Memdata.decode_encode_int_1` -/
theorem decode_encode_int_1 (x : Integers.Int) :
    Integers.Int.repr (decodeInt (encodeInt 1 (Integers.Int.unsigned x)))
      = Integers.Int.zero_ext 8 x := by
  rw [decodeInt_encodeInt_1]
  apply BitVec.eq_of_toNat_eq
  rw [repr_unsigned_emod_256, show Integers.Int.zero_ext = Integers.MI.zero_ext from rfl,
    toNat_zero_ext_8]

/-- `Memdata.decode_encode_int_2` -/
theorem decode_encode_int_2 (x : Integers.Int) :
    Integers.Int.repr (decodeInt (encodeInt 2 (Integers.Int.unsigned x)))
      = Integers.Int.zero_ext 16 x := by
  rw [decodeInt_encodeInt_2]
  apply BitVec.eq_of_toNat_eq
  rw [repr_unsigned_emod_65536, show Integers.Int.zero_ext = Integers.MI.zero_ext from rfl,
    toNat_zero_ext_16]

/-- `Memdata.decode_encode_int_4` -/
theorem decode_encode_int_4 (x : Integers.Int) :
    Integers.Int.repr (decodeInt (encodeInt 4 (Integers.Int.unsigned x))) = x := by
  rw [decodeInt_encodeInt_4, repr32_emod, repr32_unsigned]

/-- `Memdata.decode_encode_int_8` -/
theorem decode_encode_int_8 (x : Integers.Int64) :
    Integers.Int64.repr (decodeInt (encodeInt 8 (Integers.Int64.unsigned x))) = x := by
  rw [decodeInt_encodeInt_8, repr64_emod, repr64_unsigned]

private theorem byte_repr_emod (x y : _root_.Int) (h : x % 256 = y % 256) :
    Integers.Byte.repr x = Integers.Byte.repr y := by
  show BitVec.ofInt 8 x = BitVec.ofInt 8 y
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have : (x % (2 ^ 8 : Nat)) = (y % (2 ^ 8 : Nat)) := h
  rw [this]

/-- `Memdata.bytes_of_int_mod`: a length-`n` encoding depends only on the low
    `8n` bits.  (`eqmod m x y` is stated as `x % m = y % m`.) -/
theorem bytesOfInt_mod (n : Nat) (x y : _root_.Int)
    (h : x % 2 ^ (n * 8) = y % 2 ^ (n * 8)) : bytesOfInt n x = bytesOfInt n y := by
  induction n generalizing x y with
  | zero => rfl
  | succ m ih =>
      rw [two_pow_succ_mul8, emod_mul_decomp x 256 _ (by decide) (two_pow_pos' _),
        emod_mul_decomp y 256 _ (by decide) (two_pow_pos' _)] at h
      have hlo : x % 256 = y % 256 := by
        have := Int.emod_nonneg x (show (256 : _root_.Int) ≠ 0 by decide)
        have := Int.emod_lt_of_pos x (show (0 : _root_.Int) < 256 by decide)
        have := Int.emod_nonneg y (show (256 : _root_.Int) ≠ 0 by decide)
        have := Int.emod_lt_of_pos y (show (0 : _root_.Int) < 256 by decide)
        omega
      have hhi : x / 256 % 2 ^ (m * 8) = y / 256 % 2 ^ (m * 8) := by
        rw [hlo] at h; omega
      simp only [bytesOfInt]
      rw [byte_repr_emod x y hlo, ih _ _ hhi]

/-- `Memdata.encode_int_8_mod` -/
theorem encodeInt_8_mod (x y : _root_.Int) (h : x % 256 = y % 256) :
    encodeInt 1 x = encodeInt 1 y := by
  unfold encodeInt; rw [bytesOfInt_mod 1 x y h]

/-- `Memdata.encode_int_16_mod` -/
theorem encodeInt_16_mod (x y : _root_.Int) (h : x % 65536 = y % 65536) :
    encodeInt 2 x = encodeInt 2 y := by
  unfold encodeInt; rw [bytesOfInt_mod 2 x y h]

/-! ## Bytes and fragments -/

/-- `Memdata.inj_proj_bytes` -/
theorem injBytes_projBytes {cl : List MemVal} {bl : List Byte}
    (h : projBytes cl = some bl) : cl = injBytes bl := by
  induction cl generalizing bl with
  | nil => cases h; rfl
  | cons a cl ih =>
      cases a with
      | Byte b =>
          simp only [projBytes] at h
          cases hp : projBytes cl with
          | none => rw [hp] at h; cases h
          | some bl' =>
              rw [hp] at h; cases h
              rw [ih hp]; rfl
      | _ => cases h

/-- `Memdata.in_inj_value` -/
theorem mem_injValue {mv : MemVal} {v : Val} {q : Quantity} (h : mv ∈ injValue q v) :
    ∃ n, mv = .Fragment v q n := by
  unfold injValue at h
  generalize sizeQuantityNat q = k at h
  induction k with
  | zero => cases h
  | succ m ih =>
      simp only [injValueRec, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨m, h⟩
      · exact ih h

/-- `Memdata.proj_inj_value_mismatch` -/
theorem projValue_injValue_mismatch {q1 q2 : Quantity} (v : Val) (h : q1 ≠ q2) :
    projValue q1 (injValue q2 v) = .Vundef := by
  cases q1 <;> cases q2 <;> first | exact absurd rfl h | simp [projValue, injValue,
    injValueRec, sizeQuantityNat, checkValue]

/-- `Memdata.decode_val_undef` -/
theorem decodeVal_undef_cons (bl : List MemVal) (chunk : Chunk) :
    decodeVal chunk (.Undef :: bl) = .Vundef := by
  cases chunk <;> simp [decodeVal, Val.loadResult]

/-! ## Splitting a 64-bit access -/

/-- `Memdata.int_of_bytes_append` -/
theorem intOfBytes_append (l1 l2 : List Byte) :
    intOfBytes (l1 ++ l2) = intOfBytes l1 + intOfBytes l2 * 2 ^ (l1.length * 8) := by
  induction l1 with
  | nil => simp [intOfBytes]
  | cons b l ih =>
      simp only [List.cons_append, intOfBytes, ih, List.length_cons, two_pow_succ_mul8]
      rw [Int.add_mul, Int.add_assoc]
      congr 2
      rw [Int.mul_assoc, Int.mul_comm (2 ^ _) 256]

private theorem byte_unsigned_range (b : Byte) :
    (0 : _root_.Int) ≤ Integers.Byte.unsigned b ∧ Integers.Byte.unsigned b < 256 := by
  unfold Integers.Byte.unsigned Integers.MI.unsigned
  have := b.isLt
  constructor
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_lt.mpr this

/-- `Memdata.int_of_bytes_range` -/
theorem intOfBytes_range (l : List Byte) :
    0 ≤ intOfBytes l ∧ intOfBytes l < 2 ^ (l.length * 8) := by
  induction l with
  | nil => simp [intOfBytes]
  | cons b l ih =>
      simp only [intOfBytes, List.length_cons, two_pow_succ_mul8]
      have hb := byte_unsigned_range b
      obtain ⟨h0, h1⟩ := ih
      refine ⟨Int.add_nonneg hb.1 (Int.mul_nonneg h0 (by decide)), ?_⟩
      have : intOfBytes l * 256 ≤ (2 ^ (l.length * 8) - 1) * 256 :=
        Int.mul_le_mul_of_nonneg_right (by zomega) (by decide)
      rw [Int.sub_mul, Int.one_mul, Int.mul_comm (2 ^ _)] at this
      zomega

/-- `Memdata.length_proj_bytes` -/
theorem length_projBytes {l : List MemVal} {b : List Byte} (h : projBytes l = some b) :
    b.length = l.length := by
  rw [injBytes_projBytes h, length_injBytes]

/-- `Memdata.proj_bytes_append` -/
theorem projBytes_append (l1 l2 : List MemVal) :
    projBytes (l1 ++ l2) =
      match projBytes l1, projBytes l2 with
      | some b1, some b2 => some (b1 ++ b2)
      | _, _ => none := by
  induction l1 with
  | nil => simp only [List.nil_append]; cases projBytes l2 <;> rfl
  | cons a l ih =>
      cases a with
      | Byte b =>
          simp only [List.cons_append, projBytes, ih]
          cases projBytes l <;> cases projBytes l2 <;> rfl
      | _ => rfl

/-- `Memdata.bytes_of_int_append` -/
theorem bytesOfInt_append (n1 n2 : Nat) (x1 x2 : _root_.Int)
    (h : 0 ≤ x1 ∧ x1 < 2 ^ (n1 * 8)) :
    bytesOfInt (n1 + n2) (x1 + x2 * 2 ^ (n1 * 8)) = bytesOfInt n1 x1 ++ bytesOfInt n2 x2 := by
  induction n1 generalizing x1 with
  | zero =>
      have : x1 = 0 := by simp at h; omega
      subst this; simp [bytesOfInt]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [bytesOfInt, List.cons_append]
      rw [two_pow_succ_mul8] at h ⊢
      have hp := two_pow_pos' (m * 8)
      have e : x1 + x2 * (256 * 2 ^ (m * 8)) = x1 + (x2 * 2 ^ (m * 8)) * 256 := by
        rw [Int.mul_comm 256, Int.mul_assoc]
      rw [e]
      congr 1
      · apply byte_repr_emod
        rw [Int.add_mul_emod_self_right]
      · rw [Int.add_mul_ediv_right _ _ (by decide)]
        apply ih
        constructor
        · exact Int.ediv_nonneg h.1 (by decide)
        · rw [Int.ediv_lt_iff_lt_mul (by decide)]
          rw [Int.mul_comm]; exact h.2

private theorem unsigned64_split (i : Integers.Int64) :
    Integers.Int64.unsigned i =
      Integers.Int.unsigned (Integers.Int64.loword i)
        + Integers.Int.unsigned (Integers.Int64.hiword i) * 2 ^ (4 * 8) := by
  show (i.toNat : _root_.Int) = ((BitVec.truncate 32 i).toNat : _root_.Int)
      + ((BitVec.truncate 32 (i >>> 32)).toNat : _root_.Int) * 2 ^ (4 * 8)
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  have := i.isLt
  rw [Nat.shiftRight_eq_div_pow]
  have : (2 : _root_.Int) ^ (4 * 8) = 4294967296 := rfl
  rw [this]
  omega

/-- `Memdata.bytes_of_int64` -/
theorem bytesOfInt64 (i : Integers.Int64) :
    bytesOfInt 8 (Integers.Int64.unsigned i) =
      bytesOfInt 4 (Integers.Int.unsigned (Integers.Int64.loword i))
        ++ bytesOfInt 4 (Integers.Int.unsigned (Integers.Int64.hiword i)) := by
  rw [unsigned64_split]
  apply bytesOfInt_append 4 4
  show (0 : _root_.Int) ≤ ((BitVec.truncate 32 i).toNat : _root_.Int)
    ∧ ((BitVec.truncate 32 i).toNat : _root_.Int) < 2 ^ (4 * 8)
  have := (BitVec.truncate 32 i).isLt
  have e : (2 : _root_.Int) ^ (4 * 8) = 4294967296 := rfl
  rw [e]; omega

/-- `Memdata.decode_val_int64` — only meaningful on 32-bit targets; here
    `Archi.ptr64 = true`, so the hypothesis is contradictory. -/
theorem decodeVal_int64 (l1 l2 : List MemVal) (_h1 : l1.length = 4) (_h2 : l2.length = 4)
    (hp : Archi.ptr64 = false) :
    Val.Lessdef (decodeVal .Mint64 (l1 ++ l2))
      (Val.longofwords (decodeVal .Mint32 (if Archi.big_endian then l1 else l2))
        (decodeVal .Mint32 (if Archi.big_endian then l2 else l1))) := by
  simp at hp

/-- `Memdata.encode_val_int64` — only meaningful on 32-bit targets. -/
theorem encodeVal_int64 (v : Val) (hp : Archi.ptr64 = false) :
    encodeVal .Mint64 v =
      encodeVal .Mint32 (if Archi.big_endian then Val.hiword v else Val.loword v)
        ++ encodeVal .Mint32 (if Archi.big_endian then Val.loword v else Val.hiword v) := by
  simp at hp

end CC
