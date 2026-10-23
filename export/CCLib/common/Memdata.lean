/-
  In-memory representation of values — port of `common/Memdata.v` lines 1–456
  (the rest of the file is `decode_encode_val_general`, `shape_encoding`, and the
  `memval_inject`/`memval_lessdef` relations, all needed only by CompCert's pass
  proofs).

  The interesting part is how pointers survive a store/load round trip: a
  pointer is written as `size_quantity_nat q` copies of `Fragment v q i`
  (`i` counting down), and reading it back succeeds only if *all* the fragments
  are present, agree on the value and quantity, and carry consecutive indices
  (`check_value`).  Overwriting any single byte therefore destroys the pointer,
  which is exactly what makes pointer forging impossible in CompCert.
-/
import CCLib.common.Values

namespace CC

/-! ## Chunk sizes and alignments -/

/-- `Memdata.size_chunk` -/
def sizeChunk : Chunk → Z
  | .Mbool | .Mint8signed | .Mint8unsigned => 1
  | .Mint16signed | .Mint16unsigned => 2
  | .Mint32 | .Mfloat32 | .Many32 => 4
  | .Mint64 | .Mfloat64 | .Many64 => 8

/-- `Memdata.size_chunk_nat` -/
def sizeChunkNat (c : Chunk) : Nat := (sizeChunk c).toNat

/-- `Memdata.align_chunk`.  Note `Mfloat64`/`Many64` require only 4-byte
    alignment (CompCert follows PowerPC/ARM/x86 here). -/
def alignChunk : Chunk → Z
  | .Mbool | .Mint8signed | .Mint8unsigned => 1
  | .Mint16signed | .Mint16unsigned => 2
  | .Mint32 | .Mfloat32 | .Many32 => 4
  | .Mint64 => 8
  | .Mfloat64 | .Many64 => 4

/-! ## Byte-level encoding of integers -/

/-- CompCert's `byte` (`Integers.Byte.int`). -/
abbrev Byte := Integers.Byte

/-- `Memdata.bytes_of_int` — little-endian byte decomposition. -/
def bytesOfInt : Nat → Z → List Byte
  | 0, _ => []
  | m + 1, x => Integers.Byte.repr x :: bytesOfInt m (x / 256)

/-- `Memdata.int_of_bytes` — little-endian recomposition. -/
def intOfBytes : List Byte → Z
  | [] => 0
  | b :: l => Integers.Byte.unsigned b + intOfBytes l * 256

/-- `Memdata.rev_if_be` — byte order for the target. -/
def revIfBe (l : List Byte) : List Byte :=
  if Archi.big_endian then l.reverse else l

/-- `Memdata.encode_int` -/
def encodeInt (sz : Nat) (x : Z) : List Byte := revIfBe (bytesOfInt sz x)

/-- `Memdata.decode_int` -/
def decodeInt (b : List Byte) : Z := intOfBytes (revIfBe b)

/-! ## Memory values -/

/-- `Memdata.quantity` -/
inductive Quantity where
  | Q32 | Q64
  deriving DecidableEq, Repr, Inhabited

/-- `Memdata.size_quantity_nat` -/
def sizeQuantityNat : Quantity → Nat
  | .Q32 => 4
  | .Q64 => 8

/-- `Memdata.quantity_chunk` -/
def quantityChunk : Chunk → Quantity
  | .Mint64 | .Mfloat64 | .Many64 => .Q64
  | _ => .Q32

/-- `Memdata.memval` — the contents of one byte of memory. -/
inductive MemVal where
  /-- uninitialised -/
  | Undef
  /-- a concrete byte -/
  | Byte (b : CC.Byte)
  /-- one byte of the pointer-or-any value `v` (`i` counts down) -/
  | Fragment (v : Val) (q : Quantity) (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- `Memdata.inj_bytes` -/
def injBytes (bl : List Byte) : List MemVal := bl.map MemVal.Byte

/-- `Memdata.proj_bytes` — succeeds only if every cell is a concrete byte. -/
def projBytes : List MemVal → Option (List Byte)
  | [] => some []
  | .Byte b :: vl => (projBytes vl).map (b :: ·)
  | _ => none

/-- `Memdata.inj_value_rec` -/
def injValueRec (n : Nat) (v : Val) (q : Quantity) : List MemVal :=
  match n with
  | 0 => []
  | m + 1 => .Fragment v q m :: injValueRec m v q

/-- `Memdata.inj_value` — the byte-level image of a pointer (or `Many*` value). -/
def injValue (q : Quantity) (v : Val) : List MemVal :=
  injValueRec (sizeQuantityNat q) v q

/-- `Memdata.check_value` — all fragments present, consistent, consecutive. -/
def checkValue : Nat → Val → Quantity → List MemVal → Bool
  | 0, _, _, [] => true
  | m + 1, v, q, .Fragment v' q' m' :: vl' =>
      (v == v') && (q == q') && (m == m') && checkValue m v q vl'
  | _, _, _, _ => false

/-- `Memdata.proj_value` -/
def projValue (q : Quantity) (vl : List MemVal) : Val :=
  match vl with
  | .Fragment v _ _ :: _ =>
      if checkValue (sizeQuantityNat q) v q vl then v else .Vundef
  | _ => .Vundef

/-! ## `encode_val` / `decode_val` -/

/-- `Memdata.encode_val` — the bytes written by storing `v` with `chunk`. -/
def encodeVal (chunk : Chunk) (v : Val) : List MemVal :=
  match v, chunk with
  | .Vint n, .Mbool => injBytes (encodeInt 1 (Integers.Int.unsigned n))
  | .Vint n, .Mint8signed => injBytes (encodeInt 1 (Integers.Int.unsigned n))
  | .Vint n, .Mint8unsigned => injBytes (encodeInt 1 (Integers.Int.unsigned n))
  | .Vint n, .Mint16signed => injBytes (encodeInt 2 (Integers.Int.unsigned n))
  | .Vint n, .Mint16unsigned => injBytes (encodeInt 2 (Integers.Int.unsigned n))
  | .Vint n, .Mint32 => injBytes (encodeInt 4 (Integers.Int.unsigned n))
  | .Vptr _ _, .Mint32 =>
      if Archi.ptr64 then List.replicate 4 .Undef else injValue .Q32 v
  | .Vlong n, .Mint64 => injBytes (encodeInt 8 (Integers.Int64.unsigned n))
  | .Vptr _ _, .Mint64 =>
      if Archi.ptr64 then injValue .Q64 v else List.replicate 8 .Undef
  | .Vsingle n, .Mfloat32 =>
      injBytes (encodeInt 4 (Integers.Int.unsigned (Floats.Float32.toBits n)))
  | .Vfloat n, .Mfloat64 =>
      injBytes (encodeInt 8 (Integers.Int64.unsigned (Floats.Float.toBits n)))
  | _, .Many32 => injValue .Q32 v
  | _, .Many64 => injValue .Q64 v
  | _, _ => List.replicate (sizeChunkNat chunk) .Undef

/-- `Memdata.decode_val` — the value read back from `vl` with `chunk`. -/
def decodeVal (chunk : Chunk) (vl : List MemVal) : Val :=
  match projBytes vl with
  | some bl =>
      match chunk with
      | .Mbool =>
          Val.normBool (.Vint (Integers.Int.zero_ext 8
            (Integers.Int.repr (decodeInt bl))))
      | .Mint8signed =>
          .Vint (Integers.Int.sign_ext 8 (Integers.Int.repr (decodeInt bl)))
      | .Mint8unsigned =>
          .Vint (Integers.Int.zero_ext 8 (Integers.Int.repr (decodeInt bl)))
      | .Mint16signed =>
          .Vint (Integers.Int.sign_ext 16 (Integers.Int.repr (decodeInt bl)))
      | .Mint16unsigned =>
          .Vint (Integers.Int.zero_ext 16 (Integers.Int.repr (decodeInt bl)))
      | .Mint32 => .Vint (Integers.Int.repr (decodeInt bl))
      | .Mint64 => .Vlong (Integers.Int64.repr (decodeInt bl))
      | .Mfloat32 =>
          .Vsingle (Floats.Float32.ofBits (Integers.Int.repr (decodeInt bl)))
      | .Mfloat64 =>
          .Vfloat (Floats.Float.ofBits (Integers.Int64.repr (decodeInt bl)))
      | .Many32 => .Vundef
      | .Many64 => .Vundef
  | none =>
      match chunk with
      | .Mint32 =>
          if Archi.ptr64 then .Vundef
          else Val.loadResult chunk (projValue .Q32 vl)
      | .Many32 => Val.loadResult chunk (projValue .Q32 vl)
      | .Mint64 =>
          if Archi.ptr64 then Val.loadResult chunk (projValue .Q64 vl)
          else .Vundef
      | .Many64 => Val.loadResult chunk (projValue .Q64 vl)
      | _ => .Vundef

/-! ## Length facts (needed by the memory model) -/

@[simp] theorem length_bytesOfInt (n : Nat) (x : Z) :
    (bytesOfInt n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ m ih => simp [bytesOfInt, ih]

@[simp] theorem length_revIfBe (l : List Byte) :
    (revIfBe l).length = l.length := by
  simp [revIfBe]; split <;> simp

@[simp] theorem length_encodeInt (sz : Nat) (x : Z) :
    (encodeInt sz x).length = sz := by
  simp [encodeInt]

@[simp] theorem length_injBytes (bl : List Byte) :
    (injBytes bl).length = bl.length := by
  simp [injBytes]

@[simp] theorem length_injValueRec (n : Nat) (v : Val) (q : Quantity) :
    (injValueRec n v q).length = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp [injValueRec, ih]

@[simp] theorem length_injValue (q : Quantity) (v : Val) :
    (injValue q v).length = sizeQuantityNat q := by
  simp [injValue]

/-- `Memdata.encode_val_length`: a store always writes exactly `size_chunk_nat`
    bytes.  The memory model relies on this for its `store` to preserve the
    access invariants. -/
theorem length_encodeVal (chunk : Chunk) (v : Val) :
    (encodeVal chunk v).length = sizeChunkNat chunk := by
  cases v <;> cases chunk <;>
    simp [encodeVal, sizeChunkNat, sizeChunk, sizeQuantityNat, Archi.ptr64] <;> rfl

/-- `sizeChunkNat` casts back to `sizeChunk`. -/
theorem sizeChunkNat_cast (chunk : Chunk) :
    ((sizeChunkNat chunk : Nat) : _root_.Int) = sizeChunk chunk := by
  cases chunk <;> rfl

/-- `Memdata.size_chunk_pos`: every chunk is at least one byte. -/
theorem sizeChunk_pos (chunk : Chunk) : (0 : _root_.Int) < sizeChunk chunk := by
  cases chunk <;> decide

end CC
