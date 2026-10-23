/-
  Abstract specification of the memory model — port of `common/Memtype.v`
  (the module type `MEM`).

  `Memtype.v` declares the operations of the memory model (`empty`, `alloc`,
  `free`, `load`, `store`, `loadbytes`, `storebytes`, `drop_perm`,
  `nextblock`, `perm`, `valid_pointer`, `extends`, `inject`,
  `inject_neutral`) as parameters, defines a few derived notions in terms of
  them (`loadv`, `storev`, `free_list`, `valid_block`, `range_perm`,
  `valid_access`, `weak_valid_pointer`, `compat_pointer_chunks`,
  `inj_offset_aligned`, `flat_inj`), and states 168 properties as axioms.

  Here the parameters are the class `MemOps mem`, the derived notions are
  definitions in the namespace `MemOps`, and the axioms are the fields of the
  class `MEM mem`, with the same names and statements.  The concrete memory
  model of the port (`CC.Mem`, `common/Memory*.lean`) is shown to be an
  instance in `CCLib.common.MemoryMemtype`.

  Differences from Rocq:
  * `permission`, `perm_kind` and `perm_order` are the port's `Permission`,
    `PermKind` and `permOrder` (a `Bool`; `perm_order p1 p2` is
    `permOrder p1 p2 = true`), defined in `CCLib.common.Memory`;
    `perm_order_trans` is `permOrder_trans`;
  * `perm_dec` is a `Decidable` field;
  * as in Rocq's `Memtype.v`, `loadv`/`storev` are defined directly from
    `load`/`store`; the concrete `Mem.loadv`/`Mem.storev` additionally reject
    accesses that wrap around the address space (as in this CompCert's
    `Memory.v`, which therefore no longer declares `Mem <: MEM`);
  * `list_forall2 memval_lessdef` and `list_forall2 (memval_inject f)` are
    `MemvalInjectList Val.inject_id` and `MemvalInjectList f`.
-/
import CCLib.common.MemoryInject
import CCLib.common.Builtins
import CCLib.common.ValuesOps
import CCLib.common.MemdataEncode

namespace CC
namespace Memtype

open Integers (Ptrofs)

/-- The parameters of `Memtype.MEM`: the operations of the memory model. -/
class MemOps (mem : Type) where
  empty : mem
  alloc : mem → Z → Z → mem × Block
  free : mem → Block → Z → Z → Option mem
  load : Chunk → mem → Block → Z → Option Val
  store : Chunk → mem → Block → Z → Val → Option mem
  loadbytes : mem → Block → Z → Z → Option (List MemVal)
  storebytes : mem → Block → Z → List MemVal → Option mem
  drop_perm : mem → Block → Z → Z → Permission → Option mem
  nextblock : mem → Block
  perm : mem → Block → Z → PermKind → Permission → Prop
  valid_pointer : mem → Block → Z → Bool
  «extends» : mem → mem → Prop
  inject : Val.Meminj → mem → mem → Prop
  inject_neutral : Block → mem → Prop

namespace MemOps

variable {mem : Type} [MemOps mem]

/-- `Memtype.loadv` -/
def loadv (chunk : Chunk) (m : mem) (addr : Val) : Option Val :=
  match addr with
  | .Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => none

/-- `Memtype.storev` -/
def storev (chunk : Chunk) (m : mem) (addr v : Val) : Option mem :=
  match addr with
  | .Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => none

/-- `Memtype.free_list` -/
def free_list (m : mem) : List (Block × Z × Z) → Option mem
  | [] => some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | none => none
      | some m' => free_list m' l'

/-- `Memtype.valid_block` -/
def valid_block (m : mem) (b : Block) : Prop := b < nextblock m

/-- `Memtype.range_perm` -/
def range_perm (m : mem) (b : Block) (lo hi : Z) (k : PermKind) (p : Permission) : Prop :=
  ∀ ofs, lo ≤ ofs → ofs < hi → perm m b ofs k p

/-- `Memtype.valid_access` -/
def valid_access (m : mem) (chunk : Chunk) (b : Block) (ofs : Z) (p : Permission) : Prop :=
  range_perm m b ofs (ofs + sizeChunk chunk) .Cur p ∧ alignChunk chunk ∣ ofs

/-- `Memtype.weak_valid_pointer` -/
def weak_valid_pointer (m : mem) (b : Block) (ofs : Z) : Bool :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1)

end MemOps

/-- `Memtype.compat_pointer_chunks` -/
def compat_pointer_chunks (chunk1 chunk2 : Chunk) : Prop :=
  match chunk1, chunk2 with
  | .Mint32, .Mint32 | .Mint32, .Many32 | .Many32, .Mint32 | .Many32, .Many32 => True
  | .Mint64, .Mint64 | .Mint64, .Many64 | .Many64, .Mint64 | .Many64, .Many64 => True
  | _, _ => False

/-- `Memtype.inj_offset_aligned` -/
def inj_offset_aligned (delta size : Z) : Prop := minSafeAlignment size ∣ delta

/-- `Memtype.flat_inj` -/
def flat_inj (thr : Block) : Val.Meminj := fun b => if b < thr then some (b, 0) else none

open MemOps in
/-- `Memtype.MEM`: the properties every implementation of the memory model
must satisfy (the axioms of the Rocq module type). -/
class MEM (mem : Type) extends MemOps mem where
  -- Validity of blocks and permissions
  valid_not_valid_diff : ∀ (m : mem) b b', valid_block m b → ¬ valid_block m b' → b ≠ b'
  perm_implies : ∀ (m : mem) b ofs k p1 p2,
    perm m b ofs k p1 → permOrder p1 p2 = true → perm m b ofs k p2
  perm_cur_max : ∀ (m : mem) b ofs p, perm m b ofs .Cur p → perm m b ofs .Max p
  perm_cur : ∀ (m : mem) b ofs k p, perm m b ofs .Cur p → perm m b ofs k p
  perm_max : ∀ (m : mem) b ofs k p, perm m b ofs k p → perm m b ofs .Max p
  perm_valid_block : ∀ (m : mem) b ofs k p, perm m b ofs k p → valid_block m b
  perm_dec : ∀ (m : mem) b ofs k p, Decidable (perm m b ofs k p)
  range_perm_implies : ∀ (m : mem) b lo hi k p1 p2,
    range_perm m b lo hi k p1 → permOrder p1 p2 = true → range_perm m b lo hi k p2
  valid_access_implies : ∀ (m : mem) chunk b ofs p1 p2,
    valid_access m chunk b ofs p1 → permOrder p1 p2 = true → valid_access m chunk b ofs p2
  valid_access_valid_block : ∀ (m : mem) chunk b ofs,
    valid_access m chunk b ofs .Nonempty → valid_block m b
  valid_access_perm : ∀ (m : mem) chunk b ofs k p,
    valid_access m chunk b ofs p → perm m b ofs k p
  valid_pointer_nonempty_perm : ∀ (m : mem) b ofs,
    valid_pointer m b ofs = true ↔ perm m b ofs .Cur .Nonempty
  valid_pointer_valid_access : ∀ (m : mem) b ofs,
    valid_pointer m b ofs = true ↔ valid_access m .Mint8unsigned b ofs .Nonempty
  weak_valid_pointer_spec : ∀ (m : mem) b ofs,
    weak_valid_pointer m b ofs = true ↔
      valid_pointer m b ofs = true ∨ valid_pointer m b (ofs - 1) = true
  valid_pointer_implies : ∀ (m : mem) b ofs,
    valid_pointer m b ofs = true → weak_valid_pointer m b ofs = true
  -- Properties of the empty store
  nextblock_empty : nextblock (empty : mem) = Positive.xH
  perm_empty : ∀ b ofs k p, ¬ perm (empty : mem) b ofs k p
  valid_access_empty : ∀ chunk b ofs p, ¬ valid_access (empty : mem) chunk b ofs p
  -- Properties of `load`
  valid_access_load : ∀ (m : mem) chunk b ofs,
    valid_access m chunk b ofs .Readable → ∃ v, load chunk m b ofs = some v
  load_valid_access : ∀ (m : mem) chunk b ofs v,
    load chunk m b ofs = some v → valid_access m chunk b ofs .Readable
  load_type : ∀ (m : mem) chunk b ofs v, load chunk m b ofs = some v → Val.HasType v chunk.typ
  load_xtype : ∀ (m : mem) chunk b ofs v,
    load chunk m b ofs = some v → Val.hasRettype v chunk.xtype
  load_cast : ∀ (m : mem) chunk b ofs v, load chunk m b ofs = some v →
    match chunk with
    | .Mbool => v = Val.normBool v
    | .Mint8signed => v = Val.signExt 8 v
    | .Mint8unsigned => v = Val.zeroExt 8 v
    | .Mint16signed => v = Val.signExt 16 v
    | .Mint16unsigned => v = Val.zeroExt 16 v
    | _ => True
  load_bool_int8_unsigned : ∀ (m : mem) b ofs,
    load .Mbool m b ofs = (load .Mint8unsigned m b ofs).map Val.normBool
  load_int8_signed_unsigned : ∀ (m : mem) b ofs,
    load .Mint8signed m b ofs = (load .Mint8unsigned m b ofs).map (Val.signExt 8)
  load_int16_signed_unsigned : ∀ (m : mem) b ofs,
    load .Mint16signed m b ofs = (load .Mint16unsigned m b ofs).map (Val.signExt 16)
  -- Properties of `loadbytes`
  range_perm_loadbytes : ∀ (m : mem) b ofs len,
    range_perm m b ofs (ofs + len) .Cur .Readable → ∃ bytes, loadbytes m b ofs len = some bytes
  loadbytes_range_perm : ∀ (m : mem) b ofs len bytes,
    loadbytes m b ofs len = some bytes → range_perm m b ofs (ofs + len) .Cur .Readable
  loadbytes_load : ∀ chunk (m : mem) b ofs bytes,
    loadbytes m b ofs (sizeChunk chunk) = some bytes → alignChunk chunk ∣ ofs →
    load chunk m b ofs = some (decodeVal chunk bytes)
  load_loadbytes : ∀ chunk (m : mem) b ofs v, load chunk m b ofs = some v →
    ∃ bytes, loadbytes m b ofs (sizeChunk chunk) = some bytes ∧ v = decodeVal chunk bytes
  loadbytes_length : ∀ (m : mem) b ofs n bytes,
    loadbytes m b ofs n = some bytes → bytes.length = n.toNat
  loadbytes_empty : ∀ (m : mem) b ofs n, n ≤ 0 → loadbytes m b ofs n = some []
  loadbytes_concat : ∀ (m : mem) b ofs n1 n2 bytes1 bytes2,
    loadbytes m b ofs n1 = some bytes1 → loadbytes m b (ofs + n1) n2 = some bytes2 →
    n1 ≥ 0 → n2 ≥ 0 → loadbytes m b ofs (n1 + n2) = some (bytes1 ++ bytes2)
  loadbytes_split : ∀ (m : mem) b ofs n1 n2 bytes,
    loadbytes m b ofs (n1 + n2) = some bytes → n1 ≥ 0 → n2 ≥ 0 →
    ∃ bytes1 bytes2, loadbytes m b ofs n1 = some bytes1 ∧
      loadbytes m b (ofs + n1) n2 = some bytes2 ∧ bytes = bytes1 ++ bytes2
  -- Properties of `store`
  nextblock_store : ∀ chunk (m1 : mem) b ofs v m2,
    store chunk m1 b ofs v = some m2 → nextblock m2 = nextblock m1
  store_valid_block_1 : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ b', valid_block m1 b' → valid_block m2 b'
  store_valid_block_2 : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ b', valid_block m2 b' → valid_block m1 b'
  perm_store_1 : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ b' ofs' k p, perm m1 b' ofs' k p → perm m2 b' ofs' k p
  perm_store_2 : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ b' ofs' k p, perm m2 b' ofs' k p → perm m1 b' ofs' k p
  valid_access_store : ∀ (m1 : mem) chunk b ofs v,
    valid_access m1 chunk b ofs .Writable → { m2 : mem // store chunk m1 b ofs v = some m2 }
  store_valid_access_1 : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ chunk' b' ofs' p, valid_access m1 chunk' b' ofs' p → valid_access m2 chunk' b' ofs' p
  store_valid_access_2 : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ chunk' b' ofs' p, valid_access m2 chunk' b' ofs' p → valid_access m1 chunk' b' ofs' p
  store_valid_access_3 : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    valid_access m1 chunk b ofs .Writable
  load_store_similar : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ chunk', sizeChunk chunk' = sizeChunk chunk → alignChunk chunk' ≤ alignChunk chunk →
    ∃ v', load chunk' m2 b ofs = some v' ∧ decodeEncodeVal v chunk chunk' v'
  load_store_same : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    load chunk m2 b ofs = some (Val.loadResult chunk v)
  load_store_other : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ chunk' b' ofs',
    b' ≠ b ∨ ofs' + sizeChunk chunk' ≤ ofs ∨ ofs + sizeChunk chunk ≤ ofs' →
    load chunk' m2 b' ofs' = load chunk' m1 b' ofs'
  load_store_pointer_overlap : ∀ chunk (m1 : mem) b ofs v_b v_o m2 chunk' ofs' v,
    store chunk m1 b ofs (.Vptr v_b v_o) = some m2 → load chunk' m2 b ofs' = some v →
    ofs' ≠ ofs → ofs' + sizeChunk chunk' > ofs → ofs + sizeChunk chunk > ofs' → v = .Vundef
  load_store_pointer_mismatch : ∀ chunk (m1 : mem) b ofs v_b v_o m2 chunk' v,
    store chunk m1 b ofs (.Vptr v_b v_o) = some m2 → load chunk' m2 b ofs = some v →
    ¬ compat_pointer_chunks chunk chunk' → v = .Vundef
  load_pointer_store : ∀ chunk (m1 : mem) b ofs v m2 chunk' b' ofs' v_b v_o,
    store chunk m1 b ofs v = some m2 → load chunk' m2 b' ofs' = some (.Vptr v_b v_o) →
    (v = .Vptr v_b v_o ∧ compat_pointer_chunks chunk chunk' ∧ b' = b ∧ ofs' = ofs) ∨
    (b' ≠ b ∨ ofs' + sizeChunk chunk' ≤ ofs ∨ ofs + sizeChunk chunk ≤ ofs')
  loadbytes_store_same : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    loadbytes m2 b ofs (sizeChunk chunk) = some (encodeVal chunk v)
  loadbytes_store_other : ∀ chunk (m1 : mem) b ofs v m2, store chunk m1 b ofs v = some m2 →
    ∀ b' ofs' n, b' ≠ b ∨ n ≤ 0 ∨ ofs' + n ≤ ofs ∨ ofs + sizeChunk chunk ≤ ofs' →
    loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n
  store_bool_unsigned_8 : ∀ (m : mem) b ofs v,
    store .Mbool m b ofs v = store .Mint8unsigned m b ofs v
  store_signed_unsigned_8 : ∀ (m : mem) b ofs v,
    store .Mint8signed m b ofs v = store .Mint8unsigned m b ofs v
  store_signed_unsigned_16 : ∀ (m : mem) b ofs v,
    store .Mint16signed m b ofs v = store .Mint16unsigned m b ofs v
  store_int8_zero_ext : ∀ (m : mem) b ofs n,
    store .Mint8unsigned m b ofs (.Vint (Integers.Int.zero_ext 8 n)) =
      store .Mint8unsigned m b ofs (.Vint n)
  store_int8_sign_ext : ∀ (m : mem) b ofs n,
    store .Mint8signed m b ofs (.Vint (Integers.Int.sign_ext 8 n)) =
      store .Mint8signed m b ofs (.Vint n)
  store_int16_zero_ext : ∀ (m : mem) b ofs n,
    store .Mint16unsigned m b ofs (.Vint (Integers.Int.zero_ext 16 n)) =
      store .Mint16unsigned m b ofs (.Vint n)
  store_int16_sign_ext : ∀ (m : mem) b ofs n,
    store .Mint16signed m b ofs (.Vint (Integers.Int.sign_ext 16 n)) =
      store .Mint16signed m b ofs (.Vint n)
  -- Properties of `storebytes`
  range_perm_storebytes : ∀ (m1 : mem) b ofs bytes,
    range_perm m1 b ofs (ofs + (bytes.length : Z)) .Cur .Writable →
    { m2 : mem // storebytes m1 b ofs bytes = some m2 }
  storebytes_range_perm : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    range_perm m1 b ofs (ofs + (bytes.length : Z)) .Cur .Writable
  perm_storebytes_1 : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ b' ofs' k p, perm m1 b' ofs' k p → perm m2 b' ofs' k p
  perm_storebytes_2 : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ b' ofs' k p, perm m2 b' ofs' k p → perm m1 b' ofs' k p
  storebytes_valid_access_1 : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ chunk' b' ofs' p, valid_access m1 chunk' b' ofs' p → valid_access m2 chunk' b' ofs' p
  storebytes_valid_access_2 : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ chunk' b' ofs' p, valid_access m2 chunk' b' ofs' p → valid_access m1 chunk' b' ofs' p
  nextblock_storebytes : ∀ (m1 : mem) b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 → nextblock m2 = nextblock m1
  storebytes_valid_block_1 : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ b', valid_block m1 b' → valid_block m2 b'
  storebytes_valid_block_2 : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ b', valid_block m2 b' → valid_block m1 b'
  storebytes_store : ∀ (m1 : mem) b ofs chunk v m2,
    storebytes m1 b ofs (encodeVal chunk v) = some m2 → alignChunk chunk ∣ ofs →
    store chunk m1 b ofs v = some m2
  store_storebytes : ∀ (m1 : mem) b ofs chunk v m2,
    store chunk m1 b ofs v = some m2 → storebytes m1 b ofs (encodeVal chunk v) = some m2
  loadbytes_storebytes_same : ∀ (m1 : mem) b ofs bytes m2,
    storebytes m1 b ofs bytes = some m2 → loadbytes m2 b ofs (bytes.length : Z) = some bytes
  loadbytes_storebytes_other : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ b' ofs' len, len ≥ 0 →
    b' ≠ b ∨ ofs' + len ≤ ofs ∨ ofs + (bytes.length : Z) ≤ ofs' →
    loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len
  load_storebytes_other : ∀ (m1 : mem) b ofs bytes m2, storebytes m1 b ofs bytes = some m2 →
    ∀ chunk b' ofs',
    b' ≠ b ∨ ofs' + sizeChunk chunk ≤ ofs ∨ ofs + (bytes.length : Z) ≤ ofs' →
    load chunk m2 b' ofs' = load chunk m1 b' ofs'
  storebytes_concat : ∀ (m : mem) b ofs bytes1 m1 bytes2 m2,
    storebytes m b ofs bytes1 = some m1 →
    storebytes m1 b (ofs + (bytes1.length : Z)) bytes2 = some m2 →
    storebytes m b ofs (bytes1 ++ bytes2) = some m2
  storebytes_split : ∀ (m : mem) b ofs bytes1 bytes2 m2,
    storebytes m b ofs (bytes1 ++ bytes2) = some m2 →
    ∃ m1, storebytes m b ofs bytes1 = some m1 ∧
      storebytes m1 b (ofs + (bytes1.length : Z)) bytes2 = some m2
  -- Properties of `alloc`
  alloc_result : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) → b = nextblock m1
  nextblock_alloc : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    nextblock m2 = (nextblock m1).succ
  valid_block_alloc : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ b', valid_block m1 b' → valid_block m2 b'
  fresh_block_alloc : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) → ¬ valid_block m1 b
  valid_new_block : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) → valid_block m2 b
  valid_block_alloc_inv : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ b', valid_block m2 b' → b' = b ∨ valid_block m1 b'
  perm_alloc_1 : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ b' ofs k p, perm m1 b' ofs k p → perm m2 b' ofs k p
  perm_alloc_2 : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ ofs k, lo ≤ ofs → ofs < hi → perm m2 b ofs k .Freeable
  perm_alloc_3 : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ ofs k p, perm m2 b ofs k p → lo ≤ ofs ∧ ofs < hi
  perm_alloc_4 : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ b' ofs k p, perm m2 b' ofs k p → b' ≠ b → perm m1 b' ofs k p
  perm_alloc_inv : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ b' ofs k p, perm m2 b' ofs k p →
    if b' = b then lo ≤ ofs ∧ ofs < hi else perm m1 b' ofs k p
  valid_access_alloc_other : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ chunk b' ofs p, valid_access m1 chunk b' ofs p → valid_access m2 chunk b' ofs p
  valid_access_alloc_same : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ chunk ofs, lo ≤ ofs → ofs + sizeChunk chunk ≤ hi → alignChunk chunk ∣ ofs →
    valid_access m2 chunk b ofs .Freeable
  valid_access_alloc_inv : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ chunk b' ofs p, valid_access m2 chunk b' ofs p →
    if b' = b then lo ≤ ofs ∧ ofs + sizeChunk chunk ≤ hi ∧ alignChunk chunk ∣ ofs
    else valid_access m1 chunk b' ofs p
  load_alloc_unchanged : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ chunk b' ofs, valid_block m1 b' → load chunk m2 b' ofs = load chunk m1 b' ofs
  load_alloc_other : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ chunk b' ofs v, load chunk m1 b' ofs = some v → load chunk m2 b' ofs = some v
  load_alloc_same : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ chunk ofs v, load chunk m2 b ofs = some v → v = .Vundef
  load_alloc_same' : ∀ (m1 : mem) lo hi m2 b, alloc m1 lo hi = (m2, b) →
    ∀ chunk ofs, lo ≤ ofs → ofs + sizeChunk chunk ≤ hi → alignChunk chunk ∣ ofs →
    load chunk m2 b ofs = some .Vundef
  -- Properties of `free`
  range_perm_free : ∀ (m1 : mem) b lo hi,
    range_perm m1 b lo hi .Cur .Freeable → { m2 : mem // free m1 b lo hi = some m2 }
  free_range_perm : ∀ (m1 : mem) bf lo hi m2,
    free m1 bf lo hi = some m2 → range_perm m1 bf lo hi .Cur .Freeable
  nextblock_free : ∀ (m1 : mem) bf lo hi m2,
    free m1 bf lo hi = some m2 → nextblock m2 = nextblock m1
  valid_block_free_1 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ b, valid_block m1 b → valid_block m2 b
  valid_block_free_2 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ b, valid_block m2 b → valid_block m1 b
  perm_free_1 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ b ofs k p, b ≠ bf ∨ ofs < lo ∨ hi ≤ ofs → perm m1 b ofs k p → perm m2 b ofs k p
  perm_free_2 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ ofs k p, lo ≤ ofs → ofs < hi → ¬ perm m2 bf ofs k p
  perm_free_3 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ b ofs k p, perm m2 b ofs k p → perm m1 b ofs k p
  valid_access_free_1 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ chunk b ofs p, valid_access m1 chunk b ofs p →
    b ≠ bf ∨ lo ≥ hi ∨ ofs + sizeChunk chunk ≤ lo ∨ hi ≤ ofs → valid_access m2 chunk b ofs p
  valid_access_free_2 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ chunk ofs p, lo < hi → ofs + sizeChunk chunk > lo → ofs < hi →
    ¬ valid_access m2 chunk bf ofs p
  valid_access_free_inv_1 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ chunk b ofs p, valid_access m2 chunk b ofs p → valid_access m1 chunk b ofs p
  valid_access_free_inv_2 : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ chunk ofs p, valid_access m2 chunk bf ofs p →
    lo ≥ hi ∨ ofs + sizeChunk chunk ≤ lo ∨ hi ≤ ofs
  load_free : ∀ (m1 : mem) bf lo hi m2, free m1 bf lo hi = some m2 →
    ∀ chunk b ofs, b ≠ bf ∨ lo ≥ hi ∨ ofs + sizeChunk chunk ≤ lo ∨ hi ≤ ofs →
    load chunk m2 b ofs = load chunk m1 b ofs
  -- Properties of `drop_perm`
  nextblock_drop : ∀ (m : mem) b lo hi p m',
    drop_perm m b lo hi p = some m' → nextblock m' = nextblock m
  drop_perm_valid_block_1 : ∀ (m : mem) b lo hi p m', drop_perm m b lo hi p = some m' →
    ∀ b', valid_block m b' → valid_block m' b'
  drop_perm_valid_block_2 : ∀ (m : mem) b lo hi p m', drop_perm m b lo hi p = some m' →
    ∀ b', valid_block m' b' → valid_block m b'
  range_perm_drop_1 : ∀ (m : mem) b lo hi p m',
    drop_perm m b lo hi p = some m' → range_perm m b lo hi .Cur .Freeable
  range_perm_drop_2 : ∀ (m : mem) b lo hi p,
    range_perm m b lo hi .Cur .Freeable → { m' : mem // drop_perm m b lo hi p = some m' }
  perm_drop_1 : ∀ (m : mem) b lo hi p m', drop_perm m b lo hi p = some m' →
    ∀ ofs k, lo ≤ ofs → ofs < hi → perm m' b ofs k p
  perm_drop_2 : ∀ (m : mem) b lo hi p m', drop_perm m b lo hi p = some m' →
    ∀ ofs k p', lo ≤ ofs → ofs < hi → perm m' b ofs k p' → permOrder p p' = true
  perm_drop_3 : ∀ (m : mem) b lo hi p m', drop_perm m b lo hi p = some m' →
    ∀ b' ofs k p', b' ≠ b ∨ ofs < lo ∨ hi ≤ ofs → perm m b' ofs k p' → perm m' b' ofs k p'
  perm_drop_4 : ∀ (m : mem) b lo hi p m', drop_perm m b lo hi p = some m' →
    ∀ b' ofs k p', perm m' b' ofs k p' → perm m b' ofs k p'
  load_drop : ∀ (m : mem) b lo hi p m', drop_perm m b lo hi p = some m' →
    ∀ chunk b' ofs,
    b' ≠ b ∨ ofs + sizeChunk chunk ≤ lo ∨ hi ≤ ofs ∨ permOrder p .Readable = true →
    load chunk m' b' ofs = load chunk m b' ofs
  -- Memory extensions
  extends_refl : ∀ m : mem, «extends» m m
  load_extends : ∀ chunk (m1 m2 : mem) b ofs v1, «extends» m1 m2 →
    load chunk m1 b ofs = some v1 → ∃ v2, load chunk m2 b ofs = some v2 ∧ Val.Lessdef v1 v2
  loadv_extends : ∀ chunk (m1 m2 : mem) addr1 addr2 v1, «extends» m1 m2 →
    loadv chunk m1 addr1 = some v1 → Val.Lessdef addr1 addr2 →
    ∃ v2, loadv chunk m2 addr2 = some v2 ∧ Val.Lessdef v1 v2
  loadbytes_extends : ∀ (m1 m2 : mem) b ofs len bytes1, «extends» m1 m2 →
    loadbytes m1 b ofs len = some bytes1 →
    ∃ bytes2, loadbytes m2 b ofs len = some bytes2 ∧ MemvalInjectList Val.inject_id bytes1 bytes2
  store_within_extends : ∀ chunk (m1 m2 : mem) b ofs v1 m1' v2, «extends» m1 m2 →
    store chunk m1 b ofs v1 = some m1' → Val.Lessdef v1 v2 →
    ∃ m2', store chunk m2 b ofs v2 = some m2' ∧ «extends» m1' m2'
  store_outside_extends : ∀ chunk (m1 m2 : mem) b ofs v m2', «extends» m1 m2 →
    store chunk m2 b ofs v = some m2' →
    (∀ ofs', perm m1 b ofs' .Cur .Readable → ofs ≤ ofs' → ofs' < ofs + sizeChunk chunk → False) →
    «extends» m1 m2'
  storev_extends : ∀ chunk (m1 m2 : mem) addr1 v1 m1' addr2 v2, «extends» m1 m2 →
    storev chunk m1 addr1 v1 = some m1' → Val.Lessdef addr1 addr2 → Val.Lessdef v1 v2 →
    ∃ m2', storev chunk m2 addr2 v2 = some m2' ∧ «extends» m1' m2'
  storebytes_within_extends : ∀ (m1 m2 : mem) b ofs bytes1 m1' bytes2, «extends» m1 m2 →
    storebytes m1 b ofs bytes1 = some m1' → MemvalInjectList Val.inject_id bytes1 bytes2 →
    ∃ m2', storebytes m2 b ofs bytes2 = some m2' ∧ «extends» m1' m2'
  storebytes_outside_extends : ∀ (m1 m2 : mem) b ofs bytes2 m2', «extends» m1 m2 →
    storebytes m2 b ofs bytes2 = some m2' →
    (∀ ofs', perm m1 b ofs' .Cur .Readable → ofs ≤ ofs' → ofs' < ofs + (bytes2.length : Z) →
      False) →
    «extends» m1 m2'
  alloc_extends : ∀ (m1 m2 : mem) lo1 hi1 b m1' lo2 hi2, «extends» m1 m2 →
    alloc m1 lo1 hi1 = (m1', b) → lo2 ≤ lo1 → hi1 ≤ hi2 →
    ∃ m2', alloc m2 lo2 hi2 = (m2', b) ∧ «extends» m1' m2'
  free_left_extends : ∀ (m1 m2 : mem) b lo hi m1', «extends» m1 m2 →
    free m1 b lo hi = some m1' → «extends» m1' m2
  free_right_extends : ∀ (m1 m2 : mem) b lo hi m2', «extends» m1 m2 →
    free m2 b lo hi = some m2' →
    (∀ ofs k p, perm m1 b ofs k p → lo ≤ ofs → ofs < hi → False) → «extends» m1 m2'
  free_parallel_extends : ∀ (m1 m2 : mem) b lo hi m1', «extends» m1 m2 →
    free m1 b lo hi = some m1' → ∃ m2', free m2 b lo hi = some m2' ∧ «extends» m1' m2'
  valid_block_extends : ∀ (m1 m2 : mem) b, «extends» m1 m2 →
    (valid_block m1 b ↔ valid_block m2 b)
  perm_extends : ∀ (m1 m2 : mem) b ofs k p, «extends» m1 m2 →
    perm m1 b ofs k p → perm m2 b ofs k p
  valid_access_extends : ∀ (m1 m2 : mem) chunk b ofs p, «extends» m1 m2 →
    valid_access m1 chunk b ofs p → valid_access m2 chunk b ofs p
  valid_pointer_extends : ∀ (m1 m2 : mem) b ofs, «extends» m1 m2 →
    valid_pointer m1 b ofs = true → valid_pointer m2 b ofs = true
  weak_valid_pointer_extends : ∀ (m1 m2 : mem) b ofs, «extends» m1 m2 →
    weak_valid_pointer m1 b ofs = true → weak_valid_pointer m2 b ofs = true
  -- Memory injections
  valid_block_inject_1 : ∀ f (m1 m2 : mem) b1 b2 delta,
    f b1 = some (b2, delta) → inject f m1 m2 → valid_block m1 b1
  valid_block_inject_2 : ∀ f (m1 m2 : mem) b1 b2 delta,
    f b1 = some (b2, delta) → inject f m1 m2 → valid_block m2 b2
  perm_inject : ∀ f (m1 m2 : mem) b1 b2 delta ofs k p,
    f b1 = some (b2, delta) → inject f m1 m2 → perm m1 b1 ofs k p → perm m2 b2 (ofs + delta) k p
  valid_access_inject : ∀ f (m1 m2 : mem) chunk b1 ofs b2 delta p,
    f b1 = some (b2, delta) → inject f m1 m2 → valid_access m1 chunk b1 ofs p →
    valid_access m2 chunk b2 (ofs + delta) p
  valid_pointer_inject : ∀ f (m1 m2 : mem) b1 ofs b2 delta,
    f b1 = some (b2, delta) → inject f m1 m2 → valid_pointer m1 b1 ofs = true →
    valid_pointer m2 b2 (ofs + delta) = true
  weak_valid_pointer_inject : ∀ f (m1 m2 : mem) b1 ofs b2 delta,
    f b1 = some (b2, delta) → inject f m1 m2 → weak_valid_pointer m1 b1 ofs = true →
    weak_valid_pointer m2 b2 (ofs + delta) = true
  address_inject : ∀ f (m1 m2 : mem) b1 ofs1 b2 delta p,
    inject f m1 m2 → perm m1 b1 (Ptrofs.unsigned ofs1) .Cur p → f b1 = some (b2, delta) →
    Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta
  valid_pointer_inject_no_overflow : ∀ f (m1 m2 : mem) b ofs b' delta,
    inject f m1 m2 → valid_pointer m1 b (Ptrofs.unsigned ofs) = true → f b = some (b', delta) →
    0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned
  weak_valid_pointer_inject_no_overflow : ∀ f (m1 m2 : mem) b ofs b' delta,
    inject f m1 m2 → weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
    f b = some (b', delta) →
    0 ≤ Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ∧
      Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) ≤ Ptrofs.max_unsigned
  valid_pointer_inject_val : ∀ f (m1 m2 : mem) b ofs b' ofs',
    inject f m1 m2 → valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
    Val.Inject f (.Vptr b ofs) (.Vptr b' ofs') → valid_pointer m2 b' (Ptrofs.unsigned ofs') = true
  weak_valid_pointer_inject_val : ∀ f (m1 m2 : mem) b ofs b' ofs',
    inject f m1 m2 → weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true →
    Val.Inject f (.Vptr b ofs) (.Vptr b' ofs') →
    weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true
  inject_no_overlap : ∀ f (m1 m2 : mem) b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
    inject f m1 m2 → b1 ≠ b2 → f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
    perm m1 b1 ofs1 .Max .Nonempty → perm m1 b2 ofs2 .Max .Nonempty →
    b1' ≠ b2' ∨ ofs1 + delta1 ≠ ofs2 + delta2
  different_pointers_inject : ∀ f (m m' : mem) b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
    inject f m m' → b1 ≠ b2 → valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
    valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
    f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
    b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))
  load_inject : ∀ f (m1 m2 : mem) chunk b1 ofs b2 delta v1,
    inject f m1 m2 → load chunk m1 b1 ofs = some v1 → f b1 = some (b2, delta) →
    ∃ v2, load chunk m2 b2 (ofs + delta) = some v2 ∧ Val.Inject f v1 v2
  loadv_inject : ∀ f (m1 m2 : mem) chunk a1 a2 v1,
    inject f m1 m2 → loadv chunk m1 a1 = some v1 → Val.Inject f a1 a2 →
    ∃ v2, loadv chunk m2 a2 = some v2 ∧ Val.Inject f v1 v2
  loadbytes_inject : ∀ f (m1 m2 : mem) b1 ofs len b2 delta bytes1,
    inject f m1 m2 → loadbytes m1 b1 ofs len = some bytes1 → f b1 = some (b2, delta) →
    ∃ bytes2, loadbytes m2 b2 (ofs + delta) len = some bytes2 ∧ MemvalInjectList f bytes1 bytes2
  store_mapped_inject : ∀ f chunk (m1 : mem) b1 ofs v1 n1 m2 b2 delta v2,
    inject f m1 m2 → store chunk m1 b1 ofs v1 = some n1 → f b1 = some (b2, delta) →
    Val.Inject f v1 v2 → ∃ n2, store chunk m2 b2 (ofs + delta) v2 = some n2 ∧ inject f n1 n2
  store_unmapped_inject : ∀ f chunk (m1 : mem) b1 ofs v1 n1 m2,
    inject f m1 m2 → store chunk m1 b1 ofs v1 = some n1 → f b1 = none → inject f n1 m2
  store_outside_inject : ∀ f (m1 m2 : mem) chunk b ofs v m2',
    inject f m1 m2 →
    (∀ b' delta ofs', f b' = some (b, delta) → perm m1 b' ofs' .Cur .Readable →
      ofs ≤ ofs' + delta → ofs' + delta < ofs + sizeChunk chunk → False) →
    store chunk m2 b ofs v = some m2' → inject f m1 m2'
  storev_mapped_inject : ∀ f chunk (m1 : mem) a1 v1 n1 m2 a2 v2,
    inject f m1 m2 → storev chunk m1 a1 v1 = some n1 → Val.Inject f a1 a2 →
    Val.Inject f v1 v2 → ∃ n2, storev chunk m2 a2 v2 = some n2 ∧ inject f n1 n2
  storebytes_mapped_inject : ∀ f (m1 : mem) b1 ofs bytes1 n1 m2 b2 delta bytes2,
    inject f m1 m2 → storebytes m1 b1 ofs bytes1 = some n1 → f b1 = some (b2, delta) →
    MemvalInjectList f bytes1 bytes2 →
    ∃ n2, storebytes m2 b2 (ofs + delta) bytes2 = some n2 ∧ inject f n1 n2
  storebytes_unmapped_inject : ∀ f (m1 : mem) b1 ofs bytes1 n1 m2,
    inject f m1 m2 → storebytes m1 b1 ofs bytes1 = some n1 → f b1 = none → inject f n1 m2
  storebytes_outside_inject : ∀ f (m1 m2 : mem) b ofs bytes2 m2',
    inject f m1 m2 →
    (∀ b' delta ofs', f b' = some (b, delta) → perm m1 b' ofs' .Cur .Readable →
      ofs ≤ ofs' + delta → ofs' + delta < ofs + (bytes2.length : Z) → False) →
    storebytes m2 b ofs bytes2 = some m2' → inject f m1 m2'
  alloc_right_inject : ∀ f (m1 m2 : mem) lo hi b2 m2',
    inject f m1 m2 → alloc m2 lo hi = (m2', b2) → inject f m1 m2'
  alloc_left_unmapped_inject : ∀ f (m1 m2 : mem) lo hi m1' b1,
    inject f m1 m2 → alloc m1 lo hi = (m1', b1) →
    ∃ f', inject f' m1' m2 ∧ Val.inject_incr f f' ∧ f' b1 = none ∧ (∀ b, b ≠ b1 → f' b = f b)
  alloc_left_mapped_inject : ∀ f (m1 m2 : mem) lo hi m1' b1 b2 delta,
    inject f m1 m2 → alloc m1 lo hi = (m1', b1) → valid_block m2 b2 →
    0 ≤ delta → delta ≤ Ptrofs.max_unsigned →
    (∀ ofs k p, perm m2 b2 ofs k p → delta = 0 ∨ (0 ≤ ofs ∧ ofs < Ptrofs.max_unsigned)) →
    (∀ ofs k p, lo ≤ ofs → ofs < hi → perm m2 b2 (ofs + delta) k p) →
    inj_offset_aligned delta (hi - lo) →
    (∀ b delta' ofs k p, f b = some (b2, delta') → perm m1 b ofs k p →
      lo + delta ≤ ofs + delta' → ofs + delta' < hi + delta → False) →
    ∃ f', inject f' m1' m2 ∧ Val.inject_incr f f' ∧ f' b1 = some (b2, delta) ∧
      (∀ b, b ≠ b1 → f' b = f b)
  alloc_parallel_inject : ∀ f (m1 m2 : mem) lo1 hi1 m1' b1 lo2 hi2,
    inject f m1 m2 → alloc m1 lo1 hi1 = (m1', b1) → lo2 ≤ lo1 → hi1 ≤ hi2 →
    ∃ f' m2' b2, alloc m2 lo2 hi2 = (m2', b2) ∧ inject f' m1' m2' ∧ Val.inject_incr f f' ∧
      f' b1 = some (b2, 0) ∧ (∀ b, b ≠ b1 → f' b = f b)
  free_inject : ∀ f (m1 : mem) l m1' m2 b lo hi m2',
    inject f m1 m2 → free_list m1 l = some m1' → free m2 b lo hi = some m2' →
    (∀ b1 delta ofs k p, f b1 = some (b, delta) → perm m1 b1 ofs k p →
      lo ≤ ofs + delta → ofs + delta < hi →
      ∃ lo1 hi1, (b1, lo1, hi1) ∈ l ∧ lo1 ≤ ofs ∧ ofs < hi1) →
    inject f m1' m2'
  free_parallel_inject : ∀ f (m1 m2 : mem) b lo hi m1' b' delta,
    inject f m1 m2 → free m1 b lo hi = some m1' → f b = some (b', delta) →
    ∃ m2', free m2 b' (lo + delta) (hi + delta) = some m2' ∧ inject f m1' m2'
  drop_outside_inject : ∀ f (m1 m2 : mem) b lo hi p m2',
    inject f m1 m2 → drop_perm m2 b lo hi p = some m2' →
    (∀ b' delta ofs k p, f b' = some (b, delta) → perm m1 b' ofs k p →
      lo ≤ ofs + delta → ofs + delta < hi → False) →
    inject f m1 m2'
  -- Memory states that inject into themselves
  neutral_inject : ∀ m : mem, inject_neutral (nextblock m) m →
    inject (flat_inj (nextblock m)) m m
  empty_inject_neutral : ∀ thr, inject_neutral thr (empty : mem)
  alloc_inject_neutral : ∀ thr (m : mem) lo hi b m',
    alloc m lo hi = (m', b) → inject_neutral thr m → nextblock m < thr → inject_neutral thr m'
  store_inject_neutral : ∀ chunk (m : mem) b ofs v m' thr,
    store chunk m b ofs v = some m' → inject_neutral thr m → b < thr →
    Val.Inject (flat_inj thr) v v → inject_neutral thr m'
  drop_inject_neutral : ∀ (m : mem) b lo hi p m' thr,
    drop_perm m b lo hi p = some m' → inject_neutral thr m → b < thr → inject_neutral thr m'

end Memtype
end CC
