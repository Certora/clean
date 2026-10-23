/-
  Differential test SUBJECT for CCLib/common/Memory.lean.

  Kept in lockstep with `mem_oracle.ml`, which runs the same scenarios against
  CompCert's extracted memory model.  (CompCert's `Mem.store`/`load`/`free`
  cannot be evaluated by Coq's `Compute` — `range_perm_dec` uses well-founded
  recursion over an opaque accessibility proof — so the oracle is the OCaml
  extraction, which is what CompCert's own interpreter runs.)

  Every value observation prints three lines: tag, then payload (block number
  for a pointer), then 0 (offset for a pointer).

  Run with:  lean --run MemDiff.lean
-/
import CCLib
open CC

def outi (i : Int) : IO Unit := IO.println (toString i)

def vtag : Val → Int
  | .Vundef => 0 | .Vint _ => 1 | .Vlong _ => 2
  | .Vfloat _ => 3 | .Vsingle _ => 4 | .Vptr _ _ => 5

def outv (v : Val) : IO Unit := do
  outi (vtag v)
  match v with
  | .Vundef => outi 0; outi 0
  | .Vint n => outi (Integers.Int.unsigned n); outi 0
  | .Vlong n => outi (Integers.Int64.unsigned n); outi 0
  | .Vfloat f => outi (Integers.Int64.unsigned (Floats.Float.toBits f)); outi 0
  | .Vsingle f => outi (Integers.Int.unsigned (Floats.Float32.toBits f)); outi 0
  | .Vptr b ofs => outi (b.toNat : Int); outi (Integers.Ptrofs.unsigned ofs)

def outov : Option Val → IO Unit
  | none => do outi (-1); outi 0; outi 0
  | some v => outv v

def bcode (b : Bool) : Int := if b then 1 else 0
def omcode : Option Mem → Int | none => -1 | some _ => 1

def ld (chunk : Chunk) (om : Option Mem) (b : Block) (ofs : Z) : IO Unit :=
  match om with
  | none => do outi (-2); outi 0; outi 0
  | some m => outov (Mem.load chunk m b ofs)

def vp (om : Option Mem) (b : Block) (ofs : Z) : IO Unit :=
  match om with
  | none => outi (-2)
  | some m => outi (bcode (Mem.validPointer m b ofs))

def nb : Option Mem → IO Unit
  | none => outi (-2)
  | some m => outi (m.nextblock.toNat : Int)

def vint (k : Z) : Val := .Vint (Integers.Int.repr k)
def vlong (k : Z) : Val := .Vlong (Integers.Int64.repr k)
def ptrofs (k : Z) : Integers.Ptrofs := Integers.Ptrofs.repr k

def main : IO Unit := do
  -- scenario setup
  let m0 := Mem.empty
  let (m1, bb) := Mem.alloc m0 0 16

  -- nextblock and freshness
  outi (m0.nextblock.toNat : Int)
  outi (m1.nextblock.toNat : Int)
  outi (bb.toNat : Int)
  outi (bcode (Mem.validBlock m0 bb))
  outi (bcode (Mem.validBlock m1 bb))

  -- permissions on a fresh block
  outi (bcode (Mem.validPointer m1 bb 0))
  outi (bcode (Mem.validPointer m1 bb 15))
  outi (bcode (Mem.validPointer m1 bb 16))
  outi (bcode (Mem.validPointer m1 bb (-1)))
  outi (bcode (Mem.weakValidPointer m1 bb 16))
  outi (bcode (Mem.weakValidPointer m1 bb 17))

  -- fresh memory reads as Undef
  ld Chunk.Mint32 (some m1) bb 0
  ld Chunk.Mint8unsigned (some m1) bb 3

  -- stores and loads
  let s32 := Mem.store Chunk.Mint32 m1 bb 0 (vint 1234567)
  outi (omcode s32)
  ld Chunk.Mint32 s32 bb 0
  ld Chunk.Mint8unsigned s32 bb 0
  ld Chunk.Mint8unsigned s32 bb 1
  ld Chunk.Mint8signed s32 bb 0
  ld Chunk.Mint16unsigned s32 bb 0
  ld Chunk.Mint64 s32 bb 0

  outi (omcode (Mem.store Chunk.Mint32 m1 bb 1 (vint 1)))
  outi (omcode (Mem.store Chunk.Mint32 m1 bb 2 (vint 1)))
  outi (omcode (Mem.store Chunk.Mint32 m1 bb 16 (vint 1)))
  outi (omcode (Mem.store Chunk.Mint32 m1 bb (-4) (vint 1)))
  outi (omcode (Mem.store Chunk.Mint64 m1 bb 0 (vlong 42)))
  outi (omcode (Mem.store Chunk.Mint64 m1 bb 8 (vlong 42)))

  let s64 := Mem.store Chunk.Mint64 m1 bb 0 (vlong 1234567890123)
  ld Chunk.Mint64 s64 bb 0
  ld Chunk.Mint32 s64 bb 0
  ld Chunk.Mint32 s64 bb 4

  -- float round trip through memory
  let dbl : Val := .Vfloat (Floats.Float.ofBits (Integers.Int64.repr 4611686018427387904))
  let sf := Mem.store Chunk.Mfloat64 m1 bb 0 dbl
  ld Chunk.Mfloat64 sf bb 0
  ld Chunk.Mint64 sf bb 0
  let sgl : Val := .Vsingle (Floats.Float32.ofBits (Integers.Int.repr 1065353216))
  let sfs := Mem.store Chunk.Mfloat32 m1 bb 0 sgl
  ld Chunk.Mfloat32 sfs bb 0
  ld Chunk.Mint32 sfs bb 0

  -- pointers in memory: the Fragment machinery
  let sp := Mem.store Chunk.Mint64 m1 bb 0 (.Vptr bb (ptrofs 8))
  ld Chunk.Mint64 sp bb 0
  let sp' := match sp with
             | none => none
             | some m => Mem.store Chunk.Mint8unsigned m bb 3 (vint 0)
  ld Chunk.Mint64 sp' bb 0
  ld Chunk.Mint32 sp bb 0
  let sany := Mem.store Chunk.Many64 m1 bb 0 (.Vptr bb (ptrofs 8))
  ld Chunk.Many64 sany bb 0

  -- storebytes
  let bytes := encodeVal Chunk.Mint32 (vint 7)
  let sb := Mem.storebytes m1 bb 0 bytes
  outi (omcode sb)
  ld Chunk.Mint32 sb bb 0
  outi (omcode (Mem.storebytes m1 bb 1 bytes))
  outi (omcode (Mem.storebytes m1 bb 13 bytes))

  -- freeing
  let f1 := Mem.free m1 bb 0 16
  outi (omcode f1)
  vp f1 bb 0
  ld Chunk.Mint32 f1 bb 0
  nb f1
  let f2 := Mem.free m1 bb 0 8
  outi (omcode f2)
  vp f2 bb 0
  vp f2 bb 8
  outi (omcode (Mem.free m1 bb 0 32))
  outi (omcode (Mem.free m0 bb 0 16))
  outi (omcode (match f1 with | none => none | some m => Mem.free m bb 0 16))

  -- two blocks are independent
  let (m2, bb2) := Mem.alloc m1 0 8
  outi (bb2.toNat : Int)
  let t1 := Mem.store Chunk.Mint32 m2 bb 0 (vint 111)
  let t2 := match t1 with
            | none => none
            | some m => Mem.store Chunk.Mint32 m bb2 0 (vint 222)
  ld Chunk.Mint32 t2 bb 0
  ld Chunk.Mint32 t2 bb2 0
  let t3 := match t2 with | none => none | some m => Mem.free m bb2 0 8
  ld Chunk.Mint32 t3 bb 0
  ld Chunk.Mint32 t3 bb2 0

  -- free_list
  outi (omcode (Mem.freeList m2 [(bb, 0, 16), (bb2, 0, 8)]))
  outi (omcode (Mem.freeList m2 [(bb2, 0, 8), (bb, 0, 16)]))
  outi (omcode (Mem.freeList m2 [(bb, 0, 16), (bb, 0, 16)]))
  outi (omcode (Mem.freeList m2 []))
