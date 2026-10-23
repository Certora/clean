/-
  The no-wrap-around check of `Mem.loadv` / `Mem.storev`.

  In `common/Memory.v`, `loadv`/`storev` fail when
  `Ptrofs.unsigned ofs + size_chunk chunk > Ptrofs.modulus`, i.e. when the
  access would run past the end of the address space.  The Lean port now does
  the same.  The check only matters for blocks larger than `2^64` bytes and for
  the 8-byte chunks that are only 4-byte aligned (`Mfloat64`, `Many64`); this
  file builds such a block and shows that

  * the raw `load` at offset `2^64 - 4` succeeds, but
  * `loadv` through the pointer `(b, 2^64 - 4)` fails, as in CompCert, and
  * for every other chunk `loadv` is just `load` (`Mem.loadv_ptr` with the
    default `ChunkNoWrap` argument).
-/
import CCLib
open CC

namespace LoadvWrapCheck

/-- A block of `2^64 + 8` bytes. -/
def big : Mem × Block := Mem.alloc Mem.empty 0 (2 ^ 64 + 8)

def m : Mem := big.1
def b : Block := big.2

/-- The last 4-aligned offset below `2^64`. -/
def top : Integers.Ptrofs := Integers.Ptrofs.repr (2 ^ 64 - 4)

theorem top_unsigned : Integers.Ptrofs.unsigned top = 2 ^ 64 - 4 := by decide

/-- The raw `load` of a `double` straddling `2^64` succeeds … -/
theorem load_succeeds :
    (Mem.load .Mfloat64 m b (2 ^ 64 - 4)).isSome = true := by
  unfold Mem.load
  rw [if_pos]
  · rfl
  · simp only [Mem.validAccess, Bool.and_eq_true, beq_iff_eq]
    refine ⟨Mem.rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => ?_, by decide⟩
    exact Mem.perm_implies (Mem.perm_alloc_same Mem.empty 0 (2 ^ 64 + 8) o .Cur
      (by omega) (by simp only [sizeChunk] at h2; omega)) rfl

/-- … but `loadv` through the pointer rejects it, as CompCert's `Mem.loadv` does. -/
theorem loadv_rejects_wrap : Mem.loadv .Mfloat64 m (.Vptr b top) = none := by
  simp only [Mem.loadv, top_unsigned]
  rw [if_neg (by decide)]

/-- Likewise for `storev`. -/
theorem storev_rejects_wrap (v : Val) : Mem.storev .Mfloat64 m (.Vptr b top) v = none := by
  simp only [Mem.storev, top_unsigned]
  rw [if_neg (by decide)]

/-- For a chunk whose alignment equals its size, `loadv` is `load`
    unconditionally. -/
example (mem : Mem) (blk : Block) (ofs : Integers.Ptrofs) :
    Mem.loadv .Mint32 mem (.Vptr blk ofs) = Mem.load .Mint32 mem blk (Integers.Ptrofs.unsigned ofs) :=
  Mem.loadv_ptr _ _ _ _ (Or.inl rfl)

end LoadvWrapCheck
