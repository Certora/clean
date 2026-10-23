/-
  Non-vacuity checks for memory extensions and injections
  (`CCLib/common/MemoryExtends.lean`, `CCLib/common/MemoryInjections.lean`).

  `Mem.Extends` and `Mem.Inject` are records of seven conditions each; a typo
  in one of them could make the relation unsatisfiable, and then every theorem
  about it would hold vacuously.  This file exhibits concrete memories related
  by both, and runs a load and a store through the transfer theorems.
-/
import CCLib
open CC

namespace MemInjCheck

def blk : Mem × Block := Mem.alloc Mem.empty 0 8
def m0 : Mem := blk.1
def b0 : Block := blk.2

/-- A memory extends itself. -/
theorem m0_extends : Mem.Extends m0 m0 := Mem.extends_refl m0

/-- The one-block memory is related to itself by the flat injection below its
    `nextblock`, built with `empty_inject_neutral`, `alloc_inject_neutral` and
    `neutral_inject` — so `Mem.Inject` is satisfiable on a non-empty memory. -/
theorem m0_inject : Mem.Inject (Mem.flatInj m0.nextblock) m0 m0 := by
  apply Mem.neutral_inject
  exact Mem.alloc_inject_neutral (rfl : Mem.alloc Mem.empty 0 8 = (m0, b0))
    (Mem.empty_inject_neutral _) (by decide)

/-- A store into the block, transported through the injection. -/
theorem store_transported :
    ∃ m1 m2, Mem.store .Mint32 m0 b0 0 (.Vint (Integers.Int.repr 7)) = some m1 ∧
      Mem.store .Mint32 m0 b0 (0 + 0) (.Vint (Integers.Int.repr 7)) = some m2 ∧
      Mem.Inject (Mem.flatInj m0.nextblock) m1 m2 := by
  obtain ⟨m1, hs⟩ := Mem.valid_access_store (chunk := .Mint32) (m := m0) (b := b0) (ofs := 0)
    (.Vint (Integers.Int.repr 7)) (by decide)
  obtain ⟨m2, hs2, hi⟩ := Mem.store_mapped_inject m0_inject hs
    (show Mem.flatInj m0.nextblock b0 = some (b0, 0) by decide) (.int _)
  exact ⟨m1, m2, hs, hs2, hi⟩

/-- … and the value read back through the injection is the one stored. -/
theorem load_transported :
    ∀ m1, Mem.store .Mint32 m0 b0 0 (.Vint (Integers.Int.repr 7)) = some m1 →
      ∃ v2, Mem.load .Mint32 m1 b0 (0 + 0) = some v2 ∧
        Val.Inject (Mem.flatInj m0.nextblock) (.Vint (Integers.Int.repr 7)) v2 := by
  intro m1 hs
  obtain ⟨m2, hs2, hi⟩ := Mem.store_mapped_inject m0_inject hs
    (show Mem.flatInj m0.nextblock b0 = some (b0, 0) by decide) (.int _)
  rw [Int.add_zero, hs] at hs2
  cases hs2
  exact Mem.load_inject hi (Mem.load_store_same hs)
    (show Mem.flatInj m0.nextblock b0 = some (b0, 0) by decide)

end MemInjCheck
