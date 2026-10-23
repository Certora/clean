/-
  Checks of the operator printers of the ARM and PowerPC back ends
  (`CCLib/arm/PrintOp.lean`, `CCLib/powerpc/PrintOp.lean`, ports of
  `arm/PrintOp.ml` and `powerpc/PrintOp.ml`): the strings agree with what the
  OCaml `fprintf` formats produce.
-/
import CCLib.arm.PrintOp
import CCLib.powerpc.PrintOp

open CC

private def r (n : Nat) : String := s!"x{n}"

/-- ARM: `Oaddimm` prints a signed 32-bit immediate. -/
example : Arm.PrintOp.printOperation r (.Oaddimm (Integers.Int.repr (-4))) [1] = "x1 + -4" := by
  native_decide

/-- ARM: a shifted operand. -/
example : Arm.PrintOp.printOperation r
    (.Orsubshift (.Slsl ⟨Integers.Int.repr 3, by decide⟩)) [1, 2] = "x2 << 3 - x1" := by
  native_decide

/-- ARM: `Omulhs` has no case in `arm/PrintOp.ml`. -/
example : Arm.PrintOp.printOperation r .Omulhs [1, 2] = "<bad operator>" := by native_decide

/-- PowerPC: rotate-and-mask, with the mask in hexadecimal. -/
example : PowerPC.PrintOp.printOperation r
    (.Orolm (Integers.Int.repr 8) (Integers.Int.repr 255)) [3] = "(x3 rol 8) & 0xff" := by
  native_decide

/-- PowerPC: a comparison with a 64-bit immediate. -/
example : PowerPC.PrintOp.printCondition r
    (.Ccomplimm .Cle (Integers.Int64.repr (-1))) [5] = "x5 <=ls -1" := by native_decide
