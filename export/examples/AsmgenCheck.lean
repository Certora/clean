/-
  Checks for the port of `aarch64/Asmgen.v` (`CCLib/aarch64/Asmgen.lean`).
-/
import CCLib.aarch64.Asmgen

namespace AsmgenCheck
open CC Asmgen

/-! Logical and arithmetic immediates. -/

example : isLogicalImm32 (Integers.Int.repr 0xFF) = true := by decide
example : isLogicalImm32 (Integers.Int.repr 0x00FF00FF) = true := by decide
example : isLogicalImm32 (Integers.Int.repr 0x123) = false := by decide
example : isLogicalImm32 Integers.Int.zero = false := by decide
example : isLogicalImm64 (Integers.Int64.repr 0x0F0F0F0F0F0F0F0F) = true := by decide
example : isArithImm32 (Integers.Int.repr 0x5000) = true := by decide
example : isArithImm32 (Integers.Int.repr 0x5001) = false := by decide

/-! Decomposition of literals into 16-bit fragments. -/

example : decomposeInt 4 0x123400005678 0 = [(0x5678, 0), (0x1234, 32)] := by decide
example : decomposeInt 2 0 0 = [] := by decide

/-- `0x123400005678` needs a `movz` and one `movk`. -/
example : (loadimm64 .X0 (Integers.Int64.repr 0x123400005678) []).length = 2 := by decide
/-- `-2` is a logical immediate: one `orr`. -/
example : (loadimm64 .X0 (Integers.Int64.repr (-2)) []).length = 1 := by decide
/-- `-0x10001` (`0xFFFFFFFFFFFEFFFF`) is cheapest as `movn`. -/
example : (loadimm64 .X0 (Integers.Int64.repr (-0x10001)) []).length = 1 := by decide

/-! A whole function: `return 0x12345678;` with a 16-byte frame. -/

def f : Mach.Function :=
  { fn_sig := { sig_args := [], sig_res := .Xint, sig_cc := default }
    fn_code := [.Mop (.Ointconst (Integers.Int.repr 0x12345678)) [] .R0, .Mreturn]
    fn_stacksize := 16
    fn_link_ofs := Integers.Ptrofs.repr 0
    fn_retaddr_ofs := Integers.Ptrofs.repr 8 }

/-- `Pallocframe`, `Pcfi_rel_offset`, `movz` + `movk` for the constant,
    `ldr x30` + `Pfreeframe` for the epilogue, and `ret`. -/
example : ((transfFunction {} f).toOption.map (·.fn_code.length)) = some 7 := by decide

/-- The two code translations agree on it. -/
example : translCode' {} f f.fn_code true = translCode {} f f.fn_code true :=
  transl_code'_transl_code _ _ _ _

/-- An ill-formed operation (a float register as destination of an
    integer constant) is rejected. -/
example : (translOp {} (.Ointconst Integers.Int.zero) [] .F0 []).isOK = false := by decide

end AsmgenCheck
