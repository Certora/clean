/-
  Checks for the RISC-V back end (`CCLib/riscV/…`).
-/
import CCLib.riscV.OpInject
import CCLib.riscV.Asmgen

namespace RiscVCheck
open CC

/-! ## RISC-V operators -/

/-- `addi` with immediate `4`. -/
example {F V : Type} (ge : Genv F V) (sp : Val) (m : Mem) :
    RiscV.Op.evalOperation ge sp (.Oaddimm (Integers.Int.repr 4)) [.Vint (Integers.Int.repr 3)] m =
      some (.Vint (Integers.Int.repr 7)) := rfl

/-- Unsigned conversion float → int is a native RISC-V operator. -/
example {F V : Type} (ge : Genv F V) (sp : Val) (m : Mem) :
    RiscV.Op.evalOperation ge sp .Ointuoffloat [.Vint Integers.Int.zero] m = none := rfl

/-- Constants that fit in 12 bits are "trivial" for CSE; larger ones are not. -/
example : RiscV.Op.isTrivialOp (.Ointconst (Integers.Int.repr 2047)) = true := by decide
example : RiscV.Op.isTrivialOp (.Ointconst (Integers.Int.repr 2048)) = false := by decide

/-! ## RISC-V calling conventions -/

/-- The first eight integer arguments go in `a0`–`a7` (`x10`–`x17`), the
ninth on the stack. -/
example : RiscV.Conventions1.locArguments
      (mksignature (List.replicate 9 .Xint) .Xint cc_default) =
    [.One (.R .R10), .One (.R .R11), .One (.R .R12), .One (.R .R13), .One (.R .R14),
     .One (.R .R15), .One (.R .R16), .One (.R .R17), .One (.S .Outgoing 0 .Tint)] := by decide

/-- Fixed FP arguments go in `fa0`… -/
example : RiscV.Conventions1.locArguments
      (mksignature [.Xint, .Xfloat] .Xvoid cc_default) =
    [.One (.R .R10), .One (.R .F10)] := by decide

/-- …but a variadic FP argument is put in an extra FP register and reserves
the next integer register. -/
example : RiscV.Conventions1.locArguments
      (mksignature [.Xint, .Xfloat, .Xint] .Xvoid { cc_default with cc_vararg := some 1 }) =
    [.One (.R .R10), .One (.R .F1), .One (.R .R12)] := by decide

/-- Results are in `a0` (integers) or `fa0` (floats). -/
example : RiscV.Conventions1.locResult (mksignature [] .Xfloat cc_default) = .One .F10 := rfl
example : RiscV.Conventions1.locResult (mksignature [] .Xlong cc_default) = .One .R10 := rfl

/-! ## RISC-V code generation -/

/-- `0x12345` does not fit in 12 bits: it is split into `lui 0x12; addi 0x345`. -/
example : (match RiscV.Asmgen.makeImmed32 (Integers.Int.repr 0x12345) with
    | .Imm32_pair hi lo => (Integers.Int.unsigned hi, Integers.Int.signed lo)
    | .Imm32_single _ => (0, 0)) = (0x12, 0x345) := by decide

/-- `0x12fff`: the low part is sign-extended, so the high part is rounded up. -/
example : (match RiscV.Asmgen.makeImmed32 (Integers.Int.repr 0x12fff) with
    | .Imm32_pair hi lo => (Integers.Int.unsigned hi, Integers.Int.signed lo)
    | .Imm32_single _ => (0, 0)) = (0x13, -1) := by decide

/-- A Mach function returning the constant 5. -/
def retFive : RiscV.Mach.Function where
  fn_sig := mksignature [] .Xint cc_default
  fn_code := [.Mop (.Ointconst (Integers.Int.repr 5)) [] .R10, .Mreturn]
  fn_stacksize := 16
  fn_link_ofs := Integers.Ptrofs.zero
  fn_retaddr_ofs := Integers.Ptrofs.repr 8

/-- It is translated to `Pallocframe; sd ra; .cfi; addiw a0, x0, 5; ld ra;
Pfreeframe; jr ra`. -/
example : (match RiscV.Asmgen.transfFunction {} retFive with
    | .OK tf => tf.fn_code.length
    | .Error _ => 0) = 7 := by decide

/-- `Ocast32signed` must have the same source and destination register. -/
example : (match RiscV.Asmgen.translOp {} .Ocast32signed [.R5] .R6 [] with
    | .OK _ => false
    | .Error _ => true) = true := by decide

/-! ## RISC-V assembly semantics -/

/-- `x0` reads as zero. -/
example (rs : RiscV.Asm.Regset) : RiscV.Asm.get0w rs .X0 = .Vint Integers.Int.zero := rfl

/-- `lui` loads its immediate shifted by 12. -/
example (sym : RiscV.Asm.HalfSplit) (ge : RiscV.Asm.CGenv) (f : RiscV.Asm.Function)
    (rs : RiscV.Asm.Regset) (m : Mem) :
    RiscV.Asm.execInstr sym ge f (.Pluiw .X5 (Integers.Int.repr 1)) rs m =
      .Next (RiscV.Asm.nextinstr (rs.set (.IR .X5) (.Vint (Integers.Int.repr 4096)))) m := by
  rfl

end RiscVCheck
