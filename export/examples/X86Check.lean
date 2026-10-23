/-
  Checks for the x86-64 back end (`CCLib/x86/…`) and the per-target
  parameters (`CCLib/targets/Archi.lean`).
-/
import CCLib.targets.Archi
import CCLib.x86.OpInject
import CCLib.x86.Asmgen

namespace X86Check
open CC

/-! ## Target parameters -/

/-- NaN propagation differs between targets: given a quiet NaN followed by a
signaling NaN, x86 returns the first NaN, AArch64 the signaling one, and
RISC-V always the canonical NaN. -/
example : Targets.x86_64.choose_nan_64 [(true, 2 ^ 51), (false, 1)] = (true, 2 ^ 51) := by
  decide
example : Targets.aarch64.choose_nan_64 [(true, 2 ^ 51), (false, 1)] = (false, 1) := by
  decide
example : (Targets.riscV true).choose_nan_64 [(true, 2 ^ 51), (false, 1)] = (false, 2 ^ 51) := by
  decide
example : Targets.x86_32.ptr64 = false ∧ Targets.x86_32.align_int64 = 4 := ⟨rfl, rfl⟩
example : (Targets.powerpc false).big_endian = true := rfl

/-! ## x86 operators -/

/-- `lea 4(%r1)` in 32-bit mode adds 4. -/
example {F V : Type} (ge : Genv F V) (sp : Val) (m : Mem) :
    X86.Op.evalOperation ge sp (.Olea (.Aindexed 4)) [.Vint (Integers.Int.repr 3)] m =
      some (.Vint (Integers.Int.repr 7)) := rfl

/-- `leaq 8(%r1,%r2,4)` computes `r1 + r2 * 4 + 8`. -/
example {F V : Type} (ge : Genv F V) (sp : Val) (m : Mem) :
    X86.Op.evalOperation ge sp (.Oleal (.Aindexed2scaled 4 8))
      [.Vlong (Integers.Int64.repr 100), .Vlong (Integers.Int64.repr 3)] m =
      some (.Vlong (Integers.Int64.repr 120)) := rfl

/-- Signed division by zero is undefined. -/
example {F V : Type} (ge : Genv F V) (sp : Val) (m : Mem) :
    X86.Op.evalOperation ge sp .Odiv [.Vint (Integers.Int.repr 3), .Vint Integers.Int.zero] m =
      none := rfl

/-- `maxsd` returns the second argument when the first is not greater. -/
example : X86.Op.floatMax Floats.Float.zero Floats.Float.zero = Floats.Float.zero := by decide

/-! ## x86-64 calling conventions -/

/-- ELF ABI: the first six integer arguments go in `DI SI DX CX R8 R9`, the
seventh on the stack. -/
example : X86.Conventions1.locArguments false
      (mksignature (List.replicate 7 .Xint) .Xint cc_default) =
    [.One (.R .DI), .One (.R .SI), .One (.R .DX), .One (.R .CX), .One (.R .R8), .One (.R .R9),
     .One (.S .Outgoing 0 .Tint)] := by decide

/-- Win64 ABI: arguments use `CX DX R8 R9` / `XMM0-3` by position. -/
example : X86.Conventions1.locArguments true
      (mksignature [.Xint, .Xfloat, .Xlong] .Xvoid cc_default) =
    [.One (.R .CX), .One (.R .X1), .One (.R .R8)] := by decide

/-- Results are in `RAX` (integers) or `XMM0` (floats). -/
example : X86.Conventions1.locResult (mksignature [] .Xfloat cc_default) = .One .X0 := rfl

/-- `SI` and `DI` are caller-save in the ELF ABI and callee-save in Win64. -/
example : X86.Conventions1.isCalleeSave false .SI = false ∧
    X86.Conventions1.isCalleeSave true .SI = true := ⟨rfl, rfl⟩

/-! ## x86 code generation -/

/-- A Mach function returning the constant 5. -/
def retFive : X86.Mach.Function where
  fn_sig := mksignature [] .Xint cc_default
  fn_code := [.Mop (.Ointconst (Integers.Int.repr 5)) [] .AX, .Mreturn]
  fn_stacksize := 16
  fn_link_ofs := Integers.Ptrofs.zero
  fn_retaddr_ofs := Integers.Ptrofs.repr 8

/-- It is translated to `Pallocframe; movl $5, %eax; Pfreeframe; ret`. -/
example : (match X86.Asmgen.transfFunction retFive with
    | .OK tf => tf.fn_code.length
    | .Error _ => 0) = 4 := by decide

/-- Two-address operations whose result is not their first argument are
rejected. -/
example : (match X86.Asmgen.translOp .Oneg [.BX] .CX [] with
    | .OK _ => false
    | .Error _ => true) = true := by decide

/-- Division must use `AX`/`CX`. -/
example : (match X86.Asmgen.translOp .Odiv [.AX, .CX] .AX [] with
    | .OK c => c.length
    | .Error _ => 0) = 2 := by decide

/-! ## x86 assembly semantics -/

/-- After `cmpl` of `1` and `2`, the "less than" condition holds. -/
example (m : Mem) (rs : X86.Asm.Regset) :
    X86.Asm.evalTestcond .Cond_l
      (X86.Asm.compareInts (.Vint (Integers.Int.repr 1)) (.Vint (Integers.Int.repr 2)) rs m) =
      some true := rfl

/-- …and the unsigned "above" condition does not. -/
example (m : Mem) (rs : X86.Asm.Regset) :
    X86.Asm.evalTestcond .Cond_a
      (X86.Asm.compareInts (.Vint (Integers.Int.repr 1)) (.Vint (Integers.Int.repr 2)) rs m) =
      some false := rfl

end X86Check
