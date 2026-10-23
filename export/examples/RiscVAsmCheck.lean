/-
  End-to-end check of the RISC-V (RV64) assembly output: the verified
  compiler (`RiscV.Compiler`), then `Asmexpand` and `TargetPrinter`/`PrintAsm`
  (`CCLib/riscV/Driver.lean`), on the programs of `AsmTestPrograms.lean`.

  The `#guard`s below run when this file is built: every program must be
  compiled and printed, and the printed text must contain the expected
  symbols and instructions.  (No RISC-V assembler is used here; the files
  can be written with `lake exe asmgen riscv <dir>`.)
-/
import CCLib.riscV.Driver
import AsmTestPrograms

namespace RiscVAsmCheck
open CC AsmTestPrograms

/-- The assembly text of every program. -/
def asmFiles (pic : Bool := false) : List (String × Res String) :=
  clightPrograms.map (fun (n, p) => (n, RiscV.Driver.compileClightProgram p (pic := pic))) ++
  cPrograms.map (fun (n, p) => (n, RiscV.Driver.compileCProgram p (pic := pic)))

/-- The text of one program (empty on error). -/
def text (name : String) (pic : Bool := false) : String :=
  match (asmFiles pic).lookup name with
  | some (.OK s) => s
  | _ => ""

def hasLine (s line : String) : Bool := (s.splitOn "\n").contains line
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

-- every program is compiled and printed
#guard (asmFiles).all fun (_, r) => r matches .OK _
#guard (asmFiles true).all fun (_, r) => r matches .OK _
-- RV32 is rejected
#guard !(RiscV.Driver.compileClightProgram Swap.prog { model := "32" }).isOK

-- symbols and directives
#guard hasLine (text "swap") "\t.option nopic"
#guard hasLine (text "swap" true) "\t.option pic"
#guard hasLine (text "swap") "\t.globl swap"
#guard hasLine (text "swap") "swap:"
#guard hasLine (text "swap") "\t.type\tswap, @function"
#guard hasLine (text "swap") "\t.cfi_startproc"
#guard hasLine (text "swap") "\tjr\tx1"
-- `Pallocframe`/`Pfreeframe` are expanded into stack-pointer arithmetic
#guard !has (text "swap") "allocframe"
#guard hasLine (text "swap") "\tmv\tx30, x2"
#guard hasLine (text "swap") "\taddi\tx2, x2, -16"
-- the pointers stay in the argument registers (`Regalloc.regallocIRC`)
#guard hasLine (text "swap") "\tlw\tx13, 0(x10)"
-- the global variable of `demo.c` (`int g = 42;`)
#guard hasLine (text "demo") "g:"
#guard hasLine (text "demo") "\t.long\t42"
-- the switch becomes a jump table of relative offsets
#guard has (text "switch") "# jumptable"
#guard ((text "switch").splitOn "\t.long\t.L").length > 9
-- calls with stack arguments; float constants go to the literal pool
#guard hasLine (text "args") "\tcall\tf"
#guard has (text "args") ".section\t.rodata.cst8,\"aM\",@progbits,8"
#guard has (text "args") "\tfcvt.w.d\t"

end RiscVAsmCheck
