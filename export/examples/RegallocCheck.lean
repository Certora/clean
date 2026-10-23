/-
  Check of the register allocator ported from `backend/Regalloc.ml`
  (`Regalloc.regallocIRC`, with `XTL`, `IRC` and `Splitting`), for the
  AArch64, x86-64 (System V and Win64) and RV64 back ends: the whole
  compiler is run on the programs of `AsmTestPrograms.lean` with the
  coloring allocator *without* its spill-everything fallback, so every
  allocation must be accepted by the validator `Allocation.check_function`.
-/
import CCLib.driver.Driver
import CCLib.x86.Driver
import CCLib.riscV.Driver
import AsmTestPrograms

namespace RegallocCheck
open CC AsmTestPrograms

def aarch64Cfg : Compiler.Config :=
  { Extraction.defaultConfig with
    regalloc := Regalloc.regallocIRC (ExtractionMachdep.abi ({} : ExtractionMachdep.Target).abi) }

def x86Cfg (system : String) : X86.Compiler.Config :=
  { X86.ExtractionMachdep.configFor { system } with
    regalloc := X86.Regalloc.regallocIRC (X86.ExtractionMachdep.win64 system) }

def riscVCfg : RiscV.Compiler.Config :=
  { RiscV.ExtractionMachdep.defaultConfig with regalloc := RiscV.Regalloc.regallocIRC }

-- AArch64
#guard clightPrograms.all fun (_, p) => (Compiler.transfClightProgram aarch64Cfg p).isOK
#guard cPrograms.all fun (_, p) => (Compiler.transfCProgram aarch64Cfg p).isOK
-- x86-64, System V and Win64
#guard clightPrograms.all fun (_, p) => (X86.Compiler.transfClightProgram (x86Cfg "linux") p).isOK
#guard cPrograms.all fun (_, p) => (X86.Compiler.transfCProgram (x86Cfg "linux") p).isOK
#guard clightPrograms.all fun (_, p) => (X86.Compiler.transfClightProgram (x86Cfg "cygwin") p).isOK
#guard cPrograms.all fun (_, p) => (X86.Compiler.transfCProgram (x86Cfg "cygwin") p).isOK
-- RV64
#guard clightPrograms.all fun (_, p) => (RiscV.Compiler.transfClightProgram riscVCfg p).isOK
#guard cPrograms.all fun (_, p) => (RiscV.Compiler.transfCProgram riscVCfg p).isOK

/-- The AArch64 assembly of `swap`: with register allocation, the four
    memory accesses use registers only (no stack slots). -/
def swapText : String :=
  match clightPrograms.lookup "swap" with
  | some p => match Driver.compileClightProgram p "linux" with
    | .OK s => s
    | .Error _ => ""
  | none => ""

#guard (swapText.splitOn "\n").contains "\tldr\tw3, [x0, #0]"
#guard (swapText.splitOn "\n").contains "\tstr\tw3, [x1, #0]"

end RegallocCheck
