/-
  Output of the `Asm` program in JSON format — port of `x86/AsmToJSON.ml`.

  For this target CompCert does not implement the JSON output (option
  `-sdump`): `print_if` and `pp_mnemonics` do nothing.  They are ported as
  such, so that a driver can call them for every target.
-/
import CCLib.x86.Asm

namespace CC
namespace X86
namespace AsmToJSON

/-- `AsmToJSON.print_if`: does nothing on this target. -/
def printIf {P : Type} (_destination : Option String) (_prog : P) (_sourcename : String) :
    IO Unit := pure ()

/-- `AsmToJSON.pp_mnemonics`: no mnemonics on this target. -/
def ppMnemonics : String := ""

end AsmToJSON
end X86
end CC
