/-
  Port of `arm/CBuiltins.ml`: processor-dependent builtin C functions
  (their C types, for the elaborator and `C2C`), the type of `va_list`, and
  `asm_mem_argument` (used by `ExtendedAsm` and `C2C`).
-/
import CCLib.cparser.C

namespace CC
namespace Arm
namespace CBuiltins

open CC.CParser.C

private def dbl : Typ := .TFloat .FDouble []
private def flt : Typ := .TFloat .FFloat []
private def tint (ik : IKind) : Typ := .TInt ik []
private def void : Typ := .TVoid []
private def voidp : Typ := .TPtr (.TVoid []) []
private def ptr (t : Typ) : Typ := .TPtr t []
private def cptr (ik : IKind) : Typ := .TPtr (.TInt ik [.AConst]) []

def builtins : Builtins where
  builtin_typedefs := [("__builtin_va_list", voidp)]
  builtin_functions := [
    ("__builtin_read16_reversed", (tint .IUShort, [cptr .IUShort], false)),
    ("__builtin_read32_reversed", (tint .IUInt, [cptr .IUInt], false)),
    ("__builtin_write16_reversed", (void, [ptr (tint .IUShort), tint .IUShort], false)),
    ("__builtin_write32_reversed", (void, [ptr (tint .IUInt), tint .IUInt], false)),
    ("__builtin_dmb", (void, [], false)),
    ("__builtin_dsb", (void, [], false)),
    ("__builtin_isb", (void, [], false)) ]

def size_va_list : Int := 4
def va_list_scalar : Bool := true

/-- Expand memory references inside extended asm statements. -/
def asm_mem_argument (arg : String) : String := s!"[{arg}, #0]"

end CBuiltins
end Arm
end CC
