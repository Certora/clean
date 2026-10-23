/-
  Port of `riscV/CBuiltins.ml`: processor-dependent builtin C functions
  (their C types, for the elaborator and `C2C`), the type of `va_list`, and
  `asm_mem_argument` (used by `ExtendedAsm` and `C2C`).

  `Archi.ptr64` is an explicit argument of `size_va_list`.
-/
import CCLib.cparser.C

namespace CC
namespace RiscV
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
    ("__builtin_fence", (void, [], false)),
    ("__builtin_fmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fmax", (dbl, [dbl, dbl], false)),
    ("__builtin_fmin", (dbl, [dbl, dbl], false)) ]

def va_list_type : Typ := voidp
def size_va_list (ptr64 : Bool) : Int := if ptr64 then 8 else 4
def va_list_scalar : Bool := true

/-- Expand memory references inside extended asm statements. -/
def asm_mem_argument (arg : String) : String := s!"0({arg})"

end CBuiltins
end RiscV
end CC
