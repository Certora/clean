/-
  Port of `x86/CBuiltins.ml`: processor-dependent builtin C functions
  (their C types, for the elaborator and `C2C`), the type of `va_list`, and
  `asm_mem_argument` (used by `ExtendedAsm` and `C2C`).

  `Archi.ptr64` and `Archi.win64` are explicit arguments.
-/
import CCLib.cparser.C

namespace CC
namespace X86
namespace CBuiltins

open CC.CParser.C

private def dbl : Typ := .TFloat .FDouble []
private def flt : Typ := .TFloat .FFloat []
private def tint (ik : IKind) : Typ := .TInt ik []
private def void : Typ := .TVoid []
private def voidp : Typ := .TPtr (.TVoid []) []
private def ptr (t : Typ) : Typ := .TPtr t []
private def cptr (ik : IKind) : Typ := .TPtr (.TInt ik [.AConst]) []

/-- `(va_list_type, va_list_scalar, size_va_list)` -/
def va_list_info (ptr64 win64 : Bool) : Typ × Bool × Int :=
  if ptr64 then
    if win64 then (voidp, true, 8)
    else (.TArray (tint .IULong) (some 3) [], false, 3 * 8)
  else (voidp, true, 4)

def va_list_type (ptr64 win64 : Bool) : Typ := (va_list_info ptr64 win64).1
def va_list_scalar (ptr64 win64 : Bool) : Bool := (va_list_info ptr64 win64).2.1
def size_va_list (ptr64 win64 : Bool) : Int := (va_list_info ptr64 win64).2.2

def builtins (ptr64 win64 : Bool) : Builtins where
  builtin_typedefs := [("__builtin_va_list", va_list_type ptr64 win64)]
  builtin_functions := [
    ("__builtin_fmax", (dbl, [dbl, dbl], false)),
    ("__builtin_fmin", (dbl, [dbl, dbl], false)),
    ("__builtin_fmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_read16_reversed", (tint .IUShort, [cptr .IUShort], false)),
    ("__builtin_read32_reversed", (tint .IUInt, [cptr .IUInt], false)),
    ("__builtin_write16_reversed", (void, [ptr (tint .IUShort), tint .IUShort], false)),
    ("__builtin_write32_reversed", (void, [ptr (tint .IUInt), tint .IUInt], false)) ]

/-- Expand memory references inside extended asm statements. -/
def asm_mem_argument (arg : String) : String := s!"0({arg})"

end CBuiltins
end X86
end CC
