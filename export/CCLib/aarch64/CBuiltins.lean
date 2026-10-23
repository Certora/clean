/-
  Port of `aarch64/CBuiltins.ml`: processor-dependent builtin C functions
  (their C types, for the elaborator and `C2C`), the type of `va_list`, and
  `asm_mem_argument` (used by `ExtendedAsm` and `C2C`).

  `Archi.abi` is the explicit argument `apple` (`true` for `Archi.Apple`,
  `false` for `Archi.AAPCS64`) and `Configuration.system = "macos"` the
  argument `macos`.
-/
import CCLib.cparser.C

namespace CC
namespace AArch64
namespace CBuiltins

open CC.CParser.C

private def dbl : Typ := .TFloat .FDouble []
private def flt : Typ := .TFloat .FFloat []
private def tint (ik : IKind) : Typ := .TInt ik []
private def void : Typ := .TVoid []
private def voidp : Typ := .TPtr (.TVoid []) []
private def ptr (t : Typ) : Typ := .TPtr t []
private def cptr (ik : IKind) : Typ := .TPtr (.TInt ik [.AConst]) []

/-- `(va_list_type, size_va_list, va_list_scalar)`: AAPCS64: `va_list` is a
    struct of size 32 and alignment 8, passed by reference; Apple: a pointer. -/
def va_list_info (apple : Bool) : Typ × Int × Bool :=
  if apple then (voidp, 8, true)
  else (.TArray (tint .IULong) (some 4) [], 32, false)

def va_list_type (apple : Bool) : Typ := (va_list_info apple).1
def size_va_list (apple : Bool) : Int := (va_list_info apple).2.1
def va_list_scalar (apple : Bool) : Bool := (va_list_info apple).2.2

/-- Dummy definition of the GCC types `__int128_t`, `__uint128_t`. -/
def int128_type : Typ := .TArray (tint .IULong) (some 2) []

def builtins (apple macos : Bool) : Builtins where
  builtin_typedefs :=
    [("__builtin_va_list", va_list_type apple)] ++
    (if macos then [("__int128_t", int128_type), ("__uint128_t", int128_type)] else [])
  builtin_functions := [
    ("__builtin_cls", (tint .IInt, [tint .IInt], false)),
    ("__builtin_clsl", (tint .IInt, [tint .ILong], false)),
    ("__builtin_clsll", (tint .IInt, [tint .ILongLong], false)),
    ("__builtin_fmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fmax", (dbl, [dbl, dbl], false)),
    ("__builtin_fmin", (dbl, [dbl, dbl], false)) ]

/-- Expand memory references inside extended asm statements. -/
def asm_mem_argument (arg : String) : String := s!"[{arg}]"

end CBuiltins
end AArch64
end CC
