/-
  Port of `powerpc/CBuiltins.ml`: processor-dependent builtin C functions
  (their C types, for the elaborator and `C2C`), the type of `va_list`, and
  `asm_mem_argument` (used by `ExtendedAsm` and `C2C`).
-/
import CCLib.cparser.C

namespace CC
namespace PowerPC
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
  builtin_typedefs := [("__builtin_va_list", .TArray (tint .IUInt) (some 3) [])]
  builtin_functions := [
    ("__builtin_mulhw", (tint .IInt, [tint .IInt, tint .IInt], false)),
    ("__builtin_mulhwu", (tint .IUInt, [tint .IUInt, tint .IUInt], false)),
    ("__builtin_cmpb", (tint .IUInt, [tint .IUInt, tint .IUInt], false)),
    ("__builtin_mulhd", (tint .ILongLong, [tint .ILongLong, tint .ILongLong], false)),
    ("__builtin_mulhdu", (tint .IULongLong, [tint .IULongLong, tint .IULongLong], false)),
    ("__builtin_fmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmadd", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fnmsub", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_frsqrte", (dbl, [dbl], false)),
    ("__builtin_fres", (flt, [flt], false)),
    ("__builtin_fsel", (dbl, [dbl, dbl, dbl], false)),
    ("__builtin_fcti", (tint .IInt, [dbl], false)),
    ("__builtin_read16_reversed", (tint .IUShort, [cptr .IUShort], false)),
    ("__builtin_read32_reversed", (tint .IUInt, [cptr .IUInt], false)),
    ("__builtin_write16_reversed", (void, [ptr (tint .IUShort), tint .IUShort], false)),
    ("__builtin_write32_reversed", (void, [ptr (tint .IUInt), tint .IUInt], false)),
    ("__builtin_read64_reversed", (tint .IULongLong, [cptr .IULongLong], false)),
    ("__builtin_write64_reversed", (void, [ptr (tint .IULongLong), tint .IULongLong], false)),
    ("__builtin_eieio", (void, [], false)),
    ("__builtin_sync", (void, [], false)),
    ("__builtin_isync", (void, [], false)),
    ("__builtin_lwsync", (void, [], false)),
    ("__builtin_mbar", (void, [tint .IInt], false)),
    ("__builtin_trap", (void, [], false)),
    ("__builtin_dcbf", (void, [voidp], false)),
    ("__builtin_dcbi", (void, [voidp], false)),
    ("__builtin_icbi", (void, [voidp], false)),
    ("__builtin_prefetch", (void, [voidp, tint .IInt, tint .IInt], false)),
    ("__builtin_dcbtls", (void, [voidp, tint .IInt], false)),
    ("__builtin_icbtls", (void, [voidp, tint .IInt], false)),
    ("__builtin_dcbz", (void, [voidp], false)),
    ("__builtin_get_spr", (tint .IUInt, [tint .IInt], false)),
    ("__builtin_set_spr", (void, [tint .IInt, tint .IUInt], false)),
    ("__builtin_get_spr64", (tint .IULongLong, [tint .IInt], false)),
    ("__builtin_set_spr64", (void, [tint .IInt, tint .IULongLong], false)),
    ("__builtin_mr", (void, [tint .IInt, tint .IInt], false)),
    ("__builtin_call_frame", (voidp, [], false)),
    ("__builtin_return_address", (voidp, [], false)),
    ("__builtin_isel", (tint .IInt, [tint .IBool, tint .IInt, tint .IInt], false)),
    ("__builtin_uisel", (tint .IUInt, [tint .IBool, tint .IUInt, tint .IUInt], false)),
    ("__builtin_isel64", (tint .ILongLong, [tint .IBool, tint .ILongLong, tint .ILongLong], false)),
    ("__builtin_uisel64", (tint .IULongLong, [tint .IBool, tint .IULongLong, tint .IULongLong], false)),
    ("__builtin_bsel", (tint .IBool, [tint .IBool, tint .IBool, tint .IBool], false)),
    ("__builtin_nop", (void, [], false)),
    ("__builtin_atomic_exchange", (void, [ptr (tint .IInt), ptr (tint .IInt), ptr (tint .IInt)], false)),
    ("__builtin_atomic_load", (void, [ptr (tint .IInt), ptr (tint .IInt)], false)),
    ("__builtin_atomic_compare_exchange", (tint .IBool, [ptr (tint .IInt), ptr (tint .IInt), ptr (tint .IInt)], false)),
    ("__builtin_sync_fetch_and_add", (tint .IInt, [ptr (tint .IInt), tint .IInt], false)) ]

def size_va_list : Int := 12
def va_list_scalar : Bool := false

/-- Expand memory references inside extended asm statements. -/
def asm_mem_argument (arg : String) : String := s!"0({arg})"

end CBuiltins
end PowerPC
end CC
