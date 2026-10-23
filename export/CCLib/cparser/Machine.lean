/-
  Port of `cparser/Machine.ml`: machine-dependent aspects of the C front end
  (sizes and alignments of the C types, endianness, struct passing).

  OCaml keeps the current configuration in the global reference
  `Machine.config`; here it is the field `config` of the front-end state
  (`Diagnostics.State`), read by `Cutil` through the monad `CParser.M`.
-/
import CCLib.cparser.C

namespace CC
namespace CParser
namespace Machine

open C

inductive StructPassingStyle where
  /-- by reference, callee takes copy -/
  | SP_ref_callee
  /-- by reference, caller takes copy -/
  | SP_ref_caller
  /-- by value, as a sequence of ints -/
  | SP_split_args
  deriving BEq, DecidableEq, Inhabited, Repr

inductive StructReturnStyle where
  /-- return by content if size is 1, 2, 4 or 8 bytes -/
  | SR_int1248
  /-- return by content if size is <= 4 -/
  | SR_int1to4
  /-- return by content if size is <= 8 -/
  | SR_int1to8
  /-- always return by assignment to a reference given as extra argument -/
  | SR_ref
  deriving BEq, DecidableEq, Inhabited, Repr

/-- `Machine.t` -/
structure T where
  name : String
  char_signed : Bool
  sizeof_ptr : Int
  sizeof_short : Int
  sizeof_int : Int
  sizeof_long : Int
  sizeof_longlong : Int
  sizeof_float : Int
  sizeof_double : Int
  sizeof_longdouble : Int
  sizeof_void : Option Int
  sizeof_fun : Option Int
  wchar_ikind : IKind
  sizeof_size_t : Int
  sizeof_ptrdiff_t : Int
  sizeof_intreg : Int
  alignof_ptr : Int
  alignof_short : Int
  alignof_int : Int
  alignof_long : Int
  alignof_longlong : Int
  alignof_float : Int
  alignof_double : Int
  alignof_longdouble : Int
  alignof_void : Option Int
  alignof_fun : Option Int
  bigendian : Bool
  bitfields_msb_first : Bool
  supports_unaligned_accesses : Bool
  struct_passing_style : StructPassingStyle
  struct_return_style : StructReturnStyle
  deriving BEq, Inhabited, Repr

def ilp32ll64 : T where
  name := "ilp32ll64"
  char_signed := false
  sizeof_ptr := 4
  sizeof_short := 2
  sizeof_int := 4
  sizeof_long := 4
  sizeof_longlong := 8
  sizeof_float := 4
  sizeof_double := 8
  sizeof_longdouble := 8
  sizeof_void := none
  sizeof_fun := none
  wchar_ikind := .IInt
  sizeof_size_t := 4
  sizeof_ptrdiff_t := 4
  sizeof_intreg := 4
  alignof_ptr := 4
  alignof_short := 2
  alignof_int := 4
  alignof_long := 4
  alignof_longlong := 8
  alignof_float := 4
  alignof_double := 8
  alignof_longdouble := 8
  alignof_void := none
  alignof_fun := none
  bigendian := false
  bitfields_msb_first := false
  supports_unaligned_accesses := false
  struct_passing_style := .SP_ref_callee
  struct_return_style := .SR_ref

def i32lpll64 : T :=
  { ilp32ll64 with
    name := "i32lpll64"
    sizeof_ptr := 8
    sizeof_long := 8
    sizeof_size_t := 8
    sizeof_ptrdiff_t := 8
    sizeof_intreg := 8
    alignof_ptr := 8
    alignof_long := 8 }

def il32pll64 : T :=
  { ilp32ll64 with
    name := "il32pll64"
    sizeof_ptr := 8
    sizeof_size_t := 8
    sizeof_ptrdiff_t := 8
    sizeof_intreg := 8
    alignof_ptr := 8 }

/-! Canned configurations for some ABIs -/

def x86_32 : T :=
  { ilp32ll64 with
    name := "x86_32"
    char_signed := true
    alignof_longlong := 4, alignof_double := 4, alignof_longdouble := 4
    supports_unaligned_accesses := true
    struct_passing_style := .SP_split_args
    struct_return_style := .SR_ref }

def x86_32_macos : T :=
  { x86_32 with struct_passing_style := .SP_split_args,
                struct_return_style := .SR_int1248 }

def x86_32_bsd : T := x86_32_macos

def x86_64 : T :=
  { i32lpll64 with name := "x86_64", char_signed := true,
                   struct_passing_style := .SP_ref_callee,
                   struct_return_style := .SR_ref }

def win32 : T :=
  { ilp32ll64 with name := "win32", char_signed := true,
                   wchar_ikind := .IUShort,
                   struct_passing_style := .SP_split_args,
                   struct_return_style := .SR_ref }

def win64 : T :=
  { il32pll64 with name := "win64", char_signed := true, wchar_ikind := .IUShort }

def ppc_32_bigendian : T :=
  { ilp32ll64 with name := "powerpc",
                   bigendian := true,
                   wchar_ikind := .ILong,
                   bitfields_msb_first := true,
                   supports_unaligned_accesses := true,
                   struct_passing_style := .SP_ref_caller,
                   struct_return_style := .SR_int1to8 }

def ppc_32_r64_bigendian : T := { ppc_32_bigendian with sizeof_intreg := 8 }

def ppc_32_diab_bigendian : T := { ppc_32_bigendian with wchar_ikind := .IUShort }

def ppc_32_r64_diab_bigendian : T := { ppc_32_diab_bigendian with sizeof_intreg := 8 }

def ppc_32_linux_bigendian : T := { ppc_32_bigendian with struct_return_style := .SR_ref }

def ppc_32_r64_linux_bigendian : T := { ppc_32_linux_bigendian with sizeof_intreg := 8 }

def arm_littleendian : T :=
  { ilp32ll64 with name := "arm",
                   wchar_ikind := .IUInt,
                   struct_passing_style := .SP_split_args,
                   struct_return_style := .SR_int1to4 }

def arm_bigendian : T :=
  { arm_littleendian with bigendian := true, bitfields_msb_first := true }

def rv32 : T :=
  { ilp32ll64 with name := "rv32",
                   struct_passing_style := .SP_ref_callee,
                   struct_return_style := .SR_ref }

def rv64 : T :=
  { i32lpll64 with name := "rv64",
                   struct_passing_style := .SP_ref_callee,
                   struct_return_style := .SR_ref }

def aarch64 : T :=
  { i32lpll64 with name := "aarch64",
                   wchar_ikind := .IUInt,
                   struct_passing_style := .SP_ref_callee,
                   struct_return_style := .SR_ref }

def aarch64_apple : T :=
  { aarch64 with char_signed := true, wchar_ikind := .IInt }

/-- Add GCC extensions re: sizeof and alignof -/
def gcc_extensions (c : T) : T :=
  { c with sizeof_void := some 1, sizeof_fun := some 1,
           alignof_void := some 1, alignof_fun := some 1 }

/-- Normalize configuration for use with the CompCert reference interpreter -/
def compcert_interpreter (c : T) : T :=
  { c with supports_unaligned_accesses := false }

/-- Undefined configuration -/
def undef : T :=
  { ilp32ll64 with
    name := "UNDEFINED"
    sizeof_ptr := 0, sizeof_short := 0, sizeof_int := 0, sizeof_long := 0
    sizeof_longlong := 0, sizeof_float := 0, sizeof_double := 0
    sizeof_longdouble := 0
    sizeof_size_t := 0, sizeof_ptrdiff_t := 0, sizeof_intreg := 0
    alignof_ptr := 0, alignof_short := 0, alignof_int := 0, alignof_long := 0
    alignof_longlong := 0, alignof_float := 0, alignof_double := 0
    alignof_longdouble := 0 }

end Machine
end CParser
end CC
