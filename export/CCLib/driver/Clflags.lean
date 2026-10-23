/-
  Port of `driver/Clflags.ml`: the command-line flags of the compiler.

  OCaml keeps every flag in a global reference (`let option_x = ref …`).
  Here the flags are the fields of one value `Clflags.Flags`, which the
  driver threads explicitly (see `CCLib.driver.Driver`, `Frontend`, and the
  `flags` field of `C2C.Target`).  The field names are the OCaml names.

  The defaults are the OCaml initial values.  Five of them depend on the
  configuration (`Configuration.pic_supported`, `model`, `system`, `arch`,
  `abi`, `stdlib_path`, `has_standard_headers`); here the defaults are those
  of a Linux configuration (PIC supported, not `armv7m`, not `diab`, not
  PowerPC EABI), and `Driver.initialFlags` recomputes them from the actual
  configuration.
-/

namespace CC
namespace Clflags

/-- The flags of `driver/Clflags.ml`. -/
structure Flags where
  prepro_options : List String := []
  linker_options : List String := []
  assembler_options : List String := []
  option_flongdouble : Bool := false
  option_fstruct_passing : Bool := false
  option_fvararg_calls : Bool := true
  option_funprototyped : Bool := true
  option_fpacked_structs : Bool := false
  option_funstructured_switch : Bool := false
  option_ffpu : Bool := true
  option_fpic : Bool := false
  /-- OCaml: `Configuration.pic_supported` -/
  option_fpie : Bool := true
  option_ffloatconstprop : Nat := 2
  option_ftailcalls : Bool := true
  option_fconstprop : Bool := true
  option_fcse : Bool := true
  option_fredundancy : Bool := true
  option_fifconversion : Bool := true
  option_Obranchless : Bool := false
  option_falignfunctions : Option Nat := none
  option_falignbranchtargets : Nat := 0
  option_faligncondbranchs : Nat := 0
  option_finline_asm : Bool := false
  option_fcommon : Bool := true
  /-- OCaml: `Configuration.model = "armv7m"` -/
  option_mthumb : Bool := false
  option_Osize : Bool := false
  option_finline : Bool := true
  option_finline_functions_called_once : Bool := true
  option_dprepro : Bool := false
  option_dparse : Bool := false
  option_dcmedium : Bool := false
  option_dclight : Bool := false
  option_dcminor : Bool := false
  option_drtl : Bool := false
  option_dltl : Bool := false
  option_dalloctrace : Bool := false
  option_dmach : Bool := false
  option_dasm : Bool := false
  option_sdump : Bool := false
  option_g : Bool := false
  /-- OCaml: `if Configuration.system = "diab" then 2 else 3` -/
  option_gdwarf : Nat := 3
  option_gdepth : Nat := 3
  option_o : Option String := none
  option_E : Bool := false
  option_S : Bool := false
  option_c : Bool := false
  option_v : Bool := false
  option_interp : Bool := false
  /-- OCaml: `8` for PowerPC EABI under Diab, `0` otherwise -/
  option_small_data : Int := 0
  /-- OCaml: the initial value of `option_small_data` -/
  option_small_const : Int := 0
  option_timings : Bool := false
  option_std : String := "c99"
  /-- OCaml: `Configuration.stdlib_path` -/
  stdlib_path : String := ""
  /-- OCaml: `Configuration.has_standard_headers` -/
  use_standard_headers : Bool := true
  main_function_name : String := "main"
  deriving Inhabited, Repr

end Clflags
end CC
