/-
  Auxiliary functions on machine registers — port of `x86/Machregsaux.ml`,
  together with the module `Machregsnames` that CompCert's build generates
  from `Machregs.register_names` (used by the printers `PrintLTL`,
  `PrintMach`, … and by the register allocator).
-/
import CCLib.x86.Machregs
import CCLib.backend.Machregsnames

namespace CC
namespace X86
namespace Machregsaux

/-- `Machregsnames.name_of_register`: the last name of `r` in
    `Machregs.register_names` (see `backend/Machregsnames.lean`). -/
def nameOfRegister (r : Mreg) : Option String :=
  Machregsnames.nameOfRegister Mreg.registerNames r

/-- `Machregsnames.register_by_name` (case-insensitive, as in OCaml) -/
def registerByName (s : String) : Option Mreg := Mreg.registerByName s.toUpper

/-- `Machregsaux.is_scratch_register` -/
def isScratchRegister (_s : String) : Bool := false

end Machregsaux
end X86
end CC
