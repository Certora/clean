/-
  Auxiliary functions on machine registers — port of `aarch64/Machregsaux.ml`,
  together with the module `Machregsnames` that CompCert's build generates
  from `Machregs.register_names` (used by the printers `PrintLTL`,
  `PrintMach`, … and by the register allocator).
-/
import CCLib.aarch64.Machregs
import CCLib.backend.Machregsnames

namespace CC
namespace Machregsaux

/-- `Machregsnames.name_of_register`: the last name of `r` in
    `Machregs.register_names` (see `backend/Machregsnames.lean`). -/
def nameOfRegister (r : Mreg) : Option String :=
  Machregsnames.nameOfRegister Mreg.registerNames r

/-- `Machregsnames.register_by_name` (case-insensitive, as in OCaml) -/
def registerByName (s : String) : Option Mreg := Mreg.registerByName s.toUpper

/-- `Machregsaux.is_scratch_register` -/
def isScratchRegister (s : String) : Bool :=
  s == "X16" || s == "x16" || s == "W16" || s == "w16" ||
  s == "X30" || s == "x30" || s == "W30" || s == "w30"

end Machregsaux
end CC
