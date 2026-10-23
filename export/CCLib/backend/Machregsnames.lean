/-
  Names of machine registers — port of `backend/Machregsnames.ml`.

  The OCaml module fills a hash table from `Machregs.register_names` with
  `Hashtbl.add`, which hides (rather than replaces) earlier bindings: when a
  register has several names (`RAX` and `EAX` for `AX` on x86, `X0` and
  `W0` for `R0` on AArch64, …), `name_of_register` returns the *last* one
  of the list.  The module is shared by all targets; here it is generic in
  the type of machine registers and takes `Machregs.register_names` and
  `Machregs.register_by_name` as arguments.  Each target's
  `Machregsaux.lean` instantiates it.
-/

namespace CC
namespace Machregsnames

variable {Mreg : Type} [BEq Mreg]

/-- `Machregsnames.name_of_register`: the last name of `r` in
    `registerNames` (the binding visible in OCaml's hash table). -/
def nameOfRegister (registerNames : List (String × Mreg)) (r : Mreg) : Option String :=
  (registerNames.reverse.find? (·.2 == r)).map (·.1)

/-- `Machregsnames.register_by_name`: `Machregs.register_by_name` of the
    upper-case name. -/
def registerByName (registerByName : String → Option Mreg) (s : String) : Option Mreg :=
  registerByName s.toUpper

#guard nameOfRegister [("RAX", 0), ("RBX", 1), ("EAX", 0)] 0 = some "EAX"
#guard nameOfRegister [("RAX", 0), ("RBX", 1), ("EAX", 0)] 1 = some "RBX"

end Machregsnames
end CC
