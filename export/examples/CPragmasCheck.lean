/-
  Checks of `lib/Tokenize.lean`, `cfrontend/CPragmas.lean` and the section
  table of `common/Sections.lean`: `#guard`s written from reading the OCaml
  code.
-/
import CCLib.cfrontend.CPragmas

namespace CPragmasCheck

open CC CParser

def run {α} (cfg : Machine.T) (x : M α) : Option α × Array String :=
  match x.run { config := cfg } with
  | .ok a s => (some a, s.messages)
  | .error _ s => (none, s.messages)

def loc : C.Location := ("t.c", 1)

/-! ### `Tokenize` and `#pragma` handling (`CPragmas`, `Sections`) -/

#guard Tokenize.string "section  SEC \".a\\tb\" 'x y' far-data RW" ==
  ["section", "SEC", ".a\tb", "x y", "far-data", "RW"]
#guard Tokenize.string "use_section CODE f, g;" == ["use_section", "CODE", "f", ",", "g", ";"]

/-- A toy target: registers are names, only `RBX` is callee-save, and
    identifier `n` is the atom of a name of length `n`. -/
def toyTarget : CPragmas.Target String :=
  { register_by_name := fun s => if s == "RBX" || s == "RAX" then some s else none,
    is_callee_save := fun r => r == "RBX",
    intern_string := fun s => Positive.ofNat s.length }

def pragmas (ps : List String) : Option (List Bool × CPragmas.PState String) × Array String :=
  run Machine.x86_64 ((ps.mapM (CPragmas.process_pragma toyTarget loc)).run {})

/- `#pragma section` defines a user section; `use_section` binds `foo` (atom 3)
   to it; the section is then used for `foo` by `Sections.for_function`. -/
#guard (run Machine.x86_64 do
  let (_, st) ← ((["section MYCODE \".mytext\" \".mybss\" RX", "use_section MYCODE foo"].mapM
      (CPragmas.process_pragma toyTarget loc)).run {})
  Sections.for_function st.sections loc (Positive.ofNat 3) []).1 ==
  some [.Section_user ".mytext" false true, .Section_literal 0, .Section_jumptable]
#guard (pragmas ["reserve_register rbx", "reserve_register rax", "reserve_register r99",
                 "use_section NOPE f", "use_section DATA 1x", "section", "frobnicate"]).2 ==
  #["t.c:1: error: cannot reserve this register (not a callee-save)",
    "t.c:1: error: unknown register in `reserve_register' pragma",
    "t.c:1: error: unknown section name `NOPE'",
    "t.c:1: error: bad identifier `1x' in #pragma use_section",
    "t.c:1: error: ill-formed `section' pragma"]
#guard ((pragmas ["reserve_register rbx", "frobnicate"]).1.map
  fun (bs, st) => (bs, st.reserved_registers)) == some ([true, false], ["RBX"])

end CPragmasCheck
