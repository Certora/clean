/-
  Port of `cfrontend/CPragmas.ml`: handling of the pragmas
  `#pragma section`, `#pragma use_section` and `#pragma reserve_register`.

  Differences from the OCaml code:
  * The global state (the section tables of `Sections` and the list
    `reserved_registers`) is the explicit value `PState`, threaded by the
    state monad `PM` on top of the diagnostics monad of `cparser/`.
  * `C2C.error` / `C2C.warning` report at `C2C.currentLocation`; here the
    location is an argument `loc` (C2C is not ported).
  * The target-dependent functions (`Machregsnames.register_by_name`,
    `Conventions1.is_callee_save`) and the atom table (`intern_string`) are
    fields of the argument `Target`.  As in `Machregsnames`, the register
    name is upper-cased before the lookup.
  * `initialize` (which installs `process_pragma` as `C2C`'s hook) has no
    counterpart: callers call `process_pragma` directly.
-/
import CCLib.common.Sections
import CCLib.lib.Tokenize

namespace CC
namespace CPragmas

open CParser

/-- Target-dependent functions used by the pragmas. -/
structure Target (Mreg : Type) where
  /-- `Machregsnames.register_by_name` (on an upper-cased name) -/
  register_by_name : String → Option Mreg
  /-- `Conventions1.is_callee_save` -/
  is_callee_save : Mreg → Bool
  /-- `Camlcoq.intern_string` -/
  intern_string : String → Ident

/-- The global state of `CPragmas` and `Sections`. -/
structure PState (Mreg : Type) where
  sections : Sections.Table := Sections.«initialize»
  /-- `CPragmas.reserved_registers` -/
  reserved_registers : List Mreg := []

/-- The pragma-processing monad. -/
abbrev PM (Mreg : Type) := StateT (PState Mreg) M

variable {Mreg : Type}

/-- `#pragma section` -/
def process_section_pragma (classname istring ustring addrmode accmode : String) :
    PM Mreg Unit := do
  let access : Option Sections.AccessMode :=
    match addrmode with
    | "" => none
    | "near-data" => some .Access_near
    | "far-data" => some .Access_far
    | _ => some .Access_default
  let iname := if istring == "" then none else some istring
  let uname := if ustring == "" then none else some ustring
  let writable := if accmode == "" then none else some (accmode.contains 'W')
  let executable := if accmode == "" then none else some (accmode.contains 'X')
  let st ← get
  let t := Sections.define_section st.sections classname iname uname writable executable access
  set { st with sections := t }

/-- `Str.string_match "[A-Za-z_][A-Za-z_0-9]*$" id 0` -/
def is_c_ident (id : String) : Bool :=
  match id.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')

/-- `#pragma use_section` -/
def process_use_section_pragma (tgt : Target Mreg) (loc : C.Location)
    (classname id : String) : PM Mreg Unit := do
  if id == "," || id == ";" then return
  if !is_c_ident id then
    liftM (m := M) (Diagnostics.error loc s!"bad identifier `{id}' in #pragma use_section")
  let st ← get
  match Sections.use_section_for st.sections (tgt.intern_string id) classname with
  | some t => set { st with sections := t }
  | none => liftM (m := M) (Diagnostics.error loc s!"unknown section name `{classname}'")

/-- `#pragma reserve_register` -/
def process_reserve_register_pragma (tgt : Target Mreg) (loc : C.Location)
    (name : String) : PM Mreg Unit := do
  match tgt.register_by_name name.toUpper with
  | none => liftM (m := M) (Diagnostics.error loc "unknown register in `reserve_register' pragma")
  | some r =>
    if tgt.is_callee_save r then
      modify fun st => { st with reserved_registers := r :: st.reserved_registers }
    else
      liftM (m := M) (Diagnostics.error loc "cannot reserve this register (not a callee-save)")

/-- `CPragmas.process_pragma`: parsing of pragmas.  Returns `true` if the
    pragma was recognized. -/
def process_pragma (tgt : Target Mreg) (loc : C.Location) (name : String) :
    PM Mreg Bool := do
  let err (msg : String) : PM Mreg Bool := do
    liftM (m := M) (Diagnostics.error loc msg); return true
  match Tokenize.string name with
  | ["section", classname, istring, ustring, addrmode, accmode] =>
      process_section_pragma classname istring ustring addrmode accmode
      return true
  | ["section", classname, istring, ustring, accmode] =>
      process_section_pragma classname istring ustring "" accmode
      return true
  | "section" :: _ => err "ill-formed `section' pragma"
  | "use_section" :: classname :: identlist =>
      if identlist.isEmpty then
        liftM (m := M) (Diagnostics.warning loc .Unnamed "empty `use_section' pragma")
      for id in identlist do
        process_use_section_pragma tgt loc classname id
      return true
  | "use_section" :: _ => err "ill-formed `use_section' pragma"
  | ["reserve_register", reg] =>
      process_reserve_register_pragma tgt loc reg
      return true
  | "reserve_register" :: _ => err "ill-formed `reserve_register' pragma"
  | _ => return false

/-- `CPragmas.reset` -/
def reset : PM Mreg Unit :=
  modify fun st => { st with reserved_registers := [] }

end CPragmas
end CC
