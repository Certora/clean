/-
  Linker sections — port of the part of `common/Sections.ml` that the
  assembly printers use.

  Ported: `initialized`, `section_name`, `with_size`, `access_mode`, and
  (at the end of the file) the table of sections defined by `#pragma section`
  (`section_info`, `builtin_sections`, `define_section`, `use_section_for`,
  `gcc_section`, `get_attr_section`, `for_variable`, `for_function`,
  `for_stringlit`).

  The OCaml hash tables `current_section_table` and `use_section_table` are
  the explicit value `Table`; the functions that update them return the new
  table.  `Clflags.option_small_const` / `option_small_data` are explicit
  arguments of `for_variable`.

  `Sections.forVariable` / `forFunction` are the default rules that apply
  when no pragma or attribute is present (used by the assembly printers,
  which do not see the C environment): read-only variables go to the
  constant section, the others to the data section, classified by their
  initializer.
-/
import CCLib.common.ASTTheory
import CCLib.cparser.Cutil

namespace CC
namespace Sections

/-- `Sections.initialized` -/
inductive Initialized where
  /-- uninitialized data area -/
  | Uninit
  /-- initialized with fixed, non-relocatable data -/
  | Init
  /-- initialized with relocatable data (symbol addresses) -/
  | Init_reloc
  deriving DecidableEq, Repr

/-- `Sections.section_name` -/
inductive SectionName where
  | Section_text
  | Section_data (i : Initialized)
  | Section_small_data (i : Initialized)
  | Section_const (i : Initialized)
  | Section_small_const (i : Initialized)
  /-- character size; zero if unknown -/
  | Section_string (sz : Nat)
  /-- literal size; zero if unknown -/
  | Section_literal (sz : Nat)
  | Section_jumptable
  | Section_user (name : String) (writable executable : Bool)
  | Section_debug_abbrev
  | Section_debug_info (s : Option String)
  | Section_debug_loc
  | Section_debug_line (s : Option String)
  | Section_debug_ranges
  | Section_debug_str
  | Section_ais_annotation
  deriving DecidableEq, Repr

open SectionName

/-- `Sections.with_size` -/
def withSize (sz : Nat) : SectionName → SectionName
  | .Section_string _ => .Section_string sz
  | .Section_literal _ => .Section_literal sz
  | sec => sec

/-- `Sections.access_mode` -/
inductive AccessMode where
  | Access_default | Access_near | Access_far
  deriving DecidableEq, Repr

/-- Initialization status of a variable with initializer `init`:
    `[Init_space _]` is uninitialized, an initializer that mentions a symbol
    address needs relocations. -/
def initStatus (init : List InitData) : Initialized :=
  match init with
  | [.Init_space _] => .Uninit
  | _ =>
    if init.any (fun i => match i with | .Init_addrof _ _ => true | _ => false)
    then .Init_reloc else .Init

/-- The default section of a variable (`Sections.for_variable` without
    `#pragma section` or `section` attribute). -/
def forVariable (readonly : Bool) (init : List InitData) : SectionName :=
  if readonly then .Section_const (initStatus init) else .Section_data (initStatus init)

/-- The default sections of a function: code, literals, jump tables
    (`Sections.for_function` without pragmas). -/
def forFunction : SectionName × SectionName × SectionName :=
  (.Section_text, .Section_literal 0, .Section_jumptable)

/-! ### User-defined sections (`#pragma section`, `#pragma use_section`) -/

/-- `Sections.section_info` -/
structure SectionInfo where
  sec_name_init : SectionName
  sec_name_init_reloc : SectionName
  sec_name_uninit : SectionName
  sec_writable : Bool
  sec_executable : Bool
  sec_access : AccessMode
  deriving DecidableEq, Repr

/-- `Sections.default_section_info` -/
def default_section_info : SectionInfo :=
  { sec_name_init := .Section_data .Init,
    sec_name_init_reloc := .Section_data .Init_reloc,
    sec_name_uninit := .Section_data .Uninit,
    sec_writable := true, sec_executable := false, sec_access := .Access_default }

/-- A section info whose three names are `n`. -/
private def uniform (n : SectionName) (w x : Bool) (a : AccessMode) : SectionInfo :=
  { sec_name_init := n, sec_name_init_reloc := n, sec_name_uninit := n,
    sec_writable := w, sec_executable := x, sec_access := a }

/-- A section info `f Init`, `f Init_reloc`, `f Uninit`. -/
private def byInit (f : Initialized → SectionName) (w : Bool) (a : AccessMode) :
    SectionInfo :=
  { sec_name_init := f .Init, sec_name_init_reloc := f .Init_reloc,
    sec_name_uninit := f .Uninit, sec_writable := w, sec_executable := false,
    sec_access := a }

/-- `Sections.builtin_sections` -/
def builtin_sections : List (String × SectionInfo) :=
  [ ("CODE", uniform .Section_text false true .Access_default),
    ("DATA", byInit .Section_data true .Access_default),
    ("SDATA", byInit .Section_small_data true .Access_near),
    ("CONST", byInit .Section_const false .Access_default),
    ("SCONST", byInit .Section_small_const false .Access_near),
    ("STRING", uniform (.Section_string 0) false false .Access_default),
    ("LITERAL", uniform (.Section_literal 0) false false .Access_default),
    ("JUMPTABLE", uniform .Section_jumptable false false .Access_default) ]

/-- The OCaml tables `current_section_table` (section names to section info)
    and `use_section_table` (the section assigned to a global symbol by a
    `use_section` pragma).  As with `Hashtbl.add`/`Hashtbl.find`, the most
    recent binding of `use_section` comes first. -/
structure Table where
  current : List (String × SectionInfo)
  use_section : List (Ident × SectionInfo)
  deriving Repr

/-- `Hashtbl.find` on an association list -/
private def assoc {α β} [BEq α] (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: l => if k' == k then some v else assoc k l

/-- `Sections.initialize` -/
def «initialize» : Table := { current := builtin_sections, use_section := [] }

/-- `Sections.define_section`: define or update a given section. -/
def define_section (t : Table) (name : String) (iname uname : Option String := none)
    (writable executable : Option Bool := none) (access : Option AccessMode := none) :
    Table :=
  let si := (assoc name t.current).getD default_section_info
  let writable := writable.getD si.sec_writable
  let executable := executable.getD si.sec_executable
  let access := access.getD si.sec_access
  let user (o : Option String) (d : SectionName) : SectionName :=
    match o with
    | some s => .Section_user s writable executable
    | none => d
  let new_si : SectionInfo :=
    { sec_name_init := user iname si.sec_name_init,
      sec_name_init_reloc := user iname si.sec_name_init_reloc,
      sec_name_uninit := user uname si.sec_name_uninit,
      sec_writable := writable, sec_executable := executable, sec_access := access }
  { t with current := (name, new_si) :: t.current.filter (·.1 != name) }

/-- `Sections.use_section_for`: explicitly associate a section to a global
    symbol.  `none` (OCaml: `false`) if the section is unknown. -/
def use_section_for (t : Table) (id : Ident) (name : String) : Option Table :=
  (assoc name t.current).map fun si => { t with use_section := (id, si) :: t.use_section }

/-- `Sections.gcc_section`: undeclared section attached to a global variable,
    GCC-style -/
def gcc_section (name : String) (readonly exec : Bool) : SectionInfo :=
  uniform (.Section_user name (!readonly) exec) (!readonly) exec .Access_default

open CParser in
/-- `Sections.get_attr_section`: check and extract whether a section was
    given as attribute -/
def get_attr_section (loc : C.Location) (attr : C.Attributes) :
    M (Option String) := do
  match Cutil.find_custom_attributes ["section", "__section__"] attr with
  | [] => return none
  | [[.AString name]] => return some name
  | [[_]] =>
      Diagnostics.error loc "'section' attribute requires a string"
      return none
  | _ =>
      Diagnostics.error loc "ambiguous 'section' attribute"
      return none

open CParser in
private def findCurrent (t : Table) (name : String) : M SectionInfo :=
  match assoc name t.current with
  | some si => pure si
  | none => assertFalse "Sections"

open CParser in
/-- `Sections.for_variable`: section for a variable definition.
    `small_const` and `small_data` are `Clflags.option_small_const` and
    `Clflags.option_small_data`. -/
def for_variable (small_const small_data : Int) (t : Table) (env : Env.T)
    (loc : C.Location) (id : Ident) (ty : C.Typ) (init : Initialized) :
    M (SectionName × AccessMode) := do
  let attr ← Cutil.attributes_of_type env ty
  let readonly := attr.contains .AConst && !attr.contains .AVolatile
  let si ← match assoc id t.use_section with
    | some si => pure si
    | none =>
      match ← get_attr_section loc attr with
      | some name => pure (gcc_section name readonly false)
      | none =>
        let size ← match ← Cutil.sizeof env ty with
          | some sz => pure sz
          | none => pure (2 ^ 62 - 1 : Int)
        let name :=
          if readonly then (if size ≤ small_const then "SCONST" else "CONST")
          else (if size ≤ small_data then "SDATA" else "DATA")
        findCurrent t name
  let secname := match init with
    | .Uninit => si.sec_name_uninit
    | .Init => si.sec_name_init
    | .Init_reloc => si.sec_name_init_reloc
  return (secname, si.sec_access)

open CParser in
/-- `Sections.for_function`: sections for a function definition (code,
    literals, jump tables). -/
def for_function (t : Table) (loc : C.Location) (id : Ident) (attr : C.Attributes) :
    M (List SectionName) := do
  let si_code ← match assoc id t.use_section with
    | some si => pure si
    | none =>
      match ← get_attr_section loc attr with
      | some name => pure (gcc_section name true true)
      | none => findCurrent t "CODE"
  let si_literal ← findCurrent t "LITERAL"
  let si_jumptbl ← findCurrent t "JUMPTABLE"
  return [si_code.sec_name_init, si_literal.sec_name_init, si_jumptbl.sec_name_init]

/-- `Sections.for_stringlit` -/
def for_stringlit (t : Table) (sz : Nat) : Option SectionName :=
  (assoc "STRING" t.current).map fun si => withSize sz si.sec_name_init

end Sections
end CC
