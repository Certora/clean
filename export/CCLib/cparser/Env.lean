/-
  Port of `cparser/Env.ml`: the typing environment of the C elaborator.

  * The error type `Env.Error` is declared in `Diagnostics.lean` (it is part
    of the exception type `Exn` of the front-end monad); `raise (Error e)`
    is `throw (.EnvError e)`.
  * The global counter `gensym` is the field `gensym` of the front-end
    state, so `fresh_ident` and the `enter_*` functions run in the monad `M`.
  * OCaml's `Env.Init` module (the initial environment with the builtins,
    held in global references) is the structure `Env.InitEnv`, computed by
    `set_builtins`.
-/
import CCLib.cparser.Diagnostics
import Std.Data.HashMap

namespace CC
namespace CParser
namespace Env

open C

/-- Maps over identifiers, accessible both by name and by name + stamp
    (`Env.IdentMap`). -/
abbrev IdentMap (α : Type) := Std.HashMap String (List (Ident × α))

namespace IdentMap

def empty {α} : IdentMap α := {}

/-- Search by name and return topmost binding -/
def lookup {α} (s : String) (m : IdentMap α) : Option (Ident × α) :=
  match m.get? s with
  | some (x :: _) => some x
  | _ => none

/-- Search by identifier and return associated binding -/
def find {α} (id : Ident) (m : IdentMap α) : Option α :=
  match m.get? id.name with
  | none => none
  | some l => (l.find? (fun (id', _) => id'.stamp == id.stamp)).map (·.2)

/-- Insert by identifier -/
def add {α} (id : Ident) (data : α) (m : IdentMap α) : IdentMap α :=
  let l := (m.get? id.name).getD []
  m.insert id.name ((id, data) :: l)

end IdentMap

/-- `fresh_ident s` -/
def fresh_ident (s : String) : M Ident := do
  modify fun st => { st with gensym := st.gensym + 1 }
  return { name := s, stamp := (← get).gensym }

/-- Infos associated with structs or unions -/
structure CompositeInfo where
  ci_kind : StructOrUnion
  /-- members, in order -/
  ci_members : List Field
  /-- alignment; `none` if incomplete -/
  ci_alignof : Option Int
  /-- size; `none` if incomplete -/
  ci_sizeof : Option Int
  /-- attributes, if any -/
  ci_attr : Attributes
  deriving BEq, Inhabited, Repr

/-- Infos associated with an ordinary identifier -/
inductive IdentInfo where
  | II_ident (sto : Storage) (ty : Typ)
  /-- value of enumerator -/
  | II_enum (v : Int64)
  deriving Inhabited

/-- Infos associated with a typedef -/
abbrev TypedefInfo := Typ

/-- Infos associated with an enum -/
structure EnumInfo where
  /-- list of all members -/
  ei_members : List Enumerator
  /-- attributes, if any -/
  ei_attr : Attributes
  deriving Inhabited

/-- Environments -/
structure T where
  env_scope : Int
  env_ident : IdentMap IdentInfo
  env_tag : IdentMap CompositeInfo
  env_typedef : IdentMap TypedefInfo
  env_enum : IdentMap EnumInfo
  deriving Inhabited

def empty : T :=
  { env_scope := 0, env_ident := {}, env_tag := {}, env_typedef := {}, env_enum := {} }

/-- Enter a new scope. -/
def new_scope (env : T) : M T := do
  return { env with env_scope := (← get).gensym + 1 }

def in_current_scope (env : T) (id : Ident) : Bool := id.stamp ≥ env.env_scope

private def raiseE {α} (e : Error) : M α := throw (.EnvError e)

/-! Looking up things by source name -/

def lookup_ident (env : T) (s : String) : M (Ident × IdentInfo) :=
  match IdentMap.lookup s env.env_ident with
  | some r => pure r
  | none => raiseE (.Unbound_identifier s)

def lookup_struct (env : T) (s : String) : M (Ident × CompositeInfo) :=
  match IdentMap.lookup s env.env_tag with
  | some (id, ci) =>
      if ci.ci_kind != .Struct then raiseE (.Tag_mismatch s "struct" "union")
      else pure (id, ci)
  | none => raiseE (.Unbound_tag s "struct")

def lookup_union (env : T) (s : String) : M (Ident × CompositeInfo) :=
  match IdentMap.lookup s env.env_tag with
  | some (id, ci) =>
      if ci.ci_kind != .Union then raiseE (.Tag_mismatch s "union" "struct")
      else pure (id, ci)
  | none => raiseE (.Unbound_tag s "union")

def lookup_composite (env : T) (s : String) : Option (Ident × CompositeInfo) :=
  IdentMap.lookup s env.env_tag

def lookup_typedef (env : T) (s : String) : M (Ident × TypedefInfo) :=
  match IdentMap.lookup s env.env_typedef with
  | some r => pure r
  | none => raiseE (.Unbound_typedef s)

def lookup_enum (env : T) (s : String) : M (Ident × EnumInfo) :=
  match IdentMap.lookup s env.env_enum with
  | some r => pure r
  | none => raiseE (.Unbound_tag s "enum")

/-- Checking if a source name is bound -/
def ident_is_bound (env : T) (s : String) : Bool := env.env_ident.contains s

/-! Finding things by translated identifier -/

def find_ident (env : T) (id : Ident) : M IdentInfo :=
  match IdentMap.find id env.env_ident with
  | some r => pure r
  | none => raiseE (.Unbound_identifier id.name)

def find_struct (env : T) (id : Ident) : M CompositeInfo :=
  match IdentMap.find id env.env_tag with
  | some ci =>
      if ci.ci_kind != .Struct then raiseE (.Tag_mismatch id.name "struct" "union")
      else pure ci
  | none => raiseE (.Unbound_tag id.name "struct")

def find_union (env : T) (id : Ident) : M CompositeInfo :=
  match IdentMap.find id env.env_tag with
  | some ci =>
      if ci.ci_kind != .Union then raiseE (.Tag_mismatch id.name "union" "struct")
      else pure ci
  | none => raiseE (.Unbound_tag id.name "union")

def tag_id : Typ → M Ident
  | .TStruct id _ | .TUnion id _ => pure id
  | _ => assertFalse "Env.tag_id"

/-- `find_member env ci m`: the path of fields leading to member `m`
    (innermost first), looking inside anonymous members; `none` for OCaml's
    `Not_found`. -/
partial def find_member (env : T) (ci : List Field) (m : String) : M (Option (List Field)) :=
  member [] ci
where
  member (acc : List Field) : List Field → M (Option (List Field))
    | [] => pure none
    | f :: rest =>
      if f.fld_name == m then pure (some (f :: acc))
      else if f.fld_anonymous then do
        match ← tag acc f with
        | some r => pure (some r)
        | none => member acc rest
      else member acc rest
  tag (acc : List Field) (fld : Field) : M (Option (List Field)) := do
    let id ← tag_id fld.fld_typ
    match IdentMap.find id env.env_tag with
    | none => pure none
    | some ci => member (fld :: acc) ci.ci_members

def find_struct_member (env : T) (id : Ident) (m : String) : M (List Field) := do
  let ci ← tryCatch (find_struct env id) fun
    | .EnvError (.Unbound_tag _ _) => raiseE (.No_member id.name "struct" m)
    | e => throw e
  match ← find_member env ci.ci_members m with
  | some r => pure r
  | none => raiseE (.No_member id.name "struct" m)

def find_union_member (env : T) (id : Ident) (m : String) : M (List Field) := do
  let ci ← tryCatch (find_union env id) fun
    | .EnvError (.Unbound_tag _ _) => raiseE (.No_member id.name "union" m)
    | e => throw e
  match ← find_member env ci.ci_members m with
  | some r => pure r
  | none => raiseE (.No_member id.name "union" m)

def find_typedef (env : T) (id : Ident) : M TypedefInfo :=
  match IdentMap.find id env.env_typedef with
  | some r => pure r
  | none => raiseE (.Unbound_typedef id.name)

def find_enum (env : T) (id : Ident) : M EnumInfo :=
  match IdentMap.find id env.env_enum with
  | some r => pure r
  | none => raiseE (.Unbound_tag id.name "enum")

/-! Inserting things by source name, with generation of a translated name -/

def enter_ident (env : T) (s : String) (sto : Storage) (ty : Typ) : M (Ident × T) := do
  let id ← fresh_ident s
  return (id, { env with env_ident := IdentMap.add id (.II_ident sto ty) env.env_ident })

def enter_composite (env : T) (s : String) (ci : CompositeInfo) : M (Ident × T) := do
  let id ← fresh_ident s
  return (id, { env with env_tag := IdentMap.add id ci env.env_tag })

def enter_enum_item (env : T) (s : String) (v : Int64) : M (Ident × T) := do
  let id ← fresh_ident s
  return (id, { env with env_ident := IdentMap.add id (.II_enum v) env.env_ident })

def enter_typedef (env : T) (s : String) (info : TypedefInfo) : M (Ident × T) := do
  let id ← fresh_ident s
  return (id, { env with env_typedef := IdentMap.add id info env.env_typedef })

def enter_enum (env : T) (s : String) (info : EnumInfo) : M (Ident × T) := do
  let id ← fresh_ident s
  return (id, { env with env_enum := IdentMap.add id info env.env_enum })

/-! Inserting things by translated name -/

def add_ident (env : T) (id : Ident) (sto : Storage) (ty : Typ) : T :=
  { env with env_ident := IdentMap.add id (.II_ident sto ty) env.env_ident }

def add_composite (env : T) (id : Ident) (ci : CompositeInfo) : T :=
  { env with env_tag := IdentMap.add id ci env.env_tag }

def add_typedef (env : T) (id : Ident) (info : TypedefInfo) : T :=
  { env with env_typedef := IdentMap.add id info env.env_typedef }

def add_enum (env : T) (id : Ident) (info : EnumInfo) : T :=
  info.ei_members.foldl
    (fun env (id, v, _) =>
      { env with env_ident := IdentMap.add id (.II_enum v) env.env_ident })
    { env with env_enum := IdentMap.add id info env.env_enum }

def add_types (env_old env_new : T) : T :=
  { env_new with env_ident := env_old.env_ident, env_scope := env_old.env_scope }

/-! Initial environment describing the built-in types and functions
    (OCaml's module `Env.Init`). -/

structure InitEnv where
  env : T := empty
  /-- the identifiers of the builtins, most recent first -/
  idents : List Ident := []
  /-- their declarations, most recent first -/
  decls : List Globdecl := []
  deriving Inhabited

namespace InitEnv

def no_loc : Location := ("", -1)

def add_typedef (i : InitEnv) (s : String) (ty : Typ) : M InitEnv := do
  let (id, env') ← enter_typedef i.env s ty
  return { env := env', idents := id :: i.idents,
           decls := { gdesc := .Gtypedef id ty, gloc := no_loc } :: i.decls }

def add_function (i : InitEnv) (s : String) (res : Typ) (args : List Typ) (va : Bool) :
    M InitEnv := do
  let params ← args.mapM fun ty => do return (← fresh_ident "", ty)
  let ty := Typ.TFun res (some params) va []
  let (id, env') ← enter_ident i.env s .Storage_extern ty
  return { env := env', idents := id :: i.idents,
           decls := { gdesc := .Gdecl (.mk .Storage_extern id ty none), gloc := no_loc }
                      :: i.decls }

end InitEnv

/-- `set_builtins blt`: the initial environment for the given builtins. -/
def set_builtins (blt : Builtins) : M InitEnv := do
  let mut i : InitEnv := {}
  for (s, ty) in blt.builtin_typedefs do
    i ← i.add_typedef s ty
  for (s, (res, args, va)) in blt.builtin_functions do
    i ← i.add_function s res args va
  return i

def InitEnv.initial (i : InitEnv) : T := i.env
def InitEnv.initial_identifiers (i : InitEnv) : List Ident := i.idents
def InitEnv.initial_declarations (i : InitEnv) : List Globdecl := i.decls.reverse
def InitEnv.is_builtin (i : InitEnv) (name : String) : Bool := ident_is_bound i.env name

/-! Error reporting -/

def composite_tag_name (name : String) : String :=
  if name == "" then "<anonymous>" else name

def error_message : Error → String
  | .Unbound_identifier name => s!"use of undeclared identifier '{name}'"
  | .Unbound_tag name kind => s!"unbound {kind} '{composite_tag_name name}'"
  | .Tag_mismatch name expected actual =>
      s!"'{composite_tag_name name}' was declared as a {actual} but is used as a {expected}"
  | .Unbound_typedef name => s!"unbound typedef '{name}'"
  | .No_member compname compkind memname =>
      s!"no member named '{memname}' in '{compkind} {composite_tag_name compname}'"

end Env
end CParser
end CC
