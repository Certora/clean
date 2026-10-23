/-
  Port of `debug/DebugInformation.ml` (and `.mli`): the collection of
  debugging information (types, global definitions, local variables,
  scopes, live ranges and section addresses) during compilation.

  OCaml keeps this information in module-level references and hash tables.
  Here they are the fields of the record `DebugInformation.St`, and the
  functions run in the monad `DM`, an exception-state monad whose state is
  `St` together with the state of the C front end (`CParser.State`, needed
  by `Cutil.is_function_type` and for `Machine.config`).  The exception
  `Not_found` of `Hashtbl.find` is `Exn.Not_found`; as in OCaml, the side
  effects done before an exception are kept (the state is not rolled back
  by `try ... with Not_found -> ...`).

  The hash tables are modelled by `OHashtbl` (`lib/OCamlHashtbl.lean`),
  which reproduces OCaml's bucket layout and iteration order for `int` and
  `string` keys, so that `fold_types`, `fold_definitions`,
  `fold_section_start` and `compute_diab_file_enum` visit the bindings in
  the same order as the OCaml compiler.  `StringSet` is a sorted list.

  `CBuiltins.builtins.builtin_typedefs` (target specific) is the field
  `builtin_typedefs` of the state.  The record `default_debug` of hook
  functions is `default_debug ref`, where `ref : IO.Ref Full` holds the
  state (the hooks of `Debug.Implem` run in `IO`); an exception of `DM`
  becomes an `IO` error.

  `typ_to_string` prints with `Cprint.print_debug_idents` set, as in OCaml.
-/
import CCLib.debug.Debug
import CCLib.debug.DebugTypes
import CCLib.cparser.Cutil
import CCLib.lib.OCamlHashtbl

namespace CC
namespace DebugInformation

open DebugTypes Sections
open CParser (Exn Env.T)
open CParser.C (Storage Typ Globdecl Location StructOrUnion Attribute Decl)

/-- C identifiers (`C.ident`). -/
abbrev CIdent := CParser.C.Ident

/-! ## State -/

/-- `StringSet.add` on a sorted list. -/
def stringSetAdd (s : String) : List String → List String
  | [] => [s]
  | x :: xs =>
    if s < x then s :: x :: xs
    else if s == x then x :: xs
    else x :: stringSetAdd s xs

/-- The module-level references and hash tables of `DebugInformation.ml`. -/
structure St where
  /-- `id` (the id generator) -/
  id : Int := 0
  /-- `file_name`: the name of the current compilation unit -/
  file_name : String := ""
  /-- `all_files`: all files used in the debug entries (sorted) -/
  all_files : List String := []
  /-- `types`: all types encountered -/
  types : OHashtbl Int DebugTypes := {}
  /-- `lookup_types`: lookup table for types -/
  lookup_types : OHashtbl String Int := {}
  /-- `definitions`: all global definitions encountered -/
  definitions : OHashtbl Int DefinitionType := {}
  /-- `stamp_to_definition` -/
  stamp_to_definition : OHashtbl Int Int := {}
  /-- `name_to_definition` -/
  name_to_definition : OHashtbl String Int := {}
  /-- `atom_to_definition` -/
  atom_to_definition : OHashtbl Ident Int := {}
  /-- `local_variables` -/
  local_variables : OHashtbl Int LocalInformation := {}
  /-- `stamp_to_local` -/
  stamp_to_local : OHashtbl Int Int := {}
  /-- `scope_to_local`: function id + scope id to debug id -/
  scope_to_local : OHashtbl (Int × Int) Int := {}
  /-- `atom_to_scope`: function atom + scope id to debug id -/
  atom_to_scope : OHashtbl (Ident × Int) Int := {}
  /-- `var_locations` -/
  var_locations : OHashtbl (Ident × Ident) VarLocation := {}
  /-- `scope_ranges` -/
  scope_ranges : OHashtbl Int (List ScopeRange) := {}
  /-- `label_translation` -/
  label_translation : OHashtbl (Ident × Positive) Int := {}
  /-- `compilation_section_start` -/
  compilation_section_start : OHashtbl String Int := {}
  /-- `compilation_section_end` -/
  compilation_section_end : OHashtbl String Int := {}
  /-- `diab_additional` -/
  diab_additional : OHashtbl String (Int × Int × SectionName) := {}
  /-- `filenum` -/
  filenum : OHashtbl (String × String) Int := {}
  /-- `printed_symbols` (sorted) -/
  printed_symbols : List String := []
  /-- `CBuiltins.builtins.builtin_typedefs` of the target -/
  builtin_typedefs : List (String × Typ) := []

instance : Inhabited St := ⟨{}⟩

/-- The whole state: the debug information and the state of the C front
    end. -/
structure Full where
  di : St := {}
  fe : CParser.State := {}

instance : Inhabited Full := ⟨{}⟩

/-- The monad of `DebugInformation`. -/
abbrev DM := EStateM Exn Full

def getSt : DM St := do return (← get).di
def modifySt (f : St → St) : DM Unit := modify fun s => { s with di := f s.di }

/-- Run a function of the C front end. -/
def liftFE {α : Type} (x : CParser.M α) : DM α := fun s =>
  match x s.fe with
  | .ok a fe => .ok a { s with fe := fe }
  | .error e fe => .error e { s with fe := fe }

/-- `Hashtbl.find`: `Not_found` on a missing key. -/
def findNF {α : Type} : Option α → DM α
  | some a => pure a
  | none => throw .Not_found

/-- `try x with Not_found -> h` -/
def catchNF {α : Type} (x : DM α) (h : DM α) : DM α :=
  tryCatch x fun
    | .Not_found => h
    | e => throw e

/-- `assert false` -/
def assertFalse {α : Type} (where_ : String) : DM α :=
  throw (.Failure s!"assertion failed in DebugInformation.{where_}")

/-! ## Simple id generator -/

/-- `next_id` -/
def next_id : DM Int := do
  let s ← getSt
  modifySt fun s => { s with id := s.id + 1 }
  return s.id

/-! ## Auxiliary functions -/

/-- `list_replace` -/
def list_replace {α : Type} (c : α → Bool) (f : α → α) (l : List α) : List α :=
  l.map fun a => if c a then f a else a

/-- `add_file` -/
def add_file (file : String) : DM Unit :=
  modifySt fun s => { s with all_files := stringSetAdd file s.all_files }

/-- `get_type` -/
def get_type (id : Int) : DM DebugTypes := do findNF ((← getSt).types.find? id)

/-- `fold_types` -/
def fold_types {α : Type} (f : Int → DebugTypes → α → α) (a : α) : DM α := do
  return (← getSt).types.fold f a

/-- `typ_to_string`: translate a `C.typ` to a string needed for hashing. -/
def typ_to_string (ty : Typ) : String :=
  Format.render (CParser.Cprint.typ { print_debug_idents := true } ty)

/-- `strip_attributes`: we are only interested in `const` and `volatile`. -/
def strip_attributes (typ : Typ) : Typ :=
  CParser.Cutil.strip_attributes_type typ [.AConst, .AVolatile]

/-- `find_type`: find the type id of a type. -/
def find_type (ty : Typ) : DM Int := do
  let ty := strip_attributes ty
  findNF ((← getSt).lookup_types.find? (typ_to_string ty))

/-- inner function `insert` of `insert_type` -/
def insert_aux (d_ty : DebugTypes) (ty : Typ) : DM Int := do
  let id ← next_id
  let name := typ_to_string ty
  modifySt fun s => { s with types := s.types.add id d_ty,
                             lookup_types := s.lookup_types.add name id }
  return id

/-- inner function `size` of `insert_type` (arrays of arrays) -/
def array_sizes : List (Option Int64) → Typ → Typ × List (Option Int64)
  | acc, .TArray child s _ => array_sizes (s :: acc) child
  | acc, t => (t, acc.reverse)

mutual
/-- inner function `typ_aux` of `insert_type` -/
partial def typ_aux (ty : Typ) : DM Int :=
  catchNF (find_type ty) do
    let d_ty ← match ty with
      | .TVoid _ => pure DebugTypes.Void
      | .TInt k _ => pure (.IntegerType { int_kind := k })
      | .TFloat k _ => pure (.FloatType { float_kind := k })
      | .TPtr t _ => do
        let id ← attr_aux t
        pure (.PointerType { pts := id })
      | .TArray t s _ => do
        let (t, s) := array_sizes [s] t
        let id ← attr_aux t
        pure (.ArrayType { arr_type := id, arr_size := s.map (·.map Int64.toInt) })
      | .TFun t param _ _ => do
        let (param, prot) ← match param with
          | none => pure ([], false)
          | some p => do
            let ps ← p.mapM fun (i, t) => do
              let t ← attr_aux t
              pure ({ param_type := t, param_name := i.name } : ParameterType)
            pure (ps, true)
        let ret ← match t with
          | .TVoid _ => pure none
          | _ => some <$> attr_aux t
        pure (.FunctionType { fun_type_return_type := ret, fun_type_prototyped := prot,
                              fun_type_params := param })
      | .TNamed id _ => do
        let typ ← match (← getSt).builtin_typedefs.find? (fun a => a.1 == id.name) with
          | some (_, t) => some <$> attr_aux t
          | none => pure none
        pure (.Typedef { td_file_loc := none, td_name := id.name, typ := typ })
      | .TStruct id _ =>
        pure (.CompositeType { ct_name := id.name, ct_sou := .Struct, ct_file_loc := none,
                               ct_members := [], ct_declaration := true, ct_sizeof := none })
      | .TUnion id _ =>
        pure (.CompositeType { ct_name := id.name, ct_sou := .Union, ct_file_loc := none,
                               ct_members := [], ct_declaration := true, ct_sizeof := none })
      | .TEnum id _ =>
        pure (.EnumType { enum_name := id.name, enum_byte_size := none, enum_file_loc := none,
                          enum_enumerators := [] })
    insert_aux d_ty ty

/-- inner function `attr_aux` of `insert_type` -/
partial def attr_aux (ty : Typ) : DM Int :=
  catchNF (find_type ty) do
    match CParser.Cutil.strip_last_attribute ty with
    | (some .AConst, t) =>
      let id ← attr_aux t
      insert_aux (.ConstType { cst_type := id }) ty
    | (some .AVolatile, t) =>
      let id ← attr_aux t
      insert_aux (.VolatileType { vol_type := id }) ty
    | (some _, t) => attr_aux t
    | (none, t) => typ_aux t
end

/-- `insert_type`: add a type and its information. -/
def insert_type (ty : Typ) : DM Int := attr_aux (strip_attributes ty)

/-- `replace_composite`: replace the composite information. -/
def replace_composite (id : Int) (f : CompositeType → CompositeType) : DM Unit := do
  match ← findNF ((← getSt).types.find? id) with
  | .CompositeType comp =>
    modifySt fun s => { s with types := s.types.replace id (.CompositeType (f comp)) }
  | _ => assertFalse "replace_composite"

/-- `replace_enum`: replace the enum information. -/
def replace_enum (id : Int) (f : EnumType → EnumType) : DM Unit := do
  match ← findNF ((← getSt).types.find? id) with
  | .EnumType comp =>
    modifySt fun s => { s with types := s.types.replace id (.EnumType (f comp)) }
  | _ => assertFalse "replace_enum"

/-- `replace_typedef`: replace the typedef information. -/
def replace_typedef (id : Int) (f : Typedef → Typedef) : DM Unit := do
  match ← findNF ((← getSt).types.find? id) with
  | .Typedef typ =>
    modifySt fun s => { s with types := s.types.replace id (.Typedef (f typ)) }
  | _ => assertFalse "replace_typedef"

/-! ## Global definitions -/

/-- `fold_definitions` -/
def fold_definitions {α : Type} (f : Int → DefinitionType → α → α) (a : α) : DM α := do
  return (← getSt).definitions.fold f a

/-- `find_gvar_stamp` -/
def find_gvar_stamp (id : Int) : DM (Int × GlobalVariableInformation) := do
  let id ← findNF ((← getSt).stamp_to_definition.find? id)
  match ← findNF ((← getSt).definitions.find? id) with
  | .GlobalVariable var => return (id, var)
  | _ => assertFalse "find_gvar_stamp"

/-- `find_fun_stamp` -/
def find_fun_stamp (id : Int) : DM (Int × FunctionInformation) := do
  let id ← findNF ((← getSt).stamp_to_definition.find? id)
  match ← findNF ((← getSt).definitions.find? id) with
  | .Function f => return (id, f)
  | _ => assertFalse "find_fun_stamp"

/-- `find_fun_atom` -/
def find_fun_atom (id : Ident) : DM (Int × FunctionInformation) := do
  let id ← findNF ((← getSt).atom_to_definition.find? id)
  match ← findNF ((← getSt).definitions.find? id) with
  | .Function f => return (id, f)
  | _ => assertFalse "find_fun_atom"

/-- `replace_var` -/
def replace_var (id : Int) (var : GlobalVariableInformation) : DM Unit :=
  modifySt fun s => { s with definitions := s.definitions.replace id (.GlobalVariable var) }

/-- `replace_fun` -/
def replace_fun (id : Int) (f : FunctionInformation) : DM Unit :=
  modifySt fun s => { s with definitions := s.definitions.replace id (.Function f) }

/-! ## Local variables -/

/-- `get_local_variable` -/
def get_local_variable (id : Int) : DM LocalInformation := do
  findNF ((← getSt).local_variables.find? id)

/-- `find_lvar_stamp` -/
def find_lvar_stamp (id : Int) : DM (Int × LocalVariableInformation) := do
  let id ← findNF ((← getSt).stamp_to_local.find? id)
  match ← findNF ((← getSt).local_variables.find? id) with
  | .LocalVariable v => return (id, v)
  | _ => assertFalse "find_lvar_stamp"

/-- `replace_lvar` -/
def replace_lvar (id : Int) (var : LocalVariableInformation) : DM Unit :=
  modifySt fun s => { s with local_variables := s.local_variables.replace id (.LocalVariable var) }

/-- `find_scope_id` -/
def find_scope_id (fid id : Int) : DM (Int × ScopeInformation) := do
  let id ← findNF ((← getSt).scope_to_local.find? (fid, id))
  match ← findNF ((← getSt).local_variables.find? id) with
  | .Scope v => return (id, v)
  | _ => assertFalse "find_scope_id"

/-- `replace_scope` -/
def replace_scope (id : Int) (var : ScopeInformation) : DM Unit :=
  modifySt fun s => { s with local_variables := s.local_variables.replace id (.Scope var) }

/-- `gen_comp_typ` -/
def gen_comp_typ (sou : StructOrUnion) (id : CIdent) (at_ : CParser.C.Attributes) : Typ :=
  if sou == .Struct then .TStruct id at_ else .TUnion id at_

/-- `remove_unused` -/
def remove_unused (id : CIdent) : DM Unit :=
  catchNF (do
    let id' ← findNF ((← getSt).stamp_to_definition.find? id.stamp)
    match ← findNF ((← getSt).definitions.find? id') with
    | .Function _ => pure ()
    | _ => modifySt fun s => { s with definitions := s.definitions.remove id',
                                      stamp_to_definition := s.stamp_to_definition.remove id.stamp })
    (pure ())

/-- `remove_unused_function` -/
def remove_unused_function (id : CIdent) : DM Unit :=
  catchNF (do
    let id' ← findNF ((← getSt).stamp_to_definition.find? id.stamp)
    modifySt fun s => { s with definitions := s.definitions.remove id',
                               stamp_to_definition := s.stamp_to_definition.remove id.stamp })
    (pure ())

/-- `try Hashtbl.find name_to_definition n with Not_found -> (fresh id)` -/
def name_definition_id (n : String) : DM Int := do
  match (← getSt).name_to_definition.find? n with
  | some id' => return id'
  | none =>
    let id' ← next_id
    modifySt fun s => { s with name_to_definition := s.name_to_definition.add n id' }
    return id'

/-- `insert_global_declaration` -/
def insert_global_declaration (env : Env.T) (dec : Globdecl) : DM Unit := do
  add_file dec.gloc.1
  let insert (d_dec : DefinitionType) (stamp : Int) : DM Unit := do
    let id ← next_id
    modifySt fun s => { s with definitions := s.definitions.add id d_dec,
                               stamp_to_definition := s.stamp_to_definition.add stamp id }
  match dec.gdesc with
  | .Gdecl (.mk sto id ty init) =>
    if !(← liftFE (CParser.Cutil.is_function_type env ty)) then
      if !(← getSt).stamp_to_definition.mem id.stamp then
        let (at_decl, ext) := match sto with
          | .Storage_extern => (init.isNone, true)
          | .Storage_static => (false, false)
          | _ => (false, true)
        let ty ← insert_type ty
        let decl : GlobalVariableInformation :=
          { gvar_name := id.name, gvar_atom := none, gvar_file_loc := dec.gloc,
            gvar_declaration := at_decl, gvar_external := ext, gvar_type := ty }
        insert (.GlobalVariable decl) id.stamp
      else if init.isSome || sto != .Storage_extern then
        -- it is a definition
        let (id, var) ← find_gvar_stamp id.stamp
        replace_var id { var with gvar_declaration := false }
    else
      -- implicit declarations need special handling
      let id' ← name_definition_id id.name
      modifySt fun s => { s with stamp_to_definition := s.stamp_to_definition.add id.stamp id' }
  | .Gfundef f =>
    let ret ← match f.fd_ret with
      | .TVoid _ => pure none
      | _ => some <$> insert_type f.fd_ret
    let ext := match f.fd_storage with
      | .Storage_static => false
      | _ => true
    let params ← f.fd_params.mapM fun (p, ty) => do
      let ty ← insert_type ty
      pure ({ parameter_name := p.name, parameter_ident := p.stamp, parameter_atom := none,
              parameter_type := ty } : ParameterInformation)
    let fd : FunctionInformation :=
      { fun_name := f.fd_name.name, fun_atom := none, fun_file_loc := dec.gloc,
        fun_external := ext, fun_return_type := ret, fun_vararg := f.fd_vararg,
        fun_parameter := params, fun_low_pc := none, fun_high_pc := none, fun_scope := none }
    let id' ← name_definition_id f.fd_name.name
    modifySt fun s => { s with stamp_to_definition := s.stamp_to_definition.add f.fd_name.stamp id',
                               definitions := s.definitions.add id' (.Function fd) }
  | .Gcompositedecl sou id at_ =>
    discard <| insert_type (gen_comp_typ sou id at_)
    let id ← find_type (gen_comp_typ sou id [])
    replace_composite id fun comp =>
      if comp.ct_file_loc.isNone then { comp with ct_file_loc := some dec.gloc } else comp
  | .Gcompositedef sou id at_ fi =>
    discard <| insert_type (gen_comp_typ sou id at_)
    let id ← find_type (gen_comp_typ sou id [])
    -- fields without names need no info
    let fi := fi.filter fun f => f.fld_name != ""
    let fields ← fi.mapM fun f => do
      let t ← insert_type f.fld_typ
      pure ({ cfd_name := f.fld_name, cfd_atom := none, cfd_anon := f.fld_anonymous,
              cfd_typ := t, cfd_bit_size := f.fld_bitfield, cfd_bit_offset := none,
              cfd_byte_offset := none, cfd_byte_size := none } : CompositeField)
    replace_composite id fun comp =>
      let loc := if comp.ct_file_loc.isNone then some dec.gloc else comp.ct_file_loc
      { comp with ct_file_loc := loc, ct_members := fields, ct_declaration := false }
  | .Gtypedef id t =>
    let id ← insert_type (.TNamed id [])
    let tid ← insert_type t
    replace_typedef id fun typ => { typ with td_file_loc := some dec.gloc, typ := some tid }
  | .Genumdef n at_ e =>
    discard <| insert_type (.TEnum n at_)
    let id ← find_type (.TEnum n [])
    let enumerator := e.map fun (i, c, _) => ({ e_name := i.name, e_const := c.toInt } : Enumerator)
    replace_enum id fun en =>
      { en with enum_file_loc := some dec.gloc, enum_enumerators := enumerator }
  | .Gpragma _ => pure ()

/-- `atom_is_member` -/
def atom_is_member (id : Ident) (f : CompositeField) : Bool :=
  match f.cfd_atom with
  | none => false
  | some f => f == id

/-- `set_member_atom` -/
def set_member_atom (str_id : Ident) (field : String) (fld_id : Ident) : DM Unit := do
  let sid ← findNF ((← getSt).atom_to_definition.find? str_id)
  replace_composite sid fun comp =>
    let name (f : CompositeField) := f.cfd_name == field
    let members := list_replace name (fun a => { a with cfd_atom := some fld_id }) comp.ct_members
    { comp with ct_members := members }

/-- `set_member_offset` -/
def set_member_offset (str_id fld_id : Ident) (offset : Int) : DM Unit := do
  let id ← findNF ((← getSt).atom_to_definition.find? str_id)
  replace_composite id fun comp =>
    let members := list_replace (atom_is_member fld_id)
      (fun a => { a with cfd_byte_offset := some offset }) comp.ct_members
    { comp with ct_members := members }

/-- `set_composite_size` -/
def set_composite_size (comp : CIdent) (intern_name : Ident) (sou : StructOrUnion)
    (size : Option Int) : DM Unit := do
  let id ← find_type (gen_comp_typ sou comp [])
  modifySt fun s => { s with atom_to_definition := s.atom_to_definition.add intern_name id }
  replace_composite id fun comp => { comp with ct_sizeof := size }

/-- `set_bitfield_offset` -/
def set_bitfield_offset (str_id fld_id : Ident) (bit_ofs byte_ofs size : Int) : DM Unit := do
  let id ← findNF ((← getSt).atom_to_definition.find? str_id)
  replace_composite id fun comp =>
    let members := list_replace (atom_is_member fld_id) (fun a =>
      { a with cfd_bit_offset := some bit_ofs, cfd_byte_size := some size,
               cfd_byte_offset := some byte_ofs }) comp.ct_members
    { comp with ct_members := members }

/-- `atom_global` -/
def atom_global (id : CIdent) (atom : Ident) : DM Unit :=
  catchNF (do
    let id' ← findNF ((← getSt).stamp_to_definition.find? id.stamp)
    match ← findNF ((← getSt).definitions.find? id') with
    | .Function f =>
      replace_fun id' { f with fun_atom := some atom }
      modifySt fun s => { s with atom_to_definition := s.atom_to_definition.add atom id' }
      (← getSt).scope_to_local.iterM (m := DM) fun (fid, sid) tid =>
        if fid == id.stamp then
          modifySt fun s => { s with atom_to_scope := s.atom_to_scope.add (atom, sid) tid }
        else pure ()
    | .GlobalVariable var =>
      replace_var id' { var with gvar_atom := some atom })
    (pure ())

/-- `atom_parameter` -/
def atom_parameter (fid id : CIdent) (atom : Ident) : DM Unit :=
  catchNF (do
    let (fid', f) ← find_fun_stamp fid.stamp
    let name (p : ParameterInformation) := p.parameter_ident == id.stamp
    let params := list_replace name (fun p => { p with parameter_atom := some atom }) f.fun_parameter
    replace_fun fid' { f with fun_parameter := params })
    (pure ())

/-- `add_fun_addr` -/
def add_fun_addr (atom : Ident) (addr : Int × Int) : DM Unit :=
  let (high, low) := addr
  catchNF (do
    let (id, f) ← find_fun_atom atom
    replace_fun id { f with fun_high_pc := some high, fun_low_pc := some low })
    (pure ())

/-- `atom_local_variable` -/
def atom_local_variable (id : CIdent) (atom : Ident) : DM Unit :=
  catchNF (do
    let (id, var) ← find_lvar_stamp id.stamp
    replace_lvar id { var with lvar_atom := some atom })
    (pure ())

/-- `add_lvar_scope` -/
def add_lvar_scope (f_id : Int) (var_id : CIdent) (s_id : Int) : DM Unit :=
  catchNF (do
    let (s_id', scope) ← find_scope_id f_id s_id
    let (var_id, _) ← find_lvar_stamp var_id.stamp
    replace_scope s_id' { scope_variables := var_id :: scope.scope_variables })
    (pure ())

/-- `insert_local_declaration` -/
def insert_local_declaration (sto : Storage) (id : CIdent) (ty : Typ) (loc : Location) : DM Unit := do
  add_file loc.1
  let ty ← insert_type ty
  let var : LocalVariableInformation :=
    { lvar_name := id.name, lvar_atom := none, lvar_file_loc := loc, lvar_type := ty,
      lvar_static := sto == .Storage_static }
  let id' ← next_id
  modifySt fun s => { s with local_variables := s.local_variables.add id' (.LocalVariable var),
                             stamp_to_local := s.stamp_to_local.add id.stamp id' }

/-- `new_scope` -/
def new_scope (f_id sc_id : Int) : DM Int := do
  let scope : ScopeInformation := { scope_variables := [] }
  let id ← next_id
  modifySt fun s => { s with local_variables := s.local_variables.add id (.Scope scope),
                             scope_to_local := s.scope_to_local.add (f_id, sc_id) id }
  return id

/-- `enter_function_scope` -/
def enter_function_scope (fun_id sc_id : Int) : DM Unit :=
  catchNF (do
    let id ← new_scope fun_id sc_id
    let (fun_id, f) ← find_fun_stamp fun_id
    replace_fun fun_id { f with fun_scope := some id })
    (pure ())

/-- `enter_scope` -/
def enter_scope (f_id p_id id : Int) : DM Unit :=
  catchNF (do
    let id' ← new_scope f_id id
    let (p_id', scope) ← find_scope_id f_id p_id
    replace_scope p_id' { scope_variables := id' :: scope.scope_variables })
    (pure ())

/-! ## Locations, scopes and labels -/

/-- `variable_location` -/
def variable_location (var f : Ident) : DM VarLocation := do
  findNF ((← getSt).var_locations.find? (var, f))

/-- `get_scope_ranges` -/
def get_scope_ranges (id : Int) : DM (List ScopeRange) := do
  findNF ((← getSt).scope_ranges.find? id)

/-- `translate_label` -/
def translate_label (f : Ident) (l : Positive) : DM Int := do
  findNF ((← getSt).label_translation.find? (f, l))

/-- `add_label` -/
def add_label (atom : Ident) (p : Positive) (i : Int) : DM Unit :=
  modifySt fun s => { s with label_translation := s.label_translation.add (atom, p) i }

/-- `open_scope` -/
def open_scope (atom : Ident) (s_id : Int) (lbl : Positive) : DM Unit :=
  catchNF (do
    let s_id ← findNF ((← getSt).atom_to_scope.find? (atom, s_id))
    let old_r := ((← getSt).scope_ranges.find? s_id).getD []
    let n_scop : ScopeRange := { start_addr := some lbl, end_addr := none }
    modifySt fun s => { s with scope_ranges := s.scope_ranges.replace s_id (n_scop :: old_r) })
    (pure ())

/-- `close_scope` -/
def close_scope (atom : Ident) (s_id : Int) (lbl : Positive) : DM Unit :=
  catchNF (do
    let s_id ← findNF ((← getSt).atom_to_scope.find? (atom, s_id))
    let old_r := ((← getSt).scope_ranges.find? s_id).getD []
    -- we must have an opening scope
    let (last_r, rest) ← match old_r with
      | a :: rest => pure (a, rest)
      | _ => assertFalse "close_scope"
    let new_r :=
      if last_r.start_addr == some lbl then rest
      else { last_r with end_addr := some lbl } :: rest
    modifySt fun s => { s with scope_ranges := s.scope_ranges.replace s_id new_r })
    (pure ())

/-- `start_live_range` -/
def start_live_range (fv : Ident × Ident) (lbl : Positive) (loc : Int × BuiltinArg Int) : DM Unit := do
  let old_r := ((← getSt).var_locations.find? fv).getD (.RangeLoc [])
  match old_r with
  | .RangeLoc old_r =>
    let n_r : VarRange := { range_start := some lbl, range_end := none, var_loc := loc }
    modifySt fun s => { s with var_locations := s.var_locations.replace fv (.RangeLoc (n_r :: old_r)) }
  | _ => pure ()   -- parameter that is passed as variable

/-- `end_live_range` -/
def end_live_range (fv : Ident × Ident) (lbl : Positive) : DM Unit := do
  match (← getSt).var_locations.find? fv with
  | some (.RangeLoc (n_r :: old_r)) =>
    -- we can skip non open locations
    if n_r.range_end.isNone then
      let n_r := { n_r with range_end := some lbl }
      modifySt fun s => { s with var_locations := s.var_locations.replace fv (.RangeLoc (n_r :: old_r)) }
  | _ => pure ()

/-- `stack_variable` -/
def stack_variable (fv : Ident × Ident) (spl : Int × BuiltinArg Int) : DM Unit :=
  modifySt fun s => { s with var_locations := s.var_locations.add fv (.FunctionLoc spl.1 spl.2) }

/-! ## Sections -/

/-- `section_start` -/
def section_start (n : String) : DM Int := do
  findNF ((← getSt).compilation_section_start.find? n)

/-- `fold_section_start` -/
def fold_section_start {α : Type} (f : String → Int → α → α) (a : α) : DM α := do
  return (← getSt).compilation_section_start.fold f a

/-- `section_end` -/
def section_end (n : String) : DM Int := do
  findNF ((← getSt).compilation_section_end.find? n)

/-- `diab_additional_section` -/
def diab_additional_section (s : String) : DM (Int × Int) := do
  let (line_start, debug_start, _) ← findNF ((← getSt).diab_additional.find? s)
  return (line_start, debug_start)

/-- `section_to_string` -/
def section_to_string : SectionName → String
  | .Section_user n _ _ => n
  | _ => ".text"

/-- `add_diab_info` -/
def add_diab_info (sec : SectionName) (addr1 add2 addr3 : Int) : DM Unit :=
  let sec' := section_to_string sec
  modifySt fun s => { s with
    compilation_section_start := s.compilation_section_start.add sec' addr3,
    diab_additional := s.diab_additional.add sec' (addr1, add2, sec) }

/-- `diab_add_fun_addr` -/
def diab_add_fun_addr (name : Ident) (_ : SectionName) (addr : Int × Int) : DM Unit :=
  add_fun_addr name addr

/-- `gnu_add_fun_addr` -/
def gnu_add_fun_addr (name : Ident) (sec : SectionName) (addr : Int × Int) : DM Unit := do
  let (high, low) := addr
  let sec := section_to_string sec
  if !(← getSt).compilation_section_start.mem sec then
    modifySt fun s => { s with compilation_section_start := s.compilation_section_start.add sec low }
  modifySt fun s => { s with compilation_section_end := s.compilation_section_end.replace sec high }
  add_fun_addr name (high, low)

/-- `exists_section` -/
def exists_section (sec : SectionName) : DM Bool := do
  return (← getSt).compilation_section_start.mem (section_to_string sec)

/-- `diab_file_loc` -/
def diab_file_loc (f l : String) : DM Int := do
  findNF ((← getSt).filenum.find? (f, l))

/-- `compute_diab_file_enum`: the callbacks run in a monad `m` into which
    `DM` can be lifted (in OCaml they print labels as a side effect). -/
def compute_diab_file_enum {m : Type → Type} [Monad m] [MonadLiftT DM m]
    (end_label : SectionName → m Int) (entry_label : String → m Int)
    (line_end : Unit → m Unit) : m Unit := do
  let tbl := (← (getSt : DM St)).diab_additional
  tbl.iterM (m := m) fun sec (_, _, secname) => do
    let e ← end_label secname
    (modifySt fun s => { s with compilation_section_end := s.compilation_section_end.add sec e } : DM Unit)
    for file in (← (getSt : DM St)).all_files do
      let lbl ← entry_label file
      (modifySt fun s => { s with filenum := s.filenum.add (sec, file) lbl } : DM Unit)
    line_end ()

/-- `compute_gnu_file_enum` -/
def compute_gnu_file_enum {m : Type → Type} [Monad m] [MonadLiftT DM m]
    (f : String → m Unit) : m Unit := do
  for file in (← (getSt : DM St)).all_files do f file

/-- `all_files_iter` -/
def all_files_iter {m : Type → Type} [Monad m] [MonadLiftT DM m]
    (f : String → m Unit) : m Unit := compute_gnu_file_enum f

/-- `is_symbol_printed` -/
def is_symbol_printed (id : String) : DM Bool := do
  return (← getSt).printed_symbols.contains id

/-- `symbol_printed` -/
def symbol_printed (id : String) : DM Unit :=
  modifySt fun s => { s with printed_symbols := stringSetAdd id s.printed_symbols }

/-- `file_name` -/
def file_name : DM String := do return (← getSt).file_name

/-- `init`: reset all the tables (`builtin_typedefs` is kept). -/
def init (name : String) : DM Unit :=
  modifySt fun s => { s with
    id := 0
    file_name := name
    types := s.types.reset
    lookup_types := s.lookup_types.reset
    definitions := s.definitions.reset
    stamp_to_definition := s.stamp_to_definition.reset
    name_to_definition := s.name_to_definition.reset
    atom_to_definition := s.atom_to_definition.reset
    local_variables := s.local_variables.reset
    stamp_to_local := s.stamp_to_local.reset
    scope_to_local := s.scope_to_local.reset
    atom_to_scope := s.atom_to_scope.reset
    compilation_section_start := s.compilation_section_start.reset
    compilation_section_end := s.compilation_section_end.reset
    diab_additional := s.diab_additional.reset
    filenum := s.filenum.reset
    var_locations := s.var_locations.reset
    scope_ranges := s.scope_ranges.reset
    label_translation := s.label_translation.reset
    all_files := [name]
    printed_symbols := [] }

/-! ## The hook record -/

/-- Run a `DM` computation on the state held in `ref`; an exception
    becomes an `IO` error. -/
def runIO {α : Type} (ref : IO.Ref Full) (x : DM α) : IO α := do
  match x.run (← ref.get) with
  | .ok a s => ref.set s; return a
  | .error e s => ref.set s; throw (IO.userError s!"DebugInformation: {repr e}")

/-- `default_debug`: the hooks collecting debug information, with their
    state in `ref`.  As in OCaml, `add_fun_addr`, `generate_debug_info` and
    `add_diab_info` do nothing here (`DebugInit` installs the versions of
    `Dwarfgen` and of the Diab/GNU variants). -/
def default_debug (ref : IO.Ref Full) : Debug.Implem where
  init n := runIO ref (init n)
  atom_global id a := runIO ref (atom_global id a)
  set_composite_size id a sou sz := runIO ref (set_composite_size id a sou sz)
  set_member_atom s f fld := runIO ref (set_member_atom s f fld)
  set_member_offset s fld o := runIO ref (set_member_offset s fld o)
  set_bitfield_offset s fld b o sz := runIO ref (set_bitfield_offset s fld b o sz)
  insert_global_declaration env dec := runIO ref (insert_global_declaration env dec)
  add_fun_addr _ _ _ := pure ()
  generate_debug_info _ _ := pure none
  all_files_iter f := do
    for file in (← runIO ref getSt).all_files do f file
  insert_local_declaration sto id ty loc := runIO ref (insert_local_declaration sto id ty loc)
  atom_local_variable id a := runIO ref (atom_local_variable id a)
  enter_scope f p id := runIO ref (enter_scope f p id)
  enter_function_scope f s := runIO ref (enter_function_scope f s)
  add_lvar_scope f v s := runIO ref (add_lvar_scope f v s)
  open_scope a s l := runIO ref (open_scope a s l)
  close_scope a s l := runIO ref (close_scope a s l)
  start_live_range fv l loc := runIO ref (start_live_range fv l loc)
  end_live_range fv l := runIO ref (end_live_range fv l)
  stack_variable fv loc := runIO ref (stack_variable fv loc)
  add_label a p i := runIO ref (add_label a p i)
  atom_parameter f p a := runIO ref (atom_parameter f p a)
  compute_diab_file_enum end_label entry_label line_end := do
    (← runIO ref getSt).diab_additional.iterM (m := IO) fun sec (_, _, secname) => do
      let e ← end_label secname
      runIO ref (modifySt fun s => { s with compilation_section_end := s.compilation_section_end.add sec e })
      for file in (← runIO ref getSt).all_files do
        let lbl ← entry_label file
        runIO ref (modifySt fun s => { s with filenum := s.filenum.add (sec, file) lbl })
      line_end ()
  compute_gnu_file_enum f := do
    for file in (← runIO ref getSt).all_files do f file
  exists_section sec := runIO ref (exists_section sec)
  remove_unused id := runIO ref (remove_unused id)
  remove_unused_function id := runIO ref (remove_unused_function id)
  symbol_printed id := runIO ref (symbol_printed id)
  add_diab_info _ _ _ _ := pure ()

end DebugInformation
end CC
