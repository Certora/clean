/-
  Port of `debug/Dwarfgen.ml`: generation of the DWARF entries
  (`DwarfTypes.DebugEntries`) from the information collected by
  `DebugInformation`.

  * The functions run in the monad `GM`: a reader of the global settings
    `GenConfig` (`Clflags.option_gdepth`, `Clflags.option_gdwarf`,
    `Configuration`, `Sys.getcwd ()`, `Camlcoq.extern_atom` and the file
    numbers of `Fileinfo.filename_info`) over an exception-state monad
    whose state is the state of `DebugInformation` (whose id generator is
    shared, as in OCaml) together with the state `GenSt` of this module.
  * The functor `Dwarfgenaux (Target)` becomes functions taking a `Target`
    (the monadic functions `file_loc` and `string_entry`).  Its local
    references `subrange_type` and `current_section_start` are fields of
    `GenSt`, reset at each instantiation (`newGen`), as each application
    of the OCaml functor creates fresh references.
  * `IntSet` is `Std.HashSet Int` (only membership is observable);
    `StringMap` is a sorted association list.
  * OCaml evaluates the fields of a record from right to left; where
    several fields have side effects (`string_entry`, which may allocate an
    id, and `file_loc`, which may fail) the same order is used here.
  * As in OCaml, the iteration order of the hash tables of
    `DebugInformation` (reproduced by `OHashtbl`) determines the order of
    the generated entries and ids.
-/
import CCLib.debug.DebugInformation
import CCLib.debug.DwarfUtil
import CCLib.driver.Configuration
import CCLib.driver.CommonOptions

namespace CC
namespace Dwarfgen

open DebugTypes DwarfTypes DwarfUtil DebugInformation
open CParser (Exn)
open CParser.C (IKind Location)

/-- `get_opt_val`: values that must be set. -/
def get_opt_val_err : String := "Dwarfgen.get_opt_val"

/-! ## Auxiliary data structures -/

/-- `IntSet` -/
abbrev IntSet := Std.HashSet Int

/-- `dwarf_accu` -/
structure DwarfAccu where
  typs : IntSet := {}
  locs : List LocationEntry := []
  ranges : Int × DwRanges := (0, [])

/-- `up_typs` -/
def up_typs (acc : DwarfAccu) (t : Int) : DwarfAccu := { acc with typs := acc.typs.insert t }

/-- `up_locs` -/
def up_locs (acc : DwarfAccu) (loc : List LocationEntry) : DwarfAccu :=
  { acc with locs := loc ++ acc.locs }

/-- `up_ranges` -/
def up_ranges (acc : DwarfAccu) (r : RangeEntry) : DwRange × DwarfAccu :=
  let (off, old_r) := acc.ranges
  (.Offset off, { acc with ranges := (off + 1, (off, r) :: old_r) })

/-- `empty_accu` -/
def empty_accu : DwarfAccu := {}

/-! ## The monad -/

/-- The global settings read by `Dwarfgen`. -/
structure GenConfig where
  /-- `!Clflags.option_gdepth` -/
  gdepth : Nat := 3
  /-- `!Clflags.option_gdwarf` -/
  gdwarf : Nat := 3
  /-- `Configuration` (`arch`, `system`, `abi`, `model`) -/
  conf : Configuration.Config := Configuration.x86_64_linux
  /-- `Sys.getcwd ()` -/
  cwd : String := ""
  /-- `Camlcoq.extern_atom` -/
  extern_atom : Ident → String := fun _ => ""
  /-- `fst (Hashtbl.find Fileinfo.filename_info f)` -/
  gnu_filenum : String → Option Nat := fun _ => none

instance : Inhabited GenConfig := ⟨{}⟩

/-- The state of the module (`string_table`) and of the current
    instance of the functor `Dwarfgenaux`. -/
structure GenSt where
  /-- `subrange_type` (functor-local) -/
  subrange_type : Option Int := none
  /-- `current_section_start` (functor-local) -/
  current_section_start : Option Int := none
  /-- `string_table` -/
  string_table : OHashtbl String Int := {}

/-- The whole state. -/
structure GFull where
  gen : GenSt := {}
  full : Full := {}

/-- The monad of `Dwarfgen`. -/
abbrev GM := ReaderT GenConfig (EStateM Exn GFull)

/-- Run a function of `DebugInformation`. -/
def liftDI {α : Type} (x : DM α) : GM α := fun _ s =>
  match x s.full with
  | .ok a f => .ok a { s with full := f }
  | .error e f => .error e { s with full := f }

instance : MonadLift DM GM := ⟨liftDI⟩

def getGen : GM GenSt := do return (← getThe GFull).gen
def modifyGen (f : GenSt → GenSt) : GM Unit := modifyThe GFull fun s => { s with gen := f s.gen }

/-- `get_opt_val` -/
def get_opt_val {α : Type} : Option α → GM α
  | some a => pure a
  | none => throw (.Failure s!"assertion failed in {get_opt_val_err}")

/-- `assert false` -/
def assertFalse {α : Type} (where_ : String) : GM α :=
  throw (.Failure s!"assertion failed in Dwarfgen.{where_}")

/-- `try x with Not_found -> h` -/
def catchNF {α : Type} (x : GM α) (h : GM α) : GM α :=
  tryCatch x fun
    | .Not_found => h
    | e => throw e

/-- `next_id ()` (the id generator of `DebugInformation`) -/
def next_id : GM Int := liftDI DebugInformation.next_id

/-- Ids, labels and addresses are non-negative. -/
def ref (i : Int) : Nat := i.toNat

/-- `camlint_of_coqint` on a `ptrofs` (wrapped to a signed 32-bit integer) -/
def camlint_of_ptrofs (ofs : Integers.Ptrofs) : Int :=
  let v : Nat := ofs.toNat % 2 ^ 32
  if v ≥ 2 ^ 31 then (v : Int) - 2 ^ 32 else v

/-- `Int32.add` -/
def int32_add (a b : Int) : Int :=
  let v := (a + b) % (2 ^ 32 : Int)
  if v ≥ 2 ^ 31 then v - 2 ^ 32 else v

/-! ## The functor `Dwarfgenaux` -/

/-- `module type TARGET` -/
structure Target where
  file_loc : String × Int → GM FileLoc
  string_entry : String → GM StringConst

/-- A new instance of the functor: fresh local references. -/
def newGen : GM Unit :=
  modifyGen fun g => { g with subrange_type := none, current_section_start := none }

section Gen
variable (T : Target)

/-- `name_opt` -/
def name_opt (n : String) : GM (Option StringConst) :=
  if n != "" then some <$> T.string_entry n else pure none

/-- `encoding_of_ikind` -/
def encoding_of_ikind (k : IKind) : GM Encoding := do
  match k with
  | .IBool => return .DW_ATE_boolean
  | .IChar =>
    let cfg ← liftDI (liftFE CParser.getConfig)
    return if cfg.char_signed then .DW_ATE_signed_char else .DW_ATE_unsigned_char
  | .IInt | .ILong | .ILongLong | .IShort | .ISChar => return .DW_ATE_signed
  | _ => return .DW_ATE_unsigned

/-- `int_type_to_entry` -/
def int_type_to_entry (id : Int) (i : IntType) : GM DwEntry := do
  let encoding ← encoding_of_ikind i.int_kind
  let name ← T.string_entry (typ_to_string (.TInt i.int_kind []))
  let sz ← liftDI (liftFE (CParser.Cutil.sizeof_ikind i.int_kind))
  let int : DwTagBaseType :=
    { base_type_byte_size := sz, base_type_encoding := some encoding, base_type_name := name }
  return new_entry (ref id) (.DW_TAG_base_type int)

/-- `float_type_to_entry` -/
def float_type_to_entry (id : Int) (f : FloatType) : GM DwEntry := do
  let byte_size ← liftDI (liftFE (CParser.Cutil.sizeof_fkind f.float_kind))
  let name ← T.string_entry (typ_to_string (.TFloat f.float_kind []))
  let float : DwTagBaseType :=
    { base_type_byte_size := byte_size, base_type_encoding := some .DW_ATE_float,
      base_type_name := name }
  return new_entry (ref id) (.DW_TAG_base_type float)

/-- `void_to_entry` -/
def void_to_entry (id : Int) : GM DwEntry := do
  let name ← T.string_entry "void"
  let void : DwTagBaseType :=
    { base_type_byte_size := 0, base_type_encoding := none, base_type_name := name }
  return new_entry (ref id) (.DW_TAG_base_type void)

/-- `file_loc_opt` -/
def file_loc_opt : Option Location → GM (Option FileLoc)
  | none => pure none
  | some (f, l) => catchNF (some <$> T.file_loc (f, l)) (pure none)

/-- `typedef_to_entry` -/
def typedef_to_entry (id : Int) (t : Typedef) : GM DwEntry := do
  let i ← get_opt_val t.typ
  let name ← T.string_entry t.td_name
  let loc ← file_loc_opt T t.td_file_loc
  let td : DwTagTypedef := { typedef_file_loc := loc, typedef_name := name, typedef_type := ref i }
  return new_entry (ref id) (.DW_TAG_typedef td)

/-- `pointer_to_entry` -/
def pointer_to_entry (id : Int) (p : PtrType) : DwEntry :=
  new_entry (ref id) (.DW_TAG_pointer_type { pointer_type := ref p.pts })

/-- `array_to_entry` -/
def array_to_entry (id : Int) (arr : ArrayType) : GM DwEntry := do
  let arr_entry := new_entry (ref id) (.DW_TAG_array_type { array_type := ref arr.arr_type })
  let children ← arr.arr_size.mapM fun a => do
    let r := match a with
      | none => none
      | some i => if i != 0 then some (BoundValue.BoundConst (i - 1)) else none
    let st ← match (← getGen).subrange_type with
      | none =>
        let id ← next_id
        modifyGen fun g => { g with subrange_type := some id }
        pure id
      | some id => pure id
    let s : DwTagSubrangeType := { subrange_type := ref st, subrange_upper_bound := r }
    return new_entry (ref (← next_id)) (.DW_TAG_subrange_type s)
  return add_children arr_entry children

/-- `const_to_entry` -/
def const_to_entry (id : Int) (c : ConstType) : DwEntry :=
  new_entry (ref id) (.DW_TAG_const_type { const_type := ref c.cst_type })

/-- `volatile_to_entry` -/
def volatile_to_entry (id : Int) (v : VolatileType) : DwEntry :=
  new_entry (ref id) (.DW_TAG_volatile_type { volatile_type := ref v.vol_type })

/-- `enum_to_entry` -/
def enum_to_entry (id : Int) (e : EnumType) : GM DwEntry := do
  let enumerator_to_entry (e : Enumerator) : GM DwEntry := do
    let name ← T.string_entry e.e_name
    let tag : DwTagEnumerator := { enumerator_value := e.e_const, enumerator_name := name }
    return new_entry (ref (← next_id)) (.DW_TAG_enumerator tag)
  let bs ← liftDI (liftFE (CParser.Cutil.sizeof_ikind CParser.Cutil.enum_ikind))
  let name ← T.string_entry e.enum_name
  let loc ← file_loc_opt T e.enum_file_loc
  let enum : DwTagEnumerationType :=
    { enumeration_file_loc := loc, enumeration_byte_size := bs,
      enumeration_declaration := some false, enumeration_name := name }
  let enum := new_entry (ref id) (.DW_TAG_enumeration_type enum)
  let children ← e.enum_enumerators.mapM enumerator_to_entry
  return add_children enum children

/-- `fun_type_to_entry` -/
def fun_type_to_entry (id : Int) (f : FunctionType) : GM DwEntry := do
  let children ←
    if !f.fun_type_prototyped then do
      let u : DwTagUnspecifiedParameter := { unspecified_parameter_artificial := none }
      pure [new_entry (ref (← next_id)) (.DW_TAG_unspecified_parameter u)]
    else
      f.fun_type_params.mapM fun p => do
        let fp : DwTagFormalParameter :=
          { formal_parameter_artificial := none, formal_parameter_name := none,
            formal_parameter_type := ref p.param_type,
            formal_parameter_variable_parameter := none, formal_parameter_location := none }
        return new_entry (ref (← next_id)) (.DW_TAG_formal_parameter fp)
  let s : DwTagSubroutineType :=
    { subroutine_type := f.fun_type_return_type.map ref,
      subroutine_prototyped := f.fun_type_prototyped }
  return add_children (new_entry (ref id) (.DW_TAG_subroutine_type s)) children

/-- `member_to_entry` -/
def member_to_entry (mem : CompositeField) : GM DwEntry := do
  let name ← if mem.cfd_anon then pure none else some <$> T.string_entry mem.cfd_name
  let m : DwTagMember :=
    { member_byte_size := mem.cfd_byte_size, member_bit_offset := mem.cfd_bit_offset,
      member_bit_size := mem.cfd_bit_size,
      member_data_member_location :=
        mem.cfd_byte_offset.map fun s => .DataLocBlock (.DW_OP_plus_uconst s),
      member_declaration := none, member_name := name, member_type := ref mem.cfd_typ }
  return new_entry (ref (← next_id)) (.DW_TAG_member m)

/-- `struct_to_entry` -/
def struct_to_entry (id : Int) (s : CompositeType) : GM DwEntry := do
  let name ← name_opt T s.ct_name
  let loc ← file_loc_opt T s.ct_file_loc
  let tag : DwTagStructureType :=
    { structure_file_loc := loc, structure_byte_size := s.ct_sizeof,
      structure_declaration := if s.ct_declaration then some s.ct_declaration else none,
      structure_name := name }
  let entry := new_entry (ref id) (.DW_TAG_structure_type tag)
  let child ← s.ct_members.mapM (member_to_entry T)
  return add_children entry child

/-- `union_to_entry` -/
def union_to_entry (id : Int) (s : CompositeType) : GM DwEntry := do
  let name ← name_opt T s.ct_name
  let loc ← file_loc_opt T s.ct_file_loc
  let tag : DwTagUnionType :=
    { union_file_loc := loc, union_byte_size := s.ct_sizeof,
      union_declaration := if s.ct_declaration then some s.ct_declaration else none,
      union_name := name }
  let entry := new_entry (ref id) (.DW_TAG_union_type tag)
  let child ← s.ct_members.mapM (member_to_entry T)
  return add_children entry child

/-- `composite_to_entry` -/
def composite_to_entry (id : Int) (s : CompositeType) : GM DwEntry :=
  match s.ct_sou with
  | .Struct => struct_to_entry T id s
  | .Union => union_to_entry T id s

/-- `infotype_to_entry` -/
def infotype_to_entry (id : Int) : DebugTypes → GM DwEntry
  | .IntegerType i => int_type_to_entry T id i
  | .FloatType f => float_type_to_entry T id f
  | .PointerType p => pure (pointer_to_entry id p)
  | .ArrayType arr => array_to_entry id arr
  | .CompositeType c => composite_to_entry T id c
  | .EnumType e => enum_to_entry T id e
  | .FunctionType f => fun_type_to_entry id f
  | .Typedef t => typedef_to_entry T id t
  | .ConstType c => pure (const_to_entry id c)
  | .VolatileType v => pure (volatile_to_entry id v)
  | .Void => void_to_entry T id

/-- `needs_types` -/
def needs_types (id : Int) (d : IntSet) : GM (IntSet × Bool) := do
  let add_type (id : Int) (d : IntSet) : IntSet × Bool :=
    if !d.contains id then (d.insert id, true) else (d, false)
  match ← liftDI (get_type id) with
  | .IntegerType _ | .FloatType _ | .Void | .EnumType _ => return (d, false)
  | .Typedef t => return add_type (← get_opt_val t.typ) d
  | .PointerType p => return add_type p.pts d
  | .ArrayType arr => return add_type arr.arr_type d
  | .ConstType c => return add_type c.cst_type d
  | .VolatileType v => return add_type v.vol_type d
  | .FunctionType f =>
    let (d, c) := match f.fun_type_return_type with
      | some t => add_type t d
      | none => (d, false)
    return f.fun_type_params.foldl (fun (d, c) p =>
      let (d, c') := add_type p.param_type d
      (d, c || c')) (d, c)
  | .CompositeType c =>
    return c.ct_members.foldl (fun (d, c) f =>
      let (d, c') := add_type f.cfd_typ d
      (d, c || c')) (d, false)

/-- `gen_types` -/
partial def gen_types (needed : IntSet) : GM (List DwEntry) := do
  let rec aux (d : IntSet) : GM IntSet := do
    let (d', c) ← d.toList.foldlM (fun (d, c) id => do
      let (d, c') ← needs_types id d
      pure (d, c || c')) (d, false)
    if c then aux d' else pure d'
  let typs ← aux needed
  let res ← ((← liftDI getSt).types.toList.filter fun (id, _) => typs.contains id).mapM
    fun (id, t) => infotype_to_entry T id t
  match (← getGen).subrange_type with
  | none => return res
  | some id =>
    let encoding ← encoding_of_ikind (← liftDI (liftFE CParser.Cutil.size_t_ikind))
    let name ← T.string_entry "sizetype"
    let cfg ← liftDI (liftFE CParser.getConfig)
    let tag : DwTagBaseType :=
      { base_type_byte_size := cfg.sizeof_size_t, base_type_encoding := some encoding,
        base_type_name := name }
    return new_entry (ref id) (.DW_TAG_base_type tag) :: res

/-- `global_variable_to_entry` -/
def global_variable_to_entry (acc : DwarfAccu) (id : Int) (v : GlobalVariableInformation) :
    GM (DwEntry × DwarfAccu) := do
  let loc ← match v.gvar_atom with
    | some a =>
      if ← liftDI (is_symbol_printed ((← read).extern_atom a)) then
        pure (some (LocationValue.LocSymbol a))
      else pure none
    | none => pure none
  let name ← T.string_entry v.gvar_name
  let floc ← T.file_loc v.gvar_file_loc
  let var : DwTagVariable :=
    { variable_file_loc := floc, variable_declaration := some v.gvar_declaration,
      variable_external := some v.gvar_external, variable_name := name,
      variable_type := ref v.gvar_type, variable_location := loc }
  let acc := up_typs acc v.gvar_type
  return (new_entry (ref id) (.DW_TAG_variable var), acc)

/-- `gen_splitlong` -/
def gen_splitlong (op_hi op_lo : List LocationExpression) : List LocationExpression :=
  let op_piece := LocationExpression.DW_OP_piece 4
  op_piece :: op_hi ++ (op_piece :: op_lo)

/-- `translate_function_loc` -/
def translate_function_loc (a : Int) : BuiltinArg Int → Option LocationValue × List LocationEntry
  | .BA_addrstack ofs =>
    (some (.LocSimple (.DW_OP_bregx a (camlint_of_ptrofs ofs))), [])
  | .BA_splitlong (.BA_addrstack hi) (.BA_addrstack lo) =>
    let hi := camlint_of_ptrofs hi
    let lo := camlint_of_ptrofs lo
    if lo == int32_add hi 4 then
      (some (.LocSimple (.DW_OP_bregx a hi)), [])
    else
      (some (.LocList (gen_splitlong [.DW_OP_bregx a hi] [.DW_OP_bregx a lo])), [])
  | _ => (none, [])

/-- inner function `aux` of `range_entry_loc` -/
def range_entry_loc_aux (sp : Int) : BuiltinArg Int → GM (List LocationExpression)
  | .BA i => pure [.DW_OP_reg i]
  | .BA_addrstack ofs => pure [.DW_OP_bregx sp (camlint_of_ptrofs ofs)]
  | .BA_splitlong hi lo => do
    let hi ← range_entry_loc_aux sp hi
    let lo ← range_entry_loc_aux sp lo
    pure (gen_splitlong hi lo)
  | _ => assertFalse "range_entry_loc"

/-- `range_entry_loc` -/
def range_entry_loc (spl : Int × BuiltinArg Int) : GM LocationValue := do
  match ← range_entry_loc_aux spl.1 spl.2 with
  | [] => assertFalse "range_entry_loc"
  | [a] => return .LocSimple a
  | a :: rest => return .LocList (a :: rest)

/-- `location_entry` -/
def location_entry (f_id atom : Ident) : GM (Option LocationValue × List LocationEntry) := do
  if (← read).gdepth > 2 then
    catchNF (do
      match ← liftDI (variable_location f_id atom) with
      | .FunctionLoc a r => return translate_function_loc a r
      | .RangeLoc l =>
        let l ← l.foldlM (fun acc i => do
          let hi ← get_opt_val i.range_start
          let lo ← get_opt_val i.range_end
          let hi ← liftDI (translate_label f_id hi)
          let lo ← liftDI (translate_label f_id lo)
          let e ← range_entry_loc i.var_loc
          return (ref hi, ref lo, e) :: acc) []
        let id ← next_id
        let sec := (← getGen).current_section_start
        return (some (.LocRef (ref id)),
                [{ loc_sec_begin := sec.map ref, loc := l, loc_id := ref id }]))
      (pure (none, []))
  else
    return (none, [])

/-- `function_parameter_to_entry` -/
def function_parameter_to_entry (f_id : Ident) (acc : DwarfAccu) (p : ParameterInformation) :
    GM (DwEntry × DwarfAccu) := do
  let (loc, loc_list) ← match p.parameter_atom with
    | none => pure (none, [])
    | some p => location_entry f_id p
  let name ← name_opt T p.parameter_name
  let p : DwTagFormalParameter :=
    { formal_parameter_artificial := none, formal_parameter_name := name,
      formal_parameter_type := ref p.parameter_type,
      formal_parameter_variable_parameter := none, formal_parameter_location := loc }
  let acc := up_locs (up_typs acc p.formal_parameter_type) loc_list
  return (new_entry (ref (← next_id)) (.DW_TAG_formal_parameter p), acc)

/-- `scope_range` -/
def scope_range (f_id : Ident) (id : Int) (acc : DwarfAccu) : GM (DwRange × DwarfAccu) :=
  catchNF (do
    let r ← liftDI (get_scope_ranges id)
    let lbl (l h : Option Positive) : GM (Nat × Nat) := do
      match l, h with
      | some l, some h =>
        let l ← liftDI (translate_label f_id l)
        let h ← liftDI (translate_label f_id h)
        return (ref l, ref h)
      | _, _ => throw .Not_found
    match r with
    | [] => return (.Empty, acc)
    | [a] =>
      let (l, h) ← lbl a.start_addr a.end_addr
      return (.Pc_pair l h, acc)
    | a :: rest =>
      if (← read).gdwarf > 2 then
        let r ← r.mapM fun e => lbl e.start_addr e.end_addr
        let r := match (← getGen).current_section_start with
          | none => RangeEntry.AddressRange r
          | some s => .OffsetRange (ref s) r
        return up_ranges acc r
      else
        let last ← match rest.reverse with
          | x :: _ => pure x
          | [] => throw (.Failure "hd")
        let (l, h) ← lbl last.start_addr a.end_addr
        return (.Pc_pair l h, acc))
    (pure (.Empty, acc))

mutual
/-- `local_variable_to_entry` -/
partial def local_variable_to_entry (f_id : Ident) (acc : DwarfAccu)
    (v : LocalVariableInformation) (id : Int) : GM (Option DwEntry × DwarfAccu) := do
  match v.lvar_atom with
  | none => return (none, acc)
  | some loc =>
    let (loc, loc_list) ← location_entry f_id loc
    let name ← T.string_entry v.lvar_name
    let floc ← T.file_loc v.lvar_file_loc
    let var : DwTagVariable :=
      { variable_file_loc := floc, variable_declaration := none, variable_external := none,
        variable_name := name, variable_type := ref v.lvar_type, variable_location := loc }
    let acc := up_locs (up_typs acc v.lvar_type) loc_list
    return (some (new_entry (ref id) (.DW_TAG_variable var)), acc)

/-- `scope_to_entry` -/
partial def scope_to_entry (f_id : Ident) (acc : DwarfAccu) (sc : ScopeInformation) (id : Int) :
    GM (DwEntry × DwarfAccu) := do
  let (r, acc) ← scope_range f_id id acc
  let scope : DwTagLexicalBlock := { lexical_block_range := r }
  let (vars, acc) ← mmap_opt f_id acc sc.scope_variables
  let entry := new_entry (ref id) (.DW_TAG_lexical_block scope)
  return (add_children entry vars, acc)

/-- `local_to_entry` -/
partial def local_to_entry (f_id : Ident) (acc : DwarfAccu) (id : Int) :
    GM (Option DwEntry × DwarfAccu) := do
  match ← liftDI (get_local_variable id) with
  | .LocalVariable v => local_variable_to_entry f_id acc v id
  | .Scope v =>
    let (s, acc) ← scope_to_entry f_id acc v id
    return (some s, acc)

/-- `mmap_opt (local_to_entry f_id)` -/
partial def mmap_opt (f_id : Ident) (env : DwarfAccu) : List Int → GM (List DwEntry × DwarfAccu)
  | [] => pure ([], env)
  | hd :: tl => do
    let (hd', env1) ← local_to_entry f_id env hd
    let (tl', env2) ← mmap_opt f_id env1 tl
    match hd' with
    | some hd => return (hd :: tl', env2)
    | none => return (tl', env2)
end

/-- `fun_scope_to_entries` -/
def fun_scope_to_entries (f_id : Ident) (acc : DwarfAccu) :
    Option Int → GM (List DwEntry × DwarfAccu)
  | none => pure ([], acc)
  | some id => do
    match ← liftDI (get_local_variable id) with
    | .Scope sc => mmap_opt T f_id acc sc.scope_variables
    | _ => assertFalse "fun_scope_to_entries"

/-- `mmap (function_parameter_to_entry f_id)` -/
def mmap_params (f_id : Ident) (env : DwarfAccu) :
    List ParameterInformation → GM (List DwEntry × DwarfAccu)
  | [] => pure ([], env)
  | hd :: tl => do
    let (hd', env1) ← function_parameter_to_entry T f_id env hd
    let (tl', env2) ← mmap_params f_id env1 tl
    return (hd' :: tl', env2)

/-- `function_to_entry` -/
def function_to_entry (sec_name : Ident → String) (acc : DwarfAccu) (id : Int)
    (f : FunctionInformation) : GM (DwEntry × DwarfAccu) := do
  let r := match f.fun_low_pc, f.fun_high_pc with
    | some l, some h => DwRange.Pc_pair (ref l) (ref h)
    | _, _ => .Empty
  let name ← T.string_entry f.fun_name
  let floc ← T.file_loc f.fun_file_loc
  let f_tag : DwTagSubprogram :=
    { subprogram_file_loc := floc, subprogram_external := some f.fun_external,
      subprogram_name := name, subprogram_prototyped := true,
      subprogram_type := f.fun_return_type.map ref, subprogram_range := r }
  let f_id ← get_opt_val f.fun_atom
  let start_sec ← catchNF (some <$> liftDI (section_start (sec_name f_id))) (pure none)
  modifyGen fun g => { g with current_section_start := start_sec }
  let acc := match f.fun_return_type with
    | some s => up_typs acc s
    | none => acc
  let f_entry := new_entry (ref id) (.DW_TAG_subprogram f_tag)
  let (children, acc) ←
    if (← read).gdepth > 1 then do
      let (params, acc) ← mmap_params T f_id acc f.fun_parameter
      let (vars, acc) ← fun_scope_to_entries T f_id acc f.fun_scope
      pure (params ++ vars, acc)
    else pure ([], acc)
  return (add_children f_entry children, acc)

/-- `definition_to_entry` -/
def definition_to_entry (sec_name : Ident → String) (acc : DwarfAccu) (id : Int) :
    DefinitionType → GM (Option (DwEntry × DwarfAccu))
  | .GlobalVariable g => some <$> global_variable_to_entry T acc id g
  | .Function f => do
    if ← liftDI (is_symbol_printed f.fun_name) then
      some <$> function_to_entry T sec_name acc id f
    else
      return none

end Gen

/-! ## Diab -/

/-- `diab_file_loc sec (f, l)` -/
def diab_file_loc (sec : String) (fl : String × Int) : GM FileLoc := do
  return .Diab_file_loc (← liftDI (DebugInformation.diab_file_loc sec fl.1)) fl.2

/-- `prod_name` -/
def prod_name (conf : Configuration.Config) : String :=
  let version_string :=
    if CommonOptions.buildnr != "" && CommonOptions.tag != "" && CommonOptions.branch != "" then
      s!"Release: {CommonOptions.version}, Build: {CommonOptions.buildnr}, Tag: {CommonOptions.tag}, Branch:{CommonOptions.branch}"
    else CommonOptions.version
  s!"AbsInt Angewandte Informatik GmbH:CompCert Version {version_string}:({conf.arch},{conf.system},{conf.abi},{conf.model})"

/-- `diab_gen_compilation_section` -/
def diab_gen_compilation_section (sec_name : Ident → String) (s : String)
    (defs : List (Int × DefinitionType)) (acc : DiabEntries) : GM DiabEntries := do
  newGen
  let T : Target := { file_loc := diab_file_loc s, string_entry := fun s => pure (.Simple_string s) }
  let (defs, accu) ← defs.foldlM (fun (acc, bcc) (id, t) => do
    match ← definition_to_entry T sec_name bcc id t with
    | some (t, bcc) => return (t :: acc, bcc)
    | none => return (acc, bcc)) ([], empty_accu)
  let low_pc ← liftDI (section_start s)
  let (line_start, debug_start) ← liftDI (diab_additional_section s)
  let high_pc ← liftDI (section_end s)
  let cp : DwTagCompileUnit :=
    { compile_unit_name := .Simple_string (← liftDI file_name),
      compile_unit_range := .Pc_pair (ref low_pc) (ref high_pc),
      compile_unit_dir := .Simple_string (← read).cwd,
      compile_unit_prod_name := .Simple_string (prod_name (← read).conf) }
  let cp := new_entry (ref (← next_id)) (.DW_TAG_compile_unit cp)
  let cp := add_children cp ((← gen_types T accu.typs) ++ defs)
  return { section_name := s, start_label := ref debug_start, line_label := ref line_start,
           diab_entry := cp, diab_locs := accu.locs } :: acc

/-- `StringMap.add` on a sorted association list. -/
def stringMapAdd {α : Type} (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k == k' then (k, v) :: rest
    else (k', v') :: stringMapAdd k v rest

/-- `gen_diab_debug_info` -/
def gen_diab_debug_info (sec_name : Ident → String) (var_section : String) : GM DebugEntries := do
  let defs ← (← liftDI getSt).definitions.toList.foldlM (fun acc (id, t) => do
    let s ← match t with
      | .GlobalVariable _ => pure var_section
      | .Function f => sec_name <$> get_opt_val f.fun_atom
    let old := (acc.lookup s).getD []
    return stringMapAdd s ((id, t) :: old) acc) ([] : List (String × List (Int × DefinitionType)))
  let entries ← defs.foldlM (fun acc (s, d) => diab_gen_compilation_section sec_name s d acc) []
  return .Diab entries

/-! ## GNU -/

/-- `gnu_file_loc` -/
def gnu_file_loc (fl : String × Int) : GM FileLoc := do
  match (← read).gnu_filenum fl.1 with
  | some n => return .Gnu_file_loc n fl.2
  | none => throw .Not_found

/-- `gnu_string_entry` -/
def gnu_string_entry (s : String) : GM StringConst := do
  let system := (← read).conf.system
  -- macos needs debug_str; Cygwin does not use the debug_str section
  if (s.utf8ByteSize < 4 && system != "macos") || system == "cygwin" then
    return .Simple_string s
  else
    match (← getGen).string_table.find? s with
    | some i => return .Offset_string (ref i) s
    | none =>
      let id ← next_id
      modifyGen fun g => { g with string_table := g.string_table.add s id }
      return .Offset_string (ref id) s

/-- `gen_gnu_debug_info` -/
def gen_gnu_debug_info (sec_name : Ident → String) (var_section : String) : GM DebugEntries := do
  modifyGen fun g => { g with string_table := g.string_table.reset }
  let (r, accu) ← catchNF (do
      if (← read).gdwarf > 2 then
        let pcs ← (← liftDI getSt).compilation_section_start.toList.foldlM (fun acc (s, low) => do
          return (ref low, ref (← liftDI (section_end s))) :: acc) []
        match pcs with
        | [] => return (DwRange.Empty, empty_accu)
        | [(l, h)] => return (.Pc_pair l h, empty_accu)
        | _ => return up_ranges empty_accu (.AddressRange pcs)
      else
        let l ← liftDI (section_start ".text")
        let h ← liftDI (section_end ".text")
        return (.Pc_pair (ref l) (ref h), empty_accu))
    (pure (.Empty, empty_accu))
  newGen
  let T : Target := { file_loc := gnu_file_loc, string_entry := gnu_string_entry }
  let (defs, accu, sec) ← (← liftDI getSt).definitions.toList.foldlM
    (fun (acc, bcc, sec) (id, t) => do
      let s ← match t with
        | .GlobalVariable _ => pure var_section
        | .Function f => sec_name <$> get_opt_val f.fun_atom
      match ← definition_to_entry T sec_name bcc id t with
      | some (t, bcc) => return (t :: acc, bcc, stringSetAdd s sec)
      | none => return (acc, bcc, sec)) ([], accu, ([] : List String))
  let types ← gen_types T accu.typs
  -- the fields of the record are evaluated from right to left
  let prod ← gnu_string_entry (prod_name (← read).conf)
  let dir ← gnu_string_entry (← read).cwd
  let name ← gnu_string_entry (← liftDI file_name)
  let cp : DwTagCompileUnit :=
    { compile_unit_name := name, compile_unit_range := r, compile_unit_dir := dir,
      compile_unit_prod_name := prod }
  let cp := new_entry (ref (← next_id)) (.DW_TAG_compile_unit cp)
  let cp := add_children cp (types ++ defs)
  let string_table := (← getGen).string_table.fold (fun s i acc => (ref i, s) :: acc) []
  return .Gnu { string_table := string_table, range_table := accu.ranges.2,
                gnu_locs := accu.locs, gnu_entry := cp, several_secs := sec.length > 1 }

/-- Run a `GM` computation on the state of the debug hooks held in
    `ref` (the state `GenSt` of this module persists in `gref`). -/
def runIO {α : Type} (ref : IO.Ref Full) (gref : IO.Ref GenSt) (cfg : GenConfig) (x : GM α) : IO α := do
  match (x cfg).run { gen := ← gref.get, full := ← ref.get } with
  | .ok a s => ref.set s.full; gref.set s.gen; return a
  | .error e s => ref.set s.full; gref.set s.gen; throw (IO.userError s!"Dwarfgen: {repr e}")

end Dwarfgen
end CC
