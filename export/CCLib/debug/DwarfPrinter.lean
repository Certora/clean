/-
  Port of `debug/DwarfPrinter.ml`: printer for the DWARF 2/3 debug
  information in assembly.

  The OCaml functor `DwarfPrinter(Target : DWARF_TARGET)` becomes functions
  parameterised by a `DwarfPrinter.Config`, which holds the target functions
  (`DwarfTypes.DwarfTarget`) and the global settings the OCaml code reads
  (`Clflags.option_S || option_dasm`, `Clflags.option_gdwarf`,
  `Machine.config.sizeof_ptr`).

  The module-level references and hash tables of the functor
  (`abbrev_mapping`, `range_labels`, `entry_labels`, `loc_labels`,
  `abbrev_start_addr`, …) are the record `DwarfPrinter.St`, threaded
  through the state monad `DwarfPrinter.DM` on top of the assembly printing
  monad `PrintAsmaux.M` (which provides the output and `new_label`).
  `Hashtbl.add` followed by `Hashtbl.find` returns the most recent binding;
  the association lists below are searched from the most recent entry.
  `Hashtbl.find` on a missing key (`Not_found`) is a failure of the monad.

  Formats: `%X` prints OCaml's (63-bit, two's complement) `int` in upper
  case hexadecimal; the legacy format `%l` prints its argument as an
  unsigned decimal.
-/
import CCLib.debug.DwarfUtil
import CCLib.backend.PrintAsmaux

namespace CC
namespace DwarfPrinter

open DwarfTypes DwarfUtil Sections PrintAsmaux

/-- The parameters of the functor and the global settings it reads. -/
structure Config where
  target : DwarfTarget
  /-- `include_comment = !Clflags.option_S || !Clflags.option_dasm` -/
  include_comment : Bool := false
  /-- `!Clflags.option_gdwarf` -/
  gdwarf : Nat := 3
  /-- `!Machine.config.Machine.sizeof_ptr` -/
  sizeof_ptr : Nat := 8

/-- The state of the functor (its module-level references and tables). -/
structure St where
  abbrev_start_addr : Int := -1
  curr_abbrev : Nat := 1
  /-- `abbrev_mapping`, most recent first -/
  abbrev_mapping : List (String × Nat) := []
  /-- `range_labels`, most recent first -/
  range_labels : List (Int × Nat) := []
  debug_start_addr : Int := -1
  debug_stmt_list : Int := -1
  debug_ranges_addr : Int := -1
  /-- `entry_labels`, most recent first -/
  entry_labels : List (Nat × Nat) := []
  /-- `loc_labels`, most recent first -/
  loc_labels : List (Nat × Nat) := []

/-- The printing monad of the functor. -/
abbrev DM := ReaderT Config (StateT St PrintAsmaux.M)

/-- `output_string oc s` -/
def emit (s : String) : DM Unit := (PrintAsmaux.out s : PrintAsmaux.M Unit)

/-- `new_label ()` -/
def new_label : DM Nat := (PrintAsmaux.newLabel : PrintAsmaux.M Nat)

/-- Upper-case hexadecimal (`%X`) of an OCaml `int`. -/
def hexUpper (v : Int) : String :=
  String.ofList ((Nat.toDigits 16 (ocamlUnsigned v)).map Char.toUpper)

/-- `label lbl` (labels are non-negative; `-1` means "not yet set"). -/
def lbl (n : Int) : DM String := do
  return (← read).target.label n.toNat

/-- Do we need verbose debug information? -/
def print_comment (s : String) : DM String := do
  let cfg ← read
  return if cfg.include_comment && s != "" then s!"\t{cfg.target.comment} {s}" else ""

/-- `string_of_comment` -/
def string_of_comment (cfg : Config) (s : String) : String :=
  if cfg.include_comment then " " ++ cfg.target.comment ++ " " ++ s else ""

/-- `string_of_byte`: byte value to string. -/
def string_of_byte (cfg : Config) (value : Bool) (ct : String) : String :=
  s!"\t.byte\t\t{if value then "0x1" else "0x0"}{string_of_comment cfg ct}\n"

/-- `print_label` -/
def print_label (l : Int) : DM Unit := do emit s!"{← lbl l}:\n"

/-- `section oc sec` (`section` is a Lean keyword) -/
def printSection (sec : SectionName) : DM Unit := do emit ((← read).target.printSec sec)

/-! ## Abbreviations -/

section Abbrev
variable (cfg : Config)

/-- `add_abbr_uleb` -/
def add_abbr_uleb (v : Nat) (ct : String) : String :=
  s!"\t.uleb128\t{v}{string_of_comment cfg ct}\n"

/-- `add_abbr_entry` -/
def add_abbr_entry (v1 : Nat) (c1 : String) (f : DwForm) : String :=
  let (v2, c2) := code_of_dw_form f
  add_abbr_uleb cfg v1 c1 ++ s!"\t.uleb128\t{v2}{string_of_comment cfg c2}\n"

def add_file_loc : String :=
  add_abbr_entry cfg 0x3a "DW_AT_decl_file" .DW_FORM_data4 ++
  add_abbr_entry cfg 0x3b "DW_AT_decl_line" .DW_FORM_udata

def add_type : String := add_abbr_entry cfg 0x49 "DW_AT_type" .DW_FORM_ref_addr
def add_byte_size : String := add_abbr_entry cfg 0x0b "DW_AT_byte_size" .DW_FORM_data1
def add_member_size : String := add_abbr_entry cfg 0x0b "DW_AT_byte_size" .DW_FORM_udata
def add_low_pc : String := add_abbr_entry cfg 0x11 "DW_AT_low_pc" .DW_FORM_addr
def add_declaration : String := add_abbr_entry cfg 0x3c "DW_AT_declaration" .DW_FORM_flag

def add_string (id : Nat) (c : String) : StringConst → String
  | .Simple_string _ => add_abbr_entry cfg id c .DW_FORM_string
  | .Offset_string _ _ => add_abbr_entry cfg id c .DW_FORM_strp

def add_name : StringConst → String := add_string cfg 0x3 "DW_AT_name"

def add_name_opt : Option StringConst → String
  | none => ""
  | some s => add_name cfg s

def add_location : Option LocationValue → String
  | none => ""
  | some (.LocRef _) => add_abbr_entry cfg 0x2 "DW_AT_location" .DW_FORM_data4
  | some _ => add_abbr_entry cfg 0x2 "DW_AT_location" .DW_FORM_block

def add_range : DwRange → String
  | .Pc_pair _ _ =>
    add_abbr_entry cfg 0x11 "DW_AT_low_pc" .DW_FORM_addr ++
    add_abbr_entry cfg 0x12 "DW_AT_high_pc" .DW_FORM_addr
  | .Offset _ => add_abbr_entry cfg 0x55 "DW_AT_ranges" .DW_FORM_data4
  | .Empty => ""

/-- `add_attr_some` -/
def add_attr_some {α : Type} (v : Option α) (s : String) : String :=
  if v.isSome then s else ""

/-- `abbrev_string_of_entity`: DWARF entity to (abbreviation) string. -/
def abbrev_string_of_entity (entity : DwEntry) (has_sibling : Bool) : String :=
  let prologue (id : Nat) (c : String) : String :=
    let has_child := !entity.children.isEmpty
    add_abbr_uleb cfg id c ++
    string_of_byte cfg has_child (if has_child then "DW_CHILDREN_yes" else "DW_CHILDREN_no") ++
    (if has_sibling then add_abbr_entry cfg 0x1 "DW_AT_sibling" .DW_FORM_ref4 else "")
  match entity.tag with
  | .DW_TAG_array_type _ => prologue 0x1 "DW_TAG_array_type" ++ add_type cfg
  | .DW_TAG_base_type b =>
    prologue 0x24 "DW_TAG_base_type" ++ add_byte_size cfg ++
    add_attr_some b.base_type_encoding (add_abbr_entry cfg 0x3e "DW_AT_encoding" .DW_FORM_data1) ++
    add_name cfg b.base_type_name
  | .DW_TAG_compile_unit e =>
    prologue 0x11 "DW_TAG_compile_unit" ++
    add_string cfg 0x1b "DW_AT_comp_dir" e.compile_unit_dir ++
    add_range cfg e.compile_unit_range ++
    add_abbr_entry cfg 0x13 "DW_AT_language" .DW_FORM_udata ++
    add_name cfg e.compile_unit_name ++
    add_string cfg 0x25 "DW_AT_producer" e.compile_unit_prod_name ++
    add_abbr_entry cfg 0x10 "DW_AT_stmt_list" .DW_FORM_data4
  | .DW_TAG_const_type _ => prologue 0x26 "DW_TAG_const_type" ++ add_type cfg
  | .DW_TAG_enumeration_type e =>
    prologue 0x4 "DW_TAG_enumeration_type" ++
    add_attr_some e.enumeration_file_loc (add_file_loc cfg) ++
    add_byte_size cfg ++
    add_attr_some e.enumeration_declaration (add_declaration cfg) ++
    add_name cfg e.enumeration_name
  | .DW_TAG_enumerator e =>
    prologue 0x28 "DW_TAG_enumerator" ++
    add_abbr_entry cfg 0x1c "DW_AT_const_value" .DW_FORM_sdata ++
    add_name cfg e.enumerator_name
  | .DW_TAG_formal_parameter e =>
    prologue 0x5 "DW_TAG_formal_parameter" ++
    add_attr_some e.formal_parameter_artificial (add_abbr_entry cfg 0x34 "DW_AT_artificial" .DW_FORM_flag) ++
    add_name_opt cfg e.formal_parameter_name ++
    add_type cfg ++
    add_attr_some e.formal_parameter_variable_parameter
      (add_abbr_entry cfg 0x4b "DW_AT_variable_parameter" .DW_FORM_flag) ++
    add_location cfg e.formal_parameter_location
  | .DW_TAG_label e =>
    prologue 0xa "DW_TAG_label" ++ add_low_pc cfg ++ add_name cfg e.label_name
  | .DW_TAG_lexical_block a =>
    prologue 0xb "DW_TAG_lexical_block" ++ add_range cfg a.lexical_block_range
  | .DW_TAG_member e =>
    prologue 0xd "DW_TAG_member" ++
    add_attr_some e.member_byte_size (add_byte_size cfg) ++
    add_attr_some e.member_bit_offset (add_abbr_entry cfg 0xc "DW_AT_bit_offset" .DW_FORM_data1) ++
    add_attr_some e.member_bit_size (add_abbr_entry cfg 0xd "DW_AT_bit_size" .DW_FORM_data1) ++
    add_attr_some e.member_declaration (add_declaration cfg) ++
    add_name_opt cfg e.member_name ++
    add_type cfg ++
    (match e.member_data_member_location with
     | none => ""
     | some (.DataLocBlock _) => add_abbr_entry cfg 0x38 "DW_AT_data_member_location" .DW_FORM_block
     | some (.DataLocRef _) => add_abbr_entry cfg 0x38 "DW_AT_data_member_location" .DW_FORM_ref4)
  | .DW_TAG_pointer_type _ => prologue 0xf "DW_TAG_pointer_type" ++ add_type cfg
  | .DW_TAG_structure_type e =>
    prologue 0x13 "DW_TAG_structure_type" ++
    add_attr_some e.structure_file_loc (add_file_loc cfg) ++
    add_attr_some e.structure_byte_size (add_member_size cfg) ++
    add_attr_some e.structure_declaration (add_declaration cfg) ++
    add_name_opt cfg e.structure_name
  | .DW_TAG_subprogram e =>
    prologue 0x2e "DW_TAG_subprogram" ++
    add_file_loc cfg ++
    add_attr_some e.subprogram_external (add_abbr_entry cfg 0x3f "DW_AT_external" .DW_FORM_flag) ++
    add_range cfg e.subprogram_range ++
    add_name cfg e.subprogram_name ++
    add_abbr_entry cfg 0x27 "DW_AT_prototyped" .DW_FORM_flag ++
    add_attr_some e.subprogram_type (add_type cfg)
  | .DW_TAG_subrange_type e =>
    prologue 0x21 "DW_TAG_subrange_type" ++
    add_type cfg ++
    (match e.subrange_upper_bound with
     | none => ""
     | some (.BoundConst _) => add_abbr_entry cfg 0x2f "DW_AT_upper_bound" .DW_FORM_udata
     | some (.BoundRef _) => add_abbr_entry cfg 0x2f "DW_AT_upper_bound" .DW_FORM_ref4)
  | .DW_TAG_subroutine_type e =>
    prologue 0x15 "DW_TAG_subroutine_type" ++
    add_attr_some e.subroutine_type (add_type cfg) ++
    add_abbr_entry cfg 0x27 "DW_AT_prototyped" .DW_FORM_flag
  | .DW_TAG_typedef e =>
    prologue 0x16 "DW_TAG_typedef" ++
    add_attr_some e.typedef_file_loc (add_file_loc cfg) ++
    add_name cfg e.typedef_name ++
    add_type cfg
  | .DW_TAG_union_type e =>
    prologue 0x17 "DW_TAG_union_type" ++
    add_attr_some e.union_file_loc (add_file_loc cfg) ++
    add_attr_some e.union_byte_size (add_member_size cfg) ++
    add_attr_some e.union_declaration (add_declaration cfg) ++
    add_name_opt cfg e.union_name
  | .DW_TAG_unspecified_parameter e =>
    prologue 0x18 "DW_TAG_unspecified_parameter" ++
    add_attr_some e.unspecified_parameter_artificial
      (add_abbr_entry cfg 0x34 "DW_AT_artificial" .DW_FORM_flag)
  | .DW_TAG_variable e =>
    prologue 0x34 "DW_TAG_variable" ++
    add_file_loc cfg ++
    add_attr_some e.variable_declaration (add_declaration cfg) ++
    add_attr_some e.variable_external (add_abbr_entry cfg 0x3f "DW_AT_external" .DW_FORM_flag) ++
    add_location cfg e.variable_location ++
    add_name cfg e.variable_name ++
    add_type cfg
  | .DW_TAG_volatile_type _ => prologue 0x35 "DW_TAG_volatile_type" ++ add_type cfg

end Abbrev

/-- `next_abbrev`: unique abbreviation ids. -/
def next_abbrev : DM Nat := do
  let st ← get
  set { st with curr_abbrev := st.curr_abbrev + 1 }
  return st.curr_abbrev

/-- `get_abbrev`: look up the id of the abbreviation and add it if it is
    missing. -/
def get_abbrev (entity : DwEntry) (has_sibling : Bool) : DM Nat := do
  let s := abbrev_string_of_entity (← read) entity has_sibling
  match (← get).abbrev_mapping.lookup s with
  | some id => return id
  | none =>
    let id ← next_abbrev
    modify fun st => { st with abbrev_mapping := (s, id) :: st.abbrev_mapping }
    return id

/-- `compute_abbrev`: the abbreviations of an entry and its children. -/
def compute_abbrev (entry : DwEntry) : DM Unit :=
  entry_iter_sib (fun sib e => do let _ ← get_abbrev e sib.isSome) (fun _ => pure ()) entry

/-- `print_abbrev`: the `debug_abbrev` section. -/
def print_abbrev : DM Unit := do
  let abbrevs := (← get).abbrev_mapping.mergeSort (fun a b => a.2 ≤ b.2)
  printSection .Section_debug_abbrev
  print_label (← get).abbrev_start_addr
  for (s, id) in abbrevs do
    emit s!"\t.uleb128\t{id}{← print_comment "Abbreviation Code"}\n"
    emit s
    emit s!"\t.uleb128\t0{← print_comment "EOM(1)"}\n"
    emit s!"\t.uleb128\t0{← print_comment "EOM(2)"}\n"
  emit s!"\t.sleb128\t0{← print_comment "EOM(3)"}\n"

/-- `entry_to_label`: translate the ids to address labels. -/
def entry_to_label (id : Nat) : DM Nat := do
  match (← get).entry_labels.lookup id with
  | some l => return l
  | none =>
    let l ← new_label
    modify fun st => { st with entry_labels := (id, l) :: st.entry_labels }
    return l

/-- `loc_to_label` -/
def loc_to_label (id : Nat) : DM Nat := do
  match (← get).loc_labels.lookup id with
  | some l => return l
  | none =>
    let l ← new_label
    modify fun st => { st with loc_labels := (id, l) :: st.loc_labels }
    return l

/-! ## Helper functions for debug printing -/

def print_loc_ref (c : String) (r : Nat) : DM Unit := do
  let ref ← loc_to_label r
  emit s!"\t.4byte\t\t{← lbl ref}{← print_comment c}\n"

def print_opt_value {α : Type} (c : String) (o : Option α) (f : String → α → DM Unit) : DM Unit :=
  match o with
  | none => pure ()
  | some o => f c o

def print_flag (c : String) (b : Bool) : DM Unit := do emit (string_of_byte (← read) b c)

def print_string (c : String) : StringConst → DM Unit
  | .Simple_string s => do emit s!"\t.asciz\t\t{quoteString s}{← print_comment c}\n"
  | .Offset_string o s => print_loc_ref s!"{c} {quoteString s}" o

def print_uleb128 (c : String) (d : Int) : DM Unit := do
  emit s!"\t.uleb128\t{d}{← print_comment c}\n"

def print_sleb128 (c : String) (d : Int) : DM Unit := do
  emit s!"\t.sleb128\t{d}{← print_comment c}\n"

def print_byte (c : String) (b : Int) : DM Unit := do
  emit s!"\t.byte\t\t0x{hexUpper b}{← print_comment c}\n"

def print_2byte (c : String) (b : Int) : DM Unit := do
  emit s!"\t.2byte\t\t0x{hexUpper b}{← print_comment c}\n"

def print_ref (c : String) (r : Nat) : DM Unit := do
  let ref ← entry_to_label r
  emit s!"\t.4byte\t\t{← lbl ref}{← print_comment c}\n"

def print_file_loc : Option FileLoc → DM Unit
  | some (.Diab_file_loc file col) => do
    emit s!"\t.4byte\t\t{← lbl file}{← print_comment "DW_AT_decl_file"}\n"
    print_uleb128 "DW_AT_decl_line" col
  | some (.Gnu_file_loc file col) => do
    emit s!"\t.4byte\t\t{ocamlUnsigned file}{← print_comment "DW_AT_decl_file"}\n"
    print_uleb128 "DW_AT_decl_line" col
  | none => pure ()

def print_loc_expr : LocationExpression → DM Unit
  | .DW_OP_bregx a b => do
    print_byte "DW_OP_bregx" dw_op_bregx
    print_uleb128 "Register number" a
    print_sleb128 "Offset" b
  | .DW_OP_plus_uconst i => do
    print_byte "DW_OP_plus_uconst" dw_op_plus_uconst
    print_uleb128 "Constant" i
  | .DW_OP_piece i => do
    print_byte "DW_op_piece" dw_op_piece
    print_uleb128 "Piece" i
  | .DW_OP_reg i =>
    if i < 32 then print_byte "DW_op_reg" (dw_op_reg0 + i)
    else do
      print_byte "DW_op_regx" dw_op_regx
      print_uleb128 "Register number" i

def print_loc (c : String) : LocationValue → DM Unit
  | .LocSymbol s => do
    let cfg ← read
    print_sleb128 c (1 + cfg.sizeof_ptr)
    print_byte "" dw_op_addr
    emit s!"\t{cfg.target.address}\t\t{cfg.target.symbol s}\n"
  | .LocSimple e => do
    print_sleb128 c (size_of_loc_expr e)
    print_loc_expr e
  | .LocList e => do
    let size := e.foldl (fun acc a => acc + size_of_loc_expr a) 0
    print_sleb128 "" size
    e.forM print_loc_expr
  | .LocRef f => print_loc_ref c f

def print_list_loc : LocationValue → DM Unit
  | .LocSymbol s => do
    let cfg ← read
    print_2byte "" (1 + cfg.sizeof_ptr)
    print_byte "" dw_op_addr
    emit s!"\t{cfg.target.address}\t\t{cfg.target.symbol s}\n"
  | .LocSimple e => do
    print_2byte "" (size_of_loc_expr e)
    print_loc_expr e
  | .LocList e => do
    let size := e.foldl (fun acc a => acc + size_of_loc_expr a) 0
    print_2byte "" size
    e.forM print_loc_expr
  | .LocRef f => print_loc_ref "" f

def print_data_location (c : String) : DataLocationValue → DM Unit
  | .DataLocBlock e => do
    print_sleb128 c (size_of_loc_expr e)
    print_loc_expr e
  | _ => pure ()

def print_addr (c : String) (a : Int) : DM Unit := do
  emit s!"\t{(← read).target.address}\t\t{← lbl a}{← print_comment c}\n"

def print_data4_addr (c : String) (a : Int) : DM Unit := do
  emit s!"\t.4byte\t{← lbl a}{← print_comment c}\n"

def print_array_type (arr : DwTagArrayType) : DM Unit := print_ref "DW_AT_type" arr.array_type

def print_bound_value (c : String) : BoundValue → DM Unit
  | .BoundConst bc => print_uleb128 c bc
  | .BoundRef br => print_ref c br

def print_base_type (bt : DwTagBaseType) : DM Unit := do
  print_byte "DW_AT_byte_size" bt.base_type_byte_size
  match bt.base_type_encoding with
  | some e =>
    let encoding : Int := match e with
      | .DW_ATE_address => 0x1
      | .DW_ATE_boolean => 0x2
      | .DW_ATE_complex_float => 0x3
      | .DW_ATE_float => 0x4
      | .DW_ATE_signed => 0x5
      | .DW_ATE_signed_char => 0x6
      | .DW_ATE_unsigned => 0x7
      | .DW_ATE_unsigned_char => 0x8
    print_byte "DW_AT_encoding" encoding
  | none => pure ()
  print_string "DW_AT_name" bt.base_type_name

def print_range : DwRange → DM Unit
  | .Pc_pair l h => do
    print_addr "DW_AT_low_pc" l
    print_addr "DW_AT_high_pc" h
  | .Offset i => do
    let l ← new_label
    modify fun st => { st with range_labels := (i, l) :: st.range_labels }
    emit s!"\t.4byte\t\t{← lbl l}{← print_comment "DW_AT_ranges"}\n"
  | _ => pure ()

def print_compilation_unit (tag : DwTagCompileUnit) : DM Unit := do
  print_string "DW_AT_comp_dir" tag.compile_unit_dir
  print_range tag.compile_unit_range
  print_uleb128 "DW_AT_language" 1
  print_string "DW_AT_name" tag.compile_unit_name
  print_string "DW_AT_producer" tag.compile_unit_prod_name
  print_data4_addr "DW_AT_stmt_list" (← get).debug_stmt_list

def print_const_type (ct : DwTagConstType) : DM Unit := print_ref "DW_AT_type" ct.const_type

def print_enumeration_type (et : DwTagEnumerationType) : DM Unit := do
  print_file_loc et.enumeration_file_loc
  print_uleb128 "DW_AT_byte_size" et.enumeration_byte_size
  print_opt_value "DW_AT_declaration" et.enumeration_declaration print_flag
  print_string "DW_AT_name" et.enumeration_name

def print_enumerator (en : DwTagEnumerator) : DM Unit := do
  print_sleb128 "DW_AT_const_value" en.enumerator_value
  print_string "DW_AT_name" en.enumerator_name

def print_formal_parameter (fp : DwTagFormalParameter) : DM Unit := do
  print_opt_value "DW_AT_artificial" fp.formal_parameter_artificial print_flag
  print_opt_value "DW_AT_name" fp.formal_parameter_name print_string
  print_ref "DW_AT_type" fp.formal_parameter_type
  print_opt_value "DW_AT_variable_parameter" fp.formal_parameter_variable_parameter print_flag
  print_opt_value "DW_AT_location" fp.formal_parameter_location print_loc

def print_tag_label (tl : DwTagLabel) : DM Unit := do
  print_ref "DW_AT_low_pc" tl.label_low_pc
  print_string "DW_AT_name" tl.label_name

def print_lexical_block (lb : DwTagLexicalBlock) : DM Unit := print_range lb.lexical_block_range

def print_member (mb : DwTagMember) : DM Unit := do
  print_opt_value "DW_AT_byte_size" mb.member_byte_size print_byte
  print_opt_value "DW_AT_bit_offset" mb.member_bit_offset print_byte
  print_opt_value "DW_AT_bit_size" mb.member_bit_size print_byte
  print_opt_value "DW_AT_declaration" mb.member_declaration print_flag
  print_opt_value "DW_AT_name" mb.member_name print_string
  print_ref "DW_AT_type" mb.member_type
  print_opt_value "DW_AT_data_member_location" mb.member_data_member_location print_data_location

def print_pointer (pt : DwTagPointerType) : DM Unit := print_ref "DW_AT_type" pt.pointer_type

def print_structure (st : DwTagStructureType) : DM Unit := do
  print_file_loc st.structure_file_loc
  print_opt_value "DW_AT_byte_size" st.structure_byte_size print_uleb128
  print_opt_value "DW_AT_declaration" st.structure_declaration print_flag
  print_opt_value "DW_AT_name" st.structure_name print_string

def print_subprogram (sp : DwTagSubprogram) : DM Unit := do
  print_file_loc (some sp.subprogram_file_loc)
  print_opt_value "DW_AT_external" sp.subprogram_external print_flag
  print_range sp.subprogram_range
  print_string "DW_AT_name" sp.subprogram_name
  print_flag "DW_AT_prototyped" sp.subprogram_prototyped
  print_opt_value "DW_AT_type" sp.subprogram_type print_ref

def print_subrange (sr : DwTagSubrangeType) : DM Unit := do
  print_ref "DW_AT_type" sr.subrange_type
  print_opt_value "DW_AT_upper_bound" sr.subrange_upper_bound print_bound_value

def print_subroutine (st : DwTagSubroutineType) : DM Unit := do
  print_opt_value "DW_AT_type" st.subroutine_type print_ref
  print_flag "DW_AT_prototyped" st.subroutine_prototyped

def print_typedef (td : DwTagTypedef) : DM Unit := do
  print_file_loc td.typedef_file_loc
  print_string "DW_AT_name" td.typedef_name
  print_ref "DW_AT_type" td.typedef_type

def print_union_type (ut : DwTagUnionType) : DM Unit := do
  print_file_loc ut.union_file_loc
  print_opt_value "DW_AT_byte_size" ut.union_byte_size print_uleb128
  print_opt_value "DW_AT_declaration" ut.union_declaration print_flag
  print_opt_value "DW_AT_name" ut.union_name print_string

def print_unspecified_parameter (up : DwTagUnspecifiedParameter) : DM Unit :=
  print_opt_value "DW_AT_artificial" up.unspecified_parameter_artificial print_flag

def print_variable (var : DwTagVariable) : DM Unit := do
  print_file_loc (some var.variable_file_loc)
  print_opt_value "DW_AT_declaration" var.variable_declaration print_flag
  print_opt_value "DW_AT_external" var.variable_external print_flag
  print_opt_value "DW_AT_location" var.variable_location print_loc
  print_string "DW_AT_name" var.variable_name
  print_ref "DW_AT_type" var.variable_type

def print_volatile_type (vt : DwTagVolatileType) : DM Unit := print_ref "DW_AT_type" vt.volatile_type

/-- `print_entry`: print a debug entry. -/
def print_entry (entry : DwEntry) : DM Unit :=
  entry_iter_sib
    (fun sib entry => do
      print_label (← entry_to_label entry.id)
      let id ← get_abbrev entry sib.isSome
      print_sleb128 s!"Abbrev [{id}] {string_of_dw_tag entry.tag}" id
      match sib with
      | none => pure ()
      | some s =>
        let l ← entry_to_label s
        emit s!"\t.4byte\t\t{← lbl l}-{← lbl (← get).debug_start_addr}{← print_comment "DW_AT_sibling"}\n"
      match entry.tag with
      | .DW_TAG_array_type arr_type => print_array_type arr_type
      | .DW_TAG_compile_unit comp => print_compilation_unit comp
      | .DW_TAG_base_type bt => print_base_type bt
      | .DW_TAG_const_type ct => print_const_type ct
      | .DW_TAG_enumeration_type et => print_enumeration_type et
      | .DW_TAG_enumerator et => print_enumerator et
      | .DW_TAG_formal_parameter fp => print_formal_parameter fp
      | .DW_TAG_label lb => print_tag_label lb
      | .DW_TAG_lexical_block lb => print_lexical_block lb
      | .DW_TAG_member mb => print_member mb
      | .DW_TAG_pointer_type pt => print_pointer pt
      | .DW_TAG_structure_type st => print_structure st
      | .DW_TAG_subprogram sb => print_subprogram sb
      | .DW_TAG_subrange_type sb => print_subrange sb
      | .DW_TAG_subroutine_type st => print_subroutine st
      | .DW_TAG_typedef tp => print_typedef tp
      | .DW_TAG_union_type ut => print_union_type ut
      | .DW_TAG_unspecified_parameter up => print_unspecified_parameter up
      | .DW_TAG_variable var => print_variable var
      | .DW_TAG_volatile_type vt => print_volatile_type vt)
    (fun e => if !e.children.isEmpty then print_sleb128 "End Of Children Mark" 0 else pure ())
    entry

/-- `print_debug_info`: the debug info section. -/
def print_debug_info (start line_start : Nat) (entry : DwEntry) : DM Unit := do
  modify fun st => { st with entry_labels := [], debug_start_addr := start,
                             debug_stmt_list := line_start }
  print_label start
  -- address used for length calculation
  let debug_length_start ← new_label
  let debug_end ← new_label
  emit s!"\t.4byte\t\t{← lbl debug_end}-{← lbl debug_length_start}{← print_comment "Length of Unit"}\n"
  print_label debug_length_start
  let cfg ← read
  emit s!"\t.2byte\t\t0x{cfg.gdwarf}{← print_comment "DWARF version number"}\n"
  print_data4_addr "Offset Into Abbrev. Section" (← get).abbrev_start_addr
  print_byte "Address Size (in bytes)" cfg.sizeof_ptr
  print_entry entry
  print_sleb128 "" 0
  print_label debug_end

/-- `print_location_entry` -/
def print_location_entry (needs_base : Bool) (c_low : Nat) (l : LocationEntry) : DM Unit := do
  print_label (← loc_to_label l.loc_id)
  let address := (← read).target.address
  -- with multiple ranges per compilation unit, the location needs a base
  -- address
  if needs_base then
    emit s!"\t{address}\t\t-1\n"
    emit s!"\t{address}\t\t{← lbl c_low}\n"
  for (b, e, loc) in l.loc do
    emit s!"\t{address}\t\t{← lbl b}-{← lbl c_low}\n"
    emit s!"\t{address}\t\t{← lbl e}-{← lbl c_low}\n"
    print_list_loc loc
  emit s!"\t{address}\t0\n"
  emit s!"\t{address}\t0\n"

/-- `print_location_entry_abs` -/
def print_location_entry_abs (l : LocationEntry) : DM Unit := do
  print_label (← loc_to_label l.loc_id)
  let address := (← read).target.address
  for (b, e, loc) in l.loc do
    emit s!"\t{address}\t\t{← lbl b}\n"
    emit s!"\t{address}\t\t{← lbl e}\n"
    print_list_loc loc
  emit s!"\t{address}\t0\n"
  emit s!"\t{address}\t0\n"

/-- `print_location_list` -/
def print_location_list (needs_base : Bool) (l : DwLocations) : DM Unit :=
  l.forM fun l => match l.loc_sec_begin with
    | some s => print_location_entry needs_base s l
    | none => print_location_entry_abs l

/-- `print_diab_entries` -/
def print_diab_entries (entries : DiabEntries) : DM Unit := do
  let abbrev_start ← new_label
  modify fun st => { st with abbrev_start_addr := abbrev_start }
  entries.forM fun e => compute_abbrev e.diab_entry
  print_abbrev
  entries.forM fun e => do
    let name := if e.section_name != ".text" then some e.section_name else none
    printSection (.Section_debug_info name)
    print_debug_info e.start_label e.line_label e.diab_entry
  if entries.any (fun e => !e.diab_locs.isEmpty) then
    printSection .Section_debug_loc
    entries.forM fun e => print_location_list false e.diab_locs

/-- `print_ranges` -/
def print_ranges (r : DwRanges) : DM Unit := do
  let address := (← read).target.address
  let print_range_entry : RangeEntry → DM Unit
    | .AddressRange l => l.forM fun (b, e) => do
        emit s!"\t{address}\t\t{← lbl b}\n"
        emit s!"\t{address}\t\t{← lbl e}\n"
    | .OffsetRange start l => l.forM fun (b, e) => do
        emit s!"\t{address}\t\t{← lbl b}-{← lbl start}\n"
        emit s!"\t{address}\t\t{← lbl e}-{← lbl start}\n"
  printSection .Section_debug_ranges
  print_label (← get).debug_ranges_addr
  for (l, e) in r do
    match (← get).range_labels.lookup l with
    | some rl => print_label rl
    | none => throw "DwarfPrinter.print_ranges: Not_found"
    print_range_entry e
    emit s!"\t{address}\t0\n"
    emit s!"\t{address}\t0\n"

/-- `print_gnu_entries` -/
def print_gnu_entries (entries : GnuEntries) : DM Unit := do
  compute_abbrev entries.gnu_entry
  let line_start ← new_label
  let start ← new_label
  let abbrev_start ← new_label
  let range_label ← new_label
  modify fun st => { st with debug_ranges_addr := range_label, abbrev_start_addr := abbrev_start }
  printSection (.Section_debug_info none)
  print_debug_info start line_start entries.gnu_entry
  print_abbrev
  if !entries.gnu_locs.isEmpty then
    printSection .Section_debug_loc
    print_location_list entries.several_secs entries.gnu_locs
  if !entries.range_table.isEmpty then
    print_ranges entries.range_table
  printSection (.Section_debug_line none)
  print_label line_start
  if !entries.string_table.isEmpty then
    printSection .Section_debug_str
    let s := entries.string_table.mergeSort (fun a b => a.1 ≤ b.1)
    for (id, str) in s do
      print_label (← loc_to_label id)
      emit s!"\t.asciz\t\t{quoteString str}\n"

/-- `print_debug`: print the debug info and abbreviation sections. -/
def print_debug (debug : DebugEntries) : DM Unit := do
  modify fun st => { st with abbrev_mapping := [], range_labels := [], loc_labels := [] }
  match debug with
  | .Diab entries => print_diab_entries entries
  | .Gnu entries => print_gnu_entries entries

/-- Run `print_debug` on a fresh functor state, inside the assembly
    printing monad. -/
def printDebug (cfg : Config) (debug : DebugEntries) : PrintAsmaux.M Unit := do
  let _ ← (print_debug debug).run cfg |>.run {}

end DwarfPrinter
end CC
