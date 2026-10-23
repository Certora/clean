/-
  Port of `debug/DwarfTypes.mli`: the types used for writing DWARF debug
  information.

  OCaml records become Lean structures with the same field names; OCaml
  `int` becomes `Int` for constants (enumerator values may be negative) and
  `Nat` for references, addresses and labels (always non-negative in
  CompCert); `int32` becomes `Int`.

  The module type `DWARF_TARGET` (target-specific printing functions) is the
  structure `DwarfTarget`, whose functions return the printed text instead
  of writing to an output channel.
-/
import CCLib.common.Sections

namespace CC
namespace DwarfTypes

open Sections

/-! ## Basic types for the value of attributes -/

/-- `constant` -/
abbrev Constant := Int
/-- `flag` -/
abbrev Flag := Bool
/-- `reference` -/
abbrev Reference := Nat
/-- `address` -/
abbrev Address := Nat

/-- `encoding` -/
inductive Encoding where
  | DW_ATE_address
  | DW_ATE_boolean
  | DW_ATE_complex_float
  | DW_ATE_float
  | DW_ATE_signed
  | DW_ATE_signed_char
  | DW_ATE_unsigned
  | DW_ATE_unsigned_char
  deriving DecidableEq, Repr, Inhabited

/-- `location_expression` -/
inductive LocationExpression where
  | DW_OP_plus_uconst (c : Constant)
  | DW_OP_bregx (c : Constant) (ofs : Int)
  | DW_OP_piece (c : Constant)
  | DW_OP_reg (c : Constant)
  deriving DecidableEq, Repr, Inhabited

/-- `location_value` -/
inductive LocationValue where
  | LocSymbol (a : Ident)
  | LocRef (a : Address)
  | LocSimple (e : LocationExpression)
  | LocList (l : List LocationExpression)
  deriving DecidableEq, Repr, Inhabited

/-- `data_location_value` -/
inductive DataLocationValue where
  | DataLocBlock (e : LocationExpression)
  | DataLocRef (r : Reference)
  deriving DecidableEq, Repr, Inhabited

/-- `bound_value` -/
inductive BoundValue where
  | BoundConst (c : Constant)
  | BoundRef (r : Reference)
  deriving DecidableEq, Repr, Inhabited

/-- `string_const` -/
inductive StringConst where
  | Simple_string (s : String)
  | Offset_string (r : Reference) (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- `file_loc` -/
inductive FileLoc where
  | Diab_file_loc (file line : Constant)
  | Gnu_file_loc (file line : Constant)
  deriving DecidableEq, Repr, Inhabited

/-- `dw_form` -/
inductive DwForm where
  | DW_FORM_addr
  | DW_FORM_block2
  | DW_FORM_block4
  | DW_FORM_data2
  | DW_FORM_data4
  | DW_FORM_data8
  | DW_FORM_string
  | DW_FORM_block
  | DW_FORM_block1
  | DW_FORM_data1
  | DW_FORM_flag
  | DW_FORM_sdata
  | DW_FORM_strp
  | DW_FORM_udata
  | DW_FORM_ref_addr
  | DW_FORM_ref1
  | DW_FORM_ref2
  | DW_FORM_ref4
  | DW_FORM_ref8
  | DW_FORM_ref_udata
  | DW_FORM_ref_indirect
  deriving DecidableEq, Repr, Inhabited

/-- `dw_range` -/
inductive DwRange where
  /-- simple low, high pc -/
  | Pc_pair (lo hi : Reference)
  /-- DWARF 3 version for different range -/
  | Offset (c : Constant)
  /-- needed for compilation units only containing variables -/
  | Empty
  deriving DecidableEq, Repr, Inhabited

/-! ## Attribute information per tag value -/

/-- `dw_tag_array_type` -/
structure DwTagArrayType where
  array_type : Reference
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_base_type` -/
structure DwTagBaseType where
  base_type_byte_size : Constant
  base_type_encoding : Option Encoding
  base_type_name : StringConst
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_compile_unit` -/
structure DwTagCompileUnit where
  compile_unit_name : StringConst
  compile_unit_range : DwRange
  compile_unit_dir : StringConst
  compile_unit_prod_name : StringConst
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_const_type` -/
structure DwTagConstType where
  const_type : Reference
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_enumeration_type` -/
structure DwTagEnumerationType where
  enumeration_file_loc : Option FileLoc
  enumeration_byte_size : Constant
  enumeration_declaration : Option Flag
  enumeration_name : StringConst
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_enumerator` -/
structure DwTagEnumerator where
  enumerator_value : Constant
  enumerator_name : StringConst
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_formal_parameter` -/
structure DwTagFormalParameter where
  formal_parameter_artificial : Option Flag
  formal_parameter_name : Option StringConst
  formal_parameter_type : Reference
  formal_parameter_variable_parameter : Option Flag
  formal_parameter_location : Option LocationValue
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_label` -/
structure DwTagLabel where
  label_low_pc : Address
  label_name : StringConst
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_lexical_block` -/
structure DwTagLexicalBlock where
  lexical_block_range : DwRange
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_member` -/
structure DwTagMember where
  member_byte_size : Option Constant
  member_bit_offset : Option Constant
  member_bit_size : Option Constant
  member_data_member_location : Option DataLocationValue
  member_declaration : Option Flag
  member_name : Option StringConst
  member_type : Reference
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_pointer_type` -/
structure DwTagPointerType where
  pointer_type : Reference
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_structure_type` -/
structure DwTagStructureType where
  structure_file_loc : Option FileLoc
  structure_byte_size : Option Constant
  structure_declaration : Option Flag
  structure_name : Option StringConst
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_subprogram` -/
structure DwTagSubprogram where
  subprogram_file_loc : FileLoc
  subprogram_external : Option Flag
  subprogram_name : StringConst
  subprogram_prototyped : Flag
  subprogram_type : Option Reference
  subprogram_range : DwRange
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_subrange_type` -/
structure DwTagSubrangeType where
  subrange_type : Reference
  subrange_upper_bound : Option BoundValue
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_subroutine_type` -/
structure DwTagSubroutineType where
  subroutine_type : Option Reference
  subroutine_prototyped : Flag
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_typedef` -/
structure DwTagTypedef where
  typedef_file_loc : Option FileLoc
  typedef_name : StringConst
  typedef_type : Reference
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_union_type` -/
structure DwTagUnionType where
  union_file_loc : Option FileLoc
  union_byte_size : Option Constant
  union_declaration : Option Flag
  union_name : Option StringConst
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_unspecified_parameter` -/
structure DwTagUnspecifiedParameter where
  unspecified_parameter_artificial : Option Flag
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_variable` -/
structure DwTagVariable where
  variable_file_loc : FileLoc
  variable_declaration : Option Flag
  variable_external : Option Flag
  variable_name : StringConst
  variable_type : Reference
  variable_location : Option LocationValue
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag_volatile_type` -/
structure DwTagVolatileType where
  volatile_type : Reference
  deriving DecidableEq, Repr, Inhabited

/-- `dw_tag` -/
inductive DwTag where
  | DW_TAG_array_type (t : DwTagArrayType)
  | DW_TAG_base_type (t : DwTagBaseType)
  | DW_TAG_compile_unit (t : DwTagCompileUnit)
  | DW_TAG_const_type (t : DwTagConstType)
  | DW_TAG_enumeration_type (t : DwTagEnumerationType)
  | DW_TAG_enumerator (t : DwTagEnumerator)
  | DW_TAG_formal_parameter (t : DwTagFormalParameter)
  | DW_TAG_label (t : DwTagLabel)
  | DW_TAG_lexical_block (t : DwTagLexicalBlock)
  | DW_TAG_member (t : DwTagMember)
  | DW_TAG_pointer_type (t : DwTagPointerType)
  | DW_TAG_structure_type (t : DwTagStructureType)
  | DW_TAG_subprogram (t : DwTagSubprogram)
  | DW_TAG_subrange_type (t : DwTagSubrangeType)
  | DW_TAG_subroutine_type (t : DwTagSubroutineType)
  | DW_TAG_typedef (t : DwTagTypedef)
  | DW_TAG_union_type (t : DwTagUnionType)
  | DW_TAG_unspecified_parameter (t : DwTagUnspecifiedParameter)
  | DW_TAG_variable (t : DwTagVariable)
  | DW_TAG_volatile_type (t : DwTagVolatileType)
  deriving DecidableEq, Repr, Inhabited

/-- `dw_entry`: the type of the entries. -/
structure DwEntry where
  tag : DwTag
  children : List DwEntry
  id : Reference
  deriving Repr, Inhabited

/-- `location_entry`: the type for the location list. -/
structure LocationEntry where
  loc : List (Address × Address × LocationValue)
  loc_id : Reference
  loc_sec_begin : Option Address
  deriving DecidableEq, Repr, Inhabited

/-- `dw_locations` -/
abbrev DwLocations := List LocationEntry

/-- `range_entry` -/
inductive RangeEntry where
  | AddressRange (l : List (Address × Address))
  | OffsetRange (r : Reference) (l : List (Address × Address))
  deriving DecidableEq, Repr, Inhabited

/-- `dw_ranges` -/
abbrev DwRanges := List (Int × RangeEntry)

/-- `dw_string` -/
abbrev DwString := List (Nat × String)

/-- `diab_entry` -/
structure DiabEntry where
  section_name : String
  start_label : Nat
  line_label : Nat
  diab_entry : DwEntry
  diab_locs : DwLocations
  deriving Repr, Inhabited

/-- `diab_entries` -/
abbrev DiabEntries := List DiabEntry

/-- `gnu_entries` -/
structure GnuEntries where
  string_table : DwString
  range_table : DwRanges
  gnu_locs : DwLocations
  gnu_entry : DwEntry
  several_secs : Bool
  deriving Repr, Inhabited

/-- `debug_entries` -/
inductive DebugEntries where
  | Diab (e : DiabEntries)
  | Gnu (e : GnuEntries)
  deriving Repr, Inhabited

/-- `module type DWARF_TARGET`: the target-specific functions for printing
    the debug information (they return the printed text). -/
structure DwarfTarget where
  label : Nat → String
  printSec : SectionName → String
  symbol : Ident → String
  comment : String
  address : String

end DwarfTypes
end CC
