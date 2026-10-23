/-
  Port of `debug/DebugTypes.mli`: the types of the information collected
  by `DebugInformation` about types, global definitions and local
  variables.

  OCaml `int` becomes `Int` (type and variable ids, sizes, offsets) and
  `atom` / `positive` become `Ident` / `Positive`.
-/
import CCLib.common.ASTTheory
import CCLib.cparser.C

namespace CC
namespace DebugTypes

open CParser.C (Location StructOrUnion IKind FKind)

/-! ## Types for the information of type info -/

/-- `composite_field` -/
structure CompositeField where
  cfd_name : String
  cfd_atom : Option Ident
  cfd_anon : Bool
  cfd_typ : Int
  cfd_bit_size : Option Int
  cfd_bit_offset : Option Int
  cfd_byte_offset : Option Int
  cfd_byte_size : Option Int
  deriving Repr, Inhabited

/-- `composite_type` -/
structure CompositeType where
  ct_name : String
  ct_sou : StructOrUnion
  ct_file_loc : Option Location
  ct_members : List CompositeField
  ct_sizeof : Option Int
  ct_declaration : Bool
  deriving Repr, Inhabited

/-- `ptr_type` -/
structure PtrType where
  pts : Int
  deriving Repr, Inhabited

/-- `const_type` -/
structure ConstType where
  cst_type : Int
  deriving Repr, Inhabited

/-- `volatile_type` -/
structure VolatileType where
  vol_type : Int
  deriving Repr, Inhabited

/-- `array_type` -/
structure ArrayType where
  arr_type : Int
  arr_size : List (Option Int)
  deriving Repr, Inhabited

/-- `typedef` -/
structure Typedef where
  td_file_loc : Option Location
  td_name : String
  typ : Option Int
  deriving Repr, Inhabited

/-- `enumerator` -/
structure Enumerator where
  e_name : String
  e_const : Int
  deriving Repr, Inhabited

/-- `enum_type` -/
structure EnumType where
  enum_name : String
  enum_byte_size : Option Int
  enum_file_loc : Option Location
  enum_enumerators : List Enumerator
  deriving Repr, Inhabited

/-- `int_type` -/
structure IntType where
  int_kind : IKind
  deriving Repr, Inhabited

/-- `float_type` -/
structure FloatType where
  float_kind : FKind
  deriving Repr, Inhabited

/-- `parameter_type` -/
structure ParameterType where
  param_type : Int
  param_name : String
  deriving Repr, Inhabited

/-- `function_type` -/
structure FunctionType where
  fun_type_return_type : Option Int
  fun_type_prototyped : Bool
  fun_type_params : List ParameterType
  deriving Repr, Inhabited

/-- `debug_types` -/
inductive DebugTypes where
  | IntegerType (t : IntType)
  | FloatType (t : FloatType)
  | PointerType (t : PtrType)
  | ArrayType (t : ArrayType)
  | CompositeType (t : CompositeType)
  | EnumType (t : EnumType)
  | FunctionType (t : FunctionType)
  | Typedef (t : Typedef)
  | ConstType (t : ConstType)
  | VolatileType (t : VolatileType)
  | Void
  deriving Repr, Inhabited

/-! ## Types for global definitions -/

/-- `global_variable_information` -/
structure GlobalVariableInformation where
  gvar_name : String
  gvar_atom : Option Ident
  gvar_file_loc : Location
  gvar_declaration : Bool
  gvar_external : Bool
  gvar_type : Int
  deriving Repr, Inhabited

/-- `parameter_information` -/
structure ParameterInformation where
  parameter_name : String
  parameter_ident : Int
  parameter_atom : Option Ident
  parameter_type : Int
  deriving Repr, Inhabited

/-- `function_information` -/
structure FunctionInformation where
  fun_name : String
  fun_atom : Option Ident
  fun_file_loc : Location
  fun_external : Bool
  /-- `none` for `void` functions -/
  fun_return_type : Option Int
  fun_vararg : Bool
  fun_parameter : List ParameterInformation
  fun_low_pc : Option Int
  fun_high_pc : Option Int
  fun_scope : Option Int
  deriving Repr, Inhabited

/-- `definition_type` -/
inductive DefinitionType where
  | GlobalVariable (i : GlobalVariableInformation)
  | Function (i : FunctionInformation)
  deriving Repr, Inhabited

/-! ## Information for local variables -/

/-- `local_variable_information` -/
structure LocalVariableInformation where
  lvar_name : String
  lvar_atom : Option Ident
  lvar_file_loc : Location
  lvar_type : Int
  /-- static variables are mapped to symbols -/
  lvar_static : Bool
  deriving Repr, Inhabited

/-- `scope_information` -/
structure ScopeInformation where
  /-- variable and scope ids -/
  scope_variables : List Int
  deriving Repr, Inhabited

/-- `local_information` -/
inductive LocalInformation where
  | LocalVariable (i : LocalVariableInformation)
  | Scope (i : ScopeInformation)
  deriving Repr, Inhabited

/-- `scope_range` -/
structure ScopeRange where
  start_addr : Option Positive
  end_addr : Option Positive
  deriving Repr, Inhabited

/-- `var_range` -/
structure VarRange where
  range_start : Option Positive
  range_end : Option Positive
  var_loc : Int × BuiltinArg Int

/-- `var_location` -/
inductive VarLocation where
  | RangeLoc (l : List VarRange)
  /-- stack allocated variables -/
  | FunctionLoc (sz : Int) (a : BuiltinArg Int)

end DebugTypes
end CC
