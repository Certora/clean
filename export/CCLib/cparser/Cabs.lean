/-
  Port of `cparser/Cabs.v`: the abstract syntax of C produced by the parser
  (`cparser/Parser.vy`, `CCLib.cparser.Parser`) and consumed by the
  elaborator (`cparser/Elab.ml`, `CCLib.cparser.Elab`).

  Naming: the Rocq type names are turned into Lean type names by the rule of
  `export/tools/gen_parser.py` (`typeSpecifier` ↦ `TypeSpecifier`,
  `decl_type` ↦ `DeclType`, `init_name_group` ↦ `InitNameGroup`, …), which is
  what the generated parser refers to.  Constructor names are Rocq's.

  The three Rocq `Parameter`s are instantiated as in the OCaml extraction
  (`extraction/extraction.v` and `cparser/Cabs.ml`):
  * `string` is Lean's `String`;
  * `char_code` (OCaml `int64`) is `Int64`;
  * `loc` is the OCaml record `Cabs.loc = { lineno; filename; byteno; ident }`.
-/

namespace CC
namespace Cabs

/-- OCaml's `int64`, used for the individual characters of literals. -/
abbrev CharCode := Int64

/-- Context information (`cparser/Cabs.ml`, type `loc`). -/
structure Loc where
  lineno : Int
  filename : String
  byteno : Int
  ident : Int
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.floatInfo` -/
structure FloatInfo where
  isHex_FI : Bool
  integer_FI : Option String
  fraction_FI : Option String
  exponent_FI : Option String
  suffix_FI : Option String
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.encoding` -/
inductive Encoding where
  | EncNone   -- no prefix
  | EncWide   -- `L` prefix
  | EncU16    -- `u` prefix
  | EncU32    -- `U` prefix
  | EncUTF8   -- `u8` prefix (strings only)
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.structOrUnion` -/
inductive StructOrUnion where
  | STRUCT | UNION
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.storage` -/
inductive Storage where
  | AUTO | STATIC | EXTERN | REGISTER | TYPEDEF
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.funspec` -/
inductive Funspec where
  | INLINE | NORETURN
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.binary_operator` -/
inductive BinaryOperator where
  | ADD | SUB | MUL | DIV | MOD
  | AND | OR
  | BAND | BOR | XOR | SHL | SHR
  | EQ | NE | LT | GT | LE | GE
  | ASSIGN
  | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
  | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN
  | COMMA
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.unary_operator` -/
inductive UnaryOperator where
  | MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
  | PREINCR | PREDECR | POSINCR | POSDECR
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.gcc_attribute_word` -/
inductive GccAttributeWord where
  | GCC_ATTR_IDENT (s : String)
  | GCC_ATTR_CONST
  | GCC_ATTR_PACKED
  deriving Repr, Inhabited, BEq, DecidableEq

/-- `Cabs.constant`.  The string of `CONST_INT` is the textual representation
of the constant in the source code. -/
inductive Constant where
  | CONST_INT (s : String)
  | CONST_FLOAT (f : FloatInfo)
  | CONST_CHAR (enc : Encoding) (chars : List CharCode)
  | CONST_STRING (enc : Encoding) (chars : List CharCode)
  deriving Repr, Inhabited, BEq, DecidableEq

mutual

/-- `Cabs.typeSpecifier` (all specifiers merged into one type).  The struct,
union and enum specifiers contain a field or item list iff they are a
definition. -/
inductive TypeSpecifier where
  | Tvoid
  | Tchar
  | Tshort
  | Tint
  | Tlong
  | Tfloat
  | Tfloat16
  | Tdouble
  | Tsigned
  | Tunsigned
  | T_Bool
  | Tnamed (s : String)
  | Tstruct_union (su : StructOrUnion) (name : Option String)
      (fields : Option (List FieldGroup)) (attrs : List Attribute)
  | Tenum (name : Option String) (items : Option (List ((String × Option Expression) × Loc)))
      (attrs : List Attribute)

/-- `Cabs.cvspec` -/
inductive Cvspec where
  | CV_CONST | CV_VOLATILE | CV_RESTRICT
  | CV_ATTR (a : Attribute)

/-- `Cabs.spec_elem`: the elements of the "word soup" at the start of a
declaration. -/
inductive SpecElem where
  | SpecCV (cv : Cvspec)
  | SpecStorage (s : Storage)
  | SpecFunction (f : Funspec)
  | SpecType (t : TypeSpecifier)

/-- `Cabs.decl_type`: declarators, in the order in which they are printed. -/
inductive DeclType where
  | JUSTBASE
  /-- The `Bool` is `true` for `static` array declarators. -/
  | ARRAY (d : DeclType) (cv : List Cvspec) (static : Bool) (size : Option Expression)
  | PTR (cv : List Cvspec) (d : DeclType)
  /-- The `Bool` is `true` for variable-length parameter lists. -/
  | PROTO (d : DeclType) (params : List Parameter × Bool)
  | PROTO_OLD (d : DeclType) (params : List String)

/-- `Cabs.parameter` -/
inductive Parameter where
  | PARAM (specs : List SpecElem) (name : Option String) (d : DeclType)
      (attrs : List Attribute) (loc : Loc)

/-- `Cabs.field_group`; the optional expression is the bit-field width. -/
inductive FieldGroup where
  | Field_group (specs : List SpecElem) (fields : List (Option Name × Option Expression))
      (loc : Loc)
  | Field_group_static_assert (e : Expression) (eloc : Loc) (msg : Constant) (mloc : Loc)
      (loc : Loc)

/-- `Cabs.name`: a declarator with the name of the declared identifier pulled
out. -/
inductive Name where
  | Name (s : String) (d : DeclType) (attrs : List Attribute) (loc : Loc)

/-- `Cabs.init_name`: a declarator with an initializer. -/
inductive InitName where
  | Init_name (n : Name) (i : InitExpression)

/-- `Cabs.expression` -/
inductive Expression where
  | UNARY (op : UnaryOperator) (e : Expression)
  | BINARY (op : BinaryOperator) (e1 e2 : Expression)
  | QUESTION (e1 e2 e3 : Expression)
  /-- A `CAST` can actually be a compound literal. -/
  | CAST (t : List SpecElem × DeclType) (i : InitExpression)
  | CALL (f : Expression) (args : List Expression)
  | BUILTIN_VA_ARG (e : Expression) (t : List SpecElem × DeclType)
  | CONSTANT (c : Constant)
  | VARIABLE (s : String)
  | EXPR_SIZEOF (e : Expression)
  | TYPE_SIZEOF (t : List SpecElem × DeclType)
  | INDEX (e1 e2 : Expression)
  | MEMBEROF (e : Expression) (f : String)
  | MEMBEROFPTR (e : Expression) (f : String)
  | ALIGNOF (t : List SpecElem × DeclType)
  | GENERIC (e : Expression) (assocs : List (Option (List SpecElem × DeclType) × Expression))
  | BUILTIN_OFFSETOF (t : List SpecElem × DeclType) (path : List Initwhat)

/-- `Cabs.init_expression` -/
inductive InitExpression where
  | NO_INIT
  | SINGLE_INIT (e : Expression)
  | COMPOUND_INIT (l : List (List Initwhat × InitExpression))

/-- `Cabs.initwhat` -/
inductive Initwhat where
  | INFIELD_INIT (s : String)
  | ATINDEX_INIT (e : Expression)

/-- `Cabs.attribute` -/
inductive Attribute where
  | GCC_ATTR (l : List GccAttribute) (loc : Loc)
  | PACKED_ATTR (l : List Expression) (loc : Loc)
  | ALIGNAS_ATTR (l : List Expression) (loc : Loc)

/-- `Cabs.gcc_attribute` -/
inductive GccAttribute where
  | GCC_ATTR_EMPTY
  | GCC_ATTR_NOARGS (w : GccAttributeWord)
  | GCC_ATTR_ARGS (w : GccAttributeWord) (args : List Expression)

end

instance : Inhabited TypeSpecifier := ⟨.Tvoid⟩
instance : Inhabited Cvspec := ⟨.CV_CONST⟩
instance : Inhabited SpecElem := ⟨.SpecType .Tvoid⟩
instance : Inhabited DeclType := ⟨.JUSTBASE⟩
instance : Inhabited Expression := ⟨.VARIABLE ""⟩
instance : Inhabited InitExpression := ⟨.NO_INIT⟩
instance : Inhabited Initwhat := ⟨.INFIELD_INIT ""⟩
instance : Inhabited Attribute := ⟨.GCC_ATTR [] default⟩
instance : Inhabited GccAttribute := ⟨.GCC_ATTR_EMPTY⟩
instance : Inhabited Name := ⟨.Name "" .JUSTBASE [] default⟩
instance : Inhabited InitName := ⟨.Init_name default .NO_INIT⟩
instance : Inhabited Parameter := ⟨.PARAM [] none .JUSTBASE [] default⟩
instance : Inhabited FieldGroup := ⟨.Field_group [] [] default⟩

/-- `Cabs.init_name_group`: declarators that may have initializers, sharing a
base type and storage class (e.g. `int x = 1, y = 2;`). -/
abbrev InitNameGroup := List SpecElem × List InitName

/-- `Cabs.name_group` (e.g. `int x, y;`). -/
abbrev NameGroup := List SpecElem × List Name

/-- `Cabs.type_name` -/
abbrev TypeName := List SpecElem × DeclType

/-- `Cabs.generic_assoc` -/
abbrev GenericAssoc := Option TypeName × Expression

/-- `Cabs.asm_operand` (GCC extended asm). -/
inductive AsmOperand where
  | ASMOPERAND (name : Option String) (enc : Encoding) (cstr : List CharCode) (e : Expression)
  deriving Inhabited

/-- `Cabs.asm_flag` -/
abbrev AsmFlag := Encoding × List CharCode

mutual

/-- `Cabs.definition`: top-level declarations and definitions. -/
inductive Definition where
  | FUNDEF (specs : List SpecElem) (n : Name) (oldparams : List Definition) (body : Statement)
      (loc : Loc)
  /-- Global variable(s), or function prototype. -/
  | DECDEF (ing : InitNameGroup) (loc : Loc)
  | PRAGMA (s : String) (loc : Loc)
  | STATIC_ASSERT (e : Expression) (eloc : Loc) (msg : Constant) (mloc : Loc) (loc : Loc)

/-- `Cabs.statement` -/
inductive Statement where
  | NOP (loc : Loc)
  | COMPUTATION (e : Expression) (loc : Loc)
  | BLOCK (l : List Statement) (loc : Loc)
  | If (e : Expression) (s1 : Statement) (s2 : Option Statement) (loc : Loc)
  | WHILE (e : Expression) (s : Statement) (loc : Loc)
  | DOWHILE (e : Expression) (s : Statement) (loc : Loc)
  | FOR (init : Option ForClause) (cond : Option Expression) (incr : Option Expression)
      (s : Statement) (loc : Loc)
  | BREAK (loc : Loc)
  | CONTINUE (loc : Loc)
  | RETURN (e : Option Expression) (loc : Loc)
  | SWITCH (e : Expression) (s : Statement) (loc : Loc)
  | CASE (e : Expression) (s : Statement) (loc : Loc)
  | DEFAULT (s : Statement) (loc : Loc)
  | LABEL (l : String) (s : Statement) (loc : Loc)
  | GOTO (l : String) (loc : Loc)
  | ASM (cv : List Cvspec) (enc : Encoding) (template : List CharCode)
      (outputs inputs : List AsmOperand) (flags : List AsmFlag) (loc : Loc)
  /-- Definition or declaration of a variable or type. -/
  | DEFINITION (d : Definition)

/-- `Cabs.for_clause` -/
inductive ForClause where
  | FC_EXP (e : Expression)
  | FC_DECL (d : Definition)

end

instance : Inhabited Definition := ⟨.PRAGMA "" default⟩
instance : Inhabited Statement := ⟨.NOP default⟩
instance : Inhabited ForClause := ⟨.FC_EXP default⟩

end Cabs
end CC
