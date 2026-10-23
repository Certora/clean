/-
  Port of `cparser/C.mli`: the abstract syntax of C after elaboration, as
  used by CompCert's (untrusted, OCaml) front end: the elaborator `Elab`, the
  source-to-source transformations of `cparser/` and the translation `C2C`
  to CompCert C.

  Differences from OCaml:
  * OCaml's `int64` is `Int64`; OCaml's `int` is `Int`.
  * The records `exp`, `stmt` and `globdecl` are mutually recursive with
    their `*_desc` types, so they are single-constructor inductives with the
    projections `Exp.edesc`, `Exp.etyp`, `Stmt.sdesc`, … defined by hand.
    `⟨d, t⟩` builds an `Exp` (resp. `Stmt`).
  * Structural equality (`=` in OCaml) is the derived `BEq`.  The derived
    `Ord` on attributes is the order of OCaml's polymorphic `compare`
    (constant constructors first, then by tag, then by arguments), which the
    sorted attribute lists of `Cutil` rely on.
-/

namespace CC
namespace CParser
namespace C

/-- Locations: file name and line number. -/
abbrev Location := String × Int

/-- Identifiers: name as in the source, and unique stamp. -/
structure Ident where
  name : String
  stamp : Int
  deriving BEq, Hashable, Inhabited, Repr

instance : Ord Ident := ⟨fun a b => compare a.stamp b.stamp⟩

/-- Kinds of integers. -/
inductive IKind where
  | IBool | IChar | ISChar | IUChar | IInt | IUInt | IShort | IUShort
  | ILong | IULong | ILongLong | IULongLong
  deriving BEq, DecidableEq, Ord, Inhabited, Repr, Hashable

/-- Kinds of floating-point numbers. -/
inductive FKind where
  | FFloat16 | FFloat | FDouble | FLongDouble
  deriving BEq, DecidableEq, Ord, Inhabited, Repr, Hashable

/-- Floating-point constants, as written in the source. -/
structure FloatCst where
  hex : Bool
  intPart : String
  fracPart : String
  exp : String
  deriving BEq, Ord, Inhabited, Repr, Hashable

/-- Constants. -/
inductive Constant where
  /-- integer value, kind, and the text as it appeared in the source -/
  | CInt (v : Int64) (ik : IKind) (s : String)
  | CFloat (f : FloatCst) (fk : FKind)
  | CStr (s : String)
  | CWStr (l : List Int64) (ik : IKind)
  /-- enum tag, integer value -/
  | CEnum (id : Ident) (v : Int64)
  deriving BEq, Inhabited, Repr

/-- Arguments of attributes. -/
inductive AttrArg where
  | AIdent (s : String)
  | AInt (n : Int64)
  | AString (s : String)
  deriving BEq, Ord, Inhabited, Repr, Hashable

/-- Attributes. -/
inductive Attribute where
  | AConst
  | AVolatile
  | ARestrict
  /-- always a power of 2 -/
  | AAlignas (n : Int)
  | Attr (name : String) (args : List AttrArg)
  deriving BEq, Ord, Inhabited, Repr, Hashable

instance : LT Attribute := ⟨fun a b => compare a b = .lt⟩
instance (a b : Attribute) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compare a b = .lt))

abbrev Attributes := List Attribute

/-- Storage classes. -/
inductive Storage where
  /-- used for toplevel names without explicit storage -/
  | Storage_default
  | Storage_extern
  | Storage_static
  /-- used for block-scoped names without explicit storage -/
  | Storage_auto
  | Storage_register
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Unary operators. -/
inductive UnaryOperator where
  | Ominus | Oplus | Olognot | Onot | Oderef | Oaddrof
  | Opreincr | Opredecr | Opostincr | Opostdecr
  | Odot (f : String)
  | Oarrow (f : String)
  deriving BEq, Inhabited, Repr

/-- Binary operators. -/
inductive BinaryOperator where
  | Oadd | Osub | Omul | Odiv | Omod | Oand | Oor | Oxor | Oshl | Oshr
  | Oeq | One | Olt | Ogt | Ole | Oge | Oindex
  | Oassign | Oadd_assign | Osub_assign | Omul_assign | Odiv_assign
  | Omod_assign | Oand_assign | Oor_assign | Oxor_assign | Oshl_assign
  | Oshr_assign | Ocomma | Ologand | Ologor
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Types. -/
inductive Typ where
  | TVoid (a : Attributes)
  | TInt (ik : IKind) (a : Attributes)
  | TFloat (fk : FKind) (a : Attributes)
  | TPtr (t : Typ) (a : Attributes)
  | TArray (t : Typ) (sz : Option Int64) (a : Attributes)
  | TFun (res : Typ) (params : Option (List (Ident × Typ))) (vararg : Bool)
      (a : Attributes)
  | TNamed (id : Ident) (a : Attributes)
  | TStruct (id : Ident) (a : Attributes)
  | TUnion (id : Ident) (a : Attributes)
  | TEnum (id : Ident) (a : Attributes)
  deriving BEq, Inhabited, Repr

/-- Struct or union field. -/
structure Field where
  fld_name : String
  fld_typ : Typ
  fld_bitfield : Option Int
  fld_anonymous : Bool
  deriving BEq, Inhabited, Repr

inductive StructOrUnion where
  | Struct
  | Union
  deriving BEq, DecidableEq, Inhabited, Repr

mutual
/-- Expressions: `{ edesc; etyp }`. -/
inductive Exp where
  | mk (edesc : ExpDesc) (etyp : Typ)

inductive ExpDesc where
  | EConst (c : Constant)
  | ESizeof (t : Typ)
  | EAlignof (t : Typ)
  | EVar (id : Ident)
  | EUnop (op : UnaryOperator) (e : Exp)
  /-- the type is the one at which the operation is performed -/
  | EBinop (op : BinaryOperator) (e1 e2 : Exp) (ty : Typ)
  | EConditional (e1 e2 e3 : Exp)
  | ECast (t : Typ) (e : Exp)
  | ECompound (t : Typ) (i : Init)
  | ECall (f : Exp) (args : List Exp)

/-- Initializers. -/
inductive Init where
  | Init_single (e : Exp)
  | Init_array (l : List Init)
  | Init_struct (id : Ident) (l : List (Field × Init))
  | Init_union (id : Ident) (f : Field) (i : Init)
end

mutual
partial def Exp.beq : Exp → Exp → Bool
  | .mk d1 t1, .mk d2 t2 => ExpDesc.beq d1 d2 && t1 == t2
partial def ExpDesc.beq : ExpDesc → ExpDesc → Bool
  | .EConst c1, .EConst c2 => c1 == c2
  | .ESizeof t1, .ESizeof t2 => t1 == t2
  | .EAlignof t1, .EAlignof t2 => t1 == t2
  | .EVar i1, .EVar i2 => i1 == i2
  | .EUnop o1 e1, .EUnop o2 e2 => o1 == o2 && Exp.beq e1 e2
  | .EBinop o1 a1 b1 t1, .EBinop o2 a2 b2 t2 =>
      o1 == o2 && Exp.beq a1 a2 && Exp.beq b1 b2 && t1 == t2
  | .EConditional a1 b1 c1, .EConditional a2 b2 c2 =>
      Exp.beq a1 a2 && Exp.beq b1 b2 && Exp.beq c1 c2
  | .ECast t1 e1, .ECast t2 e2 => t1 == t2 && Exp.beq e1 e2
  | .ECompound t1 i1, .ECompound t2 i2 => t1 == t2 && Init.beq i1 i2
  | .ECall f1 l1, .ECall f2 l2 =>
      Exp.beq f1 f2 && l1.length == l2.length &&
        (l1.zip l2).all (fun (a, b) => Exp.beq a b)
  | _, _ => false
partial def Init.beq : Init → Init → Bool
  | .Init_single e1, .Init_single e2 => Exp.beq e1 e2
  | .Init_array l1, .Init_array l2 =>
      l1.length == l2.length && (l1.zip l2).all (fun (a, b) => Init.beq a b)
  | .Init_struct i1 l1, .Init_struct i2 l2 =>
      i1 == i2 && l1.length == l2.length &&
        (l1.zip l2).all (fun ((f1, a), (f2, b)) => f1 == f2 && Init.beq a b)
  | .Init_union i1 f1 a, .Init_union i2 f2 b =>
      i1 == i2 && f1 == f2 && Init.beq a b
  | _, _ => false
end

instance : BEq Exp := ⟨Exp.beq⟩
instance : BEq ExpDesc := ⟨ExpDesc.beq⟩
instance : BEq Init := ⟨Init.beq⟩

instance : Inhabited ExpDesc := ⟨.ESizeof default⟩
instance : Inhabited Exp := ⟨.mk default default⟩
instance : Inhabited Init := ⟨.Init_array []⟩

def Exp.edesc : Exp → ExpDesc | .mk d _ => d
def Exp.etyp : Exp → Typ | .mk _ t => t

/-- `{ e with edesc = d }` -/
def Exp.withDesc (e : Exp) (d : ExpDesc) : Exp := .mk d e.etyp

/-- GCC extended asm operand: optional label, constraint, expression. -/
abbrev AsmOperand := Option String × String × Exp

mutual
/-- Statements: `{ sdesc; sloc }`. -/
inductive Stmt where
  | mk (sdesc : StmtDesc) (sloc : Location)

inductive StmtDesc where
  | Sskip
  | Sdo (e : Exp)
  | Sseq (s1 s2 : Stmt)
  | Sif (e : Exp) (s1 s2 : Stmt)
  | Swhile (e : Exp) (s : Stmt)
  | Sdowhile (s : Stmt) (e : Exp)
  | Sfor (s1 : Stmt) (e : Exp) (s2 s3 : Stmt)
  | Sbreak
  | Scontinue
  | Sswitch (e : Exp) (s : Stmt)
  | Slabeled (l : SLabel) (s : Stmt)
  | Sgoto (lbl : String)
  | Sreturn (e : Option Exp)
  | Sblock (l : List Stmt)
  | Sdecl (d : Decl)
  | Sasm (attr : Attributes) (template : String) (outputs inputs : List AsmOperand)
      (clobbers : List String)

inductive SLabel where
  | Slabel (s : String)
  | Scase (e : Exp) (v : Int64)
  | Sdefault

/-- Declarations: storage, name, type, optional initializer. -/
inductive Decl where
  | mk (sto : Storage) (id : Ident) (ty : Typ) (init : Option Init)
end

instance : Inhabited StmtDesc := ⟨.Sskip⟩
instance : Inhabited Stmt := ⟨.mk .Sskip ("", -1)⟩
instance : Inhabited Decl := ⟨.mk .Storage_default default default none⟩

def Stmt.sdesc : Stmt → StmtDesc | .mk d _ => d
def Stmt.sloc : Stmt → Location | .mk _ l => l

def Decl.sto : Decl → Storage | .mk s _ _ _ => s
def Decl.id : Decl → Ident | .mk _ i _ _ => i
def Decl.ty : Decl → Typ | .mk _ _ t _ => t
def Decl.init : Decl → Option Init | .mk _ _ _ i => i

/-- Function definitions. -/
structure Fundef where
  fd_storage : Storage
  fd_inline : Bool
  fd_name : Ident
  fd_attrib : Attributes
  /-- return type -/
  fd_ret : Typ
  /-- formal parameters -/
  fd_params : List (Ident × Typ)
  /-- variable arguments? -/
  fd_vararg : Bool
  /-- local variables -/
  fd_locals : List Decl
  fd_body : Stmt
  deriving Inhabited

/-- Element of an enumeration: name, value, optional source expression. -/
abbrev Enumerator := Ident × Int64 × Option Exp

/-- Global declarations (`globdecl_desc`). -/
inductive GlobdeclDesc where
  /-- variable declaration, function prototype -/
  | Gdecl (d : Decl)
  /-- function definition -/
  | Gfundef (f : Fundef)
  /-- struct/union declaration -/
  | Gcompositedecl (su : StructOrUnion) (id : Ident) (a : Attributes)
  /-- struct/union definition -/
  | Gcompositedef (su : StructOrUnion) (id : Ident) (a : Attributes) (fl : List Field)
  /-- typedef -/
  | Gtypedef (id : Ident) (t : Typ)
  /-- enum definition -/
  | Genumdef (id : Ident) (a : Attributes) (l : List Enumerator)
  /-- `#pragma` directive -/
  | Gpragma (s : String)
  deriving Inhabited

/-- Global declarations: `{ gdesc; gloc }`. -/
structure Globdecl where
  gdesc : GlobdeclDesc
  gloc : Location
  deriving Inhabited

abbrev Program := List Globdecl

/-- Builtin types and functions. -/
structure Builtins where
  builtin_typedefs : List (String × Typ)
  /-- name, (result type, argument types, variadic?) -/
  builtin_functions : List (String × (Typ × List Typ × Bool))
  deriving Inhabited

end C
end CParser
end CC
