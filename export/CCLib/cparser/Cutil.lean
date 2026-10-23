/-
  Port of `cparser/Cutil.ml`: operations on C types and abstract syntax
  (attributes, typedef unrolling, type compatibility, sizes and alignments,
  struct layout, conversions, classification of types and expressions,
  smart constructors, default initializers, substitution).

  Functions that can raise an OCaml exception (`Env.Error`, `Not_found`, a
  failed `assert`) or read global state (`Machine.config`, the attribute
  table) run in the front-end monad `M` (see `Diagnostics.lean`).  The local
  exceptions `Incompat` and `No_default_init` become `OptionT M` (or `none`).

  `align x boundary` is computed as `(x + boundary - 1) / boundary * boundary`,
  which equals OCaml's `land`/`lnot` computation for the powers of two (and
  zero) that it is applied to.

  The first part of this file is split off into `CCLib.cparser.CutilAttr`.
-/

import CCLib.cparser.CutilAttr

namespace CC
namespace CParser
namespace Cutil
open C Env Diagnostics

/-! Some classification functions over types -/

def is_void_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TVoid _ => return true | _ => return false

def is_integer_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TInt .. | .TEnum .. => return true
  | _ => return false

def is_float_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TFloat .. => return true | _ => return false

def is_arith_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TInt .. | .TFloat .. | .TEnum .. => return true
  | _ => return false

def is_pointer_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TPtr .. => return true | _ => return false

def is_scalar_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TInt .. | .TFloat .. | .TPtr .. | .TArray .. | .TFun .. | .TEnum .. => return true
  | _ => return false

def is_composite_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TStruct .. | .TUnion .. => return true
  | _ => return false

def is_array_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TArray .. => return true | _ => return false

def is_function_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TFun .. => return true | _ => return false

def is_anonymous_composite : Typ → Bool
  | .TStruct id _ | .TUnion id _ => id.name == ""
  | _ => false

def is_anonymous_type : Typ → Bool
  | .TEnum id _ | .TStruct id _ | .TUnion id _ => id.name == ""
  | _ => false

def is_function_pointer_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TPtr ty _ => is_function_type env ty
  | _ => return false

/-- Find the info for a field access -/
def field_of_dot_access (env : Env.T) (t : Typ) (m : String) : M Field := do
  let m ← match ← unroll env t with
    | .TStruct id _ => Env.find_struct_member env id m
    | .TUnion id _ => Env.find_union_member env id m
    | _ => assertFalse "Cutil.field_of_dot_access"
  match m.reverse with
  | f :: _ => return f
  | [] => throw (.Failure "hd")

def field_of_arrow_access (env : Env.T) (t : Typ) (m : String) : M Field := do
  match ← unroll env t with
  | .TPtr t _ | .TArray t _ _ => field_of_dot_access env t m
  | _ => assertFalse "Cutil.field_of_arrow_access"

/-- Ranking of integer kinds -/
def integer_rank : IKind → Int
  | .IBool => 1
  | .IChar | .ISChar | .IUChar => 2
  | .IShort | .IUShort => 3
  | .IInt | .IUInt => 4
  | .ILong | .IULong => 5
  | .ILongLong | .IULongLong => 6

/-- Ranking of float kinds -/
def float_rank : FKind → Int
  | .FFloat16 => 0
  | .FFloat => 1
  | .FDouble => 2
  | .FLongDouble => 3

/-- Test for qualified array types -/
def is_qualified_array : Typ → Bool
  | .TArray ty _ attr => attr.any attr_is_standard || is_qualified_array ty
  | .TPtr ty _ => is_qualified_array ty
  | .TFun ty_ret _ _ _ => is_qualified_array ty_ret
  | _ => false

/-- Array and function types "decay" to pointer types in many cases -/
def pointer_decay (env : Env.T) (t : Typ) : M Typ := do
  match ← unroll env t with
  | .TArray ty _ _ => return .TPtr ty []
  | ty@(.TFun ..) => return .TPtr ty []
  | t => return t

/-- The usual unary conversions (H&S 6.3.3) -/
def unary_conversion (env : Env.T) (t : Typ) : M Typ := do
  match ← unroll env t with
  | .TInt kind _ =>
      match kind with
      | .IBool | .IChar | .ISChar | .IUChar | .IShort | .IUShort => return .TInt .IInt []
      | _ => return .TInt kind []
  | .TEnum _ _ => return .TInt enum_ikind []
  | .TArray ty _ _ => return .TPtr ty []
  | ty@(.TFun ..) => return .TPtr ty []
  | .TFloat kind _ => return .TFloat kind []
  | .TPtr ty _ => return .TPtr ty []
  | _ => return t

/-- The usual binary conversions (H&S 6.3.4).  Applies only to arithmetic
    types.  Return the type to which both sides are to be converted. -/
def binary_conversion (env : Env.T) (t1 t2 : Typ) : M Typ := do
  let t1 ← unary_conversion env t1
  let t2 ← unary_conversion env t2
  let isIF : Typ → Bool := fun | .TInt .. | .TFloat .. => true | _ => false
  let isI : Typ → Bool := fun | .TInt .. => true | _ => false
  let u1 ← unroll env t1
  let u2 ← unroll env t2
  match u1, u2 with
  | .TFloat .FLongDouble _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FLongDouble _ => if isIF u1 then return t2 else assertFalse "binary_conversion"
  | .TFloat .FDouble _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FDouble _ => if isIF u1 then return t2 else assertFalse "binary_conversion"
  | .TFloat .FFloat _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FFloat _ => if isIF u1 then return t2 else assertFalse "binary_conversion"
  | .TFloat .FFloat16 _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FFloat16 _ => if isI u1 then return t2 else assertFalse "binary_conversion"
  | .TInt k1 _, .TInt k2 _ =>
      if k1 == k2 then return t1
      match ← is_signed_ikind k1, ← is_signed_ikind k2 with
      | true, true | false, false =>
          return if integer_rank k1 ≥ integer_rank k2 then t1 else t2
      | false, true =>
          if integer_rank k1 ≥ integer_rank k2 then return t1
          else if (← sizeof_ikind k2) > (← sizeof_ikind k1) then return t2
          else return .TInt (unsigned_ikind_of k2) []
      | true, false =>
          if integer_rank k2 ≥ integer_rank k1 then return t2
          else if (← sizeof_ikind k1) > (← sizeof_ikind k2) then return t1
          else return .TInt (unsigned_ikind_of k1) []
  | _, _ => assertFalse "binary_conversion"

/-- Conversion on function arguments (with prototypes) -/
def argument_conversion (env : Env.T) (t : Typ) : M Typ := do
  match ← unroll env t with
  | .TArray ty _ attr => return .TPtr ty attr
  | ty@(.TFun ..) => return .TPtr ty []
  | _ => return t

/-- Conversion on function arguments (old-style unprototyped, or vararg)
    (H&S 6.3.5) -/
def default_argument_conversion (env : Env.T) (t : Typ) : M Typ := do
  match ← unary_conversion env t with
  | .TFloat .FFloat attr => return .TFloat .FDouble attr
  | t' => return t'

/-- Is the type `Tptr(ty, a)` appropriate for pointer arithmetic? -/
def pointer_arithmetic_ok (env : Env.T) (ty : Typ) : M Bool := do
  match ← unroll env ty with
  | .TVoid _ | .TFun .. => return false
  | _ => return !(← incomplete_type env ty)

/-- The type of `x.fld`. -/
def type_of_member (env : Env.T) (fld : Field) : M Typ := do
  match fld.fld_bitfield with
  | none => return fld.fld_typ
  | some w =>
      let (ik, attr) ← match ← unroll env fld.fld_typ with
        | .TInt ik attr => pure (ik, attr)
        | .TEnum _ attr => pure (enum_ikind, attr)
        | _ => assertFalse "Cutil.type_of_member"
      if w < (← sizeof_ikind ik) * 8 then return .TInt (signed_ikind_of ik) attr
      else return fld.fld_typ

/-! Special types -/

def find_matching_unsigned_ikind (sz : Int) : M IKind := do
  let c ← getConfig
  if sz ≤ 0 then assertFalse "find_matching_unsigned_ikind"
  if sz == c.sizeof_short then return .IUShort
  else if sz == c.sizeof_int then return .IUInt
  else if sz == c.sizeof_long then return .IULong
  else if sz == c.sizeof_longlong then return .IULongLong
  else assertFalse "find_matching_unsigned_ikind"

def find_matching_signed_ikind (sz : Int) : M IKind := do
  let c ← getConfig
  if sz ≤ 0 then assertFalse "find_matching_signed_ikind"
  if sz == c.sizeof_int then return .IInt
  else if sz == c.sizeof_long then return .ILong
  else if sz == c.sizeof_longlong then return .ILongLong
  else assertFalse "find_matching_signed_ikind"

def wchar_ikind : M IKind := do return (← getConfig).wchar_ikind
def size_t_ikind : M IKind := do find_matching_unsigned_ikind (← getConfig).sizeof_size_t
def ptr_t_ikind : M IKind := do find_matching_unsigned_ikind (← getConfig).sizeof_ptr
def ptrdiff_t_ikind : M IKind := do find_matching_signed_ikind (← getConfig).sizeof_ptrdiff_t

/-- The type of a constant (the length of a `CStr` is its number of bytes). -/
def type_of_constant : Constant → Typ
  | .CInt _ ik _ => .TInt ik []
  | .CFloat _ fk => .TFloat fk []
  | .CStr s => .TArray (.TInt .IChar []) (some (Int64.ofNat (s.utf8ByteSize + 1))) []
  | .CWStr s ik => .TArray (.TInt ik []) (some (Int64.ofNat (s.length + 1))) []
  | .CEnum _ _ => .TInt .IInt []

/-- Check that a C expression is a lvalue -/
partial def is_lvalue (e : Exp) : Bool :=
  match e.edesc with
  | .EVar _ => true
  | .EConst (.CStr _) | .EConst (.CWStr ..) => true
  | .EUnop .Oderef _ | .EUnop (.Oarrow _) _ => true
  | .EUnop (.Odot _) e' => is_lvalue e'
  | .EBinop .Oindex _ _ _ => true
  | .ECompound .. => true
  | _ => false

/-- Is a type const-qualified (or a composite with a const member)? -/
partial def is_const_type (env : Env.T) (ty : Typ) : M Bool := do
  if (← attributes_of_type env ty).contains .AConst then return true
  match ← unroll env ty with
  | .TStruct s _ =>
      let ci ← Env.find_struct env s
      ci.ci_members.anyM fun m => is_const_type env m.fld_typ
  | .TUnion s _ =>
      let ci ← Env.find_union env s
      ci.ci_members.anyM fun m => is_const_type env m.fld_typ
  | _ => return false

/-- Check that a C expression is a modifiable l-value. -/
def is_modifiable_lvalue (env : Env.T) (e : Exp) : M Bool := do
  if !is_lvalue e then return false
  if ← incomplete_type env e.etyp then return false
  if ← is_const_type env e.etyp then return false
  match ← unroll env e.etyp with
  | .TFun .. | .TArray .. => return false
  | _ => return true

/-- Check that a C expression is the literal "0", which can be used as a
    pointer. -/
def is_literal_0 (e : Exp) : Bool :=
  match e.edesc with
  | .EConst (.CInt 0 _ _) => true
  | _ => false

/-- Check that a C statement is a debug annotation -/
def is_debug_stmt (s : Stmt) : Bool :=
  match s.sdesc with
  | .Sdo (.mk (.ECall (.mk (.EVar id) _) _) _) => id.name == "__builtin_debug"
  | _ => false

def is_call_to_fun (e : Exp) (s : String) : Bool :=
  match e.edesc with
  | .EVar id => id.name == s
  | _ => false

def is_bitfield (env : Env.T) (e : Exp) : M Bool := do
  match e.edesc with
  | .EUnop (.Odot f) b => return (← field_of_dot_access env b.etyp f).fld_bitfield.isSome
  | .EUnop (.Oarrow f) b => return (← field_of_arrow_access env b.etyp f).fld_bitfield.isSome
  | _ => return false

def contains_flex_array_mem (env : Env.T) (ty : Typ) : M Bool := do
  match ← unroll env ty with
  | .TStruct id _ =>
      let ci ← Env.find_struct env id
      let rec check_mem : List Field → Bool
        | [] => false
        | [{ fld_typ := .TArray _ none _, .. }] => true
        | _ :: rem => check_mem rem
      return check_mem ci.ci_members
  | _ => return false

/-- Assignment compatibility check over attributes. -/
def valid_assignment_attr (afrom ato : Attributes) : Bool :=
  let (afromstd, _) := afrom.partition attr_is_standard
  let (atostd, _) := ato.partition attr_is_standard
  incl_attributes afromstd atostd

/-- Check that an assignment is allowed -/
def valid_assignment (env : Env.T) (from_ : Exp) (tto : Typ) : M Bool := do
  match ← pointer_decay env from_.etyp, ← pointer_decay env tto with
  | .TInt .., .TInt .. | .TInt .., .TFloat .. | .TInt .., .TEnum ..
  | .TFloat .., .TInt .. | .TFloat .., .TFloat .. | .TFloat .., .TEnum ..
  | .TEnum .., .TInt .. | .TEnum .., .TFloat .. | .TEnum .., .TEnum .. => return true
  | .TInt .., .TPtr .. => return is_literal_0 from_
  | .TPtr ty _, .TPtr ty' _ =>
      return valid_assignment_attr (← attributes_of_type env ty) (← attributes_of_type env ty')
        && ((← is_void_type env ty) || (← is_void_type env ty')
            || (← compatible_types .AttrIgnoreTop env ty ty'))
  | .TStruct s _, .TStruct s' _ => return s == s'
  | .TUnion s _, .TUnion s' _ => return s == s'
  | _, _ => return false

/-- Check that a cast is allowed -/
def valid_cast (env : Env.T) (tfrom tto : Typ) : M Bool := do
  let f ← unroll env tfrom
  let t ← unroll env tto
  match t with
  | .TVoid _ => return true
  | _ =>
    let fromIntPtr := match f with
      | .TInt .. | .TPtr .. | .TArray .. | .TFun .. | .TEnum .. => true | _ => false
    let toIntPtr := match t with | .TInt .. | .TPtr .. | .TEnum .. => true | _ => false
    let fromArith := match f with | .TInt .. | .TFloat .. | .TEnum .. => true | _ => false
    let toArith := match t with | .TInt .. | .TFloat .. | .TEnum .. => true | _ => false
    return (fromIntPtr && toIntPtr) || (fromArith && toArith)

/-- Check that the cast from `tfrom` to `tto` is an integer to pointer
    conversion -/
def int_pointer_conversion (env : Env.T) (tfrom tto : Typ) : M Bool := do
  match ← unroll env tfrom, ← unroll env tto with
  | .TInt .., .TPtr .. | .TEnum .., .TPtr .. | .TPtr .., .TInt .. | .TPtr .., .TEnum .. =>
      return true
  | _, _ => return false

/-! Smart constructors -/

/-- Construct an integer constant -/
def intconst (v : Int64) (ik : IKind) : Exp := .mk (.EConst (.CInt v ik "")) (.TInt ik [])

/-- Construct the 0 float constant of double type -/
def floatconst0 : Exp :=
  .mk (.EConst (.CFloat { hex := false, intPart := "0", fracPart := "0", exp := "0" } .FDouble))
    (.TFloat .FDouble [])

/-- Construct a cast expression -/
def ecast (ty : Typ) (e : Exp) : Exp := .mk (.ECast ty e) ty

/-- Construct the literal "0" with void * type -/
def nullconst : Exp := ecast (.TPtr (.TVoid []) []) (intconst 0 .IInt)

/-- Construct an assignment expression -/
def eassign (e1 e2 : Exp) : Exp := .mk (.EBinop .Oassign e1 e2 e1.etyp) e1.etyp

/-- Construct a "," expression.  Reassociate to the left. -/
partial def ecomma (e1 e2 : Exp) : Exp :=
  match e2.edesc with
  | .EBinop .Ocomma e2' e2'' _ => ecomma (ecomma e1 e2') e2''
  | _ => .mk (.EBinop .Ocomma e1 e2 e2.etyp) e2.etyp

/-- Construct a cascade of "," expressions. -/
def ecommalist (el : List Exp) (e : Exp) : Exp :=
  match el with
  | [] => e
  | e1 :: el => ecomma (el.foldl ecomma e1) e

/-- Construct an address-of expression. -/
partial def eaddrof (e : Exp) : Exp :=
  match e.edesc with
  | .EUnop .Oderef e1 => e1
  | .EBinop .Ocomma e1 e2 _ => ecomma e1 (eaddrof e2)
  | .EConditional e1 e2 e3 => .mk (.EConditional e1 (eaddrof e2) (eaddrof e3)) (.TPtr e.etyp [])
  | _ => .mk (.EUnop .Oaddrof e) (.TPtr e.etyp [])

/-- Construct a sequence -/
def sseq (loc : Location) (s1 s2 : Stmt) : Stmt :=
  match s1.sdesc, s2.sdesc with
  | .Sskip, _ => s2
  | _, .Sskip => s1
  | _, .Sblock sl => .mk (.Sblock (s1 :: sl)) loc
  | _, _ => .mk (.Sseq s1 s2) loc

/-- Construct an assignment statement -/
def sassign (loc : Location) (lv rv : Exp) : Stmt := .mk (.Sdo (eassign lv rv)) loc

/-- Dummy skip statement -/
def sskip : Stmt := .mk .Sskip no_loc

/-- Print a location -/
def printloc (loc : Location) : String :=
  if loc.1 != "" then s!"{loc.1}:{loc.2}: " else ""

/-- Format a location -/
def formatloc := printloc

/-- Generate the default initializer for the given type (`none` for the
    exception `No_default_init`). -/
partial def default_init (env : Env.T) (ty : Typ) : M (Option Init) := (go ty).run
where
  go (ty : Typ) : OptionT M Init := do
    match ← (unroll env ty : M Typ) with
    | .TInt .. | .TEnum .. => return .Init_single (intconst 0 .IInt)
    | .TFloat .. => return .Init_single floatconst0
    | .TPtr .. => return .Init_single nullconst
    | .TArray .. => return .Init_array []
    | .TStruct id _ =>
        let ci ← (Env.find_struct env id : M CompositeInfo)
        let flds ← ci.ci_members.filterMapM fun f1 =>
          if f1.fld_name == "" then pure none
          else do return some (f1, ← go f1.fld_typ)
        return .Init_struct id flds
    | .TUnion id _ =>
        let ci ← (Env.find_union env id : M CompositeInfo)
        match ci.ci_members.find? (·.fld_name != "") with
        | none => failure
        | some fld => return .Init_union id fld (← go fld.fld_typ)
    | _ => failure

/-! Substitution of variables by expressions -/

mutual
partial def subst_expr (phi : IdentMap Exp) (e : Exp) : Exp :=
  match e.edesc with
  | .EConst _ | .ESizeof _ | .EAlignof _ => e
  | .EVar x => (phi.get? x).getD e
  | .EUnop op e1 => e.withDesc (.EUnop op (subst_expr phi e1))
  | .EBinop op e1 e2 ty => e.withDesc (.EBinop op (subst_expr phi e1) (subst_expr phi e2) ty)
  | .EConditional e1 e2 e3 =>
      e.withDesc (.EConditional (subst_expr phi e1) (subst_expr phi e2) (subst_expr phi e3))
  | .ECast ty e1 => e.withDesc (.ECast ty (subst_expr phi e1))
  | .ECompound ty i => e.withDesc (.ECompound ty (subst_init phi i))
  | .ECall e1 el => e.withDesc (.ECall (subst_expr phi e1) (el.map (subst_expr phi)))

partial def subst_init (phi : IdentMap Exp) : Init → Init
  | .Init_single e => .Init_single (subst_expr phi e)
  | .Init_array il => .Init_array (il.map (subst_init phi))
  | .Init_struct name fl => .Init_struct name (fl.map fun (f, i) => (f, subst_init phi i))
  | .Init_union name f i => .Init_union name f (subst_init phi i)
end

def subst_decl (phi : IdentMap Exp) : Decl → Decl
  | .mk sto name ty optinit => .mk sto name ty (optinit.map (subst_init phi))

partial def subst_stmt (phi : IdentMap Exp) (s : Stmt) : Stmt :=
  .mk (match s.sdesc with
    | .Sskip | .Sbreak | .Scontinue | .Sgoto _ => s.sdesc
    | .Sdo e => .Sdo (subst_expr phi e)
    | .Sseq s1 s2 => .Sseq (subst_stmt phi s1) (subst_stmt phi s2)
    | .Sif e s1 s2 => .Sif (subst_expr phi e) (subst_stmt phi s1) (subst_stmt phi s2)
    | .Swhile e s1 => .Swhile (subst_expr phi e) (subst_stmt phi s1)
    | .Sdowhile s1 e => .Sdowhile (subst_stmt phi s1) (subst_expr phi e)
    | .Sfor s1 e s2 s3 =>
        .Sfor (subst_stmt phi s1) (subst_expr phi e) (subst_stmt phi s2) (subst_stmt phi s3)
    | .Sswitch e s1 => .Sswitch (subst_expr phi e) (subst_stmt phi s1)
    | .Slabeled l s1 => .Slabeled l (subst_stmt phi s1)
    | .Sreturn none => s.sdesc
    | .Sreturn (some e) => .Sreturn (some (subst_expr phi e))
    | .Sblock sl => .Sblock (sl.map (subst_stmt phi))
    | .Sdecl d => .Sdecl (subst_decl phi d)
    | .Sasm attr template outputs inputs clob =>
        let op : AsmOperand → AsmOperand := fun (lbl, cstr, e) => (lbl, cstr, subst_expr phi e)
        .Sasm attr template (outputs.map op) (inputs.map op) clob) s.sloc

def is_volatile_variable (env : Env.T) (exp : Exp) : M Bool := do
  match exp.edesc with
  | .EVar _ => return (← attributes_of_type env exp.etyp).contains .AVolatile
  | _ => return false

end Cutil
end CParser
end CC
