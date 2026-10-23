/-
  First part of the port of `cparser/Cutil.ml` (split from `CCLib.cparser.Cutil`): attributes, type compatibility, sizes and alignments, composite info records.
-/
import CCLib.cparser.Env
import CCLib.cparser.Cprint

namespace CC
namespace CParser
namespace Cutil

open C Env Diagnostics

/-- Empty location -/
def no_loc : Location := ("", -1)

/-- Sets and maps over identifiers. -/
abbrev IdentSet := Std.HashSet Ident
abbrev IdentMap (α : Type) := Std.HashMap Ident α

/-! ### Operations on attributes -/

/-- Normalize the name of an attribute, removing starting and trailing `__` -/
def normalize_attrname (a : String) : String :=
  if a.length ≥ 4 && a.startsWith "__" && a.endsWith "__" then
    ((a.drop 2).dropEnd 2).toString
  else a

/-- Lists of attributes are kept sorted in increasing order -/
def add_attributes : Attributes → Attributes → Attributes
  | [], al2 => al2
  | al1, [] => al1
  | a1 :: al1', a2 :: al2' =>
      if a1 < a2 then a1 :: add_attributes al1' (a2 :: al2')
      else if a2 < a1 then a2 :: add_attributes (a1 :: al1') al2'
      else a1 :: add_attributes al1' al2'

/-- viewed as sets: `al1 \ al2` -/
def remove_attributes : Attributes → Attributes → Attributes
  | [], _ => []
  | al1, [] => al1
  | a1 :: al1', a2 :: al2' =>
      if a1 < a2 then a1 :: remove_attributes al1' (a2 :: al2')
      else if a2 < a1 then remove_attributes (a1 :: al1') al2'
      else remove_attributes al1' al2'

def incl_attributes : Attributes → Attributes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a1 :: al1', a2 :: al2' =>
      if a1 < a2 then false
      else if a2 < a1 then incl_attributes (a1 :: al1') al2'
      else incl_attributes al1' al2'

def find_custom_attributes (names : List String) : Attributes → List (List AttrArg)
  | [] => []
  | .Attr name args :: tl =>
      if names.contains name then args :: find_custom_attributes names tl
      else find_custom_attributes names tl
  | _ :: tl => find_custom_attributes names tl

def remove_custom_attributes (names : List String) : Attributes → Attributes
  | [] => []
  | a :: tl =>
      match a with
      | .Attr name _ =>
          if names.contains name then remove_custom_attributes names tl
          else a :: remove_custom_attributes names tl
      | _ => a :: remove_custom_attributes names tl

/-! Classification of attributes (`attribute_class` is `AttributeClass`,
    declared in `Diagnostics.lean`) -/

def declare_attribute (name : String) (cls : AttributeClass) : M Unit :=
  modify fun s =>
    let n := normalize_attrname name
    { s with attr_class := (n, cls) :: s.attr_class.filter (·.1 != n) }

def declare_attributes (l : List (String × AttributeClass)) : M Unit :=
  l.forM fun (n, c) => declare_attribute n c

def class_of_attribute : Attribute → M AttributeClass
  | .AConst | .AVolatile | .ARestrict => pure .Attr_type
  | .AAlignas _ => pure .Attr_object
  | .Attr name _ => do
      match (← get).attr_class.lookup (normalize_attrname name) with
      | some c => pure c
      | none => pure .Attr_unknown

/-- Name for printing an attribute -/
def name_of_attribute : Attribute → String
  | .AConst => "const"
  | .AVolatile => "volatile"
  | .ARestrict => "restrict"
  | .AAlignas _ => "_Alignas"
  | .Attr name _ => name

/-- Is an attribute a ISO C standard attribute? -/
def attr_is_standard : Attribute → Bool
  | .AConst | .AVolatile | .ARestrict => true
  | .AAlignas _ | .Attr .. => false

/-- Is an attribute applicable to a whole array (true) or only to
    array elements (false)? -/
def attr_array_applicable (a : Attribute) : M Bool := do
  return (← class_of_attribute a) != .Attr_type

/-- Is an attribute of a composite type applicable to members of this type
    when they are accessed? -/
def attr_inherited_by_members : Attribute → Bool
  | .AConst | .AVolatile | .ARestrict => true
  | .AAlignas _ | .Attr .. => false

/-- Adding top-level attributes to a type.  Doesn't need to unroll defns.
    For array types, standard attrs are pushed to the element type. -/
partial def add_attributes_type (attr : Attributes) (t : Typ) : M Typ :=
  match t with
  | .TVoid a => pure (.TVoid (add_attributes attr a))
  | .TInt ik a => pure (.TInt ik (add_attributes attr a))
  | .TFloat fk a => pure (.TFloat fk (add_attributes attr a))
  | .TPtr ty a => pure (.TPtr ty (add_attributes attr a))
  | .TArray ty sz a => do
      let mut attr_arr := []
      let mut attr_elt := []
      for x in attr do
        if ← attr_array_applicable x then attr_arr := attr_arr ++ [x]
        else attr_elt := attr_elt ++ [x]
      return .TArray (← add_attributes_type attr_elt ty) sz (add_attributes attr_arr a)
  | .TFun ty params vararg a => pure (.TFun ty params vararg (add_attributes attr a))
  | .TNamed s a => pure (.TNamed s (add_attributes attr a))
  | .TStruct s a => pure (.TStruct s (add_attributes attr a))
  | .TUnion s a => pure (.TUnion s (add_attributes attr a))
  | .TEnum s a => pure (.TEnum s (add_attributes attr a))

/-- Unrolling of typedef -/
partial def unroll (env : Env.T) (t : Typ) : M Typ :=
  match t with
  | .TNamed name attr => do
      let ty ← Env.find_typedef env name
      unroll env (← add_attributes_type attr ty)
  | _ => pure t

private def catchUnboundTag {α} (x : M α) (dflt : α) : M α :=
  tryCatch x fun
    | .EnvError (.Unbound_tag _ _) => pure dflt
    | e => throw e

/-- Extracting the attributes of a type, including the attributes attached
    to typedefs, structs and unions. -/
partial def attributes_of_type (env : Env.T) (t : Typ) : M Attributes :=
  match t with
  | .TVoid a | .TInt _ a | .TFloat _ a | .TPtr _ a | .TFun _ _ _ a => pure a
  | .TArray ty _ a => do return add_attributes a (← attributes_of_type env ty)
  | .TNamed _ _ => do attributes_of_type env (← unroll env t)
  | .TStruct s a =>
      catchUnboundTag (do return add_attributes (← Env.find_struct env s).ci_attr a) a
  | .TUnion s a =>
      catchUnboundTag (do return add_attributes (← Env.find_union env s).ci_attr a) a
  | .TEnum s a =>
      catchUnboundTag (do return add_attributes (← Env.find_enum env s).ei_attr a) a

/-- Extracting the attributes of a type, excluding the attributes attached to
    typedefs, structs and unions. -/
def attributes_of_type_no_expand : Typ → Attributes
  | .TVoid a | .TInt _ a | .TFloat _ a | .TPtr _ a | .TFun _ _ _ a => a
  | .TArray ty _ a => add_attributes a (attributes_of_type_no_expand ty)
  | .TNamed _ a | .TStruct _ a | .TUnion _ a | .TEnum _ a => a

/-- Changing the attributes of a type (at top-level) -/
partial def change_attributes_type (env : Env.T) (f : Attributes → Attributes) (t : Typ) :
    M Typ :=
  match t with
  | .TVoid a => pure (.TVoid (f a))
  | .TInt ik a => pure (.TInt ik (f a))
  | .TFloat fk a => pure (.TFloat fk (f a))
  | .TPtr ty a => pure (.TPtr ty (f a))
  | .TArray ty sz a => do return .TArray (← change_attributes_type env f ty) sz (f a)
  | .TFun ty params vararg a => pure (.TFun ty params vararg (f a))
  | .TNamed _ _ => do
      let t1 ← unroll env t
      let t2 ← change_attributes_type env f t1
      return if t2 == t1 then t else t2
  | .TStruct s a => pure (.TStruct s (f a))
  | .TUnion s a => pure (.TUnion s (f a))
  | .TEnum s a => pure (.TEnum s (f a))

def remove_attributes_type (env : Env.T) (attr : Attributes) (t : Typ) : M Typ :=
  change_attributes_type env (fun a => remove_attributes a attr) t

def erase_attributes_type (env : Env.T) (t : Typ) : M Typ :=
  change_attributes_type env (fun _ => []) t

/-- Remove all attributes from type that are not contained in `attr` -/
def strip_attributes_type (t : Typ) (attr : Attributes) : Typ :=
  let strip := List.filter (fun a => attr.contains a)
  match t with
  | .TVoid at_ => .TVoid (strip at_)
  | .TInt k at_ => .TInt k (strip at_)
  | .TFloat k at_ => .TFloat k (strip at_)
  | .TPtr t at_ => .TPtr t (strip at_)
  | .TArray t s at_ => .TArray t s (strip at_)
  | .TFun t arg v at_ => .TFun t arg v (strip at_)
  | .TNamed n at_ => .TNamed n (strip at_)
  | .TStruct n at_ => .TStruct n (strip at_)
  | .TUnion n at_ => .TUnion n (strip at_)
  | .TEnum n at_ => .TEnum n (strip at_)

/-- Remove the last attribute from the toplevel and return the changed type -/
def strip_last_attribute (typ : Typ) : Option Attribute × Typ :=
  let hd_opt : Attributes → Option Attribute × Attributes
    | [] => (none, [])
    | a :: rest => (some a, rest)
  match typ with
  | .TVoid at_ => let (l, r) := hd_opt at_; (l, .TVoid r)
  | .TInt k at_ => let (l, r) := hd_opt at_; (l, .TInt k r)
  | .TFloat k at_ => let (l, r) := hd_opt at_; (l, .TFloat k r)
  | .TPtr t at_ => let (l, r) := hd_opt at_; (l, .TPtr t r)
  | .TArray t s at_ => let (l, r) := hd_opt at_; (l, .TArray t s r)
  | .TFun t arg v at_ => let (l, r) := hd_opt at_; (l, .TFun t arg v r)
  | .TNamed n at_ => let (l, r) := hd_opt at_; (l, .TNamed n r)
  | .TStruct n at_ => let (l, r) := hd_opt at_; (l, .TStruct n r)
  | .TUnion n at_ => let (l, r) := hd_opt at_; (l, .TUnion n r)
  | .TEnum n at_ => let (l, r) := hd_opt at_; (l, .TEnum n r)

/-- Check whether the attributes contain `_Alignas` attribute -/
def has_std_alignas (env : Env.T) (typ : Typ) : M Bool := do
  return (← attributes_of_type env typ).any fun | .AAlignas _ => true | _ => false

/-- Extracting alignment value from a set of attributes.  Return 0 if none. -/
def alignas_attribute (al : Attributes) : Int :=
  al.foldl (fun accu a =>
    match a with
    | .AAlignas n => max n accu
    | .Attr "aligned" [.AInt n] | .Attr "__aligned__" [.AInt n] => max n.toInt accu
    | _ => accu) 0

/-- Extracting struct packing parameters from a set of attributes. -/
def packing_parameters (al : Attributes) : Int × Int × Bool :=
  match find_custom_attributes ["packed", "__packed__"] al with
  | [[]] => (1, 0, false)
  | [[.AInt n]] => (n.toInt, 0, false)
  | [[.AInt n, .AInt p]] => (n.toInt, p.toInt, false)
  | [[.AInt n, .AInt p, .AInt q]] => (n.toInt, p.toInt, q == 1)
  | _ => (0, 0, false)

/-! ### Type compatibility -/

def enum_ikind : IKind := .IInt

inductive AttrHandling where
  | AttrCompat
  | AttrIgnoreTop
  | AttrIgnoreAll
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Check that `t1` and `t2` are compatible and produce a type that combines
    the information in `t1` and `t2`. -/
partial def combine_types (mode : AttrHandling) (env : Env.T) (t1 t2 : Typ) :
    M (Option Typ) :=
  (comp mode t1 t2).run
where
  comp_attr (m : AttrHandling) (a1 a2 : Attributes) : OptionT M Attributes :=
    if a1 == a2 then pure a2 else
    match m with
    | .AttrCompat =>
        let (a1std, a1other) := a1.partition attr_is_standard
        let (a2std, a2other) := a2.partition attr_is_standard
        if a1std == a2std then pure (add_attributes a1std (add_attributes a1other a2other))
        else failure
    | .AttrIgnoreTop | .AttrIgnoreAll => pure (add_attributes a1 a2)
  comp_base {α} [BEq α] (x1 x2 : α) : OptionT M α :=
    if x1 == x2 then pure x2 else failure
  comp_array_size (sz1 sz2 : Option Int64) : OptionT M (Option Int64) :=
    match sz1, sz2 with
    | none, _ => pure sz2
    | _, none => pure sz1
    | some n1, some n2 => if n1 == n2 then pure (some n2) else failure
  comp_conv (p : Ident × Typ) : OptionT M Unit := do
    match ← (unroll env p.2 : M Typ) with
    | .TInt kind _ =>
        match kind with
        | .IBool | .IChar | .ISChar | .IUChar | .IShort | .IUShort => failure
        | _ => pure ()
    | .TFloat .FFloat _ => failure
    | _ => pure ()
  comp (m : AttrHandling) (t1 t2 : Typ) : OptionT M Typ := do
    match t1, t2 with
    | .TVoid a1, .TVoid a2 => return .TVoid (← comp_attr m a1 a2)
    | .TInt ik1 a1, .TInt ik2 a2 =>
        return .TInt (← comp_base ik1 ik2) (← comp_attr m a1 a2)
    | .TFloat fk1 a1, .TFloat fk2 a2 =>
        return .TFloat (← comp_base fk1 fk2) (← comp_attr m a1 a2)
    | .TPtr ty1 a1, .TPtr ty2 a2 =>
        let m' := if m == .AttrIgnoreTop then .AttrCompat else m
        return .TPtr (← comp m' ty1 ty2) (← comp_attr m a1 a2)
    | .TArray ty1 sz1 a1, .TArray ty2 sz2 a2 =>
        return .TArray (← comp m ty1 ty2) (← comp_array_size sz1 sz2) (← comp_attr m a1 a2)
    | .TFun ty1 params1 vararg1 a1, .TFun ty2 params2 vararg2 a2 =>
        let (params, vararg) ← (match params1, params2 with
          | none, none => pure (none, false)
          | none, some l2 => do l2.forM comp_conv; pure (params2, vararg2)
          | some l1, none => do l1.forM comp_conv; pure (params1, vararg1)
          | some l1, some l2 => do
              if l1.length != l2.length then failure
              let ps ← (l1.zip l2).mapM fun ((_, ty1), (id2, ty2)) => do
                return (id2, ← comp .AttrIgnoreTop ty1 ty2)
              pure (some ps, ← comp_base vararg1 vararg2) :
            OptionT M (Option (List (Ident × Typ)) × Bool))
        let m' := if m == .AttrIgnoreTop then .AttrCompat else m
        return .TFun (← comp m' ty1 ty2) params vararg (← comp_attr m a1 a2)
    | .TNamed .., _ => comp m (← (unroll env t1 : M Typ)) t2
    | _, .TNamed .. => comp m t1 (← (unroll env t2 : M Typ))
    | .TStruct s1 a1, .TStruct s2 a2 => return .TStruct (← comp_base s1 s2) (← comp_attr m a1 a2)
    | .TUnion s1 a1, .TUnion s2 a2 => return .TUnion (← comp_base s1 s2) (← comp_attr m a1 a2)
    | .TEnum s1 a1, .TEnum s2 a2 => return .TEnum (← comp_base s1 s2) (← comp_attr m a1 a2)
    | .TEnum s a1, .TInt ik a2 =>
        if ik == enum_ikind then return .TEnum s (← comp_attr m a1 a2) else failure
    | .TInt ik a2, .TEnum s a1 =>
        if ik == enum_ikind then return .TEnum s (← comp_attr m a1 a2) else failure
    | _, _ => failure

partial def equal_types (env : Env.T) (t1 t2 : Typ) : M Bool := do
  match t1, t2 with
  | .TVoid a1, .TVoid a2 => return a1 == a2
  | .TInt ik1 a1, .TInt ik2 a2 => return ik1 == ik2 && a1 == a2
  | .TFloat fk1 a1, .TFloat fk2 a2 => return fk1 == fk2 && a1 == a2
  | .TPtr ty1 a1, .TPtr ty2 a2 => return a1 == a2 && (← equal_types env ty1 ty2)
  | .TArray ty1 sz1 a1, .TArray ty2 sz2 a2 =>
      let size := match sz1, sz2 with
        | none, none => true
        | some s1, some s2 => s1 == s2
        | _, _ => false
      return size && a1 == a2 && (← equal_types env ty1 ty2)
  | .TFun ty1 params1 vararg1 a1, .TFun ty2 params2 vararg2 a2 =>
      let params ← match params1, params2 with
        | none, none => pure true
        | none, some _ | some _, none => pure false
        | some l1, some l2 =>
            if l1.length != l2.length then pure false
            else (l1.zip l2).allM fun ((_, t1), (_, t2)) => equal_types env t1 t2
      return params && a1 == a2 && vararg1 == vararg2 && (← equal_types env ty1 ty2)
  | .TNamed .., _ => equal_types env (← unroll env t1) t2
  | _, .TNamed .. => equal_types env t1 (← unroll env t2)
  | .TStruct s1 a1, .TStruct s2 a2 | .TUnion s1 a1, .TUnion s2 a2
  | .TEnum s1 a1, .TEnum s2 a2 => return s1 == s2 && a1 == a2
  | _, _ => return false

/-- Check whether two types are compatible. -/
def compatible_types (mode : AttrHandling) (env : Env.T) (t1 t2 : Typ) : M Bool := do
  return (← combine_types mode env t1 t2).isSome

/-! ### Sizes and alignments -/

/-- Natural alignment, in bytes -/
def alignof_ikind (ik : IKind) : M Int := do
  let c ← getConfig
  return match ik with
  | .IBool | .IChar | .ISChar | .IUChar => 1
  | .IInt | .IUInt => c.alignof_int
  | .IShort | .IUShort => c.alignof_short
  | .ILong | .IULong => c.alignof_long
  | .ILongLong | .IULongLong => c.alignof_longlong

def alignof_fkind (fk : FKind) : M Int := do
  let c ← getConfig
  return match fk with
  | .FFloat16 => 2
  | .FFloat => c.alignof_float
  | .FDouble => c.alignof_double
  | .FLongDouble => c.alignof_longdouble

/-- Return natural alignment of given type, or `none` if the type is
    incomplete -/
partial def alignof (env : Env.T) (t : Typ) : M (Option Int) := do
  let a := alignas_attribute (← attributes_of_type env t)
  if a > 0 then return some a
  let c ← getConfig
  match t with
  | .TVoid _ => return c.alignof_void
  | .TInt ik _ => return some (← alignof_ikind ik)
  | .TFloat fk _ => return some (← alignof_fkind fk)
  | .TPtr _ _ => return some c.alignof_ptr
  | .TArray ty _ _ => alignof env ty
  | .TFun .. => return c.alignof_fun
  | .TNamed _ _ => alignof env (← unroll env t)
  | .TStruct name _ => return (← Env.find_struct env name).ci_alignof
  | .TUnion name _ => return (← Env.find_union env name).ci_alignof
  | .TEnum _ _ => return some (← alignof_ikind enum_ikind)

/-- Compute the natural alignment of a struct or union. -/
def alignof_struct_union (env : Env.T) (members : List Field) : M (Option Int) := do
  let mut al : Int := 1
  for m in members do
    if m.fld_name == "" then continue
    match ← alignof env m.fld_typ with
    | none => return none
    | some a => al := max a al
  return some al

/-- `align x boundary` (boundary must be a power of 2) -/
def align (x boundary : Int) : Int :=
  (x + boundary - 1) / boundary * boundary

/-- Size of, in bytes -/
def sizeof_ikind (ik : IKind) : M Int := do
  let c ← getConfig
  return match ik with
  | .IBool | .IChar | .ISChar | .IUChar => 1
  | .IInt | .IUInt => c.sizeof_int
  | .IShort | .IUShort => c.sizeof_short
  | .ILong | .IULong => c.sizeof_long
  | .ILongLong | .IULongLong => c.sizeof_longlong

def sizeof_fkind (fk : FKind) : M Int := do
  let c ← getConfig
  return match fk with
  | .FFloat16 => 2
  | .FFloat => c.sizeof_float
  | .FDouble => c.sizeof_double
  | .FLongDouble => c.sizeof_longdouble

/-- OCaml's `max_int` (63-bit integers). -/
def max_int : Int := 2 ^ 62 - 1

/-- Overflow-avoiding multiplication of an int64 and an int, with result in
    type int. -/
def cautious_mul (a : Int64) (b : Int) : Option Int :=
  if b == 0 || a.toInt ≤ max_int / b then some (a.toInt * b) else none

/-- Return size of type, in bytes, or `none` if the type is incomplete -/
partial def sizeof (env : Env.T) (t : Typ) : M (Option Int) := do
  let c ← getConfig
  match t with
  | .TVoid _ => return c.sizeof_void
  | .TInt ik _ => return some (← sizeof_ikind ik)
  | .TFloat fk _ => return some (← sizeof_fkind fk)
  | .TPtr _ _ => return some c.sizeof_ptr
  | .TArray _ none _ => return none
  | .TArray ty (some n) _ =>
      match ← sizeof env ty with
      | none => return none
      | some s =>
        match cautious_mul n s with
        | some sz => return some sz
        | none =>
            error no_loc s!"sizeof({Cprint.toText (Cprint.typ {} t)}) overflows"
            return some 1
  | .TFun .. => return c.sizeof_fun
  | .TNamed _ _ => sizeof env (← unroll env t)
  | .TStruct name _ => return (← Env.find_struct env name).ci_sizeof
  | .TUnion name _ => return (← Env.find_union env name).ci_sizeof
  | .TEnum _ _ => return some (← sizeof_ikind enum_ikind)

/-- Compute the size of a union (max of the sizes of fields). -/
def sizeof_union (env : Env.T) (members : List Field) : M (Option Int) := do
  let mut sz : Int := 0
  for m in members do
    match ← sizeof env m.fld_typ with
    | none => return none
    | some s => sz := max sz s
  return some sz

/-- Compute the size (in bits) of a struct and the byte offset of the
    members (most recent first).  `ma` is the maximal alignment for each
    member (0: ignored). -/
def sizeof_layout_struct (env : Env.T) (members : List Field) (ma : Int) :
    M (Option (Int × List (String × Int))) := do
  let align_bit_offset (pos a : Int) : Int :=
    align pos (8 * (if ma > 0 && a > ma then ma else a))
  let record_field (name : String) (pos : Int) : M (String × Int) := do
    if pos % 8 != 0 then assertFalse "Cutil.sizeof_layout_struct"
    return (name, pos / 8)
  let rec sizeof_rec (pos : Int) (accu : List (String × Int)) :
      List Field → M (Option (Int × List (String × Int)))
    | [] => return some (pos, accu)
    | [m@{ fld_typ := .TArray _ none _, .. }] => do
        match ← alignof env m.fld_typ with
        | some a =>
            let pos := align_bit_offset pos a
            return some (pos, (← record_field m.fld_name pos) :: accu)
        | none => return none
    | m :: rem => do
        match ← alignof env m.fld_typ, ← sizeof env m.fld_typ with
        | some a, some s =>
            match m.fld_bitfield with
            | none =>
                let pos := align_bit_offset pos a
                sizeof_rec (pos + s * 8) ((← record_field m.fld_name pos) :: accu) rem
            | some width =>
                if alignas_attribute (← attributes_of_type env m.fld_typ) != 0 then
                  assertFalse "Cutil.sizeof_layout_struct (bitfield)"
                let curr := pos / (a * 8) * (a * 8)
                let next := curr + s * 8
                let pos' :=
                  if width ≤ 0 then align pos (a * 8)
                  else if pos + width ≤ next then pos + width
                  else next + width
                sizeof_rec pos' accu rem
        | _, _ => return none
  sizeof_rec 0 [] members

def sizeof_struct (env : Env.T) (members : List Field) (ma : Int) : M (Option Int) := do
  match ← sizeof_layout_struct env members ma with
  | none => return none
  | some (bitsize, _) => return some ((bitsize + 7) / 8)

/-- Compute the offsets of all non-bitfield members of a struct. -/
def struct_layout (env : Env.T) (attrs : Attributes) (members : List Field) :
    M (List (String × Int)) := do
  let (ma, _, _) := packing_parameters attrs
  match ← sizeof_layout_struct env members ma with
  | some (_, offsets) => return offsets
  | none => return []

/-- Compute the offset of a struct member -/
def offsetof (env : Env.T) (ty : Typ) (field : Field) : M Int := do
  match ← unroll env ty with
  | .TStruct id _ =>
      let str ← Env.find_struct env id
      let offsets ← struct_layout env str.ci_attr str.ci_members
      match offsets.lookup field.fld_name with
      | some o => return o
      | none => throw (.EnvError (.No_member id.name "struct" field.fld_name))
  | .TUnion .. => return 0
  | _ => assertFalse "Cutil.offsetof"

/-- Determine whether a type is incomplete -/
def incomplete_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TVoid _ => return true
  | _ => return (← sizeof env t).isNone

/-! Computing composite_info records -/

def composite_info_decl (su : StructOrUnion) (attr : Attributes) : CompositeInfo :=
  { ci_kind := su, ci_members := [], ci_alignof := none, ci_sizeof := none,
    ci_attr := attr }

def composite_info_def (env : Env.T) (su : StructOrUnion) (attr : Attributes)
    (m : List Field) : M CompositeInfo := do
  let (max_field_align, min_struct_align, _) := packing_parameters attr
  let attr_align := alignas_attribute attr
  let natural_align ← alignof_struct_union env m
  let al :=
    if attr_align > 0 then some attr_align
    else if su == .Union then natural_align
    else match natural_align with
      | none => none
      | some a =>
          let a := if max_field_align > 0 && a > max_field_align then max_field_align else a
          let a := if min_struct_align > 0 && a < min_struct_align then min_struct_align else a
          some a
  let sz ← match su with
    | .Struct => sizeof_struct env m max_field_align
    | .Union => sizeof_union env m
  return { ci_kind := su, ci_members := m, ci_alignof := al,
           ci_sizeof := match sz, al with
             | some s, some a => some (align s a)
             | _, _ => none,
           ci_attr := attr }

/-- Is an integer `v` representable in `n` bits, signed or unsigned? -/
def int_representable (v : Int64) (nbits : Int) (sgn : Bool) : Bool :=
  if nbits ≥ 64 then true else
  if sgn then
    let p : Int64 := (1 : Int64) <<< (Int64.ofInt (nbits - 1)); Int64.neg p ≤ v && v < p
  else
    0 ≤ v && v < (1 : Int64) <<< (Int64.ofInt nbits)

def valid_array_size (env : Env.T) (ty : Typ) (v : Int64) : M Bool := do
  match ← sizeof env ty with
  | none => return true
  | some sz =>
      let sz := Int64.ofInt sz
      let ptr_bits := (← getConfig).sizeof_ptr * 8 - 1
      if sz == 0 || v ≤ Int64.maxValue / sz then
        return int_representable (sz * v) ptr_bits true
      else return false

/-- Type of a function definition -/
def fundef_typ (fd : Fundef) : Typ :=
  .TFun fd.fd_ret (some fd.fd_params) fd.fd_vararg fd.fd_attrib

/-- Signedness of integer kinds -/
def is_signed_ikind (ik : IKind) : M Bool := do
  match ik with
  | .IBool => return false
  | .IChar => return (← getConfig).char_signed
  | .ISChar => return true
  | .IUChar => return false
  | .IInt => return true
  | .IUInt => return false
  | .IShort => return true
  | .IUShort => return false
  | .ILong => return true
  | .IULong => return false
  | .ILongLong => return true
  | .IULongLong => return false

/-- Conversion to unsigned ikind -/
def unsigned_ikind_of : IKind → IKind
  | .IBool => .IBool
  | .IChar | .ISChar | .IUChar => .IUChar
  | .IInt | .IUInt => .IUInt
  | .IShort | .IUShort => .IUShort
  | .ILong | .IULong => .IULong
  | .ILongLong | .IULongLong => .IULongLong

/-- Conversion to signed ikind -/
def signed_ikind_of : IKind → IKind
  | .IBool => .IBool
  | .IChar | .ISChar | .IUChar => .ISChar
  | .IInt | .IUInt => .IInt
  | .IShort | .IUShort => .IShort
  | .ILong | .IULong => .ILong
  | .ILongLong | .IULongLong => .ILongLong

end Cutil
end CParser
end CC
