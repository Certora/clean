/-
  Port of `cparser/PackedStructs.ml`: emulation of `#pragma pack` and of
  byte-swapped struct fields (experimental).  Assumes and preserves
  unblocked code.

  The global table `byteswapped_fields` and the flag `use_reversed` are
  threaded explicitly: the composite rewriting returns the new byte-swapped
  fields, and the expression, statement and initializer rewritings receive
  the table (`PS`) as an argument.
-/
import CCLib.cparser.Transform
import CCLib.cparser.Ceval

namespace CC
namespace CParser
namespace PackedStructs

open C Cutil Diagnostics Transform

/-- The set of struct fields that are byte-swapped, identified by (struct
    name, field name), and whether `__builtin_*_reversed` is used. -/
structure PS where
  byteswapped_fields : List (Ident × String) := []
  use_reversed : Bool := false
  deriving Inhabited

def PS.mem (ps : PS) (id : Ident) (f : String) : Bool :=
  ps.byteswapped_fields.any fun (i, g) => i == id && g == f

/-- What are the types that can be byte-swapped? (can swap, must swap) -/
partial def can_byte_swap (env : Env.T) (ty : Typ) : M (Bool × Bool) := do
  match ← unroll env ty with
  | .TInt ik _ =>
      let s ← sizeof_ikind ik
      return (s ≤ (← getConfig).sizeof_intreg, s > 1)
  | .TEnum .. => return (true, (← sizeof_ikind enum_ikind) > 1)
  | .TPtr .. => return (true, true)
  | .TArray ty_elt _ _ => can_byte_swap env ty_elt
  | _ => return (false, false)

/-- "Safe" `alignof` function, with detection of incomplete types. -/
def safe_alignof (loc : Location) (env : Env.T) (ty : Typ) : M Int := do
  match ← alignof env ty with
  | some al => return al
  | none => error loc "incomplete type for a struct field"; return 1

def remove_alignas_attr (attrs : Attributes) : Attributes :=
  attrs.filter fun | .AAlignas _ => false | _ => true

def set_alignas_attr (al : Int) (attrs : Attributes) : Attributes :=
  add_attributes [.AAlignas al] (remove_alignas_attr attrs)

/-- Rewriting field declarations; also returns the field to register as
    byte-swapped, if any. -/
def transf_field_decl (mfa : Int) (swapped : Bool) (loc : Location) (env : Env.T)
    (struct_id : Ident) (f : Field) : M (Field × Option (Ident × String)) := do
  let mut reg := none
  if swapped then
    if f.fld_bitfield.isSome then error loc "byte-swapped bit fields are not supported"
    let (can_swap, must_swap) ← can_byte_swap env f.fld_typ
    if !can_swap then
      fatal_error loc s!"cannot byte-swap field of type '{Cprint.toText (Cprint.typ {} f.fld_typ)}'"
    if must_swap then reg := some (struct_id, f.fld_name)
  if mfa == 0 then return (f, reg)
  if f.fld_bitfield.isSome then
    error loc "bit fields in packed structs are not supported"
    return (f, reg)
  let al ← safe_alignof loc env f.fld_typ
  return ({ f with fld_typ := ← change_attributes_type env (set_alignas_attr (min mfa al)) f.fld_typ },
          reg)

/-- Rewriting struct declarations -/
def transf_struct_decl (mfa msa : Int) (swapped : Bool) (loc : Location) (env : Env.T)
    (struct_id : Ident) (attrs : Attributes) (ml : List Field) :
    M ((Attributes × List Field) × List (Ident × String)) := do
  let attrs' := remove_custom_attributes ["packed", "__packed__"] attrs
  let res ← ml.mapM (transf_field_decl mfa swapped loc env struct_id)
  let ml' := res.map (·.1)
  let regs := res.filterMap (·.2)
  if msa == 0 then return ((attrs', ml'), regs)
  let ci ← composite_info_def env .Struct attrs ml
  match ci.ci_alignof with
  | none => error loc "incomplete struct"; return ((attrs', ml'), regs)
  | some al => return ((set_alignas_attr al attrs', ml'), regs)

/-- Rewriting composite declarations -/
def transf_composite (loc : Location) (env : Env.T) (su : StructOrUnion) (id : Ident)
    (attrs : Attributes) (ml : List Field) :
    M ((Attributes × List Field) × List (Ident × String)) := do
  match su with
  | .Union => return ((attrs, ml), [])
  | .Struct =>
      let (mfa, msa, swapped) ← match find_custom_attributes ["packed", "__packed__"] attrs with
        | [] => pure (0, 0, false)
        | [_] => pure (packing_parameters attrs)
        | _ => do error loc "multiple __packed__ attributes"; pure (0, 0, false)
      transf_struct_decl mfa msa swapped loc env id attrs ml

/-! Accessor functions -/

def lookup_function (env : Env.T) (name : String) : M (Ident × Typ) := do
  match ← Env.lookup_ident env name with
  | (id, .II_ident _ ty) => return (id, ty)
  | (_, .II_enum _) => throw (.EnvError (.Unbound_identifier name))

/-- Type for the access -/
def accessor_type (loc : Location) (env : Env.T) (ty : Typ) : M (Int × Typ) := do
  match ← unroll env ty with
  | .TInt ik _ => return (8 * (← sizeof_ikind ik), .TInt (unsigned_ikind_of ik) [])
  | .TEnum .. => return (8 * (← sizeof_ikind enum_ikind), .TInt (unsigned_ikind_of enum_ikind) [])
  | .TPtr .. => return (8 * (← getConfig).sizeof_ptr, .TInt (← ptr_t_ikind) [])
  | _ =>
      error loc "unsupported type for byte-swapped field access"
      return (32, .TVoid [])

def ecast_opt (env : Env.T) (ty : Typ) (e : Exp) : M Exp := do
  if ← compatible_types .AttrCompat env ty e.etyp then return e else return ecast ty e

private def check_bsize (bsize : Int) : M Unit := do
  if !(bsize == 16 || bsize == 32 || (bsize == 64 && (← getConfig).sizeof_intreg == 8)) then
    assertFalse "PackedStructs: access size"

private def withEnvErrorFatal {α} (loc : Location) (x : M α) : M α :=
  tryCatch x fun
    | .EnvError msg => fatal_error loc (Env.error_message msg)
    | e => throw e

/-- `(ty) __builtin_readNN_reversed(&lval)` or `(ty) __builtin_bswapNN(lval)` -/
def bswap_read (ps : PS) (loc : Location) (env : Env.T) (lval : Exp) : M Exp := do
  let ty := lval.etyp
  let (bsize, aty) ← accessor_type loc env ty
  check_bsize bsize
  withEnvErrorFatal loc do
    if ps.use_reversed then
      let (id, fty) ← lookup_function env s!"__builtin_read{bsize}_reversed"
      let fn : Exp := .mk (.EVar id) fty
      let args := [← ecast_opt env (.TPtr aty []) (eaddrof lval)]
      ecast_opt env ty (.mk (.ECall fn args) aty)
    else
      let (id, fty) ← lookup_function env s!"__builtin_bswap{bsize}"
      let fn : Exp := .mk (.EVar id) fty
      let args := [← ecast_opt env aty lval]
      ecast_opt env ty (.mk (.ECall fn args) aty)

/-- `__builtin_write_intNN_reversed(&lhs,rhs)` or `lhs = __builtin_bswapNN(rhs)` -/
def bswap_write (ps : PS) (loc : Location) (env : Env.T) (lhs rhs : Exp) : M Exp := do
  let ty := lhs.etyp
  let (bsize, aty) ← accessor_type loc env ty
  check_bsize bsize
  withEnvErrorFatal loc do
    if ps.use_reversed then
      let (id, fty) ← lookup_function env s!"__builtin_write{bsize}_reversed"
      let fn : Exp := .mk (.EVar id) fty
      let args := [← ecast_opt env (.TPtr aty []) (eaddrof lhs), ← ecast_opt env aty rhs]
      return .mk (.ECall fn args) (.TVoid [])
    else
      let (id, fty) ← lookup_function env s!"__builtin_bswap{bsize}"
      let fn : Exp := .mk (.EVar id) fty
      let args := [← ecast_opt env aty rhs]
      return eassign lhs (← ecast_opt env ty (.mk (.ECall fn args) aty))

/-- Expressions -/
partial def transf_expr (ps : PS) (loc : Location) (env : Env.T) (ctx : Context) (e : Exp) :
    M Exp :=
  texp ctx e
where
  is_byteswapped (ty : Typ) (fieldname : String) : M Bool := do
    match ← unroll env ty with
    | .TStruct id _ => return ps.mem id fieldname
    | _ => return false
  is_byteswapped_ptr (ty : Typ) (fieldname : String) : M Bool := do
    match ← unroll env ty with
    | .TPtr ty' _ => is_byteswapped ty' fieldname
    | _ => return false
  lvalue (e : Exp) : M (Exp × Bool) := do
    match e.edesc with
    | .EUnop (.Odot fieldname) e1 =>
        return (.mk (.EUnop (.Odot fieldname) (← texp .Val e1)) e.etyp,
                ← is_byteswapped e1.etyp fieldname)
    | .EUnop (.Oarrow fieldname) e1 =>
        return (.mk (.EUnop (.Oarrow fieldname) (← texp .Val e1)) e.etyp,
                ← is_byteswapped_ptr e1.etyp fieldname)
    | .EBinop .Oindex e1 e2 tyres =>
        let (e1', swap) ← lvalue e1
        return (.mk (.EBinop .Oindex e1' e2 tyres) e.etyp, swap)
    | _ => return (← texp .Val e, false)
  texp (ctx : Context) (e : Exp) : M Exp := do
    let rd := bswap_read ps loc env
    let wr := bswap_write ps loc env
    match e.edesc with
    | .EConst _ | .ESizeof _ | .EAlignof _ | .EVar _ => return e
    | .EUnop (.Odot _) _ | .EUnop (.Oarrow _) _ | .EBinop .Oindex _ _ _ =>
        let (e', swap) ← lvalue e
        if swap then rd e' else return e'
    | .EUnop .Oaddrof e1 =>
        let (e1', swap) ← lvalue e1
        if swap then error loc "& over byte-swapped field"
        return .mk (.EUnop .Oaddrof e1') e.etyp
    | .EUnop op@.Opreincr e1 | .EUnop op@.Opredecr e1 =>
        let (e1', swap) ← lvalue e1
        if swap then expand_preincrdecr rd wr env ctx op e1'
        else return .mk (.EUnop op e1') e.etyp
    | .EUnop op@.Opostincr e1 | .EUnop op@.Opostdecr e1 =>
        let (e1', swap) ← lvalue e1
        if swap then expand_postincrdecr rd wr env ctx op e1'
        else return .mk (.EUnop op e1') e.etyp
    | .EUnop op e1 => return .mk (.EUnop op (← texp .Val e1)) e.etyp
    | .EBinop .Oassign e1 e2 ty =>
        let (e1', swap) ← lvalue e1
        let e2' ← texp .Val e2
        if swap then expand_assign wr env ctx e1' e2'
        else return .mk (.EBinop .Oassign e1' e2' ty) e.etyp
    | .EBinop op e1 e2 ty =>
        match op with
        | .Oadd_assign | .Osub_assign | .Omul_assign | .Odiv_assign | .Omod_assign
        | .Oand_assign | .Oor_assign | .Oxor_assign | .Oshl_assign | .Oshr_assign =>
            let (e1', swap) ← lvalue e1
            let e2' ← texp .Val e2
            if swap then expand_assignop rd wr env ctx op e1' e2' ty
            else return .mk (.EBinop op e1' e2' ty) e.etyp
        | .Ocomma =>
            return .mk (.EBinop .Ocomma (← texp .Effects e1) (← texp .Val e2) ty) e.etyp
        | _ => return .mk (.EBinop op (← texp .Val e1) (← texp .Val e2) ty) e.etyp
    | .EConditional e1 e2 e3 =>
        return .mk (.EConditional (← texp .Val e1) (← texp ctx e2) (← texp ctx e3)) e.etyp
    | .ECast ty e1 => return .mk (.ECast ty (← texp .Val e1)) e.etyp
    | .ECompound .. => assertFalse "PackedStructs.transf_expr (compound literal)"
    | .ECall e1 el => return .mk (.ECall (← texp .Val e1) (← el.mapM (texp .Val))) e.etyp

/-- Statements -/
def transf_stmt (ps : PS) (env : Env.T) (s : Stmt) : M Stmt :=
  Transform.stmt (transf_expr ps) (env := env) (s := s)

/-- Functions -/
def transf_fundef (ps : PS) (env : Env.T) (f : Fundef) : M Fundef :=
  Transform.fundef (transf_stmt ps) env f

/-! Initializers -/

def extract_byte (n : Int64) (i : Nat) : Int64 :=
  (n.toUInt64 >>> (i * 8).toUInt64).toInt64 &&& 0xFF

def byteswap_int (nbytes : Int) (n : Int64) : Int64 := Id.run do
  let mut res : Int64 := 0
  for i in [0:nbytes.toNat] do
    res := (res <<< 8) ||| extract_byte n i
  return res

partial def transf_init (ps : PS) (loc : Location) (env : Env.T) (i : Init) : M Init :=
  trinit none i
where
  trinit (swap : Option Typ) (i : Init) : M Init := do
    match i with
    | .Init_single e =>
        match swap with
        | none => return i
        | some ty =>
            match ← Ceval.constant_expr env ty e with
            | some (.CInt n ik _) =>
                let n' := byteswap_int (← sizeof_ikind ik) n
                return .Init_single (.mk (.EConst (.CInt n' ik "")) e.etyp)
            | _ =>
                error loc ("initializer for byte-swapped field is not " ++
                           "a compile-time integer constant")
                return i
    | .Init_array il =>
        let swap_elt ← match swap with
          | none => pure none
          | some ty => do
              match ← unroll env ty with
              | .TArray ty_elt _ _ => pure (some ty_elt)
              | _ => assertFalse "PackedStructs.transf_init"
        return .Init_array (← il.mapM (trinit swap_elt))
    | .Init_struct id fld_init_list =>
        return .Init_struct id (← fld_init_list.mapM fun (f, i) => do
          let swap_f := if ps.mem id f.fld_name then some f.fld_typ else none
          return (f, ← trinit swap_f i))
    | .Init_union id fld i => return .Init_union id fld (← trinit none i)

/-- Declarations -/
def transf_decl (ps : PS) (loc : Location) (env : Env.T) : Decl → M Decl
  | .mk sto id ty init_opt => do
      match init_opt with
      | none => return .mk sto id ty none
      | some i => return .mk sto id ty (some (← transf_init ps loc env i))

/-- Global declarations -/
def transf_globdecls (ps0 : PS) (env0 : Env.T) (p : List Globdecl) : M (List Globdecl) := do
  let mut env := env0
  let mut ps := ps0
  let mut accu : Array Globdecl := #[]
  for g in p do
    match g.gdesc with
    | .Gdecl d@(.mk sto id ty _) =>
        accu := accu.push { g with gdesc := .Gdecl (← transf_decl ps g.gloc env d) }
        env := Env.add_ident env id sto ty
    | .Gfundef f =>
        accu := accu.push { g with gdesc := .Gfundef (← transf_fundef ps env f) }
        env := Env.add_ident env f.fd_name f.fd_storage (fundef_typ f)
    | .Gcompositedecl su id attr =>
        let attr' := match su with
          | .Union => attr
          | .Struct => remove_custom_attributes ["packed", "__packed__"] attr
        env := Env.add_composite env id (composite_info_decl su attr')
        accu := accu.push { g with gdesc := .Gcompositedecl su id attr' }
    | .Gcompositedef su id attr fl =>
        let ((attr', fl'), regs) ← transf_composite g.gloc env su id attr fl
        ps := { ps with byteswapped_fields := regs.reverse ++ ps.byteswapped_fields }
        env := Env.add_composite env id (← composite_info_def env su attr' fl')
        accu := accu.push { g with gdesc := .Gcompositedef su id attr' fl' }
    | .Gtypedef id ty =>
        env := Env.add_typedef env id ty
        accu := accu.push g
    | .Genumdef id attr el =>
        env := Env.add_enum env id { ei_members := el, ei_attr := attr }
        accu := accu.push g
    | .Gpragma _ => accu := accu.push g
  return accu.toList

/-- Program.  `env0` is `Env.initial ()`. -/
def program (env0 : Env.T) (p : Program) : M Program := do
  let use_reversed := (← getConfig).name == "powerpc"
  transf_globdecls { use_reversed } env0 p

end PackedStructs
end CParser
end CC
