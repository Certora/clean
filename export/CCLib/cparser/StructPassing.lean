/-
  Port of `cparser/StructPassing.ml`: eliminate structs and unions that are
  returned by value as function results or passed by value as function
  parameters, according to the ABI's struct passing and returning styles.

  * The global references `struct_return_style` and `struct_passing_style`
    are the argument `sty : Styles`; `program` computes it from the machine
    configuration and `Clflags.option_interp` (argument `option_interp`).
  * Where OCaml evaluates several subexpressions in an unspecified order
    (constructor and function arguments), this port evaluates them left to
    right.  This can only change the stamps of the fresh temporaries, not
    the result of the transformation up to renaming.
-/
import CCLib.cparser.Transform

namespace CC
namespace CParser
namespace StructPassing

open C Cutil Transform Machine

structure Styles where
  passing : StructPassingStyle := .SP_ref_callee
  ret : StructReturnStyle := .SR_ref
  deriving Inhabited

/-- Classification of function return types. -/
inductive ReturnKind where
  /-- a scalar type, returned as usual -/
  | Ret_scalar
  /-- a composite type, returned by reference -/
  | Ret_ref
  /-- a small composite type, returned as an integer (type, size, alignment) -/
  | Ret_value (ty : Typ) (sz al : Int)

def classify_return (sty : Styles) (env : Env.T) (ty : Typ) : M ReturnKind := do
  if ← is_composite_type env ty then
    match ← sizeof env ty, ← alignof env ty with
    | some sz, some al =>
        match sty.ret with
        | .SR_int1248 =>
            if sz == 1 || sz == 2 || sz == 4 then return .Ret_value (.TInt .IUInt []) sz al
            else if sz == 8 then return .Ret_value (.TInt .IULongLong []) sz al
            else return .Ret_ref
        | .SR_int1to4 =>
            if sz ≤ 4 then return .Ret_value (.TInt .IUInt []) sz al else return .Ret_ref
        | .SR_int1to8 =>
            if sz ≤ 4 then return .Ret_value (.TInt .IUInt []) sz al
            else if sz > 4 && sz ≤ 8 then return .Ret_value (.TInt .IULongLong []) sz al
            else return .Ret_ref
        | .SR_ref => return .Ret_ref
    | _, _ => return .Ret_ref
  else return .Ret_scalar

/-- Classification of function parameter types. -/
inductive ParamKind where
  /-- passed as is -/
  | Param_unchanged
  /-- passed by reference to a copy taken by the caller -/
  | Param_ref_caller
  /-- passed as N integer arguments (N, size, alignment) -/
  | Param_flattened (n sz al : Int)

def classify_param (sty : Styles) (env : Env.T) (ty : Typ) : M ParamKind := do
  if ← is_composite_type env ty then
    match sty.passing with
    | .SP_ref_callee => return .Param_unchanged
    | .SP_ref_caller => return .Param_ref_caller
    | _ =>
      match ← sizeof env ty, ← alignof env ty with
      | some sz, some al => return .Param_flattened ((sz + 3) / 4) sz al
      | _, _ => return .Param_unchanged
  else return .Param_unchanged

/-- Return the list `[f 0; f 1; ...; f (n-1)]` -/
def list_map_n {α} (f : Int → α) (n : Int) : List α :=
  (List.range n.toNat).map fun (i : Nat) => f i

def list_map_nM {α} (f : Int → M α) (n : Int) : M (List α) :=
  (List.range n.toNat).mapM fun (i : Nat) => f i

/-! Declaring and accessing buffers (arrays of int) -/

def uchar : Typ := .TInt .IUChar []
def ushort : Typ := .TInt .IUShort []
def uint : Typ := .TInt .IUInt []
def ulonglong : Typ := .TInt .IULongLong []
def ucharptr : Typ := .TPtr uchar []
def ushortptr : Typ := .TPtr ushort []
def uintptr : Typ := .TPtr uint []
def ulonglongptr : Typ := .TPtr ulonglong []

def ty_buffer (n : Int) : Typ := .TArray uint (some (Int64.ofInt n)) []

def ebuffer_index (base : Exp) (idx : Int) : Exp :=
  .mk (.EBinop .Oindex base (intconst (Int64.ofInt idx) .IInt) uintptr) uint

def attr_structret : Attributes := [.Attr "__structreturn" []]

/-! Expression constructor functions -/

def ereinterpret (ty : Typ) (e : Exp) : Exp :=
  .mk (.EUnop .Oderef (ecast (.TPtr ty []) (eaddrof e))) ty

def or2 (a b : Exp) : Exp := .mk (.EBinop .Oor a b uint) uint
def or3 (a b c : Exp) : Exp := or2 (or2 a b) c
def or4 (a b c d : Exp) : Exp := or2 (or2 (or2 a b) c) d

def lshift (a : Exp) (nbytes : Int) : Exp :=
  if nbytes == 0 then a else
  .mk (.EBinop .Oshl a (intconst (Int64.ofInt (nbytes * 8)) .IInt) uint) uint

def offsetptr (base : Exp) (ofs : Int) : Exp :=
  if ofs == 0 then base else
  .mk (.EBinop .Oadd base (intconst (Int64.ofInt ofs) .IInt) ucharptr) ucharptr

def load1 (cfg : Machine.T) (base : Exp) (ofs shift_le shift_be : Int) : Exp :=
  let shift := if cfg.bigendian then shift_be else shift_le
  lshift (.mk (.EUnop .Oderef (offsetptr base ofs)) uchar) shift

def load2 (cfg : Machine.T) (base : Exp) (ofs shift_le shift_be : Int) : Exp :=
  let shift := if cfg.bigendian then shift_be else shift_le
  lshift (.mk (.EUnop .Oderef (ecast ushortptr (offsetptr base ofs))) ushort) shift

def load4 (base : Exp) (ofs : Int) : Exp :=
  .mk (.EUnop .Oderef (ecast uintptr (offsetptr base ofs))) uint

def load8 (base : Exp) (ofs : Int) : Exp :=
  .mk (.EUnop .Oderef (ecast ulonglongptr (offsetptr base ofs))) ulonglong

def lshift_ll (a : Exp) (nbytes : Int) : Exp :=
  let a := ecast ulonglong a
  if nbytes == 0 then a else
  .mk (.EBinop .Oshl a (intconst (Int64.ofInt (nbytes * 8)) .IInt) ulonglong) ulonglong

def or2_ll (a b : Exp) : Exp := .mk (.EBinop .Oor a b uint) ulonglong

/-- Loading a memory area as one or several integers. -/
def load_word (base : Exp) (ofs sz al : Int) : M Exp := do
  let cfg ← getConfig
  let ua := cfg.supports_unaligned_accesses
  match sz with
  | 0 => return intconst 0 .IInt
  | 1 => return load1 cfg base ofs 0 3
  | 2 =>
      if al ≥ 2 || ua then return load2 cfg base ofs 0 2
      else return or2 (load1 cfg base ofs 0 3) (load1 cfg base (ofs + 1) 1 2)
  | 3 =>
      if al ≥ 2 || ua then return or2 (load2 cfg base ofs 0 2) (load1 cfg base (ofs + 2) 2 1)
      else return (or3 (load1 cfg base ofs 0 3) (load1 cfg base (ofs + 1) 1 2)
          (load1 cfg base (ofs + 2) 2 1))
  | 4 =>
      if al ≥ 4 || ua then return load4 base ofs
      else if al ≥ 2 then return or2 (load2 cfg base ofs 0 2) (load2 cfg base (ofs + 2) 2 0)
      else return (or4 (load1 cfg base ofs 0 3) (load1 cfg base (ofs + 1) 1 2)
          (load1 cfg base (ofs + 2) 2 1) (load1 cfg base (ofs + 3) 3 0))
  | _ => assertFalse "StructPassing.load_word"

partial def load_words (base : Exp) (ofs sz al : Int) : M (List Exp) := do
  if ofs ≥ sz then return []
  else if ofs + 4 ≥ sz then return [← load_word base ofs (sz - ofs) al]
  else return (← load_word base ofs 4 al) :: (← load_words base (ofs + 4) sz al)

def load_result (base : Exp) (sz al : Int) : M Exp := do
  if sz > 8 then assertFalse "StructPassing.load_result"
  let cfg ← getConfig
  if sz ≤ 4 then load_word base 0 sz al
  else if sz == 8 && (al ≥ 8 || cfg.supports_unaligned_accesses) then return load8 base 0
  else
    let (shift1, shift2) := if cfg.bigendian then (4, 0) else (0, 4)
    return or2_ll (lshift_ll (← load_word base 0 4 al) shift1)
      (lshift_ll (← load_word base 4 (sz - 4) al) shift2)

mutual
/-- Rewriting of function types. -/
partial def transf_type (sty : Styles) (env : Env.T) (t : Typ) : M Typ := do
  match ← unroll env t with
  | .TFun tres none vararg attr =>
      let tres' ← transf_type sty env tres
      match ← classify_return sty env tres with
      | .Ret_scalar => return .TFun tres' none vararg attr
      | .Ret_ref => return .TFun (.TVoid []) none vararg (add_attributes attr attr_structret)
      | .Ret_value ty _ _ => return .TFun ty none vararg attr
  | .TFun tres (some args) vararg attr =>
      let args' ← transf_funargs sty env args
      let tres' ← transf_type sty env tres
      match ← classify_return sty env tres with
      | .Ret_scalar => return .TFun tres' (some args') vararg attr
      | .Ret_ref =>
          let res ← Env.fresh_ident "_res"
          return .TFun (.TVoid []) (some ((res, .TPtr tres' []) :: args')) vararg
            (add_attributes attr attr_structret)
      | .Ret_value ty _ _ => return .TFun ty (some args') vararg attr
  | .TPtr t1 attr =>
      let t1' ← transf_type sty env t1
      if t1' == t1 then return t else return .TPtr (← transf_type sty env t1) attr
  | .TArray t1 sz attr =>
      let t1' ← transf_type sty env t1
      if t1' == t1 then return t else return .TArray (← transf_type sty env t1) sz attr
  | _ => return t

partial def transf_funargs (sty : Styles) (env : Env.T) :
    List (Ident × Typ) → M (List (Ident × Typ))
  | [] => return []
  | (id, t) :: args => do
      let t' ← transf_type sty env t
      let args' ← transf_funargs sty env args
      match ← classify_param sty env t with
      | .Param_unchanged => return (id, t') :: args'
      | .Param_ref_caller => return (id, .TPtr t' []) :: args'
      | .Param_flattened n _ _ =>
          return (← list_map_nM (fun _ => do return (← Env.fresh_ident id.name, uint)) n) ++ args'
end

/-! Expressions: transform calls + rewrite the types -/

partial def translates_to_extended_lvalue (arg : Exp) : Bool :=
  is_lvalue arg ||
  match arg.edesc with
  | .ECall .. => true
  | .EBinop .Ocomma _ b _ => translates_to_extended_lvalue b
  | _ => false

mutual
partial def transf_expr (sty : Styles) (env : Env.T) (ctx : Context) (e : Exp) : M Exp := do
  let newty ← transf_type sty env e.etyp
  match e.edesc with
  | .EConst c => return .mk (.EConst c) newty
  | .ESizeof ty => return .mk (.ESizeof (← transf_type sty env ty)) newty
  | .EAlignof ty => return .mk (.EAlignof (← transf_type sty env ty)) newty
  | .EVar x => return .mk (.EVar x) newty
  | .EUnop op e1 => return .mk (.EUnop op (← transf_expr sty env .Val e1)) newty
  | .EBinop .Oassign lhs (.mk (.ECall fn args) ty) _ =>
      transf_call sty env ctx (some (← transf_expr sty env .Val lhs)) fn args ty
  | .EBinop .Ocomma e1 e2 _ =>
      return ecomma (← transf_expr sty env .Effects e1) (← transf_expr sty env ctx e2)
  | .EBinop op e1 e2 ty =>
      return .mk (.EBinop op (← transf_expr sty env .Val e1) (← transf_expr sty env .Val e2)
        (← transf_type sty env ty)) newty
  | .EConditional e1 e2 e3 =>
      return .mk (.EConditional (← transf_expr sty env .Val e1) (← transf_expr sty env ctx e2)
        (← transf_expr sty env ctx e3)) newty
  | .ECast ty e1 =>
      return .mk (.ECast (← transf_type sty env ty) (← transf_expr sty env .Val e1)) newty
  | .ECompound ty ie =>
      return .mk (.ECompound (← transf_type sty env ty) (← transf_init sty env ie)) newty
  | .ECall fn args => transf_call sty env ctx none fn args e.etyp

/-- Function calls returning a composite by reference or by value. -/
partial def transf_call (sty : Styles) (env : Env.T) (ctx : Context) (opt_lhs : Option Exp)
    (fn : Exp) (args : List Exp) (ty : Typ) : M Exp := do
  let ty' ← transf_type sty env ty
  let fn' ← transf_expr sty env .Val fn
  let opt_eassign (e : Exp) : Exp := match opt_lhs with
    | none => e
    | some lhs => eassign lhs e
  let special := match fn.edesc with
    | .EVar id => ["__builtin_va_arg", "__builtin_annot", "__builtin_annot_intval",
                   "__builtin_ais_annot"].contains id.name
    | _ => false
  if special then
    -- Do not transform the call in this case
    let args' ← args.mapM (transf_expr sty env .Val)
    return opt_eassign (.mk (.ECall fn args') ty)
  let (assignments, args') ← transf_arguments sty env args
  let call ← match ← classify_return sty env ty with
    | .Ret_scalar => pure (opt_eassign (.mk (.ECall fn' args') ty'))
    | .Ret_ref =>
        match ctx, opt_lhs with
        | .Effects, none => do
            let tmp ← new_temp ty "_res"
            pure (.mk (.ECall fn' (eaddrof tmp :: args')) (.TVoid []))
        | .Val, none => do
            let tmp ← new_temp ty "_res"
            pure (ecomma (.mk (.ECall fn' (eaddrof tmp :: args')) (.TVoid [])) tmp)
        | _, some lhs => do
            let tmp ← new_temp ty "_res"
            pure (ecomma (.mk (.ECall fn' (eaddrof tmp :: args')) (.TVoid [])) (eassign lhs tmp))
    | .Ret_value ty_ret _ _ =>
        let ecall : Exp := .mk (.ECall fn' args') ty_ret
        match ctx, opt_lhs with
        | .Effects, none => pure ecall
        | _, _ => do
            let tmp ← new_temp ty_ret "_res"
            pure (opt_eassign (ecomma (eassign tmp ecall) (ereinterpret ty' tmp)))
  return ecommalist assignments call

/-- Function arguments of `ref_caller` or `flattened` kind. -/
partial def transf_arguments (sty : Styles) (env : Env.T) :
    List Exp → M (List Exp × List Exp)
  | [] => return ([], [])
  | arg :: args => do
      let (assignments, args') ← transf_arguments sty env args
      match ← classify_param sty env arg.etyp with
      | .Param_unchanged =>
          let arg' ← transf_expr sty env .Val arg
          return (assignments, arg' :: args')
      | .Param_ref_caller =>
          let ty' ← transf_type sty env arg.etyp
          let tmp ← new_temp ty' "_arg"
          return ((← transf_assign sty env tmp arg) :: assignments, eaddrof tmp :: args')
      | .Param_flattened n sz al =>
          let ty' ← transf_type sty env arg.etyp
          if translates_to_extended_lvalue arg then
            let tmp ← new_temp ucharptr "_arg"
            return (eassign tmp (ecast ucharptr (eaddrof (← transf_expr sty env .Val arg)))
                      :: assignments,
                    (← load_words tmp 0 sz al) ++ args')
          else
            let tmp ← new_temp (ty_buffer n) "_arg"
            return ((← transf_assign sty env (ereinterpret ty' tmp) arg) :: assignments,
                    list_map_n (ebuffer_index tmp) n ++ args')

partial def transf_assign (sty : Styles) (env : Env.T) (lhs e : Exp) : M Exp := do
  match e.edesc with
  | .ECall fn args => transf_call sty env .Effects (some lhs) fn args e.etyp
  | _ => return eassign lhs (← transf_expr sty env .Val e)

partial def transf_init (sty : Styles) (env : Env.T) : Init → M Init
  | .Init_single e => do return .Init_single (← transf_expr sty env .Val e)
  | .Init_array il => do return .Init_array (← il.mapM (transf_init sty env))
  | .Init_struct id fil => do
      return .Init_struct id (← fil.mapM fun (fld, i) => do return (fld, ← transf_init sty env i))
  | .Init_union id fld i => do return .Init_union id fld (← transf_init sty env i)
end

/-- Declarations -/
def transf_decl (sty : Styles) (env : Env.T) (_loc : Location) : Decl → M Decl
  | .mk sto id ty init => do
      let init' ← match init with
        | none => pure none
        | some i => do pure (some (← transf_init sty env i))
      return .mk sto id (← transf_type sty env ty) init'

/-- Transformation of statements and function bodies -/
partial def transf_funbody (sty : Styles) (env : Env.T) (body : Stmt) (optres : Option Exp) :
    M Stmt :=
  transf_stmt body
where
  transf_stmt (s : Stmt) : M Stmt := do
    let te := transf_expr sty env
    let mk (d : StmtDesc) : Stmt := .mk d s.sloc
    match s.sdesc with
    | .Sskip | .Sbreak | .Scontinue | .Sgoto _ | .Sreturn none => return s
    | .Sdo e => return mk (.Sdo (← te .Effects e))
    | .Sseq s1 s2 => return mk (.Sseq (← transf_stmt s1) (← transf_stmt s2))
    | .Sif e s1 s2 => return mk (.Sif (← te .Val e) (← transf_stmt s1) (← transf_stmt s2))
    | .Swhile e s1 => return mk (.Swhile (← te .Val e) (← transf_stmt s1))
    | .Sdowhile s1 e => return mk (.Sdowhile (← transf_stmt s1) (← te .Val e))
    | .Sfor s1 e s2 s3 =>
        return mk (.Sfor (← transf_stmt s1) (← te .Val e) (← transf_stmt s2) (← transf_stmt s3))
    | .Sswitch e s1 => return mk (.Sswitch (← te .Val e) (← transf_stmt s1))
    | .Slabeled lbl s1 => return mk (.Slabeled lbl (← transf_stmt s1))
    | .Sreturn (some e) =>
        let e' ← te .Val e
        match ← classify_return sty env e'.etyp, optres with
        | .Ret_scalar, none => return mk (.Sreturn (some e'))
        | .Ret_ref, some dst =>
            return sseq s.sloc (sassign s.sloc dst e') (mk (.Sreturn none))
        | .Ret_value ty sz al, none =>
            if translates_to_extended_lvalue e then
              let tmp ← new_temp ucharptr "_res"
              return sseq s.sloc (sassign s.sloc tmp (ecast ucharptr (eaddrof e')))
                (mk (.Sreturn (some (← load_result tmp sz al))))
            else
              let dst ← new_temp ty "_res"
              return sseq s.sloc (sassign s.sloc (ereinterpret e'.etyp dst) e')
                (mk (.Sreturn (some dst)))
        | _, _ => assertFalse "StructPassing.transf_funbody"
    | .Sblock sl => return mk (.Sblock (← sl.mapM transf_stmt))
    | .Sdecl d => return mk (.Sdecl (← transf_decl sty env s.sloc d))
    | .Sasm attr template outputs inputs clob =>
        let op : AsmOperand → M AsmOperand := fun (lbl, cstr, e) => do
          return (lbl, cstr, ← te .Val e)
        return mk (.Sasm attr template (← outputs.mapM op) (← inputs.mapM op) clob)

/-- Binding arguments to parameters: parameter list, actions to perform at
    the beginning of the function, substitution to apply to the body. -/
def transf_funparams (sty : Styles) (loc : Location) (env : Env.T) :
    List (Ident × Typ) → M (List (Ident × Typ) × Stmt × IdentMap Exp)
  | [] => return ([], sskip, {})
  | (x, tx) :: params => do
      let tx' ← transf_type sty env tx
      let (params', actions, subst) ← transf_funparams sty loc env params
      match ← classify_param sty env tx with
      | .Param_unchanged => return ((x, tx') :: params', actions, subst)
      | .Param_ref_caller =>
          let tpx : Typ := .TPtr tx' []
          let ex : Exp := .mk (.EVar x) tpx
          let estarx : Exp := .mk (.EUnop .Oderef ex) tx'
          return ((x, tpx) :: params', actions, subst.insert x estarx)
      | .Param_flattened n _ _ =>
          let y ← new_temp (ty_buffer n) x.name
          let yparts ← list_map_nM (fun _ => Env.fresh_ident x.name) n
          let assign_part (e : Exp) (p : Ident) (act : Stmt) : Stmt :=
            sseq loc (sassign loc e (.mk (.EVar p) uint)) act
          let actions' := ((list_map_n (ebuffer_index y) n).zip yparts).foldr
            (fun (e, p) act => assign_part e p act) actions
          return (yparts.map (fun p => (p, uint)) ++ params', actions',
                  subst.insert x (ereinterpret tx' y))

def transf_fundef (sty : Styles) (env : Env.T) (loc : Location) (f : Fundef) : M Fundef := do
  reset_temps
  let ret ← transf_type sty env f.fd_ret
  let (params, actions, subst) ← transf_funparams sty f.fd_body.sloc env f.fd_params
  let locals ← f.fd_locals.mapM fun d => transf_decl sty env loc (subst_decl subst d)
  let (attr1, ret1, params1, body1) ← match ← classify_return sty env f.fd_ret with
    | .Ret_scalar => do
        pure (f.fd_attrib, ret, params, ← transf_funbody sty env (subst_stmt subst f.fd_body) none)
    | .Ret_ref => do
        let vres ← Env.fresh_ident "_res"
        let tres : Typ := .TPtr ret []
        let eres : Exp := .mk (.EVar vres) tres
        let eeres : Exp := .mk (.EUnop .Oderef eres) ret
        pure (add_attributes f.fd_attrib attr_structret, Typ.TVoid [], (vres, tres) :: params,
              ← transf_funbody sty env (subst_stmt subst f.fd_body) (some eeres))
    | .Ret_value ty _ _ => do
        pure (f.fd_attrib, ty, params, ← transf_funbody sty env (subst_stmt subst f.fd_body) none)
  let temps ← get_temps
  return { f with fd_attrib := attr1, fd_ret := ret1, fd_params := params1,
                  fd_locals := locals ++ temps, fd_body := sseq f.fd_body.sloc actions body1 }

/-- Composites -/
def transf_composite (sty : Styles) (env : Env.T) (_loc : Location) (_su : StructOrUnion)
    (_id : Ident) (attr : Attributes) (fl : List Field) : M (Attributes × List Field) := do
  return (attr, ← fl.mapM fun f => do return { f with fld_typ := ← transf_type sty env f.fld_typ })

/-- Entry point.  `env0` is `Env.initial ()`. -/
def program (option_interp : Bool) (env0 : Env.T) (p : Program) : M Program := do
  let cfg ← getConfig
  let sty : Styles :=
    { passing := if option_interp then .SP_ref_callee else cfg.struct_passing_style
      ret := if option_interp then .SR_ref else cfg.struct_return_style }
  Transform.program
    { decl := transf_decl sty
      fundef := transf_fundef sty
      composite := transf_composite sty
      typedef := fun env _ _ ty => transf_type sty env ty }
    env0 p

end StructPassing
end CParser
end CC
