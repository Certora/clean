/-
  Port of `cfrontend/C2C.ml`, part 2 of 2: expressions, statements,
  functions, initializers, global variables and `convertProgram`.  The
  state, the atom table, the builtins and the translation of types are in
  `C2CBase.lean` (see its header for the differences from OCaml).
-/
import CCLib.cfrontend.C2CBase
import CCLib.backend.AisAnnot

namespace CC
namespace C2C

open CParser (M)
open Csyntax

/-! ### Expressions -/

def check_volatile_bitfield (env : CParser.Env.T) (e : CParser.C.Exp) : CM Unit := do
  if (← (CParser.Cutil.is_bitfield env e : M Bool))
      && (← (CParser.Cutil.attributes_of_type env e.etyp : M _)).contains .AVolatile then
    warning .Unnamed "access to a volatile bit field, the 'volatile' qualifier is ignored"

def ewrap : Res Expr → CM Expr
  | .OK e => return e
  | .Error msg => do
    error s!"retyping error: {msg}"
    return ezero

def convertBinop : CParser.C.BinaryOperator → Option Binop
  | .Oadd | .Oadd_assign => some .Oadd
  | .Osub | .Osub_assign => some .Osub
  | .Omul | .Omul_assign => some .Omul
  | .Odiv | .Odiv_assign => some .Odiv
  | .Omod | .Omod_assign => some .Omod
  | .Oand | .Oand_assign => some .Oand
  | .Oor | .Oor_assign => some .Oor
  | .Oxor | .Oxor_assign => some .Oxor
  | .Oshl | .Oshl_assign => some .Oshl
  | .Oshr | .Oshr_assign => some .Oshr
  | .Oeq => some .Oeq
  | .One => some .One
  | .Olt => some .Olt
  | .Ogt => some .Ogt
  | .Ole => some .Ole
  | .Oge => some .Oge
  | _ => none

def is_assignop : CParser.C.BinaryOperator → Bool
  | .Oadd_assign | .Osub_assign | .Omul_assign | .Odiv_assign | .Omod_assign
  | .Oand_assign | .Oor_assign | .Oxor_assign | .Oshl_assign | .Oshr_assign => true
  | _ => false

mutual

partial def convertExpr (env : CParser.Env.T) (e : CParser.C.Exp) : CM Expr := do
  match e.edesc with
  | .EConst (.CStr _) | .EConst (.CWStr ..) | .EVar _
  | .EUnop .Oderef _ | .EUnop (.Odot _) _ | .EUnop (.Oarrow _) _
  | .EBinop .Oindex _ _ _ =>
    let l ← convertLvalue env e
    check_volatile_bitfield env e
    ewrap (Ctyping.evalof l)

  | .EConst (.CInt i k _) =>
    let sg : Signedness := if ← (CParser.Cutil.is_signed_ikind k : M Bool) then .Signed else .Unsigned
    if (← (CParser.Cutil.sizeof_ikind k : M Int)) == 8 then
      return Ctyping.econstLong (convertInt64 i) sg
    else
      return Ctyping.econstInt (convertInt32 i) sg
  | .EConst (.CFloat f k) =>
    if k == .FLongDouble && !(← get).flags.option_flongdouble then
      unsupported "'long double' floating-point constant"
    convertFloat f k
  | .EConst (.CEnum _ i) => return Ctyping.econstInt (convertInt32 i) .Signed
  | .ESizeof ty1 => return Ctyping.esizeof (← convertTyp env ty1)
  | .EAlignof ty1 => return Ctyping.ealignof (← convertTyp env ty1)

  | .EUnop .Ominus e1 => ewrap (Ctyping.eunop .Oneg (← convertExpr env e1))
  | .EUnop .Oplus e1 => convertExpr env e1
  | .EUnop .Olognot e1 => ewrap (Ctyping.eunop .Onotbool (← convertExpr env e1))
  | .EUnop .Onot e1 => ewrap (Ctyping.eunop .Onotint (← convertExpr env e1))
  | .EUnop .Oaddrof e1 => ewrap (Ctyping.eaddrof (← convertLvalue env e1))
  | .EUnop .Opreincr e1 => ewrap (Ctyping.epreincr (← convertLvalue env e1))
  | .EUnop .Opredecr e1 => ewrap (Ctyping.epredecr (← convertLvalue env e1))
  | .EUnop .Opostincr e1 => ewrap (Ctyping.epostincr (← convertLvalue env e1))
  | .EUnop .Opostdecr e1 => ewrap (Ctyping.epostdecr (← convertLvalue env e1))

  | .EBinop .Oassign e1 e2 _ =>
    let e1' ← convertLvalue env e1
    let e2' ← convertExpr env e2
    if (← (CParser.Cutil.is_composite_type env e1.etyp : M Bool))
        && (← (CParser.Cutil.attributes_of_type env e1.etyp : M _)).contains .AVolatile then
      warning .Unnamed "assignment to an lvalue of volatile composite type, the 'volatile' qualifier is ignored"
    if (← (CParser.Cutil.is_composite_type env e2.etyp : M Bool))
        && (← (CParser.Cutil.attributes_of_type env e2.etyp : M _)).contains .AVolatile then
      warning .Unnamed "assignment of a value of volatile composite type, the 'volatile' qualifier is ignored"
    check_volatile_bitfield env e1
    ewrap (Ctyping.eassign e1' e2')
  | .EBinop .Ocomma e1 e2 _ =>
    ewrap (Ctyping.ecomma (← convertExpr env e1) (← convertExpr env e2))
  | .EBinop .Ologand e1 e2 _ =>
    ewrap (Ctyping.eseqand (← convertExpr env e1) (← convertExpr env e2))
  | .EBinop .Ologor e1 e2 _ =>
    ewrap (Ctyping.eseqor (← convertExpr env e1) (← convertExpr env e2))
  | .EBinop op e1 e2 _ =>
    match convertBinop op with
    | none => throw (.Failure "assert false: convertExpr EBinop")
    | some op' =>
      if is_assignop op then
        let e1' ← convertLvalue env e1
        let e2' ← convertExpr env e2
        check_volatile_bitfield env e1
        ewrap (Ctyping.eassignop op' e1' e2')
      else
        ewrap (Ctyping.ebinop op' (← convertExpr env e1) (← convertExpr env e2))

  | .EConditional e1 e2 e3 =>
    ewrap (Ctyping.econdition (← convertExpr env e1) (← convertExpr env e2)
      (← convertExpr env e3))
  | .ECast ty1 e1 => ewrap (Ctyping.ecast (← convertTyp env ty1) (← convertExpr env e1))
  | .ECompound .. =>
    unsupported "compound literals"
    return ezero

  | .ECall fn args =>
    match fn.edesc, args with
    | .EVar ⟨"__builtin_debug", _⟩, _ =>
      if args.length < 2 then
        error "too few arguments to function call, expected at least 2, have 0"
        return ezero
      let (kind, args1) ← match args with
        | a :: args1 =>
          match a.edesc with
          | .EConst (.CInt n _ _) =>
            if n != 0 then pure (n, args1) else do
              error "argument 1 of '__builtin_debug' must be a non-zero constant"
              pure (1, args1)
          | _ => do
            error "argument 1 of '__builtin_debug' must be a non-zero constant"
            pure (1, args1)
        | [] => throw (.Failure "assert false: __builtin_debug")
      let (text, args2) ← match args1 with
        | a :: args2 =>
          match a.edesc with
          | .EConst (.CStr txt) => pure (txt, args2)
          | .EVar id => pure (id.name, args2)
          | _ => do
            error "argument 2 of '__builtin_debug' must be either a string literal or a variable"
            pure ("", args2)
        | [] => throw (.Failure "assert false: __builtin_debug")
      let targs2 ← convertTypAnnotArgs env args2
      return .Ebuiltin
        (.EF_debug (Positive.ofNat kind.toUInt64.toNat) (← intern_string text)
          (targs2.map typOfType))
        targs2 (← convertExprList env args2) (← convertTyp env e.etyp)

    | .EVar ⟨"__builtin_annot", _⟩, a :: args1 =>
      match a.edesc with
      | .EConst (.CStr txt) =>
        let targs1 ← convertTypAnnotArgs env args1
        return .Ebuiltin (.EF_annot (Positive.ofNat 1) txt (targs1.map typOfType))
          targs1 (← convertExprList env args1) (← convertTyp env e.etyp)
      | _ =>
        error "argument 1 of '__builtin_annot' must be a string literal"
        return ezero
    | .EVar ⟨"__builtin_annot", _⟩, [] =>
      error "argument 1 of '__builtin_annot' must be a string literal"
      return ezero

    | .EVar ⟨"__builtin_annot_intval", _⟩, _ =>
      match args with
      | [a, arg] =>
        match a.edesc with
        | .EConst (.CStr txt) =>
          let targ ← convertTyp env
            (← (CParser.Cutil.default_argument_conversion env arg.etyp : M _))
          return .Ebuiltin (.EF_annot_val (Positive.ofNat 1) txt (typOfType targ))
            [targ] (← convertExprList env [arg]) (← convertTyp env e.etyp)
        | _ =>
          error "argument 1 of '__builtin_annot_intval' must be a string literal"
          return ezero
      | _ =>
        error "argument 1 of '__builtin_annot_intval' must be a string literal"
        return ezero

    | .EVar ⟨"__builtin_ais_annot", _⟩, _ =>
      if !(← get).target.elf_target then convertCall env e fn args else
      match args with
      | a :: args1 =>
        match a.edesc with
        | .EConst (.CStr txt) =>
          let (file, line) := (← get).currentLocation
          let fun_name := (← get).currentFunction
          let loc_string := s!"# file:{file} line:{line} function:{fun_name}\n"
          let targs1 ← convertTypAnnotArgs env args1
          AisAnnot.validate_ais_annot env (← get).currentLocation txt args1
          return .Ebuiltin
            (.EF_annot (Positive.ofNat 2) (loc_string ++ txt) (targs1.map typOfType))
            targs1 (← convertExprList env args1) (← convertTyp env e.etyp)
        | _ =>
          error "argument 1 of '__builtin_ais_annot' must be a string literal"
          return ezero
      | [] =>
        error "argument 1 of '__builtin_ais_annot' must be a string literal"
        return ezero

    | .EVar ⟨"__builtin_memcpy_aligned", _⟩, _ =>
      make_builtin_memcpy (← convertExprList env args)

    | .EVar ⟨"__builtin_fabs", _⟩, [arg] =>
      ewrap (Ctyping.eunop .Oabsfloat (← convertExpr env arg))

    | .EVar ⟨"__builtin_va_start", _⟩, [arg] =>
      return .Ecall (← convertExpr env fn) (.Econs (← va_list_ptr (← convertExpr env arg)) .Enil)
        (← convertTyp env e.etyp)

    | .EVar ⟨"__builtin_va_arg", _⟩, [arg1, _] =>
      make_builtin_va_arg (← convertTyp env e.etyp) (← convertExpr env arg1)

    | .EVar ⟨"__builtin_va_end", _⟩, [arg] =>
      return .Ecast (← convertExpr env arg) .Tvoid

    | .EVar ⟨"__builtin_va_copy", _⟩, [arg1, arg2] =>
      let dst ← convertExpr env arg1
      let src ← convertExpr env arg2
      return .Ebuiltin (.EF_memcpy (← get).target.size_va_list 4)
        [.Tpointer .Tvoid noattr, .Tpointer .Tvoid noattr]
        (.Econs (← va_list_ptr dst) (.Econs (← va_list_ptr src) .Enil)) .Tvoid

    | .EVar ⟨"__builtin_sel", _⟩, [arg1, arg2, arg3] =>
      ewrap (Ctyping.eselection (← convertExpr env arg1) (← convertExpr env arg2)
        (← convertExpr env arg3))

    | .EVar ⟨"__builtin_expect", _⟩, [arg1, _] => convertExpr env arg1

    | .EVar ⟨"printf", _⟩, _ =>
      if !(← get).flags.option_interp then convertCall env e fn args else do
      let targs ← convertTypArgs env [] args
      let tres ← convertTyp env e.etyp
      let sg := signatureOfType targs tres
        { cc_vararg := some 1, cc_unproto := false, cc_structret := false }
      return .Ebuiltin (.EF_external "printf" sg) targs (← convertExprList env args) tres

    | _, _ => convertCall env e fn args


/-- The general case of a function call -/
partial def convertCall (env : CParser.Env.T) (e fn : CParser.C.Exp) (args : List CParser.C.Exp) :
    CM Expr := do
  match ← projFunType env fn.etyp with
  | none => error "wrong type for function part of a call"
  | some (_, targs, va) =>
    if targs.isNone && !(← get).flags.option_funprototyped then
      unsupported "call to unprototyped function (consider adding option [-funprototyped])"
    if va && !(← get).flags.option_fvararg_calls then
      unsupported "call to variable-argument function (consider adding option [-fvararg-calls])"
  checkResultType env e.etyp
  for arg in args do checkArgumentType env arg.etyp
  ewrap (Ctyping.ecall (← convertExpr env fn) (← convertExprList env args))

partial def convertLvalue (env : CParser.Env.T) (e : CParser.C.Exp) : CM Expr := do
  match e.edesc with
  | .EVar id => return .Evar (← intern_string id.name) (← convertTyp env e.etyp)
  | .EUnop .Oderef e1 => ewrap (Ctyping.ederef (← convertExpr env e1))
  | .EUnop (.Odot id) e1 =>
    ewrap (Ctyping.efield (← get).comp_env (← convertExpr env e1) (← intern_string id))
  | .EUnop (.Oarrow id) e1 =>
    let e1' ← convertExpr env e1
    let e2' ← ewrap (Ctyping.ederef e1')
    let e3' ← ewrap (Ctyping.evalof e2')
    ewrap (Ctyping.efield (← get).comp_env e3' (← intern_string id))
  | .EBinop .Oindex e1 e2 _ =>
    let e1' ← convertExpr env e1
    let e2' ← convertExpr env e2
    let e3' ← ewrap (Ctyping.ebinop .Oadd e1' e2')
    ewrap (Ctyping.ederef e3')
  | .EConst (.CStr s) =>
    let ty ← typeStringLiteral s
    return .Evar (← name_for_string_literal s) ty
  | .EConst (.CWStr s ik) =>
    let ty ← typeWideStringLiteral s ik
    return .Evar (← name_for_wide_string_literal s ik) ty
  | _ =>
    error "illegal lvalue"
    return ezero

partial def convertExprList (env : CParser.Env.T) : List CParser.C.Exp → CM ExprList
  | [] => return .Enil
  | e1 :: el => do return .Econs (← convertExpr env e1) (← convertExprList env el)

end

/-! ### Extended assembly -/

def convertAsm (loc : CParser.C.Location) (env : CParser.Env.T) (txt : String)
    (outputs inputs : List CParser.C.AsmOperand) (clobber : List String) : CM Expr := do
  let (txt', output', inputs') ←
    (CParser.ExtendedAsm.transf_asm (← get).target.asm loc env txt outputs inputs clobber : M _)
  let clobber' := clobber.map String.toUpper
  let ty_res : CParser.C.Typ := match output' with
    | none => .TVoid []
    | some e => e.etyp
  -- Build the Ebuiltin expression
  let tinputs ← convertTypAnnotArgs env inputs'
  let toutput ← convertTyp env ty_res
  let e := Expr.Ebuiltin (.EF_inline_asm txt' (signatureOfType tinputs toutput cc_default) clobber')
    tinputs (← convertExprList env inputs') toutput
  -- Add an assignment to the output, if any
  match output' with
  | none => return e
  | some lhs => return .Eassign (← convertLvalue env lhs) e (Csyntax.typeof e)

/-! ### Statements -/

def swrap : Res Stmt → CM Stmt
  | .OK s => return s
  | .Error msg => do
    error s!"retyping error: {msg}"
    return .Sskip

mutual

partial def convertStmt (env : CParser.Env.T) (s : CParser.C.Stmt) : CM Stmt := do
  updateLoc s.sloc
  match s.sdesc with
  | .Sskip => return .Sskip
  | .Sdo e => swrap (Ctyping.sdo (← convertExpr env e))
  | .Sseq s1 s2 =>
    let s1' ← convertStmt env s1
    let s2' ← convertStmt env s2
    return .Ssequence s1' s2'
  | .Sif e s1 s2 =>
    let te ← convertExpr env e
    swrap (Ctyping.sifthenelse te (← convertStmt env s1) (← convertStmt env s2))
  | .Swhile e s1 =>
    let te ← convertExpr env e
    swrap (Ctyping.swhile te (← convertStmt env s1))
  | .Sdowhile s1 e =>
    let te ← convertExpr env e
    swrap (Ctyping.sdowhile te (← convertStmt env s1))
  | .Sfor s1 e s2 s3 =>
    let te ← convertExpr env e
    swrap (Ctyping.sfor (← convertStmt env s1) te (← convertStmt env s2) (← convertStmt env s3))
  | .Sbreak => return .Sbreak
  | .Scontinue => return .Scontinue
  | .Sswitch e s1 =>
    let te ← convertExpr env e
    swrap (Ctyping.sswitch te (← convertSwitch env (← is_int64 env e.etyp) s1))
  | .Slabeled (.Slabel lbl) s1 => return .Slabel (← intern_string lbl) (← convertStmt env s1)
  | .Slabeled (.Scase ..) _ =>
    unsupported "'case' statement not in 'switch' statement"
    return .Sskip
  | .Slabeled .Sdefault _ =>
    unsupported "'default' statement not in 'switch' statement"
    return .Sskip
  | .Sgoto lbl => return .Sgoto (← intern_string lbl)
  | .Sreturn none => return .Sreturn none
  | .Sreturn (some e) => return .Sreturn (some (← convertExpr env e))
  | .Sblock _ =>
    unsupported "nested blocks"
    return .Sskip
  | .Sdecl _ =>
    unsupported "inner declarations"
    return .Sskip
  | .Sasm _ txt outputs inputs clobber =>
    if !(← get).flags.option_finline_asm then
      unsupported "inline 'asm' statement (consider adding option [-finline-asm])"
    return .Sdo (← convertAsm s.sloc env txt outputs inputs clobber)

partial def convertSwitch (env : CParser.Env.T) (is_64 : Bool) (s : CParser.C.Stmt) :
    CM LStmts := do
  match s.sdesc with
  | .Sskip => return .LSnil
  | .Slabeled lbl s => convertSwitchCase env is_64 lbl s .LSnil
  | .Sseq s1 rem =>
    match s1.sdesc with
    | .Slabeled lbl s => convertSwitchCase env is_64 lbl s (← convertSwitch env is_64 rem)
    | _ => throw (.Failure "assert false: convertSwitch")
  | _ => throw (.Failure "assert false: convertSwitch")

partial def convertSwitchCase (env : CParser.Env.T) (is_64 : Bool) (lbl : CParser.C.SLabel)
    (s : CParser.C.Stmt) (k : LStmts) : CM LStmts := do
  let lbl' ← match lbl with
    | .Sdefault => pure none
    | .Scase _ v =>
      pure (some (if is_64 then (v.toUInt64.toNat : Int) else (v.toInt32.toUInt32.toNat : Int)))
    | _ => throw (.Failure "assert false: convertSwitchCase")
  return .LScons lbl' (← convertStmt env s) k

end

/-! ### Function definitions -/

def convertFundef (loc : CParser.C.Location) (env : CParser.Env.T) (fd : CParser.C.Fundef) :
    CM (Ident × GlobDef FunDef Ty) := do
  checkFunctionType env fd.fd_ret (some fd.fd_params)
  updateFunction fd.fd_name.name
  if fd.fd_vararg && !(← get).flags.option_fvararg_calls then
    unsupported "variable-argument function (consider adding option [-fvararg-calls])"
  let ret ← convertTyp env fd.fd_ret
  let params ← fd.fd_params.mapM fun (id, ty) => do
    return (← intern_string id.name, ← convertTyp env ty)
  let vars ← fd.fd_locals.mapM fun d => do
    match d with
    | .mk sto id ty init =>
      if sto == .Storage_extern || sto == .Storage_static then
        unsupported "'static' or 'extern' local variable"
      if init.isSome then
        unsupported "initialized local variable"
      return (← intern_string id.name, ← convertTyp env ty)
  let body' ← convertStmt env fd.fd_body
  let id' ← intern_string fd.fd_name.name
  let noinline := !(CParser.Cutil.find_custom_attributes ["noinline", "__noinline__"] fd.fd_attrib).isEmpty
  let inline : InlineStatus :=
    if noinline || fd.fd_vararg then .Noinline -- PR#15
    else if fd.fd_inline then .Inline
    else .No_specifier
  let secs ← (Sections.for_function (← get).sections loc id' fd.fd_attrib : M _)
  add_atom id'
    { a_storage := fd.fd_storage, a_defined := true, a_alignment := none, a_size := none
      a_sections := secs, a_access := .Access_default, a_inline := inline
      a_literal := .No_literal, a_loc := loc }
  return (id', .Gfun (.Internal
    { fn_return := ret
      fn_callconv := convertCallconv (some fd.fd_params) fd.fd_vararg fd.fd_attrib
      fn_params := params
      fn_vars := vars
      fn_body := body' }))

/-! ### External function declaration -/

def convertFundecl (env : CParser.Env.T) (id : CParser.C.Ident) (ty : CParser.C.Typ) :
    CM (Ident × GlobDef FunDef Ty) := do
  let (args, res, cconv) ← match ← convertTyp env ty with
    | .Tfunction args res cconv => pure (args, res, cconv)
    | _ => throw (.Failure "assert false: convertFundecl")
  let id' ← intern_string id.name
  let sg := signatureOfType args res cconv
  let bfuns := (builtins (← get).target).builtin_functions
  let ef : ExtFun :=
    if id.name == "malloc" then .EF_malloc
    else if id.name == "free" then .EF_free
    else if id.name.startsWith "__builtin_"
        && (bfuns.lookup id.name).isSome then
      .EF_builtin id.name sg
    else .EF_external id.name sg
  return (id', .Gfun (.External ef args res cconv))

/-! ### Initializers -/

mutual

partial def convertInit (env : CParser.Env.T) : CParser.C.Init → CM Initializers.Initializer
  | .Init_single e => do return .Init_single (← convertExpr env e)
  | .Init_array il => do return .Init_array (← convertInitList env il.reverse .Init_nil)
  | .Init_struct _ flds => do
    return .Init_struct (← convertInitList env (flds.map (·.2)).reverse .Init_nil)
  | .Init_union _ fld i => do
    return .Init_union (← intern_string fld.fld_name) (← convertInit env i)

partial def convertInitList (env : CParser.Env.T) (il : List CParser.C.Init)
    (accu : Initializers.InitializerList) : CM Initializers.InitializerList := do
  match il with
  | [] => return accu
  | i :: il' => convertInitList env il' (.Init_cons (← convertInit env i) accu)

end

def convertInitializer (env : CParser.Env.T) (ty : CParser.C.Typ) (i : CParser.C.Init) :
    CM (List InitData) := do
  match Initializers.translInit (← get).comp_env (← convertTyp env ty) (← convertInit env i) with
  | .OK init => return init
  | .Error msg =>
    error s!"initializer element is not a compile-time constant ({msg})"
    return []

/-! ### Global variable -/

def convertGlobvar (loc : CParser.C.Location) (env : CParser.Env.T) (sto : CParser.C.Storage)
    (id : CParser.C.Ident) (ty : CParser.C.Typ) (optinit : Option CParser.C.Init) :
    CM (Ident × GlobDef FunDef Ty) := do
  let id' ← intern_string id.name
  let ty' ← convertTyp env ty
  let ce := (← get).comp_env
  let sz := sizeof ce ty'
  let al := max (alignof ce ty') (minSafeAlignment sz)
  let attr ← (CParser.Cutil.attributes_of_type env ty : M _)
  let init' ← match optinit with
    | none => pure (if sto == .Storage_extern then [] else [InitData.Init_space sz])
    | some i => convertInitializer env ty i
  let initialized : Sections.Initialized :=
    if optinit.isNone then .Uninit
    else if init'.any (fun | .Init_addrof .. => true | _ => false) then .Init_reloc
    else .Init
  let fl := (← get).flags
  let (sec, access) ← (Sections.for_variable fl.option_small_const fl.option_small_data
    (← get).sections env loc id' ty initialized : M _)
  if sz > 0xFFFF_FFFF then
    error s!"'{id.name}' is too big ({sz} bytes)"
  if sto != .Storage_extern && (← (CParser.Cutil.incomplete_type env ty : M Bool)) then
    error s!"'{id.name}' has incomplete type"
  add_atom id'
    { a_storage := sto, a_defined := optinit.isSome, a_alignment := some al
      a_size := some sz, a_sections := [sec], a_access := access
      a_inline := .No_specifier, a_literal := .No_literal, a_loc := loc }
  let volatile := attr.contains .AVolatile
  let readonly := attr.contains .AConst && !volatile
  return (id', .Gvar { gvar_info := ty', gvar_init := init',
                       gvar_readonly := readonly, gvar_volatile := volatile })

/-- Convert a list of global declarations.  Result is a list of CompCert C
    global declarations (functions + variables). -/
def convertGlobdecls (env : CParser.Env.T) (gl : List CParser.C.Globdecl) :
    CM (List (Ident × GlobDef FunDef Ty)) := do
  let mut res := []
  for g in gl do
    updateLoc g.gloc
    match g.gdesc with
    | .Gdecl (.mk sto id ty optinit) =>
      -- Functions become external declarations.
      -- Other types become variable declarations.
      match ← (CParser.Cutil.unroll env ty : M _) with
      | .TFun _ targs _ _ =>
        if targs.isNone then
          warning .Unnamed s!"'{id.name}' is declared without a function prototype"
        res := (← convertFundecl env id ty) :: res
      | _ =>
        res := (← convertGlobvar g.gloc env sto id ty optinit) :: res
    | .Gfundef fd =>
      res := (← convertFundef g.gloc env fd) :: res
    | .Gcompositedecl .. | .Gcompositedef .. | .Gtypedef .. | .Genumdef .. =>
      -- Composites are treated in a separate pass, typedefs are unrolled,
      -- and enum tags are folded.  So we just skip their declarations.
      pure ()
    | .Gpragma s =>
      let st ← get
      let (ok, tbl) ← (st.target.process_pragma st.currentLocation s st.sections : M _)
      modify fun st => { st with sections := tbl }
      if !ok then
        warning .Unknown_pragmas "unknown pragma ignored"
  return res.reverse

/-- Convert struct and union declarations.  Result is a list of CompCert C
    composite declarations. -/
def convertCompositedefs (env : CParser.Env.T) (gl : List CParser.C.Globdecl) :
    CM (List CompositeDef) := do
  let mut res := []
  for g in gl do
    updateLoc g.gloc
    match g.gdesc with
    | .Gcompositedef su id a m => res := (← convertCompositedef env su id a m) :: res
    | _ => pure ()
  return res.reverse

/-! ### Helper functions (for varargs and for int64 arithmetic) -/

def helper_functions : CM (List (String × Ty × List Ty)) := do
  let size_t ← convertIkind (← (CParser.Cutil.size_t_ikind : M _)) noattr
  return [
    ("__compcert_va_int32", .Tint .I32 .Unsigned noattr, [.Tpointer .Tvoid noattr]),
    ("__compcert_va_int64", .Tlong .Unsigned noattr, [.Tpointer .Tvoid noattr]),
    ("__compcert_va_float64", .Tfloat .F64 noattr, [.Tpointer .Tvoid noattr]),
    ("__compcert_va_composite", .Tpointer .Tvoid noattr, [.Tpointer .Tvoid noattr, size_t]),
    ("__compcert_i64_dtos", .Tlong .Signed noattr, [.Tfloat .F64 noattr]),
    ("__compcert_i64_dtou", .Tlong .Unsigned noattr, [.Tfloat .F64 noattr]),
    ("__compcert_i64_stod", .Tfloat .F64 noattr, [.Tlong .Signed noattr]),
    ("__compcert_i64_utod", .Tfloat .F64 noattr, [.Tlong .Unsigned noattr]),
    ("__compcert_i64_stof", .Tfloat .F32 noattr, [.Tlong .Signed noattr]),
    ("__compcert_i64_utof", .Tfloat .F32 noattr, [.Tlong .Unsigned noattr]),
    ("__compcert_i64_sdiv", .Tlong .Signed noattr, [.Tlong .Signed noattr, .Tlong .Signed noattr]),
    ("__compcert_i64_udiv", .Tlong .Unsigned noattr,
      [.Tlong .Unsigned noattr, .Tlong .Unsigned noattr]),
    ("__compcert_i64_smod", .Tlong .Signed noattr, [.Tlong .Signed noattr, .Tlong .Signed noattr]),
    ("__compcert_i64_umod", .Tlong .Unsigned noattr,
      [.Tlong .Unsigned noattr, .Tlong .Unsigned noattr]),
    ("__compcert_i64_shl", .Tlong .Signed noattr, [.Tlong .Signed noattr, .Tint .I32 .Signed noattr]),
    ("__compcert_i64_shr", .Tlong .Unsigned noattr,
      [.Tlong .Unsigned noattr, .Tint .I32 .Signed noattr]),
    ("__compcert_i64_sar", .Tlong .Signed noattr, [.Tlong .Signed noattr, .Tint .I32 .Signed noattr]),
    ("__compcert_i64_smulh", .Tlong .Signed noattr,
      [.Tlong .Signed noattr, .Tlong .Signed noattr]),
    ("__compcert_i64_umulh", .Tlong .Unsigned noattr,
      [.Tlong .Unsigned noattr, .Tlong .Unsigned noattr]) ]

def helper_function_declaration (h : String × Ty × List Ty) : CM (Ident × GlobDef FunDef Ty) := do
  let (name, tyres, tyargs) := h
  let ef := ExtFun.EF_runtime name (signatureOfType tyargs tyres cc_default)
  return (← intern_string name, .Gfun (.External ef tyargs tyres cc_default))

def add_helper_functions (globs : List (Ident × GlobDef FunDef Ty)) :
    CM (List (Ident × GlobDef FunDef Ty)) := do
  return (← (← helper_functions).mapM helper_function_declaration) ++ globs

/-! ### Build environment of typedefs, structs, unions and enums -/

def translEnv (env : CParser.Env.T) (gl : List CParser.C.Globdecl) : M CParser.Env.T := do
  let mut env := env
  for g in gl do
    env ← match g.gdesc with
      | .Gcompositedecl su id attr =>
        pure (CParser.Env.add_composite env id (CParser.Cutil.composite_info_decl su attr))
      | .Gcompositedef su id attr fld => do
        pure (CParser.Env.add_composite env id (← CParser.Cutil.composite_info_def env su attr fld))
      | .Gtypedef id ty => pure (CParser.Env.add_typedef env id ty)
      | .Genumdef id attr members =>
        pure (CParser.Env.add_enum env id { ei_members := members, ei_attr := attr })
      | _ => pure env
  return env

/-! ### Eliminate multiple declarations of globals -/

def cleanupGlobals (p : List CParser.C.Globdecl) : CM (List CParser.C.Globdecl) := do
  -- First pass: determine what is defined
  let mut strong : Std.HashSet CParser.C.Ident := {} -- def functions or variables with inits
  let mut weak : Std.HashSet CParser.C.Ident := {}   -- variables without inits
  for g in p do
    updateLoc g.gloc
    match g.gdesc with
    | .Gfundef fd =>
      if strong.contains fd.fd_name then
        error s!"multiple definitions of {fd.fd_name.name}"
      strong := strong.insert fd.fd_name
    | .Gdecl (.mk .Storage_extern _ _ _) => pure ()
    | .Gdecl (.mk _ id _ (some _)) =>
      if strong.contains id then
        error s!"multiple definitions of {id.name}"
      strong := strong.insert id
    | .Gdecl (.mk _ id _ none) => weak := weak.insert id
    | _ => pure ()
  -- Second pass: keep "best" definition for each identifier
  let mut defs : Std.HashSet CParser.C.Ident := {}
  let mut accu : List CParser.C.Globdecl := []
  for g in p.reverse do
    updateLoc g.gloc
    match g.gdesc with
    | .Gdecl (.mk sto id _ init) =>
      let better_def_exists :=
        if sto == .Storage_extern then strong.contains id || weak.contains id
        else if init.isNone then strong.contains id
        else false
      if !(defs.contains id || better_def_exists) then
        defs := defs.insert id
        accu := g :: accu
    | .Gfundef fd =>
      defs := defs.insert fd.fd_name
      accu := g :: accu
    | _ => accu := g :: accu
  return accu

/-- Extract the list of public (non-static) names -/
def public_globals (tbl : List (Nat × AtomInfo)) (gl : List (Ident × GlobDef FunDef Ty)) :
    List Ident :=
  gl.foldl (fun accu (id, _) => if atom_is_static tbl id then accu else id :: accu) []

/-! ## Convert a `C.program` into a `Csyntax.program` -/

/-- `convertProgram p`.  `init` is the initial environment of the
    elaborator (see `Env.set_builtins`), whose declarations are added to
    `p`.  Returns the program and the final atom table (`decl_atom`). -/
def convertProgram (flags : Clflags.Flags) (tgt : Target) (init : CParser.Env.InitEnv)
    (p : CParser.C.Program) : M (Program × List (Nat × AtomInfo)) := do
  CParser.Diagnostics.reset
  let act : CM (Program × List (Nat × AtomInfo)) := do
    let p ← cleanupGlobals (init.initial_declarations ++ p)
    let env ← (translEnv CParser.Env.empty p : M _)
    let typs ← convertCompositedefs env p
    match h : buildCompositeEnv typs with
    | .Error msg => fatal_error s!"incorrect struct or union definition: {msg}"
    | .OK ce =>
      modify fun s => { s with comp_env := ce }
      let gl1 ← convertGlobdecls env p
      let gl2 ← globals_for_strings gl1
      let gl3 ← add_helper_functions gl2
      modify fun s => { s with comp_env := PTree.empty }
      let tbl := (← get).decl_atom
      let p' : Program :=
        { prog_defs := gl3
          prog_public := public_globals tbl gl3
          prog_main := identOfString flags.main_function_name
          prog_types := typs
          prog_comp_env := ce
          prog_comp_env_eq := h }
      (CParser.Diagnostics.check_errors : M Unit)
      return (p', tbl)
  let r ← tryCatch (act.run' { flags, target := tgt }) fun
    | .EnvError msg => CParser.Diagnostics.fatal_error CParser.Cutil.no_loc (CParser.Env.error_message msg)
    | e => throw e
  return r

end C2C
end CC
