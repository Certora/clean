/-
  Port of `cparser/Elab.ml`, part 5 of 5: elaboration of top-level and
  local definitions, function definitions, statements, and the entry point
  `elab_file`.

  Differences from OCaml:
  * The functions on definitions and statements form one mutual block, so the
    forward reference `elab_funbody_f` is not needed.
  * The initial environment `Env.initial ()` (with the builtins) is the
    argument `init` of `elab_file` (see `Env.set_builtins`), and
    `Clflags.option_Obranchless` is the argument `option_Obranchless`.
  * Debug information (`Debug.insert_local_declaration`) is not produced:
    the hooks (`debug/DebugInformation.lean`) exist but are not threaded
    through the front end yet.
-/
import CCLib.cparser.ElabExpr
import CCLib.cparser.Cflow
import CCLib.cparser.Checks
import CCLib.cparser.Cprint
import CCLib.cparser.Cabshelper

namespace CC
namespace CParser
namespace Elab

open C Cutil Diagnostics
open CC.Cabs (Loc)

/-! ### Elaboration of top-level and local definitions -/

def is_no_init : Cabs.InitExpression → Bool
  | .NO_INIT => true
  | _ => false

def enter_typedef (loc : Loc) (env : Env.T) (_sto : Storage)
    (d : String × Typ × Cabs.InitExpression) : EM Env.T := do
  let (s, ty, init) := d
  if !is_no_init init then
    error loc "initializer in typedef"
  if ← (has_std_alignas env ty : M Bool) then
    error loc s!"alignment specified for typedef '{s}'"
  for a in attributes_of_type_no_expand ty do
    match ← (class_of_attribute a : M AttributeClass) with
    | .Attr_object | .Attr_struct =>
      error loc s!"attribute '{name_of_attribute a}' not allowed in 'typedef'"
    | _ => pure ()
  let prev ← previous_def (Env.lookup_typedef env s)
  match prev with
  | some (s', ty') =>
    if Env.in_current_scope env s' then
      if ← (equal_types env ty ty' : M Bool) then
        warning loc .Celeven_extension s!"redefinition of typedef '{s}' is a C11 extension"
        return env
      else
        error loc s!"redefinition of typedef '{s}' with different type ({← print_typ env ty} vs {← print_typ env ty'})"
        return env
    else enter_new s ty
  | none => enter_new s ty
where
  enter_new (s : String) (ty : Typ) : EM Env.T := do
    if ← redef (Env.lookup_ident env s) env then
      error loc s!"redefinition of '{s}' as different kind of symbol"
    let (id, env') ← (Env.enter_typedef env s ty : M _)
    check_reduced_alignment loc env' ty
    emit_elab false loc (.Gtypedef id ty)
    return env'

def enter_decdef [ElabExprFwd] (local_ nonstatic_inline : Bool) (loc : Loc) (sto : Storage)
    (acc : List Decl × Env.T) (d : String × Typ × Cabs.InitExpression) :
    EM (List Decl × Env.T) := do
  let (decls, env) := acc
  let (s, ty, init) := d
  let isfun ← (is_function_type env ty : M Bool)
  let has_init := !is_no_init init
  if sto == .Storage_register && (← (has_std_alignas env ty : M Bool)) then
    error loc s!"alignment specified for 'register' object '{s}'"
  if sto == .Storage_extern && has_init then
    error loc "'extern' declaration variable has an initializer"
  if local_ && isfun then
    match sto with
    | .Storage_static =>
      error loc "function declared in block scope cannot have 'static' storage class"
    | .Storage_auto | .Storage_register =>
      error loc s!"illegal storage class {name_of_storage_class sto} on function"
    | _ => pure ()
  if is_qualified_array ty then
    error loc "type qualifier used in array declarator outside of function prototype"
  -- Local variable declarations with default storage are treated as 'auto'.
  -- Local function declarations with default storage remain with default storage.
  let sto1 := if local_ && sto == .Storage_default && !isfun then .Storage_auto else sto
  -- enter ident in environment with declared type, because initializer can refer to the ident
  let (id, sto', env1, ty, linkage) ← enter_or_refine_ident local_ loc env s sto1 ty
  if has_init && !local_ then
    add_global_define loc s
  -- check if the type is void or incomplete and the declaration is initialized
  if !isfun then
    let incomplete_init := !(← (is_array_type env1 ty : M Bool))
      && (← wrap (incomplete_type env1 ty) loc) && has_init
    if (← (is_void_type env1 ty : M Bool)) || incomplete_init then
      fatal_error loc s!"variable '{s}' has incomplete type {← print_typ env ty}"
  -- process the initializer
  let (ty', init', env2) ← elab_initializer loc env1 s ty init
  -- update environment with refined type
  let env3 := Env.add_ident env2 id sto' ty'
  -- check for incomplete type
  if !isfun && (← wrap (incomplete_type env ty') loc) then
    if !local_ && sto' == .Storage_static then
      warning loc .Tentative_incomplete_static "tentative static definition with incomplete type"
    else if local_ && sto' != .Storage_extern then
      error loc s!"variable '{s}' has incomplete type {← print_typ env ty'}"
  -- check if alignment is reduced
  check_reduced_alignment loc env ty'
  -- check for static variables in nonstatic inline functions
  if local_ && nonstatic_inline && sto' == .Storage_static
      && !(← (attributes_of_type env ty' : M Attributes)).contains .AConst then
    warning loc .Static_in_inline s!"non-constant static local variable '{s}' in inline function may be different in different files"
  if local_ && !isfun && sto' != .Storage_extern && sto' != .Storage_static then
    -- Local definition
    return (.mk sto' id ty' init' :: decls, env3)
  else
    -- Global definition
    emit_elab linkage loc (.Gdecl (.mk sto' id ty' init'))
    -- Make sure the initializer is constant.
    match init' with
    | some i =>
      if !(← (Ceval.is_constant_init env3 i : M Bool)) then
        error loc "initializer is not a compile-time constant"
    | none => pure ()
    return (decls, env3)

/-- Processing of K&R-style function definitions.  Synopsis:
      `T f(X1, ..., Xn) T1 Y1; ...; Tm Ym; { ... }`
  "params" is the list `[X1; ...; Xn]`, "defs" is the list of declarations
  `[T1 Y1; ... Tm Ym]`.  We need to match the names Xi's with the Yj's so as
  to find the types Ti' of the Xi and produce a typed argument list in
  prototyped style.  Owing to default argument promotion, the types Ti' and
  Tj may not match, in which case we need to declare a local variable with
  the correct type.  E.g. `float f(x) float x; { return x; }` becomes
  `float f(double x) { float x1 = x; return x1; }`. -/
def elab_KR_function_parameters [ElabExprFwd] (env : Env.T) (params : List String)
    (defs : List Cabs.Definition) (loc : Loc) :
    EM (List (Ident × Typ) × List Decl × Env.T) := do
  -- Check that the parameters have unique names
  for id in params do
    if (params.filter (· == id)).length > 1 then
      fatal_error loc s!"redefinition of parameter '{id}'"
  -- Check that the declarations only declare parameters
  let extract_name : Cabs.InitName → EM Cabs.Name
    | .Init_name name@(.Name s _ _ loc') ie => do
      if !params.contains s then
        error loc' s!"declaration of '{s}' which is not a function parameter"
      if !is_no_init ie then
        error loc' s!"illegal initialization of parameter '{s}'"
      return name
  -- Extract names and types from the declarations
  let elab_param_def (env : Env.T) : Cabs.Definition → EM (List (String × Typ) × Env.T)
    | .DECDEF (spec', name_init_list) loc' => do
      let name_list ← name_init_list.mapM extract_name
      if name_list.isEmpty then
        error loc' "declaration does not declare a parameter"
      let (paramsenv, sto) ← elab_name_group loc' env spec' name_list
      if sto != .Storage_default && sto != .Storage_register then
        -- NB: 'auto' not allowed
        error loc' s!"invalid storage class {name_of_storage_class sto} for function parameter"
      return paramsenv
    | d => -- Should never be produced by the parser
      fatal_error (Cabshelper.get_definitionloc d) "illegal declaration of function parameter"
  let (params_l, paramsenv) ← mmap elab_param_def env defs
  let kr_params_defs := params_l.flatten
  -- Find the type of a parameter
  let type_of_param (param : String) : EM Typ := do
    match kr_params_defs.filter (fun (p, _) => p == param) with
    | [] =>
      -- Parameter is not declared, defaults to "int" in ISO C90,
      -- is an error in ISO C99.  Just emit a warning.
      warning loc .Implicit_int s!"type of '{param}' defaults to 'int'"
      return .TInt .IInt []
    | (_, ty) :: rem =>
      if !rem.isEmpty then
        error loc s!"redefinition of parameter '{param}'"
      return ty
  -- Match parameters against declarations
  let mut params' : List (Ident × Typ) := []
  let mut extra_decls : List Decl := []
  for p in params do
    let ty ← type_of_param p
    let ty_var ← (argument_conversion env ty : M Typ)
    let ty_param ← (default_argument_conversion env ty : M Typ)
    if ← (compatible_types .AttrIgnoreTop env ty_var ty_param : M Bool) then
      -- No need for an extra conversion
      let id ← (Env.fresh_ident p : M Ident)
      params' := (id, ty_var) :: params'
    else
      -- Local variable of type ty_var is to be initialized from the parameter of type ty_param
      let id_param ← (Env.fresh_ident p : M Ident)
      let id_var ← (Env.fresh_ident p : M Ident)
      let init := Init.Init_single (.mk (.EVar id_param) ty_param)
      params' := (id_param, ty_param) :: params'
      extra_decls := .mk .Storage_default id_var ty_var (some init) :: extra_decls
  return (params'.reverse, extra_decls.reverse, paramsenv)

/-- Look for varargs flag in previous definitions of a function -/
def inherit_vararg (env : Env.T) (s : String) (sto : Storage) (ty : Typ) : EM Bool := do
  match ← previous_def (Env.lookup_ident env s) with
  | some (id, .II_ident _ old_ty) =>
    if sto == .Storage_extern || Env.in_current_scope env id then
      match old_ty, ty with
      | .TFun _ _ true _, .TFun .. => return true
      | _, _ => return false
    else return false
  | _ => return false

/-- Extended asm -/
def elab_asm_operand (ctx : ElabContext) (loc : Loc) (env : Env.T) :
    Cabs.AsmOperand → EM (AsmOperand × Env.T)
  | .ASMOPERAND label wide chars e => do
    let s ← elab_simple_string loc wide chars
    let (e', env) ← elab_expr ctx loc env e
    return ((label, s, e'), env)

/-! ### Operations over contexts -/

partial def stmt_labels (stmt : Cabs.Statement) : EM (Std.HashSet String) := do
  let rec do_stmt (lbls : Std.HashSet String) : Cabs.Statement → EM (Std.HashSet String)
    | .BLOCK b _ => b.foldlM do_stmt lbls
    | .If _ s1 (some s2) _ => do do_stmt (← do_stmt lbls s1) s2
    | .If _ s1 none _ => do_stmt lbls s1
    | .WHILE _ s1 _ => do_stmt lbls s1
    | .DOWHILE _ s1 _ => do_stmt lbls s1
    | .FOR _ _ _ s1 _ => do_stmt lbls s1
    | .SWITCH _ s1 _ => do_stmt lbls s1
    | .CASE _ s1 _ => do_stmt lbls s1
    | .DEFAULT s1 _ => do_stmt lbls s1
    | .LABEL lbl s1 loc => do
      if lbls.contains lbl then
        error loc s!"redefinition of label '{lbl}'\n"
      do_stmt (lbls.insert lbl) s1
    | _ => pure lbls
  do_stmt {} stmt

def ctx_loop (ctx : ElabContext) : ElabContext := { ctx with ctx_break := true, ctx_continue := true }

def ctx_switch (ctx : ElabContext) (ty : Typ) : ElabContext :=
  { ctx with ctx_break := true, ctx_in_switch := some ty }

/-- Check the uniqueness of 'case' and 'default' in a 'switch' -/
def check_switch_cases (switch_body : Stmt) : EM Unit := do
  let rec check (st : List Int64 × Bool) (s : Stmt) : EM (List Int64 × Bool) := do
    match s with
    | .mk sd sloc =>
    match sd with
    | .Sseq s1 s2 => check (← check st s1) s2
    | .Sif _ s1 s2 => check (← check st s1) s2
    | .Swhile _ s1 => check st s1
    | .Sdowhile s1 _ => check st s1
    | .Sfor s1 _ s2 s3 => check (← check (← check st s1) s2) s3
    | .Sswitch _ _ => pure st -- already checked during elaboration of this switch
    | .Slabeled lbl s1 =>
      let (cases, dflt) := st
      let st' ← match lbl with
        | .Slabel _ => pure st
        | .Scase _ n =>
          if cases.contains n then do
            (Diagnostics.error sloc s!"duplicate case value '{n}'" : M Unit)
            pure st
          else pure (n :: cases, dflt)
        | .Sdefault =>
          if dflt then do
            (Diagnostics.error sloc "multiple default labels in one switch" : M Unit)
            pure st
          else pure (cases, true)
      check st' s1
    | .Sblock sl => sl.attach.foldlM (fun st ⟨s, _⟩ => check st s) st
    | _ => pure st
  termination_by sizeOf s
  decreasing_by all_goals (simp_wf; (try have := List.sizeOf_lt_of_mem ‹_›); omega)
  discard <| check ([], false) switch_body

/-! ### Function definitions and statements -/

variable [ElabExprFwd]

mutual

/-- Function definitions -/
partial def elab_fundef (genv : Env.T) (spec : List Cabs.SpecElem) (name : Cabs.Name)
    (defs : List Cabs.Definition) (body : Cabs.Statement) (loc : Loc) :
    EM Env.T := do
  /- We maintain two environments:
     - genv is the "global", file-scope environment.  It is enriched with the
       declaration of the function, and also with structs and unions defined
       as part of its return type.
     - lenv is the "local" environment used to elaborate the function body.
       It contains everything that genv contains, including a declaration
       for the function, so as to support recursive calls.  In addition, it
       contains declarations for function parameters and structs and unions
       defined in the parameter list. -/
  let (fun_id, sto, inline, noret, ty, kr_params, genv, lenv) ←
    elab_fundef_name genv spec name
  if Env.ident_is_bound (← get).initial_env fun_id.name then
    error loc s!"definition of builtin function '{fun_id.name}'"
  let s := fun_id.name
  if sto == .Storage_auto || sto == .Storage_register then
    fatal_error loc s!"invalid storage class {name_of_storage_class sto} on function"
  match kr_params, defs with
  | none, d :: _ =>
    error (Cabshelper.get_definitionloc d)
      "old-style parameter declarations in prototyped function definition"
  | _, _ => pure ()
  /- Process the parameters and the K&R declarations, if any, to obtain:
      - [ty]: the full, prototyped type of the function
      - [extra_decls]: extra declarations to be inserted at the beginning of
        the function
      - [lenv]: a first cut at the local environment, containing in
        particular the structs and unions defined in the parameter list. -/
  let (ty, extra_decls, lenv) ← match ty, kr_params with
    | .TFun _ (some _) _ _, none => pure (ty, [], lenv)
    | .TFun ty_ret none false attr, none => do
      let ty := Typ.TFun ty_ret (some []) (← inherit_vararg genv s sto ty) attr
      warning loc .CompCert_conformance s!"function definition without a prototype, converting to prototype form. New type is '{Cprint.toText (Cprint.simple_decl {} fun_id ty)}'"
      pure (ty, [], lenv)
    | .TFun ty_ret none false attr, some params => do
      let (params', extra_decls, lenv) ← elab_KR_function_parameters lenv params defs loc
      let ty := Typ.TFun ty_ret (some params') (← inherit_vararg genv s sto ty) attr
      warning loc .CompCert_conformance s!"function definition without a prototype, converting to prototype form. New type is '{Cprint.toText (Cprint.simple_decl {} fun_id ty)}'"
      pure (ty, extra_decls, lenv)
    | _, _ => fatal_error loc "wrong type for function definition"
  -- Add the noreturn to the function type since for calls we only check for
  -- noreturn attributes in the type of the function call.
  let ty ← if noret then (add_attributes_type [.Attr "noreturn" []] ty : M Typ) else pure ty
  -- Extract infos from the type of the function.
  let (ty_ret, params, vararg) ← match ty with
    | .TFun ty_ret (some params) vararg _ => pure (ty_ret, params, vararg)
    | _ => throw (.Failure "assert false: elab_fundef")
  -- Checks on the return type must be done in the global environment.
  if ← (has_std_alignas genv ty : M Bool) then
    error loc s!"alignment specified for function '{s}'"
  if (← wrap (incomplete_type genv ty_ret) loc) && !(← (is_void_type genv ty_ret : M Bool)) then
    fatal_error loc s!"incomplete result type {← print_typ genv ty_ret} in function definition"
  -- Enter function in the global environment
  let (fun_id, sto1, genv, new_ty, _) ← enter_or_refine_function loc genv fun_id sto ty
  add_global_define loc s
  -- Also enter it in the local environment, for recursive references
  let lenv := Env.add_ident lenv fun_id sto new_ty
  -- Take into account attributes from previous declarations of the function
  let attr ← (attributes_of_type genv new_ty : M Attributes)
  /- Additional checks on function parameters. They should have a complete
     type and additionally they should have an identifier. In both cases a
     fatal error is raised in order to avoid problems at later places. -/
  let add_param (env : Env.T) (p : Ident × Typ) : EM Env.T := do
    let (id, ty) := p
    if id.name == "" then
      fatal_error loc "parameter name omitted"
    if ← wrap (incomplete_type env ty) loc then
      fatal_error loc s!"parameter '{id.name}' has incomplete type {← print_typ env ty}"
    return Env.add_ident env id .Storage_default ty
  /- Enter parameters and extra declarations in the local environment.
     For K&R functions this hasn't been done yet.  For prototyped functions
     this has been done by [elab_fundef_name] already, but some parameter
     may have been shadowed by the function name, while it should be the
     other way around, e.g. [int f(int f) { return f+1; }]. -/
  let lenv ← params.foldlM add_param lenv
  let lenv := extra_decls.foldl (fun e d => Env.add_ident e d.id d.sto d.ty) lenv
  -- Define "__func__" and enter it in the local environment
  let (func_ty, func_init) := __func__type_and_init s
  let (func_id, _, lenv, func_ty, _) ←
    enter_or_refine_ident true loc lenv "__func__" .Storage_static func_ty
  emit_elab false loc (.Gdecl (.mk .Storage_static func_id func_ty (some func_init)))
  -- Elaborate function body
  let body1 ← elab_funbody ty_ret vararg (inline && sto != .Storage_static) lenv body
  -- Analyse it for returns
  let (can_return, can_fallthrough) ← (Cflow.function_returns lenv body1 : M _)
  -- Special treatment of the "main" function.
  let body2 ← if s == "main" then do
      if inline then
        error loc "'main' is not allowed to be declared inline"
      if noret then
        warning loc .Unnamed "'main' is not allowed to be declared _Noreturn"
      match ← (unroll genv ty_ret : M Typ) with
      | .TInt .IInt [] =>
        -- Add implicit "return 0;" at end of function body.
        pure (sseq Cutil.no_loc body1 (.mk (.Sreturn (some (intconst 0 .IInt))) Cutil.no_loc))
      | _ =>
        warning loc .Main_return_type "return type of 'main' should be 'int'"
        pure body1
    else do
      -- For non-"main" functions, warn if the body can fall through and the
      -- return type is not "void".
      if can_fallthrough && !(← (is_void_type genv ty_ret : M Bool)) then
        warning loc .Return_type "control reaches end of non-void function"
      pure body1
  -- Add the extra declarations if any
  let body3 := if extra_decls.isEmpty then body2 else
    .mk (.Sblock (extra_decls.map (fun d => Stmt.mk (.Sdecl d) Cutil.no_loc) ++ [body2])) Cutil.no_loc
  -- Handling of _Noreturn and of attribute("noreturn")
  if noret then
    warning loc .Celeven_extension "_Noreturn functions are a C11 extension"
  if (noret || !(find_custom_attributes ["noreturn", "__noreturn__"] attr).isEmpty)
      && can_return then
    warning loc .Invalid_noreturn s!"function '{s}' declared 'noreturn' should not return"
  -- Build and emit function definition
  let fn : Fundef :=
    { fd_storage := sto1
      fd_inline := inline
      fd_name := fun_id
      fd_attrib := if noret then add_attributes [.Attr "noreturn" []] attr else attr
      fd_ret := ty_ret
      fd_params := params
      fd_vararg := vararg
      fd_locals := []
      fd_body := body3 }
  emit_elab true loc (.Gfundef fn)
  return genv

/-- Definitions -/
partial def elab_decdef (for_loop local_ nonstatic_inline : Bool) (env : Env.T)
    (ing : Cabs.InitNameGroup) (loc : Loc) : EM (List Decl × Env.T) := do
  let (spec, namelist) := ing
  let (sto, inl, noret, tydef, bty, env') ← elab_specifier namelist.isEmpty loc env spec
  -- Sanity checks on storage class
  if tydef then
    if sto != .Storage_default then
      error loc "non-default storage class on 'typedef' definition"
    if namelist.isEmpty then
      warning loc .Missing_declarations "typedef requires a name"
  else
    if (sto == .Storage_auto || sto == .Storage_register) && !local_ then
      fatal_error loc s!"illegal storage class {name_of_storage_class sto} on file-scoped variable"
    if sto != .Storage_default && namelist.isEmpty then
      warning loc .Missing_declarations "declaration does not declare anything"
  let elab_one_name (acc : List Decl × Env.T) : Cabs.InitName → EM (List Decl × Env.T)
    | .Init_name (.Name id decl attr loc) init => do
      let (decls, env) := acc
      let ((ty, _), env1) ← elab_type_declarator false false loc env bty decl
      let a ← elab_attributes env attr
      let has_fun_typ ← (is_function_type env ty : M Bool)
      if for_loop && (has_fun_typ || sto == .Storage_extern || sto == .Storage_static || tydef) then
        error loc "declaration of non-local variable in 'for' loop"
      if has_fun_typ then
        if noret then
          warning loc .Celeven_extension "_Noreturn functions are a C11 extension"
      else
        if inl then
          error loc "'inline' can only appear on functions"
        if noret then
          error loc "'_Noreturn' can only appear on functions"
      let a' := if noret then add_attributes [.Attr "noreturn" []] a else a
      if (← (has_std_alignas env ty : M Bool)) && has_fun_typ then
        error loc s!"alignment specified for function '{id}'"
      let decl := (id, ← (add_attributes_type a' ty : M Typ), init)
      if tydef then
        return (decls, ← enter_typedef loc env1 sto decl)
      else
        enter_decdef local_ nonstatic_inline loc sto (decls, env1) decl
  let (decls, env') ← namelist.foldlM elab_one_name ([], env')
  return (decls.reverse, env')

partial def elab_definition (for_loop local_ nonstatic_inline : Bool) (env : Env.T) :
    Cabs.Definition → EM (List Decl × Env.T)
  -- "int f(int x) { ... }"
  -- "int f(x, y) double y; { ... }"
  | .FUNDEF spec name defs body loc => do
    -- This should actually never be triggered, catched by pre-parser
    if local_ then error loc "function definition is not allowed here"
    let env1 ← elab_fundef env spec name defs body loc
    return ([], env1)
  -- "int x = 12, y[10], *z"
  | .DECDEF init_name_group loc =>
    elab_decdef for_loop local_ nonstatic_inline env init_name_group loc
  -- pragma
  | .PRAGMA s loc => do
    if local_ then
      warning loc .Unnamed "pragmas are ignored inside functions"
    else
      emit_elab false loc (.Gpragma s)
    return ([], env)
  -- static assertion
  | .STATIC_ASSERT exp loc_exp msg loc_msg loc => do
    elab_static_assert env exp loc_exp msg loc_msg loc
    return ([], env)

/-- Elaboration of statements -/
partial def elab_stmt (env : Env.T) (ctx : ElabContext) : Cabs.Statement → EM (Stmt × Env.T)

  -- 6.8.3 Expression statements

  | .COMPUTATION a loc => do
    let (a, env) ← elab_expr ctx loc env a
    return (.mk (.Sdo a) (elab_loc loc), env)

  -- 6.8.1 Labeled statements

  | .LABEL lbl s1 loc => do
    let (s1, env) ← elab_stmt env ctx s1
    return (.mk (.Slabeled (.Slabel lbl) s1) (elab_loc loc), env)

  | .CASE a s1 loc => do
    let (a', env) ← elab_expr ctx loc env a
    let a' ← match ctx.ctx_in_switch with
      | none => do
        error loc "'case' statement not in switch statement"
        pure a'
      | some ty@(.TInt ..) => pure (ecast ty a')
      | _ => pure a'
    let n ← match ← (Ceval.integer_expr env a' : M _) with
      | none => do
        error loc "expression of 'case' label is not an integer constant expression"
        pure 0
      | some n => pure n
    let (s1, env) ← elab_stmt env ctx s1
    return (.mk (.Slabeled (.Scase a' n) s1) (elab_loc loc), env)

  | .DEFAULT s1 loc => do
    if ctx.ctx_in_switch.isNone then
      error loc "'case' statement not in switch statement"
    let (s1, env) ← elab_stmt env ctx s1
    return (.mk (.Slabeled .Sdefault s1) (elab_loc loc), env)

  -- 6.8.2 Compound statements

  | .BLOCK b loc => elab_block loc env ctx b

  -- 6.8.4 Conditional statements

  | .If a s1 s2 loc => do
    let (a', env') ← elab_expr ctx loc (← (Env.new_scope env : M Env.T)) a
    if !(← (is_scalar_type env' a'.etyp : M Bool)) then
      error loc s!"controlling expression of 'if' does not have scalar type ({← print_typ env' a'.etyp} invalid)"
    let s1' ← elab_stmt_new_scope env' ctx s1
    let s2' ← match s2 with
      | none => pure sskip
      | some s2 => elab_stmt_new_scope env' ctx s2
    return (.mk (.Sif a' s1' s2') (elab_loc loc), env)

  -- 6.8.5 Iterative statements

  | .WHILE a s1 loc => do
    let (a', env') ← elab_expr ctx loc (← (Env.new_scope env : M Env.T)) a
    if !(← (is_scalar_type env' a'.etyp : M Bool)) then
      error loc s!"controlling expression of 'while' does not have scalar type ({← print_typ env' a'.etyp} invalid)"
    let s1' ← elab_stmt_new_scope env' (ctx_loop ctx) s1
    return (.mk (.Swhile a' s1') (elab_loc loc), env)

  | .DOWHILE a s1 loc => do
    let s1' ← elab_stmt_new_scope env (ctx_loop ctx) s1
    let (a', env') ← elab_expr ctx loc (← (Env.new_scope env : M Env.T)) a
    if !(← (is_scalar_type env' a'.etyp : M Bool)) then
      error loc s!"controlling expression of 'while' does not have scalar type ({← print_typ env' a'.etyp} invalid)"
    return (.mk (.Sdowhile s1' a') (elab_loc loc), env)

  | .FOR fc a2 a3 s1 loc => do
    let env' ← (Env.new_scope env : M Env.T)
    let (a1', env_decls, decls') ← match fc with
      | some (.FC_EXP a1) => do
        let (a1, env) ← elab_for_expr ctx loc env' (some a1)
        pure (a1, env, none)
      | none => do
        let (a1, env) ← elab_for_expr ctx loc env' none
        pure (a1, env, none)
      | some (.FC_DECL def_) => do
        let (dcl, env') ← elab_definition true true ctx.ctx_nonstatic_inline env' def_
        let loc := elab_loc (Cabshelper.get_definitionloc def_)
        pure (sskip, env', some (dcl.map fun d => Stmt.mk (.Sdecl d) loc))
    let (a2', env_test) ← match a2 with
      | none => pure (intconst 1 .IInt, env_decls)
      | some a2 => elab_expr ctx loc env_decls a2
    if !(← (is_scalar_type env_test a2'.etyp : M Bool)) then
      error loc s!"controlling expression of 'for' does not have scalar type ({← print_typ env a2'.etyp} invalid)"
    let (a3', env_for) ← elab_for_expr ctx loc env_test a3
    let s1' ← elab_stmt_new_scope env_for (ctx_loop ctx) s1
    let sfor : Stmt := .mk (.Sfor a1' a2' a3' s1') (elab_loc loc)
    match decls' with
    | none => return (sfor, env)
    | some sl => return (.mk (.Sblock (sl ++ [sfor])) (elab_loc loc), env)

  -- 6.8.4 Switch statement

  | .SWITCH a s1 loc => do
    let (a', env') ← elab_expr ctx loc (← (Env.new_scope env : M Env.T)) a
    if !(← (is_integer_type env' a'.etyp : M Bool)) then
      error loc s!"controlling expression of 'switch' does not have integer type ({← print_typ env' a'.etyp} invalid)"
    let s1' ← elab_stmt_new_scope env'
      (ctx_switch ctx (← (unary_conversion env a'.etyp : M Typ))) s1
    check_switch_cases s1'
    return (.mk (.Sswitch a' s1') (elab_loc loc), env)

  -- 6.8.6 Break and continue statements

  | .BREAK loc => do
    if !ctx.ctx_break then
      error loc "'break' statement not in loop or switch statement"
    return (.mk .Sbreak (elab_loc loc), env)

  | .CONTINUE loc => do
    if !ctx.ctx_continue then
      error loc "'continue' statement not in loop statement"
    return (.mk .Scontinue (elab_loc loc), env)

  -- 6.8.6 Return statements

  | .RETURN a loc => do
    let (a', env) ← elab_opt_expr ctx loc env a
    let rt := ctx.ctx_return_typ
    match ← (unroll env rt : M Typ), a' with
    | .TVoid _, none => pure ()
    | .TVoid _, some _ => error loc "'return' with a value in a function returning void"
    | _, none => warning loc .Return_type "'return' with no value, in a function returning non-void"
    | _, some b =>
      if !(← wrap (valid_assignment env b rt) loc) then
        if ← wrap (valid_cast env b.etyp rt) loc then
          if ← wrap (int_pointer_conversion env b.etyp rt) loc then
            warning loc .Int_conversion s!"incompatible integer-pointer conversion: returning {← print_typ env b.etyp} from a function with result type {← print_typ env rt}"
          else
            warning loc .Unnamed s!"incompatible conversion: returning {← print_typ env b.etyp} from a function with result type {← print_typ env rt}"
        else
          error loc s!"returning {← print_typ env b.etyp} from a function with incompatible result type {← print_typ env rt}"
    return (.mk (.Sreturn a') (elab_loc loc), env)

  -- 6.8.6 Goto statements

  | .GOTO lbl loc => do
    if !ctx.ctx_labels.contains lbl then
      error loc s!"use of undeclared label '{lbl}'"
    return (.mk (.Sgoto lbl) (elab_loc loc), env)

  -- 6.8.3 Null statements

  | .NOP loc => return (.mk .Sskip (elab_loc loc), env)

  -- Traditional extensions

  | .ASM cv_specs wide chars outputs inputs flags loc => do
    let a ← elab_cvspecs env cv_specs
    let s ← elab_simple_string loc wide chars
    let (outputs, env) ← mmap (elab_asm_operand ctx loc) env outputs
    for (_, _, e) in outputs do
      if !(← (is_modifiable_lvalue env e : M Bool)) then
        error loc "asm output is not a modifiable l-value"
    let (inputs, env) ← mmap (elab_asm_operand ctx loc) env inputs
    let flags ← flags.mapM fun (w, c) => elab_simple_string loc w c
    return (.mk (.Sasm a s outputs inputs flags) (elab_loc loc), env)

  -- Unsupported

  | .DEFINITION def_ => do
    error (Cabshelper.get_definitionloc def_) "ill-placed definition"
    return (sskip, env)

/-- Elaborate a statement as a block whose scope is a strict subset of the
    scope of its enclosing block. -/
partial def elab_stmt_new_scope (env : Env.T) (ctx : ElabContext) (s : Cabs.Statement) :
    EM Stmt := do
  return (← elab_stmt (← (Env.new_scope env : M Env.T)) ctx s).1

partial def elab_block (loc : Loc) (env : Env.T) (ctx : ElabContext) (b : List Cabs.Statement) :
    EM (Stmt × Env.T) := do
  let (b', _) ← elab_block_body (← (Env.new_scope env : M Env.T)) ctx b
  return (.mk (.Sblock b') (elab_loc loc), env)

partial def elab_block_body (env : Env.T) (ctx : ElabContext) :
    List Cabs.Statement → EM (List Stmt × Env.T)
  | [] => return ([], env)
  | .DEFINITION def_ :: sl1 => do
    let (dcl, env') ← elab_definition false true ctx.ctx_nonstatic_inline env def_
    let loc := elab_loc (Cabshelper.get_definitionloc def_)
    let dcl := dcl.map fun d => Stmt.mk (.Sdecl d) loc
    let (sl1', env') ← elab_block_body env' ctx sl1
    return (dcl ++ sl1', env')
  | s :: sl1 => do
    let (s', env) ← elab_stmt env ctx s
    let (sl1', env) ← elab_block_body env ctx sl1
    return (s' :: sl1', env)

/-- Elaboration of a function body.  Return the corresponding C statement. -/
partial def elab_funbody (return_typ : Typ) (vararg nonstatic_inline : Bool) (env : Env.T)
    (b : Cabs.Statement) : EM Stmt := do
  let ctx : ElabContext :=
    { ctx_return_typ := return_typ
      ctx_labels := ← stmt_labels b
      ctx_break := false
      ctx_continue := false
      ctx_in_switch := none
      ctx_vararg := vararg
      ctx_nonstatic_inline := nonstatic_inline }
  -- The function body appears as a block in the AST but should not create a
  -- new scope.  Instead, the scope used for function parameters must be used
  -- for the body.
  match b with
  | .BLOCK b loc =>
    let (b', _) ← elab_block_body env ctx b
    return .mk (.Sblock b') (elab_loc loc)
  | _ => throw (.Failure "assert false: elab_funbody")

end

/-! ### Entry point -/

/-- `elab_file prog`, with the initial environment `init` (builtins) -/
def elab_file (init : Env.InitEnv) (prog : List Cabs.Definition)
    (option_Obranchless : Bool := false) : M Program := do
  let act : EM Program := do
    reset
    modify fun st => { st with initial_env := init.initial }
    let env := init.initial
    let mut env := env
    for d in prog do
      env := (← elab_definition false false false env d).2
    elaborated_program
  let p ← act.run' {}
  let env0 := init.initial
  Checks.unused_variables env0 p
  Checks.unknown_attrs_program env0 p
  Checks.non_linear_conditional option_Obranchless env0 p
  return p

end Elab
end CParser
end CC
