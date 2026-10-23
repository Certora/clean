/-
  Port of `cparser/Unblock.ml`: simplification of blocks and initializers
  within functions (block-scoped declarations are moved to the function's
  locals, initializers become assignments, compound literals become fresh
  variables).  Assumes nothing; produces unblocked code.

  * The global references `local_variables`, `global_variables`,
    `curr_fun_id` and `next_scope_id` are the state of the monad `UM`.
  * `Clflags.option_g` is the explicit argument `option_g`.  The calls to
    the debug-information module `Debug` (`add_lvar_scope`, `enter_scope`,
    `enter_function_scope`), which only record scopes for DWARF output, are
    omitted: `debug/*` is not ported.
  * `debug_id` and `debug_ty` (identifiers created when the OCaml module is
    initialised) are created by `program`.
-/
import CCLib.cparser.Cutil

namespace CC
namespace CParser
namespace Unblock

open C Cutil

structure UState where
  local_variables : List Decl := []
  global_variables : List Decl := []
  curr_fun_id : Int := 0
  next_scope_id : Int := 0
  debug_id : Ident := default
  debug_ty : Typ := default
  option_g : Bool := false
  deriving Inhabited

abbrev UM := StateT UState M

/-- Convert an initializer to a list of assignment expressions. -/
partial def local_initializer (env : Env.T) (path : Exp) (init : Init) (k : List Exp) :
    M (List Exp) := do
  match init with
  | .Init_single e => return .mk (.EBinop .Oassign path e path.etyp) path.etyp :: k
  | .Init_array il =>
      let (ty_elt, sz) ← match ← unroll env path.etyp with
        | .TArray ty_elt (some sz) _ => pure (ty_elt, sz)
        | .TArray ty_elt none _ =>
            if il.isEmpty then pure (ty_elt, 0)
            else Diagnostics.fatal_error Diagnostics.no_loc "wrong type for array initializer"
        | _ => Diagnostics.fatal_error Diagnostics.no_loc "wrong type for array initializer"
      let rec array_init (pos : Int64) (il : List Init) (fuel : Nat) : M (List Exp) := do
        if pos ≥ sz then return k
        match fuel with
        | 0 => return k
        | fuel + 1 =>
          let (i1, il') ← match il with
            | [] => do
                match ← default_init env ty_elt with
                | some i => pure (i, [])
                | none => throw (.Failure "Cutil.No_default_init")
            | i1 :: il' => pure (i1, il')
          local_initializer env
            (.mk (.EBinop .Oindex path (intconst pos .IInt) (.TPtr ty_elt [])) ty_elt) i1
            (← array_init (pos + 1) il' fuel)
      array_init 0 il sz.toInt.toNat
  | .Init_struct _ fil =>
      fil.foldrM (fun (fld, i) k =>
        local_initializer env (.mk (.EUnop (.Odot fld.fld_name) path) fld.fld_typ) i k) k
  | .Init_union _ fld i =>
      local_initializer env (.mk (.EUnop (.Odot fld.fld_name) path) fld.fld_typ) i k

/-- Prepend assignments to the given statement. -/
def add_inits_stmt (loc : Location) (inits : List Exp) (s : Stmt) : Stmt :=
  inits.foldr (fun e s => sseq loc (.mk (.Sdo e) loc) s) s

/-- Remove top-level `const` attribute (also on element type of arrays). -/
def remove_const (env : Env.T) (ty : Typ) : M Typ := remove_attributes_type env [.AConst] ty

/-- Process a compound literal `(ty) { init }`. -/
def process_compound_literal (islocal : Bool) (env : Env.T) (ty : Typ) (init : Init) :
    UM (List Exp × Exp) := do
  let id ← Env.fresh_ident "__compound"
  if islocal then
    let ty' ← remove_const env ty
    let e : Exp := .mk (.EVar id) ty'
    modify fun s => { s with local_variables := .mk .Storage_default id ty' none :: s.local_variables }
    return (← local_initializer env e init [], e)
  else
    modify fun s =>
      { s with global_variables := .mk .Storage_static id ty (some init) :: s.global_variables }
    return ([], .mk (.EVar id) ty)

mutual
/-- Elimination of compound literals within an expression. -/
partial def expand_expr (islocal : Bool) (env : Env.T) (e : Exp) : UM Exp := do
  let (e', inits) ← (expand e).run []
  return ecommalist inits e'
where
  expand (e : Exp) : StateT (List Exp) UM Exp := do
    match e.edesc with
    | .EConst _ | .ESizeof _ | .EAlignof _ | .EVar _ => return e
    | .EUnop op e1 => return .mk (.EUnop op (← expand e1)) e.etyp
    | .EBinop op e1 e2 ty =>
        let e1' ← expand e1
        let e2' ← match op with
          | .Ocomma | .Ologand | .Ologor => (expand_expr islocal env e2 : UM Exp)
          | _ => expand e2
        return .mk (.EBinop op e1' e2' ty) e.etyp
    | .EConditional e1 e2 e3 =>
        let e1' ← expand e1
        return .mk (.EConditional e1' (← (expand_expr islocal env e2 : UM Exp))
          (← (expand_expr islocal env e3 : UM Exp))) e.etyp
    | .ECast ty e1 => return .mk (.ECast ty (← expand e1)) e.etyp
    | .ECompound ty ie =>
        let ie' ← (expand_init islocal env ie : UM Init)
        let (l, e') ← (process_compound_literal islocal env ty ie' : UM _)
        modify fun inits => l ++ inits
        return e'
    | .ECall e1 el =>
        let e1' ← expand e1
        return .mk (.ECall e1' (← el.mapM expand)) e.etyp

/-- Elimination of compound literals within an initializer. -/
partial def expand_init (islocal : Bool) (env : Env.T) (i : Init) : UM Init := do
  match i with
  | .Init_single (.mk (.ECompound _ i'@(.Init_struct ..)) _)
  | .Init_single (.mk (.ECompound _ i'@(.Init_union ..)) _) => expand_init islocal env i'
  | .Init_single e => return .Init_single (← expand_expr islocal env e)
  | .Init_array il => return .Init_array (← il.mapM (expand_init islocal env))
  | .Init_struct id flds =>
      return .Init_struct id (← flds.mapM fun (f, i) => do return (f, ← expand_init islocal env i))
  | .Init_union id fld i => return .Init_union id fld (← expand_init islocal env i)
end

/-! Insertion of debug annotation, for `-g` mode -/

def debug_annot (kind : Int64) (args : List Exp) : UM Stmt := do
  let s ← get
  return .mk (.Sdo (.mk (.ECall (.mk (.EVar s.debug_id) s.debug_ty) (intconst kind .IInt :: args))
    (.TVoid []))) no_loc

def string_const (str : String) : Exp :=
  let c := Constant.CStr str
  .mk (.EConst c) (type_of_constant c)

def integer_const (n : Int) : Exp := intconst (Int64.ofInt n) .IInt

/-- Line number annotation: `__builtin_debug(1, "#line:filename:lineno")` -/
def debug_lineno (loc : Location) : UM Stmt :=
  debug_annot 1 [string_const s!"#line:{loc.1}:{loc.2}"]

def empty_string : Exp := string_const ""

/-- Scope annotation: `__builtin_debug(6, "", scope1, ..., scopeN)` -/
def debug_scope (ctx : List Int) : UM Stmt :=
  debug_annot 6 (empty_string :: (ctx.map integer_const).reverse)

/-- Add line number debug annotation if the line number changes.  Add scope
    debug annotation regardless. -/
def add_lineno (ctx : List Int) (prev_loc this_loc : Location) (s : Stmt) : UM Stmt := do
  if (← get).option_g then
    let s' ← if this_loc != prev_loc && this_loc != no_loc then
        do pure (sseq no_loc (← debug_lineno this_loc) s)
      else pure s
    return sseq no_loc (← debug_scope ctx) s'
  else return s

/-- Generate fresh scope identifiers, for blocks that contain at least one
    declaration -/
def block_contains_decl (sl : List Stmt) : Bool :=
  sl.any fun s => match s.sdesc with | .Sdecl _ => true | _ => false

def new_scope_id : UM Int := do
  modify fun s => { s with next_scope_id := s.next_scope_id + 1 }
  return (← get).next_scope_id

/-- Process a block-scoped variable declaration. -/
def process_decl (loc : Location) (env : Env.T) (_ctx : List Int) (d : Decl) (k : Stmt) :
    UM Stmt := do
  let .mk sto id ty optinit := d
  let ty' ← remove_const env ty
  modify fun s => { s with local_variables := .mk sto id ty' none :: s.local_variables }
  match optinit with
  | none => return k
  | some init =>
      let init' ← expand_init true env init
      let l ← local_initializer env (.mk (.EVar id) ty') init' []
      return add_inits_stmt loc l k

mutual
/-- Simplification of blocks within a statement -/
partial def unblock_stmt (env : Env.T) (ctx : List Int) (ploc : Location) (s : Stmt) :
    UM Stmt := do
  let loc := s.sloc
  let mk (d : StmtDesc) : Stmt := .mk d loc
  match s.sdesc with
  | .Sskip => return s
  | .Sdo e => add_lineno ctx ploc loc (mk (.Sdo (← expand_expr true env e)))
  | .Sseq s1 s2 =>
      return mk (.Sseq (← unblock_stmt env ctx ploc s1) (← unblock_stmt env ctx s1.sloc s2))
  | .Sif e s1 s2 =>
      add_lineno ctx ploc loc (mk (.Sif (← expand_expr true env e)
        (← unblock_stmt env ctx loc s1) (← unblock_stmt env ctx loc s2)))
  | .Swhile e s1 =>
      add_lineno ctx ploc loc (mk (.Swhile (← expand_expr true env e)
        (← unblock_stmt env ctx loc s1)))
  | .Sdowhile s1 e =>
      add_lineno ctx ploc loc (mk (.Sdowhile (← unblock_stmt env ctx loc s1)
        (← expand_expr true env e)))
  | .Sfor s1 e s2 s3 =>
      add_lineno ctx ploc loc (mk (.Sfor (← unblock_stmt env ctx loc s1)
        (← expand_expr true env e) (← unblock_stmt env ctx loc s2)
        (← unblock_stmt env ctx loc s3)))
  | .Sbreak | .Scontinue => return s
  | .Sswitch e s1 =>
      add_lineno ctx ploc loc (mk (.Sswitch (← expand_expr true env e)
        (← unblock_stmt env ctx loc s1)))
  | .Slabeled lbl s1 =>
      let s1' ← if loc != s1.sloc then
          do add_lineno ctx ploc loc (← unblock_stmt env ctx loc s1)
        else unblock_stmt env ctx ploc s1
      return mk (.Slabeled lbl s1')
  | .Sgoto _ | .Sreturn none => add_lineno ctx ploc loc s
  | .Sreturn (some e) => add_lineno ctx ploc loc (mk (.Sreturn (some (← expand_expr true env e))))
  | .Sblock sl =>
      let ctx' ← if block_contains_decl sl then do
          let id ← new_scope_id
          pure (id :: ctx)
        else pure ctx
      unblock_block env ctx' ploc sl
  | .Sdecl _ => assertFalse "Unblock.unblock_stmt"
  | .Sasm attr template outputs inputs clob =>
      let op : AsmOperand → UM AsmOperand := fun (lbl, cstr, e) => do
        return (lbl, cstr, ← expand_expr true env e)
      add_lineno ctx ploc loc (mk (.Sasm attr template (← outputs.mapM op) (← inputs.mapM op) clob))

partial def unblock_block (env : Env.T) (ctx : List Int) (ploc : Location) :
    List Stmt → UM Stmt
  | [] => return sskip
  | s :: sl =>
    match s.sdesc with
    | .Sdecl d => do
        add_lineno ctx ploc s.sloc
          (← process_decl s.sloc env ctx d (← unblock_block env ctx s.sloc sl))
    | _ => do
        return sseq s.sloc (← unblock_stmt env ctx ploc s) (← unblock_block env ctx s.sloc sl)
end

/-- Simplification of blocks and compound literals within a function -/
def unblock_fundef (env : Env.T) (f : Fundef) : UM Fundef := do
  modify fun s => { s with local_variables := [], curr_fun_id := f.fd_name.stamp }
  let body ← unblock_stmt env [] no_loc f.fd_body
  let decls := (← get).local_variables
  modify fun s => { s with local_variables := [] }
  return { f with fd_locals := f.fd_locals ++ decls, fd_body := body }

/-- Simplification of compound literals within a top-level declaration -/
def unblock_decl (env : Env.T) (d : Decl) : UM (List Decl) := do
  let .mk sto id ty optinit := d
  match optinit with
  | none => return [d]
  | some init =>
      modify fun s => { s with global_variables := [] }
      let init' ← expand_init false env init
      let decls := (← get).global_variables.reverse
      modify fun s => { s with global_variables := [] }
      return decls ++ [.mk sto id ty (some init')]

/-- Unblocking and simplification for whole files. -/
def unblock_glob (env0 : Env.T) (p : List Globdecl) : UM (List Globdecl) := do
  let mut env := env0
  let mut accu : Array Globdecl := #[]
  for g in p do
    match g.gdesc with
    | .Gdecl d =>
        for d' in ← unblock_decl env d do
          accu := accu.push { g with gdesc := .Gdecl d' }
    | .Gfundef f =>
        accu := accu.push { g with gdesc := .Gfundef (← unblock_fundef env f) }
    | .Gcompositedecl su id attr =>
        env := Env.add_composite env id (composite_info_decl su attr)
        accu := accu.push g
    | .Gcompositedef su id attr fl =>
        env := Env.add_composite env id (← composite_info_def env su attr fl)
        accu := accu.push g
    | .Gtypedef id ty =>
        env := Env.add_typedef env id ty
        accu := accu.push g
    | .Genumdef id attr members =>
        env := Env.add_enum env id { ei_members := members, ei_attr := attr }
        accu := accu.push g
    | .Gpragma _ => accu := accu.push g
  return accu.toList

/-- Entry point.  `env0` is `Env.initial ()`. -/
def program (option_g : Bool) (env0 : Env.T) (p : Program) : M Program := do
  let debug_id ← Env.fresh_ident "__builtin_debug"
  let kind ← Env.fresh_ident "kind"
  let debug_ty : Typ := .TFun (.TVoid []) (some [(kind, .TInt .IInt [])]) true []
  let st : UState := { debug_id, debug_ty, option_g }
  let (gl, _) ← (unblock_glob env0 p).run st
  return { gloc := no_loc, gdesc := .Gdecl (.mk .Storage_extern debug_id debug_ty none) } :: gl

end Unblock
end CParser
end CC
