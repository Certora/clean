/-
  Port of `cparser/Checks.ml`: AST traversals and the warnings emitted
  after elaboration (unknown attributes, unused variables and parameters,
  conditional expressions that cannot be linearized).

  Traversal callbacks run in the front-end monad `M`.  `traverse_program`
  starts from `Env.initial ()` in OCaml; here the initial environment is
  the argument `env0`.  `Clflags.option_Obranchless` is the argument
  `option_Obranchless` of `non_linear_conditional`.
-/
import CCLib.cparser.Cutil

namespace CC
namespace CParser
namespace Checks

open C Cutil Diagnostics

/-! AST traversal functions -/

partial def fold_over_stmt_loc {α} (expr : α → Location → Exp → M α)
    (decl : α → Location → Decl → M α) (a : α) (s : Stmt) : M α :=
  fold a s
where
  asm_operands (a : α) (loc : Location) (l : List AsmOperand) : M α :=
    l.foldlM (fun a (_, _, e) => expr a loc e) a
  fold (a : α) (s : Stmt) : M α := do
    match s.sdesc with
    | .Sskip | .Sbreak | .Scontinue | .Sgoto _ | .Sreturn none => return a
    | .Slabeled _ s1 => fold a s1
    | .Sreturn (some e) => expr a s.sloc e
    | .Sasm _ _ outs ins _ => asm_operands (← asm_operands a s.sloc outs) s.sloc ins
    | .Sdo e => expr a s.sloc e
    | .Sif e s1 s2 => fold (← fold (← expr a s.sloc e) s1) s2
    | .Sseq s1 s2 => fold (← fold a s1) s2
    | .Sfor s1 e s2 s3 => fold (← fold (← expr (← fold a s1) s.sloc e) s2) s3
    | .Swhile e s1 => fold (← expr a s.sloc e) s1
    | .Sdowhile s1 e => expr (← fold a s1) s.sloc e
    | .Sswitch e s1 => fold (← expr a s.sloc e) s1
    | .Sblock sl => sl.foldlM fold a
    | .Sdecl d => decl a s.sloc d

def iter_over_stmt_loc (expr : Location → Exp → M Unit := fun _ _ => pure ())
    (decl : Location → Decl → M Unit := fun _ _ => pure ()) (s : Stmt) : M Unit :=
  fold_over_stmt_loc (fun () loc e => expr loc e) (fun () loc d => decl loc d) () s

def fold_over_stmt {α} (expr : α → Exp → M α) (decl : α → Location → Decl → M α) (a : α)
    (s : Stmt) : M α :=
  fold_over_stmt_loc (fun a _ e => expr a e) decl a s

def iter_over_stmt (expr : Exp → M Unit := fun _ => pure ())
    (decl : Location → Decl → M Unit := fun _ _ => pure ()) (s : Stmt) : M Unit :=
  fold_over_stmt_loc (fun () _ e => expr e) (fun () loc d => decl loc d) () s

partial def fold_over_init {α} (expr : α → Exp → M α) (a : α) (i : Init) : M α :=
  match i with
  | .Init_single e => expr a e
  | .Init_array il => il.foldlM (fold_over_init expr) a
  | .Init_struct _ sl => sl.foldlM (fun a (_, i) => fold_over_init expr a i) a
  | .Init_union _ _ ui => fold_over_init expr a ui

def iter_over_init (expr : Exp → M Unit) (i : Init) : M Unit :=
  fold_over_init (fun () e => expr e) () i

def fold_over_decl {α} (expr : α → Exp → M α) (a : α) (_loc : Location) : Decl → M α
  | .mk _ _ _ (some i) => fold_over_init expr a i
  | .mk _ _ _ none => pure a

/-- The optional arguments of `traverse_program`. -/
structure TraverseHooks where
  decl : Env.T → Location → Decl → M Unit := fun _ _ _ => pure ()
  fundef : Env.T → Location → Fundef → M Unit := fun _ _ _ => pure ()
  compositedecl : Env.T → Location → StructOrUnion → Ident → Attributes → M Unit :=
    fun _ _ _ _ _ => pure ()
  compositedef : Env.T → Location → StructOrUnion → Ident → Attributes → List Field →
      M Unit := fun _ _ _ _ _ _ => pure ()
  typedef : Env.T → Location → Ident → Typ → M Unit := fun _ _ _ _ => pure ()
  enum : Env.T → Location → Ident → Attributes → List Enumerator → M Unit :=
    fun _ _ _ _ _ => pure ()
  pragma : Env.T → Location → String → M Unit := fun _ _ _ => pure ()

def traverse_program (h : TraverseHooks) (env0 : Env.T) (p : Program) : M Unit := do
  let mut env := env0
  for g in p do
    env ← match g.gdesc with
      | .Gdecl d@(.mk sto id ty _) => do
          h.decl env g.gloc d; pure (Env.add_ident env id sto ty)
      | .Gfundef f => do
          h.fundef env g.gloc f; pure (Env.add_ident env f.fd_name f.fd_storage (fundef_typ f))
      | .Gcompositedecl su id attr => do
          h.compositedecl env g.gloc su id attr
          pure (Env.add_composite env id (composite_info_decl su attr))
      | .Gcompositedef su id attr fl => do
          h.compositedef env g.gloc su id attr fl
          pure (Env.add_composite env id (← composite_info_def env su attr fl))
      | .Gtypedef id ty => do
          h.typedef env g.gloc id ty; pure (Env.add_typedef env id ty)
      | .Genumdef id attr members => do
          h.enum env g.gloc id attr members
          pure (Env.add_enum env id { ei_members := members, ei_attr := attr })
      | .Gpragma s => do h.pragma env g.gloc s; pure env

/-! Unknown attributes warning -/

def unknown_attrs (loc : Location) (attrs : Attributes) : M Unit :=
  attrs.forM fun attr => do
    if (← class_of_attribute attr) == .Attr_unknown then
      warning loc .Unknown_attribute s!"unknown attribute '{name_of_attribute attr}' ignored"

def unknown_attrs_typ (env : Env.T) (loc : Location) (ty : Typ) : M Unit := do
  unknown_attrs loc (← attributes_of_type env ty)

def unknown_attrs_decl (env : Env.T) (loc : Location) : Decl → M Unit
  | .mk _ _ ty _ => unknown_attrs_typ env loc ty

def unknown_attrs_stmt (env : Env.T) (s : Stmt) : M Unit :=
  iter_over_stmt (decl := unknown_attrs_decl env) (s := s)

def unknown_attrs_program (env0 : Env.T) (p : Program) : M Unit :=
  traverse_program
    { decl := fun env loc d => unknown_attrs_decl env loc d
      fundef := fun env loc f => do
        f.fd_params.forM fun (_, typ) => unknown_attrs_typ env loc typ
        unknown_attrs loc f.fd_attrib
        unknown_attrs_stmt env f.fd_body
        f.fd_locals.forM (unknown_attrs_decl env loc)
      compositedecl := fun _ loc _ _ attr => unknown_attrs loc attr
      compositedef := fun env loc _ _ attr fl => do
        unknown_attrs loc attr
        fl.forM fun fld => unknown_attrs_typ env loc fld.fld_typ
      typedef := fun env loc _ ty => unknown_attrs_typ env loc ty
      enum := fun _ loc _ attr _ => unknown_attrs loc attr }
    env0 p

/-! Unused variables and parameters warning -/

mutual
partial def vars_used_expr (env : IdentSet) (e : Exp) : M IdentSet := do
  match e.edesc with
  | .EConst _ | .ESizeof _ | .EAlignof _ => return env
  | .EVar id => return env.insert id
  | .ECast _ e | .EUnop _ e => vars_used_expr env e
  | .EBinop _ e1 e2 _ => vars_used_expr (← vars_used_expr env e1) e2
  | .EConditional e1 e2 e3 =>
      vars_used_expr (← vars_used_expr (← vars_used_expr env e1) e2) e3
  | .ECompound _ init => vars_used_init env init
  | .ECall e p => p.foldlM vars_used_expr (← vars_used_expr env e)

partial def vars_used_init (env : IdentSet) (init : Init) : M IdentSet :=
  fold_over_init vars_used_expr env init
end

def vars_used_stmt (env : IdentSet) (s : Stmt) : M IdentSet :=
  fold_over_stmt vars_used_expr (fold_over_decl vars_used_expr) env s

def unused_variable (env : Env.T) (used : IdentSet) (loc : Location) : Ident × Typ → M Unit
  | (id, ty) => do
    let attr ← attributes_of_type env ty
    let unused_attr := !(find_custom_attributes ["unused", "__unused__"] attr).isEmpty
    if !(used.contains id || unused_attr) then
      warning loc .Unused_variable s!"unused variable '{id.name}'"

def unused_variables_stmt (env : Env.T) (used : IdentSet) (s : Stmt) : M Unit :=
  iter_over_stmt (decl := fun loc d => unused_variable env used loc (d.id, d.ty)) (s := s)

def unused_variables (env0 : Env.T) (p : Program) : M Unit :=
  traverse_program
    { fundef := fun env loc fd => do
        let used ← vars_used_stmt {} fd.fd_body
        unused_variables_stmt env used fd.fd_body
        fd.fd_params.forM (unused_variable env used loc) }
    env0 p

/-! Warning for conditionals that cannot be transformed into linear code -/

mutual
/-- The set of local variables that do not have their address taken -/
partial def non_stack_locals_expr (vars : IdentSet) (e : Exp) : M IdentSet := do
  match e.edesc with
  | .ECast _ e => non_stack_locals_expr vars e
  | .EUnop .Oaddrof e =>
      match e.edesc with
      | .EVar id => return vars.erase id
      | _ => return vars
  | .EUnop .Oderef e =>
      match e.edesc with
      | .EUnop .Oaddrof e => non_stack_locals_expr vars e
      | _ => non_stack_locals_expr vars e
  | .EUnop _ e => non_stack_locals_expr vars e
  | .EBinop _ e1 e2 _ => non_stack_locals_expr (← non_stack_locals_expr vars e1) e2
  | .EConditional e1 e2 e3 =>
      non_stack_locals_expr (← non_stack_locals_expr (← non_stack_locals_expr vars e1) e2) e3
  | .ECompound _ init => non_stack_locals_init vars init
  | .ECall e p => p.foldlM non_stack_locals_expr (← non_stack_locals_expr vars e)
  | _ => return vars

partial def non_stack_locals_init (vars : IdentSet) (init : Init) : M IdentSet :=
  fold_over_init non_stack_locals_expr vars init
end

def add_vars (env : Env.T) (vars : IdentSet) : Ident × Typ → M IdentSet
  | (id, ty) => do
    let volatile := (← attributes_of_type env ty).contains .AVolatile
    return if !volatile then vars.insert id else vars

def non_stack_locals_stmt (env : Env.T) (vars : IdentSet) (s : Stmt) : M IdentSet :=
  fold_over_stmt non_stack_locals_expr
    (fun vars _ d => do
      let vars ← match d.init with
        | some init => non_stack_locals_init vars init
        | none => pure vars
      add_vars env vars (d.id, d.ty))
    vars s

/-- Check whether an expression is safe and can be always evaluated -/
def safe_cast (env : Env.T) (tfrom tto : Typ) : M Bool := do
  match ← unroll env tfrom, ← unroll env tto with
  | .TInt .., .TInt .. | .TInt .., .TPtr .. | .TInt .., .TEnum ..
  | .TPtr .., .TInt .. | .TPtr .., .TPtr .. | .TPtr .., .TEnum ..
  | .TArray .., .TInt .. | .TArray .., .TPtr .. | .TArray .., .TEnum ..
  | .TFun .., .TInt .. | .TFun .., .TPtr .. | .TFun .., .TEnum ..
  | .TEnum .., .TInt .. | .TEnum .., .TPtr .. | .TEnum .., .TEnum .. => return true
  | .TFloat .., .TFloat .. => return true
  | _, _ => equal_types env tfrom tto

partial def safe_expr (vars : IdentSet) (env : Env.T) (e : Exp) : M Bool :=
  expr e
where
  expr (e : Exp) : M Bool := do
    match e.edesc with
    | .EConst _ | .ESizeof _ | .EAlignof _ | .ECompound .. => return true
    | .EVar id => return vars.contains id || !(← is_scalar_type env e.etyp)
    | .ECast ty e => return (← safe_cast env e.etyp ty) && (← expr e)
    | .EUnop op e => unop op e
    | .EBinop op e1 e2 _ => binop op e1 e2
    | .EConditional .. | .ECall .. => return false
  binop (op : BinaryOperator) (e1 e2 : Exp) : M Bool := do
    let is_long_long_type (ty : Typ) : M Bool := do
      match ← unroll env ty with
      | .TInt .ILongLong _ | .TInt .IULongLong _ => return true
      | _ => return false
    match op with
    | .Oadd | .Osub | .Omul | .Oand | .Oor | .Oxor | .Oshl | .Oshr =>
        return (← expr e1) && (← expr e2)
    | .Oeq | .One | .Olt | .Ogt | .Ole | .Oge =>
        let not_long_long := !(← is_long_long_type e1.etyp) && !(← is_long_long_type e2.etyp)
        return not_long_long && (← expr e1) && (← expr e2)
    | _ => return false
  unop (op : UnaryOperator) (e : Exp) : M Bool := do
    match op with
    | .Ominus | .Onot | .Olognot | .Oplus => expr e
    | .Oaddrof =>
        match e.edesc with
        | .EUnop .Oderef e => expr e
        | .EUnop (.Odot _) e => expr e
        | _ => expr e
    | .Oderef =>
        match e.edesc with
        | .EUnop .Oaddrof e => expr e
        | _ => return false
    | .Odot m =>
        let fld ← field_of_dot_access env e.etyp m
        return ((← is_array_type env fld.fld_typ) || (← is_composite_type env fld.fld_typ))
          && (← expr e)
    | _ => return false

mutual
/-- Check expressions if they contain conditionals that cannot be
    transformed in linear code. -/
partial def non_linear_cond_expr (inner_cond : Bool) (vars : IdentSet) (env : Env.T)
    (loc : Location) (e : Exp) : M Unit := do
  match e.edesc with
  | .EConst _ | .ESizeof _ | .EAlignof _ | .EVar _ => pure ()
  | .ECast _ e | .EUnop _ e => non_linear_cond_expr false vars env loc e
  | .EBinop op e1 e2 _ =>
      let inner_cond := match op with
        | .Ocomma => inner_cond
        | .Ologand | .Ologor => true
        | _ => false
      non_linear_cond_expr false vars env loc e1
      non_linear_cond_expr inner_cond vars env loc e2
  | .EConditional _ e1 e2 =>
      let can_cast := (← safe_cast env e1.etyp e.etyp) && (← safe_cast env e2.etyp e.etyp)
      if !can_cast || inner_cond || !(← safe_expr vars env e1) || !(← safe_expr vars env e2) then
        warning loc .Non_linear_cond_expr "conditional expression may not be linearized"
      non_linear_cond_expr true vars env loc e1
      non_linear_cond_expr true vars env loc e2
  | .ECompound _ init => non_linear_cond_init vars env loc init
  | .ECall e params =>
      non_linear_cond_expr false vars env loc e
      params.forM (non_linear_cond_expr false vars env loc)

partial def non_linear_cond_init (vars : IdentSet) (env : Env.T) (loc : Location)
    (init : Init) : M Unit :=
  iter_over_init (non_linear_cond_expr false vars env loc) init
end

def non_linear_cond_stmt (vars : IdentSet) (env : Env.T) (s : Stmt) : M Unit :=
  iter_over_stmt_loc (non_linear_cond_expr false vars env)
    (fun loc d => match d.init with
      | none => pure ()
      | some init => non_linear_cond_init vars env loc init) s

def non_linear_conditional (option_Obranchless : Bool) (env0 : Env.T) (p : Program) :
    M Unit := do
  if (← active_warning .Non_linear_cond_expr) && option_Obranchless then
    traverse_program
      { fundef := fun env _ fd => do
          let vars ← fd.fd_params.foldlM (add_vars env) {}
          let vars ← non_stack_locals_stmt env vars fd.fd_body
          non_linear_cond_stmt vars env fd.fd_body }
      env0 p

end Checks
end CParser
end CC
