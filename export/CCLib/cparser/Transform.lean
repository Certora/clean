/-
  Port of `cparser/Transform.ml`: generic program transformation (fresh
  temporaries, expansion of assignment operators, statement and program
  traversals).

  * The global list `temporaries` is the field `temporaries` of the
    front-end state.
  * The optional arguments of `stmt` and `program` are the fields (with the
    same defaults) of the structures `StmtHooks` and `ProgramHooks`.
  * `program` starts from `Env.initial ()` in OCaml; here the initial
    environment is an explicit argument `env0` (see `Env.set_builtins`).
-/
import CCLib.cparser.Cutil

namespace CC
namespace CParser
namespace Transform

open C Cutil

/-! Recording fresh temporaries -/

def reset_temps : M Unit := modify fun s => { s with temporaries := [] }

def get_temps : M (List Decl) := do
  let temps := (← get).temporaries
  modify fun s => { s with temporaries := [] }
  return temps.reverse

def new_temp_var (ty : Typ) (name : String := "t") : M Ident := do
  let id ← Env.fresh_ident name
  modify fun s => { s with temporaries := .mk .Storage_default id ty none :: s.temporaries }
  return id

def new_temp (ty : Typ) (name : String := "t") : M Exp := do
  let id ← new_temp_var ty name
  return .mk (.EVar id) ty

/-- Temporaries should not be `const` nor `volatile`. -/
def attributes_to_remove_from_temp : Attributes := add_attributes [.AConst] [.AVolatile]

def mk_temp (env : Env.T) (ty : Typ) : M Exp := do
  new_temp (← remove_attributes_type env attributes_to_remove_from_temp ty)

/-- Is a l-value invariant (no need to bind it to a temporary)? -/
partial def invariant_lvalue (e : Exp) : Bool :=
  match e.edesc with
  | .EVar _ => true
  | .EUnop (.Odot _) e1 => invariant_lvalue e1
  | _ => false

/-- Bind a l-value to a temporary variable if it is not invariant. -/
def bind_lvalue (_env : Env.T) (e : Exp) (fn : Exp → M Exp) : M Exp := do
  if invariant_lvalue e then fn e
  else
    let tmp ← new_temp (.TPtr e.etyp [])
    return ecomma (eassign tmp (eaddrof e)) (← fn (.mk (.EUnop .Oderef tmp) e.etyp))

/-- Whether the value of an expression is needed (`Val`) or it is evaluated
    only for its side effects (`Effects`). -/
inductive Context where
  | Val | Effects
  deriving BEq, DecidableEq, Inhabited, Repr

/-! Expansion of assignment expressions -/

def op_for_assignop : BinaryOperator → M BinaryOperator
  | .Oadd_assign => pure .Oadd
  | .Osub_assign => pure .Osub
  | .Omul_assign => pure .Omul
  | .Odiv_assign => pure .Odiv
  | .Omod_assign => pure .Omod
  | .Oand_assign => pure .Oand
  | .Oor_assign => pure .Oor
  | .Oxor_assign => pure .Oxor
  | .Oshl_assign => pure .Oshl
  | .Oshr_assign => pure .Oshr
  | _ => assertFalse "Transform.op_for_assignop"

def op_for_incr_decr : UnaryOperator → M BinaryOperator
  | .Opreincr | .Opostincr => pure .Oadd
  | .Opredecr | .Opostdecr => pure .Osub
  | _ => assertFalse "Transform.op_for_incr_decr"

def assignop_for_incr_decr : UnaryOperator → M BinaryOperator
  | .Opreincr => pure .Oadd_assign
  | .Opredecr => pure .Osub_assign
  | _ => assertFalse "Transform.assignop_for_incr_decr"

def expand_assign (write : Exp → Exp → M Exp) (env : Env.T) (ctx : Context) (l r : Exp) :
    M Exp := do
  match ctx with
  | .Effects => write l r
  | .Val =>
      let tmp ← mk_temp env l.etyp
      return ecomma (eassign tmp r) (ecomma (← write l tmp) tmp)

def expand_assignop (read : Exp → M Exp) (write : Exp → Exp → M Exp) (env : Env.T)
    (ctx : Context) (op : BinaryOperator) (l r : Exp) (ty : Typ) : M Exp :=
  bind_lvalue env l fun l => do
    let res := Exp.mk (.EBinop (← op_for_assignop op) (← read l) r ty) ty
    match ctx with
    | .Effects => write l res
    | .Val =>
        let tmp ← mk_temp env l.etyp
        return ecomma (eassign tmp res) (ecomma (← write l tmp) tmp)

def expand_preincrdecr (read : Exp → M Exp) (write : Exp → Exp → M Exp) (env : Env.T)
    (ctx : Context) (op : UnaryOperator) (l : Exp) : M Exp := do
  expand_assignop read write env ctx (← assignop_for_incr_decr op) l (intconst 1 .IInt)
    (← unary_conversion env l.etyp)

def expand_postincrdecr (read : Exp → M Exp) (write : Exp → Exp → M Exp) (env : Env.T)
    (ctx : Context) (op : UnaryOperator) (l : Exp) : M Exp :=
  bind_lvalue env l fun l => do
    let ty ← unary_conversion env l.etyp
    match ctx with
    | .Effects =>
        let newval := Exp.mk (.EBinop (← op_for_incr_decr op) (← read l) (intconst 1 .IInt) ty) ty
        write l newval
    | .Val =>
        let tmp ← mk_temp env l.etyp
        let newval := Exp.mk (.EBinop (← op_for_incr_decr op) tmp (intconst 1 .IInt) ty) ty
        return ecomma (eassign tmp (← read l)) (ecomma (← write l newval) tmp)

/-- Generic transformation of a statement, transforming expressions within
    and preserving the statement structure.  If `decl` is not given, it
    applies only to unblocked code. -/
partial def stmt (expr : Location → Env.T → Context → Exp → M Exp)
    (decl : Env.T → Decl → M Decl := fun _ _ => assertFalse "Transform.stmt: decl")
    (env : Env.T) (s : Stmt) : M Stmt :=
  stm s
where
  stm (s : Stmt) : M Stmt := do
    let loc := s.sloc
    let d ← match s.sdesc with
      | .Sskip => pure s.sdesc
      | .Sdo e => pure (.Sdo (← expr loc env .Effects e))
      | .Sseq s1 s2 => pure (.Sseq (← stm s1) (← stm s2))
      | .Sif e s1 s2 => pure (.Sif (← expr loc env .Val e) (← stm s1) (← stm s2))
      | .Swhile e s1 => pure (.Swhile (← expr loc env .Val e) (← stm s1))
      | .Sdowhile s1 e => pure (.Sdowhile (← stm s1) (← expr loc env .Val e))
      | .Sfor s1 e s2 s3 =>
          pure (.Sfor (← stm s1) (← expr loc env .Val e) (← stm s2) (← stm s3))
      | .Sbreak | .Scontinue => pure s.sdesc
      | .Sswitch e s1 => pure (.Sswitch (← expr loc env .Val e) (← stm s1))
      | .Slabeled lbl s1 => pure (.Slabeled lbl (← stm s1))
      | .Sgoto _ | .Sreturn none => pure s.sdesc
      | .Sreturn (some e) => pure (.Sreturn (some (← expr loc env .Val e)))
      | .Sasm attr template outputs inputs clob =>
          let op : AsmOperand → M AsmOperand := fun (lbl, cstr, e) => do
            return (lbl, cstr, ← expr loc env .Val e)
          pure (.Sasm attr template (← outputs.mapM op) (← inputs.mapM op) clob)
      | .Sblock sl => pure (.Sblock (← sl.mapM stm))
      | .Sdecl d => pure (.Sdecl (← decl env d))
    return .mk d loc

/-- Generic transformation of a function definition -/
def fundef (trstmt : Env.T → Stmt → M Stmt) (env : Env.T) (f : Fundef) : M Fundef := do
  reset_temps
  let newbody ← trstmt env f.fd_body
  let temps ← get_temps
  return { f with fd_locals := f.fd_locals ++ temps, fd_body := newbody }

/-- The optional arguments of `program`. -/
structure ProgramHooks where
  decl : Env.T → Location → Decl → M Decl := fun _ _ d => pure d
  fundef : Env.T → Location → Fundef → M Fundef := fun _ _ fd => pure fd
  composite : Env.T → Location → StructOrUnion → Ident → Attributes → List Field →
      M (Attributes × List Field) := fun _ _ _ _ attr fl => pure (attr, fl)
  typedef : Env.T → Location → Ident → Typ → M Typ := fun _ _ _ ty => pure ty
  enum : Env.T → Location → Ident → Attributes → List Enumerator →
      M (Attributes × List Enumerator) := fun _ _ _ attr members => pure (attr, members)
  pragma : Env.T → Location → String → M String := fun _ _ s => pure s

/-- Generic transformation of a program, starting from the environment
    `env0` (OCaml: `Env.initial ()`). -/
def program (h : ProgramHooks) (env0 : Env.T) (p : Program) : M Program := do
  let mut env := env0
  let mut accu : Array Globdecl := #[]
  for g in p do
    let (desc', env') ← match g.gdesc with
      | .Gdecl d@(.mk sto id ty _) => do
          pure (GlobdeclDesc.Gdecl (← h.decl env g.gloc d), Env.add_ident env id sto ty)
      | .Gfundef f => do
          pure (.Gfundef (← h.fundef env g.gloc f),
                Env.add_ident env f.fd_name f.fd_storage (fundef_typ f))
      | .Gcompositedecl su id attr =>
          pure (.Gcompositedecl su id attr,
                Env.add_composite env id (composite_info_decl su attr))
      | .Gcompositedef su id attr fl => do
          let (attr', fl') ← h.composite env g.gloc su id attr fl
          pure (.Gcompositedef su id attr' fl',
                Env.add_composite env id (← composite_info_def env su attr fl))
      | .Gtypedef id ty => do
          pure (.Gtypedef id (← h.typedef env g.gloc id ty), Env.add_typedef env id ty)
      | .Genumdef id attr members => do
          let (attr', members') ← h.enum env g.gloc id attr members
          pure (.Genumdef id attr' members',
                Env.add_enum env id { ei_members := members, ei_attr := attr })
      | .Gpragma s => do pure (.Gpragma (← h.pragma env g.gloc s), env)
    env := env'
    accu := accu.push { g with gdesc := desc' }
  return accu.toList

end Transform
end CParser
end CC
