/-
  Port of `cparser/Cleanup.ml`: removing unused declarations.

  The global references `referenced` and `ref_changed` are the state of the
  monad `CM`.  The calls `Debug.remove_unused` and
  `Debug.remove_unused_function` are omitted: the debug hooks
  (`debug/Debug.lean`, `debug/DebugInformation.lean`) run in `IO` and are
  not threaded through the front end yet.

  As in OCaml, `program` expects the declarations in *reverse* order (it is
  applied by `Elab.elaborated_program` to the list of declarations built by
  consing) and returns them in source order.
-/
import CCLib.cparser.Cutil

namespace CC
namespace CParser
namespace Cleanup

open C Cutil

/-- `(referenced, ref_changed)` -/
abbrev CM := StateT (IdentSet × Bool) M

/-- Record a reference to an identifier. -/
def addref (id : Ident) : CM Unit :=
  modify fun (r, ch) => if r.contains id then (r, ch) else (r.insert id, true)

def needed (id : Ident) : CM Bool := do return (← get).1.contains id

mutual
partial def add_typ : Typ → CM Unit
  | .TPtr ty _ => add_typ ty
  | .TArray ty _ _ => add_typ ty
  | .TFun res none _ _ => add_typ res
  | .TFun res (some params) _ _ => do add_typ res; add_vars params
  | .TNamed id _ | .TStruct id _ | .TUnion id _ | .TEnum id _ => addref id
  | _ => pure ()

partial def add_vars (vl : List (Ident × Typ)) : CM Unit :=
  vl.forM fun (_, ty) => add_typ ty
end

mutual
partial def add_exp (e : Exp) : CM Unit := do
  add_typ e.etyp
  match e.edesc with
  | .EConst (.CEnum id _) => addref id
  | .EConst _ => pure ()
  | .ESizeof ty | .EAlignof ty => add_typ ty
  | .EVar id => addref id
  | .EUnop _ e1 => add_exp e1
  | .EBinop _ e1 e2 _ => do add_exp e1; add_exp e2
  | .EConditional e1 e2 e3 => do add_exp e1; add_exp e2; add_exp e3
  | .ECast ty e1 => do add_typ ty; add_exp e1
  | .ECompound ty ie => do add_typ ty; add_init ie
  | .ECall e1 el => do add_exp e1; el.forM add_exp

partial def add_init : Init → CM Unit
  | .Init_single e => add_exp e
  | .Init_array il => il.forM add_init
  | .Init_struct id il => do addref id; il.forM fun (_, i) => add_init i
  | .Init_union id _ i => do addref id; add_init i
end

def add_decl : Decl → CM Unit
  | .mk _ _ ty init => do
      add_typ ty
      match init with
      | none => pure ()
      | some i => add_init i

def add_asm_operand : AsmOperand → CM Unit
  | (_, _, e) => add_exp e

partial def add_stmt (s : Stmt) : CM Unit := do
  match s.sdesc with
  | .Sskip | .Sbreak | .Scontinue | .Sgoto _ | .Sreturn none => pure ()
  | .Sdo e => add_exp e
  | .Sseq s1 s2 => do add_stmt s1; add_stmt s2
  | .Sif e s1 s2 => do add_exp e; add_stmt s1; add_stmt s2
  | .Swhile e s1 => do add_exp e; add_stmt s1
  | .Sdowhile s1 e => do add_stmt s1; add_exp e
  | .Sfor e1 e2 e3 s1 => do add_stmt e1; add_exp e2; add_stmt e3; add_stmt s1
  | .Sswitch e s1 => do add_exp e; add_stmt s1
  | .Slabeled lbl s =>
      match lbl with
      | .Scase e _ => do add_exp e; add_stmt s
      | _ => add_stmt s
  | .Sreturn (some e) => add_exp e
  | .Sblock sl => sl.forM add_stmt
  | .Sdecl d => add_decl d
  | .Sasm _ _ outputs inputs _ => do outputs.forM add_asm_operand; inputs.forM add_asm_operand

def add_fundef (f : Fundef) : CM Unit := do
  add_typ f.fd_ret
  add_vars f.fd_params
  f.fd_locals.forM add_decl
  add_stmt f.fd_body

def add_field (f : Field) : CM Unit := add_typ f.fld_typ

def add_enum (e : List Enumerator) : CM Unit :=
  e.forM fun (_, _, opt_e) => match opt_e with
    | some e => add_exp e
    | none => pure ()

/-! Saturate the set of referenced identifiers, starting with externally
    visible global declarations. -/

def visible_decl : Decl → Bool
  | .mk sto _ ty _ =>
      sto == .Storage_default && match ty with | .TFun .. => false | _ => true

def visible_fundef (f : Fundef) : M Bool :=
  match f.fd_storage with
  | .Storage_default => pure !f.fd_inline
  | .Storage_extern => pure true
  | .Storage_static => pure false
  | .Storage_auto | .Storage_register => assertFalse "Cleanup.visible_fundef"

/-- `add_init_globdecls accu p`: process the visible declarations, keep the
    others (in reverse order) for later iterations. -/
def add_init_globdecls (accu : List Globdecl) (p : List Globdecl) :
    CM (List Globdecl) := do
  let mut accu := accu
  for g in p do
    match g.gdesc with
    | .Gdecl decl =>
        if visible_decl decl then add_decl decl else accu := g :: accu
    | .Gfundef f =>
        if ← visible_fundef f then add_fundef f else accu := g :: accu
    | .Gcompositedef .. | .Gtypedef .. | .Genumdef .. => accu := g :: accu
    | .Gcompositedecl .. | .Gpragma _ => pure ()
  return accu

def add_needed_globdecls (accu : List Globdecl) (p : List Globdecl) :
    CM (List Globdecl) := do
  let mut accu := accu
  for g in p do
    match g.gdesc with
    | .Gdecl decl@(.mk _ id _ _) =>
        if ← needed id then add_decl decl else accu := g :: accu
    | .Gfundef f =>
        if ← needed f.fd_name then add_fundef f else accu := g :: accu
    | .Gcompositedef _ id _ flds =>
        if ← needed id then flds.forM add_field else accu := g :: accu
    | .Gtypedef id ty =>
        if ← needed id then add_typ ty else accu := g :: accu
    | .Genumdef id _ enu =>
        if (← needed id) || (← enu.anyM fun (id, _, _) => needed id) then add_enum enu
        else accu := g :: accu
    | _ => assertFalse "Cleanup.add_needed_globdecls"
  return accu

def saturate (p : List Globdecl) : CM Unit := do
  modify fun (r, _) => (r, false)
  let mut p ← add_init_globdecls [] p
  -- each iteration adds at least one identifier; the program has finitely many
  for _ in [0:p.length + 1] do
    if !(← get).2 then break
    modify fun (r, _) => (r, false)
    p ← add_needed_globdecls [] p

/-- Remove unreferenced definitions (the result is in reverse order of the
    argument). -/
def simpl_globdecls (accu : List Globdecl) (p : List Globdecl) :
    CM (List Globdecl) := do
  let mut accu := accu
  for g in p do
    let need ← match g.gdesc with
      | .Gdecl decl@(.mk _ id _ _) => do pure (visible_decl decl || (← needed id))
      | .Gfundef f => do pure ((← visible_fundef f) || (← needed f.fd_name))
      | .Gcompositedecl _ id _ => needed id
      | .Gcompositedef _ id _ _ => needed id
      | .Gtypedef id _ => needed id
      | .Genumdef id _ enu => do
          pure ((← needed id) || (← enu.anyM fun (id, _, _) => needed id))
      | .Gpragma _ => pure true
    if need then accu := g :: accu
  return accu

def program (p : Program) : M Program := do
  let (p', _) ← (do saturate p; simpl_globdecls [] p).run ({}, false)
  return p'

end Cleanup
end CParser
end CC
