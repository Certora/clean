/-
  Port of `cparser/Rename.ml`: renaming of identifiers, so that every
  identifier of the program gets a unique name (public globals keep theirs;
  others get `name__N` if needed).

  `Env.initial_identifiers ()` (the builtins) is an explicit argument of
  `program`.  Functions that can report the fatal error "unbound" run in `M`.
-/
import CCLib.cparser.Cutil

namespace CC
namespace CParser
namespace Rename

open C Cutil

structure RenameEnv where
  re_id : Cutil.IdentMap Ident
  re_public : Std.HashMap String Ident
  re_used : Std.HashSet String
  deriving Inhabited

def empty_env : RenameEnv := { re_id := {}, re_public := {}, re_used := {} }

/-- For public global identifiers, we must keep their names -/
def enter_public (env : RenameEnv) (id : Ident) : RenameEnv :=
  match env.re_public.get? id.name with
  | some id' => { env with re_id := env.re_id.insert id id' }
  | none =>
      { re_id := env.re_id.insert id id,
        re_public := env.re_public.insert id.name id,
        re_used := env.re_used.insert id.name }

/-- For static or local identifiers, we make up a new name if needed.  If
    the same identifier has already been declared, don't rename a second
    time. -/
def rename (env : RenameEnv) (id : Ident) : Ident × RenameEnv :=
  match env.re_id.get? id with
  | some id' => (id', env)
  | none =>
      let basename := if id.name == "" then s!"_{id.stamp}" else id.name
      let newname :=
        if !env.re_used.contains basename then basename
        else Id.run do
          -- `find_name 1`: the first `basename__n` not yet used
          let mut n := 1
          for _ in [0:env.re_used.size + 1] do
            if env.re_used.contains s!"{basename}__{n}" then n := n + 1
          return s!"{basename}__{n}"
      let newid : Ident := { name := newname, stamp := id.stamp }
      (newid, { re_id := env.re_id.insert id newid, re_public := env.re_public,
                re_used := env.re_used.insert newname })

/-- Monadic map to thread an environment -/
def mmap {α β} (f : RenameEnv → α → M (β × RenameEnv)) (env : RenameEnv) :
    List α → M (List β × RenameEnv)
  | [] => pure ([], env)
  | hd :: tl => do
      let (hd', env1) ← f env hd
      let (tl', env2) ← mmap f env1 tl
      return (hd' :: tl', env2)

def ident (env : RenameEnv) (id : Ident) : M Ident :=
  match env.re_id.get? id with
  | some id' => pure id'
  | none => Diagnostics.fatal_error Diagnostics.no_loc
      s!"internal error: rename: {id.name}__{id.stamp} unbound"

mutual
partial def typ (env : RenameEnv) : Typ → M Typ
  | .TPtr ty a => do return .TPtr (← typ env ty) a
  | .TArray ty sz a => do return .TArray (← typ env ty) sz a
  | .TFun res none va a => do return .TFun (← typ env res) none va a
  | .TFun res (some p) va a => do
      let (p', _) ← mmap param env p
      return .TFun (← typ env res) (some p') va a
  | .TNamed id a => do return .TNamed (← ident env id) a
  | .TStruct id a => do return .TStruct (← ident env id) a
  | .TUnion id a => do return .TUnion (← ident env id) a
  | .TEnum id a => do return .TEnum (← ident env id) a
  | ty => pure ty

partial def param (env : RenameEnv) : Ident × Typ → M ((Ident × Typ) × RenameEnv)
  | (id, ty) => do
    if id.name == "" then return ((id, ← typ env ty), env)
    else
      let (id', env') := rename env id
      return ((id', ← typ env' ty), env')
end

def field (env : RenameEnv) (f : Field) : M Field := do
  return { f with fld_typ := ← typ env f.fld_typ }

def constant (env : RenameEnv) : Constant → M Constant
  | .CEnum id v => do return .CEnum (← ident env id) v
  | cst => pure cst

mutual
partial def exp (env : RenameEnv) (e : Exp) : M Exp := do
  return .mk (← exp_desc env e.edesc) (← typ env e.etyp)

partial def exp_desc (env : RenameEnv) : ExpDesc → M ExpDesc
  | .EConst cst => do return .EConst (← constant env cst)
  | .ESizeof ty => do return .ESizeof (← typ env ty)
  | .EAlignof ty => do return .EAlignof (← typ env ty)
  | .EVar id => do return .EVar (← ident env id)
  | .EUnop op a => do return .EUnop op (← exp env a)
  | .EBinop op a b ty => do return .EBinop op (← exp env a) (← exp env b) (← typ env ty)
  | .EConditional a b c => do return .EConditional (← exp env a) (← exp env b) (← exp env c)
  | .ECast ty a => do return .ECast (← typ env ty) (← exp env a)
  | .ECompound ty ie => do return .ECompound (← typ env ty) (← init env ie)
  | .ECall a al => do return .ECall (← exp env a) (← al.mapM (exp env))

partial def init (env : RenameEnv) : Init → M Init
  | .Init_single e => do return .Init_single (← exp env e)
  | .Init_array il => do return .Init_array (← il.mapM (init env))
  | .Init_struct id il => do
      return .Init_struct (← ident env id)
        (← il.mapM fun (f, i) => do return (← field env f, ← init env i))
  | .Init_union id f i => do return .Init_union (← ident env id) (← field env f) (← init env i)
end

def optexp (env : RenameEnv) : Option Exp → M (Option Exp)
  | none => pure none
  | some a => do return some (← exp env a)

def decl (env : RenameEnv) : Decl → M (Decl × RenameEnv)
  | .mk sto id ty int => do
      let (id', env') := rename env id
      let int' ← match int with
        | none => pure none
        | some i => do pure (some (← init env' i))
      return (.mk sto id' (← typ env' ty) int', env')

def asm_operand (env : RenameEnv) : AsmOperand → M AsmOperand
  | (lbl, cstr, e) => do return (lbl, cstr, ← exp env e)

mutual
partial def stmt (env : RenameEnv) (s : Stmt) : M Stmt := do
  return .mk (← stmt_desc env s.sdesc) s.sloc

partial def stmt_desc (env : RenameEnv) : StmtDesc → M StmtDesc
  | .Sskip => pure .Sskip
  | .Sdo a => do return .Sdo (← exp env a)
  | .Sseq s1 s2 => do return .Sseq (← stmt env s1) (← stmt env s2)
  | .Sif a s1 s2 => do return .Sif (← exp env a) (← stmt env s1) (← stmt env s2)
  | .Swhile a s => do return .Swhile (← exp env a) (← stmt env s)
  | .Sdowhile s a => do return .Sdowhile (← stmt env s) (← exp env a)
  | .Sfor a1 a2 a3 s => do
      return .Sfor (← stmt env a1) (← exp env a2) (← stmt env a3) (← stmt env s)
  | .Sbreak => pure .Sbreak
  | .Scontinue => pure .Scontinue
  | .Sswitch a s => do return .Sswitch (← exp env a) (← stmt env s)
  | .Slabeled lbl s => do return .Slabeled (← slabel env lbl) (← stmt env s)
  | .Sgoto lbl => pure (.Sgoto lbl)
  | .Sreturn a => do return .Sreturn (← optexp env a)
  | .Sblock sl => do
      let (sl', _) ← mmap stmt_or_decl env sl
      return .Sblock sl'
  | .Sdecl _ => assertFalse "Rename.stmt_desc"
  | .Sasm attr txt outputs inputs flags => do
      return .Sasm attr txt (← outputs.mapM (asm_operand env)) (← inputs.mapM (asm_operand env))
        flags

partial def stmt_or_decl (env : RenameEnv) (s : Stmt) : M (Stmt × RenameEnv) := do
  match s.sdesc with
  | .Sdecl d =>
      let (d', env') ← decl env d
      return (.mk (.Sdecl d') s.sloc, env')
  | _ => return (← stmt env s, env)

partial def slabel (env : RenameEnv) : SLabel → M SLabel
  | .Scase e n => do return .Scase (← exp env e) n
  | sl => pure sl
end

def fundef (env : RenameEnv) (f : Fundef) : M (Fundef × RenameEnv) := do
  let (name', env0) := rename env f.fd_name
  let (params', env1) ← mmap param env0 f.fd_params
  let (locals', env2) ← mmap decl env1 f.fd_locals
  return ({ fd_storage := f.fd_storage, fd_inline := f.fd_inline, fd_name := name',
            fd_attrib := f.fd_attrib, fd_ret := ← typ env0 f.fd_ret, fd_params := params',
            fd_vararg := f.fd_vararg, fd_locals := locals', fd_body := ← stmt env2 f.fd_body },
          env0)

def enum (env : RenameEnv) : Enumerator → M (Enumerator × RenameEnv)
  | (id, v, opte) => do
      let (id', env') := rename env id
      return ((id', v, ← optexp env' opte), env')

def globdecl_desc (env : RenameEnv) : GlobdeclDesc → M (GlobdeclDesc × RenameEnv)
  | .Gdecl d => do
      let (d', env') ← decl env d
      return (.Gdecl d', env')
  | .Gfundef fd => do
      let (fd', env') ← fundef env fd
      return (.Gfundef fd', env')
  | .Gcompositedecl kind id attr => do
      let (id', env') := rename env id
      return (.Gcompositedecl kind id' attr, env')
  | .Gcompositedef kind id attr members => do
      return (.Gcompositedef kind (← ident env id) attr (← members.mapM (field env)), env)
  | .Gtypedef id ty => do
      let (id', env') := rename env id
      return (.Gtypedef id' (← typ env' ty), env')
  | .Genumdef id attr members => do
      let (id', env') := rename env id
      let (members', env'') ← mmap enum env' members
      return (.Genumdef id' attr members', env'')
  | .Gpragma s => pure (.Gpragma s, env)

def globdecl (env : RenameEnv) (g : Globdecl) : M (Globdecl × RenameEnv) := do
  let (desc', env') ← globdecl_desc env g.gdesc
  return ({ gdesc := desc', gloc := g.gloc }, env')

def globdecls (env : RenameEnv) (p : List Globdecl) : M (List Globdecl) := do
  let (p', _) ← mmap globdecl env p
  return p'

/-- Reserve names of builtins -/
def reserve_builtins (initial_identifiers : List Ident) : RenameEnv :=
  initial_identifiers.foldl enter_public empty_env

/-- Reserve global declarations with public visibility -/
def reserve_public (env : RenameEnv) : List Globdecl → M RenameEnv
  | [] => pure env
  | dcl :: rem => do
      let env' ← match dcl.gdesc with
        | .Gdecl (.mk sto id _ _) =>
            match sto with
            | .Storage_default | .Storage_extern => pure (enter_public env id)
            | .Storage_static => pure env
            | _ => assertFalse "Rename.reserve_public"
        | .Gfundef f =>
            match f.fd_storage with
            | .Storage_default | .Storage_extern => pure (enter_public env f.fd_name)
            | .Storage_static => pure env
            | _ => assertFalse "Rename.reserve_public"
        | _ => pure env
      reserve_public env' rem

/-- Rename the program (`initial_identifiers`: the builtins). -/
def program (initial_identifiers : List Ident) (p : Program) : M Program := do
  globdecls (← reserve_public (reserve_builtins initial_identifiers) p) p

end Rename
end CParser
end CC
