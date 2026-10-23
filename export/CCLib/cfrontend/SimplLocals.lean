/-
  Pulling local scalar variables whose address is not taken into
  temporaries — port of `cfrontend/SimplLocals.v` (the whole file).

  This is the second pass of CompCert's compiler (Clight → Clight).

  Differences from Rocq:
  * `VSet` (an AVL set of positives, `FSetAVL.Make(OrderedPositive)`) is a
    list of identifiers without duplicates (`VSet.add` checks membership).
    Only `mem`, `empty`, `singleton`, `add` and `union` are used.
  * Rocq's OCaml parameters `Compopts.debug` and `Archi.abi` (the aarch64
    ABI, which decides `Conventions1.parameter_needs_normalization`) are the
    fields of an explicit `Options` structure.  The defaults are
    `debug := false` and `abi := .AAPCS64` (Linux).
  * Error messages are plain strings (the port's `Res`).
  * Clight programs in the port do not store `prog_comp_env_eq`.
-/
import CCLib.common.ASTTheory
import CCLib.cfrontend.Clight
import CCLib.aarch64.Conventions1

namespace CC
namespace SimplLocals

open Conventions1 (AbiKind parameterNeedsNormalization)

/-- The OCaml-side parameters the pass depends on: `Compopts.debug` and
    `Archi.abi`. -/
structure Options where
  debug : Bool := false
  abi : AbiKind := .AAPCS64

/-! ## Sets of variables -/

/-- `SimplLocals.VSet.t`, as a duplicate-free list. -/
abbrev VSet := List Ident

namespace VSet
def empty : VSet := []
def mem (x : Ident) (s : VSet) : Bool := s.contains x
def singleton (x : Ident) : VSet := [x]
def add (x : Ident) (s : VSet) : VSet := if mem x s then s else x :: s
def union (s1 s2 : VSet) : VSet := s1.foldr add s2

theorem mem_iff {x : Ident} {s : VSet} : mem x s = true ↔ x ∈ s := by
  simp [mem]

theorem mem_empty (x : Ident) : mem x empty = false := rfl

theorem mem_add {x y : Ident} {s : VSet} : mem x (add y s) = true ↔ x = y ∨ mem x s = true := by
  unfold add
  by_cases h : mem y s = true
  · simp only [h, if_true]
    constructor
    · exact Or.inr
    · rintro (rfl | h') <;> assumption
  · simp only [h, mem_iff]
    simp

theorem mem_singleton {x y : Ident} : mem x (singleton y) = true ↔ x = y := by
  simp [mem, singleton]

theorem mem_union {x : Ident} {s1 s2 : VSet} :
    mem x (union s1 s2) = true ↔ mem x s1 = true ∨ mem x s2 = true := by
  induction s1 with
  | nil => simp [union, mem]
  | cons y s1 ih =>
    simp only [union, List.foldr_cons] at *
    rw [mem_add, ih]
    simp only [mem_iff, List.mem_cons]
    constructor
    · rintro (h | h | h) <;> simp [h]
    · rintro ((h | h) | h) <;> simp [h]
end VSet

/-- `SimplLocals.compilenv`: the local variables that can be lifted to
    temporaries, because they are scalar and their address is not taken. -/
abbrev Compilenv := VSet

/-- `SimplLocals.is_liftable_var` -/
def isLiftableVar (cenv : Compilenv) : Expr → Option Ident
  | .Evar id _ => if VSet.mem id cenv then some id else none
  | _ => none

/-- `SimplLocals.make_cast`: smart constructor for casts. -/
def makeCast (a : Expr) (tto : Ty) : Expr :=
  match Cop.classifyCast (typeof a) tto with
  | .pointer => a
  | .i2i .I32 _ => a
  | .f2f => a
  | .s2s => a
  | .l2l => a
  | .struct _ _ => a
  | .union _ _ => a
  | .void => a
  | _ => .Ecast a tto

/-! ## Debug annotations -/

/-- `SimplLocals.Sdebug_temp` -/
def Sdebug_temp (id : Ident) (ty : Ty) : Stmt :=
  .Sbuiltin none (.EF_debug (Positive.ofNat 2) id [typOfType ty]) [typeconv ty]
    [.Etempvar id ty]

/-- `SimplLocals.Sdebug_var` -/
def Sdebug_var (id : Ident) (ty : Ty) : Stmt :=
  .Sbuiltin none (.EF_debug (Positive.ofNat 5) id [Tptr]) [.Tpointer ty noattr]
    [.Eaddrof (.Evar id ty) (.Tpointer ty noattr)]

section OPTS
variable (opts : Options)

/-- `SimplLocals.Sset_debug` -/
def Sset_debug (id : Ident) (ty : Ty) (a : Expr) : Stmt :=
  if opts.debug then .Ssequence (.Sset id (makeCast a ty)) (Sdebug_temp id ty)
  else .Sset id (makeCast a ty)

/-! ## Rewriting of expressions and statements -/

/-- `SimplLocals.simpl_expr` -/
def simplExpr (cenv : Compilenv) : Expr → Expr
  | a@(.Econst_int _ _) => a
  | a@(.Econst_float _ _) => a
  | a@(.Econst_single _ _) => a
  | a@(.Econst_long _ _) => a
  | .Evar id ty => if VSet.mem id cenv then .Etempvar id ty else .Evar id ty
  | .Etempvar id ty => .Etempvar id ty
  | .Ederef a1 ty => .Ederef (simplExpr cenv a1) ty
  | .Eaddrof a1 ty => .Eaddrof (simplExpr cenv a1) ty
  | .Eunop op a1 ty => .Eunop op (simplExpr cenv a1) ty
  | .Ebinop op a1 a2 ty => .Ebinop op (simplExpr cenv a1) (simplExpr cenv a2) ty
  | .Ecast a1 ty => .Ecast (simplExpr cenv a1) ty
  | .Efield a1 fld ty => .Efield (simplExpr cenv a1) fld ty
  | a@(.Esizeof _ _) => a
  | a@(.Ealignof _ _) => a

/-- `SimplLocals.simpl_exprlist` -/
def simplExprlist (cenv : Compilenv) (al : List Expr) : List Expr :=
  al.map (simplExpr cenv)

/-- `SimplLocals.check_temp` -/
def checkTemp (cenv : Compilenv) (id : Ident) : Res Unit :=
  if VSet.mem id cenv then .Error "bad temporary" else .OK ()

/-- `SimplLocals.check_opttemp` -/
def checkOpttemp (cenv : Compilenv) : Option Ident → Res Unit
  | some id => checkTemp cenv id
  | none => .OK ()

mutual
/-- `SimplLocals.simpl_stmt` -/
def simplStmt (cenv : Compilenv) : Stmt → Res Stmt
  | .Sskip => .OK .Sskip
  | .Sassign a1 a2 =>
    match isLiftableVar cenv a1 with
    | some id => .OK (Sset_debug opts id (typeof a1) (simplExpr cenv a2))
    | none => .OK (.Sassign (simplExpr cenv a1) (simplExpr cenv a2))
  | .Sset id a => do
    let _ ← checkTemp cenv id
    .OK (.Sset id (simplExpr cenv a))
  | .Scall optid a al => do
    let _ ← checkOpttemp cenv optid
    .OK (.Scall optid (simplExpr cenv a) (simplExprlist cenv al))
  | .Sbuiltin optid ef tyargs al => do
    let _ ← checkOpttemp cenv optid
    .OK (.Sbuiltin optid ef tyargs (simplExprlist cenv al))
  | .Ssequence s1 s2 => do
    let s1' ← simplStmt cenv s1
    let s2' ← simplStmt cenv s2
    .OK (.Ssequence s1' s2')
  | .Sifthenelse a s1 s2 => do
    let s1' ← simplStmt cenv s1
    let s2' ← simplStmt cenv s2
    .OK (.Sifthenelse (simplExpr cenv a) s1' s2')
  | .Sloop s1 s2 => do
    let s1' ← simplStmt cenv s1
    let s2' ← simplStmt cenv s2
    .OK (.Sloop s1' s2')
  | .Sbreak => .OK .Sbreak
  | .Scontinue => .OK .Scontinue
  | .Sreturn opta => .OK (.Sreturn (opta.map (simplExpr cenv)))
  | .Sswitch a ls => do
    let ls' ← simplLblstmt cenv ls
    .OK (.Sswitch (simplExpr cenv a) ls')
  | .Slabel lbl s => do
    let s' ← simplStmt cenv s
    .OK (.Slabel lbl s')
  | .Sgoto lbl => .OK (.Sgoto lbl)

/-- `SimplLocals.simpl_lblstmt` -/
def simplLblstmt (cenv : Compilenv) : LStmts → Res LStmts
  | .LSnil => .OK .LSnil
  | .LScons c s ls1 => do
    let s' ← simplStmt cenv s
    let ls1' ← simplLblstmt cenv ls1
    .OK (.LScons c s' ls1')
end

/-- `SimplLocals.store_params`: parameters that are not lifted to
    temporaries are stored in their local variable at function entry; the
    others may need to be normalized to their types. -/
def storeParams (cenv : Compilenv) : List (Ident × Ty) → Stmt → Stmt
  | [], s => s
  | (id, ty) :: params', s =>
    if VSet.mem id cenv then
      if parameterNeedsNormalization opts.abi (argtypeOfType ty) then
        .Ssequence (.Sset id (makeCast (.Etempvar id ty) ty)) (storeParams cenv params' s)
      else storeParams cenv params' s
    else .Ssequence (.Sassign (.Evar id ty) (.Etempvar id ty)) (storeParams cenv params' s)

end OPTS

/-! ## Variables whose address is taken -/

/-- `SimplLocals.addr_taken_expr` -/
def addrTakenExpr : Expr → VSet
  | .Econst_int _ _ | .Econst_float _ _ | .Econst_single _ _ | .Econst_long _ _ => VSet.empty
  | .Evar _ _ | .Etempvar _ _ => VSet.empty
  | .Ederef a1 _ => addrTakenExpr a1
  | .Eaddrof (.Evar id _) _ => VSet.singleton id
  | .Eaddrof a1 _ => addrTakenExpr a1
  | .Eunop _ a1 _ => addrTakenExpr a1
  | .Ebinop _ a1 a2 _ => VSet.union (addrTakenExpr a1) (addrTakenExpr a2)
  | .Ecast a1 _ => addrTakenExpr a1
  | .Efield a1 _ _ => addrTakenExpr a1
  | .Esizeof _ _ | .Ealignof _ _ => VSet.empty

/-- `SimplLocals.addr_taken_exprlist` -/
def addrTakenExprlist : List Expr → VSet
  | [] => VSet.empty
  | a :: l' => VSet.union (addrTakenExpr a) (addrTakenExprlist l')

mutual
/-- `SimplLocals.addr_taken_stmt` -/
def addrTakenStmt : Stmt → VSet
  | .Sskip => VSet.empty
  | .Sassign a b => VSet.union (addrTakenExpr a) (addrTakenExpr b)
  | .Sset _ a => addrTakenExpr a
  | .Scall _ a bl => VSet.union (addrTakenExpr a) (addrTakenExprlist bl)
  | .Sbuiltin _ _ _ bl => addrTakenExprlist bl
  | .Ssequence s1 s2 => VSet.union (addrTakenStmt s1) (addrTakenStmt s2)
  | .Sifthenelse a s1 s2 =>
    VSet.union (addrTakenExpr a) (VSet.union (addrTakenStmt s1) (addrTakenStmt s2))
  | .Sloop s1 s2 => VSet.union (addrTakenStmt s1) (addrTakenStmt s2)
  | .Sbreak => VSet.empty
  | .Scontinue => VSet.empty
  | .Sreturn none => VSet.empty
  | .Sreturn (some a) => addrTakenExpr a
  | .Sswitch a ls => VSet.union (addrTakenExpr a) (addrTakenLblstmt ls)
  | .Slabel _ s => addrTakenStmt s
  | .Sgoto _ => VSet.empty

/-- `SimplLocals.addr_taken_lblstmt` -/
def addrTakenLblstmt : LStmts → VSet
  | .LSnil => VSet.empty
  | .LScons _ s ls' => VSet.union (addrTakenStmt s) (addrTakenLblstmt ls')
end

/-! ## The compilation environment of a function -/

/-- `SimplLocals.add_local_variable` -/
def addLocalVariable (atk : VSet) (idTy : Ident × Ty) (cenv : Compilenv) : Compilenv :=
  match accessMode idTy.2 with
  | .By_value _ => if VSet.mem idTy.1 atk then cenv else VSet.add idTy.1 cenv
  | _ => cenv

/-- `SimplLocals.cenv_for`: the local variables (and parameters) that are
    scalars and whose address is not taken. -/
def cenvFor (f : Function) : Compilenv :=
  let atk := addrTakenStmt f.fn_body
  (f.fn_params ++ f.fn_vars).foldr (addLocalVariable atk) VSet.empty

/-! ## Transforming a function -/

/-- `SimplLocals.add_debug_var` -/
def addDebugVar (idTy : Ident × Ty) (s : Stmt) : Stmt :=
  .Ssequence (Sdebug_var idTy.1 idTy.2) s

/-- `SimplLocals.add_debug_vars` -/
def addDebugVars (opts : Options) (vars : List (Ident × Ty)) (s : Stmt) : Stmt :=
  if opts.debug then vars.foldr addDebugVar s else s

/-- `SimplLocals.add_debug_param` -/
def addDebugParam (idTy : Ident × Ty) (s : Stmt) : Stmt :=
  .Ssequence (Sdebug_temp idTy.1 idTy.2) s

/-- `SimplLocals.add_debug_params` -/
def addDebugParams (opts : Options) (params : List (Ident × Ty)) (s : Stmt) : Stmt :=
  if opts.debug then params.foldr addDebugParam s else s

/-- `SimplLocals.remove_lifted` -/
def removeLifted (cenv : Compilenv) (vars : List (Ident × Ty)) : List (Ident × Ty) :=
  vars.filter (fun idTy => !VSet.mem idTy.1 cenv)

/-- `SimplLocals.add_lifted` -/
def addLifted (cenv : Compilenv) (vars1 vars2 : List (Ident × Ty)) : List (Ident × Ty) :=
  vars1.filter (fun idTy => VSet.mem idTy.1 cenv) ++ vars2

/-- `SimplLocals.transf_function` -/
def transfFunction (opts : Options) (f : Function) : Res Function :=
  let cenv := cenvFor f
  if listDisjoint (varNames f.fn_params) (varNames f.fn_temps) then
    match simplStmt opts cenv f.fn_body with
    | .Error msg => .Error msg
    | .OK body' =>
      let vars' := removeLifted cenv (f.fn_params ++ f.fn_vars)
      let temps' := addLifted cenv f.fn_vars f.fn_temps
      .OK { fn_return := f.fn_return,
            fn_callconv := f.fn_callconv,
            fn_params := f.fn_params,
            fn_vars := vars',
            fn_temps := temps',
            fn_body := addDebugParams opts f.fn_params
                         (storeParams opts cenv f.fn_params (addDebugVars opts vars' body')) }
  else .Error "assertion failed"

/-- `SimplLocals.transf_fundef` -/
def transfFundef (opts : Options) : FunDef → Res FunDef
  | .Internal f =>
    match transfFunction opts f with
    | .OK tf => .OK (.Internal tf)
    | .Error msg => .Error msg
  | .External ef targs tres cc => .OK (.External ef targs tres cc)

/-- The generic program underlying a Clight program. -/
def programToAST (p : Program) : ASTProgram FunDef Ty :=
  { prog_defs := p.prog_defs, prog_public := p.prog_public, prog_main := p.prog_main }

/-- `SimplLocals.transf_program` -/
def transfProgram (opts : Options) (p : Program) : Res Program :=
  match transformPartialProgram (transfFundef opts) (programToAST p) with
  | .Error msg => .Error msg
  | .OK p1 =>
    .OK { prog_defs := p1.prog_defs, prog_public := p1.prog_public,
          prog_main := p1.prog_main, prog_types := p.prog_types,
          prog_comp_env := p.prog_comp_env }

/-! ## Basic properties -/

/-- The transformation keeps the signature of a function. -/
theorem transfFunction_sig {opts : Options} {f tf : Function}
    (h : transfFunction opts f = .OK tf) :
    tf.fn_return = f.fn_return ∧ tf.fn_callconv = f.fn_callconv ∧
      tf.fn_params = f.fn_params := by
  unfold transfFunction at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · cases h; exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- Lifted variables are no longer read from memory: `simplExpr` replaces
    every `Evar id` with `id ∈ cenv` by the temporary `Etempvar id`. -/
theorem simplExpr_Evar_lifted {cenv : Compilenv} {id : Ident} {ty : Ty}
    (h : VSet.mem id cenv = true) : simplExpr cenv (.Evar id ty) = .Etempvar id ty := by
  simp [simplExpr, h]

/-- A variable lifted by `cenvFor` does not have its address taken in the
    function body, and is a parameter or local variable of the function. -/
theorem cenvFor_spec {f : Function} {id : Ident} (h : VSet.mem id (cenvFor f) = true) :
    VSet.mem id (addrTakenStmt f.fn_body) = false ∧
      ∃ ty, (id, ty) ∈ f.fn_params ++ f.fn_vars ∧ ∃ chunk, accessMode ty = .By_value chunk := by
  unfold cenvFor at h
  generalize f.fn_params ++ f.fn_vars = l at h ⊢
  induction l with
  | nil => simp [VSet.empty, VSet.mem] at h
  | cons p l ih =>
    simp only [List.foldr_cons] at h
    unfold addLocalVariable at h
    split at h
    · rename_i chunk hm
      by_cases ha : VSet.mem p.1 (addrTakenStmt f.fn_body) = true
      · simp only [ha, if_true] at h
        obtain ⟨h1, ty, h2, h3⟩ := ih h
        exact ⟨h1, ty, List.mem_cons_of_mem _ h2, h3⟩
      · simp only [ha] at h
        rcases VSet.mem_add.mp h with rfl | h
        · exact ⟨by simpa using ha, p.2, by simp, chunk, hm⟩
        · obtain ⟨h1, ty, h2, h3⟩ := ih h
          exact ⟨h1, ty, List.mem_cons_of_mem _ h2, h3⟩
    · obtain ⟨h1, ty, h2, h3⟩ := ih h
      exact ⟨h1, ty, List.mem_cons_of_mem _ h2, h3⟩

end SimplLocals
end CC
