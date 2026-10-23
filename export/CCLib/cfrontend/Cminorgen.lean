/-
  Translation from Csharpminor to Cminor — port of `cfrontend/Cminorgen.v`
  (the whole file).

  This is the fourth pass of CompCert's compiler.  Local variables whose
  address is taken become sub-blocks of the Cminor stack frame (accessed
  with `Oaddrstack`), and Csharpminor's `switch` with labelled cases becomes
  a cascade of Cminor blocks and a jump-table `Sswitch`.

  Differences from Rocq:
  * `VarSort` (`Mergesort.Sort` on sizes) is a structural stable insertion
    sort (`varSort`); both are stable sorts for the same total preorder, so
    they compute the same permutation.  Unlike `List.mergeSort` (defined by
    well-founded recursion), `varSort` reduces in the kernel.
  * Error messages are plain strings (the port's `Res`).
-/
import CCLib.cfrontend.Csharpminor
import CCLib.common.MemoryInject

namespace CC
namespace Cminorgen

local notation "SExpr" => Csharpminor.Expr

/-! ## Handling of variables -/

/-- `Cminorgen.compilenv`: the stack offset of every Csharpminor local
    variable. -/
abbrev Compilenv := PTree Z

/-- `Cminorgen.var_addr` -/
def varAddr (cenv : Compilenv) (id : Ident) : Cminor.Expr :=
  match PTree.get id cenv with
  | some ofs => .Econst (.Oaddrstack (Integers.Ptrofs.repr ofs))
  | none => .Econst (.Oaddrsymbol id Integers.Ptrofs.zero)

/-! ## Expressions and statements -/

/-- `Cminorgen.transl_constant` -/
def translConstant : Csharpminor.Constant → Cminor.Constant
  | .Ointconst n => .Ointconst n
  | .Ofloatconst n => .Ofloatconst n
  | .Osingleconst n => .Osingleconst n
  | .Olongconst n => .Olongconst n

/-- `Cminorgen.transl_expr` -/
def translExpr (cenv : Compilenv) : SExpr → Res Cminor.Expr
  | .Evar id => .OK (.Evar id)
  | .Eaddrof id => .OK (varAddr cenv id)
  | .Econst cst => .OK (.Econst (translConstant cst))
  | .Eunop op e1 => do
    let te1 ← translExpr cenv e1
    .OK (.Eunop op te1)
  | .Ebinop op e1 e2 => do
    let te1 ← translExpr cenv e1
    let te2 ← translExpr cenv e2
    .OK (.Ebinop op te1 te2)
  | .Eload chunk e => do
    let te ← translExpr cenv e
    .OK (.Eload chunk te)

/-- `Cminorgen.transl_exprlist` -/
def translExprlist (cenv : Compilenv) : List SExpr → Res (List Cminor.Expr)
  | [] => .OK []
  | e1 :: e2 => do
    let te1 ← translExpr cenv e1
    let te2 ← translExprlist cenv e2
    .OK (te1 :: te2)

/-- `Cminorgen.exit_env`: `true` for a block of the source, `false` for a
    block inserted by the translation of `switch`. -/
abbrev ExitEnv := List Bool

/-- `Cminorgen.shift_exit` -/
def shiftExit : ExitEnv → Nat → Nat
  | [], n => n
  | false :: e', n => shiftExit e' n + 1
  | true :: _, 0 => 0
  | true :: e', m + 1 => shiftExit e' m + 1

/-- `Cminorgen.switch_table` -/
def switchTable : Csharpminor.LblStmt → Nat → List (Z × Nat) × Nat
  | .LSnil, k => ([], k)
  | .LScons none _ rem, k =>
    let (tbl, _) := switchTable rem (k + 1)
    (tbl, k)
  | .LScons (some ni) _ rem, k =>
    let (tbl, dfl) := switchTable rem (k + 1)
    ((ni, k) :: tbl, dfl)

/-- `Cminorgen.switch_env` -/
def switchEnv : Csharpminor.LblStmt → ExitEnv → ExitEnv
  | .LSnil, e => e
  | .LScons _ _ ls', e => false :: switchEnv ls' e

mutual
/-- `Cminorgen.transl_stmt` -/
def translStmt (cenv : Compilenv) (xenv : ExitEnv) : Csharpminor.Stmt → Res Cminor.Stmt
  | .Sskip => .OK .Sskip
  | .Sset id e => do
    let te ← translExpr cenv e
    .OK (.Sassign id te)
  | .Sstore chunk e1 e2 => do
    let te1 ← translExpr cenv e1
    let te2 ← translExpr cenv e2
    .OK (.Sstore chunk te1 te2)
  | .Scall optid sig e el => do
    let te ← translExpr cenv e
    let tel ← translExprlist cenv el
    .OK (.Scall optid sig te tel)
  | .Sbuiltin optid ef el => do
    let tel ← translExprlist cenv el
    .OK (.Sbuiltin optid ef tel)
  | .Sseq s1 s2 => do
    let ts1 ← translStmt cenv xenv s1
    let ts2 ← translStmt cenv xenv s2
    .OK (.Sseq ts1 ts2)
  | .Sifthenelse e s1 s2 => do
    let te ← translExpr cenv e
    let ts1 ← translStmt cenv xenv s1
    let ts2 ← translStmt cenv xenv s2
    .OK (.Sifthenelse te ts1 ts2)
  | .Sloop s => do
    let ts ← translStmt cenv xenv s
    .OK (.Sloop ts)
  | .Sblock s => do
    let ts ← translStmt cenv (true :: xenv) s
    .OK (.Sblock ts)
  | .Sexit n => .OK (.Sexit (shiftExit xenv n))
  | .Sswitch long e ls =>
    let (tbl, dfl) := switchTable ls 0
    do
      let te ← translExpr cenv e
      translLblstmt cenv (switchEnv ls xenv) ls (.Sswitch long te tbl dfl)
  | .Sreturn none => .OK (.Sreturn none)
  | .Sreturn (some e) => do
    let te ← translExpr cenv e
    .OK (.Sreturn (some te))
  | .Slabel lbl s => do
    let ts ← translStmt cenv xenv s
    .OK (.Slabel lbl ts)
  | .Sgoto lbl => .OK (.Sgoto lbl)

/-- `Cminorgen.transl_lblstmt` -/
def translLblstmt (cenv : Compilenv) (xenv : ExitEnv) :
    Csharpminor.LblStmt → Cminor.Stmt → Res Cminor.Stmt
  | .LSnil, body => .OK (.Sseq (.Sblock body) .Sskip)
  | .LScons _ s ls', body => do
    let ts ← translStmt cenv xenv s
    translLblstmt cenv xenv.tail ls' (.Sseq (.Sblock body) ts)
end

/-! ## Stack layout -/

/-- `Cminorgen.assign_variable` -/
def assignVariable (cenvStacksize : Compilenv × Z) (idSz : Ident × Z) : Compilenv × Z :=
  let (id, sz) := idSz
  let (cenv, stacksize) := cenvStacksize
  let ofs := align stacksize (minSafeAlignment sz)
  (PTree.set id ofs cenv, ofs + max 0 sz)

/-- `Cminorgen.assign_variables` -/
def assignVariables (cenvStacksize : Compilenv × Z) (vars : List (Ident × Z)) : Compilenv × Z :=
  vars.foldl assignVariable cenvStacksize

/-- `Cminorgen.VarOrder.leb` -/
def varLeb (v1 v2 : Ident × Z) : Bool := decide (v1.2 ≤ v2.2)

/-- Insert `v` before the first element of a sorted list that is `≥` it
    (so `v` stays ahead of elements of equal size: the sort is stable). -/
def varInsert (v : Ident × Z) : List (Ident × Z) → List (Ident × Z)
  | [] => [v]
  | w :: ws => if varLeb v w then v :: w :: ws else w :: varInsert v ws

/-- `Cminorgen.VarSort.sort`: stable sort by increasing size. -/
def varSort : List (Ident × Z) → List (Ident × Z)
  | [] => []
  | v :: vs => varInsert v (varSort vs)

theorem varInsert_perm (v : Ident × Z) (l : List (Ident × Z)) : (varInsert v l).Perm (v :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons w ws ih =>
    unfold varInsert
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons w ih).trans (List.Perm.swap v w ws)

/-- `varSort` is a permutation of its input. -/
theorem varSort_perm (l : List (Ident × Z)) : (varSort l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons v vs ih => exact (varInsert_perm v _).trans (List.Perm.cons v ih)

/-- `Cminorgen.build_compilenv`: variables are laid out by increasing size
    to minimize padding. -/
def buildCompilenv (f : Csharpminor.Function) : Compilenv × Z :=
  assignVariables (PTree.empty, 0) (varSort f.fn_vars)

/-! ## Functions and programs -/

/-- `Cminorgen.transl_funbody` -/
def translFunbody (cenv : Compilenv) (stacksize : Z) (f : Csharpminor.Function) :
    Res Cminor.Function := do
  let tbody ← translStmt cenv [] f.fn_body
  .OK { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_vars := f.fn_temps,
        fn_stackspace := stacksize, fn_body := tbody }

/-- `Cminorgen.transl_function`: fails if the stack frame is too large. -/
def translFunction (f : Csharpminor.Function) : Res Cminor.Function :=
  let (cenv, stacksize) := buildCompilenv f
  if stacksize ≤ Integers.Ptrofs.max_unsigned then translFunbody cenv stacksize f
  else .Error "Cminorgen: too many local variables, stack size exceeded"

/-- `Cminorgen.transl_fundef` -/
def translFundef (f : Csharpminor.Fundef) : Res Cminor.Fundef :=
  ASTFundef.transfPartial translFunction f

/-- `Cminorgen.transl_program` -/
def translProgram (p : Csharpminor.Program) : Res Cminor.Program :=
  transformPartialProgram translFundef p

end Cminorgen
end CC
