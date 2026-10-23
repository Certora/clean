/-
  Abstract syntax of the CompCert C language — port of `cfrontend/Csyntax.v`
  (the whole file), together with the three pieces of `cfrontend/Cop.v` that
  only CompCert C uses: `incr_or_decr`, `sem_incrdecr` and `incrdecr_type`.

  CompCert C is the source language of CompCert's front end: expressions have
  side effects (assignments, calls, `++`/`--`), and the reduction semantics of
  `CCLib.cfrontend.Csem` leaves the evaluation order unspecified.

  Everything lives in the namespace `CC.Csyntax`, because several names
  (`Expr`, `Stmt`, `Function`, `typeof`, …) are also used by Clight in `CC`.

  Notes on faithfulness:
  * `Csyntax.program` is `Ctypes.program function`, a record that carries the
    proof `prog_comp_env_eq : build_composite_env prog_types = OK prog_comp_env`.
    `Csyntax.Program` below keeps that field (unlike the Clight `Program`, whose
    shape is fixed by the `clightgen -lean` printer).
  * Switch case labels are `Z` (Lean's `Int`), as in Rocq.
-/
import CCLib.cfrontend.Clight
import CCLib.cfrontend.CopArith

namespace CC

namespace Cop

/-- `Cop.incr_or_decr` -/
inductive IncrOrDecr where
  | Incr
  | Decr
  deriving DecidableEq, Repr, Inhabited

/-- `Cop.sem_incrdecr` -/
def semIncrdecr (cenv : CompositeEnv) (id : IncrOrDecr) (v : Val) (ty : Ty) (m : Mem) :
    Option Val :=
  match id with
  | .Incr => semAdd cenv v ty (.Vint Integers.Int.one) type_int32s m
  | .Decr => semSub cenv v ty (.Vint Integers.Int.one) type_int32s m

/-- `Cop.incrdecr_type` -/
def incrdecrType (ty : Ty) : Ty :=
  match typeconv ty with
  | .Tpointer ty a => .Tpointer ty a
  | .Tint sz sg _ => .Tint sz sg noattr
  | .Tlong sg _ => .Tlong sg noattr
  | .Tfloat sz _ => .Tfloat sz noattr
  | _ => .Tvoid

end Cop

/-- `Ctypes.type_bool` -/
def type_bool : Ty := .Tint .IBool .Signed noattr

namespace Csyntax

/-! ## Expressions -/

mutual
/-- `Csyntax.expr`.  L-values (`Evar`, `Ederef`, `Efield`, and `Eloc` during
    reduction) denote locations; all other forms are r-values. -/
inductive Expr where
  /-- constant -/
  | Eval (v : Val) (ty : Ty)
  /-- variable -/
  | Evar (x : Ident) (ty : Ty)
  /-- access to a member of a struct or union -/
  | Efield (l : Expr) (f : Ident) (ty : Ty)
  /-- l-value used as an r-value -/
  | Evalof (l : Expr) (ty : Ty)
  /-- pointer dereference (unary `*`) -/
  | Ederef (r : Expr) (ty : Ty)
  /-- address-of operator (`&`) -/
  | Eaddrof (l : Expr) (ty : Ty)
  /-- unary arithmetic operation -/
  | Eunop (op : Unop) (r : Expr) (ty : Ty)
  /-- binary arithmetic operation -/
  | Ebinop (op : Binop) (r1 r2 : Expr) (ty : Ty)
  /-- type cast `(ty) r` -/
  | Ecast (r : Expr) (ty : Ty)
  /-- sequential "and" `r1 && r2` -/
  | Eseqand (r1 r2 : Expr) (ty : Ty)
  /-- sequential "or" `r1 || r2` -/
  | Eseqor (r1 r2 : Expr) (ty : Ty)
  /-- conditional `r1 ? r2 : r3` -/
  | Econdition (r1 r2 r3 : Expr) (ty : Ty)
  /-- size of a type -/
  | Esizeof (ty' : Ty) (ty : Ty)
  /-- natural alignment of a type -/
  | Ealignof (ty' : Ty) (ty : Ty)
  /-- assignment `l = r` -/
  | Eassign (l : Expr) (r : Expr) (ty : Ty)
  /-- assignment with arithmetic `l op= r` -/
  | Eassignop (op : Binop) (l : Expr) (r : Expr) (tyres ty : Ty)
  /-- post-increment `l++` and post-decrement `l--` -/
  | Epostincr (id : Cop.IncrOrDecr) (l : Expr) (ty : Ty)
  /-- sequence expression `r1, r2` -/
  | Ecomma (r1 r2 : Expr) (ty : Ty)
  /-- function call `r1(rargs)` -/
  | Ecall (r1 : Expr) (rargs : ExprList) (ty : Ty)
  /-- builtin function call -/
  | Ebuiltin (ef : ExtFun) (tyargs : List Ty) (rargs : ExprList) (ty : Ty)
  /-- memory location, result of evaluating an l-value -/
  | Eloc (b : Block) (ofs : Integers.Ptrofs) (bf : Bitfield) (ty : Ty)
  /-- marked subexpression -/
  | Eparen (r : Expr) (tycast : Ty) (ty : Ty)

/-- `Csyntax.exprlist` -/
inductive ExprList where
  | Enil
  | Econs (r1 : Expr) (rl : ExprList)
end

open Expr ExprList

/-- `Csyntax.Eindex`: array access `r1[r2]` is `*(r1 + r2)`. -/
def Eindex (r1 r2 : Expr) (ty : Ty) : Expr :=
  .Ederef (.Ebinop .Oadd r1 r2 (.Tpointer ty noattr)) ty

/-- `Csyntax.Epreincr`: `++l` and `--l` are `l += 1` and `l -= 1`. -/
def Epreincr (id : Cop.IncrOrDecr) (l : Expr) (ty : Ty) : Expr :=
  .Eassignop (match id with | .Incr => .Oadd | .Decr => .Osub)
    l (.Eval (.Vint Integers.Int.one) type_int32s) (typeconv ty) ty

/-- `Csyntax.Eselection`: a conditional that evaluates both arms, expressed as
    a call to the builtin `__builtin_sel`. -/
def Eselection (r1 r2 r3 : Expr) (ty : Ty) : Expr :=
  let t := (typOfType ty).inj
  let sg := mksignature [.Xint, t, t] t cc_default
  .Ebuiltin (.EF_builtin "__builtin_sel" sg) [type_bool, ty, ty]
    (.Econs r1 (.Econs r2 (.Econs r3 .Enil))) ty

/-- `Csyntax.typeof`: the type annotation of an expression. -/
def typeof : Expr → Ty
  | .Eloc _ _ _ ty | .Evar _ ty | .Ederef _ ty | .Efield _ _ ty | .Eval _ ty
  | .Evalof _ ty | .Eaddrof _ ty | .Eunop _ _ ty | .Ebinop _ _ _ ty | .Ecast _ ty
  | .Econdition _ _ _ ty | .Eseqand _ _ ty | .Eseqor _ _ ty | .Esizeof _ ty
  | .Ealignof _ ty | .Eassign _ _ ty | .Eassignop _ _ _ _ ty | .Epostincr _ _ ty
  | .Ecomma _ _ ty | .Ecall _ _ ty | .Ebuiltin _ _ _ ty | .Eparen _ _ ty => ty

/-! ## Statements -/

/-- `Csyntax.label` -/
abbrev Label := Ident

mutual
/-- `Csyntax.statement` -/
inductive Stmt where
  /-- do nothing -/
  | Sskip
  /-- evaluate an expression for its side effects -/
  | Sdo (e : Expr)
  /-- sequence -/
  | Ssequence (s1 s2 : Stmt)
  /-- conditional -/
  | Sifthenelse (e : Expr) (s1 s2 : Stmt)
  /-- `while` loop -/
  | Swhile (e : Expr) (s : Stmt)
  /-- `do` loop -/
  | Sdowhile (e : Expr) (s : Stmt)
  /-- `for` loop -/
  | Sfor (s1 : Stmt) (e : Expr) (s2 s3 : Stmt)
  /-- `break` statement -/
  | Sbreak
  /-- `continue` statement -/
  | Scontinue
  /-- `return` statement -/
  | Sreturn (e : Option Expr)
  /-- `switch` statement -/
  | Sswitch (e : Expr) (ls : LStmts)
  | Slabel (lbl : Label) (s : Stmt)
  | Sgoto (lbl : Label)

/-- `Csyntax.labeled_statements`: the cases of a `switch`; `none` is
    `default`, `some x` is `case x`. -/
inductive LStmts where
  | LSnil
  | LScons (c : Option Z) (s : Stmt) (ls : LStmts)
end

/-! ## Functions and programs -/

/-- `Csyntax.function` -/
structure Function where
  fn_return : Ty
  fn_callconv : CallConv
  fn_params : List (Ident × Ty)
  fn_vars : List (Ident × Ty)
  fn_body : Stmt

/-- `Csyntax.var_names` -/
def varNames (vars : List (Ident × Ty)) : List Ident := vars.map (·.1)

/-- `Csyntax.fundef` = `Ctypes.fundef function` -/
abbrev FunDef := FunDefGen Function

/-- `Csyntax.type_of_function` -/
def typeOfFunction (f : Function) : Ty :=
  .Tfunction (typeOfParams f.fn_params) f.fn_return f.fn_callconv

/-- `Csyntax.type_of_fundef` -/
def typeOfFundef : FunDef → Ty
  | .Internal fd => typeOfFunction fd
  | .External _ args res cc => .Tfunction args res cc

/-- `Csyntax.program` = `Ctypes.program function`, including the proof that
    the stored composite environment is the one built from the composite
    definitions. -/
structure Program where
  prog_defs : List (Ident × GlobDef FunDef Ty)
  prog_public : List Ident
  prog_main : Ident
  prog_types : List CompositeDef
  prog_comp_env : CompositeEnv
  prog_comp_env_eq : buildCompositeEnv prog_types = .OK prog_comp_env

/-- `Ctypes.program_of_program`: the underlying generic program. -/
def Program.toAST (p : Program) : ASTProgram FunDef Ty :=
  { prog_defs := p.prog_defs, prog_public := p.prog_public, prog_main := p.prog_main }

end Csyntax
end CC
