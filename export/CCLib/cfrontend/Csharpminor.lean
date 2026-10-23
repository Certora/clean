/-
  Abstract syntax of Csharpminor — port of the syntax part of
  `cfrontend/Csharpminor.v`.

  Csharpminor is the target of `Cshmgen` (Clight → Csharpminor) and the
  source of `Cminorgen`.  Its operators are those of Cminor.
-/
import CCLib.backend.Cminor

namespace CC
namespace Csharpminor

/-- `Csharpminor.constant` -/
inductive Constant where
  | Ointconst (n : Integers.Int)
  | Ofloatconst (f : Floats.Float)
  | Osingleconst (f : Floats.Float32)
  | Olongconst (n : Integers.Int64)

/-- `Csharpminor.unary_operation` -/
abbrev UnaryOperation := Cminor.UnaryOperation
/-- `Csharpminor.binary_operation` -/
abbrev BinaryOperation := Cminor.BinaryOperation

/-- `Csharpminor.expr` -/
inductive Expr where
  /-- reading a temporary variable -/
  | Evar (id : Ident)
  /-- taking the address of a variable -/
  | Eaddrof (id : Ident)
  | Econst (c : Constant)
  | Eunop (op : UnaryOperation) (a : Expr)
  | Ebinop (op : BinaryOperation) (a1 a2 : Expr)
  | Eload (chunk : Chunk) (a : Expr)

/-- `Csharpminor.label` -/
abbrev Label := Ident

mutual
/-- `Csharpminor.stmt` -/
inductive Stmt where
  | Sskip
  | Sset (id : Ident) (a : Expr)
  | Sstore (chunk : Chunk) (addr a : Expr)
  | Scall (optid : Option Ident) (sg : Signature) (fn : Expr) (args : List Expr)
  | Sbuiltin (optid : Option Ident) (ef : ExtFun) (args : List Expr)
  | Sseq (s1 s2 : Stmt)
  | Sifthenelse (a : Expr) (s1 s2 : Stmt)
  | Sloop (s : Stmt)
  | Sblock (s : Stmt)
  | Sexit (n : Nat)
  | Sswitch (islong : Bool) (a : Expr) (cases : LblStmt)
  | Sreturn (a : Option Expr)
  | Slabel (lbl : Label) (s : Stmt)
  | Sgoto (lbl : Label)

/-- `Csharpminor.lbl_stmt` -/
inductive LblStmt where
  | LSnil
  | LScons (c : Option Z) (s : Stmt) (ls : LblStmt)
end

/-- `Csharpminor.function` -/
structure Function where
  fn_sig : Signature
  fn_params : List Ident
  fn_vars : List (Ident × Z)
  fn_temps : List Ident
  fn_body : Stmt

/-- `Csharpminor.fundef` -/
abbrev Fundef := ASTFundef Function

/-- `Csharpminor.program` -/
abbrev Program := ASTProgram Fundef Unit

/-- `Csharpminor.funsig` -/
def funsig : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External ef => ef.sig

end Csharpminor
end CC
