/-
  A big-step semantics for CompCert C implementing the compiler's reduction
  strategy — the definitions of the second half of `cfrontend/Cstrategy.v`
  (section `BIGSTEP`, `bigstep_program_terminates`/`_diverges`,
  `bigstep_semantics`).

  * `EvalExpression`, `EvalExpr`, `EvalExprlist`, `ExecStmt`, `EvalFuncall`:
    terminating evaluations of expressions, statements and function calls
    (Rocq: `eval_expression`, `eval_expr`, `eval_exprlist`, `exec_stmt`,
    `eval_funcall`, one mutually inductive family).  `EvalExpr e m K a t m' a'`
    evaluates all side effects of `a`, leaving the simple expression `a'`.
  * `EvalinfExpr`, `EvalinfExprlist`, `ExecinfStmt`, `EvalinfFuncall`:
    diverging evaluations (Rocq: `evalinf_*`, `execinf_stmt`, mutually
    *coinductive*; here Lean `coinductive` predicates).

  Outcomes (`Outcome`, `OutNormalOrContinue`, `OutBreakOrReturn`,
  `outcomeSwitch`, `outcomeResultValue`) are identical to Clight's, so the
  definitions of `CCLib.cfrontend.ClightBigstep` are reused.

  The soundness proof (`bigstep_semantics_sound`) is in
  `CCLib.cfrontend.CstrategyBigstepSound`.
-/
import CCLib.cfrontend.Cstrategy
import CCLib.cfrontend.ClightBigstep

namespace CC
namespace Cstrategy

open Smallstep
open ClightBigstep (Outcome OutNormalOrContinue OutBreakOrReturn outcomeSwitch outcomeResultValue)
open ClightBigstep.Outcome

section BIGSTEP

variable (ge : Csem.CGenv)

mutual
/-- `Cstrategy.eval_expression`: full evaluation of an expression to a value. -/
inductive EvalExpression : Env → Mem → Csyntax.Expr → Trace → Mem → Val → Prop where
  | intro (e m a t m' a' v) :
      EvalExpr e m .RV a t m' a' → EvalSimpleRvalue ge e m' a' v →
      EvalExpression e m a t m' v

/-- `Cstrategy.eval_expr`: evaluation of the side effects of an expression,
    leaving a simple expression. -/
inductive EvalExpr : Env → Mem → Csem.Kind → Csyntax.Expr → Trace → Mem → Csyntax.Expr → Prop where
  | val (e m v ty) : EvalExpr e m .RV (.Eval v ty) E0 m (.Eval v ty)
  | var (e m x ty) : EvalExpr e m .LV (.Evar x ty) E0 m (.Evar x ty)
  | field (e m a t m' a' f ty) :
      EvalExpr e m .RV a t m' a' →
      EvalExpr e m .LV (.Efield a f ty) t m' (.Efield a' f ty)
  | valof (e m a t m' a' ty) :
      typeIsVolatile (Csyntax.typeof a) = false →
      EvalExpr e m .LV a t m' a' →
      EvalExpr e m .RV (.Evalof a ty) t m' (.Evalof a' ty)
  | valof_volatile (e m a t1 m' a' ty b ofs bf t2 v) :
      typeIsVolatile (Csyntax.typeof a) = true →
      EvalExpr e m .LV a t1 m' a' →
      EvalSimpleLvalue ge e m' a' b ofs bf →
      Csem.DerefLoc ge (Csyntax.typeof a) m' b ofs bf t2 v →
      ty = Csyntax.typeof a →
      EvalExpr e m .RV (.Evalof a ty) (Eapp t1 t2) m' (.Eval v ty)
  | deref (e m a t m' a' ty) :
      EvalExpr e m .RV a t m' a' →
      EvalExpr e m .LV (.Ederef a ty) t m' (.Ederef a' ty)
  | addrof (e m a t m' a' ty) :
      EvalExpr e m .LV a t m' a' →
      EvalExpr e m .RV (.Eaddrof a ty) t m' (.Eaddrof a' ty)
  | unop (e m a t m' a' op ty) :
      EvalExpr e m .RV a t m' a' →
      EvalExpr e m .RV (.Eunop op a ty) t m' (.Eunop op a' ty)
  | binop (e m a1 t1 m' a1' a2 t2 m'' a2' op ty) :
      EvalExpr e m .RV a1 t1 m' a1' → EvalExpr e m' .RV a2 t2 m'' a2' →
      EvalExpr e m .RV (.Ebinop op a1 a2 ty) (Eapp t1 t2) m'' (.Ebinop op a1' a2' ty)
  | cast (e m a t m' a' ty) :
      EvalExpr e m .RV a t m' a' →
      EvalExpr e m .RV (.Ecast a ty) t m' (.Ecast a' ty)
  | seqand_true (e m a1 a2 ty t1 m' a1' v1 t2 m'' a2' v2 v) :
      EvalExpr e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some true →
      EvalExpr e m' .RV a2 t2 m'' a2' → EvalSimpleRvalue ge e m'' a2' v2 →
      Cop.semCast v2 (Csyntax.typeof a2) type_bool m'' = some v →
      EvalExpr e m .RV (.Eseqand a1 a2 ty) (Eapp t1 t2) m'' (.Eval v ty)
  | seqand_false (e m a1 a2 ty t1 m' a1' v1) :
      EvalExpr e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some false →
      EvalExpr e m .RV (.Eseqand a1 a2 ty) t1 m' (.Eval (.Vint Integers.Int.zero) ty)
  | seqor_false (e m a1 a2 ty t1 m' a1' v1 t2 m'' a2' v2 v) :
      EvalExpr e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some false →
      EvalExpr e m' .RV a2 t2 m'' a2' → EvalSimpleRvalue ge e m'' a2' v2 →
      Cop.semCast v2 (Csyntax.typeof a2) type_bool m'' = some v →
      EvalExpr e m .RV (.Eseqor a1 a2 ty) (Eapp t1 t2) m'' (.Eval v ty)
  | seqor_true (e m a1 a2 ty t1 m' a1' v1) :
      EvalExpr e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some true →
      EvalExpr e m .RV (.Eseqor a1 a2 ty) t1 m' (.Eval (.Vint Integers.Int.one) ty)
  | condition (e m a1 a2 a3 ty t1 m' a1' v1 t2 m'' a' v' b v) :
      EvalExpr e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some b →
      EvalExpr e m' .RV (if b then a2 else a3) t2 m'' a' → EvalSimpleRvalue ge e m'' a' v' →
      Cop.semCast v' (Csyntax.typeof (if b then a2 else a3)) ty m'' = some v →
      EvalExpr e m .RV (.Econdition a1 a2 a3 ty) (Eapp t1 t2) m'' (.Eval v ty)
  | sizeof (e m ty' ty) : EvalExpr e m .RV (.Esizeof ty' ty) E0 m (.Esizeof ty' ty)
  | alignof (e m ty' ty) : EvalExpr e m .RV (.Ealignof ty' ty) E0 m (.Ealignof ty' ty)
  | assign (e m l r ty t1 m1 l' t2 m2 r' b ofs bf v v1 v' t3 m3) :
      EvalExpr e m .LV l t1 m1 l' → EvalExpr e m1 .RV r t2 m2 r' →
      EvalSimpleLvalue ge e m2 l' b ofs bf →
      EvalSimpleRvalue ge e m2 r' v →
      Cop.semCast v (Csyntax.typeof r) (Csyntax.typeof l) m2 = some v1 →
      Csem.AssignLoc ge (Csyntax.typeof l) m2 b ofs bf v1 t3 m3 v' →
      ty = Csyntax.typeof l →
      EvalExpr e m .RV (.Eassign l r ty) (Eapp t1 (Eapp t2 t3)) m3 (.Eval v' ty)
  | assignop (e m op l r tyres ty t1 m1 l' t2 m2 r' b ofs bf v1 v2 v3 v4 v' t3 t4 m3) :
      EvalExpr e m .LV l t1 m1 l' → EvalExpr e m1 .RV r t2 m2 r' →
      EvalSimpleLvalue ge e m2 l' b ofs bf →
      Csem.DerefLoc ge (Csyntax.typeof l) m2 b ofs bf t3 v1 →
      EvalSimpleRvalue ge e m2 r' v2 →
      Cop.semBinaryOperation ge.genv_cenv op v1 (Csyntax.typeof l) v2 (Csyntax.typeof r) m2 =
        some v3 →
      Cop.semCast v3 tyres (Csyntax.typeof l) m2 = some v4 →
      Csem.AssignLoc ge (Csyntax.typeof l) m2 b ofs bf v4 t4 m3 v' →
      ty = Csyntax.typeof l →
      EvalExpr e m .RV (.Eassignop op l r tyres ty) (Eapp t1 (Eapp t2 (Eapp t3 t4))) m3
        (.Eval v' ty)
  | postincr (e m id l ty t1 m1 l' b ofs bf v1 v2 v3 v' m2 t2 t3) :
      EvalExpr e m .LV l t1 m1 l' →
      EvalSimpleLvalue ge e m1 l' b ofs bf →
      Csem.DerefLoc ge ty m1 b ofs bf t2 v1 →
      Cop.semIncrdecr ge.genv_cenv id v1 ty m1 = some v2 →
      Cop.semCast v2 (Cop.incrdecrType ty) ty m1 = some v3 →
      Csem.AssignLoc ge ty m1 b ofs bf v3 t3 m2 v' →
      ty = Csyntax.typeof l →
      EvalExpr e m .RV (.Epostincr id l ty) (Eapp t1 (Eapp t2 t3)) m2 (.Eval v1 ty)
  | comma (e m r1 r2 ty t1 m1 r1' v1 t2 m2 r2') :
      EvalExpr e m .RV r1 t1 m1 r1' →
      EvalSimpleRvalue ge e m1 r1' v1 →
      EvalExpr e m1 .RV r2 t2 m2 r2' →
      ty = Csyntax.typeof r2 →
      EvalExpr e m .RV (.Ecomma r1 r2 ty) (Eapp t1 t2) m2 r2'
  | call (e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs targs tres cconv fd t3 m3 vres) :
      EvalExpr e m .RV rf t1 m1 rf' → EvalExprlist e m1 rargs t2 m2 rargs' →
      EvalSimpleRvalue ge e m2 rf' vf →
      EvalSimpleList ge e m2 rargs' targs vargs →
      Cop.classifyFun (Csyntax.typeof rf) = .f targs tres cconv →
      Genv.findFunct ge.genv_genv vf = some fd →
      Csyntax.typeOfFundef fd = .Tfunction targs tres cconv →
      EvalFuncall m2 fd vargs t3 m3 vres →
      EvalExpr e m .RV (.Ecall rf rargs ty) (Eapp t1 (Eapp t2 t3)) m3 (.Eval vres ty)

/-- `Cstrategy.eval_exprlist` -/
inductive EvalExprlist : Env → Mem → Csyntax.ExprList → Trace → Mem → Csyntax.ExprList → Prop where
  | nil (e m) : EvalExprlist e m .Enil E0 m .Enil
  | cons (e m a1 al t1 m1 a1' t2 m2 al') :
      EvalExpr e m .RV a1 t1 m1 a1' → EvalExprlist e m1 al t2 m2 al' →
      EvalExprlist e m (.Econs a1 al) (Eapp t1 t2) m2 (.Econs a1' al')

/-- `Cstrategy.exec_stmt`: terminating execution of a statement, with its
    outcome. -/
inductive ExecStmt : Env → Mem → Csyntax.Stmt → Trace → Mem → Outcome → Prop where
  | skip (e m) : ExecStmt e m .Sskip E0 m Out_normal
  | do_ (e m a t m' v) :
      EvalExpression e m a t m' v →
      ExecStmt e m (.Sdo a) t m' Out_normal
  | seq_1 (e m s1 s2 t1 m1 t2 m2 out) :
      ExecStmt e m s1 t1 m1 Out_normal →
      ExecStmt e m1 s2 t2 m2 out →
      ExecStmt e m (.Ssequence s1 s2) (Eapp t1 t2) m2 out
  | seq_2 (e m s1 s2 t1 m1 out) :
      ExecStmt e m s1 t1 m1 out →
      out ≠ Out_normal →
      ExecStmt e m (.Ssequence s1 s2) t1 m1 out
  | ifthenelse (e m a s1 s2 t1 m1 v1 t2 m2 b out) :
      EvalExpression e m a t1 m1 v1 →
      Cop.boolVal v1 (Csyntax.typeof a) m1 = some b →
      ExecStmt e m1 (if b then s1 else s2) t2 m2 out →
      ExecStmt e m (.Sifthenelse a s1 s2) (Eapp t1 t2) m2 out
  | return_none (e m) : ExecStmt e m (.Sreturn none) E0 m (Out_return none)
  | return_some (e m a t m' v) :
      EvalExpression e m a t m' v →
      ExecStmt e m (.Sreturn (some a)) t m' (Out_return (some (v, Csyntax.typeof a)))
  | break_ (e m) : ExecStmt e m .Sbreak E0 m Out_break
  | continue_ (e m) : ExecStmt e m .Scontinue E0 m Out_continue
  | while_false (e m a s t m' v) :
      EvalExpression e m a t m' v →
      Cop.boolVal v (Csyntax.typeof a) m' = some false →
      ExecStmt e m (.Swhile a s) t m' Out_normal
  | while_stop (e m a s t1 m1 v t2 m2 out' out) :
      EvalExpression e m a t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a) m1 = some true →
      ExecStmt e m1 s t2 m2 out' →
      OutBreakOrReturn out' out →
      ExecStmt e m (.Swhile a s) (Eapp t1 t2) m2 out
  | while_loop (e m a s t1 m1 v t2 m2 out1 t3 m3 out) :
      EvalExpression e m a t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a) m1 = some true →
      ExecStmt e m1 s t2 m2 out1 →
      OutNormalOrContinue out1 →
      ExecStmt e m2 (.Swhile a s) t3 m3 out →
      ExecStmt e m (.Swhile a s) (Eapp t1 (Eapp t2 t3)) m3 out
  | dowhile_false (e m s a t1 m1 out1 t2 m2 v) :
      ExecStmt e m s t1 m1 out1 →
      OutNormalOrContinue out1 →
      EvalExpression e m1 a t2 m2 v →
      Cop.boolVal v (Csyntax.typeof a) m2 = some false →
      ExecStmt e m (.Sdowhile a s) (Eapp t1 t2) m2 Out_normal
  | dowhile_stop (e m s a t m1 out1 out) :
      ExecStmt e m s t m1 out1 →
      OutBreakOrReturn out1 out →
      ExecStmt e m (.Sdowhile a s) t m1 out
  | dowhile_loop (e m s a t1 m1 out1 t2 m2 v t3 m3 out) :
      ExecStmt e m s t1 m1 out1 →
      OutNormalOrContinue out1 →
      EvalExpression e m1 a t2 m2 v →
      Cop.boolVal v (Csyntax.typeof a) m2 = some true →
      ExecStmt e m2 (.Sdowhile a s) t3 m3 out →
      ExecStmt e m (.Sdowhile a s) (Eapp t1 (Eapp t2 t3)) m3 out
  | for_start (e m s a1 a2 a3 out m1 m2 t1 t2) :
      ExecStmt e m a1 t1 m1 Out_normal →
      ExecStmt e m1 (.Sfor .Sskip a2 a3 s) t2 m2 out →
      ExecStmt e m (.Sfor a1 a2 a3 s) (Eapp t1 t2) m2 out
  | for_false (e m s a2 a3 t m' v) :
      EvalExpression e m a2 t m' v →
      Cop.boolVal v (Csyntax.typeof a2) m' = some false →
      ExecStmt e m (.Sfor .Sskip a2 a3 s) t m' Out_normal
  | for_stop (e m s a2 a3 t1 m1 v t2 m2 out1 out) :
      EvalExpression e m a2 t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a2) m1 = some true →
      ExecStmt e m1 s t2 m2 out1 →
      OutBreakOrReturn out1 out →
      ExecStmt e m (.Sfor .Sskip a2 a3 s) (Eapp t1 t2) m2 out
  | for_loop (e m s a2 a3 t1 m1 v t2 m2 out1 t3 m3 t4 m4 out) :
      EvalExpression e m a2 t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a2) m1 = some true →
      ExecStmt e m1 s t2 m2 out1 →
      OutNormalOrContinue out1 →
      ExecStmt e m2 a3 t3 m3 Out_normal →
      ExecStmt e m3 (.Sfor .Sskip a2 a3 s) t4 m4 out →
      ExecStmt e m (.Sfor .Sskip a2 a3 s) (Eapp t1 (Eapp t2 (Eapp t3 t4))) m4 out
  | switch (e m a sl t1 m1 v n t2 m2 out) :
      EvalExpression e m a t1 m1 v →
      Cop.semSwitchArg v (Csyntax.typeof a) = some n →
      ExecStmt e m1 (Csem.seqOfLabeledStatement (Csem.selectSwitch n sl)) t2 m2 out →
      ExecStmt e m (.Sswitch a sl) (Eapp t1 t2) m2 (outcomeSwitch out)

/-- `Cstrategy.eval_funcall` -/
inductive EvalFuncall : Mem → Csyntax.FunDef → List Val → Trace → Mem → Val → Prop where
  | internal (m f vargs t e m1 m2 m3 out vres m4) :
      listNorepet (Csyntax.varNames f.fn_params ++ Csyntax.varNames f.fn_vars) →
      Csem.AllocVariables ge emptyEnv m (f.fn_params ++ f.fn_vars) e m1 →
      Csem.BindParameters ge e m1 f.fn_params vargs m2 →
      ExecStmt e m2 f.fn_body t m3 out →
      outcomeResultValue out f.fn_return vres m3 →
      Mem.freeList m3 (blocksOfEnv ge.genv_cenv e) = some m4 →
      EvalFuncall m (.Internal f) vargs t m4 vres
  | external (m ef targs tres cconv vargs t vres m') :
      externalCall ef ge.genv_genv.toSenv vargs m t vres m' →
      EvalFuncall m (.External ef targs tres cconv) vargs t m' vres
end

mutual
/-- `Cstrategy.evalinf_expr`: the evaluation of the expression diverges. -/
coinductive EvalinfExpr : Env → Mem → Csem.Kind → Csyntax.Expr → Traceinf → Prop where
  | field (e m a t f ty) :
      EvalinfExpr e m .RV a t → EvalinfExpr e m .LV (.Efield a f ty) t
  | valof (e m a t ty) :
      EvalinfExpr e m .LV a t → EvalinfExpr e m .RV (.Evalof a ty) t
  | deref (e m a t ty) :
      EvalinfExpr e m .RV a t → EvalinfExpr e m .LV (.Ederef a ty) t
  | addrof (e m a t ty) :
      EvalinfExpr e m .LV a t → EvalinfExpr e m .RV (.Eaddrof a ty) t
  | unop (e m a t op ty) :
      EvalinfExpr e m .RV a t → EvalinfExpr e m .RV (.Eunop op a ty) t
  | binop_left (e m a1 t1 a2 op ty) :
      EvalinfExpr e m .RV a1 t1 → EvalinfExpr e m .RV (.Ebinop op a1 a2 ty) t1
  | binop_right (e m a1 t1 m' a1' a2 t2 op ty) :
      EvalExpr ge e m .RV a1 t1 m' a1' → EvalinfExpr e m' .RV a2 t2 →
      EvalinfExpr e m .RV (.Ebinop op a1 a2 ty) (Eappinf t1 t2)
  | cast (e m a t ty) :
      EvalinfExpr e m .RV a t → EvalinfExpr e m .RV (.Ecast a ty) t
  | seqand (e m a1 a2 ty t1) :
      EvalinfExpr e m .RV a1 t1 → EvalinfExpr e m .RV (.Eseqand a1 a2 ty) t1
  | seqand_2 (e m a1 a2 ty t1 m' a1' v1 t2) :
      EvalExpr ge e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some true →
      EvalinfExpr e m' .RV a2 t2 →
      EvalinfExpr e m .RV (.Eseqand a1 a2 ty) (Eappinf t1 t2)
  | seqor (e m a1 a2 ty t1) :
      EvalinfExpr e m .RV a1 t1 → EvalinfExpr e m .RV (.Eseqor a1 a2 ty) t1
  | seqor_2 (e m a1 a2 ty t1 m' a1' v1 t2) :
      EvalExpr ge e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some false →
      EvalinfExpr e m' .RV a2 t2 →
      EvalinfExpr e m .RV (.Eseqor a1 a2 ty) (Eappinf t1 t2)
  | condition (e m a1 a2 a3 ty t1) :
      EvalinfExpr e m .RV a1 t1 → EvalinfExpr e m .RV (.Econdition a1 a2 a3 ty) t1
  | condition_2 (e m a1 a2 a3 ty t1 m' a1' v1 t2 b) :
      EvalExpr ge e m .RV a1 t1 m' a1' → EvalSimpleRvalue ge e m' a1' v1 →
      Cop.boolVal v1 (Csyntax.typeof a1) m' = some b →
      EvalinfExpr e m' .RV (if b then a2 else a3) t2 →
      EvalinfExpr e m .RV (.Econdition a1 a2 a3 ty) (Eappinf t1 t2)
  | assign_left (e m a1 t1 a2 ty) :
      EvalinfExpr e m .LV a1 t1 → EvalinfExpr e m .RV (.Eassign a1 a2 ty) t1
  | assign_right (e m a1 t1 m' a1' a2 t2 ty) :
      EvalExpr ge e m .LV a1 t1 m' a1' → EvalinfExpr e m' .RV a2 t2 →
      EvalinfExpr e m .RV (.Eassign a1 a2 ty) (Eappinf t1 t2)
  | assignop_left (e m a1 t1 a2 op tyres ty) :
      EvalinfExpr e m .LV a1 t1 → EvalinfExpr e m .RV (.Eassignop op a1 a2 tyres ty) t1
  | assignop_right (e m a1 t1 m' a1' a2 t2 op tyres ty) :
      EvalExpr ge e m .LV a1 t1 m' a1' → EvalinfExpr e m' .RV a2 t2 →
      EvalinfExpr e m .RV (.Eassignop op a1 a2 tyres ty) (Eappinf t1 t2)
  | postincr (e m a t id ty) :
      EvalinfExpr e m .LV a t → EvalinfExpr e m .RV (.Epostincr id a ty) t
  | comma_left (e m a1 t1 a2 ty) :
      EvalinfExpr e m .RV a1 t1 → EvalinfExpr e m .RV (.Ecomma a1 a2 ty) t1
  | comma_right (e m a1 t1 m1 a1' v1 a2 t2 ty) :
      EvalExpr ge e m .RV a1 t1 m1 a1' → EvalSimpleRvalue ge e m1 a1' v1 →
      ty = Csyntax.typeof a2 →
      EvalinfExpr e m1 .RV a2 t2 →
      EvalinfExpr e m .RV (.Ecomma a1 a2 ty) (Eappinf t1 t2)
  | call_left (e m a1 t1 a2 ty) :
      EvalinfExpr e m .RV a1 t1 → EvalinfExpr e m .RV (.Ecall a1 a2 ty) t1
  | call_right (e m a1 t1 m1 a1' a2 t2 ty) :
      EvalExpr ge e m .RV a1 t1 m1 a1' →
      EvalinfExprlist e m1 a2 t2 →
      EvalinfExpr e m .RV (.Ecall a1 a2 ty) (Eappinf t1 t2)
  | call (e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs targs tres cconv fd t3) :
      EvalExpr ge e m .RV rf t1 m1 rf' → EvalExprlist ge e m1 rargs t2 m2 rargs' →
      EvalSimpleRvalue ge e m2 rf' vf →
      EvalSimpleList ge e m2 rargs' targs vargs →
      Cop.classifyFun (Csyntax.typeof rf) = .f targs tres cconv →
      Genv.findFunct ge.genv_genv vf = some fd →
      Csyntax.typeOfFundef fd = .Tfunction targs tres cconv →
      EvalinfFuncall m2 fd vargs t3 →
      EvalinfExpr e m .RV (.Ecall rf rargs ty) (Eappinf t1 (Eappinf t2 t3))

/-- `Cstrategy.evalinf_exprlist` -/
coinductive EvalinfExprlist : Env → Mem → Csyntax.ExprList → Traceinf → Prop where
  | cons_left (e m a1 al t1) :
      EvalinfExpr e m .RV a1 t1 → EvalinfExprlist e m (.Econs a1 al) t1
  | cons_right (e m a1 al t1 m1 a1' t2) :
      EvalExpr ge e m .RV a1 t1 m1 a1' → EvalinfExprlist e m1 al t2 →
      EvalinfExprlist e m (.Econs a1 al) (Eappinf t1 t2)

/-- `Cstrategy.execinf_stmt`: the execution of the statement diverges. -/
coinductive ExecinfStmt : Env → Mem → Csyntax.Stmt → Traceinf → Prop where
  | do_ (e m a t) : EvalinfExpr e m .RV a t → ExecinfStmt e m (.Sdo a) t
  | seq_1 (e m s1 s2 t1) : ExecinfStmt e m s1 t1 → ExecinfStmt e m (.Ssequence s1 s2) t1
  | seq_2 (e m s1 s2 t1 m1 t2) :
      ExecStmt ge e m s1 t1 m1 Out_normal →
      ExecinfStmt e m1 s2 t2 →
      ExecinfStmt e m (.Ssequence s1 s2) (Eappinf t1 t2)
  | ifthenelse_test (e m a s1 s2 t1) :
      EvalinfExpr e m .RV a t1 → ExecinfStmt e m (.Sifthenelse a s1 s2) t1
  | ifthenelse (e m a s1 s2 t1 m1 v1 t2 b) :
      EvalExpression ge e m a t1 m1 v1 →
      Cop.boolVal v1 (Csyntax.typeof a) m1 = some b →
      ExecinfStmt e m1 (if b then s1 else s2) t2 →
      ExecinfStmt e m (.Sifthenelse a s1 s2) (Eappinf t1 t2)
  | return_some (e m a t) :
      EvalinfExpr e m .RV a t → ExecinfStmt e m (.Sreturn (some a)) t
  | while_test (e m a s t1) :
      EvalinfExpr e m .RV a t1 → ExecinfStmt e m (.Swhile a s) t1
  | while_body (e m a s t1 m1 v t2) :
      EvalExpression ge e m a t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a) m1 = some true →
      ExecinfStmt e m1 s t2 →
      ExecinfStmt e m (.Swhile a s) (Eappinf t1 t2)
  | while_loop (e m a s t1 m1 v t2 m2 out1 t3) :
      EvalExpression ge e m a t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a) m1 = some true →
      ExecStmt ge e m1 s t2 m2 out1 →
      OutNormalOrContinue out1 →
      ExecinfStmt e m2 (.Swhile a s) t3 →
      ExecinfStmt e m (.Swhile a s) (Eappinf t1 (Eappinf t2 t3))
  | dowhile_body (e m s a t1) :
      ExecinfStmt e m s t1 → ExecinfStmt e m (.Sdowhile a s) t1
  | dowhile_test (e m s a t1 m1 out1 t2) :
      ExecStmt ge e m s t1 m1 out1 →
      OutNormalOrContinue out1 →
      EvalinfExpr e m1 .RV a t2 →
      ExecinfStmt e m (.Sdowhile a s) (Eappinf t1 t2)
  | dowhile_loop (e m s a t1 m1 out1 t2 m2 v t3) :
      ExecStmt ge e m s t1 m1 out1 →
      OutNormalOrContinue out1 →
      EvalExpression ge e m1 a t2 m2 v →
      Cop.boolVal v (Csyntax.typeof a) m2 = some true →
      ExecinfStmt e m2 (.Sdowhile a s) t3 →
      ExecinfStmt e m (.Sdowhile a s) (Eappinf t1 (Eappinf t2 t3))
  | for_start_1 (e m s a1 a2 a3 t1) :
      ExecinfStmt e m a1 t1 → ExecinfStmt e m (.Sfor a1 a2 a3 s) t1
  | for_start_2 (e m s a1 a2 a3 m1 t1 t2) :
      ExecStmt ge e m a1 t1 m1 Out_normal → a1 ≠ .Sskip →
      ExecinfStmt e m1 (.Sfor .Sskip a2 a3 s) t2 →
      ExecinfStmt e m (.Sfor a1 a2 a3 s) (Eappinf t1 t2)
  | for_test (e m s a2 a3 t) :
      EvalinfExpr e m .RV a2 t → ExecinfStmt e m (.Sfor .Sskip a2 a3 s) t
  | for_body (e m s a2 a3 t1 m1 v t2) :
      EvalExpression ge e m a2 t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a2) m1 = some true →
      ExecinfStmt e m1 s t2 →
      ExecinfStmt e m (.Sfor .Sskip a2 a3 s) (Eappinf t1 t2)
  | for_next (e m s a2 a3 t1 m1 v t2 m2 out1 t3) :
      EvalExpression ge e m a2 t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a2) m1 = some true →
      ExecStmt ge e m1 s t2 m2 out1 →
      OutNormalOrContinue out1 →
      ExecinfStmt e m2 a3 t3 →
      ExecinfStmt e m (.Sfor .Sskip a2 a3 s) (Eappinf t1 (Eappinf t2 t3))
  | for_loop (e m s a2 a3 t1 m1 v t2 m2 out1 t3 m3 t4) :
      EvalExpression ge e m a2 t1 m1 v →
      Cop.boolVal v (Csyntax.typeof a2) m1 = some true →
      ExecStmt ge e m1 s t2 m2 out1 →
      OutNormalOrContinue out1 →
      ExecStmt ge e m2 a3 t3 m3 Out_normal →
      ExecinfStmt e m3 (.Sfor .Sskip a2 a3 s) t4 →
      ExecinfStmt e m (.Sfor .Sskip a2 a3 s) (Eappinf t1 (Eappinf t2 (Eappinf t3 t4)))
  | switch_expr (e m a sl t1) :
      EvalinfExpr e m .RV a t1 → ExecinfStmt e m (.Sswitch a sl) t1
  | switch_body (e m a sl t1 m1 v n t2) :
      EvalExpression ge e m a t1 m1 v →
      Cop.semSwitchArg v (Csyntax.typeof a) = some n →
      ExecinfStmt e m1 (Csem.seqOfLabeledStatement (Csem.selectSwitch n sl)) t2 →
      ExecinfStmt e m (.Sswitch a sl) (Eappinf t1 t2)

/-- `Cstrategy.evalinf_funcall` -/
coinductive EvalinfFuncall : Mem → Csyntax.FunDef → List Val → Traceinf → Prop where
  | internal (m f vargs t e m1 m2) :
      listNorepet (Csyntax.varNames f.fn_params ++ Csyntax.varNames f.fn_vars) →
      Csem.AllocVariables ge emptyEnv m (f.fn_params ++ f.fn_vars) e m1 →
      Csem.BindParameters ge e m1 f.fn_params vargs m2 →
      ExecinfStmt e m2 f.fn_body t →
      EvalinfFuncall m (.Internal f) vargs t
end

end BIGSTEP

/-! ## Whole programs -/

/-- `Cstrategy.bigstep_program_terminates` -/
inductive BigstepProgramTerminates (p : Csyntax.Program) : Trace → Integers.Int → Prop where
  | intro (b f m0 m1 t r) :
      Csem.initMem p = some m0 →
      Genv.findSymbol (Csem.globalenv p).genv_genv p.prog_main = some b →
      Genv.findFunctPtr (Csem.globalenv p).genv_genv b = some f →
      Csyntax.typeOfFundef f = .Tfunction [] type_int32s cc_default →
      EvalFuncall (Csem.globalenv p) m0 f [] t m1 (.Vint r) →
      BigstepProgramTerminates p t r

/-- `Cstrategy.bigstep_program_diverges` -/
inductive BigstepProgramDiverges (p : Csyntax.Program) : Traceinf → Prop where
  | intro (b f m0 t) :
      Csem.initMem p = some m0 →
      Genv.findSymbol (Csem.globalenv p).genv_genv p.prog_main = some b →
      Genv.findFunctPtr (Csem.globalenv p).genv_genv b = some f →
      Csyntax.typeOfFundef f = .Tfunction [] type_int32s cc_default →
      EvalinfFuncall (Csem.globalenv p) m0 f [] t →
      BigstepProgramDiverges p t

/-- `Cstrategy.bigstep_semantics` -/
def bigstepSemantics (p : Csyntax.Program) : BigstepSemantics :=
  ⟨BigstepProgramTerminates p, BigstepProgramDiverges p⟩

end Cstrategy
end CC
