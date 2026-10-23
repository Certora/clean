/-
  Checks for the CompCert C semantics (`CCLib.cfrontend.Csyntax`, `CCLib.cfrontend.Csem`) and the
  compiler's evaluation strategy (`CCLib.cfrontend.Cstrategy`).
-/
import CCLib.cfrontend.CstrategyInversion

open CC

namespace CsemCheck

/-- `1 + 2` is a head redex with value `3`, whatever the memory. -/
example (ge : Csem.CGenv) (m : Mem) :
    Csem.Rred ge (.Ebinop .Oadd (.Eval (.Vint 1) tint) (.Eval (.Vint 2) tint) tint) m
      E0 (.Eval (.Vint 3) tint) m :=
  .binop _ _ _ _ _ _ _ _ rfl

/-- The same reduction as a step of an expression state, at the top context. -/
example (ge : Csem.CGenv) (f : Csyntax.Function) (k : Csem.Cont) (e : Env) (m : Mem) :
    Csem.Step ge (.ExprState f (.Ebinop .Oadd (.Eval (.Vint 1) tint) (.Eval (.Vint 2) tint) tint) k e m)
      E0 (.ExprState f (.Eval (.Vint 3) tint) k e m) :=
  .inl (.rred (fun x => x) f _ k e m E0 _ m (.binop _ _ _ _ _ _ _ _ rfl) (.top _))

/-- Evaluation order is unspecified: reduction may take place in either operand of a
    binary operator (here, in `a op □` and in `□ op b`). -/
example (op : Binop) (a b : Csyntax.Expr) (ty : Ty) :
    Csem.Context .RV .RV (fun x => .Ebinop op a x ty) ∧ Csem.Context .RV .RV (fun x => .Ebinop op x b ty) :=
  ⟨.binop_right _ _ _ _ _ (.top _), .binop_left _ _ _ _ _ (.top _)⟩

/-- `0 && r` short-circuits to `0` without touching `r`. -/
example (ge : Csem.CGenv) (m : Mem) (r : Csyntax.Expr) :
    Csem.Rred ge (.Eseqand (.Eval (.Vint 0) tint) r tint) m E0 (.Eval (.Vint 0) tint) m :=
  .seqand_false _ _ _ _ _ rfl

/-- `sizeof(long)` reduces to `8`. -/
example (ge : Csem.CGenv) (m : Mem) :
    Csem.Rred ge (.Esizeof (.Tlong .Signed noattr) tulong) m
      E0 (.Eval (Val.Vptrofs (Integers.Ptrofs.repr 8)) tulong) m :=
  .sizeof _ _ _

/-- `__builtin_sel(1, 10, 20)` at type `int` selects `10`. -/
example (ge : Csem.CGenv) (m : Mem) :
    Csem.Rred ge (Csyntax.Eselection (.Eval (.Vint 1) tint) (.Eval (.Vint 10) tint) (.Eval (.Vint 20) tint) tint) m
      E0 (.Eval (.Vint 10) tint) m :=
  Csem.red_selection ge (b := true) (by simp [tint]) rfl rfl rfl

/-- A continue in a `for` body moves on to the increment statement. -/
example (ge : Csem.CGenv) (f : Csyntax.Function) (a2 : Csyntax.Expr) (a3 s : Csyntax.Stmt) (k : Csem.Cont)
    (e : Env) (m : Mem) :
    Csem.Step ge (.State f .Scontinue (.Kfor3 a2 a3 s k) e m) E0 (.State f a3 (.Kfor4 a2 a3 s k) e m) :=
  .inr (.skip_or_continue_for3 _ _ _ _ _ _ _ _ (.inr rfl))

/-- Every step of every CompCert C program emits at most one event. -/
example (p : Csyntax.Program) : Smallstep.SingleEvents (Csem.semantics p) :=
  Csem.semantics_single_events p

/-- `1 + 2` is a simple expression; `x = 1` is not. -/
example : Cstrategy.simple (.Ebinop .Oadd (.Eval (.Vint 1) tint) (.Eval (.Vint 2) tint) tint) = true :=
  rfl
example (x : Ident) :
    Cstrategy.simple (.Eassign (.Evar x tint) (.Eval (.Vint 1) tint) tint) = false := rfl

/-- The strategy evaluates the simple expression `1 + 2` in one big step. -/
example (ge : Csem.CGenv) (f : Csyntax.Function) (k : Csem.Cont) (e : Env) (m : Mem) :
    Cstrategy.Step ge
      (.ExprState f (.Ebinop .Oadd (.Eval (.Vint 1) tint) (.Eval (.Vint 2) tint) tint) k e m)
      E0 (.ExprState f (.Eval (.Vint 3) tint) k e m) :=
  .inl (.expr _ _ _ _ _ _ _
    (.binop _ _ _ _ _ _ _ (.val _ _) (.val _ _) rfl) trivial rfl)

/-- In `a + (x = 1)` the strategy may reduce the assignment only because `a` is
    simple: `□ + …` to the right of a simple expression is a left context. -/
example (x : Ident) :
    Cstrategy.LeftContext .RV .RV
      (fun h => .Ebinop .Oadd (.Eval (.Vint 1) tint) h tint) :=
  .binop_right _ _ _ _ _ rfl (.top _)

/-- Reading through the null pointer `*(int * )0` is undefined behaviour: no state
    about to evaluate it is safe. -/
example (ge : Csem.CGenv) (f : Csyntax.Function) (k : Csem.Cont) (e : Env) (m : Mem) (t : Ty) :
    ¬ Cstrategy.Safe ge
      (.ExprState f (.Evalof (.Ederef (.Eval (.Vint 0) (tptr t)) t) t) k e m) := by
  intro hs
  obtain ⟨b, ofs, h⟩ := Cstrategy.safe_inv (C := fun x => .Evalof x t) hs (.rvalof _ _ _ (.top _))
  cases h

end CsemCheck
