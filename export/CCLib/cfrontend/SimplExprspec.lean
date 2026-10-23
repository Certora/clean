/-
  Relational specification of expression simplification — port of
  `cfrontend/SimplExprspec.v` (the whole file).

  `TrExpr le dst a sl a' tmps` says that the CompCert C expression `a` is
  translated to the Clight statements `sl` and the pure Clight expression
  `a'`, using only temporaries from `tmps`.  The main results are
  `transl_meets_spec` (the functions of `CCLib.cfrontend.SimplExpr` satisfy the
  relation), `transl_stmt_meets_spec`, `transl_function_spec` and
  `transl_fundef_spec`.

  Differences from Rocq:
  * `In`, `incl` and `list_disjoint` are Lean's `∈`, `⊆` and the port's
    `listDisjoint`;
  * the `eauto with gensym` automation is replaced by the local tactics
    `pos_omega`, `within_tac`, `contained_tac`, `disj_tac` and `incl_tac`.
-/
import CCLib.cfrontend.SimplExpr

namespace CC
namespace SimplExpr

open Destination SetDestination

/-! ## Relational specification of the translation of expressions -/

/-- `SimplExprspec.final` -/
def final (dst : Destination) (a : Expr) : List Stmt :=
  match dst with
  | .For_val => []
  | .For_effects => []
  | .For_set sd => doSet sd a

section SPEC

variable (ce : CompositeEnv)

/-- `SimplExprspec.tr_is_bitfield_access` -/
def TrIsBitfieldAccess (l : Expr) (bf : Bitfield) : Prop :=
  match l with
  | .Efield r f _ =>
    ∃ co ofs,
      match typeof r with
      | .Tstruct id _ => ce.get id = some co ∧ fieldOffset ce f co.co_members = .OK (ofs, bf)
      | .Tunion id _ => ce.get id = some co ∧ unionFieldOffset ce f co.co_members = .OK (ofs, bf)
      | _ => False
  | _ => bf = .Full

/-- `SimplExprspec.tr_rvalof` -/
inductive TrRvalof : Ty → Expr → List Stmt → Expr → List Ident → Prop where
  | tr_rvalof_nonvol (ty a tmp) :
      typeIsVolatile ty = false →
      TrRvalof ty a [] a tmp
  | tr_rvalof_vol (ty a t bf tmp) :
      typeIsVolatile ty = true → t ∈ tmp →
      TrIsBitfieldAccess ce a bf →
      TrRvalof ty a [makeSet bf t a] (.Etempvar t ty) tmp

mutual
/-- `SimplExprspec.tr_expr`.  It covers every case of `transl_expr`, two
    extra cases for `Csyntax.Eparen` (to follow the reduction of
    conditionals), and cases letting `Csyntax.Eval v` match any Clight
    expression that evaluates to `v` in every environment agreeing with
    `le` on `tmp`. -/
inductive TrExpr : TempEnv → Destination → Csyntax.Expr → List Stmt → Expr → List Ident → Prop where
  | tr_var (le dst id ty tmp) :
      TrExpr le dst (.Evar id ty) (final dst (.Evar id ty)) (.Evar id ty) tmp
  | tr_deref (le dst e1 ty sl1 a1 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp →
      TrExpr le dst (.Ederef e1 ty) (sl1 ++ final dst (Ederef' a1 ty)) (Ederef' a1 ty) tmp
  | tr_field (le dst e1 f ty sl1 a1 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp →
      TrExpr le dst (.Efield e1 f ty) (sl1 ++ final dst (.Efield a1 f ty)) (.Efield a1 f ty) tmp
  | tr_val_effect (le v ty any tmp) :
      TrExpr le For_effects (.Eval v ty) [] any tmp
  | tr_val_value (le v ty a tmp) :
      typeof a = ty →
      (∀ tge e le' m, (∀ id, id ∈ tmp → le'.get id = le.get id) → EvalExpr tge e le' m a v) →
      TrExpr le For_val (.Eval v ty) [] a tmp
  | tr_val_set (le sd v ty a any tmp) :
      typeof a = ty →
      (∀ tge e le' m, (∀ id, id ∈ tmp → le'.get id = le.get id) → EvalExpr tge e le' m a v) →
      TrExpr le (For_set sd) (.Eval v ty) (doSet sd a) any tmp
  | tr_sizeof (le dst ty' ty tmp) :
      TrExpr le dst (.Esizeof ty' ty) (final dst (.Esizeof ty' ty)) (.Esizeof ty' ty) tmp
  | tr_alignof (le dst ty' ty tmp) :
      TrExpr le dst (.Ealignof ty' ty) (final dst (.Ealignof ty' ty)) (.Ealignof ty' ty) tmp
  | tr_valof (le dst e1 ty tmp sl1 a1 tmp1 sl2 a2 tmp2) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrRvalof ce (Csyntax.typeof e1) a1 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExpr le dst (.Evalof e1 ty) (sl1 ++ sl2 ++ final dst a2) a2 tmp
  | tr_addrof (le dst e1 ty tmp sl1 a1) :
      TrExpr le For_val e1 sl1 a1 tmp →
      TrExpr le dst (.Eaddrof e1 ty) (sl1 ++ final dst (Eaddrof' a1 ty)) (Eaddrof' a1 ty) tmp
  | tr_unop (le dst op e1 ty tmp sl1 a1) :
      TrExpr le For_val e1 sl1 a1 tmp →
      TrExpr le dst (.Eunop op e1 ty) (sl1 ++ final dst (.Eunop op a1 ty)) (.Eunop op a1 ty) tmp
  | tr_binop (le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_val e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExpr le dst (.Ebinop op e1 e2 ty) (sl1 ++ sl2 ++ final dst (.Ebinop op a1 a2 ty))
        (.Ebinop op a1 a2 ty) tmp
  | tr_cast_effects (le e1 ty sl1 a1 any tmp) :
      TrExpr le For_effects e1 sl1 a1 tmp →
      TrExpr le For_effects (.Ecast e1 ty) sl1 any tmp
  | tr_cast_val (le dst e1 ty sl1 a1 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp →
      TrExpr le dst (.Ecast e1 ty) (sl1 ++ final dst (.Ecast a1 ty)) (.Ecast a1 ty) tmp
  | tr_seqand_val (le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp → t ∈ tmp →
      TrExpr le For_val (.Eseqand e1 e2 ty)
        (sl1 ++ [makeif a1 (makeseq sl2) (.Sset t (.Econst_int Integers.Int.zero ty))])
        (.Etempvar t ty) tmp
  | tr_seqand_effects (le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_effects e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExpr le For_effects (.Eseqand e1 e2 ty) (sl1 ++ [makeif a1 (makeseq sl2) .Sskip]) any tmp
  | tr_seqand_set (le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp → t ∈ tmp →
      TrExpr le (For_set sd) (.Eseqand e1 e2 ty)
        (sl1 ++ [makeif a1 (makeseq sl2) (makeseq (doSet sd (.Econst_int Integers.Int.zero ty)))])
        any tmp
  | tr_seqor_val (le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp → t ∈ tmp →
      TrExpr le For_val (.Eseqor e1 e2 ty)
        (sl1 ++ [makeif a1 (.Sset t (.Econst_int Integers.Int.one ty)) (makeseq sl2)])
        (.Etempvar t ty) tmp
  | tr_seqor_effects (le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_effects e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExpr le For_effects (.Eseqor e1 e2 ty) (sl1 ++ [makeif a1 .Sskip (makeseq sl2)]) any tmp
  | tr_seqor_set (le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp → t ∈ tmp →
      TrExpr le (For_set sd) (.Eseqor e1 e2 ty)
        (sl1 ++ [makeif a1 (makeseq (doSet sd (.Econst_int Integers.Int.one ty))) (makeseq sl2)])
        any tmp
  | tr_condition_val (le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2 →
      TrExpr le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3 →
      listDisjoint tmp1 tmp2 → listDisjoint tmp1 tmp3 →
      tmp1 ⊆ tmp → tmp2 ⊆ tmp → tmp3 ⊆ tmp → t ∈ tmp →
      TrExpr le For_val (.Econdition e1 e2 e3 ty)
        (sl1 ++ [makeif a1 (makeseq sl2) (makeseq sl3)]) (.Etempvar t ty) tmp
  | tr_condition_effects (le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_effects e2 sl2 a2 tmp2 →
      TrExpr le For_effects e3 sl3 a3 tmp3 →
      listDisjoint tmp1 tmp2 → listDisjoint tmp1 tmp3 →
      tmp1 ⊆ tmp → tmp2 ⊆ tmp → tmp3 ⊆ tmp →
      TrExpr le For_effects (.Econdition e1 e2 e3 ty)
        (sl1 ++ [makeif a1 (makeseq sl2) (makeseq sl3)]) any tmp
  | tr_condition_set (le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le (For_set (SDcons ty ty t sd)) e2 sl2 a2 tmp2 →
      TrExpr le (For_set (SDcons ty ty t sd)) e3 sl3 a3 tmp3 →
      listDisjoint tmp1 tmp2 → listDisjoint tmp1 tmp3 →
      tmp1 ⊆ tmp → tmp2 ⊆ tmp → tmp3 ⊆ tmp → t ∈ tmp →
      TrExpr le (For_set sd) (.Econdition e1 e2 e3 ty)
        (sl1 ++ [makeif a1 (makeseq sl2) (makeseq sl3)]) any tmp
  | tr_assign_effects (le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_val e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrIsBitfieldAccess ce a1 bf →
      TrExpr le For_effects (.Eassign e1 e2 ty) (sl1 ++ sl2 ++ [makeAssign bf a1 a2]) any tmp
  | tr_assign_val (le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2 bf) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_val e2 sl2 a2 tmp2 →
      tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      listDisjoint tmp1 tmp2 →
      t ∈ tmp → t ∉ tmp1 → t ∉ tmp2 →
      ty1 = Csyntax.typeof e1 →
      ty2 = Csyntax.typeof e2 →
      TrIsBitfieldAccess ce a1 bf →
      TrExpr le dst (.Eassign e1 e2 ty)
        (sl1 ++ sl2 ++ .Sset t (.Ecast a2 ty1) :: makeAssign bf a1 (.Etempvar t ty1) ::
          final dst (makeAssignValue bf (.Etempvar t ty1)))
        (makeAssignValue bf (.Etempvar t ty1)) tmp
  | tr_assignop_effects (le op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf sl3 a3 tmp3 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_val e2 sl2 a2 tmp2 →
      ty1 = Csyntax.typeof e1 →
      TrRvalof ce ty1 a1 sl3 a3 tmp3 →
      listDisjoint tmp1 tmp2 → listDisjoint tmp1 tmp3 → listDisjoint tmp2 tmp3 →
      tmp1 ⊆ tmp → tmp2 ⊆ tmp → tmp3 ⊆ tmp →
      TrIsBitfieldAccess ce a1 bf →
      TrExpr le For_effects (.Eassignop op e1 e2 tyres ty)
        (sl1 ++ sl2 ++ sl3 ++ [makeAssign bf a1 (.Ebinop op a3 a2 tyres)]) any tmp
  | tr_assignop_val (le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t bf tmp ty1) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExpr le For_val e2 sl2 a2 tmp2 →
      TrRvalof ce ty1 a1 sl3 a3 tmp3 →
      listDisjoint tmp1 tmp2 → listDisjoint tmp1 tmp3 → listDisjoint tmp2 tmp3 →
      tmp1 ⊆ tmp → tmp2 ⊆ tmp → tmp3 ⊆ tmp →
      t ∈ tmp → t ∉ tmp1 → t ∉ tmp2 → t ∉ tmp3 →
      ty1 = Csyntax.typeof e1 →
      TrIsBitfieldAccess ce a1 bf →
      TrExpr le dst (.Eassignop op e1 e2 tyres ty)
        (sl1 ++ sl2 ++ sl3 ++ .Sset t (.Ecast (.Ebinop op a3 a2 tyres) ty1) ::
          makeAssign bf a1 (.Etempvar t ty1) :: final dst (makeAssignValue bf (.Etempvar t ty1)))
        (makeAssignValue bf (.Etempvar t ty1)) tmp
  | tr_postincr_effects (le id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrRvalof ce ty1 a1 sl2 a2 tmp2 →
      ty1 = Csyntax.typeof e1 →
      tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      listDisjoint tmp1 tmp2 →
      TrIsBitfieldAccess ce a1 bf →
      TrExpr le For_effects (.Epostincr id e1 ty)
        (sl1 ++ sl2 ++ [makeAssign bf a1 (translIncrdecr id a2 ty1)]) any tmp
  | tr_postincr_val (le dst id e1 ty sl1 a1 tmp1 bf t ty1 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      tmp1 ⊆ tmp → t ∈ tmp → t ∉ tmp1 →
      ty1 = Csyntax.typeof e1 →
      TrIsBitfieldAccess ce a1 bf →
      TrExpr le dst (.Epostincr id e1 ty)
        (sl1 ++ makeSet bf t a1 :: makeAssign bf a1 (translIncrdecr id (.Etempvar t ty1) ty1) ::
          final dst (.Etempvar t ty1))
        (.Etempvar t ty1) tmp
  | tr_comma (le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp) :
      TrExpr le For_effects e1 sl1 a1 tmp1 →
      TrExpr le dst e2 sl2 a2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExpr le dst (.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
  | tr_call_effects (le e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExprlist le el2 sl2 al2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExpr le For_effects (.Ecall e1 el2 ty) (sl1 ++ sl2 ++ [.Scall none a1 al2]) any tmp
  | tr_call_val (le dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp) :
      dst ≠ For_effects →
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExprlist le el2 sl2 al2 tmp2 →
      listDisjoint tmp1 tmp2 → t ∈ tmp → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExpr le dst (.Ecall e1 el2 ty)
        (sl1 ++ sl2 ++ .Scall (some t) a1 al2 :: final dst (.Etempvar t ty)) (.Etempvar t ty) tmp
  | tr_builtin_effects (le ef tyargs el ty sl al tmp1 any tmp) :
      TrExprlist le el sl al tmp1 →
      tmp1 ⊆ tmp →
      TrExpr le For_effects (.Ebuiltin ef tyargs el ty) (sl ++ [.Sbuiltin none ef tyargs al]) any tmp
  | tr_builtin_val (le dst ef tyargs el ty sl al tmp1 t tmp) :
      dst ≠ For_effects →
      TrExprlist le el sl al tmp1 →
      t ∈ tmp → tmp1 ⊆ tmp →
      TrExpr le dst (.Ebuiltin ef tyargs el ty)
        (sl ++ .Sbuiltin (some t) ef tyargs al :: final dst (.Etempvar t ty)) (.Etempvar t ty) tmp
  | tr_paren_val (le e1 tycast ty sl1 a1 t tmp) :
      TrExpr le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp →
      t ∈ tmp →
      TrExpr le For_val (.Eparen e1 tycast ty) sl1 (.Etempvar t ty) tmp
  | tr_paren_effects (le e1 tycast ty sl1 a1 tmp any) :
      TrExpr le For_effects e1 sl1 a1 tmp →
      TrExpr le For_effects (.Eparen e1 tycast ty) sl1 any tmp
  | tr_paren_set (le t sd e1 tycast ty sl1 a1 tmp any) :
      TrExpr le (For_set (SDcons tycast ty t sd)) e1 sl1 a1 tmp →
      t ∈ tmp →
      TrExpr le (For_set sd) (.Eparen e1 tycast ty) sl1 any tmp

/-- `SimplExprspec.tr_exprlist` -/
inductive TrExprlist : TempEnv → Csyntax.ExprList → List Stmt → List Expr → List Ident → Prop where
  | tr_nil (le tmp) : TrExprlist le .Enil [] [] tmp
  | tr_cons (le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp) :
      TrExpr le For_val e1 sl1 a1 tmp1 →
      TrExprlist le el2 sl2 al2 tmp2 →
      listDisjoint tmp1 tmp2 → tmp1 ⊆ tmp → tmp2 ⊆ tmp →
      TrExprlist le (.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp
end

/-! ### Invariance properties -/

theorem tr_rvalof_monotone {ty a sl b tmps} (h : TrRvalof ce ty a sl b tmps) {tmps'}
    (hi : tmps ⊆ tmps') : TrRvalof ce ty a sl b tmps' := by
  match h with
  | .tr_rvalof_nonvol _ _ _ hv => exact .tr_rvalof_nonvol _ _ _ hv
  | .tr_rvalof_vol _ _ _ _ _ hv hin hbf => exact .tr_rvalof_vol _ _ _ _ _ hv (hi hin) hbf

mutual
/-- `SimplExprspec.tr_expr_invariant` -/
theorem tr_expr_invariant {le dst r sl a tmps} (h : TrExpr ce le dst r sl a tmps) {le' : TempEnv}
    (hle : ∀ x, x ∈ tmps → le'.get x = le.get x) : TrExpr ce le' dst r sl a tmps := by
  match h with
  | .tr_var .. => exact .tr_var ..
  | .tr_deref _ _ _ _ _ _ _ h1 => exact .tr_deref _ _ _ _ _ _ _ (tr_expr_invariant h1 hle)
  | .tr_field _ _ _ _ _ _ _ _ h1 => exact .tr_field _ _ _ _ _ _ _ _ (tr_expr_invariant h1 hle)
  | .tr_val_effect .. => exact .tr_val_effect ..
  | .tr_val_value _ _ _ _ _ hty hev =>
    exact .tr_val_value _ _ _ _ _ hty fun tge e le'' m h =>
      hev tge e le'' m fun id hid => (h id hid).trans (hle id hid)
  | .tr_val_set _ _ _ _ _ _ _ hty hev =>
    exact .tr_val_set _ _ _ _ _ _ _ hty fun tge e le'' m h =>
      hev tge e le'' m fun id hid => (h id hid).trans (hle id hid)
  | .tr_sizeof .. => exact .tr_sizeof ..
  | .tr_alignof .. => exact .tr_alignof ..
  | .tr_valof _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_valof _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx)) h2 h3 h4 h5
  | .tr_addrof _ _ _ _ _ _ _ h1 => exact .tr_addrof _ _ _ _ _ _ _ (tr_expr_invariant h1 hle)
  | .tr_unop _ _ _ _ _ _ _ _ h1 => exact .tr_unop _ _ _ _ _ _ _ _ (tr_expr_invariant h1 hle)
  | .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_expr_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5
  | .tr_cast_effects _ _ _ _ _ _ _ h1 => exact .tr_cast_effects _ _ _ _ _ _ _ (tr_expr_invariant h1 hle)
  | .tr_cast_val _ _ _ _ _ _ _ h1 => exact .tr_cast_val _ _ _ _ _ _ _ (tr_expr_invariant h1 hle)
  | .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_expr_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5 h6
  | .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_expr_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5
  | .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_expr_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5 h6
  | .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_expr_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5 h6
  | .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_expr_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5
  | .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_expr_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5 h6
  | .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h6 hx)) (tr_expr_invariant h2 fun x hx => hle x (h7 hx))
      (tr_expr_invariant h3 fun x hx => hle x (h8 hx)) h4 h5 h6 h7 h8 h9
  | .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h6 hx)) (tr_expr_invariant h2 fun x hx => hle x (h7 hx))
      (tr_expr_invariant h3 fun x hx => hle x (h8 hx)) h4 h5 h6 h7 h8
  | .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h6 hx)) (tr_expr_invariant h2 fun x hx => hle x (h7 hx))
      (tr_expr_invariant h3 fun x hx => hle x (h8 hx)) h4 h5 h6 h7 h8 h9
  | .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h4 hx)) (tr_expr_invariant h2 fun x hx => hle x (h5 hx))
      h3 h4 h5 h6
  | .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h3 hx)) (tr_expr_invariant h2 fun x hx => hle x (h4 hx))
      h3 h4 h5 h6 h7 h8 h9 h10 h11
  | .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h8 hx)) (tr_expr_invariant h2 fun x hx => hle x (h9 hx))
      h3 h4 h5 h6 h7 h8 h9 h10 h11
  | .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
    exact .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h7 hx)) (tr_expr_invariant h2 fun x hx => hle x (h8 hx))
      h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  | .tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
    exact .tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h4 hx)) h2 h3 h4 h5 h6 h7
  | .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h2 hx)) h2 h3 h4 h5 h6
  | .tr_comma _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_comma _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h4 hx)) (tr_expr_invariant h2 fun x hx => hle x (h5 hx))
      h3 h4 h5
  | .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_invariant h1 fun x hx => hle x (h4 hx)) (tr_exprlist_invariant h2 fun x hx => hle x (h5 hx))
      h3 h4 h5
  | .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0
      (tr_expr_invariant h1 fun x hx => hle x (h5 hx)) (tr_exprlist_invariant h2 fun x hx => hle x (h6 hx))
      h3 h4 h5 h6
  | .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ (tr_exprlist_invariant h1 fun x hx => hle x (h2 hx)) h2
  | .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
    exact .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0
      (tr_exprlist_invariant h1 fun x hx => hle x (h3 hx)) h2 h3
  | .tr_paren_val _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_paren_val _ _ _ _ _ _ _ _ (tr_expr_invariant h1 hle) h2
  | .tr_paren_effects _ _ _ _ _ _ _ _ h1 =>
    exact .tr_paren_effects _ _ _ _ _ _ _ _ (tr_expr_invariant h1 hle)
  | .tr_paren_set _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_paren_set _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 hle) h2

/-- `SimplExprspec.tr_exprlist_invariant` -/
theorem tr_exprlist_invariant {le rl sl al tmps} (h : TrExprlist ce le rl sl al tmps)
    {le' : TempEnv} (hle : ∀ x, x ∈ tmps → le'.get x = le.get x) :
    TrExprlist ce le' rl sl al tmps := by
  match h with
  | .tr_nil .. => exact .tr_nil ..
  | .tr_cons _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_cons _ _ _ _ _ _ _ _ _ _ (tr_expr_invariant h1 fun x hx => hle x (h4 hx))
      (tr_exprlist_invariant h2 fun x hx => hle x (h5 hx)) h3 h4 h5
end

/-- `SimplExprspec.tr_expr_monotone` -/
theorem tr_expr_monotone {le dst r sl a tmps} (h : TrExpr ce le dst r sl a tmps) {tmps'}
    (hi : tmps ⊆ tmps') : TrExpr ce le dst r sl a tmps' := by
  have T {l1 : List Ident} (h : l1 ⊆ tmps) : l1 ⊆ tmps' := fun _ hx => hi (h hx)
  match h with
  | .tr_var .. => exact .tr_var ..
  | .tr_deref _ _ _ _ _ _ _ h1 => exact .tr_deref _ _ _ _ _ _ _ (tr_expr_monotone h1 hi)
  | .tr_field _ _ _ _ _ _ _ _ h1 => exact .tr_field _ _ _ _ _ _ _ _ (tr_expr_monotone h1 hi)
  | .tr_val_effect .. => exact .tr_val_effect ..
  | .tr_val_value _ _ _ _ _ hty hev =>
    exact .tr_val_value _ _ _ _ _ hty fun tge e le'' m h =>
      hev tge e le'' m fun id hid => h id (hi hid)
  | .tr_val_set _ _ _ _ _ _ _ hty hev =>
    exact .tr_val_set _ _ _ _ _ _ _ hty fun tge e le'' m h =>
      hev tge e le'' m fun id hid => h id (hi hid)
  | .tr_sizeof .. => exact .tr_sizeof ..
  | .tr_alignof .. => exact .tr_alignof ..
  | .tr_valof _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_valof _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5)
  | .tr_addrof _ _ _ _ _ _ _ h1 => exact .tr_addrof _ _ _ _ _ _ _ (tr_expr_monotone h1 hi)
  | .tr_unop _ _ _ _ _ _ _ _ h1 => exact .tr_unop _ _ _ _ _ _ _ _ (tr_expr_monotone h1 hi)
  | .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5)
  | .tr_cast_effects _ _ _ _ _ _ _ h1 => exact .tr_cast_effects _ _ _ _ _ _ _ (tr_expr_monotone h1 hi)
  | .tr_cast_val _ _ _ _ _ _ _ h1 => exact .tr_cast_val _ _ _ _ _ _ _ (tr_expr_monotone h1 hi)
  | .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5) (hi h6)
  | .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5)
  | .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5) (hi h6)
  | .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5) (hi h6)
  | .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5)
  | .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5) (hi h6)
  | .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (T h6) (T h7) (T h8) (hi h9)
  | .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (T h6) (T h7) (T h8)
  | .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (T h6) (T h7) (T h8) (hi h9)
  | .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5) h6
  | .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 (T h3) (T h4) h5 (hi h6) h7 h8 h9 h10 h11
  | .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7
      (T h8) (T h9) (T h10) h11
  | .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
    exact .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6
      (T h7) (T h8) (T h9) (hi h10) h11 h12 h13 h14 h15
  | .tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
    exact .tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5) h6 h7
  | .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ h1 (T h2) (hi h3) h4 h5 h6
  | .tr_comma _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_comma _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5)
  | .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (T h4) (T h5)
  | .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 (hi h4) (T h5) (T h6)
  | .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ h1 (T h2)
  | .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
    exact .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0 h1 (hi h2) (T h3)
  | .tr_paren_val _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_paren_val _ _ _ _ _ _ _ _ (tr_expr_monotone h1 hi) (hi h2)
  | .tr_paren_effects _ _ _ _ _ _ _ _ h1 =>
    exact .tr_paren_effects _ _ _ _ _ _ _ _ (tr_expr_monotone h1 hi)
  | .tr_paren_set _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_paren_set _ _ _ _ _ _ _ _ _ _ (tr_expr_monotone h1 hi) (hi h2)

/-- `SimplExprspec.tr_exprlist_monotone` -/
theorem tr_exprlist_monotone {le rl sl al tmps} (h : TrExprlist ce le rl sl al tmps) {tmps'}
    (hi : tmps ⊆ tmps') : TrExprlist ce le rl sl al tmps' := by
  match h with
  | .tr_nil .. => exact .tr_nil ..
  | .tr_cons _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_cons _ _ _ _ _ _ _ _ _ _ h1 h2 h3 (fun _ hx => hi (h4 hx)) (fun _ hx => hi (h5 hx))

/-! ## Top-level translation

`TrTop` is `TrExpr` plus one extra case: at top level a `Csyntax.Eval v`
can be matched by a Clight expression whose value depends on the current
memory state. -/

/-- `SimplExprspec.tr_top` -/
inductive TrTop (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    Destination → Csyntax.Expr → List Stmt → Expr → List Ident → Prop where
  | tr_top_val_val (v ty a tmp) :
      typeof a = ty → EvalExpr ge e le m a v →
      TrTop ge e le m For_val (.Eval v ty) [] a tmp
  | tr_top_base (dst r sl a tmp) :
      TrExpr ce le dst r sl a tmp →
      TrTop ge e le m dst r sl a tmp

/-! ## Translation of statements -/

/-- `SimplExprspec.tr_expression` -/
inductive TrExpression : Csyntax.Expr → Stmt → Expr → Prop where
  | tr_expression_intro (r sl a tmps) :
      (∀ ge e le m, TrTop ce ge e le m For_val r sl a tmps) →
      TrExpression r (makeseq sl) a

/-- `SimplExprspec.tr_expr_stmt` -/
inductive TrExprStmt : Csyntax.Expr → Stmt → Prop where
  | tr_expr_stmt_intro (r sl a tmps) :
      (∀ ge e le m, TrTop ce ge e le m For_effects r sl a tmps) →
      TrExprStmt r (makeseq sl)

/-- `SimplExprspec.tr_if` -/
inductive TrIf : Csyntax.Expr → Stmt → Stmt → Stmt → Prop where
  | tr_if_intro (r s1 s2 sl a tmps) :
      (∀ ge e le m, TrTop ce ge e le m For_val r sl a tmps) →
      TrIf r s1 s2 (makeseq (sl ++ [makeif a s1 s2]))

mutual
/-- `SimplExprspec.tr_stmt` -/
inductive TrStmt : Csyntax.Stmt → Stmt → Prop where
  | tr_skip : TrStmt .Sskip .Sskip
  | tr_do (r s) : TrExprStmt ce r s → TrStmt (.Sdo r) s
  | tr_seq (s1 s2 ts1 ts2) :
      TrStmt s1 ts1 → TrStmt s2 ts2 → TrStmt (.Ssequence s1 s2) (.Ssequence ts1 ts2)
  | tr_ifthenelse_empty (r s' a) :
      TrExpression ce r s' a →
      TrStmt (.Sifthenelse r .Sskip .Sskip) (.Ssequence s' .Sskip)
  | tr_ifthenelse (r s1 s2 s' a ts1 ts2) :
      TrExpression ce r s' a → TrStmt s1 ts1 → TrStmt s2 ts2 →
      TrStmt (.Sifthenelse r s1 s2) (.Ssequence s' (.Sifthenelse a ts1 ts2))
  | tr_while (r s1 s' ts1) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt s1 ts1 →
      TrStmt (.Swhile r s1) (.Sloop (.Ssequence s' ts1) .Sskip)
  | tr_dowhile (r s1 s' ts1) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt s1 ts1 →
      TrStmt (.Sdowhile r s1) (.Sloop ts1 s')
  | tr_for_1 (r s3 s4 s' ts3 ts4) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt s3 ts3 → TrStmt s4 ts4 →
      TrStmt (.Sfor .Sskip r s3 s4) (.Sloop (.Ssequence s' ts4) ts3)
  | tr_for_2 (s1 r s3 s4 s' ts1 ts3 ts4) :
      TrIf ce r .Sskip .Sbreak s' → s1 ≠ .Sskip →
      TrStmt s1 ts1 → TrStmt s3 ts3 → TrStmt s4 ts4 →
      TrStmt (.Sfor s1 r s3 s4) (.Ssequence ts1 (.Sloop (.Ssequence s' ts4) ts3))
  | tr_break : TrStmt .Sbreak .Sbreak
  | tr_continue : TrStmt .Scontinue .Scontinue
  | tr_return_none : TrStmt (.Sreturn none) (.Sreturn none)
  | tr_return_some (r s' a) :
      TrExpression ce r s' a →
      TrStmt (.Sreturn (some r)) (.Ssequence s' (.Sreturn (some a)))
  | tr_switch (r ls s' a tls) :
      TrExpression ce r s' a → TrLblstmts ls tls →
      TrStmt (.Sswitch r ls) (.Ssequence s' (.Sswitch a tls))
  | tr_label (lbl s ts) : TrStmt s ts → TrStmt (.Slabel lbl s) (.Slabel lbl ts)
  | tr_goto (lbl) : TrStmt (.Sgoto lbl) (.Sgoto lbl)

/-- `SimplExprspec.tr_lblstmts` -/
inductive TrLblstmts : Csyntax.LStmts → LStmts → Prop where
  | tr_ls_nil : TrLblstmts .LSnil .LSnil
  | tr_ls_cons (c s ls ts tls) :
      TrStmt s ts → TrLblstmts ls tls → TrLblstmts (.LScons c s ls) (.LScons c ts tls)
end

/-- `SimplExprspec.tr_function` -/
inductive TrFunction : Csyntax.Function → Function → Prop where
  | tr_function_intro (f tf) :
      TrStmt ce f.fn_body tf.fn_body →
      tf.fn_return = f.fn_return →
      tf.fn_callconv = f.fn_callconv →
      tf.fn_params = f.fn_params →
      tf.fn_vars = f.fn_vars →
      TrFunction f tf

end SPEC

/-- `SimplExprspec.tr_fundef` -/
inductive TrFundef (p : Csyntax.Program) : Csyntax.FunDef → FunDef → Prop where
  | tr_internal (f tf) : TrFunction p.prog_comp_env f tf → TrFundef p (.Internal f) (.Internal tf)
  | tr_external (ef targs tres cconv) :
      TrFundef p (.External ef targs tres cconv) (.External ef targs tres cconv)

end SimplExpr
end CC
