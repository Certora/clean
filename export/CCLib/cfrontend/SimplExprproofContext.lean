/-
  Expression simplification: semantic preservation — port of
  `cfrontend/SimplExprproof.v`, part 2: commutation between the translation
  of expressions and left reduction contexts (`typeof_context`,
  `tr_expr_leftcontext_rec`, `tr_expr_leftcontext`, `tr_top_leftcontext`).

  Differences from Rocq:
  * the five-fold existential conclusion of `tr_expr_leftcontext_rec` is
    packaged as `LCRes`, and the step shared by every case (re-associating
    the statement lists and widening the set of temporaries) is the lemma
    `lc_compose`;
  * the mutual induction on `leftcontext`/`leftcontextlist` is a mutual
    structural recursion.
-/
import CCLib.cfrontend.SimplExprproofEnv

namespace CC
namespace SimplExpr

open Destination SetDestination Cstrategy

/-- `SimplExprproof.typeof_context` -/
theorem typeof_context {k1 k2 C} (h : LeftContext k1 k2 C) {e1 e2 : Csyntax.Expr}
    (heq : Csyntax.typeof e1 = Csyntax.typeof e2) :
    Csyntax.typeof (C e1) = Csyntax.typeof (C e2) := by
  cases h <;> first | exact heq | rfl

section TRANSLATION
variable (ce : CompositeEnv)

/-- The conclusion of `SimplExprproof.tr_expr_leftcontext_rec`: the
    translation of `C e` decomposes into a translation of `e` (statements
    `sl1`, temporaries `tmp'`) followed by statements `sl2`, and `e` can be
    replaced by any `e'` translated in the same way, giving `P le' e' (sl3 ++
    sl2)`. -/
def LCRes (le : TempEnv) (e : Csyntax.Expr) (sl : List Stmt) (tmps : List Ident)
    (P : TempEnv → Csyntax.Expr → List Stmt → Prop) : Prop :=
  ∃ dst' sl1 sl2 a' tmp', TrExpr ce le dst' e sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧ tmp' ⊆ tmps ∧
    ∀ le' e' sl3, TrExpr ce le' dst' e' sl3 a' tmp' →
      (∀ id, id ∉ tmp' → le'.get id = le.get id) →
      Csyntax.typeof e' = Csyntax.typeof e → P le' e' (sl3 ++ sl2)

variable {ce}

theorem lc_compose {le e sl0 tmp0 P} (h : LCRes ce le e sl0 tmp0 P) {sl rest tmps}
    {Q : TempEnv → Csyntax.Expr → List Stmt → Prop}
    (hsl : sl = sl0 ++ rest) (hinc : tmp0 ⊆ tmps)
    (hQ : ∀ le' e' sl' tmp', tmp' ⊆ tmp0 → P le' e' sl' →
      (∀ id, id ∉ tmp' → le'.get id = le.get id) →
      Csyntax.typeof e' = Csyntax.typeof e → Q le' e' (sl' ++ rest)) :
    LCRes ce le e sl tmps Q := by
  obtain ⟨dst', sl1, sl2, a', tmp', h1, h2, h3, h4⟩ := h
  refine ⟨dst', sl1, sl2 ++ rest, a', tmp', h1, by rw [hsl, h2, List.append_assoc],
    fun _ hx => hinc (h3 hx), fun le' e' sl3 ht hle hty => ?_⟩
  rw [← List.append_assoc]
  exact hQ le' e' (sl3 ++ sl2) tmp' h3 (h4 le' e' sl3 ht hle hty) hle hty

/-- `UNCHANGED` for a subexpression to the right of the context. -/
theorem unchanged_right {le le' : TempEnv} {tmp' tmp1 tmp2 : List Ident}
    (hle : ∀ id, id ∉ tmp' → le'.get id = le.get id) (hsub : tmp' ⊆ tmp1)
    (hd : listDisjoint tmp1 tmp2) : ∀ x, x ∈ tmp2 → le'.get x = le.get x :=
  fun x hx => hle x fun hx' => hd x (hsub hx') hx

/-- `UNCHANGED` for a subexpression to the left of the context. -/
theorem unchanged_left {le le' : TempEnv} {tmp' tmp1 tmp2 : List Ident}
    (hle : ∀ id, id ∉ tmp' → le'.get id = le.get id) (hsub : tmp' ⊆ tmp2)
    (hd : listDisjoint tmp1 tmp2) : ∀ x, x ∈ tmp1 → le'.get x = le.get x :=
  fun x hx => hle x fun hx' => hd x hx (hsub hx')

theorem TrExpr.sl_congr {le dst r sl sl' a tmps} (h : sl' = sl)
    (ht : TrExpr ce le dst r sl' a tmps) : TrExpr ce le dst r sl a tmps := h ▸ ht

theorem TrExprlist.sl_congr {le rl sl sl' al tmps} (h : sl' = sl)
    (ht : TrExprlist ce le rl sl' al tmps) : TrExprlist ce le rl sl al tmps := h ▸ ht

theorem lc_top {le e dst sl a tmps} (h : TrExpr ce le dst e sl a tmps) :
    LCRes ce le e sl tmps (fun le' e' sl' => TrExpr ce le' dst e' sl' a tmps) :=
  ⟨dst, sl, [], a, tmps, h, by rw [List.append_nil], fun _ hx => hx,
    fun _ _ _ h' _ _ => by rw [List.append_nil]; exact h'⟩

mutual
/-- `SimplExprproof.tr_expr_leftcontext_rec` (contexts) -/
theorem tr_expr_leftcontext_rec {k1} : ∀ {k2 C}, LeftContext k1 k2 C →
    ∀ {le e dst sl a tmps}, TrExpr ce le dst (C e) sl a tmps →
      LCRes ce le e sl tmps (fun le' e' sl' => TrExpr ce le' dst (C e') sl' a tmps)
  | _, _, .top _, _, _, _, _, _, _, htr => lc_top htr
  | _, _, .deref _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_deref _ _ _ _ _ _ _ h1 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => .tr_deref _ _ _ _ _ _ _ hP
  | _, _, .field _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_field _ _ _ _ _ _ _ _ h1 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => .tr_field _ _ _ _ _ _ _ _ hP
  | _, _, .rvalof _ C _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_valof _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      refine lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_assoc _ _ _) h4
        fun le' e' _ _ _ hP _ hty => ?_
      have h2' := h2
      rw [← typeof_context hC hty] at h2'
      exact TrExpr.sl_congr (by simp only [List.append_assoc])
        (.tr_valof _ _ _ _ _ _ _ _ _ _ _ hP h2' h3 h4 h5)
  | _, _, .addrof _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_addrof _ _ _ _ _ _ _ h1 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => .tr_addrof _ _ _ _ _ _ _ hP
  | _, _, .unop _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_unop _ _ _ _ _ _ _ _ h1 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => .tr_unop _ _ _ _ _ _ _ _ hP
  | _, _, .binop_left _ _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_assoc _ _ _) h4
        fun _ _ _ _ hsub hP hle _ => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5)
  | _, _, .binop_right _ _ _ _ _ hs hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_expr_leftcontext_rec hC h2) rfl h5
        fun _ _ _ _ hsub hP hle _ => .tr_binop _ _ _ _ _ _ [] _ _ _ _ _ _
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h3)) hP h3 h4 h5
  | _, _, .cast _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_cast_effects _ _ _ _ _ _ _ h1 =>
      refine lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_nil _).symm (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => ?_
      rw [List.append_nil]; exact .tr_cast_effects _ _ _ _ _ _ _ hP
    | .tr_cast_val _ _ _ _ _ _ _ h1 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => .tr_cast_val _ _ _ _ _ _ _ hP
  | _, _, .seqand _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5 h6
    | .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5
    | .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5 h6
  | _, _, .seqor _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5 h6
    | .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5
    | .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5 h6
  | _, _, .condition _ _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h6
        fun _ _ _ _ hsub hP hle _ => .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h4))
          (tr_expr_invariant ce h3 (unchanged_right hle hsub h5)) h4 h5 h6 h7 h8 h9
    | .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h6
        fun _ _ _ _ hsub hP hle _ => .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h4))
          (tr_expr_invariant ce h3 (unchanged_right hle hsub h5)) h4 h5 h6 h7 h8
    | .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h6
        fun _ _ _ _ hsub hP hle _ => .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h4))
          (tr_expr_invariant ce h3 (unchanged_right hle hsub h5)) h4 h5 h6 h7 h8 h9
  | _, _, .assign_left _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_assoc _ _ _) h4
        fun _ _ _ _ hsub hP hle _ => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5 h6)
    | .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_assoc _ _ _) h3
        fun _ _ _ _ hsub hP hle hty => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h5)) h3 h4 h5 h6 h7 h8
          (h9.trans (typeof_context hC hty).symm) h10 h11)
  | _, _, .assign_right _ _ _ _ hs hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_expr_leftcontext_rec hC h2) rfl h5
        fun _ _ _ _ hsub hP hle _ => .tr_assign_effects _ _ _ _ [] _ _ _ _ _ _ _ _
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h3)) hP h3 h4 h5 h6
    | .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_expr_leftcontext_rec hC h2) rfl h4
        fun _ _ _ _ hsub hP hle hty => .tr_assign_val _ _ _ _ _ [] _ _ _ _ _ _ _ _ _ _
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h5)) hP h3 h4 h5 h6 h7 h8 h9
          (h10.trans (typeof_context hC hty).symm) h11
  | _, _, .assignop_left _ _ _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1)
        ((List.append_assoc _ _ _).trans (List.append_assoc _ _ _)) h8
        fun _ _ _ _ hsub hP hle hty => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          hP (tr_expr_invariant ce h2 (unchanged_right hle hsub h5))
          (h3.trans (typeof_context hC hty).symm) h4 h5 h6 h7 h8 h9 h10 h11)
    | .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1)
        ((List.append_assoc _ _ _).trans (List.append_assoc _ _ _)) h7
        fun _ _ _ _ hsub hP hle hty => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          hP (tr_expr_invariant ce h2 (unchanged_right hle hsub h4)) h3 h4 h5 h6 h7 h8 h9 h10
          h11 h12 h13 (h14.trans (typeof_context hC hty).symm) h15)
  | _, _, .assignop_right _ _ _ _ _ _ hs hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_expr_leftcontext_rec hC h2) (List.append_assoc _ _ _) h9
        fun _ _ _ _ hsub hP hle _ => TrExpr.sl_congr (by simp only [List.append_assoc, List.nil_append]) (.tr_assignop_effects _ _ _ _ _ _ _ [] _ _ _ _ _ _ _ _ _ _ _
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h5)) hP h3 h4 h5 h6 h7 h8 h9 h10 h11)
    | .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_expr_leftcontext_rec hC h2) (List.append_assoc _ _ _) h8
        fun _ _ _ _ hsub hP hle _ => TrExpr.sl_congr (by simp only [List.append_assoc, List.nil_append]) (.tr_assignop_val _ _ _ _ _ _ _ [] _ _ _ _ _ _ _ _ _ _ _ _
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h4)) hP h3 h4 h5 h6 h7 h8 h9 h10
          h11 h12 h13 h14 h15)
  | _, _, .postincr _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_assoc _ _ _) h4
        fun _ _ _ _ _ hP _ hty => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP h2
          (h3.trans (typeof_context hC hty).symm) h4 h5 h6 h7)
    | .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h2
        fun _ _ _ _ _ hP _ hty => .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ hP h2 h3 h4
          (h5.trans (typeof_context hC hty).symm) h6
  | _, _, .call_left _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_assoc _ _ _) h4
        fun _ _ _ _ hsub hP hle _ => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_exprlist_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5)
    | .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_assoc _ _ _) h5
        fun _ _ _ _ hsub hP hle _ => TrExpr.sl_congr (by simp only [List.append_assoc]) (.tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0 hP
          (tr_exprlist_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5 h6)
  | _, _, .call_right _ _ _ _ hs hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_exprlist_leftcontext_rec hC h2) rfl h5
        fun _ _ _ _ hsub hP hle _ => .tr_call_effects _ _ _ _ [] _ _ _ _ _ _ _
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h3)) hP h3 h4 h5
    | .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_exprlist_leftcontext_rec hC h2) rfl h6
        fun _ _ _ _ hsub hP hle _ => .tr_call_val _ _ _ _ _ [] _ _ _ _ _ _ _ h0
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h3)) hP h3 h4 h5 h6
  | _, _, .builtin _ _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ h1 h2 =>
      exact lc_compose (tr_exprlist_leftcontext_rec hC h1) rfl h2
        fun _ _ _ _ _ hP _ _ => .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ hP h2
    | .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
      exact lc_compose (tr_exprlist_leftcontext_rec hC h1) rfl h3
        fun _ _ _ _ _ hP _ _ => .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0 hP h2 h3
  | _, _, .comma _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_comma _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_comma _ _ _ _ _ _ _ _ _ _ _ _ hP
          (tr_expr_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5
  | _, _, .paren _ _ _ _ hC, _, _, _, _, _, _, htr => by
    match htr with
    | .tr_paren_val _ _ _ _ _ _ _ _ h1 h2 =>
      refine lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_nil _).symm (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => ?_
      rw [List.append_nil]; exact .tr_paren_val _ _ _ _ _ _ _ _ hP h2
    | .tr_paren_effects _ _ _ _ _ _ _ _ h1 =>
      refine lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_nil _).symm (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => ?_
      rw [List.append_nil]; exact .tr_paren_effects _ _ _ _ _ _ _ _ hP
    | .tr_paren_set _ _ _ _ _ _ _ _ _ _ h1 h2 =>
      refine lc_compose (tr_expr_leftcontext_rec hC h1) (List.append_nil _).symm (fun _ h => h)
        fun _ _ _ _ _ hP _ _ => ?_
      rw [List.append_nil]; exact .tr_paren_set _ _ _ _ _ _ _ _ _ _ hP h2

/-- `SimplExprproof.tr_expr_leftcontext_rec` (context lists) -/
theorem tr_exprlist_leftcontext_rec {k} : ∀ {C}, LeftContextList k C →
    ∀ {le e sl al tmps}, TrExprlist ce le (C e) sl al tmps →
      LCRes ce le e sl tmps (fun le' e' sl' => TrExprlist ce le' (C e') sl' al tmps)
  | _, .head _ _ _ hC, _, _, _, _, _, htr => by
    match htr with
    | .tr_cons _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      exact lc_compose (tr_expr_leftcontext_rec hC h1) rfl h4
        fun _ _ _ _ hsub hP hle _ => .tr_cons _ _ _ _ _ _ _ _ _ _ hP
          (tr_exprlist_invariant ce h2 (unchanged_right hle hsub h3)) h3 h4 h5
  | _, .tail _ _ _ hs hC, _, _, _, _, _, htr => by
    match htr with
    | .tr_cons _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
      have := tr_simple_expr_nil ce h1 (.inl rfl) hs
      subst this
      exact lc_compose (tr_exprlist_leftcontext_rec hC h2) (List.append_nil _).symm h5
        fun _ _ _ _ hsub hP hle _ => TrExprlist.sl_congr (by simp) (.tr_cons _ _ _ [] _ _ _ _ _ _
          (tr_expr_invariant ce h1 (unchanged_left hle hsub h3)) hP h3 h4 h5)
end

/-- `SimplExprproof.tr_expr_leftcontext` -/
theorem tr_expr_leftcontext {C le r dst sl a tmps} (hC : LeftContext .RV .RV C)
    (htr : TrExpr ce le dst (C r) sl a tmps) :
    ∃ dst' sl1 sl2 a' tmp', TrExpr ce le dst' r sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧ tmp' ⊆ tmps ∧
      ∀ le' r' sl3, TrExpr ce le' dst' r' sl3 a' tmp' →
        (∀ id, id ∉ tmp' → le'.get id = le.get id) →
        Csyntax.typeof r' = Csyntax.typeof r → TrExpr ce le' dst (C r') (sl3 ++ sl2) a tmps :=
  tr_expr_leftcontext_rec hC htr

/-- `SimplExprproof.tr_top_leftcontext` -/
theorem tr_top_leftcontext {tge : CGenv} {e le m dst rtop sl a tmps}
    (htr : TrTop ce tge e le m dst rtop sl a tmps) {r C} (hr : rtop = C r)
    (hC : LeftContext .RV .RV C) :
    ∃ dst' sl1 sl2 a' tmp', TrTop ce tge e le m dst' r sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
      tmp' ⊆ tmps ∧
      ∀ le' m' r' sl3, TrExpr ce le' dst' r' sl3 a' tmp' →
        (∀ id, id ∉ tmp' → le'.get id = le.get id) →
        Csyntax.typeof r' = Csyntax.typeof r →
        TrTop ce tge e le' m' dst (C r') (sl3 ++ sl2) a tmps := by
  cases htr with
  | tr_top_val_val v ty a tmp hty hev =>
    cases hC <;> try (cases hr; done)
    subst hr
    refine ⟨.For_val, [], [], a, tmps, .tr_top_val_val _ _ _ _ hty hev, rfl, fun _ h => h,
      fun le' m' r' sl3 h _ _ => ?_⟩
    rw [List.append_nil]; exact .tr_top_base _ _ _ _ _ h
  | tr_top_base dst r0 sl a tmp h =>
    subst hr
    obtain ⟨dst', sl1, sl2, a', tmp', h1, h2, h3, h4⟩ := tr_expr_leftcontext hC h
    exact ⟨dst', sl1, sl2, a', tmp', .tr_top_base _ _ _ _ _ h1, h2, h3,
      fun le' m' r' sl3 h5 h6 h7 => .tr_top_base _ _ _ _ _ (h4 le' r' sl3 h5 h6 h7)⟩

end TRANSLATION

end SimplExpr
end CC
