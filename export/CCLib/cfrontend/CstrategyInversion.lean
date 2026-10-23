/-
  `cfrontend/Cstrategy.v`, section `INVERSION_LEMMAS`: what a safe CompCert C
  expression state says about the redex at any reduction context.

  `invert_expr_prop a m` is the condition under which the head of `a` can
  reduce (for instance, `*(Eval v)` needs `v` to be a pointer, and `l = r` with
  `l`, `r` evaluated needs the cast and the store to succeed).  The lemmas
  `lred_invert`, `rred_invert` and `callred_invert` show that every head redex
  satisfies it, `invert_expr_context` that it propagates through contexts, and
  `imm_safe_inv`/`safe_inv` that every immediately safe (resp. safe) non-value
  expression satisfies it.

  Also `simple_can_eval` (and its `_rval`/`_lval` forms): in a safe state, a
  simple expression at a reduction context can be evaluated in one big step.
-/
import CCLib.cfrontend.Cstrategy

namespace CC
namespace Cstrategy

section INVERSION_LEMMAS

variable (ge : Csem.CGenv) (e : Env)

/-- `Cstrategy.exprlist_all_values` -/
def exprlistAllValues : Csyntax.ExprList → Prop
  | .Enil => True
  | .Econs (.Eval _ _) rl' => exprlistAllValues rl'
  | .Econs _ _ => False

/-- `Cstrategy.invert_expr_prop` -/
def invertExprProp (a : Csyntax.Expr) (m : Mem) : Prop :=
  match a with
  | .Eloc _ _ _ _ => False
  | .Evar x ty =>
      ∃ b, e.get x = some (b, ty) ∨ (e.get x = none ∧ Genv.findSymbol ge.genv_genv x = some b)
  | .Ederef (.Eval v _) _ => ∃ b ofs, v = .Vptr b ofs
  | .Eaddrof (.Eloc _ _ bf _) _ => bf = .Full
  | .Efield (.Eval v ty1) f _ =>
      ∃ b ofs, v = .Vptr b ofs ∧
      match ty1 with
      | .Tstruct id _ => ∃ co delta bf, ge.genv_cenv.get id = some co ∧
          fieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf)
      | .Tunion id _ => ∃ co delta bf, ge.genv_cenv.get id = some co ∧
          unionFieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf)
      | _ => False
  | .Eval _ _ => False
  | .Evalof (.Eloc b ofs bf ty') ty =>
      ty' = ty ∧ ∃ t v, Csem.DerefLoc ge ty m b ofs bf t v
  | .Eunop op (.Eval v1 ty1) _ => ∃ v, Cop.semUnaryOperation op v1 ty1 m = some v
  | .Ebinop op (.Eval v1 ty1) (.Eval v2 ty2) _ =>
      ∃ v, Cop.semBinaryOperation ge.genv_cenv op v1 ty1 v2 ty2 m = some v
  | .Ecast (.Eval v1 ty1) ty => ∃ v, Cop.semCast v1 ty1 ty m = some v
  | .Eseqand (.Eval v1 ty1) _ _ => ∃ b, Cop.boolVal v1 ty1 m = some b
  | .Eseqor (.Eval v1 ty1) _ _ => ∃ b, Cop.boolVal v1 ty1 m = some b
  | .Econdition (.Eval v1 ty1) _ _ _ => ∃ b, Cop.boolVal v1 ty1 m = some b
  | .Eassign (.Eloc b ofs bf ty1) (.Eval v2 ty2) ty =>
      ∃ v m' v' t, ty = ty1 ∧ Cop.semCast v2 ty2 ty1 m = some v ∧
        Csem.AssignLoc ge ty1 m b ofs bf v t m' v'
  | .Eassignop _ (.Eloc b ofs bf ty1) (.Eval _ _) _ ty =>
      ∃ t v1, ty = ty1 ∧ Csem.DerefLoc ge ty1 m b ofs bf t v1
  | .Epostincr _ (.Eloc b ofs bf ty1) ty =>
      ∃ t v1, ty = ty1 ∧ Csem.DerefLoc ge ty m b ofs bf t v1
  | .Ecomma (.Eval _ _) r2 ty => Csyntax.typeof r2 = ty
  | .Eparen (.Eval v1 ty1) ty2 _ => ∃ v, Cop.semCast v1 ty1 ty2 m = some v
  | .Ecall (.Eval vf tyf) rargs _ =>
      exprlistAllValues rargs →
      ∃ tyargs tyres cconv fd vl,
        Cop.classifyFun tyf = .f tyargs tyres cconv ∧
        Genv.findFunct ge.genv_genv vf = some fd ∧
        Csem.CastArguments m rargs tyargs vl ∧
        Csyntax.typeOfFundef fd = .Tfunction tyargs tyres cconv
  | .Ebuiltin ef tyargs rargs _ =>
      exprlistAllValues rargs →
      ∃ vargs t vres m', Csem.CastArguments m rargs tyargs vargs ∧
        externalCall ef ge.genv_genv.toSenv vargs m t vres m'
  | _ => True

variable {ge e}

/-- `Cstrategy.lred_invert` -/
theorem lred_invert {l m l' m'} (h : Csem.Lred ge e l m l' m') : invertExprProp ge e l m := by
  cases h with
  | var_local x ty m b hx => exact ⟨b, .inl hx⟩
  | var_global x ty m b hx hs => exact ⟨b, .inr ⟨hx, hs⟩⟩
  | deref b ofs => exact ⟨b, ofs, rfl⟩
  | field_struct b ofs id co a f ty m delta bf hco hfo =>
    exact ⟨b, ofs, rfl, co, delta, bf, hco, hfo⟩
  | field_union b ofs id co a f ty m delta bf hco hfo =>
    exact ⟨b, ofs, rfl, co, delta, bf, hco, hfo⟩

/-- `Cstrategy.rred_invert` -/
theorem rred_invert {r m t r' m'} (h : Csem.Rred ge r m t r' m') : invertExprProp ge e r m := by
  cases h with
  | rvalof _ _ _ _ _ t v hd => exact ⟨rfl, t, v, hd⟩
  | addrof => rfl
  | unop _ _ _ _ _ v hv => exact ⟨v, hv⟩
  | binop _ _ _ _ _ _ _ v hv => exact ⟨v, hv⟩
  | cast _ _ _ _ v hv => exact ⟨v, hv⟩
  | seqand_true _ _ _ _ _ hb => exact ⟨true, hb⟩
  | seqand_false _ _ _ _ _ hb => exact ⟨false, hb⟩
  | seqor_true _ _ _ _ _ hb => exact ⟨true, hb⟩
  | seqor_false _ _ _ _ _ hb => exact ⟨false, hb⟩
  | condition _ _ _ _ _ b _ hb => exact ⟨b, hb⟩
  | sizeof => trivial
  | alignof => trivial
  | assign _ _ _ _ _ _ _ v t m' v' hc ha => exact ⟨v, m', v', t, rfl, hc, ha⟩
  | assignop _ _ _ _ _ _ _ _ _ t v1 hd => exact ⟨t, v1, rfl, hd⟩
  | postincr _ _ _ _ _ _ t v1 _ hd _ => exact ⟨t, v1, rfl, hd⟩
  | comma _ _ _ _ _ hty => exact hty
  | paren _ _ _ _ _ v hv => exact ⟨v, hv⟩
  | builtin _ _ _ _ _ vargs t vres m' hc he => exact fun _ => ⟨vargs, t, vres, m', hc, he⟩

/-- `Cstrategy.callred_invert` -/
theorem callred_invert {r fd args ty m} (h : Csem.Callred ge r m fd args ty) :
    invertExprProp ge e r m := by
  cases h with
  | call _ _ _ _ _ _ _ _ _ _ hf hc ht hcl =>
    exact fun _ => ⟨_, _, _, _, _, hcl, hf, hc, ht⟩

/-- A redex that satisfies `invert_expr_prop` is neither a value nor a location. -/
theorem invertExprProp_not_val {a m} (h : invertExprProp ge e a m) :
    (∀ v ty, a ≠ .Eval v ty) ∧ (∀ b ofs bf ty, a ≠ .Eloc b ofs bf ty) := by
  constructor
  · rintro v ty rfl; exact h
  · rintro b ofs bf ty rfl; exact h

mutual
/-- `Cstrategy.invert_expr_context` (first half): `invert_expr_prop` propagates
    from a redex to any expression built around it by a reduction context. -/
theorem invert_expr_context {from_} : ∀ {to C}, Csem.Context from_ to C →
    ∀ {a m}, invertExprProp ge e a m → invertExprProp ge e (C a) m
  | _, _, .top _, _, _, h => h
  | _, _, .deref _ C _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .field _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .rvalof _ C _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .addrof _ C _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .unop _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .binop_left _ C _ _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .cast _ C _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .seqand _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .seqor _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .condition _ C _ _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .assign_left _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .assignop_left _ C _ _ _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .postincr _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .call_left _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .comma _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .paren _ C _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | trivial | exact absurd rfl (hx.1 _ _) | exact absurd rfl (hx.2 _ _ _ _)
  | _, _, .binop_right _ C _ e1 _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> (try exact absurd rfl (hx.1 _ _)) <;> cases e1 <;> trivial
  | _, _, .assign_right _ C e1 _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> (try exact absurd rfl (hx.1 _ _)) <;> cases e1 <;> trivial
  | _, _, .assignop_right _ C _ e1 _ _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> (try exact absurd rfl (hx.1 _ _)) <;> cases e1 <;> trivial
  | _, _, .call_right _ C e1 _ hC, a, _, h => by
    dsimp only
    have hx := invert_exprlist_context hC h
    cases e1 <;> first | trivial | exact fun hall => absurd hall hx
  | _, _, .builtin _ C _ _ _ hC, a, _, h => fun hall => absurd hall (invert_exprlist_context hC h)

/-- `Cstrategy.invert_expr_context` (second half): an argument list with a redex
    in it is not fully evaluated. -/
theorem invert_exprlist_context {from_} : ∀ {C}, Csem.ContextList from_ C →
    ∀ {a m}, invertExprProp ge e a m → ¬ exprlistAllValues (C a)
  | _, .head _ C _ hC, a, _, h => by
    have hx := invertExprProp_not_val (invert_expr_context hC h)
    dsimp only
    generalize C a = x at hx ⊢
    cases x <;> first | exact absurd rfl (hx.1 _ _) | exact fun hh => hh
  | _, .tail _ C e1 hC, a, _, h => by
    dsimp only
    have hx := invert_exprlist_context hC h
    cases e1 <;> first | exact hx | exact fun hh => hh

end

/-- The conclusion of `Cstrategy.imm_safe_inv`: a value or location, or an
    expression satisfying `invert_expr_prop`. -/
def invertOrValue (ge : Csem.CGenv) (e : Env) (a : Csyntax.Expr) (m : Mem) : Prop :=
  match a with
  | .Eloc _ _ _ _ => True
  | .Eval _ _ => True
  | _ => invertExprProp ge e a m

/-- `invert_expr_prop` implies `invertOrValue`. -/
theorem invertOrValue_of_invert {a m} (h : invertExprProp ge e a m) : invertOrValue ge e a m := by
  cases a <;> first | trivial | exact h

/-- `Cstrategy.imm_safe_inv`: an immediately safe expression is a value, a
    location, or satisfies `invert_expr_prop`. -/
theorem imm_safe_inv {k a m} (h : Csem.ImmSafe ge e k a m) : invertOrValue ge e a m := by
  cases h with
  | val => trivial
  | loc => trivial
  | lred _ _ _ _ _ _ hl hC => exact invertOrValue_of_invert (invert_expr_context hC (lred_invert hl))
  | rred _ _ _ _ _ _ _ hr hC => exact invertOrValue_of_invert (invert_expr_context hC (rred_invert hr))
  | callred _ _ _ _ _ _ _ hc hC =>
    exact invertOrValue_of_invert (invert_expr_context hC (callred_invert hc))

/-- `Cstrategy.safe_inv` -/
theorem safe_inv {k C f a K m} (hs : Safe ge (.ExprState f (C a) K e m))
    (hC : Csem.Context k .RV C) : invertOrValue ge e a m :=
  imm_safe_inv (safe_imm_safe hs hC)

end INVERSION_LEMMAS

section SIMPLE_CAN_EVAL
variable {ge : Csem.CGenv} {f : Csyntax.Function} {k : Csem.Cont} {e : Env} {m : Mem}

/-- The conclusion of `Cstrategy.simple_can_eval`. -/
def CanEval (ge : Csem.CGenv) (e : Env) (m : Mem) : Csem.Kind → Csyntax.Expr → Prop
  | .LV, a => ∃ b ofs bf, EvalSimpleLvalue ge e m a b ofs bf
  | .RV, a => ∃ v, EvalSimpleRvalue ge e m a v

/-- `Cstrategy.simple_can_eval`: in a safe state, a simple expression at a
    reduction context can be evaluated in one big step. -/
theorem simple_can_eval (a : Csyntax.Expr) : ∀ {from_ C}, simple a = true →
    Csem.Context from_ .RV C → Safe ge (.ExprState f (C a) k e m) → CanEval ge e m from_ a := by
  intro from_ C hs hC hsafe
  have K := safe_expr_kind hC hsafe
  subst K
  cases a with
  | Eval v ty => exact ⟨v, .val v ty⟩
  | Evar x ty =>
    obtain ⟨b, hb⟩ := safe_inv hsafe hC
    rcases hb with hb | ⟨hn, hs'⟩
    · exact ⟨b, _, _, .var_local _ _ _ hb⟩
    · exact ⟨b, _, _, .var_global _ _ _ hn hs'⟩
  | Efield a1 fl ty =>
    have hC' : Csem.Context .RV .RV (fun x => C (.Efield x fl ty)) :=
      context_compose (.field _ _ _ _ (.top _)) hC
    obtain ⟨v, E⟩ := simple_can_eval a1 (C := fun x => C (.Efield x fl ty)) hs hC' hsafe
    have hsafe' := eval_simple_rvalue_safe E hC' hsafe
    obtain ⟨b, ofs, rfl, TY⟩ := safe_inv hsafe' hC
    generalize hT : Csyntax.typeof a1 = T at TY
    cases T with
    | Tstruct id at_ =>
      obtain ⟨co, delta, bf, hco, hfo⟩ := TY
      exact ⟨b, _, bf, .field_struct _ _ _ _ _ _ _ _ _ _ E hT hco hfo⟩
    | Tunion id at_ =>
      obtain ⟨co, delta, bf, hco, hfo⟩ := TY
      exact ⟨b, _, bf, .field_union _ _ _ _ _ _ _ _ _ _ E hT hfo hco⟩
    | _ => exact TY.elim
  | Evalof l ty =>
    simp only [simple, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hC' : Csem.Context .LV .RV (fun x => C (.Evalof x ty)) :=
      context_compose (.rvalof _ _ _ (.top _)) hC
    obtain ⟨b, ofs, bf, E⟩ := simple_can_eval l (C := fun x => C (.Evalof x ty)) hs1 hC' hsafe
    have hsafe' := eval_simple_lvalue_safe E hC' hsafe
    obtain ⟨hty, t, v, hd⟩ := safe_inv hsafe' hC
    subst hty
    cases hd with
    | volatile _ _ _ _ hv _ => rw [hs2] at hv; cases hv
    | value chunk v h1 h2 h3 => exact ⟨v, .rvalof _ _ _ _ _ _ E rfl hs2 (.value _ _ h1 h2 h3)⟩
    | reference h1 => exact ⟨_, .rvalof _ _ _ _ _ _ E rfl hs2 (.reference h1)⟩
    | copy h1 => exact ⟨_, .rvalof _ _ _ _ _ _ E rfl hs2 (.copy h1)⟩
    | bitfield sz sg pos width v h1 =>
      exact ⟨v, .rvalof _ _ _ _ _ _ E rfl hs2 (.bitfield _ _ _ _ _ h1)⟩
  | Ederef r ty =>
    have hC' : Csem.Context .RV .RV (fun x => C (.Ederef x ty)) :=
      context_compose (.deref _ _ _ (.top _)) hC
    obtain ⟨v, E⟩ := simple_can_eval r (C := fun x => C (.Ederef x ty)) hs hC' hsafe
    have hsafe' := eval_simple_rvalue_safe E hC' hsafe
    obtain ⟨b, ofs, rfl⟩ := safe_inv hsafe' hC
    exact ⟨b, ofs, _, .deref _ _ _ _ E⟩
  | Eaddrof l ty =>
    have hC' : Csem.Context .LV .RV (fun x => C (.Eaddrof x ty)) :=
      context_compose (.addrof _ _ _ (.top _)) hC
    obtain ⟨b, ofs, bf, E⟩ := simple_can_eval l (C := fun x => C (.Eaddrof x ty)) hs hC' hsafe
    have hsafe' := eval_simple_lvalue_safe E hC' hsafe
    have hbf : bf = .Full := safe_inv hsafe' hC
    subst hbf
    exact ⟨_, .addrof _ _ _ _ E⟩
  | Eunop op r ty =>
    have hC' : Csem.Context .RV .RV (fun x => C (.Eunop op x ty)) :=
      context_compose (.unop _ _ _ _ (.top _)) hC
    obtain ⟨v, E⟩ := simple_can_eval r (C := fun x => C (.Eunop op x ty)) hs hC' hsafe
    have hsafe' := eval_simple_rvalue_safe E hC' hsafe
    obtain ⟨v', hv⟩ := safe_inv hsafe' hC
    exact ⟨v', .unop _ _ _ _ _ E hv⟩
  | Ebinop op r1 r2 ty =>
    simp only [simple, Bool.and_eq_true] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hC1 : Csem.Context .RV .RV (fun x => C (.Ebinop op x r2 ty)) :=
      context_compose (.binop_left _ _ _ _ _ (.top _)) hC
    obtain ⟨v1, E1⟩ := simple_can_eval r1 (C := fun x => C (.Ebinop op x r2 ty)) hs1 hC1 hsafe
    have hsafe1 := eval_simple_rvalue_safe E1 hC1 hsafe
    have hC2 : Csem.Context .RV .RV
        (fun x => C (.Ebinop op (.Eval v1 (Csyntax.typeof r1)) x ty)) :=
      context_compose (.binop_right _ _ _ _ _ (.top _)) hC
    obtain ⟨v2, E2⟩ := simple_can_eval r2
      (C := fun x => C (.Ebinop op (.Eval v1 (Csyntax.typeof r1)) x ty)) hs2 hC2 hsafe1
    have hsafe2 := eval_simple_rvalue_safe E2 hC2 hsafe1
    obtain ⟨v', hv⟩ := safe_inv hsafe2 hC
    exact ⟨v', .binop _ _ _ _ _ _ _ E1 E2 hv⟩
  | Ecast r ty =>
    have hC' : Csem.Context .RV .RV (fun x => C (.Ecast x ty)) :=
      context_compose (.cast _ _ _ (.top _)) hC
    obtain ⟨v, E⟩ := simple_can_eval r (C := fun x => C (.Ecast x ty)) hs hC' hsafe
    have hsafe' := eval_simple_rvalue_safe E hC' hsafe
    obtain ⟨v', hv⟩ := safe_inv hsafe' hC
    exact ⟨v', .cast _ _ _ _ E hv⟩
  | Esizeof ty1 ty => exact ⟨_, .sizeof _ _⟩
  | Ealignof ty1 ty => exact ⟨_, .alignof _ _⟩
  | Eloc b ofs bf ty => exact ⟨b, ofs, bf, .loc _ _ _ _⟩
  | _ => simp [simple] at hs
termination_by sizeOf a


/-- `Cstrategy.simple_can_eval_rval` -/
theorem simple_can_eval_rval {r C} (hs : simple r = true) (hC : Csem.Context .RV .RV C)
    (hsafe : Safe ge (.ExprState f (C r) k e m)) :
    ∃ v, EvalSimpleRvalue ge e m r v ∧
      Safe ge (.ExprState f (C (.Eval v (Csyntax.typeof r))) k e m) := by
  obtain ⟨v, E⟩ := simple_can_eval r (from_ := .RV) hs hC hsafe
  exact ⟨v, E, eval_simple_rvalue_safe E hC hsafe⟩

/-- `Cstrategy.simple_can_eval_lval` -/
theorem simple_can_eval_lval {l C} (hs : simple l = true) (hC : Csem.Context .LV .RV C)
    (hsafe : Safe ge (.ExprState f (C l) k e m)) :
    ∃ b ofs bf, EvalSimpleLvalue ge e m l b ofs bf ∧
      Safe ge (.ExprState f (C (.Eloc b ofs bf (Csyntax.typeof l))) k e m) := by
  obtain ⟨b, ofs, bf, E⟩ := simple_can_eval l (from_ := .LV) hs hC hsafe
  exact ⟨b, ofs, bf, E, eval_simple_lvalue_safe E hC hsafe⟩

end SIMPLE_CAN_EVAL

end Cstrategy
end CC
