/-
  Port of `cfrontend/Cexec.v`, part 3: soundness and completeness of the
  reduction of expressions (`Cexec.v` lines 986–1944): `imm_safe_t`,
  `invert_expr_prop`, `reducts_ok`, `step_expr_sound`, `lred_topred`,
  `rred_topred`, `callred_topred`, `step_expr_context`,
  `not_imm_safe_stuck_red`, `imm_safe_imm_safe_t` and `not_imm_safe_t`.

  As in Rocq, the soundness of `step_expr` already needs the completeness of
  the executable memory accesses and external calls: a `Stuckred` reduct is
  only correct if *no* reduction is possible.  So `step_expr_sound` takes the
  injectivity of the symbol table (see `CCLib.cfrontend.CexecEvents`) and both
  `ExtOracle.Sound` and `ExtOracle.Complete`.
-/
import CCLib.cfrontend.CexecEvents
import CCLib.cfrontend.Cstrategy

namespace CC
namespace Cexec

open Csyntax

section EXPRS

variable (ge : Csem.CGenv) (ox : ExtOracle) (e : Env) (w : World)

/-! ## Immediately safe expressions, relative to a world -/

/-- `Cexec.imm_safe_t`: like `Csem.imm_safe`, but a reduction that emits
    events counts only if world `w` accepts them. -/
inductive ImmSafeT : Csem.Kind → Csyntax.Expr → Mem → Prop where
  | val (v ty m) : ImmSafeT .RV (.Eval v ty) m
  | loc (b ofs ty bf m) : ImmSafeT .LV (.Eloc b ofs bf ty) m
  | lred (to C l m l' m') :
      Csem.Lred ge e l m l' m' → Csem.Context .LV to C → ImmSafeT to (C l) m
  | rred (to C r m t r' m' w') :
      Csem.Rred ge r m t r' m' → PossibleTrace w t w' → Csem.Context .RV to C →
      ImmSafeT to (C r) m
  | callred (to C r m fd args ty) :
      Csem.Callred ge r m fd args ty → Csem.Context .RV to C → ImmSafeT to (C r) m

/-- `Cexec.imm_safe_t_imm_safe` -/
theorem immSafeT_immSafe {k a m} (h : ImmSafeT ge e w k a m) : Csem.ImmSafe ge e k a m := by
  cases h with
  | val => exact .val _ _ _
  | loc => exact .loc _ _ _ _ _
  | lred _ _ _ _ _ _ hl hC => exact .lred _ _ _ _ _ _ hl hC
  | rred _ _ _ _ _ _ _ _ hr _ hC => exact .rred _ _ _ _ _ _ _ hr hC
  | callred _ _ _ _ _ _ _ hc hC => exact .callred _ _ _ _ _ _ _ hc hC

/-- `Cexec.exprlist_all_values` -/
def exprlistAllValues : Csyntax.ExprList → Prop
  | .Enil => True
  | .Econs (.Eval _ _) rl' => exprlistAllValues rl'
  | .Econs _ _ => False

/-- `Cexec.invert_expr_prop`: what must hold of the head of an expression that
    is immediately safe (and not already a value or location). -/
def InvertExprProp (a : Csyntax.Expr) (m : Mem) : Prop :=
  match a with
  | .Eloc _ _ _ _ => False
  | .Evar x ty =>
      ∃ b, e.get x = some (b, ty) ∨ (e.get x = none ∧ Genv.findSymbol ge.genv_genv x = some b)
  | .Ederef r _ =>
      match r with
      | .Eval v _ => ∃ b ofs, v = .Vptr b ofs
      | _ => True
  | .Eaddrof l _ =>
      match l with
      | .Eloc _ _ bf _ => bf = .Full
      | _ => True
  | .Efield r f _ =>
      match r with
      | .Eval v ty1 =>
          ∃ b ofs, v = .Vptr b ofs ∧
            match ty1 with
            | .Tstruct id _ => ∃ co delta bf, ge.genv_cenv.get id = some co ∧
                fieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf)
            | .Tunion id _ => ∃ co delta bf, ge.genv_cenv.get id = some co ∧
                unionFieldOffset ge.genv_cenv f co.co_members = .OK (delta, bf)
            | _ => False
      | _ => True
  | .Eval _ _ => False
  | .Evalof l ty =>
      match l with
      | .Eloc b ofs bf ty' =>
          ty' = ty ∧ ∃ t v w', Csem.DerefLoc ge ty m b ofs bf t v ∧ PossibleTrace w t w'
      | _ => True
  | .Eunop op r1 _ =>
      match r1 with
      | .Eval v1 ty1 => ∃ v, Cop.semUnaryOperation op v1 ty1 m = some v
      | _ => True
  | .Ebinop op r1 r2 _ =>
      match r1, r2 with
      | .Eval v1 ty1, .Eval v2 ty2 =>
          ∃ v, Cop.semBinaryOperation ge.genv_cenv op v1 ty1 v2 ty2 m = some v
      | _, _ => True
  | .Ecast r1 ty =>
      match r1 with
      | .Eval v1 ty1 => ∃ v, Cop.semCast v1 ty1 ty m = some v
      | _ => True
  | .Eseqand r1 _ _ =>
      match r1 with
      | .Eval v1 ty1 => ∃ b, Cop.boolVal v1 ty1 m = some b
      | _ => True
  | .Eseqor r1 _ _ =>
      match r1 with
      | .Eval v1 ty1 => ∃ b, Cop.boolVal v1 ty1 m = some b
      | _ => True
  | .Econdition r1 _ _ _ =>
      match r1 with
      | .Eval v1 ty1 => ∃ b, Cop.boolVal v1 ty1 m = some b
      | _ => True
  | .Eassign l1 r2 ty =>
      match l1, r2 with
      | .Eloc b ofs bf ty1, .Eval v2 ty2 =>
          ∃ v m' v' t w', ty = ty1 ∧ Cop.semCast v2 ty2 ty1 m = some v ∧
            Csem.AssignLoc ge ty1 m b ofs bf v t m' v' ∧ PossibleTrace w t w'
      | _, _ => True
  | .Eassignop _ l1 r2 _ ty =>
      match l1, r2 with
      | .Eloc b ofs bf ty1, .Eval _ _ =>
          ∃ t v1 w', ty = ty1 ∧ Csem.DerefLoc ge ty1 m b ofs bf t v1 ∧ PossibleTrace w t w'
      | _, _ => True
  | .Epostincr _ l ty =>
      match l with
      | .Eloc b ofs bf ty1 =>
          ∃ t v1 w', ty = ty1 ∧ Csem.DerefLoc ge ty m b ofs bf t v1 ∧ PossibleTrace w t w'
      | _ => True
  | .Ecomma r1 r2 ty =>
      match r1 with
      | .Eval _ _ => Csyntax.typeof r2 = ty
      | _ => True
  | .Eparen r1 tycast _ =>
      match r1 with
      | .Eval v1 ty1 => ∃ v, Cop.semCast v1 ty1 tycast m = some v
      | _ => True
  | .Ecall r1 rargs _ =>
      match r1 with
      | .Eval vf tyf =>
          exprlistAllValues rargs →
            ∃ tyargs tyres cconv fd vl,
              Cop.classifyFun tyf = .f tyargs tyres cconv
              ∧ Genv.findFunct ge.genv_genv vf = some fd
              ∧ Csem.CastArguments m rargs tyargs vl
              ∧ Csyntax.typeOfFundef fd = .Tfunction tyargs tyres cconv
      | _ => True
  | .Ebuiltin ef tyargs rargs _ =>
      exprlistAllValues rargs →
        ∃ vargs t vres m' w',
          Csem.CastArguments m rargs tyargs vargs
          ∧ externalCall ef ge.genv_genv.toSenv vargs m t vres m'
          ∧ PossibleTrace w t w'
  | _ => True

/-- `Cexec.lred_invert` -/
theorem lred_invert {l m l' m'} (h : Csem.Lred ge e l m l' m') : InvertExprProp ge e w l m := by
  cases h with
  | var_local x ty m b hb => exact ⟨b, .inl hb⟩
  | var_global x ty m b hn hb => exact ⟨b, .inr ⟨hn, hb⟩⟩
  | deref b ofs => exact ⟨b, ofs, rfl⟩
  | field_struct b ofs id co a f ty m delta bf hco hf =>
      exact ⟨b, ofs, rfl, co, delta, bf, hco, hf⟩
  | field_union b ofs id co a f ty m delta bf hco hf =>
      exact ⟨b, ofs, rfl, co, delta, bf, hco, hf⟩

/-- `Cexec.rred_invert` -/
theorem rred_invert {w' r m t r' m'} (h : Csem.Rred ge r m t r' m') (hp : PossibleTrace w t w') :
    InvertExprProp ge e w r m := by
  cases h with
  | rvalof b ofs bf ty m t v hd => exact ⟨rfl, t, v, w', hd, hp⟩
  | addrof => rfl
  | unop op v1 ty1 ty m v hv => exact ⟨v, hv⟩
  | binop op v1 ty1 v2 ty2 ty m v hv => exact ⟨v, hv⟩
  | cast ty v1 ty1 m v hv => exact ⟨v, hv⟩
  | seqand_true _ _ _ _ _ hb => exact ⟨true, hb⟩
  | seqand_false _ _ _ _ _ hb => exact ⟨false, hb⟩
  | seqor_true _ _ _ _ _ hb => exact ⟨true, hb⟩
  | seqor_false _ _ _ _ _ hb => exact ⟨false, hb⟩
  | condition _ _ _ _ _ b _ hb => exact ⟨b, hb⟩
  | sizeof => trivial
  | alignof => trivial
  | assign b ofs ty1 bf v2 ty2 m v t m' v' hc ha => exact ⟨v, m', v', t, w', rfl, hc, ha, hp⟩
  | assignop op b ofs ty1 bf v2 ty2 tyres m t v1 hd => exact ⟨t, v1, w', rfl, hd, hp⟩
  | postincr id b ofs ty bf m t v1 op hd _ => exact ⟨t, v1, w', rfl, hd, hp⟩
  | comma v ty1 r2 ty m ht => exact ht
  | paren v1 ty1 ty2 ty m v hv => exact ⟨v, hv⟩
  | builtin ef tyargs el ty m vargs t vres m' hc he =>
      exact fun _ => ⟨vargs, t, vres, m', w', hc, he, hp⟩

/-- `Cexec.callred_invert` -/
theorem callred_invert {r fd args ty m} (h : Csem.Callred ge r m fd args ty) :
    InvertExprProp ge e w r m := by
  cases h with
  | call =>
      rename_i hf hc ht hcl
      exact fun _ => ⟨_, _, _, _, _, hf, hc, hcl, ht⟩

/-- An expression whose head satisfies `invert_expr_prop` is neither a value
    nor a location. -/
theorem invert_not_val_loc {a m} (h : InvertExprProp ge e w a m) :
    (∀ v ty, a ≠ .Eval v ty) ∧ (∀ b ofs bf ty, a ≠ .Eloc b ofs bf ty) := by
  constructor <;> intros <;> rintro rfl <;> exact h

/-- Closes the goal `InvertExprProp (C' (C a))` for a one-level context `C'`,
    given that `C a` is neither a value nor a location. -/
macro "inv_ctx_tac " hn:ident : tactic => `(tactic| (
  simp only [InvertExprProp]
  repeat' split
  all_goals first
    | trivial
    | (exfalso; exact $hn.1 _ _ ‹_›)
    | (exfalso; exact $hn.2 _ _ _ _ ‹_›)))

mutual
/-- `Cexec.invert_expr_context` (first half) -/
theorem invert_expr_context {from_ : Csem.Kind} : ∀ {to C}, Csem.Context from_ to C →
    ∀ a m, InvertExprProp ge e w a m → InvertExprProp ge e w (C a) m
  | _, _, .top _, _, _, h => h
  | _, _, .deref _ C ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .field _ C f ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .rvalof _ C ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .addrof _ C ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .unop _ C op ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .binop_left _ C op e2 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .binop_right _ C op e1 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .cast _ C ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .seqand _ C r2 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .seqor _ C r2 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .condition _ C r2 r3 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .assign_left _ C e2 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .assign_right _ C e1 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .assignop_left _ C op e2 tyres ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .assignop_right _ C op e1 tyres ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .postincr _ C id ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .call_left _ C el ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .comma _ C e2 ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .paren _ C tycast ty hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      inv_ctx_tac hn
  | _, _, .call_right _ C e1 ty hC, a, m, h => by
      have hn := invert_exprlist_context hC a m h
      simp only [InvertExprProp]
      split
      · exact fun h' => absurd h' hn
      · trivial
  | _, _, .builtin _ C ef tyargs ty hC, a, m, h => by
      have hn := invert_exprlist_context hC a m h
      simp only [InvertExprProp]
      exact fun h' => absurd h' hn

/-- `Cexec.invert_expr_context` (second half) -/
theorem invert_exprlist_context {from_ : Csem.Kind} : ∀ {C}, Csem.ContextList from_ C →
    ∀ a m, InvertExprProp ge e w a m → ¬ exprlistAllValues (C a)
  | _, .head _ C el hC, a, m, h => by
      have hn := invert_not_val_loc ge e w (invert_expr_context hC a m h)
      show ¬ exprlistAllValues (.Econs (C a) el)
      generalize C a = x at hn ⊢
      cases x <;> first | exact fun h => h | exact absurd rfl (hn.1 _ _)
  | _, .tail _ C e1 hC, a, m, h => by
      have hn := invert_exprlist_context hC a m h
      cases e1 <;> simp only [exprlistAllValues, not_false_eq_true] <;> exact hn
end

/-- `Cexec.imm_safe_t_inv` -/
theorem immSafeT_inv {k a m} (h : ImmSafeT ge e w k a m)
    (hv : ∀ v ty, a ≠ .Eval v ty) (hl : ∀ b ofs bf ty, a ≠ .Eloc b ofs bf ty) :
    InvertExprProp ge e w a m := by
  cases h with
  | val v ty => exact absurd rfl (hv v ty)
  | loc b ofs ty bf => exact absurd rfl (hl b ofs bf ty)
  | lred _ C l _ l' m' hr hC => exact invert_expr_context ge e w hC _ _ (lred_invert ge e w hr)
  | rred _ C r _ t r' m' w' hr hp hC =>
      exact invert_expr_context ge e w hC _ _ (rred_invert ge e w hr hp)
  | callred _ C r _ fd args ty hr hC =>
      exact invert_expr_context ge e w hC _ _ (callred_invert ge e w hr)

/-! ## Soundness of `step_expr` -/

/-- `Cexec.reduction_ok` -/
def ReductionOk (k : Csem.Kind) (a : Csyntax.Expr) (m : Mem) (rd : Reduction) : Prop :=
  match k, rd with
  | .LV, .Lred _ l' m' => Csem.Lred ge e a m l' m'
  | .RV, .Rred _ r' m' t => Csem.Rred ge a m t r' m' ∧ ∃ w', PossibleTrace w t w'
  | .RV, .Callred _ fd args tyres m' => Csem.Callred ge a m fd args tyres ∧ m' = m
  | .LV, .Stuckred => ¬ ImmSafeT ge e w k a m
  | .RV, .Stuckred => ¬ ImmSafeT ge e w k a m
  | _, _ => False

/-- `Cexec.reducts_ok`: every reduct is a correct reduction at some context,
    and there are no reducts only if the expression is fully reduced. -/
def ReductsOk (k : Csem.Kind) (a : Csyntax.Expr) (m : Mem) (ll : Reducts Csyntax.Expr) : Prop :=
  (∀ C rd, (C, rd) ∈ ll →
      ∃ a' k', Csem.Context k' k C ∧ a = C a' ∧ ReductionOk ge e w k' a' m rd)
  ∧ (ll = [] → match k with | .LV => isLoc a ≠ none | .RV => isVal a ≠ none)

/-- `Cexec.list_reducts_ok` -/
def ListReductsOk (al : Csyntax.ExprList) (m : Mem) (ll : Reducts Csyntax.ExprList) : Prop :=
  (∀ C rd, (C, rd) ∈ ll →
      ∃ a' k', Csem.ContextList k' C ∧ al = C a' ∧ ReductionOk ge e w k' a' m rd)
  ∧ (ll = [] → isValList al ≠ none)

/-- `Cexec.sem_cast_arguments_sound` -/
theorem semCastArguments_sound {m} : ∀ {rargs vtl tyargs vargs},
    isValList rargs = some vtl → semCastArguments vtl tyargs m = some vargs →
    Csem.CastArguments m rargs tyargs vargs
  | .Enil, vtl, tyargs, vargs, h1, h2 => by
      simp only [isValList, Option.some.injEq] at h1
      subst h1
      cases tyargs with
      | nil => simp only [semCastArguments, Option.some.injEq] at h2; subst h2; exact .nil
      | cons => simp [semCastArguments] at h2
  | .Econs a1 al, vtl, tyargs, vargs, h1, h2 => by
      simp only [isValList] at h1
      split at h1
      · next vt1 hv1 =>
          split at h1
          · next vtl' hvl =>
              cases h1
              obtain ⟨v1, t1⟩ := vt1
              rw [isVal_inv hv1]
              cases tyargs with
              | nil => simp [semCastArguments] at h2
              | cons t1' tl =>
                  simp only [semCastArguments] at h2
                  split at h2
                  · next v hv =>
                      split at h2
                      · next vl hvl' =>
                          cases h2
                          exact .cons _ _ _ _ _ _ _ hv (semCastArguments_sound hvl hvl')
                      · cases h2
                  · cases h2
          · cases h1
      · cases h1

/-- `Cexec.sem_cast_arguments_complete` -/
theorem semCastArguments_complete {m al tyl vl} (h : Csem.CastArguments m al tyl vl) :
    ∃ vtl, isValList al = some vtl ∧ semCastArguments vtl tyl m = some vl := by
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons v ty el targ1 targs v1 vl hc _ ih =>
      obtain ⟨vtl, h1, h2⟩ := ih
      exact ⟨(v, ty) :: vtl, by simp [isValList, isVal, h1], by simp [semCastArguments, hc, h2]⟩

/-- `Cexec.topred_ok` -/
theorem topred_ok {k a m rd} (h : ReductionOk ge e w k a m rd) :
    ReductsOk ge e w k a m (topred rd) := by
  refine ⟨fun C rd' hin => ?_, fun h' => by simp [topred] at h'⟩
  simp only [topred, List.mem_singleton, Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  exact ⟨a, k, .top _, rfl, h⟩

/-- `Cexec.stuck_ok` -/
theorem stuck_ok {k a m} (h : ¬ ImmSafeT ge e w k a m) : ReductsOk ge e w k a m stuck := by
  refine ⟨fun C rd' hin => ?_, fun h' => by simp [stuck] at h'⟩
  simp only [stuck, List.mem_singleton, Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  exact ⟨a, k, .top _, rfl, by cases k <;> exact h⟩

/-- `Cexec.wrong_kind_ok` -/
theorem wrong_kind_ok {k a m} (h : k ≠ Cstrategy.exprKind a) : ReductsOk ge e w k a m stuck :=
  stuck_ok ge e w fun hs => h (Cstrategy.imm_safe_kind (immSafeT_immSafe ge e w hs)).symm

/-- `Cexec.not_invert_ok` -/
theorem not_invert_ok {k a m} (hv : ∀ v ty, a ≠ .Eval v ty)
    (hl : ∀ b ofs bf ty, a ≠ .Eloc b ofs bf ty) (h : ¬ InvertExprProp ge e w a m) :
    ReductsOk ge e w k a m stuck :=
  stuck_ok ge e w fun hs => h (immSafeT_inv ge e w hs hv hl)

/-- `Cexec.incontext_ok` -/
theorem incontext_ok {k a m C res k' a'} (h : ReductsOk ge e w k' a' m res) (ha : a = C a')
    (hC : Csem.Context k' k C)
    (hnv : match k' with | .LV => isLoc a' = none | .RV => isVal a' = none) :
    ReductsOk ge e w k a m (incontext C res) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun C' rd hin => ?_, fun hnil => ?_⟩
  · simp only [incontext, List.mem_map] at hin
    obtain ⟨⟨C1, rd1⟩, hmem, heq⟩ := hin
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h1 C1 rd1 hmem
    exact ⟨a'', k'', Cstrategy.context_compose hC'' hC, by rw [ha, ha''], hrd⟩
  · have : res = [] := by simpa [incontext] using hnil
    have := h2 this
    cases k' <;> simp_all

/-- `Cexec.incontext2_ok` -/
theorem incontext2_ok {k a m k1 a1 res1 k2 a2 res2 C1 C2}
    (h1 : ReductsOk ge e w k1 a1 m res1) (h2 : ReductsOk ge e w k2 a2 m res2)
    (ha1 : a = C1 a1) (ha2 : a = C2 a2)
    (hC1 : Csem.Context k1 k C1) (hC2 : Csem.Context k2 k C2)
    (hnv : (match k1 with | .LV => isLoc a1 = none | .RV => isVal a1 = none)
      ∨ (match k2 with | .LV => isLoc a2 = none | .RV => isVal a2 = none)) :
    ReductsOk ge e w k a m (incontext2 C1 res1 C2 res2) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨fun C' rd hin => ?_, fun hnil => ?_⟩
  · simp only [incontext2, incontext, List.mem_append, List.mem_map] at hin
    rcases hin with ⟨⟨C0, rd0⟩, hmem, heq⟩ | ⟨⟨C0, rd0⟩, hmem, heq⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h1a C0 rd0 hmem
      exact ⟨a'', k'', Cstrategy.context_compose hC'' hC1, by rw [ha1, ha''], hrd⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h2a C0 rd0 hmem
      exact ⟨a'', k'', Cstrategy.context_compose hC'' hC2, by rw [ha2, ha''], hrd⟩
  · simp only [incontext2, incontext, List.append_eq_nil_iff, List.map_eq_nil_iff] at hnil
    have e1 := h1b hnil.1
    have e2 := h2b hnil.2
    rcases hnv with hnv | hnv
    · cases k1 <;> simp_all
    · cases k2 <;> simp_all

/-- `Cexec.incontext_list_ok` -/
theorem incontext_list_ok {ef tyargs al ty m res} (h : ListReductsOk ge e w al m res)
    (hnv : isValList al = none) :
    ReductsOk ge e w .RV (.Ebuiltin ef tyargs al ty) m
      (incontext (fun x => .Ebuiltin ef tyargs x ty) res) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun C' rd hin => ?_, fun hnil => ?_⟩
  · simp only [incontext, List.mem_map] at hin
    obtain ⟨⟨C1, rd1⟩, hmem, heq⟩ := hin
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h1 C1 rd1 hmem
    exact ⟨a'', k'', .builtin _ _ _ _ _ hC'', by rw [ha''], hrd⟩
  · have : res = [] := by simpa [incontext] using hnil
    exact absurd hnv (h2 this)

/-- `Cexec.incontext2_list_ok` -/
theorem incontext2_list_ok {a1 a2 ty m res1 res2} (h1 : ReductsOk ge e w .RV a1 m res1)
    (h2 : ListReductsOk ge e w a2 m res2) (hnv : isVal a1 = none ∨ isValList a2 = none) :
    ReductsOk ge e w .RV (.Ecall a1 a2 ty) m
      (incontext2 (fun x => .Ecall x a2 ty) res1 (fun x => .Ecall a1 x ty) res2) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨fun C' rd hin => ?_, fun hnil => ?_⟩
  · simp only [incontext2, incontext, List.mem_append, List.mem_map] at hin
    rcases hin with ⟨⟨C0, rd0⟩, hmem, heq⟩ | ⟨⟨C0, rd0⟩, hmem, heq⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h1a C0 rd0 hmem
      exact ⟨a'', k'', .call_left _ _ _ _ hC'', by rw [ha''], hrd⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h2a C0 rd0 hmem
      exact ⟨a'', k'', .call_right _ _ _ _ hC'', by rw [ha''], hrd⟩
  · simp only [incontext2, incontext, List.append_eq_nil_iff, List.map_eq_nil_iff] at hnil
    have e1 := h1b hnil.1
    have e2 := h2b hnil.2
    rcases hnv with hnv | hnv
    · exact absurd hnv e1
    · exact absurd hnv e2

/-- `Cexec.incontext2_list_ok'` -/
theorem incontext2_list_ok' {a1 a2 m res1 res2} (h1 : ReductsOk ge e w .RV a1 m res1)
    (h2 : ListReductsOk ge e w a2 m res2) :
    ListReductsOk ge e w (.Econs a1 a2) m
      (incontext2 (fun x => .Econs x a2) res1 (fun x => .Econs a1 x) res2) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨fun C' rd hin => ?_, fun hnil => ?_⟩
  · simp only [incontext2, incontext, List.mem_append, List.mem_map] at hin
    rcases hin with ⟨⟨C0, rd0⟩, hmem, heq⟩ | ⟨⟨C0, rd0⟩, hmem, heq⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h1a C0 rd0 hmem
      exact ⟨a'', k'', .head _ _ _ hC'', by rw [ha''], hrd⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨a'', k'', hC'', ha'', hrd⟩ := h2a C0 rd0 hmem
      exact ⟨a'', k'', .tail _ _ _ hC'', by rw [ha''], hrd⟩
  · simp only [incontext2, incontext, List.append_eq_nil_iff, List.map_eq_nil_iff] at hnil
    have e1 := h1b hnil.1
    have e2 := h2b hnil.2
    simp only [isValList]
    cases hv : isVal a1 with
    | none => exact absurd hv e1
    | some vt =>
        cases hvl : isValList a2 with
        | none => exact absurd hvl e2
        | some vtl => simp

/-- `Cexec.is_val_list_all_values` -/
theorem isValList_allValues : ∀ {al vtl}, isValList al = some vtl → exprlistAllValues al
  | .Enil, _, _ => trivial
  | .Econs a1 al, vtl, h => by
      simp only [isValList] at h
      split at h
      · next vt1 hv1 =>
          split at h
          · next vtl' hvl =>
              obtain ⟨v, ty⟩ := vt1
              rw [isVal_inv hv1]
              exact (isValList_allValues hvl : exprlistAllValues al)
          · cases h
      · cases h

end EXPRS

end Cexec
end CC
