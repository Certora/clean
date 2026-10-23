/-
  Port of `cfrontend/Cexec.v`, part 5: completeness of `step_expr`
  (`Cexec.v` lines 1615–1942).

  * Part 1: every head reduction is found at the top (`lred_topred`,
    `rred_topred`, `callred_topred`), and the reducts of a subexpression in a
    reduction context are among the reducts of the whole expression
    (`step_expr_context`).
  * Part 2: if an expression can go wrong, `step_expr` lists a `Stuckred`
    reduct (`not_imm_safe_stuck_red`), and the relation between `imm_safe_t`
    and `Csem.imm_safe` (`imm_safe_imm_safe_t`, `not_imm_safe_t`).
-/
import CCLib.cfrontend.CexecExprSound

namespace CC
namespace Cexec

open Csyntax

section EXPRS

variable (ge : Csem.CGenv) (ox : ExtOracle) (e : Env) (w : World)

/-- `Cexec.step_exprlist_val_list` -/
theorem stepExprlist_valList {m} : ∀ {al}, isValList al ≠ none → stepExprlist ge ox e w al m = []
  | .Enil, _ => by simp [stepExprlist]
  | .Econs a1 al, h => by
      simp only [isValList] at h
      split at h
      · next vt1 hv1 =>
          split at h
          · next vtl hvl =>
              obtain ⟨v, ty⟩ := vt1
              rw [isVal_inv hv1]
              simp only [stepExprlist, incontext2, incontext]
              rw [stepExprlist_valList (by rw [hvl]; simp)]
              simp [stepExpr]
          · exact absurd rfl h
      · exact absurd rfl h

/-! ## Completeness, part 1: all non-error reducts are listed -/

/-- `Cexec.lred_topred` -/
theorem lred_topred {l1 m1 l2 m2} (h : Csem.Lred ge e l1 m1 l2 m2) :
    ∃ rule, stepExpr ge ox e w .LV l1 m1 = topred (.Lred rule l2 m2) := by
  cases h with
  | var_local x ty m b hb => exact ⟨_, by simp [stepExpr, hb] <;> rfl⟩
  | var_global x ty m b hn hb => exact ⟨_, by simp [stepExpr, hn, hb] <;> rfl⟩
  | deref b ofs ty1 ty m => exact ⟨_, by simp [stepExpr, isVal] <;> rfl⟩
  | field_struct b ofs id co a f ty m delta bf hco hf =>
      exact ⟨_, by simp [stepExpr, isVal, hco, hf] <;> rfl⟩
  | field_union b ofs id co a f ty m delta bf hco hf =>
      exact ⟨_, by simp [stepExpr, isVal, hco, hf] <;> rfl⟩

/-- `Cexec.rred_topred` -/
theorem rred_topred (hinj : Genv.SymbInjective ge.genv_genv) (hC : ox.Complete)
    {w' r1 m1 t r2 m2} (h : Csem.Rred ge r1 m1 t r2 m2) (hp : PossibleTrace w t w') :
    ∃ rule, stepExpr ge ox e w .RV r1 m1 = topred (.Rred rule r2 m2 t) := by
  cases h with
  | rvalof b ofs bf ty m t v hd =>
      exact ⟨_, by simp [stepExpr, isLoc, doDerefLoc_complete ge hinj hd hp] <;> rfl⟩
  | addrof b ofs ty1 ty m =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isLoc] <;> rfl⟩
  | unop op v1 ty1 ty m v hv =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hv] <;> rfl⟩
  | binop op v1 ty1 v2 ty2 ty m v hv =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hv] <;> rfl⟩
  | cast ty v1 ty1 m v hv =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hv] <;> rfl⟩
  | seqand_true v1 ty1 r2 ty m hb =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hb] <;> rfl⟩
  | seqand_false v1 ty1 r2 ty m hb =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hb] <;> rfl⟩
  | seqor_true v1 ty1 r2 ty m hb =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hb] <;> rfl⟩
  | seqor_false v1 ty1 r2 ty m hb =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hb] <;> rfl⟩
  | condition v1 ty1 r1 r2 ty b m hb =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hb] <;> rfl⟩
  | sizeof ty1 ty m =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr] <;> rfl⟩
  | alignof ty1 ty m =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr] <;> rfl⟩
  | assign b ofs ty1 bf v2 ty2 m v t m' v' hc ha =>
      exact ⟨_, by simp [stepExpr, isLoc, isVal, hc, doAssignLoc_complete ge hinj ha hp] <;> rfl⟩
  | assignop op b ofs ty1 bf v2 ty2 tyres m t v1 hd =>
      exact ⟨_, by simp [stepExpr, isLoc, isVal, doDerefLoc_complete ge hinj hd hp] <;> rfl⟩
  | postincr id b ofs ty bf m t v1 op hd hop =>
      subst hop
      exact ⟨_, by simp [stepExpr, isLoc, doDerefLoc_complete ge hinj hd hp] <;> rfl⟩
  | comma v ty1 r2 ty m ht =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, ht] <;> rfl⟩
  | paren v1 ty1 ty2 ty m v hv =>
      cases possibleTrace_E0_inv hp; exact ⟨_, by simp [stepExpr, isVal, hv] <;> rfl⟩
  | builtin ef tyargs el ty m vargs t vres m' hca hec =>
      obtain ⟨vtl, h1, h2⟩ := semCastArguments_complete hca
      exact ⟨_, by simp [stepExpr, h1, h2, doExternal_complete ge ox hinj hC hec hp] <;> rfl⟩

/-- `Cexec.callred_topred` -/
theorem callred_topred {a fd args ty m} (h : Csem.Callred ge a m fd args ty) :
    ∃ rule, stepExpr ge ox e w .RV a m = topred (.Callred rule fd args ty m) := by
  cases h with
  | call =>
      rename_i h₁ h₂ h₃ hca
      obtain ⟨vtl, h1, h2⟩ := semCastArguments_complete hca
      exact ⟨_, by simp [stepExpr, isVal, h1, h2, h₁, h₂, h₃] <;> rfl⟩

/-- `Cexec.reducts_incl`: the reducts `res1`, put in context `C`, are among
    the reducts `res2`. -/
def ReductsIncl {A B : Type} (C : A → B) (res1 : Reducts A) (res2 : Reducts B) : Prop :=
  ∀ C1 rd, (C1, rd) ∈ res1 → ((fun x => C (C1 x)), rd) ∈ res2

/-- `Cexec.reducts_incl_trans` -/
theorem reductsIncl_trans {A1 A2 A3 : Type} {C : A1 → A2} {res1 res2} {C' : A2 → A3} {res3}
    (h1 : ReductsIncl C res1 res2) (h2 : ReductsIncl C' res2 res3) :
    ReductsIncl (fun x => C' (C x)) res1 res3 :=
  fun C1 rd h => h2 _ _ (h1 C1 rd h)

/-- `Cexec.reducts_incl_nil` -/
theorem reductsIncl_nil {A B : Type} (C : A → B) (res : Reducts B) : ReductsIncl C [] res :=
  fun _ _ h => nomatch h

/-- `Cexec.reducts_incl_val` -/
theorem reductsIncl_val {A : Type} {a m v ty} (C : Csyntax.Expr → A) (res : Reducts A)
    (h : isVal a = some (v, ty)) : ReductsIncl C (stepExpr ge ox e w .RV a m) res := by
  rw [isVal_inv h]; exact reductsIncl_nil C res

/-- `Cexec.reducts_incl_loc` -/
theorem reductsIncl_loc {A : Type} {a m b ofs bf ty} (C : Csyntax.Expr → A) (res : Reducts A)
    (h : isLoc a = some (b, ofs, bf, ty)) : ReductsIncl C (stepExpr ge ox e w .LV a m) res := by
  rw [isLoc_inv h]; exact reductsIncl_nil C res

/-- `Cexec.reducts_incl_listval` -/
theorem reductsIncl_listval {A : Type} {a m vtl} (C : Csyntax.ExprList → A) (res : Reducts A)
    (h : isValList a = some vtl) : ReductsIncl C (stepExprlist ge ox e w a m) res := by
  rw [stepExprlist_valList ge ox e w (by rw [h]; simp)]; exact reductsIncl_nil C res

/-- `Cexec.reducts_incl_incontext` -/
theorem reductsIncl_incontext {A B : Type} (C : A → B) (res : Reducts A) :
    ReductsIncl C res (incontext C res) := by
  intro C1 rd h
  simp only [incontext, List.mem_map]
  exact ⟨(C1, rd), h, rfl⟩

/-- `Cexec.reducts_incl_incontext2_left` -/
theorem reductsIncl_incontext2_left {A1 A2 B : Type} (C1 : A1 → B) (res1 : Reducts A1)
    (C2 : A2 → B) (res2 : Reducts A2) : ReductsIncl C1 res1 (incontext2 C1 res1 C2 res2) := by
  intro C0 rd h
  simp only [incontext2, incontext, List.mem_append, List.mem_map]
  exact .inl ⟨(C0, rd), h, rfl⟩

/-- `Cexec.reducts_incl_incontext2_right` -/
theorem reductsIncl_incontext2_right {A1 A2 B : Type} (C1 : A1 → B) (res1 : Reducts A1)
    (C2 : A2 → B) (res2 : Reducts A2) : ReductsIncl C2 res2 (incontext2 C1 res1 C2 res2) := by
  intro C0 rd h
  simp only [incontext2, incontext, List.mem_append, List.mem_map]
  exact .inr ⟨(C0, rd), h, rfl⟩

/-- One step of `step_expr_context` through a one-level context whose hole is
    an r-value: if the hole is a value it has no reducts, otherwise the
    reducts of the hole are among those of the whole expression. -/
theorem reductsIncl_stepRV {A : Type} {x m} (C' : Csyntax.Expr → A) (res : Reducts A)
    (h : isVal x = none → ReductsIncl C' (stepExpr ge ox e w .RV x m) res) :
    ReductsIncl C' (stepExpr ge ox e w .RV x m) res := by
  cases hv : isVal x with
  | none => exact h hv
  | some p => exact reductsIncl_val ge ox e w C' res (v := p.1) (ty := p.2) hv

/-- The same, for a hole that is an l-value. -/
theorem reductsIncl_stepLV {A : Type} {x m} (C' : Csyntax.Expr → A) (res : Reducts A)
    (h : isLoc x = none → ReductsIncl C' (stepExpr ge ox e w .LV x m) res) :
    ReductsIncl C' (stepExpr ge ox e w .LV x m) res := by
  cases hl : isLoc x with
  | none => exact h hl
  | some p =>
      exact reductsIncl_loc ge ox e w C' res (b := p.1) (ofs := p.2.1) (bf := p.2.2.1)
        (ty := p.2.2.2) hl

/-- The same, for a hole that is a list of r-values. -/
theorem reductsIncl_stepList {A : Type} {x m} (C' : Csyntax.ExprList → A) (res : Reducts A)
    (h : isValList x = none → ReductsIncl C' (stepExprlist ge ox e w x m) res) :
    ReductsIncl C' (stepExprlist ge ox e w x m) res := by
  cases hv : isValList x with
  | none => exact h hv
  | some p => exact reductsIncl_listval ge ox e w C' res hv

/-- Closes one step of `step_expr_context`. -/
macro "ctx_step_tac" : tactic => `(tactic| (
  intro hv
  simp only [stepExpr, hv]
  first
  | exact reductsIncl_incontext _ _
  | exact reductsIncl_incontext2_left _ _ _ _
  | exact reductsIncl_incontext2_right _ _ _ _
  | (split
     · next h1 h2 => simp_all
     · first
       | exact reductsIncl_incontext2_left _ _ _ _
       | exact reductsIncl_incontext2_right _ _ _ _)))

mutual
/-- `Cexec.step_expr_context` -/
theorem step_expr_context {from_ : Csem.Kind} : ∀ {to C}, Csem.Context from_ to C →
    ∀ a m, ReductsIncl C (stepExpr ge ox e w from_ a m) (stepExpr ge ox e w to (C a) m)
  | _, _, .top _, _, _ => fun _ _ h => h
  | _, _, .deref _ C ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ederef x ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .field _ C f ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Efield x f ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .rvalof _ C ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Evalof x ty) (step_expr_context hC a m)
        (reductsIncl_stepLV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .addrof _ C ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eaddrof x ty) (step_expr_context hC a m)
        (reductsIncl_stepLV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .unop _ C op ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eunop op x ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .binop_left _ C op e2 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ebinop op x e2 ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .binop_right _ C op e1 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ebinop op e1 x ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .cast _ C ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ecast x ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .seqand _ C r2 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eseqand x r2 ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .seqor _ C r2 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eseqor x r2 ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .condition _ C r2 r3 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Econdition x r2 r3 ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .assign_left _ C e2 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eassign x e2 ty) (step_expr_context hC a m)
        (reductsIncl_stepLV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .assign_right _ C e1 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eassign e1 x ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .assignop_left _ C op e2 tyres ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eassignop op x e2 tyres ty) (step_expr_context hC a m)
        (reductsIncl_stepLV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .assignop_right _ C op e1 tyres ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eassignop op e1 x tyres ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .postincr _ C id ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Epostincr id x ty) (step_expr_context hC a m)
        (reductsIncl_stepLV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .call_left _ C el ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ecall x el ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .comma _ C e2 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ecomma x e2 ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .paren _ C tycast ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Eparen x tycast ty) (step_expr_context hC a m)
        (reductsIncl_stepRV ge ox e w _ _ (by ctx_step_tac))
  | _, _, .call_right _ C e1 ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ecall e1 x ty) (step_exprlist_context hC a m)
        (reductsIncl_stepList ge ox e w _ _ (by ctx_step_tac))
  | _, _, .builtin _ C ef tyargs ty hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.Expr.Ebuiltin ef tyargs x ty) (step_exprlist_context hC a m)
        (reductsIncl_stepList ge ox e w _ _ (by ctx_step_tac))

/-- `Cexec.step_exprlist_context` -/
theorem step_exprlist_context {from_ : Csem.Kind} : ∀ {C}, Csem.ContextList from_ C →
    ∀ a m, ReductsIncl C (stepExpr ge ox e w from_ a m) (stepExprlist ge ox e w (C a) m)
  | _, .head _ C el hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.ExprList.Econs x el) (step_expr_context hC a m)
        (by simp only [stepExprlist]; exact reductsIncl_incontext2_left _ _ _ _)
  | _, .tail _ C e1 hC, a, m =>
      reductsIncl_trans (C' := fun x => Csyntax.ExprList.Econs e1 x) (step_exprlist_context hC a m)
        (by simp only [stepExprlist]; exact reductsIncl_incontext2_right _ _ _ _)
end

/-! ## Completeness, part 2: stuck expressions have a `Stuckred` reduct -/

/-- `Cexec.not_stuckred_imm_safe` -/
theorem not_stuckred_imm_safe (hinj : Genv.SymbInjective ge.genv_genv) (hS : ox.Sound)
    (hC : ox.Complete) {m a k}
    (h : ∀ C, (C, Reduction.Stuckred) ∉ stepExpr ge ox e w k a m) : ImmSafeT ge e w k a m := by
  obtain ⟨A, B⟩ := stepExpr_sound ge ox e w hinj hS hC a k m
  cases hst : stepExpr ge ox e w k a m with
  | nil =>
      have hB := B hst
      cases k with
      | LV =>
          cases a <;> simp [isLoc] at hB
          exact .loc _ _ _ _ _
      | RV =>
          cases a <;> simp [isVal] at hB
          exact .val _ _ _
  | cons p res =>
      obtain ⟨C, rd⟩ := p
      have hmem : (C, rd) ∈ stepExpr ge ox e w k a m := by rw [hst]; exact List.mem_cons_self
      have hns : rd ≠ .Stuckred := by rintro rfl; exact h C hmem
      obtain ⟨a', k', hctx, rfl, hrd⟩ := A C rd hmem
      cases k' <;> cases rd <;> simp only [ReductionOk] at hrd
      · exact .lred _ _ _ _ _ _ hrd hctx
      · exact absurd rfl hns
      · obtain ⟨hr, w', hp⟩ := hrd
        exact .rred _ _ _ _ _ _ _ _ hr hp hctx
      · obtain ⟨hr, rfl⟩ := hrd
        exact .callred _ _ _ _ _ _ _ hr hctx
      · exact absurd rfl hns

/-- `Cexec.not_imm_safe_stuck_red` -/
theorem not_imm_safe_stuck_red (hinj : Genv.SymbInjective ge.genv_genv) (hS : ox.Sound)
    (hC : ox.Complete) {m a k C} (hctx : Csem.Context k .RV C)
    (h : ¬ ImmSafeT ge e w k a m) :
    ∃ C', (C', Reduction.Stuckred) ∈ stepExpr ge ox e w .RV (C a) m := by
  have : ∃ C', (C', Reduction.Stuckred) ∈ stepExpr ge ox e w k a m := by
    refine Classical.byContradiction fun hn => h ?_
    exact not_stuckred_imm_safe ge ox e w hinj hS hC fun C' hm => hn ⟨C', hm⟩
  obtain ⟨C', hin⟩ := this
  exact ⟨fun x => C (C' x), step_expr_context ge ox e w hctx a m C' _ hin⟩

/-! ## `imm_safe_t` versus `imm_safe` -/

/-- `Cexec.imm_safe_imm_safe_t`: an immediately safe expression is immediately
    safe in world `w`, unless it can only reduce by emitting events that `w`
    rejects. -/
theorem imm_safe_imm_safe_t {k a m} (h : Csem.ImmSafe ge e k a m) :
    ImmSafeT ge e w k a m ∨
      ∃ C a1 t a1' m', Csem.Context .RV k C ∧ a = C a1 ∧ Csem.Rred ge a1 m t a1' m' ∧
        ∀ w', ¬ PossibleTrace w t w' := by
  cases h with
  | val => exact .inl (.val _ _ _)
  | loc => exact .inl (.loc _ _ _ _ _)
  | lred _ C e' _ e'' m' hl hctx => exact .inl (.lred _ _ _ _ _ _ hl hctx)
  | rred _ C e' _ t e'' m' hr hctx =>
      by_cases hw : ∃ w', PossibleTrace w t w'
      · obtain ⟨w', hp⟩ := hw
        exact .inl (.rred _ _ _ _ _ _ _ _ hr hp hctx)
      · exact .inr ⟨C, e', t, e'', m', hctx, rfl, hr, fun w' hp => hw ⟨w', hp⟩⟩
  | callred _ C e' _ fd args ty hc hctx => exact .inl (.callred _ _ _ _ _ _ _ hc hctx)

end EXPRS

/-- `Cexec.can_crash_world`: state `S` can make an observable transition whose
    trace world `w` does not accept. -/
def CanCrashWorld (ge : Csem.CGenv) (w : World) (S : Csem.State) : Prop :=
  ∃ t S', Csem.Step ge S t S' ∧ ∀ w', ¬ PossibleTrace w t w'

/-- `Cexec.not_imm_safe_t` -/
theorem not_imm_safe_t (ge : Csem.CGenv) (e : Env) (w : World) {K C a m f k}
    (hctx : Csem.Context K .RV C) (h : ¬ ImmSafeT ge e w K a m) :
    Csem.Step ge (.ExprState f (C a) k e m) E0 .Stuckstate ∨
      CanCrashWorld ge w (.ExprState f (C a) k e m) := by
  by_cases hs : Csem.ImmSafe ge e K a m
  · rcases imm_safe_imm_safe_t ge e w hs with hs' | ⟨C1, a1, t, a1', m', hc1, rfl, hr, hw⟩
    · exact absurd hs' h
    · exact .inr ⟨t, _, .inl (.rred (fun x => C (C1 x)) f a1 k e m t a1' m' hr
        (Cstrategy.context_compose hc1 hctx)), hw⟩
  · exact .inl (.inl (.stuck _ _ _ _ _ _ _ hctx hs))


end Cexec
end CC
