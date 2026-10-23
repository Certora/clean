/-
  Soundness of the CompCert C type-checker — port of the section
  "Soundness of the smart constructors" of `cfrontend/Ctyping.v`:
  `check_cast_sound`, …, `type_conditional_cast`, the soundness of each smart
  constructor (`evar_sound`, …, `sswitch_sound`), `retype_expr_sound`,
  `retype_stmt_sound`, `retype_function_sound`, `retype_fundef_sound` and
  `typecheck_program_sound`.

  Differences from Rocq: the hypotheses of `type_combine_cast` are phrased with
  the auxiliary predicate `NotArrayOrFunction`; the finite case analyses over
  integer/float sizes and signedness are done by the local tactic
  `cases_sizes` (a recursive `cases` on every hypothesis of these types).
-/
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Cases
import CCLib.cfrontend.Ctyping

namespace CC
namespace Ctyping

open Csyntax (typeof)

open Lean Meta Elab Tactic in
/-- Recursively case-split every hypothesis of type `IntSize`, `Signedness` or
    `FloatSize`. -/
partial def casesSizesCore (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isConstOf ``CC.IntSize || ty.isConstOf ``CC.Signedness || ty.isConstOf ``CC.FloatSize then
      let subgoals ← g.cases d.fvarId
      let mut res := []
      for s in subgoals do
        res := res ++ (← casesSizesCore s.mvarId)
      return res
  return [g]

open Lean Elab Tactic in
/-- `cases_sizes`: see `casesSizesCore`. -/
elab "cases_sizes" : tactic => liftMetaTactic casesSizesCore


@[simp] theorem Res.bind_eq_OK {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (bind x f = Res.OK b) ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]


theorem checkCast_sound {t1 t2 : Ty} {x} (h : checkCast t1 t2 = .OK x) : WtCast t1 t2 := by
  unfold checkCast at h; unfold WtCast
  split at h <;> simp_all

theorem checkBool_sound {t : Ty} {x} (h : checkBool t = .OK x) : WtBool t := by
  unfold checkBool at h; unfold WtBool
  split at h <;> simp_all

theorem checkArguments_sound :
    ∀ (el : Csyntax.ExprList) (tl : List Ty) x, checkArguments el tl = .OK x →
      WtArguments el tl
  | .Enil, [], _, _ => .nil
  | .Enil, _ :: _, _, h => by simp [checkArguments] at h
  | .Econs a al, [], _, h => by
      cases hs : strict
      · exact .extra a al hs
      · simp [checkArguments, hs] at h
  | .Econs a al, ty :: tyl, _, h => by
      simp only [checkArguments, Res.bind_eq_OK] at h
      obtain ⟨u, h1, h2⟩ := h
      exact .cons _ _ _ _ (checkCast_sound h1) (checkArguments_sound al tyl _ h2)

theorem checkRval_sound {a : Csyntax.Expr} {x} (h : checkRval a = .OK x) : exprKind a = .RV := by
  cases a <;> simp_all [checkRval, exprKind]

theorem checkLval_sound {a : Csyntax.Expr} {x} (h : checkLval a = .OK x) : exprKind a = .LV := by
  cases a <;> simp_all [checkLval, exprKind]

theorem wtBool_cast {ty : Ty} (h : WtBool ty) : WtCast ty type_bool := by
  unfold WtBool Cop.classifyBool at h; unfold WtCast
  cases ty <;> cases_sizes <;> simp_all [typeconv, removeAttributes, tattr, Cop.classifyCast, type_bool]

theorem wtCast_int (i1 s1 a1 i2 s2 a2) : WtCast (.Tint i1 s1 a1) (.Tint i2 s2 a2) := by
  unfold WtCast; cases i2 <;> simp [Cop.classifyCast]

/-- The side condition of `type_combine_cast`. -/
def NotArrayOrFunction (t : Ty) : Prop :=
  match t with
  | .Tarray _ _ _ => False
  | .Tfunction _ _ _ => False
  | _ => True

theorem typeconv_cast {t1 t2 : Ty} (h : WtCast (typeconv t1) t2) : WtCast t1 t2 := by
  unfold WtCast at *
  cases t1 <;> cases t2 <;> cases_sizes <;> simp_all [typeconv, removeAttributes, tattr, tint, Cop.classifyCast]

theorem binarithType_cast {t1 t2 : Ty} {m t} (h : binarithType t1 t2 m = .OK t) :
    WtCast t1 t ∧ WtCast t2 t := by
  unfold binarithType at h; unfold WtCast
  cases t1 <;> cases t2 <;> cases_sizes <;> simp [Cop.classifyBinarith] at h <;> subst h <;> simp [Cop.classifyCast]

theorem typeCombine_cast {t1 t2 t : Ty} (h : typeCombine t1 t2 = .OK t)
    (h1 : NotArrayOrFunction t1) (h2 : NotArrayOrFunction t2) :
    WtCast t1 t ∧ WtCast t2 t := by
  cases t1 <;> cases t2 <;> simp [typeCombine, NotArrayOrFunction] at h h1 h2
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; simp [WtCast, Cop.classifyCast])
    | (split at h <;> simp at h; obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; subst h; cases_sizes <;> simp [WtCast, Cop.classifyCast])
    | (split at h <;> simp at h; subst_vars; cases_sizes <;> simp [WtCast, Cop.classifyCast])
    | (subst h; simp [WtCast, Cop.classifyCast])

theorem typeConditional_cast {t1 t2 t : Ty} (h : typeConditional t1 t2 = .OK t) :
    WtCast t1 t ∧ WtCast t2 t := by
  have A : ∀ x, NotArrayOrFunction (typeconv x) := by
    intro x; cases x <;> cases_sizes <;> simp [NotArrayOrFunction, typeconv, removeAttributes, tattr, tint]
  have D : typeCombine (typeconv t1) (typeconv t2) = .OK t → WtCast t1 t ∧ WtCast t2 t := by
    intro hc
    have := typeCombine_cast hc (A t1) (A t2)
    exact ⟨typeconv_cast this.1, typeconv_cast this.2⟩
  unfold typeConditional at h
  split at h
  all_goals first
    | exact binarithType_cast h
    | exact D h
    | (simp at h; subst h; refine ⟨typeconv_cast ?_, typeconv_cast ?_⟩ <;>
        simp [WtCast, Cop.classifyCast, *])

section SOUNDNESS_CONSTRUCTORS

variable {ce : CompositeEnv} {e : Typenv} {rt : Ty}

theorem checkRval_wt {a : Csyntax.Expr} {x} (hw : WtExpr ce e a) (h : checkRval a = .OK x) :
    WtRvalue ce e a := by
  have := checkRval_sound h
  unfold WtExpr at hw; rw [this] at hw; exact hw

theorem checkLval_wt {a : Csyntax.Expr} {x} (hw : WtExpr ce e a) (h : checkLval a = .OK x) :
    WtLvalue ce e a := by
  have := checkLval_sound h
  unfold WtExpr at hw; rw [this] at hw; exact hw

/-- An r-value is well typed as an expression. -/
theorem wtExpr_of_rvalue {a : Csyntax.Expr} (hk : exprKind a = .RV) (h : WtRvalue ce e a) :
    WtExpr ce e a := by
  unfold WtExpr; rw [hk]; exact h

/-- An l-value is well typed as an expression. -/
theorem wtExpr_of_lvalue {a : Csyntax.Expr} (hk : exprKind a = .LV) (h : WtLvalue ce e a) :
    WtExpr ce e a := by
  unfold WtExpr; rw [hk]; exact h

theorem evar_sound {x a} (h : evar e x = .OK a) : WtExpr ce e a := by
  unfold evar at h
  split at h <;> simp at h
  subst h
  exact wtExpr_of_lvalue rfl (.var _ _ ‹_›)

theorem ederef_sound {r a} (h : ederef r = .OK a) (hr : WtExpr ce e r) : WtExpr ce e a := by
  simp only [ederef, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, h1, ty, h2, rfl⟩ := h
  exact wtExpr_of_lvalue rfl (.deref _ _ (checkRval_wt hr h1) h2)

theorem efield_sound {r f a} (h : efield ce r f = .OK a) (hr : WtExpr ce e r) : WtExpr ce e a := by
  simp only [efield, Res.bind_eq_OK] at h
  obtain ⟨_, h1, h⟩ := h
  have hr' := checkRval_wt hr h1
  split at h <;> try simp at h
  all_goals
    split at h <;> simp only [Res.bind_eq_OK, Res.OK.injEq, reduceCtorEq] at h
    obtain ⟨ty, h2, rfl⟩ := h
    first
      | exact wtExpr_of_lvalue rfl (.field _ _ _ _ _ _ hr' (.inl ‹_›) ‹_› h2)
      | exact wtExpr_of_lvalue rfl (.field _ _ _ _ _ _ hr' (.inr ‹_›) ‹_› h2)

theorem econstInt_sound (n sg) : WtExpr ce e (econstInt n sg) :=
  wtExpr_of_rvalue rfl (.val _ _ (.int _ _ _ _ trivial))

theorem econstPtrInt_sound (n ty) : WtExpr ce e (econstPtrInt n ty) := by
  unfold econstPtrInt
  cases hp : Archi.ptr64
  · exact wtExpr_of_rvalue rfl (.val _ _ (.int_pointer _ _ _ hp))
  · exact wtExpr_of_rvalue rfl (.val _ _ (.long_pointer _ _ _ hp))

theorem econstLong_sound (n sg) : WtExpr ce e (econstLong n sg) :=
  wtExpr_of_rvalue rfl (.val _ _ (.long _ _ _))

theorem econstPtrLong_sound (n ty) : WtExpr ce e (econstPtrLong n ty) := by
  unfold econstPtrLong
  cases hp : Archi.ptr64
  · exact wtExpr_of_rvalue rfl (.val _ _ (.int_pointer _ _ _ hp))
  · exact wtExpr_of_rvalue rfl (.val _ _ (.long_pointer _ _ _ hp))

theorem econstFloat_sound (n) : WtExpr ce e (econstFloat n) :=
  wtExpr_of_rvalue rfl (.val _ _ (.float _ _))

theorem econstSingle_sound (n) : WtExpr ce e (econstSingle n) :=
  wtExpr_of_rvalue rfl (.val _ _ (.single _ _))

theorem evalof_sound {l a} (h : evalof l = .OK a) (hl : WtExpr ce e l) : WtExpr ce e a := by
  simp only [evalof, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, h1, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.valof _ (checkLval_wt hl h1))

theorem eaddrof_sound {l a} (h : eaddrof l = .OK a) (hl : WtExpr ce e l) : WtExpr ce e a := by
  simp only [eaddrof, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, h1, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.addrof _ (checkLval_wt hl h1))

theorem eunop_sound {op r a} (h : eunop op r = .OK a) (hr : WtExpr ce e r) : WtExpr ce e a := by
  simp only [eunop, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, h1, ty, h2, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.unop _ _ _ (checkRval_wt hr h1) h2)

theorem ebinop_sound {op r1 r2 a} (h : ebinop op r1 r2 = .OK a)
    (h1 : WtExpr ce e r1) (h2 : WtExpr ce e r2) : WtExpr ce e a := by
  simp only [ebinop, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, ty, c3, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.binop _ _ _ _ (checkRval_wt h1 c1) (checkRval_wt h2 c2) c3)

theorem ecast_sound {ty r a} (h : ecast ty r = .OK a) (hr : WtExpr ce e r) : WtExpr ce e a := by
  simp only [ecast, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.cast _ _ (checkRval_wt hr c1) (checkCast_sound c2))

theorem eseqand_sound {r1 r2 a} (h : eseqand r1 r2 = .OK a)
    (h1 : WtExpr ce e r1) (h2 : WtExpr ce e r2) : WtExpr ce e a := by
  simp only [eseqand, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, _, c3, _, c4, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.seqand _ _ (checkRval_wt h1 c1) (checkRval_wt h2 c2)
    (checkBool_sound c3) (checkBool_sound c4))

theorem eseqor_sound {r1 r2 a} (h : eseqor r1 r2 = .OK a)
    (h1 : WtExpr ce e r1) (h2 : WtExpr ce e r2) : WtExpr ce e a := by
  simp only [eseqor, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, _, c3, _, c4, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.seqor _ _ (checkRval_wt h1 c1) (checkRval_wt h2 c2)
    (checkBool_sound c3) (checkBool_sound c4))

theorem econdition_sound {r1 r2 r3 a} (h : econdition r1 r2 r3 = .OK a)
    (h1 : WtExpr ce e r1) (h2 : WtExpr ce e r2) (h3 : WtExpr ce e r3) : WtExpr ce e a := by
  simp only [econdition, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, _, c3, _, c4, ty, c5, rfl⟩ := h
  have := typeConditional_cast c5
  exact wtExpr_of_rvalue rfl (.condition _ _ _ _ (checkRval_wt h1 c1) (checkRval_wt h2 c2)
    (checkRval_wt h3 c3) (checkBool_sound c4) this.1 this.2)

theorem econdition'_sound {r1 r2 r3 ty a} (h : econdition' r1 r2 r3 ty = .OK a)
    (h1 : WtExpr ce e r1) (h2 : WtExpr ce e r2) (h3 : WtExpr ce e r3) : WtExpr ce e a := by
  simp only [econdition', Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, _, c3, _, c4, _, c5, _, c6, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.condition _ _ _ _ (checkRval_wt h1 c1) (checkRval_wt h2 c2)
    (checkRval_wt h3 c3) (checkBool_sound c4) (checkCast_sound c5) (checkCast_sound c6))

theorem esizeof_sound (ty) : WtExpr ce e (esizeof ty) := wtExpr_of_rvalue rfl (.sizeof _)

theorem ealignof_sound (ty) : WtExpr ce e (ealignof ty) := wtExpr_of_rvalue rfl (.alignof _)

theorem eassign_sound {l r a} (h : eassign l r = .OK a)
    (hl : WtExpr ce e l) (hr : WtExpr ce e r) : WtExpr ce e a := by
  simp only [eassign, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, _, c3, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.assign _ _ (checkLval_wt hl c1) (checkRval_wt hr c2)
    (checkCast_sound c3))

theorem eassignop_sound {op l r a} (h : eassignop op l r = .OK a)
    (hl : WtExpr ce e l) (hr : WtExpr ce e r) : WtExpr ce e a := by
  simp only [eassignop, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, ty, c3, _, c4, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.assignop _ _ _ _ (checkLval_wt hl c1) (checkRval_wt hr c2) c3
    (checkCast_sound c4))

theorem epostincrdecr_sound {id l a} (h : epostincrdecr id l = .OK a) (hl : WtExpr ce e l) :
    WtExpr ce e a := by
  simp only [epostincrdecr, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, ty, c2, _, c3, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.postincr _ _ _ (checkLval_wt hl c1) c2 (checkCast_sound c3))

theorem ecomma_sound {r1 r2 a} (h : ecomma r1 r2 = .OK a)
    (h1 : WtExpr ce e r1) (h2 : WtExpr ce e r2) : WtExpr ce e a := by
  simp only [ecomma, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.comma _ _ (checkRval_wt h1 c1) (checkRval_wt h2 c2))

theorem ecall_sound {fn args a} (h : ecall fn args = .OK a)
    (hf : WtExpr ce e fn) (ha : WtExprlist ce e args) : WtExpr ce e a := by
  simp only [ecall, Res.bind_eq_OK] at h
  obtain ⟨_, c1, _, _, h⟩ := h
  split at h <;> simp only [Res.bind_eq_OK, Res.OK.injEq, reduceCtorEq] at h
  obtain ⟨_, c3, rfl⟩ := h
  exact wtExpr_of_rvalue rfl (.call _ _ _ _ _ (checkRval_wt hf c1) ha ‹_›
    (checkArguments_sound _ _ _ c3))

theorem ebuiltin_sound {ef tyargs args tyres a} (h : ebuiltin ef tyargs args tyres = .OK a)
    (ha : WtExprlist ce e args) : WtExpr ce e a := by
  simp only [ebuiltin, Res.bind_eq_OK] at h
  obtain ⟨_, _, _, c2, h⟩ := h
  split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h
  subst h
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact wtExpr_of_rvalue rfl (.builtin _ _ _ _ ha (checkArguments_sound _ _ _ c2) (.inl hc))

theorem eselection_sound {r1 r2 r3 a} (h : eselection r1 r2 r3 = .OK a)
    (h1 : WtExpr ce e r1) (h2 : WtExpr ce e r2) (h3 : WtExpr ce e r3) : WtExpr ce e a := by
  simp only [eselection, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, _, c3, _, c4, ty, c5, rfl⟩ := h
  have := typeConditional_cast c5
  have w1 := checkRval_wt h1 c1
  have w2 := checkRval_wt h2 c2
  have w3 := checkRval_wt h3 c3
  exact wtExpr_of_rvalue rfl (.builtin _ _ _ _ (.cons _ _ w1 (.cons _ _ w2 (.cons _ _ w3 .nil)))
    (.cons _ _ _ _ (wtBool_cast (checkBool_sound c4))
      (.cons _ _ _ _ this.1 (.cons _ _ _ _ this.2 .nil)))
    (.inr ⟨rfl, rfl⟩))

theorem sdo_sound {a s} (h : sdo a = .OK s) (ha : WtExpr ce e a) : WtStmt ce e rt s := by
  simp only [sdo, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, rfl⟩ := h
  exact .do_ _ (checkRval_wt ha c1)

theorem sifthenelse_sound {a s1 s2 s} (h : sifthenelse a s1 s2 = .OK s) (ha : WtExpr ce e a)
    (h1 : WtStmt ce e rt s1) (h2 : WtStmt ce e rt s2) : WtStmt ce e rt s := by
  simp only [sifthenelse, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, rfl⟩ := h
  exact .ifthenelse _ _ _ (checkRval_wt ha c1) h1 h2 (checkBool_sound c2)

theorem swhile_sound {a s1 s} (h : swhile a s1 = .OK s) (ha : WtExpr ce e a)
    (h1 : WtStmt ce e rt s1) : WtStmt ce e rt s := by
  simp only [swhile, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, rfl⟩ := h
  exact .while_ _ _ (checkRval_wt ha c1) h1 (checkBool_sound c2)

theorem sdowhile_sound {a s1 s} (h : sdowhile a s1 = .OK s) (ha : WtExpr ce e a)
    (h1 : WtStmt ce e rt s1) : WtStmt ce e rt s := by
  simp only [sdowhile, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, rfl⟩ := h
  exact .dowhile _ _ (checkRval_wt ha c1) h1 (checkBool_sound c2)

theorem sfor_sound {s1 a s2 s3 s} (h : sfor s1 a s2 s3 = .OK s) (h1 : WtStmt ce e rt s1)
    (ha : WtExpr ce e a) (h2 : WtStmt ce e rt s2) (h3 : WtStmt ce e rt s3) :
    WtStmt ce e rt s := by
  simp only [sfor, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, rfl⟩ := h
  exact .for_ _ _ _ _ (checkRval_wt ha c1) h1 h2 h3 (checkBool_sound c2)

theorem sreturn_sound {a s} (h : sreturn rt a = .OK s) (ha : WtExpr ce e a) :
    WtStmt ce e rt s := by
  simp only [sreturn, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨_, c1, _, c2, rfl⟩ := h
  exact .return_some _ (checkRval_wt ha c1) (checkCast_sound c2)

theorem sswitch_sound {a sl s} (h : sswitch a sl = .OK s) (ha : WtExpr ce e a)
    (hl : WtLblstmts ce e rt sl) : WtStmt ce e rt s := by
  simp only [sswitch, Res.bind_eq_OK] at h
  obtain ⟨_, c1, h⟩ := h
  split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h <;> subst h
  · exact .switch _ _ _ _ _ (checkRval_wt ha c1) (.inl ‹_›) hl
  · exact .switch _ _ _ .I32 _ (checkRval_wt ha c1) (.inr ‹_›) hl

mutual
theorem retypeExpr_sound : ∀ (a a' : Csyntax.Expr), retypeExpr ce e a = .OK a' → WtExpr ce e a'
  | .Eval v ty, a', h => by
      cases v <;> cases ty <;> simp only [retypeExpr, Res.OK.injEq, reduceCtorEq] at h <;> subst h
      all_goals first
        | exact econstInt_sound _ _
        | exact econstPtrInt_sound _ _
        | exact econstLong_sound _ _
        | exact econstFloat_sound _
        | exact econstSingle_sound _
  | .Evar x _, a', h => evar_sound (by simpa only [retypeExpr] using h)
  | .Esizeof ty _, a', h => by
      simp only [retypeExpr, Res.OK.injEq] at h; subst h; exact esizeof_sound _
  | .Ealignof ty _, a', h => by
      simp only [retypeExpr, Res.OK.injEq] at h; subst h; exact ealignof_sound _
  | .Eloc _ _ _ _, a', h => by simp [retypeExpr] at h
  | .Eparen _ _ _, a', h => by simp [retypeExpr] at h
  | .Efield r f _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r', h0, hc⟩ := h
      exact efield_sound hc (retypeExpr_sound r _ h0)
  | .Evalof l _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨l', h0, hc⟩ := h
      exact evalof_sound hc (retypeExpr_sound l _ h0)
  | .Ederef r _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r', h0, hc⟩ := h
      exact ederef_sound hc (retypeExpr_sound r _ h0)
  | .Eaddrof l _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨l', h0, hc⟩ := h
      exact eaddrof_sound hc (retypeExpr_sound l _ h0)
  | .Eunop op r _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r', h0, hc⟩ := h
      exact eunop_sound hc (retypeExpr_sound r _ h0)
  | .Ebinop op r1 r2 _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r1', h0, r2', h1, hc⟩ := h
      exact ebinop_sound hc (retypeExpr_sound r1 _ h0) (retypeExpr_sound r2 _ h1)
  | .Ecast r ty, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r', h0, hc⟩ := h
      exact ecast_sound hc (retypeExpr_sound r _ h0)
  | .Eseqand r1 r2 _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r1', h0, r2', h1, hc⟩ := h
      exact eseqand_sound hc (retypeExpr_sound r1 _ h0) (retypeExpr_sound r2 _ h1)
  | .Eseqor r1 r2 _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r1', h0, r2', h1, hc⟩ := h
      exact eseqor_sound hc (retypeExpr_sound r1 _ h0) (retypeExpr_sound r2 _ h1)
  | .Econdition r1 r2 r3 _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r1', h0, r2', h1, r3', h2, hc⟩ := h
      exact econdition_sound hc (retypeExpr_sound r1 _ h0) (retypeExpr_sound r2 _ h1) (retypeExpr_sound r3 _ h2)
  | .Eassign l r _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨l', h0, r', h1, hc⟩ := h
      exact eassign_sound hc (retypeExpr_sound l _ h0) (retypeExpr_sound r _ h1)
  | .Eassignop op l r _ _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨l', h0, r', h1, hc⟩ := h
      exact eassignop_sound hc (retypeExpr_sound l _ h0) (retypeExpr_sound r _ h1)
  | .Epostincr id l _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨l', h0, hc⟩ := h
      exact epostincrdecr_sound hc (retypeExpr_sound l _ h0)
  | .Ecomma r1 r2 _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r1', h0, r2', h1, hc⟩ := h
      exact ecomma_sound hc (retypeExpr_sound r1 _ h0) (retypeExpr_sound r2 _ h1)
  | .Ecall r1 rl _, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨r1', h0, rl', h1, hc⟩ := h
      exact ecall_sound hc (retypeExpr_sound r1 _ h0) (retypeExprlist_sound rl _ h1)
  | .Ebuiltin ef tyargs rl tyres, a', h => by
      simp only [retypeExpr, Res.bind_eq_OK] at h
      obtain ⟨rl', h0, hc⟩ := h
      exact ebuiltin_sound hc (retypeExprlist_sound rl _ h0)

theorem retypeExprlist_sound :
    ∀ (al al' : Csyntax.ExprList), retypeExprlist ce e al = .OK al' → WtExprlist ce e al'
  | .Enil, al', h => by
      simp [retypeExprlist] at h; subst h; exact .nil
  | .Econs a1 al, al', h => by
      simp only [retypeExprlist, Res.bind_eq_OK, Res.OK.injEq] at h
      obtain ⟨a1', h1, al'', h2, _, h3, rfl⟩ := h
      exact .cons _ _ (checkRval_wt (retypeExpr_sound _ _ h1) h3) (retypeExprlist_sound _ _ h2)
end

mutual
theorem retypeStmt_sound :
    ∀ (s s' : Csyntax.Stmt), retypeStmt ce e rt s = .OK s' → WtStmt ce e rt s'
  | .Sskip, s', h => by simp only [retypeStmt, Res.OK.injEq] at h; subst h; exact .skip
  | .Sbreak, s', h => by simp only [retypeStmt, Res.OK.injEq] at h; subst h; exact .break_
  | .Scontinue, s', h => by simp only [retypeStmt, Res.OK.injEq] at h; subst h; exact .continue_
  | .Sgoto _, s', h => by simp only [retypeStmt, Res.OK.injEq] at h; subst h; exact .goto _
  | .Sreturn none, s', h => by
      simp only [retypeStmt, Res.OK.injEq] at h; subst h; exact .return_none
  | .Sreturn (some a), s', h => by
      simp only [retypeStmt, Res.bind_eq_OK] at h
      obtain ⟨a', h0, hc⟩ := h
      exact sreturn_sound hc (retypeExpr_sound a _ h0)
  | .Sdo a, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK] at h
      obtain ⟨a', h0, hc⟩ := h
      exact sdo_sound hc (retypeExpr_sound a _ h0)
  | .Ssequence s1 s2, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK, Res.OK.injEq] at h
      obtain ⟨s1', h1, s2', h2, rfl⟩ := h
      exact .sequence _ _ (retypeStmt_sound s1 _ h1) (retypeStmt_sound s2 _ h2)
  | .Sifthenelse a s1 s2, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK] at h
      obtain ⟨a', h0, s1', h1, s2', h2, hc⟩ := h
      exact sifthenelse_sound hc (retypeExpr_sound a _ h0) (retypeStmt_sound s1 _ h1)
        (retypeStmt_sound s2 _ h2)
  | .Swhile a s1, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK] at h
      obtain ⟨a', h0, s1', h1, hc⟩ := h
      exact swhile_sound hc (retypeExpr_sound a _ h0) (retypeStmt_sound s1 _ h1)
  | .Sdowhile a s1, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK] at h
      obtain ⟨a', h0, s1', h1, hc⟩ := h
      exact sdowhile_sound hc (retypeExpr_sound a _ h0) (retypeStmt_sound s1 _ h1)
  | .Sfor s1 a s2 s3, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK] at h
      obtain ⟨a', h0, s1', h1, s2', h2, s3', h3, hc⟩ := h
      exact sfor_sound hc (retypeStmt_sound s1 _ h1) (retypeExpr_sound a _ h0)
        (retypeStmt_sound s2 _ h2) (retypeStmt_sound s3 _ h3)
  | .Sswitch a sl, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK] at h
      obtain ⟨a', h0, sl', h1, hc⟩ := h
      exact sswitch_sound hc (retypeExpr_sound a _ h0) (retypeLblstmts_sound sl _ h1)
  | .Slabel _ s1, s', h => by
      simp only [retypeStmt, Res.bind_eq_OK, Res.OK.injEq] at h
      obtain ⟨s1', h1, rfl⟩ := h
      exact .label _ _ (retypeStmt_sound s1 _ h1)

theorem retypeLblstmts_sound :
    ∀ (sl sl' : Csyntax.LStmts), retypeLblstmts ce e rt sl = .OK sl' → WtLblstmts ce e rt sl'
  | .LSnil, sl', h => by simp only [retypeLblstmts, Res.OK.injEq] at h; subst h; exact .nil
  | .LScons _ s1 sl, sl', h => by
      simp only [retypeLblstmts, Res.bind_eq_OK, Res.OK.injEq] at h
      obtain ⟨s1', h1, sl'', h2, rfl⟩ := h
      exact .cons _ _ _ (retypeStmt_sound s1 _ h1) (retypeLblstmts_sound sl _ h2)
end

end SOUNDNESS_CONSTRUCTORS

theorem retypeFunction_sound {ce e f f'} (h : retypeFunction ce e f = .OK f') :
    WtFunction ce e f' := by
  simp only [retypeFunction, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨s, h1, rfl⟩ := h
  exact .intro _ (retypeStmt_sound _ _ h1)

theorem retypeFundef_sound {ce e fd fd'} (h : retypeFundef ce e fd = .OK fd') :
    WtFundef ce e fd' := by
  cases fd with
  | Internal f =>
      simp only [retypeFundef, Res.bind_eq_OK, Res.OK.injEq] at h
      obtain ⟨f', h1, rfl⟩ := h
      exact .internal _ (retypeFunction_sound h1)
  | External ef targs tres cc =>
      simp only [retypeFundef, assertion] at h
      split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h
      subst h
      exact .external _ _ _ _ (of_decide_eq_true ‹_›)

/-- Re-typing a function definition does not change its type. -/
theorem retypeFundef_type {ce e fd fd'} (h : retypeFundef ce e fd = .OK fd') :
    Csyntax.typeOfFundef fd' = Csyntax.typeOfFundef fd := by
  cases fd with
  | Internal f =>
      simp only [retypeFundef, retypeFunction, Res.bind_eq_OK, Res.OK.injEq] at h
      obtain ⟨f', ⟨s, _, rfl⟩, rfl⟩ := h
      rfl
  | External ef targs tres cc =>
      simp only [retypeFundef, assertion] at h
      split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h
      subst h; rfl

theorem bindGlobdef_retype {ce e} :
    ∀ (defs defs' : List (Ident × GlobDef Csyntax.FunDef Ty)) (t : Typenv),
      transfGlobdefs (fun _ f => retypeFundef ce e f) (fun _ v => .OK v) defs = .OK defs' →
      bindGlobdef t defs' = bindGlobdef t defs
  | [], defs', t, h => by simp [transfGlobdefs] at h; subst h; rfl
  | (id, .Gfun fd) :: l, defs', t, h => by
      simp only [transfGlobdefs] at h
      split at h <;> try simp at h
      split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h
      subst h
      rename_i fd' hfd _ l' hl
      simp only [bindGlobdef, retypeFundef_type hfd]
      exact bindGlobdef_retype l l' _ hl
  | (id, .Gvar v) :: l, defs', t, h => by
      simp only [transfGlobdefs, transfGlobvar] at h
      split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h
      subst h
      rename_i l' hl
      simp only [bindGlobdef]
      exact bindGlobdef_retype l l' _ hl

theorem mem_retype {ce e} :
    ∀ (defs defs' : List (Ident × GlobDef Csyntax.FunDef Ty)),
      transfGlobdefs (fun _ f => retypeFundef ce e f) (fun _ v => .OK v) defs = .OK defs' →
      ∀ id fd', (id, GlobDef.Gfun fd') ∈ defs' → ∃ fd, retypeFundef ce e fd = .OK fd'
  | [], defs', h, id, fd', hm => by simp [transfGlobdefs] at h; subst h; simp at hm
  | (id0, .Gfun fd) :: l, defs', h, id, fd', hm => by
      simp only [transfGlobdefs] at h
      split at h <;> try simp at h
      split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h
      subst h
      rename_i fd'' hfd _ l' hl
      simp only [List.mem_cons, Prod.mk.injEq, GlobDef.Gfun.injEq] at hm
      rcases hm with ⟨_, rfl⟩ | hm
      · exact ⟨fd, hfd⟩
      · exact mem_retype l l' hl id fd' hm
  | (id0, .Gvar v) :: l, defs', h, id, fd', hm => by
      simp only [transfGlobdefs, transfGlobvar] at h
      split at h <;> simp only [Res.OK.injEq, reduceCtorEq] at h
      subst h
      rename_i l' hl
      simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hm
      exact mem_retype l l' hl id fd' hm

/-- `Ctyping.typecheck_program_sound`: a program accepted by the type-checker
    is well typed. -/
theorem typecheckProgram_sound {p p' : Csyntax.Program} (h : typecheckProgram p = .OK p') :
    WtProgram p' := by
  simp only [typecheckProgram, Res.bind_eq_OK, Res.OK.injEq] at h
  obtain ⟨defs, hd, rfl⟩ := h
  intro id fd hm
  simp only [bindGlobdef_retype _ _ _ hd]
  obtain ⟨fd0, hfd⟩ := mem_retype _ _ hd id fd hm
  exact retypeFundef_sound hfd

end Ctyping
end CC
