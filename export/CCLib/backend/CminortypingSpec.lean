/-
  Type system for Cminor — port of the relational part of
  `backend/Cminortyping.v` and of the soundness of type inference:
  `wt_expr`, `wt_opt_assign`, `wt_stmt`, `wt_function`, `wt_fundef`,
  `wt_program`; `expect_incr`, `expect_sound`, `type_expr_incr`,
  `type_expr_sound`, `type_exprlist_incr`, `type_exprlist_sound`,
  `type_assign_incr`, `type_assign_sound`, `opt_set_incr`, `opt_set_sound`,
  `type_stmt_incr`, `type_stmt_sound`, **`type_function_sound`**.

  Difference from Rocq: each `*_incr`/`*_sound` pair is proved as one lemma
  (`*_sound'`) whose conclusion is the conjunction of the two.
-/
import CCLib.backend.Cminortyping
import CCLib.common.UnitypingSound
import CCLib.common.LinkingTheory

namespace CC
namespace Cminortyping

open Cminor UniSolver

section SPEC
variable (env : Typenv) (tret : XType)

/-- `Cminortyping.wt_expr` -/
inductive WtExpr : Cminor.Expr → ATyp → Prop where
  | Evar (id) : WtExpr (.Evar id) (env id)
  | Econst (c) : WtExpr (.Econst c) (typeConstant c)
  | Eunop (op a1 targ1 tres) : typeUnop op = (targ1, tres) → WtExpr a1 targ1 →
      WtExpr (.Eunop op a1) tres
  | Ebinop (op a1 a2 targ1 targ2 tres) : typeBinop op = (targ1, targ2, tres) →
      WtExpr a1 targ1 → WtExpr a2 targ2 → WtExpr (.Ebinop op a1 a2) tres
  | Eload (chunk a1) : WtExpr a1 Tptr → WtExpr (.Eload chunk a1) chunk.typ

/-- `Cminortyping.wt_opt_assign` -/
def WtOptAssign (optid : Option Ident) (ty : XType) : Prop :=
  match optid with
  | some id => ty.proj = env id
  | none => True

/-- `Cminortyping.wt_stmt` -/
inductive WtStmt : Cminor.Stmt → Prop where
  | Sskip : WtStmt .Sskip
  | Sassign (id a) : WtExpr env a (env id) → WtStmt (.Sassign id a)
  | Sstore (chunk a1 a2) : WtExpr env a1 Tptr → WtExpr env a2 chunk.typ →
      WtStmt (.Sstore chunk a1 a2)
  | Scall (optid sg a1 al) : WtExpr env a1 Tptr → ListForall2 (WtExpr env) al (projSigArgs sg) →
      WtOptAssign env optid sg.sig_res → WtStmt (.Scall optid sg a1 al)
  | Stailcall (sg a1 al) : WtExpr env a1 Tptr → ListForall2 (WtExpr env) al (projSigArgs sg) →
      sg.sig_res = tret → WtStmt (.Stailcall sg a1 al)
  | Sbuiltin (optid ef al) : ListForall2 (WtExpr env) al (projSigArgs ef.sig) →
      WtOptAssign env optid ef.sig.sig_res → WtStmt (.Sbuiltin optid ef al)
  | Sseq (s1 s2) : WtStmt s1 → WtStmt s2 → WtStmt (.Sseq s1 s2)
  | Sifthenelse (a s1 s2) : WtExpr env a .Tint → WtStmt s1 → WtStmt s2 →
      WtStmt (.Sifthenelse a s1 s2)
  | Sloop (s1) : WtStmt s1 → WtStmt (.Sloop s1)
  | Sblock (s1) : WtStmt s1 → WtStmt (.Sblock s1)
  | Sexit (n) : WtStmt (.Sexit n)
  | Sswitch (sz : Bool) (a tbl dfl) : WtExpr env a (if sz then .Tlong else .Tint) →
      WtStmt (.Sswitch sz a tbl dfl)
  | Sreturn_none : WtStmt (.Sreturn none)
  | Sreturn_some (a) : WtExpr env a tret.proj → WtStmt (.Sreturn (some a))
  | Slabel (lbl s1) : WtStmt s1 → WtStmt (.Slabel lbl s1)
  | Sgoto (lbl) : WtStmt (.Sgoto lbl)

end SPEC

/-- `Cminortyping.wt_function` -/
structure WtFunction (env : Typenv) (f : Cminor.Function) : Prop where
  type_ok : typeFunction f = .OK env
  params : f.fn_params.map env = projSigArgs f.fn_sig
  body : WtStmt env f.fn_sig.sig_res f.fn_body

/-- `Cminortyping.wt_fundef` -/
inductive WtFundef : Cminor.Fundef → Prop where
  | internal (env f) : WtFunction env f → WtFundef (.Internal f)
  | external (ef) : WtFundef (.External ef)

/-- `Cminortyping.wt_program` -/
def WtProgram (p : Cminor.Program) : Prop :=
  ∀ i f, (i, GlobDef.Gfun f) ∈ p.prog_defs → WtFundef f

/-! ## Soundness of type inference -/

theorem expect_ok {e : STypenv} {t1 t2 : ATyp} {e' : STypenv} (h : expect e t1 t2 = .OK e') :
    t1 = t2 ∧ e' = e := by
  unfold expect at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · cases h

/-- `Cminortyping.expect_incr` -/
theorem expect_incr {te : Typenv} {e : STypenv} {t1 t2 : ATyp} {e' : STypenv}
    (h : expect e t1 t2 = .OK e') (hs : Satisf te e') : Satisf te e := by
  obtain ⟨_, rfl⟩ := expect_ok h; exact hs

/-- `Cminortyping.expect_sound` -/
theorem expect_sound {e : STypenv} {t1 t2 : ATyp} {e' : STypenv}
    (h : expect e t1 t2 = .OK e') : t1 = t2 := (expect_ok h).1

/-- `type_expr_incr` and `type_expr_sound` -/
theorem typeExpr_sound' (te : Typenv) :
    ∀ (a : Cminor.Expr) {t : ATyp} {e e' : STypenv},
    typeExpr e a t = .OK e' → Satisf te e' → Satisf te e ∧ WtExpr te a t
  | .Evar id, t, e, e', h, hs => by
    simp only [typeExpr] at h
    refine ⟨set_incr h hs, ?_⟩
    rw [← set_sound h hs]; exact .Evar id
  | .Econst c, t, e, e', h, hs => by
    simp only [typeExpr] at h
    obtain ⟨rfl, rfl⟩ := expect_ok h
    exact ⟨hs, .Econst c⟩
  | .Eunop op a1, t, e, e', h, hs => by
    rcases hu : typeUnop op with ⟨targ1, tres⟩
    simp only [typeExpr, hu] at h
    split at h
    · next e1 h1 =>
      obtain ⟨rfl, rfl⟩ := expect_ok h
      obtain ⟨A, B⟩ := typeExpr_sound' te a1 h1 hs
      exact ⟨A, .Eunop op a1 targ1 tres hu B⟩
    · cases h
  | .Ebinop op a1 a2, t, e, e', h, hs => by
    rcases hb : typeBinop op with ⟨targ1, targ2, tres⟩
    simp only [typeExpr, hb] at h
    split at h
    · next e1 h1 =>
      split at h
      · next e2 h2 =>
        obtain ⟨rfl, rfl⟩ := expect_ok h
        obtain ⟨A2, B2⟩ := typeExpr_sound' te a2 h2 hs
        obtain ⟨A1, B1⟩ := typeExpr_sound' te a1 h1 A2
        exact ⟨A1, .Ebinop op a1 a2 targ1 targ2 tres hb B1 B2⟩
      · cases h
    · cases h
  | .Eload chunk a1, t, e, e', h, hs => by
    simp only [typeExpr] at h
    split at h
    · next e1 h1 =>
      obtain ⟨rfl, rfl⟩ := expect_ok h
      obtain ⟨A, B⟩ := typeExpr_sound' te a1 h1 hs
      exact ⟨A, .Eload chunk a1 B⟩
    · cases h

/-- `Cminortyping.type_expr_incr` -/
theorem typeExpr_incr {te : Typenv} {a : Cminor.Expr} {t : ATyp} {e e' : STypenv}
    (h : typeExpr e a t = .OK e') (hs : Satisf te e') : Satisf te e :=
  (typeExpr_sound' te a h hs).1

/-- `Cminortyping.type_expr_sound` -/
theorem typeExpr_sound {te : Typenv} {a : Cminor.Expr} {t : ATyp} {e e' : STypenv}
    (h : typeExpr e a t = .OK e') (hs : Satisf te e') : WtExpr te a t :=
  (typeExpr_sound' te a h hs).2

/-- `type_exprlist_incr` and `type_exprlist_sound` -/
theorem typeExprlist_sound' (te : Typenv) :
    ∀ (al : List Cminor.Expr) {tl : List ATyp} {e e' : STypenv},
    typeExprlist e al tl = .OK e' → Satisf te e' → Satisf te e ∧ ListForall2 (WtExpr te) al tl
  | [], [], _, _, h, hs => by cases h; exact ⟨hs, .nil⟩
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | a :: al, t :: tl, e, e', h, hs => by
    simp only [typeExprlist] at h
    split at h
    · next e1 h1 =>
      obtain ⟨A, B⟩ := typeExprlist_sound' te al h hs
      obtain ⟨C, D⟩ := typeExpr_sound' te a h1 A
      exact ⟨C, .cons D B⟩
    · cases h

/-- `Cminortyping.type_exprlist_incr` -/
theorem typeExprlist_incr {te : Typenv} {al : List Cminor.Expr} {tl : List ATyp} {e e' : STypenv}
    (h : typeExprlist e al tl = .OK e') (hs : Satisf te e') : Satisf te e :=
  (typeExprlist_sound' te al h hs).1

/-- `Cminortyping.type_exprlist_sound` -/
theorem typeExprlist_sound {te : Typenv} {al : List Cminor.Expr} {tl : List ATyp}
    {e e' : STypenv} (h : typeExprlist e al tl = .OK e') (hs : Satisf te e') :
    ListForall2 (WtExpr te) al tl :=
  (typeExprlist_sound' te al h hs).2

/-- `type_assign_incr` and `type_assign_sound` -/
theorem typeAssign_sound' {te : Typenv} {id : Ident} {a : Cminor.Expr} {e e' : STypenv}
    (h : typeAssign e id a = .OK e') (hs : Satisf te e') :
    Satisf te e ∧ WtExpr te a (te id) := by
  cases a with
  | Evar id' =>
    simp only [typeAssign] at h
    split at h
    · next ch e1 hm =>
      cases h
      refine ⟨move_incr hm hs, ?_⟩
      rw [move_sound hm hs]; exact .Evar id'
    · cases h
  | Econst c =>
    simp only [typeAssign] at h
    refine ⟨set_incr h hs, ?_⟩
    rw [set_sound h hs]; exact .Econst c
  | Eunop op a1 =>
    rcases hu : typeUnop op with ⟨targ1, tres⟩
    simp only [typeAssign, hu] at h
    split at h
    · next e1 h1 =>
      have A := set_incr h hs
      obtain ⟨B, C⟩ := typeExpr_sound' te a1 h1 A
      refine ⟨B, ?_⟩
      rw [set_sound h hs]; exact .Eunop op a1 targ1 tres hu C
    · cases h
  | Ebinop op a1 a2 =>
    rcases hb : typeBinop op with ⟨targ1, targ2, tres⟩
    simp only [typeAssign, hb] at h
    split at h
    · next e1 h1 =>
      split at h
      · next e2 h2 =>
        have A := set_incr h hs
        obtain ⟨B2, C2⟩ := typeExpr_sound' te a2 h2 A
        obtain ⟨B1, C1⟩ := typeExpr_sound' te a1 h1 B2
        refine ⟨B1, ?_⟩
        rw [set_sound h hs]; exact .Ebinop op a1 a2 targ1 targ2 tres hb C1 C2
      · cases h
    · cases h
  | Eload chunk a1 =>
    simp only [typeAssign] at h
    split at h
    · next e1 h1 =>
      have A := set_incr h hs
      obtain ⟨B, C⟩ := typeExpr_sound' te a1 h1 A
      refine ⟨B, ?_⟩
      rw [set_sound h hs]; exact .Eload chunk a1 C
    · cases h

/-- `Cminortyping.type_assign_incr` -/
theorem typeAssign_incr {te : Typenv} {id : Ident} {a : Cminor.Expr} {e e' : STypenv}
    (h : typeAssign e id a = .OK e') (hs : Satisf te e') : Satisf te e :=
  (typeAssign_sound' h hs).1

/-- `Cminortyping.type_assign_sound` -/
theorem typeAssign_sound {te : Typenv} {id : Ident} {a : Cminor.Expr} {e e' : STypenv}
    (h : typeAssign e id a = .OK e') (hs : Satisf te e') : WtExpr te a (te id) :=
  (typeAssign_sound' h hs).2

/-- `Cminortyping.opt_set_incr` -/
theorem optSet_incr {te : Typenv} {optid : Option Ident} {ty : ATyp} {e e' : STypenv}
    (h : optSet e optid ty = .OK e') (hs : Satisf te e') : Satisf te e := by
  cases optid with
  | none => cases h; exact hs
  | some id => exact set_incr h hs

/-- `Cminortyping.opt_set_sound` -/
theorem optSet_sound {te : Typenv} {optid : Option Ident} {sg : Signature} {e e' : STypenv}
    (h : optSet e optid (projSigRes sg) = .OK e') (hs : Satisf te e') :
    WtOptAssign te optid sg.sig_res := by
  cases optid with
  | none => trivial
  | some id => exact (set_sound h hs).symm

/-- `type_stmt_incr` and `type_stmt_sound` -/
theorem typeStmt_sound' (te : Typenv) (tret : XType) :
    ∀ (s : Cminor.Stmt) {e e' : STypenv},
    typeStmt tret e s = .OK e' → Satisf te e' → Satisf te e ∧ WtStmt te tret s
  | .Sskip, _, _, h, hs => by cases h; exact ⟨hs, .Sskip⟩
  | .Sassign id a, _, _, h, hs => by
    simp only [typeStmt] at h
    obtain ⟨A, B⟩ := typeAssign_sound' h hs
    exact ⟨A, .Sassign id a B⟩
  | .Sstore chunk a1 a2, _, _, h, hs => by
    simp only [typeStmt] at h
    split at h
    · next e1 h1 =>
      obtain ⟨A, B⟩ := typeExpr_sound' te a2 h hs
      obtain ⟨C, D⟩ := typeExpr_sound' te a1 h1 A
      exact ⟨C, .Sstore chunk a1 a2 D B⟩
    · cases h
  | .Scall optid sg fn args, _, _, h, hs => by
    simp only [typeStmt] at h
    split at h
    · next e1 h1 =>
      split at h
      · next e2 h2 =>
        have A := optSet_incr h hs
        obtain ⟨B, C⟩ := typeExprlist_sound' te args h2 A
        obtain ⟨D, E⟩ := typeExpr_sound' te fn h1 B
        exact ⟨D, .Scall optid sg fn args E C (optSet_sound h hs)⟩
      · cases h
    · cases h
  | .Stailcall sg fn args, _, _, h, hs => by
    simp only [typeStmt] at h
    split at h
    · next hres =>
      split at h
      · next e1 h1 =>
        obtain ⟨B, C⟩ := typeExprlist_sound' te args h hs
        obtain ⟨D, E⟩ := typeExpr_sound' te fn h1 B
        exact ⟨D, .Stailcall sg fn args E C hres⟩
      · cases h
    · cases h
  | .Sbuiltin optid ef args, _, _, h, hs => by
    simp only [typeStmt] at h
    split at h
    · next e1 h1 =>
      have A := optSet_incr h hs
      obtain ⟨B, C⟩ := typeExprlist_sound' te args h1 A
      exact ⟨B, .Sbuiltin optid ef args C (optSet_sound h hs)⟩
    · cases h
  | .Sseq s1 s2, _, _, h, hs => by
    simp only [typeStmt] at h
    split at h
    · next e1 h1 =>
      obtain ⟨A, B⟩ := typeStmt_sound' te tret s2 h hs
      obtain ⟨C, D⟩ := typeStmt_sound' te tret s1 h1 A
      exact ⟨C, .Sseq s1 s2 D B⟩
    · cases h
  | .Sifthenelse a s1 s2, _, _, h, hs => by
    simp only [typeStmt] at h
    split at h
    · next e1 h1 =>
      split at h
      · next e2 h2 =>
        obtain ⟨A, B⟩ := typeStmt_sound' te tret s2 h hs
        obtain ⟨C, D⟩ := typeStmt_sound' te tret s1 h2 A
        obtain ⟨E, F⟩ := typeExpr_sound' te a h1 C
        exact ⟨E, .Sifthenelse a s1 s2 F D B⟩
      · cases h
    · cases h
  | .Sloop s1, _, _, h, hs => by
    simp only [typeStmt] at h
    obtain ⟨A, B⟩ := typeStmt_sound' te tret s1 h hs
    exact ⟨A, .Sloop s1 B⟩
  | .Sblock s1, _, _, h, hs => by
    simp only [typeStmt] at h
    obtain ⟨A, B⟩ := typeStmt_sound' te tret s1 h hs
    exact ⟨A, .Sblock s1 B⟩
  | .Sexit n, _, _, h, hs => by cases h; exact ⟨hs, .Sexit n⟩
  | .Sswitch sz a tbl dfl, _, _, h, hs => by
    simp only [typeStmt] at h
    obtain ⟨A, B⟩ := typeExpr_sound' te a h hs
    exact ⟨A, .Sswitch sz a tbl dfl B⟩
  | .Sreturn none, _, _, h, hs => by cases h; exact ⟨hs, .Sreturn_none⟩
  | .Sreturn (some a), _, _, h, hs => by
    simp only [typeStmt] at h
    obtain ⟨A, B⟩ := typeExpr_sound' te a h hs
    exact ⟨A, .Sreturn_some a B⟩
  | .Slabel lbl s1, _, _, h, hs => by
    simp only [typeStmt] at h
    obtain ⟨A, B⟩ := typeStmt_sound' te tret s1 h hs
    exact ⟨A, .Slabel lbl s1 B⟩
  | .Sgoto lbl, _, _, h, hs => by cases h; exact ⟨hs, .Sgoto lbl⟩

/-- `Cminortyping.type_stmt_incr` -/
theorem typeStmt_incr {te : Typenv} {tret : XType} {s : Cminor.Stmt} {e e' : STypenv}
    (h : typeStmt tret e s = .OK e') (hs : Satisf te e') : Satisf te e :=
  (typeStmt_sound' te tret s h hs).1

/-- `Cminortyping.type_stmt_sound` -/
theorem typeStmt_sound {te : Typenv} {tret : XType} {s : Cminor.Stmt} {e e' : STypenv}
    (h : typeStmt tret e s = .OK e') (hs : Satisf te e') : WtStmt te tret s :=
  (typeStmt_sound' te tret s h hs).2

/-- `Cminortyping.type_function_sound` -/
theorem typeFunction_sound {f : Cminor.Function} {env : Typenv} (h : typeFunction f = .OK env) :
    WtFunction env f := by
  have h0 := h
  unfold typeFunction at h
  split at h
  · next e1 h1 =>
    split at h
    · next e2 h2 =>
      have S : Satisf env e2 := solve_sound h
      obtain ⟨A, B⟩ := typeStmt_sound' env _ _ h2 S
      exact ⟨h0, set_list_sound h1 A, B⟩
    · cases h
  · cases h

end Cminortyping
end CC
