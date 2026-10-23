/-
  Correctness of instruction selection for x86-64 (the x86 instance of
  `CCLib/backend/SelectionproofIfconv.lean`) — port of `backend/Selectionproof.v`,
  part 5: if-conversion (`eventually`, `eventually_step`,
  `classify_stmt_sound`, `classify_stmt_wt`, `if_conversion_base_correct`,
  `if_conversion_correct`).

  Difference from Rocq: CompCert's `PTree`s are canonical, so
  `PTree.gsident` rewrites `PTree.set id v e` to `e` when `e!id = Some v`.
  The port's trees are not canonical; the states reached "eventually" are
  therefore described up to pointwise equality of environments (`EnvEqv`).
  Everything the simulation needs about environments (`env_lessdef`,
  `wt_env`, `def_env`) is invariant under `EnvEqv`.
-/
import CCLib.x86.SelectionproofExprs
import CCLib.backend.CminortypingSubject
import CCLib.common.SimulationEventually

namespace CC
namespace X86
namespace Selectionproof

open Op CminorSel SelectOp Selection Cminortyping Smallstep
open CC.Selection (StmtClass classifyStmt)

/-- Pointwise equality of Cminor environments. -/
def EnvEqv (e1 e2 : Cminor.Env) : Prop := ∀ x, e1.get x = e2.get x

theorem EnvEqv.rfl {e : Cminor.Env} : EnvEqv e e := fun _ => _root_.rfl
theorem EnvEqv.symm {e1 e2 : Cminor.Env} (h : EnvEqv e1 e2) : EnvEqv e2 e1 := fun x => (h x).symm
theorem EnvEqv.trans {e1 e2 e3 : Cminor.Env} (h1 : EnvEqv e1 e2) (h2 : EnvEqv e2 e3) :
    EnvEqv e1 e3 := fun x => (h1 x).trans (h2 x)

theorem EnvEqv.set {e1 e2 : Cminor.Env} (h : EnvEqv e1 e2) (id : Ident) (v : Val) :
    EnvEqv (PTree.set id v e1) (PTree.set id v e2) := by
  intro x
  rw [PTree.gsspec, PTree.gsspec]
  split
  · rfl
  · exact h x

theorem envEqv_gsident {e : Cminor.Env} {id : Ident} {v : Val} (h : e.get id = some v) :
    EnvEqv (PTree.set id v e) e := fun x => PTree.gsident id x v e h

theorem EnvEqv.lessdef {e1 e2 e3 : Cminor.Env} (h : EnvEqv e1 e2) (hl : EnvLessdef e2 e3) :
    EnvLessdef e1 e3 := fun id v hv => hl id v ((h id).symm.trans hv)

theorem EnvEqv.wtEnv {env : Typenv} {e1 e2 : Cminor.Env} (h : EnvEqv e1 e2) (hw : WtEnv env e2) :
    WtEnv env e1 := fun id v hv => hw id v ((h id).symm.trans hv)

theorem EnvEqv.defEnv {f : Cminor.Function} {e1 e2 : Cminor.Env} (h : EnvEqv e1 e2)
    (hd : DefEnv f e2) : DefEnv f e1 := fun id hin => by
  obtain ⟨v, hv⟩ := hd id hin
  exact ⟨v, (h id).trans hv⟩

theorem evalExpr_envEqv {ge : Cminor.CGenv} {sp : Val} {e e' : Cminor.Env} {m : Mem}
    {a : Cminor.Expr} {v : Val} (h : Cminor.EvalExpr ge sp e m a v) (he : EnvEqv e e') :
    Cminor.EvalExpr ge sp e' m a v := by
  induction h with
  | Evar id v hv => exact .Evar _ _ ((he id).symm.trans hv)
  | Econst cst v hv => exact .Econst _ _ hv
  | Eunop op a1 v1 v _ hv ih => exact .Eunop _ _ _ _ ih hv
  | Ebinop op a1 a2 v1 v2 v _ _ hv ih1 ih2 => exact .Ebinop _ _ _ _ _ _ ih1 ih2 hv
  | Eload chunk addr vaddr v _ hl ih => exact .Eload _ _ _ _ ih hl

section EXPRESSIONS
variable {ge : Cminor.CGenv}

/-- `Selectionproof.eventually` -/
abbrev Eventually (ge : Cminor.CGenv) :=
  Smallstep.Eventually (Cminor.Step ge) Cminor.FinalState

/-- `Selectionproof.eventually_step` -/
theorem eventually_step {f : Cminor.Function} {s : Cminor.Stmt} {k : Cminor.Cont} {sp : Val}
    {e : Cminor.Env} {m : Mem} {n : Nat} {P : Cminor.State → Prop}
    (h : ∀ t S', Cminor.Step ge (.State f s k sp e m) t S' → t = E0 ∧ Eventually ge n S' P) :
    Eventually ge (n + 1) (.State f s k sp e m) P :=
  Smallstep.Eventually.later' (fun _ hf => by cases hf) h

/-- The state reached after running a statement to completion, with an environment
pointwise equal to `e`. -/
def SkipState (f : Cminor.Function) (k : Cminor.Cont) (sp : Val) (e : Cminor.Env) (m : Mem)
    (S : Cminor.State) : Prop :=
  ∃ e1, EnvEqv e1 e ∧ S = .State f .Sskip k sp e1 m

theorem eventually_seq {s1 s2 : Cminor.Stmt} {n1 n2 : Nat} {f : Cminor.Function} {sp : Val}
    {m : Mem} {e e' e'' : Cminor.Env}
    (h1 : ∀ k, Eventually ge n1 (.State f s1 k sp e m) (SkipState f k sp e' m))
    (h2 : ∀ k e1, EnvEqv e1 e' → Eventually ge n2 (.State f s2 k sp e1 m) (SkipState f k sp e'' m))
    (k : Cminor.Cont) :
    Eventually ge (n1 + (n2 + 1) + 1) (.State f (.Sseq s1 s2) k sp e m) (SkipState f k sp e'' m) := by
  apply eventually_step
  intro t S' hst
  cases hst with
  | seq =>
    refine ⟨_root_.rfl, ?_⟩
    apply Smallstep.eventually_trans (h1 (.Kseq s2 k))
    rintro S2 ⟨e1, he1, rfl⟩
    apply eventually_step
    intro t S' hst
    cases hst with
    | skip_seq => exact ⟨_root_.rfl, h2 k e1 he1⟩
    | skip_call _ _ _ _ _ _ hc => cases hc

/-- The `SCskip` half of `classify_stmt_sound`. -/
def SkipSound (ge : Cminor.CGenv) (s : Cminor.Stmt) : Prop :=
  ∃ n, ∀ f k sp e m, Eventually ge n (.State f s k sp e m) (SkipState f k sp e m)

/-- The `SCassign` half of `classify_stmt_sound`. -/
def AssignSound (ge : Cminor.CGenv) (s : Cminor.Stmt) (id : Ident) (a : Cminor.Expr) : Prop :=
  ∃ n, ∀ f k sp e m v, Cminor.EvalExpr ge sp e m a v →
    Eventually ge n (.State f s k sp e m) (SkipState f k sp (PTree.set id v e) m)

theorem assign_base (id : Ident) (a : Cminor.Expr) : AssignSound ge (.Sassign id a) id a := by
  refine ⟨1, fun f k sp e m v hv => eventually_step fun t S' hst => ?_⟩
  cases hst with
  | assign _ _ _ _ _ _ _ v0 hv0 =>
    rw [Cminor.evalExpr_determ hv hv0]
    exact ⟨_root_.rfl, .now ⟨_, EnvEqv.rfl, _root_.rfl⟩⟩

/-- `Selectionproof.classify_stmt_sound` (up to `EnvEqv`, see the header; the two
non-trivial cases of Rocq's `match` are the two conjuncts). -/
theorem classify_stmt_sound (s : Cminor.Stmt) :
    (classifyStmt s = .SCskip → SkipSound ge s) ∧
    (∀ id a, classifyStmt s = .SCassign id a → AssignSound ge s id a) := by
  induction s with
  | Sskip =>
    refine ⟨fun _ => ⟨0, fun f k sp e m => .now ⟨e, EnvEqv.rfl, _root_.rfl⟩⟩, ?_⟩
    intro id a h; simp [classifyStmt] at h
  | Sassign id a =>
    cases a with
    | Evar id2 =>
      by_cases hid : id = id2
      · subst hid
        refine ⟨fun _ => ⟨1, fun f k sp e m => eventually_step fun t S' hst => ?_⟩, ?_⟩
        · cases hst with
          | assign _ _ _ _ _ _ _ v0 hv0 =>
            cases hv0 with
            | Evar _ _ hget => exact ⟨_root_.rfl, .now ⟨_, envEqv_gsident hget, _root_.rfl⟩⟩
        · intro id' a' h; simp [classifyStmt] at h
      · refine ⟨fun h => (by simp [classifyStmt, hid] at h), ?_⟩
        intro id' a' h
        simp only [classifyStmt, hid, if_false, StmtClass.SCassign.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact assign_base _ _
    | _ =>
      refine ⟨fun h => (by simp [classifyStmt] at h), ?_⟩
      intro id' a' h
      simp only [classifyStmt, StmtClass.SCassign.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact assign_base _ _
  | Sbuiltin optid ef args =>
    cases optid with
    | none =>
      cases ef with
      | EF_debug =>
        refine ⟨fun _ => ⟨1, fun f k sp e m => eventually_step fun t S' hst => ?_⟩, ?_⟩
        · cases hst with
          | builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hx =>
            cases hx
            exact ⟨_root_.rfl, .now ⟨_, EnvEqv.rfl, _root_.rfl⟩⟩
        · intro id' a' h; simp [classifyStmt] at h
      | _ => exact ⟨fun h => (by simp [classifyStmt] at h), fun _ _ h => (by simp [classifyStmt] at h)⟩
    | some _ => exact ⟨fun h => (by simp [classifyStmt] at h), fun _ _ h => (by simp [classifyStmt] at h)⟩
  | Sseq s1 s2 ih1 ih2 =>
    simp only [classifyStmt]
    obtain ⟨A1, B1⟩ := ih1
    obtain ⟨A2, B2⟩ := ih2
    rcases h1 : classifyStmt s1 with _ | ⟨id1, a1⟩ | _ <;>
      rcases h2 : classifyStmt s2 with _ | ⟨id2, a2⟩ | _
    · refine ⟨fun _ => ?_, fun _ _ h => (by cases h)⟩
      obtain ⟨n1, E1⟩ := A1 h1
      obtain ⟨n2, E2⟩ := A2 h2
      exact ⟨_, fun f k sp e m => eventually_seq (fun k => E1 f k sp e m)
        (fun k e1 he1 => Smallstep.eventually_implies (E2 f k sp e1 m)
          (fun _ ⟨e2, he2, hS⟩ => ⟨e2, he2.trans he1, hS⟩)) k⟩
    · refine ⟨fun h => (by cases h), ?_⟩
      intro id a h
      cases h
      obtain ⟨n1, E1⟩ := A1 h1
      obtain ⟨n2, E2⟩ := B2 _ _ h2
      exact ⟨_, fun f k sp e m v hv => eventually_seq (fun k => E1 f k sp e m)
        (fun k e1 he1 => Smallstep.eventually_implies
          (E2 f k sp e1 m v (evalExpr_envEqv hv he1.symm))
          (fun _ ⟨e2, he2, hS⟩ => ⟨e2, he2.trans (he1.set id2 v), hS⟩)) k⟩
    · exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
    · refine ⟨fun h => (by cases h), ?_⟩
      intro id a h
      cases h
      obtain ⟨n1, E1⟩ := B1 _ _ h1
      obtain ⟨n2, E2⟩ := A2 h2
      exact ⟨_, fun f k sp e m v hv => eventually_seq (fun k => E1 f k sp e m v hv)
        (fun k e1 he1 => Smallstep.eventually_implies (E2 f k sp e1 m)
          (fun _ ⟨e2, he2, hS⟩ => ⟨e2, he2.trans he1, hS⟩)) k⟩
    all_goals exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
  | _ => exact ⟨fun h => (by simp [classifyStmt] at h), fun _ _ h => (by simp [classifyStmt] at h)⟩

/-- `Selectionproof.classify_stmt_wt` -/
theorem classify_stmt_wt {env : Typenv} {tret : XType} {id : Ident} {a : Cminor.Expr} :
    ∀ (s : Cminor.Stmt), classifyStmt s = .SCassign id a → WtStmt env tret s →
    WtExpr env a (env id)
  | .Sassign id' a', hc, hw => by
    simp only [classifyStmt] at hc
    have key : id' = id ∧ a' = a := by
      split at hc
      · split at hc
        · cases hc
        · cases hc; exact ⟨_root_.rfl, _root_.rfl⟩
      · cases hc; exact ⟨_root_.rfl, _root_.rfl⟩
    obtain ⟨rfl, rfl⟩ := key
    cases hw with
    | Sassign _ _ h => exact h
  | .Sbuiltin optid ef args, hc, _ => by
    cases optid with
    | none => cases ef <;> simp [classifyStmt] at hc
    | some _ => simp [classifyStmt] at hc
  | .Sseq s1 s2, hc, hw => by
    cases hw with
    | Sseq _ _ h1 h2 =>
      simp only [classifyStmt] at hc
      revert hc
      have ih1 : classifyStmt s1 = .SCassign id a → WtExpr env a (env id) :=
        fun h => classify_stmt_wt s1 h h1
      have ih2 : classifyStmt s2 = .SCassign id a → WtExpr env a (env id) :=
        fun h => classify_stmt_wt s2 h h2
      revert ih1 ih2
      generalize classifyStmt s1 = c1
      generalize classifyStmt s2 = c2
      intro ih1 ih2 hc
      cases c1 <;> cases c2 <;> simp only [] at hc <;> cases hc
      · exact ih2 _root_.rfl
      · exact ih1 _root_.rfl
  | .Sskip, hc, _ => by simp [classifyStmt] at hc
  | .Sstore .., hc, _ => by simp [classifyStmt] at hc
  | .Scall .., hc, _ => by simp [classifyStmt] at hc
  | .Stailcall .., hc, _ => by simp [classifyStmt] at hc
  | .Sifthenelse .., hc, _ => by simp [classifyStmt] at hc
  | .Sloop _, hc, _ => by simp [classifyStmt] at hc
  | .Sblock _, hc, _ => by simp [classifyStmt] at hc
  | .Sexit _, hc, _ => by simp [classifyStmt] at hc
  | .Sswitch .., hc, _ => by simp [classifyStmt] at hc
  | .Sreturn _, hc, _ => by simp [classifyStmt] at hc
  | .Slabel .., hc, _ => by simp [classifyStmt] at hc
  | .Sgoto _, hc, _ => by simp [classifyStmt] at hc

variable {tge : CminorSel.CGenv}
  (hsym : ∀ id, Genv.findSymbol tge id = Genv.findSymbol ge id)
  (opts : Options) {hf : CC.SplitLong.HelperFunctions}
  (HF : SplitLongproof.HelpersDeclaredGe tge hf)

include hsym HF in
/-- `Selectionproof.if_conversion_base_correct` -/
theorem if_conversion_base_correct {f : Cminor.Function} {env : Typenv} {cond : Cminor.Expr}
    {id : Ident} {ifso ifnot : Cminor.Expr} {kont s : CminorSel.Stmt} {e : Cminor.Env} {ty : ATyp}
    {vb : Val} {b : Bool} {sp : Val} {m : Mem} {tf : CminorSel.Function} {tk : CminorSel.Cont}
    {e' : Cminor.Env} {m' : Mem}
    (h : ifConversionBase opts hf (CC.Selection.knownId f) env cond id ifso ifnot kont = some s)
    (hde : DefEnv f e) (hwe : WtEnv env e) (hty : env id = ty)
    (h1 : WtExpr env ifso ty) (h2 : WtExpr env ifnot ty)
    (hc : Cminor.EvalExpr ge sp e m cond vb) (hb : Val.BoolOfVal vb b)
    (he : EnvLessdef e e') (hm : Mem.Extends m m') :
    ∃ v1 v2 v', Cminor.EvalExpr ge sp e m ifso v1 ∧ Cminor.EvalExpr ge sp e m ifnot v2 ∧
      Val.Lessdef (if b then v1 else v2) v' ∧
      CminorSel.Step tge (.State tf s tk sp e' m') E0
        (.State tf .Sskip tk sp (PTree.set id v' e') m') := by
  subst hty
  unfold ifConversionBase at h
  dsimp only at h
  split at h
  · next hcond =>
    cases h
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨⟨⟨⟨_, _⟩, hs1⟩, hs2⟩, _⟩ := hcond
    obtain ⟨v1, EV1⟩ := eval_safe_expr ge f sp e m hde ifso hs1
    obtain ⟨v2, EV2⟩ := eval_safe_expr ge f sp e m hde ifnot hs2
    have TY1 : Val.HasType v1 (env id) := wt_eval_expr EV1 h1 hwe
    have TY2 : Val.HasType v2 (env id) := wt_eval_expr EV2 h2 hwe
    obtain ⟨v', EV, LD⟩ := sel_select_expr_correct (le := []) hsym opts HF (env id) hc EV1 EV2
      hb he hm
    have hn : Val.select (some b) v1 v2 (env id) = if b then v1 else v2 := by
      show Val.normalize _ (env id) = _
      cases b
      · exact Val.normalize_idem TY2
      · exact Val.normalize_idem TY1
    rw [hn] at LD
    exact ⟨v1, v2, v', EV1, EV2, LD, .assign _ _ _ _ _ _ _ _ EV⟩
  · cases h

include hsym HF in
/-- `Selectionproof.if_conversion_correct` (up to `EnvEqv`, see the header). -/
theorem if_conversion_correct {f : Cminor.Function} {env : Typenv} {tret : XType}
    {cond : Cminor.Expr} {ifso ifnot : Cminor.Stmt} {kont s : CminorSel.Stmt} {vb : Val} {b : Bool}
    {k : Cminor.Cont} {f' : CminorSel.Function} {k' : CminorSel.Cont} {sp : Val}
    {e : Cminor.Env} {m : Mem} {e' : Cminor.Env} {m' : Mem}
    (hifc : ifConversion opts hf (CC.Selection.knownId f) env cond ifso ifnot kont = some s)
    (hde : DefEnv f e) (hwe : WtEnv env e)
    (hw1 : WtStmt env tret ifso) (hw2 : WtStmt env tret ifnot)
    (hc : Cminor.EvalExpr ge sp e m cond vb) (hb : Val.BoolOfVal vb b)
    (he : EnvLessdef e e') (hm : Mem.Extends m m') :
    ∃ n e1 e1',
      CminorSel.Step tge (.State f' s k' sp e' m') E0 (.State f' .Sskip k' sp e1' m') ∧
      Eventually ge n (.State f (if b then ifso else ifnot) k sp e m) (SkipState f k sp e1 m) ∧
      EnvLessdef e1 e1' := by
  obtain ⟨A1, B1⟩ := classify_stmt_sound (ge := ge) ifso
  obtain ⟨A2, B2⟩ := classify_stmt_sound (ge := ge) ifnot
  unfold ifConversion at hifc
  rcases h1 : classifyStmt ifso with _ | ⟨id1, a1⟩ | _ <;>
    rcases h2 : classifyStmt ifnot with _ | ⟨id2, a2⟩ | _ <;>
    rw [h1, h2] at hifc <;> dsimp only at hifc
  all_goals first | (cases hifc; done) | skip
  · obtain ⟨n1, EV1⟩ := A1 h1
    obtain ⟨n2, EV2⟩ := B2 _ _ h2
    obtain ⟨v1, v2, v', E1, E2, VLD, STEP⟩ := if_conversion_base_correct hsym opts HF hifc hde
      hwe _root_.rfl (.Evar id2) (classify_stmt_wt ifnot h2 hw2) hc hb he hm
    refine ⟨if b then n1 else n2, PTree.set id2 (if b then v1 else v2) e, _, STEP, ?_,
      set_var_lessdef he VLD⟩
    cases b
    · exact EV2 f k sp e m v2 E2
    · cases E1 with
      | Evar _ _ hget =>
        exact Smallstep.eventually_implies (EV1 f k sp e m)
          (fun _ ⟨e2, he2, hS⟩ => ⟨e2, he2.trans (envEqv_gsident hget).symm, hS⟩)
  · obtain ⟨n1, EV1⟩ := B1 _ _ h1
    obtain ⟨n2, EV2⟩ := A2 h2
    obtain ⟨v1, v2, v', E1, E2, VLD, STEP⟩ := if_conversion_base_correct hsym opts HF hifc hde
      hwe _root_.rfl (classify_stmt_wt ifso h1 hw1) (.Evar id1) hc hb he hm
    refine ⟨if b then n1 else n2, PTree.set id1 (if b then v1 else v2) e, _, STEP, ?_,
      set_var_lessdef he VLD⟩
    cases b
    · cases E2 with
      | Evar _ _ hget =>
        exact Smallstep.eventually_implies (EV2 f k sp e m)
          (fun _ ⟨e2, he2, hS⟩ => ⟨e2, he2.trans (envEqv_gsident hget).symm, hS⟩)
    · exact EV1 f k sp e m v1 E1
  · split at hifc
    · next hid =>
      subst hid
      obtain ⟨n1, EV1⟩ := B1 _ _ h1
      obtain ⟨n2, EV2⟩ := B2 _ _ h2
      obtain ⟨v1, v2, v', E1, E2, VLD, STEP⟩ := if_conversion_base_correct hsym opts HF hifc
        hde hwe _root_.rfl (classify_stmt_wt ifso h1 hw1) (classify_stmt_wt ifnot h2 hw2) hc hb
        he hm
      refine ⟨if b then n1 else n2, PTree.set id1 (if b then v1 else v2) e, _, STEP, ?_,
        set_var_lessdef he VLD⟩
      cases b
      · exact EV2 f k sp e m v2 E2
      · exact EV1 f k sp e m v1 E1
    · cases hifc

end EXPRESSIONS

end Selectionproof
end X86
end CC
