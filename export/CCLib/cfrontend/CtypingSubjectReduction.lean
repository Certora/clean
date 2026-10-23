/-
  Subject reduction for CompCert C, part 2 — port of the sections
  `WT_SWITCH` and `PRESERVATION` of `cfrontend/Ctyping.v`: typing of
  continuations and states (`wt_expr_cont`, `wt_stmt_cont`, `wt_call_cont`,
  `wt_state`), `wt_find_label`, `preservation_estep`, `preservation_sstep`,
  **`preservation`** and **`wt_initial_state`**; and the final section
  "Additional type-related results" (`sem_cast_already_typed`,
  `sem_cast_already_typed_idem`).  With `CCLib.cfrontend.Ctyping`,
  `CCLib.cfrontend.CtypingSound` and `CCLib.cfrontend.CtypingPreservation`, all of `Ctyping.v` is
  ported.

  Differences from Rocq: CompCert gets the well-typedness of the results of
  external calls from its axioms on external functions; here the
  uninterpreted externals (`externalFunctionsSem`, `inlineAssemblySem`)
  contribute it as the hypotheses `hext`/`hasm` of the theorems that need it
  (the same hypotheses as `externalCall_wellTyped`).
-/
import CCLib.cfrontend.CtypingPreservation
import CCLib.common.GlobalenvsTheory

namespace CC
namespace Ctyping

/-! ## `switch` -/

/-- `Ctyping.wt_select_switch` (default case). -/
theorem wt_select_switch_default {ce : CompositeEnv} {e : Typenv} {rt : Ty} :
    ∀ {sl : Csyntax.LStmts}, WtLblstmts ce e rt sl → WtLblstmts ce e rt (Csem.selectSwitchDefault sl)
  | .LSnil, h => h
  | .LScons none _ _, h => h
  | .LScons (some _) _ _, h => by
      cases h with
      | cons _ _ _ _ h2 => simp only [Csem.selectSwitchDefault]; exact wt_select_switch_default h2

/-- `Ctyping.wt_select_switch` (case selection). -/
theorem wt_select_switch_case {ce : CompositeEnv} {e : Typenv} {rt : Ty} {n : Z} :
    ∀ {sl sl' : Csyntax.LStmts}, WtLblstmts ce e rt sl → Csem.selectSwitchCase n sl = some sl' →
      WtLblstmts ce e rt sl'
  | .LSnil, _, _, hs => by simp [Csem.selectSwitchCase] at hs
  | .LScons none _ _, _, h, hs => by
      cases h with
      | cons _ _ _ _ h2 =>
        simp only [Csem.selectSwitchCase] at hs
        exact wt_select_switch_case h2 hs
  | .LScons (some c) _ _, _, h, hs => by
      simp only [Csem.selectSwitchCase] at hs
      split at hs
      · cases hs; exact h
      · cases h with
        | cons _ _ _ _ h2 => exact wt_select_switch_case h2 hs

/-- `Ctyping.wt_select_switch` -/
theorem wt_select_switch {ce : CompositeEnv} {e : Typenv} {rt : Ty} (n : Z)
    {sl : Csyntax.LStmts} (h : WtLblstmts ce e rt sl) :
    WtLblstmts ce e rt (Csem.selectSwitch n sl) := by
  unfold Csem.selectSwitch
  cases hs : Csem.selectSwitchCase n sl with
  | none => exact wt_select_switch_default h
  | some sl' => exact wt_select_switch_case h hs

/-- `Ctyping.wt_seq_of_ls` -/
theorem wt_seq_of_ls {ce : CompositeEnv} {e : Typenv} {rt : Ty} :
    ∀ {sl : Csyntax.LStmts}, WtLblstmts ce e rt sl →
      WtStmt ce e rt (Csem.seqOfLabeledStatement sl)
  | .LSnil, _ => .skip
  | .LScons _ _ _, h => by
      cases h with
      | cons _ _ _ h1 h2 => exact .sequence _ _ h1 (wt_seq_of_ls h2)

/-! ## Typing of continuations and states -/

section CONT

variable (ce : CompositeEnv)

mutual
/-- `Ctyping.wt_expr_cont`: typing of the continuation of an expression state. -/
inductive WtExprCont : Typenv → Csyntax.Function → Csem.Cont → Prop where
  | Kdo (te f k) : WtStmtCont te f k → WtExprCont te f (.Kdo k)
  | Kifthenelse (te f s1 s2 k) :
      WtStmtCont te f k → WtStmt ce te f.fn_return s1 → WtStmt ce te f.fn_return s2 →
      WtExprCont te f (.Kifthenelse s1 s2 k)
  | Kwhile1 (te f r s k) :
      WtStmtCont te f k → WtRvalue ce te r → WtStmt ce te f.fn_return s → WtBool (Csyntax.typeof r) →
      WtExprCont te f (.Kwhile1 r s k)
  | Kdowhile2 (te f r s k) :
      WtStmtCont te f k → WtRvalue ce te r → WtStmt ce te f.fn_return s → WtBool (Csyntax.typeof r) →
      WtExprCont te f (.Kdowhile2 r s k)
  | Kfor2 (te f r s2 s3 k) :
      WtStmtCont te f k → WtRvalue ce te r → WtStmt ce te f.fn_return s2 →
      WtStmt ce te f.fn_return s3 → Cop.classifyBool (Csyntax.typeof r) ≠ .default →
      WtExprCont te f (.Kfor2 r s2 s3 k)
  | Kswitch1 (te f ls k) :
      WtStmtCont te f k → WtLblstmts ce te f.fn_return ls → WtExprCont te f (.Kswitch1 ls k)
  | Kreturn (te f k) : WtStmtCont te f k → WtExprCont te f (.Kreturn k)

/-- `Ctyping.wt_stmt_cont`: typing of the continuation of a statement state. -/
inductive WtStmtCont : Typenv → Csyntax.Function → Csem.Cont → Prop where
  | Kseq (te f s k) :
      WtStmtCont te f k → WtStmt ce te f.fn_return s → WtStmtCont te f (.Kseq s k)
  | Kwhile2 (te f r s k) :
      WtStmtCont te f k → WtRvalue ce te r → WtStmt ce te f.fn_return s → WtBool (Csyntax.typeof r) →
      WtStmtCont te f (.Kwhile2 r s k)
  | Kdowhile1 (te f r s k) :
      WtStmtCont te f k → WtRvalue ce te r → WtStmt ce te f.fn_return s → WtBool (Csyntax.typeof r) →
      WtStmtCont te f (.Kdowhile1 r s k)
  | Kfor3 (te f r s2 s3 k) :
      WtStmtCont te f k → WtRvalue ce te r → WtStmt ce te f.fn_return s2 →
      WtStmt ce te f.fn_return s3 → WtBool (Csyntax.typeof r) → WtStmtCont te f (.Kfor3 r s2 s3 k)
  | Kfor4 (te f r s2 s3 k) :
      WtStmtCont te f k → WtRvalue ce te r → WtStmt ce te f.fn_return s2 →
      WtStmt ce te f.fn_return s3 → WtBool (Csyntax.typeof r) → WtStmtCont te f (.Kfor4 r s2 s3 k)
  | Kswitch2 (te f k) : WtStmtCont te f k → WtStmtCont te f (.Kswitch2 k)
  | Kstop' (te f) : WtStmtCont te f .Kstop
  | Kcall' (te f f' e C ty k) :
      WtCallCont (.Kcall f' e C ty k) ty → ty = f.fn_return →
      WtStmtCont te f (.Kcall f' e C ty k)

/-- `Ctyping.wt_call_cont`: typing of the continuation of a call, for a call
    whose result has type `ty`. -/
inductive WtCallCont : Csem.Cont → Ty → Prop where
  | Kstop (ty) : WtCallCont .Kstop ty
  | Kcall (te f e C ty k) :
      WtExprCont te f k → WtStmt ce te f.fn_return f.fn_body →
      (∀ v, WtVal v ty → WtRvalue ce te (C (.Eval v ty))) →
      WtCallCont (.Kcall f e C ty k) ty
end

variable {ce}

/-- `Ctyping.is_wt_call_cont` -/
theorem is_wt_call_cont {te : Typenv} {f : Csyntax.Function} {k : Csem.Cont}
    (hk : Csem.IsCallCont k) (h : WtStmtCont ce te f k) : WtCallCont ce k f.fn_return := by
  cases h with
  | Kstop' => exact .Kstop _
  | Kcall' _ _ _ _ _ _ _ h1 h2 => exact h2 ▸ h1
  | _ => exact hk.elim

/-- `Ctyping.wt_call_cont_stmt_cont` -/
theorem wt_call_cont_stmt_cont {te : Typenv} {f : Csyntax.Function} {k : Csem.Cont}
    (h : WtCallCont ce k f.fn_return) : WtStmtCont ce te f k := by
  cases k with
  | Kstop => exact .Kstop' _ _
  | Kcall f' e C ty k =>
    have : ty = f.fn_return := by cases h; rfl
    subst this
    exact .Kcall' _ _ _ _ _ _ _ h rfl
  | _ => cases h

/-- `Ctyping.call_cont_wt` -/
theorem call_cont_wt {te : Typenv} {f : Csyntax.Function} :
    ∀ {k : Csem.Cont}, WtStmtCont ce te f k → WtCallCont ce (Csem.callCont k) f.fn_return
  | .Kstop, _ => .Kstop _
  | .Kseq _ _, .Kseq _ _ _ _ h _ => by rw [Csem.callCont]; exact call_cont_wt h
  | .Kwhile2 _ _ _, .Kwhile2 _ _ _ _ _ h _ _ _ => by rw [Csem.callCont]; exact call_cont_wt h
  | .Kdowhile1 _ _ _, .Kdowhile1 _ _ _ _ _ h _ _ _ => by rw [Csem.callCont]; exact call_cont_wt h
  | .Kfor3 _ _ _ _, .Kfor3 _ _ _ _ _ _ h _ _ _ _ => by rw [Csem.callCont]; exact call_cont_wt h
  | .Kfor4 _ _ _ _, .Kfor4 _ _ _ _ _ _ h _ _ _ _ => by rw [Csem.callCont]; exact call_cont_wt h
  | .Kswitch2 _, .Kswitch2 _ _ _ h => by rw [Csem.callCont]; exact call_cont_wt h
  | .Kcall _ _ _ _ _, .Kcall' _ _ _ _ _ _ _ h1 h2 => h2 ▸ h1

/-- `Ctyping.call_cont_wt'` -/
theorem call_cont_wt' {te : Typenv} {f : Csyntax.Function} :
    ∀ {k : Csem.Cont}, WtStmtCont ce te f k → WtStmtCont ce te f (Csem.callCont k)
  | .Kstop, h => h
  | .Kseq _ _, .Kseq _ _ _ _ h _ => by rw [Csem.callCont]; exact call_cont_wt' h
  | .Kwhile2 _ _ _, .Kwhile2 _ _ _ _ _ h _ _ _ => by rw [Csem.callCont]; exact call_cont_wt' h
  | .Kdowhile1 _ _ _, .Kdowhile1 _ _ _ _ _ h _ _ _ => by rw [Csem.callCont]; exact call_cont_wt' h
  | .Kfor3 _ _ _ _, .Kfor3 _ _ _ _ _ _ h _ _ _ _ => by rw [Csem.callCont]; exact call_cont_wt' h
  | .Kfor4 _ _ _ _, .Kfor4 _ _ _ _ _ _ h _ _ _ _ => by rw [Csem.callCont]; exact call_cont_wt' h
  | .Kswitch2 _, .Kswitch2 _ _ _ h => by rw [Csem.callCont]; exact call_cont_wt' h
  | .Kcall _ _ _ _ _, h => h

mutual
/-- `Ctyping.wt_find_label` -/
theorem wt_find_label {lbl : Csyntax.Label} {te : Typenv} {f : Csyntax.Function} :
    ∀ {s : Csyntax.Stmt}, WtStmt ce te f.fn_return s →
    ∀ {k s' k'}, Csem.findLabel lbl s k = some (s', k') → WtStmtCont ce te f k →
      WtStmt ce te f.fn_return s' ∧ WtStmtCont ce te f k'
  | _, .skip, _, _, _, hf, _ => by simp [Csem.findLabel] at hf
  | _, .do_ _ _, _, _, _, hf, _ => by simp [Csem.findLabel] at hf
  | _, .sequence s1 s2 h1 h2, k, _, _, hf, hk => by
      simp only [Csem.findLabel] at hf
      cases e : Csem.findLabel lbl s1 (.Kseq s2 k) with
      | some sk =>
        rw [e] at hf; cases hf
        exact wt_find_label h1 e (.Kseq _ _ _ _ hk h2)
      | none => rw [e] at hf; exact wt_find_label h2 hf hk
  | _, .ifthenelse _ s1 s2 _ h1 h2 _, k, _, _, hf, hk => by
      simp only [Csem.findLabel] at hf
      cases e : Csem.findLabel lbl s1 k with
      | some sk => rw [e] at hf; cases hf; exact wt_find_label h1 e hk
      | none => rw [e] at hf; exact wt_find_label h2 hf hk
  | _, .while_ _ _ hr hs hb, _, _, _, hf, hk => by
      simp only [Csem.findLabel] at hf
      exact wt_find_label hs hf (.Kwhile2 _ _ _ _ _ hk hr hs hb)
  | _, .dowhile _ _ hr hs hb, _, _, _, hf, hk => by
      simp only [Csem.findLabel] at hf
      exact wt_find_label hs hf (.Kdowhile1 _ _ _ _ _ hk hr hs hb)
  | _, .for_ s1 r s2 s3 hr h1 h2 h3 hb, k, _, _, hf, hk => by
      simp only [Csem.findLabel] at hf
      cases e : Csem.findLabel lbl s1 (.Kseq (.Sfor .Sskip r s2 s3) k) with
      | some sk =>
        rw [e] at hf; cases hf
        exact wt_find_label h1 e (.Kseq _ _ _ _ hk (.for_ _ _ _ _ hr .skip h2 h3 hb))
      | none =>
        rw [e] at hf
        cases e2 : Csem.findLabel lbl s3 (.Kfor3 r s2 s3 k) with
        | some sk =>
          rw [e2] at hf; cases hf
          exact wt_find_label h3 e2 (.Kfor3 _ _ _ _ _ _ hk hr h2 h3 hb)
        | none =>
          rw [e2] at hf
          exact wt_find_label h2 hf (.Kfor4 _ _ _ _ _ _ hk hr h2 h3 hb)
  | _, .break_, _, _, _, hf, _ => by simp [Csem.findLabel] at hf
  | _, .continue_, _, _, _, hf, _ => by simp [Csem.findLabel] at hf
  | _, .return_none, _, _, _, hf, _ => by simp [Csem.findLabel] at hf
  | _, .return_some _ _ _, _, _, _, hf, _ => by simp [Csem.findLabel] at hf
  | _, .switch _ _ _ _ _ _ _ hls, _, _, _, hf, hk => by
      simp only [Csem.findLabel] at hf
      exact wt_find_label_ls hls hf (.Kswitch2 _ _ _ hk)
  | _, .label lbl' s hs, _, _, _, hf, hk => by
      simp only [Csem.findLabel] at hf
      split at hf
      · cases hf; exact ⟨hs, hk⟩
      · exact wt_find_label hs hf hk
  | _, .goto _, _, _, _, hf, _ => by simp [Csem.findLabel] at hf

/-- `Ctyping.wt_find_label` (for labeled statements). -/
theorem wt_find_label_ls {lbl : Csyntax.Label} {te : Typenv} {f : Csyntax.Function} :
    ∀ {ls : Csyntax.LStmts}, WtLblstmts ce te f.fn_return ls →
    ∀ {k s' k'}, Csem.findLabelLs lbl ls k = some (s', k') → WtStmtCont ce te f k →
      WtStmt ce te f.fn_return s' ∧ WtStmtCont ce te f k'
  | _, .nil, _, _, _, hf, _ => by simp [Csem.findLabelLs] at hf
  | _, .cons _ s ls hs hls, k, _, _, hf, hk => by
      simp only [Csem.findLabelLs] at hf
      cases e : Csem.findLabel lbl s (.Kseq (Csem.seqOfLabeledStatement ls) k) with
      | some sk =>
        rw [e] at hf; cases hf
        exact wt_find_label hs e (.Kseq _ _ _ _ hk (wt_seq_of_ls hls))
      | none => rw [e] at hf; exact wt_find_label_ls hls hf hk
end

end CONT

/-! ## Preservation -/

section PRESERVATION

variable (prog : Csyntax.Program)

/-- `Ctyping.fundef_return` -/
def fundefReturn : Csyntax.FunDef → Ty
  | .Internal f => f.fn_return
  | .External _ _ tres _ => tres

/-- `Ctyping.wt_state`: well-typedness of execution states of program `prog`
    (with respect to its composite environment and its global type
    environment). -/
inductive WtState : Csem.State → Prop where
  | stmt (f s k e m te) :
      WtStmtCont prog.prog_comp_env te f k →
      WtStmt prog.prog_comp_env te f.fn_return f.fn_body →
      WtStmt prog.prog_comp_env te f.fn_return s →
      WtState (.State f s k e m)
  | expr (f r k e m te) :
      WtExprCont prog.prog_comp_env te f k →
      WtStmt prog.prog_comp_env te f.fn_return f.fn_body →
      WtRvalue prog.prog_comp_env te r →
      WtState (.ExprState f r k e m)
  | call (b fd vargs k m) :
      WtCallCont prog.prog_comp_env k (fundefReturn fd) →
      WtFundef prog.prog_comp_env (bindGlobdef PTree.empty prog.prog_defs) fd →
      Genv.findFunct (Csem.globalenv prog).genv_genv b = some fd →
      WtState (.Callstate fd vargs k m)
  | ret (v k m ty) :
      WtCallCont prog.prog_comp_env k ty → WtVal v ty → WtState (.Returnstate v k m)
  | stuck : WtState .Stuckstate

variable {prog}

/-- `Ctyping.wt_find_funct` -/
theorem wt_find_funct (WTPROG : WtProgram prog) {v : Val} {fd : Csyntax.FunDef}
    (h : Genv.findFunct (Csem.globalenv prog).genv_genv v = some fd) :
    WtFundef prog.prog_comp_env (bindGlobdef PTree.empty prog.prog_defs) fd :=
  Genv.findFunct_prop _ (fun id f hin => WTPROG id f hin) h

/-- `Ctyping.preservation_estep` -/
theorem preservation_estep (WTPROG : WtProgram prog) {S : Csem.State} {t : Trace}
    {S' : Csem.State} (h : Csem.Estep (Csem.globalenv prog) S t S') (WT : WtState prog S) :
    WtState prog S' := by
  cases h with
  | lred C f a k e m a' m' hl hC =>
    cases WT with
    | expr _ _ _ _ _ te WTK WTB WTE =>
      exact .expr _ _ _ _ _ te WTK WTB
        (wt_context (lred_same_type hl) hC WTE (wt_lred hl (wt_subexpr hC WTE)))
  | rred C f a k e m t a' m' hr hC =>
    cases WT with
    | expr _ _ _ _ _ te WTK WTB WTE =>
      exact .expr _ _ _ _ _ te WTK WTB
        (wt_context (rred_same_type hr) hC WTE (wt_rred hr (wt_subexpr hC WTE)))
  | call C f a k e m fd vargs ty hc hC =>
    cases WT with
    | expr _ _ _ _ _ te WTK WTB WTE =>
      have A : WtRvalue _ te a := wt_subexpr hC WTE
      cases hc with
      | call vf tyf m tyargs tyres cconv el ty fd vargs hf hca htf hcf =>
        cases A with
        | call _ _ tyargs' _ cconv' _ _ hcf' _ =>
          simp only [Csyntax.typeof] at hcf'
          rw [hcf] at hcf'
          cases hcf'
          have hret : fundefReturn fd = ty := by
            cases fd with
            | Internal f' =>
              simp only [Csyntax.typeOfFundef, Csyntax.typeOfFunction, Ty.Tfunction.injEq] at htf
              exact htf.2.1
            | External ef targs tres cc =>
              simp only [Csyntax.typeOfFundef, Ty.Tfunction.injEq] at htf
              exact htf.2.1
          refine .call vf _ _ _ _ ?_ (wt_find_funct WTPROG hf) hf
          rw [hret]
          refine .Kcall te f e C ty k WTK WTB (fun v hv => ?_)
          exact wt_context (C := C) (a := .Ecall (.Eval vf tyf) el ty) (a' := .Eval v ty) rfl hC WTE
            (.val _ _ hv)
  | stuck => exact .stuck

/-- `Ctyping.preservation_sstep`.  The hypotheses `hext`/`hasm` say that the
    uninterpreted external functions and inline assembly return values of the
    result type of their signature (CompCert assumes this by axiom). -/
theorem preservation_sstep
    (hext : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasm : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    {S : Csem.State} {t : Trace} {S' : Csem.State}
    (h : Csem.Sstep (Csem.globalenv prog) S t S') (WT : WtState prog S) :
    WtState prog S' := by
  cases h with
  | do_1 =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with | do_ _ hr => exact .expr _ _ _ _ _ te (.Kdo _ _ _ WTK) WTB hr
  | do_2 =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with | Kdo _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | seq =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | sequence _ _ h1 h2 => exact .stmt _ _ _ _ _ te (.Kseq _ _ _ _ WTK h2) WTB h1
  | skip_seq =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kseq _ _ _ _ hk hs => exact .stmt _ _ _ _ _ te hk WTB hs
  | continue_seq =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kseq _ _ _ _ hk hs => exact .stmt _ _ _ _ _ te hk WTB .continue_
  | break_seq =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kseq _ _ _ _ hk hs => exact .stmt _ _ _ _ _ te hk WTB .break_
  | ifthenelse_1 =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | ifthenelse _ _ _ hr h1 h2 _ =>
      exact .expr _ _ _ _ _ te (.Kifthenelse _ _ _ _ _ WTK h1 h2) WTB hr
  | ifthenelse_2 _ _ _ _ _ _ _ _ b =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with
    | Kifthenelse _ _ _ _ _ hk h1 h2 =>
      cases b
      · exact .stmt _ _ _ _ _ te hk WTB h2
      · exact .stmt _ _ _ _ _ te hk WTB h1
  | «while» =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | while_ _ _ hr hs hb => exact .expr _ _ _ _ _ te (.Kwhile1 _ _ _ _ _ WTK hr hs hb) WTB hr
  | while_false =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with | Kwhile1 _ _ _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | while_true =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with
    | Kwhile1 _ _ _ _ _ hk hr hs hb =>
      exact .stmt _ _ _ _ _ te (.Kwhile2 _ _ _ _ _ hk hr hs hb) WTB hs
  | skip_or_continue_while =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with
    | Kwhile2 _ _ _ _ _ hk hr hs hb => exact .stmt _ _ _ _ _ te hk WTB (.while_ _ _ hr hs hb)
  | break_while =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kwhile2 _ _ _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | dowhile =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | dowhile _ _ hr hs hb =>
      exact .stmt _ _ _ _ _ te (.Kdowhile1 _ _ _ _ _ WTK hr hs hb) WTB hs
  | skip_or_continue_dowhile =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with
    | Kdowhile1 _ _ _ _ _ hk hr hs hb =>
      exact .expr _ _ _ _ _ te (.Kdowhile2 _ _ _ _ _ hk hr hs hb) WTB hr
  | dowhile_false =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with | Kdowhile2 _ _ _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | dowhile_true =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with
    | Kdowhile2 _ _ _ _ _ hk hr hs hb => exact .stmt _ _ _ _ _ te hk WTB (.dowhile _ _ hr hs hb)
  | break_dowhile =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kdowhile1 _ _ _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | for_start =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | for_ _ _ _ _ hr h1 h2 h3 hb =>
      exact .stmt _ _ _ _ _ te (.Kseq _ _ _ _ WTK (.for_ _ _ _ _ hr .skip h2 h3 hb)) WTB h1
  | «for» =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | for_ _ _ _ _ hr h1 h2 h3 hb =>
      exact .expr _ _ _ _ _ te (.Kfor2 _ _ _ _ _ _ WTK hr h2 h3 hb) WTB hr
  | for_false =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with | Kfor2 _ _ _ _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | for_true =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with
    | Kfor2 _ _ _ _ _ _ hk hr h2 h3 hb =>
      exact .stmt _ _ _ _ _ te (.Kfor3 _ _ _ _ _ _ hk hr h2 h3 hb) WTB h3
  | skip_or_continue_for3 =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with
    | Kfor3 _ _ _ _ _ _ hk hr h2 h3 hb =>
      exact .stmt _ _ _ _ _ te (.Kfor4 _ _ _ _ _ _ hk hr h2 h3 hb) WTB h2
  | break_for3 =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kfor3 _ _ _ _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | skip_for4 =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with
    | Kfor4 _ _ _ _ _ _ hk hr h2 h3 hb =>
      exact .stmt _ _ _ _ _ te hk WTB (.for_ _ _ _ _ hr .skip h2 h3 hb)
  | return_0 =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    exact .ret _ _ _ _ (call_cont_wt WTK) (.undef _)
  | return_1 =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | return_some _ hr _ => exact .expr _ _ _ _ _ te (.Kreturn _ _ _ WTK) WTB hr
  | return_2 _ _ _ _ _ _ _ _ hc =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with
    | Kreturn _ _ _ hk => exact .ret _ _ _ _ (call_cont_wt hk) (pres_sem_cast hc)
  | skip_call _ _ _ _ _ hcc =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    exact .ret _ _ _ _ (is_wt_call_cont hcc WTK) (.undef _)
  | switch =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with
    | switch _ _ _ _ _ hr _ hls => exact .expr _ _ _ _ _ te (.Kswitch1 _ _ _ _ WTK hls) WTB hr
  | expr_switch _ _ _ _ _ _ _ n =>
    cases WT with | expr _ _ _ _ _ te WTK WTB WTE =>
    cases WTK with
    | Kswitch1 _ _ _ _ hk hls =>
      exact .stmt _ _ _ _ _ te (.Kswitch2 _ _ _ hk) WTB (wt_seq_of_ls (wt_select_switch n hls))
  | skip_break_switch =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kswitch2 _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .skip
  | continue_switch =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTK with | Kswitch2 _ _ _ hk => exact .stmt _ _ _ _ _ te hk WTB .continue_
  | label =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    cases WTS with | label _ _ hs => exact .stmt _ _ _ _ _ te WTK WTB hs
  | goto _ _ _ _ _ _ _ hf =>
    cases WT with | stmt _ _ _ _ _ te WTK WTB WTS =>
    obtain ⟨A, B⟩ := wt_find_label WTB hf (call_cont_wt' WTK)
    exact .stmt _ _ _ _ _ te B WTB A
  | internal_function =>
    cases WT with | call _ _ _ _ _ WTK WTFD _ =>
    cases WTFD with | internal _ hf =>
    cases hf with | intro hb =>
    exact .stmt _ _ _ _ _ _ (wt_call_cont_stmt_cont WTK) hb hb
  | external_function ef targs tres cc vargs k m vres t m' hcall =>
    cases WT with | call _ _ _ _ _ WTK WTFD _ =>
    cases WTFD with | external _ _ _ _ hsig =>
    refine .ret _ _ _ _ WTK (has_rettype_wt_val (ty := tres) ?_)
    rw [← hsig]
    exact externalCall_wellTyped ef hext hasm _ _ _ _ _ _ hcall
  | returnstate =>
    cases WT with | ret _ _ _ _ WTK VAL =>
    cases WTK with | Kcall te _ _ _ _ _ hk hb hC => exact .expr _ _ _ _ _ te hk hb (hC _ VAL)

/-- `Ctyping.preservation`: every step of the CompCert C semantics of a
    well-typed program preserves the well-typedness of states. -/
theorem preservation (WTPROG : WtProgram prog)
    (hext : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasm : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    {S : Csem.State} {t : Trace} {S' : Csem.State}
    (h : Csem.Step (Csem.globalenv prog) S t S') (WT : WtState prog S) : WtState prog S' := by
  rcases h with h | h
  · exact preservation_estep WTPROG h WT
  · exact preservation_sstep hext hasm h WT

/-- `Ctyping.wt_initial_state`: the initial state of a well-typed program is
    well typed. -/
theorem wt_initial_state (WTPROG : WtProgram prog) {S : Csem.State}
    (h : Csem.InitialState prog S) : WtState prog S := by
  cases h with
  | intro b f m0 _ _ hf _ =>
    refine .call (.Vptr b Integers.Ptrofs.zero) _ _ _ _ (.Kstop _) ?_ ?_
    · exact Genv.findFunctPtr_prop _ (fun id f hin => WTPROG id f hin) hf
    · rw [Genv.findFunct_findFunctPtr]; exact hf

end PRESERVATION

/-! ## Additional type-related results -/

theorem castIntInt_of_wtInt {n : Integers.Int} {sz : IntSize} {sg : Signedness}
    (h : WtInt n sz sg) : Cop.castIntInt sz sg n = n := by
  cases sz <;> cases sg <;> simp only [WtInt, Cop.castIntInt] at h ⊢ <;>
    first | exact h | rfl | (rcases h with h | h <;> subst h <;> decide)

theorem bool_of_wtInt {n : Integers.Int} {sg : Signedness} (h : WtInt n .IBool sg) :
    (if Integers.Int.eq n Integers.Int.zero then Integers.Int.zero else Integers.Int.one) = n := by
  rcases h with h | h <;> subst h <;> decide

/-- `Ctyping.sem_cast_already_typed`: casting a value to a type that it
    already has does not change the value (the cast may be undefined if the
    value does not belong to the source type). -/
theorem sem_cast_already_typed {v : Val} {t1 t2 : Ty} {m : Mem} (h : WtVal v t2) :
    Cop.semCast v t1 t2 m = some v ∨ Cop.semCast v t1 t2 m = none := by
  cases h with
  | int n sz sg a hn =>
    rcases t1 with _ | ⟨sz1, sg1, a1⟩ | ⟨sg1, a1⟩ | ⟨fs1, a1⟩ | ⟨t, a1⟩ | ⟨t, n1, a1⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a1⟩ | ⟨id, a1⟩ <;> cases_sizes <;>
      simp [Cop.semCast, Cop.classifyCast, Archi.ptr64, castIntInt_of_wtInt hn] <;>
      exact bool_of_wtInt hn
  | void => simp [Cop.semCast, Cop.classifyCast]
  | undef => unfold Cop.semCast; split <;> simp
  | _ =>
    rcases t1 with _ | ⟨sz1, sg1, a1⟩ | ⟨sg1, a1⟩ | ⟨fs1, a1⟩ | ⟨t, a1⟩ | ⟨t, n1, a1⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a1⟩ | ⟨id, a1⟩ <;> cases_sizes <;>
      simp_all [Cop.semCast, Cop.classifyCast, Archi.ptr64] <;>
      (try split) <;> (try simp_all) <;> exact Classical.em _

/-- `Ctyping.sem_cast_already_typed_idem` -/
theorem sem_cast_already_typed_idem {v : Val} {t1 t2 : Ty} {m : Mem} {v' : Val}
    (h : Cop.semCast v t1 t2 m = some v') (hv : WtVal v t2) : v' = v := by
  rcases sem_cast_already_typed (t1 := t1) (m := m) hv with e | e <;> rw [e] at h
  · exact (Option.some.inj h).symm
  · cases h

end Ctyping
end CC
