/-
  Expression simplification: semantic preservation — port of
  `cfrontend/SimplExprproof.v`, part 4: the matching between continuations
  and states (`match_cont`, `match_cont_exp`, `match_states`), the translation
  of `switch` selection, the commutation between the translation and
  `find_label`, and the anti-stuttering measure.

  Differences from Rocq:
  * whole-program statement: every function is translated with the
    composite environment `ce` of the program, so the composite-environment
    index of `match_cont` and the `linkorder` hypotheses disappear (and with
    them `match_cont_is_call_cont`);
  * `match_states` is parameterized by the source program and the target
    global environment.
-/
import CCLib.cfrontend.SimplExprproofSmart

namespace CC
namespace SimplExpr

open Destination SetDestination Cstrategy

/-! ## Matching between continuations -/

section MATCH
variable (ce : CompositeEnv) (tge : CGenv)

mutual
/-- `SimplExprproof.match_cont` -/
inductive MatchCont : Csem.Cont → Cont → Prop where
  | Kstop : MatchCont .Kstop .Kstop
  | Kseq (s k ts tk) : TrStmt ce s ts → MatchCont k tk → MatchCont (.Kseq s k) (.Kseq ts tk)
  | Kwhile2 (r s k s' ts tk) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt ce s ts → MatchCont k tk →
      MatchCont (.Kwhile2 r s k) (.Kloop1 (.Ssequence s' ts) .Sskip tk)
  | Kdowhile1 (r s k s' ts tk) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt ce s ts → MatchCont k tk →
      MatchCont (.Kdowhile1 r s k) (.Kloop1 ts s' tk)
  | Kfor3 (r s3 s k ts3 s' ts tk) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt ce s3 ts3 → TrStmt ce s ts → MatchCont k tk →
      MatchCont (.Kfor3 r s3 s k) (.Kloop1 (.Ssequence s' ts) ts3 tk)
  | Kfor4 (r s3 s k ts3 s' ts tk) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt ce s3 ts3 → TrStmt ce s ts → MatchCont k tk →
      MatchCont (.Kfor4 r s3 s k) (.Kloop2 (.Ssequence s' ts) ts3 tk)
  | Kswitch2 (k tk) : MatchCont k tk → MatchCont (.Kswitch2 k) (.Kswitch tk)
  | Kcall (f e C ty k optid tf le sl tk a dest tmps) :
      TrFunction ce f tf → LeftContext .RV .RV C →
      (∀ v m, TrTop ce tge e (setOpttemp optid v le) m dest (C (.Eval v ty)) sl a tmps) →
      MatchContExp dest a k tk →
      MatchCont (.Kcall f e C ty k) (.Kcall optid tf e le (Kseqlist sl tk))

/-- `SimplExprproof.match_cont_exp` -/
inductive MatchContExp : Destination → Expr → Csem.Cont → Cont → Prop where
  | Kdo (k a tk) : MatchCont k tk → MatchContExp .For_effects a (.Kdo k) tk
  | Kifthenelse_empty (a k tk) :
      MatchCont k tk → MatchContExp .For_val a (.Kifthenelse .Sskip .Sskip k) (.Kseq .Sskip tk)
  | Kifthenelse_1 (a s1 s2 k ts1 ts2 tk) :
      TrStmt ce s1 ts1 → TrStmt ce s2 ts2 → MatchCont k tk →
      MatchContExp .For_val a (.Kifthenelse s1 s2 k) (.Kseq (.Sifthenelse a ts1 ts2) tk)
  | Kwhile1 (r s k s' a ts tk) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt ce s ts → MatchCont k tk →
      MatchContExp .For_val a (.Kwhile1 r s k)
        (.Kseq (makeif a .Sskip .Sbreak) (.Kseq ts (.Kloop1 (.Ssequence s' ts) .Sskip tk)))
  | Kdowhile2 (r s k s' a ts tk) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt ce s ts → MatchCont k tk →
      MatchContExp .For_val a (.Kdowhile2 r s k) (.Kseq (makeif a .Sskip .Sbreak) (.Kloop2 ts s' tk))
  | Kfor2 (r s3 s k s' a ts3 ts tk) :
      TrIf ce r .Sskip .Sbreak s' → TrStmt ce s3 ts3 → TrStmt ce s ts → MatchCont k tk →
      MatchContExp .For_val a (.Kfor2 r s3 s k)
        (.Kseq (makeif a .Sskip .Sbreak) (.Kseq ts (.Kloop1 (.Ssequence s' ts) ts3 tk)))
  | Kswitch1 (ls k a tls tk) :
      TrLblstmts ce ls tls → MatchCont k tk →
      MatchContExp .For_val a (.Kswitch1 ls k) (.Kseq (.Sswitch a tls) tk)
  | Kreturn (k a tk) :
      MatchCont k tk → MatchContExp .For_val a (.Kreturn k) (.Kseq (.Sreturn (some a)) tk)
end

variable {ce tge}

/-- `SimplExprproof.match_cont_call_cont` -/
theorem match_cont_call_cont {k tk} (h : MatchCont ce tge k tk) :
    MatchCont ce tge (Csem.callCont k) (callCont tk) := by
  cases h with
  | Kstop => exact .Kstop
  | Kseq _ _ _ _ _ h => dsimp only [Csem.callCont, callCont]; exact match_cont_call_cont h
  | Kwhile2 _ _ _ _ _ _ _ _ h => dsimp only [Csem.callCont, callCont]; exact match_cont_call_cont h
  | Kdowhile1 _ _ _ _ _ _ _ _ h => dsimp only [Csem.callCont, callCont]; exact match_cont_call_cont h
  | Kfor3 _ _ _ _ _ _ _ _ _ _ _ h => dsimp only [Csem.callCont, callCont]; exact match_cont_call_cont h
  | Kfor4 _ _ _ _ _ _ _ _ _ _ _ h => dsimp only [Csem.callCont, callCont]; exact match_cont_call_cont h
  | Kswitch2 _ _ h => dsimp only [Csem.callCont, callCont]; exact match_cont_call_cont h
  | Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 => exact .Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

end MATCH

/-! ## Matching between states -/

/-- `SimplExprproof.match_states` -/
inductive MatchStates (p : Csyntax.Program) (tge : CGenv) : Csem.State → State → Prop where
  | exprstates (f r k e m tf sl tk le dest a tmps) :
      TrFunction p.prog_comp_env f tf →
      TrTop p.prog_comp_env tge e le m dest r sl a tmps →
      MatchContExp p.prog_comp_env tge dest a k tk →
      MatchStates p tge (.ExprState f r k e m) (.State tf .Sskip (Kseqlist sl tk) e le m)
  | regularstates (f s k e m tf ts tk le) :
      TrFunction p.prog_comp_env f tf →
      TrStmt p.prog_comp_env s ts →
      MatchCont p.prog_comp_env tge k tk →
      MatchStates p tge (.State f s k e m) (.State tf ts tk e le m)
  | callstates (fd args k m tfd tk) :
      TrFundef p fd tfd →
      MatchCont p.prog_comp_env tge k tk →
      MatchStates p tge (.Callstate fd args k m) (.Callstate tfd args tk m)
  | returnstates (res k m tk) :
      MatchCont p.prog_comp_env tge k tk →
      MatchStates p tge (.Returnstate res k m) (.Returnstate res tk m)
  | stuckstate (S) : MatchStates p tge .Stuckstate S

/-! ## Additional results on the translation of statements -/

section STMTS
variable {ce : CompositeEnv}

theorem tr_select_switch_default {ls tls} (h : TrLblstmts ce ls tls) :
    TrLblstmts ce (Csem.selectSwitchDefault ls) (selectSwitchDefault tls) := by
  cases h with
  | tr_ls_nil => exact .tr_ls_nil
  | tr_ls_cons c s ls ts tls h1 h2 =>
    cases c with
    | none => exact .tr_ls_cons _ _ _ _ _ h1 h2
    | some c => dsimp only [Csem.selectSwitchDefault, selectSwitchDefault]; exact tr_select_switch_default h2

theorem tr_select_switch_case (n : Z) {ls tls} (h : TrLblstmts ce ls tls) :
    match Csem.selectSwitchCase n ls with
    | none => selectSwitchCase n tls = none
    | some ls' => ∃ tls', selectSwitchCase n tls = some tls' ∧ TrLblstmts ce ls' tls' := by
  cases h with
  | tr_ls_nil => rfl
  | tr_ls_cons c s ls ts tls h1 h2 =>
    cases c with
    | none =>
      dsimp only [Csem.selectSwitchCase, selectSwitchCase]; exact tr_select_switch_case n h2
    | some c =>
      simp only [Csem.selectSwitchCase, selectSwitchCase]
      by_cases hc : c = n
      · simp only [hc, if_true]; exact ⟨_, rfl, .tr_ls_cons _ _ _ _ _ h1 h2⟩
      · simp only [hc, if_false]; exact tr_select_switch_case n h2

/-- `SimplExprproof.tr_select_switch` -/
theorem tr_select_switch (n : Z) {ls tls} (h : TrLblstmts ce ls tls) :
    TrLblstmts ce (Csem.selectSwitch n ls) (selectSwitch n tls) := by
  have hc := tr_select_switch_case n h
  unfold Csem.selectSwitch selectSwitch
  split
  · rename_i ls' hls
    rw [hls] at hc
    obtain ⟨tls', h1, h2⟩ := hc
    rw [h1]; exact h2
  · rename_i hls
    rw [hls] at hc
    rw [hc]; exact tr_select_switch_default h

/-- `SimplExprproof.tr_seq_of_labeled_statement` -/
theorem tr_seq_of_labeled_statement {ls tls} (h : TrLblstmts ce ls tls) :
    TrStmt ce (Csem.seqOfLabeledStatement ls) (seqOfLabeledStatement tls) := by
  cases h with
  | tr_ls_nil => exact .tr_skip
  | tr_ls_cons _ _ _ _ _ h1 h2 =>
    dsimp only [Csem.seqOfLabeledStatement, seqOfLabeledStatement]
    exact .tr_seq _ _ _ _ h1 (tr_seq_of_labeled_statement h2)

end STMTS

/-! ## Commutation between the translation and `find_label` -/

section FIND_LABEL
variable (lbl : Ident)

/-- `SimplExprproof.nolabel` -/
def Nolabel (s : Stmt) : Prop := ∀ k, findLabel lbl s k = none

/-- `SimplExprproof.nolabel_list` -/
def NolabelList : List Stmt → Prop
  | [] => True
  | s1 :: sl' => Nolabel lbl s1 ∧ NolabelList sl'

variable {lbl}

/-- `SimplExprproof.nolabel_list_app` -/
theorem nolabel_list_app {sl2 : List Stmt} :
    ∀ {sl1 : List Stmt}, NolabelList lbl sl1 → NolabelList lbl sl2 → NolabelList lbl (sl1 ++ sl2)
  | [], _, h2 => h2
  | _ :: _, ⟨h1, h1'⟩, h2 => ⟨h1, nolabel_list_app h1' h2⟩

theorem makeseqRec_nolabel : ∀ (sl : List Stmt) {s : Stmt}, Nolabel lbl s →
    NolabelList lbl sl → Nolabel lbl (makeseqRec s sl)
  | [], _, hs, _ => hs
  | s' :: l, s, hs, ⟨h1, h2⟩ => makeseqRec_nolabel l (fun k => by
      simp only [findLabel, hs (.Kseq s' k)]; exact h1 k) h2

/-- `SimplExprproof.makeseq_nolabel` -/
theorem makeseq_nolabel {sl : List Stmt} (h : NolabelList lbl sl) : Nolabel lbl (makeseq sl) :=
  makeseqRec_nolabel sl (fun _ => by simp [findLabel]) h

/-- `SimplExprproof.makeif_nolabel` -/
theorem makeif_nolabel {a s1 s2} (h1 : Nolabel lbl s1) (h2 : Nolabel lbl s2) :
    Nolabel lbl (makeif a s1 s2) := by
  intro k
  unfold makeif
  split
  · split
    · split
      · exact h1 k
      · exact h2 k
    · simp only [findLabel, h1 k]; exact h2 k
  · simp only [findLabel, h1 k]; exact h2 k

/-- `SimplExprproof.make_set_nolabel` -/
theorem make_set_nolabel (bf : Bitfield) (t : Ident) (a : Expr) : Nolabel lbl (makeSet bf t a) := by
  intro k; unfold makeSet; split <;> rfl

/-- `SimplExprproof.make_assign_nolabel` -/
theorem make_assign_nolabel (bf : Bitfield) (l r : Expr) : Nolabel lbl (makeAssign bf l r) := by
  intro k; unfold makeAssign; split <;> rfl

/-- `SimplExprproof.tr_rvalof_nolabel` -/
theorem tr_rvalof_nolabel {ce ty a sl a' tmp} (h : TrRvalof ce ty a sl a' tmp) :
    NolabelList lbl sl := by
  cases h with
  | tr_rvalof_nonvol => trivial
  | tr_rvalof_vol => exact ⟨make_set_nolabel _ _ _, trivial⟩

/-- `SimplExprproof.nolabel_do_set` -/
theorem nolabel_do_set : ∀ (sd : SetDestination) (a : Expr), NolabelList lbl (doSet sd a)
  | .SDbase _ _ _, _ => ⟨fun _ => rfl, trivial⟩
  | .SDcons _ _ _ sd, _ => ⟨fun _ => rfl, nolabel_do_set sd _⟩

/-- `SimplExprproof.nolabel_final` -/
theorem nolabel_final (dst : Destination) (a : Expr) : NolabelList lbl (final dst a) := by
  cases dst with
  | For_val => trivial
  | For_effects => trivial
  | For_set sd => exact nolabel_do_set sd a

theorem nolabel_cons {s sl} (h1 : Nolabel lbl s) (h2 : NolabelList lbl sl) :
    NolabelList lbl (s :: sl) := ⟨h1, h2⟩

theorem nolabel_skip : Nolabel lbl .Sskip := fun _ => rfl
theorem nolabel_set (t : Ident) (a : Expr) : Nolabel lbl (.Sset t a) := fun _ => rfl
theorem nolabel_call (o : Option Ident) (a : Expr) (al : List Expr) :
    Nolabel lbl (.Scall o a al) := fun _ => rfl
theorem nolabel_builtin (o : Option Ident) (ef : ExtFun) (tyl : List Ty) (al : List Expr) :
    Nolabel lbl (.Sbuiltin o ef tyl al) := fun _ => rfl

/-- `NoLabelTac` -/
local syntax "nolabel_tac" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| nolabel_tac) => `(tactic| first
    | exact trivial
    | exact nolabel_final _ _
    | exact nolabel_do_set _ _
    | (apply nolabel_cons <;> nolabel_tac)
    | (apply nolabel_list_app <;> nolabel_tac)
    | (apply makeseq_nolabel; nolabel_tac)
    | (apply makeif_nolabel <;> nolabel_tac)
    | exact nolabel_skip
    | exact nolabel_set _ _
    | exact nolabel_call _ _ _
    | exact nolabel_builtin _ _ _ _
    | exact make_set_nolabel _ _ _
    | exact make_assign_nolabel _ _ _
    | (exact fun _ => rfl)
    | exact tr_rvalof_nolabel ‹TrRvalof _ _ _ _ _ _›
    | exact tr_find_label_expr ‹TrExpr _ _ _ _ _ _ _›
    | exact tr_find_label_exprlist ‹TrExprlist _ _ _ _ _ _›)

variable {ce : CompositeEnv}

mutual
/-- `SimplExprproof.tr_find_label_expr` (expressions) -/
theorem tr_find_label_expr {le dst r sl a tmps} (h : TrExpr ce le dst r sl a tmps) :
    NolabelList lbl sl := by
  cases h <;> nolabel_tac

/-- `SimplExprproof.tr_find_label_expr` (expression lists) -/
theorem tr_find_label_exprlist {le rl sl al tmps} (h : TrExprlist ce le rl sl al tmps) :
    NolabelList lbl sl := by
  cases h with
  | tr_nil => trivial
  | tr_cons =>
    exact nolabel_list_app (tr_find_label_expr ‹TrExpr _ _ _ _ _ _ _›)
      (tr_find_label_exprlist ‹TrExprlist _ _ _ _ _ _›)
end

section TOP
variable {tge : CGenv}

/-- `SimplExprproof.tr_find_label_top` -/
theorem tr_find_label_top {e le m dst r sl a tmps} (h : TrTop ce tge e le m dst r sl a tmps) :
    NolabelList lbl sl := by
  cases h with
  | tr_top_val_val => trivial
  | tr_top_base _ _ _ _ _ h => exact tr_find_label_expr h

end TOP

/-- Some Clight global environment (the translation relations quantify over
    all of them). -/
def someCGenv : CGenv := { genv_genv := Genv.emptyGenv [], genv_cenv := PTree.empty }

/-- `SimplExprproof.tr_find_label_expression` -/
theorem tr_find_label_expression {r s a} (h : TrExpression ce r s a) : Nolabel lbl s := by
  cases h with
  | tr_expression_intro =>
    rename_i h
    exact makeseq_nolabel (tr_find_label_top (h someCGenv emptyEnv PTree.empty Mem.empty))

/-- `SimplExprproof.tr_find_label_expr_stmt` -/
theorem tr_find_label_expr_stmt {r s} (h : TrExprStmt ce r s) : Nolabel lbl s := by
  cases h with
  | tr_expr_stmt_intro =>
    rename_i h
    exact makeseq_nolabel (tr_find_label_top (h someCGenv emptyEnv PTree.empty Mem.empty))

/-- `SimplExprproof.tr_find_label_if` -/
theorem tr_find_label_if {r s} (h : TrIf ce r .Sskip .Sbreak s) : Nolabel lbl s := by
  cases h with
  | tr_if_intro =>
    rename_i h
    exact makeseq_nolabel (nolabel_list_app
      (tr_find_label_top (h someCGenv emptyEnv PTree.empty Mem.empty))
      ⟨makeif_nolabel nolabel_skip (fun _ => rfl), trivial⟩)

/-- The conclusion of `SimplExprproof.tr_find_label`. -/
def FLRes (ce : CompositeEnv) (tge : CGenv) :
    Option (Csyntax.Stmt × Csem.Cont) → Option (Stmt × Cont) → Prop
  | none, TA => TA = none
  | some (s', k'), TA => ∃ ts' tk', TA = some (ts', tk') ∧ TrStmt ce s' ts' ∧ MatchCont ce tge k' tk'

section FL
variable {tge : CGenv}

theorem fl_seq {A : Option (Csyntax.Stmt × Csem.Cont)} {TA : Option (Stmt × Cont)} {B TB}
    (hA : FLRes ce tge A TA) (hB : FLRes ce tge B TB) :
    FLRes ce tge (match (generalizing := false) A with | some sk => some sk | none => B)
      (match (generalizing := false) TA with | some sk => some sk | none => TB) := by
  cases A with
  | none => simp only [FLRes] at hA; subst hA; exact hB
  | some sk =>
    obtain ⟨s', k'⟩ := sk
    obtain ⟨ts', tk', h1, h2, h3⟩ := hA
    subst h1
    exact ⟨ts', tk', rfl, h2, h3⟩

theorem fl_none_right {A : Option (Csyntax.Stmt × Csem.Cont)} {TA : Option (Stmt × Cont)}
    (hA : FLRes ce tge A TA) :
    FLRes ce tge A (match (generalizing := false) TA with | some sk => some sk | none => none) := by
  cases TA <;> exact hA

end FL

section FL2
variable {tge : CGenv}

local macro "fl_simp" : tactic =>
  `(tactic| simp only [Csem.findLabel, findLabel, Csem.findLabelLs, findLabelLs])

mutual
/-- `SimplExprproof.tr_find_label` -/
theorem tr_find_label {s ts} (h : TrStmt ce s ts) {k tk} (hk : MatchCont ce tge k tk) :
    FLRes ce tge (Csem.findLabel lbl s k) (findLabel lbl ts tk) := by
  match h with
  | .tr_skip => exact rfl
  | .tr_do _ _ h1 =>
    have := tr_find_label_expr_stmt (lbl := lbl) h1 tk
    fl_simp; exact this
  | .tr_seq _ _ _ _ h1 h2 =>
    fl_simp
    exact fl_seq (tr_find_label h1 (.Kseq _ _ _ _ h2 hk)) (tr_find_label h2 hk)
  | .tr_ifthenelse_empty _ _ _ h1 =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_expression h1
    fl_simp; simp only [hnl]; exact rfl
  | .tr_ifthenelse _ _ _ _ _ _ _ h0 h1 h2 =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_expression h0
    fl_simp; simp only [hnl]
    exact fl_seq (tr_find_label h1 hk) (tr_find_label h2 hk)
  | .tr_while _ _ _ _ hif h1 =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_if hif
    fl_simp; simp only [hnl]
    exact fl_none_right (tr_find_label h1 (.Kwhile2 _ _ _ _ _ _ hif h1 hk))
  | .tr_dowhile _ _ _ _ hif h1 =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_if hif
    fl_simp; simp only [hnl]
    exact fl_none_right (tr_find_label h1 (.Kdowhile1 _ _ _ _ _ _ hif h1 hk))
  | .tr_for_1 _ _ _ _ _ _ hif h3 h4 =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_if hif
    fl_simp; simp only [hnl]
    exact fl_seq (tr_find_label h4 (.Kfor3 _ _ _ _ _ _ _ _ hif h3 h4 hk))
      (tr_find_label h3 (.Kfor4 _ _ _ _ _ _ _ _ hif h3 h4 hk))
  | .tr_for_2 _ _ _ _ _ _ _ _ hif _ h1 h3 h4 =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_if hif
    fl_simp; simp only [hnl]
    exact fl_seq (tr_find_label h1 (.Kseq _ _ _ _ (.tr_for_1 _ _ _ _ _ _ hif h3 h4) hk))
      (fl_seq (tr_find_label h4 (.Kfor3 _ _ _ _ _ _ _ _ hif h3 h4 hk))
        (tr_find_label h3 (.Kfor4 _ _ _ _ _ _ _ _ hif h3 h4 hk)))
  | .tr_break => exact rfl
  | .tr_continue => exact rfl
  | .tr_return_none => exact rfl
  | .tr_return_some _ _ _ h1 =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_expression h1
    fl_simp; simp only [hnl]; exact rfl
  | .tr_switch _ _ _ _ _ h1 hls =>
    have hnl : ∀ k, findLabel lbl _ k = none := tr_find_label_expression h1
    fl_simp; simp only [hnl]
    exact tr_find_label_ls hls (.Kswitch2 _ _ hk)
  | .tr_label l _ _ h1 =>
    fl_simp
    by_cases hl : lbl = l
    · simp only [hl, if_true]; exact ⟨_, _, rfl, h1, hk⟩
    · simp only [hl, if_false]; exact tr_find_label h1 hk
  | .tr_goto _ => exact rfl

/-- `SimplExprproof.tr_find_label_ls` -/
theorem tr_find_label_ls {s ts} (h : TrLblstmts ce s ts) {k tk} (hk : MatchCont ce tge k tk) :
    FLRes ce tge (Csem.findLabelLs lbl s k) (findLabelLs lbl ts tk) := by
  match h with
  | .tr_ls_nil => exact rfl
  | .tr_ls_cons _ _ _ _ _ h1 h2 =>
    fl_simp
    exact fl_seq (tr_find_label h1 (.Kseq _ _ _ _ (tr_seq_of_labeled_statement h2) hk))
      (tr_find_label_ls h2 hk)
end

end FL2

end FIND_LABEL

end SimplExpr
end CC
