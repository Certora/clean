/-
  Correctness of instruction selection — port of `backend/Selectionproof.v`,
  part 6: the relation between Cminor and CminorSel states and the facts it
  needs: `classify_call_correct`, `match_cont`/`match_call_cont`,
  `match_states`, `match_states_skip`, `call_cont_commut`,
  `match_is_call_cont`, `nolabel`, `classify_stmt_nolabel`,
  `if_conversion_base_nolabel`, `if_conversion_nolabel`,
  `sel_builtin_nolabel`, `find_label_commut`.

  As in Rocq, the relation is linking-aware: each function frame records the
  definition map `dm` (Rocq: `prog_defmap cunit`) and helper record `hf` it
  was translated with.  Rocq's side condition on the compilation unit
  (`linkorder cunit prog` and `helper_functions_declared cunit hf`) is
  abstracted as the parameter `Adm dm hf`, instantiated in
  `SelectionproofMain`.
-/
import CCLib.backend.SelectionproofIfconv
import CCLib.common.LinkingFundef

namespace CC
namespace Selectionproof

open Op CminorSel SelectOp Selection Cminortyping Smallstep

theorem res_bind_ok {A B : Type} {x : Res A} {f : A → Res B} {b : B} :
    (x >>= f) = Res.OK b ↔ ∃ a, x = .OK a ∧ f a = .OK b := by
  cases x <;> simp [bind, Res.bind]

/-! ### Calls -/

/-- `Selectionproof.classify_call_correct`: calls classified with the definitions of a
compilation unit `cu` of the program `p`. -/
theorem classify_call_correct (p : Cminor.Program) {cu : Cminor.Program}
    (LINK : Linker.linkorder cu p) {sp : Val} {e : Cminor.Env} {m : Mem}
    {a : Cminor.Expr} {v : Val} {fd : Cminor.Fundef}
    (ha : Cminor.EvalExpr p.globalenv sp e m a v) (hfd : Genv.findFunct p.globalenv v = some fd) :
    match classifyCall cu.defmap a with
    | .Call_default => True
    | .Call_imm id => ∃ b, Genv.findSymbol p.globalenv id = some b ∧ v = .Vptr b Integers.Ptrofs.zero
    | .Call_builtin ef => fd = .External ef := by
  unfold classifyCall
  rcases hea : exprIsAddrofIdent a with _ | id
  · trivial
  · have := expr_is_addrof_ident_correct hea
    subst this
    cases ha with
    | Econst _ _ hv =>
      simp only [Cminor.evalConstant, Option.some.injEq] at hv
      subst hv
      unfold Genv.symbolAddress at hfd ⊢
      rcases hfs : Genv.findSymbol p.globalenv id with _ | b
      · rw [hfs] at hfd; cases hfd
      · rw [hfs] at hfd
        have DFL : ∃ b1, Genv.findSymbol p.globalenv id = some b1 ∧
            Val.Vptr b Integers.Ptrofs.zero = .Vptr b1 Integers.Ptrofs.zero := ⟨b, hfs, rfl⟩
        dsimp only
        rcases hg : PTree.get id (ASTProgram.defmap cu) with _ | ⟨_ | ef⟩ | gv
        · exact DFL
        · exact DFL
        · dsimp only
          rcases hin : ef.inline with _ | _
          · exact DFL
          · show fd = .External ef
            obtain ⟨gd, D, LO⟩ := Linking.prog_defmap_linkorder LINK hg
            have hgd : gd = .Gfun (.External ef) := by
              change Linking.LinkorderDef _ _ at LO
              cases LO with
              | gfun h2 =>
                change Linking.LinkorderASTFundef _ _ at h2
                cases h2 with
                | refl => rfl
                | ext_int => simp [ExtFun.inline] at hin
            subst hgd
            rw [Genv.findFunct_findFunctPtr] at hfd
            obtain ⟨b', X, Y⟩ := (Genv.find_def_symbol p.prog_public p.prog_defs id _).mp D
            have hb : b' = b := by
              have : Genv.findSymbol p.globalenv id = some b' := X
              rw [hfs] at this; cases this; rfl
            subst hb
            have : Genv.findFunctPtr p.globalenv b' = some (.External ef) :=
              (Genv.findFunctPtr_iff _ _ _).mpr Y
            have h2 : Genv.findFunctPtr p.globalenv b' = some fd := hfd
            rw [this] at h2; cases h2; rfl
        · exact DFL

/-! ### Simulation relation -/

section MATCH
variable (opts : Options) (Adm : PTree Globdef → SplitLong.HelperFunctions → Prop)

mutual
/-- `Selectionproof.match_cont` (the continuation of a function translated with the
definitions `dm` and helpers `hf`) -/
inductive MatchCont : PTree Globdef → SplitLong.HelperFunctions → KnownIdents → Typenv →
    Cminor.Cont → CminorSel.Cont → Prop where
  | seq {dm hf} (ki env s kont s' k k') : selStmt opts dm ki env s kont = .OK s' →
      MatchCont dm hf ki env k k' → MatchCont dm hf ki env (.Kseq s k) (.Kseq s' k')
  | block {dm hf} (ki env k k') : MatchCont dm hf ki env k k' →
      MatchCont dm hf ki env (.Kblock k) (.Kblock k')
  | other {dm hf} (ki env k k') : MatchCallCont k k' → MatchCont dm hf ki env k k'

/-- `Selectionproof.match_call_cont` -/
inductive MatchCallCont : Cminor.Cont → CminorSel.Cont → Prop where
  | stop : MatchCallCont .Kstop .Kstop
  | call {dm hf} (env id f sp e k f' e' k') : selFunction opts dm hf f = .OK f' →
      typeFunction f = .OK env → MatchCont dm hf (Selection.knownId f) env k k' →
      EnvLessdef e e' → Adm dm hf →
      MatchCallCont (.Kcall id f sp e k) (.Kcall id f' sp e' k')
end

variable (ge : Cminor.CGenv)

/-- `Selectionproof.match_states` -/
inductive MatchStates : Cminor.State → CminorSel.State → Prop where
  | state {dm hf} (f f' s kont k s' k' sp e m e' m' env) :
      selFunction opts dm hf f = .OK f' → typeFunction f = .OK env →
      selStmt opts dm (Selection.knownId f) env s kont = .OK s' →
      MatchCont opts Adm dm hf (Selection.knownId f) env k k' → EnvLessdef e e' →
      Mem.Extends m m' → Adm dm hf →
      MatchStates (.State f s k sp e m) (.State f' s' k' sp e' m')
  | callstate {dm hf} (f f' args args' k k' m m') :
      selFundef opts dm hf f = .OK f' → MatchCallCont opts Adm k k' →
      Val.LessdefList args args' → Mem.Extends m m' → Adm dm hf →
      MatchStates (.Callstate f args k m) (.Callstate f' args' k' m')
  | returnstate (v v' k k' m m') :
      MatchCallCont opts Adm k k' → Val.Lessdef v v' → Mem.Extends m m' →
      MatchStates (.Returnstate v k m) (.Returnstate v' k' m')
  | builtin_1 {dm hf} (ef args optid f sp e k m al f' e' k' m' env) :
      selFunction opts dm hf f = .OK f' → typeFunction f = .OK env →
      MatchCont opts Adm dm hf (Selection.knownId f) env k k' →
      Cminor.EvalExprlist ge sp e m al args → EnvLessdef e e' → Mem.Extends m m' →
      Adm dm hf →
      MatchStates (.Callstate (.External ef) args (.Kcall optid f sp e k) m)
        (.State f' (selBuiltin opts optid ef al) k' sp e' m')
  | builtin_2 {dm hf} (v v' optid f sp e k m f' e' m' k' env) :
      selFunction opts dm hf f = .OK f' → typeFunction f = .OK env →
      MatchCont opts Adm dm hf (Selection.knownId f) env k k' →
      Val.Lessdef v v' → EnvLessdef (Cminor.setOptvar optid v e) e' → Mem.Extends m m' →
      Adm dm hf →
      MatchStates (.Returnstate v (.Kcall optid f sp e k) m) (.State f' .Sskip k' sp e' m')

variable {opts Adm ge} {dm : PTree Globdef} {hf : SplitLong.HelperFunctions}

/-- `Selectionproof.match_states_skip` -/
theorem match_states_skip {f : Cminor.Function} {f' : CminorSel.Function} {k : Cminor.Cont}
    {k' : CminorSel.Cont} {sp : Val} {e : Cminor.Env} {m : Mem} {e' : Cminor.Env} {m' : Mem}
    {env : Typenv} (ADM : Adm dm hf) (TF : selFunction opts dm hf f = .OK f')
    (TYF : typeFunction f = .OK env)
    (MC : MatchCont opts Adm dm hf (Selection.knownId f) env k k') (LD : EnvLessdef e e')
    (ME : Mem.Extends m m') :
    MatchStates opts Adm ge (.State f .Sskip k sp e m) (.State f' .Sskip k' sp e' m') :=
  .state _ _ _ .Sskip _ _ _ _ _ _ _ _ _ TF TYF rfl MC LD ME ADM

/-- `Selectionproof.call_cont_commut` -/
theorem call_cont_commut {ki : KnownIdents} {env : Typenv} :
    ∀ {k : Cminor.Cont} {k' : CminorSel.Cont}, MatchCont opts Adm dm hf ki env k k' →
    MatchCallCont opts Adm (Cminor.callCont k) (CminorSel.callCont k')
  | .Kstop, _, h => by
    cases h with
    | other _ _ _ _ hc => cases hc; exact .stop
  | .Kseq _ _, _, h => by
    cases h with
    | seq _ _ _ _ _ _ _ _ h' => have := call_cont_commut h'; exact this
    | other _ _ _ _ hc => cases hc
  | .Kblock _, _, h => by
    cases h with
    | block _ _ _ _ h' => have := call_cont_commut h'; exact this
    | other _ _ _ _ hc => cases hc
  | .Kcall .., _, h => by
    cases h with
    | other _ _ _ _ hc =>
      cases hc with
      | call _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 => exact .call _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5

/-- `Selectionproof.match_is_call_cont` -/
theorem match_is_call_cont {ki : KnownIdents} {env : Typenv} {k : Cminor.Cont}
    {k' : CminorSel.Cont} (h : MatchCont opts Adm dm hf ki env k k')
    (hc : Cminor.isCallCont k = true) :
    MatchCallCont opts Adm k k' ∧ CminorSel.isCallCont k' = true := by
  cases h with
  | seq => cases hc
  | block => cases hc
  | other _ _ _ _ h =>
    refine ⟨h, ?_⟩
    cases h <;> rfl

/-! ### Labels -/

/-- `Selectionproof.nolabel` -/
def NoLabel (s : Cminor.Stmt) : Prop := ∀ lbl k, Cminor.findLabel lbl s k = none
/-- `Selectionproof.nolabel'` -/
def NoLabel' (s : CminorSel.Stmt) : Prop := ∀ lbl k, CminorSel.findLabel lbl s k = none

/-- `Selectionproof.classify_stmt_nolabel` -/
theorem classify_stmt_nolabel : ∀ (s : Cminor.Stmt), classifyStmt s ≠ .SCother → NoLabel s
  | .Sskip, _ => fun _ _ => rfl
  | .Sassign _ _, _ => fun _ _ => rfl
  | .Sbuiltin _ _ _, _ => fun _ _ => rfl
  | .Sseq s1 s2, h => by
    have CL : classifyStmt s1 ≠ .SCother ∧ classifyStmt s2 ≠ .SCother := by
      simp only [classifyStmt] at h
      revert h
      cases classifyStmt s1 <;> cases classifyStmt s2 <;> simp
    have N1 := classify_stmt_nolabel s1 CL.1
    have N2 := classify_stmt_nolabel s2 CL.2
    intro lbl k
    simp only [Cminor.findLabel]
    rw [N1 lbl (.Kseq s2 k)]
    exact N2 lbl k
  | .Sstore .., h => by simp [classifyStmt] at h
  | .Scall .., h => by simp [classifyStmt] at h
  | .Stailcall .., h => by simp [classifyStmt] at h
  | .Sifthenelse .., h => by simp [classifyStmt] at h
  | .Sloop _, h => by simp [classifyStmt] at h
  | .Sblock _, h => by simp [classifyStmt] at h
  | .Sexit _, h => by simp [classifyStmt] at h
  | .Sswitch .., h => by simp [classifyStmt] at h
  | .Sreturn _, h => by simp [classifyStmt] at h
  | .Slabel .., h => by simp [classifyStmt] at h
  | .Sgoto _, h => by simp [classifyStmt] at h

/-- `Selectionproof.if_conversion_base_nolabel` -/
theorem if_conversion_base_nolabel {ki : KnownIdents} {env : Typenv} {a : Cminor.Expr}
    {id : Ident} {a1 a2 : Cminor.Expr} {kont s : CminorSel.Stmt}
    (h : ifConversionBase opts ki env a id a1 a2 kont = some s) : NoLabel' s := by
  unfold ifConversionBase at h
  dsimp only at h
  split at h
  · cases h; intro _ _; rfl
  · cases h

/-- `Selectionproof.if_conversion_nolabel` -/
theorem if_conversion_nolabel {ki : KnownIdents} {env : Typenv} {a : Cminor.Expr}
    {s1 s2 : Cminor.Stmt} {kont s : CminorSel.Stmt}
    (h : ifConversion opts ki env a s1 s2 kont = some s) :
    NoLabel s1 ∧ NoLabel s2 ∧ NoLabel' s := by
  unfold ifConversion at h
  rcases h1 : classifyStmt s1 with _ | ⟨id1, b1⟩ | _ <;>
    rcases h2 : classifyStmt s2 with _ | ⟨id2, b2⟩ | _ <;>
    rw [h1, h2] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  · exact ⟨classify_stmt_nolabel s1 (by rw [h1]; simp), classify_stmt_nolabel s2 (by rw [h2]; simp),
      if_conversion_base_nolabel h⟩
  · exact ⟨classify_stmt_nolabel s1 (by rw [h1]; simp), classify_stmt_nolabel s2 (by rw [h2]; simp),
      if_conversion_base_nolabel h⟩
  · split at h
    · exact ⟨classify_stmt_nolabel s1 (by rw [h1]; simp),
        classify_stmt_nolabel s2 (by rw [h2]; simp), if_conversion_base_nolabel h⟩
    · cases h

/-- `Selectionproof.sel_builtin_nolabel` -/
theorem sel_builtin_nolabel (optid : Option Ident) (ef : ExtFun) (args : List Cminor.Expr) :
    NoLabel' (selBuiltin opts optid ef args) := by
  intro lbl k
  unfold selBuiltin
  split
  · split
    · split
      · split
        · rfl
        · rfl
      · rfl
    · rfl
  · rfl

theorem store_nolabel (chunk : Chunk) (a1 a2 : CminorSel.Expr) :
    NoLabel' (Selection.store opts chunk a1 a2) := by
  intro lbl k
  unfold Selection.store
  rfl

/-- The conclusion of `Selectionproof.find_label_commut`. -/
inductive FindLabelCommut (ki : KnownIdents) (env : Typenv) :
    Option (Cminor.Stmt × Cminor.Cont) → Option (CminorSel.Stmt × CminorSel.Cont) → Prop where
  | none : FindLabelCommut ki env none none
  | some (s1 k1 s1' k1' kont1) : selStmt opts dm ki env s1 kont1 = .OK s1' →
      MatchCont opts Adm dm hf ki env k1 k1' → FindLabelCommut ki env (some (s1, k1)) (some (s1', k1'))

/-- `Selectionproof.find_label_commut` -/
theorem find_label_commut {ki : KnownIdents} {env : Typenv} (lbl : Cminor.Label) :
    ∀ (s : Cminor.Stmt) {kont : CminorSel.Stmt} {k : Cminor.Cont} {k' : CminorSel.Cont}
      {s' : CminorSel.Stmt},
    MatchCont opts Adm dm hf ki env k k' → selStmt opts dm ki env s kont = .OK s' →
    FindLabelCommut (opts := opts) (Adm := Adm) (dm := dm) (hf := hf) ki env (Cminor.findLabel lbl s k) (CminorSel.findLabel lbl s' k')
  | .Sskip, _, _, _, _, _, h => by cases h; exact .none
  | .Sassign .., _, _, _, _, _, h => by cases h; exact .none
  | .Sstore chunk addr rhs, _, _, k', _, _, h => by
    cases h; rw [store_nolabel chunk _ _ lbl k']; exact .none
  | .Scall optid sg fn args, _, _, k', _, _, h => by
    simp only [selStmt] at h; cases h
    rcases classifyCall dm fn with _ | id | ef
    · exact .none
    · exact .none
    · rw [sel_builtin_nolabel optid ef args lbl k']; exact .none
  | .Stailcall sg fn args, _, _, _, _, _, h => by
    simp only [selStmt] at h; cases h
    rcases classifyCall dm fn with _ | id | ef <;> exact .none
  | .Sbuiltin optid ef args, _, _, k', _, _, h => by
    simp only [selStmt] at h; cases h
    rw [sel_builtin_nolabel optid ef args lbl k']; exact .none
  | .Sseq s1 s2, kont, k, k', s', MC, h => by
    simp only [selStmt] at h
    obtain ⟨x, hx, h⟩ := res_bind_ok.mp h
    obtain ⟨x0, hx0, h⟩ := res_bind_ok.mp h
    cases h
    have IH1 := find_label_commut lbl s1 (k := .Kseq s2 k) (k' := .Kseq x k')
      (.seq _ _ _ _ _ _ _ hx MC) hx0
    simp only [Cminor.findLabel, CminorSel.findLabel]
    revert IH1
    generalize Cminor.findLabel lbl s1 (.Kseq s2 k) = o1
    generalize CminorSel.findLabel lbl x0 (.Kseq x k') = o2
    intro IH1
    cases IH1 with
    | none => exact find_label_commut lbl s2 MC hx
    | some _ _ _ _ _ h1 h2 => exact .some _ _ _ _ _ h1 h2
  | .Sifthenelse a s1 s2, kont, k, k', s', MC, h => by
    simp only [selStmt] at h
    split at h
    · next s0 hifc =>
      cases h
      obtain ⟨A, B, C⟩ := if_conversion_nolabel hifc
      simp only [Cminor.findLabel]
      rw [A lbl k, B lbl k, C lbl k']
      exact .none
    · obtain ⟨x, hx, h⟩ := res_bind_ok.mp h
      obtain ⟨x0, hx0, h⟩ := res_bind_ok.mp h
      cases h
      have IH1 := find_label_commut lbl s1 MC hx
      simp only [Cminor.findLabel, CminorSel.findLabel]
      revert IH1
      generalize Cminor.findLabel lbl s1 k = o1
      generalize CminorSel.findLabel lbl x k' = o2
      intro IH1
      cases IH1 with
      | none => exact find_label_commut lbl s2 MC hx0
      | some _ _ _ _ _ h1 h2 => exact .some _ _ _ _ _ h1 h2
  | .Sloop s1, kont, k, k', s', MC, h => by
    simp only [selStmt] at h
    obtain ⟨x, hx, h⟩ := res_bind_ok.mp h
    cases h
    simp only [Cminor.findLabel, CminorSel.findLabel]
    exact find_label_commut lbl s1 (.seq _ _ (.Sloop s1) .Sskip _ _ _
      (by simp only [selStmt, hx]; rfl) MC) hx
  | .Sblock s1, kont, k, k', s', MC, h => by
    simp only [selStmt] at h
    obtain ⟨x, hx, h⟩ := res_bind_ok.mp h
    cases h
    simp only [Cminor.findLabel, CminorSel.findLabel]
    exact find_label_commut lbl s1 (.block _ _ _ _ MC) hx
  | .Sexit _, _, _, _, _, _, h => by cases h; exact .none
  | .Sswitch b e cases dfl, _, _, _, _, _, h => by
    cases b <;> simp only [selStmt] at h <;> split at h <;> cases h <;> exact .none
  | .Sreturn none, _, _, _, _, _, h => by cases h; exact .none
  | .Sreturn (some _), _, _, _, _, _, h => by cases h; exact .none
  | .Slabel l s1, kont, k, k', s', MC, h => by
    simp only [selStmt] at h
    obtain ⟨x, hx, h⟩ := res_bind_ok.mp h
    cases h
    simp only [Cminor.findLabel, CminorSel.findLabel]
    by_cases hl : lbl = l
    · simp only [hl, if_true]
      exact .some _ _ _ _ kont hx MC
    · simp only [hl, if_false]
      exact find_label_commut lbl s1 MC hx
  | .Sgoto _, _, _, _, _, _, h => by cases h; exact .none

end MATCH

end Selectionproof
end CC
