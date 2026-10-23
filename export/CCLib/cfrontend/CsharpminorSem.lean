/-
  Small-step semantics of Csharpminor — port of the semantic part of
  `cfrontend/Csharpminor.v` (environments, continuations, states,
  `select_switch`, `find_label`, `alloc_variables`, `eval_var_addr`,
  `eval_expr`, `step`, `initial_state`, `final_state`, `semantics`).

  Rocq proves no properties of this semantics in `Csharpminor.v`; this file
  adds receptiveness and determinacy (`semantics_receptive`,
  `semantics_determinate`), which are proved the same way as for Cminor.

  Differences from Rocq: `is_call_cont` is a `Bool`; `list_norepet` /
  `list_disjoint` are `listNorepet` / `listDisjoint` from `CCLib.cfrontend.Clight`.
-/
import CCLib.cfrontend.Csharpminor
import CCLib.backend.CminorSem

namespace CC
namespace Csharpminor

open Smallstep

/-- `Csharpminor.genv` -/
abbrev CGenv := Genv Fundef Unit
/-- `Csharpminor.env` -/
abbrev Env := PTree (Block × Z)
/-- `Csharpminor.temp_env` -/
abbrev TempEnv := PTree Val

/-- `Csharpminor.empty_env` -/
def emptyEnv : Env := PTree.empty
/-- `Csharpminor.empty_temp_env` -/
def emptyTempEnv : TempEnv := PTree.empty

/-- `Csharpminor.create_undef_temps` -/
def createUndefTemps : List Ident → TempEnv
  | [] => PTree.empty
  | id :: temps' => PTree.set id .Vundef (createUndefTemps temps')

/-- `Csharpminor.bind_parameters` -/
def bindParameters : List Ident → List Val → TempEnv → Option TempEnv
  | [], [], le => some le
  | id :: xl, v :: vl, le => bindParameters xl vl (PTree.set id v le)
  | _, _, _ => none

/-- `Csharpminor.cont` -/
inductive Cont where
  | Kstop
  | Kseq (s : Stmt) (k : Cont)
  | Kblock (k : Cont)
  | Kcall (optid : Option Ident) (f : Function) (e : Env) (le : TempEnv) (k : Cont)

/-- `Csharpminor.state` -/
inductive State where
  | State (f : Function) (s : Stmt) (k : Cont) (e : Env) (le : TempEnv) (m : Mem)
  | Callstate (f : Fundef) (args : List Val) (k : Cont) (m : Mem)
  | Returnstate (v : Val) (k : Cont) (m : Mem)

/-- `Csharpminor.call_cont` -/
def callCont : Cont → Cont
  | .Kseq _ k => callCont k
  | .Kblock k => callCont k
  | k => k

/-- `Csharpminor.is_call_cont` -/
def isCallCont : Cont → Bool
  | .Kstop => true
  | .Kcall .. => true
  | _ => false

/-- `Csharpminor.select_switch_default` -/
def selectSwitchDefault : LblStmt → LblStmt
  | .LSnil => .LSnil
  | .LScons none s sl' => .LScons none s sl'
  | .LScons (some _) _ sl' => selectSwitchDefault sl'

/-- `Csharpminor.select_switch_case` -/
def selectSwitchCase (n : Z) : LblStmt → Option LblStmt
  | .LSnil => none
  | .LScons none _ sl' => selectSwitchCase n sl'
  | .LScons (some c) s sl' => if c = n then some (.LScons (some c) s sl') else selectSwitchCase n sl'

/-- `Csharpminor.select_switch` -/
def selectSwitch (n : Z) (sl : LblStmt) : LblStmt :=
  match selectSwitchCase n sl with
  | some sl' => sl'
  | none => selectSwitchDefault sl

/-- `Csharpminor.seq_of_lbl_stmt` -/
def seqOfLblStmt : LblStmt → Stmt
  | .LSnil => .Sskip
  | .LScons _ s sl' => .Sseq s (seqOfLblStmt sl')

mutual
/-- `Csharpminor.find_label` -/
def findLabel (lbl : Label) : Stmt → Cont → Option (Stmt × Cont)
  | .Sseq s1 s2, k =>
      match findLabel lbl s1 (.Kseq s2 k) with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Sifthenelse _ s1 s2, k =>
      match findLabel lbl s1 k with
      | some sk => some sk
      | none => findLabel lbl s2 k
  | .Sloop s1, k => findLabel lbl s1 (.Kseq (.Sloop s1) k)
  | .Sblock s1, k => findLabel lbl s1 (.Kblock k)
  | .Sswitch _ _ sl, k => findLabelLs lbl sl k
  | .Slabel lbl' s', k => if lbl = lbl' then some (s', k) else findLabel lbl s' k
  | _, _ => none

/-- `Csharpminor.find_label_ls` -/
def findLabelLs (lbl : Label) : LblStmt → Cont → Option (Stmt × Cont)
  | .LSnil, _ => none
  | .LScons _ s sl', k =>
      match findLabel lbl s (.Kseq (seqOfLblStmt sl') k) with
      | some sk => some sk
      | none => findLabelLs lbl sl' k
end

/-- `Csharpminor.eval_constant` -/
def evalConstant : Constant → Option Val
  | .Ointconst n => some (.Vint n)
  | .Ofloatconst n => some (.Vfloat n)
  | .Osingleconst n => some (.Vsingle n)
  | .Olongconst n => some (.Vlong n)

/-- `Csharpminor.eval_unop` -/
abbrev evalUnop := Cminor.evalUnop
/-- `Csharpminor.eval_binop` -/
abbrev evalBinop := Cminor.evalBinop

/-- `Csharpminor.alloc_variables` -/
inductive AllocVariables : Env → Mem → List (Ident × Z) → Env → Mem → Prop where
  | nil (e m) : AllocVariables e m [] e m
  | cons (e m id sz vars m1 b1 m2 e2) :
      Mem.alloc m 0 sz = (m1, b1) →
      AllocVariables (PTree.set id (b1, sz) e) m1 vars e2 m2 →
      AllocVariables e m ((id, sz) :: vars) e2 m2

/-- `Csharpminor.block_of_binding` -/
def blockOfBinding (p : Ident × (Block × Z)) : Block × Z × Z := (p.2.1, 0, p.2.2)

/-- `Csharpminor.blocks_of_env` -/
def blocksOfEnv (e : Env) : List (Block × Z × Z) := e.elements.map blockOfBinding

section RELSEM
variable (ge : CGenv)

/-- `Csharpminor.eval_var_addr` -/
inductive EvalVarAddr : Env → Ident → Block → Prop where
  | local (e id b sz) : PTree.get id e = some (b, sz) → EvalVarAddr e id b
  | global (e id b) : PTree.get id e = none → Genv.findSymbol ge id = some b → EvalVarAddr e id b

section EVAL_EXPR
variable (e : Env) (le : TempEnv) (m : Mem)

/-- `Csharpminor.eval_expr` -/
inductive EvalExpr : Expr → Val → Prop where
  | Evar (id v) : PTree.get id le = some v → EvalExpr (.Evar id) v
  | Eaddrof (id b) : EvalVarAddr ge e id b → EvalExpr (.Eaddrof id) (.Vptr b Integers.Ptrofs.zero)
  | Econst (cst v) : evalConstant cst = some v → EvalExpr (.Econst cst) v
  | Eunop (op a1 v1 v) : EvalExpr a1 v1 → evalUnop op v1 = some v → EvalExpr (.Eunop op a1) v
  | Ebinop (op a1 a2 v1 v2 v) :
      EvalExpr a1 v1 → EvalExpr a2 v2 → evalBinop op v1 v2 m = some v →
      EvalExpr (.Ebinop op a1 a2) v
  | Eload (chunk a v1 v) :
      EvalExpr a v1 → Mem.loadv chunk m v1 = some v → EvalExpr (.Eload chunk a) v

/-- `Csharpminor.eval_exprlist` -/
inductive EvalExprlist : List Expr → List Val → Prop where
  | nil : EvalExprlist [] []
  | cons (a1 al v1 vl) : EvalExpr ge e le m a1 v1 → EvalExprlist al vl →
      EvalExprlist (a1 :: al) (v1 :: vl)

end EVAL_EXPR

/-- `Csharpminor.step` -/
inductive Step : State → Trace → State → Prop where
  | skip_seq (f s k e le m) :
      Step (.State f .Sskip (.Kseq s k) e le m) E0 (.State f s k e le m)
  | skip_block (f k e le m) :
      Step (.State f .Sskip (.Kblock k) e le m) E0 (.State f .Sskip k e le m)
  | skip_call (f k e le m m') :
      isCallCont k = true →
      Mem.freeList m (blocksOfEnv e) = some m' →
      Step (.State f .Sskip k e le m) E0 (.Returnstate .Vundef k m')
  | set (f id a k e le m v) :
      EvalExpr ge e le m a v →
      Step (.State f (.Sset id a) k e le m) E0 (.State f .Sskip k e (PTree.set id v le) m)
  | store (f chunk addr a k e le m vaddr v m') :
      EvalExpr ge e le m addr vaddr →
      EvalExpr ge e le m a v →
      Mem.storev chunk m vaddr v = some m' →
      Step (.State f (.Sstore chunk addr a) k e le m) E0 (.State f .Sskip k e le m')
  | call (f optid sig a bl k e le m vf vargs fd) :
      EvalExpr ge e le m a vf →
      EvalExprlist ge e le m bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      Step (.State f (.Scall optid sig a bl) k e le m) E0
        (.Callstate fd vargs (.Kcall optid f e le k) m)
  | builtin (f optid ef bl k e le m vargs t vres m') :
      EvalExprlist ge e le m bl vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      Step (.State f (.Sbuiltin optid ef bl) k e le m) t
        (.State f .Sskip k e (Cminor.setOptvar optid vres le) m')
  | seq (f s1 s2 k e le m) :
      Step (.State f (.Sseq s1 s2) k e le m) E0 (.State f s1 (.Kseq s2 k) e le m)
  | ifthenelse (f a s1 s2 k e le m v b) :
      EvalExpr ge e le m a v →
      Val.BoolOfVal v b →
      Step (.State f (.Sifthenelse a s1 s2) k e le m) E0
        (.State f (if b then s1 else s2) k e le m)
  | loop (f s k e le m) :
      Step (.State f (.Sloop s) k e le m) E0 (.State f s (.Kseq (.Sloop s) k) e le m)
  | block (f s k e le m) :
      Step (.State f (.Sblock s) k e le m) E0 (.State f s (.Kblock k) e le m)
  | exit_seq (f n s k e le m) :
      Step (.State f (.Sexit n) (.Kseq s k) e le m) E0 (.State f (.Sexit n) k e le m)
  | exit_block_0 (f k e le m) :
      Step (.State f (.Sexit 0) (.Kblock k) e le m) E0 (.State f .Sskip k e le m)
  | exit_block_S (f n k e le m) :
      Step (.State f (.Sexit (n + 1)) (.Kblock k) e le m) E0 (.State f (.Sexit n) k e le m)
  | switch (f islong a cases k e le m v n) :
      EvalExpr ge e le m a v →
      Switch.SwitchArgument islong v n →
      Step (.State f (.Sswitch islong a cases) k e le m) E0
        (.State f (seqOfLblStmt (selectSwitch n cases)) k e le m)
  | return_0 (f k e le m m') :
      Mem.freeList m (blocksOfEnv e) = some m' →
      Step (.State f (.Sreturn none) k e le m) E0 (.Returnstate .Vundef (callCont k) m')
  | return_1 (f a k e le m v m') :
      EvalExpr ge e le m a v →
      Mem.freeList m (blocksOfEnv e) = some m' →
      Step (.State f (.Sreturn (some a)) k e le m) E0 (.Returnstate v (callCont k) m')
  | label (f lbl s k e le m) :
      Step (.State f (.Slabel lbl s) k e le m) E0 (.State f s k e le m)
  | goto (f lbl k e le m s' k') :
      findLabel lbl f.fn_body (callCont k) = some (s', k') →
      Step (.State f (.Sgoto lbl) k e le m) E0 (.State f s' k' e le m)
  | internal_function (f vargs k m m1 e le) :
      Val.HasArgtypeList vargs f.fn_sig.sig_args →
      listNorepet (f.fn_vars.map Prod.fst) →
      listNorepet f.fn_params →
      listDisjoint f.fn_params f.fn_temps →
      AllocVariables emptyEnv m f.fn_vars e m1 →
      bindParameters f.fn_params vargs (createUndefTemps f.fn_temps) = some le →
      Step (.Callstate (.Internal f) vargs k m) E0 (.State f f.fn_body k e le m1)
  | external_function (ef vargs k m t vres m') :
      externalCall ef ge.toSenv vargs m t vres m' →
      Step (.Callstate (.External ef) vargs k m) t (.Returnstate vres k m')
  | return (v optid f e le k m) :
      Step (.Returnstate v (.Kcall optid f e le k) m) E0
        (.State f .Sskip k e (Cminor.setOptvar optid v le) m)

end RELSEM

/-- `Csharpminor.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (b f m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      InitialState p (.Callstate f [] .Kstop m0)

/-- `Csharpminor.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (r m) : FinalState (.Returnstate (.Vint r) .Kstop m) r

/-- `Csharpminor.semantics` -/
def semantics (p : Program) : Semantics where
  state := State
  step := Step p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

/-! ## Receptiveness and determinacy (not in Rocq) -/

theorem singleEvents (p : Program) : SingleEvents (semantics p) := by
  intro s t s' h
  have hinj : (Genv.toSenv p.globalenv).SymbolsInjective := Genv.toSenv_symbolsInjective
    (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
  cases h with
  | builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | external_function _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | _ => simp [E0]

/-- Csharpminor is receptive. -/
theorem semantics_receptive (p : Program)
    (hx : ExternalsReceptive (Genv.toSenv p.globalenv)) :
    Receptive (semantics p) where
  sr_receptive := by
    intro s t1 s1 t2 h hm
    have hp := Genv.toSenv_publicSymbolExists p.globalenv
    have h' := h
    cases h with
    | builtin f optid ef bl k e le m vargs t vres m' hevl hec =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .builtin f optid ef bl k e le m vargs t2 vres2 m2 hevl h2⟩
    | external_function ef vargs k m t vres m' hec =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .external_function ef vargs k m t2 vres2 m2 h2⟩
    | _ => rw [EventsReceptive.matchTraces_E0 hm]; exact ⟨_, h'⟩
  sr_traces := singleEvents p

theorem evalVarAddr_determ {ge : CGenv} {e id b1 b2} (h1 : EvalVarAddr ge e id b1)
    (h2 : EvalVarAddr ge e id b2) : b2 = b1 := by
  cases h1 <;> cases h2 <;> simp_all

theorem evalExpr_determ {ge : CGenv} {e le m a v} (h : EvalExpr ge e le m a v) :
    ∀ {v'}, EvalExpr ge e le m a v' → v' = v := by
  induction h with
  | Evar _ _ h1 => intro v' h2; cases h2; simp_all
  | Eaddrof _ _ h1 => intro v' h2; cases h2 with
    | Eaddrof _ _ h2 => rw [evalVarAddr_determ h1 h2]
  | Econst _ _ h1 => intro v' h2; cases h2; simp_all
  | Eunop _ _ _ _ _ h1 ih =>
    intro v' h2; cases h2 with
    | Eunop _ _ _ _ ha hu => rw [ih ha] at hu; simp_all
  | Ebinop _ _ _ _ _ _ _ _ h1 ih1 ih2 =>
    intro v' h2; cases h2 with
    | Ebinop _ _ _ _ _ _ ha1 ha2 hb => rw [ih1 ha1, ih2 ha2] at hb; simp_all
  | Eload _ _ _ _ _ h1 ih =>
    intro v' h2; cases h2 with
    | Eload _ _ _ _ ha hl => rw [ih ha] at hl; simp_all

theorem evalExprlist_determ {ge : CGenv} {e le m al vl} (h : EvalExprlist ge e le m al vl) :
    ∀ {vl'}, EvalExprlist ge e le m al vl' → vl' = vl := by
  induction h with
  | nil => intro vl' h2; cases h2; rfl
  | cons _ _ _ _ ha _ ih =>
    intro vl' h2; cases h2 with
    | cons _ _ _ _ ha' hl' => rw [evalExpr_determ ha ha', ih hl']

theorem allocVariables_determ {e m vars e1 m1} (h : AllocVariables e m vars e1 m1) :
    ∀ {e2 m2}, AllocVariables e m vars e2 m2 → (e2, m2) = (e1, m1) := by
  induction h with
  | nil => intro e2 m2 h2; cases h2; rfl
  | cons _ _ _ _ _ _ _ _ _ ha _ ih =>
    intro e2 m2 h2; cases h2 with
    | cons _ _ _ _ _ _ _ _ _ ha' hr =>
      rw [ha] at ha'
      simp only [Prod.mk.injEq] at ha'
      obtain ⟨h1, h2⟩ := ha'
      subst h1; subst h2
      exact ih hr

theorem allocVariables_determ_env {e m vars e1 m1 e2 m2} (h1 : AllocVariables e m vars e1 m1)
    (h2 : AllocVariables e m vars e2 m2) : e2 = e1 :=
  congrArg Prod.fst (allocVariables_determ h1 h2)

theorem allocVariables_determ_mem {e m vars e1 m1 e2 m2} (h1 : AllocVariables e m vars e1 m1)
    (h2 : AllocVariables e m vars e2 m2) : m2 = m1 :=
  congrArg Prod.snd (allocVariables_determ h1 h2)

set_option maxHeartbeats 1000000 in
theorem step_determ {ge : CGenv} (hinj : (Genv.toSenv ge).SymbolsInjective)
    {s t1 s1 t2 s2} (h1 : Step ge s t1 s1) (h2 : Step ge s t2 s2) :
    MatchTraces (Genv.toSenv ge) t1 t2 ∧ (t1 = t2 → s1 = s2) := by
  cases h1 <;> cases h2 <;>
    try (first
          | exact ⟨MatchTraces.nil, fun _ => rfl⟩
          | (exfalso; simp_all [isCallCont]; done))
  case builtin.builtin =>
    determ_using [evalExprlist_determ]
    rename_i hec1 _ _ _ hec2
    obtain ⟨hmt, hrest⟩ := (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ hec1 hec2
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    rw [hv, hm]
  case external_function.external_function =>
    rename_i hec1 _ _ hec2
    obtain ⟨hmt, hrest⟩ := (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ hec1 hec2
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    rw [hv, hm]
  all_goals
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    determ_using [evalExpr_determ, evalExprlist_determ, Switch.switchArgument_determ,
      Cminor.boolOfVal_determ, allocVariables_determ_env, allocVariables_determ_mem]
    simp_all

/-- Csharpminor is determinate. -/
theorem semantics_determinate (p : Program) : Smallstep.Determinate (semantics p) where
  sd_determ := fun _ _ _ _ _ h1 h2 =>
    step_determ (Genv.toSenv_symbolsInjective
      (Genv.symbInjective_globalenv p.prog_public p.prog_defs)) h1 h2
  sd_traces := singleEvents p
  sd_initial_determ := by
    intro s1 s2 h1 h2
    cases h1 with
    | intro _ _ _ hm1 hs1 hf1 _ =>
      cases h2 with
      | intro _ _ _ hm2 hs2 hf2 _ =>
        rw [hm1] at hm2; rw [hs1] at hs2
        simp only [Option.some.injEq] at hm2 hs2
        subst hm2; subst hs2
        rw [hf1] at hf2
        simp only [Option.some.injEq] at hf2
        subst hf2; rfl
  sd_final_nostep := by
    intro s r h t s' hs
    cases h; cases hs
  sd_final_determ := by
    intro s r1 r2 h1 h2
    cases h1; cases h2; rfl

end Csharpminor
end CC
