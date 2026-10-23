/-
  Small-step semantics of Cminor — port of the `RELSEM` section of
  `backend/Cminor.v` together with `initial_state`, `final_state`,
  `semantics`, `semantics_receptive`, `eval_expr_determ`,
  `eval_exprlist_determ` and `semantics_determinate`.

  Differences from Rocq:
  * `is_call_cont` is a `Bool`.
  * As for Clight (`CCLib.cfrontend.ClightReceptive`), receptiveness of the
    uninterpreted external functions and inline assembly, which CompCert
    assumes by axiom, is the hypothesis `ExternalsReceptive`.
-/
import CCLib.backend.Cminor
import CCLib.common.Switch
import CCLib.common.Smallstep
import CCLib.common.GlobalenvsTransf
import CCLib.cfrontend.ClightReceptive
import CCLib.common.DetermTac

namespace CC
namespace Cminor

open Smallstep

section RELSEM
variable (ge : CGenv)

section EVAL_EXPR
variable (sp : Val) (e : Env) (m : Mem)

/-- `Cminor.eval_expr` -/
inductive EvalExpr : Expr → Val → Prop where
  | Evar (id v) : e.get id = some v → EvalExpr (.Evar id) v
  | Econst (cst v) : evalConstant ge sp cst = some v → EvalExpr (.Econst cst) v
  | Eunop (op a1 v1 v) : EvalExpr a1 v1 → evalUnop op v1 = some v → EvalExpr (.Eunop op a1) v
  | Ebinop (op a1 a2 v1 v2 v) :
      EvalExpr a1 v1 → EvalExpr a2 v2 → evalBinop op v1 v2 m = some v →
      EvalExpr (.Ebinop op a1 a2) v
  | Eload (chunk addr vaddr v) :
      EvalExpr addr vaddr → Mem.loadv chunk m vaddr = some v → EvalExpr (.Eload chunk addr) v

/-- `Cminor.eval_exprlist` -/
inductive EvalExprlist : List Expr → List Val → Prop where
  | nil : EvalExprlist [] []
  | cons (a1 al v1 vl) : EvalExpr ge sp e m a1 v1 → EvalExprlist al vl →
      EvalExprlist (a1 :: al) (v1 :: vl)

end EVAL_EXPR

/-- `Cminor.call_cont` -/
def callCont : Cont → Cont
  | .Kseq _ k => callCont k
  | .Kblock k => callCont k
  | k => k

/-- `Cminor.is_call_cont` -/
def isCallCont : Cont → Bool
  | .Kstop => true
  | .Kcall .. => true
  | _ => false

/-- `Cminor.find_label` -/
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
  | .Slabel lbl' s', k => if lbl = lbl' then some (s', k) else findLabel lbl s' k
  | _, _ => none

/-- `Cminor.step` -/
inductive Step : State → Trace → State → Prop where
  | skip_seq (f s k sp e m) :
      Step (.State f .Sskip (.Kseq s k) sp e m) E0 (.State f s k sp e m)
  | skip_block (f k sp e m) :
      Step (.State f .Sskip (.Kblock k) sp e m) E0 (.State f .Sskip k sp e m)
  | skip_call (f k sp e m m') :
      isCallCont k = true →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f .Sskip k (.Vptr sp Integers.Ptrofs.zero) e m) E0 (.Returnstate .Vundef k m')
  | assign (f id a k sp e m v) :
      EvalExpr ge sp e m a v →
      Step (.State f (.Sassign id a) k sp e m) E0 (.State f .Sskip k sp (e.set id v) m)
  | store (f chunk addr a k sp e m vaddr v m') :
      EvalExpr ge sp e m addr vaddr →
      EvalExpr ge sp e m a v →
      Mem.storev chunk m vaddr v = some m' →
      Step (.State f (.Sstore chunk addr a) k sp e m) E0 (.State f .Sskip k sp e m')
  | call (f optid sig a bl k sp e m vf vargs fd) :
      EvalExpr ge sp e m a vf →
      EvalExprlist ge sp e m bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      Step (.State f (.Scall optid sig a bl) k sp e m) E0
        (.Callstate fd vargs (.Kcall optid f sp e k) m)
  | tailcall (f sig a bl k sp e m vf vargs fd m') :
      EvalExpr ge (.Vptr sp Integers.Ptrofs.zero) e m a vf →
      EvalExprlist ge (.Vptr sp Integers.Ptrofs.zero) e m bl vargs →
      Genv.findFunct ge vf = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f (.Stailcall sig a bl) k (.Vptr sp Integers.Ptrofs.zero) e m) E0
        (.Callstate fd vargs (callCont k) m')
  | builtin (f optid ef bl k sp e m vargs t vres m') :
      EvalExprlist ge sp e m bl vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      Step (.State f (.Sbuiltin optid ef bl) k sp e m) t
        (.State f .Sskip k sp (setOptvar optid vres e) m')
  | seq (f s1 s2 k sp e m) :
      Step (.State f (.Sseq s1 s2) k sp e m) E0 (.State f s1 (.Kseq s2 k) sp e m)
  | ifthenelse (f a s1 s2 k sp e m v b) :
      EvalExpr ge sp e m a v →
      Val.BoolOfVal v b →
      Step (.State f (.Sifthenelse a s1 s2) k sp e m) E0
        (.State f (if b then s1 else s2) k sp e m)
  | loop (f s k sp e m) :
      Step (.State f (.Sloop s) k sp e m) E0 (.State f s (.Kseq (.Sloop s) k) sp e m)
  | block (f s k sp e m) :
      Step (.State f (.Sblock s) k sp e m) E0 (.State f s (.Kblock k) sp e m)
  | exit_seq (f n s k sp e m) :
      Step (.State f (.Sexit n) (.Kseq s k) sp e m) E0 (.State f (.Sexit n) k sp e m)
  | exit_block_0 (f k sp e m) :
      Step (.State f (.Sexit 0) (.Kblock k) sp e m) E0 (.State f .Sskip k sp e m)
  | exit_block_S (f n k sp e m) :
      Step (.State f (.Sexit (n + 1)) (.Kblock k) sp e m) E0 (.State f (.Sexit n) k sp e m)
  | switch (f islong a cases default k sp e m v n) :
      EvalExpr ge sp e m a v →
      Switch.SwitchArgument islong v n →
      Step (.State f (.Sswitch islong a cases default) k sp e m) E0
        (.State f (.Sexit (Switch.switchTarget n default cases)) k sp e m)
  | return_0 (f k sp e m m') :
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f (.Sreturn none) k (.Vptr sp Integers.Ptrofs.zero) e m) E0
        (.Returnstate .Vundef (callCont k) m')
  | return_1 (f a k sp e m v m') :
      EvalExpr ge (.Vptr sp Integers.Ptrofs.zero) e m a v →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step (.State f (.Sreturn (some a)) k (.Vptr sp Integers.Ptrofs.zero) e m) E0
        (.Returnstate v (callCont k) m')
  | label (f lbl s k sp e m) :
      Step (.State f (.Slabel lbl s) k sp e m) E0 (.State f s k sp e m)
  | goto (f lbl k sp e m s' k') :
      findLabel lbl f.fn_body (callCont k) = some (s', k') →
      Step (.State f (.Sgoto lbl) k sp e m) E0 (.State f s' k' sp e m)
  | internal_function (f vargs k m m' sp e) :
      Val.HasArgtypeList vargs f.fn_sig.sig_args →
      Mem.alloc m 0 f.fn_stackspace = (m', sp) →
      setLocals f.fn_vars (setParams vargs f.fn_params) = e →
      Step (.Callstate (.Internal f) vargs k m) E0
        (.State f f.fn_body k (.Vptr sp Integers.Ptrofs.zero) e m')
  | external_function (ef vargs k m t vres m') :
      externalCall ef ge.toSenv vargs m t vres m' →
      Step (.Callstate (.External ef) vargs k m) t (.Returnstate vres k m')
  | return (v optid f sp e k m) :
      Step (.Returnstate v (.Kcall optid f sp e k) m) E0
        (.State f .Sskip k sp (setOptvar optid v e) m)

end RELSEM

/-- `Cminor.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (b f m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      InitialState p (.Callstate f [] .Kstop m0)

/-- `Cminor.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (r m) : FinalState (.Returnstate (.Vint r) .Kstop m) r

/-- `Cminor.semantics` -/
def semantics (p : Program) : Semantics where
  state := State
  step := Step p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

/-! ## Receptiveness and determinacy -/

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

/-- `Cminor.semantics_receptive` -/
theorem semantics_receptive (p : Program)
    (hx : ExternalsReceptive (Genv.toSenv p.globalenv)) :
    Receptive (semantics p) where
  sr_receptive := by
    intro s t1 s1 t2 h hm
    have hp := Genv.toSenv_publicSymbolExists p.globalenv
    have h' := h
    cases h with
    | builtin f optid ef bl k sp e m vargs t vres m' hevl hec =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .builtin f optid ef bl k sp e m vargs t2 vres2 m2 hevl h2⟩
    | external_function ef vargs k m t vres m' hec =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .external_function ef vargs k m t2 vres2 m2 h2⟩
    | _ => rw [EventsReceptive.matchTraces_E0 hm]; exact ⟨_, h'⟩
  sr_traces := singleEvents p

/-- `Cminor.eval_expr_determ` -/
theorem evalExpr_determ {ge : CGenv} {sp e m a v} (h : EvalExpr ge sp e m a v) :
    ∀ {v'}, EvalExpr ge sp e m a v' → v' = v := by
  induction h with
  | Evar _ _ h1 => intro v' h2; cases h2; simp_all
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

/-- `Cminor.eval_exprlist_determ` -/
theorem evalExprlist_determ {ge : CGenv} {sp e m al vl} (h : EvalExprlist ge sp e m al vl) :
    ∀ {vl'}, EvalExprlist ge sp e m al vl' → vl' = vl := by
  induction h with
  | nil => intro vl' h2; cases h2; rfl
  | cons _ _ _ _ ha _ ih =>
    intro vl' h2; cases h2 with
    | cons _ _ _ _ ha' hl' => rw [evalExpr_determ ha ha', ih hl']

theorem boolOfVal_determ {v b1 b2} (h1 : Val.BoolOfVal v b1) (h2 : Val.BoolOfVal v b2) :
    b1 = b2 := by
  cases h1; cases h2; rfl

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
      boolOfVal_determ]
    simp_all

/-- `Cminor.semantics_determinate` -/
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

end Cminor
end CC
