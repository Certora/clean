/-
  Type system for Cminor: semantic soundness — port of the rest of
  `backend/Cminortyping.v`: `wt_env`, `def_env`, `wt_cont_call`/`wt_cont`,
  `wt_state`, `wt_is_call_cont`, `call_cont_wt`, `wt_env_assign`,
  `def_env_assign`, `wt_env_set_params`, `def_set_params`,
  `wt_env_set_locals`, `def_set_locals`, `wt_find_label`,
  `type_constant_sound`, `type_unop_sound`, `type_binop_sound`,
  `wt_eval_expr`, `wt_eval_exprlist`, `wt_find_funct`,
  **`subject_reduction`**, `subject_reduction_star`, `wt_initial_state`,
  and `eval_safe_expr`.

  Difference from Rocq: `external_call_well_typed`, which CompCert derives
  from the axioms on external functions and inline assembly, comes from the
  hypotheses `hext`/`hasm` of `subject_reduction` (see
  `CCLib.common.EventsProps.externalCall_wellTyped`).
-/
import CCLib.backend.CminortypingSpec
import CCLib.backend.CminorSem
import CCLib.common.EventsProps
import CCLib.common.MemdataEncode
import CCLib.common.GlobalenvsTheory
import CCLib.common.ValuesTheory

namespace CC
namespace Cminortyping

open Cminor Smallstep

/-- `Cminortyping.wt_env` -/
def WtEnv (env : Typenv) (e : Cminor.Env) : Prop :=
  ∀ id v, e.get id = some v → Val.HasType v (env id)

/-- `Cminortyping.def_env` -/
def DefEnv (f : Cminor.Function) (e : Cminor.Env) : Prop :=
  ∀ id, id ∈ f.fn_params ∨ id ∈ f.fn_vars → ∃ v, e.get id = some v

mutual
/-- `Cminortyping.wt_cont_call` -/
inductive WtContCall : Cminor.Cont → XType → Prop where
  | Kstop : WtContCall .Kstop .Xint
  | Kcall (optid f sp e k tret env) :
      WtFunction env f → WtCont env f.fn_sig.sig_res k → WtEnv env e → DefEnv f e →
      WtOptAssign env optid tret → WtContCall (.Kcall optid f sp e k) tret

/-- `Cminortyping.wt_cont` -/
inductive WtCont : Typenv → XType → Cminor.Cont → Prop where
  | Kseq (env tret s k) : WtStmt env tret s → WtCont env tret k → WtCont env tret (.Kseq s k)
  | Kblock (env tret k) : WtCont env tret k → WtCont env tret (.Kblock k)
  | other (env tret k) : WtContCall k tret → WtCont env tret k
end

/-- `Cminortyping.wt_state` -/
inductive WtState : Cminor.State → Prop where
  | normal (f s k sp e m env) : WtFunction env f → WtStmt env f.fn_sig.sig_res s →
      WtCont env f.fn_sig.sig_res k → WtEnv env e → DefEnv f e → WtState (.State f s k sp e m)
  | call (f args k m) : WtFundef f → Val.HasTypeList args (projSigArgs (funsig f)) →
      WtContCall k (funsig f).sig_res → WtState (.Callstate f args k m)
  | ret (v k m tret) : Val.HasType v tret.proj → WtContCall k tret →
      WtState (.Returnstate v k m)

/-- `Cminortyping.wt_is_call_cont` -/
theorem wt_is_call_cont {env : Typenv} {tret : XType} {k : Cminor.Cont}
    (h : WtCont env tret k) (hc : Cminor.isCallCont k = true) : WtContCall k tret := by
  cases h with
  | Kseq => simp [Cminor.isCallCont] at hc
  | Kblock => simp [Cminor.isCallCont] at hc
  | other _ _ _ h => exact h

/-- `Cminortyping.call_cont_wt` -/
theorem call_cont_wt {env : Typenv} {tret : XType} {k : Cminor.Cont}
    (h : WtCont env tret k) : WtContCall (Cminor.callCont k) tret := by
  induction k with
  | Kstop => cases h with | other _ _ _ h => exact h
  | Kseq s k ih =>
    cases h with
    | Kseq _ _ _ _ _ hk => exact ih hk
    | other _ _ _ h => cases h
  | Kblock k ih =>
    cases h with
    | Kblock _ _ _ hk => exact ih hk
    | other _ _ _ h => cases h
  | Kcall => cases h with | other _ _ _ h => exact h

/-- `Cminortyping.wt_env_assign` -/
theorem wt_env_assign {env : Typenv} {id : Ident} {e : Cminor.Env} {v : Val}
    (he : WtEnv env e) (hv : Val.HasType v (env id)) : WtEnv env (PTree.set id v e) := by
  intro id0 v0 h
  rw [PTree.gsspec] at h
  split at h
  · next heq => cases h; subst heq; exact hv
  · exact he _ _ h

/-- `Cminortyping.def_env_assign` -/
theorem def_env_assign {f : Cminor.Function} {e : Cminor.Env} {id : Ident} {v : Val}
    (he : DefEnv f e) : DefEnv f (PTree.set id v e) := by
  intro i hin
  rw [PTree.gsspec]
  split
  · exact ⟨v, rfl⟩
  · exact he i hin

/-- `Cminortyping.wt_env_set_params` -/
theorem wt_env_set_params (env : Typenv) :
    ∀ (il : List Ident) {vl : List Val}, Val.HasTypeList vl (il.map env) →
    WtEnv env (Cminor.setParams vl il)
  | [], vl, _ => by
    intro id v h; cases vl <;> simp [Cminor.setParams] at h
  | _ :: _, [], h => by simp [Val.HasTypeList] at h
  | i :: il, v :: vl, h => by
    obtain ⟨h1, h2⟩ := h
    exact wt_env_assign (wt_env_set_params env il h2) h1

/-- `Cminortyping.def_set_params` -/
theorem def_set_params (id : Ident) :
    ∀ (il : List Ident) (vl : List Val), id ∈ il → ∃ v, (Cminor.setParams vl il).get id = some v
  | [], _, hin => by cases hin
  | i :: il, vl, hin => by
    cases vl with
    | nil =>
      simp only [Cminor.setParams]
      rw [PTree.gsspec]
      split
      · exact ⟨_, rfl⟩
      · next hne =>
        rcases List.mem_cons.mp hin with h | h
        · exact absurd h hne
        · exact def_set_params id il [] h
    | cons v vl =>
      simp only [Cminor.setParams]
      rw [PTree.gsspec]
      split
      · exact ⟨_, rfl⟩
      · next hne =>
        rcases List.mem_cons.mp hin with h | h
        · exact absurd h hne
        · exact def_set_params id il vl h

/-- `Cminortyping.wt_env_set_locals` -/
theorem wt_env_set_locals {env : Typenv} :
    ∀ (il : List Ident) {e : Cminor.Env}, WtEnv env e → WtEnv env (Cminor.setLocals il e)
  | [], _, h => h
  | _ :: il, _, h => wt_env_assign (wt_env_set_locals il h) rfl

/-- `Cminortyping.def_set_locals` -/
theorem def_set_locals (id : Ident) :
    ∀ (il : List Ident) {e : Cminor.Env}, (∃ v, e.get id = some v) ∨ id ∈ il →
    ∃ v, (Cminor.setLocals il e).get id = some v
  | [], _, h => by
    rcases h with h | h
    · exact h
    · cases h
  | i :: il, e, h => by
    simp only [Cminor.setLocals]
    rw [PTree.gsspec]
    split
    · exact ⟨_, rfl⟩
    · next hne =>
      apply def_set_locals id il
      rcases h with h | h
      · exact .inl h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h hne
        · exact .inr h

/-- `Cminortyping.wt_find_label` -/
theorem wt_find_label {env : Typenv} {tret : XType} (lbl : Cminor.Label) :
    ∀ (s : Cminor.Stmt) {k : Cminor.Cont}, WtStmt env tret s → WtCont env tret k →
    match Cminor.findLabel lbl s k with
    | some (s', k') => WtStmt env tret s' ∧ WtCont env tret k'
    | none => True
  | .Sseq s1 s2, k, hs, hk => by
    cases hs with
    | Sseq _ _ h1 h2 =>
      have ih1 := wt_find_label lbl s1 h1 (.Kseq _ _ _ _ h2 hk)
      simp only [Cminor.findLabel]
      rcases hf : Cminor.findLabel lbl s1 (.Kseq s2 k) with _ | ⟨s', k'⟩
      · dsimp only; exact wt_find_label lbl s2 h2 hk
      · rw [hf] at ih1; exact ih1
  | .Sifthenelse a s1 s2, k, hs, hk => by
    cases hs with
    | Sifthenelse _ _ _ _ h1 h2 =>
      have ih1 := wt_find_label lbl s1 h1 hk
      simp only [Cminor.findLabel]
      rcases hf : Cminor.findLabel lbl s1 k with _ | ⟨s', k'⟩
      · dsimp only; exact wt_find_label lbl s2 h2 hk
      · rw [hf] at ih1; exact ih1
  | .Sloop s1, k, hs, hk => by
    have hs' := hs
    cases hs with
    | Sloop _ h1 => exact wt_find_label lbl s1 h1 (.Kseq _ _ _ _ hs' hk)
  | .Sblock s1, k, hs, hk => by
    cases hs with
    | Sblock _ h1 => exact wt_find_label lbl s1 h1 (.Kblock _ _ _ hk)
  | .Slabel lbl' s1, k, hs, hk => by
    cases hs with
    | Slabel _ _ h1 =>
      simp only [Cminor.findLabel]
      by_cases heq : lbl = lbl'
      · simp only [heq, if_true]; exact ⟨h1, hk⟩
      · simp only [heq, if_false]; exact wt_find_label lbl s1 h1 hk
  | .Sskip, _, _, _ => trivial
  | .Sassign .., _, _, _ => trivial
  | .Sstore .., _, _, _ => trivial
  | .Scall .., _, _, _ => trivial
  | .Stailcall .., _, _, _ => trivial
  | .Sbuiltin .., _, _, _ => trivial
  | .Sexit _, _, _, _ => trivial
  | .Sswitch .., _, _, _ => trivial
  | .Sreturn _, _, _, _ => trivial
  | .Sgoto _, _, _, _ => trivial

/-! ## Subject reduction -/

theorem hasType_undef (t : ATyp) : Val.HasType .Vundef t := by
  cases t <;> rfl

/-- `Cminortyping.type_constant_sound` -/
theorem type_constant_sound {ge : Cminor.CGenv} {sp : Val} {cst : Constant} {v : Val}
    (h : Cminor.evalConstant ge sp cst = some v) : Val.HasType v (typeConstant cst) := by
  cases cst <;> simp only [Cminor.evalConstant, Option.some.injEq] at h <;> subst h
  · rfl
  · rfl
  · rfl
  · rfl
  · unfold Genv.symbolAddress
    split
    · exact Val.Vptr_has_type _ _
    · exact hasType_undef _
  · unfold Val.offsetPtr
    split
    · exact Val.Vptr_has_type _ _
    · exact hasType_undef _

/-- `Cminortyping.type_unop_sound` -/
theorem type_unop_sound {op : UnaryOperation} {v1 v : Val} (h : Cminor.evalUnop op v1 = some v) :
    Val.HasType v (typeUnop op).2 := by
  cases op <;> simp only [Cminor.evalUnop, Option.some.injEq] at h <;> (try subst h) <;>
    cases v1 <;> simp [typeUnop, Val.HasType, Val.hasType, Val.zeroExt, Val.signExt, Val.negint, Val.notint, Val.negf, Val.absf, Val.negfs, Val.absfs, Val.singleoffloat, Val.floatofsingle, Val.negl, Val.notl, Val.loword, Val.longofint, Val.longofintu, Val.intoffloat, Val.intuoffloat, Val.floatofint, Val.floatofintu, Val.intofsingle, Val.intuofsingle, Val.singleofint, Val.singleofintu, Val.longoffloat, Val.longuoffloat, Val.floatoflong, Val.floatoflongu, Val.longofsingle, Val.longuofsingle, Val.singleoflong, Val.singleoflongu] at * <;> (try obtain ⟨_, _, h⟩ := h) <;> (try subst h) <;> rfl

theorem hasType_ofOptbool (o : Option Bool) : Val.HasType (Val.ofOptbool o) .Tint := by
  rcases o with _ | ⟨_ | _⟩ <;> rfl

theorem hasType_mapOfBool {o : Option Bool} {v : Val} (h : o.map Val.ofBool = some v) :
    Val.HasType v .Tint := by
  rcases o with _ | ⟨_ | _⟩ <;> simp at h <;> subst h <;> rfl

theorem hasType_ite {c : Prop} [Decidable c] {a b : Val} {t : ATyp} (ha : Val.HasType a t)
    (hb : Val.HasType b t) : Val.HasType (if c then a else b) t := by
  split <;> assumption

/-- `Cminortyping.type_binop_sound` -/
theorem type_binop_sound {op : BinaryOperation} {v1 v2 : Val} {m : Mem} {v : Val}
    (h : Cminor.evalBinop op v1 v2 m = some v) : Val.HasType v (typeBinop op).2.2 := by
  cases op
  case Ocmp c => cases h; exact hasType_ofOptbool _
  case Ocmpu c => cases h; exact hasType_ofOptbool _
  case Ocmpf c => cases h; exact hasType_ofOptbool _
  case Ocmpfs c => cases h; exact hasType_ofOptbool _
  case Ocmpl c => exact hasType_mapOfBool h
  case Ocmplu c => exact hasType_mapOfBool h
  all_goals
    simp only [Cminor.evalBinop, Option.some.injEq] at h <;> (try subst h) <;>
    cases v1 <;> cases v2 <;> simp [typeBinop, Val.add, Val.sub, Val.mul, Val.divs, Val.divu, Val.mods, Val.modu, Val.and, Val.or, Val.xor, Val.shl, Val.shr, Val.shru, Val.addf, Val.subf, Val.mulf, Val.divf, Val.addfs, Val.subfs, Val.mulfs, Val.divfs, Val.addl, Val.subl, Val.mull, Val.divls, Val.divlu, Val.modls, Val.modlu, Val.andl, Val.orl, Val.xorl, Val.shll, Val.shrl, Val.shrlu, Archi.ptr64] at * <;> (try obtain ⟨_, h⟩ := h) <;> (try subst h) <;> first | rfl | (apply hasType_ite <;> rfl) | fail "left"

/-- `Cminortyping.wt_eval_expr` -/
theorem wt_eval_expr {ge : Cminor.CGenv} {env : Typenv} {sp : Val} {e : Cminor.Env} {m : Mem}
    {a : Cminor.Expr} {v : Val} (h : Cminor.EvalExpr ge sp e m a v) :
    ∀ {t : ATyp}, WtExpr env a t → WtEnv env e → Val.HasType v t := by
  induction h with
  | Evar id v hv => intro t ht he; cases ht; exact he _ _ hv
  | Econst cst v hv => intro t ht _; cases ht; exact type_constant_sound hv
  | Eunop op a1 v1 v _ hv _ =>
    intro t ht _
    cases ht with
    | Eunop _ _ targ1 _ hu _ =>
      have := type_unop_sound hv
      rw [hu] at this; exact this
  | Ebinop op a1 a2 v1 v2 v _ _ hv _ _ =>
    intro t ht _
    cases ht with
    | Ebinop _ _ _ _ _ _ hb _ _ =>
      have := type_binop_sound hv
      rw [hb] at this; exact this
  | Eload chunk addr vaddr v _ hl _ =>
    intro t ht _
    cases ht
    cases vaddr <;> simp only [Mem.loadv] at hl <;> try cases hl
    split at hl
    · rw [← Chunk.proj_xtype]
      exact Val.has_proj_xtype (EventsProps.load_hasRettype hl)
    · cases hl

/-- `Cminortyping.wt_eval_exprlist` -/
theorem wt_eval_exprlist {ge : Cminor.CGenv} {env : Typenv} {sp : Val} {e : Cminor.Env}
    {m : Mem} {al : List Cminor.Expr} {vl : List Val} (h : Cminor.EvalExprlist ge sp e m al vl) :
    ∀ {tl : List ATyp}, ListForall2 (WtExpr env) al tl → WtEnv env e → Val.HasTypeList vl tl := by
  induction h with
  | nil => intro tl ht _; cases ht; trivial
  | cons a1 al v1 vl h1 _ ih =>
    intro tl ht he
    cases ht with
    | cons ha hl => exact ⟨wt_eval_expr h1 ha he, ih hl he⟩

section SUBJECT_REDUCTION
variable (p : Cminor.Program) (wt_p : WtProgram p)
  (hext : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
  (hasm : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)

include wt_p in
/-- `Cminortyping.wt_find_funct` -/
theorem wt_find_funct {v : Val} {fd : Cminor.Fundef}
    (h : Genv.findFunct p.globalenv v = some fd) : WtFundef fd :=
  Genv.findFunct_prop WtFundef (fun id f hin => wt_p id f hin) h

include wt_p hext hasm in
/-- `Cminortyping.subject_reduction` -/
theorem subject_reduction {st1 : Cminor.State} {t : Trace} {st2 : Cminor.State}
    (hst : Cminor.Step p.globalenv st1 t st2) (hwt : WtState st1) : WtState st2 := by
  have hec : ∀ ef, ExtcallWellTyped (externalCall ef) ef.sig :=
    fun ef => externalCall_wellTyped ef hext hasm
  cases hst with
  | skip_seq f s k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WK with
      | Kseq _ _ _ _ hs hk => exact .normal _ _ _ _ _ _ env WF hs hk WE DE
      | other _ _ _ h => cases h
  | skip_block f k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WK with
      | Kblock _ _ _ hk => exact .normal _ _ _ _ _ _ env WF .Sskip hk WE DE
      | other _ _ _ h => cases h
  | skip_call f k sp e m m' hc _ =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      exact .ret _ _ _ _ (hasType_undef _) (wt_is_call_cont WK hc)
  | assign f id a k sp e m v hv =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Sassign _ _ ha =>
        exact .normal _ _ _ _ _ _ env WF .Sskip WK (wt_env_assign WE (wt_eval_expr hv ha WE))
          (def_env_assign DE)
  | store f chunk addr a k sp e m vaddr v m' =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE => exact .normal _ _ _ _ _ _ env WF .Sskip WK WE DE
  | call f optid sig a bl k sp e m vf vargs fd _ hargs hfd hsig =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Scall _ _ _ _ _ hal hopt =>
        subst hsig
        exact .call _ _ _ _ (wt_find_funct p wt_p hfd) (wt_eval_exprlist hargs hal WE)
          (.Kcall _ _ _ _ _ _ env WF WK WE DE hopt)
  | tailcall f sig a bl k sp e m vf vargs fd m' _ hargs hfd hsig _ =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Stailcall _ _ _ _ hal hres =>
        subst hsig
        refine .call _ _ _ _ (wt_find_funct p wt_p hfd) (wt_eval_exprlist hargs hal WE) ?_
        rw [hres]; exact call_cont_wt WK
  | builtin f optid ef bl k sp e m vargs t vres m' _ hx =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Sbuiltin _ _ _ _ hopt =>
        have TRES := Val.has_proj_xtype (hec ef _ _ _ _ _ _ hx)
        refine .normal _ _ _ _ _ _ env WF .Sskip WK ?_ ?_
        · cases optid with
          | none => exact WE
          | some id => exact wt_env_assign WE (hopt ▸ TRES)
        · cases optid with
          | none => exact DE
          | some id => exact def_env_assign DE
  | seq f s1 s2 k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Sseq _ _ h1 h2 => exact .normal _ _ _ _ _ _ env WF h1 (.Kseq _ _ _ _ h2 WK) WE DE
  | ifthenelse f a s1 s2 k sp e m v b =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Sifthenelse _ _ _ _ h1 h2 =>
        cases b
        · exact .normal _ _ _ _ _ _ env WF h2 WK WE DE
        · exact .normal _ _ _ _ _ _ env WF h1 WK WE DE
  | loop f s k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      have WS' := WS
      cases WS with
      | Sloop _ h1 => exact .normal _ _ _ _ _ _ env WF h1 (.Kseq _ _ _ _ WS' WK) WE DE
  | block f s k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Sblock _ h1 => exact .normal _ _ _ _ _ _ env WF h1 (.Kblock _ _ _ WK) WE DE
  | exit_seq f n s k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WK with
      | Kseq _ _ _ _ _ hk => exact .normal _ _ _ _ _ _ env WF (.Sexit _) hk WE DE
      | other _ _ _ h => cases h
  | exit_block_0 f k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WK with
      | Kblock _ _ _ hk => exact .normal _ _ _ _ _ _ env WF .Sskip hk WE DE
      | other _ _ _ h => cases h
  | exit_block_S f n k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WK with
      | Kblock _ _ _ hk => exact .normal _ _ _ _ _ _ env WF (.Sexit _) hk WE DE
      | other _ _ _ h => cases h
  | switch f islong a cases default k sp e m v n =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      exact .normal _ _ _ _ _ _ env WF (.Sexit _) WK WE DE
  | return_0 f k sp e m m' =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      exact .ret _ _ _ _ (hasType_undef _) (call_cont_wt WK)
  | return_1 f a k sp e m v m' hv =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Sreturn_some _ ha => exact .ret _ _ _ _ (wt_eval_expr hv ha WE) (call_cont_wt WK)
  | label f lbl s k sp e m =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      cases WS with
      | Slabel _ _ h1 => exact .normal _ _ _ _ _ _ env WF h1 WK WE DE
  | goto f lbl k sp e m s' k' hfl =>
    cases hwt with
    | normal _ _ _ _ _ _ env WF WS WK WE DE =>
      have WCK : WtCont env f.fn_sig.sig_res (Cminor.callCont k) := .other _ _ _ (call_cont_wt WK)
      have := wt_find_label lbl _ WF.body WCK
      rw [hfl] at this
      exact .normal _ _ _ _ _ _ env WF this.1 this.2 WE DE
  | internal_function f vargs k m m' sp e _ _ he =>
    cases hwt with
    | call _ _ _ _ WFD WA WK =>
      cases WFD with
      | internal env _ WF =>
        subst he
        refine .normal _ _ _ _ _ _ env WF WF.body (.other _ _ _ WK) ?_ ?_
        · apply wt_env_set_locals
          apply wt_env_set_params
          rw [WF.params]; exact WA
        · intro id hin
          apply def_set_locals
          rcases hin with hin | hin
          · exact .inl (def_set_params id _ _ hin)
          · exact .inr hin
  | external_function ef vargs k m t vres m' hx =>
    cases hwt with
    | call _ _ _ _ WFD WA WK =>
      exact .ret _ _ _ _ (Val.has_proj_xtype (hec ef _ _ _ _ _ _ hx)) WK
  | «return» v optid f sp e k m =>
    cases hwt with
    | ret _ _ _ tret WR WK =>
      cases WK with
      | Kcall _ _ _ _ _ _ env WF WK WE DE WD =>
        refine .normal _ _ _ _ _ _ env WF .Sskip WK ?_ ?_
        · cases optid with
          | none => exact WE
          | some id => exact wt_env_assign WE (WD ▸ WR)
        · cases optid with
          | none => exact DE
          | some id => exact def_env_assign DE

include wt_p hext hasm in
/-- `Cminortyping.subject_reduction_star` -/
theorem subject_reduction_star {st1 : Cminor.State} {t : Trace} {st2 : Cminor.State}
    (hst : Smallstep.Star (Cminor.Step p.globalenv) st1 t st2) (hwt : WtState st1) : WtState st2 := by
  induction hst with
  | refl => exact hwt
  | step h1 _ _ ih => exact ih (subject_reduction p wt_p hext hasm h1 hwt)

include wt_p in
/-- `Cminortyping.wt_initial_state` -/
theorem wt_initial_state {S : Cminor.State} (h : Cminor.InitialState p S) : WtState S := by
  cases h with
  | intro b f m0 _ _ hf hsig =>
    refine .call _ _ _ _ (Genv.findFunctPtr_prop WtFundef (fun id f hin => wt_p id f hin) hf) ?_ ?_
    · rw [hsig]; trivial
    · rw [hsig]; exact .Kstop

end SUBJECT_REDUCTION

/-! ## Safe expressions -/

/-- `Cminortyping.eval_safe_expr` -/
theorem eval_safe_expr (ge : Cminor.CGenv) (f : Cminor.Function) (sp : Val) (e : Cminor.Env)
    (m : Mem) (hd : DefEnv f e) :
    ∀ (a : Cminor.Expr), safeExpr (knownId f) a = true → ∃ v, Cminor.EvalExpr ge sp e m a v
  | .Evar id, h => by
    obtain ⟨v, hv⟩ := hd id (knownId_sound_2 f id h)
    exact ⟨v, .Evar _ _ hv⟩
  | .Econst c, _ => by
    cases c <;> exact ⟨_, .Econst _ _ rfl⟩
  | .Eunop op a1, h => by
    simp only [safeExpr, Bool.and_eq_true] at h
    obtain ⟨v1, h1⟩ := eval_safe_expr ge f sp e m hd a1 h.2
    have : ∃ v, Cminor.evalUnop op v1 = some v := by
      cases op <;> simp [safeUnop] at h <;> exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := this
    exact ⟨v, .Eunop _ _ _ _ h1 hv⟩
  | .Ebinop op a1 a2, h => by
    simp only [safeExpr, Bool.and_eq_true] at h
    obtain ⟨v1, h1⟩ := eval_safe_expr ge f sp e m hd a1 h.1.2
    obtain ⟨v2, h2⟩ := eval_safe_expr ge f sp e m hd a2 h.2
    have : ∃ v, Cminor.evalBinop op v1 v2 m = some v := by
      cases op <;> simp [safeBinop] at h <;> exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := this
    exact ⟨v, .Ebinop _ _ _ _ _ _ h1 h2 hv⟩
  | .Eload _ _, h => by simp [safeExpr] at h

end Cminortyping
end CC
