/-
  [x86-64 instance of `CCLib/backend/RTLgenproofExpr.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness of RTL generation — port of `backend/RTLgenproof.v`, part 2:
  `sig_transl_function`, `tr_move_correct`, and semantic preservation for
  the translation of expressions (`transl_expr_correct`,
  `transl_exprlist_correct`, `transl_condexpr_correct`) and exit
  expressions (`transl_exitexpr_correct`).

  The global environments enter only through the hypotheses `hsym`
  (symbols preserved), `hsenv` (same symbol environment) and `hfext`
  (external functions preserved); `hec` is the compatibility of external
  calls with memory extensions.
-/
import CCLib.x86.RTLgenproofEnv
import CCLib.x86.OpTheory
import CCLib.x86.Conventions
import CCLib.x86.OpInject
import CCLib.common.EventsExtends

namespace CC
namespace X86
namespace RTLgen

open Op CminorSel Smallstep

/-- `RTLgenproof.sig_transl_function` -/
theorem sig_transl_function {moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool}
    {f : CminorSel.Fundef} {tf : RTL.Fundef} (h : translFundef moreLikely f = .OK tf) :
    RTL.funsig tf = CminorSel.funsig f := by
  cases f with
  | Internal f =>
    simp only [translFundef, ASTFundef.transfPartial] at h
    split at h
    · next tf' htf =>
      cases h
      unfold translFunction at htf
      split at htf
      · cases htf
      · cases htf; rfl
    · cases h
  | External ef => cases h; rfl

section CORRECTNESS_EXPR
variable {ge : CminorSel.CGenv} {tge : RTL.CGenv}
  (hsym : ∀ id, Genv.findSymbol tge id = Genv.findSymbol ge id)
  (hsenv : Genv.toSenv tge = Genv.toSenv ge)
  (hfext : ∀ b ef, Genv.findFunctPtr ge b = some (.External ef) →
    Genv.findFunctPtr tge b = some (.External ef))
  (hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv ge))

/-- `RTLgenproof.tr_move_correct` -/
theorem tr_move_correct {r1 : Reg} {ns : RTL.Node} {r2 : Reg} {nd : RTL.Node}
    {cs : List RTL.Stackframe} {f : RTL.Function} {sp : Val} {rs : RTL.Regset} {m : Mem}
    (h : TrMove f.fn_code ns r1 nd r2) :
    ∃ rs', Smallstep.Star (RTL.Step tge) (.State cs f sp ns rs m) E0 (.State cs f sp nd rs' m) ∧
      rs'.get r2 = rs.get r1 ∧ ∀ r, r ≠ r2 → rs'.get r = rs.get r := by
  cases h with
  | zero => exact ⟨rs, .refl _, rfl, fun _ _ => rfl⟩
  | one =>
    rename_i h
    refine ⟨rs.set r2 (rs.get r1), star_one (RTL.Step.Iop _ _ _ _ _ _ _ _ _ _ _ h rfl), PMap.gss _ _ _,
      fun r hr => PMap.gso _ _ _ _ (Ne.symm hr)⟩

variable (sp : Val) (e : Cminor.Env) (m : Mem)

/-- `RTLgenproof.transl_expr_prop` -/
def TranslExprProp (tge : RTL.CGenv) (sp : Val) (e : Cminor.Env) (m : Mem) (le : Letenv)
    (a : CminorSel.Expr) (v : Val) : Prop :=
  ∀ (tm : Mem) (cs : List RTL.Stackframe) (f : RTL.Function) (map : Mapping) (pr : List Reg)
    (ns nd : RTL.Node) (rd : Reg) (rs : RTL.Regset) (dst : Option Ident),
    MapWf map → TrExpr f.fn_code map pr a ns nd rd dst → MatchEnv map e le rs → Mem.Extends m tm →
    ∃ rs' tm', Smallstep.Star (RTL.Step tge) (.State cs f sp ns rs tm) E0 (.State cs f sp nd rs' tm') ∧
      MatchEnv map (Cminor.setOptvar dst v e) le rs' ∧ Val.Lessdef v (rs'.get rd) ∧
      (∀ r, r ∈ pr → rs'.get r = rs.get r) ∧ Mem.Extends m tm'

/-- `RTLgenproof.transl_exprlist_prop` -/
def TranslExprlistProp (tge : RTL.CGenv) (sp : Val) (e : Cminor.Env) (m : Mem) (le : Letenv)
    (al : Exprlist) (vl : List Val) : Prop :=
  ∀ (tm : Mem) (cs : List RTL.Stackframe) (f : RTL.Function) (map : Mapping) (pr : List Reg)
    (ns nd : RTL.Node) (rl : List Reg) (rs : RTL.Regset),
    MapWf map → TrExprlist f.fn_code map pr al ns nd rl → MatchEnv map e le rs →
    Mem.Extends m tm →
    ∃ rs' tm', Smallstep.Star (RTL.Step tge) (.State cs f sp ns rs tm) E0 (.State cs f sp nd rs' tm') ∧
      MatchEnv map e le rs' ∧ Val.LessdefList vl (rs'.getList rl) ∧
      (∀ r, r ∈ pr → rs'.get r = rs.get r) ∧ Mem.Extends m tm'

/-- `RTLgenproof.transl_condexpr_prop` -/
def TranslCondexprProp (tge : RTL.CGenv) (sp : Val) (e : Cminor.Env) (m : Mem) (le : Letenv)
    (a : Condexpr) (v : Bool) : Prop :=
  ∀ (tm : Mem) (cs : List RTL.Stackframe) (f : RTL.Function) (map : Mapping) (pr : List Reg)
    (ns ntrue nfalse : RTL.Node) (rs : RTL.Regset),
    MapWf map → TrCondition f.fn_code map pr a ns ntrue nfalse → MatchEnv map e le rs →
    Mem.Extends m tm →
    ∃ rs' tm', Smallstep.Plus (RTL.Step tge) (.State cs f sp ns rs tm) E0
        (.State cs f sp (if v then ntrue else nfalse) rs' tm') ∧
      MatchEnv map e le rs' ∧ (∀ r, r ∈ pr → rs'.get r = rs.get r) ∧ Mem.Extends m tm'

/-- `RTLgenproof.eval_builtin_args_trivial` -/
theorem eval_builtin_args_trivial (senv : Senv) (rs : RTL.Regset) (sp : Val) (m : Mem) :
    ∀ (rl : List Reg), EvalBuiltinArgs senv (fun r => rs.get r) sp m (rl.map .BA) (rs.getList rl)
  | [] => .nil
  | _ :: rl => .cons (.BA _) (eval_builtin_args_trivial senv rs sp m rl)

/-- Moves: the common part of the `Evar` and `Eletvar` cases. -/
theorem transl_move_case {map : Mapping} {pr : List Reg} {e : Cminor.Env} {le : Letenv}
    {rs rs' : RTL.Regset} {r rd : Reg} {dst : Option Ident} {v : Val} (MWF : MapWf map)
    (ME : MatchEnv map e le rs) (EQ : Val.Lessdef v (rs.get r))
    (hd : (rd = r ∧ dst = none) ∨ (RegMapOk map rd dst ∧ rd ∉ pr))
    (B : rs'.get rd = rs.get r) (C : ∀ r0, r0 ≠ rd → rs'.get r0 = rs.get r0) :
    MatchEnv map (Cminor.setOptvar dst v e) le rs' ∧ Val.Lessdef v (rs'.get rd) ∧
      (∀ r0, r0 ∈ pr → rs'.get r0 = rs.get r0) := by
  rcases hd with ⟨rfl, rfl⟩ | ⟨D, E⟩
  · have hall : ∀ r0, rs'.get r0 = rs.get r0 := by
      intro r0
      by_cases h : r0 = rd
      · subst h; exact B
      · exact C r0 h
    exact ⟨match_env_invariant ME (fun r0 _ => hall r0), by rw [B]; exact EQ, fun r0 _ => hall r0⟩
  · refine ⟨match_env_invariant (match_env_update_dest EQ MWF D ME) (fun r0 _ => ?_),
      by rw [B]; exact EQ, fun r0 h0 => C r0 (fun he => E (he ▸ h0))⟩
    rw [PMap.gsspec]
    split
    · next he => subst he; exact B
    · next hne => exact C r0 hne

include hsym hsenv hfext hec in
mutual
/-- `RTLgenproof.transl_expr_correct` -/
theorem transl_expr_correct {le : Letenv} {a : CminorSel.Expr} {v : Val} :
    CminorSel.EvalExpr ge sp e m le a v → TranslExprProp tge sp e m le a v
  | .Evar _ id _ he => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    cases TE with
    | Evar _ _ _ _ _ r _ _ hr hd hmv =>
      have EQ := match_env_find_var ME he hr
      obtain ⟨rs', A, B, C⟩ := tr_move_correct (cs := cs) (sp := sp) (m := tm) (tge := tge) hmv
      obtain ⟨X, Y, Z⟩ := transl_move_case MWF ME EQ hd B C
      exact ⟨rs', tm, A, X, Y, Z, EXT⟩
  | .Eop _ op al vl _ hl hop => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    cases TE with
    | Eop _ _ _ _ _ _ _ n1 rl _ htl hcode hrm hpr =>
      obtain ⟨rs1, tm1, EX1, ME1, RR1, RO1, EXT1⟩ :=
        transl_exprlist_correct hl tm cs f map pr ns n1 rl rs MWF htl ME EXT
      obtain ⟨v', A, B⟩ := evalOperation_lessdef ge sp op RR1 EXT1 hop
      refine ⟨rs1.set rd v', tm1, star_right EX1 (.Iop _ _ _ _ _ _ _ _ _ _ _ hcode
        (by rw [Op.evalOperation_preserved ge tge hsym]; exact A)) rfl,
        match_env_update_dest B MWF hrm ME1, by rw [PMap.gss]; exact B, fun r hr => ?_, EXT1⟩
      rw [PMap.gso _ _ _ _ (fun he => hpr (by subst he; exact hr))]
      exact RO1 r hr
  | .Eload _ chunk addr al vl vaddr _ hl ha hld => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    cases TE with
    | Eload _ _ _ _ _ _ _ _ n1 rl _ htl hcode hrm hpr =>
      obtain ⟨rs1, tm1, EX1, ME1, RR1, RO1, EXT1⟩ :=
        transl_exprlist_correct hl tm cs f map pr ns n1 rl rs MWF htl ME EXT
      obtain ⟨vaddr', A, B⟩ := evalAddressing_lessdef ge sp addr RR1 ha
      obtain ⟨v', C, D⟩ := Mem.loadv_extends EXT1 hld B
      refine ⟨rs1.set rd v', tm1, star_right EX1 (.Iload _ _ _ _ _ _ _ _ _ _ _ _ _ hcode
        (by rw [Op.evalAddressing_preserved ge tge hsym]; exact A) C) rfl,
        match_env_update_dest D MWF hrm ME1, by rw [PMap.gss]; exact D, fun r hr => ?_, EXT1⟩
      rw [PMap.gso _ _ _ _ (fun he => hpr (by subst he; exact hr))]
      exact RO1 r hr
  | .Econdition _ a b c va _ hc hv => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    have IH2 := transl_expr_correct hv
    cases TE with
    | Econdition _ _ _ _ _ _ _ _ ntrue nfalse _ htc htb htc' =>
      obtain ⟨rs1, tm1, EX1, ME1, OTHER1, EXT1⟩ :=
        transl_condexpr_correct hc tm cs f map pr ns ntrue nfalse rs MWF htc ME EXT
      have TE' : TrExpr f.fn_code map pr (if va then b else c) (if va then ntrue else nfalse) nd rd
          dst := by cases va <;> assumption
      obtain ⟨rs2, tm2, EX2, ME2, RES2, OTHER2, EXT2⟩ :=
        IH2 tm1 cs f map pr _ nd rd rs1 dst MWF TE' ME1 EXT1
      exact ⟨rs2, tm2, star_trans (plus_star EX1) EX2 rfl, ME2, RES2,
        fun r hr => (OTHER2 r hr).trans (OTHER1 r hr), EXT2⟩
  | .Elet _ a b v1 _ h1 h2 => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    cases TE with
    | Elet _ _ _ _ _ _ _ n1 r _ hnr hta htb =>
      obtain ⟨rs1, tm1, EX1, ME1, RES1, OTHER1, EXT1⟩ :=
        transl_expr_correct h1 tm cs f map pr ns n1 r rs none MWF hta ME EXT
      obtain ⟨rs2, tm2, EX2, ME3, RES2, OTHER2, EXT2⟩ :=
        transl_expr_correct h2 tm1 cs f (addLetvar map r) pr n1 nd rd rs1 dst
          (add_letvar_wf MWF hnr) htb (match_env_bind_letvar ME1 RES1) EXT1
      exact ⟨rs2, tm2, star_trans EX1 EX2 rfl, match_env_unbind_letvar ME3, RES2,
        fun r0 hr => (OTHER2 r0 hr).trans (OTHER1 r0 hr), EXT2⟩
  | .Eletvar _ n _ hn => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    cases TE with
    | Eletvar _ _ _ _ _ _ r _ hr hd hmv =>
      have EQ := match_env_find_letvar ME hn hr
      obtain ⟨rs', A, B, C⟩ := tr_move_correct (cs := cs) (sp := sp) (m := tm) (tge := tge) hmv
      obtain ⟨X, Y, Z⟩ := transl_move_case MWF ME EQ hd B C
      exact ⟨rs', tm, A, X, Y, Z, EXT⟩
  | .Ebuiltin _ ef al vl _ hl hx => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    cases TE with
    | Ebuiltin _ _ _ _ _ _ _ _ n1 rl htl hcode hrm hpr =>
      obtain ⟨rs1, tm1, EX1, ME1, RR1, RO1, EXT1⟩ :=
        transl_exprlist_correct hl tm cs f map pr ns n1 rl rs MWF htl ME EXT
      obtain ⟨v', tm2, A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hx EXT1 RR1
      refine ⟨rs1.set rd v', tm2, star_right EX1 (.Ibuiltin _ _ _ _ _ _ _ _ (.BR rd) _ _ _ v' tm2
        hcode (eval_builtin_args_trivial _ rs1 sp tm1 rl) (by rw [hsenv]; exact A)) rfl,
        match_env_update_dest B MWF hrm ME1, by rw [PMap.gss]; exact B, fun r hr => ?_, C⟩
      rw [PMap.gso _ _ _ _ (fun he => hpr (by subst he; exact hr))]
      exact RO1 r hr
  | .Eexternal _ id sg al b ef vl _ hfs hfp hsig hl hx => by
    intro tm cs f map pr ns nd rd rs dst MWF TE ME EXT
    cases TE with
    | Eexternal _ _ _ _ _ _ _ _ _ n1 rl htl hcode hrm hpr =>
      obtain ⟨rs1, tm1, EX1, ME1, RR1, RO1, EXT1⟩ :=
        transl_exprlist_correct hl tm cs f map pr ns n1 rl rs MWF htl ME EXT
      obtain ⟨v', tm2, A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hx EXT1 RR1
      have hfind : RTL.findFunction tge (.inr id) rs1 = some (.External ef) := by
        simp only [RTL.findFunction, hsym, hfs]
        exact hfext _ _ hfp
      refine ⟨rs1.set rd v', tm2, star_trans EX1
        (star_left (.Icall _ _ _ _ _ _ _ _ _ _ _ _ hcode hfind hsig)
          (star_left (.function_external _ _ _ _ _ _ _ (by rw [hsenv]; exact A))
            (star_one (.return _ _ _ _ _ _ _ _)) rfl) rfl) rfl,
        match_env_update_dest B MWF hrm ME1, by rw [PMap.gss]; exact B, fun r hr => ?_, C⟩
      rw [PMap.gso _ _ _ _ (fun he => hpr (by subst he; exact hr))]
      exact RO1 r hr

/-- `RTLgenproof.transl_exprlist_correct` -/
theorem transl_exprlist_correct {le : Letenv} {al : Exprlist} {vl : List Val} :
    CminorSel.EvalExprlist ge sp e m le al vl → TranslExprlistProp tge sp e m le al vl
  | .Enil _ => by
    intro tm cs f map pr ns nd rl rs MWF TE ME EXT
    cases TE
    exact ⟨rs, tm, .refl _, ME, .nil, fun _ _ => rfl, EXT⟩
  | .Econs _ a1 al v1 vl h1 hl => by
    intro tm cs f map pr ns nd rl rs MWF TE ME EXT
    cases TE with
    | Econs _ _ _ _ _ _ r1 rl' n1 hta htl =>
      obtain ⟨rs1, tm1, EX1, ME1, RES1, OTHER1, EXT1⟩ :=
        transl_expr_correct h1 tm cs f map pr ns n1 r1 rs none MWF hta ME EXT
      obtain ⟨rs2, tm2, EX2, ME2, RES2, OTHER2, EXT2⟩ :=
        transl_exprlist_correct hl tm1 cs f map (r1 :: pr) n1 nd rl' rs1 MWF htl ME1 EXT1
      exact ⟨rs2, tm2, star_trans EX1 EX2 rfl, ME2,
        .cons (by show Val.Lessdef _ (PMap.get r1 rs2); rw [OTHER2 r1 (.head _)]; exact RES1) RES2,
        fun r hr => (OTHER2 r (.tail _ hr)).trans (OTHER1 r hr), EXT2⟩

/-- `RTLgenproof.transl_condexpr_correct` -/
theorem transl_condexpr_correct {le : Letenv} {a : Condexpr} {v : Bool} :
    CminorSel.EvalCondexpr ge sp e m le a v → TranslCondexprProp tge sp e m le a v
  | .CEcond _ cond al vl _ hl hc => by
    intro tm cs f map pr ns ntrue nfalse rs MWF TE ME EXT
    cases TE with
    | CEcond _ _ _ _ _ _ _ n1 rl htl hcode =>
      obtain ⟨rs1, tm1, EX1, ME1, RES1, OTHER1, EXT1⟩ :=
        transl_exprlist_correct hl tm cs f map pr ns n1 rl rs MWF htl ME EXT
      exact ⟨rs1, tm1, plus_right EX1 (.Icond _ _ _ _ _ _ _ _ _ _ _ _ hcode
        (evalCondition_lessdef RES1 EXT1 hc) rfl) rfl, ME1, OTHER1, EXT1⟩
  | .CEcondition _ a b c va _ ha hb => by
    intro tm cs f map pr ns ntrue nfalse rs MWF TE ME EXT
    have IH2 := transl_condexpr_correct hb
    cases TE with
    | CEcondition _ _ _ _ _ _ _ _ n2 n3 hta htb htc =>
      obtain ⟨rs1, tm1, EX1, ME1, OTHER1, EXT1⟩ :=
        transl_condexpr_correct ha tm cs f map pr ns n2 n3 rs MWF hta ME EXT
      have TE' : TrCondition f.fn_code map pr (if va then b else c) (if va then n2 else n3)
          ntrue nfalse := by cases va <;> assumption
      obtain ⟨rs2, tm2, EX2, ME2, OTHER2, EXT2⟩ :=
        IH2 tm1 cs f map pr _ ntrue nfalse rs1 MWF TE' ME1 EXT1
      exact ⟨rs2, tm2, plus_trans EX1 EX2 rfl, ME2,
        fun r hr => (OTHER2 r hr).trans (OTHER1 r hr), EXT2⟩
  | .CElet _ a b v1 _ ha hb => by
    intro tm cs f map pr ns ntrue nfalse rs MWF TE ME EXT
    cases TE with
    | CElet _ _ _ _ _ _ _ r n1 hnr hta htb =>
      obtain ⟨rs1, tm1, EX1, ME1, RES1, OTHER1, EXT1⟩ :=
        transl_expr_correct ha tm cs f map pr ns n1 r rs none MWF hta ME EXT
      obtain ⟨rs2, tm2, EX2, ME3, OTHER2, EXT2⟩ :=
        transl_condexpr_correct hb tm1 cs f (addLetvar map r) pr n1 ntrue nfalse rs1
          (add_letvar_wf MWF hnr) htb (match_env_bind_letvar ME1 RES1) EXT1
      exact ⟨rs2, tm2, star_plus_trans EX1 EX2 rfl, match_env_unbind_letvar ME3,
        fun r0 hr => (OTHER2 r0 hr).trans (OTHER1 r0 hr), EXT2⟩
end

/-- `RTLgenproof.transl_exitexpr_prop` -/
def TranslExitexprProp (tge : RTL.CGenv) (sp : Val) (e : Cminor.Env) (m : Mem) (le : Letenv)
    (a : Exitexpr) (x : Nat) : Prop :=
  ∀ (tm : Mem) (cs : List RTL.Stackframe) (f : RTL.Function) (map : Mapping) (ns : RTL.Node)
    (nexits : List RTL.Node) (rs : RTL.Regset),
    MapWf map → TrExitexpr f.fn_code map a ns nexits → MatchEnv map e le rs → Mem.Extends m tm →
    ∃ nd rs' tm', Smallstep.Star (RTL.Step tge) (.State cs f sp ns rs tm) E0 (.State cs f sp nd rs' tm') ∧
      nexits[x]? = some nd ∧ MatchEnv map e le rs' ∧ Mem.Extends m tm'

include hsym hsenv hfext hec in
/-- `RTLgenproof.transl_exitexpr_correct` -/
theorem transl_exitexpr_correct {le : Letenv} {a : Exitexpr} {x : Nat} :
    CminorSel.EvalExitexpr ge sp e m le a x → TranslExitexprProp tge sp e m le a x
  | .XEexit _ _ => by
    intro tm cs f map ns nexits rs MWF TE ME EXT
    cases TE with
    | XEcond _ _ _ _ hn => exact ⟨ns, rs, tm, .refl _, hn, ME, EXT⟩
  | .XEjumptable _ a tbl n _ ha hl => by
    intro tm cs f map ns nexits rs MWF TE ME EXT
    cases TE with
    | XEjumptable _ _ _ _ _ n1 r tbl' hjt hta hcode =>
      obtain ⟨nd, A, B⟩ := hjt _ _ hl
      obtain ⟨rs1, tm1, EX1, ME1, RES1, _, EXT1⟩ :=
        transl_expr_correct hsym hsenv hfext hec sp e m ha tm cs f map [] ns n1 r rs none MWF hta
          ME EXT
      have hr : rs1.get r = .Vint n := by
        revert RES1; generalize rs1.get r = x; intro RES1; cases RES1; rfl
      exact ⟨nd, rs1, tm1, star_right EX1 (.Ijumptable _ _ _ _ _ _ _ _ _ _ hcode hr A) rfl, B,
        ME1, EXT1⟩
  | .XEcondition _ a b c va _ ha hb => by
    intro tm cs f map ns nexits rs MWF TE ME EXT
    have IH2 := transl_exitexpr_correct hb
    cases TE with
    | XEcondition _ _ _ _ _ _ n2 n3 htc htb htc' =>
      obtain ⟨rs1, tm1, EX1, ME1, _, EXT1⟩ :=
        transl_condexpr_correct hsym hsenv hfext hec sp e m ha tm cs f map [] ns n2 n3 rs MWF htc
          ME EXT
      have TE' : TrExitexpr f.fn_code map (if va then b else c) (if va then n2 else n3) nexits := by
        cases va <;> assumption
      obtain ⟨nd, rs2, tm2, EX2, EXIT2, ME2, EXT2⟩ := IH2 tm1 cs f map _ nexits rs1 MWF TE' ME1 EXT1
      exact ⟨nd, rs2, tm2, star_trans (plus_star EX1) EX2 rfl, EXIT2, ME2, EXT2⟩
  | .XElet _ a b v _ ha hb => by
    intro tm cs f map ns nexits rs MWF TE ME EXT
    cases TE with
    | XElet _ _ _ _ _ r n1 hnr hta htb =>
      obtain ⟨rs1, tm1, EX1, ME1, RES1, _, EXT1⟩ :=
        transl_expr_correct hsym hsenv hfext hec sp e m ha tm cs f map [] ns n1 r rs none MWF hta
          ME EXT
      obtain ⟨nd, rs2, tm2, EX2, EXIT2, ME2, EXT2⟩ :=
        transl_exitexpr_correct hb tm1 cs f (addLetvar map r) n1 nexits rs1
          (add_letvar_wf MWF hnr) htb (match_env_bind_letvar ME1 RES1) EXT1
      exact ⟨nd, rs2, tm2, star_trans EX1 EX2 rfl, EXIT2, match_env_unbind_letvar ME2, EXT2⟩

end CORRECTNESS_EXPR

end RTLgen
end X86
end CC
