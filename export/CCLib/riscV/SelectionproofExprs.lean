/-
  Correctness of instruction selection for RV64 (the RISC-V instance of
  `CCLib/backend/SelectionproofExprs.lean`) — port of `backend/Selectionproof.v`,
  part 4: recognition of calls (`expr_is_addrof_ident_correct`,
  `classify_call_correct`) and `Section EXPRESSIONS` up to the built-ins:
  `sel_expr_correct`, `sel_exprlist_correct`, `sel_select_expr_correct`,
  `sel_builtin_arg_correct`, `sel_builtin_args_correct`,
  `sel_builtin_res_correct`, `sel_builtin_default_correct`,
  `sel_builtin_correct`.

  Differences from Rocq: instead of the section variables `prog`/`tprog`, the
  Cminor global environment `ge` and the CminorSel global environment `tge`
  are arbitrary, related only by `hsym` (same symbol table) and, for the
  built-ins, `hsenv` (same symbol environment). `external_call_mem_extends`
  (an axiom-derived property in Rocq) is the hypothesis `hec`.
  `classify_call_correct` is stated for the whole
  program (no `linkorder` context).
-/
import CCLib.riscV.SelectionproofLessdef
import CCLib.common.EventsExtends

namespace CC
namespace RiscV
namespace Selectionproof

open Op CminorSel SelectOp Selection Builtins
open CC.Selection (Globdef CallKind exprIsAddrofIdent classifyCall selBuiltinRes StmtClass
  classifyStmt getHelpers)

/-- `Selectionproof.expr_is_addrof_ident_correct` -/
theorem expr_is_addrof_ident_correct {e : Cminor.Expr} {id : Ident}
    (h : exprIsAddrofIdent e = some id) :
    e = .Econst (.Oaddrsymbol id Integers.Ptrofs.zero) := by
  unfold exprIsAddrofIdent at h
  split at h
  · next id' ofs =>
    by_cases hz : Integers.Ptrofs.eq ofs Integers.Ptrofs.zero = true
    · rw [if_pos hz] at h
      cases h
      have : ofs = Integers.Ptrofs.zero := (Integers.MI.eq_spec _ _).mp hz
      rw [this]
    · rw [if_neg hz] at h; cases h
  · cases h

theorem symbolAddress_preserved {F1 V1 F2 V2 : Type} {ge : Genv F1 V1} {tge : Genv F2 V2}
    (hsym : ∀ id, Genv.findSymbol tge id = Genv.findSymbol ge id) (id : Ident)
    (ofs : Integers.Ptrofs) : Genv.symbolAddress tge id ofs = Genv.symbolAddress ge id ofs := by
  unfold Genv.symbolAddress; rw [hsym]

section EXPRESSIONS
variable {ge : Cminor.CGenv} {tge : CminorSel.CGenv}
  (hsym : ∀ id, Genv.findSymbol tge id = Genv.findSymbol ge id)
  (opts : Options)

include hsym in
/-- `Selectionproof.sel_expr_correct` -/
theorem sel_expr_correct {sp : Val} {e : Cminor.Env} {m : Mem} {a : Cminor.Expr} {v : Val}
    (h : Cminor.EvalExpr ge sp e m a v) :
    ∀ {e' : Cminor.Env} {le : Letenv} {m' : Mem}, EnvLessdef e e' → Mem.Extends m m' →
    ∃ v', CminorSel.EvalExpr tge sp e' m' le (selExpr opts a) v' ∧ Val.Lessdef v v' := by
  induction h with
  | Evar id v hv =>
    intro e' le m' he _
    obtain ⟨v', h1, h2⟩ := he _ _ hv
    exact ⟨v', .Evar _ _ _ h1, h2⟩
  | Econst cst v hv =>
    intro e' le m' _ _
    cases cst <;> simp only [Cminor.evalConstant] at hv <;> cases hv
    · exact ⟨_, .Eop _ _ _ _ _ (.Enil _) rfl, .refl _⟩
    · exact ⟨_, .Eop _ _ _ _ _ (.Enil _) rfl, .refl _⟩
    · exact ⟨_, .Eop _ _ _ _ _ (.Enil _) rfl, .refl _⟩
    · exact ⟨_, SelectLongproof.eval_longconst _ _, .refl _⟩
    · rename_i id ofs
      rw [← symbolAddress_preserved hsym]
      exact SelectOpproof.eval_addrsymbol _ _ _
    · exact SelectOpproof.eval_addrstack _ _
  | Eunop op a1 v1 v _ hv ih =>
    intro e' le m' he hm
    obtain ⟨v1', A, B⟩ := ih he hm
    obtain ⟨v', C, D⟩ := eval_unop_lessdef hv B
    obtain ⟨v'', E, F⟩ := eval_sel_unop A C
    exact ⟨v'', E, Val.lessdef_trans D F⟩
  | Ebinop op a1 a2 v1 v2 v _ _ hv ih1 ih2 =>
    intro e' le m' he hm
    obtain ⟨v1', A, B⟩ := ih1 he hm
    obtain ⟨v2', C, D⟩ := ih2 he hm
    obtain ⟨v', E, F⟩ := eval_binop_lessdef hv B D hm
    obtain ⟨v'', P, Q⟩ := eval_sel_binop opts A C E
    exact ⟨v'', P, Val.lessdef_trans F Q⟩
  | Eload chunk addr vaddr v _ hl ih =>
    intro e' le m' he hm
    obtain ⟨vaddr', A, B⟩ := ih he hm
    obtain ⟨v', C, D⟩ := Mem.loadv_extends hm hl B
    exact ⟨v', eval_load opts A C, D⟩

include hsym in
/-- `Selectionproof.sel_exprlist_correct` -/
theorem sel_exprlist_correct {sp : Val} {e : Cminor.Env} {m : Mem} {al : List Cminor.Expr}
    {vl : List Val} (h : Cminor.EvalExprlist ge sp e m al vl) :
    ∀ {e' : Cminor.Env} {le : Letenv} {m' : Mem}, EnvLessdef e e' → Mem.Extends m m' →
    ∃ vl', CminorSel.EvalExprlist tge sp e' m' le (selExprlist opts al) vl' ∧
      Val.LessdefList vl vl' := by
  induction h with
  | nil => intro _ _ _ _ _; exact ⟨[], .Enil _, .nil⟩
  | cons a1 al v1 vl h1 _ ih =>
    intro e' le m' he hm
    obtain ⟨v1', A, B⟩ := sel_expr_correct hsym opts h1 he hm
    obtain ⟨vl', C, D⟩ := ih he hm
    exact ⟨v1' :: vl', .Econs _ _ _ _ _ A C, .cons B D⟩

include hsym in
/-- `Selectionproof.sel_select_expr_correct` -/
theorem sel_select_expr_correct (ty : ATyp) {cond a1 a2 : Cminor.Expr} {sp : Val}
    {e : Cminor.Env} {m : Mem} {vcond v1 v2 : Val} {b : Bool} {e' : Cminor.Env} {m' : Mem}
    {le : Letenv}
    (hc : Cminor.EvalExpr ge sp e m cond vcond) (h1 : Cminor.EvalExpr ge sp e m a1 v1)
    (h2 : Cminor.EvalExpr ge sp e m a2 v2) (hb : Val.BoolOfVal vcond b)
    (he : EnvLessdef e e') (hm : Mem.Extends m m') :
    ∃ v', CminorSel.EvalExpr tge sp e' m' le (selSelectExpr opts ty cond a1 a2) v' ∧
      Val.Lessdef (Val.select (some b) v1 v2 ty) v' := by
  obtain ⟨vcond', EVC, LDC⟩ := sel_expr_correct (le := le) hsym opts hc he hm
  obtain ⟨v1', EV1, LD1⟩ := sel_expr_correct (le := le) hsym opts h1 he hm
  obtain ⟨v2', EV2, LD2⟩ := sel_expr_correct (le := le) hsym opts h2 he hm
  have hb' : Val.BoolOfVal vcond' b := by
    cases hb with
    | int n => cases LDC; exact .int n
  obtain ⟨vargs', EVARGS, EVCOND⟩ := eval_condition_of_expr EVC hb'
  unfold selSelectExpr
  rcases hce : conditionOfExpr (selExpr opts cond) with ⟨cnd, args⟩
  rw [hce] at EVARGS EVCOND
  dsimp only
  obtain ⟨v', X, Y⟩ := SelectOpproof.eval_select ty cnd EVARGS EV1 EV2
  rw [EVCOND] at Y
  refine ⟨v', X, Val.lessdef_trans ?_ Y⟩
  apply Val.normalize_lessdef
  cases b
  · exact LD2
  · exact LD1

include hsym in
/-- `Selectionproof.sel_builtin_arg_correct` -/
theorem sel_builtin_arg_correct {sp : Val} {e e' : Cminor.Env} {m m' : Mem} {a : Cminor.Expr}
    {v : Val} (c : BuiltinArgConstraint) (he : EnvLessdef e e') (hm : Mem.Extends m m')
    (ha : Cminor.EvalExpr ge sp e m a v) :
    ∃ v', CminorSel.EvalBuiltinArg tge sp e' m' (selBuiltinArg opts a c) v' ∧
      Val.Lessdef v v' := by
  obtain ⟨v1, A, B⟩ := sel_expr_correct (le := []) hsym opts ha he hm
  refine ⟨v1, ?_, B⟩
  unfold selBuiltinArg
  dsimp only
  split
  · exact SelectOpproof.eval_builtin_arg A
  · exact .BA _ _ A

include hsym in
/-- `Selectionproof.sel_builtin_args_correct` -/
theorem sel_builtin_args_correct {sp : Val} {e e' : Cminor.Env} {m m' : Mem}
    (he : EnvLessdef e e') (hm : Mem.Extends m m') {al : List Cminor.Expr} {vl : List Val}
    (h : Cminor.EvalExprlist ge sp e m al vl) :
    ∀ (cl : List BuiltinArgConstraint), ∃ vl',
      ListForall2 (CminorSel.EvalBuiltinArg tge sp e' m') (selBuiltinArgs opts al cl) vl' ∧
      Val.LessdefList vl vl' := by
  induction h with
  | nil => intro cl; exact ⟨[], .nil, .nil⟩
  | cons a1 al v1 vl h1 _ ih =>
    intro cl
    obtain ⟨v1', A, B⟩ := sel_builtin_arg_correct hsym opts (cl.headD .OK_default) he hm h1
    obtain ⟨vl', C, D⟩ := ih cl.tail
    exact ⟨v1' :: vl', .cons A C, .cons B D⟩

/-- `Selectionproof.sel_builtin_res_correct` -/
theorem sel_builtin_res_correct {oid : Option Ident} {v v' : Val} {e e' : Cminor.Env}
    (he : EnvLessdef e e') (hv : Val.Lessdef v v') :
    EnvLessdef (Cminor.setOptvar oid v e) (setBuiltinRes (selBuiltinRes oid) v' e') := by
  cases oid with
  | none => exact he
  | some id => exact set_var_lessdef he hv

variable (hsenv : Genv.toSenv tge = Genv.toSenv ge)
  (hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv ge))

include hsym hsenv hec in
/-- `Selectionproof.sel_builtin_default_correct` -/
theorem sel_builtin_default_correct {optid : Option Ident} {ef : ExtFun} {al : List Cminor.Expr}
    {sp : Val} {e1 : Cminor.Env} {m1 : Mem} {vl : List Val} {t : Trace} {v : Val} {m2 : Mem}
    {e1' : Cminor.Env} {m1' : Mem} {f : CminorSel.Function} {k : CminorSel.Cont}
    (hl : Cminor.EvalExprlist ge sp e1 m1 al vl)
    (hx : externalCall ef (Genv.toSenv ge) vl m1 t v m2)
    (he : EnvLessdef e1 e1') (hm : Mem.Extends m1 m1') :
    ∃ e2' m2', Smallstep.Plus (CminorSel.Step tge)
        (.State f (selBuiltinDefault opts optid ef al) k sp e1' m1') t
        (.State f .Sskip k sp e2' m2') ∧
      EnvLessdef (Cminor.setOptvar optid v e1) e2' ∧ Mem.Extends m2 m2' := by
  obtain ⟨vl', A, B⟩ := sel_builtin_args_correct hsym opts he hm hl (builtinConstraints ef)
  obtain ⟨v', m2', D, E, F, _⟩ := hec ef _ _ _ _ _ _ _ hx hm B
  refine ⟨_, m2', Smallstep.plus_one ?_, sel_builtin_res_correct he E, F⟩
  unfold selBuiltinDefault
  exact .builtin _ _ _ _ _ _ _ _ _ _ _ _ A (by rw [hsenv]; exact D)

include hsym hsenv hec in
/-- `Selectionproof.sel_builtin_correct` -/
theorem sel_builtin_correct {optid : Option Ident} {ef : ExtFun} {al : List Cminor.Expr}
    {sp : Val} {e1 : Cminor.Env} {m1 : Mem} {vl : List Val} {t : Trace} {v : Val} {m2 : Mem}
    {e1' : Cminor.Env} {m1' : Mem} {f : CminorSel.Function} {k : CminorSel.Cont}
    (hl : Cminor.EvalExprlist ge sp e1 m1 al vl)
    (hx : externalCall ef (Genv.toSenv ge) vl m1 t v m2)
    (he : EnvLessdef e1 e1') (hm : Mem.Extends m1 m1') :
    ∃ e2' m2', Smallstep.Plus (CminorSel.Step tge)
        (.State f (selBuiltin opts optid ef al) k sp e1' m1') t
        (.State f .Sskip k sp e2' m2') ∧
      EnvLessdef (Cminor.setOptvar optid v e1) e2' ∧ Mem.Extends m2 m2' := by
  have dflt := sel_builtin_default_correct (f := f) (k := k) (optid := optid) hsym opts
    hsenv hec hl hx he hm
  obtain ⟨vl', A, B⟩ := sel_exprlist_correct (le := []) hsym opts hl he hm
  obtain ⟨v', m2', D, E, F, _⟩ := hec ef _ _ _ _ _ _ _ hx hm B
  unfold selBuiltin
  split
  · next name sg =>
    split
    · next bf hlk =>
      have D' := D
      simp only [externalCall, builtinOrExternalSem, hlk] at D'
      cases D' with
      | intro _ _ _ _ hsem =>
      simp only [externalCall, builtinOrExternalSem, hlk] at hx
      cases hx with
      | intro _ _ _ _ hsem0 =>
      split
      · next id =>
        split
        · next a hskb =>
          obtain ⟨v'', U, V⟩ := eval_sel_known_builtin hskb A hsem
          refine ⟨_, _, Smallstep.plus_one (.assign _ _ _ _ _ _ _ _ U), ?_, F⟩
          exact set_var_lessdef he (Val.lessdef_trans E V)
        · exact dflt
      · exact ⟨e1', _, Smallstep.plus_left (.seq _ _ _ _ _ _ _) (Smallstep.star_one (.skip_seq _ _ _ _ _ _)) rfl, he, F⟩
    · exact dflt
  · exact dflt

end EXPRESSIONS

end Selectionproof
end RiscV
end CC
