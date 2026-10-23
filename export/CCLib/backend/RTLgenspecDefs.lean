/-
  Abstract specification of RTL generation — port of `backend/RTLgenspec.v`,
  part 2: the relational specification of the translation (`tr_move`,
  `reg_map_ok`, `tr_expr`/`tr_condition`/`tr_exprlist`, `tr_jumptable`,
  `tr_exitexpr`, `tr_builtin_res`, `tr_stmt`, `tr_function`), its
  monotonicity under `state_incr` (`tr_move_incr`, `tr_expr_incr`,
  `tr_condition_incr`, `tr_exprlist_incr`), `new_reg_return_ok` and
  `add_move_charact`.
-/
import CCLib.backend.RTLgenspecBasic

namespace CC
namespace RTLgen

open Op CminorSel RTL

/-- `RTLgenspec.new_reg_return_ok` -/
theorem new_reg_return_ok {s1 s2 : State} {r : Reg} {map : Mapping} {sig : Signature}
    {i : StateIncr s1 s2} (h : newReg s1 = .OK r s2 i) (hm : MapValid map s1) :
    ReturnRegOk s2 map (retReg sig r) := by
  unfold retReg
  split
  · exact .none _ _
  · exact .some _ _ _ (new_reg_not_in_map h hm) (new_reg_valid h)

/-! ## Relational specification of the translation -/

/-- `RTLgenspec.tr_move` -/
inductive TrMove (c : Code) : Node → Reg → Node → Reg → Prop where
  | zero (n r) : TrMove c n r n r
  | one (ns rs nd rd) : c.get ns = some (.Iop .Omove [rs] rd nd) → TrMove c ns rs nd rd

/-- `RTLgenspec.reg_map_ok` -/
inductive RegMapOk : Mapping → Reg → Option Ident → Prop where
  | novar (map rd) : ¬ RegInMap map rd → RegMapOk map rd none
  | somevar (map rd id) : map.map_vars.get id = some rd → RegMapOk map rd (some id)

mutual
/-- `RTLgenspec.tr_expr` -/
inductive TrExpr (c : Code) :
    Mapping → List Reg → CminorSel.Expr → Node → Node → Reg → Option Ident → Prop where
  | Evar (map pr id ns nd r rd dst) : map.map_vars.get id = some r →
      ((rd = r ∧ dst = none) ∨ (RegMapOk map rd dst ∧ rd ∉ pr)) →
      TrMove c ns r nd rd → TrExpr c map pr (.Evar id) ns nd rd dst
  | Eop (map pr op al ns nd rd n1 rl dst) : TrExprlist c map pr al ns n1 rl →
      c.get n1 = some (.Iop op rl rd nd) → RegMapOk map rd dst → rd ∉ pr →
      TrExpr c map pr (.Eop op al) ns nd rd dst
  | Eload (map pr chunk addr al ns nd rd n1 rl dst) : TrExprlist c map pr al ns n1 rl →
      c.get n1 = some (.Iload chunk addr rl rd nd) → RegMapOk map rd dst → rd ∉ pr →
      TrExpr c map pr (.Eload chunk addr al) ns nd rd dst
  | Econdition (map pr a ifso ifnot ns nd rd ntrue nfalse dst) :
      TrCondition c map pr a ns ntrue nfalse →
      TrExpr c map pr ifso ntrue nd rd dst → TrExpr c map pr ifnot nfalse nd rd dst →
      TrExpr c map pr (.Econdition a ifso ifnot) ns nd rd dst
  | Elet (map pr b1 b2 ns nd rd n1 r dst) : ¬ RegInMap map r →
      TrExpr c map pr b1 ns n1 r none → TrExpr c (addLetvar map r) pr b2 n1 nd rd dst →
      TrExpr c map pr (.Elet b1 b2) ns nd rd dst
  | Eletvar (map pr n ns nd rd r dst) : map.map_letvars[n]? = some r →
      ((rd = r ∧ dst = none) ∨ (RegMapOk map rd dst ∧ rd ∉ pr)) →
      TrMove c ns r nd rd → TrExpr c map pr (.Eletvar n) ns nd rd dst
  | Ebuiltin (map pr ef al ns nd rd dst n1 rl) : TrExprlist c map pr al ns n1 rl →
      c.get n1 = some (.Ibuiltin ef (rl.map .BA) (.BR rd) nd) → RegMapOk map rd dst → rd ∉ pr →
      TrExpr c map pr (.Ebuiltin ef al) ns nd rd dst
  | Eexternal (map pr id sg al ns nd rd dst n1 rl) : TrExprlist c map pr al ns n1 rl →
      c.get n1 = some (.Icall sg (.inr id) rl rd nd) → RegMapOk map rd dst → rd ∉ pr →
      TrExpr c map pr (.Eexternal id sg al) ns nd rd dst

/-- `RTLgenspec.tr_condition` -/
inductive TrCondition (c : Code) : Mapping → List Reg → Condexpr → Node → Node → Node → Prop where
  | CEcond (map pr cond bl ns ntrue nfalse n1 rl) : TrExprlist c map pr bl ns n1 rl →
      c.get n1 = some (.Icond cond rl ntrue nfalse) →
      TrCondition c map pr (.CEcond cond bl) ns ntrue nfalse
  | CEcondition (map pr a1 a2 a3 ns ntrue nfalse n2 n3) :
      TrCondition c map pr a1 ns n2 n3 → TrCondition c map pr a2 n2 ntrue nfalse →
      TrCondition c map pr a3 n3 ntrue nfalse →
      TrCondition c map pr (.CEcondition a1 a2 a3) ns ntrue nfalse
  | CElet (map pr a b ns ntrue nfalse r n1) : ¬ RegInMap map r →
      TrExpr c map pr a ns n1 r none → TrCondition c (addLetvar map r) pr b n1 ntrue nfalse →
      TrCondition c map pr (.CElet a b) ns ntrue nfalse

/-- `RTLgenspec.tr_exprlist` -/
inductive TrExprlist (c : Code) : Mapping → List Reg → Exprlist → Node → Node → List Reg → Prop where
  | Enil (map pr n) : TrExprlist c map pr .Enil n n []
  | Econs (map pr a1 al ns nd r1 rl n1) : TrExpr c map pr a1 ns n1 r1 none →
      TrExprlist c map (r1 :: pr) al n1 nd rl →
      TrExprlist c map pr (.Econs a1 al) ns nd (r1 :: rl)
end

/-- `RTLgenspec.tr_jumptable` -/
def TrJumptable (nexits : List Node) (tbl : List Nat) (ttbl : List Node) : Prop :=
  ∀ v act, CminorSel.listNthZ tbl v = some act →
    ∃ n, CminorSel.listNthZ ttbl v = some n ∧ nexits[act]? = some n

/-- `RTLgenspec.tr_exitexpr` -/
inductive TrExitexpr (c : Code) : Mapping → Exitexpr → Node → List Node → Prop where
  | XEcond (map x n nexits) : nexits[x]? = some n → TrExitexpr c map (.XEexit x) n nexits
  | XEjumptable (map a tbl ns nexits n1 r tbl') : TrJumptable nexits tbl tbl' →
      TrExpr c map [] a ns n1 r none → c.get n1 = some (.Ijumptable r tbl') →
      TrExitexpr c map (.XEjumptable a tbl) ns nexits
  | XEcondition (map a1 a2 a3 ns nexits n2 n3) : TrCondition c map [] a1 ns n2 n3 →
      TrExitexpr c map a2 n2 nexits → TrExitexpr c map a3 n3 nexits →
      TrExitexpr c map (.XEcondition a1 a2 a3) ns nexits
  | XElet (map a b ns nexits r n1) : ¬ RegInMap map r → TrExpr c map [] a ns n1 r none →
      TrExitexpr c (addLetvar map r) b n1 nexits → TrExitexpr c map (.XElet a b) ns nexits

/-- `RTLgenspec.tr_builtin_res` -/
inductive TrBuiltinRes : Mapping → BuiltinRes Ident → BuiltinRes Reg → Prop where
  | var (map id r) : map.map_vars.get id = some r → TrBuiltinRes map (.BR id) (.BR r)
  | none (map) : TrBuiltinRes map .BR_none .BR_none
  | fresh (map r) : ¬ RegInMap map r → TrBuiltinRes map .BR_none (.BR r)

/-- `RTLgenspec.tr_stmt` -/
inductive TrStmt (c : Code) (map : Mapping) :
    CminorSel.Stmt → Node → Node → List Node → Labelmap → Node → Option Reg → Prop where
  | Sskip (ns nexits ngoto nret rret) : TrStmt c map .Sskip ns ns nexits ngoto nret rret
  | Sassign (id a ns nd nexits ngoto nret rret r) : map.map_vars.get id = some r →
      TrExpr c map [] a ns nd r (some id) →
      TrStmt c map (.Sassign id a) ns nd nexits ngoto nret rret
  | Sstore (chunk addr al b ns nd nexits ngoto nret rret rd n1 rl n2) :
      TrExprlist c map [] al ns n1 rl → TrExpr c map rl b n1 n2 rd none →
      c.get n2 = some (.Istore chunk addr rl rd nd) →
      TrStmt c map (.Sstore chunk addr al b) ns nd nexits ngoto nret rret
  | Scall (optid sig b cl ns nd nexits ngoto nret rret rd n1 rf n2 rargs) :
      TrExpr c map [] b ns n1 rf none → TrExprlist c map [rf] cl n1 n2 rargs →
      c.get n2 = some (.Icall sig (.inl rf) rargs rd nd) → RegMapOk map rd optid →
      TrStmt c map (.Scall optid sig (.inl b) cl) ns nd nexits ngoto nret rret
  | Scall_imm (optid sig id cl ns nd nexits ngoto nret rret rd n2 rargs) :
      TrExprlist c map [] cl ns n2 rargs →
      c.get n2 = some (.Icall sig (.inr id) rargs rd nd) → RegMapOk map rd optid →
      TrStmt c map (.Scall optid sig (.inr id) cl) ns nd nexits ngoto nret rret
  | Stailcall (sig b cl ns nd nexits ngoto nret rret n1 rf n2 rargs) :
      TrExpr c map [] b ns n1 rf none → TrExprlist c map [rf] cl n1 n2 rargs →
      c.get n2 = some (.Itailcall sig (.inl rf) rargs) →
      TrStmt c map (.Stailcall sig (.inl b) cl) ns nd nexits ngoto nret rret
  | Stailcall_imm (sig id cl ns nd nexits ngoto nret rret n2 rargs) :
      TrExprlist c map [] cl ns n2 rargs → c.get n2 = some (.Itailcall sig (.inr id) rargs) →
      TrStmt c map (.Stailcall sig (.inr id) cl) ns nd nexits ngoto nret rret
  | Sbuiltin (res ef args ns nd nexits ngoto nret rret res' n1 rargs) :
      TrExprlist c map [] (exprlistOfExprList (BuiltinArg.paramsList args)) ns n1 rargs →
      c.get n1 = some (.Ibuiltin ef (convertBuiltinArgs args rargs) res' nd) →
      TrBuiltinRes map res res' →
      TrStmt c map (.Sbuiltin res ef args) ns nd nexits ngoto nret rret
  | Sseq (s1 s2 ns nd nexits ngoto nret rret n) :
      TrStmt c map s2 n nd nexits ngoto nret rret → TrStmt c map s1 ns n nexits ngoto nret rret →
      TrStmt c map (.Sseq s1 s2) ns nd nexits ngoto nret rret
  | Sifthenelse (a strue sfalse ns nd nexits ngoto nret rret ntrue nfalse) :
      TrStmt c map strue ntrue nd nexits ngoto nret rret →
      TrStmt c map sfalse nfalse nd nexits ngoto nret rret →
      TrCondition c map [] a ns ntrue nfalse →
      TrStmt c map (.Sifthenelse a strue sfalse) ns nd nexits ngoto nret rret
  | Sloop (sbody ns nd nexits ngoto nret rret nloop nend) :
      TrStmt c map sbody nloop nend nexits ngoto nret rret →
      c.get ns = some (.Inop nloop) → c.get nend = some (.Inop nloop) →
      TrStmt c map (.Sloop sbody) ns nd nexits ngoto nret rret
  | Sblock (sbody ns nd nexits ngoto nret rret) :
      TrStmt c map sbody ns nd (nd :: nexits) ngoto nret rret →
      TrStmt c map (.Sblock sbody) ns nd nexits ngoto nret rret
  | Sexit (n ns nd nexits ngoto nret rret) : nexits[n]? = some ns →
      TrStmt c map (.Sexit n) ns nd nexits ngoto nret rret
  | Sswitch (a ns nd nexits ngoto nret rret) : TrExitexpr c map a ns nexits →
      TrStmt c map (.Sswitch a) ns nd nexits ngoto nret rret
  | Sreturn_none (nret nd nexits ngoto rret) :
      TrStmt c map (.Sreturn none) nret nd nexits ngoto nret rret
  | Sreturn_some (a ns nd nexits ngoto nret rret) : TrExpr c map [] a ns nret rret none →
      TrStmt c map (.Sreturn (some a)) ns nd nexits ngoto nret (some rret)
  | Slabel (lbl s ns nd nexits ngoto nret rret n) : ngoto.get lbl = some n →
      c.get n = some (.Inop ns) → TrStmt c map s ns nd nexits ngoto nret rret →
      TrStmt c map (.Slabel lbl s) ns nd nexits ngoto nret rret
  | Sgoto (lbl ns nd nexits ngoto nret rret) : ngoto.get lbl = some ns →
      TrStmt c map (.Sgoto lbl) ns nd nexits ngoto nret rret

/-- `RTLgenspec.tr_function` -/
inductive TrFunction : CminorSel.Function → RTL.Function → Prop where
  | intro (f code rparams map1 s0 s1 i1 rvars map2 s2 i2 nentry ngoto nret rret orret) :
      addVars initMapping f.fn_params s0 = .OK (rparams, map1) s1 i1 →
      addVars map1 f.fn_vars s1 = .OK (rvars, map2) s2 i2 →
      orret = retReg f.fn_sig rret →
      TrStmt code map2 f.fn_body nentry nret [] ngoto nret orret →
      code.get nret = some (.Ireturn orret) →
      TrFunction f { fn_sig := f.fn_sig, fn_params := rparams, fn_stacksize := f.fn_stackspace,
                     fn_code := code, fn_entrypoint := nentry }

/-! ## Monotonicity -/

/-- `RTLgenspec.tr_move_incr` -/
theorem tr_move_incr {s1 s2 : State} (hi : StateIncr s1 s2) {ns : Node} {rs : Reg} {nd : Node}
    {rd : Reg} (h : TrMove s1.st_code ns rs nd rd) : TrMove s2.st_code ns rs nd rd := by
  cases h with
  | zero => exact .zero _ _
  | one => rename_i h; exact .one _ _ _ _ (instr_at_incr hi h)

mutual
/-- `RTLgenspec.tr_expr_incr` -/
theorem tr_expr_incr {s1 s2 : State} (hi : StateIncr s1 s2) {map : Mapping} {pr : List Reg}
    {a : CminorSel.Expr} {ns nd : Node} {rd : Reg} {dst : Option Ident} :
    TrExpr s1.st_code map pr a ns nd rd dst → TrExpr s2.st_code map pr a ns nd rd dst
  | .Evar _ _ _ _ _ _ _ _ h1 h2 h3 => .Evar _ _ _ _ _ _ _ _ h1 h2 (tr_move_incr hi h3)
  | .Eop _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
      .Eop _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2) h3 h4
  | .Eload _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
      .Eload _ _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2) h3 h4
  | .Econdition _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Econdition _ _ _ _ _ _ _ _ _ _ _ (tr_condition_incr hi h1) (tr_expr_incr hi h2)
        (tr_expr_incr hi h3)
  | .Elet _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Elet _ _ _ _ _ _ _ _ _ _ h1 (tr_expr_incr hi h2) (tr_expr_incr hi h3)
  | .Eletvar _ _ _ _ _ _ _ _ h1 h2 h3 => .Eletvar _ _ _ _ _ _ _ _ h1 h2 (tr_move_incr hi h3)
  | .Ebuiltin _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
      .Ebuiltin _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2) h3 h4
  | .Eexternal _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
      .Eexternal _ _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2) h3 h4

/-- `RTLgenspec.tr_condition_incr` -/
theorem tr_condition_incr {s1 s2 : State} (hi : StateIncr s1 s2) {map : Mapping} {pr : List Reg}
    {a : Condexpr} {ns ntrue nfalse : Node} :
    TrCondition s1.st_code map pr a ns ntrue nfalse → TrCondition s2.st_code map pr a ns ntrue nfalse
  | .CEcond _ _ _ _ _ _ _ _ _ h1 h2 =>
      .CEcond _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2)
  | .CEcondition _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .CEcondition _ _ _ _ _ _ _ _ _ _ (tr_condition_incr hi h1) (tr_condition_incr hi h2)
        (tr_condition_incr hi h3)
  | .CElet _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .CElet _ _ _ _ _ _ _ _ _ h1 (tr_expr_incr hi h2) (tr_condition_incr hi h3)

/-- `RTLgenspec.tr_exprlist_incr` -/
theorem tr_exprlist_incr {s1 s2 : State} (hi : StateIncr s1 s2) {map : Mapping} {pr : List Reg}
    {al : Exprlist} {ns nd : Node} {rl : List Reg} :
    TrExprlist s1.st_code map pr al ns nd rl → TrExprlist s2.st_code map pr al ns nd rl
  | .Enil _ _ _ => .Enil _ _ _
  | .Econs _ _ _ _ _ _ _ _ _ h1 h2 =>
      .Econs _ _ _ _ _ _ _ _ _ (tr_expr_incr hi h1) (tr_exprlist_incr hi h2)
end

/-- `RTLgenspec.add_move_charact` -/
theorem add_move_charact {s s' : State} {ns : Node} {rs : Reg} {nd : Node} {rd : Reg}
    {i : StateIncr s s'} (h : addMove rs rd nd s = .OK ns s' i) :
    TrMove s'.st_code ns rs nd rd := by
  unfold addMove at h
  split at h
  · next he => cases h; subst he; exact .zero _ _
  · exact .one _ _ _ _ (add_instr_at h)

end RTLgen
end CC
