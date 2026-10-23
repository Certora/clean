/-
  Correctness of instruction selection — port of `backend/Selectionproof.v`,
  part 1 (`Section CMCONSTR`): `eval_condexpr_of_expr`,
  `eval_condition_of_expr`, `eval_load`, `eval_store`, `eval_sel_unop`,
  `eval_sel_binop`, `eval_sel_select`, `eval_sel_known_builtin`, together with
  `SelectDivproof.eval_divf` / `eval_divfs`.

  Differences from Rocq: the section variables `prog`, `tprog`, `cunit`, `hf`
  are not needed for these lemmas, which hold for an arbitrary CminorSel global
  environment `ge` (Rocq states them for `tge`). `eval_divf` / `eval_divfs`
  use `Float.div_mul_inverse` / `Float32.div_mul_inverse` from
  `CCLib.lib.FloatsArith`.
-/
import CCLib.backend.Selection
import CCLib.aarch64.SelectOpproof3
import CCLib.backend.SelectDivproof2
import CCLib.common.ValuesInject

namespace CC
namespace Selectionproof

open Op CminorSel SelectOp Selection Builtins

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

theorem evalOperation_Ocmp (ge : CminorSel.CGenv) (sp : Val) (c : Condition) (vl : List Val)
    (m : Mem) : evalOperation ge sp (.Ocmp c) vl m = some (Val.ofOptbool (evalCondition c vl m)) := by
  rfl

theorem negint_eq_sub (v : Val) : Val.negint v = Val.sub Val.Vzero v := by
  cases v <;> simp [Val.negint, Val.sub, Val.Vzero, Integers.Int.sub_zero_l]

theorem negl_eq_subl (v : Val) : Val.negl v = Val.subl (.Vlong Integers.Int64.zero) v := by
  cases v <;> simp [Val.negl, Val.subl, Integers.Int64.sub_zero_l]

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-- `Selectionproof.eval_condexpr_of_expr` -/
theorem eval_condexpr_of_expr (a : CminorSel.Expr) :
    ∀ {le : Letenv} {v : Val} {b : Bool},
    CminorSel.EvalExpr ge sp e m le a v → Val.BoolOfVal v b →
    CminorSel.EvalCondexpr ge sp e m le (condexprOfExpr a) b := by
  induction a using condexprOfExpr.induct with
  | case1 c el =>
    intro le v b ha hb
    cases ha with
    | Eop _ _ _ vl _ hl ho =>
      rw [evalOperation_Ocmp] at ho
      cases ho
      exact .CEcond _ _ _ _ _ hl (Val.bool_of_val_of_optbool hb)
  | case2 a b c ihb ihc =>
    intro le v bb ha hb
    cases ha with
    | Econdition _ _ _ _ va _ hc hv =>
      refine .CEcondition _ _ _ _ va _ hc ?_
      cases va
      · exact ihc hv hb
      · exact ihb hv hb
  | case3 a b ih =>
    intro le v bb ha hb
    cases ha with
    | Elet _ _ _ v1 _ h1 h2 => exact .CElet _ _ _ v1 _ h1 (ih h2 hb)
  | case4 e' h1 h2 h3 =>
    intro le v b ha hb
    rw [condexprOfExpr.eq_4 e' h1 h2 h3]
    refine .CEcond _ _ _ [v] _ (.Econs _ _ _ _ _ ha (.Enil _)) ?_
    cases hb
    rfl

/-- `Selectionproof.eval_condition_of_expr` -/
theorem eval_condition_of_expr {le : Letenv} {a : CminorSel.Expr} {v : Val} {b : Bool}
    (ha : CminorSel.EvalExpr ge sp e m le a v) (hb : Val.BoolOfVal v b) :
    ∃ vl, CminorSel.EvalExprlist ge sp e m le (conditionOfExpr a).2 vl ∧
      evalCondition (conditionOfExpr a).1 vl m = some b := by
  unfold conditionOfExpr
  split
  · cases ha with
    | Eop _ _ _ vl _ hl ho =>
      rw [evalOperation_Ocmp] at ho
      cases ho
      exact ⟨vl, hl, Val.bool_of_val_of_optbool hb⟩
  · refine ⟨[v], .Econs _ _ _ _ _ ha (.Enil _), ?_⟩
    cases hb
    rfl

/-- `Selectionproof.eval_load` -/
theorem eval_load (opts : Options) {le : Letenv} {a : CminorSel.Expr} {v v' : Val} {chunk : Chunk}
    (ha : CminorSel.EvalExpr ge sp e m le a v) (hl : Mem.loadv chunk m v = some v') :
    CminorSel.EvalExpr ge sp e m le (load opts chunk a) v' := by
  cases v with
  | Vptr b ofs =>
    obtain ⟨vl, hvl, hev⟩ := SelectOpproof.eval_addressing opts.symbolIsRelocatable chunk ha rfl
    unfold load
    exact .Eload _ _ _ _ vl _ _ hvl hev hl
  | _ => simp [Mem.loadv] at hl

/-- `Selectionproof.eval_store` -/
theorem eval_store (opts : Options) {chunk : Chunk} {a1 a2 : CminorSel.Expr} {v1 v2 : Val}
    {f : CminorSel.Function} {k : CminorSel.Cont} {m' : Mem}
    (h1 : CminorSel.EvalExpr ge sp e m [] a1 v1) (h2 : CminorSel.EvalExpr ge sp e m [] a2 v2)
    (hs : Mem.storev chunk m v1 v2 = some m') :
    CminorSel.Step ge (.State f (store opts chunk a1 a2) k sp e m) E0 (.State f .Sskip k sp e m') := by
  cases v1 with
  | Vptr b ofs =>
    obtain ⟨vl, hvl, hev⟩ := SelectOpproof.eval_addressing opts.symbolIsRelocatable chunk h1 rfl
    unfold store
    exact .store _ _ _ _ _ _ _ _ _ vl _ _ _ hvl h2 hev hs
  | _ => simp [Mem.storev] at hs

open SelectOpproof SelectLongproof SelectDivproof in
/-- `Selectionproof.eval_sel_unop` -/
theorem eval_sel_unop {le : Letenv} {op : Cminor.UnaryOperation} {a1 : CminorSel.Expr} {v1 v : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a1 v1) (hv : Cminor.evalUnop op v1 = some v) :
    ∃ v', CminorSel.EvalExpr ge sp e m le (selUnop op a1) v' ∧ Val.Lessdef v v' := by
  cases op
  case Ocast8unsigned => cases hv; exact eval_cast8unsigned _ _ _ ha
  case Ocast8signed => cases hv; exact eval_cast8signed _ _ _ ha
  case Ocast16unsigned => cases hv; exact eval_cast16unsigned _ _ _ ha
  case Ocast16signed => cases hv; exact eval_cast16signed _ _ _ ha
  case Onotint => cases hv; exact eval_notint _ _ _ ha
  case Onegf => cases hv; exact eval_negf _ _ _ ha
  case Oabsf => cases hv; exact eval_absf _ _ _ ha
  case Onegfs => cases hv; exact eval_negfs _ _ _ ha
  case Oabsfs => cases hv; exact eval_absfs _ _ _ ha
  case Osingleoffloat => cases hv; exact eval_singleoffloat _ _ _ ha
  case Ofloatofsingle => cases hv; exact eval_floatofsingle _ _ _ ha
  case Onotl => cases hv; exact eval_notl _ _ _ ha
  case Ointoflong => cases hv; exact eval_intoflong _ _ _ ha
  case Olongofint => cases hv; exact eval_longofint _ _ _ ha
  case Olongofintu => cases hv; exact eval_longofintu _ _ _ ha
  case Ointoffloat => exact eval_intoffloat ha hv
  case Ointuoffloat => exact eval_intuoffloat ha hv
  case Ofloatofint => exact eval_floatofint ha hv
  case Ofloatofintu => exact eval_floatofintu ha hv
  case Ointofsingle => exact eval_intofsingle ha hv
  case Ointuofsingle => exact eval_intuofsingle ha hv
  case Osingleofint => exact eval_singleofint ha hv
  case Osingleofintu => exact eval_singleofintu ha hv
  case Olongoffloat => exact eval_longoffloat _ _ _ _ ha hv
  case Olonguoffloat => exact eval_longuoffloat _ _ _ _ ha hv
  case Ofloatoflong => exact eval_floatoflong _ _ _ _ ha hv
  case Ofloatoflongu => exact eval_floatoflongu _ _ _ _ ha hv
  case Olongofsingle => exact eval_longofsingle _ _ _ _ ha hv
  case Olonguofsingle => exact eval_longuofsingle _ _ _ _ ha hv
  case Osingleoflong => exact eval_singleoflong _ _ _ _ ha hv
  case Osingleoflongu => exact eval_singleoflongu _ _ _ _ ha hv
  case Onegint =>
    cases hv
    obtain ⟨v', h, hl⟩ := eval_negint _ _ _ ha
    exact ⟨v', h, by rw [negint_eq_sub]; exact hl⟩
  case Onegl =>
    cases hv
    obtain ⟨v', h, hl⟩ := eval_negl _ _ _ ha
    exact ⟨v', h, by rw [negl_eq_subl]; exact hl⟩

open SelectOpproof in
/-- `SelectDivproof.eval_divf` -/
theorem eval_divf : BinarySound ge sp e m SelectDiv.divf Val.divf := by
  intro le a x b y hx hy
  unfold SelectDiv.divf
  split
  · next n2 =>
    unfold SelectDiv.divfimm
    split
    · next n2' hinv =>
      have h0 : some (Val.Vfloat n2) = some y := inv_op0 hy
      cases h0
      refine ⟨_, eval_op2 hx (eval_op0 (op := .Ofloatconst n2') rfl) rfl, ?_⟩
      cases x <;> simp only [Val.divf, Val.mulf, Floats.Float.div_mul_inverse _ _ _ hinv] <;> exact .refl _
    · exact ⟨_, eval_op2 hx hy rfl, .refl _⟩
  · exact ⟨_, eval_op2 hx hy rfl, .refl _⟩

open SelectOpproof in
/-- `SelectDivproof.eval_divfs` -/
theorem eval_divfs : BinarySound ge sp e m SelectDiv.divfs Val.divfs := by
  intro le a x b y hx hy
  unfold SelectDiv.divfs
  split
  · next n2 =>
    unfold SelectDiv.divfsimm
    split
    · next n2' hinv =>
      have h0 : some (Val.Vsingle n2) = some y := inv_op0 hy
      cases h0
      refine ⟨_, eval_op2 hx (eval_op0 (op := .Osingleconst n2') rfl) rfl, ?_⟩
      cases x <;> simp only [Val.divfs, Val.mulfs, Floats.Float32.div_mul_inverse _ _ _ hinv] <;> exact .refl _
    · exact ⟨_, eval_op2 hx hy rfl, .refl _⟩
  · exact ⟨_, eval_op2 hx hy rfl, .refl _⟩

open SelectOpproof SelectLongproof SelectDivproof in
/-- `Selectionproof.eval_sel_binop` -/
theorem eval_sel_binop (opts : Options)
    {le : Letenv} {op : Cminor.BinaryOperation} {a1 a2 : CminorSel.Expr} {v1 v2 v : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a1 v1) (hb : CminorSel.EvalExpr ge sp e m le a2 v2)
    (hv : Cminor.evalBinop op v1 v2 m = some v) :
    ∃ v', CminorSel.EvalExpr ge sp e m le (selBinop opts op a1 a2) v' ∧ Val.Lessdef v v' := by
  cases op
  case Oadd => cases hv; exact eval_add _ _ _ _ _ ha hb
  case Osub => cases hv; exact eval_sub _ _ _ _ _ ha hb
  case Omul => cases hv; exact eval_mul _ _ _ _ _ ha hb
  case Oand => cases hv; exact eval_and _ _ _ _ _ ha hb
  case Oor => cases hv; exact eval_or _ _ _ _ _ ha hb
  case Oxor => cases hv; exact eval_xor _ _ _ _ _ ha hb
  case Oshl => cases hv; exact eval_shl _ _ _ _ _ ha hb
  case Oshr => cases hv; exact eval_shr _ _ _ _ _ ha hb
  case Oshru => cases hv; exact eval_shru _ _ _ _ _ ha hb
  case Oaddf => cases hv; exact eval_addf _ _ _ _ _ ha hb
  case Osubf => cases hv; exact eval_subf _ _ _ _ _ ha hb
  case Omulf => cases hv; exact eval_mulf _ _ _ _ _ ha hb
  case Oaddfs => cases hv; exact eval_addfs _ _ _ _ _ ha hb
  case Osubfs => cases hv; exact eval_subfs _ _ _ _ _ ha hb
  case Omulfs => cases hv; exact eval_mulfs _ _ _ _ _ ha hb
  case Oaddl => cases hv; exact eval_addl _ _ _ _ _ ha hb
  case Osubl => cases hv; exact eval_subl _ _ _ _ _ ha hb
  case Omull => cases hv; exact eval_mull _ _ _ _ _ ha hb
  case Oandl => cases hv; exact eval_andl _ _ _ _ _ ha hb
  case Oorl => cases hv; exact eval_orl _ _ _ _ _ ha hb
  case Oxorl => cases hv; exact eval_xorl _ _ _ _ _ ha hb
  case Oshll => cases hv; exact eval_shll _ _ _ _ _ ha hb
  case Oshrl => cases hv; exact eval_shrl _ _ _ _ _ ha hb
  case Oshrlu => cases hv; exact eval_shrlu _ _ _ _ _ ha hb
  case Odiv => exact eval_divs _ ha hb hv
  case Odivu => exact eval_divu _ ha hb hv
  case Omod => exact eval_mods _ ha hb hv
  case Omodu => exact eval_modu _ ha hb hv
  case Odivl => exact eval_divls _ ha hb hv
  case Odivlu => exact eval_divlu _ ha hb hv
  case Omodl => exact eval_modls _ ha hb hv
  case Omodlu => exact eval_modlu _ ha hb hv
  case Odivf => cases hv; exact eval_divf _ _ _ _ _ ha hb
  case Odivfs => cases hv; exact eval_divfs _ _ _ _ _ ha hb
  case Ocmp c => cases hv; exact eval_comp c _ _ _ _ _ ha hb
  case Ocmpu c => cases hv; exact eval_compu c _ _ _ _ _ ha hb
  case Ocmpf c => cases hv; exact eval_compf c _ _ _ _ _ ha hb
  case Ocmpfs c => cases hv; exact eval_compfs c _ _ _ _ _ ha hb
  case Ocmpl c => exact ⟨v, eval_cmpl c ha hb hv, .refl _⟩
  case Ocmplu c => exact ⟨v, eval_cmplu c ha hb hv, .refl _⟩

/-- `Selectionproof.eval_sel_select` -/
theorem eval_sel_select (ty : ATyp) {le : Letenv} {a1 a2 a3 : CminorSel.Expr} {v1 v2 v3 : Val}
    {b : Bool} (h1 : CminorSel.EvalExpr ge sp e m le a1 v1)
    (h2 : CminorSel.EvalExpr ge sp e m le a2 v2) (h3 : CminorSel.EvalExpr ge sp e m le a3 v3)
    (hb : Val.BoolOfVal v1 b) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (selSelect ty a1 a2 a3) v ∧
      Val.Lessdef (Val.select (some b) v2 v3 ty) v := by
  obtain ⟨vl, hl, hc⟩ := eval_condition_of_expr h1 hb
  unfold selSelect
  rcases hce : conditionOfExpr a1 with ⟨cond, args⟩
  rw [hce] at hl hc
  dsimp only
  split
  · have := SelectOpproof.eval_select ty cond hl h2 h3
    rwa [hc] at this
  · refine ⟨if b then v2 else v3,
      .Econdition _ _ _ _ b _ (eval_condexpr_of_expr a1 h1 hb) ?_, Val.lessdef_normalize _ _⟩
    cases b
    · exact h3
    · exact h2

/-- `Selectionproof.eval_sel_known_builtin` -/
theorem eval_sel_known_builtin {bf : BuiltinFunction} {args : CminorSel.Exprlist}
    {a : CminorSel.Expr} {vl : List Val} {v : Val} {le : Letenv}
    (hsel : selKnownBuiltin bf args = some a) (hargs : CminorSel.EvalExprlist ge sp e m le args vl)
    (hsem : (builtinFunctionSem bf).sem vl = some v) :
    ∃ v', CminorSel.EvalExpr ge sp e m le a v' ∧ Val.Lessdef v v' := by
  unfold selKnownBuiltin at hsel
  split at hsel
  · exact SelectOpproof.eval_platform_builtin _ _ _ hsel v
  · next ty a1 a2 a3 =>
    cases hsel
    cases hargs with | Econs _ _ _ x1 _ h1 hargs =>
    cases hargs with | Econs _ _ _ x2 _ h2 hargs =>
    cases hargs with | Econs _ _ _ x3 _ h3 hargs =>
    cases hargs
    cases x1 with
    | Vint n =>
      have hv : some (Val.normalize (if Integers.Int.eq n Integers.Int.zero then x3 else x2) ty)
          = some v := hsem
      cases hv
      have := eval_sel_select ty h1 h2 h3 (Val.BoolOfVal.int n)
      revert this
      cases Integers.Int.eq n Integers.Int.zero <;> exact id
    | _ => cases hsem
  · next a1 =>
    cases hsel
    cases hargs with | Econs _ _ _ x1 _ h1 hargs =>
    cases hargs
    cases x1 with
    | Vfloat f =>
      have hv : some (Val.Vfloat (Floats.Float.abs f)) = some v := hsem
      cases hv
      exact SelectOpproof.eval_absf _ _ _ h1
    | _ =>
      cases hsem
      obtain ⟨w, hw, _⟩ := SelectOpproof.eval_absf _ _ _ h1
      exact ⟨w, hw, .undef _⟩
  · next a1 =>
    cases hsel
    cases hargs with | Econs _ _ _ x1 _ h1 hargs =>
    cases hargs
    cases x1 with
    | Vsingle f =>
      have hv : some (Val.Vsingle (Floats.Float32.abs f)) = some v := hsem
      cases hv
      exact SelectOpproof.eval_absfs _ _ _ h1
    | _ =>
      cases hsem
      obtain ⟨w, hw, _⟩ := SelectOpproof.eval_absfs _ _ _ h1
      exact ⟨w, hw, .undef _⟩
  · cases hsel

end CMCONSTR

end Selectionproof
end CC
