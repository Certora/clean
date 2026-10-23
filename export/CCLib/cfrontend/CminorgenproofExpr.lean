/-
  Correctness of Cminor generation — port of `cfrontend/Cminorgenproof.v`,
  part 3: compatibility of the evaluation of operators with memory
  injections (`eval_unop_compat`, `eval_binop_compat`), correctness of the
  variable accessor `var_addr` (`var_addr_correct`) and semantic
  preservation for expressions (`transl_constant_correct`,
  `transl_expr_correct`, `transl_exprlist_correct`).
-/
import CCLib.cfrontend.CminorgenproofAlloc
import CCLib.aarch64.OpInject

namespace CC
namespace Cminorgen

open Smallstep

/-! ## Compatibility of evaluation functions with memory injections -/

/-- `Cminorgenproof.eval_unop_compat` -/
theorem eval_unop_compat {f : Val.Meminj} {op : Cminor.UnaryOperation} {v1 tv1 v : Val}
    (h : Cminor.evalUnop op v1 = some v) (hv : Val.Inject f v1 tv1) :
    ∃ tv, Cminor.evalUnop op tv1 = some tv ∧ Val.Inject f v tv := by
  cases hv <;> cases op <;> simp [Cminor.evalUnop, Val.zeroExt, Val.signExt, Val.negint, Val.notint, Val.negf, Val.absf, Val.negfs, Val.absfs, Val.singleoffloat, Val.floatofsingle, Val.intoffloat, Val.intuoffloat, Val.floatofint, Val.floatofintu, Val.intofsingle, Val.intuofsingle, Val.singleofint, Val.singleofintu, Val.negl, Val.notl, Val.loword, Val.longofint, Val.longofintu, Val.longoffloat, Val.longuoffloat, Val.floatoflong, Val.floatoflongu, Val.longofsingle, Val.longuofsingle, Val.singleoflong, Val.singleoflongu] at h ⊢ <;> (try subst h) <;> (try exact .undef _) <;> (try first | exact .int _ | exact .long _ | exact .float _ | exact .single _) <;> (obtain ⟨a, h1, rfl⟩ := h; first | exact ⟨_, ⟨a, h1, rfl⟩, .int _⟩ | exact ⟨_, ⟨a, h1, rfl⟩, .long _⟩)

/-- `Cminorgenproof.eval_binop_compat` -/
theorem eval_binop_compat {f : Val.Meminj} {op : Cminor.BinaryOperation} {v1 tv1 v2 tv2 v : Val}
    {m tm : Mem} (h : Cminor.evalBinop op v1 v2 m = some v) (hv1 : Val.Inject f v1 tv1)
    (hv2 : Val.Inject f v2 tv2) (hm : Mem.Inject f m tm) :
    ∃ tv, Cminor.evalBinop op tv1 tv2 tm = some tv ∧ Val.Inject f v tv := by
  cases op
  case Oadd => simp only [Cminor.evalBinop, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, Val.add_inject hv1 hv2⟩
  case Osub => simp only [Cminor.evalBinop, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, Val.sub_inject hv1 hv2⟩
  case Oaddl => simp only [Cminor.evalBinop, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, Op.addl_inject hv1 hv2⟩
  case Osubl => simp only [Cminor.evalBinop, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, Op.subl_inject hv1 hv2⟩
  case Ocmplu c =>
    simp only [Cminor.evalBinop] at h ⊢
    simp only [Val.cmplu, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    refine ⟨Val.ofBool b, ?_, ?_⟩
    · simp only [Val.cmplu]; rw [Cop.cmplu_bool_inject (Cop.copInjHyps_of_inject hm) hv1 hv2 hb]; rfl
    · cases b <;> exact .int _
  case Ocmpu c =>
    simp only [Cminor.evalBinop, Option.some.injEq] at h ⊢
    subst h
    refine ⟨_, rfl, ?_⟩
    simp only [Val.cmpu]
    cases hb : Val.cmpu_bool (Mem.validPointer m) c v1 v2 with
    | none => simp [Val.ofOptbool]; exact .undef _
    | some b =>
      rw [Val.cmpu_bool_inject (Cop.copInjHyps_of_inject hm) hv1 hv2 hb]
      cases b <;> exact .int _
  all_goals cases hv1 <;> cases hv2 <;> simp [Cminor.evalBinop, Val.mul, Val.divs, Val.divu, Val.mods, Val.modu, Val.and, Val.or, Val.xor, Val.shl, Val.shr, Val.shru, Val.addf, Val.subf, Val.mulf, Val.divf, Val.addfs, Val.subfs, Val.mulfs, Val.divfs, Val.mull, Val.divls, Val.divlu, Val.modls, Val.modlu, Val.andl, Val.orl, Val.xorl, Val.shll, Val.shrl, Val.shrlu, Val.cmp, Val.cmpf, Val.cmpfs, Val.cmpl, Val.cmp_bool, Val.cmpf_bool, Val.cmpfs_bool, Val.cmpl_bool, Val.ofOptbool, Val.ofBool] at h ⊢ <;> (try subst h) <;> (try exact .undef _) <;> (try first | exact .int _ | exact .long _ | exact .float _ | exact .single _) <;> (try (obtain ⟨h1, rfl⟩ := h; exact ⟨_, ⟨h1, rfl⟩, by first | exact .int _ | exact .long _⟩)) <;> (try (split <;> first | exact .int _ | exact .long _ | exact .undef _))

/-- `Cminorgenproof.bool_of_val_inject` -/
theorem bool_of_val_inject {f : Val.Meminj} {v tv : Val} {b : Bool} (h : Val.BoolOfVal v b)
    (hi : Val.Inject f v tv) : Val.BoolOfVal tv b := by
  cases h; cases hi; exact .int _

/-! ## Correctness of Cminor construction functions -/

section TRANSLATION
variable {prog : Csharpminor.Program} {tprog : Cminor.Program}
  (TRANSL : translProgram prog = .OK tprog)
include TRANSL

/-- `Cminorgenproof.var_addr_correct` -/
theorem var_addr_correct {cenv : Compilenv} {id : Ident} {f : Val.Meminj} {tf : Cminor.Function}
    {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {te : Cminor.Env} {sp lo hi : Block}
    {m : Mem} {cs : Callstack} {tm : Mem} {b : Block}
    (MCS : MatchCallstack prog.globalenv f m tm (⟨cenv, tf, e, le, te, sp, lo, hi⟩ :: cs)
      m.nextblock tm.nextblock)
    (EV : Csharpminor.EvalVarAddr prog.globalenv e id b) :
    ∃ tv, Cminor.EvalExpr tprog.globalenv (.Vptr sp Integers.Ptrofs.zero) te tm (varAddr cenv id) tv ∧
      Val.Inject f (.Vptr b Integers.Ptrofs.zero) tv := by
  have MV : MatchVar f sp (e.get id) (cenv.get id) := by
    cases MCS with
    | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ MENV _ _ _ => exact MENV.me_vars id
  cases EV with
  | «local» sz he =>
    rw [he] at MV
    revert MV
    unfold varAddr
    generalize cenv.get id = y
    intro MV
    cases MV with
    | «local» _ _ ofs hi =>
      refine ⟨_, .Econst _ _ rfl, ?_⟩
      simp only [Val.offsetPtr, Integers.Ptrofs.add_zero_l]
      exact hi
  | global he hs =>
    rw [he] at MV
    revert MV
    unfold varAddr
    generalize cenv.get id = y
    intro MV
    cases MV with
    | global =>
      obtain ⟨bnd, MG⟩ := match_callstack_match_globalenvs MCS
      refine ⟨_, .Econst _ _ rfl, ?_⟩
      simp only [Genv.symbolAddress, symbols_preserved TRANSL, hs]
      exact .ptr 0 (MG.domain b (MG.symbols id b hs)) (EventsInject.ptrofs_add_repr_zero _).symm

omit TRANSL in
/-- `Cminorgenproof.transl_constant_correct` -/
theorem transl_constant_correct {f : Val.Meminj} {sp : Val} {cst : Csharpminor.Constant} {v : Val}
    (h : Csharpminor.evalConstant cst = some v) :
    ∃ tv, Cminor.evalConstant tprog.globalenv sp (translConstant cst) = some tv ∧ Val.Inject f v tv := by
  cases cst <;> simp only [Csharpminor.evalConstant, Option.some.injEq] at h <;> subst h
  · exact ⟨_, rfl, .int _⟩
  · exact ⟨_, rfl, .float _⟩
  · exact ⟨_, rfl, .single _⟩
  · exact ⟨_, rfl, .long _⟩

/-- `Cminorgenproof.transl_expr_correct` -/
theorem transl_expr_correct {f : Val.Meminj} {m tm : Mem} {cenv : Compilenv} {tf : Cminor.Function}
    {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {te : Cminor.Env} {sp lo hi : Block}
    {cs : Callstack} (MINJ : Mem.Inject f m tm)
    (MATCH : MatchCallstack prog.globalenv f m tm (⟨cenv, tf, e, le, te, sp, lo, hi⟩ :: cs)
      m.nextblock tm.nextblock)
    {a : Csharpminor.Expr} {v : Val} (EV : Csharpminor.EvalExpr prog.globalenv e le m a v) :
    ∀ {ta}, translExpr cenv a = .OK ta →
    ∃ tv, Cminor.EvalExpr tprog.globalenv (.Vptr sp Integers.Ptrofs.zero) te tm ta tv ∧
      Val.Inject f v tv := by
  induction EV with
  | Evar id v hv =>
    intro ta TR
    simp only [translExpr] at TR; cases TR
    cases MATCH with
    | cons _ _ _ _ _ _ _ _ _ _ _ _ _ MTMP _ _ _ _ =>
      obtain ⟨tv, A, B⟩ := MTMP id v hv
      exact ⟨tv, .Evar _ _ A, B⟩
  | Eaddrof id b hb =>
    intro ta TR
    simp only [translExpr] at TR; cases TR
    exact var_addr_correct TRANSL MATCH hb
  | Econst cst v hc =>
    intro ta TR
    simp only [translExpr] at TR; cases TR
    obtain ⟨tv, A, B⟩ := transl_constant_correct (tprog := tprog) (f := f)
      (sp := .Vptr sp Integers.Ptrofs.zero) hc
    exact ⟨tv, .Econst _ _ A, B⟩
  | Eunop op a1 v1 v _ hu ih =>
    intro ta TR
    simp only [translExpr, Cshmgen.res_bind_eq_OK] at TR
    obtain ⟨ta1, h1, h⟩ := TR; cases h
    obtain ⟨tv1, A, B⟩ := ih h1
    obtain ⟨tv, C, D⟩ := eval_unop_compat hu B
    exact ⟨tv, .Eunop _ _ _ _ A C, D⟩
  | Ebinop op a1 a2 v1 v2 v _ _ hb ih1 ih2 =>
    intro ta TR
    simp only [translExpr, Cshmgen.res_bind_eq_OK] at TR
    obtain ⟨ta1, h1, ta2, h2, h⟩ := TR; cases h
    obtain ⟨tv1, A, B⟩ := ih1 h1
    obtain ⟨tv2, A2, B2⟩ := ih2 h2
    obtain ⟨tv, C, D⟩ := eval_binop_compat hb B B2 MINJ
    exact ⟨tv, .Ebinop _ _ _ _ _ _ A A2 C, D⟩
  | Eload chunk a v1 v _ hl ih =>
    intro ta TR
    simp only [translExpr, Cshmgen.res_bind_eq_OK] at TR
    obtain ⟨ta1, h1, h⟩ := TR; cases h
    obtain ⟨tv1, A, B⟩ := ih h1
    obtain ⟨tv, C, D⟩ := Mem.loadv_inject MINJ hl B
    exact ⟨tv, .Eload _ _ _ _ A C, D⟩

/-- `Cminorgenproof.transl_exprlist_correct` -/
theorem transl_exprlist_correct {f : Val.Meminj} {m tm : Mem} {cenv : Compilenv}
    {tf : Cminor.Function} {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {te : Cminor.Env}
    {sp lo hi : Block} {cs : Callstack} (MINJ : Mem.Inject f m tm)
    (MATCH : MatchCallstack prog.globalenv f m tm (⟨cenv, tf, e, le, te, sp, lo, hi⟩ :: cs)
      m.nextblock tm.nextblock)
    {al : List Csharpminor.Expr} {vl : List Val}
    (EV : Csharpminor.EvalExprlist prog.globalenv e le m al vl) :
    ∀ {tal}, translExprlist cenv al = .OK tal →
    ∃ tvl, Cminor.EvalExprlist tprog.globalenv (.Vptr sp Integers.Ptrofs.zero) te tm tal tvl ∧
      Val.InjectList f vl tvl := by
  induction EV with
  | nil => intro tal TR; simp only [translExprlist] at TR; cases TR; exact ⟨[], .nil, .nil⟩
  | cons a1 al v1 vl h1 _ ih =>
    intro tal TR
    simp only [translExprlist, Cshmgen.res_bind_eq_OK] at TR
    obtain ⟨ta1, t1, tal', t2, h⟩ := TR; cases h
    obtain ⟨tv1, A, B⟩ := transl_expr_correct TRANSL MINJ MATCH h1 t1
    obtain ⟨tvl, C, D⟩ := ih t2
    exact ⟨tv1 :: tvl, .cons _ _ _ _ A C, .cons B D⟩

end TRANSLATION

end Cminorgen
end CC
