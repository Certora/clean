/-
  Pulling local scalar variables into temporaries: semantic preservation —
  port of `cfrontend/SimplLocalsproof.v`, part 3: matching of global
  environments (`match_globalenvs`) and correctness of the rewriting of
  expressions (`deref_loc_inject`, `eval_simpl_expr`, `eval_simpl_lvalue`,
  `eval_simpl_exprlist`).
-/
import CCLib.cfrontend.SimplLocalsproofAlloc
import CCLib.cfrontend.CopInject
import CCLib.lib.IntegersPtrofs

namespace CC
namespace SimplLocals

open Smallstep

/-! ## Matching global environments -/

/-- `SimplLocalsproof.match_globalenvs` -/
structure MatchGlobalenvs (ge : Genv FunDef Ty) (f : Val.Meminj) (bound : Block) : Prop where
  domain : ∀ b, b < bound → f b = some (b, 0)
  image : ∀ b1 b2 delta, f b1 = some (b2, delta) → b2 < bound → b1 = b2
  symbols : ∀ id b, Genv.findSymbol ge id = some b → b < bound
  functions : ∀ b fd, Genv.findFunctPtr ge b = some fd → b < bound
  varinfos : ∀ b gv, Genv.findVarInfo ge b = some gv → b < bound

/-- From `match_globalenvs`, the injection relates the symbol environment of
    the source program to that of the target program (which are equal). -/
theorem match_globalenvs_symbols_inject {ge : Genv FunDef Ty} {f : Val.Meminj} {bound : Block}
    (MG : MatchGlobalenvs ge f bound) {sge : Senv} (hs : sge = Genv.toSenv ge) :
    SymbolsInject f (Genv.toSenv ge) sge := by
  subst hs
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro id b1 b2 delta hf hfs
    rw [MG.domain b1 (MG.symbols id b1 hfs)] at hf
    cases hf
    exact ⟨rfl, hfs⟩
  · intro id b1 _ hfs
    exact ⟨b1, MG.domain b1 (MG.symbols id b1 hfs), hfs⟩
  · intro b1 b2 delta hf
    show Genv.blockIsVolatile ge b2 = Genv.blockIsVolatile ge b1
    by_cases hb1 : b1 < bound
    · rw [MG.domain b1 hb1] at hf; cases hf; rfl
    · by_cases hb2 : b2 < bound
      · rw [MG.image b1 b2 delta hf hb2]
      · have none_of : ∀ b, ¬ b < bound → Genv.blockIsVolatile ge b = false := by
          intro b hb
          unfold Genv.blockIsVolatile
          cases hv : Genv.findVarInfo ge b with
          | none => rfl
          | some gv => exact absurd (MG.varinfos b gv hv) hb
        rw [none_of b1 hb1, none_of b2 hb2]

/-! ## Evaluation of expressions -/

/-- `SimplLocalsproof.typeof_simpl_expr` -/
theorem typeof_simpl_expr (cenv : Compilenv) (a : Expr) : typeof (simplExpr cenv a) = typeof a := by
  cases a with
  | Evar id t => unfold simplExpr; split <;> rfl
  | _ => rfl

/-- The side condition of `eval_simpl_lvalue`: `a` is not a lifted variable. -/
def NotLiftedVar (cenv : Compilenv) : Expr → Prop
  | .Evar id _ => VSet.mem id cenv = false
  | _ => True

theorem compat_addrof {cenv : Compilenv} {a : Expr} {t : Ty}
    (h : CompatCenv (addrTakenExpr (.Eaddrof a t)) cenv) :
    CompatCenv (addrTakenExpr a) cenv ∧
      NotLiftedVar cenv a := by
  cases a with
  | Evar id ty =>
    refine ⟨fun _ h1 _ => by simp [addrTakenExpr, VSet.mem_empty] at h1, ?_⟩
    show VSet.mem id cenv = false
    cases hm : VSet.mem id cenv with
    | false => rfl
    | true => exact (h id (by simp [addrTakenExpr, VSet.mem_singleton]) hm).elim
  | _ => exact ⟨h, trivial⟩

section EVAL_EXPR

variable {ge tge : CGenv} (hce : tge.genv_cenv = ge.genv_cenv)
  (hsym : ∀ s, Genv.findSymbol tge.genv_genv s = Genv.findSymbol ge.genv_genv s)
  {e te : Env} {le tle : TempEnv} {m tm : Mem} {f : Val.Meminj} {cenv : Compilenv}
  {lo hi tlo thi : Block}
  (MATCH : MatchEnvs f cenv e le m lo hi te tle tlo thi)
  (MEMINJ : Mem.Inject f m tm)
  (GLOB : ∃ bound, MatchGlobalenvs ge.genv_genv f bound)

include MEMINJ in
/-- `SimplLocalsproof.deref_loc_inject` -/
theorem deref_loc_inject {ty : Ty} {loc : Block} {ofs : Integers.Ptrofs} {bf : Bitfield} {v : Val}
    {loc' : Block} {ofs' : Integers.Ptrofs} (hd : DerefLoc ty m loc ofs bf v)
    (hi : Val.Inject f (.Vptr loc ofs) (.Vptr loc' ofs')) :
    ∃ tv, DerefLoc ty tm loc' ofs' bf tv ∧ Val.Inject f v tv := by
  cases hd with
  | value chunk v hm hl =>
    obtain ⟨tv, A, B⟩ := Mem.loadv_inject MEMINJ hl hi
    exact ⟨tv, .value _ _ hm A, B⟩
  | reference hm => exact ⟨_, .reference hm, hi⟩
  | copy hm => exact ⟨_, .copy hm, hi⟩
  | bitfield sz sg pos width v hlb =>
    cases hlb with
    | intro sz sg1 attr sg pos width m addr c h1 h2 h3 h4 h5 h6 =>
    obtain ⟨tc, A, B⟩ := Mem.loadv_inject MEMINJ h6 hi
    cases B
    exact ⟨_, .bitfield _ _ _ _ _ (.intro _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 A), .int _⟩

theorem lifted_or_not (cenv : Compilenv) (a : Expr) :
    (∃ id ty, a = .Evar id ty ∧ VSet.mem id cenv = true) ∨ NotLiftedVar cenv a := by
  cases a with
  | Evar id ty =>
    cases hm : VSet.mem id cenv with
    | true => exact Or.inl ⟨id, ty, rfl, hm⟩
    | false => exact Or.inr hm
  | _ => exact Or.inr trivial

include hce hsym MATCH MEMINJ GLOB in
mutual
/-- `SimplLocalsproof.eval_simpl_expr` -/
theorem eval_simpl_expr {a : Expr} {v : Val} :
    EvalExpr ge e le m a v → CompatCenv (addrTakenExpr a) cenv →
    ∃ tv, EvalExpr tge te tle tm (simplExpr cenv a) tv ∧ Val.Inject f v tv
  | .Econst_int i ty, _ => ⟨_, .Econst_int i ty, .int _⟩
  | .Econst_float x ty, _ => ⟨_, .Econst_float x ty, .float _⟩
  | .Econst_single x ty, _ => ⟨_, .Econst_single x ty, .single _⟩
  | .Econst_long i ty, _ => ⟨_, .Econst_long i ty, .long _⟩
  | .Etempvar id ty v h, _ => by
    obtain ⟨⟨tv, A, B⟩, _⟩ := MATCH.me_temps id v h
    exact ⟨tv, .Etempvar _ _ _ A, B⟩
  | .Eaddrof a ty loc ofs hl, hc => by
    obtain ⟨hc1, hc2⟩ := compat_addrof hc
    obtain ⟨b', ofs', A, B⟩ := eval_simpl_lvalue hl hc1 hc2
    exact ⟨_, .Eaddrof _ _ _ _ A, B⟩
  | .Eunop op a ty v1 v h hs, hc => by
    obtain ⟨tv1, A, B⟩ := eval_simpl_expr h hc
    obtain ⟨tv, C, D⟩ := Cop.semUnaryOperation_inject hs B MEMINJ
    exact ⟨tv, .Eunop _ _ _ _ _ A (by rw [typeof_simpl_expr]; exact C), D⟩
  | .Ebinop op a1 a2 ty v1 v2 v h1 h2 hs, hc => by
    obtain ⟨tv1, A, B⟩ := eval_simpl_expr h1 (compat_cenv_union_l hc)
    obtain ⟨tv2, C, D⟩ := eval_simpl_expr h2 (compat_cenv_union_r hc)
    obtain ⟨tv, E, F⟩ := Cop.semBinaryOperation_inject hs B D MEMINJ
    exact ⟨tv, .Ebinop _ _ _ _ _ _ _ A C
      (by rw [typeof_simpl_expr, typeof_simpl_expr, hce]; exact E), F⟩
  | .Ecast a ty v1 v h hs, hc => by
    obtain ⟨tv1, A, B⟩ := eval_simpl_expr h hc
    obtain ⟨tv, C, D⟩ := Cop.semCast_inject hs B MEMINJ
    exact ⟨tv, .Ecast _ _ _ _ A (by rw [typeof_simpl_expr]; exact C), D⟩
  | .Esizeof ty1 ty, _ => by
    refine ⟨_, .Esizeof ty1 ty, ?_⟩
    rw [hce]; exact Cop.vptrofs_inject _
  | .Ealignof ty1 ty, _ => by
    refine ⟨_, .Ealignof ty1 ty, ?_⟩
    rw [hce]; exact Cop.vptrofs_inject _
  | .Elvalue a loc ofs bf v hl hd, hc => by
    rcases lifted_or_not cenv a with ⟨id, ty, rfl, hlift⟩ | hnon
    · simp only [simplExpr, hlift, if_true]
      cases MATCH.me_vars id with
      | not_lifted _ _ _ _ _ h3 _ => rw [hlift] at h3; cases h3
      | not_local _ _ h3 => rw [hlift] at h3; cases h3
      | lifted b ty0 chunk v0 tv ENV _ _ _ MODE LOAD TLENV VINJ =>
      cases hl with
      | Evar_global _ _ _ h1 _ => rw [ENV] at h1; cases h1
      | Evar_local _ _ _ h1 =>
      rw [ENV] at h1; cases h1
      cases hd with
      | value chunk' v hm hl' =>
        simp only [typeof] at hm
        rw [MODE] at hm; cases hm
        have := Mem.loadv_load hl'
        rw [ptrofs_unsigned_zero, LOAD] at this; cases this
        exact ⟨tv, .Etempvar _ _ _ TLENV, VINJ⟩
      | reference hm => simp only [typeof] at hm; rw [MODE] at hm; cases hm
      | copy hm => simp only [typeof] at hm; rw [MODE] at hm; cases hm
    · obtain ⟨loc', ofs', A, B⟩ := eval_simpl_lvalue hl hc hnon
      obtain ⟨tv, C, D⟩ := deref_loc_inject MEMINJ hd B
      exact ⟨tv, .Elvalue _ _ _ _ _ A (by rw [typeof_simpl_expr]; exact C), D⟩

/-- `SimplLocalsproof.eval_simpl_lvalue` -/
theorem eval_simpl_lvalue {a : Expr} {b : Block} {ofs : Integers.Ptrofs} {bf : Bitfield} :
    EvalLvalue ge e le m a b ofs bf → CompatCenv (addrTakenExpr a) cenv →
    NotLiftedVar cenv a →
    ∃ b' ofs', EvalLvalue tge te tle tm (simplExpr cenv a) b' ofs' bf ∧
      Val.Inject f (.Vptr b ofs) (.Vptr b' ofs')
  | .Evar_local id l ty h, _, hn => by
    simp only [NotLiftedVar] at hn
    simp only [simplExpr, hn]
    cases MATCH.me_vars id with
    | lifted _ _ _ _ _ _ _ h3 _ _ _ _ _ => rw [hn] at h3; cases h3
    | not_local h1 _ _ => rw [h] at h1; cases h1
    | not_lifted b ty0 b' ENV TENV _ MAPPED =>
    rw [h] at ENV; cases ENV
    exact ⟨b', _, .Evar_local _ _ _ TENV, .ptr 0 MAPPED (EventsInject.ptrofs_add_repr_zero _).symm⟩
  | .Evar_global id l ty h hs, _, hn => by
    simp only [NotLiftedVar] at hn
    simp only [simplExpr, hn]
    cases MATCH.me_vars id with
    | lifted _ _ _ _ _ _ _ h3 _ _ _ _ _ => rw [hn] at h3; cases h3
    | not_lifted _ _ _ h1 _ _ _ => rw [h] at h1; cases h1
    | not_local _ TENV _ =>
    obtain ⟨bound, MG⟩ := GLOB
    exact ⟨l, _, .Evar_global _ _ _ TENV (by rw [hsym]; exact hs),
      .ptr 0 (MG.domain l (MG.symbols id l hs)) (EventsInject.ptrofs_add_repr_zero _).symm⟩
  | .Ederef a ty l ofs h, hc, _ => by
    obtain ⟨tv, A, B⟩ := eval_simpl_expr h hc
    cases B with
    | ptr delta hf ho =>
    exact ⟨_, _, .Ederef _ _ _ _ A, .ptr delta hf ho⟩
  | .Efield_struct a i ty l ofs id co att delta bf h hty hco hfo, hc, _ => by
    obtain ⟨tv, A, B⟩ := eval_simpl_expr h hc
    cases B with
    | ptr d hf ho =>
    subst ho
    refine ⟨_, _, .Efield_struct _ _ _ _ _ _ _ _ _ _ A (by rw [typeof_simpl_expr]; exact hty)
      (by rw [hce]; exact hco) (by rw [hce]; exact hfo), .ptr d hf ?_⟩
    rw [Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_commut (Integers.Ptrofs.repr d)]
  | .Efield_union a i ty l ofs id co att delta bf h hty hco hfo, hc, _ => by
    obtain ⟨tv, A, B⟩ := eval_simpl_expr h hc
    cases B with
    | ptr d hf ho =>
    subst ho
    refine ⟨_, _, .Efield_union _ _ _ _ _ _ _ _ _ _ A (by rw [typeof_simpl_expr]; exact hty)
      (by rw [hce]; exact hco) (by rw [hce]; exact hfo), .ptr d hf ?_⟩
    rw [Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_commut (Integers.Ptrofs.repr d)]
end

include hce hsym MATCH MEMINJ GLOB in
/-- `SimplLocalsproof.eval_simpl_exprlist` -/
theorem eval_simpl_exprlist {al : List Expr} {tyl : List Ty} {vl : List Val}
    (h : EvalExprlist ge e le m al tyl vl) (hc : CompatCenv (addrTakenExprlist al) cenv) :
    ValCastedList vl tyl ∧
      ∃ tvl, EvalExprlist tge te tle tm (simplExprlist cenv al) tyl tvl ∧ Val.InjectList f vl tvl := by
  induction h with
  | nil => exact ⟨.nil, [], .nil, .nil⟩
  | cons a bl ty tyl v1 v2 vl h1 h2 _ ih =>
    obtain ⟨tv1, A, B⟩ := eval_simpl_expr hce hsym MATCH MEMINJ GLOB h1 (compat_cenv_union_l hc)
    obtain ⟨tv2, C, D⟩ := Cop.semCast_inject h2 B MEMINJ
    obtain ⟨E, tvl, F, G⟩ := ih (compat_cenv_union_r hc)
    exact ⟨.cons (Cop.cast_val_is_casted h2) E, tv2 :: tvl,
      .cons _ _ _ _ _ _ _ A (by rw [typeof_simpl_expr]; exact C) F, .cons D G⟩

end EVAL_EXPR

end SimplLocals
end CC
