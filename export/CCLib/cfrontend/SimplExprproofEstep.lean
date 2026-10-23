/-
  Expression simplification: semantic preservation — port of
  `cfrontend/SimplExprproof.v`, part 5: the anti-stuttering measure
  (`esize`, `measure`, `leftcontext_size`) and the forward simulation for
  expression reductions (`estep_simulation`).

  Differences from Rocq:
  * every case of `estep_simulation` is a separate lemma, stated over the
    components of `match_exprstates`;
  * the source and target global environments are related by `GenvRel`, and
    the translation of function definitions is the hypothesis `FunsTranslated`
    (proved for whole programs by `functions_translated`).
-/
import CCLib.cfrontend.SimplExprproofMatch
import CCLib.cfrontend.CopTheory

namespace CC
namespace SimplExpr

open Destination SetDestination Cstrategy Smallstep

/-! ## Anti-stuttering measure -/

mutual
/-- `SimplExprproof.esize` -/
def esize : Csyntax.Expr → Nat
  | .Eloc _ _ _ _ => 1
  | .Evar _ _ => 1
  | .Ederef r1 _ => esize r1 + 1
  | .Efield l1 _ _ => esize l1 + 1
  | .Eval _ _ => 0
  | .Evalof l1 _ => esize l1 + 1
  | .Eaddrof l1 _ => esize l1 + 1
  | .Eunop _ r1 _ => esize r1 + 1
  | .Ebinop _ r1 r2 _ => esize r1 + esize r2 + 1
  | .Ecast r1 _ => esize r1 + 1
  | .Eseqand r1 _ _ => esize r1 + 1
  | .Eseqor r1 _ _ => esize r1 + 1
  | .Econdition r1 _ _ _ => esize r1 + 1
  | .Esizeof _ _ => 1
  | .Ealignof _ _ => 1
  | .Eassign l1 r2 _ => esize l1 + esize r2 + 1
  | .Eassignop _ l1 r2 _ _ => esize l1 + esize r2 + 1
  | .Epostincr _ l1 _ => esize l1 + 1
  | .Ecomma r1 r2 _ => esize r1 + esize r2 + 1
  | .Ecall r1 rl2 _ => esize r1 + esizelist rl2 + 1
  | .Ebuiltin _ _ rl _ => esizelist rl + 1
  | .Eparen r1 _ _ => esize r1 + 1

/-- `SimplExprproof.esizelist` -/
def esizelist : Csyntax.ExprList → Nat
  | .Enil => 0
  | .Econs r1 rl2 => esize r1 + esizelist rl2
end

/-- `SimplExprproof.measure` -/
def measure : Csem.State → Nat
  | .ExprState _ r _ _ _ => esize r + 1
  | .State _ .Sskip _ _ _ => 0
  | .State _ (.Sdo r) _ _ _ => esize r + 2
  | .State _ (.Sifthenelse r _ _) _ _ _ => esize r + 2
  | _ => 0

mutual
/-- `SimplExprproof.leftcontext_size` -/
theorem leftcontext_size {k1} : ∀ {k2 C}, LeftContext k1 k2 C →
    ∀ {e1 e2 : Csyntax.Expr}, esize e1 < esize e2 → esize (C e1) < esize (C e2)
  | _, _, .top _, _, _, h => h
  | _, _, .deref _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .field _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .rvalof _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .addrof _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .unop _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .binop_left _ _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .binop_right _ _ _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .cast _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .seqand _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .seqor _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .condition _ _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .assign_left _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .assign_right _ _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .assignop_left _ _ _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .assignop_right _ _ _ _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .postincr _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .call_left _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .call_right _ _ _ _ _ hC, _, _, h => by
    have := leftcontextlist_size hC h; simp only [esize]; omega
  | _, _, .builtin _ _ _ _ _ hC, _, _, h => by
    have := leftcontextlist_size hC h; simp only [esize]; omega
  | _, _, .comma _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega
  | _, _, .paren _ _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esize]; omega

/-- `SimplExprproof.leftcontextlist_size` -/
theorem leftcontextlist_size {k} : ∀ {C}, LeftContextList k C →
    ∀ {e1 e2 : Csyntax.Expr}, esize e1 < esize e2 → esizelist (C e1) < esizelist (C e2)
  | _, .head _ _ _ hC, _, _, h => by
    have := leftcontext_size hC h; simp only [esizelist]; omega
  | _, .tail _ _ _ _ hC, _, _, h => by
    have := leftcontextlist_size hC h; simp only [esizelist]; omega
end

theorem esize_pos {r : Csyntax.Expr} (h : match r with | .Eval _ _ => False | _ => True) :
    0 < esize r := by
  cases r <;> simp only [esize] at h ⊢ <;> first | omega | exact h.elim

/-! ## Forward simulation for expressions -/

section TRVAL
variable {ce : CompositeEnv}

/-- `SimplExprproof.tr_val_gen` -/
theorem tr_val_gen {le dst v ty a tmp} (hty : typeof a = ty)
    (hev : ∀ tge e le' m, (∀ id, id ∈ tmp → le'.get id = le.get id) → EvalExpr tge e le' m a v) :
    TrExpr ce le dst (.Eval v ty) (final dst a) a tmp := by
  cases dst with
  | For_val => exact .tr_val_value _ _ _ _ _ hty hev
  | For_effects => exact .tr_val_effect _ _ _ _ _
  | For_set sd => exact .tr_val_set _ _ _ _ _ _ _ hty hev

end TRVAL

/-- The conclusion of `SimplExprproof.estep_simulation` and
    `SimplExprproof.sstep_simulation`. -/
def SimGoal (p : Csyntax.Program) (tge : CGenv) (S1 : Csem.State) (t : Trace) (S2 : Csem.State)
    (S1' : State) : Prop :=
  ∃ S2', (Smallstep.Plus (Step1 tge) S1' t S2' ∨ (Smallstep.Star (Step1 tge) S1' t S2' ∧ measure S2 < measure S1)) ∧
    MatchStates p tge S2 S2'

/-- The translation of function definitions, as needed by the simulation
    (`SimplExprproof.functions_translated`). -/
def FunsTranslated (p : Csyntax.Program) (tge : CGenv) : Prop :=
  ∀ v fd, Genv.findFunct (Csem.globalenv p).genv_genv v = some fd →
    ∃ tfd, Genv.findFunct tge.genv_genv v = some tfd ∧ TrFundef p fd tfd

theorem ms_expr {p : Csyntax.Program} {tge : CGenv} {f r k e m tf sl tk le dest a} (tmps : List Ident)
    (hf : TrFunction p.prog_comp_env f tf) (htop : TrTop p.prog_comp_env tge e le m dest r sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    MatchStates p tge (.ExprState f r k e m) (.State tf .Sskip (Kseqlist sl tk) e le m) :=
  .exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk

theorem set_unchanged {le : TempEnv} {t : Ident} {v : Val} {tmp : List Ident} (hin : t ∈ tmp) :
    ∀ id, id ∉ tmp → (le.set t v).get id = le.get id :=
  fun _ hid => PTree.gso _ _ _ _ (fun h => hid (h ▸ hin))

theorem eval_set_temp {le : TempEnv} {t : Ident} {v : Val} {ty : Ty} {tmp : List Ident}
    (hin : t ∈ tmp) :
    ∀ (tge : CGenv) e le' m, (∀ id, id ∈ tmp → le'.get id = (le.set t v).get id) →
      EvalExpr tge e le' m (.Etempvar t ty) v :=
  fun _ _ _ _ h => .Etempvar _ _ _ (by rw [h t hin, PTree.gss])

theorem ms_expr_app {p : Csyntax.Program} {tge : CGenv} {f r k e m tf sl1 sl2 tk le dest a}
    (tmps : List Ident) (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest r (sl1 ++ sl2) a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    MatchStates p tge (.ExprState f r k e m) (.State tf .Sskip (Kseqlist sl1 (Kseqlist sl2 tk)) e le m) := by
  rw [← Kseqlist_app]; exact ms_expr tmps hf htop hk

/-- Executing `makeif a s1 s2` followed by the statements of the chosen
    branch. -/
theorem plus_makeif_seq {tge : CGenv} {f a s1 s2 k e le m v1 b sl'}
    (hev : EvalExpr tge e le m a v1) (hb : Cop.boolVal v1 (typeof a) m = some b)
    (hs : (if b then s1 else s2) = makeseq sl') :
    Smallstep.Plus (Step1 tge) (.State f .Sskip (.Kseq (makeif a s1 s2) k) e le m) E0
      (.State f .Sskip (Kseqlist sl' k) e le m) :=
  plus_left (Step.skip_seq _ _ _ _ _ _)
    (star_trans (step_makeif hev hb) (hs ▸ push_seq) rfl) rfl

/-- Executing `makeif a s1 s2` when the chosen branch is a single
    statement. -/
theorem plus_makeif_one {tge : CGenv} {f a s1 s2 k e le m v1 b t s' S}
    (hev : EvalExpr tge e le m a v1) (hb : Cop.boolVal v1 (typeof a) m = some b)
    (hs : (if b then s1 else s2) = s')
    (hstep : Step1 tge (.State f s' k e le m) t S) :
    Smallstep.Plus (Step1 tge) (.State f .Sskip (.Kseq (makeif a s1 s2) k) e le m) t S :=
  plus_left (Step.skip_seq _ _ _ _ _ _)
    (star_trans (step_makeif hev hb) (hs ▸ star_one hstep) rfl) rfl

theorem eval_translIncrdecr {tge : CGenv} {e le m a v1 v2 ty} (id : Cop.IncrOrDecr)
    (hev : EvalExpr tge e le m a v1) (hty : typeof a = ty)
    (h : Cop.semIncrdecr tge.genv_cenv id v1 ty m = some v2) :
    EvalExpr tge e le m (translIncrdecr id a ty) v2 := by
  subst hty
  cases id
  · exact .Ebinop _ _ _ _ _ _ _ hev (.Econst_int _ _) h
  · exact .Ebinop _ _ _ _ _ _ _ hev (.Econst_int _ _) h

theorem typeof_translIncrdecr (id : Cop.IncrOrDecr) (a : Expr) (ty : Ty) :
    typeof (translIncrdecr id a ty) = Cop.incrdecrType ty := by
  cases id <;> rfl

section ESTEP
variable {p : Csyntax.Program} {tge : CGenv} (GR : GenvRel (Csem.globalenv p) tge)

theorem GenvRel.cenv' (GR : GenvRel (Csem.globalenv p) tge) : tge.genv_cenv = p.prog_comp_env :=
  GR.cenv

include GR

theorem estep_expr {f r k e m v ty tf le dest sl a tmps tk}
    (hr : EvalSimpleRvalue (Csem.globalenv p) e m r v)
    (hnv : match (generalizing := false) r with | .Eval _ _ => False | _ => True) (hty : ty = Csyntax.typeof r)
    (hf : TrFunction p.prog_comp_env f tf) (htop : TrTop p.prog_comp_env tge e le m dest r sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f r k e m) E0 (.ExprState f (.Eval v ty) k e m)
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  have htr : TrExpr p.prog_comp_env le dest r sl a tmps := by
    cases htop with
    | tr_top_val_val => exact hnv.elim
    | tr_top_base _ _ _ _ _ h => exact h
  have hs := tr_simple_rvalue _ GR hr htr
  have hpos := esize_pos hnv
  cases dest with
  | For_val =>
    obtain ⟨rfl, hty1, hev⟩ := hs
    refine ⟨_, .inr ⟨Smallstep.Star.refl _, by simp only [measure, esize]; omega⟩,
      ms_expr tmps hf (.tr_top_val_val _ _ _ _ (by rw [hty, hty1]) hev) hk⟩
  | For_effects =>
    subst hs
    refine ⟨_, .inr ⟨Smallstep.Star.refl _, by simp only [measure, esize]; omega⟩,
      ms_expr tmps hf (.tr_top_base _ _ _ _ _ (.tr_val_effect _ _ _ _ _)) hk⟩
  | For_set sd => cases hk

theorem estep_rvalof_volatile {f C l ty k e m b ofs bf t v tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hl : EvalSimpleLvalue (Csem.globalenv p) e m l b ofs bf)
    (hd : Csem.DerefLoc (Csem.globalenv p) ty m b ofs bf t v) (hty : ty = Csyntax.typeof l)
    (hvol : typeIsVolatile ty = true)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Evalof l ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Evalof l ty)) k e m) t (.ExprState f (C (.Eval v ty)) k e m)
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  subst hty
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_valof _ _ _ _ sl1' a1 tmp1 sl2' a2 tmp2 h1 h2 _ _ hi2 =>
  cases h2 with
  | tr_rvalof_nonvol _ hnv => rw [hvol] at hnv; cases hnv
  | tr_rvalof_vol t0 bf0 _ _ hin hbf =>
  obtain ⟨rfl, hty1, hev⟩ := tr_simple_lvalue _ GR hl h1
  have := is_bitfield_access_sound GR.cenv' hev hbf; subst this
  exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _) (star_one (step_make_set GR hd hev hty1.symm))
      rfl),
    ms_expr tmps hf (S (le.set t0 v) m (.Eval v _) _ (tr_val_gen rfl (eval_set_temp (hi2 hin)))
      (set_unchanged (hi2 hin)) rfl) hk⟩

theorem estep_seqand_true {f C r1 r2 ty k e m v tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hr : EvalSimpleRvalue (Csem.globalenv p) e m r1 v)
    (hb : Cop.boolVal v (Csyntax.typeof r1) m = some true)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eseqand r1 r2 ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eparen r2 type_bool ty)) k e m) (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_seqand_val _ _ _ _ _ _ t _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_paren_val _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2) ht)
        (fun _ _ => rfl) rfl) hk⟩
  | tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ hi2 =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_paren_effects _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2))
        (fun _ _ => rfl) rfl) hk⟩
  | tr_seqand_set _ _ _ _ _ _ _ t _ _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_paren_set _ _ _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2) ht)
        (fun _ _ => rfl) rfl) hk⟩

theorem estep_seqand_false {f C r1 r2 ty k e m v tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hr : EvalSimpleRvalue (Csem.globalenv p) e m r1 v)
    (hb : Cop.boolVal v (Csyntax.typeof r1) m = some false)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eseqand r1 r2 ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Eseqand r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eval (.Vint Integers.Int.zero) ty)) k e m)
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_seqand_val _ _ _ _ _ _ t _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_one (b := false) hev (hty1 ▸ hb) rfl (Step.set _ _ _ _ _ _ _ _ (.Econst_int _ _))),
      ms_expr tmps hf (S _ m _ [] (.tr_val_value _ _ _ _ _ rfl (eval_set_temp ht))
        (set_unchanged ht) rfl) hk⟩
  | tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ hi2 =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _) (step_makeif hev (hty1 ▸ hb)) rfl),
      ms_expr tmps hf (S le m _ [] (.tr_val_effect _ _ _ _ _) (fun _ _ => rfl) rfl) hk⟩
  | tr_seqand_set _ _ _ _ _ _ _ t _ _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_val_set _ _ _ _ _ _ _ rfl (fun _ _ _ _ _ => .Econst_int _ _))
        (fun _ _ => rfl) rfl) hk⟩

theorem estep_seqor_true {f C r1 r2 ty k e m v tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hr : EvalSimpleRvalue (Csem.globalenv p) e m r1 v)
    (hb : Cop.boolVal v (Csyntax.typeof r1) m = some true)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eseqor r1 r2 ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eval (.Vint Integers.Int.one) ty)) k e m)
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_seqor_val _ _ _ _ _ _ t _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_one (b := true) hev (hty1 ▸ hb) rfl (Step.set _ _ _ _ _ _ _ _ (.Econst_int _ _))),
      ms_expr tmps hf (S _ m _ [] (.tr_val_value _ _ _ _ _ rfl (eval_set_temp ht))
        (set_unchanged ht) rfl) hk⟩
  | tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ hi2 =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _) (step_makeif hev (hty1 ▸ hb)) rfl),
      ms_expr tmps hf (S le m _ [] (.tr_val_effect _ _ _ _ _) (fun _ _ => rfl) rfl) hk⟩
  | tr_seqor_set _ _ _ _ _ _ _ t _ _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_val_set _ _ _ _ _ _ _ rfl (fun _ _ _ _ _ => .Econst_int _ _))
        (fun _ _ => rfl) rfl) hk⟩

theorem estep_seqor_false {f C r1 r2 ty k e m v tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hr : EvalSimpleRvalue (Csem.globalenv p) e m r1 v)
    (hb : Cop.boolVal v (Csyntax.typeof r1) m = some false)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eseqor r1 r2 ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Eseqor r1 r2 ty)) k e m) E0
      (.ExprState f (C (.Eparen r2 type_bool ty)) k e m) (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_seqor_val _ _ _ _ _ _ t _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_paren_val _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2) ht)
        (fun _ _ => rfl) rfl) hk⟩
  | tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ hi2 =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_paren_effects _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2))
        (fun _ _ => rfl) rfl) hk⟩
  | tr_seqor_set _ _ _ _ _ _ _ t _ _ _ _ _ h1 h2 _ _ hi2 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
      ms_expr_app tmps hf (S le m _ _ (.tr_paren_set _ _ _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2) ht)
        (fun _ _ => rfl) rfl) hk⟩

theorem estep_condition {f C r1 r2 r3 ty k e m v b tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hr : EvalSimpleRvalue (Csem.globalenv p) e m r1 v)
    (hb : Cop.boolVal v (Csyntax.typeof r1) m = some b)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Econdition r1 r2 r3 ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Econdition r1 r2 r3 ty)) k e m) E0
      (.ExprState f (C (.Eparen (if b then r2 else r3) ty ty)) k e m)
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ t _ h1 h2 h3 _ _ _ hi2 hi3 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    cases b
    · exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
        ms_expr_app tmps hf (S le m _ _ (.tr_paren_val _ _ _ _ _ _ _ _ (tr_expr_monotone _ h3 hi3) ht)
          (fun _ _ => rfl) rfl) hk⟩
    · exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
        ms_expr_app tmps hf (S le m _ _ (.tr_paren_val _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2) ht)
          (fun _ _ => rfl) rfl) hk⟩
  | tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 _ _ _ hi2 hi3 =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    cases b
    · exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
        ms_expr_app tmps hf (S le m _ _ (.tr_paren_effects _ _ _ _ _ _ _ _ (tr_expr_monotone _ h3 hi3))
          (fun _ _ => rfl) rfl) hk⟩
    · exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
        ms_expr_app tmps hf (S le m _ _ (.tr_paren_effects _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2))
          (fun _ _ => rfl) rfl) hk⟩
  | tr_condition_set _ t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 _ _ _ hi2 hi3 ht =>
    obtain ⟨rfl, hty1, hev⟩ := tr_simple_rvalue _ GR hr h1
    cases b
    · exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
        ms_expr_app tmps hf (S le m _ _
          (.tr_paren_set _ _ _ _ _ _ _ _ _ _ (tr_expr_monotone _ h3 hi3) ht) (fun _ _ => rfl) rfl) hk⟩
    · exact ⟨_, .inl (plus_makeif_seq hev (hty1 ▸ hb) rfl),
        ms_expr_app tmps hf (S le m _ _
          (.tr_paren_set _ _ _ _ _ _ _ _ _ _ (tr_expr_monotone _ h2 hi2) ht) (fun _ _ => rfl) rfl) hk⟩

theorem estep_assign {f C l r ty k e m b ofs bf v v1 t m' v' tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hl : EvalSimpleLvalue (Csem.globalenv p) e m l b ofs bf)
    (hr : EvalSimpleRvalue (Csem.globalenv p) e m r v)
    (hc : Cop.semCast v (Csyntax.typeof r) (Csyntax.typeof l) m = some v1)
    (ha : Csem.AssignLoc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf v1 t m' v')
    (hty : ty = Csyntax.typeof l)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eassign l r ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Eassign l r ty)) k e m) t (.ExprState f (C (.Eval v' ty)) k e m')
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  subst hty
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ _ hbf =>
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue _ GR hr h2
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    have := is_bitfield_access_sound GR.cenv' hev1 hbf; subst this
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (step_make_assign GR ha hev1 hev2 (by rw [← hty2]; exact hc) hty1.symm)) rfl),
      ms_expr tmps hf (S le m' _ [] (.tr_val_effect _ _ _ _ _) (fun _ _ => rfl) rfl) hk⟩
  | tr_assign_val _ _ _ _ _ _ _ _ a2 _ t _ _ _ _ h1 h2 _ _ _ ht htn1 _ hty1e _ hbf =>
    subst hty1e
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue _ GR hr h2
    have h1' := tr_expr_invariant _ h1 (le' := le.set t v1)
      (fun x hx => PTree.gso _ _ _ _ (fun h => htn1 (h ▸ hx)))
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1'
    have := is_bitfield_access_sound GR.cenv' hev1 hbf; subst this
    have hc' : Cop.semCast v (typeof a2) (Csyntax.typeof l) m = some v1 := by rw [← hty2]; exact hc
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_left (Step.set _ _ _ _ _ _ _ _ (.Ecast _ _ _ _ hev2 hc'))
          (star_left (Step.skip_seq _ _ _ _ _ _)
            (star_one (step_make_assign GR ha hev1 (.Etempvar _ _ _ (PTree.gss _ _ _))
              (Cop.cast_idempotent hc') hty1.symm)) rfl) rfl) rfl),
      ms_expr tmps hf (S (le.set t v1) m' (.Eval v' _) _
        (tr_val_gen (by rw [typeof_make_assign_value]; rfl)
          (fun _ _ _ _ h => make_assign_value_sound ha rfl (eval_set_temp ht _ _ _ _ h)))
        (set_unchanged ht) rfl) hk⟩

theorem estep_assignop {f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1 t2 m' v' t tf le dest sl a
    tmps tk}
    (hC : LeftContext .RV .RV C) (hl : EvalSimpleLvalue (Csem.globalenv p) e m l b ofs bf)
    (hd : Csem.DerefLoc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf t1 v1)
    (hr : EvalSimpleRvalue (Csem.globalenv p) e m r v2)
    (hop : Cop.semBinaryOperation (Csem.globalenv p).genv_cenv op v1 (Csyntax.typeof l) v2
      (Csyntax.typeof r) m = some v3)
    (hc : Cop.semCast v3 tyres (Csyntax.typeof l) m = some v4)
    (ha : Csem.AssignLoc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf v4 t2 m' v')
    (hty : ty = Csyntax.typeof l) (ht : t = Eapp t1 t2)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eassignop op l r tyres ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t
      (.ExprState f (C (.Eval v' ty)) k e m') (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  subst hty ht
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_assignop_effects _ _ _ _ _ _ _ a1 _ _ a2 _ bf0 sl3 a3 _ _ _ h1 h2 hty1e hrv _ hd13 hd23 _ _ hi3 hbf =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    have := is_bitfield_access_sound GR.cenv' hev1 hbf; subst bf0
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue _ GR hr h2
    obtain ⟨le', EXEC, hev3, hty3, INV⟩ := step_tr_rvalof (k := .Kseq (makeAssign bf a1
      (.Ebinop op a3 a2 tyres)) (Kseqlist sl2 tk)) (f := tf) GR GR.cenv' hd hev1 hrv hty1.symm
    obtain ⟨-, -, hev1'⟩ := tr_simple_lvalue _ GR hl (tr_expr_invariant _ h1 (le' := le')
      (fun x hx => INV x (fun hx3 => hd13 x hx hx3)))
    obtain ⟨-, -, hev2'⟩ := tr_simple_rvalue _ GR hr (tr_expr_invariant _ h2 (le' := le')
      (fun x hx => INV x (fun hx3 => hd23 x hx hx3)))
    have hop' : Cop.semBinaryOperation tge.genv_cenv op v1 (typeof a3) v2 (typeof a2) m = some v3 := by
      rw [hty3, ← hty1, ← hty2, GR.cenv']; exact hop
    rw [show (([] ++ [] ++ sl3 ++ [makeAssign bf a1 (.Ebinop op a3 a2 tyres)]) ++ sl2 : List Stmt) =
      sl3 ++ (makeAssign bf a1 (.Ebinop op a3 a2 tyres) :: sl2) by simp, Kseqlist_app]
    exact ⟨_, .inl (star_plus_trans EXEC (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (step_make_assign GR ha hev1' (.Ebinop _ _ _ _ _ _ _ hev3 hev2' hop') hc hty1.symm))
        rfl) rfl),
      ms_expr tmps hf (S le' m' _ [] (.tr_val_effect _ _ _ _ _)
        (fun x hx => INV x (fun hx3 => hx (hi3 hx3))) rfl) hk⟩
  | tr_assignop_val _ _ _ _ _ _ _ a1 _ _ a2 _ sl3 a3 _ t bf0 _ _ h1 h2 hrv _ hd13 hd23 _ _ hi3 ht htn1
      _ _ hty1e hbf =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    have := is_bitfield_access_sound GR.cenv' hev1 hbf; subst bf0
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue _ GR hr h2
    obtain ⟨le', EXEC, hev3, hty3, INV⟩ := step_tr_rvalof (f := tf) (k := .Kseq
      (.Sset t (.Ecast (.Ebinop op a3 a2 tyres) (Csyntax.typeof l)))
      (.Kseq (makeAssign bf a1 (.Etempvar t (Csyntax.typeof l)))
        (Kseqlist (final dst' (makeAssignValue bf (.Etempvar t (Csyntax.typeof l))) ++ sl2) tk)))
      GR GR.cenv' hd hev1 hrv hty1.symm
    obtain ⟨-, -, hev2'⟩ := tr_simple_rvalue _ GR hr (tr_expr_invariant _ h2 (le' := le')
      (fun x hx => INV x (fun hx3 => hd23 x hx hx3)))
    obtain ⟨-, -, hev1'⟩ := tr_simple_lvalue _ GR hl (tr_expr_invariant _ h1 (le' := le'.set t v4)
      (fun x hx => by
        rw [PTree.gso _ _ _ _ (by rintro rfl; exact htn1 hx)]
        exact INV x (fun hx3 => hd13 x hx hx3)))
    have hop' : Cop.semBinaryOperation tge.genv_cenv op v1 (typeof a3) v2 (typeof a2) m = some v3 := by
      rw [hty3, ← hty1, ← hty2, GR.cenv']; exact hop
    rw [show (([] ++ [] ++ sl3 ++ .Sset t (.Ecast (.Ebinop op a3 a2 tyres) (Csyntax.typeof l)) ::
        makeAssign bf a1 (.Etempvar t (Csyntax.typeof l)) ::
        final dst' (makeAssignValue bf (.Etempvar t (Csyntax.typeof l)))) ++ sl2 : List Stmt) =
      sl3 ++ (.Sset t (.Ecast (.Ebinop op a3 a2 tyres) (Csyntax.typeof l)) ::
        makeAssign bf a1 (.Etempvar t (Csyntax.typeof l)) ::
        (final dst' (makeAssignValue bf (.Etempvar t (Csyntax.typeof l))) ++ sl2)) by simp,
      Kseqlist_app]
    exact ⟨_, .inl (star_plus_trans EXEC (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_left (Step.set _ _ _ _ _ _ _ _
            (.Ecast _ _ _ _ (.Ebinop _ _ _ _ _ _ _ hev3 hev2' hop') hc))
          (star_left (Step.skip_seq _ _ _ _ _ _)
            (star_one (step_make_assign GR ha hev1' (.Etempvar _ _ _ (PTree.gss _ _ _))
              (Cop.cast_idempotent hc) hty1.symm)) rfl) rfl) rfl) rfl),
      ms_expr tmps hf (S (le'.set t v4) m' (.Eval v' _) _
        (tr_val_gen (by rw [typeof_make_assign_value]; rfl)
          (fun _ _ _ _ h => make_assign_value_sound ha rfl (eval_set_temp ht _ _ _ _ h)))
        (fun x hx => by
          rw [PTree.gso _ _ _ _ (by rintro rfl; exact hx ht)]
          exact INV x (fun hx3 => hx (hi3 hx3))) rfl) hk⟩

theorem estep_assignop_stuck {f C op l r tyres ty k e m b ofs bf v1 v2 t tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hl : EvalSimpleLvalue (Csem.globalenv p) e m l b ofs bf)
    (hd : Csem.DerefLoc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf t v1)
    (hr : EvalSimpleRvalue (Csem.globalenv p) e m r v2)
    (hty : ty = Csyntax.typeof l)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eassignop op l r tyres ty)) sl a tmps) :
    SimGoal p tge (.ExprState f (C (.Eassignop op l r tyres ty)) k e m) t .Stuckstate
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  subst hty
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_assignop_effects _ _ _ _ _ _ _ a1 _ _ a2 _ bf0 sl3 a3 _ _ _ h1 h2 hty1e hrv =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue _ GR hr h2
    obtain ⟨le', EXEC, -⟩ := step_tr_rvalof (k := .Kseq (makeAssign bf0 a1
      (.Ebinop op a3 a2 tyres)) (Kseqlist sl2 tk)) (f := tf) GR GR.cenv' hd hev1 hrv hty1.symm
    rw [show (([] ++ [] ++ sl3 ++ [makeAssign bf0 a1 (.Ebinop op a3 a2 tyres)]) ++ sl2 : List Stmt) =
      sl3 ++ (makeAssign bf0 a1 (.Ebinop op a3 a2 tyres) :: sl2) by simp, Kseqlist_app]
    exact ⟨_, .inr ⟨EXEC, by simp only [measure]; omega⟩, .stuckstate _⟩
  | tr_assignop_val _ _ _ _ _ _ _ a1 _ _ a2 _ sl3 a3 _ t bf0 _ _ h1 h2 hrv _ _ _ _ _ _ _ _ _ _ hty1e _ =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue _ GR hr h2
    obtain ⟨le', EXEC, -⟩ := step_tr_rvalof (f := tf) (k := .Kseq
      (.Sset t (.Ecast (.Ebinop op a3 a2 tyres) (Csyntax.typeof l)))
      (.Kseq (makeAssign bf0 a1 (.Etempvar t (Csyntax.typeof l)))
        (Kseqlist (final dst' (makeAssignValue bf0 (.Etempvar t (Csyntax.typeof l))) ++ sl2) tk)))
      GR GR.cenv' hd hev1 hrv hty1.symm
    rw [List.nil_append, List.nil_append, List.append_assoc, Kseqlist_app]
    exact ⟨_, .inr ⟨EXEC, by simp only [measure]; omega⟩, .stuckstate _⟩

theorem estep_postincr {f C id l ty k e m b ofs bf v1 v2 v3 t1 t2 m' v' t tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hl : EvalSimpleLvalue (Csem.globalenv p) e m l b ofs bf)
    (hd : Csem.DerefLoc (Csem.globalenv p) ty m b ofs bf t1 v1)
    (hinc : Cop.semIncrdecr (Csem.globalenv p).genv_cenv id v1 ty m = some v2)
    (hc : Cop.semCast v2 (Cop.incrdecrType ty) ty m = some v3)
    (ha : Csem.AssignLoc (Csem.globalenv p) ty m b ofs bf v3 t2 m' v')
    (hty : ty = Csyntax.typeof l) (ht : t = Eapp t1 t2)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Epostincr id l ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Epostincr id l ty)) k e m) t
      (.ExprState f (C (.Eval v1 ty)) k e m') (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  subst hty ht
  replace hinc : Cop.semIncrdecr tge.genv_cenv id v1 (Csyntax.typeof l) m = some v2 := by
    rw [GR.cenv]; exact hinc
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_postincr_effects _ _ _ _ _ a1 _ sl2' a2 _ bf0 _ _ h1 hrv hty1e _ hi2 hd12 hbf =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    have := is_bitfield_access_sound GR.cenv' hev1 hbf; subst bf0
    obtain ⟨le', EXEC, hev3, hty3, INV⟩ := step_tr_rvalof (f := tf) (k := .Kseq
      (makeAssign bf a1 (translIncrdecr id a2 (Csyntax.typeof l))) (Kseqlist sl2 tk))
      GR GR.cenv' hd hev1 hrv hty1.symm
    obtain ⟨-, -, hev1'⟩ := tr_simple_lvalue _ GR hl (tr_expr_invariant _ h1 (le' := le')
      (fun x hx => INV x (fun hx2 => hd12 x hx hx2)))
    rw [show (([] ++ sl2' ++ [makeAssign bf a1 (translIncrdecr id a2 (Csyntax.typeof l))]) ++ sl2 :
        List Stmt) = sl2' ++ (makeAssign bf a1 (translIncrdecr id a2 (Csyntax.typeof l)) :: sl2) by
      simp, Kseqlist_app]
    exact ⟨_, .inl (star_plus_trans EXEC (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (step_make_assign GR ha hev1'
          (eval_translIncrdecr id hev3 (by rw [hty3, hty1]) hinc)
          (by rw [typeof_translIncrdecr]; exact hc) hty1.symm)) rfl) rfl),
      ms_expr tmps hf (S le' m' _ [] (.tr_val_effect _ _ _ _ _)
        (fun x hx => INV x (fun hx2 => hx (hi2 hx2))) rfl) hk⟩
  | tr_postincr_val _ _ _ _ _ a1 _ bf0 t _ _ h1 _ ht htn1 hty1e hbf =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    have := is_bitfield_access_sound GR.cenv' hev1 hbf; subst bf0
    obtain ⟨-, -, hev1'⟩ := tr_simple_lvalue _ GR hl (tr_expr_invariant _ h1 (le' := le.set t v1)
      (fun x hx => PTree.gso _ _ _ _ (by rintro rfl; exact htn1 hx)))
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_left (step_make_set GR hd hev1 hty1.symm)
          (star_left (Step.skip_seq _ _ _ _ _ _)
            (star_one (step_make_assign GR ha hev1'
              (eval_translIncrdecr id (.Etempvar _ _ _ (PTree.gss _ _ _)) rfl hinc)
              (by rw [typeof_translIncrdecr]; exact hc) hty1.symm)) rfl) rfl) rfl),
      ms_expr tmps hf (S (le.set t v1) m' (.Eval v1 _) _ (tr_val_gen rfl (eval_set_temp ht))
        (set_unchanged ht) rfl) hk⟩

theorem estep_postincr_stuck {f C id l ty k e m b ofs bf v1 t tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hl : EvalSimpleLvalue (Csem.globalenv p) e m l b ofs bf)
    (hd : Csem.DerefLoc (Csem.globalenv p) ty m b ofs bf t v1)
    (hty : ty = Csyntax.typeof l)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Epostincr id l ty)) sl a tmps) :
    SimGoal p tge (.ExprState f (C (.Epostincr id l ty)) k e m) t .Stuckstate
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  subst hty
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_postincr_effects _ _ _ _ _ a1 _ sl2' a2 _ bf0 _ _ h1 hrv hty1e =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    obtain ⟨le', EXEC, -⟩ := step_tr_rvalof (f := tf) (k := .Kseq
      (makeAssign bf0 a1 (translIncrdecr id a2 (Csyntax.typeof l))) (Kseqlist sl2 tk))
      GR GR.cenv' hd hev1 hrv hty1.symm
    rw [show (([] ++ sl2' ++ [makeAssign bf0 a1 (translIncrdecr id a2 (Csyntax.typeof l))]) ++ sl2 :
        List Stmt) = sl2' ++ (makeAssign bf0 a1 (translIncrdecr id a2 (Csyntax.typeof l)) :: sl2) by
      simp, Kseqlist_app]
    exact ⟨_, .inr ⟨EXEC, by simp only [measure]; omega⟩, .stuckstate _⟩
  | tr_postincr_val _ _ _ _ _ a1 _ bf0 t _ _ h1 _ ht htn1 hty1e hbf =>
    subst hty1e
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue _ GR hl h1
    have := is_bitfield_access_sound GR.cenv' hev1 hbf; subst bf0
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (step_make_set GR hd hev1 hty1.symm)) rfl), .stuckstate _⟩

theorem estep_comma {f C r1 r2 ty k e m v tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hr : EvalSimpleRvalue (Csem.globalenv p) e m r1 v)
    (hty : ty = Csyntax.typeof r2)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Ecomma r1 r2 ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Ecomma r1 r2 ty)) k e m) E0 (.ExprState f (C r2) k e m)
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  subst hty
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_comma _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ _ hi2 =>
    have hsl : _ = [] := tr_simple_rvalue _ GR hr h1
    subst hsl
    have hlt := leftcontext_size hC (e1 := r2) (e2 := .Ecomma r1 r2 (Csyntax.typeof r2))
      (by simp only [esize]; omega)
    exact ⟨_, .inr ⟨Smallstep.Star.refl _, by simp only [measure]; omega⟩,
      ms_expr tmps hf (S le m _ _ (tr_expr_monotone _ h2 hi2) (fun _ _ => rfl) rfl) hk⟩

theorem estep_paren {f C r tycast ty k e m v1 v tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C) (hr : EvalSimpleRvalue (Csem.globalenv p) e m r v1)
    (hc : Cop.semCast v1 (Csyntax.typeof r) tycast m = some v)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Eparen r tycast ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Eparen r tycast ty)) k e m) E0 (.ExprState f (C (.Eval v ty)) k e m)
      (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_paren_val _ _ _ _ _ t _ h1 ht =>
    obtain ⟨b, rfl, hty1, hev1⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (Step.set _ _ _ _ _ _ _ _ (.Ecast _ _ _ _ hev1 (hty1 ▸ hc)))) rfl),
      ms_expr tmps hf (S (le.set t v) m _ [] (.tr_val_value _ _ _ _ _ rfl (eval_set_temp ht))
        (set_unchanged ht) rfl) hk⟩
  | tr_paren_effects _ _ _ _ _ _ _ h1 =>
    have hsl : _ = [] := tr_simple_rvalue _ GR hr h1
    subst hsl
    have hlt := leftcontext_size hC (e1 := .Eval v ty) (e2 := .Eparen r tycast ty)
      (by simp only [esize]; omega)
    exact ⟨_, .inr ⟨Smallstep.Star.refl _, by simp only [measure]; omega⟩,
      ms_expr tmps hf (S le m _ [] (.tr_val_effect _ _ _ _ _) (fun _ _ => rfl) rfl) hk⟩
  | tr_paren_set t sd _ _ _ _ _ _ _ h1 ht =>
    obtain ⟨b, rfl, hty1, hev1⟩ := tr_simple_rvalue _ GR hr h1
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (Step.set _ _ _ _ _ _ _ _ (.Ecast _ _ _ _ hev1 (hty1 ▸ hc)))) rfl),
      ms_expr tmps hf (S (le.set t v) m _ _ (.tr_val_set _ _ _ _ _ _ _ rfl (eval_set_temp ht))
        (set_unchanged ht) rfl) hk⟩

theorem estep_call {f C rf rargs ty k e m targs tres cconv vf vargs fd tf le dest sl a tmps tk}
    (FT : FunsTranslated p tge)
    (hC : LeftContext .RV .RV C)
    (hcf : Cop.classifyFun (Csyntax.typeof rf) = .f targs tres cconv)
    (hrf : EvalSimpleRvalue (Csem.globalenv p) e m rf vf)
    (hargs : EvalSimpleList (Csem.globalenv p) e m rargs targs vargs)
    (hfd : Genv.findFunct (Csem.globalenv p).genv_genv vf = some fd)
    (htfd : Csyntax.typeOfFundef fd = .Tfunction targs tres cconv)
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Ecall rf rargs ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Ecall rf rargs ty)) k e m) E0
      (.Callstate fd vargs (.Kcall f e C ty k) m) (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  obtain ⟨tfd, htfind, htr⟩ := FT _ _ hfd
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_call_effects _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_rvalue _ GR hrf h1
    obtain ⟨rfl, hevl⟩ := tr_simple_exprlist _ GR h2 hargs
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (Step.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hty1 ▸ hcf) hev1 hevl htfind
          (by rw [type_of_fundef_preserved htr]; exact htfd))) rfl),
      .callstates _ _ _ _ _ _ htr (.Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ hf hC
        (fun v m' => S le m' (.Eval v ty) [] (.tr_val_effect _ _ _ _ _) (fun _ _ => rfl) rfl) hk)⟩
  | tr_call_val _ _ _ _ _ _ _ _ _ _ t _ _ h1 h2 _ ht =>
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_rvalue _ GR hrf h1
    obtain ⟨rfl, hevl⟩ := tr_simple_exprlist _ GR h2 hargs
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (Step.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hty1 ▸ hcf) hev1 hevl htfind
          (by rw [type_of_fundef_preserved htr]; exact htfd))) rfl),
      .callstates _ _ _ _ _ _ htr (.Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ hf hC
        (fun v m' => S (le.set t v) m' (.Eval v ty) _ (tr_val_gen rfl (eval_set_temp ht))
          (set_unchanged ht) rfl) hk)⟩

theorem estep_builtin {f C ef tyargs rargs ty k e m vargs t vres m' tf le dest sl a tmps tk}
    (hC : LeftContext .RV .RV C)
    (hargs : EvalSimpleList (Csem.globalenv p) e m rargs tyargs vargs)
    (hext : externalCall ef (Csem.globalenv p).genv_genv.toSenv vargs m t vres m')
    (hf : TrFunction p.prog_comp_env f tf)
    (htop : TrTop p.prog_comp_env tge e le m dest (C (.Ebuiltin ef tyargs rargs ty)) sl a tmps)
    (hk : MatchContExp p.prog_comp_env tge dest a k tk) :
    SimGoal p tge (.ExprState f (C (.Ebuiltin ef tyargs rargs ty)) k e m) t
      (.ExprState f (C (.Eval vres ty)) k e m') (.State tf .Sskip (Kseqlist sl tk) e le m) := by
  obtain ⟨dst', sl1, sl2, a', tmp', P, rfl, _, S⟩ := tr_top_leftcontext htop rfl hC
  have hext' : externalCall ef tge.genv_genv.toSenv vargs m t vres m' := by rw [GR.senv]; exact hext
  cases P with
  | tr_top_base _ _ _ _ _ P =>
  cases P with
  | tr_builtin_effects _ _ _ _ _ _ _ _ _ h1 _ =>
    obtain ⟨rfl, hevl⟩ := tr_simple_exprlist _ GR h1 hargs
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (Step.builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hevl hext')) rfl),
      ms_expr tmps hf (S le m' _ [] (.tr_val_effect _ _ _ _ _) (fun _ _ => rfl) rfl) hk⟩
  | tr_builtin_val _ _ _ _ _ _ _ _ t _ _ h1 ht =>
    obtain ⟨rfl, hevl⟩ := tr_simple_exprlist _ GR h1 hargs
    exact ⟨_, .inl (plus_left (Step.skip_seq _ _ _ _ _ _)
        (star_one (Step.builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hevl hext')) rfl),
      ms_expr tmps hf (S (le.set t vres) m' (.Eval vres ty) _ (tr_val_gen rfl (eval_set_temp ht))
        (set_unchanged ht) rfl) hk⟩

/-- `SimplExprproof.estep_simulation` -/
theorem estep_simulation (FT : FunsTranslated p tge) {S1 t S2}
    (h : Estep (Csem.globalenv p) S1 t S2) {S1'} (hm : MatchStates p tge S1 S1') :
    SimGoal p tge S1 t S2 S1' := by
  cases h with
  | expr _ _ _ _ _ _ _ hr hnv hty =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_expr GR hr hnv hty hf htop hk
  | rvalof_volatile _ _ _ _ _ _ _ _ _ _ _ _ hC hl hd hty hvol =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_rvalof_volatile GR hC hl hd hty hvol hf htop hk
  | seqand_true _ _ _ _ _ _ _ _ _ hC hr hb =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_seqand_true GR hC hr hb hf htop hk
  | seqand_false _ _ _ _ _ _ _ _ _ hC hr hb =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_seqand_false GR hC hr hb hf htop hk
  | seqor_true _ _ _ _ _ _ _ _ _ hC hr hb =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_seqor_true GR hC hr hb hf htop hk
  | seqor_false _ _ _ _ _ _ _ _ _ hC hr hb =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_seqor_false GR hC hr hb hf htop hk
  | condition _ _ _ _ _ _ _ _ _ _ _ hC hr hb =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_condition GR hC hr hb hf htop hk
  | assign _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hl hr hc ha hty =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_assign GR hC hl hr hc ha hty hf htop hk
  | assignop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hl hd hr hop hc ha hty ht =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_assignop GR hC hl hd hr hop hc ha hty ht hf htop hk
  | assignop_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hl hd hr _ hty =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ _ htop _ =>
    exact estep_assignop_stuck GR hC hl hd hr hty htop
  | postincr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hl hd hinc hc ha hty ht =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_postincr GR hC hl hd hinc hc ha hty ht hf htop hk
  | postincr_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ hC hl hd _ hty =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ _ htop _ =>
    exact estep_postincr_stuck GR hC hl hd hty htop
  | comma _ _ _ _ _ _ _ _ _ hC hr hty =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_comma GR hC hr hty hf htop hk
  | paren _ _ _ _ _ _ _ _ _ _ hC hr hc =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_paren GR hC hr hc hf htop hk
  | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hcf hrf hargs hfd htfd =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_call GR FT hC hcf hrf hargs hfd htfd hf htop hk
  | builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hC hargs hext =>
    cases hm with | exprstates _ _ _ _ _ _ _ _ _ _ _ _ hf htop hk =>
    exact estep_builtin GR hC hargs hext hf htop hk

end ESTEP

end SimplExpr
end CC
