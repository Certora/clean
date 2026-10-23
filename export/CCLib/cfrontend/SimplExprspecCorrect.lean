/-
  Correctness of the translation functions of `CCLib.cfrontend.SimplExpr` with respect
  to the relational specification of `CCLib.cfrontend.SimplExprspec` — port of the
  second half of `cfrontend/SimplExprspec.v` ("Correctness proof with
  respect to the specification").

  Main results: `transl_meets_spec`, `transl_expr_meets_spec`,
  `transl_expression_meets_spec`, `transl_expr_stmt_meets_spec`,
  `transl_if_meets_spec`, `transl_stmt_meets_spec`, `transl_function_spec`
  and `transl_fundef_spec`.
-/
import CCLib.cfrontend.SimplExprspec
import Lean.Elab.Tactic

namespace CC
namespace SimplExpr

open Destination SetDestination

/-! ## Properties of the monad -/

theorem ple_iff (p q : Positive) : p ≤ q ↔ p.toNat ≤ q.toNat := Iff.rfl

theorem bind_inv {A B : Type} {x : Mon A} {f : A → Mon B} {g : Generator} {b : B}
    {g'' : Generator} {I} (H : Mon.bind x f g = .Res b g'' I) :
    ∃ a g' I1 I2, x g = .Res a g' I1 ∧ f a g' = .Res b g'' I2 := by
  unfold Mon.bind at H
  split at H
  · cases H
  · rename_i a g' i _
    split at H
    · cases H
    · rename_i b' g3 i' _
      cases H
      exact ⟨a, g', i, i', by assumption, by assumption⟩

theorem ret_inv {A : Type} {x : A} {g : Generator} {b : A} {g' : Generator} {I}
    (H : Mon.ret x g = .Res b g' I) : x = b ∧ g = g' := by
  unfold Mon.ret at H; cases H; exact ⟨rfl, rfl⟩

theorem error_inv {A : Type} {msg} {g : Generator} {b : A} {g' : Generator} {I}
    (H : (Mon.error msg : Mon A) g = .Res b g' I) : False := by
  unfold Mon.error at H; cases H

theorem gensym_inv {ty g id g' I} (H : gensym ty g = .Res id g' I) :
    id = g.gen_next ∧ g' = ⟨g.gen_next.succ, (g.gen_next, ty) :: g.gen_trail⟩ := by
  unfold gensym at H; cases H; exact ⟨rfl, rfl⟩

/-! ## Freshness and separation properties -/

/-- `SimplExprspec.within` -/
def within (id : Ident) (g1 g2 : Generator) : Prop :=
  g1.gen_next ≤ id ∧ id < g2.gen_next

theorem ple_toNat {p q : Positive} (h : p ≤ q) : p.toNat ≤ q.toNat := h
theorem plt_toNat {p q : Positive} (h : p < q) : p.toNat < q.toNat := h
theorem within_toNat {id g1 g2} (h : within id g1 g2) :
    g1.gen_next.toNat ≤ id.toNat ∧ id.toNat < g2.gen_next.toNat := h

open Lean Elab Tactic Meta in
/-- `omega` for goals about the order of identifiers and generators: every
    hypothesis `p ≤ q`, `p < q` or `within id g1 g2` is first restated on
    `Positive.toNat`. -/
elab "pos_omega" : tactic => do
  let g ← withMainContext do
    let mut facts : Array Lean.Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      for lem in [``ple_toNat, ``plt_toNat, ``within_toNat] do
        try
          facts := facts.push (← mkAppM lem #[d.toExpr])
        catch _ => pure ()
    let mut g ← getMainGoal
    for e in facts do
      g ← g.assert `hpos (← inferType e) e
    return g
  replaceMainGoal [g]
  evalTactic (← `(tactic| ((try simp only [within, ple_iff, Positive.lt_iff, Positive.toNat_succ]);
                           intros; omega)))

theorem gensym_within {ty g1 id g2 I} (H : gensym ty g1 = .Res id g2 I) : within id g1 g2 := by
  obtain ⟨rfl, rfl⟩ := gensym_inv H
  show _ ∧ _
  simp only [ple_iff, Positive.lt_iff, Positive.toNat_succ]; omega

theorem within_widen {id g1 g2 g1' g2'} (h : within id g1 g2)
    (h1 : g1'.gen_next ≤ g1.gen_next) (h2 : g2.gen_next ≤ g2'.gen_next) : within id g1' g2' := by
  pos_omega

/-- `SimplExprspec.contained` -/
def contained (l : List Ident) (g1 g2 : Generator) : Prop :=
  ∀ id, id ∈ l → within id g1 g2

theorem contained_nil {g1 g2} : contained [] g1 g2 := fun _ h => by cases h

theorem contained_widen {l g1 g2 g1' g2'} (h : contained l g1 g2)
    (h1 : g1'.gen_next ≤ g1.gen_next) (h2 : g2.gen_next ≤ g2'.gen_next) : contained l g1' g2' :=
  fun id hid => within_widen (h id hid) h1 h2

theorem contained_cons {id l g1 g2} (h1 : within id g1 g2) (h2 : contained l g1 g2) :
    contained (id :: l) g1 g2 := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h1
  · exact h2 x hx

theorem contained_app {l1 l2 g1 g2} (h1 : contained l1 g1 g2) (h2 : contained l2 g1 g2) :
    contained (l1 ++ l2) g1 g2 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

theorem mem_within {l g1 g2 x} (h : contained l g1 g2) (hx : x ∈ l) : within x g1 g2 := h x hx

theorem contained_disjoint {g1 l1 g2 l2 g3} (h1 : contained l1 g1 g2) (h2 : contained l2 g2 g3) :
    listDisjoint l1 l2 := by
  intro x hx1 hx2
  have := h1 x hx1; have := h2 x hx2
  pos_omega

theorem contained_notin {g1 l g2 id g3} (h1 : contained l g1 g2) (h2 : within id g2 g3) :
    id ∉ l := by
  intro hx
  have := h1 id hx
  pos_omega

theorem listDisjoint_cons_r {l1 l2 : List Ident} {a} (h1 : listDisjoint l1 l2) (h2 : a ∉ l1) :
    listDisjoint l1 (a :: l2) := by
  intro x hx1 hx2
  rcases List.mem_cons.mp hx2 with rfl | hx2
  · exact h2 hx1
  · exact h1 x hx1 hx2

/-! ## Properties of destinations -/

/-- `SimplExprspec.dest_below` -/
def destBelow (dst : Destination) (g : Generator) : Prop :=
  match dst with
  | .For_set sd => sdTemp sd < g.gen_next
  | _ => True

theorem destBelow_le {dst g1 g2} (h : destBelow dst g1) (h' : g1.gen_next ≤ g2.gen_next) :
    destBelow dst g2 := by
  cases dst <;> simp only [destBelow] at * <;> pos_omega

/-- `SimplExprspec.good_temp_for_sd` -/
def goodTempForSd (ty : Ty) (tmp : Ident) (sd : SetDestination) (g1 g2 g3 : Generator) : Prop :=
  sdTemp sd < g1.gen_next ∧ g1.gen_next ≤ g2.gen_next ∧ g2.gen_next ≤ g3.gen_next ∧
  if ty = sdHeadType sd then tmp = sdTemp sd else within tmp g2 g3

theorem temp_for_sd_charact {ty tmp sd g1 g2 g3 I} (h1 : destBelow (For_set sd) g1)
    (h2 : tempForSd ty sd g2 = .Res tmp g3 I) (h3 : g1.gen_next ≤ g2.gen_next) :
    goodTempForSd ty tmp sd g1 g2 g3 := by
  unfold tempForSd at h2
  unfold goodTempForSd
  by_cases hty : ty = sdHeadType sd
  · rw [if_pos hty] at h2
    obtain ⟨rfl, rfl⟩ := ret_inv h2
    exact ⟨h1, h3, Mon.ple_refl _, by rw [if_pos hty]⟩
  · rw [if_neg hty] at h2
    exact ⟨h1, h3, I, by rw [if_neg hty]; exact gensym_within h2⟩

theorem dest_for_set_cons_below {tycast ty tmp sd g1 g2 g3}
    (h : goodTempForSd ty tmp sd g1 g2 g3) : destBelow (For_set (SDcons tycast ty tmp sd)) g3 := by
  obtain ⟨P, Q, R, S⟩ := h
  show tmp < g3.gen_next
  split at S
  · subst S; pos_omega
  · pos_omega

theorem sd_temp_notin {sd g1 g2 l} (h1 : destBelow (For_set sd) g1) (h2 : contained l g1 g2) :
    sdTemp sd ∉ l := by
  intro hx
  have := h2 _ hx
  simp only [destBelow] at h1
  pos_omega

/-- `SimplExprspec.used_temp_for_sd` -/
def usedTempForSd (ty : Ty) (tmp : Ident) (sd : SetDestination) : List Ident :=
  if ty = sdHeadType sd then [] else [tmp]

theorem temp_for_sd_disj {tmp1 tmp2 ty t sd g1 g2 g3 g4}
    (h : goodTempForSd ty t sd g1 g2 g3) (h1 : contained tmp1 g1 g2) (h2 : contained tmp2 g3 g4) :
    listDisjoint tmp1 (t :: tmp2) := by
  obtain ⟨P, Q, R, S⟩ := h
  apply listDisjoint_cons_r
  · exact contained_disjoint h1 (contained_widen h2 R (Mon.ple_refl _))
  · split at S
    · subst S; exact sd_temp_notin P h1
    · exact contained_notin h1 S

theorem temp_for_sd_in {tmp ty t sd g1 g2 g3} (h : goodTempForSd ty t sd g1 g2 g3) :
    t ∈ sdTemp sd :: (usedTempForSd ty t sd ++ tmp) := by
  obtain ⟨_, _, _, S⟩ := h
  unfold usedTempForSd
  split at S
  · subst S; exact List.mem_cons_self
  · rename_i hty; rw [if_neg hty]; simp

theorem temp_for_sd_contained {ty t sd g1 g2 g3} (h : goodTempForSd ty t sd g1 g2 g3) :
    contained (usedTempForSd ty t sd) g2 g3 := by
  obtain ⟨_, _, _, S⟩ := h
  unfold usedTempForSd
  split at S
  · rename_i hty; rw [if_pos hty]; exact contained_nil
  · rename_i hty; rw [if_neg hty]; exact contained_cons S contained_nil

/-! ## Correctness of the translation functions -/

theorem finish_meets_spec_1 {dst sl a sl' a'} (h : finish dst sl a = (sl', a')) :
    sl' = sl ++ final dst a := by
  cases dst <;> simp only [finish, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [final]

theorem finish_meets_spec_2 {dst sl a sl' a'} (h : finish dst sl a = (sl', a')) : a' = a := by
  cases dst <;> simp only [finish, Prod.mk.injEq] at h <;> exact h.2.symm

/-- `SimplExprspec.add_dest` -/
def addDest (dst : Destination) (tmps : List Ident) : List Ident :=
  match dst with
  | .For_set sd => sdTemp sd :: tmps
  | _ => tmps

theorem addDest_incl (dst tmps) : tmps ⊆ addDest dst tmps := by
  cases dst <;> simp [addDest]

section CE

variable (ce : CompositeEnv)

theorem tr_expr_add_dest {le dst r sl a tmps} (h : TrExpr ce le dst r sl a tmps) :
    TrExpr ce le dst r sl a (addDest dst tmps) :=
  tr_expr_monotone ce h (addDest_incl dst tmps)

theorem is_bitfield_access_meets_spec {l g bf g' I}
    (h : isBitfieldAccess ce l g = .Res bf g' I) : TrIsBitfieldAccess ce l bf := by
  have AUX : ∀ fn id i, isBitfieldAccessAux ce fn id i g = .Res bf g' I →
      ∃ co ofs, ce.get id = some co ∧ fn ce i co.co_members = .OK (ofs, bf) := by
    intro fn id i h
    unfold isBitfieldAccessAux at h
    cases hc : ce.get id with
    | none => simp only [hc] at h; exact (error_inv h).elim
    | some co =>
      simp only [hc] at h
      cases hfn : fn ce i co.co_members with
      | OK p =>
        obtain ⟨ofs, bf1⟩ := p
        simp only [hfn] at h
        obtain ⟨rfl, -⟩ := ret_inv h
        exact ⟨co, ofs, rfl, hfn⟩
      | Error _ => simp only [hfn] at h; exact (error_inv h).elim
  unfold TrIsBitfieldAccess
  cases l with
  | Efield r f t =>
    simp only [isBitfieldAccess] at h
    revert h
    cases hty : typeof r <;> intro h <;> simp only at h <;> (try exact (error_inv h).elim)
    · obtain ⟨co, ofs, h1, h2⟩ := AUX _ _ _ h
      exact ⟨co, ofs, by simp only [hty]; exact ⟨h1, h2⟩⟩
    · obtain ⟨co, ofs, h1, h2⟩ := AUX _ _ _ h
      exact ⟨co, ofs, by simp only [hty]; exact ⟨h1, h2⟩⟩
  | _ => simp only [isBitfieldAccess] at h; exact (ret_inv h).1.symm

theorem transl_valof_meets_spec {ty a g sl b g' I}
    (h : translValof ce ty a g = .Res (sl, b) g' I) :
    ∃ tmps, TrRvalof ce ty a sl b tmps ∧ contained tmps g g' := by
  unfold translValof at h
  split at h
  · rename_i hv
    simp only [Mon.bind_eq] at h
    obtain ⟨t, g1, I1, I2, h1, h⟩ := bind_inv h
    obtain ⟨bf, g2, I3, I4, h2, h⟩ := bind_inv h
    obtain ⟨he, rfl⟩ := ret_inv h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨[t], .tr_rvalof_vol _ _ _ _ _ hv List.mem_cons_self
      (is_bitfield_access_meets_spec ce h2), ?_⟩
    exact contained_cons (within_widen (gensym_within h1) (Mon.ple_refl _) I3) contained_nil
  · rename_i hv
    obtain ⟨he, rfl⟩ := ret_inv h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨[], .tr_rvalof_nonvol _ _ _ (by simpa using hv), contained_nil⟩

theorem contained_disjoint' {l1 l2 a b c d} (h1 : contained l1 a b) (h2 : contained l2 c d)
    (h : b.gen_next ≤ c.gen_next) : listDisjoint l1 l2 := by
  intro x hx1 hx2
  have := h1 x hx1; have := h2 x hx2
  pos_omega

theorem contained_notin' {l a b t c d} (h1 : contained l a b) (h2 : within t c d)
    (h : b.gen_next ≤ c.gen_next) : t ∉ l := by
  intro hx
  have := h1 t hx
  pos_omega

theorem tr_sl_eq {le dst r sl a tmps sl'} (h : TrExpr ce le dst r sl a tmps) (e : sl = sl') :
    TrExpr ce le dst r sl' a tmps := e ▸ h

/-- Invert one `bind` of the generator monad. -/
macro "minv " H:ident x:ident E:ident : tactic =>
  `(tactic| (obtain ⟨$x:ident, _, _, _, $E:ident, $H:ident⟩ := bind_inv $H; try simp only at $H:ident))

/-- Invert one `bind` of the generator monad whose result is a pair. -/
macro "minv2 " H:ident x:ident y:ident E:ident : tactic =>
  `(tactic| (obtain ⟨⟨$x:ident, $y:ident⟩, _, _, _, $E:ident, $H:ident⟩ := bind_inv $H;
             try simp only at $H:ident))

/-- Invert the final `ret` of a translation. -/
macro "mret " H:ident : tactic =>
  `(tactic| (obtain ⟨he, hg⟩ := ret_inv $H; subst hg;
             first
             | (have h1 := finish_meets_spec_1 he; have h2 := finish_meets_spec_2 he;
                subst h1; subst h2)
             | (obtain ⟨h1, h2⟩ := Prod.mk.inj he; subst h1; subst h2)
             | subst he))

/-- Close a `contained` goal from the `contained`/`within` hypotheses, by
    recursion on the shape of the list. -/
syntax "contained_tac" : tactic

open Lean Elab Tactic Meta in
/-- Implementation of `contained_tac`. -/
partial def containedTac : TacticM Unit := do
  let kind ← withMainContext do
    let goal ← getMainGoal
    let ty ← instantiateMVars (← goal.getType)
    match ty.getAppFnArgs with
    | (``contained, #[l, _, _]) =>
      let l ← whnfR (← instantiateMVars l)
      match l.getAppFnArgs with
      | (``List.nil, _) => return 0
      | (``List.cons, _) => return 1
      | (``HAppend.hAppend, _) => return 2
      | _ => return 3
    | _ => throwError "contained_tac: goal is not `contained _ _ _`"
  match kind with
  | 0 => evalTactic (← `(tactic| exact contained_nil))
  | 1 =>
    evalTactic (← `(tactic| (focus (refine contained_cons ?_ ?_; (focus (apply within_widen; assumption; all_goals pos_omega)); contained_tac))))
  | 2 => evalTactic (← `(tactic| (focus (refine contained_app ?_ ?_ <;> contained_tac))))
  | _ => evalTactic (← `(tactic| (focus (apply contained_widen; assumption; all_goals pos_omega))))

elab_rules : tactic
  | `(tactic| contained_tac) => containedTac

/-- Close a `listDisjoint` goal between temporaries created at different
    times. -/
macro "disj_tac" : tactic =>
  `(tactic| first
    | (focus (apply contained_disjoint'; assumption; assumption; all_goals pos_omega))
    | (focus (apply listDisjoint_cons_r; (focus (apply contained_disjoint'; assumption; assumption; all_goals pos_omega)); (focus (apply contained_notin'; assumption; assumption; all_goals pos_omega)))))

/-- Close a `t ∉ l` goal. -/
macro "notin_tac" : tactic =>
  `(tactic| (focus (apply contained_notin'; assumption; assumption; all_goals pos_omega)))

/-- Close an inclusion or membership goal between lists of temporaries. -/
macro "incl_tac" : tactic =>
  `(tactic| first
    | (simp [addDest, sdTemp]; done)
    | (intro y hy; (try simp only [addDest, sdTemp] at hy); simp [addDest, sdTemp, hy]; done)
    | (intro y hy; (try simp only [addDest, sdTemp] at hy);
       rw [List.mem_cons] at hy; rcases hy with h | h <;> simp [addDest, sdTemp, h]; done))

/-- Close any of the side conditions about temporaries. -/
macro "side_tac" : tactic =>
  `(tactic| first | contained_tac | disj_tac | notin_tac | incl_tac)

theorem incl_sd_cons {ty t sd g1 g2 g3 tycast ty'} {tmp2 rest : List Ident}
    (G : goodTempForSd ty t sd g1 g2 g3) (h : tmp2 ⊆ rest) :
    addDest (For_set (SDcons tycast ty' t sd)) tmp2 ⊆
      addDest (For_set sd) (usedTempForSd ty t sd ++ rest) := by
  intro y hy
  rcases List.mem_cons.mp hy with hy | hy
  · subst hy; exact temp_for_sd_in G
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ (h hy))

theorem destBelow_set_base {tycast ty t g1 g2} (h : within t g1 g2) :
    destBelow (For_set (SDbase tycast ty t)) g2 := h.2

/-- `transl_expr` satisfies the specification for the expression `r`. -/
def ExprSpec (r : Csyntax.Expr) : Prop :=
  ∀ (dst : Destination) (g : Generator) (sl : List Stmt) (a : Expr) (g' : Generator)
    (I : g.gen_next ≤ g'.gen_next),
    translExpr ce dst r g = .Res (sl, a) g' I → destBelow dst g →
    ∃ tmps, (∀ le, TrExpr ce le dst r sl a (addDest dst tmps)) ∧ contained tmps g g'

/-- `transl_exprlist` satisfies the specification for the list `rl`. -/
def ExprlistSpec (rl : Csyntax.ExprList) : Prop :=
  ∀ (g : Generator) (sl : List Stmt) (al : List Expr) (g' : Generator)
    (I : g.gen_next ≤ g'.gen_next),
    translExprlist ce rl g = .Res (sl, al) g' I →
    ∃ tmps, (∀ le, TrExprlist ce le rl sl al tmps) ∧ contained tmps g g'

end CE

end SimplExpr
end CC
