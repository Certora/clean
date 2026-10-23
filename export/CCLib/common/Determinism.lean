/-
  Determinism of the Clight step relation — the analogue of
  `Clight.semantics_determinate` (`cfrontend/Clight.v`).

  `CCLib.cfrontend.Clight`'s header records that the one lemma of `Clight.v`,
  `semantics_receptive`, was skipped as pass-proof support; `semantics_determinate`
  went with it, because `ec_determ` is a field of the `extcall_properties` record
  that `CCLib.common.Events`' header lists as skipped.  This file supplies the missing
  half.  Nothing in `CCLib` changes: `Step`, `EvalExpr`, `AssignLoc`,
  `externalCall` and the two base axioms are untouched, and the new material in
  `CCLib.common.Events` is appended rather than woven in.

  ## What it rests on

  * `CC.externalFunctionsSemDeterm` and `CC.inlineAssemblySemDeterm`
    (`CCLib.common.Events`) — `ec_determ` + `ec_trace_length` for the two uninterpreted
    externals, mirroring CompCert's `external_functions_properties` /
    `inline_assembly_properties`.  These are the only axioms this development
    adds, and the file that states them also records the consistency witness.
  * `Genv.symbInjective_globalenv` (`CCLib.common.Globalenvs`) — the `genv_vars_inj`
    invariant CompCert's proof-carrying `Genv.t` keeps and this port dropped.
    It is recovered as a lemma about `globalenv`, exactly as the `Globalenvs`
    header promised, so determinism needs no hypothesis about the environment.

  Of `Step`'s 25 rules, only the `EF_external`/`EF_builtin`/`EF_runtime`/
  `EF_inline_asm` family is genuinely nondeterministic; the other 24 are
  discriminated by the statement, by the continuation, or by a *function*
  (`accessMode`, `typeof`, `Cop.boolVal`, `Cop.semSwitchArg`, `findLabel`,
  `isCallCont`, `Mem.load`/`store`/`alloc`/`free`).  That is why the double case
  analysis in `step_determ` leaves only twelve goals with content.

  ## The one technical trap

  `EvalExpr` and `EvalLvalue` are a *mutual* inductive, and Lean 4's mutual
  recursors are awkward in tactic mode.  `eval_determ` therefore inducts on the
  **expression** — a plain inductive — carrying both claims as a conjunction, and
  inverts the derivations inside each syntactic case.  Do not try to induct on
  the derivations.

  Several proofs go through hand-written inversion lemmas (`volatileLoad_inv`,
  `loadBitfield_inv`, …) rather than a second `cases`.  Two reasons: `cases` on an
  indexed family leaves a binder count that depends on which indices happen to be
  free variables, which is fragile to hard-code; and for `ExtcallMallocSem` the
  argument list is `[Val.Vptrofs sz]`, so dependent elimination cannot recover
  `sz` at all (see `extcallMallocSem_inv`).
-/
import CCLib.cfrontend.ClightExecSound

namespace CC

/-! ## Bitfield accesses (`Cop.load_bitfield` / `Cop.store_bitfield`) -/

theorem loadBitfield_inv {ty sz sg pos width m addr v}
    (h : Cop.LoadBitfield ty sz sg pos width m addr v) :
    ∃ c, Mem.loadv (Cop.chunkForCarrier sz) m addr = some (.Vint c)
      ∧ v = .Vint (Cop.bitfieldExtract sz sg pos width c) := by
  cases h; exact ⟨_, by assumption, rfl⟩

theorem loadBitfield_determ {ty sz sg pos width m addr v1 v2}
    (h1 : Cop.LoadBitfield ty sz sg pos width m addr v1)
    (h2 : Cop.LoadBitfield ty sz sg pos width m addr v2) : v1 = v2 := by
  obtain ⟨c1, hl1, hv1⟩ := loadBitfield_inv h1
  obtain ⟨c2, hl2, hv2⟩ := loadBitfield_inv h2
  rw [hl1] at hl2
  injection hl2 with hl2
  injection hl2 with hl2
  subst hl2; subst hv1; subst hv2; rfl

theorem storeBitfield_inv {ty sz sg pos width m addr v m' v'}
    (h : Cop.StoreBitfield ty sz sg pos width m addr v m' v') :
    ∃ c n, v = .Vint n
      ∧ Mem.loadv (Cop.chunkForCarrier sz) m addr = some (.Vint c)
      ∧ Mem.storev (Cop.chunkForCarrier sz) m addr
          (.Vint (Integers.Int.bitfield_insert (Cop.firstBit sz pos width).toNat
                    width.toNat c n)) = some m'
      ∧ v' = .Vint (Cop.bitfieldNormalize sz sg width n) := by
  cases h; exact ⟨_, _, rfl, by assumption, by assumption, rfl⟩

theorem storeBitfield_determ {ty sz sg pos width m addr v m1 v1 m2 v2}
    (h1 : Cop.StoreBitfield ty sz sg pos width m addr v m1 v1)
    (h2 : Cop.StoreBitfield ty sz sg pos width m addr v m2 v2) : m1 = m2 ∧ v1 = v2 := by
  obtain ⟨c1, n1, hv1, hl1, hs1, hr1⟩ := storeBitfield_inv h1
  obtain ⟨c2, n2, hv2, hl2, hs2, hr2⟩ := storeBitfield_inv h2
  subst hv1
  injection hv2 with hn; subst hn
  rw [hl1] at hl2
  injection hl2 with hl2
  injection hl2 with hl2
  subst hl2
  rw [hs1] at hs2
  injection hs2 with hs2
  exact ⟨hs2, by rw [hr1, hr2]⟩

theorem derefLoc_determ {ty m b ofs bf v1 v2}
    (h1 : DerefLoc ty m b ofs bf v1) (h2 : DerefLoc ty m b ofs bf v2) : v1 = v2 := by
  cases h1 <;> cases h2 <;> try simp_all
  rename_i hb1 hb2
  exact loadBitfield_determ hb1 hb2

theorem assignLoc_determ {ce ty m b ofs bf v m1 m2}
    (h1 : AssignLoc ce ty m b ofs bf v m1) (h2 : AssignLoc ce ty m b ofs bf v m2) :
    m1 = m2 := by
  cases h1 <;> cases h2 <;> try simp_all
  rename_i _ hb1 _ hb2
  exact (storeBitfield_determ hb1 hb2).1

/-! ## Expression evaluation

`EvalExpr` and `EvalLvalue` are a *mutual* inductive, and Lean 4's mutual
recursors are awkward in tactic mode.  The induction below is therefore on the
**expression**, which is a plain inductive, carrying both claims as a
conjunction; `cases` then inverts the two derivations inside each syntactic
case.  Every case is discriminated either by the syntax or by a function
(`accessMode`, `typeof`, `Cop.semBinaryOperation`, `fieldOffset`, `Mem.loadv`), so
nothing here needs an extra hypothesis. -/

theorem eval_determ (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) :
    ∀ a : Expr,
      (∀ v1 v2, EvalExpr ge e le m a v1 → EvalExpr ge e le m a v2 → v1 = v2)
      ∧ (∀ b1 o1 bf1 b2 o2 bf2,
           EvalLvalue ge e le m a b1 o1 bf1 → EvalLvalue ge e le m a b2 o2 bf2 →
           b1 = b2 ∧ o1 = o2 ∧ bf1 = bf2) := by
  intro a
  induction a with
  | Econst_int i ty =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Econst_int _ _ =>
            cases h2 with
            | Econst_int _ _ => rfl
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Econst_float f ty =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Econst_float _ _ =>
            cases h2 with
            | Econst_float _ _ => rfl
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Econst_single f ty =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Econst_single _ _ =>
            cases h2 with
            | Econst_single _ _ => rfl
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Econst_long i ty =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Econst_long _ _ =>
            cases h2 with
            | Econst_long _ _ => rfl
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Esizeof t1 ty =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Esizeof _ _ =>
            cases h2 with
            | Esizeof _ _ => rfl
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Ealignof t1 ty =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Ealignof _ _ =>
            cases h2 with
            | Ealignof _ _ => rfl
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Etempvar id ty =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Etempvar _ _ _ hg1 =>
            cases h2 with
            | Etempvar _ _ _ hg2 =>
                rw [hg1] at hg2; injection hg2 with hg2
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Evar id ty =>
      have hlv : ∀ b1 o1 bf1 b2 o2 bf2,
          EvalLvalue ge e le m (.Evar id ty) b1 o1 bf1 →
          EvalLvalue ge e le m (.Evar id ty) b2 o2 bf2 →
          b1 = b2 ∧ o1 = o2 ∧ bf1 = bf2 := by
        intro _ _ _ _ _ _ h1 h2
        cases h1 with
        | Evar_local _ _ _ hg1 =>
            cases h2 with
            | Evar_local _ _ _ hg2 =>
                rw [hg1] at hg2
                simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hg2
                exact ⟨hg2, rfl, rfl⟩
            | Evar_global _ _ _ hn2 _ => rw [hg1] at hn2; exact absurd hn2 (by simp)
        | Evar_global _ _ _ hn1 hs1 =>
            cases h2 with
            | Evar_local _ _ _ hg2 => rw [hg2] at hn1; exact absurd hn1 (by simp)
            | Evar_global _ _ _ _ hs2 =>
                rw [hs1] at hs2; injection hs2 with hs2
                exact ⟨hs2, rfl, rfl⟩
      refine ⟨?_, hlv⟩
      intro _ _ h1 h2
      cases h1 with
      | Elvalue _ _ _ _ _ hl1 hd1 =>
          cases h2 with
          | Elvalue _ _ _ _ _ hl2 hd2 =>
              obtain ⟨hb, ho, hbf⟩ := hlv _ _ _ _ _ _ hl1 hl2
              subst hb; subst ho; subst hbf
              exact derefLoc_determ hd1 hd2
  | Ederef a ty ih =>
      have hlv : ∀ b1 o1 bf1 b2 o2 bf2,
          EvalLvalue ge e le m (.Ederef a ty) b1 o1 bf1 →
          EvalLvalue ge e le m (.Ederef a ty) b2 o2 bf2 →
          b1 = b2 ∧ o1 = o2 ∧ bf1 = bf2 := by
        intro _ _ _ _ _ _ h1 h2
        cases h1 with
        | Ederef _ _ _ _ he1 =>
            cases h2 with
            | Ederef _ _ _ _ he2 =>
                have hp := ih.1 _ _ he1 he2
                injection hp with hb ho
                exact ⟨hb, ho, rfl⟩
      refine ⟨?_, hlv⟩
      intro _ _ h1 h2
      cases h1 with
      | Elvalue _ _ _ _ _ hl1 hd1 =>
          cases h2 with
          | Elvalue _ _ _ _ _ hl2 hd2 =>
              obtain ⟨hb, ho, hbf⟩ := hlv _ _ _ _ _ _ hl1 hl2
              subst hb; subst ho; subst hbf
              exact derefLoc_determ hd1 hd2
  | Efield a fld ty ih =>
      have hlv : ∀ b1 o1 bf1 b2 o2 bf2,
          EvalLvalue ge e le m (.Efield a fld ty) b1 o1 bf1 →
          EvalLvalue ge e le m (.Efield a fld ty) b2 o2 bf2 →
          b1 = b2 ∧ o1 = o2 ∧ bf1 = bf2 := by
        intro _ _ _ _ _ _ h1 h2
        cases h1 with
        | Efield_struct _ _ _ _ _ _ _ _ _ _ he1 hty1 hco1 hfo1 =>
            cases h2 with
            | Efield_struct _ _ _ _ _ _ _ _ _ _ he2 hty2 hco2 hfo2 =>
                have hp := ih.1 _ _ he1 he2
                injection hp with hb ho
                subst hb; subst ho
                rw [hty1] at hty2
                injection hty2 with hid _
                subst hid
                rw [hco1] at hco2
                injection hco2 with hco2
                subst hco2
                rw [hfo1] at hfo2
                injection hfo2 with hfo2
                injection hfo2 with hd hbf
                exact ⟨rfl, by rw [hd], hbf⟩
            | Efield_union _ _ _ _ _ _ _ _ _ _ _ hty2 _ _ =>
                rw [hty1] at hty2; exact absurd hty2 (by simp)
        | Efield_union _ _ _ _ _ _ _ _ _ _ he1 hty1 hco1 hfo1 =>
            cases h2 with
            | Efield_struct _ _ _ _ _ _ _ _ _ _ _ hty2 _ _ =>
                rw [hty1] at hty2; exact absurd hty2 (by simp)
            | Efield_union _ _ _ _ _ _ _ _ _ _ he2 hty2 hco2 hfo2 =>
                have hp := ih.1 _ _ he1 he2
                injection hp with hb ho
                subst hb; subst ho
                rw [hty1] at hty2
                injection hty2 with hid _
                subst hid
                rw [hco1] at hco2
                injection hco2 with hco2
                subst hco2
                rw [hfo1] at hfo2
                injection hfo2 with hfo2
                injection hfo2 with hd hbf
                exact ⟨rfl, by rw [hd], hbf⟩
      refine ⟨?_, hlv⟩
      intro _ _ h1 h2
      cases h1 with
      | Elvalue _ _ _ _ _ hl1 hd1 =>
          cases h2 with
          | Elvalue _ _ _ _ _ hl2 hd2 =>
              obtain ⟨hb, ho, hbf⟩ := hlv _ _ _ _ _ _ hl1 hl2
              subst hb; subst ho; subst hbf
              exact derefLoc_determ hd1 hd2
  | Eaddrof a ty ih =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Eaddrof _ _ _ _ hl1 =>
            cases h2 with
            | Eaddrof _ _ _ _ hl2 =>
                obtain ⟨hb, ho, _⟩ := ih.2 _ _ _ _ _ _ hl1 hl2
                rw [hb, ho]
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Eunop op a ty ih =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Eunop _ _ _ _ _ he1 hs1 =>
            cases h2 with
            | Eunop _ _ _ _ _ he2 hs2 =>
                have hv := ih.1 _ _ he1 he2
                subst hv
                rw [hs1] at hs2; injection hs2 with hs2
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Ebinop op a1 a2 ty ih1 ih2 =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Ebinop _ _ _ _ _ _ _ ha1 hb1 hs1 =>
            cases h2 with
            | Ebinop _ _ _ _ _ _ _ ha2 hb2 hs2 =>
                have e1 := ih1.1 _ _ ha1 ha2
                have e2 := ih2.1 _ _ hb1 hb2
                subst e1; subst e2
                rw [hs1] at hs2; injection hs2 with hs2
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1
  | Ecast a ty ih =>
      refine ⟨?_, ?_⟩
      · intro _ _ h1 h2
        cases h1 with
        | Ecast _ _ _ _ he1 hs1 =>
            cases h2 with
            | Ecast _ _ _ _ he2 hs2 =>
                have hv := ih.1 _ _ he1 he2
                subst hv
                rw [hs1] at hs2; injection hs2 with hs2
            | Elvalue _ _ _ _ _ hlv _ => cases hlv
        | Elvalue _ _ _ _ _ hlv _ => cases hlv
      · intro _ _ _ _ _ _ h1 _; cases h1

/-- `EvalExpr` is single-valued. -/
theorem evalExpr_determ {ge e le m a v1 v2}
    (h1 : EvalExpr ge e le m a v1) (h2 : EvalExpr ge e le m a v2) : v1 = v2 :=
  (eval_determ ge e le m a).1 _ _ h1 h2

/-- `EvalLvalue` is single-valued. -/
theorem evalLvalue_determ {ge e le m a b1 o1 bf1 b2 o2 bf2}
    (h1 : EvalLvalue ge e le m a b1 o1 bf1) (h2 : EvalLvalue ge e le m a b2 o2 bf2) :
    b1 = b2 ∧ o1 = o2 ∧ bf1 = bf2 :=
  (eval_determ ge e le m a).2 _ _ _ _ _ _ h1 h2

theorem evalExprlist_determ {ge e le m al tyl vl1}
    (h1 : EvalExprlist ge e le m al tyl vl1) :
    ∀ vl2, EvalExprlist ge e le m al tyl vl2 → vl1 = vl2 := by
  induction h1 with
  | nil => intro _ h2; cases h2; rfl
  | cons _ _ _ _ _ _ _ he1 hc1 _ ih =>
      intro _ h2
      cases h2 with
      | cons _ _ _ _ _ _ _ he2 hc2 hl2 =>
          have hv := evalExpr_determ he1 he2
          subst hv
          rw [hc1] at hc2
          injection hc2 with hc2
          rw [hc2, ih _ hl2]

/-! ## Function entry -/

theorem allocVariables_determ {ce en m vars e1 m1}
    (h1 : AllocVariables ce en m vars e1 m1) :
    ∀ e2 m2, AllocVariables ce en m vars e2 m2 → e1 = e2 ∧ m1 = m2 := by
  induction h1 with
  | nil => intro _ _ h2; cases h2; exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ _ _ _ _ ha1 _ ih =>
      intro _ _ h2
      cases h2 with
      | cons _ _ _ _ _ _ _ _ _ ha2 hr2 =>
          rw [ha1] at ha2
          simp only [Prod.mk.injEq] at ha2
          obtain ⟨hm, hb⟩ := ha2
          subst hm; subst hb
          exact ih _ _ hr2

theorem bindParameters_determ {ce en m params vl m1}
    (h1 : BindParameters ce en m params vl m1) :
    ∀ m2, BindParameters ce en m params vl m2 → m1 = m2 := by
  induction h1 with
  | nil => intro _ h2; cases h2; rfl
  | cons _ _ _ _ _ _ _ _ _ hg1 hal1 _ ih =>
      intro _ h2
      cases h2 with
      | cons _ _ _ _ _ _ _ _ _ hg2 hal2 hr2 =>
          rw [hg1] at hg2
          simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hg2
          subst hg2
          have hm := assignLoc_determ hal1 hal2
          subst hm
          exact ih _ hr2

theorem functionEntry1_determ {ge f vargs m e1 le1 m1 e2 le2 m2}
    (h1 : FunctionEntry1 ge f vargs m e1 le1 m1)
    (h2 : FunctionEntry1 ge f vargs m e2 le2 m2) :
    e1 = e2 ∧ le1 = le2 ∧ m1 = m2 := by
  cases h1 with
  | intro _ _ hav1 hbp1 hle1 =>
      cases h2 with
      | intro _ _ hav2 hbp2 hle2 =>
          obtain ⟨he, hm⟩ := allocVariables_determ hav1 _ _ hav2
          subst he; subst hm
          exact ⟨rfl, by rw [hle1, hle2], bindParameters_determ hbp1 _ hbp2⟩

theorem functionEntry2_determ {ge f vargs m e1 le1 m1 e2 le2 m2}
    (h1 : FunctionEntry2 ge f vargs m e1 le1 m1)
    (h2 : FunctionEntry2 ge f vargs m e2 le2 m2) :
    e1 = e2 ∧ le1 = le2 ∧ m1 = m2 := by
  cases h1 with
  | intro _ _ _ hav1 hbt1 =>
      cases h2 with
      | intro _ _ _ hav2 hbt2 =>
          obtain ⟨he, hm⟩ := allocVariables_determ hav1 _ _ hav2
          rw [hbt1] at hbt2
          injection hbt2 with hbt2
          exact ⟨he, hbt2, hm⟩

/-- What `Step`'s `functionEntry` parameter must satisfy for the relation to be
    determinate.  Both of Clight's calling conventions do. -/
def EntryDeterm (fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop) : Prop :=
  ∀ f vargs m e1 le1 m1 e2 le2 m2,
    fe f vargs m e1 le1 m1 → fe f vargs m e2 le2 m2 → e1 = e2 ∧ le1 = le2 ∧ m1 = m2

theorem entryDeterm_functionEntry1 (ge : CGenv) : EntryDeterm (FunctionEntry1 ge) :=
  fun _ _ _ _ _ _ _ _ _ h1 h2 => functionEntry1_determ h1 h2

theorem entryDeterm_functionEntry2 (ge : CGenv) : EntryDeterm (FunctionEntry2 ge) :=
  fun _ _ _ _ _ _ _ _ _ h1 h2 => functionEntry2_determ h1 h2

set_option maxHeartbeats 2000000 in
theorem step_determ {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hfe : EntryDeterm fe)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective)
    {s t1 s1 t2 s2} (h1 : Step ge fe s t1 s1) (h2 : Step ge fe s t2 s2) :
    MatchTraces (Genv.toSenv ge.genv_genv) t1 t2 ∧ (t1 = t2 → s1 = s2) := by
  cases h1 <;> cases h2 <;>
    try (first
          | exact ⟨MatchTraces.nil, fun _ => rfl⟩
          | (exfalso; simp_all [isCallCont]; done))
  -- The twelve genuinely-overlapping pairs: same rule twice.  Everything else
  -- was discriminated by the statement, the continuation, or `isCallCont`.
  case assign.assign =>
    rename_i hlv1 he1 hc1 hal1 _ _ _ _ _ _ hal2 hc2 hlv2 he2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    obtain ⟨hb, ho, hbf⟩ := evalLvalue_determ hlv1 hlv2
    subst hb; subst ho; subst hbf
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hc1] at hc2
    simp only [Option.some.injEq] at hc2
    subst hc2
    rw [assignLoc_determ hal1 hal2]
  case set.set =>
    rename_i _ he1 _ he2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    rw [evalExpr_determ he1 he2]
  case call.call =>
    rename_i hcf1 he1 hel1 hff1 _ _ _ _ _ _ _ hff2 _ hcf2 he2 hel2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    rw [hcf1] at hcf2
    simp only [Cop.FunCase.f.injEq] at hcf2
    obtain ⟨e1, e2, e3⟩ := hcf2
    subst e1; subst e2; subst e3
    have hvf := evalExpr_determ he1 he2
    subst hvf
    have hva := evalExprlist_determ hel1 _ hel2
    subst hva
    rw [hff1] at hff2
    simp only [Option.some.injEq] at hff2
    subst hff2
    rfl
  case builtin.builtin =>
    rename_i hel1 hec1 _ _ _ hel2 hec2
    have hva := evalExprlist_determ hel1 _ hel2
    subst hva
    obtain ⟨hmt, hrest⟩ :=
      (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ hec1 hec2
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    rw [hv, hm]
  case ifthenelse.ifthenelse =>
    rename_i he1 hb1 _ _ hb2 he2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hb1] at hb2
    simp_all
  case return_0.return_0 =>
    rename_i hf1 _ hf2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    rw [hf1] at hf2
    simp_all
  case return_1.return_1 =>
    rename_i he1 hc1 hf1 _ _ _ hc2 hf2 he2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hc1] at hc2
    rw [hf1] at hf2
    simp_all
  case skip_call.skip_call =>
    rename_i _ hf1 _ _ hf2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    rw [hf1] at hf2
    simp_all
  case switch.switch =>
    rename_i he1 hn1 _ _ hn2 he2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    have hv := evalExpr_determ he1 he2
    subst hv
    rw [hn1] at hn2
    simp_all
  case goto.goto =>
    rename_i hfl1 _ _ hfl2
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    rw [hfl1] at hfl2
    simp_all
  case internal_function.internal_function =>
    rename_i hfe1 _ _ _ hfe2
    obtain ⟨he, hle, hm⟩ := hfe _ _ _ _ _ _ _ _ _ hfe1 hfe2
    subst he; subst hle; subst hm
    exact ⟨MatchTraces.nil, fun _ => rfl⟩
  case external_function.external_function =>
    rename_i hec1 _ _ hec2
    obtain ⟨hmt, hrest⟩ :=
      (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ hec1 hec2
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    rw [hv, hm]

/-! ## Trace length, initial and final states -/

/-- `Clight.semantics_determinate`'s `sd_traces`: one step emits at most one
    event. -/
theorem step_traces {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop} {s t s'}
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective)
    (h : Step ge fe s t s') : t.length ≤ 1 := by
  cases h <;>
    first
      | simp [E0]
      | (rename_i hec; exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec)

theorem initialState_determ {p s1 s2}
    (h1 : InitialState p s1) (h2 : InitialState p s2) : s1 = s2 := by
  cases h1 with
  | intro _ _ _ hm1 hs1 hf1 _ =>
      cases h2 with
      | intro _ _ _ hm2 hs2 hf2 _ =>
          rw [hm1] at hm2
          rw [hs1] at hs2
          simp only [Option.some.injEq] at hm2 hs2
          subst hm2; subst hs2
          rw [hf1] at hf2
          simp only [Option.some.injEq] at hf2
          subst hf2
          rfl

theorem finalState_nostep {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop} {s r t s'}
    (h : FinalState s r) : ¬ Step ge fe s t s' := by
  cases h
  intro hstep
  cases hstep

theorem finalState_determ {s r1 r2}
    (h1 : FinalState s r1) (h2 : FinalState s r2) : r1 = r2 := by
  cases h1; cases h2; rfl

/-! ## The `Determinate` record

CompCert states `semantics_determinate` about its `semantics` record, which this
port does not have; the five fields are collected here over the program and the
calling convention instead. -/

structure Determinate (p : Program)
    (fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop) : Prop where
  sd_determ : ∀ s t1 s1 t2 s2,
    Step p.globalenv fe s t1 s1 → Step p.globalenv fe s t2 s2 →
    MatchTraces (Genv.toSenv p.globalenv.genv_genv) t1 t2 ∧ (t1 = t2 → s1 = s2)
  sd_traces : ∀ s t s', Step p.globalenv fe s t s' → t.length ≤ 1
  sd_initial_determ : ∀ s1 s2, InitialState p s1 → InitialState p s2 → s1 = s2
  sd_final_nostep : ∀ s r t s', FinalState s r → ¬ Step p.globalenv fe s t s'
  sd_final_determ : ∀ s r1 r2, FinalState s r1 → FinalState s r2 → r1 = r2

/-- Every program's symbol table is injective — the `Senv` invariant this port
    does not carry in the record.  Discharged by `Genv.symbInjective_globalenv`,
    which is why determinism needs no hypothesis about `ge`. -/
theorem program_symbolsInjective (p : Program) :
    (Genv.toSenv p.globalenv.genv_genv).SymbolsInjective :=
  Genv.toSenv_symbolsInjective (Genv.symbInjective_globalenv p.prog_public p.prog_defs)

theorem determinate_of_entryDeterm (p : Program)
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hfe : EntryDeterm fe) : Determinate p fe where
  sd_determ := fun _ _ _ _ _ h1 h2 =>
    step_determ hfe (program_symbolsInjective p) h1 h2
  sd_traces := fun _ _ _ h => step_traces (program_symbolsInjective p) h
  sd_initial_determ := fun _ _ h1 h2 => initialState_determ h1 h2
  sd_final_nostep := fun _ _ _ _ h => finalState_nostep h
  sd_final_determ := fun _ _ _ h1 h2 => finalState_determ h1 h2

/-- `Clight.semantics_determinate` for `step1` (parameters as stack variables). -/
theorem semantics_determinate1 (p : Program) :
    Determinate p (FunctionEntry1 p.globalenv) :=
  determinate_of_entryDeterm p (entryDeterm_functionEntry1 _)

/-- `Clight.semantics_determinate` for `step2` (parameters as temporaries). -/
theorem semantics_determinate2 (p : Program) :
    Determinate p (FunctionEntry2 p.globalenv) :=
  determinate_of_entryDeterm p (entryDeterm_functionEntry2 _)

/-! ## Corollaries: the silent fragment

`CCLib.logic.Hoare`'s `SStep` is `Step … E0`, and `CCLib.logic.SepHoare`'s triples are
existential ("*an* execution reaches a good outcome").  What determinism buys
there is below: the silent step relation is a partial *function*, so one
exhibited terminating run pins down every run. -/

/-- The relation `SStep` is built on is single-valued. -/
theorem sstep_determ {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hfe : EntryDeterm fe)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective) {s s1 s2}
    (h1 : Step ge fe s E0 s1) (h2 : Step ge fe s E0 s2) : s1 = s2 :=
  (step_determ hfe hinj h1 h2).2 rfl

/-- Silent runs without the trace algebra.  `Star` carries a trace and its
    `step` rule appends; every statement below is about `E0` runs, and this
    saves rederiving `t1 ++ t2 = []` at each use. -/
inductive StarE0 (R : State → Trace → State → Prop) : State → State → Prop where
  | refl (s) : StarE0 R s s
  | step (s1 s2 s3) : R s1 E0 s2 → StarE0 R s2 s3 → StarE0 R s1 s3

theorem starE0_of_star {R : State → Trace → State → Prop} {s t s'}
    (h : Star R s t s') : t = E0 → StarE0 R s s' := by
  induction h with
  | refl _ => intro _; exact StarE0.refl _
  | step _ t1 _ t2 _ _ hr _ he ih =>
      intro ht
      subst he
      cases t1 with
      | cons _ _ => simp [E0, Eapp] at ht
      | nil =>
          have hq : t2 = E0 := by simpa [E0, Eapp] using ht
          exact StarE0.step _ _ _ hr (ih hq)

theorem star_of_starE0 {R : State → Trace → State → Prop} {s s'}
    (h : StarE0 R s s') : Star R s E0 s' := by
  induction h with
  | refl _ => exact Star.refl _
  | step _ _ _ hr _ ih => exact Star.step _ _ _ _ _ _ hr ih rfl

theorem starE0_of_stuck {R : State → Trace → State → Prop} {x y}
    (h : StarE0 R x y) (hs : ∀ t s', ¬ R x t s') : x = y := by
  cases h with
  | refl _ => rfl
  | step _ _ _ hr _ => exact absurd hr (hs _ _)

/-- **∀-run from ∃-run.**  If *some* silent run from `s` reaches a state that
    cannot step, then *every* silent run from `s` is a prefix of that one. -/
theorem starE0_prefix {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hfe : EntryDeterm fe)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective) {s sa}
    (h1 : StarE0 (Step ge fe) s sa) :
    (∀ t s', ¬ Step ge fe sa t s') →
      ∀ sb, StarE0 (Step ge fe) s sb → StarE0 (Step ge fe) sb sa := by
  induction h1 with
  | refl _ =>
      intro hstuck _ h2
      cases h2 with
      | refl _ => exact StarE0.refl _
      | step _ _ _ hr _ => exact absurd hr (hstuck _ _)
  | step _ _ _ hr hrest ih =>
      intro hstuck _ h2
      cases h2 with
      | refl _ => exact StarE0.step _ _ _ hr hrest
      | step _ _ _ hr2 hrest2 =>
          have he := sstep_determ hfe hinj hr hr2
          subst he
          exact ih hstuck _ hrest2

/-- The endpoint of a terminating silent run is unique: total correctness for
    one run upgrades to all runs. -/
theorem starE0_endpoint_unique {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hfe : EntryDeterm fe)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective) {s sa sb}
    (h1 : StarE0 (Step ge fe) s sa) (h2 : StarE0 (Step ge fe) s sb)
    (ha : ∀ t s', ¬ Step ge fe sa t s') (hb : ∀ t s', ¬ Step ge fe sb t s') :
    sa = sb :=
  ((starE0_of_stuck (starE0_prefix hfe hinj h1 ha _ h2) hb)).symm

/-! ## Interpreter completeness on the deterministic fragment

`CCLib.cfrontend.ClightExecSound`'s header records the converse of soundness as owed:
completeness "is false as stated for the external-call rules … For the
deterministic fragment it should hold; it is not proved here."  With
determinacy it holds, in the precise form the caveat allows: if the interpreter
takes a step then the relation permits *no other*, up to the trace freedom
`MatchTraces` grants a volatile load or a system call. -/

theorem doStep_complete (ge : CGenv)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective) {s t s' t2 s2}
    (hi : doStep ge s = some (t, s'))
    (hr : Step ge (FunctionEntry2 ge) s t2 s2) :
    MatchTraces (Genv.toSenv ge.genv_genv) t t2 ∧ (t = t2 → s' = s2) :=
  step_determ (entryDeterm_functionEntry2 ge) hinj (doStep_sound ge s t s' hi) hr

/-- The silent case, stated as plain equality: on a step the interpreter can
    take with no observable event, the relation and the interpreter agree. -/
theorem doStep_complete_E0 (ge : CGenv)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective) {s s' s2}
    (hi : doStep ge s = some (E0, s'))
    (hr : Step ge (FunctionEntry2 ge) s E0 s2) : s' = s2 :=
  (doStep_complete ge hinj hi hr).2 rfl

end CC
