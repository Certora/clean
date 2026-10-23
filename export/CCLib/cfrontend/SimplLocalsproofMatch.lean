/-
  Pulling local scalar variables into temporaries: semantic preservation —
  port of `cfrontend/SimplLocalsproof.v`, part 4: matching of continuations
  (`match_cont`) and its invariance lemmas, matching of execution states
  (`match_states`), and the properties of `switch` statements and of
  `find_label` needed by the simulation.
-/
import CCLib.cfrontend.SimplLocalsproofExpr

namespace CC
namespace SimplLocals

open Smallstep

/-! ## Matching continuations -/

/-- `SimplLocalsproof.match_cont` -/
inductive MatchCont (opts : Options) (ge : Genv FunDef Ty) (f : Val.Meminj) :
    Compilenv → Cont → Cont → Mem → Block → Block → Prop where
  | Kstop (cenv m bound tbound hi) :
      MatchGlobalenvs ge f hi → hi ≤ bound → hi ≤ tbound →
      MatchCont opts ge f cenv .Kstop .Kstop m bound tbound
  | Kseq (cenv s k ts tk m bound tbound) :
      simplStmt opts cenv s = .OK ts →
      MatchCont opts ge f cenv k tk m bound tbound →
      CompatCenv (addrTakenStmt s) cenv →
      MatchCont opts ge f cenv (.Kseq s k) (.Kseq ts tk) m bound tbound
  | Kloop1 (cenv s1 s2 k ts1 ts2 tk m bound tbound) :
      simplStmt opts cenv s1 = .OK ts1 →
      simplStmt opts cenv s2 = .OK ts2 →
      MatchCont opts ge f cenv k tk m bound tbound →
      CompatCenv (VSet.union (addrTakenStmt s1) (addrTakenStmt s2)) cenv →
      MatchCont opts ge f cenv (.Kloop1 s1 s2 k) (.Kloop1 ts1 ts2 tk) m bound tbound
  | Kloop2 (cenv s1 s2 k ts1 ts2 tk m bound tbound) :
      simplStmt opts cenv s1 = .OK ts1 →
      simplStmt opts cenv s2 = .OK ts2 →
      MatchCont opts ge f cenv k tk m bound tbound →
      CompatCenv (VSet.union (addrTakenStmt s1) (addrTakenStmt s2)) cenv →
      MatchCont opts ge f cenv (.Kloop2 s1 s2 k) (.Kloop2 ts1 ts2 tk) m bound tbound
  | Kswitch (cenv k tk m bound tbound) :
      MatchCont opts ge f cenv k tk m bound tbound →
      MatchCont opts ge f cenv (.Kswitch k) (.Kswitch tk) m bound tbound
  | Kcall (cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x) :
      transfFunction opts fn = .OK tfn →
      MatchEnvs f (cenvFor fn) e le m lo hi te tle tlo thi →
      MatchCont opts ge f (cenvFor fn) k tk m lo tlo →
      checkOpttemp (cenvFor fn) optid = .OK x →
      hi ≤ bound → thi ≤ tbound →
      MatchCont opts ge f cenv (.Kcall optid fn e le k) (.Kcall optid tfn te tle tk) m bound tbound

section MATCH_CONT
variable {opts : Options} {ge : Genv FunDef Ty}

theorem pos_lt_of_lt_of_le {a b c : Positive} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  Nat.lt_of_lt_of_le h1 h2
theorem pos_le_trans {a b c : Positive} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := Nat.le_trans h1 h2

/-- `SimplLocalsproof.match_cont_invariant` -/
theorem match_cont_invariant {f' : Val.Meminj} {m' : Mem} {f : Val.Meminj} {cenv : Compilenv}
    {k tk : Cont} {m : Mem} {bound tbound : Block}
    (h : MatchCont opts ge f cenv k tk m bound tbound)
    (LOAD : ∀ b chunk v, f b = none → b < bound → Mem.load chunk m b 0 = some v →
      Mem.load chunk m' b 0 = some v)
    (INCR : Val.inject_incr f f')
    (INJ1 : ∀ b, b < bound → f' b = f b)
    (INJ2 : ∀ b b' delta, f' b = some (b', delta) → b' < tbound → f' b = f b) :
    MatchCont opts ge f' cenv k tk m' bound tbound := by
  induction h with
  | Kstop cenv m bound tbound hi MG h1 h2 =>
    refine .Kstop _ _ _ _ hi ⟨?_, ?_, MG.symbols, MG.functions, MG.varinfos⟩ h1 h2
    · intro b hb; rw [INJ1 b (pos_lt_of_lt_of_le hb h1)]; exact MG.domain b hb
    · intro b1 b2 delta hf hb2
      have := INJ2 b1 b2 delta hf (pos_lt_of_lt_of_le hb2 h2)
      rw [this] at hf
      exact MG.image b1 b2 delta hf hb2
  | Kseq _ _ _ _ _ _ _ _ h1 _ h3 ih => exact .Kseq _ _ _ _ _ _ _ _ h1 (ih LOAD INJ1 INJ2) h3
  | Kloop1 _ _ _ _ _ _ _ _ _ _ h1 h2 _ h4 ih => exact .Kloop1 _ _ _ _ _ _ _ _ _ _ h1 h2 (ih LOAD INJ1 INJ2) h4
  | Kloop2 _ _ _ _ _ _ _ _ _ _ h1 h2 _ h4 ih => exact .Kloop2 _ _ _ _ _ _ _ _ _ _ h1 h2 (ih LOAD INJ1 INJ2) h4
  | Kswitch _ _ _ _ _ _ _ ih => exact .Kswitch _ _ _ _ _ _ (ih LOAD INJ1 INJ2)
  | Kcall cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x h1 ME _ h4 h5 h6 ih =>
    have hlo : lo ≤ bound := pos_le_trans ME.me_incr h5
    have htlo : tlo ≤ tbound := pos_le_trans ME.me_tincr h6
    refine .Kcall _ _ _ _ _ _ _ _ _ _ _ hi thi lo tlo _ _ x h1 ?_ ?_ h4 h5 h6
    · exact match_envs_invariant ME (fun b chunk v hf hb hl => LOAD b chunk v hf
        (pos_lt_of_lt_of_le hb.2 h5) hl) INCR (fun b hb => INJ1 b (pos_lt_of_lt_of_le hb.2 h5))
        (fun b b' delta hf hb => INJ2 b b' delta hf (pos_lt_of_lt_of_le hb.2 h6))
    · exact ih (fun b chunk v hf hb hl => LOAD b chunk v hf (pos_lt_of_lt_of_le hb hlo) hl)
        (fun b hb => INJ1 b (pos_lt_of_lt_of_le hb hlo))
        (fun b b' delta hf hb => INJ2 b b' delta hf (pos_lt_of_lt_of_le hb htlo))

/-- `SimplLocalsproof.match_cont_assign_loc` -/
theorem match_cont_assign_loc {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} {ce : CompositeEnv} {ty : Ty} {loc : Block} {ofs : Integers.Ptrofs}
    {bf : Bitfield} {v : Val} {m' : Mem}
    (h : MatchCont opts ge f cenv k tk m bound tbound) (ha : AssignLoc ce ty m loc ofs bf v m')
    (hb : bound ≤ loc) : MatchCont opts ge f cenv k tk m' bound tbound := by
  refine match_cont_invariant h ?_ (Val.inject_incr_refl _) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
  intro b chunk v hf hlt hl
  have hne : b ≠ loc := by
    rintro rfl; exact absurd (pos_lt_of_lt_of_le hlt hb) (Nat.lt_irrefl _)
  cases ha with
  | value _ _ _ _ hs => exact storev_load_other hs hne hl
  | copy _ _ _ _ _ _ _ _ _ hs => exact load_storebytes_other_block hs hne hl
  | bitfield _ _ _ _ _ _ _ hs =>
    cases hs with
    | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs => exact storev_load_other hs hne hl

/-- `SimplLocalsproof.match_cont_extcall` -/
theorem match_cont_extcall {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} {tm : Mem} {f' : Val.Meminj} {m' : Mem}
    (h : MatchCont opts ge f cenv k tk m bound tbound)
    (UNCH : Mem.UnchangedOn (locUnmapped f) m m') (INCR : Val.inject_incr f f')
    (SEP : InjectSeparated f f' m tm) (HB : bound ≤ m.nextblock) (THB : tbound ≤ tm.nextblock) :
    MatchCont opts ge f' cenv k tk m' bound tbound := by
  refine match_cont_invariant h ?_ INCR ?_ ?_
  · intro b chunk v hf _ hl
    exact UNCH.load (fun _ _ _ => hf) hl
  · intro b hb
    cases hfb : f b with
    | some p => obtain ⟨b', d⟩ := p; exact INCR _ _ _ hfb
    | none =>
      cases hf'b : f' b with
      | none => rfl
      | some p =>
        obtain ⟨b', d⟩ := p
        have := (SEP b b' d hfb hf'b).1
        simp only [Mem.validBlock, decide_eq_false_iff_not] at this
        exact absurd (Nat.lt_of_lt_of_le hb HB) this
  · intro b b' delta hf' hb'
    cases hfb : f b with
    | some p => obtain ⟨b'', d⟩ := p; rw [INCR _ _ _ hfb]
    | none =>
      have := (SEP b b' delta hfb hf').2
      simp only [Mem.validBlock, decide_eq_false_iff_not] at this
      exact absurd (Nat.lt_of_lt_of_le hb' THB) this

/-- `SimplLocalsproof.match_cont_incr_bounds` -/
theorem match_cont_incr_bounds {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} (h : MatchCont opts ge f cenv k tk m bound tbound) :
    ∀ {bound' tbound'}, bound ≤ bound' → tbound ≤ tbound' →
    MatchCont opts ge f cenv k tk m bound' tbound' := by
  induction h with
  | Kstop _ _ _ _ hi MG h1 h2 =>
    intro _ _ hb ht; exact .Kstop _ _ _ _ hi MG (pos_le_trans h1 hb) (pos_le_trans h2 ht)
  | Kseq _ _ _ _ _ _ _ _ h1 _ h3 ih => intro _ _ hb ht; exact .Kseq _ _ _ _ _ _ _ _ h1 (ih hb ht) h3
  | Kloop1 _ _ _ _ _ _ _ _ _ _ h1 h2 _ h4 ih =>
    intro _ _ hb ht; exact .Kloop1 _ _ _ _ _ _ _ _ _ _ h1 h2 (ih hb ht) h4
  | Kloop2 _ _ _ _ _ _ _ _ _ _ h1 h2 _ h4 ih =>
    intro _ _ hb ht; exact .Kloop2 _ _ _ _ _ _ _ _ _ _ h1 h2 (ih hb ht) h4
  | Kswitch _ _ _ _ _ _ _ ih => intro _ _ hb ht; exact .Kswitch _ _ _ _ _ _ (ih hb ht)
  | Kcall _ _ _ _ _ _ _ _ _ _ _ hi thi lo tlo _ _ x h1 ME hk h4 h5 h6 _ =>
    intro _ _ hb ht
    exact .Kcall _ _ _ _ _ _ _ _ _ _ _ hi thi lo tlo _ _ x h1 ME hk h4 (pos_le_trans h5 hb)
      (pos_le_trans h6 ht)

/-- `SimplLocalsproof.match_cont_change_cenv` -/
theorem match_cont_change_cenv {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} (h : MatchCont opts ge f cenv k tk m bound tbound)
    (hk : isCallCont k = true) (cenv' : Compilenv) :
    MatchCont opts ge f cenv' k tk m bound tbound := by
  cases h with
  | Kstop _ _ _ _ hi MG h1 h2 => exact .Kstop _ _ _ _ hi MG h1 h2
  | Kcall _ _ _ _ _ _ _ _ _ _ _ hi thi lo tlo _ _ x h1 ME hk' h4 h5 h6 =>
    exact .Kcall _ _ _ _ _ _ _ _ _ _ _ hi thi lo tlo _ _ x h1 ME hk' h4 h5 h6
  | _ => simp [isCallCont] at hk

/-- `SimplLocalsproof.match_cont_is_call_cont` -/
theorem match_cont_is_call_cont {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} (h : MatchCont opts ge f cenv k tk m bound tbound)
    (hk : isCallCont k = true) : isCallCont tk = true := by
  cases h <;> simp_all [isCallCont]

/-- `SimplLocalsproof.match_cont_call_cont` -/
theorem match_cont_call_cont {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} (h : MatchCont opts ge f cenv k tk m bound tbound) (cenv' : Compilenv) :
    MatchCont opts ge f cenv' (callCont k) (callCont tk) m bound tbound := by
  induction h generalizing cenv' with
  | Kstop _ _ _ _ hi MG h1 h2 => exact .Kstop _ _ _ _ hi MG h1 h2
  | Kseq _ _ _ _ _ _ _ _ _ _ _ ih => exact ih cenv'
  | Kloop1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih cenv'
  | Kloop2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih cenv'
  | Kswitch _ _ _ _ _ _ _ ih => exact ih cenv'
  | Kcall _ _ _ _ _ _ _ _ _ _ _ hi thi lo tlo _ _ x h1 ME hk' h4 h5 h6 _ =>
    exact .Kcall _ _ _ _ _ _ _ _ _ _ _ hi thi lo tlo _ _ x h1 ME hk' h4 h5 h6

/-- `SimplLocalsproof.free_list_load` (as an equality). -/
theorem freeList_load {chunk : Chunk} {b' : Block} {ofs : Z} :
    ∀ {l : List (Block × Z × Z)} {m m' : Mem}, Mem.freeList m l = some m' →
    (∀ b lo hi, (b, lo, hi) ∈ l → b' ≠ b) → Mem.load chunk m' b' ofs = Mem.load chunk m b' ofs
  | [], m, m', h, _ => by simp only [Mem.freeList, Option.some.injEq] at h; subst h; rfl
  | (b, lo, hi) :: l, m, m', h, H => by
    simp only [Mem.freeList] at h
    split at h
    · cases h
    · rename_i m1 hfr
      rw [freeList_load h (fun b lo hi hin => H b lo hi (List.mem_cons_of_mem _ hin)),
        Mem.free_result hfr, Mem.load_free_other _ _ _ _ _ _ (H b lo hi (List.mem_cons_self ..))]

/-- `SimplLocalsproof.match_cont_free_env` -/
theorem match_cont_free_env {ce : CompositeEnv} {f : Val.Meminj} {cenv : Compilenv} {e : Env}
    {le : TempEnv} {m : Mem} {lo hi : Block} {te : Env} {tle : TempEnv} {tm : Mem}
    {tlo thi : Block} {k tk : Cont} {m' tm' : Mem}
    (ME : MatchEnvs f cenv e le m lo hi te tle tlo thi)
    (MC : MatchCont opts ge f cenv k tk m lo tlo)
    (HB : hi ≤ m.nextblock) (THB : thi ≤ tm.nextblock)
    (FR : Mem.freeList m (blocksOfEnv ce e) = some m')
    (TFR : Mem.freeList tm (blocksOfEnv ce te) = some tm') :
    MatchCont opts ge f cenv k tk m' m'.nextblock tm'.nextblock := by
  refine match_cont_incr_bounds (match_cont_invariant MC ?_ (Val.inject_incr_refl _)
    (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)) ?_ ?_
  · intro b chunk v _ hb hl
    rw [freeList_load FR]; exact hl
    intro b0 lo0 hi0 hin heq
    subst heq
    obtain ⟨id, ty, he, _, _⟩ := mem_blocksOfEnv hin
    exact absurd (Nat.lt_of_lt_of_le hb (ME.me_range id b ty he).1) (Nat.lt_irrefl _)
  · rw [Mem.nextblock_freeList FR]; exact pos_le_trans ME.me_incr HB
  · rw [Mem.nextblock_freeList TFR]; exact pos_le_trans ME.me_tincr THB

/-- `SimplLocalsproof.match_cont_globalenv` -/
theorem match_cont_globalenv {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} (h : MatchCont opts ge f cenv k tk m bound tbound) :
    ∃ bound, MatchGlobalenvs ge f bound := by
  induction h with
  | Kstop _ _ _ _ hi MG _ _ => exact ⟨hi, MG⟩
  | Kseq _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kloop1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kloop2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | Kswitch _ _ _ _ _ _ _ ih => exact ih
  | Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

end MATCH_CONT

/-! ## Relating execution states -/

/-- `SimplLocalsproof.match_states` -/
inductive MatchStates (opts : Options) (ge : Genv FunDef Ty) : State → State → Prop where
  | regular (f s k e le m tf ts tk te tle tm j lo hi tlo thi) :
      transfFunction opts f = .OK tf →
      simplStmt opts (cenvFor f) s = .OK ts →
      MatchEnvs j (cenvFor f) e le m lo hi te tle tlo thi →
      MatchCont opts ge j (cenvFor f) k tk m lo tlo →
      Mem.Inject j m tm →
      CompatCenv (addrTakenStmt s) (cenvFor f) →
      hi ≤ m.nextblock → thi ≤ tm.nextblock →
      MatchStates opts ge (.State f s k e le m) (.State tf ts tk te tle tm)
  | call (fd vargs k m tfd tvargs tk tm j targs tres cconv) :
      transfFundef opts fd = .OK tfd →
      (∀ cenv, MatchCont opts ge j cenv k tk m m.nextblock tm.nextblock) →
      Mem.Inject j m tm →
      Val.InjectList j vargs tvargs →
      typeOfFundef fd = .Tfunction targs tres cconv →
      ValCastedList vargs targs →
      MatchStates opts ge (.Callstate fd vargs k m) (.Callstate tfd tvargs tk tm)
  | ret (v k m tv tk tm j) :
      (∀ cenv, MatchCont opts ge j cenv k tk m m.nextblock tm.nextblock) →
      Mem.Inject j m tm →
      Val.Inject j v tv →
      MatchStates opts ge (.Returnstate v k m) (.Returnstate tv tk tm)

/-! ## The function-pointer lemma -/

section FINDFUNCT
variable {opts : Options} {prog tprog : Program} (TRANSF : transfProgram opts prog = .OK tprog)
include TRANSF

/-- `SimplLocalsproof.match_cont_find_funct` -/
theorem match_cont_find_funct {f : Val.Meminj} {cenv : Compilenv} {k tk : Cont} {m : Mem}
    {bound tbound : Block} {vf : Val} {fd : FunDef} {tvf : Val}
    (h : MatchCont opts prog.globalenv.genv_genv f cenv k tk m bound tbound)
    (hf : Genv.findFunct prog.globalenv.genv_genv vf = some fd) (hi : Val.Inject f vf tvf) :
    ∃ tfd, Genv.findFunct tprog.globalenv.genv_genv tvf = some tfd ∧ transfFundef opts fd = .OK tfd := by
  obtain ⟨bound1, MG⟩ := match_cont_globalenv h
  cases hi with
  | ptr delta hfb ho =>
    rename_i b1 ofs1 b2 ofs2
    simp only [Genv.findFunct] at hf
    split at hf
    · rename_i heq
      have hz : ofs1 = Integers.Ptrofs.zero := Integers.Ptrofs.same_if_eq heq
      subst hz
      have hd := MG.domain b1 (MG.functions b1 fd hf)
      rw [hd] at hfb; cases hfb
      subst ho
      obtain ⟨tfd, A, B⟩ := function_ptr_translated TRANSF hf
      refine ⟨tfd, ?_, B⟩
      simp only [Genv.findFunct, EventsInject.ptrofs_add_repr_zero]
      rw [if_pos heq]; exact A
    · cases hf
  | _ => simp [Genv.findFunct] at hf

end FINDFUNCT

/-! ## Switch statements -/

/-- `SimplLocalsproof.is_liftable_var_charact` -/
theorem is_liftable_var_charact (cenv : Compilenv) (a : Expr) :
    match isLiftableVar cenv a with
    | some id => ∃ ty, a = .Evar id ty ∧ VSet.mem id cenv = true
    | none => NotLiftedVar cenv a := by
  cases a with
  | Evar id ty =>
    simp only [isLiftableVar]
    cases hm : VSet.mem id cenv with
    | true => exact ⟨ty, rfl, hm⟩
    | false => exact hm
  | _ => trivial

theorem simpl_select_switch_default {opts : Options} {cenv : Compilenv} :
    ∀ {ls tls : LStmts}, simplLblstmt opts cenv ls = .OK tls →
    simplLblstmt opts cenv (selectSwitchDefault ls) = .OK (selectSwitchDefault tls)
  | .LSnil, tls, h => by simp only [simplLblstmt] at h; cases h; rfl
  | .LScons c s ls, tls, h => by
    have h' := h
    simp only [simplLblstmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨s', hs, ls', hls, h⟩ := h
    cases h
    cases c with
    | none => exact h'
    | some c => simp only [selectSwitchDefault]; exact simpl_select_switch_default hls

theorem simpl_select_switch_case {opts : Options} {cenv : Compilenv} (n : Z) :
    ∀ {ls tls : LStmts}, simplLblstmt opts cenv ls = .OK tls →
    match selectSwitchCase n ls with
    | none => selectSwitchCase n tls = none
    | some ls' => ∃ tls', selectSwitchCase n tls = some tls' ∧ simplLblstmt opts cenv ls' = .OK tls'
  | .LSnil, tls, h => by simp only [simplLblstmt] at h; cases h; rfl
  | .LScons c s ls, tls, h => by
    have h' := h
    simp only [simplLblstmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨s', hs, ls', hls, h⟩ := h
    cases h
    cases c with
    | none => simp only [selectSwitchCase]; exact simpl_select_switch_case n hls
    | some c =>
      by_cases hc : c = n
      · simp only [selectSwitchCase, hc, if_true]
        exact ⟨_, rfl, by rw [← hc]; exact h'⟩
      · simp only [selectSwitchCase, hc, if_false]
        exact simpl_select_switch_case n hls

/-- `SimplLocalsproof.simpl_select_switch` -/
theorem simpl_select_switch {opts : Options} {cenv : Compilenv} (n : Z) {ls tls : LStmts}
    (h : simplLblstmt opts cenv ls = .OK tls) :
    simplLblstmt opts cenv (selectSwitch n ls) = .OK (selectSwitch n tls) := by
  have C := simpl_select_switch_case n h
  unfold selectSwitch
  revert C
  cases heq : selectSwitchCase n ls with
  | some ls' =>
    intro C
    obtain ⟨tls', P, Q⟩ := C
    rw [P]; exact Q
  | none =>
    intro C
    rw [C]; exact simpl_select_switch_default h

/-- `SimplLocalsproof.simpl_seq_of_labeled_statement` -/
theorem simpl_seq_of_labeled_statement {opts : Options} {cenv : Compilenv} :
    ∀ {ls tls : LStmts}, simplLblstmt opts cenv ls = .OK tls →
    simplStmt opts cenv (seqOfLabeledStatement ls) = .OK (seqOfLabeledStatement tls)
  | .LSnil, tls, h => by simp only [simplLblstmt] at h; cases h; rfl
  | .LScons c s ls, tls, h => by
    simp only [simplLblstmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨s', hs, ls', hls, h⟩ := h
    cases h
    simp only [seqOfLabeledStatement, simplStmt, hs, simpl_seq_of_labeled_statement hls]
    rfl

theorem compat_lcons {cenv : Compilenv} {c : Option Z} {s : Stmt} {ls : LStmts}
    (h : CompatCenv (addrTakenLblstmt (.LScons c s ls)) cenv) :
    CompatCenv (addrTakenStmt s) cenv ∧ CompatCenv (addrTakenLblstmt ls) cenv :=
  ⟨compat_cenv_union_l (atk2 := addrTakenLblstmt ls) h, compat_cenv_union_r (atk1 := addrTakenStmt s) h⟩

theorem compat_cenv_select_switch_default {cenv : Compilenv} :
    ∀ {ls : LStmts}, CompatCenv (addrTakenLblstmt ls) cenv →
    CompatCenv (addrTakenLblstmt (selectSwitchDefault ls)) cenv
  | .LSnil, h => h
  | .LScons none _ _, h => h
  | .LScons (some _) _ _, h => by
    simp only [selectSwitchDefault]; exact compat_cenv_select_switch_default (compat_lcons h).2

theorem compat_cenv_select_switch_case {cenv : Compilenv} (n : Z) :
    ∀ {ls ls' : LStmts}, CompatCenv (addrTakenLblstmt ls) cenv →
    selectSwitchCase n ls = some ls' → CompatCenv (addrTakenLblstmt ls') cenv
  | .LSnil, _, _, h => by simp [selectSwitchCase] at h
  | .LScons none _ _, _, hc, h => compat_cenv_select_switch_case n (compat_lcons hc).2 h
  | .LScons (some c) _ _, _, hc, h => by
    simp only [selectSwitchCase] at h
    split at h
    · cases h; exact hc
    · exact compat_cenv_select_switch_case n (compat_lcons hc).2 h

/-- `SimplLocalsproof.compat_cenv_select_switch` -/
theorem compat_cenv_select_switch {cenv : Compilenv} (n : Z) {ls : LStmts}
    (h : CompatCenv (addrTakenLblstmt ls) cenv) :
    CompatCenv (addrTakenLblstmt (selectSwitch n ls)) cenv := by
  unfold selectSwitch
  cases heq : selectSwitchCase n ls with
  | some ls' => exact compat_cenv_select_switch_case n h heq
  | none => exact compat_cenv_select_switch_default h

/-- `SimplLocalsproof.addr_taken_seq_of_labeled_statement` -/
theorem addr_taken_seq_of_labeled_statement :
    ∀ ls : LStmts, addrTakenStmt (seqOfLabeledStatement ls) = addrTakenLblstmt ls
  | .LSnil => rfl
  | .LScons _ s ls => by
    simp only [seqOfLabeledStatement, addrTakenStmt, addrTakenLblstmt,
      addr_taken_seq_of_labeled_statement ls]

/-! ## `find_label` -/

section FIND_LABEL
variable {opts : Options} {ge : Genv FunDef Ty} {f : Val.Meminj} {cenv : Compilenv} {m : Mem}
  {bound tbound : Block}

variable (opts ge f cenv m bound tbound) in
/-- The conclusion of `SimplLocalsproof.simpl_find_label`. -/
def FindLabelSpec : Option (Stmt × Cont) → Option (Stmt × Cont) → Prop
  | none, tr => tr = none
  | some (s', k'), tr => ∃ ts' tk', tr = some (ts', tk') ∧ CompatCenv (addrTakenStmt s') cenv ∧
      simplStmt opts cenv s' = .OK ts' ∧ MatchCont opts ge f cenv k' tk' m bound tbound

/-- First-success combination of two label searches. -/
def optFirst {α : Type} (a b : Option α) : Option α :=
  match a with | some x => some x | none => b

theorem findLabelSpec_seq {r1 tr1 r2 tr2 : Option (Stmt × Cont)}
    (h1 : FindLabelSpec opts ge f cenv m bound tbound r1 tr1)
    (h2 : r1 = none → FindLabelSpec opts ge f cenv m bound tbound r2 tr2) :
    FindLabelSpec opts ge f cenv m bound tbound
      (optFirst r1 r2) (optFirst tr1 tr2) := by
  cases r1 with
  | none =>
    simp only [FindLabelSpec] at h1; subst h1
    exact h2 rfl
  | some p =>
    obtain ⟨s', k'⟩ := p
    obtain ⟨ts', tk', h, rest⟩ := h1
    subst h
    exact ⟨ts', tk', rfl, rest⟩

theorem findLabelSpec_none {tr : Option (Stmt × Cont)} (h : tr = none) :
    FindLabelSpec opts ge f cenv m bound tbound none tr := h

theorem findLabel_seq_eq (lbl : Ident) (s1 s2 : Stmt) (k : Cont) :
    findLabel lbl (.Ssequence s1 s2) k =
      optFirst (findLabel lbl s1 (.Kseq s2 k)) (findLabel lbl s2 k) := by
  cases h : findLabel lbl s1 (.Kseq s2 k) <;> simp [findLabel, h, optFirst]
theorem findLabel_ite_eq (lbl : Ident) (a : Expr) (s1 s2 : Stmt) (k : Cont) :
    findLabel lbl (.Sifthenelse a s1 s2) k =
      optFirst (findLabel lbl s1 k) (findLabel lbl s2 k) := by
  cases h : findLabel lbl s1 k <;> simp [findLabel, h, optFirst]
theorem findLabel_loop_eq (lbl : Ident) (s1 s2 : Stmt) (k : Cont) :
    findLabel lbl (.Sloop s1 s2) k =
      optFirst (findLabel lbl s1 (.Kloop1 s1 s2 k)) (findLabel lbl s2 (.Kloop2 s1 s2 k)) := by
  cases h : findLabel lbl s1 (.Kloop1 s1 s2 k) <;> simp [findLabel, h, optFirst]
theorem findLabelLs_cons_eq (lbl : Ident) (c : Option Z) (s : Stmt) (ls : LStmts) (k : Cont) :
    findLabelLs lbl (.LScons c s ls) k =
      optFirst (findLabel lbl s (.Kseq (seqOfLabeledStatement ls) k)) (findLabelLs lbl ls k) := by
  cases h : findLabel lbl s (.Kseq (seqOfLabeledStatement ls) k) <;> simp [findLabelLs, h, optFirst]

mutual
/-- `SimplLocalsproof.simpl_find_label` -/
theorem simpl_find_label (lbl : Ident) : ∀ (s : Stmt) {k : Cont} {ts : Stmt} {tk : Cont},
    simplStmt opts cenv s = .OK ts → MatchCont opts ge f cenv k tk m bound tbound →
    CompatCenv (addrTakenStmt s) cenv →
    FindLabelSpec opts ge f cenv m bound tbound (findLabel lbl s k) (findLabel lbl ts tk)
  | .Sskip, k, ts, tk, h, _, _ => by
    simp only [simplStmt] at h; cases h; exact findLabelSpec_none rfl
  | .Sassign a1 a2, k, ts, tk, h, _, _ => by
    simp only [simplStmt] at h
    split at h
    · cases h
      unfold Sset_debug
      cases opts.debug <;> exact findLabelSpec_none (by simp [findLabel, Sdebug_temp])
    · cases h; exact findLabelSpec_none (by simp [findLabel])
  | .Sset id a, k, ts, tk, h, _, _ => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, h⟩ := h; cases h; exact findLabelSpec_none (by simp [findLabel])
  | .Scall optid a al, k, ts, tk, h, _, _ => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, h⟩ := h; cases h; exact findLabelSpec_none (by simp [findLabel])
  | .Sbuiltin optid ef tyargs al, k, ts, tk, h, _, _ => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨_, _, h⟩ := h; cases h; exact findLabelSpec_none (by simp [findLabel])
  | .Ssequence s1 s2, k, ts, tk, h, MC, hc => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts1, h1, ts2, h2, h⟩ := h; cases h
    have hc1 : CompatCenv (addrTakenStmt s1) cenv := compat_cenv_union_l (atk2 := addrTakenStmt s2) hc
    have hc2 : CompatCenv (addrTakenStmt s2) cenv := compat_cenv_union_r (atk1 := addrTakenStmt s1) hc
    rw [findLabel_seq_eq, findLabel_seq_eq]
    exact findLabelSpec_seq (simpl_find_label lbl s1 h1 (.Kseq _ _ _ _ _ _ _ _ h2 MC hc2) hc1)
      (fun _ => simpl_find_label lbl s2 h2 MC hc2)
  | .Sifthenelse a s1 s2, k, ts, tk, h, MC, hc => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts1, h1, ts2, h2, h⟩ := h; cases h
    have hc' : CompatCenv (VSet.union (addrTakenStmt s1) (addrTakenStmt s2)) cenv :=
      compat_cenv_union_r (atk1 := addrTakenExpr a) hc
    rw [findLabel_ite_eq, findLabel_ite_eq]
    exact findLabelSpec_seq (simpl_find_label lbl s1 h1 MC (compat_cenv_union_l hc'))
      (fun _ => simpl_find_label lbl s2 h2 MC (compat_cenv_union_r hc'))
  | .Sloop s1 s2, k, ts, tk, h, MC, hc => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts1, h1, ts2, h2, h⟩ := h; cases h
    have hc1 : CompatCenv (addrTakenStmt s1) cenv := compat_cenv_union_l (atk2 := addrTakenStmt s2) hc
    have hc2 : CompatCenv (addrTakenStmt s2) cenv := compat_cenv_union_r (atk1 := addrTakenStmt s1) hc
    rw [findLabel_loop_eq, findLabel_loop_eq]
    exact findLabelSpec_seq
      (simpl_find_label lbl s1 h1 (.Kloop1 _ _ _ _ _ _ _ _ _ _ h1 h2 MC hc) hc1)
      (fun _ => simpl_find_label lbl s2 h2 (.Kloop2 _ _ _ _ _ _ _ _ _ _ h1 h2 MC hc) hc2)
  | .Sbreak, k, ts, tk, h, _, _ => by
    simp only [simplStmt] at h; cases h; exact findLabelSpec_none rfl
  | .Scontinue, k, ts, tk, h, _, _ => by
    simp only [simplStmt] at h; cases h; exact findLabelSpec_none rfl
  | .Sreturn opta, k, ts, tk, h, _, _ => by
    simp only [simplStmt] at h; cases h; exact findLabelSpec_none (by simp [findLabel])
  | .Sswitch a ls, k, ts, tk, h, MC, hc => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨tls, hls, h⟩ := h; cases h
    simp only [findLabel]
    exact simpl_find_label_ls lbl ls hls (.Kswitch _ _ _ _ _ _ MC)
      (compat_cenv_union_r (atk1 := addrTakenExpr a) hc)
  | .Slabel lbl' s, k, ts, tk, h, MC, hc => by
    simp only [simplStmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts', hs, h⟩ := h; cases h
    simp only [findLabel]
    split
    · exact ⟨ts', tk, rfl, hc, hs, MC⟩
    · exact simpl_find_label lbl s hs MC hc
  | .Sgoto lbl', k, ts, tk, h, _, _ => by
    simp only [simplStmt] at h; cases h; exact findLabelSpec_none rfl

/-- `SimplLocalsproof.simpl_find_label_ls` -/
theorem simpl_find_label_ls (lbl : Ident) : ∀ (ls : LStmts) {k : Cont} {tls : LStmts} {tk : Cont},
    simplLblstmt opts cenv ls = .OK tls → MatchCont opts ge f cenv k tk m bound tbound →
    CompatCenv (addrTakenLblstmt ls) cenv →
    FindLabelSpec opts ge f cenv m bound tbound (findLabelLs lbl ls k) (findLabelLs lbl tls tk)
  | .LSnil, k, tls, tk, h, _, _ => by
    simp only [simplLblstmt] at h; cases h; exact findLabelSpec_none rfl
  | .LScons c s ls, k, tls, tk, h, MC, hc => by
    simp only [simplLblstmt, Cshmgen.res_bind_eq_OK] at h
    obtain ⟨ts, hs, tls', hls, h⟩ := h; cases h
    obtain ⟨hc1, hc2⟩ := compat_lcons hc
    rw [findLabelLs_cons_eq, findLabelLs_cons_eq]
    exact findLabelSpec_seq
      (simpl_find_label lbl s hs (.Kseq _ _ _ _ _ _ _ _ (simpl_seq_of_labeled_statement hls) MC
        (by rw [addr_taken_seq_of_labeled_statement]; exact hc2)) hc1)
      (fun _ => simpl_find_label_ls lbl ls hls MC hc2)
end

end FIND_LABEL

/-- `SimplLocalsproof.find_label_store_params` -/
theorem find_label_store_params (opts : Options) (lbl : Ident) (cenv : Compilenv) (s : Stmt)
    (k : Cont) : ∀ params : List (Ident × Ty),
    findLabel lbl (storeParams opts cenv params s) k = findLabel lbl s k
  | [] => rfl
  | (id, ty) :: params => by
    simp only [storeParams]
    split
    · split
      · simp only [findLabel]; rw [find_label_store_params opts lbl cenv s k params]
      · exact find_label_store_params opts lbl cenv s k params
    · simp only [findLabel]; rw [find_label_store_params opts lbl cenv s k params]

/-- `SimplLocalsproof.find_label_add_debug_vars` -/
theorem find_label_add_debug_vars (opts : Options) (lbl : Ident) (s : Stmt) (k : Cont)
    (vars : List (Ident × Ty)) : findLabel lbl (addDebugVars opts vars s) k = findLabel lbl s k := by
  unfold addDebugVars
  cases opts.debug
  · rfl
  · simp only [if_true]
    induction vars with
    | nil => rfl
    | cons p vars ih => simp only [List.foldr_cons, addDebugVar, findLabel]; rw [ih]; simp [findLabel, Sdebug_var]

/-- `SimplLocalsproof.find_label_add_debug_params` -/
theorem find_label_add_debug_params (opts : Options) (lbl : Ident) (s : Stmt) (k : Cont)
    (vars : List (Ident × Ty)) : findLabel lbl (addDebugParams opts vars s) k = findLabel lbl s k := by
  unfold addDebugParams
  cases opts.debug
  · rfl
  · simp only [if_true]
    induction vars with
    | nil => rfl
    | cons p vars ih => simp only [List.foldr_cons, addDebugParam, findLabel]; rw [ih]; simp [findLabel, Sdebug_temp]

end SimplLocals
end CC
