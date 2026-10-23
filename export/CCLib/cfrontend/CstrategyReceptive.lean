/-
  `Cstrategy.semantics_strongly_receptive` (`cfrontend/Cstrategy.v`): the
  strategy semantics of CompCert C is strongly receptive.

  A strategy step can emit two events (a compound assignment `x op= e` or a
  post-increment on a volatile location reads and then writes it), so it is
  not receptive in the ordinary sense; it is *strongly* receptive: if a step
  can begin with event `ev1`, it can also begin with any event `ev2` that
  `match_traces` relates to `ev1`, and every event after the first is an
  output.  Consequently `atomic (Cstrategy.semantics p)` is receptive
  (`Smallstep.atomic_receptive`).

  As for Clight (`CCLib.cfrontend.ClightReceptive`), receptiveness of the
  uninterpreted external functions and inline assembly, which CompCert
  assumes by axiom, is a hypothesis (`ExternalsReceptive`).
-/
import CCLib.cfrontend.Cstrategy
import CCLib.cfrontend.ClightReceptive
import CCLib.common.SmallstepAtomic

namespace CC
namespace Cstrategy



/-- `Cstrategy.deref_loc_trace` -/
theorem derefLoc_trace {ge : Csem.CGenv} {ty m b ofs bf t v} (h : Csem.DerefLoc ge ty m b ofs bf t v) :
    t = [] ∨ ∃ ev, t = [ev] := by
  have := Csem.derefLoc_traceLength h
  rcases t with _ | ⟨ev, _ | ⟨_, _⟩⟩
  · exact .inl rfl
  · exact .inr ⟨ev, rfl⟩
  · simp at this

/-- `Cstrategy.deref_loc_receptive` -/
theorem derefLoc_receptive {ge : Csem.CGenv} {ty m b ofs bf ev1 t1 v ev2}
    (h : Csem.DerefLoc ge ty m b ofs bf (ev1 :: t1) v)
    (hm : MatchTraces ge.genv_genv.toSenv [ev1] [ev2]) :
    t1 = [] ∧ ∃ v', Csem.DerefLoc ge ty m b ofs bf [ev2] v' := by
  have ht1 : t1 = [] := by
    rcases derefLoc_trace h with h' | ⟨_, h'⟩
    · simp at h'
    · simp only [List.cons.injEq] at h'; exact h'.2
  subst ht1
  refine ⟨rfl, ?_⟩
  generalize htr : [ev1] = tr at h
  cases h with
  | volatile chunk _ _ hac hvol hl =>
    subst htr
    obtain ⟨v', _, hs⟩ := EventsReceptive.volatileLoadSem_receptive chunk
      (Genv.toSenv_publicSymbolExists ge.genv_genv) _ _ _ _ _ _ (.intro _ _ _ _ _ _ hl) hm
    cases hs with
    | intro _ _ _ _ _ _ hl' => exact ⟨_, .volatile chunk _ _ hac hvol hl'⟩
  | _ => simp [E0] at htr

/-- `Cstrategy.assign_loc_trace` -/
theorem assignLoc_trace {ge : Csem.CGenv} {ty m b ofs bf v t m' v'}
    (h : Csem.AssignLoc ge ty m b ofs bf v t m' v') :
    t = [] ∨ ∃ ev, t = [ev] ∧ OutputEvent ev := by
  cases h with
  | volatile _ _ _ _ _ _ hv =>
    cases hv with
    | vol => exact .inr ⟨_, rfl, trivial⟩
    | nonvol => exact .inl rfl
  | _ => exact .inl rfl

/-- `Cstrategy.assign_loc_receptive` -/
theorem assignLoc_receptive {ge : Csem.CGenv} {ty m b ofs bf ev1 t1 v m' v' ev2}
    (h : Csem.AssignLoc ge ty m b ofs bf v (ev1 :: t1) m' v')
    (hm : MatchTraces ge.genv_genv.toSenv [ev1] [ev2]) :
    ev1 :: t1 = [ev2] := by
  rcases assignLoc_trace h with h' | ⟨ev, h', ho⟩
  · simp at h'
  · simp only [List.cons.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    generalize he : [ev1] = tr at hm
    cases hm <;> simp_all [OutputEvent]

/-- The event list of a step whose length is at most one is well behaved. -/
private theorem wb_of_length {t : Trace} : t.length ≤ 1 →
    match t with
    | [] => True
    | _ :: t' => OutputTrace t' := by
  intro h
  rcases t with _ | ⟨ev, _ | ⟨_, _⟩⟩
  · trivial
  · trivial
  · simp at h

private theorem outputTrace_of_assign {ge : Csem.CGenv} {ty m b ofs bf v t m' v'}
    (h : Csem.AssignLoc ge ty m b ofs bf v t m' v') : OutputTrace t := by
  rcases assignLoc_trace h with rfl | ⟨ev, rfl, ho⟩
  · trivial
  · exact ⟨ho, trivial⟩

/-- A read followed by a write: the trace `t1 ++ t2` is well behaved. -/
private theorem wb_read_write {ge : Csem.CGenv} {ty m b ofs bf t1 v1 ty' v t2 m' v'}
    (h1 : Csem.DerefLoc ge ty m b ofs bf t1 v1) (h2 : Csem.AssignLoc ge ty' m b ofs bf v t2 m' v') :
    match Eapp t1 t2 with
    | [] => True
    | _ :: t' => OutputTrace t' := by
  have ho := outputTrace_of_assign h2
  rcases derefLoc_trace h1 with rfl | ⟨ev, rfl⟩
  · simp only [Eapp, List.nil_append]
    cases t2 with
    | nil => trivial
    | cons _ _ => exact ho.2
  · exact ho

/-- `Cstrategy.semantics_strongly_receptive` -/
theorem semantics_strongly_receptive (p : Csyntax.Program)
    (hx : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv) :
    Smallstep.StronglyReceptive (semantics p) where
  ssr_receptive := by
    intro s ev1 t1 s1 ev2 h hm
    have hp := Genv.toSenv_publicSymbolExists (Csem.globalenv p).genv_genv
    change MatchTraces (Csem.globalenv p).genv_genv.toSenv [ev1] [ev2] at hm
    change Cstrategy.Estep (Csem.globalenv p) s (ev1 :: t1) s1 ∨ Csem.Sstep (Csem.globalenv p) s (ev1 :: t1) s1
      at h
    change ∃ s2 t2, Cstrategy.Estep (Csem.globalenv p) s (ev2 :: t2) s2 ∨
      Csem.Sstep (Csem.globalenv p) s (ev2 :: t2) s2
    generalize ht : ev1 :: t1 = t at h
    rcases h with h | h
    · cases h with
      | rvalof_volatile f C l ty k e m b ofs bf t v hC hl hd hty hvol =>
        subst ht
        obtain ⟨_, v', hd'⟩ := derefLoc_receptive hd hm
        exact ⟨_, _, .inl (Cstrategy.Estep.rvalof_volatile f C l ty k e m b ofs bf _ v' hC hl hd' hty hvol)⟩
      | assign f C l r ty k e m b ofs bf v v1 t m' v' hC hl hr hc ha hty =>
        subst ht
        have heq := assignLoc_receptive ha hm
        rw [heq] at ha
        exact ⟨_, _, .inl (Cstrategy.Estep.assign f C l r ty k e m b ofs bf v v1 _ m' v' hC hl hr hc ha hty)⟩
      | assignop f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1' t2' m' v' t hC hl hd hr
          hop hc ha hty htt =>
        subst htt
        rcases t1' with _ | ⟨ev0, t1''⟩
        · -- no event in the read: the write emits it
          change ev1 :: t1 = t2' at ht
          subst ht
          have heq := assignLoc_receptive ha hm
          rw [heq] at ha
          exact ⟨_, _, .inl (Cstrategy.Estep.assignop f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 [] _ m' v'
            _ hC hl hd hr hop hc ha hty rfl)⟩
        · change ev1 :: t1 = ev0 :: (t1'' ++ t2') at ht
          simp only [List.cons.injEq] at ht
          obtain ⟨rfl, -⟩ := ht
          obtain ⟨rfl, v1', hd'⟩ := derefLoc_receptive hd hm
          cases hop' : Cop.semBinaryOperation (Csem.globalenv p).genv_cenv op v1'
              (Csyntax.typeof l) v2 (Csyntax.typeof r) m with
          | none =>
            exact ⟨_, _, .inl (Cstrategy.Estep.assignop_stuck f C op l r tyres ty k e m b ofs bf v1' v2 _ hC hl
              hd' hr (by rw [hop']; trivial) hty)⟩
          | some v3' =>
            cases hc' : Cop.semCast v3' tyres (Csyntax.typeof l) m with
            | none =>
              exact ⟨_, _, .inl (Cstrategy.Estep.assignop_stuck f C op l r tyres ty k e m b ofs bf v1' v2 _ hC hl
                hd' hr (by rw [hop']; simp only [hc']) hty)⟩
            | some v4' =>
              by_cases hex : ∃ t2'' m'' v'',
                  Csem.AssignLoc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf v4' t2'' m'' v''
              · obtain ⟨t2'', m'', v'', ha'⟩ := hex
                exact ⟨_, _, .inl (Cstrategy.Estep.assignop f C op l r tyres ty k e m b ofs bf v1' v2 v3' v4' [ev2]
                  t2'' m'' v'' _ hC hl hd' hr hop' hc' ha' hty rfl)⟩
              · exact ⟨_, _, .inl (Cstrategy.Estep.assignop_stuck f C op l r tyres ty k e m b ofs bf v1' v2 _ hC
                  hl hd' hr (by rw [hop']; simp only [hc']; intro t2 m' v' ha; exact hex ⟨t2, m', v', ha⟩) hty)⟩
      | assignop_stuck f C op l r tyres ty k e m b ofs bf v1 v2 t hC hl hd hr _ hty =>
        subst ht
        obtain ⟨rfl, v1', hd'⟩ := derefLoc_receptive hd hm
        cases hop' : Cop.semBinaryOperation (Csem.globalenv p).genv_cenv op v1'
            (Csyntax.typeof l) v2 (Csyntax.typeof r) m with
        | none =>
          exact ⟨_, _, .inl (Cstrategy.Estep.assignop_stuck f C op l r tyres ty k e m b ofs bf v1' v2 _ hC hl
            hd' hr (by rw [hop']; trivial) hty)⟩
        | some v3' =>
          cases hc' : Cop.semCast v3' tyres (Csyntax.typeof l) m with
          | none =>
            exact ⟨_, _, .inl (Cstrategy.Estep.assignop_stuck f C op l r tyres ty k e m b ofs bf v1' v2 _ hC hl
              hd' hr (by rw [hop']; simp only [hc']) hty)⟩
          | some v4' =>
            by_cases hex : ∃ t2'' m'' v'',
                Csem.AssignLoc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf v4' t2'' m'' v''
            · obtain ⟨t2'', m'', v'', ha'⟩ := hex
              exact ⟨_, _, .inl (Cstrategy.Estep.assignop f C op l r tyres ty k e m b ofs bf v1' v2 v3' v4' [ev2]
                t2'' m'' v'' _ hC hl hd' hr hop' hc' ha' hty rfl)⟩
            · exact ⟨_, _, .inl (Cstrategy.Estep.assignop_stuck f C op l r tyres ty k e m b ofs bf v1' v2 _ hC
                hl hd' hr (by rw [hop']; simp only [hc']; intro t2 m' v' ha; exact hex ⟨t2, m', v', ha⟩) hty)⟩
      | postincr f C id l ty k e m b ofs bf v1 v2 v3 t1' t2' m' v' t hC hl hd hinc hc ha hty
          htt =>
        subst htt
        rcases t1' with _ | ⟨ev0, t1''⟩
        · change ev1 :: t1 = t2' at ht
          subst ht
          have heq := assignLoc_receptive ha hm
          rw [heq] at ha
          exact ⟨_, _, .inl (Cstrategy.Estep.postincr f C id l ty k e m b ofs bf v1 v2 v3 [] _ m' v' _ hC hl hd
            hinc hc ha hty rfl)⟩
        · change ev1 :: t1 = ev0 :: (t1'' ++ t2') at ht
          simp only [List.cons.injEq] at ht
          obtain ⟨rfl, -⟩ := ht
          obtain ⟨rfl, v1', hd'⟩ := derefLoc_receptive hd hm
          cases hinc' : Cop.semIncrdecr (Csem.globalenv p).genv_cenv id v1' ty m with
          | none =>
            exact ⟨_, _, .inl (Cstrategy.Estep.postincr_stuck f C id l ty k e m b ofs bf v1' _ hC hl hd'
              (by rw [hinc']; trivial) hty)⟩
          | some v2' =>
            cases hc' : Cop.semCast v2' (Cop.incrdecrType ty) ty m with
            | none =>
              exact ⟨_, _, .inl (Cstrategy.Estep.postincr_stuck f C id l ty k e m b ofs bf v1' _ hC hl hd'
                (by rw [hinc']; simp only [hc']) hty)⟩
            | some v3' =>
              by_cases hex : ∃ t2'' m'' v'',
                  Csem.AssignLoc (Csem.globalenv p) ty m b ofs bf v3' t2'' m'' v''
              · obtain ⟨t2'', m'', v'', ha'⟩ := hex
                exact ⟨_, _, .inl (Cstrategy.Estep.postincr f C id l ty k e m b ofs bf v1' v2' v3' [ev2] t2'' m''
                  v'' _ hC hl hd' hinc' hc' ha' hty rfl)⟩
              · exact ⟨_, _, .inl (Cstrategy.Estep.postincr_stuck f C id l ty k e m b ofs bf v1' _ hC hl hd'
                  (by rw [hinc']; simp only [hc']; subst hty; intro t2 m' v' ha; exact hex ⟨t2, m', v', ha⟩) hty)⟩
      | postincr_stuck f C id l ty k e m b ofs bf v1 t hC hl hd _ hty =>
        subst ht
        obtain ⟨rfl, v1', hd'⟩ := derefLoc_receptive hd hm
        cases hinc' : Cop.semIncrdecr (Csem.globalenv p).genv_cenv id v1' ty m with
        | none =>
          exact ⟨_, _, .inl (Cstrategy.Estep.postincr_stuck f C id l ty k e m b ofs bf v1' _ hC hl hd'
            (by rw [hinc']; trivial) hty)⟩
        | some v2' =>
          cases hc' : Cop.semCast v2' (Cop.incrdecrType ty) ty m with
          | none =>
            exact ⟨_, _, .inl (Cstrategy.Estep.postincr_stuck f C id l ty k e m b ofs bf v1' _ hC hl hd'
              (by rw [hinc']; simp only [hc']) hty)⟩
          | some v3' =>
            by_cases hex : ∃ t2'' m'' v'',
                Csem.AssignLoc (Csem.globalenv p) ty m b ofs bf v3' t2'' m'' v''
            · obtain ⟨t2'', m'', v'', ha'⟩ := hex
              exact ⟨_, _, .inl (Cstrategy.Estep.postincr f C id l ty k e m b ofs bf v1' v2' v3' [ev2] t2'' m''
                v'' _ hC hl hd' hinc' hc' ha' hty rfl)⟩
            · exact ⟨_, _, .inl (Cstrategy.Estep.postincr_stuck f C id l ty k e m b ofs bf v1' _ hC hl hd'
                (by rw [hinc']; simp only [hc']; subst hty; intro t2 m' v' ha; exact hex ⟨t2, m', v', ha⟩) hty)⟩
      | builtin f C ef tyargs rargs ty k e m vargs t vres m' hC hl hec =>
        subst ht
        have hlen := (externalCall_determ ef (Genv.toSenv_symbolsInjective
          (Genv.symbInjective_globalenv p.prog_public p.prog_defs))).traceLength _ _ _ _ _ hec
        have ht1 : t1 = [] := by
          cases t1 with
          | nil => rfl
          | cons _ _ => simp at hlen
        subst ht1
        obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
        exact ⟨_, [], .inl (Cstrategy.Estep.builtin f C ef tyargs rargs ty k e m vargs _ vres2 m2 hC hl h2)⟩
      | _ => simp [E0] at ht
    · cases h with
      | external_function ef targs tres cc vargs k m vres t m' hec =>
        subst ht
        have hlen := (externalCall_determ ef (Genv.toSenv_symbolsInjective
          (Genv.symbInjective_globalenv p.prog_public p.prog_defs))).traceLength _ _ _ _ _ hec
        have ht1 : t1 = [] := by
          cases t1 with
          | nil => rfl
          | cons _ _ => simp at hlen
        subst ht1
        obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
        exact ⟨_, [], .inr (Csem.Sstep.external_function ef targs tres cc vargs k m vres2 _ m2 h2)⟩
      | _ => simp [E0] at ht
  ssr_well_behaved := by
    have hinj : (Csem.globalenv p).genv_genv.toSenv.SymbolsInjective :=
      Genv.toSenv_symbolsInjective (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
    intro s t s' h
    rcases h with h | h
    · cases h with
      | rvalof_volatile _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd => exact wb_of_length (Csem.derefLoc_traceLength hd)
      | assign _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha =>
        exact wb_of_length (Csem.assignLoc_traceLength ha)
      | assignop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd _ _ _ ha _ htt =>
        subst htt; exact wb_read_write hd ha
      | assignop_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd =>
        exact wb_of_length (Csem.derefLoc_traceLength hd)
      | postincr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd _ _ ha _ htt =>
        subst htt; exact wb_read_write hd ha
      | postincr_stuck _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd => exact wb_of_length (Csem.derefLoc_traceLength hd)
      | builtin _ _ ef _ _ _ _ _ _ _ _ _ _ _ _ he =>
        exact wb_of_length ((externalCall_determ ef hinj).traceLength _ _ _ _ _ he)
      | _ => trivial
    · cases h with
      | external_function ef _ _ _ _ _ _ _ _ _ he =>
        exact wb_of_length ((externalCall_determ ef hinj).traceLength _ _ _ _ _ he)
      | _ => trivial

/-- `atomic (Cstrategy.semantics p)` is receptive (`Smallstep.atomic_receptive`
    applied to `semantics_strongly_receptive`). -/
theorem atomic_semantics_receptive (p : Csyntax.Program)
    (hx : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv) :
    Smallstep.Receptive (Smallstep.atomic (semantics p)) :=
  Smallstep.atomic_receptive (semantics_strongly_receptive p hx)

end Cstrategy
end CC
