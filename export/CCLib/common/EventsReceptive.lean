/-
  `ec_receptive` from CompCert's `extcall_properties` (`common/Events.v`):
  if an external call can produce trace `t1`, it can also produce any trace
  `t2` that `match_traces` relates to `t1` (that is, any other value the
  outside world may return for a volatile load).

  CompCert's proof for volatile loads uses `Senv.public_symbol_exists`, an
  invariant carried by its proof-carrying `Senv.t`.  The port's `Senv` carries
  no invariants, so the property is stated here as the predicate
  `Senv.PublicSymbolExists`, and `Genv.toSenv_publicSymbolExists` proves it for
  every global environment.

  As in the other `Events*` files, the uninterpreted externals contribute the
  property as a hypothesis; this file adds no axioms.
-/
import CCLib.common.EventsProps
import CCLib.common.GlobalenvsTheory

namespace CC

/-- `Senv.public_symbol_exists` -/
def Senv.PublicSymbolExists (ge : Senv) : Prop :=
  ∀ id, ge.public_symbol id = true → ∃ b, ge.find_symbol id = some b

theorem Genv.toSenv_publicSymbolExists {F V : Type} (ge : Genv F V) :
    (Genv.toSenv ge).PublicSymbolExists :=
  fun _ h => Genv.publicSymbol_exists h

/-- `ec_receptive`, for one symbol environment. -/
def ExtcallReceptive (sem : ExtcallSem) (ge : Senv) : Prop :=
  ∀ vargs m t1 vres1 m1 t2, sem ge vargs m t1 vres1 m1 → MatchTraces ge t1 t2 →
    ∃ vres2 m2, sem ge vargs m t2 vres2 m2

namespace EventsReceptive

/-- `Events.eventval_valid_match` -/
theorem eventValValid_match {ge : Senv} (hp : ge.PublicSymbolExists) {ev : EventVal}
    (h : EventValValid ge ev) : ∃ v, EventValMatch ge ev (eventvalType ev) v := by
  cases ev with
  | EVint i => exact ⟨_, .ev_match_int i⟩
  | EVlong i => exact ⟨_, .ev_match_long i⟩
  | EVfloat f => exact ⟨_, .ev_match_float f⟩
  | EVsingle f => exact ⟨_, .ev_match_single f⟩
  | EVptr_global id ofs =>
    obtain ⟨b, hb⟩ := hp id h
    exact ⟨_, .ev_match_ptr id b ofs h hb⟩

theorem matchTraces_E0 {ge : Senv} {t : Trace} (h : MatchTraces ge E0 t) : t = E0 := by
  generalize he : E0 = t1 at h
  cases h <;> simp_all [E0]

theorem matchTraces_vstore {ge : Senv} {chunk id ofs ev} {t : Trace}
    (h : MatchTraces ge [Event.Event_vstore chunk id ofs ev] t) :
    t = [Event.Event_vstore chunk id ofs ev] := by
  generalize he : [Event.Event_vstore chunk id ofs ev] = t1 at h
  cases h <;> simp_all [E0]

theorem matchTraces_annot {ge : Senv} {text args} {t : Trace}
    (h : MatchTraces ge [Event.Event_annot text args] t) :
    t = [Event.Event_annot text args] := by
  generalize he : [Event.Event_annot text args] = t1 at h
  cases h <;> simp_all [E0]

/-- A semantics that only ever emits the empty trace is receptive. -/
theorem of_E0 {sem : ExtcallSem} {ge : Senv}
    (h : ∀ vargs m t vres m', sem ge vargs m t vres m' → t = E0) : ExtcallReceptive sem ge := by
  intro vargs m t1 vres1 m1 t2 hs hm
  have ht := h _ _ _ _ _ hs
  subst ht
  rw [matchTraces_E0 hm]
  exact ⟨_, _, hs⟩

theorem volatileLoadSem_receptive (chunk : Chunk) {ge : Senv} (hp : ge.PublicSymbolExists) :
    ExtcallReceptive (VolatileLoadSem chunk) ge := by
  intro vargs m t1 vres1 m1 t2 hs hm
  cases hs with
  | intro _ b ofs _ _ _ hl =>
    rcases volatileLoad_inv hl with ⟨id, ev, w, hv, hf, hmt, rfl, rfl⟩ | ⟨hv, rfl, hld⟩
    · generalize he : [Event.Event_vload chunk id ofs ev] = t1 at hm
      cases hm with
      | vload chunk' id' ofs' res1 res2 _ hval2 hty =>
        simp only [List.cons.injEq, Event.Event_vload.injEq, and_true] at he
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        obtain ⟨v2, hm2⟩ := eventValValid_match hp hval2
        rw [← hty, eventValMatch_type hmt] at hm2
        exact ⟨_, _, .intro _ _ _ _ _ _ (.vol _ _ _ _ id res2 v2 hv hf hm2)⟩
      | _ => simp_all [E0]
    · rw [matchTraces_E0 hm]
      exact ⟨_, _, .intro _ _ _ _ _ _ (.nonvol _ _ _ _ _ hv hld)⟩

theorem volatileStoreSem_receptive (chunk : Chunk) (ge : Senv) :
    ExtcallReceptive (VolatileStoreSem chunk) ge := by
  intro vargs m t1 vres1 m1 t2 hs hm
  cases hs with
  | intro _ b ofs _ v _ _ hst =>
    rcases volatileStore_inv hst with ⟨id, ev, _, _, _, rfl, rfl⟩ | ⟨_, rfl, _⟩
    · rw [matchTraces_vstore hm]; exact ⟨_, _, .intro _ _ _ _ _ _ _ hst⟩
    · rw [matchTraces_E0 hm]; exact ⟨_, _, .intro _ _ _ _ _ _ _ hst⟩

theorem extcallMallocSem_receptive (ge : Senv) : ExtcallReceptive ExtcallMallocSem ge :=
  of_E0 fun _ _ _ _ _ h => by cases h; rfl

theorem extcallFreeSem_receptive (ge : Senv) : ExtcallReceptive ExtcallFreeSem ge :=
  of_E0 fun _ _ _ _ _ h => by cases h <;> rfl

theorem extcallMemcpySem_receptive (sz al : Z) (ge : Senv) :
    ExtcallReceptive (ExtcallMemcpySem sz al) ge :=
  of_E0 fun _ _ _ _ _ h => by cases h; rfl

theorem extcallAnnotSem_receptive (text : String) (targs : List ATyp) (ge : Senv) :
    ExtcallReceptive (ExtcallAnnotSem text targs) ge := by
  intro vargs m t1 vres1 m1 t2 hs hm
  cases hs with
  | intro _ _ _ _ hl => rw [matchTraces_annot hm]; exact ⟨_, _, .intro _ _ _ _ hl⟩

theorem extcallAnnotValSem_receptive (text : String) (targ : ATyp) (ge : Senv) :
    ExtcallReceptive (ExtcallAnnotValSem text targ) ge := by
  intro vargs m t1 vres1 m1 t2 hs hm
  cases hs with
  | intro _ _ _ _ hl => rw [matchTraces_annot hm]; exact ⟨_, _, .intro _ _ _ _ hl⟩

theorem extcallDebugSem_receptive (ge : Senv) : ExtcallReceptive ExtcallDebugSem ge :=
  of_E0 fun _ _ _ _ _ h => by cases h; rfl

theorem knownBuiltinSem_receptive (bf : Builtins.BuiltinFunction) (ge : Senv) :
    ExtcallReceptive (KnownBuiltinSem bf) ge :=
  of_E0 fun _ _ _ _ _ h => by cases h; rfl

theorem builtinOrExternalSem_receptive (name : String) (sg : Signature) (ge : Senv)
    (hext : ExtcallReceptive (externalFunctionsSem name sg) ge) :
    ExtcallReceptive (builtinOrExternalSem name sg) ge := by
  unfold builtinOrExternalSem
  split
  · exact knownBuiltinSem_receptive _ ge
  · exact hext

end EventsReceptive

/-- `ec_receptive` for every external call (CompCert's `external_call_receptive`):
    proved for every external call whose semantics the port defines, in any
    symbol environment satisfying `public_symbol_exists`; the uninterpreted
    externals contribute it as hypotheses `hext`/`hasm`, as CompCert assumes it
    by axiom. -/
theorem externalCall_receptive (ef : ExtFun) {ge : Senv} (hp : ge.PublicSymbolExists)
    (hext : ∀ name sg, ExtcallReceptive (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg, ExtcallReceptive (inlineAssemblySem name sg) ge) :
    ExtcallReceptive (externalCall ef) ge := by
  cases ef with
  | EF_external name sg => exact hext name sg
  | EF_builtin name sg =>
    exact EventsReceptive.builtinOrExternalSem_receptive name sg ge (hext name sg)
  | EF_runtime name sg =>
    exact EventsReceptive.builtinOrExternalSem_receptive name sg ge (hext name sg)
  | EF_vload chunk => exact EventsReceptive.volatileLoadSem_receptive chunk hp
  | EF_vstore chunk => exact EventsReceptive.volatileStoreSem_receptive chunk ge
  | EF_malloc => exact EventsReceptive.extcallMallocSem_receptive ge
  | EF_free => exact EventsReceptive.extcallFreeSem_receptive ge
  | EF_memcpy sz al => exact EventsReceptive.extcallMemcpySem_receptive sz al ge
  | EF_annot _ txt targs => exact EventsReceptive.extcallAnnotSem_receptive txt targs ge
  | EF_annot_val _ txt targ => exact EventsReceptive.extcallAnnotValSem_receptive txt targ ge
  | EF_inline_asm txt sg _ => exact hasm txt sg
  | EF_debug _ _ _ => exact EventsReceptive.extcallDebugSem_receptive ge

end CC
