/-
  Port of `cfrontend/Cexec.v`, part 2: soundness and completeness of the
  executable versions of events, volatile accesses, accesses at a location and
  external calls (`Cexec.v` lines 149–705).

  Completeness lemmas that go from a symbol to its block and back (through
  `Genv.invert_symbol`) need the global environment's symbol table to be
  injective (`Genv.SymbInjective`).  In Rocq this is an invariant carried by
  every `genv`; here it is a hypothesis, which `Csem.globalenv p` satisfies
  (`Genv.symbInjective_globalenv`).
-/
import CCLib.cfrontend.Cexec
import CCLib.common.GlobalenvsTheory

namespace CC
namespace Cexec

open Csyntax Csem

/-- `Cexec.is_val_inv` -/
theorem isVal_inv {a : Csyntax.Expr} {v : Val} {ty : Ty} (h : isVal a = some (v, ty)) :
    a = .Eval v ty := by
  cases a <;> simp [isVal] at h; obtain ⟨rfl, rfl⟩ := h; rfl

/-- `Cexec.is_loc_inv` -/
theorem isLoc_inv {a : Csyntax.Expr} {b ofs bf ty}
    (h : isLoc a = some (b, ofs, bf, ty)) : a = .Eloc b ofs bf ty := by
  cases a <;> simp [isLoc] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl

section EXEC

variable (ge : Csem.CGenv)

/-! ## Events -/

/-- `Cexec.eventval_of_val_sound` -/
theorem eventvalOfVal_sound {v : Val} {t : ATyp} {ev : EventVal}
    (h : eventvalOfVal ge v t = some ev) : EventValMatch ge.genv_genv.toSenv ev t v := by
  cases v <;> simp only [eventvalOfVal] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; subst_vars; constructor; done)
    | (cases h; subst_vars; exact .ev_match_ptr _ _ _ ‹_› (Genv.invert_findSymbol ‹_›))

/-- `Cexec.eventval_of_val_complete` -/
theorem eventvalOfVal_complete (hinj : Genv.SymbInjective ge.genv_genv) {ev : EventVal}
    {t : ATyp} {v : Val} (h : EventValMatch ge.genv_genv.toSenv ev t v) :
    eventvalOfVal ge v t = some ev := by
  cases h with
  | ev_match_ptr id b ofs hp hf =>
      have hi := Genv.find_invertSymbol hinj hf
      simp only [eventvalOfVal, hi]
      simp only [Genv.toSenv] at hp
      simp [hp]
  | _ => simp [eventvalOfVal]

/-- `Cexec.list_eventval_of_val_sound` -/
theorem listEventvalOfVal_sound {vl : List Val} {tl : List ATyp} {evl : List EventVal}
    (h : listEventvalOfVal ge vl tl = some evl) :
    EventValListMatch ge.genv_genv.toSenv evl tl vl := by
  induction vl generalizing tl evl with
  | nil => cases tl <;> simp [listEventvalOfVal] at h; subst h; exact .evl_match_nil
  | cons v vl ih =>
      cases tl with
      | nil => simp [listEventvalOfVal] at h
      | cons t tl =>
          simp only [listEventvalOfVal] at h
          split at h
          · next ev1 h1 =>
              split at h
              · next evl' h2 =>
                  cases h
                  exact .evl_match_cons _ _ _ _ _ _ (eventvalOfVal_sound ge h1) (ih h2)
              · cases h
          · cases h

/-- `Cexec.list_eventval_of_val_complete` -/
theorem listEventvalOfVal_complete (hinj : Genv.SymbInjective ge.genv_genv) {evl tl vl}
    (h : EventValListMatch ge.genv_genv.toSenv evl tl vl) :
    listEventvalOfVal ge vl tl = some evl := by
  induction h with
  | evl_match_nil => rfl
  | evl_match_cons _ _ _ _ _ _ h1 _ ih =>
      simp [listEventvalOfVal, eventvalOfVal_complete ge hinj h1, ih]

/-- `Cexec.val_of_eventval_sound` -/
theorem valOfEventval_sound {ev : EventVal} {t : ATyp} {v : Val}
    (h : valOfEventval ge ev t = some v) : EventValMatch ge.genv_genv.toSenv ev t v := by
  cases ev <;> simp only [valOfEventval] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; subst_vars; constructor; done)
    | (cases h; subst_vars; exact .ev_match_ptr _ _ _ ‹_› ‹_›)

/-- `Cexec.val_of_eventval_complete` -/
theorem valOfEventval_complete {ev : EventVal} {t : ATyp} {v : Val}
    (h : EventValMatch ge.genv_genv.toSenv ev t v) : valOfEventval ge ev t = some v := by
  cases h with
  | ev_match_ptr id b ofs hp hf =>
      simp only [Genv.toSenv] at hp hf
      simp [valOfEventval, hp, hf]
  | _ => simp [valOfEventval]

/-! ## Volatile memory accesses -/

/-- `Cexec.do_volatile_load_sound` -/
theorem doVolatileLoad_sound {w chunk m b ofs w' t v}
    (h : doVolatileLoad ge w chunk m b ofs = some (w', t, v)) :
    VolatileLoad ge.genv_genv.toSenv chunk m b ofs t v ∧ PossibleTrace w t w' := by
  unfold doVolatileLoad at h
  split at h
  · next hvol =>
      split at h
      · next id hid =>
          split at h
          · cases h
          · next res w'' hnw =>
              split at h
              · next vres hv =>
                  cases h
                  exact ⟨.vol _ _ _ _ id res vres hvol (Genv.invert_findSymbol hid)
                      (valOfEventval_sound ge hv),
                    possibleTrace_single (.vload _ _ _ _ _ _ hnw)⟩
              · cases h
      · cases h
  · next hvol =>
      split at h
      · next v' hl =>
          cases h
          exact ⟨.nonvol _ _ _ _ _ (by simpa [Genv.toSenv] using hvol) hl, .nil _⟩
      · cases h

/-- `Cexec.do_volatile_load_complete` -/
theorem doVolatileLoad_complete (hinj : Genv.SymbInjective ge.genv_genv) {w chunk m b ofs w' t v}
    (h : VolatileLoad ge.genv_genv.toSenv chunk m b ofs t v) (hp : PossibleTrace w t w') :
    doVolatileLoad ge w chunk m b ofs = some (w', t, v) := by
  cases h with
  | vol id ev v hvol hf hm =>
      simp only [Genv.toSenv] at hvol hf
      have hev := possibleTrace_single_inv hp
      cases hev with
      | vload =>
          rename_i hnw
          simp [doVolatileLoad, hvol, Genv.find_invertSymbol hinj hf, hnw,
            valOfEventval_complete ge hm]
  | nonvol _ hvol hl =>
      simp only [Genv.toSenv] at hvol
      cases possibleTrace_E0_inv hp
      simp [doVolatileLoad, hvol, hl]

/-- `Cexec.do_volatile_store_sound` -/
theorem doVolatileStore_sound {w chunk m b ofs v w' t m' v'}
    (h : doVolatileStore ge w chunk m b ofs v = some (w', t, m', v')) :
    VolatileStore ge.genv_genv.toSenv chunk m b ofs v t m' ∧ PossibleTrace w t w' ∧ v' = v := by
  unfold doVolatileStore at h
  split at h
  · next hvol =>
      split at h
      · next id hid =>
          split at h
          · next ev hev =>
              split at h
              · next w'' hnw =>
                  cases h
                  exact ⟨.vol _ _ _ _ id ev v hvol (Genv.invert_findSymbol hid)
                      (eventvalOfVal_sound ge hev),
                    possibleTrace_single (.vstore _ _ _ _ _ _ hnw), rfl⟩
              · cases h
          · cases h
      · cases h
  · next hvol =>
      split at h
      · next m'' hs =>
          cases h
          exact ⟨.nonvol _ _ _ _ _ _ (by simpa [Genv.toSenv] using hvol) hs, .nil _, rfl⟩
      · cases h

/-- `Cexec.do_volatile_store_complete` -/
theorem doVolatileStore_complete (hinj : Genv.SymbInjective ge.genv_genv)
    {w chunk m b ofs v w' t m'}
    (h : VolatileStore ge.genv_genv.toSenv chunk m b ofs v t m') (hp : PossibleTrace w t w') :
    doVolatileStore ge w chunk m b ofs v = some (w', t, m', v) := by
  cases h with
  | vol id ev _ hvol hf hm =>
      simp only [Genv.toSenv] at hvol hf
      have hev := possibleTrace_single_inv hp
      cases hev with
      | vstore =>
          rename_i hnw
          simp [doVolatileStore, hvol, Genv.find_invertSymbol hinj hf, hnw,
            eventvalOfVal_complete ge hinj hm]
  | nonvol _ _ hvol hs =>
      simp only [Genv.toSenv] at hvol
      cases possibleTrace_E0_inv hp
      simp [doVolatileStore, hvol, hs]

/-! ## Accessing locations -/

/-- `Cexec.do_deref_loc_sound` -/
theorem doDerefLoc_sound {w ty m b ofs bf w' t v}
    (h : doDerefLoc ge w ty m b ofs bf = some (w', t, v)) :
    Csem.DerefLoc ge ty m b ofs bf t v ∧ PossibleTrace w t w' := by
  cases bf with
  | Full =>
      simp only [doDerefLoc] at h
      split at h
      · next chunk hm =>
          split at h
          · next hv =>
              split at h
              · next v' hl => cases h; exact ⟨.value _ _ hm hv hl, .nil _⟩
              · cases h
          · next hv =>
              obtain ⟨h1, h2⟩ := doVolatileLoad_sound ge h
              exact ⟨.volatile _ _ _ hm hv h1, h2⟩
      · next hm => cases h; exact ⟨.reference hm, .nil _⟩
      · next hm => cases h; exact ⟨.copy hm, .nil _⟩
      · cases h
  | Bits sz sg pos width =>
      simp only [doDerefLoc] at h
      split at h
      · next sz1 sg1 att =>
          by_cases hok : sz1 = sz ∧ sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg)
              ∧ bitfieldRangeOk sz pos width
          · rw [if_pos hok] at h
            obtain ⟨hsz, hsg, hpos, hw0, hwle, hcar⟩ := hok
            subst hsz
            split at h
            · next c hl =>
                cases h
                exact ⟨.bitfield _ _ _ _ _
                  (.intro _ _ _ _ _ _ _ _ _ hpos hw0 hwle hcar hsg hl), .nil _⟩
            · cases h
          · rw [if_neg hok] at h; cases h
      · cases h

/-- `Cexec.do_deref_loc_complete` -/
theorem doDerefLoc_complete (hinj : Genv.SymbInjective ge.genv_genv) {w ty m b ofs bf w' t v}
    (h : Csem.DerefLoc ge ty m b ofs bf t v) (hp : PossibleTrace w t w') :
    doDerefLoc ge w ty m b ofs bf = some (w', t, v) := by
  cases h with
  | value chunk v hm hv hl =>
      cases possibleTrace_E0_inv hp
      simp [doDerefLoc, hm, hv, hl]
  | volatile chunk t v hm hv hl =>
      simp only [doDerefLoc, hm, hv]
      exact doVolatileLoad_complete ge hinj hl hp
  | reference hm =>
      cases possibleTrace_E0_inv hp
      simp [doDerefLoc, hm]
  | copy hm =>
      cases possibleTrace_E0_inv hp
      simp [doDerefLoc, hm]
  | bitfield sz sg pos width v hlb =>
      cases possibleTrace_E0_inv hp
      cases hlb with
      | intro _ sg1 attr _ _ _ _ _ c hpos hw0 hwle hcar hsg hl =>
          simp [doDerefLoc, ← hsg, hl, bitfieldRangeOk, hpos, hw0, hwle, hcar]

/-- `Cexec.do_assign_loc_sound` -/
theorem doAssignLoc_sound {w ty m b ofs bf v w' t m' v'}
    (h : doAssignLoc ge w ty m b ofs bf v = some (w', t, m', v')) :
    Csem.AssignLoc ge ty m b ofs bf v t m' v' ∧ PossibleTrace w t w' := by
  cases bf with
  | Full =>
      simp only [doAssignLoc] at h
      split at h
      · next chunk hm =>
          split at h
          · next hv =>
              split at h
              · next m'' hs => cases h; exact ⟨.value _ _ _ hm hv hs, .nil _⟩
              · cases h
          · next hv =>
              obtain ⟨h1, h2, h3⟩ := doVolatileStore_sound ge h
              subst h3
              exact ⟨.volatile _ _ _ _ hm hv h1, h2⟩
      · next hm =>
          split at h
          · next b' ofs' =>
              split at h
              · next hok =>
                  obtain ⟨ha1, ha2, hov⟩ := hok
                  split at h
                  · next bytes hlb =>
                      split at h
                      · next m'' hsb =>
                          cases h
                          exact ⟨.copy _ _ _ _ hm ha1 ha2 hov hlb hsb, .nil _⟩
                      · cases h
                  · cases h
              · cases h
          · cases h
      · cases h
  | Bits sz sg pos width =>
      simp only [doAssignLoc] at h
      by_cases hrange : bitfieldRangeOk sz pos width
      · rw [if_pos hrange] at h
        obtain ⟨hpos, hw0, hwle, hcar⟩ := hrange
        split at h
        · next sz1 sg1 att n c hl =>
            by_cases hok : sz1 = sz ∧ sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg)
            · rw [if_pos hok] at h
              obtain ⟨hsz, hsg⟩ := hok
              subst hsz
              split at h
              · next m'' hs =>
                  cases h
                  exact ⟨.bitfield _ _ _ _ _ _ _
                    (.intro _ _ _ _ _ _ _ _ _ _ _ hpos hw0 hwle hcar hsg hl hs), .nil _⟩
              · cases h
            · rw [if_neg hok] at h; cases h
        · cases h
      · rw [if_neg hrange] at h; cases h

/-- `Cexec.do_assign_loc_complete` -/
theorem doAssignLoc_complete (hinj : Genv.SymbInjective ge.genv_genv)
    {w ty m b ofs bf v w' t m' v'}
    (h : Csem.AssignLoc ge ty m b ofs bf v t m' v') (hp : PossibleTrace w t w') :
    doAssignLoc ge w ty m b ofs bf v = some (w', t, m', v') := by
  cases h with
  | value v chunk m' hm hv hs =>
      cases possibleTrace_E0_inv hp
      simp [doAssignLoc, hm, hv, hs]
  | volatile v chunk t m' hm hv hs =>
      simp only [doAssignLoc, hm, hv]
      exact doVolatileStore_complete ge hinj hs hp
  | copy b' ofs' bytes m' hm ha1 ha2 hov hlb hsb =>
      cases possibleTrace_E0_inv hp
      have hok : AssignCopyOk ge ty b ofs b' ofs' := ⟨ha1, ha2, hov⟩
      simp [doAssignLoc, hm, if_pos hok, hlb, hsb]
  | bitfield sz sg pos width v m' v' hsb =>
      cases possibleTrace_E0_inv hp
      cases hsb with
      | intro _ sg1 attr _ _ _ _ _ c n _ hpos hw0 hwle hcar hsg hl hs =>
          simp [doAssignLoc, ← hsg, hl, hs, bitfieldRangeOk, hpos, hw0, hwle, hcar]

end EXEC

/-! ## External calls -/

/-- The hypotheses `do_external_function_sound` and `do_inline_assembly_sound`
    of `Cexec.v`: whatever the oracle returns is allowed by the (axiomatized)
    semantics of external functions and inline assembly, and the trace is
    accepted by the world. -/
structure ExtOracle.Sound (ox : ExtOracle) : Prop where
  external : ∀ id sg ge vargs m t vres m' w w',
    ox.doExternalFunction id sg ge w vargs m = some (w', t, vres, m') →
    externalFunctionsSem id sg ge vargs m t vres m' ∧ PossibleTrace w t w'
  inlineAsm : ∀ txt sg ge vargs m t vres m' w w',
    ox.doInlineAssembly txt sg ge w vargs m = some (w', t, vres, m') →
    inlineAssemblySem txt sg ge vargs m t vres m' ∧ PossibleTrace w t w'

/-- The hypotheses `do_external_function_complete` and
    `do_inline_assembly_complete` of `Cexec.v`. -/
structure ExtOracle.Complete (ox : ExtOracle) : Prop where
  external : ∀ id sg ge vargs m t vres m' w w',
    externalFunctionsSem id sg ge vargs m t vres m' → PossibleTrace w t w' →
    ox.doExternalFunction id sg ge w vargs m = some (w', t, vres, m')
  inlineAsm : ∀ txt sg ge vargs m t vres m' w w',
    inlineAssemblySem txt sg ge vargs m t vres m' → PossibleTrace w t w' →
    ox.doInlineAssembly txt sg ge w vargs m = some (w', t, vres, m')

/-- The oracle that runs nothing is sound. -/
theorem ExtOracle.none_sound : ExtOracle.none.Sound :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ _ _ _ h => (by cases h)⟩

theorem doAllocSize_sound {v : Val} {sz : Integers.Ptrofs} (h : doAllocSize v = some sz) :
    v = Val.Vptrofs sz := by
  cases v with
  | Vlong n =>
      simp only [doAllocSize, Archi.ptr64, if_true] at h
      cases h
      simp [Val.Vptrofs, Archi.ptr64, Integers.Ptrofs.to_int64,
            Integers.Ptrofs.of_int64, Integers.MI.repr, Integers.MI.unsigned]
  | Vint n => simp only [doAllocSize, Archi.ptr64, if_true] at h; exact absurd h (by simp)
  | _ => simp only [doAllocSize] at h; exact absurd h (by simp)

theorem doAllocSize_complete (n : Integers.Ptrofs) : doAllocSize (Val.Vptrofs n) = some n := by
  simp [doAllocSize, Val.Vptrofs, Archi.ptr64, Integers.Ptrofs.to_int64,
        Integers.Ptrofs.of_int64, Integers.MI.repr, Integers.MI.unsigned]

section EXT

variable (ge : Csem.CGenv) (ox : ExtOracle)

/-- `Cexec.do_ef_external_sound` -/
theorem doExternal_sound (hox : ox.Sound) {ef w vargs m w' t vres m'}
    (h : doExternal ge ox ef w vargs m = some (w', t, vres, m')) :
    externalCall ef ge.genv_genv.toSenv vargs m t vres m' ∧ PossibleTrace w t w' := by
  have BF_EX : ∀ name sg,
      doBuiltinOrExternal ge ox name sg w vargs m = some (w', t, vres, m') →
      builtinOrExternalSem name sg ge.genv_genv.toSenv vargs m t vres m' ∧
        PossibleTrace w t w' := by
    intro name sg h
    unfold doBuiltinOrExternal at h
    unfold builtinOrExternalSem
    split at h
    · next bf hbf =>
        rw [hbf]
        split at h
        · next v hv => cases h; exact ⟨.intro _ _ _ _ hv, .nil _⟩
        · cases h
    · next hbf =>
        rw [hbf]
        exact hox.external _ _ _ _ _ _ _ _ _ _ h
  cases ef with
  | EF_external name sg => exact hox.external _ _ _ _ _ _ _ _ _ _ h
  | EF_builtin name sg => exact BF_EX _ _ h
  | EF_runtime name sg => exact BF_EX _ _ h
  | EF_vload chunk =>
      simp only [doExternal, doEfVolatileLoad] at h
      split at h
      · next b ofs =>
          split at h
          · next w'' t'' v hv =>
              cases h
              obtain ⟨h1, h2⟩ := doVolatileLoad_sound ge hv
              exact ⟨.intro _ _ _ _ _ _ h1, h2⟩
          · cases h
      · cases h
  | EF_vstore chunk =>
      simp only [doExternal, doEfVolatileStore] at h
      split at h
      · next b ofs v =>
          split at h
          · next w'' t'' m'' v'' hv =>
              cases h
              obtain ⟨h1, h2, _⟩ := doVolatileStore_sound ge hv
              exact ⟨.intro _ _ _ _ _ _ _ h1, h2⟩
          · cases h
      · cases h
  | EF_malloc =>
      simp only [doExternal, doEfMalloc] at h
      split at h
      · next v =>
          split at h
          · next sz hsz =>
              split at h
              · next m'' hst =>
                  cases h
                  have hv := doAllocSize_sound hsz
                  subst hv
                  exact ⟨.intro _ _ _ _ _ _ rfl hst, .nil _⟩
              · cases h
          · cases h
      · cases h
  | EF_free =>
      simp only [doExternal, doEfFree] at h
      split at h
      · next b lo =>
          split at h
          · next vsz hload =>
              split at h
              · next sz hsz =>
                  split at h
                  · next mf hfree =>
                      cases h
                      rw [doAllocSize_sound hsz] at hload
                      exact ⟨.ptr _ _ _ _ _ _ hload hfree, .nil _⟩
                  · cases h
              · cases h
          · cases h
      · next n =>
          split at h
          · next hc => exact absurd hc.2 (by simp [Archi.ptr64])
          · cases h
      · next n =>
          split at h
          · next hc =>
              cases h
              obtain ⟨hn, _⟩ := hc
              subst hn
              exact ⟨.null _ _, .nil _⟩
          · cases h
      · cases h
  | EF_memcpy sz al =>
      simp only [doExternal, doEfMemcpy] at h
      split at h
      · next bdst odst bsrc osrc =>
          split at h
          · next hok =>
              obtain ⟨hal, hsz0, hdvd, hsrc, hdst, hno⟩ := hok
              split at h
              · next bytes hlb =>
                  split at h
                  · next mc hsb =>
                      cases h
                      exact ⟨.intro _ _ _ _ _ _ _ _ hal hsz0 hdvd hsrc hdst hno hlb hsb, .nil _⟩
                  · cases h
              · cases h
          · cases h
      · cases h
  | EF_annot kind text targs =>
      simp only [doExternal, doEfAnnot] at h
      split at h
      · next args hargs =>
          cases h
          exact ⟨.intro _ _ _ _ (listEventvalOfVal_sound ge hargs),
            possibleTrace_single (.annot _ _ _)⟩
      · cases h
  | EF_annot_val kind text targ =>
      simp only [doExternal, doEfAnnotVal] at h
      split at h
      · next varg =>
          split at h
          · next arg harg =>
              cases h
              exact ⟨.intro _ _ _ _ (eventvalOfVal_sound ge harg),
                possibleTrace_single (.annot _ _ _)⟩
          · cases h
      · cases h
  | EF_inline_asm text sg clob => exact hox.inlineAsm _ _ _ _ _ _ _ _ _ _ h
  | EF_debug kind text targs =>
      simp only [doExternal, doEfDebug] at h
      cases h
      exact ⟨.intro _ _ _, .nil _⟩

/-- `Cexec.do_ef_external_complete` -/
theorem doExternal_complete (hinj : Genv.SymbInjective ge.genv_genv) (hox : ox.Complete)
    {ef w vargs m w' t vres m'}
    (h : externalCall ef ge.genv_genv.toSenv vargs m t vres m') (hp : PossibleTrace w t w') :
    doExternal ge ox ef w vargs m = some (w', t, vres, m') := by
  have BF_EX : ∀ name sg,
      builtinOrExternalSem name sg ge.genv_genv.toSenv vargs m t vres m' →
      doBuiltinOrExternal ge ox name sg w vargs m = some (w', t, vres, m') := by
    intro name sg h
    unfold doBuiltinOrExternal
    unfold builtinOrExternalSem at h
    cases hbf : Builtins.lookupBuiltinFunction name sg with
    | some bf =>
        rw [hbf] at h
        cases h with
        | intro _ _ _ _ hv =>
            cases possibleTrace_E0_inv hp
            simp [hv]
    | none =>
        rw [hbf] at h
        exact hox.external _ _ _ _ _ _ _ _ _ _ h hp
  cases ef with
  | EF_external name sg => exact hox.external _ _ _ _ _ _ _ _ _ _ h hp
  | EF_builtin name sg => exact BF_EX _ _ h
  | EF_runtime name sg => exact BF_EX _ _ h
  | EF_vload chunk =>
      cases h with
      | intro _ b ofs _ _ _ hl =>
          simp [doExternal, doEfVolatileLoad, doVolatileLoad_complete ge hinj hl hp]
  | EF_vstore chunk =>
      cases h with
      | intro _ b ofs _ v _ _ hs =>
          simp [doExternal, doEfVolatileStore, doVolatileStore_complete ge hinj hs hp]
  | EF_malloc =>
      cases h with
      | intro _ sz _ m1 b _ hal hst =>
          cases possibleTrace_E0_inv hp
          simp [doExternal, doEfMalloc, doAllocSize_complete, hal, hst]
  | EF_free =>
      cases h with
      | ptr _ b lo sz _ _ hl hf =>
          cases possibleTrace_E0_inv hp
          simp [doExternal, doEfFree, hl, doAllocSize_complete, hf]
      | null =>
          cases possibleTrace_E0_inv hp
          simp [doExternal, doEfFree, Val.Vnullptr, Archi.ptr64]
  | EF_memcpy sz al =>
      cases h with
      | intro _ bdst odst bsrc osrc _ bytes _ hal hsz0 hdvd hsrc hdst hno hlb hsb =>
          cases possibleTrace_E0_inv hp
          have hok : MemcpyArgsOk sz al bdst (Integers.Ptrofs.unsigned odst) bsrc
              (Integers.Ptrofs.unsigned osrc) := ⟨hal, hsz0, hdvd, hsrc, hdst, hno⟩
          simp only [doExternal, doEfMemcpy, if_pos hok, hlb, hsb]
  | EF_annot kind text targs =>
      cases h with
      | intro _ _ _ args hargs =>
          cases possibleTrace_single_inv hp
          simp [doExternal, doEfAnnot, listEventvalOfVal_complete ge hinj hargs]
  | EF_annot_val kind text targ =>
      cases h with
      | intro _ varg _ arg harg =>
          cases possibleTrace_single_inv hp
          simp [doExternal, doEfAnnotVal, eventvalOfVal_complete ge hinj harg]
  | EF_inline_asm text sg clob => exact hox.inlineAsm _ _ _ _ _ _ _ _ _ _ h hp
  | EF_debug kind text targs =>
      cases h
      cases possibleTrace_E0_inv hp
      rfl

end EXT

end Cexec
end CC
