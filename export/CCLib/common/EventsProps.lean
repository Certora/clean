/-
  The two remaining non-memory fields of CompCert's `extcall_properties`
  (`common/Events.v`) for the external calls whose semantics the port defines:

  * `ec_well_typed` — the result of an external call has the result type of
    its signature (`ExtcallWellTyped`, `externalCall_wellTyped`);
  * `ec_symbols_preserved` — an external call only observes the symbol
    environment through `find_symbol`, `public_symbol` and
    `block_is_volatile`, so it runs the same in any equivalent environment
    (`Senv.Equiv`, `ExtcallSymbolsPreserved`, `externalCall_symbolsPreserved`).

  As in `CCLib.common.EventsExtends`/`CCLib.common.EventsInject`, the uninterpreted externals
  (`externalFunctionsSem`, `inlineAssemblySem`), which CompCert constrains by
  axiom, contribute the property as a hypothesis; this file adds no axioms.

  For `EF_vload` the result type is CompCert's `xtype_of_chunk chunk`
  (`Chunk.xtype`), so for example an 8-bit signed volatile load is shown to
  return a sign-extended value.
-/
import CCLib.common.Events
import CCLib.common.MemoryTheory

namespace CC

/-! ## `ec_well_typed` -/

/-- `ec_well_typed`, for an external call with signature `sg`. -/
def ExtcallWellTyped (sem : ExtcallSem) (sg : Signature) : Prop :=
  ∀ ge vargs m t vres m', sem ge vargs m t vres m' → Val.hasRettype vres sg.sig_res

namespace EventsProps

theorem normBool_zeroExt_hasRettype (n : Integers.Int) :
    Val.hasRettype (Val.normBool (.Vint (Integers.Int.zero_ext 8 n))) .Xbool := by
  unfold Val.normBool
  split
  · rename_i h
    simp only [Val.isBool, Bool.or_eq_true, beq_iff_eq, Val.Vtrue, Val.Vfalse] at h
    rcases h with h | h <;> rw [h] <;> simp [Val.hasRettype]
  · simp [Val.hasRettype]

/-- `Val.load_result_rettype` -/
theorem loadResult_hasRettype (chunk : Chunk) (v : Val) :
    Val.hasRettype (Val.loadResult chunk v) chunk.xtype := by
  cases chunk <;> cases v <;>
    simp only [Val.loadResult, Chunk.xtype, Archi.ptr64, if_true] <;>
    first
      | exact normBool_zeroExt_hasRettype _
      | simp [Val.hasRettype, Integers.Int.sign_ext_idem, Integers.Int.zero_ext_idem]

/-- `Memdata.decode_val_rettype` -/
theorem decodeVal_hasRettype (chunk : Chunk) (vl : List MemVal) :
    Val.hasRettype (decodeVal chunk vl) chunk.xtype := by
  unfold decodeVal
  split
  · cases chunk <;> simp only [Chunk.xtype] <;>
      first
        | exact normBool_zeroExt_hasRettype _
        | simp [Val.hasRettype, Integers.Int.sign_ext_idem, Integers.Int.zero_ext_idem]
  · cases chunk <;> simp only [Archi.ptr64, if_true] <;>
      first | exact loadResult_hasRettype _ _ | simp [Val.hasRettype, Chunk.xtype]

/-- `Memory.load_rettype` -/
theorem load_hasRettype {chunk : Chunk} {m : Mem} {b : Block} {ofs : Z} {v : Val}
    (h : Mem.load chunk m b ofs = some v) : Val.hasRettype v chunk.xtype := by
  unfold Mem.load at h
  split at h
  · cases h; exact decodeVal_hasRettype _ _
  · cases h

/-- An event value matched at type `ty` denotes a value of result type `ty.inj`. -/
theorem eventValMatch_hasRettype {ge : Senv} {ev : EventVal} {ty : ATyp} {v : Val}
    (h : EventValMatch ge ev ty v) : Val.hasRettype v ty.inj := by
  cases h <;> simp [Val.hasRettype, ATyp.inj, Tptr, Archi.ptr64]

theorem volatileLoadSem_wellTyped (chunk : Chunk) :
    ExtcallWellTyped (VolatileLoadSem chunk) (ExtFun.sig (.EF_vload chunk)) := by
  intro ge vargs m t vres m' h
  cases h with
  | intro _ _ _ _ _ _ hl =>
    cases volatileLoad_inv hl with
    | inl p =>
      obtain ⟨_, _, _, _, _, _, _, hv⟩ := p
      subst hv; exact loadResult_hasRettype _ _
    | inr p => exact load_hasRettype p.2.2

theorem volatileStoreSem_wellTyped (chunk : Chunk) :
    ExtcallWellTyped (VolatileStoreSem chunk) (ExtFun.sig (.EF_vstore chunk)) := by
  intro ge vargs m t vres m' h
  cases h; simp [Val.hasRettype, ExtFun.sig, mksignature]

theorem extcallMallocSem_wellTyped :
    ExtcallWellTyped ExtcallMallocSem (ExtFun.sig .EF_malloc) := by
  intro ge vargs m t vres m' h
  cases h; simp [Val.hasRettype, ExtFun.sig, mksignature]

theorem extcallFreeSem_wellTyped :
    ExtcallWellTyped ExtcallFreeSem (ExtFun.sig .EF_free) := by
  intro ge vargs m t vres m' h
  cases h <;> simp [Val.hasRettype, ExtFun.sig, mksignature]

theorem extcallMemcpySem_wellTyped (sz al : Z) :
    ExtcallWellTyped (ExtcallMemcpySem sz al) (ExtFun.sig (.EF_memcpy sz al)) := by
  intro ge vargs m t vres m' h
  cases h; simp [Val.hasRettype, ExtFun.sig, mksignature]

theorem extcallAnnotSem_wellTyped (kind : Positive) (text : String) (targs : List ATyp) :
    ExtcallWellTyped (ExtcallAnnotSem text targs) (ExtFun.sig (.EF_annot kind text targs)) := by
  intro ge vargs m t vres m' h
  cases h; simp [Val.hasRettype, ExtFun.sig, mksignature]

theorem extcallAnnotValSem_wellTyped (kind : Positive) (text : String) (targ : ATyp) :
    ExtcallWellTyped (ExtcallAnnotValSem text targ)
      (ExtFun.sig (.EF_annot_val kind text targ)) := by
  intro ge vargs m t vres m' h
  cases h with
  | intro _ _ _ _ hm => exact eventValMatch_hasRettype hm

theorem extcallDebugSem_wellTyped (kind : Positive) (text : Ident) (targs : List ATyp) :
    ExtcallWellTyped ExtcallDebugSem (ExtFun.sig (.EF_debug kind text targs)) := by
  intro ge vargs m t vres m' h
  cases h; simp [Val.hasRettype, ExtFun.sig, mksignature]

theorem knownBuiltinSem_wellTyped (bf : Builtins.BuiltinFunction) :
    ExtcallWellTyped (KnownBuiltinSem bf) (Builtins.builtinFunctionSig bf) := by
  intro ge vargs m t vres m' h
  cases h with
  | intro _ _ _ _ hs =>
    have := (Builtins.builtinFunctionSem bf).well_typed vargs
    rw [hs] at this
    exact this

theorem builtinOrExternalSem_wellTyped (name : String) (sg : Signature)
    (hext : ExtcallWellTyped (externalFunctionsSem name sg) sg) :
    ExtcallWellTyped (builtinOrExternalSem name sg) sg := by
  unfold builtinOrExternalSem
  split
  · rename_i bf hbf
    rw [← Builtins.lookupBuiltinFunction_sig name sg bf hbf]
    exact knownBuiltinSem_wellTyped bf
  · exact hext

end EventsProps

/-- `ec_well_typed` for every external call (CompCert's `external_call_well_typed`):
    proved for every external call whose semantics the port defines; the
    uninterpreted externals contribute it as hypotheses `hext`/`hasm`, as CompCert
    assumes it by axiom. -/
theorem externalCall_wellTyped (ef : ExtFun)
    (hext : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasm : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ExtcallWellTyped (externalCall ef) ef.sig := by
  cases ef with
  | EF_external name sg => exact hext name sg
  | EF_builtin name sg => exact EventsProps.builtinOrExternalSem_wellTyped name sg (hext name sg)
  | EF_runtime name sg => exact EventsProps.builtinOrExternalSem_wellTyped name sg (hext name sg)
  | EF_vload chunk => exact EventsProps.volatileLoadSem_wellTyped chunk
  | EF_vstore chunk => exact EventsProps.volatileStoreSem_wellTyped chunk
  | EF_malloc => exact EventsProps.extcallMallocSem_wellTyped
  | EF_free => exact EventsProps.extcallFreeSem_wellTyped
  | EF_memcpy sz al => exact EventsProps.extcallMemcpySem_wellTyped sz al
  | EF_annot k txt targs => exact EventsProps.extcallAnnotSem_wellTyped k txt targs
  | EF_annot_val k txt targ => exact EventsProps.extcallAnnotValSem_wellTyped k txt targ
  | EF_inline_asm txt sg _ => exact hasm txt sg
  | EF_debug k txt targs => exact EventsProps.extcallDebugSem_wellTyped k txt targs

/-! ## `ec_symbols_preserved` -/

/-- `Senv.equiv`: two symbol environments that agree on `find_symbol`,
    `public_symbol` and `block_is_volatile`. -/
structure Senv.Equiv (ge1 ge2 : Senv) : Prop where
  find_symbol : ∀ id, ge2.find_symbol id = ge1.find_symbol id
  public_symbol : ∀ id, ge2.public_symbol id = ge1.public_symbol id
  block_is_volatile : ∀ b, ge2.block_is_volatile b = ge1.block_is_volatile b

/-- `ec_symbols_preserved` -/
def ExtcallSymbolsPreserved (sem : ExtcallSem) : Prop :=
  ∀ ge1 ge2 vargs m1 t vres m2, Senv.Equiv ge1 ge2 →
    sem ge1 vargs m1 t vres m2 → sem ge2 vargs m1 t vres m2

namespace EventsProps

/-- `Events.eventval_match_preserved` -/
theorem eventValMatch_preserved {ge1 ge2 : Senv} (he : Senv.Equiv ge1 ge2)
    {ev : EventVal} {ty : ATyp} {v : Val} (h : EventValMatch ge1 ev ty v) :
    EventValMatch ge2 ev ty v := by
  cases h with
  | ev_match_int => exact .ev_match_int _
  | ev_match_long => exact .ev_match_long _
  | ev_match_float => exact .ev_match_float _
  | ev_match_single => exact .ev_match_single _
  | ev_match_ptr id b ofs hp hf =>
    exact .ev_match_ptr _ _ _ (by rw [he.public_symbol]; exact hp)
      (by rw [he.find_symbol]; exact hf)

/-- `Events.eventval_list_match_preserved` -/
theorem eventValListMatch_preserved {ge1 ge2 : Senv} (he : Senv.Equiv ge1 ge2)
    {evl : List EventVal} {tyl : List ATyp} {vl : List Val}
    (h : EventValListMatch ge1 evl tyl vl) : EventValListMatch ge2 evl tyl vl := by
  induction h with
  | evl_match_nil => exact .evl_match_nil
  | evl_match_cons _ _ _ _ _ _ h1 _ ih =>
    exact .evl_match_cons _ _ _ _ _ _ (eventValMatch_preserved he h1) ih

/-- `Events.volatile_load_preserved` -/
theorem volatileLoad_preserved {ge1 ge2 : Senv} (he : Senv.Equiv ge1 ge2)
    {chunk : Chunk} {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {t : Trace} {v : Val}
    (h : VolatileLoad ge1 chunk m b ofs t v) : VolatileLoad ge2 chunk m b ofs t v := by
  rcases volatileLoad_inv h with ⟨id, ev, w, hv, hf, hm, rfl, rfl⟩ | ⟨hv, rfl, hl⟩
  · exact .vol _ _ _ _ id ev w (by rw [he.block_is_volatile]; exact hv)
      (by rw [he.find_symbol]; exact hf) (eventValMatch_preserved he hm)
  · exact .nonvol _ _ _ _ _ (by rw [he.block_is_volatile]; exact hv) hl

/-- `Events.volatile_store_preserved` -/
theorem volatileStore_preserved {ge1 ge2 : Senv} (he : Senv.Equiv ge1 ge2)
    {chunk : Chunk} {m : Mem} {b : Block} {ofs : Integers.Ptrofs} {v : Val} {t : Trace}
    {m' : Mem} (h : VolatileStore ge1 chunk m b ofs v t m') :
    VolatileStore ge2 chunk m b ofs v t m' := by
  rcases volatileStore_inv h with ⟨id, ev, hv, hf, hm, rfl, rfl⟩ | ⟨hv, rfl, hs⟩
  · exact .vol _ _ _ _ id ev _ (by rw [he.block_is_volatile]; exact hv)
      (by rw [he.find_symbol]; exact hf) (eventValMatch_preserved he hm)
  · exact .nonvol _ _ _ _ _ _ (by rw [he.block_is_volatile]; exact hv) hs

theorem volatileLoadSem_symbolsPreserved (chunk : Chunk) :
    ExtcallSymbolsPreserved (VolatileLoadSem chunk) := by
  intro ge1 ge2 vargs m1 t vres m2 he h
  cases h with
  | intro _ _ _ _ _ _ hl => exact .intro _ _ _ _ _ _ (volatileLoad_preserved he hl)

theorem volatileStoreSem_symbolsPreserved (chunk : Chunk) :
    ExtcallSymbolsPreserved (VolatileStoreSem chunk) := by
  intro ge1 ge2 vargs m1 t vres m2 he h
  cases h with
  | intro _ _ _ _ _ _ _ hs => exact .intro _ _ _ _ _ _ _ (volatileStore_preserved he hs)

theorem extcallMallocSem_symbolsPreserved : ExtcallSymbolsPreserved ExtcallMallocSem := by
  intro ge1 ge2 vargs m1 t vres m2 _ h
  cases h with
  | intro _ _ _ _ _ _ ha hs => exact .intro _ _ _ _ _ _ ha hs

theorem extcallFreeSem_symbolsPreserved : ExtcallSymbolsPreserved ExtcallFreeSem := by
  intro ge1 ge2 vargs m1 t vres m2 _ h
  cases h with
  | ptr _ _ _ _ _ _ hl hf => exact .ptr _ _ _ _ _ _ hl hf
  | null => exact .null _ _

theorem extcallMemcpySem_symbolsPreserved (sz al : Z) :
    ExtcallSymbolsPreserved (ExtcallMemcpySem sz al) := by
  intro ge1 ge2 vargs m1 t vres m2 _ h
  cases h with
  | intro _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .intro _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8

theorem extcallAnnotSem_symbolsPreserved (text : String) (targs : List ATyp) :
    ExtcallSymbolsPreserved (ExtcallAnnotSem text targs) := by
  intro ge1 ge2 vargs m1 t vres m2 he h
  cases h with
  | intro _ _ _ _ hm => exact .intro _ _ _ _ (eventValListMatch_preserved he hm)

theorem extcallAnnotValSem_symbolsPreserved (text : String) (targ : ATyp) :
    ExtcallSymbolsPreserved (ExtcallAnnotValSem text targ) := by
  intro ge1 ge2 vargs m1 t vres m2 he h
  cases h with
  | intro _ _ _ _ hm => exact .intro _ _ _ _ (eventValMatch_preserved he hm)

theorem extcallDebugSem_symbolsPreserved : ExtcallSymbolsPreserved ExtcallDebugSem := by
  intro ge1 ge2 vargs m1 t vres m2 _ h
  cases h; exact .intro _ _ _

theorem knownBuiltinSem_symbolsPreserved (bf : Builtins.BuiltinFunction) :
    ExtcallSymbolsPreserved (KnownBuiltinSem bf) := by
  intro ge1 ge2 vargs m1 t vres m2 _ h
  cases h with
  | intro _ _ _ _ hs => exact .intro _ _ _ _ hs

theorem builtinOrExternalSem_symbolsPreserved (name : String) (sg : Signature)
    (hext : ExtcallSymbolsPreserved (externalFunctionsSem name sg)) :
    ExtcallSymbolsPreserved (builtinOrExternalSem name sg) := by
  unfold builtinOrExternalSem
  split
  · exact knownBuiltinSem_symbolsPreserved _
  · exact hext

end EventsProps

/-- `ec_symbols_preserved` for every external call (CompCert's
    `external_call_symbols_preserved`): proved for every external call whose
    semantics the port defines; the uninterpreted externals contribute it as
    hypotheses `hext`/`hasm`, as CompCert assumes it by axiom. -/
theorem externalCall_symbolsPreserved (ef : ExtFun)
    (hext : ∀ name sg, ExtcallSymbolsPreserved (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallSymbolsPreserved (inlineAssemblySem name sg)) :
    ExtcallSymbolsPreserved (externalCall ef) := by
  cases ef with
  | EF_external name sg => exact hext name sg
  | EF_builtin name sg =>
    exact EventsProps.builtinOrExternalSem_symbolsPreserved name sg (hext name sg)
  | EF_runtime name sg =>
    exact EventsProps.builtinOrExternalSem_symbolsPreserved name sg (hext name sg)
  | EF_vload chunk => exact EventsProps.volatileLoadSem_symbolsPreserved chunk
  | EF_vstore chunk => exact EventsProps.volatileStoreSem_symbolsPreserved chunk
  | EF_malloc => exact EventsProps.extcallMallocSem_symbolsPreserved
  | EF_free => exact EventsProps.extcallFreeSem_symbolsPreserved
  | EF_memcpy sz al => exact EventsProps.extcallMemcpySem_symbolsPreserved sz al
  | EF_annot _ txt targs => exact EventsProps.extcallAnnotSem_symbolsPreserved txt targs
  | EF_annot_val _ txt targ => exact EventsProps.extcallAnnotValSem_symbolsPreserved txt targ
  | EF_inline_asm txt sg _ => exact hasm txt sg
  | EF_debug _ _ _ => exact EventsProps.extcallDebugSem_symbolsPreserved

end CC
