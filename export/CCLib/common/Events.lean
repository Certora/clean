/-
  Observable events and external calls — the minimal slice of `common/Events.v`
  the Clight semantics needs (~250 of its 1819 lines).

  What is here: `eventval`, `event`, `trace`/`E0`/`Eapp`, `eventval_match`, the
  volatile load/store relations, and real semantics for the builtins a C program
  actually uses — `malloc`, `free`, `memcpy`, `annot`, `annot_val`, `debug`.

  What is deliberately NOT here:
  * `traceinf` and the infinite-trace machinery (CoInductive in Rocq).  These
    now live in `CCLib/common/Smallstep.lean` (infinite traces as event streams) and
    `CCLib/common/Behaviors.lean`.
  * `extcall_properties` and the ~770 lines proving each builtin satisfies it —
    that is pass-proof support.
  * `eventval_valid`, `symbols_inject`, `match_traces`, `eval_builtin_arg`.

  Unknown external functions and inline assembly are left UNINTERPRETED, exactly
  as in Rocq: `Events.v` lines 1487-1497 declare them with `Parameter` +
  `Axiom`, so the corresponding Lean `axiom`s below are faithful rather than a
  shortcut.  They are Prop-valued relations, hence consistent (the always-false
  relation instantiates them).
-/
import CCLib.common.Globalenvs
import CCLib.common.Builtins

namespace CC

/-! ## Symbol environments (`Events.Senv`)

A non-dependent record of lookup functions, as in Rocq; `Genv.toSenv` builds one.
Keeping `Events` over `Senv` rather than `Genv` is what makes it independent of
the function/variable type parameters. -/

structure Senv where
  find_symbol : Ident → Option Block
  public_symbol : Ident → Bool
  invert_symbol : Block → Option Ident
  block_is_volatile : Block → Bool

/-- `Genv.to_senv` -/
def Genv.toSenv {F V : Type} (ge : Genv F V) : Senv :=
  { find_symbol := Genv.findSymbol ge
    public_symbol := Genv.publicSymbol ge
    invert_symbol := Genv.invertSymbol ge
    block_is_volatile := Genv.blockIsVolatile ge }

/-! ## Events and traces -/

/-- `Events.eventval` — a value as it appears in an observable event. -/
inductive EventVal where
  | EVint (i : Integers.Int)
  | EVlong (i : Integers.Int64)
  | EVfloat (f : Floats.Float)
  | EVsingle (f : Floats.Float32)
  | EVptr_global (id : Ident) (ofs : Integers.Ptrofs)
  deriving DecidableEq, Repr, Inhabited

/-- `Events.event` -/
inductive Event where
  | Event_syscall (name : String) (args : List EventVal) (res : EventVal)
  | Event_vload (chunk : Chunk) (id : Ident) (ofs : Integers.Ptrofs) (v : EventVal)
  | Event_vstore (chunk : Chunk) (id : Ident) (ofs : Integers.Ptrofs) (v : EventVal)
  | Event_annot (text : String) (args : List EventVal)
  deriving DecidableEq, Repr, Inhabited

/-- `Events.trace` -/
abbrev Trace := List Event
/-- `Events.E0` — the empty trace. -/
def E0 : Trace := []
/-- `Events.Eapp` -/
def Eapp (t1 t2 : Trace) : Trace := t1 ++ t2

/-- `Events.eventval_match` — which values a given event value may denote. -/
inductive EventValMatch (ge : Senv) : EventVal → ATyp → Val → Prop where
  | ev_match_int (i) : EventValMatch ge (.EVint i) .Tint (.Vint i)
  | ev_match_long (i) : EventValMatch ge (.EVlong i) .Tlong (.Vlong i)
  | ev_match_float (f) : EventValMatch ge (.EVfloat f) .Tfloat (.Vfloat f)
  | ev_match_single (f) : EventValMatch ge (.EVsingle f) .Tsingle (.Vsingle f)
  | ev_match_ptr (id b ofs) :
      ge.public_symbol id = true →
      ge.find_symbol id = some b →
      EventValMatch ge (.EVptr_global id ofs) Tptr (.Vptr b ofs)

/-- `Events.eventval_list_match` -/
inductive EventValListMatch (ge : Senv) :
    List EventVal → List ATyp → List Val → Prop where
  | evl_match_nil : EventValListMatch ge [] [] []
  | evl_match_cons (ev1 ty1 v1 evl tyl vl) :
      EventValMatch ge ev1 ty1 v1 →
      EventValListMatch ge evl tyl vl →
      EventValListMatch ge (ev1 :: evl) (ty1 :: tyl) (v1 :: vl)

/-! ## Volatile accesses

A load from (or store to) a *volatile* global produces an observable event and
does not touch memory; any other address behaves like a plain access. -/

/-- `Events.volatile_load` -/
inductive VolatileLoad (ge : Senv) :
    Chunk → Mem → Block → Integers.Ptrofs → Trace → Val → Prop where
  | vol (chunk m b ofs id ev v) :
      ge.block_is_volatile b = true →
      ge.find_symbol id = some b →
      EventValMatch ge ev (Chunk.typ chunk) v →
      VolatileLoad ge chunk m b ofs [Event.Event_vload chunk id ofs ev]
        (Val.loadResult chunk v)
  | nonvol (chunk m b ofs v) :
      ge.block_is_volatile b = false →
      Mem.load chunk m b (Integers.Ptrofs.unsigned ofs) = some v →
      VolatileLoad ge chunk m b ofs E0 v

/-- `Events.volatile_store` -/
inductive VolatileStore (ge : Senv) :
    Chunk → Mem → Block → Integers.Ptrofs → Val → Trace → Mem → Prop where
  | vol (chunk m b ofs id ev v) :
      ge.block_is_volatile b = true →
      ge.find_symbol id = some b →
      EventValMatch ge ev (Chunk.typ chunk) (Val.loadResult chunk v) →
      VolatileStore ge chunk m b ofs v [Event.Event_vstore chunk id ofs ev] m
  | nonvol (chunk m b ofs v m') :
      ge.block_is_volatile b = false →
      Mem.store chunk m b (Integers.Ptrofs.unsigned ofs) v = some m' →
      VolatileStore ge chunk m b ofs v E0 m'

/-! ## The type of an external-call semantics -/

/-- `Events.extcall_sem` -/
abbrev ExtcallSem := Senv → List Val → Mem → Trace → Val → Mem → Prop

/-! ## Builtins with real semantics -/

/-- `Events.volatile_load_sem` -/
inductive VolatileLoadSem (chunk : Chunk) : ExtcallSem where
  | intro (ge b ofs m t v) :
      VolatileLoad ge chunk m b ofs t v →
      VolatileLoadSem chunk ge [.Vptr b ofs] m t v m

/-- `Events.volatile_store_sem` -/
inductive VolatileStoreSem (chunk : Chunk) : ExtcallSem where
  | intro (ge b ofs m1 v t m2) :
      VolatileStore ge chunk m1 b ofs v t m2 →
      VolatileStoreSem chunk ge [.Vptr b ofs, v] m1 t .Vundef m2

/-- `Events.extcall_malloc_sem`.  The requested size is stashed just below the
    returned pointer so that `free` can recover it. -/
inductive ExtcallMallocSem : ExtcallSem where
  | intro (ge sz m m' b m'') :
      Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz) = (m', b) →
      Mem.store Mptr m' b (- sizeChunk Mptr) (Val.Vptrofs sz) = some m'' →
      ExtcallMallocSem ge [Val.Vptrofs sz] m E0 (.Vptr b Integers.Ptrofs.zero) m''

/-- `Events.extcall_free_sem` -/
inductive ExtcallFreeSem : ExtcallSem where
  | ptr (ge b lo sz m m') :
      Mem.load Mptr m b (Integers.Ptrofs.unsigned lo - sizeChunk Mptr)
        = some (Val.Vptrofs sz) →
      Mem.free m b (Integers.Ptrofs.unsigned lo - sizeChunk Mptr)
        (Integers.Ptrofs.unsigned lo + Integers.Ptrofs.unsigned sz) = some m' →
      ExtcallFreeSem ge [.Vptr b lo] m E0 .Vundef m'
  | null (ge m) : ExtcallFreeSem ge [Val.Vnullptr] m E0 .Vundef m

/-- `Events.extcall_memcpy_sem` — the source and destination must be aligned and
    either identical or non-overlapping. -/
inductive ExtcallMemcpySem (sz al : Z) : ExtcallSem where
  | intro (ge bdst odst bsrc osrc m bytes m') :
      (al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8) → sz ≥ 0 → sz % al = 0 →
      (sz > 0 → Integers.Ptrofs.unsigned osrc % al = 0) →
      (sz > 0 → Integers.Ptrofs.unsigned odst % al = 0) →
      (bsrc ≠ bdst
        ∨ Integers.Ptrofs.unsigned osrc = Integers.Ptrofs.unsigned odst
        ∨ Integers.Ptrofs.unsigned osrc + sz ≤ Integers.Ptrofs.unsigned odst
        ∨ Integers.Ptrofs.unsigned odst + sz ≤ Integers.Ptrofs.unsigned osrc) →
      Mem.loadbytes m bsrc (Integers.Ptrofs.unsigned osrc) sz = some bytes →
      Mem.storebytes m bdst (Integers.Ptrofs.unsigned odst) bytes = some m' →
      ExtcallMemcpySem sz al ge [.Vptr bdst odst, .Vptr bsrc osrc] m E0 .Vundef m'

/-- `Events.extcall_annot_sem` -/
inductive ExtcallAnnotSem (text : String) (targs : List ATyp) : ExtcallSem where
  | intro (ge vargs m args) :
      EventValListMatch ge args targs vargs →
      ExtcallAnnotSem text targs ge vargs m [Event.Event_annot text args] .Vundef m

/-- `Events.extcall_annot_val_sem` -/
inductive ExtcallAnnotValSem (text : String) (targ : ATyp) : ExtcallSem where
  | intro (ge varg m arg) :
      EventValMatch ge arg targ varg →
      ExtcallAnnotValSem text targ ge [varg] m
        [Event.Event_annot text [arg]] varg m

/-- `Events.extcall_debug_sem` — observationally a no-op. -/
inductive ExtcallDebugSem : ExtcallSem where
  | intro (ge vargs m) : ExtcallDebugSem ge vargs m E0 .Vundef m

/-! ## Uninterpreted externals

`Events.v` 1487-1497 declares these with `Parameter`/`Axiom` in Rocq; the same
choice here.  A program that calls an unknown external therefore has
unspecified — not stuck — behaviour, matching CompCert. -/

axiom externalFunctionsSem : String → Signature → ExtcallSem
axiom inlineAssemblySem : String → Signature → ExtcallSem

/-- `Events.known_builtin_sem`: a known built-in is a pure function of its
    arguments; it emits no event and leaves memory unchanged. -/
inductive KnownBuiltinSem (bf : Builtins.BuiltinFunction) : ExtcallSem where
  | intro (ge vargs vres m) :
      (Builtins.builtinFunctionSem bf).sem vargs = some vres →
      KnownBuiltinSem bf ge vargs m E0 vres m

/-- `Events.builtin_or_external_sem`: consult the table of known built-ins
    (`Builtins.lookup_builtin_function`, see `CCLib/common/Builtins.lean`) first;
    anything else is an unknown external. -/
def builtinOrExternalSem (name : String) (sg : Signature) : ExtcallSem :=
  match Builtins.lookupBuiltinFunction name sg with
  | some bf => KnownBuiltinSem bf
  | none => externalFunctionsSem name sg

/-- `Events.external_call` — the semantics of an external function. -/
def externalCall : ExtFun → ExtcallSem
  | .EF_external name sg => externalFunctionsSem name sg
  | .EF_builtin name sg => builtinOrExternalSem name sg
  | .EF_runtime name sg => builtinOrExternalSem name sg
  | .EF_vload chunk => VolatileLoadSem chunk
  | .EF_vstore chunk => VolatileStoreSem chunk
  | .EF_malloc => ExtcallMallocSem
  | .EF_free => ExtcallFreeSem
  | .EF_memcpy sz al => ExtcallMemcpySem sz al
  | .EF_annot _ txt targs => ExtcallAnnotSem txt targs
  | .EF_annot_val _ txt targ => ExtcallAnnotValSem txt targ
  | .EF_inline_asm txt sg _ => inlineAssemblySem txt sg
  | .EF_debug _ _ _ => ExtcallDebugSem

/-! ## Determinism support

Everything from here down is what CompCert's `Clight.semantics_determinate`
consumes and this port originally left out: the definitions the header's skip
list names (`eventval_valid`, `match_traces`, and `eventval_type`, which the
first two need), plus the `extcall_properties` fields determinacy rests on.  The
step relation itself is in `CCLib.common.Determinism`. -/

/-- `Events.eventval_type` -/
def eventvalType : EventVal → ATyp
  | .EVint _ => .Tint
  | .EVlong _ => .Tlong
  | .EVfloat _ => .Tfloat
  | .EVsingle _ => .Tsingle
  | .EVptr_global _ _ => Tptr

/-- `Events.eventval_valid` — an event value the outside world could have
    supplied: a pointer may only name a public symbol. -/
def EventValValid (ge : Senv) : EventVal → Prop
  | .EVint _ => True
  | .EVlong _ => True
  | .EVfloat _ => True
  | .EVsingle _ => True
  | .EVptr_global id _ => ge.public_symbol id = true

/-- `Events.match_traces` — the traces two steps from one state may produce.

    They must be equal *except* in the value a system call or a volatile load
    returns, which the outside world chooses and which is constrained only to be
    a valid event value of the right type.  This is why determinacy is stated
    about traces rather than as plain equality. -/
inductive MatchTraces (ge : Senv) : Trace → Trace → Prop where
  | nil : MatchTraces ge E0 E0
  | syscall (name args res1 res2) :
      EventValValid ge res1 → EventValValid ge res2 →
      eventvalType res1 = eventvalType res2 →
      MatchTraces ge [Event.Event_syscall name args res1]
        [Event.Event_syscall name args res2]
  | vload (chunk id ofs res1 res2) :
      EventValValid ge res1 → EventValValid ge res2 →
      eventvalType res1 = eventvalType res2 →
      MatchTraces ge [Event.Event_vload chunk id ofs res1]
        [Event.Event_vload chunk id ofs res2]
  | vstore (chunk id ofs arg) :
      MatchTraces ge [Event.Event_vstore chunk id ofs arg]
        [Event.Event_vstore chunk id ofs arg]
  | annot (text args) :
      MatchTraces ge [Event.Event_annot text args] [Event.Event_annot text args]

/-! ### The one `Senv` invariant this port does not carry

CompCert's `Senv.t` is proof-carrying and exposes `find_symbol_injective`;
`Globalenvs.lean`'s header explains why `Genv` here carries no `Prop` fields and
promises those facts "as lemmas about `globalenv p`".  `Genv.symbInjective_globalenv`
keeps that promise; the predicate below is how the fact travels to the places
that need it. -/

/-- `Senv.find_symbol_injective`. -/
def Senv.SymbolsInjective (ge : Senv) : Prop :=
  ∀ id1 id2 b, ge.find_symbol id1 = some b → ge.find_symbol id2 = some b → id1 = id2

theorem Genv.toSenv_symbolsInjective {F V : Type} {ge : Genv F V}
    (h : Genv.SymbInjective ge) : (Genv.toSenv ge).SymbolsInjective := h

/-- `Val.Vptrofs` is injective.  Stated here rather than in `CCLib.common.Values`
    because determinism of `EF_malloc`/`EF_free` is its only client — both
    recover a block size from a `Vptrofs` stored below the pointer.  Unlike
    CompCert's generic proof this one resolves `Archi.ptr64`, which is a target
    parameter and concrete. -/
theorem vptrofs_inj {a b : Integers.Ptrofs} (h : Val.Vptrofs a = Val.Vptrofs b) :
    a = b := by
  simp only [Val.Vptrofs, Archi.ptr64, if_true] at h
  injection h

theorem vptrofs_inj_iff {a b : Integers.Ptrofs} :
    Val.Vptrofs a = Val.Vptrofs b ↔ a = b :=
  ⟨vptrofs_inj, fun h => h ▸ rfl⟩

/-! ### Determinism of event-value matching -/

theorem eventValMatch_type {ge ev ty v} (h : EventValMatch ge ev ty v) :
    eventvalType ev = ty := by
  cases h <;> rfl

theorem eventValMatch_valid {ge ev ty v} (h : EventValMatch ge ev ty v) :
    EventValValid ge ev := by
  cases h <;> simp_all [EventValValid]

/-- `Events.eventval_match_determ_1` — one event value denotes one machine
    value. -/
theorem eventValMatch_determ_1 {ge ev ty v1 v2}
    (h1 : EventValMatch ge ev ty v1) (h2 : EventValMatch ge ev ty v2) : v1 = v2 := by
  cases h1 <;> cases h2 <;> simp_all

/-- `Events.eventval_match_determ_2` — one machine value is denoted by one event
    value.  This is the direction that needs symbol injectivity: two
    identifiers naming one block would give one pointer two event values. -/
theorem eventValMatch_determ_2 {ge ev1 ev2 ty v} (hinj : ge.SymbolsInjective)
    (h1 : EventValMatch ge ev1 ty v) (h2 : EventValMatch ge ev2 ty v) : ev1 = ev2 := by
  cases h1 with
  | ev_match_int _ => cases h2 <;> rfl
  | ev_match_long _ => cases h2 <;> rfl
  | ev_match_float _ => cases h2 <;> rfl
  | ev_match_single _ => cases h2 <;> rfl
  | ev_match_ptr id1 b1 _ _ hs1 =>
      cases h2 with
      | ev_match_ptr id2 _ _ _ hs2 => rw [hinj id1 id2 b1 hs1 hs2]

theorem eventValListMatch_determ_1 {ge evl tyl vl1}
    (h1 : EventValListMatch ge evl tyl vl1) :
    ∀ vl2, EventValListMatch ge evl tyl vl2 → vl1 = vl2 := by
  induction h1 with
  | evl_match_nil => intro _ h2; cases h2; rfl
  | evl_match_cons _ _ _ _ _ _ hm _ ih =>
      intro _ h2
      cases h2 with
      | evl_match_cons _ _ _ _ _ _ hm2 hl2 =>
          rw [eventValMatch_determ_1 hm hm2, ih _ hl2]

theorem eventValListMatch_determ_2 {ge evl1 tyl vl} (hinj : ge.SymbolsInjective)
    (h1 : EventValListMatch ge evl1 tyl vl) :
    ∀ evl2, EventValListMatch ge evl2 tyl vl → evl1 = evl2 := by
  induction h1 with
  | evl_match_nil => intro _ h2; cases h2; rfl
  | evl_match_cons _ _ _ _ _ _ hm _ ih =>
      intro _ h2
      cases h2 with
      | evl_match_cons _ _ _ _ _ _ hm2 hl2 =>
          rw [eventValMatch_determ_2 hinj hm hm2, ih _ hl2]

/-! ### Determinism of volatile accesses

The inversion lemmas below exist so the proofs never depend on how many binders
`cases` leaves for an indexed family — a fragile thing to hard-code.  Each is
`cases` plus `assumption`, since the premises all have distinct types. -/

theorem volatileLoad_inv {ge chunk m b ofs t v}
    (h : VolatileLoad ge chunk m b ofs t v) :
    (∃ id ev w, ge.block_is_volatile b = true ∧ ge.find_symbol id = some b
        ∧ EventValMatch ge ev (Chunk.typ chunk) w
        ∧ t = [Event.Event_vload chunk id ofs ev] ∧ v = Val.loadResult chunk w)
    ∨ (ge.block_is_volatile b = false ∧ t = E0
        ∧ Mem.load chunk m b (Integers.Ptrofs.unsigned ofs) = some v) := by
  cases h
  · exact Or.inl ⟨_, _, _, by assumption, by assumption, by assumption, rfl, rfl⟩
  · exact Or.inr ⟨by assumption, rfl, by assumption⟩

theorem volatileStore_inv {ge chunk m b ofs v t m'}
    (h : VolatileStore ge chunk m b ofs v t m') :
    (∃ id ev, ge.block_is_volatile b = true ∧ ge.find_symbol id = some b
        ∧ EventValMatch ge ev (Chunk.typ chunk) (Val.loadResult chunk v)
        ∧ t = [Event.Event_vstore chunk id ofs ev] ∧ m' = m)
    ∨ (ge.block_is_volatile b = false ∧ t = E0
        ∧ Mem.store chunk m b (Integers.Ptrofs.unsigned ofs) v = some m') := by
  cases h
  · exact Or.inl ⟨_, _, by assumption, by assumption, by assumption, rfl, rfl⟩
  · exact Or.inr ⟨by assumption, rfl, by assumption⟩

theorem volatileLoad_determ {ge chunk m b ofs t1 v1 t2 v2}
    (hinj : ge.SymbolsInjective)
    (h1 : VolatileLoad ge chunk m b ofs t1 v1)
    (h2 : VolatileLoad ge chunk m b ofs t2 v2) :
    MatchTraces ge t1 t2 ∧ (t1 = t2 → v1 = v2) := by
  cases volatileLoad_inv h1 with
  | inl p1 =>
      obtain ⟨id1, ev1, w1, hv1, hs1, hm1, ht1, hw1⟩ := p1
      cases volatileLoad_inv h2 with
      | inl p2 =>
          obtain ⟨id2, ev2, w2, _, hs2, hm2, ht2, hw2⟩ := p2
          subst ht1; subst ht2; subst hw1; subst hw2
          have hid : id1 = id2 := hinj _ _ _ hs1 hs2
          subst hid
          refine ⟨MatchTraces.vload _ _ _ _ _ (eventValMatch_valid hm1)
            (eventValMatch_valid hm2)
            (by rw [eventValMatch_type hm1, eventValMatch_type hm2]), ?_⟩
          intro ht
          simp only [List.cons.injEq, Event.Event_vload.injEq, and_true, true_and] at ht
          subst ht
          rw [eventValMatch_determ_1 hm1 hm2]
      | inr p2 =>
          obtain ⟨hv2, _, _⟩ := p2
          rw [hv1] at hv2; exact absurd hv2 (by simp)
  | inr p1 =>
      obtain ⟨hv1, ht1, hl1⟩ := p1
      cases volatileLoad_inv h2 with
      | inl p2 =>
          obtain ⟨_, _, _, hv2, _, _, _, _⟩ := p2
          rw [hv1] at hv2; exact absurd hv2 (by simp)
      | inr p2 =>
          obtain ⟨_, ht2, hl2⟩ := p2
          subst ht1; subst ht2
          rw [hl1] at hl2
          injection hl2 with hl2
          exact ⟨MatchTraces.nil, fun _ => hl2⟩

theorem volatileStore_determ {ge chunk m b ofs v t1 m1 t2 m2}
    (hinj : ge.SymbolsInjective)
    (h1 : VolatileStore ge chunk m b ofs v t1 m1)
    (h2 : VolatileStore ge chunk m b ofs v t2 m2) :
    MatchTraces ge t1 t2 ∧ (t1 = t2 → m1 = m2) := by
  cases volatileStore_inv h1 with
  | inl p1 =>
      obtain ⟨id1, ev1, hv1, hs1, hm1, ht1, hq1⟩ := p1
      cases volatileStore_inv h2 with
      | inl p2 =>
          obtain ⟨id2, ev2, _, hs2, hm2, ht2, hq2⟩ := p2
          subst ht1; subst ht2; subst hq1; subst hq2
          have hid : id1 = id2 := hinj _ _ _ hs1 hs2
          subst hid
          have hev : ev1 = ev2 := eventValMatch_determ_2 hinj hm1 hm2
          subst hev
          exact ⟨MatchTraces.vstore _ _ _ _, fun _ => rfl⟩
      | inr p2 =>
          obtain ⟨hv2, _, _⟩ := p2
          rw [hv1] at hv2; exact absurd hv2 (by simp)
  | inr p1 =>
      obtain ⟨hv1, ht1, hs1⟩ := p1
      cases volatileStore_inv h2 with
      | inl p2 =>
          obtain ⟨_, _, hv2, _, _, _, _⟩ := p2
          rw [hv1] at hv2; exact absurd hv2 (by simp)
      | inr p2 =>
          obtain ⟨_, ht2, hs2⟩ := p2
          subst ht1; subst ht2
          rw [hs1] at hs2
          injection hs2 with hs2
          exact ⟨MatchTraces.nil, fun _ => hs2⟩

/-! ### `extcall_properties`, the two fields determinacy needs

CompCert's `extcall_properties` record has ten fields; eight of them relate an
external call to memory extensions and injections and need exactly the
machinery this file's header records as skipped.  The two below — `ec_determ`
and `ec_trace_length` — are the ones `semantics_determinate` consumes, so they
are all that is axiomatized for the uninterpreted externals. -/

/-- `Events.extcall_properties`, restricted to `ec_determ` + `ec_trace_length`
    and to one symbol environment. -/
structure ExtcallDeterm (sem : ExtcallSem) (ge : Senv) : Prop where
  /-- `ec_determ` -/
  determ : ∀ vargs m t1 vres1 m1 t2 vres2 m2,
    sem ge vargs m t1 vres1 m1 → sem ge vargs m t2 vres2 m2 →
    MatchTraces ge t1 t2 ∧ (t1 = t2 → vres1 = vres2 ∧ m1 = m2)
  /-- `ec_trace_length` — one external call emits at most one event. -/
  traceLength : ∀ vargs m t vres m',
    sem ge vargs m t vres m' → t.length ≤ 1

/-- `Events.external_functions_properties`, narrowed as described above.  This
    and `inlineAssemblySemDeterm` are the only axioms the determinism
    development adds; `externalFunctionsSem` itself is already axiomatic (see
    the section above), and constraining an uninterpreted relation is exactly
    what CompCert does here. -/
axiom externalFunctionsSemDeterm (name : String) (sg : Signature) (ge : Senv) :
    ExtcallDeterm (externalFunctionsSem name sg) ge

/-- `Events.inline_assembly_properties`, narrowed the same way. -/
axiom inlineAssemblySemDeterm (name : String) (sg : Signature) (ge : Senv) :
    ExtcallDeterm (inlineAssemblySem name sg) ge

/-- The two axioms above are consistent: the always-false relation — which this
    file's header already names as an instantiation of `externalFunctionsSem`
    and `inlineAssemblySem` — satisfies both fields vacuously, so adding them
    cannot make the development inconsistent. -/
example (ge : Senv) : ExtcallDeterm (fun _ _ _ _ _ _ => False) ge :=
  ⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- `Events.known_builtin_ok`, restricted to determinacy. -/
theorem knownBuiltinSem_determ (bf : Builtins.BuiltinFunction) (ge : Senv) :
    ExtcallDeterm (KnownBuiltinSem bf) ge where
  determ := by
    intro vargs m t1 vres1 m1 t2 vres2 m2 h1 h2
    cases h1 with
    | intro _ _ _ _ e1 =>
      cases h2 with
      | intro _ _ _ _ e2 =>
        rw [e1] at e2
        cases e2
        exact ⟨MatchTraces.nil, fun _ => ⟨rfl, rfl⟩⟩
  traceLength := by
    intro vargs m t vres m' h
    cases h; decide

theorem builtinOrExternalSem_determ (name : String) (sg : Signature) (ge : Senv) :
    ExtcallDeterm (builtinOrExternalSem name sg) ge := by
  unfold builtinOrExternalSem
  split
  · exact knownBuiltinSem_determ _ ge
  · exact externalFunctionsSemDeterm name sg ge

/-! ### The eight interpreted builtins

Each is one or two constructors whose premises are all functions, so the whole
argument is: invert both derivations and let the equations collapse. -/

theorem volatileLoadSem_inv {chunk ge vargs m t v m'}
    (h : VolatileLoadSem chunk ge vargs m t v m') :
    ∃ b ofs, vargs = [Val.Vptr b ofs] ∧ m' = m ∧ VolatileLoad ge chunk m b ofs t v := by
  cases h; exact ⟨_, _, rfl, rfl, by assumption⟩

theorem volatileStoreSem_inv {chunk ge vargs m t v m'}
    (h : VolatileStoreSem chunk ge vargs m t v m') :
    ∃ b ofs w, vargs = [Val.Vptr b ofs, w] ∧ v = Val.Vundef
      ∧ VolatileStore ge chunk m b ofs w t m' := by
  cases h; exact ⟨_, _, _, rfl, rfl, by assumption⟩

theorem volatileLoadSem_determ (chunk : Chunk) {ge : Senv} (hinj : ge.SymbolsInjective) :
    ExtcallDeterm (VolatileLoadSem chunk) ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    obtain ⟨b, ofs, hva, hq1, hl1⟩ := volatileLoadSem_inv h1
    obtain ⟨b2, ofs2, hva2, hq2, hl2⟩ := volatileLoadSem_inv h2
    subst hva
    simp only [List.cons.injEq, Val.Vptr.injEq, and_true] at hva2
    obtain ⟨hb, ho⟩ := hva2
    subst hb; subst ho; subst hq1; subst hq2
    obtain ⟨hmt, hv⟩ := volatileLoad_determ hinj hl1 hl2
    exact ⟨hmt, fun ht => ⟨hv ht, rfl⟩⟩
  · intro _ _ _ _ _ h
    obtain ⟨_, _, _, _, hl⟩ := volatileLoadSem_inv h
    cases hl <;> simp [E0]

theorem volatileStoreSem_determ (chunk : Chunk) {ge : Senv} (hinj : ge.SymbolsInjective) :
    ExtcallDeterm (VolatileStoreSem chunk) ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    obtain ⟨b, ofs, w, hva, hr1, hs1⟩ := volatileStoreSem_inv h1
    obtain ⟨b2, ofs2, w2, hva2, hr2, hs2⟩ := volatileStoreSem_inv h2
    subst hva
    simp only [List.cons.injEq, Val.Vptr.injEq, and_true] at hva2
    obtain ⟨⟨hb, ho⟩, hw⟩ := hva2
    subst hb; subst ho; subst hw; subst hr1; subst hr2
    obtain ⟨hmt, hm⟩ := volatileStore_determ hinj hs1 hs2
    exact ⟨hmt, fun ht => ⟨rfl, hm ht⟩⟩
  · intro _ _ _ _ _ h
    obtain ⟨_, _, _, _, _, hs⟩ := volatileStoreSem_inv h
    cases hs <;> simp [E0]

/-- `ExtcallMallocSem` needs an explicit inversion lemma rather than a second
    `cases`: its argument list is `[Val.Vptrofs sz]`, and `Vptrofs` is a
    function, so dependent elimination cannot recover `sz` from it.  `vptrofs_inj`
    can. -/
theorem extcallMallocSem_inv {ge vargs m t v m'}
    (h : ExtcallMallocSem ge vargs m t v m') :
    ∃ sz m1 b, vargs = [Val.Vptrofs sz] ∧ t = E0
      ∧ v = Val.Vptr b Integers.Ptrofs.zero
      ∧ Mem.alloc m (- sizeChunk Mptr) (Integers.Ptrofs.unsigned sz) = (m1, b)
      ∧ Mem.store Mptr m1 b (- sizeChunk Mptr) (Val.Vptrofs sz) = some m' := by
  cases h; exact ⟨_, _, _, rfl, rfl, rfl, by assumption, by assumption⟩

theorem extcallMallocSem_determ {ge : Senv} : ExtcallDeterm ExtcallMallocSem ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    obtain ⟨sz1, _, _, hva1, ht1, hr1, ha1, hst1⟩ := extcallMallocSem_inv h1
    obtain ⟨sz2, _, _, hva2, ht2, hr2, ha2, hst2⟩ := extcallMallocSem_inv h2
    subst hva1
    simp only [List.cons.injEq, vptrofs_inj_iff, and_true] at hva2
    subst hva2
    subst ht1; subst ht2; subst hr1; subst hr2
    rw [ha1] at ha2
    simp only [Prod.mk.injEq] at ha2
    obtain ⟨he1, he2⟩ := ha2
    subst he1; subst he2
    rw [hst1] at hst2
    injection hst2 with hst2
    exact ⟨MatchTraces.nil, fun _ => ⟨rfl, hst2⟩⟩
  · intro _ _ _ _ _ h
    obtain ⟨_, _, _, _, ht, _, _, _⟩ := extcallMallocSem_inv h
    subst ht; simp [E0]

theorem extcallFreeSem_determ {ge : Senv} : ExtcallDeterm ExtcallFreeSem ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    cases h1 <;> cases h2 <;>
      exact ⟨MatchTraces.nil, fun _ => by simp_all [vptrofs_inj_iff]⟩
  · intro _ _ _ _ _ h
    cases h <;> simp [E0]

theorem extcallMemcpySem_determ (sz al : Z) {ge : Senv} :
    ExtcallDeterm (ExtcallMemcpySem sz al) ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    cases h1; cases h2
    exact ⟨MatchTraces.nil, fun _ => by simp_all⟩
  · intro _ _ _ _ _ h
    cases h; simp [E0]

theorem extcallAnnotSem_inv {text targs ge vargs m t v m'}
    (h : ExtcallAnnotSem text targs ge vargs m t v m') :
    ∃ args, EventValListMatch ge args targs vargs
      ∧ t = [Event.Event_annot text args] ∧ v = Val.Vundef ∧ m' = m := by
  cases h; exact ⟨_, by assumption, rfl, rfl, rfl⟩

theorem extcallAnnotValSem_inv {text targ ge vargs m t v m'}
    (h : ExtcallAnnotValSem text targ ge vargs m t v m') :
    ∃ arg w, EventValMatch ge arg targ w ∧ vargs = [w]
      ∧ t = [Event.Event_annot text [arg]] ∧ v = w ∧ m' = m := by
  cases h; exact ⟨_, _, by assumption, rfl, rfl, rfl, rfl⟩

theorem extcallAnnotSem_determ (text : String) (targs : List ATyp) {ge : Senv}
    (hinj : ge.SymbolsInjective) : ExtcallDeterm (ExtcallAnnotSem text targs) ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    obtain ⟨args1, hm1, ht1, hr1, hq1⟩ := extcallAnnotSem_inv h1
    obtain ⟨args2, hm2, ht2, hr2, hq2⟩ := extcallAnnotSem_inv h2
    have h := eventValListMatch_determ_2 hinj hm1 _ hm2
    subst h; subst ht1; subst ht2; subst hr1; subst hr2; subst hq1; subst hq2
    exact ⟨MatchTraces.annot _ _, fun _ => ⟨rfl, rfl⟩⟩
  · intro _ _ _ _ _ h
    obtain ⟨_, _, ht, _, _⟩ := extcallAnnotSem_inv h
    subst ht; simp

theorem extcallAnnotValSem_determ (text : String) (targ : ATyp) {ge : Senv}
    (hinj : ge.SymbolsInjective) : ExtcallDeterm (ExtcallAnnotValSem text targ) ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    obtain ⟨arg1, w1, hm1, hva1, ht1, hr1, hq1⟩ := extcallAnnotValSem_inv h1
    obtain ⟨arg2, w2, hm2, hva2, ht2, hr2, hq2⟩ := extcallAnnotValSem_inv h2
    subst hva1
    simp only [List.cons.injEq, and_true] at hva2
    subst hva2
    have h := eventValMatch_determ_2 hinj hm1 hm2
    subst h; subst ht1; subst ht2; subst hr1; subst hr2; subst hq1; subst hq2
    exact ⟨MatchTraces.annot _ _, fun _ => ⟨rfl, rfl⟩⟩
  · intro _ _ _ _ _ h
    obtain ⟨_, _, _, _, ht, _, _⟩ := extcallAnnotValSem_inv h
    subst ht; simp

theorem extcallDebugSem_determ {ge : Senv} : ExtcallDeterm ExtcallDebugSem ge := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h1 h2
    cases h1; cases h2
    exact ⟨MatchTraces.nil, fun _ => ⟨rfl, rfl⟩⟩
  · intro _ _ _ _ _ h
    cases h; simp [E0]

/-- `Events.external_call_determ` + `external_call_trace_length`: every external
    call is determinate up to `MatchTraces` and emits at most one event.  The
    injectivity hypothesis is discharged for real programs by
    `Genv.symbInjective_globalenv`. -/
theorem externalCall_determ (ef : ExtFun) {ge : Senv} (hinj : ge.SymbolsInjective) :
    ExtcallDeterm (externalCall ef) ge := by
  cases ef with
  | EF_external name sg => exact externalFunctionsSemDeterm name sg ge
  | EF_builtin name sg => exact builtinOrExternalSem_determ name sg ge
  | EF_runtime name sg => exact builtinOrExternalSem_determ name sg ge
  | EF_vload chunk => exact volatileLoadSem_determ chunk hinj
  | EF_vstore chunk => exact volatileStoreSem_determ chunk hinj
  | EF_malloc => exact extcallMallocSem_determ
  | EF_free => exact extcallFreeSem_determ
  | EF_memcpy sz al => exact extcallMemcpySem_determ sz al
  | EF_annot _ txt targs => exact extcallAnnotSem_determ txt targs hinj
  | EF_annot_val _ txt targ => exact extcallAnnotValSem_determ txt targ hinj
  | EF_inline_asm txt sg _ => exact inlineAssemblySemDeterm txt sg ge
  | EF_debug _ _ _ => exact extcallDebugSem_determ

end CC
