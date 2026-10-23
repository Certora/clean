/-
  [x86-64 instance of `CCLib/backend/StackingproofFrame.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness proof for the layout of activation records, part 1 — port of
  the beginning of `backend/Stackingproof.v`: basic properties of the
  translation, and the separation-logic assertions describing a Mach stack
  frame (`contains_locations`, `contains_callee_saves`, `frame_contents`)
  together with the lemmas to read and update the frame.

  Differences from Rocq: `Archi.abi` is an explicit argument `win64`; the
  frame-related definitions that Rocq declares inside `Section
  FRAME_PROPERTIES` (with `b := function_bounds f`, `fe := make_env b`) take
  `win64` and `f` as explicit arguments.
-/
import CCLib.x86.Stacking
import CCLib.common.GlobalenvsTransf

namespace CC
namespace X86

/- `Archi.win64` (a Rocq `Parameter`): whether the Windows x86-64 ABI is used. -/
variable (win64 : Bool)
namespace Stackingproof

open Linear Mach Conventions1 Conventions Stacklayout Stacking Bounds Separation
open Lineartyping

/-! ## Basic properties of the translation -/

/-- `Stackingproof.match_prog` -/
def MatchProg (win64 : Bool) (p : Linear.Program) (tp : Mach.Program) : Prop :=
  transfProgram win64 p = .OK tp

/-- `Stackingproof.typesize_typesize` -/
theorem typesize_typesize (ty : ATyp) : ty.size = 4 * typesize ty := by
  cases ty <;> rfl

/-- `Stackingproof.size_type_chunk` -/
theorem size_type_chunk (ty : ATyp) : sizeChunk (Chunk.ofTyp ty) = ty.size := by
  cases ty <;> rfl

/-- `Stackingproof.align_type_chunk`.  Rocq proves the equation
`align_chunk (chunk_of_type ty) = 4 * typealign ty`; the port's `alignChunk`
gives `Mfloat64`/`Many64` alignment 4 (Rocq's aarch64 value is 8), so only the
divisibility, which is all the proof needs, holds here. -/
theorem align_type_chunk (ty : ATyp) : alignChunk (Chunk.ofTyp ty) ∣ 4 * typealign ty := by
  cases ty <;> decide

theorem size_type_chunk_4 (ty : ATyp) : sizeChunk (Chunk.ofTyp ty) = 4 * typesize ty := by
  cases ty <;> rfl

/-- `Stackingproof.slot_outgoing_argument_valid` -/
theorem slot_outgoing_argument_valid (win64 : Bool) (f : Linear.Function) (ofs : Z) (ty : ATyp)
    (sg : Signature) (h : Loc.S .Outgoing ofs ty ∈ RPair.regsList (locArguments win64 sg)) :
    slotValid win64 f .Outgoing ofs ty = true := by
  have := locArguments_acceptable_2 win64 sg _ h
  simp only [LocArgumentAcceptable] at this
  simp only [slotValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨by zomega, Int.emod_eq_zero_of_dvd this.2⟩

/-- `Stackingproof.load_result_inject` -/
theorem load_result_inject {j : Val.Meminj} {ty : ATyp} {v v' : Val} (h : Val.Inject j v v')
    (ht : Val.HasType v ty) : Val.Inject j v (Val.loadResult (Chunk.ofTyp ty) v') := by
  cases h with
  | int i => cases ty <;> simp_all [Val.HasType, Val.hasType, Val.loadResult] <;> constructor
  | long i => cases ty <;> simp_all [Val.HasType, Val.hasType, Val.loadResult] <;> constructor
  | float x => cases ty <;> simp_all [Val.HasType, Val.hasType, Val.loadResult] <;> constructor
  | single x => cases ty <;> simp_all [Val.HasType, Val.hasType, Val.loadResult] <;> constructor
  | ptr delta hb ho =>
    cases ty <;> simp_all [Val.HasType, Val.hasType, Val.loadResult, Archi.ptr64] <;>
      exact .ptr delta hb rfl
  | undef v => exact .undef _

/-! ## Accessing the stack frame with `load_stack` / `store_stack` -/

theorem max_unsigned_eq : Integers.Ptrofs.max_unsigned = Integers.Ptrofs.modulus - 1 := rfl

/-- `load_stack` at a constant offset from the base of the frame. -/
theorem loadStack_eq (m : Mem) (sp : Block) (ty : ATyp) (x : Z) (h0 : 0 ≤ x)
    (h1 : x + sizeChunk (Chunk.ofTyp ty) ≤ Integers.Ptrofs.modulus) :
    loadStack m (.Vptr sp Integers.Ptrofs.zero) ty (Integers.Ptrofs.repr x) =
      Mem.load (Chunk.ofTyp ty) m sp x := by
  have hs : 0 < sizeChunk (Chunk.ofTyp ty) := by cases ty <;> decide
  have hu : Integers.Ptrofs.unsigned (Integers.Ptrofs.repr x) = x :=
    Integers.Ptrofs.unsigned_repr h0 (by rw [max_unsigned_eq]; zomega)
  simp only [loadStack, Val.offsetPtr, Integers.Ptrofs.add_zero_l, Mem.loadv, hu]
  rw [if_pos h1]

/-- `store_stack` at a constant offset from the base of the frame. -/
theorem storeStack_eq (m : Mem) (sp : Block) (ty : ATyp) (x : Z) (v : Val) (h0 : 0 ≤ x)
    (h1 : x + sizeChunk (Chunk.ofTyp ty) ≤ Integers.Ptrofs.modulus) :
    storeStack m (.Vptr sp Integers.Ptrofs.zero) ty (Integers.Ptrofs.repr x) v =
      Mem.store (Chunk.ofTyp ty) m sp x v := by
  have hs : 0 < sizeChunk (Chunk.ofTyp ty) := by cases ty <;> decide
  have hu : Integers.Ptrofs.unsigned (Integers.Ptrofs.repr x) = x :=
    Integers.Ptrofs.unsigned_repr h0 (by rw [max_unsigned_eq]; zomega)
  simp only [storeStack, Val.offsetPtr, Integers.Ptrofs.add_zero_l, Mem.storev, hu]
  rw [if_pos h1]

/-- `Stackingproof.contains_get_stack` -/
theorem contains_get_stack {spec : Val → Prop} {m : Mem} {ty : ATyp} {sp : Block} {ofs : Z}
    (h : m ⊨ contains (Chunk.ofTyp ty) sp ofs spec) :
    ∃ v, loadStack m (.Vptr sp Integers.Ptrofs.zero) ty (Integers.Ptrofs.repr ofs) = some v ∧
      spec v := by
  rw [loadStack_eq _ _ _ _ h.1 h.2.1]
  exact load_rule h

/-- `Stackingproof.hasvalue_get_stack` -/
theorem hasvalue_get_stack {ty : ATyp} {m : Mem} {sp : Block} {ofs : Z} {v : Val}
    (h : m ⊨ hasvalue (Chunk.ofTyp ty) sp ofs v) :
    loadStack m (.Vptr sp Integers.Ptrofs.zero) ty (Integers.Ptrofs.repr ofs) = some v := by
  obtain ⟨v', h1, h2⟩ := contains_get_stack h
  rw [h1, h2]

/-- `Stackingproof.contains_set_stack` -/
theorem contains_set_stack {spec : Val → Prop} (v : Val) {spec1 : Val → Prop} {m : Mem}
    {ty : ATyp} {sp : Block} {ofs : Z} {P : MAssert}
    (h : m ⊨ contains (Chunk.ofTyp ty) sp ofs spec1 ** P)
    (hs : spec (Val.loadResult (Chunk.ofTyp ty) v)) :
    ∃ m', storeStack m (.Vptr sp Integers.Ptrofs.zero) ty (Integers.Ptrofs.repr ofs) v = some m' ∧
      m' ⊨ contains (Chunk.ofTyp ty) sp ofs spec ** P := by
  rw [storeStack_eq _ _ _ _ _ h.1.1 h.1.2.1]
  exact store_rule h hs

/-! ## The `contains_locations` assertion -/

private theorem rangePerm_sub {m : Mem} {sp : Block} {lo hi lo' hi' : Z} {p : Permission}
    (h : Mem.rangePerm m sp lo hi .Cur .Freeable = true) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    Mem.rangePerm m sp lo' hi' .Cur p = true :=
  Mem.rangePerm_intro _ _ _ _ _ _ fun i a c =>
    Mem.perm_implies (Mem.rangePerm_perm _ _ _ _ _ _ h i (by zomega) (by zomega))
      (by cases p <;> decide)

/-- `Stackingproof.contains_locations` -/
def containsLocations (j : Val.Meminj) (sp : Block) (pos bound : Z) (sl : Slot)
    (ls : LTL.Locset) : MAssert where
  pred m := (8 : Z) ∣ pos ∧ 0 ≤ pos ∧ pos + 4 * bound ≤ Integers.Ptrofs.modulus ∧
    Mem.rangePerm m sp pos (pos + 4 * bound) .Cur .Freeable = true ∧
    ∀ ofs ty, 0 ≤ ofs → ofs + typesize ty ≤ bound → typealign ty ∣ ofs →
      ∃ v, Mem.load (Chunk.ofTyp ty) m sp (pos + 4 * ofs) = some v ∧
        Val.Inject j (ls (.S sl ofs ty)) v
  footprint b ofs := b = sp ∧ pos ≤ ofs ∧ ofs < pos + 4 * bound
  invar m m' h hu := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h1, h2, h3, hu.rangePerm (fun i a c => ⟨rfl, a, c⟩) h4, ?_⟩
    intro ofs ty a b c
    obtain ⟨v, hl, hv⟩ := h5 ofs ty a b c
    refine ⟨v, hu.load (fun i a' c' => ⟨rfl, ?_, ?_⟩) hl, hv⟩
    · zomega
    · have := size_type_chunk_4 ty; zomega
  valid m b ofs h hf := by
    obtain ⟨rfl, h1, h2⟩ := hf
    exact Mem.validBlock_of_perm (Mem.rangePerm_perm _ _ _ _ _ _ h.2.2.2.1 ofs h1 h2)

/-- `Stackingproof.valid_access_location` -/
theorem valid_access_location {m : Mem} {sp : Block} {pos bound ofs : Z} {ty : ATyp}
    (p : Permission) (h8 : (8 : Z) ∣ pos)
    (hr : Mem.rangePerm m sp pos (pos + 4 * bound) .Cur .Freeable = true)
    (h0 : 0 ≤ ofs) (hb : ofs + typesize ty ≤ bound) (ha : typealign ty ∣ ofs) :
    Mem.validAccess m (Chunk.ofTyp ty) sp (pos + 4 * ofs) p = true := by
  simp only [Mem.validAccess, Bool.and_eq_true, beq_iff_eq]
  refine ⟨rangePerm_sub hr (by zomega) (by have := size_type_chunk_4 ty; zomega), ?_⟩
  apply Int.emod_eq_zero_of_dvd
  have h48 : 4 * typealign ty ∣ 8 := by cases ty <;> decide
  exact Int.dvd_add (Int.dvd_trans (align_type_chunk ty) (Int.dvd_trans h48 h8))
    (Int.dvd_trans (align_type_chunk ty) (Int.mul_dvd_mul_left 4 ha))

/-- `Stackingproof.get_location` -/
theorem get_location {m : Mem} {j : Val.Meminj} {sp : Block} {pos bound : Z} {sl : Slot}
    {ls : LTL.Locset} {ofs : Z} {ty : ATyp} (h : m ⊨ containsLocations j sp pos bound sl ls)
    (h0 : 0 ≤ ofs) (hb : ofs + typesize ty ≤ bound) (ha : typealign ty ∣ ofs) :
    ∃ v, loadStack m (.Vptr sp Integers.Ptrofs.zero) ty (Integers.Ptrofs.repr (pos + 4 * ofs)) =
        some v ∧ Val.Inject j (ls (.S sl ofs ty)) v := by
  obtain ⟨_, E, F, _, H⟩ := h
  rw [loadStack_eq _ _ _ _ (by zomega) (by have := size_type_chunk_4 ty; zomega)]
  exact H ofs ty h0 hb ha

/-- `Stackingproof.set_location` -/
theorem set_location {m : Mem} {j : Val.Meminj} {sp : Block} {pos bound : Z} {sl : Slot}
    {ls : LTL.Locset} {P : MAssert} {ofs : Z} {ty : ATyp} {v v' : Val}
    (h : m ⊨ containsLocations j sp pos bound sl ls ** P)
    (h0 : 0 ≤ ofs) (hb : ofs + typesize ty ≤ bound) (ha : typealign ty ∣ ofs)
    (hv : Val.Inject j v v') :
    ∃ m', storeStack m (.Vptr sp Integers.Ptrofs.zero) ty
        (Integers.Ptrofs.repr (pos + 4 * ofs)) v' = some m' ∧
      m' ⊨ containsLocations j sp pos bound sl (Locmap.set (.S sl ofs ty) v ls) ** P := by
  obtain ⟨⟨D, E, F, G, H⟩, hP, C⟩ := h
  have hsz := size_type_chunk_4 ty
  obtain ⟨m', STORE⟩ := Mem.valid_access_store v'
    (valid_access_location (bound := bound) .Writable D G h0 hb ha)
  have PERM : Mem.rangePerm m' sp pos (pos + 4 * bound) .Cur .Freeable = true :=
    Mem.rangePerm_store STORE _ _ _ _ _ G
  refine ⟨m', ?_, ⟨D, E, F, PERM, ?_⟩, ?_, ?_⟩
  · rw [storeStack_eq _ _ _ _ _ (by zomega) (by zomega)]; exact STORE
  · intro ofs0 ty0 a0 b0 c0
    have hsz0 := size_type_chunk_4 ty0
    unfold Locmap.set
    by_cases e : Loc.S sl ofs ty = Loc.S sl ofs0 ty0
    · simp only [Loc.S.injEq, true_and] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [if_pos rfl]
      exact ⟨_, Mem.load_store_same STORE, Val.loadResult_inject _ hv⟩
    · rw [if_neg e]
      by_cases d : Loc.diff (Loc.S sl ofs ty) (Loc.S sl ofs0 ty0)
      · rw [if_pos d]
        obtain ⟨v0, X, Y⟩ := H ofs0 ty0 a0 b0 c0
        refine ⟨v0, ?_, Y⟩
        rw [Mem.load_store_other STORE]
        · exact X
        · simp only [Loc.diff] at d
          rcases d with d | d | d
          · exact absurd rfl d
          · right; right; zomega
          · right; left; zomega
      · rw [if_neg d]
        obtain ⟨v'', LOAD⟩ := Mem.valid_access_load (m := m') (chunk := Chunk.ofTyp ty0)
          (b := sp) (ofs := pos + 4 * ofs0) (by
            rw [Mem.validAccess_store_eq STORE]
            exact valid_access_location (bound := bound) .Readable D G a0 b0 c0)
        exact ⟨v'', LOAD, .undef _⟩
  · exact P.invar _ _ hP (Mem.store_unchangedOn STORE fun i a c hi =>
      C _ _ ⟨rfl, by zomega, by zomega⟩ hi)
  · exact C

/-- `Stackingproof.initial_locations` -/
theorem initial_locations (j : Val.Meminj) (sp : Block) (pos bound : Z) (P : MAssert)
    (sl : Slot) (ls : LTL.Locset) (m : Mem) (h : m ⊨ range sp pos (pos + 4 * bound) ** P)
    (h8 : (8 : Z) ∣ pos) (hu : ∀ ofs ty, ls (.S sl ofs ty) = .Vundef) :
    m ⊨ containsLocations j sp pos bound sl ls ** P := by
  obtain ⟨⟨D, E, F⟩, hP, C⟩ := h
  have G : Mem.rangePerm m sp pos (pos + 4 * bound) .Cur .Freeable = true :=
    Mem.rangePerm_intro _ _ _ _ _ _ fun i a c => F i .Cur .Freeable a c
  refine ⟨⟨h8, D, E, G, ?_⟩, hP, C⟩
  intro ofs ty a b c
  obtain ⟨v, LOAD⟩ := Mem.valid_access_load (valid_access_location (bound := bound)
    .Readable h8 G a b c)
  exact ⟨v, LOAD, by rw [hu]; exact .undef _⟩

/-- `Stackingproof.contains_locations_exten` -/
theorem contains_locations_exten (ls ls' : LTL.Locset) (j : Val.Meminj) (sp : Block)
    (pos bound : Z) (sl : Slot)
    (h : ∀ ofs ty, Val.Lessdef (ls' (.S sl ofs ty)) (ls (.S sl ofs ty))) :
    (containsLocations j sp pos bound sl ls).Imp (containsLocations j sp pos bound sl ls') := by
  refine ⟨fun m ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, fun ofs ty x y z => ?_⟩, fun _ _ h => h⟩
  obtain ⟨v, hl, hv⟩ := e ofs ty x y z
  refine ⟨v, hl, ?_⟩
  have hl' := h ofs ty
  generalize ls' (.S sl ofs ty) = a at hl' ⊢
  cases hl' with
  | refl => exact hv
  | undef => exact .undef _

/-- `Stackingproof.contains_locations_incr` -/
theorem contains_locations_incr {j j' : Val.Meminj} (sp : Block) (pos bound : Z) (sl : Slot)
    (ls : LTL.Locset) (hj : Val.inject_incr j j') :
    (containsLocations j sp pos bound sl ls).Imp (containsLocations j' sp pos bound sl ls) := by
  refine ⟨fun m ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, fun ofs ty x y z => ?_⟩, fun _ _ h => h⟩
  obtain ⟨v, hl, hv⟩ := e ofs ty x y z
  exact ⟨v, hl, Val.inject_incr_inject hj hv⟩

/-! ## The `contains_callee_saves` assertion -/

/-- `Stackingproof.contains_callee_saves` -/
def containsCalleeSaves (j : Val.Meminj) (sp : Block) : Z → List Mreg → LTL.Locset → MAssert
  | _, [], _ => pure True
  | pos, r :: rl, ls =>
      contains (Chunk.ofTyp (Mreg.type r)) sp (align pos (Mreg.type r).size)
        (fun v => Val.Inject j (ls (.R r)) v) **
      containsCalleeSaves j sp (align pos (Mreg.type r).size + (Mreg.type r).size) rl ls

/-- `Stackingproof.contains_callee_saves_incr` -/
theorem contains_callee_saves_incr {j j' : Val.Meminj} (sp : Block) (ls : LTL.Locset)
    (hj : Val.inject_incr j j') :
    ∀ (rl : List Mreg) (pos : Z),
      (containsCalleeSaves j sp pos rl ls).Imp (containsCalleeSaves j' sp pos rl ls)
  | [], _ => .refl _
  | _ :: rl, _ =>
    sepconj_imp (contains_imp _ _ _ fun _ h => Val.inject_incr_inject hj h)
      (contains_callee_saves_incr sp ls hj rl _)

/-- `Stackingproof.contains_callee_saves_exten` -/
theorem contains_callee_saves_exten (j : Val.Meminj) (sp : Block) (ls ls' : LTL.Locset) :
    ∀ (rl : List Mreg) (pos : Z), (∀ r, r ∈ rl → ls' (.R r) = ls (.R r)) →
      (containsCalleeSaves j sp pos rl ls).Eqv (containsCalleeSaves j sp pos rl ls')
  | [], _, _ => .refl _
  | r :: rl, pos, h => by
    have hr := h r List.mem_cons_self
    refine sepconj_eqv ⟨contains_imp _ _ _ fun _ hv => ?_, contains_imp _ _ _ fun _ hv => ?_⟩
      (contains_callee_saves_exten j sp ls ls' rl _ fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    · rw [hr]; exact hv
    · rw [← hr]; exact hv

/-! ## Assertions describing a stack frame -/

/-- `function_bounds f` (Rocq's `b` in `Section FRAME_PROPERTIES`) -/
abbrev bnds (win64 : Bool) (f : Linear.Function) : Bounds win64 := functionBounds win64 f

/-- `make_env (function_bounds f)` (Rocq's `fe` in `Section FRAME_PROPERTIES`) -/
abbrev fenv (win64 : Bool) (f : Linear.Function) : FrameEnv := makeEnv (bnds win64 f)

/-- `Stackingproof.frame_contents_1` -/
def frameContents1 (win64 : Bool) (f : Linear.Function) (j : Val.Meminj) (sp : Block)
    (ls ls0 : LTL.Locset) (parent retaddr : Val) : MAssert :=
  containsLocations j sp (fenv win64 f).fe_ofs_local (bnds win64 f).bound_local .Local ls **
  containsLocations j sp (feOfsArg win64) (bnds win64 f).bound_outgoing .Outgoing ls **
  hasvalue Mptr sp (fenv win64 f).fe_ofs_link parent **
  hasvalue Mptr sp (fenv win64 f).fe_ofs_retaddr retaddr **
  containsCalleeSaves j sp (fenv win64 f).fe_ofs_callee_save (bnds win64 f).used_callee_save ls0

/-- `Stackingproof.frame_contents` -/
def frameContents (win64 : Bool) (f : Linear.Function) (j : Val.Meminj) (sp : Block)
    (ls ls0 : LTL.Locset) (parent retaddr : Val) : MAssert :=
  mconj (frameContents1 win64 f j sp ls ls0 parent retaddr)
    (range sp 0 (fenv win64 f).fe_stack_data **
     range sp ((fenv win64 f).fe_stack_data + (bnds win64 f).bound_stack_data) (fenv win64 f).fe_size)

section FRAME_ACCESS
variable {win64 : Bool} {f : Linear.Function}

private theorem slotValid_local {ofs : Z} {ty : ATyp} (h : slotValid win64 f .Local ofs ty = true) :
    0 ≤ ofs ∧ typealign ty ∣ ofs := by
  simp only [slotValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1, Int.dvd_of_emod_eq_zero h.2⟩

private theorem slotValid_outgoing {ofs : Z} {ty : ATyp}
    (h : slotValid win64 f .Outgoing ofs ty = true) : 0 ≤ ofs ∧ typealign ty ∣ ofs := by
  simp only [slotValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1, Int.dvd_of_emod_eq_zero h.2⟩

/-- `Stackingproof.frame_get_local` -/
theorem frame_get_local {ofs : Z} {ty : ATyp} {j : Val.Meminj} {sp : Block}
    {ls ls0 : LTL.Locset} {parent retaddr : Val} {m : Mem} {P : MAssert}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P)
    (hb : SlotWithinBounds (bnds win64 f) .Local ofs ty) (hv : slotValid win64 f .Local ofs ty = true) :
    ∃ v, loadStack m (.Vptr sp Integers.Ptrofs.zero) ty
        (Integers.Ptrofs.repr (offsetLocal (fenv win64 f) ofs)) = some v ∧
      Val.Inject j (ls (.S .Local ofs ty)) v := by
  obtain ⟨h0, ha⟩ := slotValid_local hv
  exact get_location (sep_proj1 (sep_proj1 (mconj_proj1 h))) h0 hb ha

/-- `Stackingproof.frame_get_outgoing` -/
theorem frame_get_outgoing {ofs : Z} {ty : ATyp} {j : Val.Meminj} {sp : Block}
    {ls ls0 : LTL.Locset} {parent retaddr : Val} {m : Mem} {P : MAssert}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P)
    (hb : SlotWithinBounds (bnds win64 f) .Outgoing ofs ty)
    (hv : slotValid win64 f .Outgoing ofs ty = true) :
    ∃ v, loadStack m (.Vptr sp Integers.Ptrofs.zero) ty
        (Integers.Ptrofs.repr (offsetArg win64 ofs)) = some v ∧
      Val.Inject j (ls (.S .Outgoing ofs ty)) v := by
  obtain ⟨h0, ha⟩ := slotValid_outgoing hv
  exact get_location (sep_pick2 (sep_proj1 (mconj_proj1 h))) h0 hb ha

/-- `Stackingproof.frame_get_parent` -/
theorem frame_get_parent {j : Val.Meminj} {sp : Block} {ls ls0 : LTL.Locset}
    {parent retaddr : Val} {m : Mem} {P : MAssert}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P) :
    loadStack m (.Vptr sp Integers.Ptrofs.zero) Tptr
      (Integers.Ptrofs.repr (fenv win64 f).fe_ofs_link) = some parent := by
  have := sep_pick3 (sep_proj1 (mconj_proj1 h))
  rw [← Chunk.ofTyp_Tptr] at this
  exact hasvalue_get_stack this

/-- `Stackingproof.frame_get_retaddr` -/
theorem frame_get_retaddr {j : Val.Meminj} {sp : Block} {ls ls0 : LTL.Locset}
    {parent retaddr : Val} {m : Mem} {P : MAssert}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P) :
    loadStack m (.Vptr sp Integers.Ptrofs.zero) Tptr
      (Integers.Ptrofs.repr (fenv win64 f).fe_ofs_retaddr) = some retaddr := by
  have := sep_pick4 (sep_proj1 (mconj_proj1 h))
  rw [← Chunk.ofTyp_Tptr] at this
  exact hasvalue_get_stack this

private theorem rearr1 {A R P : MAssert} {m : Mem} : (m ⊨ (A ** R) ** P) ↔ (m ⊨ A ** R ** P) :=
  (sep_assoc A R P).pred

private theorem rearr2 {A B R P : MAssert} {m : Mem} :
    (m ⊨ (A ** B ** R) ** P) ↔ (m ⊨ B ** A ** R ** P) :=
  ((sep_assoc _ _ _).trans ((sepconj_eqv (.refl A) (sep_assoc B R P)).trans
    (sep_swap A B (R ** P)))).pred

private theorem stack_ranges_preserved {m m' : Mem} {sp : Block} {Q1 Q2 : Z × Z}
    (hp : ∀ i k p, Mem.perm m sp i k p = true → Mem.perm m' sp i k p = true)
    (h : m ⊨ range sp Q1.1 Q1.2 ** range sp Q2.1 Q2.2) :
    m' ⊨ range sp Q1.1 Q1.2 ** range sp Q2.1 Q2.2 :=
  sep_preserved h (fun h => range_preserved h fun i k p _ _ => hp i k p)
    (fun h => range_preserved h fun i k p _ _ => hp i k p)

/-- `Stackingproof.frame_set_local` -/
theorem frame_set_local {ofs : Z} {ty : ATyp} {v v' : Val} {j : Val.Meminj} {sp : Block}
    {ls ls0 : LTL.Locset} {parent retaddr : Val} {m : Mem} {P : MAssert}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P)
    (hb : SlotWithinBounds (bnds win64 f) .Local ofs ty) (hv : slotValid win64 f .Local ofs ty = true)
    (hi : Val.Inject j v v') :
    ∃ m', storeStack m (.Vptr sp Integers.Ptrofs.zero) ty
        (Integers.Ptrofs.repr (offsetLocal (fenv win64 f) ofs)) v' = some m' ∧
      m' ⊨ frameContents win64 f j sp (Locmap.set (.S .Local ofs ty) v ls) ls0 parent retaddr ** P := by
  obtain ⟨h0, ha⟩ := slotValid_local hv
  have SEP := rearr1.1 (mconj_proj1 h)
  obtain ⟨m', A, B⟩ := set_location SEP h0 hb ha hi
  refine ⟨m', A, frame_mconj h (rearr1.2 B) ?_⟩
  have hst := A
  unfold offsetLocal at hst
  rw [storeStack_eq _ _ _ _ _ (by
      have := (sep_proj1 SEP).2.1; zomega) (by
      have := (sep_proj1 SEP).2.2.1; have := size_type_chunk_4 ty
      have hb' : ofs + typesize ty ≤ (bnds win64 f).bound_local := hb; zomega)] at hst
  exact stack_ranges_preserved (Q1 := (_, _)) (Q2 := (_, _))
    (fun i k p hp => by rw [Mem.perm_store hst]; exact hp) (sep_proj1 (mconj_proj2 h))

/-- `Stackingproof.frame_set_outgoing` -/
theorem frame_set_outgoing {ofs : Z} {ty : ATyp} {v v' : Val} {j : Val.Meminj} {sp : Block}
    {ls ls0 : LTL.Locset} {parent retaddr : Val} {m : Mem} {P : MAssert}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P)
    (hb : SlotWithinBounds (bnds win64 f) .Outgoing ofs ty)
    (hv : slotValid win64 f .Outgoing ofs ty = true)
    (hi : Val.Inject j v v') :
    ∃ m', storeStack m (.Vptr sp Integers.Ptrofs.zero) ty
        (Integers.Ptrofs.repr (offsetArg win64 ofs)) v' = some m' ∧
      m' ⊨ frameContents win64 f j sp (Locmap.set (.S .Outgoing ofs ty) v ls) ls0 parent retaddr **
        P := by
  obtain ⟨h0, ha⟩ := slotValid_outgoing hv
  have SEP := rearr2.1 (mconj_proj1 h)
  obtain ⟨m', A, B⟩ := set_location SEP h0 hb ha hi
  refine ⟨m', A, frame_mconj h (rearr2.2 B) ?_⟩
  have hst := A
  unfold offsetArg at hst
  rw [storeStack_eq _ _ _ _ _ (by
      have := (sep_proj1 SEP).2.1; zomega) (by
      have := (sep_proj1 SEP).2.2.1; have := size_type_chunk_4 ty
      have hb' : ofs + typesize ty ≤ (bnds win64 f).bound_outgoing := hb; zomega)] at hst
  exact stack_ranges_preserved (Q1 := (_, _)) (Q2 := (_, _))
    (fun i k p hp => by rw [Mem.perm_store hst]; exact hp) (sep_proj1 (mconj_proj2 h))

/-- `Stackingproof.frame_contents_exten` -/
theorem frame_contents_exten {ls ls0 ls' ls0' : LTL.Locset} {j : Val.Meminj} {sp : Block}
    {parent retaddr : Val} {P : MAssert} {m : Mem}
    (h1 : ∀ ofs ty, Val.Lessdef (ls' (.S .Local ofs ty)) (ls (.S .Local ofs ty)))
    (h2 : ∀ ofs ty, Val.Lessdef (ls' (.S .Outgoing ofs ty)) (ls (.S .Outgoing ofs ty)))
    (h3 : ∀ r, r ∈ (bnds win64 f).used_callee_save → ls0' (.R r) = ls0 (.R r))
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P) :
    m ⊨ frameContents win64 f j sp ls' ls0' parent retaddr ** P := by
  refine sep_imp h (mconj_imp ?_ (.refl _)) (.refl _)
  exact sepconj_imp (contains_locations_exten _ _ _ _ _ _ _ h1)
    (sepconj_imp (contains_locations_exten _ _ _ _ _ _ _ h2)
      (sepconj_imp (.refl _) (sepconj_imp (.refl _)
        (contains_callee_saves_exten _ _ _ _ _ _ h3).1)))

/-- `Stackingproof.frame_set_reg` -/
theorem frame_set_reg (r : Mreg) (v : Val) {j : Val.Meminj} {sp : Block}
    {ls ls0 : LTL.Locset} {parent retaddr : Val} {m : Mem} {P : MAssert}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P) :
    m ⊨ frameContents win64 f j sp (Locmap.set (.R r) v ls) ls0 parent retaddr ** P :=
  frame_contents_exten (fun _ _ => by rw [Locmap.gso (by simp [Loc.diff])]; exact .refl _)
    (fun _ _ => by rw [Locmap.gso (by simp [Loc.diff])]; exact .refl _) (fun _ _ => rfl) h

/-- `Stackingproof.frame_undef_regs` -/
theorem frame_undef_regs {j : Val.Meminj} {sp : Block} {ls ls0 : LTL.Locset}
    {parent retaddr : Val} {m : Mem} {P : MAssert} (rl : List Mreg)
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P) :
    m ⊨ frameContents win64 f j sp (LTL.undefRegs rl ls) ls0 parent retaddr ** P := by
  induction rl with
  | nil => exact h
  | cons r rl ih => exact frame_set_reg _ _ ih

/-- `Stackingproof.frame_set_regpair` -/
theorem frame_set_regpair {j : Val.Meminj} {sp : Block} {ls0 : LTL.Locset}
    {parent retaddr : Val} {m : Mem} {P : MAssert} (p : RPair Mreg) (v : Val) {ls : LTL.Locset}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P) :
    m ⊨ frameContents win64 f j sp (Locmap.setpair p v ls) ls0 parent retaddr ** P := by
  cases p with
  | One r => exact frame_set_reg _ _ h
  | Twolong r1 r2 => exact frame_set_reg _ _ (frame_set_reg _ _ h)

/-- `Stackingproof.frame_set_res` -/
theorem frame_set_res {j : Val.Meminj} {sp : Block} {ls0 : LTL.Locset}
    {parent retaddr : Val} {m : Mem} {P : MAssert} (res : BuiltinRes Mreg) :
    ∀ (v : Val) {ls : LTL.Locset}, m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P →
      m ⊨ frameContents win64 f j sp (Locmap.setres res v ls) ls0 parent retaddr ** P := by
  induction res with
  | BR r => intro v ls h; exact frame_set_reg _ _ h
  | BR_none => intro v ls h; exact h
  | BR_splitlong hi lo ihhi ihlo => intro v ls h; exact ihlo _ (ihhi _ h)

/-- `Stackingproof.frame_contents_incr` -/
theorem frame_contents_incr {j : Val.Meminj} {sp : Block} {ls ls0 : LTL.Locset}
    {parent retaddr : Val} {m : Mem} {P : MAssert} {j' : Val.Meminj}
    (h : m ⊨ frameContents win64 f j sp ls ls0 parent retaddr ** P) (hj : Val.inject_incr j j') :
    m ⊨ frameContents win64 f j' sp ls ls0 parent retaddr ** P := by
  refine sep_imp h (mconj_imp ?_ (.refl _)) (.refl _)
  exact sepconj_imp (contains_locations_incr _ _ _ _ _ hj)
    (sepconj_imp (contains_locations_incr _ _ _ _ _ hj)
      (sepconj_imp (.refl _) (sepconj_imp (.refl _) (contains_callee_saves_incr _ _ hj _ _))))

end FRAME_ACCESS

end Stackingproof
end X86
end CC
