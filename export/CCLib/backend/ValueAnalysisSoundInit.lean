/-
  Soundness of the value analysis, part 7 — the end of `backend/ValueAnalysis.v`:
  section `LINKING` (`sound_state`, `sound_step`), section `INITIAL`
  (`initial_block_classification`, the `store_init_data*` lemmas,
  `initial_mem_matches`), `sound_initial`, and the interface lemmas used by
  the optimizations (`avalue_sound`, `aaddr_sound`, `aaddressing_sound`,
  `aaddr_arg_sound`).

  Difference from Rocq: the port has no separate compilation, so
  `sound_state` is stated for the whole program — the only compilation unit
  is the program itself, i.e. Rocq's `forall cunit, linkorder cunit prog -> …`
  is instantiated at `cunit = prog`.  Consequently `romem_consistent` is only
  needed for `romem_for prog` against `prog_defmap prog`
  (`romem_for_consistent`), and `romem_for_consistent_2` is not needed.
-/
import CCLib.backend.ValueAnalysisSoundBuiltin
import CCLib.common.GlobalenvsInitChar
import CCLib.common.LinkingFundef

namespace CC
namespace ValueAnalysis

open ValueDomain RTL
open Integers (Ptrofs)

/-! ## Soundness of the initial memory abstraction (section `INITIAL`) -/

section INITIAL
variable {F V : Type}

/-- `ValueAnalysis.initial_block_classification` -/
theorem initial_block_classification {pub : List Ident} {gl : List (Ident × GlobDef F V)}
    {m : Mem} (hm : Genv.initMem pub gl = some m) :
    ∃ bc : BlockClassification,
      GenvMatch bc (Genv.globalenv pub gl) ∧ bcBelow bc m.nextblock ∧ BcNostack bc ∧
      (∀ b id, bc b = .BCglob id → Genv.findSymbol (Genv.globalenv pub gl) id = some b) ∧
      (∀ b, Mem.validBlock m b = true → bc b ≠ .BCinvalid) := by
  let ge := Genv.globalenv pub gl
  have hinj : Genv.SymbInjective ge := Genv.symbInjective_globalenv pub gl
  let f : Block → BlockClass := fun b =>
    if b < ge.genv_next then
      match Genv.invertSymbol ge b with
      | none => .BCother
      | some id => .BCglob id
    else .BCinvalid
  have F_glob_inv : ∀ b id, f b = .BCglob id → Genv.findSymbol ge id = some b := by
    intro b id h
    simp only [f] at h
    by_cases hlt : b < ge.genv_next
    · rw [if_pos hlt] at h
      cases I : Genv.invertSymbol ge b with
      | none => rw [I] at h; cases h
      | some id' => rw [I] at h; cases h; exact Genv.invert_findSymbol I
    · rw [if_neg hlt] at h; cases h
  have F_glob : ∀ b1 b2 id, f b1 = .BCglob id → f b2 = .BCglob id → b1 = b2 := by
    intro b1 b2 id h1 h2
    have e1 := F_glob_inv _ _ h1
    have e2 := F_glob_inv _ _ h2
    rw [e1] at e2; cases e2; rfl
  have F_nostack : ∀ b, f b ≠ .BCstack := by
    intro b h
    simp only [f] at h
    by_cases hlt : b < ge.genv_next
    · rw [if_pos hlt] at h
      cases I : Genv.invertSymbol ge b with
      | none => rw [I] at h; cases h
      | some id' => rw [I] at h; cases h
    · rw [if_neg hlt] at h; cases h
  have F_stack : ∀ b1 b2, f b1 = .BCstack → f b2 = .BCstack → b1 = b2 :=
    fun b1 _ h1 _ => absurd h1 (F_nostack b1)
  have F_valid : ∀ b, b < ge.genv_next → f b ≠ .BCinvalid ∧ f b ≠ .BCstack := by
    intro b hlt
    simp only [f, if_pos hlt]
    cases Genv.invertSymbol ge b <;> simp
  let bc : BlockClassification := ⟨f, F_stack, F_glob⟩
  have NG : ge.genv_next = m.nextblock := Genv.initMem_genv_next hm
  refine ⟨bc, ⟨fun id b => ?_, fun b hb => F_valid b hb⟩, fun b hb => ?_, fun b => F_nostack b,
    fun b id hb => F_glob_inv b id hb, fun b hv => ?_⟩
  · constructor
    · intro hs
      show f b = _
      simp only [f]
      rw [if_pos (Genv.symbBelow_globalenv pub gl id b hs), Genv.find_invertSymbol hinj hs]
    · exact F_glob_inv b id
  · change f b ≠ _ at hb
    simp only [f] at hb
    by_cases hlt : b < ge.genv_next
    · rw [← NG]; exact hlt
    · rw [if_neg hlt] at hb; exact absurd rfl hb
  · exact (F_valid b (by rw [NG]; exact (Mem.validBlock_iff m b).1 hv)).1

end INITIAL

/-- Reading back through `unchanged_on`: bytes loaded after the change from a
    block valid before it and unchanged everywhere were already there. -/
theorem unchangedOn_loadbytes_back {P : Block → Z → Prop} {m m' : Mem}
    (h : Mem.UnchangedOn P m m') {b : Block} (hv : Mem.validBlock m b = true)
    (hP : ∀ i, P b i) {ofs n : Z} {bytes : List MemVal}
    (hl : Mem.loadbytes m' b ofs n = some bytes) : Mem.loadbytes m b ofs n = some bytes := by
  have hr : Mem.rangePerm m' b ofs (ofs + n) .Cur .Readable = true := by
    unfold Mem.loadbytes at hl
    split at hl
    · assumption
    · cases hl
  obtain ⟨bytes0, h0⟩ : ∃ bytes0, Mem.loadbytes m b ofs n = some bytes0 := by
    unfold Mem.loadbytes
    rw [if_pos (h.rangePerm_2 hv (fun i _ _ => hP i) hr)]
    exact ⟨_, rfl⟩
  have := h.loadbytes (fun i _ _ => hP i) h0
  rw [hl] at this; cases this; exact h0

/-- A freshly allocated block contains only `Vundef`. -/
theorem smatch_alloc_same {bc : BlockClassification} {m : Mem} {lo hi : Z} {m' : Mem} {b : Block}
    (ALLOC : Mem.alloc m lo hi = (m', b)) (p : Aptr) : Smatch bc m' b p := by
  refine ⟨fun chunk ofs v hl => ?_, fun ofs b' ofs' q i hl => ?_⟩
  · obtain ⟨bytes, hb, rfl⟩ := Mem.load_loadbytes hl
    rw [loadbytes_alloc_same ALLOC hb]
    have hpos := sizeChunk_pos chunk
    obtain ⟨k, hk⟩ : ∃ k, (sizeChunk chunk).toNat = k + 1 := ⟨(sizeChunk chunk).toNat - 1, by omega⟩
    rw [hk, List.replicate_succ, decodeVal_undef_cons]
    exact .ifptr_undef _
  · have := loadbytes_alloc_same ALLOC hl
    simp at this

section INIT
variable {F V : Type} (o : ValueAOp.Options) {bc : BlockClassification} {ge : Genv F V}

/-- `ValueAnalysis.store_init_data_summary` -/
theorem store_init_data_summary (ab : Ablock) (p : Z) (id : InitData)
    (h : Pge .Glob ab.ab_summary) : Pge .Glob (storeInitData o ab p id).ab_summary := by
  cases id <;> simp only [storeInitData, ablockStore, vplub] <;> try exact h
  · cases o.propagateFloatConstants <;> exact h
  · cases o.propagateFloatConstants <;> exact h
  · exact plub_least (.glob_gl _ _) h

/-- `ValueAnalysis.store_init_data_list_summary` -/
theorem store_init_data_list_summary : ∀ (idl : List InitData) (ab : Ablock) (p : Z),
    Pge .Glob ab.ab_summary → Pge .Glob (storeInitDataList o ab p idl).ab_summary
  | [], _, _, h => h
  | id :: idl, ab, p, h =>
    store_init_data_list_summary idl _ _ (store_init_data_summary o ab p id h)

variable (GMATCH : GenvMatch bc ge)
include GMATCH

/-- `ValueAnalysis.store_init_data_sound` -/
theorem store_init_data_sound {m : Mem} {b : Block} {p : Z} {id : InitData} {m' : Mem}
    {ab : Ablock} (hs : Genv.storeInitData ge m b p id = some m') (hb : Bmatch bc m b ab) :
    Bmatch bc m' b (storeInitData o ab p id) := by
  cases id with
  | Init_int8 n => exact ablock_store_sound hs hb (.i _)
  | Init_int16 n => exact ablock_store_sound hs hb (.i _)
  | Init_int32 n => exact ablock_store_sound hs hb (.i _)
  | Init_int64 n => exact ablock_store_sound hs hb (.l _)
  | Init_float32 n =>
    simp only [storeInitData]
    split
    · exact ablock_store_sound hs hb (.s _)
    · exact ablock_store_sound hs hb (.num_s _ _)
  | Init_float64 n =>
    simp only [storeInitData]
    split
    · exact ablock_store_sound hs hb (.f _)
    · exact ablock_store_sound hs hb (.num_f _ _)
  | Init_space n =>
    simp only [Genv.storeInitData, Option.some.injEq] at hs; subst hs; exact hb
  | Init_addrof symb ofs =>
    simp only [Genv.storeInitData] at hs
    split at hs
    · cases hs
    · rename_i b' FS
      exact ablock_store_sound hs hb (.ptr _ _ _ (.gl _ ((GMATCH.1 symb b').1 FS)))

/-- `ValueAnalysis.store_init_data_list_sound` -/
theorem store_init_data_list_sound : ∀ {idl : List InitData} {m : Mem} {b : Block} {p : Z}
    {m' : Mem} {ab : Ablock}, Genv.storeInitDataList ge m b p idl = some m' →
    Bmatch bc m b ab → Bmatch bc m' b (storeInitDataList o ab p idl)
  | [], _, _, _, _, _, hs, hb => by
    simp only [Genv.storeInitDataList, Option.some.injEq] at hs; subst hs; exact hb
  | id :: idl, m, b, p, m', ab, hs, hb => by
    simp only [Genv.storeInitDataList] at hs
    split at hs
    · cases hs
    · rename_i m1 SI
      exact store_init_data_list_sound (ab := storeInitData o ab p id) hs
        (store_init_data_sound o GMATCH SI hb)

omit GMATCH

/-- `ValueAnalysis.store_init_data_other` -/
theorem store_init_data_other {m : Mem} {b : Block} {p : Z} {id : InitData} {m' : Mem}
    {ab : Ablock} {b' : Block} (hs : Genv.storeInitData ge m b p id = some m') (hne : b' ≠ b)
    (hb : Bmatch bc m b' ab) : Bmatch bc m' b' ab := by
  refine bmatch_inv hb fun ofs n _ => ?_
  cases id <;> simp only [Genv.storeInitData] at hs <;>
    first
    | exact Mem.loadbytes_store_other hs _ _ _ (.inl hne)
    | skip
  · simp only [Option.some.injEq] at hs; subst hs; rfl
  · split at hs
    · cases hs
    · exact Mem.loadbytes_store_other hs _ _ _ (.inl hne)

/-- `ValueAnalysis.store_init_data_list_other` -/
theorem store_init_data_list_other {b b' : Block} {ab : Ablock} (hne : b' ≠ b) :
    ∀ {idl : List InitData} {m : Mem} {p : Z} {m' : Mem},
    Genv.storeInitDataList ge m b p idl = some m' → Bmatch bc m b' ab → Bmatch bc m' b' ab
  | [], _, _, _, hs, hb => by
    simp only [Genv.storeInitDataList, Option.some.injEq] at hs; subst hs; exact hb
  | id :: idl, m, p, m', hs, hb => by
    simp only [Genv.storeInitDataList] at hs
    split at hs
    · cases hs
    · rename_i m1 SI
      exact store_init_data_list_other hne hs (store_init_data_other SI hne hb)

/-- `ValueAnalysis.store_zeros_same` -/
theorem store_zeros_same (p : Aptr) : ∀ (n : Nat) {m : Mem} {b : Block} {pos : Z} {m' : Mem},
    Genv.storeZerosAux m b pos n = some m' → Smatch bc m b p → Smatch bc m' b p
  | 0, _, _, _, _, hs, h => by
    simp only [Genv.storeZerosAux, Option.some.injEq] at hs; subst hs; exact h
  | n + 1, m, b, pos, m', hs, h => by
    simp only [Genv.storeZerosAux] at hs
    split at hs
    · cases hs
    · rename_i m1 ST
      exact store_zeros_same p n hs (smatch_store (av := .I Integers.Int.zero) ST h (.i _))

/-- `ValueAnalysis.store_zeros_other` -/
theorem store_zeros_other {b b' : Block} {ab : Ablock} (hne : b' ≠ b) :
    ∀ (n : Nat) {m : Mem} {pos : Z} {m' : Mem},
    Genv.storeZerosAux m b pos n = some m' → Bmatch bc m b' ab → Bmatch bc m' b' ab
  | 0, _, _, _, hs, h => by
    simp only [Genv.storeZerosAux, Option.some.injEq] at hs; subst hs; exact h
  | n + 1, m, pos, m', hs, h => by
    simp only [Genv.storeZerosAux] at hs
    split at hs
    · cases hs
    · rename_i m1 ST
      exact store_zeros_other hne n hs
        (bmatch_inv h fun ofs n _ => Mem.loadbytes_store_other ST _ _ _ (.inl hne))

end INIT

section INITMEM
variable {F V : Type} (o : ValueAOp.Options)

/-- `ValueAnalysis.initial_mem_match` -/
def InitialMemMatch (bc : BlockClassification) (m : Mem) (g : Genv F V) : Prop :=
  ∀ id b v, Genv.findSymbol g id = some b → Genv.findVarInfo g b = some v →
    v.gvar_volatile = false → v.gvar_readonly = true →
    Bmatch bc m b (storeInitDataList o (ablockInit .Pbot) 0 v.gvar_init)

variable {bc : BlockClassification} {ge : Genv F V} (GMATCH : GenvMatch bc ge)
include GMATCH

/-- `ValueAnalysis.alloc_global_match`.  Rocq's `Genv.t` carries
    `genv_symb_range`; here it is the hypothesis `hbelow`. -/
theorem alloc_global_match {m : Mem} {g : Genv F V} {idg : Ident × GlobDef F V} {m' : Mem}
    (hnext : g.genv_next = m.nextblock) (hbelow : Genv.SymbBelow g)
    (hm : InitialMemMatch o bc m g) (ha : Genv.allocGlobal ge m idg = some m') :
    InitialMemMatch o bc m' (Genv.addGlobal g idg) := by
  intro id b v hs hv hvol hro
  rw [Genv.findSymbol_addGlobal] at hs
  by_cases hid : id = idg.1
  · rw [if_pos hid] at hs
    cases hs
    simp only [Genv.findVarInfo, Genv.findDef_addGlobal, if_true] at hv
    obtain ⟨id1, gd⟩ := idg
    cases gd with
    | Gfun f => simp at hv
    | Gvar v' =>
      simp only [Option.some.injEq] at hv
      subst hv
      obtain ⟨m2, m3, h2, h3, h4⟩ := Genv.allocGlobal_gvar_eq ge ha
      rw [hnext]
      have S1 : Smatch bc (Mem.alloc m 0 (InitData.listSize v'.gvar_init)).1 m.nextblock .Pbot :=
        smatch_alloc_same (b := m.nextblock) rfl _
      have S2 := store_zeros_same (bc := bc) .Pbot _ h2 S1
      have B3 := store_init_data_list_sound o GMATCH h3 (ablock_init_sound S2)
      refine bmatch_inv B3 fun ofs n _ => Mem.loadbytes_drop h4 (.inr (.inr (.inr ?_)))
      simp [Genv.permGlobvar, hvol, hro, permOrder]
  · rw [if_neg hid] at hs
    have hlt := hbelow id b hs
    have hne : b ≠ g.genv_next := fun e => by subst e; exact Nat.lt_irrefl _ hlt
    simp only [Genv.findVarInfo, Genv.findDef_addGlobal, if_neg hne] at hv
    have B := hm id b v hs hv hvol hro
    have hvalid : Mem.validBlock m b = true := (Mem.validBlock_iff m b).2 (hnext ▸ hlt)
    rw [hnext] at hne
    exact bmatch_ext B fun ofs n bytes hl _ =>
      unchangedOn_loadbytes_back (Genv.allocGlobal_unchanged ge ha) hvalid (fun _ => hne) hl

/-- `ValueAnalysis.alloc_globals_match` -/
theorem alloc_globals_match : ∀ (gl : List (Ident × GlobDef F V)) {m : Mem} {g : Genv F V}
    {m' : Mem}, g.genv_next = m.nextblock → Genv.SymbBelow g → InitialMemMatch o bc m g →
    Genv.allocGlobals ge m gl = some m' → InitialMemMatch o bc m' (Genv.addGlobals g gl)
  | [], _, _, _, _, _, hm, ha => by
    simp only [Genv.allocGlobals, Option.some.injEq] at ha; subst ha; exact hm
  | idg :: gl, m, g, m', hnext, hbelow, hm, ha => by
    simp only [Genv.allocGlobals] at ha
    split at ha
    · cases ha
    · rename_i m1 AG
      exact alloc_globals_match gl
        (by rw [Genv.allocGlobal_nextblock ge AG, ← hnext]; rfl)
        (Genv.symbBelow_addGlobal idg hbelow)
        (alloc_global_match o GMATCH hnext hbelow hm AG) ha

end INITMEM

/-! ## `romem_for` is consistent with the program's definitions -/

section ROMEM
variable (o : ValueAOp.Options)

/-- `ValueAnalysis.romem_consistent` -/
def RomemConsistent (dm : PTree (GlobDef RTL.Fundef Unit)) (rm : Romem) : Prop :=
  ∀ id ab, rm.get id = some ab →
    ∃ v, dm.get id = some (.Gvar v) ∧ v.gvar_readonly = true ∧ v.gvar_volatile = false ∧
      definitiveInitializer v.gvar_init = true ∧
      ab = storeInitDataList o (ablockInit .Pbot) 0 v.gvar_init

/-- `ValueAnalysis.alloc_global_consistent` -/
theorem alloc_global_consistent {dm : PTree (GlobDef RTL.Fundef Unit)} {rm : Romem}
    (idg : Ident × GlobDef RTL.Fundef Unit) (h : RomemConsistent o dm rm) :
    RomemConsistent o (dm.set idg.1 idg.2) (allocGlobal o rm idg) := by
  intro id ab hab
  obtain ⟨id1, f1 | v1⟩ := idg
  · simp only [allocGlobal] at hab
    rw [PTree.grspec] at hab
    by_cases e : id = id1
    · rw [if_pos e] at hab; cases hab
    · rw [if_neg e] at hab
      simp only
      rw [PTree.gso _ _ _ _ (Ne.symm e)]
      exact h id ab hab
  · simp only [allocGlobal] at hab
    split at hab
    · rename_i RO
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at RO
      obtain ⟨⟨RO1, RO2⟩, RO3⟩ := RO
      rw [PTree.gsspec] at hab
      by_cases e : id = id1
      · rw [if_pos e] at hab
        cases hab
        subst e
        exact ⟨v1, by simp, RO1, RO2, RO3, rfl⟩
      · rw [if_neg e] at hab
        simp only
        rw [PTree.gso _ _ _ _ (Ne.symm e)]
        exact h id ab hab
    · rw [PTree.grspec] at hab
      by_cases e : id = id1
      · rw [if_pos e] at hab; cases hab
      · rw [if_neg e] at hab
        simp only
        rw [PTree.gso _ _ _ _ (Ne.symm e)]
        exact h id ab hab

/-- `ValueAnalysis.romem_for_consistent` -/
theorem romem_for_consistent (p : RTL.Program) :
    RomemConsistent o (Genv.defmap p.prog_defs) (romemFor o p) := by
  have REC : ∀ (l : List (Ident × GlobDef RTL.Fundef Unit)) dm rm, RomemConsistent o dm rm →
      RomemConsistent o (l.foldl (fun m idg => m.set idg.1 idg.2) dm) (l.foldl (allocGlobal o) rm) := by
    intro l
    induction l with
    | nil => intro dm rm h; exact h
    | cons a l ih => intro dm rm h; exact ih _ _ (alloc_global_consistent o a h)
  exact REC _ _ _ fun id ab h => by simp at h

end ROMEM

/-! ## The initial state is sound -/

section SOUNDINIT
variable (o : ValueAOp.Options) (abi : Conventions1.AbiKind)

/-- `ValueAnalysis.initial_mem_matches` (whole program: the only compilation
    unit is the program itself). -/
theorem initial_mem_matches {p : RTL.Program} {m : Mem} (hm : p.initMem = some m) :
    ∃ bc : BlockClassification,
      GenvMatch bc p.globalenv ∧ bcBelow bc m.nextblock ∧ BcNostack bc ∧
      Romatch bc m (romemFor o p) ∧
      (∀ b, Mem.validBlock m b = true → bc b ≠ .BCinvalid) := by
  obtain ⟨bc, GE, BELOW, NOSTACK, INV, VALID⟩ := initial_block_classification hm
  refine ⟨bc, GE, BELOW, NOSTACK, ?_, VALID⟩
  have A : InitialMemMatch o bc m p.globalenv :=
    alloc_globals_match o GE p.prog_defs (m := Mem.empty) (g := Genv.emptyGenv p.prog_public)
      rfl (Genv.symbBelow_emptyGenv _) (fun id b v hs => by simp at hs) hm
  have B := romem_for_consistent o p
  intro b id ab hb hab
  obtain ⟨v, DM, RO, NVOL, _, EQ⟩ := B id ab hab
  obtain ⟨b1, FS, FD⟩ := (Genv.find_def_symbol _ _ id _).1 DM
  have e : b1 = b := by
    have := INV b id hb
    change Genv.findSymbol (Genv.globalenv p.prog_public p.prog_defs) id = some b at this
    rw [FS] at this; cases this; rfl
  subst e EQ
  refine ⟨store_init_data_list_summary o _ _ _ (.bot _), ?_, fun ofs => ?_⟩
  · exact A id b1 v FS ((Genv.findVarInfo_iff _ _ _).2 FD) NVOL RO
  · have CH := (Genv.initMem_characterization_gen hm) b1 (.Gvar v) FD
    cases hperm : Mem.perm m b1 ofs .Max .Writable
    · rfl
    · have := (CH.2.1 ofs .Max .Writable hperm).2.2
      simp only [Genv.permGlobvar, NVOL, RO, permOrder] at this
      exact absurd this (by decide)

/-- `ValueAnalysis.sound_state`, for the whole program (see the header). -/
def SoundState (prog : RTL.Program) (st : RTL.State) : Prop :=
  SoundStateBase o abi (romemFor o prog) prog.globalenv st

variable {o abi}

/-- `ValueAnalysis.sound_step` -/
theorem sound_step {prog : RTL.Program}
    (hinj : ∀ ef, ExtcallMemInject (externalCall ef))
    (hprops : ∀ ef, ExtcallMemProps (externalCall ef) (Genv.toSenv prog.globalenv))
    {st : RTL.State} {t : Trace} {st' : RTL.State} (hstep : RTL.Step prog.globalenv st t st')
    (hs : SoundState o abi prog st) : SoundState o abi prog st' :=
  sound_step_base hinj hprops hstep hs

/-- `ValueAnalysis.sound_initial` -/
theorem sound_initial {prog : RTL.Program} {st : RTL.State} (h : RTL.InitialState prog st) :
    SoundState o abi prog st := by
  cases h with
  | intro b f m0 hm _ _ _ =>
    obtain ⟨bc, GE, BELOW, NOSTACK, RM, VALID⟩ := initial_mem_matches o hm
    refine .call (bc := bc) (.nil _ _ _) (fun v hv => by cases hv) RM ?_ GE NOSTACK
    apply mmatch_inj_top (m' := m0)
    have E : injOfBc bc = Mem.flatInj m0.nextblock := by
      funext x
      simp only [injOfBc, Mem.flatInj]
      by_cases hx : x < m0.nextblock
      · rw [if_pos hx]
        cases hbx : bc x <;> simp
        exact absurd hbx (VALID x ((Mem.validBlock_iff _ _).2 hx))
      · rw [if_neg hx]
        have : bc x = .BCinvalid := Classical.byContradiction fun h => hx (BELOW x h)
        rw [this]
    rw [E]
    exact Genv.initmem_inject hm

end SOUNDINIT

/-! ## Separate compilation (section `LINKING` of `ValueAnalysis.v`)

Rocq's `sound_state prog st` quantifies over every compilation unit `cunit`
with `linkorder cunit prog`: the state is sound for the read-only memory
abstraction `romem_for cunit` of each of them.  This is `SoundStateLink`
below; `SoundState` above is its instance at `cunit = prog`. -/

section LINKING
variable (o : ValueAOp.Options) (abi : Conventions1.AbiKind)

/-- `ValueAnalysis.romem_for_consistent_2` -/
theorem romem_for_consistent_2 {cu prog : RTL.Program} (hl : Linker.linkorder cu prog) :
    RomemConsistent o (Genv.defmap prog.prog_defs) (romemFor o cu) := by
  intro id ab hab
  obtain ⟨v, DM, RO, VO, DEFN, AB⟩ := romem_for_consistent o cu id ab hab
  obtain ⟨gd, P, Q⟩ := Linking.prog_defmap_linkorder hl DM
  have : gd = .Gvar v := by
    change Linking.LinkorderDef _ _ at Q
    cases Q with
    | gvar h2 =>
      change Linking.LinkorderVardef _ _ at h2
      cases h2 with
      | intro ro vo _ hi =>
        change Linking.LinkorderVarinit _ _ at hi
        cases hi with
        | refl => rfl
        | extern => simp [definitiveInitializer] at DEFN
        | common => simp [definitiveInitializer] at DEFN
  subst this
  exact ⟨v, P, RO, VO, DEFN, AB⟩

/-- `ValueAnalysis.initial_mem_matches`, for every compilation unit of the
    program. -/
theorem initial_mem_matches_link {p : RTL.Program} {m : Mem} (hm : p.initMem = some m) :
    ∃ bc : BlockClassification,
      GenvMatch bc p.globalenv ∧ bcBelow bc m.nextblock ∧ BcNostack bc ∧
      (∀ cu : RTL.Program, Linker.linkorder cu p → Romatch bc m (romemFor o cu)) ∧
      (∀ b, Mem.validBlock m b = true → bc b ≠ .BCinvalid) := by
  obtain ⟨bc, GE, BELOW, NOSTACK, INV, VALID⟩ := initial_block_classification hm
  refine ⟨bc, GE, BELOW, NOSTACK, ?_, VALID⟩
  have A : InitialMemMatch o bc m p.globalenv :=
    alloc_globals_match o GE p.prog_defs (m := Mem.empty) (g := Genv.emptyGenv p.prog_public)
      rfl (Genv.symbBelow_emptyGenv _) (fun id b v hs => by simp at hs) hm
  intro cu hcu
  have B := romem_for_consistent_2 o hcu
  intro b id ab hb hab
  obtain ⟨v, DM, RO, NVOL, _, EQ⟩ := B id ab hab
  obtain ⟨b1, FS, FD⟩ := (Genv.find_def_symbol _ _ id _).1 DM
  have e : b1 = b := by
    have := INV b id hb
    change Genv.findSymbol (Genv.globalenv p.prog_public p.prog_defs) id = some b at this
    rw [FS] at this; cases this; rfl
  subst e EQ
  refine ⟨store_init_data_list_summary o _ _ _ (.bot _), ?_, fun ofs => ?_⟩
  · exact A id b1 v FS ((Genv.findVarInfo_iff _ _ _).2 FD) NVOL RO
  · have CH := (Genv.initMem_characterization_gen hm) b1 (.Gvar v) FD
    cases hperm : Mem.perm m b1 ofs .Max .Writable
    · rfl
    · have := (CH.2.1 ofs .Max .Writable hperm).2.2
      simp only [Genv.permGlobvar, NVOL, RO, permOrder] at this
      exact absurd this (by decide)

/-- `ValueAnalysis.sound_state`: the state is sound for the read-only memory
    abstraction of every compilation unit of the program. -/
def SoundStateLink (prog : RTL.Program) (st : RTL.State) : Prop :=
  ∀ cu : RTL.Program, Linker.linkorder cu prog →
    SoundStateBase o abi (romemFor o cu) prog.globalenv st

variable {o abi}

/-- `ValueAnalysis.sound_step` (for `sound_state` over compilation units) -/
theorem sound_step_link {prog : RTL.Program}
    (hinj : ∀ ef, ExtcallMemInject (externalCall ef))
    (hprops : ∀ ef, ExtcallMemProps (externalCall ef) (Genv.toSenv prog.globalenv))
    {st : RTL.State} {t : Trace} {st' : RTL.State} (hstep : RTL.Step prog.globalenv st t st')
    (hs : SoundStateLink o abi prog st) : SoundStateLink o abi prog st' :=
  fun cu hcu => sound_step_base hinj hprops hstep (hs cu hcu)

/-- `ValueAnalysis.sound_initial` (for `sound_state` over compilation units) -/
theorem sound_initial_link {prog : RTL.Program} {st : RTL.State} (h : RTL.InitialState prog st) :
    SoundStateLink o abi prog st := by
  cases h with
  | intro b f m0 hm _ _ _ =>
    obtain ⟨bc, GE, BELOW, NOSTACK, RM, VALID⟩ := initial_mem_matches_link o hm
    intro cu hcu
    refine .call (bc := bc) (.nil _ _ _) (fun v hv => by cases hv) (RM cu hcu) ?_ GE NOSTACK
    apply mmatch_inj_top (m' := m0)
    have E : injOfBc bc = Mem.flatInj m0.nextblock := by
      funext x
      simp only [injOfBc, Mem.flatInj]
      by_cases hx : x < m0.nextblock
      · rw [if_pos hx]
        cases hbx : bc x <;> simp
        exact absurd hbx (VALID x ((Mem.validBlock_iff _ _).2 hx))
      · rw [if_neg hx]
        have : bc x = .BCinvalid := Classical.byContradiction fun h => hx (BELOW x h)
        rw [this]
    rw [E]
    exact Genv.initmem_inject hm

/-- `SoundState` is the instance of `SoundStateLink` at the program itself. -/
theorem SoundStateLink.self {prog : RTL.Program} {st : RTL.State}
    (h : SoundStateLink o abi prog st) : SoundState o abi prog st :=
  h prog (Linker.linkorder_refl _)

end LINKING

/-! ## Interface with other optimizations -/

section INTERFACE
variable {o : ValueAOp.Options} {abi : Conventions1.AbiKind} {prog : RTL.Program}

/-- `ValueAnalysis.avalue_sound` -/
theorem avalue_sound {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node}
    {e : RTL.Regset} {m : Mem} (r : Reg)
    {rm : Romem}
    (hs : SoundStateBase o abi rm prog.globalenv (.State s f (.Vptr sp Ptrofs.zero) pc e m)) :
    ∃ bc : BlockClassification,
      Vmatch bc (e.get r) (avalue ((analyze o abi rm f).get pc) r) ∧
      GenvMatch bc prog.globalenv ∧ bc sp = .BCstack := by
  cases hs with
  | regular STK AN EM RO MM GE SP => exact ⟨_, by rw [AN]; exact EM r, GE, SP⟩

/-- `ValueAnalysis.aaddr_sound` -/
theorem aaddr_sound {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node}
    {e : RTL.Regset} {m : Mem} {r : Reg} {b : Block} {ofs : Ptrofs}
    {rm : Romem}
    (hs : SoundStateBase o abi rm prog.globalenv (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (hr : e.get r = .Vptr b ofs) :
    ∃ bc : BlockClassification,
      Pmatch bc b ofs (aaddr o ((analyze o abi rm f).get pc) r) ∧
      GenvMatch bc prog.globalenv ∧ bc sp = .BCstack := by
  cases hs with
  | regular STK AN EM RO MM GE SP =>
    refine ⟨_, ?_, GE, SP⟩
    simp only [aaddr, AN]
    exact match_aptr_of_aval o.strict (hr ▸ EM r)

/-- `ValueAnalysis.aaddressing_sound` -/
theorem aaddressing_sound {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node}
    {e : RTL.Regset} {m : Mem} {addr : Op.Addressing} {args : List Reg} {b : Block}
    {ofs : Ptrofs}
    {rm : Romem}
    (hs : SoundStateBase o abi rm prog.globalenv (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (ha : Op.evalAddressing prog.globalenv (.Vptr sp Ptrofs.zero) addr (e.getList args) =
      some (.Vptr b ofs)) :
    ∃ bc : BlockClassification,
      Pmatch bc b ofs (aaddressing o ((analyze o abi rm f).get pc) addr args) ∧
      GenvMatch bc prog.globalenv ∧ bc sp = .BCstack := by
  cases hs with
  | regular STK AN EM RO MM GE SP =>
    refine ⟨_, ?_, GE, SP⟩
    simp only [aaddressing, AN]
    exact match_aptr_of_aval o.strict
      (ValueAOp.eval_static_addressing_sound GE SP addr ha (aregs_sound EM args))

/-- `ValueAnalysis.aaddr_arg_sound_1` -/
theorem aaddr_arg_sound_1 {F V : Type} {bc : BlockClassification} {rs : RTL.Regset} {ae : Aenv}
    {m : Mem} {rm : Romem} {am : Amem} {ge : Genv F V} {sp : Block} {a : BuiltinArg Reg}
    {b : Block} {ofs : Ptrofs}
    (EM : Ematch bc rs ae) (RM : Romatch bc m rm) (MM : Mmatch bc m am) (GM : GenvMatch bc ge)
    (SP : bc sp = .BCstack)
    (h : EvalBuiltinArg ge.toSenv (fun r => rs.get r) (.Vptr sp Ptrofs.zero) m a (.Vptr b ofs)) :
    Pmatch bc b ofs (aaddrArg o (.State ae am) a) := by
  have V := match_aptr_of_aval o.strict (abuiltin_arg_sound o EM RM MM GM SP h)
  cases a <;> first
    | exact V
    | exact pmatch_ge (.top _) V

/-- `ValueAnalysis.aaddr_arg_sound` -/
theorem aaddr_arg_sound {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node}
    {e : RTL.Regset} {m : Mem} {a : BuiltinArg Reg} {b : Block} {ofs : Ptrofs}
    {rm : Romem}
    (hs : SoundStateBase o abi rm prog.globalenv (.State s f (.Vptr sp Ptrofs.zero) pc e m))
    (h : EvalBuiltinArg prog.globalenv.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m a
      (.Vptr b ofs)) :
    ∃ bc : BlockClassification,
      Pmatch bc b ofs (aaddrArg o ((analyze o abi rm f).get pc) a) ∧
      GenvMatch bc prog.globalenv ∧ bc sp = .BCstack := by
  cases hs with
  | regular STK AN EM RO MM GE SP =>
    refine ⟨_, ?_, GE, SP⟩
    rw [AN]
    exact aaddr_arg_sound_1 EM RO MM GE SP h

end INTERFACE

end ValueAnalysis
end CC
