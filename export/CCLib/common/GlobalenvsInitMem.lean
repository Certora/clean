/-
  Theorems of `common/Globalenvs.v` about the initial memory state
  (`INITMEM`, `INITMEM_INJ`, `INITMEM_EXISTS`): `nextblock` and permissions
  after `alloc_globals`, the `unchanged_on` properties of `store_zeros` /
  `store_init_data`, the `*_not_fresh` lemmas, `initmem_inject`, and the
  sufficient condition `init_mem_exists`.

  As in `CCLib.common.GlobalenvsTheory`, a program is given by its public list `pub`
  and its definitions `gl`; `Genv.initMem pub gl` is `Genv.init_mem`.
  `Program.initMem` in `CCLib/cfrontend/Clight.lean` is `Genv.initMem p.prog_public
  p.prog_defs` by definition.
-/
import CCLib.common.GlobalenvsTheory
import CCLib.common.MemoryDrop

namespace CC
namespace Genv
variable {F V : Type}

open Mem

/-- `Genv.init_mem` -/
def initMem (pub : List Ident) (gl : List (Ident × GlobDef F V)) : Option Mem :=
  allocGlobals (globalenv pub gl) Mem.empty gl

section InitMem
variable (ge : Genv F V)

/-- `Genv.alloc_globals_app` -/
theorem allocGlobals_app : ∀ (gl1 gl2 : List (Ident × GlobDef F V)) (m m1 : Mem),
    allocGlobals ge m gl1 = some m1 → allocGlobals ge m1 gl2 = allocGlobals ge m (gl1 ++ gl2)
  | [], _, m, m1, h => by simp only [allocGlobals, Option.some.injEq] at h; subst h; rfl
  | a :: gl1, gl2, m, m1, h => by
    simp only [allocGlobals, List.cons_append] at h ⊢
    split at h
    · cases h
    · exact allocGlobals_app gl1 gl2 _ _ h

/-! ### `nextblock` -/

theorem storeZerosAux_nextblock : ∀ (n : Nat) {m : Mem} {b : Block} {p : Z} {m' : Mem},
    storeZerosAux m b p n = some m' → m'.nextblock = m.nextblock
  | 0, _, _, _, _, h => by simp only [storeZerosAux, Option.some.injEq] at h; subst h; rfl
  | n + 1, m, b, p, m', h => by
    simp only [storeZerosAux] at h
    split at h
    · cases h
    · next m1 hs => rw [storeZerosAux_nextblock n h, store_nextblock hs]

/-- `Genv.store_zeros_nextblock` -/
theorem storeZeros_nextblock {m : Mem} {b : Block} {p n : Z} {m' : Mem}
    (h : storeZeros m b p n = some m') : m'.nextblock = m.nextblock :=
  storeZerosAux_nextblock _ h

theorem storeInitData_nextblock {m : Mem} {b : Block} {p : Z} {i : InitData} {m' : Mem}
    (h : storeInitData ge m b p i = some m') : m'.nextblock = m.nextblock := by
  cases i <;> simp only [storeInitData] at h <;> try exact store_nextblock h
  · cases h; rfl
  · split at h
    · cases h
    · exact store_nextblock h

/-- `Genv.store_init_data_list_nextblock` -/
theorem storeInitDataList_nextblock : ∀ (idl : List InitData) {m : Mem} {b : Block} {p : Z}
    {m' : Mem}, storeInitDataList ge m b p idl = some m' → m'.nextblock = m.nextblock
  | [], _, _, _, _, h => by simp only [storeInitDataList, Option.some.injEq] at h; subst h; rfl
  | i :: idl, m, b, p, m', h => by
    simp only [storeInitDataList] at h
    split at h
    · cases h
    · next m1 hs => rw [storeInitDataList_nextblock idl h, storeInitData_nextblock ge hs]

/-- Unfolding `alloc_global` for a variable. -/
theorem allocGlobal_gvar_eq {m : Mem} {id : Ident} {v : GlobVar V} {m' : Mem}
    (h : allocGlobal ge m (id, .Gvar v) = some m') :
    ∃ m2 m3, storeZeros (alloc m 0 (InitData.listSize v.gvar_init)).1 m.nextblock 0
        (InitData.listSize v.gvar_init) = some m2 ∧
      storeInitDataList ge m2 m.nextblock 0 v.gvar_init = some m3 ∧
      dropPerm m3 m.nextblock 0 (InitData.listSize v.gvar_init) (permGlobvar v) = some m' := by
  simp only [allocGlobal, alloc] at h
  split at h
  · cases h
  · next m2 h2 =>
    split at h
    · cases h
    · next m3 h3 => exact ⟨m2, m3, h2, h3, h⟩

/-- Unfolding `alloc_global` for a function. -/
theorem allocGlobal_gfun_eq {m : Mem} {id : Ident} {f : F} {m' : Mem}
    (h : allocGlobal ge m (id, .Gfun f) = some m') :
    dropPerm (alloc m 0 1).1 m.nextblock 0 1 .Nonempty = some m' := by
  simpa only [allocGlobal, alloc] using h

/-- `Genv.alloc_global_nextblock` -/
theorem allocGlobal_nextblock {g : Ident × GlobDef F V} {m m' : Mem}
    (h : allocGlobal ge m g = some m') : m'.nextblock = m.nextblock.succ := by
  obtain ⟨id, f | v⟩ := g
  · rw [nextblock_drop (allocGlobal_gfun_eq ge h)]; rfl
  · obtain ⟨m2, m3, h2, h3, h4⟩ := allocGlobal_gvar_eq ge h
    rw [nextblock_drop h4, storeInitDataList_nextblock ge _ h3, storeZeros_nextblock h2]; rfl

/-- `Genv.alloc_globals_nextblock` -/
theorem allocGlobals_nextblock : ∀ (gl : List (Ident × GlobDef F V)) {m m' : Mem},
    allocGlobals ge m gl = some m' → m'.nextblock = advanceNext gl m.nextblock
  | [], _, _, h => by simp only [allocGlobals, Option.some.injEq] at h; subst h; rfl
  | g :: gl, m, m', h => by
    simp only [allocGlobals] at h
    split at h
    · cases h
    · next m1 hg =>
      rw [allocGlobals_nextblock gl h, allocGlobal_nextblock ge hg]; rfl

/-! ### Permissions -/

theorem storeZerosAux_perm : ∀ (n : Nat) {m : Mem} {b : Block} {p : Z} {m' : Mem},
    storeZerosAux m b p n = some m' → ∀ b' q k prm, perm m' b' q k prm = perm m b' q k prm
  | 0, _, _, _, _, h => by
    simp only [storeZerosAux, Option.some.injEq] at h; subst h; intros; rfl
  | n + 1, m, b, p, m', h => by
    simp only [storeZerosAux] at h
    split at h
    · cases h
    · next m1 hs =>
      intro b' q k prm
      rw [storeZerosAux_perm n h, perm_store hs]

/-- `Genv.store_zeros_perm` -/
theorem storeZeros_perm {m : Mem} {b : Block} {p n : Z} {m' : Mem}
    (h : storeZeros m b p n = some m') (b' : Block) (q : Z) (k : PermKind) (prm : Permission) :
    perm m' b' q k prm = perm m b' q k prm :=
  storeZerosAux_perm _ h b' q k prm

/-- `Genv.store_init_data_perm` -/
theorem storeInitData_perm {m : Mem} {b : Block} {p : Z} {i : InitData} {m' : Mem}
    (h : storeInitData ge m b p i = some m') (b' : Block) (q : Z) (k : PermKind)
    (prm : Permission) : perm m' b' q k prm = perm m b' q k prm := by
  cases i <;> simp only [storeInitData] at h <;> try exact perm_store h _ _ _ _
  · cases h; rfl
  · split at h
    · cases h
    · exact perm_store h _ _ _ _

/-- `Genv.store_init_data_list_perm` -/
theorem storeInitDataList_perm : ∀ (idl : List InitData) {m : Mem} {b : Block} {p : Z}
    {m' : Mem}, storeInitDataList ge m b p idl = some m' →
    ∀ b' q k prm, perm m' b' q k prm = perm m b' q k prm
  | [], _, _, _, _, h => by
    simp only [storeInitDataList, Option.some.injEq] at h; subst h; intros; rfl
  | i :: idl, m, b, p, m', h => by
    simp only [storeInitDataList] at h
    split at h
    · cases h
    · next m1 hs =>
      intro b' q k prm
      rw [storeInitDataList_perm idl h, storeInitData_perm ge hs]

theorem ne_nextblock_of_valid {m : Mem} {b : Block} (h : validBlock m b = true) :
    b ≠ m.nextblock := by
  intro he; subst he
  simp [validBlock, Positive.lt_iff] at h

/-- `Genv.alloc_global_perm` -/
theorem allocGlobal_perm {g : Ident × GlobDef F V} {m m' : Mem}
    (h : allocGlobal ge m g = some m') {b' : Block} (hv : validBlock m b' = true)
    (q : Z) (k : PermKind) (prm : Permission) : perm m' b' q k prm = perm m b' q k prm := by
  have hne := ne_nextblock_of_valid hv
  obtain ⟨id, f | v⟩ := g
  · rw [perm_drop_3 (allocGlobal_gfun_eq ge h) b' q k prm (Or.inl hne),
      perm_alloc_other m 0 1 b' hne]
  · obtain ⟨m2, m3, h2, h3, h4⟩ := allocGlobal_gvar_eq ge h
    rw [perm_drop_3 h4 b' q k prm (Or.inl hne), storeInitDataList_perm ge _ h3,
      storeZeros_perm h2, perm_alloc_other m _ _ b' hne]

theorem advanceNext_toNat : ∀ (gl : List (Ident × GlobDef F V)) (x : Positive),
    (advanceNext gl x).toNat = x.toNat + gl.length
  | [], _ => rfl
  | _ :: gl, x => by
    show (advanceNext gl x.succ).toNat = _
    rw [advanceNext_toNat gl x.succ, Positive.toNat_succ, List.length_cons]; omega

/-- `Genv.advance_next_le` -/
theorem advanceNext_le (gl : List (Ident × GlobDef F V)) (x : Positive) : x ≤ advanceNext gl x := by
  show x.toNat ≤ (advanceNext gl x).toNat
  rw [advanceNext_toNat]; omega

/-- `Genv.alloc_globals_perm` -/
theorem allocGlobals_perm : ∀ (gl : List (Ident × GlobDef F V)) {m m' : Mem},
    allocGlobals ge m gl = some m' → ∀ (b' : Block), validBlock m b' = true →
    ∀ q k prm, perm m' b' q k prm = perm m b' q k prm
  | [], _, _, h => by
    simp only [allocGlobals, Option.some.injEq] at h; subst h; intros; rfl
  | g :: gl, m, m', h => by
    simp only [allocGlobals] at h
    split at h
    · cases h
    · next m1 hg =>
      intro b' hv q k prm
      have hv1 : validBlock m1 b' = true := by
        simp only [validBlock, decide_eq_true_eq, Positive.lt_iff] at hv ⊢
        rw [allocGlobal_nextblock ge hg, Positive.toNat_succ]; omega
      rw [allocGlobals_perm gl h b' hv1, allocGlobal_perm ge hg hv]

/-! ### Data preservation -/

theorem storeZerosAux_unchanged (P : Block → Z → Prop) : ∀ (n : Nat) {m : Mem} {b : Block}
    {p : _root_.Int} {m' : Mem}, storeZerosAux m b p n = some m' →
    (∀ i : _root_.Int, p ≤ i → i < p + n → ¬ P b i) → UnchangedOn P m m'
  | 0, _, _, _, _, h, _ => by
    simp only [storeZerosAux, Option.some.injEq] at h; subst h; exact unchangedOn_refl _
  | n + 1, m, b, p, m', h, hP => by
    simp only [storeZerosAux] at h
    split at h
    · cases h
    · next m1 hs =>
      refine UnchangedOn.trans (store_unchangedOn hs fun i h1 h2 => hP i h1 ?_) ?_
      · simp only [sizeChunk] at h2; omega
      · exact storeZerosAux_unchanged P n h fun i h1 h2 => hP i (by omega) (by omega)

/-- `Genv.store_zeros_unchanged` -/
theorem storeZeros_unchanged (P : Block → Z → Prop) {m : Mem} {b : Block} {p n : _root_.Int}
    {m' : Mem} (h : storeZeros m b p n = some m')
    (hP : ∀ i : _root_.Int, p ≤ i → i < p + n → ¬ P b i) : UnchangedOn P m m' :=
  storeZerosAux_unchanged P _ h fun i h1 h2 => hP i h1 (by omega)

theorem sizeChunk_Mptr : sizeChunk Mptr = 8 := rfl

/-- `Genv.store_init_data_unchanged` -/
theorem storeInitData_unchanged (P : Block → Z → Prop) {m : Mem} {b : Block} {p : _root_.Int}
    {i : InitData} {m' : Mem} (h : storeInitData ge m b p i = some m')
    (hP : ∀ ofs : _root_.Int, p ≤ ofs → ofs < p + i.size → ¬ P b ofs) : UnchangedOn P m m' := by
  cases i <;> simp only [storeInitData] at h <;>
    try exact store_unchangedOn h fun o h1 h2 => hP o h1 (by exact h2)
  · cases h; exact unchangedOn_refl _
  · split at h
    · cases h
    · exact store_unchangedOn h fun o h1 h2 =>
        hP o h1 (by simpa [InitData.size, sizeChunk, Mptr, Archi.ptr64] using h2)

theorem InitData.size_nonneg (i : InitData) : (0 : _root_.Int) ≤ i.size := by
  cases i <;> simp only [InitData.size] <;> first | decide | exact Int.le_max_right _ _

/-- `Genv.store_init_data_list_unchanged` -/
theorem storeInitDataList_unchanged (P : Block → Z → Prop) : ∀ (il : List InitData) {m : Mem}
    {b : Block} {p : _root_.Int} {m' : Mem}, storeInitDataList ge m b p il = some m' →
    (∀ ofs : _root_.Int, p ≤ ofs → ¬ P b ofs) → UnchangedOn P m m'
  | [], _, _, _, _, h, _ => by
    simp only [storeInitDataList, Option.some.injEq] at h; subst h; exact unchangedOn_refl _
  | i :: il, m, b, p, m', h, hP => by
    simp only [storeInitDataList] at h
    split at h
    · cases h
    · next m1 hs =>
      have h0 : (0 : _root_.Int) ≤ i.size := InitData.size_nonneg i
      exact (storeInitData_unchanged ge P hs fun o h1 _ => hP o h1).trans
        (storeInitDataList_unchanged P il h fun o h1 => hP o (by omega))

end InitMem

/-! ## `init_mem` and the global environment -/

/-- `Genv.init_mem_genv_next` -/
theorem initMem_genv_next {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    (h : initMem pub gl = some m) : (globalenv pub gl).genv_next = m.nextblock := by
  rw [allocGlobals_nextblock _ gl h]
  exact genv_next_addGlobals gl _

/-- `Genv.find_symbol_not_fresh` -/
theorem findSymbol_not_fresh {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    {id : Ident} {b : Block} (h : initMem pub gl = some m)
    (hs : findSymbol (globalenv pub gl) id = some b) : validBlock m b = true := by
  have := symbBelow_globalenv pub gl id b hs
  rw [initMem_genv_next h] at this
  simpa [validBlock] using this

/-- `Genv.find_def_not_fresh` -/
theorem findDef_not_fresh {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    {b : Block} {g : GlobDef F V} (h : initMem pub gl = some m)
    (hd : findDef (globalenv pub gl) b = some g) : validBlock m b = true := by
  have := defsBelow_globalenv pub gl b g hd
  rw [initMem_genv_next h] at this
  simpa [validBlock] using this

/-- `Genv.find_funct_ptr_not_fresh` -/
theorem findFunctPtr_not_fresh {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    {b : Block} {f : F} (h : initMem pub gl = some m)
    (hf : findFunctPtr (globalenv pub gl) b = some f) : validBlock m b = true :=
  findDef_not_fresh h ((findFunctPtr_iff _ _ _).1 hf)

/-- `Genv.find_var_info_not_fresh` -/
theorem findVarInfo_not_fresh {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    {b : Block} {gv : GlobVar V} (h : initMem pub gl = some m)
    (hf : findVarInfo (globalenv pub gl) b = some gv) : validBlock m b = true :=
  findDef_not_fresh h ((findVarInfo_iff _ _ _).1 hf)

/-! ## Compatibility with memory injections (`INITMEM_INJ`) -/

theorem storeZerosAux_neutral (thr : Block) : ∀ (n : Nat) {m : Mem} {b : Block} {p : Z} {m' : Mem},
    InjectNeutral thr m → b < thr → storeZerosAux m b p n = some m' → InjectNeutral thr m'
  | 0, _, _, _, _, hn, _, h => by
    simp only [storeZerosAux, Option.some.injEq] at h; subst h; exact hn
  | n + 1, m, b, p, m', hn, hb, h => by
    simp only [storeZerosAux] at h
    split at h
    · cases h
    · next m1 hs =>
      exact storeZerosAux_neutral thr n (store_inject_neutral hs hn hb (.int _)) hb h

/-- `Genv.store_zeros_neutral` -/
theorem storeZeros_neutral (thr : Block) {m : Mem} {b : Block} {p n : Z} {m' : Mem}
    (hn : InjectNeutral thr m) (hb : b < thr) (h : storeZeros m b p n = some m') :
    InjectNeutral thr m' :=
  storeZerosAux_neutral thr _ hn hb h

section InitMemInj
variable (ge : Genv F V) (thr : Block)
  (symb_inject : ∀ id b, findSymbol ge id = some b → b < thr)
include symb_inject

/-- `Genv.store_init_data_neutral` -/
theorem storeInitData_neutral {m : Mem} {b : Block} {p : Z} {i : InitData} {m' : Mem}
    (hn : InjectNeutral thr m) (hb : b < thr) (h : storeInitData ge m b p i = some m') :
    InjectNeutral thr m' := by
  cases i <;> simp only [storeInitData] at h
  · exact store_inject_neutral h hn hb (.int _)
  · exact store_inject_neutral h hn hb (.int _)
  · exact store_inject_neutral h hn hb (.int _)
  · exact store_inject_neutral h hn hb (.long _)
  · exact store_inject_neutral h hn hb (.single _)
  · exact store_inject_neutral h hn hb (.float _)
  · cases h; exact hn
  · split at h
    · cases h
    · next b' hs =>
      refine store_inject_neutral h hn hb (.ptr 0 ?_ ?_)
      · simp only [flatInj, if_pos (symb_inject _ _ hs)]
      · rw [Integers.Ptrofs.repr_zero, Integers.Ptrofs.add_zero]

/-- `Genv.store_init_data_list_neutral` -/
theorem storeInitDataList_neutral : ∀ (idl : List InitData) {m : Mem} {b : Block} {p : Z}
    {m' : Mem}, InjectNeutral thr m → b < thr → storeInitDataList ge m b p idl = some m' →
    InjectNeutral thr m'
  | [], _, _, _, _, hn, _, h => by
    simp only [storeInitDataList, Option.some.injEq] at h; subst h; exact hn
  | i :: idl, m, b, p, m', hn, hb, h => by
    simp only [storeInitDataList] at h
    split at h
    · cases h
    · next m1 hs =>
      exact storeInitDataList_neutral idl (storeInitData_neutral ge thr symb_inject hn hb hs) hb h

/-- `Genv.alloc_global_neutral` -/
theorem allocGlobal_neutral {g : Ident × GlobDef F V} {m m' : Mem}
    (h : allocGlobal ge m g = some m') (hn : InjectNeutral thr m) (hlt : m.nextblock < thr) :
    InjectNeutral thr m' := by
  obtain ⟨id, f | v⟩ := g
  · exact drop_inject_neutral (allocGlobal_gfun_eq ge h)
      (alloc_inject_neutral (rfl : alloc m 0 1 = (_, m.nextblock)) hn hlt) hlt
  · obtain ⟨m2, m3, h2, h3, h4⟩ := allocGlobal_gvar_eq ge h
    refine drop_inject_neutral h4 ?_ hlt
    refine storeInitDataList_neutral ge thr symb_inject _ ?_ hlt h3
    refine storeZeros_neutral thr ?_ hlt h2
    exact alloc_inject_neutral (rfl : alloc m 0 _ = (_, m.nextblock)) hn hlt

/-- `Genv.alloc_globals_neutral` -/
theorem allocGlobals_neutral : ∀ (gl : List (Ident × GlobDef F V)) {m m' : Mem},
    allocGlobals ge m gl = some m' → InjectNeutral thr m → m'.nextblock ≤ thr →
    InjectNeutral thr m'
  | [], _, _, h, hn, _ => by
    simp only [allocGlobals, Option.some.injEq] at h; subst h; exact hn
  | g :: gl, m, m', h, hn, hle => by
    have heq := allocGlobals_nextblock ge (g :: gl) h
    simp only [allocGlobals] at h
    split at h
    · cases h
    · next m1 hg =>
      have hle' : m.nextblock.succ ≤ m'.nextblock := by
        rw [heq]; exact advanceNext_le gl _
      have hlt : m.nextblock < thr := by
        simp only [Positive.lt_iff] at *
        have := Positive.toNat_succ m.nextblock
        change m.nextblock.succ.toNat ≤ m'.nextblock.toNat at hle'
        change m'.nextblock.toNat ≤ thr.toNat at hle
        omega
      exact allocGlobals_neutral gl h (allocGlobal_neutral ge thr symb_inject hg hn hlt) hle

end InitMemInj

/-- `Genv.initmem_inject` -/
theorem initmem_inject {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    (h : initMem pub gl = some m) : Inject (flatInj m.nextblock) m m := by
  apply neutral_inject
  refine allocGlobals_neutral (globalenv pub gl) m.nextblock ?_ gl h
    (empty_inject_neutral _) (Nat.le_refl _)
  intro id b hs
  have := findSymbol_not_fresh h hs
  simpa [validBlock] using this

/-! ## Sufficient conditions for the initial memory to exist (`INITMEM_EXISTS`) -/

/-- `Genv.init_data_alignment` -/
def initDataAlignment : InitData → Z
  | .Init_int8 _ => 1
  | .Init_int16 _ => 2
  | .Init_int32 _ => 4
  | .Init_int64 _ => 8
  | .Init_float32 _ => 4
  | .Init_float64 _ => 4
  | .Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | .Init_space _ => 1

/-- `Genv.init_data_list_aligned` -/
def initDataListAligned : Z → List InitData → Prop
  | _, [] => True
  | p, i :: il => initDataAlignment i ∣ p ∧ initDataListAligned (p + i.size) il

section InitMemExists
variable (ge : Genv F V)

theorem storeZerosAux_exists : ∀ (n : Nat) (m : Mem) (b : Block) (p : _root_.Int),
    rangePerm m b p (p + (n : _root_.Int) : _root_.Int) .Cur .Writable = true →
      ∃ m', storeZerosAux m b p n = some m'
  | 0, m, _, _, _ => ⟨m, rfl⟩
  | n + 1, m, b, p, hr => by
    have hva : validAccess m .Mint8unsigned b p .Writable = true := by
      simp only [validAccess, Bool.and_eq_true]
      refine ⟨rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
        rangePerm_perm _ _ _ _ _ _ hr o h1 (by simp only [sizeChunk] at h2; omega), ?_⟩
      simp [alignChunk]
    obtain ⟨m1, hs⟩ := valid_access_store (.Vint Integers.Int.zero) hva
    simp only [storeZerosAux, hs]
    refine storeZerosAux_exists n m1 b (p + 1) (rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => ?_)
    rw [perm_store hs]
    exact rangePerm_perm _ _ _ _ _ _ hr o (by omega) (by omega)

/-- `Genv.store_zeros_exists` -/
theorem storeZeros_exists (m : Mem) (b : Block) (p n : _root_.Int)
    (hr : rangePerm m b p (p + n) .Cur .Writable = true) : ∃ m', storeZeros m b p n = some m' :=
  storeZerosAux_exists _ m b p (rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
    rangePerm_perm _ _ _ _ _ _ hr o h1 (by omega))

/-- `Genv.store_init_data_exists` -/
theorem storeInitData_exists (m : Mem) (b : Block) (p : _root_.Int) (i : InitData)
    (hr : rangePerm m b p (p + i.size) .Cur .Writable = true)
    (hal : initDataAlignment i ∣ p)
    (hsym : ∀ id ofs, i = .Init_addrof id ofs → ∃ b, findSymbol ge id = some b) :
    ∃ m', storeInitData ge m b p i = some m' := by
  have dfl : ∀ (chunk : Chunk) (v : Val), i.size = sizeChunk chunk →
      initDataAlignment i = alignChunk chunk → ∃ m', store chunk m b p v = some m' := by
    intro chunk v hs ha
    refine valid_access_store v ?_
    simp only [validAccess, Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [← hs]; exact hr, ?_⟩
    rw [← ha]
    exact Int.emod_eq_zero_of_dvd hal
  cases i with
  | Init_int8 n => exact dfl _ _ rfl rfl
  | Init_int16 n => exact dfl _ _ rfl rfl
  | Init_int32 n => exact dfl _ _ rfl rfl
  | Init_int64 n => exact dfl _ _ rfl rfl
  | Init_float32 n => exact dfl _ _ rfl rfl
  | Init_float64 n => exact dfl _ _ rfl rfl
  | Init_space n => exact ⟨m, rfl⟩
  | Init_addrof id ofs =>
    obtain ⟨b1, hb1⟩ := hsym id ofs rfl
    simp only [storeInitData, hb1]
    exact dfl _ _ rfl rfl

theorem InitData.listSize_cons (i : InitData) (il : List InitData) :
    InitData.listSize (i :: il) = i.size + InitData.listSize il := rfl

theorem InitData.listSize_nonneg : ∀ (il : List InitData), (0 : _root_.Int) ≤ InitData.listSize il
  | [] => Int.le_refl _
  | i :: il => by
    rw [InitData.listSize_cons]
    have := InitData.size_nonneg i
    have := InitData.listSize_nonneg il
    omega

/-- `Genv.store_init_data_list_exists` -/
theorem storeInitDataList_exists (b : Block) : ∀ (il : List InitData) (m : Mem) (p : _root_.Int),
    rangePerm m b p (p + InitData.listSize il) .Cur .Writable = true →
    initDataListAligned p il →
    (∀ id ofs, InitData.Init_addrof id ofs ∈ il → ∃ b, findSymbol ge id = some b) →
    ∃ m', storeInitDataList ge m b p il = some m'
  | [], m, _, _, _, _ => ⟨m, rfl⟩
  | i :: il, m, p, hr, hal, hsym => by
    rw [InitData.listSize_cons] at hr
    have h0 := InitData.size_nonneg i
    have h1 := InitData.listSize_nonneg il
    obtain ⟨m1, hs⟩ := storeInitData_exists ge m b p i
      (rangePerm_intro _ _ _ _ _ _ fun o h2 h3 => rangePerm_perm _ _ _ _ _ _ hr o h2 (by omega))
      hal.1 (fun id ofs he => hsym id ofs (by rw [he]; exact List.mem_cons_self ..))
    simp only [storeInitDataList, hs]
    refine storeInitDataList_exists b il m1 (p + i.size) (rangePerm_intro _ _ _ _ _ _ fun o h2 h3 => ?_)
      hal.2 (fun id ofs hin => hsym id ofs (List.mem_cons_of_mem _ hin))
    rw [storeInitData_perm ge hs]
    exact rangePerm_perm _ _ _ _ _ _ hr o (by omega) (by omega)

/-- The precondition of `Genv.alloc_global_exists`. -/
def AllocGlobalOk : Ident × GlobDef F V → Prop
  | (_, .Gfun _) => True
  | (_, .Gvar v) => initDataListAligned 0 v.gvar_init ∧
      ∀ i o, InitData.Init_addrof i o ∈ v.gvar_init → ∃ b, findSymbol ge i = some b

/-- `Genv.alloc_global_exists` -/
theorem allocGlobal_exists (m : Mem) (idg : Ident × GlobDef F V) (h : AllocGlobalOk ge idg) :
    ∃ m', allocGlobal ge m idg = some m' := by
  obtain ⟨id, f | v⟩ := idg
  · obtain ⟨m2, hd⟩ := dropPerm_isSome (m := (alloc m 0 1).1) (b := m.nextblock) (lo := 0) (hi := 1)
      (p := .Nonempty) (rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => perm_alloc_same m 0 1 o _ h1 h2)
    exact ⟨m2, by simpa only [allocGlobal, alloc] using hd⟩
  · obtain ⟨hP, hQ⟩ := h
    have hsz := InitData.listSize_nonneg v.gvar_init
    let sz := InitData.listSize v.gvar_init
    have P1 : rangePerm (alloc m 0 sz).1 m.nextblock 0 sz .Cur .Freeable = true :=
      rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => perm_alloc_same m 0 sz o _ h1 h2
    obtain ⟨m2, h2⟩ := storeZeros_exists (alloc m 0 sz).1 m.nextblock 0 sz
      (by rw [Int.zero_add]; exact rangePerm_implies P1 (by rfl))
    have P2 : rangePerm m2 m.nextblock 0 sz .Cur .Freeable = true := by
      rw [rangePerm_congr (fun o => storeZeros_perm h2 m.nextblock o .Cur .Freeable)]; exact P1
    obtain ⟨m3, h3⟩ := storeInitDataList_exists ge m.nextblock v.gvar_init m2 0
      (by rw [Int.zero_add]; exact rangePerm_implies P2 (by rfl)) hP hQ
    have P3 : rangePerm m3 m.nextblock 0 sz .Cur .Freeable = true := by
      rw [rangePerm_congr (fun o => storeInitDataList_perm ge _ h3 m.nextblock o .Cur .Freeable)]
      exact P2
    obtain ⟨m4, h4⟩ := dropPerm_isSome (p := permGlobvar v) P3
    refine ⟨m4, ?_⟩
    simp only [allocGlobal, alloc]
    simp only [alloc, sz] at h2 h3 h4
    rw [h2]
    simp only [h3, h4]

end InitMemExists

/-- `Genv.init_mem_exists` -/
theorem initMem_exists (pub : List Ident) (gl : List (Ident × GlobDef F V))
    (h : ∀ id v, (id, GlobDef.Gvar v) ∈ gl →
      initDataListAligned 0 v.gvar_init ∧
      ∀ i o, InitData.Init_addrof i o ∈ v.gvar_init →
        ∃ b, findSymbol (globalenv pub gl) i = some b) :
    ∃ m, initMem pub gl = some m := by
  unfold initMem
  generalize globalenv pub gl = ge at h
  suffices ∀ (l : List (Ident × GlobDef F V)) (m : Mem), (∀ g ∈ l, g ∈ gl) →
      ∃ m', allocGlobals ge m l = some m' from this gl Mem.empty (fun _ h => h)
  intro l
  induction l with
  | nil => intro m _; exact ⟨m, rfl⟩
  | cons g l ih =>
    intro m hsub
    have hok : AllocGlobalOk ge g := by
      obtain ⟨id, f | v⟩ := g
      · trivial
      · exact h id v (hsub _ (List.mem_cons_self ..))
    obtain ⟨m1, h1⟩ := allocGlobal_exists ge m g hok
    simp only [allocGlobals, h1]
    exact ih m1 (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg'))

end Genv
end CC
