/-
  Characterization of the initial memory state — port of the
  `INITMEM_INVERSION` section and of `globals_initialized` /
  `init_mem_characterization_gen` from `common/Globalenvs.v`.

  `GlobalsInitialized g ge m` omits the `load_store_init_data` conjunct of
  CompCert's `globals_initialized` (which no ported proof consumes); it keeps
  the permission facts and the `loadbytes` description of each variable.
-/
import CCLib.common.GlobalenvsBytes
import CCLib.common.MemoryUnchanged

namespace CC
namespace Genv
variable {F V : Type}

open Mem

/-! ## Inversion: what a successful `init_mem` tells about the program -/

section Inversion
variable (ge : Genv F V)

/-- `Genv.store_init_data_list_aligned` and `store_init_data_list_free_idents`. -/
theorem storeInitDataList_inv (b : Block) : ∀ (il : List InitData) {m : Mem} {p : Z} {m' : Mem},
    storeInitDataList ge m b p il = some m' →
    initDataListAligned p il ∧
      ∀ i o, InitData.Init_addrof i o ∈ il → ∃ b', findSymbol ge i = some b'
  | [], _, _, _, _ => ⟨trivial, fun _ _ h => nomatch h⟩
  | i1 :: il, m, p, m', h => by
    simp only [storeInitDataList] at h
    split at h
    · cases h
    · next m1 hs =>
      obtain ⟨A, B⟩ := storeInitDataList_inv b il h
      refine ⟨⟨storeInitData_aligned ge hs, A⟩, fun i o hin => ?_⟩
      rcases List.mem_cons.1 hin with he | hin
      · subst he
        simp only [storeInitData] at hs
        split at hs
        · cases hs
        · next b' hb => exact ⟨b', hb⟩
      · exact B i o hin

theorem allocGlobals_mem_inv : ∀ (gl : List (Ident × GlobDef F V)) {m m' : Mem},
    allocGlobals ge m gl = some m' → ∀ g ∈ gl, ∃ m1 m1', allocGlobal ge m1 g = some m1'
  | [], _, _, _, _, hin => nomatch hin
  | g0 :: gl, m, m', h, g, hin => by
    simp only [allocGlobals] at h
    split at h
    · cases h
    · next m1 hg =>
      rcases List.mem_cons.1 hin with he | hin
      · subst he; exact ⟨m, m1, hg⟩
      · exact allocGlobals_mem_inv gl h g hin

end Inversion

/-- `Genv.init_mem_inversion` -/
theorem initMem_inversion {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    (h : initMem pub gl = some m) {id : Ident} {v : GlobVar V} (hin : (id, .Gvar v) ∈ gl) :
    initDataListAligned 0 v.gvar_init ∧
      ∀ i o, InitData.Init_addrof i o ∈ v.gvar_init →
        ∃ b, findSymbol (globalenv pub gl) i = some b := by
  obtain ⟨m1, m1', ha⟩ := allocGlobals_mem_inv _ gl h _ hin
  obtain ⟨m2, m3, _, h3, _⟩ := allocGlobal_gvar_eq _ ha
  exact storeInitDataList_inv _ _ _ h3

/-! ## `globals_initialized` -/

/-- `Genv.globals_initialized` (minus `load_store_init_data`): `g` locates the
    definitions, `ge` is the environment used to compute initial bytes. -/
def GlobalsInitialized (g ge : Genv F V) (m : Mem) : Prop :=
  ∀ b gd, findDef g b = some gd →
    match gd with
    | .Gfun _ => perm m b 0 .Cur .Nonempty = true ∧
        ∀ ofs k p, perm m b ofs k p = true → ofs = 0 ∧ p = .Nonempty
    | .Gvar v =>
        rangePerm m b 0 (InitData.listSize v.gvar_init) .Cur (permGlobvar v) = true ∧
        (∀ ofs k p, perm m b ofs k p = true →
          0 ≤ ofs ∧ ofs < InitData.listSize v.gvar_init ∧ permOrder (permGlobvar v) p = true) ∧
        (v.gvar_volatile = false →
          loadbytes m b 0 (InitData.listSize v.gvar_init) = some (bytesOfInitDataList ge v.gvar_init))

section Char
variable (ge : Genv F V)

/-- `alloc_global` leaves every block other than the new one unchanged. -/
theorem allocGlobal_unchanged {m m' : Mem} {g : Ident × GlobDef F V}
    (h : allocGlobal ge m g = some m') : UnchangedOn (fun b _ => b ≠ m.nextblock) m m' := by
  obtain ⟨id, f | v⟩ := g
  · have hd := allocGlobal_gfun_eq ge h
    exact (alloc_unchangedOn (lo := 0) (hi := 1) (b := m.nextblock) rfl).trans
      (dropPerm_unchangedOn hd fun _ _ _ hne => hne rfl)
  · obtain ⟨m2, m3, h2, h3, h4⟩ := allocGlobal_gvar_eq ge h
    exact (alloc_unchangedOn (lo := 0) (hi := InitData.listSize v.gvar_init) (b := m.nextblock) rfl).trans
      ((storeZeros_unchanged _ h2 fun _ _ _ hne => hne rfl).trans
      ((storeInitDataList_unchanged ge _ _ h3 fun _ _ hne => hne rfl).trans
      (dropPerm_unchangedOn h4 fun _ _ _ hne => hne rfl)))

theorem permOrder_nonempty {p : Permission} (h : permOrder .Nonempty p = true) : p = .Nonempty := by
  cases p <;> first | rfl | (simp [permOrder, Permission.rank] at h)

theorem permGlobvar_readable {v : GlobVar V} (h : v.gvar_volatile = false) :
    permOrder (permGlobvar v) .Readable = true := by
  unfold permGlobvar; rw [h]
  simp only [Bool.false_eq_true, if_false]
  split <;> decide

/-- `Genv.alloc_global_initialized` -/
theorem allocGlobal_initialized {g : Genv F V} {m m' : Mem} {idg : Ident × GlobDef F V}
    (hnext : g.genv_next = m.nextblock) (hbelow : DefsBelow g)
    (hinit : GlobalsInitialized g ge m) (h : allocGlobal ge m idg = some m') :
    GlobalsInitialized (addGlobal g idg) ge m' := by
  intro b gd hb
  rw [findDef_addGlobal] at hb
  split at hb
  · next hbe =>
    cases hb
    rw [hnext] at hbe; subst hbe
    obtain ⟨id, f | v⟩ := idg
    · have hd := allocGlobal_gfun_eq ge h
      refine ⟨perm_drop_1 hd _ (Int.le_refl _) (by decide), fun ofs k p hp => ?_⟩
      have h1 := perm_drop_4 hd hp
      have h2 := perm_alloc_inv h1
      rw [if_pos rfl] at h2
      obtain ⟨h2a, h2b⟩ := h2
      have : ofs = 0 := by simp only [CC.Z] at *; omega
      subst this
      exact ⟨rfl, permOrder_nonempty (perm_drop_2 hd (Int.le_refl _) (by decide) hp)⟩
    · obtain ⟨m2, m3, h2, h3, h4⟩ := allocGlobal_gvar_eq ge h
      refine ⟨rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => perm_drop_1 h4 _ h1 h2,
        fun ofs k p hp => ?_, fun hvol => ?_⟩
      · have h1 := perm_drop_4 h4 hp
        rw [storeInitDataList_perm ge _ h3, storeZeros_perm h2] at h1
        have h5 := perm_alloc_inv h1
        rw [if_pos rfl] at h5
        exact ⟨h5.1, h5.2, perm_drop_2 h4 h5.1 h5.2 hp⟩
      · rw [loadbytes_drop h4 (Or.inr (Or.inr (Or.inr (permGlobvar_readable hvol))))]
        refine storeInitDataList_loadbytes ge _ _ h3 ?_
        have := storeZeros_loadbytes h2
        exact this
  · next hbe =>
    have hlt := hbelow b gd hb
    rw [hnext] at hlt
    have hne : b ≠ m.nextblock := fun he => by
      subst he; simp [Positive.lt_iff] at hlt
    have hv : validBlock m b = true := by simpa [validBlock] using hlt
    have U := allocGlobal_unchanged ge h
    have hperm : ∀ ofs k p, perm m' b ofs k p = perm m b ofs k p :=
      fun ofs k p => allocGlobal_perm ge h hv ofs k p
    have hi := hinit b gd hb
    cases gd with
    | Gfun f =>
      refine ⟨by rw [hperm]; exact hi.1, fun ofs k p hp => hi.2 ofs k p (by rw [← hperm]; exact hp)⟩
    | Gvar v =>
      refine ⟨?_, fun ofs k p hp => hi.2.1 ofs k p (by rw [← hperm]; exact hp),
        fun hvol => U.loadbytes (fun _ _ _ => hne) (hi.2.2 hvol)⟩
      rw [rangePerm_congr (fun o => hperm o .Cur _)]; exact hi.1

theorem allocGlobals_initialized : ∀ (gl : List (Ident × GlobDef F V)) {g : Genv F V} {m m' : Mem},
    g.genv_next = m.nextblock → DefsBelow g → GlobalsInitialized g ge m →
    allocGlobals ge m gl = some m' → GlobalsInitialized (addGlobals g gl) ge m'
  | [], _, _, _, _, _, hi, h => by
    simp only [allocGlobals, Option.some.injEq] at h; subst h; exact hi
  | idg :: gl, g, m, m', hn, hb, hi, h => by
    simp only [allocGlobals] at h
    split at h
    · cases h
    · next m1 hg =>
      show GlobalsInitialized (addGlobals (addGlobal g idg) gl) ge m'
      refine allocGlobals_initialized gl ?_ (defsBelow_addGlobal _ hb)
        (allocGlobal_initialized ge hn hb hi hg) h
      rw [allocGlobal_nextblock ge hg, ← hn]; rfl

end Char

/-- `Genv.init_mem_characterization_gen` -/
theorem initMem_characterization_gen {pub : List Ident} {gl : List (Ident × GlobDef F V)} {m : Mem}
    (h : initMem pub gl = some m) :
    GlobalsInitialized (globalenv pub gl) (globalenv pub gl) m :=
  allocGlobals_initialized _ gl rfl (defsBelow_emptyGenv pub)
    (fun b gd hb => by simp at hb) h

end Genv
end CC
