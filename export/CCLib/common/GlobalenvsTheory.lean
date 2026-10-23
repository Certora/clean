/-
  Theorems of `common/Globalenvs.v` about global environments: the
  `GLOBALENV_PRINCIPLES` section, the properties of the lookup functions
  (`find_symbol`, `find_def`, `find_funct`, `invert_symbol`, …), and the
  correspondence between `globalenv p` and `prog_defmap p`.

  CompCert's `Genv.t` carries the invariants `genv_symb_range`,
  `genv_defs_range` and `genv_vars_inj`; the port's `Genv` carries no
  invariants (see the header of `CCLib/common/Globalenvs.lean`).  Theorems that need
  one of these take it as a hypothesis (`SymbBelow`, `DefsBelow`,
  `SymbInjective`), and each is proved for every environment built by
  `globalenv` (`symbBelow_globalenv`, `defsBelow_globalenv`,
  `symbInjective_globalenv`), so the hypotheses can always be discharged for
  the environment of a program.

  CompCert's `globalenv p` and `prog_defmap p` take a whole `program`; the port
  has no generic program record (only Clight's), so they are stated here for a
  public list `pub` and a definition list `gl` (`Genv.globalenv pub gl`,
  `Genv.defmap gl`).  `Program.globalenv` in `CCLib/cfrontend/Clight.lean` is
  `Genv.globalenv p.prog_public p.prog_defs` by definition.
-/
import CCLib.common.Globalenvs
import CCLib.lib.MapsTheory
import CCLib.common.Values
import CCLib.lib.IntegersPtrofs

namespace CC
namespace Genv
variable {F V : Type}

/-- `Genv.globalenv` for a program with public symbols `pub` and definitions `gl`. -/
def globalenv (pub : List Ident) (gl : List (Ident × GlobDef F V)) : Genv F V :=
  addGlobals (emptyGenv pub) gl

/-- `AST.prog_defmap`: the definitions of a program as a map (later
definitions of the same name win). -/
def defmap (gl : List (Ident × GlobDef F V)) : PTree (GlobDef F V) :=
  gl.foldl (fun m idg => m.set idg.1 idg.2) PTree.empty

/-- `AST.prog_defs_names` -/
def defsNames (gl : List (Ident × GlobDef F V)) : List Ident := gl.map Prod.fst

/-- CompCert's `genv_defs_range`: every definition lives in an allocated block. -/
def DefsBelow (ge : Genv F V) : Prop :=
  ∀ b g, findDef ge b = some g → b < ge.genv_next

/-! ## Basic equations -/

@[simp] theorem addGlobals_nil (ge : Genv F V) : addGlobals ge [] = ge := rfl

@[simp] theorem addGlobals_cons (ge : Genv F V) (g : Ident × GlobDef F V)
    (gl : List (Ident × GlobDef F V)) : addGlobals ge (g :: gl) = addGlobals (addGlobal ge g) gl :=
  rfl

/-- `Genv.add_globals_app` -/
theorem addGlobals_app (gl1 gl2 : List (Ident × GlobDef F V)) (ge : Genv F V) :
    addGlobals ge (gl1 ++ gl2) = addGlobals (addGlobals ge gl1) gl2 := by
  simp [addGlobals, List.foldl_append]

theorem findSymbol_addGlobal (ge : Genv F V) (idg : Ident × GlobDef F V) (id : Ident) :
    findSymbol (addGlobal ge idg) id = if id = idg.1 then some ge.genv_next else findSymbol ge id := by
  simp only [findSymbol, addGlobal, PTree.gsspec]

theorem findDef_addGlobal (ge : Genv F V) (idg : Ident × GlobDef F V) (b : Block) :
    findDef (addGlobal ge idg) b = if b = ge.genv_next then some idg.2 else findDef ge b := by
  simp only [findDef, addGlobal, PTree.gsspec]

@[simp] theorem findSymbol_emptyGenv (pub : List Ident) (id : Ident) :
    findSymbol (emptyGenv pub : Genv F V) id = none := by simp [findSymbol, emptyGenv]

@[simp] theorem findDef_emptyGenv (pub : List Ident) (b : Block) :
    findDef (emptyGenv pub : Genv F V) b = none := by simp [findDef, emptyGenv]

/-! ## Proof principles (`GLOBALENV_PRINCIPLES`) -/

section Principles
variable (P : Genv F V → Prop)

/-- `Genv.add_globals_preserves` -/
theorem addGlobals_preserves : ∀ (gl : List (Ident × GlobDef F V)) (ge : Genv F V),
    (∀ ge id g, P ge → (id, g) ∈ gl → P (addGlobal ge (id, g))) → P ge → P (addGlobals ge gl)
  | [], _, _, h => h
  | (id, g) :: gl, ge, hstep, h =>
    addGlobals_preserves gl _ (fun ge' id' g' hp hin => hstep ge' id' g' hp (List.mem_cons_of_mem _ hin))
      (hstep ge id g h (List.mem_cons_self ..))

/-- `Genv.add_globals_ensures` -/
theorem addGlobals_ensures (id : Ident) (g : GlobDef F V) :
    ∀ (gl : List (Ident × GlobDef F V)) (ge : Genv F V),
    (∀ ge id g, P ge → (id, g) ∈ gl → P (addGlobal ge (id, g))) →
    (∀ ge, P (addGlobal ge (id, g))) → (id, g) ∈ gl → P (addGlobals ge gl)
  | [], _, _, _, hin => absurd hin (List.not_mem_nil)
  | a :: gl, ge, hstep, hens, hin => by
    rw [addGlobals_cons]
    rcases List.mem_cons.mp hin with he | hin'
    · subst he
      exact addGlobals_preserves P gl _
        (fun ge' id' g' hp hi => hstep ge' id' g' hp (List.mem_cons_of_mem _ hi)) (hens ge)
    · exact addGlobals_ensures id g gl _
        (fun ge' id' g' hp hi => hstep ge' id' g' hp (List.mem_cons_of_mem _ hi)) hens hin'

/-- `Genv.add_globals_unique_preserves` -/
theorem addGlobals_unique_preserves (id : Ident) :
    ∀ (gl : List (Ident × GlobDef F V)) (ge : Genv F V),
    (∀ ge id1 g, P ge → (id1, g) ∈ gl → id1 ≠ id → P (addGlobal ge (id1, g))) →
    id ∉ gl.map Prod.fst → P ge → P (addGlobals ge gl)
  | [], _, _, _, h => h
  | (id1, g) :: gl, ge, hstep, hni, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at hni
    exact addGlobals_unique_preserves id gl _
      (fun ge' i g' hp hin hne => hstep ge' i g' hp (List.mem_cons_of_mem _ hin) hne) hni.2
      (hstep ge id1 g h (List.mem_cons_self ..) (Ne.symm hni.1))

/-- `Genv.add_globals_unique_ensures` -/
theorem addGlobals_unique_ensures (gl1 : List (Ident × GlobDef F V)) (id : Ident)
    (g : GlobDef F V) (gl2 : List (Ident × GlobDef F V)) (ge : Genv F V)
    (hstep : ∀ ge id1 g1, P ge → (id1, g1) ∈ gl2 → id1 ≠ id → P (addGlobal ge (id1, g1)))
    (hens : ∀ ge, P (addGlobal ge (id, g))) (hni : id ∉ gl2.map Prod.fst) :
    P (addGlobals ge (gl1 ++ (id, g) :: gl2)) := by
  rw [addGlobals_app, addGlobals_cons]
  exact addGlobals_unique_preserves P id gl2 _ hstep hni (hens _)

/-- `Genv.in_norepet_unique` -/
theorem in_norepet_unique (id : Ident) (g : GlobDef F V) :
    ∀ (gl : List (Ident × GlobDef F V)), (id, g) ∈ gl → (gl.map Prod.fst).Nodup →
    ∃ gl1 gl2, gl = gl1 ++ (id, g) :: gl2 ∧ id ∉ gl2.map Prod.fst
  | [], hin, _ => absurd hin List.not_mem_nil
  | (id1, g1) :: gl, hin, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hin with he | hin'
    · cases he
      exact ⟨[], gl, rfl, hnd.1⟩
    · obtain ⟨gl1, gl2, hx, hy⟩ := in_norepet_unique id g gl hin' hnd.2
      exact ⟨(id1, g1) :: gl1, gl2, by rw [hx]; rfl, hy⟩

/-- `Genv.add_globals_norepet_ensures` -/
theorem addGlobals_norepet_ensures (id : Ident) (g : GlobDef F V)
    (gl : List (Ident × GlobDef F V)) (ge : Genv F V)
    (hstep : ∀ ge id1 g1, P ge → (id1, g1) ∈ gl → id1 ≠ id → P (addGlobal ge (id1, g1)))
    (hens : ∀ ge, P (addGlobal ge (id, g))) (hin : (id, g) ∈ gl)
    (hnd : (gl.map Prod.fst).Nodup) : P (addGlobals ge gl) := by
  obtain ⟨gl1, gl2, rfl, hy⟩ := in_norepet_unique id g gl hin hnd
  exact addGlobals_unique_ensures P gl1 id g gl2 ge
    (fun ge' i g' hp hi hne => hstep ge' i g' hp (List.mem_append_right _ (List.mem_cons_of_mem _ hi)) hne)
    hens hy

end Principles

/-! ## `genv_next`, `genv_public` and the invariants -/

/-- `Genv.advance_next` -/
def advanceNext (gl : List (Ident × GlobDef F V)) (x : Positive) : Positive :=
  gl.foldl (fun n _ => n.succ) x

/-- `Genv.genv_next_add_globals` -/
theorem genv_next_addGlobals : ∀ (gl : List (Ident × GlobDef F V)) (ge : Genv F V),
    (addGlobals ge gl).genv_next = advanceNext gl ge.genv_next
  | [], _ => rfl
  | _ :: gl, ge => genv_next_addGlobals gl (addGlobal ge _)

/-- `Genv.genv_public_add_globals` -/
theorem genv_public_addGlobals : ∀ (gl : List (Ident × GlobDef F V)) (ge : Genv F V),
    (addGlobals ge gl).genv_public = ge.genv_public
  | [], _ => rfl
  | _ :: gl, ge => genv_public_addGlobals gl (addGlobal ge _)

/-- `Genv.globalenv_public` -/
theorem globalenv_public (pub : List Ident) (gl : List (Ident × GlobDef F V)) :
    (globalenv pub gl).genv_public = pub :=
  genv_public_addGlobals gl _

theorem defsBelow_emptyGenv (pub : List Ident) : DefsBelow (emptyGenv pub : Genv F V) := by
  intro b g h; simp at h

theorem defsBelow_addGlobal {ge : Genv F V} (idg : Ident × GlobDef F V) (h : DefsBelow ge) :
    DefsBelow (addGlobal ge idg) := by
  intro b g hb
  rw [findDef_addGlobal] at hb
  have hlt : b.toNat < ge.genv_next.toNat + 1 := by
    split at hb
    · next he => subst he; omega
    · have := (Positive.lt_iff _ _).1 (h b g hb); omega
  show b.toNat < (addGlobal ge idg).genv_next.toNat
  simpa [addGlobal] using hlt

theorem defsBelow_addGlobals {ge : Genv F V} (gl : List (Ident × GlobDef F V))
    (h : DefsBelow ge) : DefsBelow (addGlobals ge gl) :=
  addGlobals_preserves DefsBelow gl ge (fun _ _ _ hp _ => defsBelow_addGlobal _ hp) h

/-- `genv_defs_range` for the environment of a program. -/
theorem defsBelow_globalenv (pub : List Ident) (gl : List (Ident × GlobDef F V)) :
    DefsBelow (globalenv pub gl) :=
  defsBelow_addGlobals gl (defsBelow_emptyGenv pub)

/-- `genv_symb_range` for the environment of a program. -/
theorem symbBelow_globalenv (pub : List Ident) (gl : List (Ident × GlobDef F V)) :
    SymbBelow (globalenv pub gl) :=
  symbBelow_addGlobals gl (symbBelow_emptyGenv pub)

/-! ## Properties of the lookup functions -/

/-- `Genv.public_symbol_exists` -/
theorem publicSymbol_exists {ge : Genv F V} {id : Ident} (h : publicSymbol ge id = true) :
    ∃ b, findSymbol ge id = some b := by
  unfold publicSymbol at h
  split at h
  · cases h
  · next b hb => exact ⟨b, hb⟩

/-- `Genv.shift_symbol_address` -/
theorem shift_symbolAddress (ge : Genv F V) (id : Ident) (ofs delta : Integers.Ptrofs) :
    symbolAddress ge id (Integers.Ptrofs.add ofs delta) =
      Val.offsetPtr (symbolAddress ge id ofs) delta := by
  unfold symbolAddress Val.offsetPtr
  split <;> rfl

/-- `Genv.shift_symbol_address_64` (the port's target is 64-bit). -/
theorem shift_symbolAddress_64 (ge : Genv F V) (id : Ident) (ofs : Integers.Ptrofs)
    (n : Integers.Int64) :
    symbolAddress ge id (Integers.Ptrofs.add ofs (Integers.Ptrofs.of_int64 n)) =
      Val.addl (symbolAddress ge id ofs) (.Vlong n) := by
  unfold symbolAddress
  split <;> rfl

/-- `Genv.find_funct_inv` -/
theorem findFunct_inv {ge : Genv F V} {v : Val} {f : F} (h : findFunct ge v = some f) :
    ∃ b, v = .Vptr b Integers.Ptrofs.zero := by
  unfold findFunct at h
  split at h
  · next b ofs =>
    split at h
    · next he => exact ⟨b, by rw [(Integers.Ptrofs.eq_spec _ _).1 he]⟩
    · cases h
  · cases h

/-- `Genv.find_funct_find_funct_ptr` -/
theorem findFunct_findFunctPtr (ge : Genv F V) (b : Block) :
    findFunct ge (.Vptr b Integers.Ptrofs.zero) = findFunctPtr ge b := by
  simp only [findFunct, Integers.Ptrofs.eq_true, ite_true]

/-- `Genv.find_funct_ptr_iff` -/
theorem findFunctPtr_iff (ge : Genv F V) (b : Block) (f : F) :
    findFunctPtr ge b = some f ↔ findDef ge b = some (.Gfun f) := by
  unfold findFunctPtr
  split <;> simp_all

/-- `Genv.find_var_info_iff` -/
theorem findVarInfo_iff (ge : Genv F V) (b : Block) (v : GlobVar V) :
    findVarInfo ge b = some v ↔ findDef ge b = some (.Gvar v) := by
  unfold findVarInfo
  split <;> simp_all

/-- `Genv.block_is_volatile_below` -/
theorem blockIsVolatile_below {ge : Genv F V} (hd : DefsBelow ge) {b : Block}
    (h : blockIsVolatile ge b = true) : b < ge.genv_next := by
  unfold blockIsVolatile at h
  split at h
  · next gv hgv => exact hd b _ ((findVarInfo_iff ge b gv).1 hgv)
  · cases h

/-- `Genv.global_addresses_distinct` -/
theorem global_addresses_distinct {ge : Genv F V} (hinj : SymbInjective ge) {id1 id2 : Ident}
    {b1 b2 : Block} (hne : id1 ≠ id2) (h1 : findSymbol ge id1 = some b1)
    (h2 : findSymbol ge id2 = some b2) : b1 ≠ b2 := by
  intro he; subst he; exact hne (hinj _ _ _ h1 h2)

/-- `Genv.invert_find_symbol` -/
theorem invert_findSymbol {ge : Genv F V} {id : Ident} {b : Block}
    (h : invertSymbol ge b = some id) : findSymbol ge id = some b := by
  unfold invertSymbol at h
  cases hf : ge.genv_symb.elements.find? (fun p => p.2 = b) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    obtain ⟨i, v⟩ := p
    simp only at h hp
    subst h hp
    exact PTree.elements_complete _ _ _ hmem

/-- `Genv.find_invert_symbol` (needs `genv_vars_inj`). -/
theorem find_invertSymbol {ge : Genv F V} (hinj : SymbInjective ge) {id : Ident} {b : Block}
    (h : findSymbol ge id = some b) : invertSymbol ge b = some id := by
  have hmem := PTree.elements_correct _ _ _ h
  unfold invertSymbol
  cases hf : ge.genv_symb.elements.find? (fun p => p.2 = b) with
  | none =>
    have := List.find?_eq_none.1 hf _ hmem
    simp at this
  | some p =>
    have hinv : invertSymbol ge b = some p.1 := by unfold invertSymbol; rw [hf]; rfl
    have := invert_findSymbol hinv
    simp only [Option.map_some, Option.some.injEq]
    exact hinj _ _ _ this h

/-! ## `globalenv` and `prog_defmap` -/

/-- `Genv.find_symbol_exists` -/
theorem findSymbol_exists {pub : List Ident} {gl : List (Ident × GlobDef F V)} {id : Ident}
    {g : GlobDef F V} (hin : (id, g) ∈ gl) : ∃ b, findSymbol (globalenv pub gl) id = some b := by
  unfold globalenv
  refine addGlobals_ensures (fun ge => ∃ b, findSymbol ge id = some b) id g gl _ ?_ ?_ hin
  · intro ge id' g' ⟨b, hb⟩ _
    rw [findSymbol_addGlobal]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨b, hb⟩
  · intro ge; rw [findSymbol_addGlobal, if_pos rfl]; exact ⟨_, rfl⟩

/-- `Genv.find_symbol_inversion` -/
theorem findSymbol_inversion {pub : List Ident} {gl : List (Ident × GlobDef F V)} {x : Ident}
    {b : Block} (h : findSymbol (globalenv pub gl) x = some b) : x ∈ defsNames gl := by
  revert h b
  unfold globalenv
  refine addGlobals_preserves (fun ge => ∀ {b}, findSymbol ge x = some b → x ∈ defsNames gl)
    gl _ ?_ ?_
  · intro ge id g hp hin b hb
    rw [findSymbol_addGlobal] at hb
    split at hb
    · next he => subst he; exact List.mem_map.2 ⟨_, hin, rfl⟩
    · exact hp hb
  · intro b hb; simp at hb

/-- `Genv.find_def_inversion` -/
theorem findDef_inversion {pub : List Ident} {gl : List (Ident × GlobDef F V)} {b : Block}
    {g : GlobDef F V} (h : findDef (globalenv pub gl) b = some g) : ∃ id, (id, g) ∈ gl := by
  revert h g
  unfold globalenv
  refine addGlobals_preserves (fun ge => ∀ {g}, findDef ge b = some g → ∃ id, (id, g) ∈ gl)
    gl _ ?_ ?_
  · intro ge id g' hp hin g hb
    rw [findDef_addGlobal] at hb
    split at hb
    · cases hb; exact ⟨id, hin⟩
    · exact hp hb
  · intro g hb; simp at hb

/-- `Genv.find_funct_ptr_inversion` -/
theorem findFunctPtr_inversion {pub : List Ident} {gl : List (Ident × GlobDef F V)} {b : Block}
    {f : F} (h : findFunctPtr (globalenv pub gl) b = some f) : ∃ id, (id, .Gfun f) ∈ gl :=
  findDef_inversion ((findFunctPtr_iff _ _ _).1 h)

/-- `Genv.find_funct_inversion` -/
theorem findFunct_inversion {pub : List Ident} {gl : List (Ident × GlobDef F V)} {v : Val}
    {f : F} (h : findFunct (globalenv pub gl) v = some f) : ∃ id, (id, .Gfun f) ∈ gl := by
  obtain ⟨b, rfl⟩ := findFunct_inv h
  rw [findFunct_findFunctPtr] at h
  exact findFunctPtr_inversion h

/-- `Genv.find_funct_ptr_prop` -/
theorem findFunctPtr_prop (P : F → Prop) {pub : List Ident} {gl : List (Ident × GlobDef F V)}
    {b : Block} {f : F} (hP : ∀ id f, (id, .Gfun f) ∈ gl → P f)
    (h : findFunctPtr (globalenv pub gl) b = some f) : P f := by
  obtain ⟨id, hin⟩ := findFunctPtr_inversion h
  exact hP id f hin

/-- `Genv.find_funct_prop` -/
theorem findFunct_prop (P : F → Prop) {pub : List Ident} {gl : List (Ident × GlobDef F V)}
    {v : Val} {f : F} (hP : ∀ id f, (id, .Gfun f) ∈ gl → P f)
    (h : findFunct (globalenv pub gl) v = some f) : P f := by
  obtain ⟨id, hin⟩ := findFunct_inversion h
  exact hP id f hin

/-- `Genv.find_def_symbol` -/
theorem find_def_symbol (pub : List Ident) (gl : List (Ident × GlobDef F V)) (id : Ident)
    (g : GlobDef F V) :
    (defmap gl).get id = some g ↔
      ∃ b, findSymbol (globalenv pub gl) id = some b ∧ findDef (globalenv pub gl) b = some g := by
  let P : PTree (GlobDef F V) → Genv F V → Prop := fun m ge =>
    (m.get id = some g ↔ ∃ b, findSymbol ge id = some b ∧ findDef ge b = some g)
  have hrec : ∀ (l : List (Ident × GlobDef F V)) m (ge : Genv F V), SymbBelow ge → P m ge →
      P (l.foldl (fun m idg => m.set idg.1 idg.2) m) (addGlobals ge l) := by
    intro l
    induction l with
    | nil => intro m ge _ h; exact h
    | cons a l ih =>
      intro m ge hb h
      simp only [P] at h
      obtain ⟨id1, g1⟩ := a
      refine ih _ _ (symbBelow_addGlobal _ hb) ?_
      simp only [P, PTree.gsspec, findSymbol_addGlobal, findDef_addGlobal]
      by_cases hid : id = id1
      · subst hid
        simp only [if_true]
        constructor
        · intro he; cases he; exact ⟨_, rfl, by simp⟩
        · rintro ⟨b, hb1, hb2⟩; cases hb1; simpa using hb2
      · simp only [hid, if_false]
        rw [h]
        constructor
        · rintro ⟨b, hb1, hb2⟩
          have hlt := hb id b hb1
          have hne : b ≠ ge.genv_next := fun he => by
            subst he; exact Nat.lt_irrefl _ ((Positive.lt_iff _ _).1 hlt)
          exact ⟨b, hb1, by simp only [hne, if_false]; exact hb2⟩
        · rintro ⟨b, hb1, hb2⟩
          have hlt := hb id b hb1
          have hne : b ≠ ge.genv_next := fun he => by
            subst he; exact Nat.lt_irrefl _ ((Positive.lt_iff _ _).1 hlt)
          simp only [hne, if_false] at hb2
          exact ⟨b, hb1, hb2⟩
  refine hrec gl PTree.empty (emptyGenv pub) (symbBelow_emptyGenv pub) ?_
  simp [P]

end Genv
end CC
