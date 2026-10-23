/-
  Global environments of transformed programs — port of the `MATCH_PROGRAMS`,
  `TRANSFORM_PARTIAL` and `TRANSFORM_TOTAL` sections of `common/Globalenvs.v`,
  together with the `match_program` relation of `common/Linking.v` they are
  stated over.

  Two programs *match* when they have the same public symbols and `main`, and
  their definition lists agree name by name, with related functions
  (`Rf`) and related variable information (`Rv`); initialisers and the
  read-only/volatile flags must be equal.  For matching programs the symbol
  tables, the symbol environments (`Senv`) and the initial memories coincide,
  and function lookups return related functions.  `transform_program` and
  `transform_partial_program(2)` produce matching programs, which gives
  CompCert's `find_funct_ptr_transf`, `find_symbol_transf`, `init_mem_transf`,
  `senv_transf`, … .

  Deviation: CompCert's `match_program_gen` passes a linking context (the whole
  source program) to the function relation, and requires `linkorder` between
  the context and each compilation unit.  Separate compilation is out of scope
  here, so the relations are context-free; CompCert's theorems are recovered by
  instantiating `Rf` with the context fixed.
-/
import CCLib.common.ASTTheory
import CCLib.common.GlobalenvsInitMem
import CCLib.common.Events
import CCLib.cfrontend.Clight

namespace CC

/-! ## `match_program` -/

namespace Genv

variable {F1 F2 V1 V2 : Type} {Rf : F1 → F2 → Prop} {Rv : V1 → V2 → Prop}

/-- `Linking.match_globvar` -/
structure MatchGlobvar (Rv : V1 → V2 → Prop) (g1 : GlobVar V1) (g2 : GlobVar V2) : Prop where
  info : Rv g1.gvar_info g2.gvar_info
  init : g1.gvar_init = g2.gvar_init
  readonly : g1.gvar_readonly = g2.gvar_readonly
  volatile : g1.gvar_volatile = g2.gvar_volatile

/-- `Linking.match_globdef` (context-free) -/
inductive MatchGlobdef (Rf : F1 → F2 → Prop) (Rv : V1 → V2 → Prop) :
    GlobDef F1 V1 → GlobDef F2 V2 → Prop where
  | gfun {f1 f2} : Rf f1 f2 → MatchGlobdef Rf Rv (.Gfun f1) (.Gfun f2)
  | gvar {v1 v2} : MatchGlobvar Rv v1 v2 → MatchGlobdef Rf Rv (.Gvar v1) (.Gvar v2)

/-- `Linking.match_ident_globdef`, lifted to definition lists (`list_forall2`):
    the same names in the same order, with matching definitions. -/
inductive MatchDefs (Rf : F1 → F2 → Prop) (Rv : V1 → V2 → Prop) :
    List (Ident × GlobDef F1 V1) → List (Ident × GlobDef F2 V2) → Prop where
  | nil : MatchDefs Rf Rv [] []
  | cons {id g1 g2 l1 l2} : MatchGlobdef Rf Rv g1 g2 → MatchDefs Rf Rv l1 l2 →
      MatchDefs Rf Rv ((id, g1) :: l1) ((id, g2) :: l2)

theorem MatchDefs.imp {Rf' : F1 → F2 → Prop} {Rv' : V1 → V2 → Prop}
    (hf : ∀ f1 f2, Rf f1 f2 → Rf' f1 f2) (hv : ∀ v1 v2, Rv v1 v2 → Rv' v1 v2) :
    ∀ {l1 l2}, MatchDefs Rf Rv l1 l2 → MatchDefs Rf' Rv' l1 l2 := by
  intro l1 l2 h
  induction h with
  | nil => exact .nil
  | cons hm _ ih =>
    refine .cons ?_ ih
    cases hm with
    | gfun hr => exact .gfun (hf _ _ hr)
    | gvar hr => exact .gvar ⟨hv _ _ hr.info, hr.init, hr.readonly, hr.volatile⟩

end Genv

/-- `Linking.match_program` (context-free, see the header). -/
structure MatchProgram {F1 F2 V1 V2 : Type} (Rf : F1 → F2 → Prop) (Rv : V1 → V2 → Prop)
    (p1 : ASTProgram F1 V1) (p2 : ASTProgram F2 V2) : Prop where
  defs : Genv.MatchDefs Rf Rv p1.prog_defs p2.prog_defs
  main_eq : p2.prog_main = p1.prog_main
  public_eq : p2.prog_public = p1.prog_public

namespace ASTProgram
variable {F V : Type}

/-- `Genv.globalenv` of a generic program. -/
def globalenv (p : ASTProgram F V) : Genv F V := Genv.globalenv p.prog_public p.prog_defs

/-- `Genv.init_mem` of a generic program. -/
def initMem (p : ASTProgram F V) : Option Mem := Genv.initMem p.prog_public p.prog_defs

/-- The generic `prog_defmap` is the one `GlobalenvsTheory` relates to
    `globalenv`. -/
theorem defmap_eq (p : ASTProgram F V) : p.defmap = Genv.defmap p.prog_defs := rfl

end ASTProgram

namespace Genv

variable {F1 F2 V1 V2 : Type} {Rf : F1 → F2 → Prop} {Rv : V1 → V2 → Prop}

/-! ## Matching environments -/

/-- Two environments with the same symbol table whose definitions are related
    block by block. -/
structure GenvMatch (Rf : F1 → F2 → Prop) (Rv : V1 → V2 → Prop)
    (ge1 : Genv F1 V1) (ge2 : Genv F2 V2) : Prop where
  public_eq : ge2.genv_public = ge1.genv_public
  symb : ge2.genv_symb = ge1.genv_symb
  next : ge2.genv_next = ge1.genv_next
  defs12 : ∀ b g1, ge1.genv_defs.get b = some g1 →
    ∃ g2, ge2.genv_defs.get b = some g2 ∧ MatchGlobdef Rf Rv g1 g2
  defs21 : ∀ b g2, ge2.genv_defs.get b = some g2 →
    ∃ g1, ge1.genv_defs.get b = some g1 ∧ MatchGlobdef Rf Rv g1 g2

theorem genvMatch_empty (pub : List Ident) :
    GenvMatch Rf Rv (emptyGenv pub : Genv F1 V1) (emptyGenv pub : Genv F2 V2) :=
  ⟨rfl, rfl, rfl, fun b g h => by simp [emptyGenv] at h, fun b g h => by simp [emptyGenv] at h⟩

theorem genvMatch_addGlobal {ge1 : Genv F1 V1} {ge2 : Genv F2 V2} (h : GenvMatch Rf Rv ge1 ge2)
    {id : Ident} {g1 g2} (hg : MatchGlobdef Rf Rv g1 g2) :
    GenvMatch Rf Rv (addGlobal ge1 (id, g1)) (addGlobal ge2 (id, g2)) := by
  refine ⟨h.public_eq, ?_, ?_, ?_, ?_⟩
  · simp only [addGlobal, h.symb, h.next]
  · simp only [addGlobal, h.next]
  · intro b g h1
    simp only [addGlobal, h.next] at h1 ⊢
    by_cases hb : ge1.genv_next = b
    · subst hb; rw [PTree.gss] at h1 ⊢; cases h1; exact ⟨_, rfl, hg⟩
    · rw [PTree.gso _ _ _ _ hb] at h1 ⊢; exact h.defs12 b g h1
  · intro b g h2
    simp only [addGlobal, h.next] at h2 ⊢
    by_cases hb : ge1.genv_next = b
    · subst hb; rw [PTree.gss] at h2 ⊢; cases h2; exact ⟨_, rfl, hg⟩
    · rw [PTree.gso _ _ _ _ hb] at h2 ⊢; exact h.defs21 b g h2

theorem genvMatch_addGlobals {l1 : List (Ident × GlobDef F1 V1)} {l2 : List (Ident × GlobDef F2 V2)}
    (hl : MatchDefs Rf Rv l1 l2) :
    ∀ {ge1 : Genv F1 V1} {ge2 : Genv F2 V2}, GenvMatch Rf Rv ge1 ge2 →
      GenvMatch Rf Rv (addGlobals ge1 l1) (addGlobals ge2 l2) := by
  induction hl with
  | nil => intro _ _ h; exact h
  | cons hg _ ih => intro ge1 ge2 h; exact ih (genvMatch_addGlobal h hg)

/-- The environments of matching definition lists match. -/
theorem genvMatch_globalenv (pub : List Ident) {l1 : List (Ident × GlobDef F1 V1)}
    {l2 : List (Ident × GlobDef F2 V2)} (hl : MatchDefs Rf Rv l1 l2) :
    GenvMatch Rf Rv (globalenv pub l1) (globalenv pub l2) :=
  genvMatch_addGlobals hl (genvMatch_empty pub)

section Lookups
variable {ge1 : Genv F1 V1} {ge2 : Genv F2 V2} (h : GenvMatch Rf Rv ge1 ge2)
include h

/-- `Genv.find_symbol_match` -/
theorem find_symbol_match (id : Ident) : findSymbol ge2 id = findSymbol ge1 id := by
  simp [findSymbol, h.symb]

/-- `Genv.public_symbol_match` -/
theorem public_symbol_match (id : Ident) : publicSymbol ge2 id = publicSymbol ge1 id := by
  simp [publicSymbol, find_symbol_match h, h.public_eq]

theorem invert_symbol_match (b : Block) : invertSymbol ge2 b = invertSymbol ge1 b := by
  simp [invertSymbol, h.symb]

/-- `Genv.find_def_match_2` -/
theorem find_def_match (b : Block) {g1} (hb : findDef ge1 b = some g1) :
    ∃ g2, findDef ge2 b = some g2 ∧ MatchGlobdef Rf Rv g1 g2 := h.defs12 b g1 hb

/-- `Genv.find_funct_ptr_match` -/
theorem find_funct_ptr_match {b : Block} {f1} (hb : findFunctPtr ge1 b = some f1) :
    ∃ f2, findFunctPtr ge2 b = some f2 ∧ Rf f1 f2 := by
  unfold findFunctPtr at hb ⊢
  split at hb
  · rename_i f heq
    cases hb
    obtain ⟨g2, hg2, hm⟩ := h.defs12 b _ heq
    cases hm with
    | gfun hr => exact ⟨_, by simp [findDef] at hg2 ⊢; rw [hg2], hr⟩
  · cases hb

/-- The converse of `find_funct_ptr_match` (CompCert gets it from
    `find_funct_ptr_match` and `find_def_match_2` in the other direction). -/
theorem find_funct_ptr_match_inv {b : Block} {f2} (hb : findFunctPtr ge2 b = some f2) :
    ∃ f1, findFunctPtr ge1 b = some f1 ∧ Rf f1 f2 := by
  unfold findFunctPtr at hb ⊢
  split at hb
  · rename_i f heq
    cases hb
    obtain ⟨g1, hg1, hm⟩ := h.defs21 b _ heq
    cases hm with
    | gfun hr => exact ⟨_, by simp [findDef] at hg1 ⊢; rw [hg1], hr⟩
  · cases hb

/-- `Genv.find_funct_match` -/
theorem find_funct_match {v : Val} {f1} (hv : findFunct ge1 v = some f1) :
    ∃ f2, findFunct ge2 v = some f2 ∧ Rf f1 f2 := by
  unfold findFunct at hv ⊢
  split at hv
  · split at hv
    · rename_i hofs; rw [if_pos hofs]; exact find_funct_ptr_match h hv
    · cases hv
  · cases hv

/-- `Genv.find_var_info_match` -/
theorem find_var_info_match {b : Block} {v1} (hb : findVarInfo ge1 b = some v1) :
    ∃ v2, findVarInfo ge2 b = some v2 ∧ MatchGlobvar Rv v1 v2 := by
  unfold findVarInfo at hb ⊢
  split at hb
  · rename_i v heq
    cases hb
    obtain ⟨g2, hg2, hm⟩ := h.defs12 b _ heq
    cases hm with
    | gvar hr => exact ⟨_, by simp [findDef] at hg2 ⊢; rw [hg2], hr⟩
  · cases hb

theorem find_var_info_match_none {b : Block} (hb : findVarInfo ge1 b = none) :
    findVarInfo ge2 b = none := by
  cases h2 : findVarInfo ge2 b with
  | none => rfl
  | some v2 =>
    exfalso
    unfold findVarInfo at h2 hb
    split at h2
    · rename_i v heq
      obtain ⟨g1, hg1, hm⟩ := h.defs21 b _ heq
      cases hm with
      | gvar _ =>
        have hd : findDef ge1 b = some (.Gvar _) := hg1
        rw [hd] at hb; cases hb
    · cases h2

/-- `Genv.block_is_volatile_match` -/
theorem block_is_volatile_match (b : Block) : blockIsVolatile ge2 b = blockIsVolatile ge1 b := by
  unfold blockIsVolatile
  cases h1 : findVarInfo ge1 b with
  | none => rw [find_var_info_match_none h h1]
  | some v1 =>
    obtain ⟨v2, h2, hm⟩ := find_var_info_match h h1
    rw [h2]; exact hm.volatile.symm

/-- `Genv.senv_match`: matching environments have the same symbol environment. -/
theorem senv_match : toSenv ge2 = toSenv ge1 := by
  simp only [toSenv]
  congr 1
  · funext id; exact find_symbol_match h id
  · funext id; exact public_symbol_match h id
  · funext b; exact invert_symbol_match h b
  · funext b; exact block_is_volatile_match h b

end Lookups

/-! ## Initial memories -/

theorem storeInitData_match {ge1 : Genv F1 V1} {ge2 : Genv F2 V2}
    (hs : ∀ id, findSymbol ge2 id = findSymbol ge1 id) (m : Mem) (b : Block) (p : Z)
    (i : InitData) : storeInitData ge2 m b p i = storeInitData ge1 m b p i := by
  cases i <;> simp [storeInitData, hs]

theorem storeInitDataList_match {ge1 : Genv F1 V1} {ge2 : Genv F2 V2}
    (hs : ∀ id, findSymbol ge2 id = findSymbol ge1 id) (il : List InitData) :
    ∀ (m : Mem) (b : Block) (p : Z),
      storeInitDataList ge2 m b p il = storeInitDataList ge1 m b p il := by
  induction il with
  | nil => intro m b p; rfl
  | cons i il ih =>
    intro m b p
    simp only [storeInitDataList, storeInitData_match hs]
    split <;> simp [ih]

theorem allocGlobal_match {ge1 : Genv F1 V1} {ge2 : Genv F2 V2}
    (hs : ∀ id, findSymbol ge2 id = findSymbol ge1 id) (m : Mem) {id1 id2 : Ident}
    {g1 : GlobDef F1 V1} {g2 : GlobDef F2 V2} (hg : MatchGlobdef Rf Rv g1 g2) :
    allocGlobal ge2 m (id2, g2) = allocGlobal ge1 m (id1, g1) := by
  cases hg with
  | gfun _ => rfl
  | gvar hv =>
    simp only [allocGlobal, permGlobvar, hv.init, hv.readonly, hv.volatile,
      storeInitDataList_match hs]

theorem allocGlobals_match {ge1 : Genv F1 V1} {ge2 : Genv F2 V2}
    (hs : ∀ id, findSymbol ge2 id = findSymbol ge1 id)
    {l1 : List (Ident × GlobDef F1 V1)} {l2 : List (Ident × GlobDef F2 V2)}
    (hl : MatchDefs Rf Rv l1 l2) :
    ∀ m, allocGlobals ge2 m l2 = allocGlobals ge1 m l1 := by
  induction hl with
  | nil => intro m; rfl
  | cons hg _ ih =>
    intro m
    rw [allocGlobals, allocGlobals, allocGlobal_match hs m hg]
    cases allocGlobal ge1 m _ <;> simp only [ih]

end Genv

/-! ## Matching programs -/

namespace MatchProgram

variable {F1 F2 V1 V2 : Type} {Rf : F1 → F2 → Prop} {Rv : V1 → V2 → Prop}
  {p1 : ASTProgram F1 V1} {p2 : ASTProgram F2 V2} (h : MatchProgram Rf Rv p1 p2)
include h

theorem genvMatch : Genv.GenvMatch Rf Rv p1.globalenv p2.globalenv := by
  unfold ASTProgram.globalenv; rw [h.public_eq]; exact Genv.genvMatch_globalenv _ h.defs

/-- `Genv.find_symbol_match` -/
theorem find_symbol (id : Ident) :
    Genv.findSymbol p2.globalenv id = Genv.findSymbol p1.globalenv id :=
  Genv.find_symbol_match h.genvMatch id

/-- `Genv.senv_match` -/
theorem senv : Genv.toSenv p2.globalenv = Genv.toSenv p1.globalenv :=
  Genv.senv_match h.genvMatch

/-- `Genv.find_funct_ptr_match` -/
theorem find_funct_ptr {b f1} (hb : Genv.findFunctPtr p1.globalenv b = some f1) :
    ∃ f2, Genv.findFunctPtr p2.globalenv b = some f2 ∧ Rf f1 f2 :=
  Genv.find_funct_ptr_match h.genvMatch hb

/-- `Genv.find_funct_match` -/
theorem find_funct {v f1} (hv : Genv.findFunct p1.globalenv v = some f1) :
    ∃ f2, Genv.findFunct p2.globalenv v = some f2 ∧ Rf f1 f2 :=
  Genv.find_funct_match h.genvMatch hv

/-- `Genv.find_var_info_match` -/
theorem find_var_info {b v1} (hb : Genv.findVarInfo p1.globalenv b = some v1) :
    ∃ v2, Genv.findVarInfo p2.globalenv b = some v2 ∧ Genv.MatchGlobvar Rv v1 v2 :=
  Genv.find_var_info_match h.genvMatch hb

/-- `Genv.init_mem_match` (as an equality: the two programs have the same
    initial memory, or both have none). -/
theorem init_mem : p2.initMem = p1.initMem := by
  unfold ASTProgram.initMem Genv.initMem
  rw [← ASTProgram.globalenv, ← ASTProgram.globalenv]
  exact Genv.allocGlobals_match (find_symbol h) h.defs _

end MatchProgram

/-! ## Program transformations produce matching programs -/

section Transform
variable {A B V W : Type}

/-- `match_transform_program` -/
theorem match_transform_program (transf : A → B) (p : ASTProgram A V) :
    MatchProgram (fun f tf => tf = transf f) Eq p (transformProgram transf p) := by
  refine ⟨?_, rfl, rfl⟩
  simp only [transformProgram]
  generalize p.prog_defs = l
  induction l with
  | nil => exact .nil
  | cons idg l ih =>
    obtain ⟨id, g⟩ := idg
    cases g with
    | Gfun f => exact .cons (.gfun rfl) ih
    | Gvar v => exact .cons (.gvar ⟨rfl, rfl, rfl, rfl⟩) ih

theorem matchDefs_transfGlobdefs {transfFun : Ident → A → Res B}
    {transfVar : Ident → V → Res W} :
    ∀ (l : List (Ident × GlobDef A V)) gl', transfGlobdefs transfFun transfVar l = .OK gl' →
      Genv.MatchDefs (fun f tf => ∃ id, transfFun id f = .OK tf)
        (fun v tv => ∃ id, transfVar id v = .OK tv) l gl' := by
  intro l
  induction l with
  | nil => intro gl' h; simp [transfGlobdefs] at h; subst h; exact .nil
  | cons idg l ih =>
    intro gl' h
    obtain ⟨id, g⟩ := idg
    cases g with
    | Gfun f =>
      simp only [transfGlobdefs] at h
      split at h
      · cases h
      · rename_i tf htf
        split at h
        · rename_i tl htl; cases h
          exact .cons (.gfun ⟨id, htf⟩) (ih _ htl)
        · cases h
    | Gvar v =>
      simp only [transfGlobdefs] at h
      split at h
      · cases h
      · rename_i tv htv
        split at h
        · rename_i tl htl; cases h
          unfold transfGlobvar at htv
          split at htv
          · rename_i info hinfo; cases htv
            exact .cons (.gvar ⟨⟨id, hinfo⟩, rfl, rfl, rfl⟩) (ih _ htl)
          · cases htv
        · cases h

/-- `match_transform_partial_program2` -/
theorem match_transform_partial_program2 {transfFun : Ident → A → Res B}
    {transfVar : Ident → V → Res W} {p : ASTProgram A V} {tp : ASTProgram B W}
    (htr : transformPartialProgram2 transfFun transfVar p = .OK tp) :
    MatchProgram (fun f tf => ∃ id, transfFun id f = .OK tf)
      (fun v tv => ∃ id, transfVar id v = .OK tv) p tp := by
  unfold transformPartialProgram2 at htr
  split at htr
  · rename_i gl' hgl
    cases htr
    exact ⟨matchDefs_transfGlobdefs _ _ hgl, rfl, rfl⟩
  · cases htr

/-- `match_transform_partial_program` -/
theorem match_transform_partial_program {transfFun : A → Res B} {p : ASTProgram A V}
    {tp : ASTProgram B V} (htr : transformPartialProgram transfFun p = .OK tp) :
    MatchProgram (fun f tf => transfFun f = .OK tf) Eq p tp := by
  have h := match_transform_partial_program2 htr
  refine ⟨h.defs.imp ?_ ?_, h.main_eq, h.public_eq⟩
  · intro f tf ⟨_, hf⟩; exact hf
  · intro v tv ⟨_, hv⟩; cases hv; rfl

/-! ### CompCert's `TRANSFORM_TOTAL` corollaries -/

/-- `Genv.find_funct_ptr_transf` -/
theorem find_funct_ptr_transf (transf : A → B) {p : ASTProgram A V} {b f}
    (h : Genv.findFunctPtr p.globalenv b = some f) :
    Genv.findFunctPtr (transformProgram transf p).globalenv b = some (transf f) := by
  obtain ⟨f2, h2, rfl⟩ := (match_transform_program transf p).find_funct_ptr h
  exact h2

/-- `Genv.find_funct_transf` -/
theorem find_funct_transf (transf : A → B) {p : ASTProgram A V} {v f}
    (h : Genv.findFunct p.globalenv v = some f) :
    Genv.findFunct (transformProgram transf p).globalenv v = some (transf f) := by
  obtain ⟨f2, h2, rfl⟩ := (match_transform_program transf p).find_funct h
  exact h2

/-- `Genv.find_symbol_transf` -/
theorem find_symbol_transf (transf : A → B) (p : ASTProgram A V) (id : Ident) :
    Genv.findSymbol (transformProgram transf p).globalenv id = Genv.findSymbol p.globalenv id :=
  (match_transform_program transf p).find_symbol id

/-- `Genv.senv_transf` -/
theorem senv_transf (transf : A → B) (p : ASTProgram A V) :
    Genv.toSenv (transformProgram transf p).globalenv = Genv.toSenv p.globalenv :=
  (match_transform_program transf p).senv

/-- `Genv.init_mem_transf` -/
theorem init_mem_transf (transf : A → B) (p : ASTProgram A V) :
    (transformProgram transf p).initMem = p.initMem :=
  (match_transform_program transf p).init_mem

/-! ### CompCert's `TRANSFORM_PARTIAL` corollaries -/

/-- `Genv.find_funct_ptr_transf_partial` -/
theorem find_funct_ptr_transf_partial {transfFun : A → Res B} {p : ASTProgram A V}
    {tp : ASTProgram B V} (htr : transformPartialProgram transfFun p = .OK tp) {b f}
    (h : Genv.findFunctPtr p.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tp.globalenv b = some tf ∧ transfFun f = .OK tf :=
  (match_transform_partial_program htr).find_funct_ptr h

/-- `Genv.find_funct_transf_partial` -/
theorem find_funct_transf_partial {transfFun : A → Res B} {p : ASTProgram A V}
    {tp : ASTProgram B V} (htr : transformPartialProgram transfFun p = .OK tp) {v f}
    (h : Genv.findFunct p.globalenv v = some f) :
    ∃ tf, Genv.findFunct tp.globalenv v = some tf ∧ transfFun f = .OK tf :=
  (match_transform_partial_program htr).find_funct h

/-- `Genv.find_symbol_transf_partial` -/
theorem find_symbol_transf_partial {transfFun : A → Res B} {p : ASTProgram A V}
    {tp : ASTProgram B V} (htr : transformPartialProgram transfFun p = .OK tp) (id : Ident) :
    Genv.findSymbol tp.globalenv id = Genv.findSymbol p.globalenv id :=
  (match_transform_partial_program htr).find_symbol id

/-- `Genv.senv_transf_partial` -/
theorem senv_transf_partial {transfFun : A → Res B} {p : ASTProgram A V}
    {tp : ASTProgram B V} (htr : transformPartialProgram transfFun p = .OK tp) :
    Genv.toSenv tp.globalenv = Genv.toSenv p.globalenv :=
  (match_transform_partial_program htr).senv

/-- `Genv.init_mem_transf_partial` -/
theorem init_mem_transf_partial {transfFun : A → Res B} {p : ASTProgram A V}
    {tp : ASTProgram B V} (htr : transformPartialProgram transfFun p = .OK tp) :
    tp.initMem = p.initMem :=
  (match_transform_partial_program htr).init_mem

end Transform

/-! ## Clight programs as generic programs -/

/-- A Clight program as a generic `AST.program` (forgetting its composite
    definitions, which the global environment does not use). -/
def Program.toAST (p : Program) : ASTProgram FunDef Ty :=
  ⟨p.prog_defs, p.prog_public, p.prog_main⟩

theorem Program.globalenv_toAST (p : Program) :
    p.globalenv.genv_genv = p.toAST.globalenv := rfl

theorem Program.initMem_toAST (p : Program) : p.initMem = p.toAST.initMem := rfl

end CC
