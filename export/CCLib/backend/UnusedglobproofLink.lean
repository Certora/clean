/-
  Correctness of the elimination of unreferenced static definitions — port of
  `backend/Unusedglobproof.v`, last part: the semantic preservation theorem
  for the relational specification `match_prog`
  (`transf_program_correct_match`, Rocq's `transf_program_correct`) and the
  commutation of `match_prog` with linking (`link_def_either`,
  `used_not_defined_2`, `link_valid_used_set`, `link_match_program`,
  `TransfUnusedglobLink`).

  Differences from Rocq: used sets are lists (`IS`), so the union of two used
  sets is list concatenation.
-/
import CCLib.backend.UnusedglobproofMain
import CCLib.common.LinkingFundef

namespace CC
namespace Unusedglob

open Linking Linker Smallstep

/-- `Unusedglobproof.transf_program_correct`, for any pair of programs related by
`match_prog`. -/
theorem transf_program_correct_match (p tp : RTL.Program) (h : MatchProg p tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg)) :
    ForwardSimulation (RTL.semantics p) (RTL.semantics tp) := by
  obtain ⟨used, USED, TRANSF⟩ := h
  exact transf_program_correct_1 TRANSF USED hext hasm

/-! ## Commutation with linking -/

theorem IS.mem_append (x : Ident) (u1 u2 : IS) :
    IS.mem x (u1 ++ u2) = (IS.mem x u1 || IS.mem x u2) := by
  simp [IS.mem]

theorem linkVarinit_either {i1 i2 i : List InitData} (h : linkVarinit i1 i2 = some i) :
    i = i1 ∨ i = i2 := by
  unfold linkVarinit at h
  split at h <;> (try split at h) <;> simp_all

/-- `Unusedglobproof.link_def_either` -/
theorem link_def_either {gd1 gd2 gd : GlobDef RTL.Fundef Unit} (h : link gd1 gd2 = some gd) :
    gd = gd1 ∨ gd = gd2 := by
  change linkDef gd1 gd2 = some gd at h
  cases gd1 <;> cases gd2 <;> simp only [linkDef, Option.map_eq_some_iff] at h
  · obtain ⟨f, hf, rfl⟩ := h
    rcases link_astfundef_either hf with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
  · cases h
  · cases h
  · obtain ⟨v, hv, rfl⟩ := h
    rename_i v1 v2
    change linkVardef v1 v2 = some v at hv
    obtain ⟨i1, init1, ro1, vo1⟩ := v1
    obtain ⟨i2, init2, ro2, vo2⟩ := v2
    unfold linkVardef at hv
    simp only at hv
    split at hv
    · cases hv
    · split at hv
      · cases hv
      · rename_i init hinit
        split at hv
        · rename_i hc
          cases hv
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          change linkVarinit init1 init2 = some init at hinit
          rcases linkVarinit_either hinit with rfl | rfl
          · exact .inl rfl
          · exact .inr rfl
        · cases hv

/-- `Unusedglobproof.used_not_defined_2` -/
theorem used_not_defined_2 {p : RTL.Program} {u : IS} (V : ValidUsedSet p u) {id : Ident}
    (hm : id ≠ p.prog_main) (hd : p.defmap.get id = none) : id ∉ u := by
  intro hu
  rcases V.defined id hu with h | h
  · obtain ⟨g, hg⟩ := ASTProgram.defmap_dom h
    rw [hd] at hg; cases hg
  · exact hm h

theorem mem_defsNames_of_defmap {p : RTL.Program} {id : Ident} {g : GlobDef RTL.Fundef Unit}
    (h : p.defmap.get id = some g) : id ∈ p.defsNames :=
  List.mem_map.mpr ⟨(id, g), ASTProgram.in_defmap h, rfl⟩

/-- A used identifier that is not defined in `p2` but used by `p2` is the main
function, which is also used by `p1`. -/
theorem used_of_used_other {p1 p2 : RTL.Program} {u1 u2 : IS} (V1 : ValidUsedSet p1 u1)
    (V2 : ValidUsedSet p2 u2) (hmain : p1.prog_main = p2.prog_main) {id : Ident}
    (hd : p2.defmap.get id = none) (hu : id ∈ u2) : id ∈ u1 := by
  by_cases hm : id = p2.prog_main
  · rw [hm, ← hmain]; exact V1.main
  · exact absurd hu (used_not_defined_2 V2 hm hd)

/-- `Unusedglobproof.link_valid_used_set` -/
theorem link_valid_used_set {p1 p2 p : RTL.Program} {u1 u2 : IS} (L : link p1 p2 = some p)
    (V1 : ValidUsedSet p1 u1) (V2 : ValidUsedSet p2 u2) : ValidUsedSet p (u1 ++ u2) := by
  obtain ⟨hmain, Y, rfl⟩ := link_prog_inv L
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id gd id' hu hgd href
    rw [linkProgResult_defmap] at hgd
    rw [List.mem_append] at hu ⊢
    rcases h1 : p1.defmap.get id with _ | g1 <;> rcases h2 : p2.defmap.get id with _ | g2 <;>
      rw [h1, h2] at hgd <;> simp only [linkProgMerge] at hgd
    · cases hgd
    · cases hgd
      have hu2 : id ∈ u2 := hu.elim (used_of_used_other V2 V1 hmain.symm h1) (fun x => x)
      exact .inr (V2.closed id _ id' hu2 h2 href)
    · cases hgd
      have hu1 : id ∈ u1 := hu.elim (fun x => x) (used_of_used_other V1 V2 hmain h2)
      exact .inl (V1.closed id _ id' hu1 h1 href)
    · obtain ⟨P1, P2, _⟩ := Y id _ _ h1 h2
      rcases link_def_either hgd with rfl | rfl
      · exact .inl (V1.closed id _ id' (V1.publics id P1) h1 href)
      · exact .inr (V2.closed id _ id' (V2.publics id P2) h2 href)
  · exact List.mem_append.mpr (.inl V1.main)
  · intro id hid
    rcases List.mem_append.mp hid with h | h
    · exact List.mem_append.mpr (.inl (V1.publics id h))
    · exact List.mem_append.mpr (.inr (V2.publics id h))
  · intro id hu
    by_cases hm : id = p1.prog_main
    · exact .inr hm
    · left
      have E : ∃ g, linkProgMerge (p1.defmap.get id) (p2.defmap.get id) = some g := by
        rcases h1 : p1.defmap.get id with _ | g1 <;> rcases h2 : p2.defmap.get id with _ | g2 <;>
          simp only [linkProgMerge]
        · rcases List.mem_append.mp hu with h | h
          · exact absurd h (used_not_defined_2 V1 hm h1)
          · exact absurd h (used_not_defined_2 V2 (by rw [← hmain]; exact hm) h2)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · obtain ⟨_, _, gd, hl⟩ := Y id _ _ h1 h2
          exact ⟨gd, hl⟩
      obtain ⟨g, hg⟩ := E
      rw [← linkProgResult_defmap] at hg
      exact mem_defsNames_of_defmap hg

/-- `Unusedglobproof.link_match_program` -/
theorem link_match_program {p1 p2 p tp1 tp2 : RTL.Program} (h : link p1 p2 = some p)
    (m1 : MatchProg p1 tp1) (m2 : MatchProg p2 tp2) :
    ∃ tp, link tp1 tp2 = some tp ∧ MatchProg p tp := by
  obtain ⟨u1, A1, B1⟩ := m1
  obtain ⟨u2, A2, B2⟩ := m2
  have VU := link_valid_used_set h A1 A2
  obtain ⟨hmain, Y, rfl⟩ := link_prog_inv h
  refine ⟨linkProgResult tp1 tp2, link_prog_succeeds ?_ ?_, u1 ++ u2, VU, ?_⟩
  · rw [B1.main_eq, B2.main_eq]; exact hmain
  · intro id tg1 tg2 e1 e2
    rw [B1.defs] at e1
    rw [B2.defs] at e2
    split at e1
    · split at e2
      · obtain ⟨P1, P2, gd, L⟩ := Y id _ _ e1 e2
        rw [B1.public_eq, B2.public_eq]
        exact ⟨P1, P2, by rw [L]; exact Option.some_ne_none _⟩
      · cases e2
    · cases e1
  · refine ⟨B1.main_eq, ?_, ?_, ?_⟩
    · show tp1.prog_public ++ tp2.prog_public = p1.prog_public ++ p2.prog_public
      rw [B1.public_eq, B2.public_eq]
    · intro id
      rw [linkProgResult_defmap, linkProgResult_defmap, B1.defs, B2.defs, IS.mem_append]
      rcases h1 : p1.defmap.get id with _ | g1 <;> rcases h2 : p2.defmap.get id with _ | g2
      · cases IS.mem id u1 <;> cases IS.mem id u2 <;> rfl
      · rcases m2 : IS.mem id u2 with _ | _
        · rcases m1 : IS.mem id u1 with _ | _
          · rfl
          · have := used_of_used_other A2 A1 hmain.symm h1 (IS.mem_iff.mp m1)
            rw [IS.mem_iff.mpr this] at m2; cases m2
        · cases IS.mem id u1 <;> rfl
      · rcases m1 : IS.mem id u1 with _ | _
        · rcases m2 : IS.mem id u2 with _ | _
          · rfl
          · have := used_of_used_other A1 A2 hmain h2 (IS.mem_iff.mp m2)
            rw [IS.mem_iff.mpr this] at m1; cases m1
        · cases IS.mem id u2 <;> rfl
      · obtain ⟨P1, P2, _⟩ := Y id _ _ h1 h2
        rw [IS.mem_iff.mpr (A1.publics id P1), IS.mem_iff.mpr (A2.publics id P2)]
        rfl
    · show ((PTree.elements _).map Prod.fst).Nodup
      exact PTree.elements_keys_norepet _

/-- `Unusedglobproof.TransfUnusedglobLink` -/
instance transfUnusedglobLink : TransfLink MatchProg where
  transf_link := link_match_program

end Unusedglob
end CC
