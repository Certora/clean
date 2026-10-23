/-
  `common/Linking.v`: the linker for the generic function definitions
  `AST.fundef` (`Linker_fundef`, `link_fundef`, `linkorder_fundef`), the
  commutation of linking with `transf_fundef` / `transf_partial_fundef`
  (`link_transf_partial_fundef`), and the standard `TransfLink` instances
  (`TransfPartialContextualLink`, `TransfPartialLink`,
  `TransfTotallContextualLink`, `TransfTotalLink`) for programs over
  `AST.fundef`, i.e. for every language after Clight.

  `CCLib/common/LinkingTheory.lean` and `LinkingMatch.lean` only treat
  `Ctypes.fundef` (`FunDefGen`); in the port, `AST.fundef` is `ASTFundef`,
  which is defined in `CCLib/backend/Cminor.lean`, hence the separate file.

  Not in Rocq: `transformPartialProgram_of_match` and
  `transformProgram_of_match`.  For a *non-contextual* function-by-function
  transformation, the matching relation determines the target program, so a
  correctness theorem stated for `transf_program p = OK tp` applies to every
  `tp` with `match_prog p tp`.  The per-pass `transf_program_correct_match`
  theorems (Rocq states `transf_program_correct` directly for `match_prog`)
  are derived this way.
-/
import CCLib.common.LinkingMatch
import CCLib.backend.Cminor

namespace CC
namespace Linking
open Linker

/-! ## `AST.fundef` (`Linking.Linker_fundef`) -/

section ASTFundefLinker
variable {F : Type}

/-- `Linking.link_fundef`: an `EF_external` declaration links with an
    internal definition; two external declarations link if identical. -/
def linkASTFundef : ASTFundef F → ASTFundef F → Option (ASTFundef F)
  | .Internal _, .Internal _ => none
  | .External ef1, .External ef2 => if ef1 = ef2 then some (.External ef1) else none
  | .Internal f, .External ef =>
    match ef with
    | .EF_external _ _ => some (.Internal f)
    | _ => none
  | .External ef, .Internal f =>
    match ef with
    | .EF_external _ _ => some (.Internal f)
    | _ => none

/-- `Linking.linkorder_fundef` -/
inductive LinkorderASTFundef : ASTFundef F → ASTFundef F → Prop where
  | refl (fd : ASTFundef F) : LinkorderASTFundef fd fd
  | ext_int (f : F) (id : String) (sg : Signature) :
      LinkorderASTFundef (.External (.EF_external id sg)) (.Internal f)

theorem linkASTFundef_linkorder {x y z : ASTFundef F} (h : linkASTFundef x y = some z) :
    LinkorderASTFundef x z ∧ LinkorderASTFundef y z := by
  cases x with
  | Internal f1 =>
    cases y with
    | Internal => simp [linkASTFundef] at h
    | External ef =>
      cases ef <;> simp [linkASTFundef] at h
      subst h; exact ⟨.refl _, .ext_int _ _ _⟩
  | External ef1 =>
    cases y with
    | Internal f2 =>
      cases ef1 <;> simp [linkASTFundef] at h
      subst h; exact ⟨.ext_int _ _ _, .refl _⟩
    | External ef2 =>
      simp only [linkASTFundef] at h
      split at h
      · rename_i hc; subst hc; cases h; exact ⟨.refl _, .refl _⟩
      · cases h

instance instLinkerASTFundef : Linker (ASTFundef F) where
  link := linkASTFundef
  linkorder := LinkorderASTFundef
  linkorder_refl := .refl
  linkorder_trans := by
    intro x y z h1 h2
    cases h1 with
    | refl => exact h2
    | ext_int => cases h2 with
      | refl => exact .ext_int _ _ _
  link_linkorder := linkASTFundef_linkorder

/-- `Linking.link_fundef_either` (for `AST.fundef`) -/
theorem link_astfundef_either {f1 f2 f : ASTFundef F} (h : link f1 f2 = some f) :
    f = f1 ∨ f = f2 := by
  change linkASTFundef f1 f2 = some f at h
  cases f1 with
  | Internal f1 =>
    cases f2 with
    | Internal => simp [linkASTFundef] at h
    | External ef => cases ef <;> simp [linkASTFundef] at h; exact .inl h.symm
  | External ef =>
    cases f2 with
    | Internal => cases ef <;> simp [linkASTFundef] at h; exact .inr h.symm
    | External =>
      simp only [linkASTFundef] at h
      split at h
      · cases h; exact .inl rfl
      · cases h

end ASTFundefLinker

/-! ## Commutation of linking with function transformations -/

section TransfASTFundef
variable {A B : Type}

/-- `Linking.link_transf_partial_fundef` (for `AST.fundef`) -/
theorem link_transf_partial_astfundef (tr1 tr2 : A → Res B) {f1 f2 f : ASTFundef A}
    {tf1 tf2 : ASTFundef B} (h : link f1 f2 = some f)
    (h1 : ASTFundef.transfPartial tr1 f1 = .OK tf1)
    (h2 : ASTFundef.transfPartial tr2 f2 = .OK tf2) :
    ∃ tf, link tf1 tf2 = some tf ∧
      (ASTFundef.transfPartial tr1 f = .OK tf ∨ ASTFundef.transfPartial tr2 f = .OK tf) := by
  change linkASTFundef f1 f2 = some f at h
  cases f1 with
  | Internal a1 =>
    cases e1 : tr1 a1 with
    | Error => simp [ASTFundef.transfPartial, e1] at h1
    | OK b1 =>
      simp only [ASTFundef.transfPartial, e1, Res.OK.injEq] at h1
      subst h1
      cases f2 with
      | Internal => simp [linkASTFundef] at h
      | External ef =>
        simp only [ASTFundef.transfPartial, Res.OK.injEq] at h2
        subst h2
        cases ef <;> simp [linkASTFundef] at h
        subst h
        exact ⟨.Internal b1, rfl, .inl (by simp [ASTFundef.transfPartial, e1])⟩
  | External ef =>
    simp only [ASTFundef.transfPartial, Res.OK.injEq] at h1
    subst h1
    cases f2 with
    | Internal a2 =>
      cases e2 : tr2 a2 with
      | Error => simp [ASTFundef.transfPartial, e2] at h2
      | OK b2 =>
        simp only [ASTFundef.transfPartial, e2, Res.OK.injEq] at h2
        subst h2
        cases ef <;> simp [linkASTFundef] at h
        subst h
        exact ⟨.Internal b2, rfl, .inr (by simp [ASTFundef.transfPartial, e2])⟩
    | External ef2 =>
      simp only [ASTFundef.transfPartial, Res.OK.injEq] at h2
      subst h2
      simp only [linkASTFundef] at h
      split at h
      · rename_i hc
        cases h
        refine ⟨.External ef, ?_, .inl rfl⟩
        change linkASTFundef _ _ = _
        simp only [linkASTFundef, if_pos hc]
      · cases h

/-- A total function transformation on `AST.fundef` (`AST.transf_fundef`):
    internal functions are mapped to internal functions, external ones are
    kept. -/
structure IsTransfFundef (T : ASTFundef A → ASTFundef B) (g : A → B) : Prop where
  internal : ∀ f, T (.Internal f) = .Internal (g f)
  external : ∀ ef, T (.External ef) = .External ef

theorem IsTransfFundef.partial {T : ASTFundef A → ASTFundef B} {g : A → B}
    (hT : IsTransfFundef T g) (fd : ASTFundef A) :
    ASTFundef.transfPartial (fun f => .OK (g f)) fd = .OK (T fd) := by
  cases fd <;> simp [ASTFundef.transfPartial, hT.internal, hT.external]

/-- The total-transformation analogue of `link_transf_partial_astfundef`. -/
theorem link_transf_astfundef {T1 T2 : ASTFundef A → ASTFundef B} {g1 g2 : A → B}
    (hT1 : IsTransfFundef T1 g1) (hT2 : IsTransfFundef T2 g2) {f1 f2 f : ASTFundef A}
    (h : link f1 f2 = some f) :
    ∃ tf, link (T1 f1) (T2 f2) = some tf ∧ (tf = T1 f ∨ tf = T2 f) := by
  obtain ⟨tf, P, Q⟩ := link_transf_partial_astfundef (fun f => .OK (g1 f))
    (fun f => .OK (g2 f)) h (hT1.partial f1) (hT2.partial f2)
  rw [hT1.partial, hT2.partial] at Q
  refine ⟨tf, P, ?_⟩
  rcases Q with Q | Q
  · cases Q; exact .inl rfl
  · cases Q; exact .inr rfl

end TransfASTFundef

/-! ## `TransfLink` instances for programs over `AST.fundef` -/

section TransfASTInstances
variable {A B V : Type} [Linker V]

/-- `Linking.TransfPartialContextualLink` (for `AST.fundef`) -/
theorem transfPartialContextualLinkAST {Cx : Type} (trFun : Cx → A → Res B)
    (ctxFor : ASTProgram (ASTFundef A) V → Cx) :
    TransfLink (fun (p1 : ASTProgram (ASTFundef A) V) (p2 : ASTProgram (ASTFundef B) V) =>
      MatchProgramCtx (fun cu f tf => ASTFundef.transfPartial (trFun (ctxFor cu)) f = .OK tf)
        Eq p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    exact link_transf_partial_astfundef _ _ hl e1 e2

/-- `Linking.TransfPartialLink` (for `AST.fundef`) -/
theorem transfPartialLinkAST (trFun : A → Res B) :
    TransfLink (fun (p1 : ASTProgram (ASTFundef A) V) (p2 : ASTProgram (ASTFundef B) V) =>
      MatchProgramCtx (fun _ f tf => ASTFundef.transfPartial trFun f = .OK tf) Eq p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    exact link_transf_partial_astfundef _ _ hl e1 e2

/-- `Linking.TransfTotallContextualLink` (for `AST.fundef`) -/
theorem transfTotalContextualLinkAST {Cx : Type} (T : Cx → ASTFundef A → ASTFundef B)
    (g : Cx → A → B) (hT : ∀ c, IsTransfFundef (T c) (g c))
    (ctxFor : ASTProgram (ASTFundef A) V → Cx) :
    TransfLink (fun (p1 : ASTProgram (ASTFundef A) V) (p2 : ASTProgram (ASTFundef B) V) =>
      MatchProgramCtx (fun cu f tf => tf = T (ctxFor cu) f) Eq p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    subst e1 e2
    exact link_transf_astfundef (hT _) (hT _) hl

/-- `Linking.TransfTotalLink` (for `AST.fundef`) -/
theorem transfTotalLinkAST (T : ASTFundef A → ASTFundef B) (g : A → B)
    (hT : IsTransfFundef T g) :
    TransfLink (fun (p1 : ASTProgram (ASTFundef A) V) (p2 : ASTProgram (ASTFundef B) V) =>
      MatchProgramCtx (fun _ f tf => tf = T f) Eq p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    subst e1 e2
    exact link_transf_astfundef hT hT hl

end TransfASTInstances

/-! ## Non-contextual matching determines the transformed program -/

section MatchDetermines
variable {C F1 F2 V : Type} [Linker C]

theorem transfGlobdefs_of_forall2 {tr : F1 → Res F2} {ctx : C} :
    ∀ {l1 : List (Ident × GlobDef F1 V)} {l2 : List (Ident × GlobDef F2 V)},
    ListForall2 (MatchIdentGlobdef (fun _ f tf => tr f = .OK tf) Eq ctx) l1 l2 →
    transfGlobdefs (fun _ f => tr f) (fun _ v => .OK v) l1 = .OK l2
  | _, _, .nil => rfl
  | (id, g1) :: _, (id', g2) :: _, .cons ⟨he, hm⟩ t => by
    simp only at he; subst he
    have ih := transfGlobdefs_of_forall2 t
    cases hm with
    | gfun _ hr => simp [transfGlobdefs, hr, ih]
    | @gvar v1 v2 hv =>
      obtain ⟨hi, hin, hr, hvo⟩ := hv
      obtain ⟨_, _, _, _⟩ := v1
      obtain ⟨_, _, _, _⟩ := v2
      simp only at hi hin hr hvo
      subst hi hin hr hvo
      simp [transfGlobdefs, transfGlobvar, ih]

/-- A `match_program` relation for a non-contextual partial transformation
    determines the target: it is the result of `transform_partial_program`. -/
theorem transformPartialProgram_of_matchGen {tr : F1 → Res F2} {ctx : C}
    {p : ASTProgram F1 V} {tp : ASTProgram F2 V}
    (h : MatchProgramGen (fun _ f tf => tr f = .OK tf) Eq ctx p tp) :
    transformPartialProgram tr p = .OK tp := by
  obtain ⟨d, m, pub⟩ := h
  obtain ⟨defs, pb, mn⟩ := tp
  simp only at m pub
  subst m pub
  simp [transformPartialProgram, transformPartialProgram2, transfGlobdefs_of_forall2 d]

theorem transformPartialProgram_of_match {F1 F2 V : Type} [Linker F1] [Linker V]
    {tr : F1 → Res F2} {p : ASTProgram F1 V} {tp : ASTProgram F2 V}
    (h : MatchProgramCtx (fun _ f tf => tr f = .OK tf) Eq p tp) :
    transformPartialProgram tr p = .OK tp :=
  transformPartialProgram_of_matchGen h

/-- The total analogue: the target is `transform_program` of the source. -/
theorem transformProgram_of_match {F1 F2 V : Type} [Linker F1] [Linker V]
    {T : F1 → F2} {p : ASTProgram F1 V} {tp : ASTProgram F2 V}
    (h : MatchProgramCtx (fun _ f tf => tf = T f) Eq p tp) :
    tp = transformProgram T p := by
  have key : ∀ {l1 : List (Ident × GlobDef F1 V)} {l2 : List (Ident × GlobDef F2 V)},
      ListForall2 (MatchIdentGlobdef (fun (_ : ASTProgram F1 V) f tf => tf = T f) Eq p) l1 l2 →
      ListForall2 (MatchIdentGlobdef
        (fun (_ : ASTProgram F1 V) f tf => (fun f => Res.OK (T f)) f = .OK tf) Eq p) l1 l2 := by
    intro l1 l2 hl
    induction hl with
    | nil => exact .nil
    | @cons a b _ _ hm _ ih =>
      refine .cons ⟨hm.1, ?_⟩ ih
      obtain ⟨_, g1⟩ := a
      obtain ⟨_, g2⟩ := b
      obtain ⟨_, hm2⟩ := hm
      cases hm2 with
      | gfun hl hr => exact .gfun hl (by simp [hr])
      | gvar hv => exact .gvar hv
  have h' : MatchProgramCtx (fun _ f tf => (fun f => Res.OK (T f)) f = .OK tf) Eq p tp :=
    ⟨key h.defs, h.main_eq, h.public_eq⟩
  have := transformPartialProgram_of_match h'
  rw [transform_program_partial_program] at this
  cases this; rfl

end MatchDetermines

end Linking
end CC
