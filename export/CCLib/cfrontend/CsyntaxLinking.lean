/-
  `Ctypes.Linker_program` for CompCert C programs (`Csyntax.program`).

  In Rocq, `Ctypes.link_program` is defined once for `Ctypes.program F` and
  any `F`.  In the port, Clight programs (`CtypesLinking.WFProgram`) and
  CompCert C programs (`Csyntax.Program`, which carries
  `prog_comp_env_eq`) are distinct types, so the linker is instantiated here
  for the latter, exactly as `CtypesLinking.linkProgram` is for the former.
-/
import CCLib.cfrontend.CtypesLinking
import CCLib.cfrontend.Csyntax

namespace CC
namespace CtypesLinking

/-- `Ctypes.link_program`, for CompCert C programs.  The `Error` case of
    `build_composite_env` cannot happen (`link_build_composite_env`). -/
def linkCProgram (p1 p2 : Csyntax.Program) : Option Csyntax.Program :=
  match Linker.link p1.toAST p2.toAST with
  | none => none
  | some p =>
    match Linker.link p1.prog_types p2.prog_types with
    | none => none
    | some typs =>
      match he : buildCompositeEnv typs with
      | .OK env =>
        some { prog_defs := p.prog_defs, prog_public := p.prog_public,
               prog_main := p.prog_main, prog_types := typs, prog_comp_env := env,
               prog_comp_env_eq := he }
      | .Error _ => none

/-- `Ctypes.linkorder_program`, for CompCert C programs. -/
def LinkorderCProgram (p1 p2 : Csyntax.Program) : Prop :=
  Linker.linkorder p1.toAST p2.toAST ∧ EnvExtends p1.prog_comp_env p2.prog_comp_env

theorem linkCProgram_inv {p1 p2 p : Csyntax.Program} (h : linkCProgram p1 p2 = some p) :
    ∃ pp typs, Linker.link p1.toAST p2.toAST = some pp ∧
      Linker.link p1.prog_types p2.prog_types = some typs ∧
      p.toAST = pp ∧ p.prog_types = typs := by
  unfold linkCProgram at h
  split at h
  · cases h
  · rename_i pp hpp
    split at h
    · cases h
    · rename_i typs ht
      split at h
      · cases h
        exact ⟨pp, typs, hpp, ht, rfl, rfl⟩
      · cases h

theorem linkCProgram_linkorder {x y z : Csyntax.Program} (h : linkCProgram x y = some z) :
    LinkorderCProgram x z ∧ LinkorderCProgram y z := by
  have h' := h
  unfold linkCProgram at h'
  split at h'
  · cases h'
  · rename_i pp hpp
    split at h'
    · cases h'
    · rename_i typs ht
      split at h'
      · rename_i env he
        cases h'
        obtain ⟨env', hb, e1, e2⟩ :=
          link_build_composite_env x.prog_comp_env_eq y.prog_comp_env_eq ht
        rw [he] at hb; cases hb
        have lo := Linker.link_linkorder hpp
        exact ⟨⟨lo.1, e1⟩, ⟨lo.2, e2⟩⟩
      · cases h'

/-- `Ctypes.Linker_program`, for CompCert C programs. -/
instance instLinkerCProgram : Linker Csyntax.Program where
  link := linkCProgram
  linkorder := LinkorderCProgram
  linkorder_refl _ := ⟨Linker.linkorder_refl _, envExtends_refl _⟩
  linkorder_trans h1 h2 := ⟨Linker.linkorder_trans h1.1 h2.1, envExtends_trans h1.2 h2.2⟩
  link_linkorder := linkCProgram_linkorder

end CtypesLinking
end CC
