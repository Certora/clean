/-
  Pulling local scalar variables out of memory: separate compilation — the
  linking part of `cfrontend/SimplLocalsproof.v` (`match_prog`,
  `transf_program_match`, `TransfSimplLocalsLink`) and the semantic
  preservation theorem stated for `match_prog`.

  Clight programs with linking are `CtypesLinking.WFProgram` (CompCert's
  `Ctypes.program`, whose composite environment is the one built from its
  composite definitions).
-/
import CCLib.cfrontend.SimplLocalsproofStep
import CCLib.cfrontend.CtypesLinking
import CCLib.common.LinkingFundef

namespace CC
namespace SimplLocals

open CtypesLinking Smallstep

/-- `SimplLocalsproof.match_prog` -/
def MatchProgLink (opts : Options) : WFProgram → WFProgram → Prop :=
  MatchProgramC (fun f tf => transfFundef opts f = .OK tf)

theorem transfFundef_internal {opts : Options} {f : Function} {tf : FunDef}
    (h : transfFundef opts (.Internal f) = .OK tf) :
    ∃ tf', transfFunction opts f = .OK tf' ∧ tf = .Internal tf' := by
  simp only [transfFundef] at h
  split at h
  · rename_i tf' e; cases h; exact ⟨tf', e, rfl⟩
  · cases h

/-- `SimplLocals.transf_fundef` commutes with linking. -/
theorem link_transfFundef {opts : Options} {f1 f2 f tf1 tf2 : FunDef}
    (h : Linker.link f1 f2 = some f) (e1 : transfFundef opts f1 = .OK tf1)
    (e2 : transfFundef opts f2 = .OK tf2) :
    ∃ tf, Linker.link tf1 tf2 = some tf ∧ transfFundef opts f = .OK tf := by
  change linkFundef f1 f2 = some f at h
  cases f1 with
  | Internal a1 =>
    cases f2 with
    | Internal => simp [linkFundef] at h
    | External ef targs tres cc =>
      cases ef <;> simp [linkFundef] at h
      subst h
      obtain ⟨b1, E1, rfl⟩ := transfFundef_internal e1
      simp only [transfFundef] at e2
      cases e2
      exact ⟨.Internal b1, rfl, by simp [transfFundef, E1]⟩
  | External ef targs tres cc =>
    cases f2 with
    | Internal a2 =>
      cases ef <;> simp [linkFundef] at h
      subst h
      obtain ⟨b2, E2, rfl⟩ := transfFundef_internal e2
      simp only [transfFundef] at e1
      cases e1
      exact ⟨.Internal b2, rfl, by simp [transfFundef, E2]⟩
    | External ef2 targs2 tres2 cc2 =>
      simp only [transfFundef] at e1 e2
      cases e1; cases e2
      simp only [linkFundef] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        cases h
        exact ⟨_, by change linkFundef _ _ = _; simp [linkFundef], rfl⟩
      · cases h

/-- `SimplLocalsproof.transf_program_match` -/
theorem transf_program_match_link {opts : Options} {p tp : WFProgram}
    (h : transfProgram opts p.val = .OK tp.val) : MatchProgLink opts p tp := by
  unfold transfProgram at h
  split at h
  · cases h
  · rename_i p1 hp1
    have e := Res.OK.inj h
    refine ⟨?_, ?_⟩
    · show Linking.MatchProgramGen _ Eq p.val.toAST p.val.toAST tp.val.toAST
      rw [← e]
      exact Linking.match_transform_partial_program hp1
    · rw [← e]

/-- `SimplLocalsproof.TransfSimplLocalsLink` -/
instance transfSimplLocalsLink (opts : Options) : Linking.TransfLink (MatchProgLink opts) where
  transf_link h m1 m2 := link_match_program (fun _ _ _ _ _ hl e1 e2 => link_transfFundef hl e1 e2)
    h m1 m2

/-- A Clight program related by `match_prog` is the output of `transf_program`. -/
theorem transfProgram_of_match {opts : Options} {p tp : WFProgram} (h : MatchProgLink opts p tp) :
    transfProgram opts p.val = .OK tp.val := by
  obtain ⟨m, ht⟩ := h
  have E : transformPartialProgram (transfFundef opts) (programToAST p.val) = .OK tp.toAST :=
    Linking.transformPartialProgram_of_matchGen m
  have hce : tp.val.prog_comp_env = p.val.prog_comp_env := by
    have h1 := tp.property
    have h2 := p.property
    rw [ht, h2] at h1
    exact (Res.OK.inj h1).symm
  unfold transfProgram
  rw [E]
  obtain ⟨⟨d, pub, mn, ty, ce⟩, _⟩ := tp
  simp only at ht hce
  subst ht hce
  rfl

/-- `SimplLocalsproof.transf_program_correct`, for `match_prog`. -/
theorem transf_program_correct_match (opts : Options) {p tp : WFProgram}
    (h : MatchProgLink opts p tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg)) :
    ForwardSimulation (Clight.semantics1 p.val) (Clight.semantics2 tp.val) :=
  transf_program_correct opts p.val tp.val (transfProgram_of_match h)
    (buildCompositeEnv_wf p.property) hext hasm

end SimplLocals
end CC
