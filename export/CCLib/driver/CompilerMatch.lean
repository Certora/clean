/-
  Separate compilation — the linking part of `driver/Compiler.v`:
  `match_if`, `total_if_match`, `partial_if_match`, `TransfIfLink`, the
  composition of the `match_prog` relations of the passes (`mkpass`,
  `CompCert's_passes`), `transf_..._program_match`, semantic preservation
  for the composed relation, and separate compilation
  (`separate_transf_..._program_correct`).

  Differences from Rocq: this file covers the compiler from Cminor to Asm
  (`transf_cminor_program`), the part whose passes are proved correct for
  their linking-aware `match_prog` relations.  The front end (CompCert C →
  Cminor) is still proved for whole programs only (`FrontendCorrect`), so the
  result is a forward simulation from the linked Cminor program to the linked
  Asm program.  CompCert's axioms on external functions and inline assembly
  are hypotheses, as in `BackendCorrect`.
-/
import CCLib.driver.BackendCorrect
import CCLib.backend.UnusedglobproofLink
import CCLib.driver.CompilerCorrect
import CCLib.cfrontend.SimplExprproofLink
import CCLib.cfrontend.SimplLocalsproofLink
import CCLib.cfrontend.CshmgenproofLink

namespace CC
namespace Compiler

open Config Smallstep Linking

/-! ## Optional passes -/

/-- `Compiler.match_if` -/
def matchIf {A : Type} (flag : Unit → Bool) (R : A → A → Prop) : A → A → Prop :=
  if flag () then R else Eq

/-- `Compiler.total_if_match` -/
theorem total_if_match {A : Type} (flag : Unit → Bool) (f : A → A) (rel : A → A → Prop)
    (prog : A) (H : ∀ p, rel p (f p)) : matchIf flag rel prog (totalIf flag f prog) := by
  unfold matchIf totalIf
  cases flag () with
  | true => exact H prog
  | false => rfl

/-- `Compiler.partial_if_match` -/
theorem partial_if_match {A : Type} (flag : Unit → Bool) (f : A → Res A) (rel : A → A → Prop)
    (prog tprog : A) (H : ∀ p tp, f p = .OK tp → rel p tp)
    (T : partialIf flag f prog = .OK tprog) : matchIf flag rel prog tprog := by
  unfold matchIf
  unfold partialIf at T
  cases hf : flag () with
  | true => rw [hf] at T; exact H _ _ T
  | false => rw [hf] at T; cases T; rfl

/-- `Compiler.TransfIfLink` -/
instance transfIfLink {A : Type} [Linker A] (flag : Unit → Bool) (R : A → A → Prop)
    [TL : TransfLink R] : TransfLink (matchIf flag R) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    unfold matchIf at *
    cases hf : flag () with
    | true =>
      simp only [hf, ↓reduceIte] at m1 m2 ⊢
      exact TL.transf_link h m1 m2
    | false =>
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at m1 m2 ⊢
      subst m1 m2
      exact ⟨p, h, rfl⟩

theorem matchIf_forward {A : Type} {L : A → Semantics} {flag : Unit → Bool} {R : A → A → Prop}
    {p tp : A} (M : matchIf flag R p tp) (H : R p tp → ForwardSimulation (L p) (L tp)) :
    ForwardSimulation (L p) (L tp) := by
  unfold matchIf at M
  cases hf : flag () with
  | true => rw [hf] at M; exact H M
  | false => rw [hf] at M; subst M; exact forward_simulation_refl _

/-! ## Composition of the passes -/

/-- `Linking.mkpass` -/
def mkpass {A B : Type} [Linker A] [Linker B] (R : A → B → Prop) [TL : TransfLink R] :
    Pass (Language.gen A) (Language.gen B) :=
  ⟨R, TL⟩

variable (c : Config)

/-- The passes of `transf_cminor_program` (the part of `CompCert's_passes`
    from Cminor to Asm), each with its `match_prog` relation. -/
def cminorPasses : Passes (Language.gen Cminor.Program) (Language.gen Asm.Program) :=
  .cons (mkpass (Selectionproof.MatchProgLink c.selectionOptions)) <|
  .cons (mkpass (RTLgen.MatchProgLink c.moreLikely)) <|
  .cons (mkpass (matchIf (fun _ => c.optimTailcalls) (Tailcallproof.MatchProgLink c.abi))) <|
  .cons (mkpass (Inlining.MatchProgLink id c.shouldInline)) <|
  .cons (mkpass Renumberproof.MatchProgLink) <|
  .cons (mkpass (matchIf (fun _ => c.optimConstprop)
    (Constpropproof.MatchProgLink c.constpropOptions c.abi))) <|
  .cons (mkpass (matchIf (fun _ => c.optimConstprop) Renumberproof.MatchProgLink)) <|
  .cons (mkpass (matchIf (fun _ => c.optimCSE) (CSEproof.MatchProgLink c.vaOptions c.abi))) <|
  .cons (mkpass (matchIf (fun _ => c.optimRedundancy)
    (Deadcodeproof.MatchProgLink c.vaOptions c.abi))) <|
  .cons (mkpass Unusedglob.MatchProg) <|
  .cons (mkpass (Allocproof.MatchProgLink c.abi c.regalloc)) <|
  .cons (mkpass Tunnelingproof.MatchProgLink) <|
  .cons (mkpass (Linearizeproof.MatchProgLink c.enumerateAux)) <|
  .cons (mkpass CleanupLabelsproof.MatchProgLink) <|
  .cons (mkpass (matchIf (fun _ => c.debug) Debugvarproof.MatchProgLink)) <|
  .cons (mkpass (Stackingproof.MatchProgLink c.abi)) <|
  .cons (mkpass (Asmgenproof.MatchProgLink c.asmgenOptions)) <|
  .nil _

/-- `Compiler.match_prog`, restricted to `transf_cminor_program`: the
    composition of the `match_prog` relations of its passes. -/
def CminorMatchProg : Cminor.Program → Asm.Program → Prop :=
  (composePasses (cminorPasses c)).pass_match

/-- `Compiler.transf_c_program_match`, for `transf_cminor_program`: the
    compiler establishes the composed `match_prog` relation. -/
theorem transf_cminor_program_match {p : Cminor.Program} {tp : Asm.Program}
    (h : transfCminorProgram c p = .OK tp) : CminorMatchProg c p tp := by
  unfold transfCminorProgram at h
  obtain ⟨p2, h12, h3⟩ := applyPartial_OK_inv h
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h12
  rw [applyPartial_OK] at h1
  simp only [time] at h1 h2
  unfold transfRtlProgram at h3
  obtain ⟨q15, e15, a16⟩ := applyPartial_OK_inv h3
  obtain ⟨q14, e14, a15⟩ := applyPartial_OK_inv e15
  obtain ⟨q13, e13, a14⟩ := applyPartial_OK_inv e14
  obtain ⟨q12, e12, a13⟩ := applyTotal_OK_inv e13
  obtain ⟨q11, e11, a12⟩ := applyPartial_OK_inv e12
  obtain ⟨q10, e10, a11⟩ := applyTotal_OK_inv e11
  obtain ⟨q9, e9, a10⟩ := applyPartial_OK_inv e10
  obtain ⟨q8, e8, a9⟩ := applyPartial_OK_inv e9
  obtain ⟨q7, e7, a8⟩ := applyPartial_OK_inv e8
  obtain ⟨q6, e6, a7⟩ := applyPartial_OK_inv e7
  obtain ⟨q5, e5, a6⟩ := applyTotal_OK_inv e6
  obtain ⟨q4, e4, a5⟩ := applyTotal_OK_inv e5
  obtain ⟨q3, e3, a4⟩ := applyTotal_OK_inv e4
  obtain ⟨q2, e2, a3⟩ := applyPartial_OK_inv e3
  obtain ⟨q1, e1, a2⟩ := applyTotal_OK_inv e2
  cases e1
  simp only [time] at a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  subst a2 a4 a5 a6 a11 a13
  simp only [CminorMatchProg, cminorPasses, composePasses, passCompose, passIdentity, mkpass]
  exact ⟨p1, Selectionproof.transf_program_match h1,
    p2, RTLgen.transf_program_match _ h2,
    _, total_if_match _ _ _ _ (Tailcallproof.transf_program_match c.abi),
    q3, Inlining.transf_program_match id c.shouldInline a3,
    _, Renumberproof.transf_program_match _,
    _, total_if_match _ _ _ _ (Constpropproof.transf_program_match _ _),
    _, total_if_match _ _ _ _ Renumberproof.transf_program_match,
    q7, partial_if_match _ _ _ _ _ (fun _ _ e => CSEproof.transf_program_match e) a7,
    q8, partial_if_match _ _ _ _ _ (fun _ _ e => Deadcodeproof.transf_program_match e) a8,
    q9, Unusedglob.transf_program_match a9,
    q10, Allocproof.transf_program_match _ _ a10,
    _, Tunnelingproof.transf_program_match _,
    q12, Linearizeproof.transf_program_match _ a12,
    _, CleanupLabelsproof.transf_program_match _,
    q14, partial_if_match _ _ _ _ _ (fun _ _ e => Debugvarproof.transf_program_match e) a14,
    q15, Stackingproof.transf_program_match _ a15,
    tp, Asmgenproof.transf_program_match_link a16,
    rfl⟩

/-- `Compiler.c_semantic_preservation`, for `transf_cminor_program` and as a
    forward simulation: any pair of programs related by the composed
    `match_prog` relation has the same semantics.  The hypotheses are those of
    `transfCminorProgram_correct`. -/
theorem cminor_semantic_preservation (sym : Asm.SymbolSplit) {p : Cminor.Program}
    {tp : Asm.Program} (M : CminorMatchProg c p tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Cminor.semantics p) (Asm.semantics sym c.abi tp) := by
  simp only [CminorMatchProg, cminorPasses, composePasses, passCompose, passIdentity,
    mkpass] at M
  obtain ⟨p1, M1, p2, M2, p3, M3, p4, M4, p5, M5, p6, M6, p7, M7, p8, M8, p9, M9, p10, M10,
    p11, M11, p12, M12, p13, M13, p14, M14, p15, M15, p16, M16, p17, M17, E⟩ := M
  subst E
  have S1 := Selectionproof.transf_program_correct_match c.selectionOptions p p1 M1 hextx hasmx
    hextw hasmw
  have S2 := RTLgen.transf_program_correct_match c.moreLikely M2 hextx hasmx
  have S3 : ForwardSimulation (RTL.semantics p2) (RTL.semantics p3) :=
    matchIf_forward (L := RTL.semantics) M3
      (fun M => Tailcallproof.transf_program_correct_match c.abi M hextx hasmx)
  have S4 := Inlining.transf_program_correct_match id c.shouldInline M4 hext hasm hextp hasmp
  have S5 := Renumberproof.transf_program_correct_match M5
  have S6 : ForwardSimulation (RTL.semantics p5) (RTL.semantics p6) :=
    matchIf_forward (L := RTL.semantics) M6
      (fun M => Constpropproof.transf_program_correct_match M hextx hasmx hext hasm hextp hasmp)
  have S7 : ForwardSimulation (RTL.semantics p6) (RTL.semantics p7) :=
    matchIf_forward (L := RTL.semantics) M7 (fun M => Renumberproof.transf_program_correct_match M)
  have S8 : ForwardSimulation (RTL.semantics p7) (RTL.semantics p8) :=
    matchIf_forward (L := RTL.semantics) M8
      (fun M => CSEproof.transf_program_correct_match M hextx hasmx hext hasm hextp hasmp)
  have S9 : ForwardSimulation (RTL.semantics p8) (RTL.semantics p9) :=
    matchIf_forward (L := RTL.semantics) M9
      (fun M => Deadcodeproof.transf_program_correct_match M hextx hasmx hext hasm hextp hasmp)
  have S10 := Unusedglob.transf_program_correct_match p9 p10 M10 hext hasm
  have S11 := Allocproof.transf_program_correct_match c.abi c.regalloc M11 hextx hasmx hextw hasmw
  have S12 := Tunnelingproof.transf_program_correct_match c.abi M12 hextx hasmx
  have S13 := Linearizeproof.transf_program_correct_match c.enumerateAux c.abi M13
  have S14 := CleanupLabelsproof.transf_program_correct_match c.abi M14
  have S15 : ForwardSimulation (Linear.semantics c.abi p14) (Linear.semantics c.abi p15) :=
    matchIf_forward (L := Linear.semantics c.abi) M15
      (fun M => Debugvarproof.transf_program_correct_match c.abi M)
  have S16 := Stackingproof.transf_program_correct_match c.abi
    (Asmgenproof0.ReturnAddressOffset c.asmgenOptions) M16
    (fun f sg ros k hk => Asmgenproof.return_address_exists c.asmgenOptions f sg ros k hk)
    hext hasm hextp hasmp hextw hasmw
  have S17 := Asmgenproof.transf_program_correct_match M17 sym c.abi (fun n sg => hextx n sg _)
    (fun n sg => hasmx n sg _)
  exact compose_forward_simulations S1 <| compose_forward_simulations S2 <|
    compose_forward_simulations S3 <| compose_forward_simulations S4 <|
    compose_forward_simulations S5 <| compose_forward_simulations S6 <|
    compose_forward_simulations S7 <| compose_forward_simulations S8 <|
    compose_forward_simulations S9 <| compose_forward_simulations S10 <|
    compose_forward_simulations S11 <| compose_forward_simulations S12 <|
    compose_forward_simulations S13 <| compose_forward_simulations S14 <|
    compose_forward_simulations S15 <| compose_forward_simulations S16 S17

/-- `Compiler.separate_transf_c_program_correct`, for `transf_cminor_program`:
    if every Cminor compilation unit of `units` is compiled to the
    corresponding Asm unit of `asmUnits`, and the Cminor units link into
    `prog`, then the Asm units link into some `asmProg`, and there is a forward
    simulation from `prog` to `asmProg`. -/
theorem separate_transf_cminor_program_correct (sym : Asm.SymbolSplit)
    {units : NList Cminor.Program} {asmUnits : NList Asm.Program} {prog : Cminor.Program}
    (hc : NListForall2 (fun cu tcu => transfCminorProgram c cu = .OK tcu) units asmUnits)
    (hl : linkList units = some prog)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ∃ asmProg, linkList asmUnits = some asmProg ∧
      Nonempty (ForwardSimulation (Cminor.semantics prog) (Asm.semantics sym c.abi asmProg)) := by
  have hm : NListForall2 (composePasses (cminorPasses c)).pass_match units asmUnits := by
    clear hl
    induction hc with
    | nbase h => exact .nbase (transf_cminor_program_match c h)
    | ncons h _ ih => exact .ncons (transf_cminor_program_match c h) ih
  obtain ⟨asmProg, P, Q⟩ := link_list_compose_passes (cminorPasses c) hm hl
  exact ⟨asmProg, P, ⟨cminor_semantic_preservation c sym Q hext hasm hextx hasmx hextw hasmw
    hextp hasmp⟩⟩

/-! ## The whole compiler, CompCert C to Asm -/

/-- `Compiler.CompCert's_passes`: the passes of `transf_c_program`, each with
    its `match_prog` relation.  The Clight programs between `SimplExpr` and
    `Cshmgen` are well-formed programs (`WFProgram`, whose composite
    environment is built from its type declarations), as in Rocq. -/
def cPasses : Passes (Language.gen Csyntax.Program) (Language.gen Asm.Program) :=
  .cons (mkpass SimplExpr.MatchProgLink) <|
  .cons (mkpass (SimplLocals.MatchProgLink c.simplLocalsOptions)) <|
  .cons (mkpass (Cshmgen.MatchProgLink (Conventions1.returnValueNeedsNormalization c.abi))) <|
  .cons (mkpass Cminorgen.MatchProgLink) <|
  cminorPasses c

/-- `Compiler.match_prog`: the composition of the `match_prog` relations of
    all the passes of the compiler. -/
def CMatchProg : Csyntax.Program → Asm.Program → Prop :=
  (composePasses (cPasses c)).pass_match

theorem simplExpr_wf {fu : Ident} {p : Csyntax.Program} {tp : CC.Program}
    (h : SimplExpr.translProgram fu p = .OK tp) :
    buildCompositeEnv tp.prog_types = .OK tp.prog_comp_env := by
  unfold SimplExpr.translProgram at h
  split at h
  · cases h
  · cases h; exact p.prog_comp_env_eq

theorem simplLocals_wf {opts : SimplLocals.Options} {p : CtypesLinking.WFProgram}
    {tp : CC.Program} (h : SimplLocals.transfProgram opts p.val = .OK tp) :
    buildCompositeEnv tp.prog_types = .OK tp.prog_comp_env := by
  unfold SimplLocals.transfProgram at h
  split at h
  · cases h
  · cases h; exact p.property

/-- `Compiler.transf_c_program_match`: the compiler establishes the composed
    `match_prog` relation. -/
theorem transf_c_program_match {p : Csyntax.Program} {tp : Asm.Program}
    (h : transfCProgram c p = .OK tp) : CMatchProg c p tp := by
  rw [transfCProgram_eq] at h
  obtain ⟨p4, h1234, h5⟩ := applyPartial_OK_inv h
  obtain ⟨p3, h123, h4⟩ := applyPartial_OK_inv h1234
  obtain ⟨p2, h12, h3⟩ := applyPartial_OK_inv h123
  obtain ⟨p1, h1, h2⟩ := applyPartial_OK_inv h12
  rw [applyPartial_OK] at h1
  simp only [time] at h1 h2 h3 h4
  let w1 : CtypesLinking.WFProgram := ⟨p1, simplExpr_wf h1⟩
  let w2 : CtypesLinking.WFProgram := ⟨p2, simplLocals_wf (p := w1) h2⟩
  simp only [CMatchProg, cPasses, composePasses, passCompose, mkpass]
  exact ⟨w1, SimplExpr.transf_program_match_link (tp := w1) h1,
    w2, SimplLocals.transf_program_match_link (p := w1) (tp := w2) h2,
    p3, Cshmgen.transf_program_match_link (p := w2) h3,
    p4, Cminorgen.transf_program_match h4,
    transf_cminor_program_match c h5⟩

/-- The forward half of `Compiler.c_semantic_preservation`: a forward
    simulation from `Cstrategy.semantics p` to `Asm.semantics tp` for programs
    related by the composed `match_prog` relation. -/
theorem cstrategy_semantic_preservation_match (sym : Asm.SymbolSplit)
    {p : Csyntax.Program} {tp : Asm.Program} (M : CMatchProg c p tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge) :
    ForwardSimulation (Cstrategy.semantics p) (Asm.semantics sym c.abi tp) := by
  simp only [CMatchProg, cPasses, composePasses, passCompose, mkpass] at M
  obtain ⟨w1, M1, w2, M2, p3, M3, p4, M4, M5⟩ := M
  exact compose_forward_simulations (SimplExpr.transl_program_correct_match M1) <|
    compose_forward_simulations
      (SimplLocals.transf_program_correct_match c.simplLocalsOptions M2 hext hasm) <|
    compose_forward_simulations
      (Cshmgen.transl_program_correct_match _ M3 hextw hasmw) <|
    compose_forward_simulations
      (Cminorgen.transl_program_correct_match M4 hext hasm hextp hasmp) <|
    cminor_semantic_preservation c sym M5 hext hasm hextx hasmx hextw hasmw hextp hasmp

/-- `Compiler.c_semantic_preservation`: for programs related by the composed
    `match_prog` relation, `Asm.semantics tp` is a backward simulation of
    `Csem.semantics p`.  CompCert's axioms on external functions and inline
    assembly (including their receptiveness) are hypotheses. -/
theorem c_semantic_preservation (sym : Asm.SymbolSplit)
    {p : Csyntax.Program} {tp : Asm.Program} (M : CMatchProg c p tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv) :
    BackwardSimulation (Csem.semantics p) (Asm.semantics sym c.abi tp) := by
  have hdet := Asm.semantics_determinate sym c.abi tp
  have hssr := Cstrategy.semantics_strongly_receptive p hrec
  exact compose_backward_simulation hdet.sd_traces
    (factor_backward_simulation (Cstrategy.strategy_simulation p)
      (Csem.semantics_single_events p) hssr.ssr_well_behaved)
    (forward_to_backward_simulation
      (factor_forward_simulation
        (cstrategy_semantic_preservation_match c sym M hext hasm hextx hasmx
          hextw hasmw hextp hasmp)
        hdet.sd_traces)
      (atomic_receptive hssr) hdet)

/-- `Compiler.separate_transf_c_program_correct`: if every CompCert C
    compilation unit of `units` is compiled to the corresponding Asm unit of
    `asmUnits`, and the C units link into `prog`, then the Asm units link into
    some `asmProg`, and `Asm.semantics asmProg` is a backward simulation of
    `Csem.semantics prog`. -/
theorem separate_transf_c_program_correct (sym : Asm.SymbolSplit)
    {units : NList Csyntax.Program} {asmUnits : NList Asm.Program} {prog : Csyntax.Program}
    (hc : NListForall2 (fun cu tcu => transfCProgram c cu = .OK tcu) units asmUnits)
    (hl : linkList units = some prog)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)
    (hrec : ExternalsReceptive (Csem.globalenv prog).genv_genv.toSenv) :
    ∃ asmProg, linkList asmUnits = some asmProg ∧
      Nonempty (BackwardSimulation (Csem.semantics prog) (Asm.semantics sym c.abi asmProg)) := by
  have hm : NListForall2 (composePasses (cPasses c)).pass_match units asmUnits := by
    clear hl
    induction hc with
    | nbase h => exact .nbase (transf_c_program_match c h)
    | ncons h _ ih => exact .ncons (transf_c_program_match c h) ih
  obtain ⟨asmProg, P, Q⟩ := link_list_compose_passes (cPasses c) hm hl
  exact ⟨asmProg, P, ⟨c_semantic_preservation c sym Q hext hasm hextx hasmx hextw hasmw
    hextp hasmp hrec⟩⟩

end Compiler
end CC
