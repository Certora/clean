/-
  Correctness of instruction selection — port of `backend/Selectionproof.v`,
  part 7: the program-level facts (`symbols_preserved`, `senv_preserved`,
  `functions_translated`, `function_ptr_translated`,
  `sig_function_translated`, `stackspace_function_translated`, `wt_prog`),
  the simulation diagram `sel_step_correct`, `sel_initial_states`,
  `sel_final_states` and the main theorem `transf_program_correct`.

  As in Rocq, the simulation is proved for the linking-aware relation
  `match_prog` (`MatchProgLink`): every function may have been translated in
  its own compilation unit `cu` (with `linkorder cu prog`), with the
  definitions map of `cu` and helpers declared in `cu`.  `transf_program_match`
  shows that `sel_program` establishes it and `transfSelectionLink` that it
  commutes with linking.

  Differences from Rocq:
  * the axioms of CompCert about external functions and inline assembly
    (compatibility with memory extensions, `ec_mem_extends`, and
    well-typedness of results, `external_call_well_typed`) are explicit
    hypotheses of `transf_program_correct`.
-/
import CCLib.backend.SelectionproofMatch
import CCLib.backend.SelectionproofHelpers

namespace CC
namespace Selectionproof

open Op CminorSel SelectOp Selection Cminortyping Smallstep

/-- `sel_program` succeeds exactly when the helpers are found and every function is
translated. -/
theorem selProgram_inv {opts : Options} {prog : Cminor.Program} {tprog : CminorSel.Program}
    (h : selProgram opts prog = .OK tprog) :
    ∃ hf, getHelpers prog.defmap = .OK hf ∧
      transformPartialProgram (selFundef opts prog.defmap hf) prog = .OK tprog :=
  res_bind_ok.mp h

theorem matchDefs_gfun {F1 F2 V1 V2 : Type} {Rf : F1 → F2 → Prop} {Rv : V1 → V2 → Prop} :
    ∀ {l1 : List (Ident × GlobDef F1 V1)} {l2 : List (Ident × GlobDef F2 V2)},
    Genv.MatchDefs Rf Rv l1 l2 → ∀ {i f}, (i, GlobDef.Gfun f) ∈ l1 → ∃ tf, Rf f tf := by
  intro l1 l2 h
  induction h with
  | nil => intro i f hin; cases hin
  | cons hg _ ih =>
    intro i f hin
    cases hin with
    | head => cases hg with | gfun hr => exact ⟨_, hr⟩
    | tail _ hin => exact ih hin

/-- `Selection.sel_function` inversion. -/
theorem selFunction_inv {opts : Options} {dm : PTree Globdef} {hf : SplitLong.HelperFunctions}
    {f : Cminor.Function} {f' : CminorSel.Function} (h : selFunction opts dm hf f = .OK f') :
    ∃ env body, typeFunction f = .OK env ∧
      selStmt opts dm (Selection.knownId f) env f.fn_body .Sskip = .OK body ∧
      f' = { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_vars := f.fn_vars,
             fn_stackspace := f.fn_stackspace, fn_body := body } := by
  unfold selFunction at h
  obtain ⟨env, h1, h⟩ := res_bind_ok.mp h
  obtain ⟨body, h2, h⟩ := res_bind_ok.mp h
  cases h
  exact ⟨env, body, h1, h2, rfl⟩

/-- `Selectionproof.stackspace_function_translated` -/
theorem stackspace_function_translated {opts : Options} {dm : PTree Globdef}
    {hf : SplitLong.HelperFunctions} {f : Cminor.Function} {f' : CminorSel.Function}
    (h : selFunction opts dm hf f = .OK f') : f'.fn_stackspace = f.fn_stackspace := by
  obtain ⟨_, _, _, _, rfl⟩ := selFunction_inv h; rfl

theorem body_function_translated {opts : Options} {dm : PTree Globdef}
    {hf : SplitLong.HelperFunctions} {f : Cminor.Function} {f' : CminorSel.Function}
    {env : Typenv} (h : selFunction opts dm hf f = .OK f') (henv : typeFunction f = .OK env) :
    selStmt opts dm (Selection.knownId f) env f.fn_body .Sskip = .OK f'.fn_body := by
  obtain ⟨env', _, h1, h2, rfl⟩ := selFunction_inv h
  rw [henv] at h1; cases h1; exact h2

/-- `Selectionproof.sig_function_translated` -/
theorem sig_function_translated {opts : Options} {dm : PTree Globdef}
    {hf : SplitLong.HelperFunctions} {f : Cminor.Fundef} {tf : CminorSel.Fundef}
    (h : selFundef opts dm hf f = .OK tf) : CminorSel.funsig tf = Cminor.funsig f := by
  cases f with
  | Internal f =>
    simp only [selFundef, ASTFundef.transfPartial] at h
    split at h
    · next f' hf' =>
      cases h
      obtain ⟨_, _, _, _, rfl⟩ := selFunction_inv hf'; rfl
    · cases h
  | External ef => cases h; rfl

/-- `Selectionproof.measure` -/
def measure : Cminor.State → Nat
  | .Callstate .. => 0
  | .State .. => 1
  | .Returnstate .. => 2

theorem lessdef_of_findFunct {F V : Type} {ge : Genv F V} {v v' : Val} {fd : F}
    (h : Genv.findFunct ge v = some fd) (hl : Val.Lessdef v v') : v' = v := by
  cases hl with
  | refl => rfl
  | undef => simp [Genv.findFunct] at h

theorem setOptvar_lessdef {e e' : Cminor.Env} {v v' : Val} (optid : Option Ident)
    (he : EnvLessdef e e') (hv : Val.Lessdef v v') :
    EnvLessdef (Cminor.setOptvar optid v e) (Cminor.setOptvar optid v' e') := by
  cases optid with
  | none => exact he
  | some id => exact set_var_lessdef he hv

/-- `Selectionproof.match_prog`: every function definition is translated by
`sel_fundef`, with the definitions map of some compilation unit `cu` of the
program and helper functions declared in `cu`. -/
def MatchProgLink (opts : Options) (p : Cminor.Program) (tp : CminorSel.Program) : Prop :=
  Linking.MatchProgramCtx
    (fun cu f tf => ∃ hf, SplitLongproof.helper_functions_declared cu hf ∧
      selFundef opts cu.defmap hf f = .OK tf) Eq p tp

/-- `Selectionproof.transf_program_match` -/
theorem transf_program_match {opts : Options} {p : Cminor.Program} {tp : CminorSel.Program}
    (h : selProgram opts p = .OK tp) : MatchProgLink opts p tp := by
  obtain ⟨hf, gh, htr⟩ := selProgram_inv h
  exact Linking.match_transform_partial_program_contextual _ htr
    (fun _ _ e => ⟨hf, get_helpers_correct gh, e⟩)

/-- `Selectionproof.TransfSelectionLink` -/
instance transfSelectionLink (opts : Options) : Linking.TransfLink (MatchProgLink opts) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := Linker.link_linkorder h
    refine Linking.link_match_program ?_ Linking.linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl ⟨hf1, d1, e1⟩ ⟨hf2, d2, e2⟩
    obtain ⟨tf, P, Q⟩ := Linking.link_transf_partial_astfundef _ _ hl e1 e2
    exact ⟨tf, P, Q.imp (fun q => ⟨hf1, d1, q⟩) (fun q => ⟨hf2, d2, q⟩)⟩

/-- The side condition on the compilation unit of a function frame: its
definitions map `dm` and helpers `hf` are those of a compilation unit of `prog`. -/
def AdmUnit (prog : Cminor.Program) (dm : PTree Globdef) (hf : SplitLong.HelperFunctions) :
    Prop :=
  ∃ cu : Cminor.Program, Linker.linkorder cu prog ∧ dm = cu.defmap ∧
    SplitLongproof.helper_functions_declared cu hf

section PRESERVATION
variable (opts : Options) (prog : Cminor.Program) (tprog : CminorSel.Program)
  (TRANSL : MatchProgLink opts prog tprog)

include TRANSL

/-- `Selectionproof.symbols_preserved` -/
theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  (Linking.MatchProgramGen.toMatchProgram TRANSL).find_symbol id

/-- `Selectionproof.senv_preserved` -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  (Linking.MatchProgramGen.toMatchProgram TRANSL).senv

/-- `Selectionproof.wt_prog` -/
theorem wt_prog : WtProgram prog := by
  intro i f hin
  obtain ⟨tf, _, _, hf, _, htf⟩ :=
    matchDefs_gfun (Linking.MatchProgramGen.toMatchProgram TRANSL).defs hin
  cases f with
  | External ef => exact .external ef
  | Internal f =>
    simp only [selFundef, ASTFundef.transfPartial] at htf
    split at htf
    · next f' hf' =>
      obtain ⟨env, _, h1, _, _⟩ := selFunction_inv hf'
      exact .internal env f (typeFunction_sound h1)
    · cases htf

variable (hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv))

/-- `Selectionproof.functions_translated` -/
theorem functions_translated {v : Val} {fd : Cminor.Fundef}
    (h : Genv.findFunct prog.globalenv v = some fd) :
    ∃ tf, ∃ cu : Cminor.Program, ∃ hf, Genv.findFunct tprog.globalenv v = some tf ∧
      selFundef opts cu.defmap hf fd = .OK tf ∧ AdmUnit prog cu.defmap hf := by
  obtain ⟨tf, A, cu, B, hf, D, C⟩ := (Linking.MatchProgramGen.toMatchProgram TRANSL).find_funct h
  exact ⟨tf, cu, hf, A, C, cu, B, rfl, D⟩

/-- `Selectionproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {fd : Cminor.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some fd) :
    ∃ tf, ∃ cu : Cminor.Program, ∃ hf, Genv.findFunctPtr tprog.globalenv b = some tf ∧
      selFundef opts cu.defmap hf fd = .OK tf ∧ AdmUnit prog cu.defmap hf := by
  obtain ⟨tf, A, cu, B, hf, D, C⟩ :=
    (Linking.MatchProgramGen.toMatchProgram TRANSL).find_funct_ptr h
  exact ⟨tf, cu, hf, A, C, cu, B, rfl, D⟩

local notation "MS" => MatchStates opts (AdmUnit prog) prog.globalenv

include hec in
/-- `Selectionproof.sel_step_correct` -/
theorem sel_step_correct {S1 : Cminor.State} {t : Trace} {S2 : Cminor.State}
    (hst : Cminor.Step prog.globalenv S1 t S2) {T1 : CminorSel.State} (hm : MS S1 T1)
    (hw : WtState S1) :
    (∃ T2, Smallstep.Plus (CminorSel.Step tprog.globalenv) T1 t T2 ∧ MS S2 T2) ∨
    (measure S2 < measure S1 ∧ t = E0 ∧ MS S2 T1) ∨
    (∃ T2 n, CminorSel.Step tprog.globalenv T1 t T2 ∧
      Eventually prog.globalenv n S2 (fun S3 => MS S3 T2)) := by
  have hsym := symbols_preserved opts prog tprog TRANSL
  have hsenv := senv_preserved opts prog tprog TRANSL
  cases hst with
  | skip_seq f s k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      cases MC with
      | seq _ _ _ kont0 s0 _ k0 hsel MC' =>
        exact .inl ⟨_, plus_one (.skip_seq _ _ _ _ _ _), .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF hsel MC' LD ME ADM⟩
      | other _ _ _ _ hc => cases hc
  | skip_block f k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      cases MC with
      | block _ _ _ k0 MC' =>
        exact .inl ⟨_, plus_one (.skip_block _ _ _ _ _), match_states_skip ADM TF TYF MC' LD ME⟩
      | other _ _ _ _ hc => cases hc
  | skip_call f k sp e m m2 hcc hfree =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      obtain ⟨m2', A, B⟩ := Mem.free_parallel_extends ME hfree
      obtain ⟨MCC, hcc'⟩ := match_is_call_cont MC hcc
      refine .inl ⟨_, plus_one (.skip_call _ _ _ _ _ _ hcc' ?_), .returnstate _ _ _ _ _ _ MCC (.refl _) B⟩
      rw [stackspace_function_translated TF]; exact A
  | assign f id a k sp e m v hev =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      obtain ⟨v', A, B⟩ := sel_expr_correct hsym opts hev LD ME (le := [])
      exact .inl ⟨_, plus_one (.assign _ _ _ _ _ _ _ _ A),
        match_states_skip ADM TF TYF MC (set_var_lessdef LD B) ME⟩
  | store f chunk addr a k sp e m vaddr v m2 h1 h2 h3 =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      obtain ⟨vaddr', A, B⟩ := sel_expr_correct hsym opts h1 LD ME (le := [])
      obtain ⟨v', C, D⟩ := sel_expr_correct hsym opts h2 LD ME (le := [])
      obtain ⟨m2', P, Q⟩ := Mem.storev_extends ME h3 B D
      exact .inl ⟨_, plus_one (eval_store opts A C P), match_states_skip ADM TF TYF MC LD Q⟩
  | call f optid sig a bl k sp e m vf vargs fd hev hevl hfd hsig =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      obtain ⟨cu, LINK, hdm, _⟩ := id ADM
      subst hdm
      have CC := classify_call_correct prog LINK hev hfd
      simp only [selStmt] at TS
      obtain ⟨vargs', C, D⟩ := sel_exprlist_correct hsym opts hevl LD ME (le := [])
      rcases hcl : classifyCall cu.defmap a with _ | id | ef <;> rw [hcl] at CC TS <;> cases TS
      · obtain ⟨vf', A, B⟩ := sel_expr_correct hsym opts hev LD ME (le := [])
        cases lessdef_of_findFunct hfd B
        obtain ⟨tf, cu', hf', U, V, ADM'⟩ := functions_translated opts prog tprog TRANSL hfd
        refine .inl ⟨_, plus_one (.call _ _ _ _ _ _ _ _ _ _ _ tf (.e _ _ _ A) C U
          (by rw [sig_function_translated V]; exact hsig)), ?_⟩
        exact .callstate _ _ _ _ _ _ _ _ V (.call _ _ _ _ _ _ _ _ _ TF TYF MC LD ADM) D ME ADM'
      · obtain ⟨b, U0, rfl⟩ := CC
        obtain ⟨tf, cu', hf', U, V, ADM'⟩ := functions_translated opts prog tprog TRANSL hfd
        refine .inl ⟨_, plus_one (.call _ _ _ _ _ _ _ _ _ _ _ tf (.s _ _ _ (by rw [hsym]; exact U0)) C U
          (by rw [sig_function_translated V]; exact hsig)), ?_⟩
        exact .callstate _ _ _ _ _ _ _ _ V (.call _ _ _ _ _ _ _ _ _ TF TYF MC LD ADM) D ME ADM'
      · subst CC
        exact .inr (.inl ⟨(by show 0 < 1; decide), rfl, .builtin_1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF MC hevl LD ME ADM⟩)
  | tailcall f sig a bl k sp e m vf vargs fd m2 hev hevl hfd hsig hfree =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      obtain ⟨cu, LINK, hdm, _⟩ := id ADM
      subst hdm
      have CC := classify_call_correct prog LINK hev hfd
      obtain ⟨m2', P, Q⟩ := Mem.free_parallel_extends ME hfree
      rw [← stackspace_function_translated TF] at P
      obtain ⟨vf', A, B⟩ := sel_expr_correct hsym opts hev LD ME (le := [])
      cases lessdef_of_findFunct hfd B
      obtain ⟨vargs', C, D⟩ := sel_exprlist_correct hsym opts hevl LD ME (le := [])
      obtain ⟨tf, cu', hf', U, V, ADM'⟩ := functions_translated opts prog tprog TRANSL hfd
      have hsig' : CminorSel.funsig tf = sig := by rw [sig_function_translated V]; exact hsig
      have MCC := call_cont_commut MC
      simp only [selStmt] at TS
      rcases hcl : classifyCall cu.defmap a with _ | id | ef <;> rw [hcl] at CC TS <;> cases TS
      · exact .inl ⟨_, plus_one (.tailcall _ _ _ _ _ _ _ _ _ _ tf _ (.e _ _ _ A) C U hsig' P),
          .callstate _ _ _ _ _ _ _ _ V MCC D Q ADM'⟩
      · obtain ⟨b, U0, hb⟩ := CC
        subst hb
        exact .inl ⟨_, plus_one (.tailcall _ _ _ _ _ _ _ _ _ _ tf _
          (.s _ _ _ (by rw [hsym]; exact U0)) C U hsig' P), .callstate _ _ _ _ _ _ _ _ V MCC D Q ADM'⟩
      · exact .inl ⟨_, plus_one (.tailcall _ _ _ _ _ _ _ _ _ _ tf _ (.e _ _ _ A) C U hsig' P),
          .callstate _ _ _ _ _ _ _ _ V MCC D Q ADM'⟩
  | builtin f optid ef bl k sp e m vargs t vres m2 hevl hx =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      obtain ⟨e2', m2', P, Q, R⟩ := sel_builtin_correct (f := f') (k := k') hsym opts hsenv hec
        hevl hx LD ME
      exact .inl ⟨_, P, match_states_skip ADM TF TYF MC Q R⟩
  | seq f s1 s2 k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS
      obtain ⟨x, hx, TS⟩ := res_bind_ok.mp TS
      obtain ⟨x0, hx0, TS⟩ := res_bind_ok.mp TS
      cases TS
      exact .inl ⟨_, plus_one (.seq _ _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF hx0 (.seq _ _ _ _ _ _ _ hx MC) LD ME ADM⟩
  | ifthenelse f a s1 s2 k sp e m v b hev hbv =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS
      split at TS
      · next s0 hifc =>
        cases TS
        cases hw with
        | normal _ _ _ _ _ _ env0 WF WS WK WE DE =>
          have := WF.type_ok
          rw [TYF] at this; cases this
          cases WS with
          | Sifthenelse _ _ _ _ hw1 hw2 =>
            obtain ⟨n, e1, e1', A, B, C⟩ := if_conversion_correct (f' := f') (k' := k') hsym opts
              hifc DE WE hw1 hw2 hev hbv LD ME
            refine .inr (.inr ⟨_, n, A, eventually_implies B ?_⟩)
            rintro S3 ⟨e2, heq, rfl⟩
            exact match_states_skip ADM TF TYF MC (heq.lessdef C) ME
      · obtain ⟨x, hx, TS⟩ := res_bind_ok.mp TS
        obtain ⟨x0, hx0, TS⟩ := res_bind_ok.mp TS
        cases TS
        obtain ⟨v', A, B⟩ := sel_expr_correct hsym opts hev LD ME (le := [])
        have hv' : v' = v := by
          cases B with
          | refl => rfl
          | undef => cases hbv
        subst hv'
        refine .inl ⟨_, plus_one (.ifthenelse _ _ _ _ _ _ _ _ _ (eval_condexpr_of_expr _ A hbv)), ?_⟩
        cases b
        · exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF hx0 MC LD ME ADM
        · exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF hx MC LD ME ADM
  | loop f s k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS
      obtain ⟨x, hx, TS⟩ := res_bind_ok.mp TS
      cases TS
      refine .inl ⟨_, plus_one (.loop _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF hx (.seq _ _ _ .Sskip _ _ _ ?_ MC) LD ME ADM⟩
      simp only [selStmt, hx]; rfl
  | block f s k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS
      obtain ⟨x, hx, TS⟩ := res_bind_ok.mp TS
      cases TS
      exact .inl ⟨_, plus_one (.block _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF hx (.block _ _ _ _ MC) LD ME ADM⟩
  | exit_seq f n s k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      cases MC with
      | seq _ _ _ kont0 s0 _ k0 hsel MC' =>
        exact .inl ⟨_, plus_one (.exit_seq _ _ _ _ _ _ _),
          .state _ _ _ .Sskip _ _ _ _ _ _ _ _ _ TF TYF rfl MC' LD ME ADM⟩
      | other _ _ _ _ hc => cases hc
  | exit_block_0 f k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      cases MC with
      | block _ _ _ k0 MC' =>
        exact .inl ⟨_, plus_one (.exit_block_0 _ _ _ _ _), match_states_skip ADM TF TYF MC' LD ME⟩
      | other _ _ _ _ hc => cases hc
  | exit_block_S f n k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      cases MC with
      | block _ _ _ k0 MC' =>
        exact .inl ⟨_, plus_one (.exit_block_S _ _ _ _ _ _),
          .state _ _ _ .Sskip _ _ _ _ _ _ _ _ _ TF TYF rfl MC' LD ME ADM⟩
      | other _ _ _ _ hc => cases hc
  | switch f islong a cases default k sp e m v n hev hsa =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      cases hsa with
      | arg32 i =>
        simp only [selStmt] at TS
        split at TS
        · next hval =>
          cases TS
          obtain ⟨v', A, B⟩ := sel_expr_correct hsym opts hev LD ME (le := [])
          cases B
          exact .inl ⟨_, plus_one (.switch _ _ _ _ _ _ _ (sel_switch_int_correct hval A)),
            .state _ _ _ .Sskip _ _ _ _ _ _ _ _ _ TF TYF rfl MC LD ME ADM⟩
        · cases TS
      | arg64 i =>
        simp only [selStmt] at TS
        split at TS
        · next hval =>
          cases TS
          obtain ⟨v', A, B⟩ := sel_expr_correct hsym opts hev LD ME (le := [])
          cases B
          exact .inl ⟨_, plus_one (.switch _ _ _ _ _ _ _ (sel_switch_long_correct hval A)),
            .state _ _ _ .Sskip _ _ _ _ _ _ _ _ _ TF TYF rfl MC LD ME ADM⟩
        · cases TS
  | return_0 f k sp e m m2 hfree =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      obtain ⟨m2', P, Q⟩ := Mem.free_parallel_extends ME hfree
      rw [← stackspace_function_translated TF] at P
      exact .inl ⟨_, plus_one (.return_0 _ _ _ _ _ _ P),
        .returnstate _ _ _ _ _ _ (call_cont_commut MC) (.refl _) Q⟩
  | return_1 f a k sp e m v m2 hev hfree =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      obtain ⟨m2', P, Q⟩ := Mem.free_parallel_extends ME hfree
      rw [← stackspace_function_translated TF] at P
      obtain ⟨v', A, B⟩ := sel_expr_correct hsym opts hev LD ME (le := [])
      exact .inl ⟨_, plus_one (.return_1 _ _ _ _ _ _ _ _ A P),
        .returnstate _ _ _ _ _ _ (call_cont_commut MC) B Q⟩
  | label f lbl s k sp e m =>
    cases hm with
    | state _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS
      obtain ⟨x, hx, TS⟩ := res_bind_ok.mp TS
      cases TS
      exact .inl ⟨_, plus_one (.label _ _ _ _ _ _ _),
        .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF hx MC LD ME ADM⟩
  | goto f lbl k sp e m s1 k1 hfl =>
    cases hm with
    | @state _ hf0 _ f' _ kont _ s' k' _ _ _ e' m' env TF TYF TS MC LD ME ADM =>
      simp only [selStmt] at TS; cases TS
      have FL := find_label_commut lbl f.fn_body (.other (hf := hf0) _ _ _ _ (call_cont_commut MC))
        (body_function_translated TF TYF)
      rw [hfl] at FL
      generalize hfl' : CminorSel.findLabel lbl f'.fn_body (CminorSel.callCont k') = o at FL
      cases FL with
      | some _ _ s1' k1' kont1 h1 h2 =>
        exact .inl ⟨_, plus_one (.goto _ _ _ _ _ _ _ _ hfl'),
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF h1 h2 LD ME ADM⟩
  | internal_function f vargs k m m2 sp e htyp halloc hset =>
    cases hm with
    | callstate _ tf _ args' _ k' _ m' TF MCC LD ME ADM =>
      simp only [selFundef, ASTFundef.transfPartial] at TF
      split at TF
      · next f' TF' =>
        cases TF
        obtain ⟨env, body, TYF, hbody, hf'⟩ := selFunction_inv TF'
        obtain ⟨m2', A, B⟩ := Mem.alloc_extends ME halloc (Int.le_refl _) (Int.le_refl _)
        subst hf'
        refine .inl ⟨_, plus_one (.internal_function _ _ _ _ _ _ _
          (Val.has_argtype_list_lessdef htyp LD) A rfl), ?_⟩
        subst hset
        exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ TF' TYF hbody (.other _ _ _ _ MCC)
          (set_locals_lessdef (set_params_lessdef _ LD) _) B ADM
      · cases TF
  | external_function ef vargs k m t vres m2 hx =>
    cases hm with
    | callstate _ tf _ args' _ k' _ m' TF MCC LD ME ADM =>
      simp only [selFundef, ASTFundef.transfPartial] at TF
      cases TF
      obtain ⟨vres', m2', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hx ME LD
      exact .inl ⟨_, plus_one (.external_function _ _ _ _ _ _ _ (by rw [hsenv]; exact A)),
        .returnstate _ _ _ _ _ _ MCC B C⟩
    | builtin_1 _ _ optid f sp e k0 _ al f' e' k' m' env TF TYF MC hevl LD ME ADM =>
      obtain ⟨e2', m2', P, Q, R⟩ := sel_builtin_correct (f := f') (k := k') hsym opts hsenv hec
        hevl hx LD ME
      exact .inl ⟨_, P, .builtin_2 _ _ _ _ _ _ _ _ _ _ _ _ _ TF TYF MC (.refl _) Q R ADM⟩
  | «return» v optid f sp e k m =>
    cases hm with
    | returnstate _ v' _ k' _ m' MCC LD ME =>
      cases MCC with
      | call env _ _ _ _ _ f' e' k'' TF TYF MC LDe ADM =>
        exact .inl ⟨_, plus_one (.return _ _ _ _ _ _ _),
          match_states_skip ADM TF TYF MC (setOptvar_lessdef optid LDe LD) ME⟩
    | builtin_2 _ v' _ _ _ _ _ _ f' e' m' k' env TF TYF MC LDv LDe ME ADM =>
      exact .inr (.inl ⟨(by show 1 < 2; decide), rfl, match_states_skip ADM TF TYF MC LDe ME⟩)

/-- `Selectionproof.sel_initial_states` -/
theorem sel_initial_states {S : Cminor.State} (h : Cminor.InitialState prog S) :
    ∃ R, CminorSel.InitialState tprog R ∧ MS S R := by
  cases h with
  | intro b f m0 hinit hmain hfp hsig =>
    obtain ⟨tf, cu, hf, A, B, ADM⟩ := function_ptr_translated opts prog tprog TRANSL hfp
    refine ⟨_, .intro b tf m0 ?_ ?_ A ?_,
      .callstate _ _ _ _ _ _ _ _ B .stop .nil (Mem.extends_refl m0) ADM⟩
    · rw [(Linking.MatchProgramGen.toMatchProgram TRANSL).init_mem]; exact hinit
    · rw [TRANSL.main_eq, symbols_preserved opts prog tprog TRANSL]
      exact hmain
    · rw [sig_function_translated B]; exact hsig

omit TRANSL in
/-- `Selectionproof.sel_final_states` -/
theorem sel_final_states {S : Cminor.State} {R : CminorSel.State} {r : Integers.Int}
    (hm : MS S R) (h : Cminor.FinalState S r) : CminorSel.FinalState R r := by
  cases h with
  | intro r m =>
    cases hm with
    | returnstate _ _ _ _ _ _ MCC LD _ =>
      cases MCC
      cases LD
      exact .intro _ _

end PRESERVATION

/-- `Selectionproof.transf_program_correct`: instruction selection preserves the semantics
of Cminor programs (forward simulation from Cminor to CminorSel), for any pair of programs
related by the linking-aware `match_prog`.

The hypotheses are CompCert's axioms on the uninterpreted external functions and inline
assembly (compatibility with memory extensions, `ec_mem_extends`, and well-typedness of
their results, `external_call_well_typed`). -/
theorem transf_program_correct_match (opts : Options) (prog : Cminor.Program)
    (tprog : CminorSel.Program) (TRANSL : MatchProgLink opts prog tprog)
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ForwardSimulation (Cminor.semantics prog) (CminorSel.semantics tprog) := by
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  have WTP := wt_prog opts prog tprog TRANSL
  refine forward_simulation_eventually_star (L1 := Cminor.semantics prog)
    (L2 := CminorSel.semantics tprog)
    (fun S T => MatchStates opts (AdmUnit prog) prog.globalenv S T ∧ WtState S) ?_ ?_ ?_ measure ?_
  · intro id
    show (Genv.toSenv tprog.globalenv).public_symbol id =
      (Genv.toSenv prog.globalenv).public_symbol id
    rw [senv_preserved opts prog tprog TRANSL]
  · intro S hS
    obtain ⟨T, P, Q⟩ := sel_initial_states opts prog tprog TRANSL hS
    exact ⟨T, P, Q, wt_initial_state prog WTP hS⟩
  · intro S T r ⟨M, _⟩ hfin
    exact sel_final_states opts prog M hfin
  · intro S1 t S2 hst T1 ⟨M, W1⟩
    have W2 := subject_reduction prog WTP hextw hasmw hst W1
    rcases sel_step_correct opts prog tprog TRANSL hec hst M W1 with
      ⟨T2, D, E⟩ | ⟨D, E, F⟩ | ⟨T2, n, D, E⟩
    · exact .inl ⟨T2, .inl D, E, W2⟩
    · subst E
      exact .inl ⟨T1, .inr ⟨.refl _, D⟩, F, W2⟩
    · exact .inr ⟨n, T2, plus_one D,
        eventually_and_invariant WtState
          (fun _ _ _ h w => subject_reduction prog WTP hextw hasmw h w) E W2⟩

/-- `Selectionproof.transf_program_correct` for the output of `sel_program`. -/
theorem transf_program_correct (opts : Options) (prog : Cminor.Program)
    (tprog : CminorSel.Program) (htp : selProgram opts prog = .OK tprog)
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ForwardSimulation (Cminor.semantics prog) (CminorSel.semantics tprog) :=
  transf_program_correct_match opts prog tprog (transf_program_match htp) hext hasm hextw hasmw

end Selectionproof
end CC
