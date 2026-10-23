/-
  Simplification of expressions (CompCert C → Clight): separate compilation —
  the linking part of `cfrontend/SimplExprproof.v` (`match_prog`,
  `transf_program_match`, `TransfSimplExprLink`) and the semantic
  preservation theorem stated for `match_prog`.

  Difference from Rocq: CompCert proves the simulation directly for
  `match_prog`, where each function satisfies `tr_function` for the
  composite environment of its own compilation unit.  Here the simulation
  proof of `SimplExprproofStep` is reused for the relational hypothesis
  "every function satisfies `tr_fundef` for the linked program"
  (`transl_program_correct_gen`): the specification depends on the
  composite environment only through `tr_is_bitfield_access`, which is
  stable under extension of the environment (`tr_function_stable`).
-/
import CCLib.cfrontend.SimplExprproofStep
import CCLib.cfrontend.CsyntaxLinking
import CCLib.cfrontend.CshmgenproofLink

namespace CC
namespace SimplExpr

open CtypesLinking Smallstep Destination SetDestination

/-! ## Stability of the specification under extension of the composite environment -/

section STABLE
variable {ce ce' : CompositeEnv} (hext : EnvExtends ce ce') (hcons : EnvConsistent ce)
include hext hcons

theorem bf_stable {a : Expr} {bf : Bitfield} (h : TrIsBitfieldAccess ce a bf) :
    TrIsBitfieldAccess ce' a bf := by
  cases a with
  | Efield r f ty =>
    simp only [TrIsBitfieldAccess] at h ⊢
    obtain ⟨co, ofs, hh⟩ := h
    refine ⟨co, ofs, ?_⟩
    revert hh
    generalize typeof r = t
    cases t with
    | Tstruct id _ =>
      rintro ⟨hco, hfo⟩
      refine ⟨hext id co hco, ?_⟩
      unfold fieldOffset at hfo ⊢
      rw [Cshmgen.fieldOffsetRec_stable hext f _ _ (hcons id co hco).complete]
      exact hfo
    | Tunion id _ =>
      rintro ⟨hco, hfo⟩
      refine ⟨hext id co hco, ?_⟩
      rw [Cshmgen.unionFieldOffset_stable hext f _ (hcons id co hco).complete]
      exact hfo
    | _ => exact id
  | _ => exact h

theorem tr_rvalof_stable {ty a sl b tmps} (h : TrRvalof ce ty a sl b tmps) :
    TrRvalof ce' ty a sl b tmps := by
  match h with
  | .tr_rvalof_nonvol _ _ _ hv => exact .tr_rvalof_nonvol _ _ _ hv
  | .tr_rvalof_vol _ _ _ _ _ hv hin hbf =>
    exact .tr_rvalof_vol _ _ _ _ _ hv hin (bf_stable hext hcons hbf)

mutual
theorem tr_expr_stable {le dst r sl a tmps} (h : TrExpr ce le dst r sl a tmps) :
    TrExpr ce' le dst r sl a tmps := by
  match h with
  | .tr_var .. => exact .tr_var ..
  | .tr_deref _ _ _ _ _ _ _ h1 => exact .tr_deref _ _ _ _ _ _ _ (tr_expr_stable h1)
  | .tr_field _ _ _ _ _ _ _ _ h1 => exact .tr_field _ _ _ _ _ _ _ _ (tr_expr_stable h1)
  | .tr_val_effect .. => exact .tr_val_effect ..
  | .tr_val_value _ _ _ _ _ hty hev => exact .tr_val_value _ _ _ _ _ hty hev
  | .tr_val_set _ _ _ _ _ _ _ hty hev => exact .tr_val_set _ _ _ _ _ _ _ hty hev
  | .tr_sizeof .. => exact .tr_sizeof ..
  | .tr_alignof .. => exact .tr_alignof ..
  | .tr_valof _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_valof _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1) (tr_rvalof_stable hext hcons h2) h3 h4 h5
  | .tr_addrof _ _ _ _ _ _ _ h1 => exact .tr_addrof _ _ _ _ _ _ _ (tr_expr_stable h1)
  | .tr_unop _ _ _ _ _ _ _ _ h1 => exact .tr_unop _ _ _ _ _ _ _ _ (tr_expr_stable h1)
  | .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1)
      (tr_expr_stable h2) h3 h4 h5
  | .tr_cast_effects _ _ _ _ _ _ _ h1 => exact .tr_cast_effects _ _ _ _ _ _ _ (tr_expr_stable h1)
  | .tr_cast_val _ _ _ _ _ _ _ h1 => exact .tr_cast_val _ _ _ _ _ _ _ (tr_expr_stable h1)
  | .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1)
      (tr_expr_stable h2) h3 h4 h5 h6
  | .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1)
      (tr_expr_stable h2) h3 h4 h5
  | .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1)
      (tr_expr_stable h2) h3 h4 h5 h6
  | .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1)
      (tr_expr_stable h2) h3 h4 h5 h6
  | .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1)
      (tr_expr_stable h2) h3 h4 h5
  | .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1)
      (tr_expr_stable h2) h3 h4 h5 h6
  | .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      (tr_expr_stable h3) h4 h5 h6 h7 h8 h9
  | .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      (tr_expr_stable h3) h4 h5 h6 h7 h8
  | .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      (tr_expr_stable h3) h4 h5 h6 h7 h8 h9
  | .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      h3 h4 h5 (bf_stable hext hcons h6)
  | .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact .tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      h3 h4 h5 h6 h7 h8 h9 h10 (bf_stable hext hcons h11)
  | .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact .tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      h3 (tr_rvalof_stable hext hcons h4) h5 h6 h7 h8 h9 h10 (bf_stable hext hcons h11)
  | .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 =>
    exact .tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      (tr_rvalof_stable hext hcons h3) h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 (bf_stable hext hcons h15)
  | .tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
    exact .tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_rvalof_stable hext hcons h2) h3 h4 h5 h6 (bf_stable hext hcons h7)
  | .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    exact .tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) h2 h3 h4 h5 (bf_stable hext hcons h6)
  | .tr_comma _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_comma _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_expr_stable h2)
      h3 h4 h5
  | .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _
      (tr_expr_stable h1) (tr_exprlist_stable h2)
      h3 h4 h5
  | .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 =>
    exact .tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ h0
      (tr_expr_stable h1) (tr_exprlist_stable h2)
      h3 h4 h5 h6
  | .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ (tr_exprlist_stable h1) h2
  | .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 =>
    exact .tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ h0
      (tr_exprlist_stable h1) h2 h3
  | .tr_paren_val _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_paren_val _ _ _ _ _ _ _ _ (tr_expr_stable h1) h2
  | .tr_paren_effects _ _ _ _ _ _ _ _ h1 =>
    exact .tr_paren_effects _ _ _ _ _ _ _ _ (tr_expr_stable h1)
  | .tr_paren_set _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    exact .tr_paren_set _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1) h2

theorem tr_exprlist_stable {le rl sl al tmps} (h : TrExprlist ce le rl sl al tmps) :
    TrExprlist ce' le rl sl al tmps := by
  match h with
  | .tr_nil .. => exact .tr_nil ..
  | .tr_cons _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_cons _ _ _ _ _ _ _ _ _ _ (tr_expr_stable h1) (tr_exprlist_stable h2) h3 h4 h5
end

theorem tr_top_stable {ge e le m dst r sl a tmps} (h : TrTop ce ge e le m dst r sl a tmps) :
    TrTop ce' ge e le m dst r sl a tmps := by
  cases h with
  | tr_top_val_val v ty a tmp h1 h2 => exact .tr_top_val_val _ _ _ _ h1 h2
  | tr_top_base dst r sl a tmp h1 => exact .tr_top_base _ _ _ _ _ (tr_expr_stable hext hcons h1)

theorem tr_expression_stable {r s a} (h : TrExpression ce r s a) : TrExpression ce' r s a := by
  match h with
  | .tr_expression_intro _ _ _ _ h =>
    exact .tr_expression_intro _ _ _ _ (fun ge e le m => tr_top_stable hext hcons (h ge e le m))

theorem tr_expr_stmt_stable {r s} (h : TrExprStmt ce r s) : TrExprStmt ce' r s := by
  match h with
  | .tr_expr_stmt_intro _ _ _ _ h =>
    exact .tr_expr_stmt_intro _ _ _ _ (fun ge e le m => tr_top_stable hext hcons (h ge e le m))

theorem tr_if_stable {r s1 s2 s} (h : TrIf ce r s1 s2 s) : TrIf ce' r s1 s2 s := by
  match h with
  | .tr_if_intro _ _ _ _ _ _ h =>
    exact .tr_if_intro _ _ _ _ _ _ (fun ge e le m => tr_top_stable hext hcons (h ge e le m))

mutual
theorem tr_stmt_stable {s ts} (h : TrStmt ce s ts) : TrStmt ce' s ts := by
  match h with
  | .tr_skip => exact .tr_skip
  | .tr_do _ _ h1 => exact .tr_do _ _ (tr_expr_stmt_stable hext hcons h1)
  | .tr_seq _ _ _ _ h1 h2 => exact .tr_seq _ _ _ _ (tr_stmt_stable h1) (tr_stmt_stable h2)
  | .tr_ifthenelse_empty _ _ _ h1 =>
    exact .tr_ifthenelse_empty _ _ _ (tr_expression_stable hext hcons h1)
  | .tr_ifthenelse _ _ _ _ _ _ _ h1 h2 h3 =>
    exact .tr_ifthenelse _ _ _ _ _ _ _ (tr_expression_stable hext hcons h1) (tr_stmt_stable h2)
      (tr_stmt_stable h3)
  | .tr_while _ _ _ _ h1 h2 => exact .tr_while _ _ _ _ (tr_if_stable hext hcons h1) (tr_stmt_stable h2)
  | .tr_dowhile _ _ _ _ h1 h2 =>
    exact .tr_dowhile _ _ _ _ (tr_if_stable hext hcons h1) (tr_stmt_stable h2)
  | .tr_for_1 _ _ _ _ _ _ h1 h2 h3 =>
    exact .tr_for_1 _ _ _ _ _ _ (tr_if_stable hext hcons h1) (tr_stmt_stable h2) (tr_stmt_stable h3)
  | .tr_for_2 _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    exact .tr_for_2 _ _ _ _ _ _ _ _ (tr_if_stable hext hcons h1) h2 (tr_stmt_stable h3)
      (tr_stmt_stable h4) (tr_stmt_stable h5)
  | .tr_break => exact .tr_break
  | .tr_continue => exact .tr_continue
  | .tr_return_none => exact .tr_return_none
  | .tr_return_some _ _ _ h1 => exact .tr_return_some _ _ _ (tr_expression_stable hext hcons h1)
  | .tr_switch _ _ _ _ _ h1 h2 =>
    exact .tr_switch _ _ _ _ _ (tr_expression_stable hext hcons h1) (tr_lblstmts_stable h2)
  | .tr_label _ _ _ h1 => exact .tr_label _ _ _ (tr_stmt_stable h1)
  | .tr_goto _ => exact .tr_goto _

theorem tr_lblstmts_stable {ls tls} (h : TrLblstmts ce ls tls) : TrLblstmts ce' ls tls := by
  match h with
  | .tr_ls_nil => exact .tr_ls_nil
  | .tr_ls_cons _ _ _ _ _ h1 h2 => exact .tr_ls_cons _ _ _ _ _ (tr_stmt_stable h1) (tr_lblstmts_stable h2)
end

/-- A function satisfying `tr_function` for the composite environment `ce`
    satisfies it for any extension `ce'` of `ce`. -/
theorem tr_function_stable {f tf} (h : TrFunction ce f tf) : TrFunction ce' f tf := by
  match h with
  | .tr_function_intro _ _ h1 h2 h3 h4 h5 =>
    exact .tr_function_intro _ _ (tr_stmt_stable hext hcons h1) h2 h3 h4 h5

end STABLE

theorem trFundef_stable {cu p : Csyntax.Program} (hl : Linker.linkorder cu p) {f tf}
    (h : TrFundef cu f tf) : TrFundef p f tf := by
  cases h with
  | tr_internal f tf h1 =>
    exact .tr_internal _ _ (tr_function_stable hl.2
      (fun _ _ hco => buildCompositeEnv_consistent cu.prog_comp_env_eq hco) h1)
  | tr_external ef targs tres cc => exact .tr_external _ _ _ _

/-! ## Semantic preservation for the relational specification -/

section GEN
variable {prog : Csyntax.Program} {tprog : Program}
  (TR : MatchProgram (fun f tf => TrFundef prog f tf) Eq prog.toAST tprog.toAST)
  (CE : tprog.prog_comp_env = prog.prog_comp_env)

include TR CE in
theorem genvRel_of_match : GenvRel (Csem.globalenv prog) tprog.globalenv :=
  ⟨fun s => TR.find_symbol s, TR.senv, CE⟩

include TR in
theorem funsTranslated_of_match : FunsTranslated prog tprog.globalenv :=
  fun _ _ h => TR.find_funct h

include TR in
theorem transl_initial_states_match {S : Csem.State} (h : Csem.InitialState prog S) :
    ∃ S', InitialState tprog S' ∧ MatchStates prog tprog.globalenv S S' := by
  cases h with
  | intro b f m0 hm hs hf ht =>
  obtain ⟨tf, A, B⟩ := TR.find_funct_ptr hf
  refine ⟨_, .intro b tf m0 ?_ ?_ A (by rw [type_of_fundef_preserved B]; exact ht),
    .callstates _ _ _ _ _ _ B .Kstop⟩
  · rw [Program.initMem_toAST, TR.init_mem]; exact hm
  · have hmain : tprog.prog_main = prog.prog_main := TR.main_eq
    rw [hmain]; exact (TR.find_symbol prog.prog_main).trans hs

include TR CE in
/-- `SimplExprproof.transl_program_correct`, for any Clight program whose
    functions satisfy the relational specification `tr_fundef` and whose
    composite environment is that of the source. -/
theorem transl_program_correct_gen :
    ForwardSimulation (Cstrategy.semantics prog) (Clight.semantics1 tprog) :=
  forward_simulation_star_wf (L1 := Cstrategy.semantics prog) (L2 := Clight.semantics1 tprog)
    (MatchStates prog tprog.globalenv)
    (fun id => by
      show (Genv.toSenv tprog.globalenv.genv_genv).public_symbol id = _
      rw [(genvRel_of_match TR CE).senv]; rfl)
    (fun _ h => transl_initial_states_match TR h)
    (fun _ _ _ hm h => transl_final_states hm h)
    (fun x y => measure x < measure y) (InvImage.wf measure Nat.lt_wfRel.wf)
    (fun _ _ _ hst _ hm =>
      simulation (genvRel_of_match TR CE) (funsTranslated_of_match TR) hst hm)

end GEN

/-! ## `match_prog` and linking -/

/-- `SimplExprproof.match_prog` -/
def MatchProgLink (p : Csyntax.Program) (tp : WFProgram) : Prop :=
  Linking.MatchProgramGen (fun (cu : Csyntax.Program) f tf => TrFundef cu f tf) Eq p p.toAST
    tp.toAST ∧ tp.val.prog_types = p.prog_types

/-- `SimplExprproof.transf_program_match` -/
theorem transf_program_match_link {fu : Ident} {p : Csyntax.Program} {tp : WFProgram}
    (h : translProgram fu p = .OK tp.val) : MatchProgLink p tp := by
  unfold translProgram at h
  split at h
  · cases h
  · rename_i p1 hp1
    have e := Res.OK.inj h
    refine ⟨?_, by rw [← e]⟩
    show Linking.MatchProgramGen _ Eq p p.toAST tp.val.toAST
    rw [← e]
    have hm := CC.match_transform_partial_program hp1
    exact ⟨Linking.forall2_of_matchDefs (fun _ _ e => transl_fundef_spec e) (fun _ _ e => e)
      hm.defs, hm.main_eq, hm.public_eq⟩

/-- `Linking.link_match_fundef` for `SimplExprspec.tr_fundef`. -/
theorem link_trFundef :
    Linking.LinkMatchFundef (fun (cu : Csyntax.Program) f tf => TrFundef cu f tf) := by
  intro c1 c2 f1 tf1 f2 tf2 f h m1 m2
  change Linking.linkFundef f1 f2 = some f at h
  cases m1 with
  | tr_internal g1 tg1 e1 =>
    cases m2 with
    | tr_internal => simp [Linking.linkFundef] at h
    | tr_external ef targs tres cc =>
      cases ef <;> simp [Linking.linkFundef] at h
      subst h
      exact ⟨.Internal tg1, rfl, .inl (.tr_internal _ _ e1)⟩
  | tr_external ef targs tres cc =>
    cases m2 with
    | tr_internal g2 tg2 e2 =>
      cases ef <;> simp [Linking.linkFundef] at h
      subst h
      exact ⟨.Internal tg2, rfl, .inr (.tr_internal _ _ e2)⟩
    | tr_external ef2 targs2 tres2 cc2 =>
      simp only [Linking.linkFundef] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        cases h
        refine ⟨.External ef targs tres cc, ?_, .inl (.tr_external _ _ _ _)⟩
        change CtypesLinking.linkFundef _ _ = _
        simp [CtypesLinking.linkFundef]
      · cases h

/-- `SimplExprproof.link_match_program` (`TransfSimplExprLink`) -/
theorem link_match_program {p1 p2 p : Csyntax.Program} {tp1 tp2 : WFProgram}
    (h : Linker.link p1 p2 = some p) (m1 : MatchProgLink p1 tp1) (m2 : MatchProgLink p2 tp2) :
    ∃ tp, Linker.link tp1 tp2 = some tp ∧ MatchProgLink p tp := by
  obtain ⟨lo1, lo2⟩ := Linker.link_linkorder h
  obtain ⟨pp, typs, hpp, ht, hpa, hpt⟩ := linkCProgram_inv h
  obtain ⟨tpp, htpp, hm⟩ :=
    Linking.link_match_program link_trFundef Linking.linkMatchVarinfo_eq hpp m1.1 m2.1 lo1 lo2
  have ht' : Linker.link tp1.val.prog_types tp2.val.prog_types = some typs := by
    rw [m1.2, m2.2]; exact ht
  obtain ⟨tp, htp, htpa, htpt⟩ := linkProgram_succeeds htpp ht'
  refine ⟨tp, htp, ?_, ?_⟩
  · rw [htpa, hpa]; exact hm
  · rw [htpt, hpt]

/-- `SimplExprproof.TransfSimplExprLink` -/
instance transfSimplExprLink : Linking.TransfLink MatchProgLink where
  transf_link h m1 m2 := link_match_program h m1 m2

/-- `match_prog` implies the whole-program relational specification. -/
theorem matchProgram_of_link {p : Csyntax.Program} {tp : WFProgram} (h : MatchProgLink p tp) :
    MatchProgram (fun f tf => TrFundef p f tf) Eq p.toAST tp.val.toAST := by
  have h' := Linking.MatchProgramGen.toMatchProgram h.1
  exact ⟨Genv.MatchDefs.imp (fun f tf ⟨cu, hl, e⟩ => trFundef_stable hl e) (fun _ _ e => e) h'.defs,
    h'.main_eq, h'.public_eq⟩

theorem comp_env_of_link {p : Csyntax.Program} {tp : WFProgram} (h : MatchProgLink p tp) :
    tp.val.prog_comp_env = p.prog_comp_env := by
  have h1 := tp.property
  rw [h.2, p.prog_comp_env_eq] at h1
  exact (Res.OK.inj h1).symm

/-- `SimplExprproof.transl_program_correct`, for `match_prog`. -/
theorem transl_program_correct_match {p : Csyntax.Program} {tp : WFProgram}
    (h : MatchProgLink p tp) :
    ForwardSimulation (Cstrategy.semantics p) (Clight.semantics1 tp.val) :=
  transl_program_correct_gen (matchProgram_of_link h) (comp_env_of_link h)

end SimplExpr
end CC
