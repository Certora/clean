/-
  [RISC-V instance of `CCLib/backend/RTLgenproofMain.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness of RTL generation — port of `backend/RTLgenproof.v`, part 5:
  the simulation diagram for statements and functions
  (`transl_step_correct`), `transl_initial_states`, `transl_final_states`
  and the main theorem `transf_program_correct`.
-/
import CCLib.riscV.RTLgenproofMatch

namespace CC
namespace RiscV
namespace RTLgen

open Op CminorSel Smallstep

theorem lessdef_findFunct {F V : Type} {ge : Genv F V} {v v' : Val} {f : F}
    (h : Val.Lessdef v v') (hf : Genv.findFunct ge v = some f) : v' = v := by
  cases h with
  | refl => rfl
  | undef => simp [Genv.findFunct] at hf

theorem translFundef_internal_inv {moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool}
    {f : CminorSel.Function} {tf : RTL.Fundef}
    (h : translFundef moreLikely (.Internal f) = .OK tf) :
    ∃ tf0, translFunction moreLikely f = .OK tf0 ∧ tf = .Internal tf0 := by
  simp only [translFundef, ASTFundef.transfPartial] at h
  split at h
  · next tf' htf => cases h; exact ⟨tf', htf, rfl⟩
  · cases h

theorem translFundef_external_inv {moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool}
    {ef : ExtFun} {tf : RTL.Fundef}
    (h : translFundef moreLikely (.External ef) = .OK tf) : tf = .External ef := by
  cases h; rfl

section CORRECTNESS
variable (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool)
  {prog : CminorSel.Program} {tprog : RTL.Program}
  (TRANSL : translProgram moreLikely prog = .OK tprog)
include TRANSL

/-- `RTLgenproof.symbols_preserved` -/
theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSL id

/-- `RTLgenproof.senv_preserved` -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSL

/-- `RTLgenproof.functions_translated` -/
theorem functions_translated {v : Val} {f : CminorSel.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧ translFundef moreLikely f = .OK tf :=
  find_funct_transf_partial TRANSL h

/-- `RTLgenproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {f : CminorSel.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧ translFundef moreLikely f = .OK tf :=
  find_funct_ptr_transf_partial TRANSL h

theorem external_functions_preserved (b : Block) (ef : ExtFun)
    (h : Genv.findFunctPtr prog.globalenv b = some (.External ef)) :
    Genv.findFunctPtr tprog.globalenv b = some (.External ef) := by
  obtain ⟨tf, A, B⟩ := function_ptr_translated moreLikely TRANSL h
  rw [translFundef_external_inv B] at A
  exact A

variable (hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv))
include hec

set_option maxHeartbeats 2000000 in
/-- `RTLgenproof.transl_step_correct` -/
theorem transl_step_correct {S1 : CminorSel.State} {t : Trace} {S2 : CminorSel.State}
    (hst : CminorSel.Step prog.globalenv S1 t S2) {R1 : RTL.State}
    (hm : MatchStates moreLikely S1 R1) :
    ∃ R2 : RTL.State, (Smallstep.Plus (RTL.Step tprog.globalenv) R1 t R2 ∨
      (Smallstep.Star (RTL.Step tprog.globalenv) R1 t R2 ∧ LtState S2 S1)) ∧
      MatchStates moreLikely S2 R2 := by
  have hsym := symbols_preserved moreLikely TRANSL
  have hsenv := senv_preserved moreLikely TRANSL
  have hfext := external_functions_preserved moreLikely TRANSL
  cases hst with
  | skip_seq f s k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS
      cases TK with
      | Kseq _ _ _ _ _ _ _ _ _ _ n h1 h2 =>
        exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inl (by simp only [sizeStmt, sizeCont]; omega))⟩,
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF h1 TF h2 ME MEXT⟩
  | skip_block f k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS
      cases TK with
      | Kblock _ _ _ _ _ _ _ _ _ h1 =>
        exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inl (by simp only [sizeStmt, sizeCont]; omega))⟩,
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sskip _ _ _ _ _) TF h1 ME MEXT⟩
  | skip_call f k sp e m m' hcall hfree =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS
      have hk : tf.fn_code.get ns = some (.Ireturn rret) ∧ MatchStacks k cs := by
        cases k with
        | Kstop => cases TK with | Kstop _ _ _ _ _ _ h1 h2 => exact ⟨h1, h2⟩
        | Kcall => cases TK with | Kcall _ _ _ _ _ _ _ _ _ _ _ h1 h2 => exact ⟨h1, h2⟩
        | Kseq => simp [CminorSel.isCallCont] at hcall
        | Kblock => simp [CminorSel.isCallCont] at hcall
      obtain ⟨hc, MS⟩ := hk
      cases TF with
      | intro nentry r hr hb hss =>
        obtain ⟨tm', A, B⟩ := Mem.free_parallel_extends MEXT hfree
        exact ⟨_, .inl (plus_one (RTL.Step.Ireturn _ _ _ _ _ _ _ _ hc (by rw [hss]; exact A))),
          .returnstate _ _ _ _ _ _ MS (.undef _) B⟩
  | assign f id a k sp e m v hev =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sassign _ _ _ _ _ _ _ _ r hr hte =>
        obtain ⟨rs', tm', A, B, C, D, E⟩ :=
          transl_expr_correct hsym hsenv hfext hec sp e m hev tm cs tf map [] ns ncont r rs
            (some id) MWF hte ME MEXT
        exact ⟨_, .inr ⟨A, lt_state_intro (.inl (by simp only [sizeStmt]; omega))⟩,
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sskip _ _ _ _ _) TF TK B E⟩
  | store f chunk addr al b k sp e m vl v vaddr m' hl hb ha hs =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sstore _ _ _ _ _ _ _ _ _ _ rd n1 rl n2 htl hte hcode =>
        obtain ⟨rs', tm', A, B, C, D, E⟩ :=
          transl_exprlist_correct hsym hsenv hfext hec sp e m hl tm cs tf map [] ns n1 rl rs
            MWF htl ME MEXT
        obtain ⟨rs'', tm'', F, G, J, K, L⟩ :=
          transl_expr_correct hsym hsenv hfext hec sp e m hb tm' cs tf map rl n1 n2 rd rs'
            none MWF hte B E
        have LD : Val.LessdefList vl (rs''.getList rl) := by
          rw [getList_exten rl K]; exact C
        obtain ⟨vaddr', P, Q⟩ := evalAddressing_lessdef _ sp addr LD ha
        obtain ⟨tm''', S, T⟩ := Mem.storev_extends L hs Q J
        exact ⟨_, .inl (plus_right (star_trans A F rfl) (RTL.Step.Istore _ _ _ _ _ _ _ _ _ _ _ _ _ hcode
            (by rw [Op.evalAddressing_preserved _ _ hsym]; exact P) S) rfl),
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sskip _ _ _ _ _) TF TK G T⟩
  | call f optid sig a bl k sp e m vf vargs fd hea hbl hfd hsig =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Scall _ _ b _ _ _ _ _ _ _ rd n1 rf n2 rargs hte htl hcode hrd =>
        cases hea with
        | e _ _ hev =>
          obtain ⟨rs', tm', A, B, C, D, X⟩ :=
            transl_expr_correct hsym hsenv hfext hec sp e m hev tm cs tf map [] ns n1 rf rs
              none MWF hte ME MEXT
          obtain ⟨rs'', tm'', E, F, G, J, Y⟩ :=
            transl_exprlist_correct hsym hsenv hfext hec sp e m hbl tm' cs tf map [rf] n1 n2 rargs
              rs' MWF htl B X
          obtain ⟨tf', P, Q⟩ := functions_translated moreLikely TRANSL hfd
          have hfind : RTL.findFunction tprog.globalenv (.inl rf) rs'' = some tf' := by
            simp only [RTL.findFunction]
            rw [J rf (.head _), lessdef_findFunct C hfd]
            exact P
          exact ⟨_, .inl (plus_right (star_trans A E rfl) (RTL.Step.Icall _ _ _ _ _ _ _ _ _ _ _ _ hcode
              hfind (by rw [sig_transl_function Q]; exact hsig)) rfl),
            .callstate _ _ _ _ _ _ _ _ Q
              (.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF TF F hrd TK) G Y⟩
      | Scall_imm _ _ id _ _ _ _ _ _ _ rd n2 rargs htl hcode hrd =>
        cases hea with
        | s _ b hfs =>
          obtain ⟨rs'', tm'', E, F, G, J, Y⟩ :=
            transl_exprlist_correct hsym hsenv hfext hec sp e m hbl tm cs tf map [] ns n2 rargs
              rs MWF htl ME MEXT
          obtain ⟨tf', P, Q⟩ := functions_translated moreLikely TRANSL hfd
          have hfind : RTL.findFunction tprog.globalenv (.inr id) rs'' = some tf' := by
            simp only [RTL.findFunction, hsym, hfs]
            rw [← Genv.findFunct_findFunctPtr]
            exact P
          exact ⟨_, .inl (plus_right E (RTL.Step.Icall _ _ _ _ _ _ _ _ _ _ _ _ hcode
              hfind (by rw [sig_transl_function Q]; exact hsig)) rfl),
            .callstate _ _ _ _ _ _ _ _ Q
              (.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF TF F hrd TK) G Y⟩
  | tailcall f sig a bl k sp e m vf vargs fd m' hea hbl hfd hsig hfree =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      obtain ⟨U, V⟩ := match_stacks_call_cont TK
      have hss : tf.fn_stacksize = f.fn_stackspace := by cases TF; assumption
      cases TS with
      | Stailcall _ b _ _ _ _ _ _ _ n1 rf n2 rargs hte htl hcode =>
        cases hea with
        | e _ _ hev =>
          obtain ⟨rs', tm', A, B, C, D, X⟩ :=
            transl_expr_correct hsym hsenv hfext hec _ e m hev tm cs tf map [] ns n1 rf rs
              none MWF hte ME MEXT
          obtain ⟨rs'', tm'', E, F, G, J, Y⟩ :=
            transl_exprlist_correct hsym hsenv hfext hec _ e m hbl tm' cs tf map [rf] n1 n2 rargs
              rs' MWF htl B X
          obtain ⟨tf', P, Q⟩ := functions_translated moreLikely TRANSL hfd
          have hfind : RTL.findFunction tprog.globalenv (.inl rf) rs'' = some tf' := by
            simp only [RTL.findFunction]
            rw [J rf (.head _), lessdef_findFunct C hfd]
            exact P
          obtain ⟨tm''', S, T⟩ := Mem.free_parallel_extends Y hfree
          exact ⟨_, .inl (plus_right (star_trans A E rfl) (RTL.Step.Itailcall _ _ _ _ _ _ _ _ _ _ _ hcode
              hfind (by rw [sig_transl_function Q]; exact hsig) (by rw [hss]; exact S)) rfl),
            .callstate _ _ _ _ _ _ _ _ Q U G T⟩
      | Stailcall_imm _ id _ _ _ _ _ _ _ n2 rargs htl hcode =>
        cases hea with
        | s _ b hfs =>
          obtain ⟨rs'', tm'', E, F, G, J, Y⟩ :=
            transl_exprlist_correct hsym hsenv hfext hec _ e m hbl tm cs tf map [] ns n2 rargs
              rs MWF htl ME MEXT
          obtain ⟨tf', P, Q⟩ := functions_translated moreLikely TRANSL hfd
          have hfind : RTL.findFunction tprog.globalenv (.inr id) rs'' = some tf' := by
            simp only [RTL.findFunction, hsym, hfs]
            rw [← Genv.findFunct_findFunctPtr]
            exact P
          obtain ⟨tm''', S, T⟩ := Mem.free_parallel_extends Y hfree
          exact ⟨_, .inl (plus_right E (RTL.Step.Itailcall _ _ _ _ _ _ _ _ _ _ _ hcode
              hfind (by rw [sig_transl_function Q]; exact hsig) (by rw [hss]; exact S)) rfl),
            .callstate _ _ _ _ _ _ _ _ Q U G T⟩
  | builtin f res ef al k sp e m vl t v m' hal hx =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sbuiltin _ _ _ _ _ _ _ _ _ res' n1 rargs htl hcode hres =>
        obtain ⟨vparams, P, Q⟩ := invert_eval_builtin_args sp e m hal
        obtain ⟨rs', tm', E, F, G, J, K⟩ :=
          transl_exprlist_correct hsym hsenv hfext hec sp e m P tm cs tf map [] ns n1 rargs rs
            MWF htl ME MEXT
        obtain ⟨vargs', U, V⟩ := transl_eval_builtin_args sp m rs' al G Q
        obtain ⟨vargs'', X, Y⟩ := evalBuiltinArgs_lessdef (e1 := fun r => rs'.get r)
          (e2 := fun r => rs'.get r) (fun _ => .refl _) K U
        obtain ⟨tv, tm'', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hx K (Val.lessdef_list_trans V Y)
        exact ⟨_, .inl (plus_right E (RTL.Step.Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcode
            (evalBuiltinArgs_preserved (ge1 := Genv.toSenv prog.globalenv) (fun id => hsym id) X) (by rw [hsenv]; exact A)) rfl),
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sskip _ _ _ _ _) TF TK
            (match_env_update_res B MWF hres F) C⟩
  | seq f s1 s2 k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sseq _ _ _ _ _ _ _ _ n h2 h1 =>
        exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inr ⟨by simp only [sizeStmt, sizeCont]; omega,
            by simp only [sizeStmt]; omega⟩)⟩,
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF h1 TF
            (.Kseq _ _ _ _ _ _ _ _ _ _ _ h2 TK) ME MEXT⟩
  | ifthenelse f c s1 s2 k sp e m b hc =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sifthenelse _ _ _ _ _ _ _ _ _ ntrue nfalse h1 h2 hcond =>
        obtain ⟨rs', tm', A, B, C, D⟩ :=
          transl_condexpr_correct hsym hsenv hfext hec sp e m hc tm cs tf map [] ns ntrue nfalse rs
            MWF hcond ME MEXT
        refine ⟨_, .inl A, ?_⟩
        cases b
        · exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF h2 TF TK B D
        · exact .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF h1 TF TK B D
  | loop f s k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sloop _ _ _ _ _ _ _ nloop nend hb h1 h2 =>
        exact ⟨_, .inl (plus_one (RTL.Step.Inop _ _ _ _ _ _ _ h1)),
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF hb TF
            (.Kseq _ _ _ _ _ _ _ _ _ _ _ (.Sloop _ _ _ _ _ _ _ _ _ hb h2 h2) TK) ME MEXT⟩
  | block f s k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sblock _ _ _ _ _ _ _ hb =>
        exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inr ⟨by simp only [sizeStmt, sizeCont]; omega,
            by simp only [sizeStmt]; omega⟩)⟩,
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF hb TF
            (.Kblock _ _ _ _ _ _ _ _ _ TK) ME MEXT⟩
  | exit_seq f n s k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sexit _ _ _ _ _ _ _ hn =>
        cases TK with
        | Kseq _ _ _ _ _ _ _ _ _ _ n' h1 h2 =>
          exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inl (by simp only [sizeStmt, sizeCont]; omega))⟩,
            .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sexit _ _ _ _ _ _ _ hn) TF h2 ME MEXT⟩
  | exit_block_0 f k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sexit _ _ _ _ _ _ _ hn =>
        cases TK with
        | Kblock _ _ _ _ _ _ _ _ _ h1 =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
          subst hn
          exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inl (by simp only [sizeStmt, sizeCont]; omega))⟩,
            .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sskip _ _ _ _ _) TF h1 ME MEXT⟩
  | exit_block_S f n k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sexit _ _ _ _ _ _ _ hn =>
        cases TK with
        | Kblock _ _ _ _ _ _ _ _ _ h1 =>
          simp only [List.getElem?_cons_succ] at hn
          exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inl (by simp only [sizeStmt, sizeCont]; omega))⟩,
            .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sexit _ _ _ _ _ _ _ hn) TF h1 ME MEXT⟩
  | switch f a k sp e m n ha =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sswitch _ _ _ _ _ _ _ hte =>
        obtain ⟨nd, rs', tm', A, B, C, D⟩ :=
          transl_exitexpr_correct hsym hsenv hfext hec sp e m ha tm cs tf map ns nexits rs MWF hte
            ME MEXT
        exact ⟨_, .inr ⟨A, lt_state_intro (.inl (by simp only [sizeStmt]; omega))⟩,
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sexit _ _ ncont _ _ _ _ B) TF TK C D⟩
  | return_0 f k sp e m m' hfree =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS
      obtain ⟨U, V⟩ := match_stacks_call_cont TK
      cases TF with
      | intro nentry r hr hb hss =>
        obtain ⟨tm', A, B⟩ := Mem.free_parallel_extends MEXT hfree
        exact ⟨_, .inl (plus_one (RTL.Step.Ireturn _ _ _ _ _ _ _ _ V (by rw [hss]; exact A))),
          .returnstate _ _ _ _ _ _ U (.undef _) B⟩
  | return_1 f a k sp e m v m' hev hfree =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sreturn_some _ _ _ _ _ _ rr hte =>
        obtain ⟨rs', tm', A, B, C, D, E⟩ :=
          transl_expr_correct hsym hsenv hfext hec _ e m hev tm cs tf map [] ns nret rr rs
            none MWF hte ME MEXT
        obtain ⟨U, V⟩ := match_stacks_call_cont TK
        cases TF with
        | intro nentry r hr hb hss =>
          obtain ⟨tm'', P, Q⟩ := Mem.free_parallel_extends E hfree
          exact ⟨_, .inl (plus_right A (RTL.Step.Ireturn _ _ _ _ _ _ _ _ V (by rw [hss]; exact P)) rfl),
            .returnstate _ _ _ _ _ _ U C Q⟩
  | label f lbl s k sp e m =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Slabel _ _ _ _ _ _ _ _ n hg hc hb =>
        exact ⟨_, .inr ⟨.refl _, lt_state_intro (.inl (by simp only [sizeStmt]; omega))⟩,
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF hb TF TK ME MEXT⟩
  | goto f lbl k sp e m s' k' hfl =>
    cases hm with
    | state _ _ _ _ _ _ tm cs tf ns rs map ncont nexits ngoto nret rret MWF TS TF TK ME MEXT =>
      cases TS with
      | Sgoto _ _ _ _ _ _ _ hg =>
        have TF' := TF
        cases TF with
        | intro nentry r hr hb hss =>
          obtain ⟨ns2, nd2, nexits2, A, B, C⟩ :=
            tr_find_label hg f.fn_body hfl hb (tr_cont_call_cont TK)
          exact ⟨_, .inl (plus_one (RTL.Step.Inop _ _ _ _ _ _ _ A)),
            .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF B TF' C ME MEXT⟩
  | internal_function f vargs k m m' sp e hargs halloc he =>
    cases hm with
    | callstate _ _ targs _ _ tm cs tf TF MS LD MEXT =>
      obtain ⟨tf0, htf, rfl⟩ := translFundef_internal_inv TF
      have TRF := transl_function_charact htf
      cases TRF with
      | intro code rparams map1 s0 s1 i1 rvars map2 s2 i2 nentry ngoto nret rret orret
          h1 h2 hor hb hret =>
        subst he
        have ME := match_init_env_init_reg h1 h2 LD
        have MWF : MapWf map2 :=
          add_vars_wf f.fn_vars h2 (add_vars_wf f.fn_params h1 init_mapping_wf (init_mapping_valid _))
            (add_vars_valid _ h1 (init_mapping_valid _)).2
        obtain ⟨tm', A, B⟩ := Mem.alloc_extends MEXT halloc (Int.le_refl _) (Int.le_refl _)
        refine ⟨_, .inl (plus_one (RTL.Step.function_internal _ _ _ _ _ _
            (Val.has_argtype_list_lessdef hargs LD) A)), ?_⟩
        refine .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF hb (.intro nentry rret hor hb rfl) ?_ ME B
        cases MS with
        | stop => exact .Kstop _ _ _ _ _ _ hret .stop
        | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1 a2 a3 a4 a5 =>
          exact .Kcall _ _ _ _ _ _ _ _ _ _ _ hret (.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1 a2 a3 a4 a5)
  | external_function ef vargs k m t vres m' hx =>
    cases hm with
    | callstate _ _ targs _ _ tm cs tf TF MS LD MEXT =>
      rw [translFundef_external_inv TF]
      obtain ⟨tvres, tm', A, B, C, _⟩ := hec ef _ _ _ _ _ _ _ hx MEXT LD
      exact ⟨_, .inl (plus_one (RTL.Step.function_external _ _ _ _ _ _ _ (by rw [hsenv]; exact A))),
        .returnstate _ _ _ _ _ _ MS B C⟩
  | «return» v optid f sp e k m =>
    cases hm with
    | returnstate _ tv _ _ tm cs MS LD MEXT =>
      cases MS with
      | call _ _ _ _ _ r tf n rs cs' map nexits ngoto nret rret MWF TF ME hr TK =>
        exact ⟨_, .inl (plus_one (RTL.Step.return _ _ _ _ _ _ _ _)),
          .state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MWF (.Sskip _ _ _ _ _) TF TK
            (match_env_update_dest LD MWF hr ME) MEXT⟩

omit hec in
/-- `RTLgenproof.transl_initial_states` -/
theorem transl_initial_states {S : CminorSel.State} (h : CminorSel.InitialState prog S) :
    ∃ R, RTL.InitialState tprog R ∧ MatchStates moreLikely S R := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, A, B⟩ := function_ptr_translated moreLikely TRANSL hf
    refine ⟨_, .intro b tf m0 ?_ ?_ A ?_, .callstate _ _ _ _ _ _ _ _ B .stop .nil
      (Mem.extends_refl _)⟩
    · exact (init_mem_transf_partial TRANSL).trans hm
    · rw [(match_transform_partial_program TRANSL).main_eq, symbols_preserved moreLikely TRANSL]
      exact hs
    · rw [sig_transl_function B]; exact hsig

end CORRECTNESS

/-- `RTLgenproof.transl_final_states` -/
theorem transl_final_states {moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool}
    {S : CminorSel.State} {R : RTL.State} {r : Integers.Int}
    (hm : MatchStates moreLikely S R) (h : CminorSel.FinalState S r) : RTL.FinalState R r := by
  cases h with
  | intro r m =>
    cases hm with
    | returnstate _ tv _ _ tm cs MS LD MEXT =>
      cases MS
      cases LD
      exact .intro _ _

/-- `RTLgenproof.transf_program_correct`: RTL generation preserves the semantics of
programs (forward simulation from CminorSel to RTL), for any branch-prediction
heuristic `moreLikely`.

The hypotheses `hext` and `hasm` state that external functions and inline assembly
are compatible with memory extensions (`ec_mem_extends`), which CompCert assumes by
axiom. -/
theorem transf_program_correct (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool)
    (prog : CminorSel.Program) (tprog : RTL.Program)
    (TRANSL : translProgram moreLikely prog = .OK tprog)
    (hext : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasm : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge) :
    ForwardSimulation (CminorSel.semantics prog) (RTL.semantics tprog) := by
  have hec : ∀ ef, ExtcallMemExtends (externalCall ef) (Genv.toSenv prog.globalenv) :=
    fun ef => externalCall_memExtends ef _ (fun n sg => hext n sg _) (fun n sg => hasm n sg _)
  exact forward_simulation_star_wf (L1 := CminorSel.semantics prog) (L2 := RTL.semantics tprog)
    (MatchStates moreLikely)
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved moreLikely TRANSL])
    (fun _ h => transl_initial_states moreLikely TRANSL h)
    (fun _ _ _ hm h => transl_final_states hm h)
    LtState lt_state_wf
    (fun _ _ _ hst _ hm => transl_step_correct moreLikely TRANSL hec hst hm)

end RTLgen
end RiscV
end CC
