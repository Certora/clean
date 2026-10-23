/-
  [x86-64 instance of `CCLib/backend/RTLtypingSubject.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Typing of RTL states and subject reduction — port of the last part of
  `backend/RTLtyping.v`: `wt_regset`, `wt_regset_assign`, `wt_regset_list`,
  `wt_regset_setres`, `wt_init_regs`, `wt_exec_Iop`, `wt_exec_Iload`,
  `wt_exec_Ibuiltin`, `wt_instr_at`, `wt_stackframes`, `wt_state`,
  `wt_stackframes_change_sig`, **`subject_reduction`**, `wt_initial_state`,
  `wt_instr_inv`.

  Differences from Rocq: the well-typedness of the results of external
  functions and inline assembly, which CompCert takes as an axiom, is a pair
  of hypotheses (`hext`, `hasm`) of `subject_reduction`.
-/
import CCLib.x86.RTLtypingSound
import CCLib.x86.OpTyping
import CCLib.common.EventsProps

namespace CC
namespace X86
namespace RTLtyping

open RTL Op

/-- `Values.has_type Vundef` -/
theorem hasType_undef (t : ATyp) : Val.HasType .Vundef t := by
  cases t <;> rfl

/-- `RTLtyping.wt_regset` -/
def WtRegset (env : Regenv) (rs : RTL.Regset) : Prop := ∀ r, Val.HasType (rs.get r) (env r)

/-- `RTLtyping.wt_regset_assign` -/
theorem wt_regset_assign {env : Regenv} {rs : RTL.Regset} {v : Val} {r : Reg}
    (h : WtRegset env rs) (hv : Val.HasType v (env r)) : WtRegset env (rs.set r v) := by
  intro r0
  rw [PMap.gsspec]
  split
  · subst r0; exact hv
  · exact h r0

/-- `RTLtyping.wt_regset_list` -/
theorem wt_regset_list {env : Regenv} {rs : RTL.Regset} (h : WtRegset env rs) :
    ∀ rl : List Reg, Val.HasTypeList (rs.getList rl) (rl.map env)
  | [] => trivial
  | r :: rl => ⟨h r, wt_regset_list h rl⟩

/-- `RTLtyping.wt_regset_setres` -/
theorem wt_regset_setres {env : Regenv} {rs : RTL.Regset} {v : Val} {res : BuiltinRes Reg}
    (h : WtRegset env rs) (hv : Val.HasType v (typeOfBuiltinRes env res)) :
    WtRegset env (regmapSetres res v rs) := by
  cases res with
  | BR r => exact wt_regset_assign h hv
  | _ => exact h

/-- `RTLtyping.wt_init_regs` -/
theorem wt_init_regs {env : Regenv} :
    ∀ (rl : List Reg) (args : List Val), Val.HasTypeList args (rl.map env) →
    WtRegset env (initRegs args rl)
  | [], [], _ => fun r => by simp only [initRegs, PMap.gi]; exact hasType_undef _
  | [], _ :: _, h => by simp [Val.HasTypeList] at h
  | _ :: _, [], h => by simp [Val.HasTypeList] at h
  | r :: rl, a :: args, h => by
    obtain ⟨h1, h2⟩ := h
    exact wt_regset_assign (wt_init_regs rl args h2) h1

section
variable {win64 : Bool}

/-- `RTLtyping.wt_exec_Iop` -/
theorem wt_exec_Iop {F V : Type} (ge : Genv F V) {env : Regenv} {f : RTL.Function} {sp : Val}
    {op : Operation} {args : List Reg} {res : Reg} {s : Node} {rs : RTL.Regset} {m : Mem}
    {v : Val} (hwt : WtInstr win64 f env (.Iop op args res s))
    (hev : evalOperation ge sp op (rs.getList args) m = some v) (hrs : WtRegset env rs) :
    WtRegset env (rs.set res v) := by
  cases hwt with
  | Iopmove r1 _ _ he _ =>
    have e : evalOperation ge sp .Omove (rs.getList [r1]) m = some (rs.get r1) := rfl
    rw [e] at hev; cases hev
    exact wt_regset_assign hrs (by rw [he]; exact hrs r1)
  | Iop _ _ _ _ hne _ hres _ =>
    exact wt_regset_assign hrs (by rw [hres]; exact type_of_operation_sound ge sp op _ m v hne hev)

/-- `RTLtyping.wt_exec_Iload` -/
theorem wt_exec_Iload {env : Regenv} {f : RTL.Function} {chunk : Chunk} {addr : Addressing}
    {args : List Reg} {dst : Reg} {s : Node} {m : Mem} {a v : Val} {rs : RTL.Regset}
    (hwt : WtInstr win64 f env (.Iload chunk addr args dst s)) (hl : Mem.loadv chunk m a = some v)
    (hrs : WtRegset env rs) : WtRegset env (rs.set dst v) := by
  cases hwt with
  | Iload _ _ _ _ _ _ hd _ =>
    refine wt_regset_assign hrs ?_
    rw [hd]
    cases a <;> simp only [Mem.loadv] at hl <;> try cases hl
    split at hl
    · rw [← Chunk.proj_xtype]
      exact Val.has_proj_xtype (EventsProps.load_hasRettype hl)
    · cases hl

/-- `RTLtyping.wt_exec_Ibuiltin` -/
theorem wt_exec_Ibuiltin {env : Regenv} {f : RTL.Function} {ef : ExtFun}
    {ge : Senv} {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {s : Node}
    {vargs : List Val} {m : Mem} {t : Trace} {vres : Val} {m' : Mem} {rs : RTL.Regset}
    (hec : ExtcallWellTyped (externalCall ef) ef.sig)
    (hwt : WtInstr win64 f env (.Ibuiltin ef args res s))
    (hcall : externalCall ef ge vargs m t vres m') (hrs : WtRegset env rs) :
    WtRegset env (regmapSetres res vres rs) := by
  cases hwt with
  | Ibuiltin _ _ _ _ _ hres _ =>
    refine wt_regset_setres hrs ?_
    rw [hres]
    exact Val.has_proj_xtype (hec _ _ _ _ _ _ hcall)

/-- `RTLtyping.wt_instr_at` -/
theorem wt_instr_at {f : RTL.Function} {env : Regenv} {pc : Node} {i : Instruction}
    (h : WtFunction win64 f env) (hpc : f.fn_code.get pc = some i) : WtInstr win64 f env i :=
  h.wt_instrs pc i hpc

end

variable (win64 : Bool)

/-- `RTLtyping.wt_stackframes` -/
inductive WtStackframes : List RTL.Stackframe → Signature → Prop where
  | nil (sg : Signature) : sg.sig_res = .Xint → WtStackframes [] sg
  | cons (s : List RTL.Stackframe) (res : Reg) (f : RTL.Function) (sp : Val) (pc : Node)
      (rs : RTL.Regset) (env : Regenv) (sg : Signature) :
      WtFunction win64 f env → WtRegset env rs → env res = projSigRes sg →
      WtStackframes s f.fn_sig → WtStackframes (.Stackframe res f sp pc rs :: s) sg

/-- `RTLtyping.wt_state` -/
inductive WtState : RTL.State → Prop where
  | intro (s : List RTL.Stackframe) (f : RTL.Function) (sp : Val) (pc : Node) (rs : RTL.Regset)
      (m : Mem) (env : Regenv) :
      WtStackframes win64 s f.fn_sig → WtFunction win64 f env → WtRegset env rs →
      WtState (.State s f sp pc rs m)
  | call (s : List RTL.Stackframe) (f : RTL.Fundef) (args : List Val) (m : Mem) :
      WtStackframes win64 s (funsig f) → WtFundef win64 f →
      Val.HasTypeList args (projSigArgs (funsig f)) → WtState (.Callstate s f args m)
  | ret (s : List RTL.Stackframe) (v : Val) (m : Mem) (sg : Signature) :
      WtStackframes win64 s sg → Val.HasType v (projSigRes sg) → WtState (.Returnstate s v m)

/-- `RTLtyping.wt_stackframes_change_sig` -/
theorem wt_stackframes_change_sig {s : List RTL.Stackframe} {sg1 sg2 : Signature}
    (he : sg1.sig_res = sg2.sig_res) (h : WtStackframes win64 s sg1) : WtStackframes win64 s sg2 := by
  cases h with
  | nil _ h => exact .nil _ (he ▸ h)
  | cons _ _ _ _ _ _ env _ A B C D =>
    exact .cons _ _ _ _ _ _ env _ A B (by rw [C]; simp only [projSigRes, he]) D

section SUBJECT_REDUCTION
variable (p : RTL.Program) (wt_p : WtProgram win64 p)
  (hext : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
  (hasm : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)

include wt_p in
theorem wt_find_function {ros : Sum Reg Ident} {rs : RTL.Regset} {fd : RTL.Fundef}
    (h : findFunction p.globalenv ros rs = some fd) : WtFundef win64 fd := by
  cases ros with
  | inl r => exact Genv.findFunct_prop (WtFundef win64) (fun id f hin => wt_p id f hin) h
  | inr id =>
    simp only [findFunction] at h
    split at h
    · cases h
    · exact Genv.findFunctPtr_prop (WtFundef win64) (fun id f hin => wt_p id f hin) h

include wt_p hext hasm in
/-- `RTLtyping.subject_reduction` -/
theorem subject_reduction {st1 : RTL.State} {t : Trace} {st2 : RTL.State}
    (hst : RTL.Step p.globalenv st1 t st2) (hwt : WtState win64 st1) : WtState win64 st2 := by
  have hec : ∀ ef, ExtcallWellTyped (externalCall ef) ef.sig :=
    fun ef => externalCall_wellTyped ef hext hasm
  cases hst with
  | Inop s f sp pc rs m pc' _ =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR => exact .intro _ _ _ _ _ _ env WS WF WR
  | Iop s f sp pc rs m op args res pc' v H H0 =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR =>
      exact .intro _ _ _ _ _ _ env WS WF (wt_exec_Iop _ (wt_instr_at WF H) H0 WR)
  | Iload s f sp pc rs m chunk addr args dst pc' a v H H0 H1 =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR =>
      exact .intro _ _ _ _ _ _ env WS WF (wt_exec_Iload (wt_instr_at WF H) H1 WR)
  | Istore s f sp pc rs m chunk addr args src pc' a m' =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR => exact .intro _ _ _ _ _ _ env WS WF WR
  | Icall s f sp pc rs m sig ros args res pc' fd H H0 H1 =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR =>
      have WTI := wt_instr_at WF H
      cases WTI with
      | Icall _ _ _ _ _ _ hargs hres _ =>
        subst H1
        refine .call _ _ _ _ (.cons _ _ _ _ _ _ env _ WF WR hres WS)
          (wt_find_function win64 p wt_p H0) ?_
        rw [← hargs]; exact wt_regset_list WR args
  | Itailcall s f stk pc rs m sig ros args fd m' H H0 H1 _ =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR =>
      have WTI := wt_instr_at WF H
      cases WTI with
      | Itailcall _ _ _ _ hargs hres _ =>
        subst H1
        refine .call _ _ _ _ (wt_stackframes_change_sig win64 hres.symm WS)
          (wt_find_function win64 p wt_p H0) ?_
        rw [← hargs]; exact wt_regset_list WR args
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m' H _ H1 =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR =>
      exact .intro _ _ _ _ _ _ env WS WF (wt_exec_Ibuiltin (hec ef) (wt_instr_at WF H) H1 WR)
  | Icond =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR => exact .intro _ _ _ _ _ _ env WS WF WR
  | Ijumptable =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR => exact .intro _ _ _ _ _ _ env WS WF WR
  | Ireturn s f stk pc rs m or m' H _ =>
    cases hwt with
    | intro _ _ _ _ _ _ env WS WF WR =>
      refine .ret _ _ _ _ WS ?_
      have WTI := wt_instr_at WF H
      cases WTI with
      | Ireturn_none _ => exact hasType_undef _
      | Ireturn_some arg _ he => simp only [regmapOptget]; rw [← he]; exact WR arg
  | function_internal s f args m m' stk _ _ =>
    cases hwt with
    | call _ _ _ _ WS WF WA =>
      cases WF with
      | internal _ env WTF =>
        refine .intro _ _ _ _ _ _ env WS WTF (wt_init_regs _ _ ?_)
        rw [WTF.wt_params]; exact WA
  | function_external s ef args res t m m' H =>
    cases hwt with
    | call _ _ _ _ WS _ _ => exact .ret _ _ _ _ WS (Val.has_proj_xtype (hec ef _ _ _ _ _ _ H))
  | «return» res f sp pc rs s vres m =>
    cases hwt with
    | ret _ _ _ sg WS WV =>
      cases WS with
      | cons _ _ _ _ _ _ env _ WF WR hres WS' =>
        exact .intro _ _ _ _ _ _ env WS' WF (wt_regset_assign WR (by rw [hres]; exact WV))

include wt_p in
/-- `RTLtyping.wt_initial_state` -/
theorem wt_initial_state {S : RTL.State} (h : RTL.InitialState p S) : WtState win64 S := by
  cases h with
  | intro b f m0 _ _ H2 H3 =>
    refine .call _ _ _ _ (.nil _ (by rw [H3]; rfl))
      (Genv.findFunctPtr_prop (WtFundef win64) (fun id f hin => wt_p id f hin) H2) ?_
    rw [H3]; trivial

/-- `RTLtyping.wt_instr_inv` -/
theorem wt_instr_inv {s : List RTL.Stackframe} {f : RTL.Function} {sp : Val} {pc : Node}
    {rs : RTL.Regset} {m : Mem} {i : Instruction} (h : WtState win64 (.State s f sp pc rs m))
    (hpc : f.fn_code.get pc = some i) : ∃ env, WtInstr win64 f env i ∧ WtRegset env rs := by
  cases h with
  | intro _ _ _ _ _ _ env _ WF WR => exact ⟨env, wt_instr_at WF hpc, WR⟩

end SUBJECT_REDUCTION

end RTLtyping
end X86
end CC
