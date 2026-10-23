/-
  [RISC-V instance of `CCLib/backend/Lineartyping.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Type-checking Linear code — port of the executable type checker of
  `backend/Lineartyping.v`: `slot_valid`, `slot_writable`, `loc_valid`,
  `wt_builtin_res`, `wt_instr`, `wt_code`, `wt_function`, and the
  run-time typing predicate `wt_locset`.

  Also ported: the lemmas about `wt_locset`, the typing of Linear states
  (`wt_callstack`, `wt_state`), `step_type_preservation`,
  `wt_initial_state`, and the properties of well-typed states used by the
  correctness proof of `Stacking`.

  As elsewhere in the port, the well-typedness of external functions and
  inline assembly (an axiom in Rocq, `external_call_well_typed`) is taken
  as hypotheses `hext`/`hasm` of `step_type_preservation`.

  Differences from Rocq: `Archi.abi` (used by `loc_parameters`) is an
  explicit argument `abi`; `Zdivide_dec (typealign ty) ofs` is the
  equivalent test `ofs % typealign ty == 0` (`typealign ty > 0`).
-/
import CCLib.riscV.Linear
import CCLib.common.EventsProps
import CCLib.common.ValuesTheory

namespace CC
namespace RiscV
namespace Lineartyping

open Linear Conventions1 Conventions

section WT_INSTR
variable (funct : Linear.Function)

/-- `Lineartyping.slot_valid` -/
def slotValid (sl : Slot) (ofs : Z) (ty : ATyp) : Bool :=
  (match sl with
   | .Local => decide (0 ≤ ofs)
   | .Outgoing => decide (0 ≤ ofs)
   | .Incoming => decide (Loc.S .Incoming ofs ty ∈ RPair.regsList (locParameters  funct.fn_sig)))
  && (ofs % typealign ty == 0)

/-- `Lineartyping.slot_writable` -/
def slotWritable (sl : Slot) : Bool :=
  match sl with
  | .Local => true
  | .Outgoing => true
  | .Incoming => false

/-- `Lineartyping.loc_valid` -/
def locValid (l : Loc) : Bool :=
  match l with
  | .R _ => true
  | .S .Local ofs ty => slotValid  funct .Local ofs ty
  | .S _ _ _ => false

/-- `Lineartyping.wt_builtin_res` -/
def wtBuiltinRes : ATyp → BuiltinRes Mreg → Bool
  | ty, .BR r => ATyp.subtype ty (Mreg.type r)
  | _, .BR_none => true
  | _, .BR_splitlong hi lo => wtBuiltinRes .Tint hi && wtBuiltinRes .Tint lo

/-- `Lineartyping.wt_instr` -/
def wtInstr (i : Instruction) : Bool :=
  match i with
  | .Lgetstack sl ofs ty r => ATyp.subtype ty (Mreg.type r) && slotValid  funct sl ofs ty
  | .Lsetstack _ sl ofs ty => slotValid  funct sl ofs ty && slotWritable sl
  | .Lop op args res =>
      match Op.isMoveOperation op args with
      | some arg => ATyp.subtype (Mreg.type arg) (Mreg.type res)
      | none => ATyp.subtype (Op.typeOfOperation op).2 (Mreg.type res)
  | .Lload chunk _ _ dst => ATyp.subtype chunk.typ (Mreg.type dst)
  | .Ltailcall sg _ => sizeArguments  sg == 0
  | .Lbuiltin ef args res =>
      wtBuiltinRes (projSigRes ef.sig) res && (BuiltinArg.paramsList args).all (locValid  funct)
  | _ => true

end WT_INSTR

/-- `Lineartyping.wt_code` -/
def wtCode (f : Linear.Function) (c : Code) : Bool := c.all (wtInstr  f)

/-- `Lineartyping.wt_function` -/
def wtFunction (f : Linear.Function) : Bool := wtCode  f f.fn_code

/-- `Lineartyping.wt_locset` -/
def WtLocset (ls : LTL.Locset) : Prop := ∀ l, Val.HasType (ls l) (Loc.type l)

/-! ## Typing of location maps -/

private theorem hasType_undef (t : ATyp) : Val.HasType .Vundef t := by
  cases t <;> rfl

/-- On RV64 every machine register has type `Tany64`, so any value fits. -/
theorem hasType_mreg (v : Val) (r : Mreg) : Val.HasType v (Mreg.type r) := by
  have : Mreg.type r = .Tany64 := by cases r <;> rfl
  rw [this]; cases v <;> rfl

/-- `Lineartyping.wt_setreg` -/
theorem wt_setreg {ls : LTL.Locset} {r : Mreg} {v : Val} (hv : Val.HasType v (Mreg.type r))
    (h : WtLocset ls) : WtLocset (Locmap.set (.R r) v ls) := by
  intro l
  unfold Locmap.set
  split
  · rename_i e; subst e; exact hv
  · split
    · exact h l
    · exact hasType_undef _

private theorem chunk_ofTyp_typ (ty : ATyp) : (Chunk.ofTyp ty).typ = ty := by
  cases ty <;> rfl

/-- `Lineartyping.wt_setstack` -/
theorem wt_setstack {ls : LTL.Locset} {sl : Slot} {ofs : Z} {ty : ATyp} {v : Val}
    (h : WtLocset ls) : WtLocset (Locmap.set (.S sl ofs ty) v ls) := by
  intro l
  unfold Locmap.set
  split
  · rename_i e; subst e
    have := Val.load_result_type (Chunk.ofTyp ty) v
    rw [chunk_ofTyp_typ] at this
    exact this
  · split
    · exact h l
    · exact hasType_undef _

/-- `Lineartyping.wt_undef_regs` -/
theorem wt_undef_regs (rs : List Mreg) {ls : LTL.Locset} (h : WtLocset ls) :
    WtLocset (LTL.undefRegs rs ls) := by
  induction rs with
  | nil => exact h
  | cons r rs ih => exact wt_setreg (hasType_undef _) ih

/-- `Lineartyping.wt_call_regs` -/
theorem wt_call_regs {ls : LTL.Locset} (h : WtLocset ls) : WtLocset (LTL.callRegs ls) := by
  intro l
  cases l with
  | R r => exact h _
  | S sl ofs ty =>
    cases sl
    · exact hasType_undef _
    · exact h (.S .Outgoing ofs ty)
    · exact hasType_undef _

/-- `Lineartyping.wt_return_regs` -/
theorem wt_return_regs {caller callee : LTL.Locset} (h1 : WtLocset caller)
    (h2 : WtLocset callee) : WtLocset (LTL.returnRegs caller callee) := by
  intro l
  cases l with
  | R r =>
    simp only [LTL.returnRegs]
    split
    · exact h1 _
    · exact h2 _
  | S sl ofs ty =>
    cases sl
    · exact h1 _
    · exact h1 _
    · exact hasType_undef _

/-- `Lineartyping.wt_undef_caller_save_regs` -/
theorem wt_undef_caller_save_regs {ls : LTL.Locset} (h : WtLocset ls) :
    WtLocset (LTL.undefCallerSaveRegs ls) := by
  intro l
  cases l with
  | R r =>
    simp only [LTL.undefCallerSaveRegs]
    split
    · exact h _
    · exact hasType_undef _
  | S sl ofs ty =>
    cases sl
    · exact h _
    · exact h _
    · exact hasType_undef _

/-- `Lineartyping.wt_init` -/
theorem wt_init : WtLocset (Locmap.init .Vundef) := fun _ => hasType_undef _

/-- `Lineartyping.wt_setpair` -/
theorem wt_setpair (sg : Signature) {v : Val} {rs : LTL.Locset}
    (hv : Val.HasType v (projSigRes sg)) (h : WtLocset rs) :
    WtLocset (Locmap.setpair (locResult sg) v rs) := by
  have hp := locResult_pair sg
  have ht := locResult_type sg
  revert hp ht
  cases locResult sg with
  | One r =>
    intro _ ht
    exact wt_setreg (Val.has_subtype ht hv) h
  | Twolong r1 r2 =>
    intro hp _
    exact absurd hp.2.2.2.2 (by decide)

private theorem hasType_loword (v : Val) : Val.HasType (Val.loword v) .Tint := by
  cases v <;> rfl

private theorem hasType_hiword (v : Val) : Val.HasType (Val.hiword v) .Tint := by
  cases v <;> rfl

/-- `Lineartyping.wt_setres` -/
theorem wt_setres (res : BuiltinRes Mreg) (ty : ATyp) (v : Val) (rs : LTL.Locset)
    (hres : wtBuiltinRes ty res = true) (hv : Val.HasType v ty) (h : WtLocset rs) :
    WtLocset (Locmap.setres res v rs) := by
  induction res generalizing ty v rs with
  | BR r =>
    simp only [wtBuiltinRes] at hres
    exact wt_setreg (Val.has_subtype hres hv) h
  | BR_none => exact h
  | BR_splitlong hi lo ihhi ihlo =>
    simp only [wtBuiltinRes, Bool.and_eq_true] at hres
    exact ihlo _ _ _ hres.2 (hasType_loword v) (ihhi _ _ _ hres.1 (hasType_hiword v) h)

/-- `Lineartyping.wt_find_label` -/
theorem wt_find_label (f : Linear.Function) (lbl : Linear.Label) (c : Code)
    (hwt : wtFunction  f = true) (h : Linear.findLabel lbl f.fn_code = some c) :
    wtCode  f c = true := by
  unfold wtFunction wtCode at hwt
  unfold wtCode
  revert hwt h
  generalize f.fn_code = c0
  intro hwt h
  induction c0 with
  | nil => cases h
  | cons a c0 ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hwt
    simp only [Linear.findLabel] at h
    split at h
    · cases h; exact hwt.2
    · exact ih hwt.2 h

/-! ## Properties of the environment at calls and returns -/

/-- `Lineartyping.agree_outgoing_arguments` -/
def AgreeOutgoingArguments (sg : Signature) (ls pls : LTL.Locset) : Prop :=
  ∀ ty ofs, Loc.S .Outgoing ofs ty ∈ RPair.regsList (locArguments  sg) →
    ls (.S .Outgoing ofs ty) = pls (.S .Outgoing ofs ty)

/-- `Lineartyping.outgoing_undef` -/
def OutgoingUndef (ls : LTL.Locset) : Prop :=
  ∀ ty ofs, ls (.S .Outgoing ofs ty) = .Vundef

/-! ## Soundness of the type system -/

/-- `Lineartyping.wt_fundef` -/
def WtFundef : Linear.Fundef → Prop
  | .Internal f => wtFunction  f = true
  | .External _ => True

/-- `Lineartyping.wt_callstack` -/
inductive WtCallstack : List Stackframe → Prop where
  | nil : WtCallstack  []
  | cons (f sp rs c s) :
      WtCallstack  s → wtFunction  f = true → wtCode  f c = true → WtLocset rs →
      WtCallstack  (.Stackframe f sp rs c :: s)

/-- `Lineartyping.wt_parent_locset` -/
theorem wt_parent_locset {s : List Stackframe} (h : WtCallstack  s) :
    WtLocset (parentLocset s) := by
  cases h with
  | nil => exact wt_init
  | cons _ _ _ _ _ _ _ _ hrs => exact hrs

/-- `Lineartyping.wt_state` -/
inductive WtState : Linear.State → Prop where
  | regular (s f sp c rs m) :
      WtCallstack  s → wtFunction  f = true → wtCode  f c = true → WtLocset rs →
      WtState (.State s f sp c rs m)
  | call (s fd rs m) :
      WtCallstack  s → WtFundef  fd → WtLocset rs →
      AgreeCalleeSave rs (parentLocset s) →
      AgreeOutgoingArguments  (funsig fd) rs (parentLocset s) →
      WtState (.Callstate s fd rs m)
  | ret (s rs m) :
      WtCallstack  s → WtLocset rs → AgreeCalleeSave rs (parentLocset s) →
      OutgoingUndef rs →
      WtState (.Returnstate s rs m)

section SOUNDNESS
variable (prog : Linear.Program)
  (wt_prog : ∀ i fd, (i, GlobDef.Gfun fd) ∈ prog.prog_defs → WtFundef  fd)
  (hext : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
  (hasm : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)

include wt_prog in
/-- `Lineartyping.wt_find_function` -/
theorem wt_find_function {ros : Sum Mreg Ident} {rs : LTL.Locset} {f : Linear.Fundef}
    (h : findFunction prog.globalenv ros rs = some f) : WtFundef  f := by
  cases ros with
  | inl r => exact Genv.findFunct_prop _ wt_prog h
  | inr s =>
    simp only [findFunction] at h
    split at h
    · cases h
    · exact Genv.findFunctPtr_prop _ wt_prog h

private theorem wtInstr_head {f : Linear.Function} {i : Instruction} {c : Code}
    (h : wtCode  f (i :: c) = true) : wtInstr  f i = true ∧ wtCode  f c = true := by
  simpa [wtCode] using h

include wt_prog hext hasm in
/-- `Lineartyping.step_type_preservation` -/
theorem step_type_preservation {S1 : Linear.State} {t : Trace} {S2 : Linear.State}
    (hst : Linear.Step  prog.globalenv S1 t S2) (hwt : WtState S1) : WtState S2 := by
  have hec : ∀ ef, ExtcallWellTyped (externalCall ef) ef.sig :=
    fun ef => externalCall_wellTyped ef hext hasm
  cases hst with
  | Lgetstack s f sp sl ofs ty dst b rs m rs' e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2
        (wt_setreg (hasType_mreg _ _) (wt_undef_regs _ hrs))
  | Lsetstack s f sp src sl ofs ty b rs m rs' e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2
        (wt_setstack (wt_undef_regs _ hrs))
  | Lop s f sp op args res b rs m v rs' _ e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2
        (wt_setreg (hasType_mreg _ _) (wt_undef_regs _ hrs))
  | Lload s f sp chunk addr args dst b rs m a v rs' _ _ e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2
        (wt_setreg (hasType_mreg _ _) (wt_undef_regs _ hrs))
  | Lstore s f sp chunk addr args src b rs m m' a rs' _ _ e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2 (wt_undef_regs _ hrs)
  | Lcall s f sp sig ros b rs m f' hf' _ =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      exact .call _ _ _ _ (.cons _ _ _ _ _ hs hf (wtInstr_head  hc).2 hrs)
        (wt_find_function  prog wt_prog hf') hrs (fun _ _ => rfl) (fun _ _ _ => rfl)
  | Ltailcall s f stk sig ros b rs m rs' f' m' e hf' hsig _ =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      have hi := (wtInstr_head  hc).1
      simp only [wtInstr, beq_iff_eq] at hi
      refine .call _ _ _ _ hs (wt_find_function  prog wt_prog hf')
        (wt_return_regs (wt_parent_locset hs) hrs) ?_ ?_
      · intro l hl
        cases l with
        | R r => simp only [CalleeSaveLoc] at hl; simp [LTL.returnRegs, hl]
        | S sl ofs ty =>
          cases sl <;> simp_all [CalleeSaveLoc, LTL.returnRegs]
      · intro ty ofs hl
        rw [← hsig] at hl
        exact absurd (zero_size_arguments_tailcall_possible  sig hi _ hl) id
  | Lbuiltin s f sp rs m ef args res b vargs t vres rs' m' _ hcall e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      have hi := (wtInstr_head  hc).1
      simp only [wtInstr, Bool.and_eq_true] at hi
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2
        (wt_setres _ _ _ _ hi.1 (Val.has_proj_xtype (hec ef _ _ _ _ _ _ hcall))
          (wt_undef_regs _ hrs))
  | Llabel s f sp lbl b rs m =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2 hrs
  | Lgoto s f sp lbl b rs m b' hl =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      exact .regular _ _ _ _ _ _ hs hf (wt_find_label  f lbl b' hf hl) hrs
  | Lcond_true s f sp cond args lbl b rs m rs' b' _ e hl =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wt_find_label  f lbl b' hf hl) (wt_undef_regs _ hrs)
  | Lcond_false s f sp cond args lbl b rs m rs' _ e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wtInstr_head  hc).2 (wt_undef_regs _ hrs)
  | Ljumptable s f sp arg tbl b rs m n lbl b' rs' _ _ hl e =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hf (wt_find_label  f lbl b' hf hl) (wt_undef_regs _ hrs)
  | Lreturn s f stk b rs m m' _ =>
    cases hwt with
    | regular _ _ _ _ _ _ hs hf hc hrs =>
      refine .ret _ _ _ hs (wt_return_regs (wt_parent_locset hs) hrs) ?_ ?_
      · intro l hl
        cases l with
        | R r => simp only [CalleeSaveLoc] at hl; simp [LTL.returnRegs, hl]
        | S sl ofs ty =>
          cases sl <;> simp_all [CalleeSaveLoc, LTL.returnRegs]
      · intro ty ofs; rfl
  | function_internal s f rs m rs' m' stk _ e =>
    cases hwt with
    | call _ _ _ _ hs hfd hrs _ _ =>
      subst rs'
      exact .regular _ _ _ _ _ _ hs hfd hfd (wt_undef_regs _ (wt_call_regs hrs))
  | function_external s ef args res rs1 rs2 m t m' _ hcall e =>
    cases hwt with
    | call _ _ _ _ hs _ hrs hagcs _ =>
      subst rs2
      refine .ret _ _ _ hs
        (wt_setpair _ (Val.has_proj_xtype (hec ef _ _ _ _ _ _ hcall))
          (wt_undef_caller_save_regs hrs)) ?_ ?_
      · intro l hl
        rw [locmap_get_set_loc_result_callee_save _ _ _ _ hl, ← hagcs l hl]
        cases l with
        | R r => simp only [CalleeSaveLoc] at hl; simp [LTL.undefCallerSaveRegs, hl]
        | S sl ofs ty => cases sl <;> simp_all [CalleeSaveLoc, LTL.undefCallerSaveRegs]
      · intro ty ofs
        rw [locmap_get_set_loc_result _ _ _ _ trivial]
        rfl
  | «return» s f sp rs0 c rs m =>
    cases hwt with
    | ret _ _ _ hs hrs _ _ =>
      cases hs with
      | cons _ _ _ _ _ hs' hf hc _ => exact .regular _ _ _ _ _ _ hs' hf hc hrs

include wt_prog in
/-- `Lineartyping.wt_initial_state` -/
theorem wt_initial_state {S : Linear.State} (h : Linear.InitialState prog S) : WtState S := by
  cases h with
  | intro b f m0 _ _ hf _ =>
    exact .call _ _ _ _ .nil (Genv.findFunctPtr_prop _ wt_prog hf) wt_init
      (fun _ _ => rfl) (fun _ _ _ => rfl)

end SOUNDNESS

/-! ## Properties of well-typed states used in `Stackingproof` -/

/-- `Lineartyping.wt_state_getstack` -/
theorem wt_state_getstack {s f sp sl ofs ty rd c rs m}
    (h : WtState (.State s f sp (.Lgetstack sl ofs ty rd :: c) rs m)) :
    slotValid  f sl ofs ty = true := by
  cases h with
  | regular _ _ _ _ _ _ _ _ hc _ =>
    have := (wtInstr_head  hc).1
    simp only [wtInstr, Bool.and_eq_true] at this
    exact this.2

/-- `Lineartyping.wt_state_setstack` -/
theorem wt_state_setstack {s f sp sl ofs ty r c rs m}
    (h : WtState (.State s f sp (.Lsetstack r sl ofs ty :: c) rs m)) :
    slotValid  f sl ofs ty = true ∧ slotWritable sl = true := by
  cases h with
  | regular _ _ _ _ _ _ _ _ hc _ =>
    have := (wtInstr_head  hc).1
    simpa only [wtInstr, Bool.and_eq_true] using this

/-- `Lineartyping.wt_state_tailcall` -/
theorem wt_state_tailcall {s f sp sg ros c rs m}
    (h : WtState (.State s f sp (.Ltailcall sg ros :: c) rs m)) :
    sizeArguments  sg = 0 := by
  cases h with
  | regular _ _ _ _ _ _ _ _ hc _ =>
    have := (wtInstr_head  hc).1
    simpa only [wtInstr, beq_iff_eq] using this

/-- `Lineartyping.wt_state_builtin` -/
theorem wt_state_builtin {s f sp ef args res c rs m}
    (h : WtState (.State s f sp (.Lbuiltin ef args res :: c) rs m)) :
    (BuiltinArg.paramsList args).all (locValid  f) = true := by
  cases h with
  | regular _ _ _ _ _ _ _ _ hc _ =>
    have := (wtInstr_head  hc).1
    simp only [wtInstr, Bool.and_eq_true] at this
    exact this.2

/-- `Lineartyping.wt_callstate_wt_regs` -/
theorem wt_callstate_wt_regs {s f rs m} (h : WtState (.Callstate s f rs m)) (r : Mreg) :
    Val.HasType (rs (.R r)) (Mreg.type r) := by
  cases h with
  | call _ _ _ _ _ _ hrs _ _ => exact hrs _

/-- `Lineartyping.wt_callstate_agree` -/
theorem wt_callstate_agree {s f rs m} (h : WtState (.Callstate s f rs m)) :
    AgreeCalleeSave rs (parentLocset s) ∧
      AgreeOutgoingArguments  (funsig f) rs (parentLocset s) := by
  cases h with
  | call _ _ _ _ _ _ _ h1 h2 => exact ⟨h1, h2⟩

/-- `Lineartyping.wt_returnstate_agree` -/
theorem wt_returnstate_agree {s rs m} (h : WtState (.Returnstate s rs m)) :
    AgreeCalleeSave rs (parentLocset s) ∧ OutgoingUndef rs := by
  cases h with
  | ret _ _ _ _ _ h1 h2 => exact ⟨h1, h2⟩

end Lineartyping
end RiscV
end CC
