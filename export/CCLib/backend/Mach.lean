/-
  Mach: the last intermediate language before assembly — port of
  `backend/Mach.v` (syntax, `load_stack`/`store_stack`, register sets,
  `undef_regs` lemmas, `find_label` lemmas, `extcall_arguments`, semantics
  parameterised by `return_address_offset`, `is_leaf_function`, `wf_state`,
  `wf_step`, `wf_initial`).

  Additions not in Rocq: `semantics_receptive`, and `semantics_determinate`
  under the hypothesis that `return_address_offset` is functional.

  Differences from Rocq: `Archi.abi` is an explicit argument `abi`;
  `Stacklayout.fe_ofs_arg` (`0` on aarch64) is defined here;
  `is_tail c c'` is `List.IsSuffix c c'` (`c <:+ c'`); the register set
  `Regmap.t val` (an `EMap`) is the function type `Mreg → Val`.
-/
import CCLib.backend.Linear

namespace CC

/-- `Stacklayout.fe_ofs_arg` (aarch64) -/
def Stacklayout.feOfsArg : Z := 0

namespace Mach

open Op Smallstep Conventions1

/-- `Mach.label` -/
abbrev Label := Positive

/-- `Mach.instruction` -/
inductive Instruction where
  | Mgetstack (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg)
  | Msetstack (src : Mreg) (ofs : Integers.Ptrofs) (ty : ATyp)
  | Mgetparam (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg)
  | Mop (op : Operation) (args : List Mreg) (res : Mreg)
  | Mload (chunk : Chunk) (addr : Addressing) (args : List Mreg) (dst : Mreg)
  | Mstore (chunk : Chunk) (addr : Addressing) (args : List Mreg) (src : Mreg)
  | Mcall (sg : Signature) (ros : Sum Mreg Ident)
  | Mtailcall (sg : Signature) (ros : Sum Mreg Ident)
  | Mbuiltin (ef : ExtFun) (args : List (BuiltinArg Mreg)) (res : BuiltinRes Mreg)
  | Mlabel (lbl : Label)
  | Mgoto (lbl : Label)
  | Mcond (cond : Condition) (args : List Mreg) (lbl : Label)
  | Mjumptable (arg : Mreg) (tbl : List Label)
  | Mreturn

/-- `Mach.code` -/
abbrev Code := List Instruction

/-- `Mach.function` -/
structure Function where
  fn_sig : Signature
  fn_code : Code
  fn_stacksize : Z
  fn_link_ofs : Integers.Ptrofs
  fn_retaddr_ofs : Integers.Ptrofs

/-- `Mach.fundef` -/
abbrev Fundef := ASTFundef Function
/-- `Mach.program` -/
abbrev Program := ASTProgram Fundef Unit

/-- `Mach.funsig` -/
def funsig : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External ef => ef.sig

/-- `Mach.genv` -/
abbrev CGenv := Genv Fundef Unit

/-- `Mach.load_stack` -/
def loadStack (m : Mem) (sp : Val) (ty : ATyp) (ofs : Integers.Ptrofs) : Option Val :=
  Mem.loadv (Chunk.ofTyp ty) m (Val.offsetPtr sp ofs)

/-- `Mach.store_stack` -/
def storeStack (m : Mem) (sp : Val) (ty : ATyp) (ofs : Integers.Ptrofs) (v : Val) : Option Mem :=
  Mem.storev (Chunk.ofTyp ty) m (Val.offsetPtr sp ofs) v

/-- `Mach.regset` -/
abbrev Regset := Mreg → Val

/-- `Regmap.set` -/
def Regset.set (r : Mreg) (v : Val) (rs : Regset) : Regset := fun r' => if r' = r then v else rs r'

/-- `Regmap.init` -/
def Regset.init (v : Val) : Regset := fun _ => v

theorem Regset.gss (r : Mreg) (v : Val) (rs : Regset) : Regset.set r v rs r = v := by
  simp [Regset.set]

theorem Regset.gso {r r' : Mreg} (v : Val) (rs : Regset) (h : r' ≠ r) :
    Regset.set r v rs r' = rs r' := by
  simp [Regset.set, h]

/-- `Mach.undef_regs` -/
def undefRegs : List Mreg → Regset → Regset
  | [], rs => rs
  | r1 :: rl', rs => Regset.set r1 .Vundef (undefRegs rl' rs)

/-- `Mach.undef_regs_other` -/
theorem undefRegs_other (r : Mreg) (rl : List Mreg) (rs : Regset) (h : r ∉ rl) :
    undefRegs rl rs r = rs r := by
  induction rl with
  | nil => rfl
  | cons a rl ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [undefRegs]
    rw [Regset.gso _ _ h.1, ih h.2]

/-- `Mach.undef_regs_same` -/
theorem undefRegs_same (r : Mreg) (rl : List Mreg) (rs : Regset) (h : r ∈ rl) :
    undefRegs rl rs r = .Vundef := by
  induction rl with
  | nil => simp at h
  | cons a rl ih =>
    simp only [undefRegs, Regset.set]
    split
    · rfl
    · rcases List.mem_cons.mp h with rfl | h
      · contradiction
      · exact ih h

/-- `Mach.undef_caller_save_regs` -/
def undefCallerSaveRegs (rs : Regset) : Regset := fun r => if isCalleeSave r then rs r else .Vundef

/-- `Mach.set_pair` -/
def setPair (p : RPair Mreg) (v : Val) (rs : Regset) : Regset :=
  match p with
  | .One r => Regset.set r v rs
  | .Twolong rhi rlo => Regset.set rlo (Val.loword v) (Regset.set rhi (Val.hiword v) rs)

/-- `Mach.set_res` -/
def setRes : BuiltinRes Mreg → Val → Regset → Regset
  | .BR r, v, rs => Regset.set r v rs
  | .BR_none, _, rs => rs
  | .BR_splitlong hi lo, v, rs => setRes lo (Val.loword v) (setRes hi (Val.hiword v) rs)

/-- `Mach.is_label` -/
def isLabel (lbl : Label) : Instruction → Bool
  | .Mlabel lbl' => decide (lbl = lbl')
  | _ => false

/-- `Mach.is_label_correct` -/
theorem isLabel_correct (lbl : Label) (instr : Instruction) :
    if isLabel lbl instr then instr = .Mlabel lbl else instr ≠ .Mlabel lbl := by
  cases instr <;> simp [isLabel]
  case Mlabel l => by_cases h : lbl = l <;> simp [h, eq_comm]

/-- `Mach.find_label` -/
def findLabel (lbl : Label) : Code → Option Code
  | [] => none
  | i1 :: il => if isLabel lbl i1 then some il else findLabel lbl il

/-- `Mach.find_label_tail` -/
theorem findLabel_tail {lbl : Label} {c c' : Code} (h : findLabel lbl c = some c') : c' <:+ c := by
  induction c with
  | nil => simp [findLabel] at h
  | cons a c ih =>
    simp only [findLabel] at h
    split at h
    · cases h; exact List.suffix_cons a c'
    · exact (ih h).trans (List.suffix_cons a c)

/-- `Mach.find_label_incl` -/
theorem findLabel_incl {lbl : Label} {c c' : Code} (h : findLabel lbl c = some c') :
    ∀ x ∈ c', x ∈ c := fun _ hx => (findLabel_tail h).subset hx

/-- `Mach.stackframe` -/
inductive Stackframe where
  | Stackframe (f : Block) (sp : Val) (retaddr : Val) (c : Code)

/-- `Mach.state` -/
inductive State where
  | State (stack : List Stackframe) (f : Block) (sp : Val) (c : Code) (rs : Regset) (m : Mem)
  | Callstate (stack : List Stackframe) (f : Block) (rs : Regset) (m : Mem)
  | Returnstate (stack : List Stackframe) (rs : Regset) (m : Mem)

/-- `Mach.parent_sp` -/
def parentSp : List Stackframe → Val
  | [] => Val.Vnullptr
  | .Stackframe _ sp _ _ :: _ => sp

/-- `Mach.parent_ra` -/
def parentRa : List Stackframe → Val
  | [] => Val.Vnullptr
  | .Stackframe _ _ ra _ :: _ => ra

/-- `Mach.find_function_ptr` -/
def findFunctionPtr (ge : CGenv) (ros : Sum Mreg Ident) (rs : Regset) : Option Block :=
  match ros with
  | .inl r =>
      match rs r with
      | .Vptr b ofs => if Integers.Ptrofs.eq ofs Integers.Ptrofs.zero then some b else none
      | _ => none
  | .inr symb => Genv.findSymbol ge symb

/-- `Mach.extcall_arg` -/
inductive ExtcallArg (rs : Regset) (m : Mem) (sp : Val) : Loc → Val → Prop where
  | reg (r) : ExtcallArg rs m sp (.R r) (rs r)
  | stack (ofs ty v) :
      loadStack m sp ty (Integers.Ptrofs.repr (Stacklayout.feOfsArg + 4 * ofs)) = some v →
      ExtcallArg rs m sp (.S .Outgoing ofs ty) v

/-- `Mach.extcall_arg_pair` -/
inductive ExtcallArgPair (rs : Regset) (m : Mem) (sp : Val) : RPair Loc → Val → Prop where
  | one (l v) : ExtcallArg rs m sp l v → ExtcallArgPair rs m sp (.One l) v
  | twolong (hi lo vhi vlo) :
      ExtcallArg rs m sp hi vhi → ExtcallArg rs m sp lo vlo →
      ExtcallArgPair rs m sp (.Twolong hi lo) (Val.longofwords vhi vlo)

/-- `Mach.extcall_arguments` -/
def ExtcallArguments (abi : AbiKind) (rs : Regset) (m : Mem) (sp : Val) (sg : Signature)
    (args : List Val) : Prop :=
  ListForall2 (ExtcallArgPair rs m sp) (locArguments abi sg) args

theorem extcallArg_determ {rs m sp l v1 v2} (h1 : ExtcallArg rs m sp l v1)
    (h2 : ExtcallArg rs m sp l v2) : v1 = v2 := by
  cases h1 with
  | reg => cases h2; rfl
  | stack _ _ _ h => cases h2 with
    | stack _ _ _ h' => rw [h] at h'; cases h'; rfl

theorem extcallArgPair_determ {rs m sp p v1 v2} (h1 : ExtcallArgPair rs m sp p v1)
    (h2 : ExtcallArgPair rs m sp p v2) : v1 = v2 := by
  cases h1 with
  | one _ _ h => cases h2 with
    | one _ _ h' => exact extcallArg_determ h h'
  | twolong _ _ _ _ ha hb => cases h2 with
    | twolong _ _ _ _ ha' hb' => rw [extcallArg_determ ha ha', extcallArg_determ hb hb']

theorem extcallArguments_determ {abi rs m sp sg args1 args2}
    (h1 : ExtcallArguments abi rs m sp sg args1) (h2 : ExtcallArguments abi rs m sp sg args2) :
    args1 = args2 := by
  unfold ExtcallArguments at h1 h2
  generalize locArguments abi sg = l at h1 h2
  induction h1 generalizing args2 with
  | nil => cases h2; rfl
  | cons ha _ ih => cases h2 with
    | cons hb hl => rw [extcallArgPair_determ ha hb, ih hl]

section RELSEM
variable (abi : AbiKind) (returnAddressOffset : Function → Code → Integers.Ptrofs → Prop)
  (ge : CGenv)

/-- `Mach.step` -/
inductive Step : State → Trace → State → Prop where
  | Mlabel (s f sp lbl c rs m) :
      Step (.State s f sp (.Mlabel lbl :: c) rs m) E0 (.State s f sp c rs m)
  | Mgetstack (s f sp ofs ty dst c rs m v) :
      loadStack m sp ty ofs = some v →
      Step (.State s f sp (.Mgetstack ofs ty dst :: c) rs m) E0
        (.State s f sp c (Regset.set dst v rs) m)
  | Msetstack (s f sp src ofs ty c rs m m' rs') :
      storeStack m sp ty ofs (rs src) = some m' →
      rs' = undefRegs (destroyedBySetstack ty) rs →
      Step (.State s f sp (.Msetstack src ofs ty :: c) rs m) E0 (.State s f sp c rs' m')
  | Mgetparam (s fb f sp ofs ty dst c rs m v rs') :
      Genv.findFunctPtr ge fb = some (.Internal f) →
      loadStack m sp Tptr f.fn_link_ofs = some (parentSp s) →
      loadStack m (parentSp s) ty ofs = some v →
      rs' = Regset.set dst v (Regset.set tempForParentFrame .Vundef rs) →
      Step (.State s fb sp (.Mgetparam ofs ty dst :: c) rs m) E0 (.State s fb sp c rs' m)
  | Mop (s f sp op args res c rs m v rs') :
      evalOperation ge sp op (args.map rs) m = some v →
      rs' = Regset.set res v (undefRegs (destroyedByOp op) rs) →
      Step (.State s f sp (.Mop op args res :: c) rs m) E0 (.State s f sp c rs' m)
  | Mload (s f sp chunk addr args dst c rs m a v rs') :
      evalAddressing ge sp addr (args.map rs) = some a →
      Mem.loadv chunk m a = some v →
      rs' = Regset.set dst v (undefRegs (destroyedByLoad chunk addr) rs) →
      Step (.State s f sp (.Mload chunk addr args dst :: c) rs m) E0 (.State s f sp c rs' m)
  | Mstore (s f sp chunk addr args src c rs m m' a rs') :
      evalAddressing ge sp addr (args.map rs) = some a →
      Mem.storev chunk m a (rs src) = some m' →
      rs' = undefRegs (destroyedByStore chunk addr) rs →
      Step (.State s f sp (.Mstore chunk addr args src :: c) rs m) E0 (.State s f sp c rs' m')
  | Mcall (s fb sp sig ros c rs m f f' ra) :
      findFunctionPtr ge ros rs = some f' →
      Genv.findFunctPtr ge fb = some (.Internal f) →
      returnAddressOffset f c ra →
      Step (.State s fb sp (.Mcall sig ros :: c) rs m) E0
        (.Callstate (.Stackframe fb sp (.Vptr fb ra) c :: s) f' rs m)
  | Mtailcall (s fb stk soff sig ros c rs m f f' m') :
      findFunctionPtr ge ros rs = some f' →
      Genv.findFunctPtr ge fb = some (.Internal f) →
      loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (parentSp s) →
      loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (parentRa s) →
      Mem.free m stk 0 f.fn_stacksize = some m' →
      Step (.State s fb (.Vptr stk soff) (.Mtailcall sig ros :: c) rs m) E0
        (.Callstate s f' rs m')
  | Mbuiltin (s f sp rs m ef args res b vargs t vres rs' m') :
      EvalBuiltinArgs ge.toSenv rs sp m args vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      rs' = setRes res vres (undefRegs (destroyedByBuiltin ef) rs) →
      Step (.State s f sp (.Mbuiltin ef args res :: b) rs m) t (.State s f sp b rs' m')
  | Mgoto (s fb f sp lbl c rs m c') :
      Genv.findFunctPtr ge fb = some (.Internal f) →
      findLabel lbl f.fn_code = some c' →
      Step (.State s fb sp (.Mgoto lbl :: c) rs m) E0 (.State s fb sp c' rs m)
  | Mcond_true (s fb f sp cond args lbl c rs m c' rs') :
      evalCondition cond (args.map rs) m = some true →
      Genv.findFunctPtr ge fb = some (.Internal f) →
      findLabel lbl f.fn_code = some c' →
      rs' = undefRegs (destroyedByCond cond) rs →
      Step (.State s fb sp (.Mcond cond args lbl :: c) rs m) E0 (.State s fb sp c' rs' m)
  | Mcond_false (s f sp cond args lbl c rs m rs') :
      evalCondition cond (args.map rs) m = some false →
      rs' = undefRegs (destroyedByCond cond) rs →
      Step (.State s f sp (.Mcond cond args lbl :: c) rs m) E0 (.State s f sp c rs' m)
  | Mjumptable (s fb f sp arg tbl c rs m n lbl c' rs') :
      rs arg = .Vint n →
      CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some lbl →
      Genv.findFunctPtr ge fb = some (.Internal f) →
      findLabel lbl f.fn_code = some c' →
      rs' = undefRegs destroyedByJumptable rs →
      Step (.State s fb sp (.Mjumptable arg tbl :: c) rs m) E0 (.State s fb sp c' rs' m)
  | Mreturn (s fb stk soff c rs m f m') :
      Genv.findFunctPtr ge fb = some (.Internal f) →
      loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (parentSp s) →
      loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (parentRa s) →
      Mem.free m stk 0 f.fn_stacksize = some m' →
      Step (.State s fb (.Vptr stk soff) (.Mreturn :: c) rs m) E0 (.Returnstate s rs m')
  | function_internal (s fb rs m f m1 m2 m3 stk rs') :
      Genv.findFunctPtr ge fb = some (.Internal f) →
      Mem.alloc m 0 f.fn_stacksize = (m1, stk) →
      storeStack m1 (.Vptr stk Integers.Ptrofs.zero) Tptr f.fn_link_ofs (parentSp s) = some m2 →
      storeStack m2 (.Vptr stk Integers.Ptrofs.zero) Tptr f.fn_retaddr_ofs (parentRa s) = some m3 →
      rs' = undefRegs destroyedAtFunctionEntry rs →
      Step (.Callstate s fb rs m) E0
        (.State s fb (.Vptr stk Integers.Ptrofs.zero) f.fn_code rs' m3)
  | function_external (s fb rs m t rs' ef args res m') :
      Genv.findFunctPtr ge fb = some (.External ef) →
      ExtcallArguments abi rs m (parentSp s) ef.sig args →
      externalCall ef ge.toSenv args m t res m' →
      rs' = setPair (locResult ef.sig) res (undefCallerSaveRegs rs) →
      Step (.Callstate s fb rs m) t (.Returnstate s rs' m')
  | return (s f sp ra c rs m) :
      Step (.Returnstate (.Stackframe f sp ra c :: s) rs m) E0 (.State s f sp c rs m)

end RELSEM

/-- `Mach.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (fb m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some fb →
      InitialState p (.Callstate [] fb (Regset.init .Vundef) m0)

/-- `Mach.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (rs m r retcode) :
      locResult signature_main = .One r →
      rs r = .Vint retcode →
      FinalState (.Returnstate [] rs m) retcode

/-- `Mach.semantics` -/
def semantics (abi : AbiKind) (rao : Function → Code → Integers.Ptrofs → Prop) (p : Program) :
    Semantics where
  state := State
  step := Step abi rao p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

/-- `Mach.is_leaf_function` -/
def isLeafFunction (f : Function) : Bool :=
  f.fn_code.all (fun i => match i with | .Mcall _ _ => false | _ => true)

section WF_STATES
variable (ge : CGenv)

/-- `Mach.wf_frame` -/
inductive WfFrame : Stackframe → Prop where
  | intro (fb sp ra c f) :
      Genv.findFunctPtr ge fb = some (.Internal f) →
      isLeafFunction f = false →
      c <:+ f.fn_code →
      WfFrame (.Stackframe fb sp ra c)

/-- `Mach.wf_state` -/
inductive WfState : State → Prop where
  | normal (s fb sp c rs m f) :
      (∀ fr ∈ s, WfFrame ge fr) →
      Genv.findFunctPtr ge fb = some (.Internal f) →
      c <:+ f.fn_code →
      WfState (.State s fb sp c rs m)
  | call (s fb rs m) : (∀ fr ∈ s, WfFrame ge fr) → WfState (.Callstate s fb rs m)
  | ret (s rs m) : (∀ fr ∈ s, WfFrame ge fr) → WfState (.Returnstate s rs m)

theorem suffix_cons_tail {α : Type} {a : α} {c l : List α} (h : a :: c <:+ l) : c <:+ l :=
  (List.suffix_cons a c).trans h

/-- `Mach.wf_step` -/
theorem wf_step {abi rao} {S1 t S2} (hs : Step abi rao ge S1 t S2) (hwf : WfState ge S1) :
    WfState ge S2 := by
  cases hs with
  | Mcall s fb sp sig ros c rs m f f' ra _ hf _ =>
    cases hwf with
    | normal _ _ _ _ _ _ f0 hst hf0 ht =>
      rw [hf] at hf0; cases hf0
      refine .call _ _ _ _ ?_
      intro fr hfr
      rcases List.mem_cons.mp hfr with rfl | hfr
      · refine .intro _ _ _ _ f hf ?_ (suffix_cons_tail ht)
        cases hl : isLeafFunction f
        · rfl
        · exfalso
          simp only [isLeafFunction, List.all_eq_true] at hl
          have := hl _ (ht.subset (List.mem_cons_self))
          simp at this
      · exact hst fr hfr
  | Mgoto s fb f sp lbl c rs m c' hf hl =>
    cases hwf with
    | normal _ _ _ _ _ _ f0 hst hf0 _ =>
      rw [hf] at hf0; cases hf0
      exact .normal _ _ _ _ _ _ f hst hf (findLabel_tail hl)
  | Mcond_true s fb f sp cond args lbl c rs m c' rs' _ hf hl _ =>
    cases hwf with
    | normal _ _ _ _ _ _ f0 hst hf0 _ =>
      rw [hf] at hf0; cases hf0
      exact .normal _ _ _ _ _ _ f hst hf (findLabel_tail hl)
  | Mjumptable s fb f sp arg tbl c rs m n lbl c' rs' _ _ hf hl _ =>
    cases hwf with
    | normal _ _ _ _ _ _ f0 hst hf0 _ =>
      rw [hf] at hf0; cases hf0
      exact .normal _ _ _ _ _ _ f hst hf (findLabel_tail hl)
  | Mtailcall => cases hwf with
    | normal _ _ _ _ _ _ _ hst _ _ => exact .call _ _ _ _ hst
  | Mreturn => cases hwf with
    | normal _ _ _ _ _ _ _ hst _ _ => exact .ret _ _ _ hst
  | function_internal s fb rs m f _ _ _ _ _ hf =>
    cases hwf with
    | call _ _ _ _ hst => exact .normal _ _ _ _ _ _ f hst hf (List.suffix_refl _)
  | function_external => cases hwf with
    | call _ _ _ _ hst => exact .ret _ _ _ hst
  | «return» s f sp ra c rs m =>
    cases hwf with
    | ret _ _ _ hst =>
      have hfr := hst _ List.mem_cons_self
      cases hfr with
      | intro _ _ _ _ f0 hf _ ht =>
        exact .normal _ _ _ _ _ _ f0 (fun fr h => hst fr (List.mem_cons_of_mem _ h)) hf ht
  | _ =>
    cases hwf with
    | normal _ _ _ _ _ _ f0 hst hf0 ht => exact .normal _ _ _ _ _ _ f0 hst hf0 (suffix_cons_tail ht)

end WF_STATES

/-- `Mach.wf_initial` -/
theorem wf_initial (p : Program) {S} (h : InitialState p S) : WfState p.globalenv S := by
  cases h; exact .call _ _ _ _ (by simp)

theorem singleEvents (abi rao) (p : Program) : SingleEvents (semantics abi rao p) := by
  intro s t s' h
  have hinj : (Genv.toSenv p.globalenv).SymbolsInjective := Genv.toSenv_symbolsInjective
    (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
  cases h with
  | Mbuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | function_external _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | _ => simp [E0]

/-- Mach is receptive (not stated in Rocq's `Mach.v`). -/
theorem semantics_receptive (abi rao) (p : Program)
    (hx : ExternalsReceptive (Genv.toSenv p.globalenv)) :
    Receptive (semantics abi rao p) where
  sr_receptive := by
    intro s t1 s1 t2 h hm
    have hp := Genv.toSenv_publicSymbolExists p.globalenv
    have h' := h
    cases h with
    | Mbuiltin s f sp rs m ef args res b vargs t vres rs' m' hargs hec hrs =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .Mbuiltin s f sp rs m ef args res b vargs t2 vres2 _ m2 hargs h2 rfl⟩
    | function_external s fb rs m t rs' ef args res m' hf hargs hec hrs =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .function_external s fb rs m t2 _ ef args vres2 m2 hf hargs h2 rfl⟩
    | _ => rw [EventsReceptive.matchTraces_E0 hm]; exact ⟨_, h'⟩
  sr_traces := singleEvents abi rao p

set_option maxHeartbeats 4000000 in
theorem step_determ {abi rao} {ge : CGenv} (hinj : (Genv.toSenv ge).SymbolsInjective)
    (hrao : ∀ f c ra1 ra2, rao f c ra1 → rao f c ra2 → ra1 = ra2)
    {s t1 s1 t2 s2} (h1 : Step abi rao ge s t1 s1) (h2 : Step abi rao ge s t2 s2) :
    MatchTraces (Genv.toSenv ge) t1 t2 ∧ (t1 = t2 → s1 = s2) := by
  cases h1 <;> cases h2 <;>
    try (first
          | exact ⟨MatchTraces.nil, fun _ => rfl⟩
          | (exfalso; simp_all; done))
  case Mcall.Mcall =>
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    pair_using (@some_eq_some_inj Fundef _ _ _) as hf
    cases hf
    pair_using (@some_eq_some_inj Block _ _ _) as hb
    subst hb
    pair_using hrao _ _ _ _ as hr
    subst hr; rfl
  case Mbuiltin.Mbuiltin =>
    determ_using [evalBuiltinArgs_determ]
    pair_using (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ as hp
    obtain ⟨hmt, hrest⟩ := hp
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    subst hv hm
    simp_all
  case function_external.function_external =>
    pair_using (@some_eq_some_inj Fundef _ _ _) as hf
    cases hf
    determ_using [extcallArguments_determ]
    have hp := (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _
      ‹externalCall _ _ _ _ t1 _ _› ‹externalCall _ _ _ _ t2 _ _›
    obtain ⟨hmt, hrest⟩ := hp
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    subst hv hm
    simp_all
  all_goals
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    simp_all

/-- Mach is determinate when `return_address_offset` is functional (not
    stated in Rocq's `Mach.v`). -/
theorem semantics_determinate (abi rao) (p : Program)
    (hrao : ∀ f c ra1 ra2, rao f c ra1 → rao f c ra2 → ra1 = ra2) :
    Smallstep.Determinate (semantics abi rao p) where
  sd_determ := fun _ _ _ _ _ h1 h2 =>
    step_determ (Genv.toSenv_symbolsInjective
      (Genv.symbInjective_globalenv p.prog_public p.prog_defs)) hrao h1 h2
  sd_traces := singleEvents abi rao p
  sd_initial_determ := by
    intro s1 s2 h1 h2
    cases h1 with
    | intro _ _ hm1 hs1 =>
      cases h2 with
      | intro _ _ hm2 hs2 =>
        rw [hm1] at hm2; rw [hs1] at hs2
        simp only [Option.some.injEq] at hm2 hs2
        subst hm2; subst hs2; rfl
  sd_final_nostep := by
    intro s r h t s' hs
    cases h; cases hs
  sd_final_determ := by
    intro s r1 r2 h1 h2
    cases h1 with
    | intro _ _ _ _ hr1 h1 =>
      cases h2 with
      | intro _ _ _ _ hr2 h2 =>
        rw [hr1] at hr2; cases hr2
        rw [h1] at h2; cases h2; rfl

end Mach
end CC
