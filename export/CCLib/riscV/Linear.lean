/-
  [RISC-V instance of `CCLib/backend/Linear.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Linear: linearized LTL code with labels and gotos — port of
  `backend/Linear.v` (syntax, `is_label`, `find_label`, semantics).

  Additions not in Rocq: `semantics_receptive` and `semantics_determinate`.

  Differences from Rocq: `Archi.abi` is an explicit argument `abi` of the
  semantics (it is used by `loc_arguments`).
-/
import CCLib.riscV.LTL

namespace CC
namespace RiscV
namespace Linear

open Op Smallstep Conventions1 LTL

/-- `Linear.label` -/
abbrev Label := Positive

/-- `Linear.instruction` -/
inductive Instruction where
  | Lgetstack (sl : Slot) (ofs : Z) (ty : ATyp) (dst : Mreg)
  | Lsetstack (src : Mreg) (sl : Slot) (ofs : Z) (ty : ATyp)
  | Lop (op : Operation) (args : List Mreg) (res : Mreg)
  | Lload (chunk : Chunk) (addr : Addressing) (args : List Mreg) (dst : Mreg)
  | Lstore (chunk : Chunk) (addr : Addressing) (args : List Mreg) (src : Mreg)
  | Lcall (sg : Signature) (ros : Sum Mreg Ident)
  | Ltailcall (sg : Signature) (ros : Sum Mreg Ident)
  | Lbuiltin (ef : ExtFun) (args : List (BuiltinArg Loc)) (res : BuiltinRes Mreg)
  | Llabel (lbl : Label)
  | Lgoto (lbl : Label)
  | Lcond (cond : Condition) (args : List Mreg) (lbl : Label)
  | Ljumptable (arg : Mreg) (tbl : List Label)
  | Lreturn

/-- `Linear.code` -/
abbrev Code := List Instruction

/-- `Linear.function` -/
structure Function where
  fn_sig : Signature
  fn_stacksize : Z
  fn_code : Code

/-- `Linear.fundef` -/
abbrev Fundef := ASTFundef Function
/-- `Linear.program` -/
abbrev Program := ASTProgram Fundef Unit

/-- `Linear.funsig` -/
def funsig : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External ef => ef.sig

/-- `Linear.genv` -/
abbrev CGenv := Genv Fundef Unit

/-- `Linear.is_label` -/
def isLabel (lbl : Label) : Instruction → Bool
  | .Llabel lbl' => decide (lbl = lbl')
  | _ => false

/-- `Linear.is_label_correct` -/
theorem isLabel_correct (lbl : Label) (instr : Instruction) :
    if isLabel lbl instr then instr = .Llabel lbl else instr ≠ .Llabel lbl := by
  cases instr <;> simp [isLabel]
  case Llabel l => by_cases h : lbl = l <;> simp [h, eq_comm]

/-- `Linear.find_label` -/
def findLabel (lbl : Label) : Code → Option Code
  | [] => none
  | i1 :: il => if isLabel lbl i1 then some il else findLabel lbl il

/-- `Linear.stackframe` -/
inductive Stackframe where
  | Stackframe (f : Function) (sp : Val) (rs : Locset) (c : Code)

/-- `Linear.state` -/
inductive State where
  | State (stack : List Stackframe) (f : Function) (sp : Val) (c : Code) (rs : Locset) (m : Mem)
  | Callstate (stack : List Stackframe) (f : Fundef) (rs : Locset) (m : Mem)
  | Returnstate (stack : List Stackframe) (rs : Locset) (m : Mem)

/-- `Linear.parent_locset` -/
def parentLocset : List Stackframe → Locset
  | [] => Locmap.init .Vundef
  | .Stackframe _ _ ls _ :: _ => ls

section RELSEM
variable (ge : CGenv)

/-- `Linear.find_function` -/
def findFunction (ros : Sum Mreg Ident) (rs : Locset) : Option Fundef :=
  match ros with
  | .inl r => Genv.findFunct ge (rs (.R r))
  | .inr symb =>
      match Genv.findSymbol ge symb with
      | none => none
      | some b => Genv.findFunctPtr ge b

/-- `Linear.step` -/
inductive Step : State → Trace → State → Prop where
  | Lgetstack (s f sp sl ofs ty dst b rs m rs') :
      rs' = Locmap.set (.R dst) (rs (.S sl ofs ty)) (undefRegs (destroyedByGetstack sl) rs) →
      Step (.State s f sp (.Lgetstack sl ofs ty dst :: b) rs m) E0 (.State s f sp b rs' m)
  | Lsetstack (s f sp src sl ofs ty b rs m rs') :
      rs' = Locmap.set (.S sl ofs ty) (rs (.R src)) (undefRegs (destroyedBySetstack ty) rs) →
      Step (.State s f sp (.Lsetstack src sl ofs ty :: b) rs m) E0 (.State s f sp b rs' m)
  | Lop (s f sp op args res b rs m v rs') :
      evalOperation ge sp op (reglist rs args) m = some v →
      rs' = Locmap.set (.R res) v (undefRegs (destroyedByOp op) rs) →
      Step (.State s f sp (.Lop op args res :: b) rs m) E0 (.State s f sp b rs' m)
  | Lload (s f sp chunk addr args dst b rs m a v rs') :
      evalAddressing ge sp addr (reglist rs args) = some a →
      Mem.loadv chunk m a = some v →
      rs' = Locmap.set (.R dst) v (undefRegs (destroyedByLoad chunk addr) rs) →
      Step (.State s f sp (.Lload chunk addr args dst :: b) rs m) E0 (.State s f sp b rs' m)
  | Lstore (s f sp chunk addr args src b rs m m' a rs') :
      evalAddressing ge sp addr (reglist rs args) = some a →
      Mem.storev chunk m a (rs (.R src)) = some m' →
      rs' = undefRegs (destroyedByStore chunk addr) rs →
      Step (.State s f sp (.Lstore chunk addr args src :: b) rs m) E0 (.State s f sp b rs' m')
  | Lcall (s f sp sig ros b rs m f') :
      findFunction ge ros rs = some f' →
      sig = funsig f' →
      Step (.State s f sp (.Lcall sig ros :: b) rs m) E0
        (.Callstate (.Stackframe f sp rs b :: s) f' rs m)
  | Ltailcall (s f stk sig ros b rs m rs' f' m') :
      rs' = returnRegs (parentLocset s) rs →
      findFunction ge ros rs' = some f' →
      sig = funsig f' →
      Mem.free m stk 0 f.fn_stacksize = some m' →
      Step (.State s f (.Vptr stk Integers.Ptrofs.zero) (.Ltailcall sig ros :: b) rs m) E0
        (.Callstate s f' rs' m')
  | Lbuiltin (s f sp rs m ef args res b vargs t vres rs' m') :
      EvalBuiltinArgs ge.toSenv rs sp m args vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      rs' = Locmap.setres res vres (undefRegs (destroyedByBuiltin ef) rs) →
      Step (.State s f sp (.Lbuiltin ef args res :: b) rs m) t (.State s f sp b rs' m')
  | Llabel (s f sp lbl b rs m) :
      Step (.State s f sp (.Llabel lbl :: b) rs m) E0 (.State s f sp b rs m)
  | Lgoto (s f sp lbl b rs m b') :
      findLabel lbl f.fn_code = some b' →
      Step (.State s f sp (.Lgoto lbl :: b) rs m) E0 (.State s f sp b' rs m)
  | Lcond_true (s f sp cond args lbl b rs m rs' b') :
      evalCondition cond (reglist rs args) m = some true →
      rs' = undefRegs (destroyedByCond cond) rs →
      findLabel lbl f.fn_code = some b' →
      Step (.State s f sp (.Lcond cond args lbl :: b) rs m) E0 (.State s f sp b' rs' m)
  | Lcond_false (s f sp cond args lbl b rs m rs') :
      evalCondition cond (reglist rs args) m = some false →
      rs' = undefRegs (destroyedByCond cond) rs →
      Step (.State s f sp (.Lcond cond args lbl :: b) rs m) E0 (.State s f sp b rs' m)
  | Ljumptable (s f sp arg tbl b rs m n lbl b' rs') :
      rs (.R arg) = .Vint n →
      CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some lbl →
      findLabel lbl f.fn_code = some b' →
      rs' = undefRegs destroyedByJumptable rs →
      Step (.State s f sp (.Ljumptable arg tbl :: b) rs m) E0 (.State s f sp b' rs' m)
  | Lreturn (s f stk b rs m m') :
      Mem.free m stk 0 f.fn_stacksize = some m' →
      Step (.State s f (.Vptr stk Integers.Ptrofs.zero) (.Lreturn :: b) rs m) E0
        (.Returnstate s (returnRegs (parentLocset s) rs) m')
  | function_internal (s f rs m rs' m' stk) :
      Mem.alloc m 0 f.fn_stacksize = (m', stk) →
      rs' = undefRegs destroyedAtFunctionEntry (callRegs rs) →
      Step (.Callstate s (.Internal f) rs m) E0
        (.State s f (.Vptr stk Integers.Ptrofs.zero) f.fn_code rs' m')
  | function_external (s ef args res rs1 rs2 m t m') :
      args = (locArguments  ef.sig).map (fun p => Locmap.getpair p rs1) →
      externalCall ef ge.toSenv args m t res m' →
      rs2 = Locmap.setpair (locResult ef.sig) res (undefCallerSaveRegs rs1) →
      Step (.Callstate s (.External ef) rs1 m) t (.Returnstate s rs2 m')
  | return (s f sp rs0 c rs m) :
      Step (.Returnstate (.Stackframe f sp rs0 c :: s) rs m) E0 (.State s f sp c rs m)

end RELSEM

/-- `Linear.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (b f m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      InitialState p (.Callstate [] f (Locmap.init .Vundef) m0)

/-- `Linear.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (rs m retcode) :
      Locmap.getpair ((locResult signature_main).map Loc.R) rs = .Vint retcode →
      FinalState (.Returnstate [] rs m) retcode

/-- `Linear.semantics` -/
def semantics (p : Program) : Semantics where
  state := State
  step := Step  p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

theorem singleEvents (p : Program) : SingleEvents (semantics  p) := by
  intro s t s' h
  have hinj : (Genv.toSenv p.globalenv).SymbolsInjective := Genv.toSenv_symbolsInjective
    (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
  cases h with
  | Lbuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | function_external _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | _ => simp [E0]

/-- Linear is receptive (not stated in Rocq's `Linear.v`). -/
theorem semantics_receptive (p : Program)
    (hx : ExternalsReceptive (Genv.toSenv p.globalenv)) :
    Receptive (semantics  p) where
  sr_receptive := by
    intro s t1 s1 t2 h hm
    have hp := Genv.toSenv_publicSymbolExists p.globalenv
    have h' := h
    cases h with
    | Lbuiltin s f sp rs m ef args res b vargs t vres rs' m' hargs hec hrs =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .Lbuiltin s f sp rs m ef args res b vargs t2 vres2 _ m2 hargs h2 rfl⟩
    | function_external s ef args res rs1 rs2 m t m' hargs hec hrs =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .function_external s ef args vres2 rs1 _ m t2 m2 hargs h2 rfl⟩
    | _ => rw [EventsReceptive.matchTraces_E0 hm]; exact ⟨_, h'⟩
  sr_traces := singleEvents  p

set_option maxHeartbeats 2000000 in
theorem step_determ {ge : CGenv} (hinj : (Genv.toSenv ge).SymbolsInjective)
    {s t1 s1 t2 s2} (h1 : Step  ge s t1 s1) (h2 : Step  ge s t2 s2) :
    MatchTraces (Genv.toSenv ge) t1 t2 ∧ (t1 = t2 → s1 = s2) := by
  cases h1 <;> cases h2 <;>
    try (first
          | exact ⟨MatchTraces.nil, fun _ => rfl⟩
          | (exfalso; simp_all; done))
  case Lbuiltin.Lbuiltin =>
    determ_using [evalBuiltinArgs_determ]
    pair_using (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ as hp
    obtain ⟨hmt, hrest⟩ := hp
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    subst hv hm
    simp_all
  case function_external.function_external =>
    subst_vars
    pair_using (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ as hp
    obtain ⟨hmt, hrest⟩ := hp
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    rw [hv, hm]
  all_goals
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    simp_all

/-- Linear is determinate (not stated in Rocq's `Linear.v`). -/
theorem semantics_determinate (p : Program) :
    Smallstep.Determinate (semantics  p) where
  sd_determ := fun _ _ _ _ _ h1 h2 =>
    step_determ (Genv.toSenv_symbolsInjective
      (Genv.symbInjective_globalenv p.prog_public p.prog_defs)) h1 h2
  sd_traces := singleEvents  p
  sd_initial_determ := by
    intro s1 s2 h1 h2
    cases h1 with
    | intro _ _ _ hm1 hs1 hf1 _ =>
      cases h2 with
      | intro _ _ _ hm2 hs2 hf2 _ =>
        rw [hm1] at hm2; rw [hs1] at hs2
        simp only [Option.some.injEq] at hm2 hs2
        subst hm2; subst hs2
        rw [hf1] at hf2
        simp only [Option.some.injEq] at hf2
        subst hf2; rfl
  sd_final_nostep := by
    intro s r h t s' hs
    cases h; cases hs
  sd_final_determ := by
    intro s r1 r2 h1 h2
    cases h1 with
    | intro _ _ _ h1 =>
      cases h2 with
      | intro _ _ _ h2 =>
        rw [h1] at h2; cases h2; rfl

end Linear
end RiscV
end CC
