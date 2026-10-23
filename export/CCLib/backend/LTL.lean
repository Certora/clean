/-
  LTL: location transfer language — port of `backend/LTL.v` (syntax with
  basic blocks, `call_regs`, `return_regs`, `undef_caller_save_regs`,
  semantics, `successors_block`).

  Additions not in Rocq: `semantics_receptive` and `semantics_determinate`
  (proved as for RTL).

  Differences from Rocq: `Archi.abi` (used by `loc_arguments`) is an explicit
  argument `abi` of the semantics.
-/
import CCLib.backend.RTL
import CCLib.backend.Conventions

namespace CC
namespace LTL

open Op Smallstep Conventions1

/-- `LTL.node` -/
abbrev Node := Positive

/-- `LTL.instruction` -/
inductive Instruction where
  | Lop (op : Operation) (args : List Mreg) (res : Mreg)
  | Lload (chunk : Chunk) (addr : Addressing) (args : List Mreg) (dst : Mreg)
  | Lgetstack (sl : Slot) (ofs : Z) (ty : ATyp) (dst : Mreg)
  | Lsetstack (src : Mreg) (sl : Slot) (ofs : Z) (ty : ATyp)
  | Lstore (chunk : Chunk) (addr : Addressing) (args : List Mreg) (src : Mreg)
  | Lcall (sg : Signature) (ros : Sum Mreg Ident)
  | Ltailcall (sg : Signature) (ros : Sum Mreg Ident)
  | Lbuiltin (ef : ExtFun) (args : List (BuiltinArg Loc)) (res : BuiltinRes Mreg)
  | Lbranch (s : Node)
  | Lcond (cond : Condition) (args : List Mreg) (s1 s2 : Node)
  | Ljumptable (arg : Mreg) (tbl : List Node)
  | Lreturn

/-- `LTL.bblock` -/
abbrev Bblock := List Instruction
/-- `LTL.code` -/
abbrev Code := PTree Bblock

/-- `LTL.function` -/
structure Function where
  fn_sig : Signature
  fn_stacksize : Z
  fn_code : Code
  fn_entrypoint : Node

/-- `LTL.fundef` -/
abbrev Fundef := ASTFundef Function
/-- `LTL.program` -/
abbrev Program := ASTProgram Fundef Unit

/-- `LTL.funsig` -/
def funsig : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External ef => ef.sig

/-- `LTL.genv` -/
abbrev CGenv := Genv Fundef Unit
/-- `LTL.locset` -/
abbrev Locset := Locmap

/-- `LTL.call_regs` -/
def callRegs (caller : Locset) : Locset := fun l =>
  match l with
  | .R r => caller (.R r)
  | .S .Local _ _ => .Vundef
  | .S .Incoming ofs ty => caller (.S .Outgoing ofs ty)
  | .S .Outgoing _ _ => .Vundef

/-- `LTL.return_regs` -/
def returnRegs (caller callee : Locset) : Locset := fun l =>
  match l with
  | .R r => if isCalleeSave r then caller (.R r) else callee (.R r)
  | .S .Outgoing _ _ => .Vundef
  | .S sl ofs ty => caller (.S sl ofs ty)

/-- `LTL.undef_caller_save_regs` -/
def undefCallerSaveRegs (ls : Locset) : Locset := fun l =>
  match l with
  | .R r => if isCalleeSave r then ls (.R r) else .Vundef
  | .S .Outgoing _ _ => .Vundef
  | .S sl ofs ty => ls (.S sl ofs ty)

/-- `LTL.stackframe` -/
inductive Stackframe where
  | Stackframe (f : Function) (sp : Val) (ls : Locset) (bb : Bblock)

/-- `LTL.state` -/
inductive State where
  | State (stack : List Stackframe) (f : Function) (sp : Val) (pc : Node) (ls : Locset) (m : Mem)
  | Block (stack : List Stackframe) (f : Function) (sp : Val) (bb : Bblock) (ls : Locset) (m : Mem)
  | Callstate (stack : List Stackframe) (f : Fundef) (ls : Locset) (m : Mem)
  | Returnstate (stack : List Stackframe) (ls : Locset) (m : Mem)

/-- `LTL.reglist` -/
def reglist (rs : Locset) (rl : List Mreg) : List Val := rl.map (fun r => rs (.R r))

/-- `LTL.undef_regs` -/
def undefRegs : List Mreg → Locset → Locset
  | [], rs => rs
  | r1 :: rl, rs => Locmap.set (.R r1) .Vundef (undefRegs rl rs)

/-- `LTL.destroyed_by_getstack` -/
def destroyedByGetstack : Slot → List Mreg
  | .Incoming => [tempForParentFrame]
  | _ => []

/-- `LTL.parent_locset` -/
def parentLocset : List Stackframe → Locset
  | [] => Locmap.init .Vundef
  | .Stackframe _ _ ls _ :: _ => ls

section RELSEM
variable (abi : AbiKind) (ge : CGenv)

/-- `LTL.find_function` -/
def findFunction (ros : Sum Mreg Ident) (rs : Locset) : Option Fundef :=
  match ros with
  | .inl r => Genv.findFunct ge (rs (.R r))
  | .inr symb =>
      match Genv.findSymbol ge symb with
      | none => none
      | some b => Genv.findFunctPtr ge b

/-- `LTL.step` -/
inductive Step : State → Trace → State → Prop where
  | start_block (s f sp pc rs m bb) :
      f.fn_code.get pc = some bb →
      Step (.State s f sp pc rs m) E0 (.Block s f sp bb rs m)
  | Lop (s f sp op args res bb rs m v rs') :
      evalOperation ge sp op (reglist rs args) m = some v →
      rs' = Locmap.set (.R res) v (undefRegs (destroyedByOp op) rs) →
      Step (.Block s f sp (.Lop op args res :: bb) rs m) E0 (.Block s f sp bb rs' m)
  | Lload (s f sp chunk addr args dst bb rs m a v rs') :
      evalAddressing ge sp addr (reglist rs args) = some a →
      Mem.loadv chunk m a = some v →
      rs' = Locmap.set (.R dst) v (undefRegs (destroyedByLoad chunk addr) rs) →
      Step (.Block s f sp (.Lload chunk addr args dst :: bb) rs m) E0 (.Block s f sp bb rs' m)
  | Lgetstack (s f sp sl ofs ty dst bb rs m rs') :
      rs' = Locmap.set (.R dst) (rs (.S sl ofs ty)) (undefRegs (destroyedByGetstack sl) rs) →
      Step (.Block s f sp (.Lgetstack sl ofs ty dst :: bb) rs m) E0 (.Block s f sp bb rs' m)
  | Lsetstack (s f sp src sl ofs ty bb rs m rs') :
      rs' = Locmap.set (.S sl ofs ty) (rs (.R src)) (undefRegs (destroyedBySetstack ty) rs) →
      Step (.Block s f sp (.Lsetstack src sl ofs ty :: bb) rs m) E0 (.Block s f sp bb rs' m)
  | Lstore (s f sp chunk addr args src bb rs m a rs' m') :
      evalAddressing ge sp addr (reglist rs args) = some a →
      Mem.storev chunk m a (rs (.R src)) = some m' →
      rs' = undefRegs (destroyedByStore chunk addr) rs →
      Step (.Block s f sp (.Lstore chunk addr args src :: bb) rs m) E0 (.Block s f sp bb rs' m')
  | Lcall (s f sp sig ros bb rs m fd) :
      findFunction ge ros rs = some fd →
      funsig fd = sig →
      Step (.Block s f sp (.Lcall sig ros :: bb) rs m) E0
        (.Callstate (.Stackframe f sp rs bb :: s) fd rs m)
  | Ltailcall (s f sp sig ros bb rs m fd rs' m') :
      rs' = returnRegs (parentLocset s) rs →
      findFunction ge ros rs' = some fd →
      funsig fd = sig →
      Mem.free m sp 0 f.fn_stacksize = some m' →
      Step (.Block s f (.Vptr sp Integers.Ptrofs.zero) (.Ltailcall sig ros :: bb) rs m) E0
        (.Callstate s fd rs' m')
  | Lbuiltin (s f sp ef args res bb rs m vargs t vres rs' m') :
      EvalBuiltinArgs ge.toSenv rs sp m args vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      rs' = Locmap.setres res vres (undefRegs (destroyedByBuiltin ef) rs) →
      Step (.Block s f sp (.Lbuiltin ef args res :: bb) rs m) t (.Block s f sp bb rs' m')
  | Lbranch (s f sp pc bb rs m) :
      Step (.Block s f sp (.Lbranch pc :: bb) rs m) E0 (.State s f sp pc rs m)
  | Lcond (s f sp cond args pc1 pc2 bb rs b pc rs' m) :
      evalCondition cond (reglist rs args) m = some b →
      pc = (if b then pc1 else pc2) →
      rs' = undefRegs (destroyedByCond cond) rs →
      Step (.Block s f sp (.Lcond cond args pc1 pc2 :: bb) rs m) E0 (.State s f sp pc rs' m)
  | Ljumptable (s f sp arg tbl bb rs m n pc rs') :
      rs (.R arg) = .Vint n →
      CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some pc →
      rs' = undefRegs destroyedByJumptable rs →
      Step (.Block s f sp (.Ljumptable arg tbl :: bb) rs m) E0 (.State s f sp pc rs' m)
  | Lreturn (s f sp bb rs m m') :
      Mem.free m sp 0 f.fn_stacksize = some m' →
      Step (.Block s f (.Vptr sp Integers.Ptrofs.zero) (.Lreturn :: bb) rs m) E0
        (.Returnstate s (returnRegs (parentLocset s) rs) m')
  | function_internal (s f rs m m' sp rs') :
      Mem.alloc m 0 f.fn_stacksize = (m', sp) →
      rs' = undefRegs destroyedAtFunctionEntry (callRegs rs) →
      Step (.Callstate s (.Internal f) rs m) E0
        (.State s f (.Vptr sp Integers.Ptrofs.zero) f.fn_entrypoint rs' m')
  | function_external (s ef t args res rs m rs' m') :
      args = (locArguments abi ef.sig).map (fun p => Locmap.getpair p rs) →
      externalCall ef ge.toSenv args m t res m' →
      rs' = Locmap.setpair (locResult ef.sig) res (undefCallerSaveRegs rs) →
      Step (.Callstate s (.External ef) rs m) t (.Returnstate s rs' m')
  | return (f sp rs1 bb s rs m) :
      Step (.Returnstate (.Stackframe f sp rs1 bb :: s) rs m) E0 (.Block s f sp bb rs m)

end RELSEM

/-- `LTL.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (b f m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      InitialState p (.Callstate [] f (Locmap.init .Vundef) m0)

/-- `LTL.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (rs m retcode) :
      Locmap.getpair ((locResult signature_main).map Loc.R) rs = .Vint retcode →
      FinalState (.Returnstate [] rs m) retcode

/-- `LTL.semantics` -/
def semantics (abi : AbiKind) (p : Program) : Semantics where
  state := State
  step := Step abi p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

theorem singleEvents (abi : AbiKind) (p : Program) : SingleEvents (semantics abi p) := by
  intro s t s' h
  have hinj : (Genv.toSenv p.globalenv).SymbolsInjective := Genv.toSenv_symbolsInjective
    (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
  cases h with
  | Lbuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | function_external _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | _ => simp [E0]

/-- LTL is receptive (not stated in Rocq's `LTL.v`). -/
theorem semantics_receptive (abi : AbiKind) (p : Program)
    (hx : ExternalsReceptive (Genv.toSenv p.globalenv)) :
    Receptive (semantics abi p) where
  sr_receptive := by
    intro s t1 s1 t2 h hm
    have hp := Genv.toSenv_publicSymbolExists p.globalenv
    have h' := h
    cases h with
    | Lbuiltin s f sp ef args res bb rs m vargs t vres rs' m' hargs hec hrs =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .Lbuiltin s f sp ef args res bb rs m vargs t2 vres2 _ m2 hargs h2 rfl⟩
    | function_external s ef t args res rs m rs' m' hargs hec hrs =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .function_external s ef t2 args vres2 rs m _ m2 hargs h2 rfl⟩
    | _ => rw [EventsReceptive.matchTraces_E0 hm]; exact ⟨_, h'⟩
  sr_traces := singleEvents abi p

set_option maxHeartbeats 2000000 in
theorem step_determ {abi : AbiKind} {ge : CGenv} (hinj : (Genv.toSenv ge).SymbolsInjective)
    {s t1 s1 t2 s2} (h1 : Step abi ge s t1 s1) (h2 : Step abi ge s t2 s2) :
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

/-- LTL is determinate (not stated in Rocq's `LTL.v`). -/
theorem semantics_determinate (abi : AbiKind) (p : Program) :
    Smallstep.Determinate (semantics abi p) where
  sd_determ := fun _ _ _ _ _ h1 h2 =>
    step_determ (Genv.toSenv_symbolsInjective
      (Genv.symbInjective_globalenv p.prog_public p.prog_defs)) h1 h2
  sd_traces := singleEvents abi p
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

/-! ## Operations over LTL -/

/-- `LTL.successors_block` -/
def successorsBlock : Bblock → List Node
  | [] => []
  | .Ltailcall _ _ :: _ => []
  | .Lbranch s :: _ => [s]
  | .Lcond _ _ s1 s2 :: _ => [s1, s2]
  | .Ljumptable _ tbl :: _ => tbl
  | .Lreturn :: _ => []
  | _ :: b' => successorsBlock b'

end LTL
end CC
