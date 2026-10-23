/-
  RTL: register transfer language — port of `backend/Registers.v` and
  `backend/RTL.v` (syntax, semantics, `semantics_receptive`,
  `transf_function`, `successors_instr`, `instr_uses`, `instr_defs`,
  `max_pc_function`, `max_reg_instr`/`max_reg_function`,
  `is_known_runtime_function`).

  Additions not in Rocq: `semantics_determinate` (proved as for Cminor).

  Differences from Rocq: `Regset` (an AVL set) is not ported here; register
  maps are `PMap`s, as in Rocq.
-/
import CCLib.aarch64.Op
import CCLib.common.EventsBuiltinArgs
import CCLib.backend.CminorSem
import CCLib.backend.CminorSel
import CCLib.common.ValuesLemmas
import CCLib.lib.MapsTheory
import CCLib.common.Builtins
import CCLib.common.DetermTac

namespace CC

/-- `Pos.max` -/
def Positive.max (p q : Positive) : Positive := if p.toNat ≤ q.toNat then q else p

/-! ## `Registers.v` -/

/-- `Registers.reg` -/
abbrev Reg := Positive

/-- `Registers.Regmap` -/
abbrev Regmap (A : Type) := PMap A

/-- `Registers.regmap_optget` -/
def regmapOptget {A : Type} (or : Option Reg) (dfl : A) (rs : Regmap A) : A :=
  match or with
  | none => dfl
  | some r => rs.get r

/-- `Registers.regmap_optset` -/
def regmapOptset {A : Type} (or : Option Reg) (v : A) (rs : Regmap A) : Regmap A :=
  match or with
  | none => rs
  | some r => rs.set r v

/-- `Registers.regmap_setres` -/
def regmapSetres {A : Type} (res : BuiltinRes Reg) (v : A) (rs : Regmap A) : Regmap A :=
  match res with
  | .BR r => rs.set r v
  | _ => rs

/-- `rs ## rl` -/
def Regmap.getList {A : Type} (rs : Regmap A) (rl : List Reg) : List A := rl.map rs.get

/-- `Registers.regs_lessdef` -/
def RegsLessdef (rs1 rs2 : Regmap Val) : Prop := ∀ r, Val.Lessdef (rs1.get r) (rs2.get r)

theorem regsLessdef_regs {rs1 rs2} (h : RegsLessdef rs1 rs2) :
    ∀ rl, Val.LessdefList (rs1.getList rl) (rs2.getList rl)
  | [] => .nil
  | r :: rl => .cons (h r) (regsLessdef_regs h rl)

theorem set_reg_lessdef {r v1 v2 rs1 rs2} (hv : Val.Lessdef v1 v2) (hr : RegsLessdef rs1 rs2) :
    RegsLessdef (rs1.set r v1) (rs2.set r v2) := by
  intro r'
  rw [PMap.gsspec, PMap.gsspec]
  split
  · exact hv
  · exact hr r'

theorem set_res_lessdef {res v1 v2 rs1 rs2} (hv : Val.Lessdef v1 v2) (hr : RegsLessdef rs1 rs2) :
    RegsLessdef (regmapSetres res v1 rs1) (regmapSetres res v2 rs2) := by
  cases res with
  | BR r => exact set_reg_lessdef hv hr
  | _ => exact hr

namespace RTL

open Op Smallstep

/-- `RTL.node` -/
abbrev Node := Positive

/-- `RTL.instruction` -/
inductive Instruction where
  | Inop (s : Node)
  | Iop (op : Operation) (args : List Reg) (res : Reg) (s : Node)
  | Iload (chunk : Chunk) (addr : Addressing) (args : List Reg) (dst : Reg) (s : Node)
  | Istore (chunk : Chunk) (addr : Addressing) (args : List Reg) (src : Reg) (s : Node)
  | Icall (sig : Signature) (ros : Sum Reg Ident) (args : List Reg) (res : Reg) (s : Node)
  | Itailcall (sig : Signature) (ros : Sum Reg Ident) (args : List Reg)
  | Ibuiltin (ef : ExtFun) (args : List (BuiltinArg Reg)) (res : BuiltinRes Reg) (s : Node)
  | Icond (cond : Condition) (args : List Reg) (ifso ifnot : Node)
  | Ijumptable (arg : Reg) (tbl : List Node)
  | Ireturn (arg : Option Reg)

/-- `RTL.code` -/
abbrev Code := PTree Instruction

/-- `RTL.function` -/
structure Function where
  fn_sig : Signature
  fn_params : List Reg
  fn_stacksize : Z
  fn_code : Code
  fn_entrypoint : Node

/-- `RTL.fundef` -/
abbrev Fundef := ASTFundef Function
/-- `RTL.program` -/
abbrev Program := ASTProgram Fundef Unit

/-- `RTL.funsig` -/
def funsig : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External ef => ef.sig

/-- `RTL.genv` -/
abbrev CGenv := Genv Fundef Unit
/-- `RTL.regset` -/
abbrev Regset := Regmap Val

/-- `RTL.init_regs` -/
def initRegs : List Val → List Reg → Regset
  | v1 :: vs, r1 :: rs => (initRegs vs rs).set r1 v1
  | _, _ => PMap.init .Vundef

/-- `RTL.stackframe` -/
inductive Stackframe where
  | Stackframe (res : Reg) (f : Function) (sp : Val) (pc : Node) (rs : Regset)

/-- `RTL.state` -/
inductive State where
  | State (stack : List Stackframe) (f : Function) (sp : Val) (pc : Node) (rs : Regset) (m : Mem)
  | Callstate (stack : List Stackframe) (f : Fundef) (args : List Val) (m : Mem)
  | Returnstate (stack : List Stackframe) (v : Val) (m : Mem)

section RELSEM
variable (ge : CGenv)

/-- `RTL.find_function` -/
def findFunction (ros : Sum Reg Ident) (rs : Regset) : Option Fundef :=
  match ros with
  | .inl r => Genv.findFunct ge (rs.get r)
  | .inr symb =>
      match Genv.findSymbol ge symb with
      | none => none
      | some b => Genv.findFunctPtr ge b

/-- `RTL.step` -/
inductive Step : State → Trace → State → Prop where
  | Inop (s f sp pc rs m pc') :
      f.fn_code.get pc = some (.Inop pc') →
      Step (.State s f sp pc rs m) E0 (.State s f sp pc' rs m)
  | Iop (s f sp pc rs m op args res pc' v) :
      f.fn_code.get pc = some (.Iop op args res pc') →
      evalOperation ge sp op (rs.getList args) m = some v →
      Step (.State s f sp pc rs m) E0 (.State s f sp pc' (rs.set res v) m)
  | Iload (s f sp pc rs m chunk addr args dst pc' a v) :
      f.fn_code.get pc = some (.Iload chunk addr args dst pc') →
      evalAddressing ge sp addr (rs.getList args) = some a →
      Mem.loadv chunk m a = some v →
      Step (.State s f sp pc rs m) E0 (.State s f sp pc' (rs.set dst v) m)
  | Istore (s f sp pc rs m chunk addr args src pc' a m') :
      f.fn_code.get pc = some (.Istore chunk addr args src pc') →
      evalAddressing ge sp addr (rs.getList args) = some a →
      Mem.storev chunk m a (rs.get src) = some m' →
      Step (.State s f sp pc rs m) E0 (.State s f sp pc' rs m')
  | Icall (s f sp pc rs m sig ros args res pc' fd) :
      f.fn_code.get pc = some (.Icall sig ros args res pc') →
      findFunction ge ros rs = some fd →
      funsig fd = sig →
      Step (.State s f sp pc rs m) E0
        (.Callstate (.Stackframe res f sp pc' rs :: s) fd (rs.getList args) m)
  | Itailcall (s f stk pc rs m sig ros args fd m') :
      f.fn_code.get pc = some (.Itailcall sig ros args) →
      findFunction ge ros rs = some fd →
      funsig fd = sig →
      Mem.free m stk 0 f.fn_stacksize = some m' →
      Step (.State s f (.Vptr stk Integers.Ptrofs.zero) pc rs m) E0
        (.Callstate s fd (rs.getList args) m')
  | Ibuiltin (s f sp pc rs m ef args res pc' vargs t vres m') :
      f.fn_code.get pc = some (.Ibuiltin ef args res pc') →
      EvalBuiltinArgs ge.toSenv (fun r => rs.get r) sp m args vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      Step (.State s f sp pc rs m) t (.State s f sp pc' (regmapSetres res vres rs) m')
  | Icond (s f sp pc rs m cond args ifso ifnot b pc') :
      f.fn_code.get pc = some (.Icond cond args ifso ifnot) →
      evalCondition cond (rs.getList args) m = some b →
      pc' = (if b then ifso else ifnot) →
      Step (.State s f sp pc rs m) E0 (.State s f sp pc' rs m)
  | Ijumptable (s f sp pc rs m arg tbl n pc') :
      f.fn_code.get pc = some (.Ijumptable arg tbl) →
      rs.get arg = .Vint n →
      CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some pc' →
      Step (.State s f sp pc rs m) E0 (.State s f sp pc' rs m)
  | Ireturn (s f stk pc rs m or m') :
      f.fn_code.get pc = some (.Ireturn or) →
      Mem.free m stk 0 f.fn_stacksize = some m' →
      Step (.State s f (.Vptr stk Integers.Ptrofs.zero) pc rs m) E0
        (.Returnstate s (regmapOptget or .Vundef rs) m')
  | function_internal (s f args m m' stk) :
      Val.HasArgtypeList args f.fn_sig.sig_args →
      Mem.alloc m 0 f.fn_stacksize = (m', stk) →
      Step (.Callstate s (.Internal f) args m) E0
        (.State s f (.Vptr stk Integers.Ptrofs.zero) f.fn_entrypoint (initRegs args f.fn_params) m')
  | function_external (s ef args res t m m') :
      externalCall ef ge.toSenv args m t res m' →
      Step (.Callstate s (.External ef) args m) t (.Returnstate s res m')
  | return (res f sp pc rs s vres m) :
      Step (.Returnstate (.Stackframe res f sp pc rs :: s) vres m) E0
        (.State s f sp pc (rs.set res vres) m)

end RELSEM

/-- `RTL.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (b f m0) :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv b = some f →
      funsig f = signature_main →
      InitialState p (.Callstate [] f [] m0)

/-- `RTL.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (r m) : FinalState (.Returnstate [] (.Vint r) m) r

/-- `RTL.semantics` -/
def semantics (p : Program) : Semantics where
  state := State
  step := Step p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

theorem singleEvents (p : Program) : SingleEvents (semantics p) := by
  intro s t s' h
  have hinj : (Genv.toSenv p.globalenv).SymbolsInjective := Genv.toSenv_symbolsInjective
    (Genv.symbInjective_globalenv p.prog_public p.prog_defs)
  cases h with
  | Ibuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | function_external _ _ _ _ _ _ _ hec =>
    exact (externalCall_determ _ hinj).traceLength _ _ _ _ _ hec
  | _ => simp [E0]

/-- `RTL.semantics_receptive` -/
theorem semantics_receptive (p : Program)
    (hx : ExternalsReceptive (Genv.toSenv p.globalenv)) :
    Receptive (semantics p) where
  sr_receptive := by
    intro s t1 s1 t2 h hm
    have hp := Genv.toSenv_publicSymbolExists p.globalenv
    have h' := h
    cases h with
    | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m' hi hargs hec =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .Ibuiltin s f sp pc rs m ef args res pc' vargs t2 vres2 m2 hi hargs h2⟩
    | function_external s ef args res t m m' hec =>
      obtain ⟨vres2, m2, h2⟩ := externalCall_receptive ef hp hx.ext hx.asm _ _ _ _ _ _ hec hm
      exact ⟨_, .function_external s ef args vres2 t2 m m2 h2⟩
    | _ => rw [EventsReceptive.matchTraces_E0 hm]; exact ⟨_, h'⟩
  sr_traces := singleEvents p

set_option maxHeartbeats 2000000 in
theorem step_determ {ge : CGenv} (hinj : (Genv.toSenv ge).SymbolsInjective)
    {s t1 s1 t2 s2} (h1 : Step ge s t1 s1) (h2 : Step ge s t2 s2) :
    MatchTraces (Genv.toSenv ge) t1 t2 ∧ (t1 = t2 → s1 = s2) := by
  cases h1 <;> cases h2 <;>
    try (first
          | exact ⟨MatchTraces.nil, fun _ => rfl⟩
          | (exfalso; simp_all; done))
  case Ibuiltin.Ibuiltin =>
    pair_using (@some_eq_some_inj Instruction _ _ _) as hi
    simp only [Instruction.Ibuiltin.injEq] at hi
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
    determ_using [evalBuiltinArgs_determ]
    pair_using (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ as hp
    obtain ⟨hmt, hrest⟩ := hp
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    rw [hv, hm]
  case function_external.function_external =>
    pair_using (externalCall_determ _ hinj).determ _ _ _ _ _ _ _ _ as hp
    obtain ⟨hmt, hrest⟩ := hp
    refine ⟨hmt, fun ht => ?_⟩
    obtain ⟨hv, hm⟩ := hrest ht
    rw [hv, hm]
  all_goals
    refine ⟨MatchTraces.nil, fun _ => ?_⟩
    simp_all

/-- RTL is determinate (not stated in Rocq's `RTL.v`). -/
theorem semantics_determinate (p : Program) : Smallstep.Determinate (semantics p) where
  sd_determ := fun _ _ _ _ _ h1 h2 =>
    step_determ (Genv.toSenv_symbolsInjective
      (Genv.symbInjective_globalenv p.prog_public p.prog_defs)) h1 h2
  sd_traces := singleEvents p
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
    cases h1; cases h2; rfl

/-! ## Operations on RTL abstract syntax -/

/-- `RTL.transf_function` -/
def transfFunction (transf : Node → Instruction → Instruction) (f : Function) : Function :=
  { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_stacksize := f.fn_stacksize,
    fn_code := PTree.map transf f.fn_code, fn_entrypoint := f.fn_entrypoint }

/-- `RTL.successors_instr` -/
def successorsInstr : Instruction → List Node
  | .Inop s => [s]
  | .Iop _ _ _ s => [s]
  | .Iload _ _ _ _ s => [s]
  | .Istore _ _ _ _ s => [s]
  | .Icall _ _ _ _ s => [s]
  | .Itailcall _ _ _ => []
  | .Ibuiltin _ _ _ s => [s]
  | .Icond _ _ ifso ifnot => [ifso, ifnot]
  | .Ijumptable _ tbl => tbl
  | .Ireturn _ => []

/-- `RTL.successors_map` -/
def successorsMap (f : Function) : PTree (List Node) := PTree.map1 successorsInstr f.fn_code

/-- `RTL.instr_uses` -/
def instrUses : Instruction → List Reg
  | .Inop _ => []
  | .Iop _ args _ _ => args
  | .Iload _ _ args _ _ => args
  | .Istore _ _ args src _ => src :: args
  | .Icall _ (.inl r) args _ _ => r :: args
  | .Icall _ (.inr _) args _ _ => args
  | .Itailcall _ (.inl r) args => r :: args
  | .Itailcall _ (.inr _) args => args
  | .Ibuiltin _ args _ _ => BuiltinArg.paramsList args
  | .Icond _ args _ _ => args
  | .Ijumptable arg _ => [arg]
  | .Ireturn none => []
  | .Ireturn (some arg) => [arg]

/-- `RTL.instr_defs` -/
def instrDefs : Instruction → Option Reg
  | .Iop _ _ res _ => some res
  | .Iload _ _ _ dst _ => some dst
  | .Icall _ _ _ res _ => some res
  | .Ibuiltin _ _ (.BR r) _ => some r
  | _ => none

/-- `RTL.max_pc_function` -/
def maxPcFunction (f : Function) : Positive :=
  PTree.fold (fun m pc _ => Positive.max m pc) f.fn_code .xH

/-- `RTL.max_reg_instr` -/
def maxRegInstr (m : Positive) (_pc : Node) : Instruction → Positive
  | .Inop _ => m
  | .Iop _ args res _ => args.foldl Positive.max (Positive.max res m)
  | .Iload _ _ args dst _ => args.foldl Positive.max (Positive.max dst m)
  | .Istore _ _ args src _ => args.foldl Positive.max (Positive.max src m)
  | .Icall _ (.inl r) args res _ => args.foldl Positive.max (Positive.max r (Positive.max res m))
  | .Icall _ (.inr _) args res _ => args.foldl Positive.max (Positive.max res m)
  | .Itailcall _ (.inl r) args => args.foldl Positive.max (Positive.max r m)
  | .Itailcall _ (.inr _) args => args.foldl Positive.max m
  | .Ibuiltin _ args res _ =>
      (BuiltinArg.paramsList args).foldl Positive.max (res.params.foldl Positive.max m)
  | .Icond _ args _ _ => args.foldl Positive.max m
  | .Ijumptable arg _ => Positive.max arg m
  | .Ireturn none => m
  | .Ireturn (some arg) => Positive.max arg m

/-- `RTL.max_reg_function` -/
def maxRegFunction (f : Function) : Positive :=
  Positive.max (PTree.fold maxRegInstr f.fn_code .xH) (f.fn_params.foldl Positive.max .xH)

/-- `RTL.defmap` -/
abbrev Defmap := PTree (GlobDef Fundef Unit)

/-- `RTL.is_known_runtime_function` -/
def isKnownRuntimeFunction (dm : Defmap) (ros : Sum Reg Ident) :
    Option Builtins.BuiltinFunction :=
  match ros with
  | .inl _ => none
  | .inr id =>
      match dm.get id with
      | some (.Gfun (.External (.EF_runtime name sg))) => Builtins.lookupBuiltinFunction name sg
      | _ => none

end RTL
end CC
