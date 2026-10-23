/-
  Live range splitting over RTL — port of `backend/Splitting.ml` (AArch64
  back end; the copies for the other targets are in `CCLib/x86/` and
  `CCLib/riscV/`).

  Every pseudo-register is renamed so that each of its live ranges gets its
  own register.  Live ranges are unification variables: the OCaml records
  with a mutable `kind` field become indices into the array
  `SplitState.ranges`, and the analysis runs in the monad `SplitM`, which
  also carries the generator of fresh registers of `XTL` (the renamed
  registers are created by `XTL.new_reg`, as in OCaml).  The analysis uses
  the solver `XTL.backwardFixpoint` instead of Kildall's
  `Backward_Dataflow_Solver`.
-/
import CCLib.x86.XTL

namespace CC
namespace X86
namespace Splitting

open RTL

/-- `Splitting.live_range_kind` -/
inductive LiveRangeKind where
  | Link (lr : Nat)
  | Var
  | Reg (r : Reg)
  deriving Inhabited

/-- The state of the analysis: the live ranges and the cache
    `live_range_cache` of the live ranges of `(pc, used register)` pairs. -/
structure SplitState where
  ranges : Array LiveRangeKind := #[]
  cache : Std.HashMap (Positive × Positive) Nat := {}
  deriving Inhabited

/-- Computations on live ranges. -/
abbrev SplitM := StateT SplitState XTL.TempM

/-- `Splitting.new_range` -/
def newRange : SplitM Nat := do
  let st ← get
  set { st with ranges := st.ranges.push .Var }
  return st.ranges.size

/-- `Splitting.repr`, with path compression. -/
partial def repr (lr : Nat) : SplitM Nat := do
  match (← get).ranges[lr]! with
  | .Link lr' =>
    let lr'' ← repr lr'
    modify fun st => { st with ranges := st.ranges.set! lr (.Link lr'') }
    return lr''
  | _ => return lr

/-- `Splitting.same_range` -/
def sameRange (lr1 lr2 : Nat) : SplitM Bool := do
  if lr1 == lr2 then return true
  return (← repr lr1) == (← repr lr2)

/-- `Splitting.unify` -/
def unify (lr1 lr2 : Nat) : SplitM Unit := do
  let lr1 ← repr lr1
  let lr2 ← repr lr2
  if lr1 != lr2 then
    let st ← get
    match st.ranges[lr1]!, st.ranges[lr2]! with
    | .Var, _ => set { st with ranges := st.ranges.set! lr1 (.Link lr2) }
    | _, .Var => set { st with ranges := st.ranges.set! lr2 (.Link lr1) }
    | _, _ => pure ()  -- OCaml: `assert false`

/-- `Splitting.reg_for` -/
def regFor (lr : Nat) : SplitM Reg := do
  let lr ← repr lr
  match (← get).ranges[lr]! with
  | .Reg r => return r
  | _ =>
    let r ← (XTL.newReg : XTL.TempM Reg)
    modify fun st => { st with ranges := st.ranges.set! lr (.Reg r) }
    return r

/-! ## The lattice of live ranges (`LRMap`): live register ↦ live range -/

/-- `Splitting.LRMap.t` -/
abbrev LRMap := Std.HashMap Reg Nat

/-- `LRMap.beq` -/
def lrBeq (m1 m2 : LRMap) : SplitM Bool := do
  if m1.size != m2.size then return false
  for (r, lr1) in m1.toList do
    match m2.get? r with
    | none => return false
    | some lr2 => if !(← sameRange lr1 lr2) then return false
  return true

/-- `LRMap.lub` (unifies the live ranges of the registers live in both). -/
def lrLub (m1 m2 : LRMap) : SplitM LRMap := do
  let mut m := m1
  for (r, lr2) in m2.toList do
    match m1.get? r with
    | some lr1 => unify lr1 lr2
    | none => m := m.insert r lr2
  return m

/-- `Splitting.live_range_for` -/
def liveRangeFor (pc r : Positive) : SplitM Nat := do
  match (← get).cache.get? (pc, r) with
  | some lr => return lr
  | none =>
    let lr ← newRange
    modify fun st => { st with cache := st.cache.insert (pc, r) lr }
    return lr

/-- `Splitting.reg_live` -/
def regLive (pc : Positive) (r : Reg) (map : LRMap) : SplitM LRMap := do
  if map.contains r then return map
  return map.insert r (← liveRangeFor pc r)

/-- `Splitting.reg_list_live` -/
def regListLive (pc : Positive) (rl : List Reg) (map : LRMap) : SplitM LRMap :=
  rl.foldrM (regLive pc) map

/-- `Splitting.transfer` -/
def transfer (f : RTL.Function) (pc : Positive) (after : LRMap) : SplitM LRMap := do
  match f.fn_code.get pc with
  | none => return {}
  | some i =>
    let across := match instrDefs i with
      | none => after
      | some r => after.erase r
    regListLive pc (instrUses i) across

/-- `Splitting.analysis` -/
def analysis (f : RTL.Function) : SplitM (Std.HashMap Positive LRMap) :=
  XTL.backwardFixpoint f.fn_code successorsInstr {} lrBeq lrLub (transfer f)

/-! ## Renaming -/

/-- `Splitting.ren_reg` -/
def renReg (map : LRMap) (r : Reg) : SplitM Reg := do
  match map.get? r with
  | some lr => regFor lr
  | none => (XTL.newReg : XTL.TempM Reg)

/-- `Splitting.ren_regs` -/
def renRegs (map : LRMap) (rl : List Reg) : SplitM (List Reg) := rl.mapM (renReg map)

/-- `Splitting.ren_ros` -/
def renRos (map : LRMap) : Sum Reg Ident → SplitM (Sum Reg Ident)
  | .inl r => return .inl (← renReg map r)
  | .inr id => return .inr id

/-- Rename the registers of a builtin argument. -/
def renArg (map : LRMap) : BuiltinArg Reg → SplitM (BuiltinArg Reg)
  | .BA r => return .BA (← renReg map r)
  | .BA_splitlong hi lo => return .BA_splitlong (← renArg map hi) (← renArg map lo)
  | .BA_addptr a1 a2 => return .BA_addptr (← renArg map a1) (← renArg map a2)
  | .BA_int n => return .BA_int n
  | .BA_long n => return .BA_long n
  | .BA_float n => return .BA_float n
  | .BA_single n => return .BA_single n
  | .BA_loadstack chunk ofs => return .BA_loadstack chunk ofs
  | .BA_addrstack ofs => return .BA_addrstack ofs
  | .BA_loadglobal chunk id ofs => return .BA_loadglobal chunk id ofs
  | .BA_addrglobal id ofs => return .BA_addrglobal id ofs

/-- Rename the registers of a builtin result. -/
def renRes (map : LRMap) : BuiltinRes Reg → SplitM (BuiltinRes Reg)
  | .BR r => return .BR (← renReg map r)
  | .BR_none => return .BR_none
  | .BR_splitlong hi lo => return .BR_splitlong (← renRes map hi) (← renRes map lo)

/-- `Splitting.ren_instr` -/
def renInstr (f : RTL.Function) (maps : Std.HashMap Positive LRMap) (pc : Positive) :
    RTL.Instruction → SplitM RTL.Instruction
  | i => do
    let after := maps.getD pc {}
    let before ← transfer f pc after
    match i with
    | .Inop s => return .Inop s
    | .Iop op args res s => return .Iop op (← renRegs before args) (← renReg after res) s
    | .Iload chunk addr args dst s =>
      return .Iload chunk addr (← renRegs before args) (← renReg after dst) s
    | .Istore chunk addr args src s =>
      return .Istore chunk addr (← renRegs before args) (← renReg before src) s
    | .Icall sg ros args res s =>
      return .Icall sg (← renRos before ros) (← renRegs before args) (← renReg after res) s
    | .Itailcall sg ros args =>
      return .Itailcall sg (← renRos before ros) (← renRegs before args)
    | .Ibuiltin ef args res s =>
      return .Ibuiltin ef (← args.mapM (renArg before)) (← renRes after res) s
    | .Icond cond args s1 s2 => return .Icond cond (← renRegs before args) s1 s2
    | .Ijumptable arg tbl => return .Ijumptable (← renReg before arg) tbl
    | .Ireturn optarg =>
      match optarg with
      | none => return .Ireturn none
      | some a => return .Ireturn (some (← renReg before a))

/-- `Splitting.rename_function` -/
def renameFunction (f : RTL.Function) : XTL.TempM RTL.Function := do
  let go : SplitM RTL.Function := do
    let maps ← analysis f
    let beforeEntrypoint ← transfer f f.fn_entrypoint (maps.getD f.fn_entrypoint {})
    let params ← renRegs beforeEntrypoint f.fn_params
    let code ← (PTree.elements f.fn_code).foldlM
      (fun c (pc, i) => do return c.set pc (← renInstr f maps pc i)) PTree.empty
    return { fn_sig := f.fn_sig, fn_params := params, fn_stacksize := f.fn_stacksize,
             fn_code := code, fn_entrypoint := f.fn_entrypoint }
  go.run' {}

end Splitting
end X86
end CC
