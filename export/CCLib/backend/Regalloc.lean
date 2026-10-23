/-
  Register allocation — port of the untrusted OCaml file
  `backend/Regalloc.ml` (AArch64 back end), on top of `XTL.lean`,
  `IRC.lean` and `Splitting.lean`.

  In Rocq, `Allocation.regalloc` is a `Parameter` that extraction binds to
  `Regalloc.regalloc` (see `extraction/extraction.v`).  Its output is checked
  by the translation validator `Allocation.check_function`, so the allocator
  is not part of the trusted base: an incorrect allocation is rejected, never
  miscompiled.  The Lean port takes it as the field `regalloc` of
  `Compiler.Config`; `Regalloc.regalloc` below is the default used by
  `CCLib/extraction/extraction.lean`.

  The file has two allocators:

  * `regallocIRC` ports `Regalloc.ml`: live-range splitting, conversion to
    XTL, dead-code elimination, iterated register coalescing (`IRC.lean`),
    spill-cost heuristics and rounds of spill/reload insertion (at most 40),
    then translation to LTL (with sequentialization of parallel moves).
  * `regallocSpillAll` is the simplest allocator that the validator accepts:
    every pseudo-register lives in its own `Local` stack slot, and each RTL
    instruction becomes an LTL block that loads its arguments into scratch
    machine registers, performs the operation, and stores the result back.
    Scratch registers: integer `X9`–`X13`, `X0`–`X8`; floating-point
    `D16`–`D31`.  They avoid `X15` (`destroyed_at_function_entry`,
    `temp_for_parent_frame`), `X16`/`X17`/`X14` (destroyed by some
    operations, jump tables and `memcpy`), and callee-save registers.

  `regalloc` runs `regallocIRC` and falls back to `regallocSpillAll` if it
  fails or if the validator rejects its result.

  The first part of this file is split off into `CCLib.backend.RegallocXTL`.
-/

import CCLib.backend.RegallocXTL

namespace CC
namespace Regalloc
open Op Conventions1 Conventions LTL
open XTL IRC

/-! ## Liveness analysis -/

/-- `Regalloc.vset_removelist` -/
def vsetRemovelist (vl : List Var) (after : VSet) : VSet := vl.foldr (fun v s => s.erase v) after
/-- `Regalloc.vset_addlist` -/
def vsetAddlist (vl : List Var) (after : VSet) : VSet := vl.foldr (fun v s => s.insert v) after

/-- `Regalloc.vset_addros` -/
def vsetAddros : Sum Var Ident → VSet → VSet
  | .inl v, after => after.insert v
  | .inr _, after => after

/-- `Regalloc.vset_addarg` -/
def vsetAddarg : BuiltinArg Var → VSet → VSet
  | .BA v, after => after.insert v
  | .BA_splitlong hi lo, after => vsetAddarg hi (vsetAddarg lo after)
  | .BA_addptr a1 a2, after => vsetAddarg a1 (vsetAddarg a2 after)
  | _, after => after

/-- `Regalloc.vset_addargs` -/
def vsetAddargs (al : List (BuiltinArg Var)) (after : VSet) : VSet := al.foldr vsetAddarg after

/-- `Regalloc.vset_removeres` -/
def vsetRemoveres : BuiltinRes Var → VSet → VSet
  | .BR v, after => after.erase v
  | .BR_none, after => after
  | .BR_splitlong hi lo, after => vsetRemoveres hi (vsetRemoveres lo after)

/-- `Regalloc.live_before` -/
def liveBefore (instr : XTL.Instruction) (after : VSet) : VSet :=
  match instr with
  | .Xmove src dst | .Xspill src dst | .Xreload src dst =>
    if after.contains dst || XTL.isStackReg src then (after.erase dst).insert src else after
  | .Xparmove srcs dsts _ _ => vsetAddlist srcs (vsetRemovelist dsts after)
  | .Xop _ args res =>
    if after.contains res then vsetAddlist args (after.erase res) else after
  | .Xload _ _ args dst =>
    if after.contains dst then vsetAddlist args (after.erase dst) else after
  | .Xstore _ _ args src => vsetAddlist args (after.insert src)
  | .Xcall _ ros args res => vsetAddlist args (vsetAddros ros (vsetRemovelist res after))
  | .Xtailcall _ ros args => vsetAddlist args (vsetAddros ros {})
  | .Xbuiltin (.EF_debug ..) _ res => vsetRemoveres res after
  | .Xbuiltin _ args res => vsetAddargs args (vsetRemoveres res after)
  | .Xbranch _ => after
  | .Xcond _ args _ _ => vsetAddlist args after
  | .Xjumptable arg _ => after.insert arg
  | .Xreturn args => vsetAddlist args {}

/-- `Regalloc.live_before_block` -/
def liveBeforeBlock : XTL.Block → VSet → VSet
  | [], after => after
  | instr :: blk, after => liveBefore instr (liveBeforeBlock blk after)

/-- `Regalloc.transfer_live` -/
def transferLive (f : XFunction) (pc : XTL.Node) (after : VSet) : VSet :=
  match f.fn_code.get pc with
  | none => {}
  | some blk => liveBeforeBlock blk after

/-- The result of the liveness analysis: the variables live after each
    block. -/
abbrev Liveness := Std.HashMap XTL.Node VSet

/-- `Regalloc.liveness_analysis` -/
def livenessAnalysis (f : XFunction) : Liveness :=
  Id.run <| backwardFixpoint f.fn_code successorsBlock ({} : VSet)
    (fun a b => pure (VSet.equal a b)) (fun a b => pure (VSet.union a b))
    (fun pc after => pure (transferLive f pc after))

/-- `PMap.get pc liveness` -/
def liveAt (lv : Liveness) (pc : XTL.Node) : VSet := lv.getD pc {}

/-! ## Dead code elimination

Eliminate pure instructions whose results are not used later; remove dead
registers from debug annotations. -/

/-- `Regalloc.dce_parmove` -/
def dceParmove (after : VSet) : List Var → List Var → List Var × List Var
  | src1 :: srcs, dst1 :: dsts =>
    let (srcs', dsts') := dceParmove after srcs dsts
    if after.contains dst1 || XTL.isStackReg src1 then (src1 :: srcs', dst1 :: dsts')
    else (srcs', dsts')
  | _, _ => ([], [])

/-- `Regalloc.keep_builtin_arg` -/
def keepBuiltinArg (after : VSet) : BuiltinArg Var → Bool
  | .BA v => after.contains v
  | .BA_splitlong a1 a2 | .BA_addptr a1 a2 => keepBuiltinArg after a1 && keepBuiltinArg after a2
  | _ => true

/-- `Regalloc.dce_instr` -/
def dceInstr (instr : XTL.Instruction) (after : VSet) (k : XTL.Block) : XTL.Block :=
  match instr with
  | .Xmove src dst =>
    if after.contains dst || XTL.isStackReg src then instr :: k else k
  | .Xparmove srcs dsts itmp ftmp =>
    match dceParmove after srcs dsts with
    | ([], []) => k
    | ([src], [dst]) => .Xmove src dst :: k
    | (srcs', dsts') => .Xparmove srcs' dsts' itmp ftmp :: k
  | .Xop _ _ res => if after.contains res then instr :: k else k
  | .Xload _ _ _ dst => if after.contains dst then instr :: k else k
  | .Xbuiltin ef@(.EF_debug ..) args res =>
    let across := vsetRemoveres res after
    .Xbuiltin ef (args.filter (keepBuiltinArg across)) res :: k
  | _ => instr :: k

/-- `Regalloc.dce_block` -/
def dceBlock : XTL.Block → VSet → VSet × XTL.Block
  | [], after => (after, [])
  | instr :: blk', after =>
    let (after', tblk') := dceBlock blk' after
    (liveBefore instr after', dceInstr instr after' tblk')

/-- `Regalloc.dead_code_elimination` -/
def deadCodeElimination (f : XFunction) (liveness : Liveness) : XFunction :=
  let code := (PTree.elements f.fn_code).foldl
    (fun c (pc, blk) => c.set pc (dceBlock blk (liveAt liveness pc)).2) PTree.empty
  { f with fn_code := code }

/-! ## Spill costs

Estimate spill costs and count other statistics for every variable.
Variables that must not be spilled are given infinite costs. -/

/-- The statistics of every pseudo-register. -/
abbrev CostTable := Std.HashMap Reg VarStats

/-- `charge` in `Regalloc.spill_costs` -/
def charge (amount : Int) (uses : Nat) (v : Var) (costs : CostTable) : CostTable :=
  match v with
  | .L _ => costs
  | .V r _ =>
    let st := costs.getD r {}
    let cost :=
      if st.cost < 0 then st.cost  -- the variable must be spilled
      else let c1 := st.cost + amount; if c1 > maxInt then maxInt else c1  -- saturating
    costs.insert r { cost := cost, usedefs := st.usedefs + uses }

/-- `charge_list` -/
def chargeList (amount : Int) (uses : Nat) (vl : List Var) (costs : CostTable) : CostTable :=
  vl.foldl (fun c v => charge amount uses v c) costs

/-- `charge_ros` -/
def chargeRos (amount : Int) : Sum Var Ident → CostTable → CostTable
  | .inl v, costs => charge amount 1 v costs
  | .inr _, costs => costs

/-- `force_stack_allocation` -/
def forceStackAllocation (v : Var) (costs : CostTable) : CostTable :=
  match v with
  | .L _ => costs
  | .V r _ => let st := costs.getD r {}; costs.insert r { st with cost := -1 }

/-- `charge_instr` -/
def chargeInstr (costs : CostTable) : XTL.Instruction → CostTable
  | .Xmove src dst =>
    if XTL.isStackReg src then forceStackAllocation dst costs
    else if XTL.isStackReg dst then forceStackAllocation src costs
    else charge 1 1 dst (charge 1 1 src costs)
  | .Xreload src dst => charge maxInt 1 dst (charge 1 1 src costs)  -- dest must not be spilled
  | .Xspill src dst => charge 1 1 dst (charge maxInt 1 src costs)   -- source must not be spilled
  | .Xparmove srcs dsts itmp ftmp =>
    charge maxInt 0 ftmp (charge maxInt 0 itmp (chargeList 1 1 dsts (chargeList 1 1 srcs costs)))
  | .Xop _ args res => charge 10 1 res (chargeList 10 1 args costs)
  | .Xload _ _ args dst => charge 10 1 dst (chargeList 10 1 args costs)
  | .Xstore _ _ args src => charge 10 1 src (chargeList 10 1 args costs)
  | .Xcall _ vos _ _ => chargeRos 10 vos costs
  | .Xtailcall _ vos _ => chargeRos 10 vos costs
  | .Xbuiltin ef args res =>
    match ef with
    | .EF_annot .. | .EF_debug .. => costs
    | .EF_vstore _ | .EF_memcpy .. =>
      -- result is not used but should not be spilled
      chargeList maxInt 0 (BuiltinRes.params res) (chargeList 10 1 (BuiltinArg.paramsList args) costs)
    | .EF_annot_val .. =>
      chargeList 1 1 (BuiltinRes.params res) (chargeList 1 1 (BuiltinArg.paramsList args) costs)
    | _ =>
      chargeList 10 1 (BuiltinRes.params res) (chargeList 10 1 (BuiltinArg.paramsList args) costs)
  | .Xbranch _ => costs
  | .Xcond _ args _ _ => chargeList 10 1 args costs
  | .Xjumptable arg _ => charge 10 1 arg costs
  | .Xreturn _ => costs

/-- `Regalloc.spill_costs`: the cost function `pseudoreg → stats`. -/
def spillCosts (f : XFunction) : Reg → VarStats :=
  let costs := (PTree.elements f.fn_code).foldl
    (fun c (_, blk) => blk.foldl chargeInstr c) ({} : CostTable)
  fun r => costs.getD r {}

/-! ## Construction and coloring of the interference graph -/

/-- `Regalloc.add_interfs_def` -/
def addInterfsDef (res : Var) (live : VSet) : GM Unit := do
  for v in live do if v != res then addInterf v res

/-- `Regalloc.add_interfs_move` -/
def addInterfsMove (src dst : Var) (live : VSet) : GM Unit := do
  for v in live do if v != src && v != dst then addInterf v dst

/-- `Regalloc.add_interfs_destroyed` -/
def addInterfsDestroyed (live : VSet) (mregs : List Mreg) : GM Unit := do
  for mr in mregs do
    for v in live do addInterf (.L (.R mr)) v

/-- `Regalloc.add_interfs_caller_save` -/
def addInterfsCallerSave (live : VSet) : GM Unit := do
  for v in live do
    let tv := XTL.typeof v
    for mr in Mreg.allMregs do
      if !(isCalleeSave mr && ATyp.subtype tv (calleeSaveType mr)) then
        addInterf (.L (.R mr)) v

/-- `Regalloc.add_interfs_live` -/
def addInterfsLive (live : VSet) (v : Var) : GM Unit := do
  for v' in live do addInterf v v'

/-- `Regalloc.add_interfs_list` -/
def addInterfsList (v : Var) (vl : List Var) : GM Unit := do
  for v' in vl do addInterf v v'

/-- `Regalloc.add_interfs_list_mreg` -/
def addInterfsListMreg (vl : List Var) (mr : Mreg) : GM Unit := do
  for v in vl do addInterf v (.L (.R mr))

/-- `Regalloc.add_interfs_pairwise` -/
def addInterfsPairwise : List Var → GM Unit
  | [] => pure ()
  | v1 :: vl => do addInterfsList v1 vl; addInterfsPairwise vl

/-- Is this an `Incoming` stack slot? -/
def isIncoming : Var → Bool
  | .L (.S .Incoming _ _) => true
  | _ => false

/-- `Regalloc.add_interfs_instr` -/
def addInterfsInstr (instr : XTL.Instruction) (live : VSet) : GM Unit :=
  match instr with
  | .Xmove src dst | .Xspill src dst | .Xreload src dst => do
    addPref src dst
    addInterfsMove src dst live
    -- Reloads from incoming slots can occur when some 64-bit parameters
    -- are split and passed as two 32-bit stack locations.
    if isIncoming src then addInterfsDef (vmreg tempForParentFrame) live
  | .Xparmove srcs dsts itmp ftmp => do
    for (s, d) in srcs.zip dsts do addPref s d
    -- Interferences with live across
    let across := vsetRemovelist dsts live
    for d in dsts do addInterfsLive across d
    addInterfsLive across itmp
    addInterfsLive across ftmp
    -- All destinations must be pairwise different
    addInterfsPairwise dsts
    -- The temporaries must be different from sources and dests
    addInterfsList itmp srcs; addInterfsList itmp dsts
    addInterfsList ftmp srcs; addInterfsList ftmp dsts
    -- Take into account destroyed reg when accessing Incoming param
    if srcs.any isIncoming then
      addInterfsList (vmreg tempForParentFrame) dsts
      addInterfsLive across (vmreg tempForParentFrame)
  | .Xop op args res => do
    match isTwoAddress op args with
    | none => addInterfsDef res live
    | some (arg1, argl) =>
      -- Treat as "res := arg1; res := op(res, argl)"
      addInterfsDef res live
      addPref arg1 res
      addInterfsMove arg1 res (vsetAddlist (res :: argl) (live.erase res))
    addInterfsDestroyed (live.erase res) (destroyedByOp op)
  | .Xload chunk addr _ dst => do
    addInterfsDef dst live
    addInterfsDestroyed (live.erase dst) (destroyedByLoad chunk addr)
  | .Xstore chunk addr _ _ => addInterfsDestroyed live (destroyedByStore chunk addr)
  | .Xcall _ vos _ res => do
    match vos with
    | .inl v => for r in destroyedAtIndirectCall do addInterf (vmreg r) v
    | .inr _ => pure ()
    addInterfsCallerSave (vsetRemovelist res live)
  | .Xtailcall _ (.inl v) _ => do
    for r in intCalleeSaveRegs ++ destroyedAtIndirectCall do addInterf (vmreg r) v
  | .Xtailcall _ (.inr _) _ => pure ()
  | .Xbuiltin ef args res => do
    -- Interferences with live across
    let across := vsetRemoveres res live
    let vres := BuiltinRes.params res
    for v in vres do addInterfsLive across v
    -- All results must be pairwise different
    addInterfsPairwise vres
    addInterfsDestroyed across (destroyedByBuiltin ef)
    match ef, args, res with
    | .EF_annot_val .., [.BA arg], .BR res => addPref arg res  -- like a move
    | .EF_inline_asm _ _ clob, _, _ =>
      let vargs := BuiltinArg.paramsList args
      -- clobbered regs interfere with res and args for GCC compatibility
      for c in clob do
        match Mreg.registerByName c with
        | none => pure ()
        | some mr => addInterfsListMreg vargs mr; addInterfsListMreg vres mr
    | _, _, _ => pure ()
  | .Xbranch _ => pure ()
  | .Xcond cond _ _ _ => addInterfsDestroyed live (destroyedByCond cond)
  | .Xjumptable _ _ => addInterfsDestroyed live destroyedByJumptable
  | .Xreturn _ => pure ()

/-- `Regalloc.add_interfs_block` -/
def addInterfsBlock : XTL.Block → VSet → GM VSet
  | [], live => return live
  | instr :: blk', live => do
    let live' ← addInterfsBlock blk' live
    addInterfsInstr instr live'
    return liveBefore instr live'

/-- `Regalloc.find_coloring` -/
def findColoring (f : XFunction) (liveness : Liveness) : Var → Loc :=
  let act : GM (Var → Loc) := do
    for (pc, blk) in PTree.elements f.fn_code do
      discard <| addInterfsBlock blk (liveAt liveness pc)
    addInterfsDestroyed (transferLive f f.fn_entrypoint (liveAt liveness f.fn_entrypoint))
      destroyedAtFunctionEntry
    coloring
  Id.run (act.run' (IRC.init (spillCosts f)))

/-! ## Determination of variables that need spill code insertion -/

section TOSPILL
variable (alloc : Var → Loc)

/-- `Regalloc.is_reg` -/
def isReg (v : Var) : Bool := match alloc v with | .R _ => true | .S .. => false

/-- `Regalloc.add_tospill` -/
def addTospill (v : Var) (ts : VSet) : VSet := if isReg alloc v then ts else ts.insert v

/-- `Regalloc.addlist_tospill` -/
def addlistTospill (vl : List Var) (ts : VSet) : VSet := vl.foldr (addTospill alloc) ts

/-- `Regalloc.addros_tospill` -/
def addrosTospill : Sum Var Ident → VSet → VSet
  | .inl v, ts => addTospill alloc v ts
  | .inr _, ts => ts

/-- `Regalloc.tospill_instr` -/
def tospillInstr (instr : XTL.Instruction) (ts : VSet) : Except String VSet :=
  match instr with
  | .Xmove src dst =>
    if isReg alloc src || isReg alloc dst || alloc src == alloc dst then .ok ts
    else .ok ((ts.insert dst).insert src)
  | .Xreload _ dst => if isReg alloc dst then .ok ts else .error "unspillable variable was spilled"
  | .Xspill src _ => if isReg alloc src then .ok ts else .error "unspillable variable was spilled"
  | .Xparmove _ _ itmp ftmp =>
    if isReg alloc itmp && isReg alloc ftmp then .ok ts
    else .error "parallel move temporary was spilled"
  | .Xop _ args res => .ok (addlistTospill alloc args (addTospill alloc res ts))
  | .Xload _ _ args dst => .ok (addlistTospill alloc args (addTospill alloc dst ts))
  | .Xstore _ _ args src => .ok (addlistTospill alloc args (addTospill alloc src ts))
  | .Xcall _ vos _ _ => .ok (addrosTospill alloc vos ts)
  | .Xtailcall _ vos _ => .ok (addrosTospill alloc vos ts)
  | .Xbuiltin (.EF_annot ..) _ _ | .Xbuiltin (.EF_debug ..) _ _ => .ok ts
  | .Xbuiltin _ args res =>
    .ok (addlistTospill alloc (BuiltinArg.paramsList args)
      (addlistTospill alloc (BuiltinRes.params res) ts))
  | .Xbranch _ => .ok ts
  | .Xcond _ args _ _ => .ok (addlistTospill alloc args ts)
  | .Xjumptable arg _ => .ok (addTospill alloc arg ts)
  | .Xreturn _ => .ok ts

/-- `Regalloc.tospill_function` -/
def tospillFunction (f : XFunction) : Except String VSet :=
  (PTree.elements f.fn_code).foldlM
    (fun ts (_, blk) => blk.foldlM (fun ts i => tospillInstr alloc i ts) ts) {}

end TOSPILL

/-! ## Spilling

A semi-naive spilling strategy: by default, spill at every definition of a
variable that could not be allocated a register, and reload before every
use, but keep a list of equations `spilled-var = temp` recording variables
recently spilled or reloaded, so as to avoid reloading a variable whose
value is still available in a temporary register. -/

/-- Equations `(var, temp, age)`. -/
abbrev Eqs := List (Var × Var × Nat)

/-- `Regalloc.find_reg_containing` -/
def findRegContaining (v : Var) : Eqs → Option Var
  | [] => none
  | (var, temp, _) :: eqs => if var == v then some temp else findRegContaining v eqs

/-- `Regalloc.add` -/
def addEq (v t : Var) (eqs : Eqs) : Eqs := (v, t, 0) :: eqs

/-- `Regalloc.kill` -/
def kill (x : Var) (eqs : Eqs) : Eqs := eqs.filter fun (v, t, _) => v != x && t != x

section SPILL
variable (tospill : VSet)

/-- `Regalloc.reload_var` -/
def reloadVar (eqs : Eqs) (v : Var) : TempM (Var × XTL.Block × Eqs) := do
  if !tospill.contains v then return (v, [], eqs)
  match findRegContaining v eqs with
  | some t => return (t, [], eqs)
  | none =>
    let t ← newTemp (XTL.typeof v)
    return (t, [.Xreload v t], addEq v t eqs)

/-- `Regalloc.reload_vars` -/
def reloadVars : Eqs → List Var → TempM (List Var × XTL.Block × Eqs)
  | eqs, [] => return ([], [], eqs)
  | eqs, v1 :: vs => do
    let (t1, c1, eqs1) ← reloadVar tospill eqs v1
    let (ts, cs, eqs2) ← reloadVars eqs1 vs
    return (t1 :: ts, c1 ++ cs, eqs2)

/-- `Regalloc.reload_arg` -/
def reloadArg : Eqs → BuiltinArg Var → TempM (BuiltinArg Var × XTL.Block × Eqs)
  | eqs, .BA v => do
    let (t, c1, eqs1) ← reloadVar tospill eqs v
    return (.BA t, c1, eqs1)
  | eqs, .BA_splitlong hi lo => do
    let (hi', c1, eqs1) ← reloadArg eqs hi
    let (lo', c2, eqs2) ← reloadArg eqs1 lo
    return (.BA_splitlong hi' lo', c1 ++ c2, eqs2)
  | eqs, .BA_addptr a1 a2 => do
    let (a1', c1, eqs1) ← reloadArg eqs a1
    let (a2', c2, eqs2) ← reloadArg eqs1 a2
    return (.BA_addptr a1' a2', c1 ++ c2, eqs2)
  | eqs, a => return (a, [], eqs)

/-- `Regalloc.reload_args` -/
def reloadArgsX : Eqs → List (BuiltinArg Var) → TempM (List (BuiltinArg Var) × XTL.Block × Eqs)
  | eqs, [] => return ([], [], eqs)
  | eqs, a1 :: al => do
    let (t1, c1, eqs1) ← reloadArg tospill eqs a1
    let (tl, cl, eqs2) ← reloadArgsX eqs1 al
    return (t1 :: tl, c1 ++ cl, eqs2)

/-- `Regalloc.save_var` -/
def saveVar (eqs : Eqs) (v : Var) : TempM (Var × XTL.Block × Eqs) := do
  if !tospill.contains v then return (v, [], kill v eqs)
  let t ← newTemp (XTL.typeof v)
  return (t, [.Xspill t v], addEq v t (kill v eqs))

/-- `Regalloc.save_res` -/
def saveRes : Eqs → BuiltinRes Var → TempM (BuiltinRes Var × XTL.Block × Eqs)
  | eqs, .BR v => do
    let (t, c1, eqs1) ← saveVar tospill eqs v
    return (.BR t, c1, eqs1)
  | eqs, .BR_none => return (.BR_none, [], eqs)
  | eqs, .BR_splitlong hi lo => do
    let (hi', c1, eqs1) ← saveRes eqs hi
    let (lo', c2, eqs2) ← saveRes eqs1 lo
    return (.BR_splitlong hi' lo', c1 ++ c2, eqs2)

/-- `Regalloc.trim`: drop equations when there are too many or when they
    are too old, to limit the live ranges of unspillable temporaries. -/
def trim (maxAge : Nat) : Nat → Eqs → Eqs
  | 0, _ => []
  | _, [] => []
  | count + 1, (v, t, date) :: eqs' =>
    if date ≤ maxAge then (v, t, date + 1) :: trim maxAge count eqs' else []

/-- `Regalloc.max_num_eqs` -/
def maxNumEqs : Nat := 3

/-- `Regalloc.spill_instr`: insertion of spill and reload instructions. -/
def spillInstr (maxAge : Nat) (eqs : Eqs) (instr : XTL.Instruction) :
    TempM (XTL.Block × Eqs) := do
  let eqs := trim maxAge maxNumEqs eqs
  match instr with
  | .Xmove src dst =>
    if tospill.contains src && tospill.contains dst then
      let (src', c1, eqs1) ← reloadVar tospill eqs src
      return (c1 ++ [.Xspill src' dst], addEq dst src' (kill dst eqs1))
    else return ([instr], kill dst eqs)
  | .Xreload .. | .Xspill .. => return ([instr], eqs)  -- OCaml: `assert false`
  | .Xparmove _ dsts _ _ => return ([instr], dsts.foldr kill eqs)
  | .Xop op args res =>
    match isTwoAddress op args with
    | none =>
      let (args', c1, eqs1) ← reloadVars tospill eqs args
      let (res', c2, eqs2) ← saveVar tospill eqs1 res
      return (c1 ++ .Xop op args' res' :: c2, eqs2)
    | some (arg1, argl) =>
      match tospill.contains res, tospill.contains arg1 with
      | false, false =>
        let (argl', c1, eqs1) ← reloadVars tospill eqs argl
        return (c1 ++ [.Xop op (arg1 :: argl') res], kill res eqs1)
      | true, false =>
        let tmp ← newTemp (XTL.typeof res)
        let (argl', c1, eqs1) ← reloadVars tospill eqs argl
        return (c1 ++ [.Xmove arg1 tmp, .Xop op (tmp :: argl') tmp, .Xspill tmp res],
                addEq res tmp (kill res eqs1))
      | false, true =>
        let eqs1 := addEq arg1 res (kill res eqs)
        let (argl', c1, eqs2) ← reloadVars tospill eqs1 argl
        return (.Xmove arg1 res :: c1 ++ [.Xop op (res :: argl') res], kill res eqs2)
      | true, true =>
        let tmp ← newTemp (XTL.typeof res)
        let eqs1 := addEq arg1 tmp eqs
        let (argl', c1, eqs2) ← reloadVars tospill eqs1 argl
        return (.Xreload arg1 tmp :: c1 ++ [.Xop op (tmp :: argl') tmp, .Xspill tmp res],
                addEq res tmp (kill tmp (kill res eqs2)))
  | .Xload chunk addr args dst =>
    let (args', c1, eqs1) ← reloadVars tospill eqs args
    let (dst', c2, eqs2) ← saveVar tospill eqs1 dst
    return (c1 ++ .Xload chunk addr args' dst' :: c2, eqs2)
  | .Xstore chunk addr args src =>
    let (args', c1, eqs1) ← reloadVars tospill eqs args
    let (src', c2, eqs2) ← reloadVar tospill eqs1 src
    return (c1 ++ c2 ++ [.Xstore chunk addr args' src'], eqs2)
  | .Xcall sg (.inl v) args res =>
    let (v', c1, _) ← reloadVar tospill eqs v
    return (c1 ++ [.Xcall sg (.inl v') args res], [])
  | .Xcall _ (.inr _) _ _ => return ([instr], [])
  | .Xtailcall sg (.inl v) args =>
    let (v', c1, _) ← reloadVar tospill eqs v
    return (c1 ++ [.Xtailcall sg (.inl v') args], [])
  | .Xtailcall _ (.inr _) _ => return ([instr], [])
  | .Xbuiltin (.EF_annot ..) _ _ | .Xbuiltin (.EF_debug ..) _ _ => return ([instr], eqs)
  | .Xbuiltin ef args res =>
    let (args', c1, eqs1) ← reloadArgsX tospill eqs args
    let (res', c2, eqs2) ← saveRes tospill eqs1 res
    return (c1 ++ .Xbuiltin ef args' res' :: c2, eqs2)
  | .Xbranch _ => return ([instr], eqs)
  | .Xcond cond args s1 s2 =>
    let (args', c1, eqs1) ← reloadVars tospill eqs args
    return (c1 ++ [.Xcond cond args' s1 s2], eqs1)
  | .Xjumptable arg tbl =>
    let (arg', c1, eqs1) ← reloadVar tospill eqs arg
    return (c1 ++ [.Xjumptable arg' tbl], eqs1)
  | .Xreturn _ => return ([instr], [])

/-- `Regalloc.spill_block` -/
def spillBlock (maxAge : Nat) : XTL.Block → Eqs → TempM (XTL.Block × Eqs)
  | [], eqs => return ([], eqs)
  | instr :: blk', eqs => do
    let (c1, eqs1) ← spillInstr tospill maxAge eqs instr
    let (c2, eqs2) ← spillBlock maxAge blk' eqs1
    return (c1 ++ c2, eqs2)

/-- `Regalloc.spill_function` -/
def spillFunction (f : XFunction) (round : Nat) : TempM XFunction :=
  let maxAge := if round ≤ 10 then 3 else if round ≤ 20 then 1 else 0
  transformBasicBlocks (fun _ blk eqs => spillBlock tospill maxAge blk eqs) ([] : Eqs) f

end SPILL

/-! ## Generation of LTL from XTL

Apply a register allocation to an XTL function.  Fails (OCaml `Bad_LTL`)
if some pseudo-registers were mapped to stack locations while machine
registers were expected. -/

section TRANSL
variable (alloc : Var → Loc)

/-- `Regalloc.mreg_of` -/
def mregOf (v : Var) : Except String Mreg :=
  match alloc v with
  | .R mr => .ok mr
  | .S .. => .error "bad LTL after spilling"

/-- `Regalloc.mregs_of` -/
def mregsOf (vl : List Var) : Except String (List Mreg) := vl.mapM (mregOf alloc)

/-- `Regalloc.mros_of` -/
def mrosOf : Sum Var Ident → Except String (Sum Mreg Ident)
  | .inl v => return .inl (← mregOf alloc v)
  | .inr id => return .inr id

end TRANSL

/-- `Regalloc.make_move` -/
def makeMove (src dst : Loc) (k : LTL.Bblock) : Except String LTL.Bblock :=
  match src, dst with
  | .R rsrc, .R rdst => .ok (if rsrc == rdst then k else .Lop .Omove [rsrc] rdst :: k)
  | .R rsrc, .S sl ofs ty => .ok (.Lsetstack rsrc sl ofs ty :: k)
  | .S sl ofs ty, .R rdst => .ok (.Lgetstack sl ofs ty rdst :: k)
  | .S .., .S .. => if src == dst then .ok k else .error "bad LTL after spilling"

/-- `Regalloc.parmove_status` -/
inductive ParmoveStatus where
  | ToMove | BeingMoved | Moved
  deriving BEq, Inhabited

/-- The mutable state of `make_parmove`. -/
structure ParmoveState where
  src : Array Loc
  status : Array ParmoveStatus
  code : List LTL.Instruction

/-- `add_move` in `make_parmove` (the code is accumulated in reverse). -/
def parmoveAddMove (itmp ftmp : Mreg) (s d : Loc) : StateM ParmoveState Unit :=
  modify fun st => { st with code := match s, d with
    | .R rs, .R rd => .Lop .Omove [rs] rd :: st.code
    | .R rs, .S sl ofs ty => .Lsetstack rs sl ofs ty :: st.code
    | .S sl ofs ty, .R rd => .Lgetstack sl ofs ty rd :: st.code
    | .S sls ofss tys, .S sld ofsd tyd =>
      let tmp := if classOfType tys == 0 then itmp else ftmp
      .Lsetstack tmp sld ofsd tyd :: .Lgetstack sls ofss tys tmp :: st.code }

/-- `move_one` in `make_parmove`. -/
partial def parmoveMoveOne (dst : Array Loc) (itmp ftmp : Mreg) (i : Nat) :
    StateM ParmoveState Unit := do
  let st ← get
  let some si := st.src[i]? | return
  let some di := dst[i]? | return
  if si != di then
    modify fun st => { st with status := st.status.set! i .BeingMoved }
    for j in [0:dst.size] do
      let st ← get
      let some sj := st.src[j]? | pure ()
      if sj == di then
        match st.status[j]? with
        | some .ToMove => parmoveMoveOne dst itmp ftmp j
        | some .BeingMoved =>
          let tmp := Loc.R (if classOfLoc sj == 0 then itmp else ftmp)
          parmoveAddMove itmp ftmp sj tmp
          modify fun st => { st with src := st.src.set! j tmp }
        | _ => pure ()
    let st ← get
    parmoveAddMove itmp ftmp (st.src[i]?.getD si) di
    modify fun st => { st with status := st.status.set! i .Moved }

/-- `Regalloc.make_parmove`: sequentialize a parallel move. -/
def makeParmove (srcs dsts : List Loc) (itmp ftmp : Mreg) (k : LTL.Bblock) : LTL.Bblock :=
  let dst := dsts.toArray
  let n := dst.size
  let act : StateM ParmoveState Unit := do
    for i in [0:n] do
      if (← get).status[i]? == some .ToMove then parmoveMoveOne dst itmp ftmp i
  let st := (Id.run (act.run { src := srcs.toArray, status := Array.replicate n .ToMove, code := [] })).2
  st.code.reverse ++ k

/-- `Regalloc.transl_instr` -/
def translInstr (alloc : Var → Loc) (instr : XTL.Instruction) (k : LTL.Bblock) :
    Except String LTL.Bblock := do
  match instr with
  | .Xmove src dst | .Xreload src dst | .Xspill src dst => makeMove (alloc src) (alloc dst) k
  | .Xparmove srcs dsts itmp ftmp =>
    return makeParmove (srcs.map alloc) (dsts.map alloc) (← mregOf alloc itmp) (← mregOf alloc ftmp) k
  | .Xop op args res =>
    let rargs ← mregsOf alloc args
    let rres ← mregOf alloc res
    match isTwoAddress op rargs with
    | none => return .Lop op rargs rres :: k
    | some (rarg1, rargl) =>
      if rarg1 == rres then return .Lop op rargs rres :: k
      else return .Lop .Omove [rarg1] rres :: .Lop op (rres :: rargl) rres :: k
  | .Xload chunk addr args dst =>
    return .Lload chunk addr (← mregsOf alloc args) (← mregOf alloc dst) :: k
  | .Xstore chunk addr args src =>
    return .Lstore chunk addr (← mregsOf alloc args) (← mregOf alloc src) :: k
  | .Xcall sg vos _ _ => return .Lcall sg (← mrosOf alloc vos) :: k
  | .Xtailcall sg vos _ => return [.Ltailcall sg (← mrosOf alloc vos)]
  | .Xbuiltin ef args res =>
    let res' : BuiltinRes Mreg ← match res with
      | .BR v => do pure (BuiltinRes.BR (← mregOf alloc v))
      | .BR_none => pure .BR_none
      | .BR_splitlong (.BR hi) (.BR lo) => do
        pure (.BR_splitlong (.BR (← mregOf alloc hi)) (.BR (← mregOf alloc lo)))
      | .BR_splitlong .. => throw "bad LTL after spilling"
    return .Lbuiltin ef (args.map (BuiltinArg.map alloc)) res' :: k
  | .Xbranch s => return [.Lbranch s]
  | .Xcond cond args s1 s2 => return [.Lcond cond (← mregsOf alloc args) s1 s2]
  | .Xjumptable arg tbl => return [.Ljumptable (← mregOf alloc arg) tbl]
  | .Xreturn _ => return [.Lreturn]

/-- `Regalloc.transl_block` -/
def translBlock (alloc : Var → Loc) : XTL.Block → Except String LTL.Bblock
  | [] => return []
  | instr :: blk' => do translInstr alloc instr (← translBlock alloc blk')

/-- `Regalloc.transl_function` -/
def translFunction (fn : XFunction) (alloc : Var → Loc) : Except String LTL.Function := do
  let code ← (PTree.elements fn.fn_code).foldlM
    (fun (c : LTL.Code) (pc, blk) => do return c.set pc (← translBlock alloc blk)) PTree.empty
  return { fn_sig := fn.fn_sig, fn_stacksize := fn.fn_stacksize,
           fn_entrypoint := fn.fn_entrypoint, fn_code := code }

/-! ## All together -/

/-- The maximal number of spilling rounds. -/
def maxRounds : Nat := 40

/-- `Regalloc.success` -/
def success (f : XFunction) (alloc : Var → Loc) : Except String LTL.Function :=
  translFunction f alloc

/-- `Regalloc.more_rounds` (`count` is the round number; `fuel` bounds the
    recursion, which OCaml stops at round 40). -/
def moreRounds (f : XFunction) : Nat → VSet → Nat → TempM (Except String LTL.Function)
  | 0, _, _ => return .error "spilling fails to converge"
  | fuel + 1, ts, count => do
    if count ≥ maxRounds then return .error "spilling fails to converge"
    let f' ← spillFunction ts f count
    let liveness := livenessAnalysis f'
    let alloc := findColoring f' liveness
    match tospillFunction alloc f' with
    | .error m => return .error m
    | .ok ts' =>
      if ts'.isEmpty then return success f' alloc
      else moreRounds f fuel (VSet.union ts ts') (count + 1)

/-- `Regalloc.first_round` -/
def firstRound (f : XFunction) (liveness : Liveness) : TempM (Except String LTL.Function) := do
  let alloc := findColoring f liveness
  match tospillFunction alloc f with
  | .error m => return .error m
  | .ok ts => if ts.isEmpty then return success f alloc else moreRounds f maxRounds ts 1

/-- `Regalloc.regalloc` of OCaml: register allocation by coloring. -/
def regallocIRC (abi : AbiKind) (f : RTL.Function) : Res LTL.Function :=
  let go : TempM (Res LTL.Function) := do
    resetTemps
    let f1 ← Splitting.renameFunction f
    match RTLtyping.typeFunction abi f1 with
    | .Error msg => return .Error ("RTL code after splitting is ill-typed: " ++ msg)
    | .OK tyenv =>
      let f2 ← functionOfRTLFunction abi f1 tyenv
      let liveness := livenessAnalysis f2
      let f3 := deadCodeElimination f2 liveness
      match ← firstRound f3 liveness with
      | .ok tf => return .OK tf
      | .error m => return .Error m
  Id.run (go.run' {})

/-- `Regalloc.regalloc`: register allocation of an RTL function.  The
    coloring allocator `regallocIRC` is tried first; if it fails, or if its
    result is rejected by the validator `Allocation.checkFunction` (which
    `Allocation.transfFunction` runs again anyway), the simple allocator
    `regallocSpillAll` is used instead. -/
def regalloc (abi : AbiKind) (f : RTL.Function) : Res LTL.Function :=
  match regallocIRC abi f with
  | .OK tf =>
    match RTLtyping.typeFunction abi f with
    | .OK env =>
      match Allocation.checkFunction abi f tf env with
      | .OK _ => .OK tf
      | .Error _ => regallocSpillAll abi f
    | .Error m => .Error m
  | .Error _ => regallocSpillAll abi f

end Regalloc
end CC
