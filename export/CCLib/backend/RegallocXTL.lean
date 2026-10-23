/-
  First part of the port of `backend/Regalloc.ml` (split from `CCLib.backend.Regalloc`): the register-allocation helpers and the conversion from RTL to XTL.
-/
import CCLib.backend.Allocation
import CCLib.backend.IRC
import CCLib.backend.Splitting

namespace CC
namespace Regalloc

open Op Conventions1 Conventions LTL

/-- Integer scratch registers. -/
def intTemps : List Mreg := [.R9, .R10, .R11, .R12, .R13, .R0, .R1, .R2, .R3, .R4, .R5, .R6, .R7, .R8]

/-- Floating-point scratch registers. -/
def floatTemps : List Mreg :=
  [.F16, .F17, .F18, .F19, .F20, .F21, .F22, .F23, .F24, .F25, .F26, .F27, .F28, .F29, .F30, .F31]

/-- Values of these types live in floating-point registers. -/
def isFloatTyp : ATyp → Bool
  | .Tfloat | .Tsingle => true
  | _ => false

/-- The first scratch register of the class of `ty`. -/
def tempFor (ty : ATyp) : Mreg := if isFloatTyp ty then .F16 else .R9

section ALLOC
variable (env : RTLtyping.Regenv)

/-- The stack slot of pseudo-register `r`: two words per register, so slots
    never overlap and are aligned for every type. -/
def slotOfs (r : Reg) : Z := 2 * ((r.toNat : Z) - 1)

/-- Load pseudo-register `r` from its slot into machine register `m`. -/
def reload (r : Reg) (m : Mreg) : Instruction := .Lgetstack .Local (slotOfs r) (env r) m

/-- Store machine register `m` into the slot of pseudo-register `r`. -/
def spill (m : Mreg) (r : Reg) : Instruction := .Lsetstack m .Local (slotOfs r) (env r)

/-- Assign scratch registers to `args`, in order, drawing integer and float
    registers from separate pools.  Returns the registers and the reloads. -/
def reloadArgs : List Reg → List Mreg → List Mreg → Option (List Mreg × Bblock)
  | [], _, _ => some ([], [])
  | r :: rs, ints, flts =>
      if isFloatTyp (env r) then
        match flts with
        | [] => none
        | m :: flts' => do
            let (ms, code) ← reloadArgs rs ints flts'
            some (m :: ms, reload env r m :: code)
      else
        match ints with
        | [] => none
        | m :: ints' => do
            let (ms, code) ← reloadArgs rs ints' flts
            some (m :: ms, reload env r m :: code)

/-- `reloadArgs` with the full scratch pools. -/
def reloadTemps (args : List Reg) : Res (List Mreg × Bblock) :=
  match reloadArgs env args intTemps floatTemps with
  | some x => .OK x
  | none => .Error "Regalloc: too many arguments"

/-- Builtin arguments: replace every pseudo-register by a scratch register
    (threading the remaining pools), collecting the reloads. -/
def reloadBuiltinArg : BuiltinArg Reg → List Mreg × List Mreg →
    Option (BuiltinArg Loc × Bblock × (List Mreg × List Mreg))
  | .BA r, (ints, flts) =>
      if isFloatTyp (env r) then
        match flts with
        | [] => none
        | m :: flts' => some (.BA (.R m), [reload env r m], (ints, flts'))
      else
        match ints with
        | [] => none
        | m :: ints' => some (.BA (.R m), [reload env r m], (ints', flts))
  | .BA_int n, p => some (.BA_int n, [], p)
  | .BA_long n, p => some (.BA_long n, [], p)
  | .BA_float f, p => some (.BA_float f, [], p)
  | .BA_single f, p => some (.BA_single f, [], p)
  | .BA_loadstack c o, p => some (.BA_loadstack c o, [], p)
  | .BA_addrstack o, p => some (.BA_addrstack o, [], p)
  | .BA_loadglobal c id o, p => some (.BA_loadglobal c id o, [], p)
  | .BA_addrglobal id o, p => some (.BA_addrglobal id o, [], p)
  | .BA_splitlong hi lo, p => do
      let (hi', c1, p1) ← reloadBuiltinArg hi p
      let (lo', c2, p2) ← reloadBuiltinArg lo p1
      some (.BA_splitlong hi' lo', c1 ++ c2, p2)
  | .BA_addptr a1 a2, p => do
      let (a1', c1, p1) ← reloadBuiltinArg a1 p
      let (a2', c2, p2) ← reloadBuiltinArg a2 p1
      some (.BA_addptr a1' a2', c1 ++ c2, p2)

/-- Builtin arguments of annotations and debug information refer directly to
    the stack slots of the pseudo-registers. -/
def slotBuiltinArg : BuiltinArg Reg → BuiltinArg Loc
  | .BA r => .BA (.S .Local (slotOfs r) (env r))
  | .BA_int n => .BA_int n
  | .BA_long n => .BA_long n
  | .BA_float f => .BA_float f
  | .BA_single f => .BA_single f
  | .BA_loadstack c o => .BA_loadstack c o
  | .BA_addrstack o => .BA_addrstack o
  | .BA_loadglobal c id o => .BA_loadglobal c id o
  | .BA_addrglobal id o => .BA_addrglobal id o
  | .BA_splitlong hi lo => .BA_splitlong (slotBuiltinArg hi) (slotBuiltinArg lo)
  | .BA_addptr a1 a2 => .BA_addptr (slotBuiltinArg a1) (slotBuiltinArg a2)

/-- All builtin arguments. -/
def reloadBuiltinArgs : List (BuiltinArg Reg) → List Mreg × List Mreg →
    Option (List (BuiltinArg Loc) × Bblock)
  | [], _ => some ([], [])
  | a :: al, p => do
      let (a', c1, p1) ← reloadBuiltinArg env a p
      let (al', c2) ← reloadBuiltinArgs al p1
      some (a' :: al', c1 ++ c2)

/-- Moves of the arguments of a call to their `loc_arguments` locations:
    arguments passed on the stack first (through the scratch register of
    their class), then arguments passed in registers. -/
def callArgMoves (args : List Reg) (locs : List (RPair Loc)) : Res Bblock := do
  let pairs := args.zip locs
  if args.length ≠ locs.length then .Error "Regalloc: bad call arguments" else
  let stk := pairs.filterMap fun (r, l) => match l with
    | .One (.S sl ofs ty) =>
        let t := tempFor (env r)
        some [reload env r t, .Lsetstack t sl ofs ty]
    | _ => none
  let regs ← pairs.filterMapM fun (r, l) => match l with
    | .One (.R m) => .OK (some (reload env r m))
    | .One (.S ..) => .OK none
    | .Twolong .. => .Error "Regalloc: split arguments are not supported"
  .OK (stk.flatten ++ regs)

/-- Function pointer of a call: reloaded last, into `X9` (not an argument
    register, not callee-save). -/
def rosMove (ros : Sum Reg Ident) : Bblock × Sum Mreg Ident :=
  match ros with
  | .inl r => ([reload env r .R9], .inl .R9)
  | .inr id => ([], .inr id)

variable (abi : AbiKind) (f : RTL.Function)

/-- The LTL block for one RTL instruction. -/
def allocInstr : RTL.Instruction → Res Bblock
  | .Inop s => .OK [.Lbranch s]
  | .Iop op args res s =>
      match op, args with
      | .Omove, [a] =>
          let t := tempFor (env a)
          .OK [reload env a t, spill env t res, .Lbranch s]
      | _, _ => do
          let (ms, code) ← reloadTemps env args
          let rt := if twoAddressOp op then ms.headD (tempFor (env res)) else tempFor (env res)
          .OK (code ++ [.Lop op ms rt, spill env rt res, .Lbranch s])
  | .Iload chunk addr args dst s => do
      let (ms, code) ← reloadTemps env args
      let rt := tempFor (env dst)
      .OK (code ++ [.Lload chunk addr ms rt, spill env rt dst, .Lbranch s])
  | .Istore chunk addr args src s => do
      let (ms, code) ← reloadTemps env (args ++ [src])
      match ms.getLast? with
      | none => .Error "Regalloc: store"
      | some ms' => .OK (code ++ [.Lstore chunk addr ms.dropLast ms', .Lbranch s])
  | .Icall sg ros args res s => do
      let mv ← callArgMoves env args (locArguments abi sg)
      let (rmv, ros') := rosMove env ros
      match locResult sg with
      | .One m => .OK (mv ++ rmv ++ [.Lcall sg ros', spill env m res, .Lbranch s])
      | .Twolong .. => .Error "Regalloc: split results are not supported"
  | .Itailcall sg ros args => do
      let mv ← callArgMoves env args (locArguments abi sg)
      let (rmv, ros') := rosMove env ros
      .OK (mv ++ rmv ++ [.Ltailcall sg ros'])
  | .Ibuiltin ef args res s => do
      let (args', code) ← match ef with
        | .EF_annot .. | .EF_debug .. => .OK (args.map (slotBuiltinArg env), [])
        | _ => match reloadBuiltinArgs env args (intTemps, floatTemps) with
          | some x => .OK x
          | none => .Error "Regalloc: too many builtin arguments"
      match res with
      | .BR r =>
          let t := tempFor (env r)
          .OK (code ++ [.Lbuiltin ef args' (.BR t), spill env t r, .Lbranch s])
      | .BR_none => .OK (code ++ [.Lbuiltin ef args' .BR_none, .Lbranch s])
      | .BR_splitlong .. => .Error "Regalloc: split builtin results are not supported"
  | .Icond cond args s1 s2 => do
      let (ms, code) ← reloadTemps env args
      .OK (code ++ [.Lcond cond ms s1 s2])
  | .Ijumptable arg tbl => .OK [reload env arg .R9, .Ljumptable .R9 tbl]
  | .Ireturn none => .OK [.Lreturn]
  | .Ireturn (some a) =>
      match locResult f.fn_sig with
      | .One m => .OK [reload env a m, .Lreturn]
      | .Twolong .. => .Error "Regalloc: split results are not supported"

/-- The entry block: copy every parameter from its `loc_parameters` location
    into its slot (register parameters first), then branch to the RTL entry
    point. -/
def entryBlock : Res Bblock := do
  let params := f.fn_params
  let locs := locParameters abi f.fn_sig
  if params.length ≠ locs.length then .Error "Regalloc: bad parameters" else
  let pairs := params.zip locs
  let regs ← pairs.filterMapM fun (r, l) => match l with
    | .One (.R m) => .OK (some (spill env m r))
    | .One (.S ..) => .OK none
    | .Twolong .. => .Error "Regalloc: split parameters are not supported"
  let stk := pairs.filterMap fun (r, l) => match l with
    | .One (.S sl ofs ty) =>
        let t := tempFor (env r)
        some [.Lgetstack sl ofs ty t, spill env t r]
    | _ => none
  .OK (regs ++ stk.flatten ++ [.Lbranch f.fn_entrypoint])

end ALLOC

/-- The simple allocator: every pseudo-register in its own stack slot.
    Used as a fallback when the coloring allocator below fails. -/
def regallocSpillAll (abi : AbiKind) (f : RTL.Function) : Res LTL.Function := do
  let env ← RTLtyping.typeFunction abi f
  let code ← (PTree.elements f.fn_code).foldlM
    (fun (c : LTL.Code) (pc, i) => do
      let b ← allocInstr env abi f i
      .OK (c.set pc b))
    PTree.empty
  let entry := (RTL.maxPcFunction f).succ
  let eb ← entryBlock env abi f
  .OK { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize,
        fn_code := code.set entry eb, fn_entrypoint := entry }

/-! # Register allocation by coloring of an interference graph

Port of the algorithm of `backend/Regalloc.ml`:

* split live ranges (`Splitting.lean`);
* convert from RTL to XTL;
* eliminate dead code;
* repeat: construct the interference graph, color it with the IRC
  algorithm (`IRC.lean`), find the variables that were spilled but must be
  in registers; if there are none, convert to LTL and exit, otherwise insert
  spill and reload instructions and try again.

The fresh temporaries of the OCaml global generator are created in the
monad `XTL.TempM`.  OCaml `assert false` failures and the exceptions
`Bad_LTL`/`Timeout` become `Except String` errors.  The trace output
(`-dalloctrace`) is not ported. -/

open XTL IRC

/-- `Regalloc.is_two_address` -/
def isTwoAddress {A : Type} (op : Operation) (args : List A) : Option (A × List A) :=
  if twoAddressOp op then
    match args with
    | [] => none
    | arg1 :: argl => some (arg1, argl)
  else none

/-! ## Initial conversion from RTL to XTL -/

section CONVERT
variable (tyenv : Reg → ATyp)

/-- `Regalloc.vreg` -/
def vreg (r : Reg) : Var := .V r (tyenv r)
/-- `Regalloc.vregs` -/
def vregs (rl : List Reg) : List Var := rl.map (vreg tyenv)

/-- `Regalloc.constrain_reg` -/
def constrainReg (v : Var) : Option Mreg → Var
  | none => v
  | some mr => .L (.R mr)

/-- `Regalloc.constrain_regs` -/
def constrainRegs : List Var → List (Option Mreg) → List Var
  | [], _ => []
  | vl, [] => vl
  | _ :: vl', some mr1 :: cl' => .L (.R mr1) :: constrainRegs vl' cl'
  | v1 :: vl', none :: cl' => v1 :: constrainRegs vl' cl'

/-- `Regalloc.move` -/
def move (v1 v2 : Var) (k : XTL.Block) : TempM XTL.Block := do
  if v1 == v2 then return k
  else if XTL.isStackReg v1 then
    let t ← newTemp (XTL.typeof v2)
    return .Xmove v1 t :: .Xmove t v2 :: k
  else if XTL.isStackReg v2 then
    let t ← newTemp (XTL.typeof v1)
    return .Xmove v1 t :: .Xmove t v2 :: k
  else return .Xmove v1 v2 :: k

/-- `Regalloc.movelist` (lists of different lengths: OCaml asserts). -/
def movelist : List Var → List Var → XTL.Block → TempM XTL.Block
  | v1 :: vl1, v2 :: vl2, k => do move v1 v2 (← movelist vl1 vl2 k)
  | _, _, k => return k

/-- The end of `parmove_regs2locs` / `parmove_locs2regs`. -/
def finishParmove (srcs dsts : List Var) (k : XTL.Block) : TempM XTL.Block :=
  match srcs, dsts with
  | [], [] => return k
  | [src], [dst] => move src dst k
  | _, _ => do
    let it ← newTemp .Tint
    let ft ← newTemp .Tfloat
    return .Xparmove srcs dsts it ft :: k

/-- `Regalloc.parmove_regs2locs` -/
def parmoveRegs2Locs (k : XTL.Block) :
    List Var → List Var → List Reg → List (RPair Loc) → TempM XTL.Block
  | srcs', dsts', [], [] => finishParmove srcs' dsts' k
  | srcs', dsts', r :: rl, .One l :: ll =>
    parmoveRegs2Locs k (.V r (tyenv r) :: srcs') (.L l :: dsts') rl ll
  | srcs', dsts', r :: rl, .Twolong l1 l2 :: ll =>
    if Archi.splitlong then do
      let tr ← twinReg r
      parmoveRegs2Locs k (.V r .Tint :: .V tr .Tint :: srcs') (.L l1 :: .L l2 :: dsts') rl ll
    else do
      let rest ← parmoveRegs2Locs k srcs' dsts' rl ll
      return .Xop .Ohighlong [.V r .Tlong] (.L l1) :: .Xop .Olowlong [.V r .Tlong] (.L l2) :: rest
  | srcs', dsts', _, _ => finishParmove srcs' dsts' k

/-- `Regalloc.parmove_locs2regs` -/
def parmoveLocs2Regs (k : XTL.Block) :
    List Var → List Var → List (RPair Loc) → List Reg → TempM XTL.Block
  | srcs', dsts', [], [] => finishParmove srcs' dsts' k
  | srcs', dsts', .One l :: ll, r :: rl =>
    parmoveLocs2Regs k (.L l :: srcs') (.V r (tyenv r) :: dsts') ll rl
  | srcs', dsts', .Twolong l1 l2 :: ll, r :: rl =>
    if Archi.splitlong then do
      let tr ← twinReg r
      parmoveLocs2Regs k (.L l1 :: .L l2 :: srcs') (.V r .Tint :: .V tr .Tint :: dsts') ll rl
    else do
      let rest ← parmoveLocs2Regs k srcs' dsts' ll rl
      return .Xop .Omakelong [.L l1, .L l2] (.V r .Tlong) :: rest
  | srcs', dsts', _, _ => finishParmove srcs' dsts' k

/-- `Regalloc.convert_builtin_arg` -/
def convertBuiltinArg : BuiltinArg Reg → TempM (BuiltinArg Var)
  | .BA r => do
    let ty := tyenv r
    if Archi.splitlong && ty == .Tlong then
      return .BA_splitlong (.BA (.V r .Tint)) (.BA (.V (← twinReg r) .Tint))
    else return .BA (.V r ty)
  | .BA_int n => return .BA_int n
  | .BA_long n => return .BA_long n
  | .BA_float n => return .BA_float n
  | .BA_single n => return .BA_single n
  | .BA_loadstack chunk ofs => return .BA_loadstack chunk ofs
  | .BA_addrstack ofs => return .BA_addrstack ofs
  | .BA_loadglobal chunk id ofs => return .BA_loadglobal chunk id ofs
  | .BA_addrglobal id ofs => return .BA_addrglobal id ofs
  | .BA_splitlong hi lo => do
    let hi' ← convertBuiltinArg hi
    let lo' ← convertBuiltinArg lo
    return .BA_splitlong hi' lo'
  | .BA_addptr a1 a2 => do
    let a1' ← convertBuiltinArg a1
    let a2' ← convertBuiltinArg a2
    return .BA_addptr a1' a2'

/-- `Regalloc.convert_builtin_res` -/
def convertBuiltinRes : BuiltinRes Reg → TempM (BuiltinRes Var)
  | .BR r => do
    let ty := tyenv r
    if Archi.splitlong && ty == .Tlong then
      return .BR_splitlong (.BR (.V r .Tint)) (.BR (.V (← twinReg r) .Tint))
    else return .BR (.V r ty)
  | .BR_none => return .BR_none
  | .BR_splitlong _ _ => return .BR_none  -- OCaml: `assert false`

end CONVERT

/-- `Regalloc.constrain_builtin_arg` -/
def constrainBuiltinArg :
    BuiltinArg Var → List (Option Mreg) → BuiltinArg Var × List (Option Mreg)
  | a@(.BA _), none :: cl' => (a, cl')
  | .BA _, some mr :: cl' => (.BA (.L (.R mr)), cl')
  | .BA_splitlong hi lo, cl =>
    let (hi', cl1) := constrainBuiltinArg hi cl
    let (lo', cl2) := constrainBuiltinArg lo cl1
    (.BA_splitlong hi' lo', cl2)
  | .BA_addptr a1 a2, cl =>
    let (a1', cl1) := constrainBuiltinArg a1 cl
    let (a2', cl2) := constrainBuiltinArg a2 cl1
    (.BA_addptr a1' a2', cl2)
  | a, cl => (a, cl)

/-- `Regalloc.constrain_builtin_args` -/
def constrainBuiltinArgs :
    List (BuiltinArg Var) → List (Option Mreg) → List (BuiltinArg Var) × List (Option Mreg)
  | [], cl => ([], cl)
  | a :: al, cl =>
    let (a', cl1) := constrainBuiltinArg a cl
    let (al', cl2) := constrainBuiltinArgs al cl1
    (a' :: al', cl2)

/-- `Regalloc.constrain_builtin_res` -/
def constrainBuiltinRes :
    BuiltinRes Var → List (Option Mreg) → BuiltinRes Var × List (Option Mreg)
  | a@(.BR _), none :: cl' => (a, cl')
  | .BR _, some mr :: cl' => (.BR (.L (.R mr)), cl')
  | .BR_splitlong hi lo, cl =>
    let (hi', cl1) := constrainBuiltinRes hi cl
    let (lo', cl2) := constrainBuiltinRes lo cl1
    (.BR_splitlong hi' lo', cl2)
  | a, cl => (a, cl)

/-- `Regalloc.block_of_RTL_instr`: the XTL basic block of an RTL
    instruction, with moves and parallel moves honoring the calling
    conventions and the register constraints of some operations. -/
def blockOfRTLInstr (abi : AbiKind) (funsig : Signature) (tyenv : Reg → ATyp) :
    RTL.Instruction → TempM XTL.Block
  | .Inop s => return [.Xbranch s]
  | .Iop op args res s => do
    match op, args with
    | .Omove, [arg] =>
      if Archi.splitlong && tyenv arg == .Tlong then
        return [.Xmove (.V arg .Tint) (.V res .Tint),
                .Xmove (.V (← twinReg arg) .Tint) (.V (← twinReg res) .Tint), .Xbranch s]
      else return [.Xmove (vreg tyenv arg) (vreg tyenv res), .Xbranch s]
    | .Omakelong, [arg1, arg2] =>
      if Archi.splitlong then
        return [.Xmove (.V arg1 .Tint) (.V res .Tint),
                .Xmove (.V arg2 .Tint) (.V (← twinReg res) .Tint), .Xbranch s]
      else generic op args res s
    | .Olowlong, [arg] =>
      if Archi.splitlong then return [.Xmove (.V (← twinReg arg) .Tint) (.V res .Tint), .Xbranch s]
      else generic op args res s
    | .Ohighlong, [arg] =>
      if Archi.splitlong then return [.Xmove (.V arg .Tint) (.V res .Tint), .Xbranch s]
      else generic op args res s
    | _, _ => generic op args res s
  | .Iload chunk addr args dst s => do
    if Archi.splitlong && chunk == .Mint64 then
      match offsetAddressing addr 4 with
      | none => return [.Xbranch s]  -- OCaml: `assert false`
      | some addr' =>
        let td ← twinReg dst
        return [.Xload .Mint32 addr (vregs tyenv args) (.V (if Archi.big_endian then dst else td) .Tint),
                .Xload .Mint32 addr' (vregs tyenv args) (.V (if Archi.big_endian then td else dst) .Tint),
                .Xbranch s]
    else return [.Xload chunk addr (vregs tyenv args) (vreg tyenv dst), .Xbranch s]
  | .Istore chunk addr args src s => do
    if Archi.splitlong && chunk == .Mint64 then
      match offsetAddressing addr 4 with
      | none => return [.Xbranch s]  -- OCaml: `assert false`
      | some addr' =>
        let ts ← twinReg src
        return [.Xstore .Mint32 addr (vregs tyenv args) (.V (if Archi.big_endian then src else ts) .Tint),
                .Xstore .Mint32 addr' (vregs tyenv args) (.V (if Archi.big_endian then ts else src) .Tint),
                .Xbranch s]
    else return [.Xstore chunk addr (vregs tyenv args) (vreg tyenv src), .Xbranch s]
  | .Icall sg ros args res s => do
    let args' := locArguments abi sg
    let res' := [RPair.map Loc.R (locResult sg)]
    let after ← parmoveLocs2Regs tyenv [.Xbranch s] [] [] res' [res]
    let ros' := match ros with | .inl r => .inl (vreg tyenv r) | .inr id => .inr id
    parmoveRegs2Locs tyenv (.Xcall sg ros' (vlocpairs args') (vlocpairs res') :: after) [] [] args args'
  | .Itailcall sg ros args => do
    let args' := locArguments abi sg
    let ros' := match ros with | .inl r => .inl (vreg tyenv r) | .inr id => .inr id
    parmoveRegs2Locs tyenv [.Xtailcall sg ros' (vlocpairs args')] [] [] args args'
  | .Ibuiltin ef args res s => do
    let (cargs, cres) := mregsForBuiltin ef
    let args1 ← args.mapM (convertBuiltinArg tyenv)
    let res1 ← convertBuiltinRes tyenv res
    let (args2, _) := constrainBuiltinArgs args1 cargs
    let (res2, _) := constrainBuiltinRes res1 cres
    let after ← movelist (BuiltinRes.params res2) (BuiltinRes.params res1) [.Xbranch s]
    movelist (BuiltinArg.paramsList args1) (BuiltinArg.paramsList args2)
      (.Xbuiltin ef args2 res2 :: after)
  | .Icond cond args s1 s2 => return [.Xcond cond (vregs tyenv args) s1 s2]
  | .Ijumptable arg tbl => return [.Xjumptable (vreg tyenv arg) tbl]
  | .Ireturn none => return [.Xreturn []]
  | .Ireturn (some arg) => do
    let args' := [RPair.map Loc.R (locResult funsig)]
    parmoveRegs2Locs tyenv [.Xreturn (vlocpairs args')] [] [] [arg] args'
where
  /-- The general case of `Iop`. -/
  generic (op : Operation) (args : List Reg) (res : Reg) (s : RTL.Node) : TempM XTL.Block := do
    let (cargs, cres) := mregsForOperation op
    let args1 := vregs tyenv args
    let res1 := vreg tyenv res
    let args2 := constrainRegs args1 cargs
    let res2 := constrainReg res1 cres
    let (args3, res3) ← match isTwoAddress op args2 with
      | none => pure (args2, res2)
      | some (arg, args2') =>
        if arg == res2 || !(args2'.contains res2) then pure (args2, res2)
        else do
          let t ← newTemp (tyenv res)
          pure (t :: args2', t)
    let after ← move res3 res1 [.Xbranch s]
    movelist args1 args3 (.Xop op args3 res3 :: after)

/-- `Regalloc.function_of_RTL_function` -/
def functionOfRTLFunction (abi : AbiKind) (f : RTL.Function) (tyenv : Reg → ATyp) :
    TempM XFunction := do
  let xc ← (PTree.elements f.fn_code).foldlM
    (fun (c : XTL.Code) (pc, i) => do return c.set pc (← blockOfRTLInstr abi f.fn_sig tyenv i))
    PTree.empty
  let pcEntrypoint := (RTL.maxPcFunction f).succ
  let bEntrypoint ← parmoveLocs2Regs tyenv [.Xbranch f.fn_entrypoint] [] []
    (locParameters abi f.fn_sig) f.fn_params
  return { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize,
           fn_entrypoint := pcEntrypoint, fn_code := xc.set pcEntrypoint bEntrypoint }

end Regalloc
end CC
