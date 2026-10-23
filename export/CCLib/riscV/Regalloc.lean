/-
  Register allocation — port of the untrusted OCaml files
  `backend/Regalloc.ml` and `backend/IRC.ml`, for the RISC-V back end
  (RV64; the copy of `CCLib/backend/Regalloc.lean` for `CCLib/riscV/`).

  In Rocq, `Allocation.regalloc` is a `Parameter` that extraction binds to
  `Regalloc.regalloc` (see `extraction/extraction.v`).  Its output is checked
  by the translation validator `Allocation.check_function`, so the allocator
  is not part of the trusted base: an incorrect allocation is rejected, never
  miscompiled.  The Lean port takes it as the field `regalloc` of
  `Compiler.Config`; `Regalloc.regalloc` below is the default used by
  `CCLib/extraction/Extraction.lean`.

  The file has two allocators.  `regallocIRC` ports `Regalloc.ml`
  (live-range splitting with `Splitting.lean`, conversion to XTL
  (`XTL.lean`), dead-code elimination, iterated register coalescing
  (`IRC.lean`), spill-cost heuristics, at most 40 rounds of spill/reload
  insertion, translation to LTL); it is the same code as
  `CCLib/backend/Regalloc.lean`, instantiated with the riscV conventions.
  `regallocSpillAll` is the simplest allocator that the validator accepts:
  every pseudo-register lives in its own `Local` stack slot, and each RTL
  instruction becomes an LTL block that loads its arguments into scratch
  machine registers, performs the operation, and stores the result back.
  `regalloc` runs `regallocIRC` and falls back to `regallocSpillAll` if it
  fails or if the validator rejects its result.

  Scratch registers of `regallocSpillAll`: integer `x5`, `x7`, `x28`, `x29`, then the argument
  registers `x10`–`x17`; floating-point `f0`–`f5`, `f7`, `f28`–`f31`.  They
  avoid `x30` (`destroyed_at_function_entry`, `temp_for_parent_frame`),
  `x6` and `f6` (destroyed by jump tables and float-to-integer
  conversions), and callee-save registers.  Builtins whose arguments or
  result must be in fixed registers (`mregs_for_builtin`: `__builtin_clz`,
  `__builtin_ctz`, …) get those registers.
-/
import CCLib.riscV.Allocation
import CCLib.riscV.IRC
import CCLib.riscV.Splitting

namespace CC
namespace RiscV
namespace Regalloc

open Op Conventions1 Conventions LTL

/-- Integer scratch registers. -/
def intTemps : List Mreg := [.R5, .R7, .R28, .R29, .R10, .R11, .R12, .R13, .R14, .R15, .R16, .R17]

/-- Floating-point scratch registers. -/
def floatTemps : List Mreg :=
  [.F0, .F1, .F2, .F3, .F4, .F5, .F7, .F28, .F29, .F30, .F31]

/-- Values of these types live in floating-point registers. -/
def isFloatTyp : ATyp → Bool
  | .Tfloat | .Tsingle => true
  | _ => false

/-- The first scratch register of the class of `ty`. -/
def tempFor (ty : ATyp) : Mreg := if isFloatTyp ty then .F0 else .R5

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

/-- Builtin arguments that `mregs_for_builtin` places in fixed registers:
    each `BA r` goes to the register given at its position (or to a scratch
    register of its class if none is given). -/
def fixedBuiltinArgs : List (BuiltinArg Reg) → List (Option Mreg) →
    Res (List (BuiltinArg Loc) × Bblock)
  | [], _ => .OK ([], [])
  | .BA r :: al, c :: cs => do
      let m := c.getD (tempFor (env r))
      let (al', code) ← fixedBuiltinArgs al cs
      .OK (.BA (.R m) :: al', reload env r m :: code)
  | _, _ => .Error "Regalloc: unsupported builtin arguments"

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

/-- Function pointer of a call: reloaded last, into `x5` (not an argument
    register, not callee-save). -/
def rosMove (ros : Sum Reg Ident) : Bblock × Sum Mreg Ident :=
  match ros with
  | .inl r => ([reload env r .R5], .inl .R5)
  | .inr id => ([], .inr id)

variable (f : RTL.Function)

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
      let mv ← callArgMoves env args (locArguments sg)
      let (rmv, ros') := rosMove env ros
      match locResult sg with
      | .One m => .OK (mv ++ rmv ++ [.Lcall sg ros', spill env m res, .Lbranch s])
      | .Twolong .. => .Error "Regalloc: split results are not supported"
  | .Itailcall sg ros args => do
      let mv ← callArgMoves env args (locArguments sg)
      let (rmv, ros') := rosMove env ros
      .OK (mv ++ rmv ++ [.Ltailcall sg ros'])
  | .Ibuiltin ef args res s => do
      let (args', code) ← match ef with
        | .EF_annot .. | .EF_debug .. => .OK (args.map (slotBuiltinArg env), [])
        | _ =>
          let (argc, _) := mregsForBuiltin ef
          if argc.isEmpty then
            match reloadBuiltinArgs env args (intTemps, floatTemps) with
            | some x => .OK x
            | none => .Error "Regalloc: too many builtin arguments"
          else fixedBuiltinArgs env args argc
      let (_, resc) := mregsForBuiltin ef
      match res with
      | .BR r =>
          let t := (resc.head?.bind id).getD (tempFor (env r))
          .OK (code ++ [.Lbuiltin ef args' (.BR t), spill env t r, .Lbranch s])
      | .BR_none => .OK (code ++ [.Lbuiltin ef args' .BR_none, .Lbranch s])
      | .BR_splitlong .. => .Error "Regalloc: split builtin results are not supported"
  | .Icond cond args s1 s2 => do
      let (ms, code) ← reloadTemps env args
      .OK (code ++ [.Lcond cond ms s1 s2])
  | .Ijumptable arg tbl => .OK [reload env arg .R5, .Ljumptable .R5 tbl]
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
  let locs := locParameters f.fn_sig
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
def regallocSpillAll (f : RTL.Function) : Res LTL.Function := do
  let env ← RTLtyping.typeFunction f
  let code ← (PTree.elements f.fn_code).foldlM
    (fun (c : LTL.Code) (pc, i) => do
      let b ← allocInstr env f i
      .OK (c.set pc b))
    PTree.empty
  let entry := (RTL.maxPcFunction f).succ
  let eb ← entryBlock env f
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
def blockOfRTLInstr (funsig : Signature) (tyenv : Reg → ATyp) :
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
    let args' := locArguments sg
    let res' := [RPair.map Loc.R (locResult sg)]
    let after ← parmoveLocs2Regs tyenv [.Xbranch s] [] [] res' [res]
    let ros' := match ros with | .inl r => .inl (vreg tyenv r) | .inr id => .inr id
    parmoveRegs2Locs tyenv (.Xcall sg ros' (vlocpairs args') (vlocpairs res') :: after) [] [] args args'
  | .Itailcall sg ros args => do
    let args' := locArguments sg
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
def functionOfRTLFunction (f : RTL.Function) (tyenv : Reg → ATyp) :
    TempM XFunction := do
  let xc ← (PTree.elements f.fn_code).foldlM
    (fun (c : XTL.Code) (pc, i) => do return c.set pc (← blockOfRTLInstr f.fn_sig tyenv i))
    PTree.empty
  let pcEntrypoint := (RTL.maxPcFunction f).succ
  let bEntrypoint ← parmoveLocs2Regs tyenv [.Xbranch f.fn_entrypoint] [] []
    (locParameters f.fn_sig) f.fn_params
  return { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize,
           fn_entrypoint := pcEntrypoint, fn_code := xc.set pcEntrypoint bEntrypoint }

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
def regallocIRC (f : RTL.Function) : Res LTL.Function :=
  let go : TempM (Res LTL.Function) := do
    resetTemps
    let f1 ← Splitting.renameFunction f
    match RTLtyping.typeFunction f1 with
    | .Error msg => return .Error ("RTL code after splitting is ill-typed: " ++ msg)
    | .OK tyenv =>
      let f2 ← functionOfRTLFunction f1 tyenv
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
def regalloc (f : RTL.Function) : Res LTL.Function :=
  match regallocIRC f with
  | .OK tf =>
    match RTLtyping.typeFunction f with
    | .OK env =>
      match Allocation.checkFunction f tf env with
      | .OK _ => .OK tf
      | .Error _ => regallocSpillAll f
    | .Error m => .Error m
  | .Error _ => regallocSpillAll f

end Regalloc
end RiscV
end CC
