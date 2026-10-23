/-
  [RISC-V instance of `CCLib/backend/Deadcode.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Elimination of unneeded computations over RTL — port of
  `backend/Deadcode.v` (definitions).

  Ported: `add_need_all`, `add_need`, `add_needs_all`, `add_needs`,
  `add_ros_need_all`, `add_opt_need_all`, `kill`, `is_dead`,
  `is_int_zero`, `transfer_builtin_arg`, `transfer_builtin_args`,
  `kill_builtin_res`, `builtin_res_dead`, `transfer_builtin`, `transfer`,
  `analyze` (the backward solver `Backward_Dataflow_Solver(NA)(NodeSetBackward)`
  is `Kildall.Backward.fixpoint`), `transf_instr`, `transf_function`,
  `transf_fundef`, `transf_program`.

  Differences from Rocq: the value-analysis options (`Compopts.va_strict`
  …) and `Archi.abi` are explicit parameters `o` and `abi`, as in
  `CSE.lean`.  The correctness proof `Deadcodeproof.v` is not ported.
-/
import CCLib.riscV.NeedOp
import CCLib.riscV.ValueAnalysis
import CCLib.backend.Kildall
import CCLib.riscV.CSE

namespace CC
namespace RiscV
namespace Deadcode

open ValueDomain ValueAnalysis RTL NeedDomain NeedOp Op

/-- `add_need_all` -/
def addNeedAll (r : Reg) (ne : Nenv) : Nenv := NE.set r .All ne

/-- `add_need` -/
def addNeed (r : Reg) (nv : Nval) (ne : Nenv) : Nenv := NE.set r (nlub nv (NE.get r ne)) ne

/-- `add_needs_all` -/
def addNeedsAll : List Reg → Nenv → Nenv
  | [], ne => ne
  | r1 :: rs, ne => addNeedAll r1 (addNeedsAll rs ne)

/-- `add_needs` -/
def addNeeds : List Reg → List Nval → Nenv → Nenv
  | [], _, ne => ne
  | rl@(_ :: _), [], ne => addNeedsAll rl ne
  | r1 :: rs, nv1 :: nvs, ne => addNeed r1 nv1 (addNeeds rs nvs ne)

/-- `add_ros_need_all` -/
def addRosNeedAll (ros : Sum Reg Ident) (ne : Nenv) : Nenv :=
  match ros with
  | .inl r => addNeedAll r ne
  | .inr _ => ne

/-- `add_opt_need_all` -/
def addOptNeedAll (or : Option Reg) (ne : Nenv) : Nenv :=
  match or with
  | some r => addNeedAll r ne
  | none => ne

/-- `kill` -/
def kill (r : Reg) (ne : Nenv) : Nenv := NE.set r .Nothing ne

/-- `is_dead` -/
def isDead (v : Nval) : Bool :=
  match v with
  | .Nothing => true
  | _ => false

/-- `is_int_zero` -/
def isIntZero (v : Nval) : Bool :=
  match v with
  | .I n => Integers.Int.eq n Integers.Int.zero
  | _ => false

/-- `transfer_builtin_arg` -/
def transferBuiltinArg (nv : Nval) (na : NAT) : BuiltinArg Reg → NAT
  | .BA r => (addNeed r nv na.1, na.2)
  | .BA_int _ | .BA_long _ | .BA_float _ | .BA_single _
  | .BA_addrstack _ | .BA_addrglobal _ _ => na
  | .BA_loadstack chunk ofs => (na.1, nmemAdd na.2 (.Stk ofs) (sizeChunk chunk))
  | .BA_loadglobal chunk id ofs => (na.1, nmemAdd na.2 (.Gl id ofs) (sizeChunk chunk))
  | .BA_splitlong hi lo => transferBuiltinArg .All (transferBuiltinArg .All na hi) lo
  | .BA_addptr hi lo => transferBuiltinArg .All (transferBuiltinArg .All na hi) lo

/-- `transfer_builtin_args` -/
def transferBuiltinArgs (na : NAT) (al : List (BuiltinArg Reg)) : NAT :=
  al.foldl (transferBuiltinArg .All) na

/-- `kill_builtin_res` -/
def killBuiltinRes (res : BuiltinRes Reg) (ne : Nenv) : Nenv :=
  match res with
  | .BR r => kill r ne
  | _ => ne

/-- `builtin_res_dead` -/
def builtinResDead (res : BuiltinRes Reg) (ne : Nenv) : Bool :=
  match res with
  | .BR r => isDead (nreg ne r)
  | _ => false

section
variable (o : ValueAOp.Options)

/-- `transfer_builtin` -/
def transferBuiltin (app : VAState) (ef : ExtFun) (args : List (BuiltinArg Reg))
    (res : BuiltinRes Reg) (ne : Nenv) (nm : Nmem) : NAT :=
  match ef, args with
  | .EF_vload chunk, [a1] =>
      transferBuiltinArg .All
        (killBuiltinRes res ne, nmemAdd nm (aaddrArg o app a1) (sizeChunk chunk)) a1
  | .EF_vstore chunk, [a1, a2] =>
      transferBuiltinArg .All
        (transferBuiltinArg (storeArgument chunk) (killBuiltinRes res ne, nm) a2) a1
  | .EF_memcpy sz _, [dst, src] =>
      if nmemContains nm (aaddrArg o app dst) sz then
        transferBuiltinArgs
          (killBuiltinRes res ne,
           nmemAdd (nmemRemove nm (aaddrArg o app dst) sz) (aaddrArg o app src) sz)
          args
      else (ne, nm)
  | .EF_annot _ _ _, _ | .EF_annot_val _ _ _, _ =>
      transferBuiltinArgs (killBuiltinRes res ne, nm) args
  | .EF_debug _ _ _, _ => (killBuiltinRes res ne, nm)
  | .EF_builtin name sg, _ =>
      match Builtins.lookupBuiltinFunction name sg with
      | some _ =>
          if builtinResDead res ne then (ne, nm)
          else transferBuiltinArgs (killBuiltinRes res ne, nm) args
      | none => transferBuiltinArgs (killBuiltinRes res ne, nmemAll) args
  | _, _ => transferBuiltinArgs (killBuiltinRes res ne, nmemAll) args

/-- `transfer`: the backward transfer function of the neededness analysis. -/
def transfer (f : RTL.Function) (dm : Defmap) (approx : PMap VAState)
    (pc : Node) (after : NAT) : NAT :=
  let ne := after.1
  let nm := after.2
  match f.fn_code.get pc with
  | none => NA.bot
  | some (.Inop _) => after
  | some (.Iop op args res _) =>
      let nres := nreg ne res
      if isDead nres then after
      else if isIntZero nres then (kill res ne, nm)
      else (addNeeds args (needsOfOperation op nres) (kill res ne), nm)
  | some (.Iload chunk addr args dst _) =>
      let ndst := nreg ne dst
      if isDead ndst then after
      else if isIntZero ndst then (kill dst ne, nm)
      else (addNeedsAll args (kill dst ne),
            nmemAdd nm (aaddressing o (approx.get pc) addr args) (sizeChunk chunk))
  | some (.Istore chunk addr args src _) =>
      let p := aaddressing o (approx.get pc) addr args
      if nmemContains nm p (sizeChunk chunk) then
        (addNeedsAll args (addNeed src (storeArgument chunk) ne),
         nmemRemove nm p (sizeChunk chunk))
      else after
  | some (.Icall _ ros args res _) =>
      match isKnownRuntimeFunction dm ros with
      | none => (addNeedsAll args (addRosNeedAll ros (kill res ne)), nmemAll)
      | some _ =>
          let nres := nreg ne res
          if isDead nres then after
          else (addNeedsAll args (addRosNeedAll ros (kill res ne)), nm)
  | some (.Itailcall _ ros args) =>
      (addNeedsAll args (addRosNeedAll ros NE.bot), nmemDeadStack f.fn_stacksize)
  | some (.Ibuiltin ef args res _) => transferBuiltin o (approx.get pc) ef args res ne nm
  | some (.Icond cond args s1 s2) =>
      if s1 = s2 then after else (addNeeds args (needsOfCondition cond) ne, nm)
  | some (.Ijumptable arg _) => (addNeedAll arg ne, nm)
  | some (.Ireturn optarg) => (addOptNeedAll optarg ne, nmemDeadStack f.fn_stacksize)

/-- `analyze`: backward dataflow analysis of neededness. -/
def analyze (f : RTL.Function) (dm : Defmap) (approx : PMap VAState) : Option (PMap NAT) :=
  letI := NA.lat
  Kildall.Backward.fixpoint (L := NAT) (NS := NodeSetBackward)
    f.fn_code successorsInstr (transfer o f dm approx)

/-- `transf_instr` -/
def transfInstr (dm : Defmap) (approx : PMap VAState) (an : PMap NAT)
    (pc : Node) (instr : Instruction) : Instruction :=
  match instr with
  | .Iop op args res s =>
      let nres := nreg (an.get pc).1 res
      if isDead nres then .Inop s
      else if isIntZero nres then .Iop (.Ointconst Integers.Int.zero) [] res s
      else if operationIsRedundant op nres then
        match args with
        | arg :: _ => .Iop .Omove [arg] res s
        | [] => instr
      else instr
  | .Iload _ _ _ dst s =>
      let ndst := nreg (an.get pc).1 dst
      if isDead ndst then .Inop s
      else if isIntZero ndst then .Iop (.Ointconst Integers.Int.zero) [] dst s
      else instr
  | .Istore chunk addr args _ s =>
      let p := aaddressing o (approx.get pc) addr args
      if nmemContains (an.get pc).2 p (sizeChunk chunk) then instr else .Inop s
  | .Icall _ ros _ res s =>
      match isKnownRuntimeFunction dm ros with
      | none => instr
      | some _ => if isDead (nreg (an.get pc).1 res) then .Inop s else instr
  | .Ibuiltin (.EF_memcpy sz _) [dst, _] _ s =>
      if nmemContains (an.get pc).2 (aaddrArg o (approx.get pc) dst) sz then instr else .Inop s
  | .Ibuiltin (.EF_builtin name sg) _ res s =>
      match Builtins.lookupBuiltinFunction name sg, builtinResDead res (an.get pc).1 with
      | some _, true => .Inop s
      | _, _ => instr
  | .Icond _ _ s1 s2 => if s1 = s2 then .Inop s1 else instr
  | _ => instr

end

section
variable (o : ValueAOp.Options)

/-- `transf_function` -/
def transfFunction (dm : Defmap) (rm : Romem) (f : RTL.Function) : Res RTL.Function :=
  let approx := ValueAnalysis.analyze o  rm f
  match analyze o f dm approx with
  | some an =>
      .OK { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_stacksize := f.fn_stacksize,
            fn_code := PTree.map (transfInstr o dm approx an) f.fn_code,
            fn_entrypoint := f.fn_entrypoint }
  | none => .Error "Neededness analysis failed"

/-- `transf_fundef` -/
def transfFundef (dm : Defmap) (rm : Romem) (fd : RTL.Fundef) : Res RTL.Fundef :=
  ASTFundef.transfPartial (transfFunction o  dm rm) fd

/-- `transf_program` -/
def transfProgram (p : RTL.Program) : Res RTL.Program :=
  transformPartialProgram (transfFundef o  p.defmap (romemFor o p)) p

end

end Deadcode
end RiscV
end CC
