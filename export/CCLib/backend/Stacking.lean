/-
  The translation from Linear to Mach — port of `backend/Stacking.v` (whole
  file).  The layout of activation records (`aarch64/Stacklayout.v`) is in
  `CCLib/aarch64/Stacklayout.lean`.

  Ported from `Stacking.v`: `offset_local`, `offset_arg`,
  `save_callee_save(_rec)`, `restore_callee_save(_rec)`, `simplify_store`,
  `simplify_load`, `transl_op`, `transl_addr`, `transl_builtin_arg`,
  `transl_instr`, `transl_code`, `transl_body`, `transf_function`,
  `transf_fundef`, `transf_program`.

  Differences from Rocq: `Archi.abi` (used by `size_arguments` and
  `loc_parameters`) is an explicit argument `abi`; `Stacklayout.fe_ofs_arg`
  is `Stacklayout.feOfsArg` from `Mach.lean`.
-/
import CCLib.aarch64.Stacklayout
import CCLib.backend.Lineartyping

namespace CC

open Bounds


namespace Stacking

open Linear Mach Conventions1 Conventions Stacklayout

/-- `Stacking.offset_local` -/
def offsetLocal (fe : FrameEnv) (x : Z) : Z := fe.fe_ofs_local + 4 * x

/-- `Stacking.offset_arg` -/
def offsetArg (x : Z) : Z := feOfsArg + 4 * x

/-- `Stacking.save_callee_save_rec` -/
def saveCalleeSaveRec : List Mreg → Z → Mach.Code → Mach.Code
  | [], _, k => k
  | r :: rl, ofs, k =>
      let ty := Mreg.type r
      let sz := ty.size
      let ofs1 := align ofs sz
      .Msetstack r (Integers.Ptrofs.repr ofs1) ty :: saveCalleeSaveRec rl (ofs1 + sz) k

/-- `Stacking.save_callee_save` -/
def saveCalleeSave (fe : FrameEnv) (k : Mach.Code) : Mach.Code :=
  saveCalleeSaveRec fe.fe_used_callee_save fe.fe_ofs_callee_save k

/-- `Stacking.restore_callee_save_rec` -/
def restoreCalleeSaveRec : List Mreg → Z → Mach.Code → Mach.Code
  | [], _, k => k
  | r :: rl, ofs, k =>
      let ty := Mreg.type r
      let sz := ty.size
      let ofs1 := align ofs sz
      .Mgetstack (Integers.Ptrofs.repr ofs1) ty r :: restoreCalleeSaveRec rl (ofs1 + sz) k

/-- `Stacking.restore_callee_save` -/
def restoreCalleeSave (fe : FrameEnv) (k : Mach.Code) : Mach.Code :=
  restoreCalleeSaveRec fe.fe_used_callee_save fe.fe_ofs_callee_save k

/-- `Stacking.simplify_store` -/
def simplifyStore (chunk : Chunk) : Chunk :=
  match chunk with
  | .Mbool => .Mint8unsigned
  | .Mint8signed => .Mint8unsigned
  | .Mint16signed => .Mint16unsigned
  | _ => chunk

/-- `Stacking.simplify_load` -/
def simplifyLoad (chunk : Chunk) : Chunk :=
  match chunk with
  | .Mbool => .Mint8unsigned
  | _ => chunk

/-- `Stacking.transl_op` -/
def translOp (fe : FrameEnv) (op : Op.Operation) : Op.Operation :=
  Op.shiftStackOperation fe.fe_stack_data op

/-- `Stacking.transl_addr` -/
def translAddr (fe : FrameEnv) (addr : Op.Addressing) : Op.Addressing :=
  Op.shiftStackAddressing fe.fe_stack_data addr

/-- `Stacking.transl_builtin_arg` -/
def translBuiltinArg (fe : FrameEnv) : BuiltinArg Loc → BuiltinArg Mreg
  | .BA (.R r) => .BA r
  | .BA (.S .Local ofs ty) =>
      .BA_loadstack (Chunk.ofTyp ty) (Integers.Ptrofs.repr (offsetLocal fe ofs))
  | .BA (.S _ _ _) => .BA_int Integers.Int.zero
  | .BA_int n => .BA_int n
  | .BA_long n => .BA_long n
  | .BA_float n => .BA_float n
  | .BA_single n => .BA_single n
  | .BA_loadstack chunk ofs =>
      .BA_loadstack chunk (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr fe.fe_stack_data))
  | .BA_addrstack ofs =>
      .BA_addrstack (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr fe.fe_stack_data))
  | .BA_loadglobal chunk id ofs => .BA_loadglobal chunk id ofs
  | .BA_addrglobal id ofs => .BA_addrglobal id ofs
  | .BA_splitlong hi lo => .BA_splitlong (translBuiltinArg fe hi) (translBuiltinArg fe lo)
  | .BA_addptr a1 a2 => .BA_addptr (translBuiltinArg fe a1) (translBuiltinArg fe a2)

/-- `Stacking.transl_instr` -/
def translInstr (fe : FrameEnv) (i : Linear.Instruction) (k : Mach.Code) : Mach.Code :=
  match i with
  | .Lgetstack sl ofs ty r =>
      match sl with
      | .Local => .Mgetstack (Integers.Ptrofs.repr (offsetLocal fe ofs)) ty r :: k
      | .Incoming => .Mgetparam (Integers.Ptrofs.repr (offsetArg ofs)) ty r :: k
      | .Outgoing => .Mgetstack (Integers.Ptrofs.repr (offsetArg ofs)) ty r :: k
  | .Lsetstack r sl ofs ty =>
      match sl with
      | .Local => .Msetstack r (Integers.Ptrofs.repr (offsetLocal fe ofs)) ty :: k
      | .Incoming => k
      | .Outgoing => .Msetstack r (Integers.Ptrofs.repr (offsetArg ofs)) ty :: k
  | .Lop op args res => .Mop (translOp fe op) args res :: k
  | .Lload chunk addr args dst => .Mload (simplifyLoad chunk) (translAddr fe addr) args dst :: k
  | .Lstore chunk addr args src => .Mstore (simplifyStore chunk) (translAddr fe addr) args src :: k
  | .Lcall sig ros => .Mcall sig ros :: k
  | .Ltailcall sig ros => restoreCalleeSave fe (.Mtailcall sig ros :: k)
  | .Lbuiltin ef args dst => .Mbuiltin ef (args.map (translBuiltinArg fe)) dst :: k
  | .Llabel lbl => .Mlabel lbl :: k
  | .Lgoto lbl => .Mgoto lbl :: k
  | .Lcond cond args lbl => .Mcond cond args lbl :: k
  | .Ljumptable arg tbl => .Mjumptable arg tbl :: k
  | .Lreturn => restoreCalleeSave fe (.Mreturn :: k)

/-- `Stacking.transl_code` -/
def translCode (fe : FrameEnv) (il : List Linear.Instruction) : Mach.Code :=
  il.foldr (translInstr fe) []

/-- `Stacking.transl_body` -/
def translBody (f : Linear.Function) (fe : FrameEnv) : Mach.Code :=
  saveCalleeSave fe (translCode fe f.fn_code)

/-- `Stacking.transf_function` -/
def transfFunction (abi : AbiKind) (f : Linear.Function) : Res Mach.Function :=
  let fe := makeEnv (functionBounds abi f)
  if !Lineartyping.wtFunction abi f then
    .Error "Ill-formed Linear code"
  else if Integers.Ptrofs.max_unsigned < fe.fe_size then
    .Error "Too many spilled variables, stack size exceeded"
  else
    .OK { fn_sig := f.fn_sig, fn_code := translBody f fe, fn_stacksize := fe.fe_size,
          fn_link_ofs := Integers.Ptrofs.repr fe.fe_ofs_link,
          fn_retaddr_ofs := Integers.Ptrofs.repr fe.fe_ofs_retaddr }

/-- `Stacking.transf_fundef` -/
def transfFundef (abi : AbiKind) (f : Linear.Fundef) : Res Mach.Fundef :=
  ASTFundef.transfPartial (transfFunction abi) f

/-- `Stacking.transf_program` -/
def transfProgram (abi : AbiKind) (p : Linear.Program) : Res Mach.Program :=
  transformPartialProgram (transfFundef abi) p

end Stacking
end CC
