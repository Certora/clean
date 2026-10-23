/-
  [RISC-V instance of `CCLib/backend/Renumber.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Postorder renumbering of RTL control-flow graphs — port of
  `backend/Renumber.v` (`renum_pc`, `renum_instr`, `renum_node`,
  `renum_cfg`, `transf_function`, `transf_fundef`, `transf_program`).
-/
import CCLib.riscV.RTL
import CCLib.lib.Postorder
import CCLib.riscV.Tailcall

namespace CC
namespace RiscV
namespace Renumber

open RTL

section RENUMBER
variable (pnum : PTree Positive)

/-- `Renumber.renum_pc` -/
def renumPc (pc : RTL.Node) : RTL.Node :=
  match pnum.get pc with
  | some pc' => pc'
  | none => .xH

/-- `Renumber.renum_instr` -/
def renumInstr (i : RTL.Instruction) : RTL.Instruction :=
  match i with
  | .Inop s => .Inop (renumPc pnum s)
  | .Iop op args res s => .Iop op args res (renumPc pnum s)
  | .Iload chunk addr args res s => .Iload chunk addr args res (renumPc pnum s)
  | .Istore chunk addr args src s => .Istore chunk addr args src (renumPc pnum s)
  | .Icall sg ros args res s => .Icall sg ros args res (renumPc pnum s)
  | .Itailcall .. => i
  | .Ibuiltin ef args res s => .Ibuiltin ef args res (renumPc pnum s)
  | .Icond cond args s1 s2 => .Icond cond args (renumPc pnum s1) (renumPc pnum s2)
  | .Ijumptable arg tbl => .Ijumptable arg (tbl.map (renumPc pnum))
  | .Ireturn _ => i

/-- `Renumber.renum_node` -/
def renumNode (c' : RTL.Code) (pc : RTL.Node) (i : RTL.Instruction) : RTL.Code :=
  match pnum.get pc with
  | none => c'
  | some pc' => c'.set pc' (renumInstr pnum i)

/-- `Renumber.renum_cfg` -/
def renumCfg (c : RTL.Code) : RTL.Code := PTree.fold (renumNode pnum) c PTree.empty

end RENUMBER

/-- `Renumber.transf_function` -/
def transfFunction (f : RTL.Function) : RTL.Function :=
  let pnum := Postorder.postorder (successorsMap f) f.fn_entrypoint
  { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_stacksize := f.fn_stacksize,
    fn_code := renumCfg pnum f.fn_code, fn_entrypoint := renumPc pnum f.fn_entrypoint }

/-- `Renumber.transf_fundef` -/
def transfFundef (fd : RTL.Fundef) : RTL.Fundef := ASTFundef.transf transfFunction fd

/-- `Renumber.transf_program` -/
def transfProgram (p : RTL.Program) : RTL.Program := transformProgram transfFundef p

end Renumber
end RiscV
end CC
