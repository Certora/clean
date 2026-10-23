/-
  The abstract syntax of Mach (`backend/Mach.v`), generic in the target's
  operators, addressing modes, conditions and machine registers.

  `CCLib.backend.Mach` is the Mach language of the configured target
  (AArch64), with its semantics.  The ARM and PowerPC instruction selectors
  (`CCLib.arm.Asmgen`, `CCLib.powerpc.Asmgen`) translate Mach code over
  their own operators and registers; they only need the syntax, which is
  given here once for every target rather than copied per target.

  Ported: `instruction`, `code`, `function`, `fundef`, `program`,
  `is_leaf_function`.
-/
import CCLib.backend.Cminor

namespace CC
namespace MachSyntax

/-- `Mach.label` -/
abbrev Label := Positive

/-- `Mach.instruction`, for operators `O`, addressing modes `A`,
conditions `C` and machine registers `R`. -/
inductive Instruction (O A C R : Type) where
  | Mgetstack (ofs : Integers.Ptrofs) (ty : ATyp) (dst : R)
  | Msetstack (src : R) (ofs : Integers.Ptrofs) (ty : ATyp)
  | Mgetparam (ofs : Integers.Ptrofs) (ty : ATyp) (dst : R)
  | Mop (op : O) (args : List R) (res : R)
  | Mload (chunk : Chunk) (addr : A) (args : List R) (dst : R)
  | Mstore (chunk : Chunk) (addr : A) (args : List R) (src : R)
  | Mcall (sg : Signature) (ros : Sum R Ident)
  | Mtailcall (sg : Signature) (ros : Sum R Ident)
  | Mbuiltin (ef : ExtFun) (args : List (BuiltinArg R)) (res : BuiltinRes R)
  | Mlabel (lbl : Label)
  | Mgoto (lbl : Label)
  | Mcond (cond : C) (args : List R) (lbl : Label)
  | Mjumptable (arg : R) (tbl : List Label)
  | Mreturn

/-- `Mach.code` -/
abbrev Code (O A C R : Type) := List (Instruction O A C R)

/-- `Mach.function` -/
structure Function (O A C R : Type) where
  fn_sig : Signature
  fn_code : Code O A C R
  fn_stacksize : Z
  fn_link_ofs : Integers.Ptrofs
  fn_retaddr_ofs : Integers.Ptrofs

/-- `Mach.fundef` -/
abbrev Fundef (O A C R : Type) := ASTFundef (Function O A C R)

/-- `Mach.program` -/
abbrev Program (O A C R : Type) := ASTProgram (Fundef O A C R) Unit

/-- `Mach.is_leaf_function`: the function makes no call. -/
def isLeafFunction {O A C R : Type} (f : Function O A C R) : Bool :=
  f.fn_code.all (fun i => match i with | .Mcall _ _ => false | _ => true)

end MachSyntax
end CC
