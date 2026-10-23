/-
  Recognition of tail calls — port of `backend/Tailcall.v` (an RTL → RTL
  optimisation): `is_return`, `niter`, `transf_instr`, `transf_function`,
  `transf_fundef`, `transf_program`.

  Difference from Rocq: `Archi.abi` (used by `tailcall_is_possible`) is an
  explicit argument `abi`.
-/
import CCLib.backend.RTL
import CCLib.backend.Conventions

namespace CC

/-- `AST.transf_fundef` -/
def ASTFundef.transf {A B : Type} (transf : A → B) : ASTFundef A → ASTFundef B
  | .Internal f => .Internal (transf f)
  | .External ef => .External ef

namespace Tailcall

open RTL Op Conventions1

/-- `Tailcall.is_return`: the code at `pc` moves `rret` to the return
    register through at most `n` `nop`s and moves and then returns it. -/
def isReturn : Nat → RTL.Function → RTL.Node → Reg → Bool
  | 0, _, _, _ => false
  | n' + 1, f, pc, rret =>
      match f.fn_code.get pc with
      | some (.Ireturn none) => true
      | some (.Ireturn (some r)) => r = rret
      | some (.Inop s) => isReturn n' f s rret
      | some (.Iop op args dst s) =>
          match isMoveOperation op args with
          | none => false
          | some src => if rret = src then isReturn n' f s dst else false
      | _ => false

/-- `Tailcall.niter` -/
def niter : Nat := 5

/-- `Tailcall.transf_instr` -/
def transfInstr (abi : AbiKind) (f : RTL.Function) (_pc : RTL.Node) (instr : RTL.Instruction) : RTL.Instruction :=
  match instr with
  | .Icall sig ros args res s =>
      if isReturn niter f s res && Conventions.tailcallIsPossible abi sig &&
          decide (sig.sig_res = f.fn_sig.sig_res)
      then .Itailcall sig ros args
      else instr
  | _ => instr

/-- `Tailcall.transf_function` -/
def transfFunction (abi : AbiKind) (f : RTL.Function) : RTL.Function :=
  if f.fn_stacksize = 0 ∧ f.fn_sig.sig_cc.cc_vararg = none
  then RTL.transfFunction (transfInstr abi f) f
  else f

/-- `Tailcall.transf_fundef` -/
def transfFundef (abi : AbiKind) (fd : RTL.Fundef) : RTL.Fundef := ASTFundef.transf (transfFunction abi) fd

/-- `Tailcall.transf_program` -/
def transfProgram (abi : AbiKind) (p : RTL.Program) : RTL.Program :=
  transformProgram (transfFundef abi) p

end Tailcall
end CC
