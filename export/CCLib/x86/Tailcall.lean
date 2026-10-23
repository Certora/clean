/-
  [x86-64 instance of `CCLib/backend/Tailcall.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Recognition of tail calls — port of `backend/Tailcall.v` (an RTL → RTL
  optimisation): `is_return`, `niter`, `transf_instr`, `transf_function`,
  `transf_fundef`, `transf_program`.

  Difference from Rocq: `Archi.abi` (used by `tailcall_is_possible`) is an
  explicit argument `win64`.
-/
import CCLib.x86.RTL
import CCLib.x86.Conventions

namespace CC
namespace X86

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
def transfInstr (win64 : Bool) (f : RTL.Function) (_pc : RTL.Node) (instr : RTL.Instruction) : RTL.Instruction :=
  match instr with
  | .Icall sig ros args res s =>
      if isReturn niter f s res && Conventions.tailcallIsPossible win64 sig &&
          decide (sig.sig_res = f.fn_sig.sig_res)
      then .Itailcall sig ros args
      else instr
  | _ => instr

/-- `Tailcall.transf_function` -/
def transfFunction (win64 : Bool) (f : RTL.Function) : RTL.Function :=
  if f.fn_stacksize = 0 ∧ f.fn_sig.sig_cc.cc_vararg = none
  then RTL.transfFunction (transfInstr win64 f) f
  else f

/-- `Tailcall.transf_fundef` -/
def transfFundef (win64 : Bool) (fd : RTL.Fundef) : RTL.Fundef := ASTFundef.transf (transfFunction win64) fd

/-- `Tailcall.transf_program` -/
def transfProgram (win64 : Bool) (p : RTL.Program) : RTL.Program :=
  transformProgram (transfFundef win64) p

end Tailcall
end X86
end CC
