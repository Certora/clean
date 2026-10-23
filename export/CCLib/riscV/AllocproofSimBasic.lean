/-
  [RISC-V instance of `CCLib/backend/AllocproofSimBasic.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Correctness of register allocation, part 5 — the beginning of the
  `PRESERVATION` section of `backend/Allocproof.v`: preservation of the
  global environment (`symbols_preserved`, `functions_translated`, …,
  `find_function_translated`) and a few helper lemmas shared by the cases of
  `step_simulation`.
-/
import CCLib.riscV.AllocproofStep

namespace CC
namespace RiscV
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions Smallstep
open Allocation.Eqs (add remove)

/-- Inversion of a successful `Option` bind (used to decompose `transfer_aux`). -/
theorem obind_some {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- A failed negated test. -/
theorem bnot_not_true {b : Bool} (h : ¬ (!b) = true) : b = true := by cases b <;> simp_all

section PRESERVATION
variable (regalloc : RTL.Function → Res LTL.Function)
  {prog : RTL.Program} {tprog : LTL.Program}
  (TRANSF : Allocation.transfProgram  regalloc prog = .OK tprog)
include TRANSF

/-- `Allocproof.symbols_preserved` -/
theorem symbols_preserved (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  find_symbol_transf_partial TRANSF id

/-- `Allocproof.senv_preserved` -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  senv_transf_partial TRANSF

/-- `Allocproof.functions_translated` -/
theorem functions_translated {v : Val} {f : RTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧
      Allocation.transfFundef  regalloc f = .OK tf :=
  find_funct_transf_partial TRANSF h

/-- `Allocproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {f : RTL.Fundef}
    (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧
      Allocation.transfFundef  regalloc f = .OK tf :=
  find_funct_ptr_transf_partial TRANSF h

omit TRANSF in
/-- `Allocproof.sig_function_translated` -/
theorem sig_function_translated {f : RTL.Fundef} {tf : LTL.Fundef}
    (h : Allocation.transfFundef  regalloc f = .OK tf) : LTL.funsig tf = RTL.funsig f := by
  cases f with
  | Internal f =>
    unfold Allocation.transfFundef ASTFundef.transfPartial at h
    dsimp only at h
    cases h' : Allocation.transfFunction  regalloc f with
    | Error _ => rw [h'] at h; cases h
    | OK tf' =>
      rw [h'] at h; cases h
      cases transf_function_inv h' with
      | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsig => simp [LTL.funsig, RTL.funsig, hsig]
  | External ef =>
    unfold Allocation.transfFundef ASTFundef.transfPartial at h
    cases h; rfl

/-- `Allocproof.find_function_translated` -/
theorem find_function_translated {ros : Sum Reg Ident} {rs : RTL.Regset} {fd : RTL.Fundef}
    {ros' : Sum Mreg Ident} {e e' : Eqs} {ls : Locset}
    (h : RTL.findFunction prog.globalenv ros rs = some fd)
    (he : addEquationRos ros ros' e = some e') (hs : Satisf rs ls e') :
    ∃ tfd, LTL.findFunction tprog.globalenv ros' ls = some tfd ∧
      Allocation.transfFundef  regalloc fd = .OK tfd := by
  cases ros with
  | inl r =>
    cases ros' with
    | inl r' =>
      simp only [addEquationRos, Option.some.injEq] at he
      subst he
      have LD := add_equation_lessdef hs
      simp only [selVal] at LD
      simp only [RTL.findFunction] at h
      have hne : rs.get r ≠ .Vundef := by
        intro hu; rw [hu] at h; simp [Genv.findFunct] at h
      generalize rs.get r = v at LD h hne
      cases LD with
      | refl => exact functions_translated  regalloc TRANSF h
      | undef => exact absurd rfl hne
    | inr _ => simp [addEquationRos] at he
  | inr id =>
    cases ros' with
    | inl _ => simp [addEquationRos] at he
    | inr id' =>
      simp only [addEquationRos] at he
      split at he
      · next hid =>
        subst hid
        simp only [RTL.findFunction] at h
        simp only [LTL.findFunction, symbols_preserved  regalloc TRANSF]
        cases e : Genv.findSymbol prog.globalenv id with
        | none => rw [e] at h; cases h
        | some b => rw [e] at h; exact function_ptr_translated  regalloc TRANSF h
      · cases he

end PRESERVATION

end Allocproof
end RiscV
end CC
