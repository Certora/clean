/-
  [RISC-V instance of `CCLib/driver/Compiler.lean`.]

  The whole compiler for the RISC-V (RV64) target — port of the definitions
  of `driver/Compiler.v` (`transf_rtl_program`, `transf_cminor_program`,
  `transf_clight_program`, `transf_c_program`) with the RISC-V back end
  (`CCLib/riscV/…`).  The front end (CompCert C → Cminor) is the shared one
  of `CCLib/cfrontend/`, and the composition operators `@@`, `@@@`,
  `totalIf`, `partialIf`, `time` are those of `CCLib/driver/Compiler.lean`.

  Differences from Rocq: as in `CCLib/driver/Compiler.lean`, the compiler
  options of `Compopts.v` and the untrusted OCaml components are fields of
  a `Config` record.  The RISC-V calling convention never needs
  normalization of small-integer arguments or results
  (`Conventions1.parameter_needs_normalization = false`); the shared front
  end, which is parameterized by an aarch64 `AbiKind`, is therefore run with
  `.Apple`, the ABI kind for which these functions are also constantly
  `false`.
-/
import CCLib.driver.Compiler
import CCLib.riscV.Selection
import CCLib.riscV.RTLgen
import CCLib.riscV.Tailcall
import CCLib.riscV.Inlining
import CCLib.riscV.Renumber
import CCLib.riscV.Constprop
import CCLib.riscV.CSE
import CCLib.riscV.Deadcode
import CCLib.riscV.Unusedglob
import CCLib.riscV.Allocation
import CCLib.riscV.Tunneling
import CCLib.riscV.Linearize
import CCLib.riscV.CleanupLabels
import CCLib.riscV.Debugvar
import CCLib.riscV.Stacking
import CCLib.riscV.Asmgen
import CCLib.driver.Compopts

namespace CC
namespace RiscV
namespace Compiler

open CC.Compiler (applyTotal applyPartial time totalIf partialIf)
open CC.Compiler

/-- The ABI kind given to the shared front end: no normalization of
    small-integer arguments and results, as on RISC-V. -/
def frontendAbi : CC.Conventions1.AbiKind := .Apple

theorem frontendAbi_no_normalization (t : XType) :
    CC.Conventions1.returnValueNeedsNormalization frontendAbi t = false ∧
    CC.Conventions1.parameterNeedsNormalization frontendAbi t = false := ⟨rfl, rfl⟩

/-- Compiler options (`Compopts.v`, inherited from `CC.Compopts`), target parameters, and the untrusted
    components that CompCert implements outside Rocq (RISC-V back end). -/
structure Config extends CC.Compopts where
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false
  /-- `SimplExpr.first_unused_ident` -/
  firstUnusedIdent : Csyntax.Program → Ident
  /-- `Selection.compile_switch` (its result is validated) -/
  compileSwitch : Z → Nat → Switch.Table → Switch.Comptree
  /-- `Selection.if_conversion_heuristic` -/
  ifConversionHeuristic :
    Ident → Cminor.Expr → Cminor.Expr → Cminor.Expr → ATyp → CminorSel.Stmt → Bool :=
    fun _ _ _ _ _ _ => true
  /-- `RTLgen.more_likely` -/
  moreLikely : CminorSel.Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool :=
    fun _ _ _ => false
  /-- `Inlining.should_inline (inlining_analysis p)` -/
  shouldInline : RTL.Program → Ident → RTL.Function → Bool := fun _ _ _ => false
  /-- `Allocation.regalloc` (its result is validated) -/
  regalloc : RTL.Function → Res LTL.Function
  /-- `Linearize.enumerate_aux` (its result is validated) -/
  enumerateAux : LTL.Function → PMap Bool → List LTL.Node

namespace Config
variable (c : Config)

def vaOptions : CC.ValueAOp.Options :=
  { strict := c.vaStrict, propagateFloatConstants := c.propagateFloatConstants }

def constpropOptions : CC.ConstpropOp.Options :=
  { strict := c.vaStrict, propagateFloatConstants := c.propagateFloatConstants,
    generateFloatConstants := c.generateFloatConstants,
    symbolIsRelocatable := c.symbolIsRelocatable }

def selectionOptions : Selection.Options :=
  { symbolIsRelocatable := c.symbolIsRelocatable, optimForSize := c.optimForSize,
    compileSwitch := c.compileSwitch, ifConversionHeuristic := c.ifConversionHeuristic }

def simplLocalsOptions : SimplLocals.Options := { debug := c.debug, abi := frontendAbi }

def asmgenOptions : Asmgen.Options := { symbolIsRelocatable := c.symbolIsRelocatable }
end Config

open Config

variable (c : Config)

/-- `transf_rtl_program`: the back end, from RTL to RISC-V assembly. -/
def transfRtlProgram (f : RTL.Program) : Res Asm.Program :=
  Res.OK f
   @@ totalIf (fun _ => c.optimTailcalls) (time "Tail calls" Tailcall.transfProgram)
  @@@ time "Inlining" (Inlining.transfProgram id c.shouldInline)
   @@ time "Renumbering" Renumber.transfProgram
   @@ totalIf (fun _ => c.optimConstprop)
        (time "Constant propagation" (Constprop.transfProgram c.constpropOptions))
   @@ totalIf (fun _ => c.optimConstprop) (time "Renumbering" Renumber.transfProgram)
  @@@ partialIf (fun _ => c.optimCSE) (time "CSE" (CSE.transfProgram c.vaOptions))
  @@@ partialIf (fun _ => c.optimRedundancy)
        (time "Redundancy elimination" (Deadcode.transfProgram c.vaOptions))
  @@@ time "Unused globals" Unusedglob.transformProgram
  @@@ time "Register allocation" (Allocation.transfProgram c.regalloc)
   @@ time "Branch tunneling" Tunneling.tunnelProgram
  @@@ time "CFG linearization" (Linearize.transfProgram c.enumerateAux)
   @@ time "Label cleanup" CleanupLabels.transfProgram
  @@@ partialIf (fun _ => c.debug)
        (time "Debugging info for local variables" Debugvar.transfProgram)
  @@@ time "Mach generation" Stacking.transfProgram
  @@@ time "Asm generation" (Asmgen.transfProgram c.asmgenOptions)

/-- `transf_cminor_program` -/
def transfCminorProgram (p : Cminor.Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Instruction selection" (Selection.selProgram c.selectionOptions)
  @@@ time "RTL generation" (RTLgen.translProgram c.moreLikely)
  @@@ transfRtlProgram c

/-- `transf_clight_program` -/
def transfClightProgram (p : Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Simplification of locals" (SimplLocals.transfProgram c.simplLocalsOptions)
  @@@ time "C#minor generation" (Cshmgen.translProgram (CC.Conventions1.returnValueNeedsNormalization frontendAbi))
  @@@ time "Cminor generation" Cminorgen.translProgram
  @@@ transfCminorProgram c

/-- `transf_c_program`: the whole compiler, from CompCert C to RISC-V
    assembly. -/
def transfCProgram (p : Csyntax.Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Clight generation" (SimplExpr.translProgram (c.firstUnusedIdent p))
  @@@ transfClightProgram c

end Compiler
end RiscV
end CC
