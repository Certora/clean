/-
  [x86-64 instance of `CCLib/driver/Compiler.lean`.]

  The whole compiler for the x86-64 target — port of the definitions of
  `driver/Compiler.v` (`transf_rtl_program`, `transf_cminor_program`,
  `transf_clight_program`, `transf_c_program`) with the x86-64 back end
  (`CCLib/x86/…`).  The front end (CompCert C → Cminor) is the shared one of
  `CCLib/cfrontend/`, and the composition operators `@@`, `@@@`, `totalIf`,
  `partialIf`, `time` are those of `CCLib/driver/Compiler.lean`.

  Differences from Rocq: as in `CCLib/driver/Compiler.lean`, the compiler
  options of `Compopts.v`, the untrusted OCaml components and the target
  parameter `Archi.win64` are fields of a `Config` record.  On x86-64,
  `Conventions1.parameter_needs_normalization` is constantly `false`, so the
  shared `SimplLocals` (parameterized by an aarch64 `AbiKind`) is run with
  `.Apple`, for which that function is also `false`; `Cshmgen` is given the
  x86 `Conventions1.return_value_needs_normalization`.
-/
import CCLib.driver.Compiler
import CCLib.x86.Selection
import CCLib.x86.RTLgen
import CCLib.x86.Tailcall
import CCLib.x86.Inlining
import CCLib.x86.Renumber
import CCLib.x86.Constprop
import CCLib.x86.CSE
import CCLib.x86.Deadcode
import CCLib.x86.Unusedglob
import CCLib.x86.Allocation
import CCLib.x86.Tunneling
import CCLib.x86.Linearize
import CCLib.x86.CleanupLabels
import CCLib.x86.Debugvar
import CCLib.x86.Stacking
import CCLib.x86.Asmgen
import CCLib.driver.Compopts

namespace CC
namespace X86
namespace Compiler

open CC.Compiler (applyTotal applyPartial time totalIf partialIf)
open CC.Compiler

/-- The ABI kind given to the shared `SimplLocals`: no normalization of
    small-integer parameters, as on x86-64. -/
def frontendAbi : CC.Conventions1.AbiKind := .Apple

theorem frontendAbi_no_param_normalization (t : XType) :
    CC.Conventions1.parameterNeedsNormalization frontendAbi t = false := rfl

/-- Compiler options (`Compopts.v`, inherited from `CC.Compopts`), target parameters, and the untrusted
    components that CompCert implements outside Rocq (x86-64 back end). -/
structure Config extends CC.Compopts where
  /-- `Archi.win64` (Windows x86-64 calling conventions) -/
  win64 : Bool := false
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
end Config

open Config

variable (c : Config)

/-- `transf_rtl_program`: the back end, from RTL to x86-64 assembly. -/
def transfRtlProgram (f : RTL.Program) : Res Asm.Program :=
  Res.OK f
   @@ totalIf (fun _ => c.optimTailcalls) (time "Tail calls" (Tailcall.transfProgram c.win64))
  @@@ time "Inlining" (Inlining.transfProgram id c.shouldInline)
   @@ time "Renumbering" Renumber.transfProgram
   @@ totalIf (fun _ => c.optimConstprop)
        (time "Constant propagation" (Constprop.transfProgram c.constpropOptions))
   @@ totalIf (fun _ => c.optimConstprop) (time "Renumbering" Renumber.transfProgram)
  @@@ partialIf (fun _ => c.optimCSE) (time "CSE" (CSE.transfProgram c.vaOptions))
  @@@ partialIf (fun _ => c.optimRedundancy)
        (time "Redundancy elimination" (Deadcode.transfProgram c.vaOptions))
  @@@ time "Unused globals" Unusedglob.transformProgram
  @@@ time "Register allocation" (Allocation.transfProgram c.win64 c.regalloc)
   @@ time "Branch tunneling" Tunneling.tunnelProgram
  @@@ time "CFG linearization" (Linearize.transfProgram c.enumerateAux)
   @@ time "Label cleanup" CleanupLabels.transfProgram
  @@@ partialIf (fun _ => c.debug)
        (time "Debugging info for local variables" (Debugvar.transfProgram c.win64))
  @@@ time "Mach generation" (Stacking.transfProgram c.win64)
  @@@ time "Asm generation" Asmgen.transfProgram

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
  @@@ time "C#minor generation" (Cshmgen.translProgram X86.Conventions1.returnValueNeedsNormalization)
  @@@ time "Cminor generation" Cminorgen.translProgram
  @@@ transfCminorProgram c

/-- `transf_c_program`: the whole compiler, from CompCert C to x86-64
    assembly. -/
def transfCProgram (p : Csyntax.Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Clight generation" (SimplExpr.translProgram (c.firstUnusedIdent p))
  @@@ transfClightProgram c

end Compiler
end X86
end CC
