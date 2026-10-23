/-
  The whole compiler — port of the definitions of `driver/Compiler.v`.

  Ported: `apply_total` (`@@`), `apply_partial` (`@@@`), `print`, `time`,
  `total_if`, `partial_if`, `transf_rtl_program`, `transf_cminor_program`,
  `transf_clight_program`, `transf_c_program`, for the AArch64 back end.

  Differences from Rocq:
  * The compiler options of `Compopts.v` (`optim_tailcalls`,
    `optim_constprop`, `optim_CSE`, `optim_redundancy`, `debug`,
    `va_strict`, `propagate_float_constants`, `generate_float_constants`,
    `optim_for_size`), the ABI (`Archi.abi`), and the untrusted components
    that CompCert implements in OCaml and leaves as `Parameter`s
    (the register allocator `regalloc`, the basic-block enumeration of
    `Linearize.enumerate_aux`, `Selection.compile_switch`,
    `Selection.if_conversion_heuristic`, `RTLgen.more_likely`,
    `Inlining.should_inline` / `inlining_analysis`,
    `SimplExpr.first_unused_ident`, `SelectOp.symbol_is_relocatable`,
    `Asmgen.symbol_is_aligned`) are fields of a `Config` record.
    `Inlining.inlining_analysis` is folded into `shouldInline`, which
    receives the whole program.
  * `print` and `time` are identities (as they are, semantically, in Rocq).
  * The correctness theorems of `Compiler.v` (`transf_c_program_correct`,
    the `match_prog` composition through `Linking`, separate compilation)
    are not ported: they need the simulation proofs of every pass.
-/
import CCLib.cfrontend.SimplExpr
import CCLib.cfrontend.SimplLocals
import CCLib.cfrontend.Cshmgen
import CCLib.cfrontend.Cminorgen
import CCLib.backend.Selection
import CCLib.backend.RTLgen
import CCLib.backend.Tailcall
import CCLib.backend.Inlining
import CCLib.backend.Renumber
import CCLib.backend.Constprop
import CCLib.backend.CSE
import CCLib.backend.Deadcode
import CCLib.backend.Unusedglob
import CCLib.backend.Allocation
import CCLib.backend.Tunneling
import CCLib.backend.Linearize
import CCLib.backend.CleanupLabels
import CCLib.backend.Debugvar
import CCLib.backend.Stacking
import CCLib.aarch64.Asmgen
import CCLib.driver.Compopts

namespace CC
namespace Compiler

/-- `apply_total`, written `a @@ f`. -/
def applyTotal {A B : Type} (x : Res A) (f : A → B) : Res B :=
  match x with
  | .Error msg => .Error msg
  | .OK x1 => .OK (f x1)

/-- `apply_partial`, written `a @@@ f`. -/
def applyPartial {A B : Type} (x : Res A) (f : A → Res B) : Res B :=
  match x with
  | .Error msg => .Error msg
  | .OK x1 => f x1

scoped infixl:50 " @@@ " => applyPartial
scoped infixl:50 " @@ " => applyTotal

/-- `print`: the printer is called for its side effect only. -/
def print {A : Type} (_printer : A → Unit) (prog : A) : A := prog

/-- `time` -/
def time {A B : Type} (_name : String) (f : A → B) : A → B := f

/-- `total_if` -/
def totalIf {A : Type} (flag : Unit → Bool) (f : A → A) (prog : A) : A :=
  if flag () then f prog else prog

/-- `partial_if` -/
def partialIf {A : Type} (flag : Unit → Bool) (f : A → Res A) (prog : A) : Res A :=
  if flag () then f prog else .OK prog

/-- Compiler options (`Compopts.v`, inherited from `CC.Compopts`), target parameters, and the untrusted
    components that CompCert implements outside Rocq. -/
structure Config extends CC.Compopts where
  /-- `Archi.abi` -/
  abi : Conventions1.AbiKind := .AAPCS64
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false
  /-- `Asmgen.symbol_is_aligned` -/
  symbolIsAligned : Ident → Z → Bool := fun _ _ => false
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

def vaOptions : ValueAOp.Options :=
  { strict := c.vaStrict, propagateFloatConstants := c.propagateFloatConstants }

def constpropOptions : ConstpropOp.Options :=
  { strict := c.vaStrict, propagateFloatConstants := c.propagateFloatConstants,
    generateFloatConstants := c.generateFloatConstants,
    symbolIsRelocatable := c.symbolIsRelocatable }

def selectionOptions : Selection.Options :=
  { symbolIsRelocatable := c.symbolIsRelocatable, optimForSize := c.optimForSize,
    compileSwitch := c.compileSwitch, ifConversionHeuristic := c.ifConversionHeuristic }

def simplLocalsOptions : SimplLocals.Options := { debug := c.debug, abi := c.abi }

def asmgenOptions : Asmgen.Options :=
  { symbolIsAligned := c.symbolIsAligned, symbolIsRelocatable := c.symbolIsRelocatable }
end Config

open Config

variable (c : Config)

/-- `transf_rtl_program`: the back end, from RTL to Asm. -/
def transfRtlProgram (f : RTL.Program) : Res Asm.Program :=
  Res.OK f
   @@ totalIf (fun _ => c.optimTailcalls) (time "Tail calls" (Tailcall.transfProgram c.abi))
  @@@ time "Inlining" (Inlining.transfProgram id c.shouldInline)
   @@ time "Renumbering" Renumber.transfProgram
   @@ totalIf (fun _ => c.optimConstprop)
        (time "Constant propagation" (Constprop.transfProgram c.constpropOptions c.abi))
   @@ totalIf (fun _ => c.optimConstprop) (time "Renumbering" Renumber.transfProgram)
  @@@ partialIf (fun _ => c.optimCSE) (time "CSE" (CSE.transfProgram c.vaOptions c.abi))
  @@@ partialIf (fun _ => c.optimRedundancy)
        (time "Redundancy elimination" (Deadcode.transfProgram c.vaOptions c.abi))
  @@@ time "Unused globals" Unusedglob.transformProgram
  @@@ time "Register allocation" (Allocation.transfProgram c.abi c.regalloc)
   @@ time "Branch tunneling" Tunneling.tunnelProgram
  @@@ time "CFG linearization" (Linearize.transfProgram c.enumerateAux)
   @@ time "Label cleanup" CleanupLabels.transfProgram
  @@@ partialIf (fun _ => c.debug)
        (time "Debugging info for local variables" Debugvar.transfProgram)
  @@@ time "Mach generation" (Stacking.transfProgram c.abi)
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
  @@@ time "C#minor generation" (Cshmgen.translProgram (Conventions1.returnValueNeedsNormalization c.abi))
  @@@ time "Cminor generation" Cminorgen.translProgram
  @@@ transfCminorProgram c

/-- `transf_c_program`: the whole compiler, from CompCert C to Asm. -/
def transfCProgram (p : Csyntax.Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Clight generation" (SimplExpr.translProgram (c.firstUnusedIdent p))
  @@@ transfClightProgram c

/-! ### Basic properties of the composition operators -/

theorem applyPartial_OK {A B : Type} (x : A) (f : A → Res B) :
    applyPartial (.OK x) f = f x := rfl

theorem applyTotal_OK {A B : Type} (x : A) (f : A → B) :
    applyTotal (.OK x) f = .OK (f x) := rfl

/-- `compose_print_identity` -/
theorem compose_print_identity {A : Type} (x : Res A) (f : A → Unit) :
    applyTotal x (print f) = x := by
  cases x <;> rfl

/-- If a composition of passes succeeds, so does each pass (inversion
    used throughout `Compiler.v`). -/
theorem applyPartial_OK_inv {A B : Type} {x : Res A} {f : A → Res B} {y : B}
    (h : applyPartial x f = .OK y) : ∃ x1, x = .OK x1 ∧ f x1 = .OK y := by
  cases x with
  | OK x1 => exact ⟨x1, rfl, h⟩
  | Error m => cases h

theorem applyTotal_OK_inv {A B : Type} {x : Res A} {f : A → B} {y : B}
    (h : applyTotal x f = .OK y) : ∃ x1, x = .OK x1 ∧ f x1 = y := by
  cases x with
  | OK x1 => cases h; exact ⟨x1, rfl, rfl⟩
  | Error m => cases h

end Compiler
end CC
