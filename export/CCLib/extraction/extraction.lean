/-
  Lean counterpart of `extraction/extraction.v`.

  In Rocq, `extraction.v` turns the verified compiler into OCaml: it says how
  to implement every `Parameter` (mostly by untrusted OCaml code) and lists
  the functions the OCaml driver calls (`Separate Extraction …`).  Lean code
  is executable as it stands, so this file only has to do the first part:

  * **Untrusted oracles** (`Extract Constant`).  The Lean port takes them as
    fields of `Compiler.Config`.  `Extraction.defaultConfig` binds them to
    Lean implementations:
    - `Selection.compile_switch` ↦ `Switchaux.compileSwitch`
      (`CCLib/common/Switchaux.lean`, port of `common/Switchaux.ml`);
    - `Linearize.enumerate_aux` ↦ `Linearize.enumerateAuxDefault`
      (port of `backend/Linearizeaux.ml`, in `CCLib/backend/Linearize.lean`);
    - `Allocation.regalloc` ↦ `Regalloc.regalloc`
      (`CCLib/backend/Regalloc.lean`, port of `backend/Regalloc.ml`, with
      a spill-everything fallback, see that file);
    - `SimplExpr.first_unused_ident` ↦ `Camlcoq.firstUnusedIdent`
      (`CCLib/lib/Camlcoq.lean`; OCaml: the next unused atom of `Camlcoq`);
    - `RTLgen.more_likely` ↦ `RTLgenaux.moreLikely`
      (`CCLib/backend/RTLgenaux.lean`, port of `backend/RTLgenaux.ml`);
    - `Selection.if_conversion_heuristic` ↦
      `Selectionaux.ifConversionHeuristic`
      (`CCLib/backend/Selectionaux.lean`, port of `backend/Selectionaux.ml`);
    - `Inlining.inlining_analysis`/`should_inline` ↦
      `Inliningaux.shouldInlineProgram`
      (`CCLib/backend/Inliningaux.lean`, port of `backend/Inliningaux.ml`;
      the `C2C` information on `inline`/`static` functions is the argument
      `inl` of `configFor`).
    The heuristics only affect code quality.
    These results are either checked by a validator (`compile_switch`,
    `regalloc`, `enumerate_aux`) or irrelevant to correctness, as in Rocq.
  * **Compiler options** (`Compopts.*` from `Clflags`): the field defaults of
    `Compiler.Config`, which match `ccomp -O` (tail calls, constant
    propagation, CSE, redundancy elimination on; debug information off).
  * **Printing and timing** (`Compiler.print_*`, `Compiler.time`): identities,
    as `Compiler.print` and `Compiler.time` already are.
  * **Target directives** (`Load extractionMachdep`, i.e.
    `aarch64/extractionMachdep.v`): the section *Target settings* below
    (`ExtractionMachdep.Target`, `ExtractionMachdep.configure`).
  * Directives about OCaml itself (`Extract Inlined Constant` for
    `Datatypes`, `Extraction Inline`, `Extraction Blacklist`, the `Cabs`
    types, `Set Extraction AccessOpaque`) have no Lean counterpart.

  The second part of the Rocq file, `Separate Extraction`, is mirrored by the
  section *Entry points*: each extracted function is named there under its
  Rocq name.  Since these are `def`s (not `noncomputable`), building this
  file checks that every entry point is executable Lean code.

  `examples/ExtractionCheck.lean` runs `transf_clight_program` with
  `defaultConfig` on the example Clight programs.
-/
import CCLib.driver.Compiler
import CCLib.backend.Regalloc
import CCLib.common.Switchaux
import CCLib.cfrontend.Cexec
import CCLib.cfrontend.Ctyping
import CCLib.cfrontend.Initializers
import CCLib.cfrontend.CtypesAttr
import CCLib.common.ASTTheory
import CCLib.lib.FloatsParsed
import CCLib.cparser.Parser
import CCLib.lib.Camlcoq
import CCLib.backend.RTLgenaux
import CCLib.backend.Selectionaux
import CCLib.backend.Inliningaux
import CCLib.driver.CompilerCorrect

namespace CC

/-! ## Target settings (`aarch64/extractionMachdep.v`)

The Rocq file binds three target parameters to OCaml code that reads the
configuration (`Configuration.abi`, `Configuration.system`) and the atom
table of `C2C`:

* `Archi.abi` ↦ `Apple` if `Configuration.abi = "apple"`, else `AAPCS64`;
* `SelectOp.symbol_is_relocatable` ↦ `C2C.atom_is_external` on macOS,
  `C2C.atom_needs_GOT_access` otherwise;
* `Asmgen.symbol_is_aligned` ↦ `C2C.atom_is_aligned`.

(`Asm.symbol_low`/`symbol_high` are `assert false` in OCaml; they are not
parameters of the Lean port.)  Here the configuration strings are the fields
`abi` and `system` of `Target`, and the two `C2C` queries are fields too; by
default no symbol is relocatable or known to be aligned, which is the
conservative choice for both. -/
namespace ExtractionMachdep

/-- The target parameters read by `aarch64/extractionMachdep.v`. -/
structure Target where
  /-- `Configuration.abi` (`"standard"` or `"apple"`) -/
  abi : String := "standard"
  /-- `Configuration.system` (`"linux"` or `"macos"`) -/
  system : String := "linux"
  /-- `C2C.atom_is_external` (used on macOS) -/
  atomIsExternal : Ident → Bool := fun _ => false
  /-- `C2C.atom_needs_GOT_access` (used on other systems) -/
  atomNeedsGOTAccess : Ident → Bool := fun _ => false
  /-- `C2C.atom_is_aligned` -/
  atomIsAligned : Ident → Z → Bool := fun _ _ => false

/-- `Archi.abi` -/
def abi (s : String) : Conventions1.AbiKind :=
  if s = "apple" then .Apple else .AAPCS64

/-- `SelectOp.symbol_is_relocatable` -/
def symbolIsRelocatable (t : Target) : Ident → Bool :=
  if t.system = "macos" then t.atomIsExternal else t.atomNeedsGOTAccess

/-- Apply the target settings to a compiler configuration. -/
def configure (t : Target) (c : Compiler.Config) : Compiler.Config :=
  { c with
    abi := abi t.abi
    symbolIsRelocatable := symbolIsRelocatable t
    symbolIsAligned := t.atomIsAligned }

theorem abi_standard : abi "standard" = .AAPCS64 := by simp [abi]
theorem abi_apple : abi "apple" = .Apple := by simp [abi]

end ExtractionMachdep

namespace Extraction

/-- The compiler configuration with every untrusted oracle bound to its Lean
    implementation, for the target settings `t` (`Configuration` and
    `C2C`, see `CCLib/aarch64/extractionMachdep.lean`) and the inlining
    information `inl`. -/
def configFor (t : ExtractionMachdep.Target) (inl : Inliningaux.Options := {}) :
    Compiler.Config :=
  ExtractionMachdep.configure t
    { firstUnusedIdent := Camlcoq.firstUnusedIdent
      compileSwitch := Switchaux.compileSwitch
      ifConversionHeuristic := Selectionaux.ifConversionHeuristic
      moreLikely := RTLgenaux.moreLikely
      shouldInline := Inliningaux.shouldInlineProgram inl
      regalloc := Regalloc.regalloc (ExtractionMachdep.abi t.abi)
      enumerateAux := Linearize.enumerateAuxDefault }

/-- `defaultConfig`: Linux, standard AAPCS64 ABI, `ccomp -O` options. -/
def defaultConfig : Compiler.Config := configFor {}

/-! ## Entry points (`Separate Extraction …`)

Each name below is one of the functions extracted by `extraction.v`; the
compiler functions are instantiated with `defaultConfig`. -/

/-- `Compiler.transf_c_program` -/
def transf_c_program : Csyntax.Program → Res Asm.Program :=
  Compiler.transfCProgram defaultConfig
/-- `Compiler.transf_cminor_program` -/
def transf_cminor_program : Cminor.Program → Res Asm.Program :=
  Compiler.transfCminorProgram defaultConfig
/-- `Compiler.transf_clight_program` (not in the Rocq list; used by the
    examples, whose programs are Clight). -/
def transf_clight_program : Program → Res Asm.Program :=
  Compiler.transfClightProgram defaultConfig

/-- `Cexec.do_initial_state` -/
def do_initial_state := @Cexec.doInitialState
/-- `Cexec.do_step` -/
def do_step := @Cexec.doStep
/-- `Cexec.at_final_state` -/
def at_final_state := @Cexec.atFinalState

/-- `Ctypes.merge_attributes` -/
def merge_attributes := @mergeAttributes
/-- `Ctypes.remove_attributes` -/
def remove_attributes := @removeAttributes
/-- `Ctypes.build_composite_env` -/
def build_composite_env := @buildCompositeEnv
/-- `Ctypes.layout_struct` -/
def layout_struct := @layoutStruct
/-- `Ctypes.make_program` -/
def make_program := @makeProgram

/-- `Initializers.transl_init` -/
def transl_init := @Initializers.translInit
/-- `Initializers.constval` -/
def constval := @Initializers.constval

/-- `Csyntax.Eindex` -/
def Eindex := @Csyntax.Eindex
/-- `Csyntax.Epreincr` -/
def Epreincr := @Csyntax.Epreincr
/-- `Csyntax.Eselection` -/
def Eselection := @Csyntax.Eselection

/-- `Ctyping.typecheck_program` -/
def typecheck_program := @Ctyping.typecheckProgram
/-- `Ctyping.epostincr` -/
def epostincr := @Ctyping.epostincr
/-- `Ctyping.epostdecr` -/
def epostdecr := @Ctyping.epostdecr
/-- `Ctyping.epreincr` -/
def epreincr := @Ctyping.epreincr
/-- `Ctyping.epredecr` -/
def epredecr := @Ctyping.epredecr
/-- `Ctyping.eselection` -/
def eselection := @Ctyping.eselection

/-- `Clight.type_of_function` -/
def type_of_function := @typeOfFunction

/-- `Conventions1.callee_save_type` -/
def callee_save_type := @Conventions1.calleeSaveType
/-- `Conventions1.is_float_reg` -/
def is_float_reg := @Conventions1.isFloatReg
/-- `Conventions1.int_caller_save_regs` -/
def int_caller_save_regs := Conventions1.intCallerSaveRegs
/-- `Conventions1.float_caller_save_regs` -/
def float_caller_save_regs := Conventions1.floatCallerSaveRegs
/-- `Conventions1.int_callee_save_regs` -/
def int_callee_save_regs := Conventions1.intCalleeSaveRegs
/-- `Conventions1.float_callee_save_regs` -/
def float_callee_save_regs := Conventions1.floatCalleeSaveRegs
/-- `Conventions1.dummy_int_reg` -/
def dummy_int_reg := Conventions1.dummyIntReg
/-- `Conventions1.dummy_float_reg` -/
def dummy_float_reg := Conventions1.dummyFloatReg
/-- `Conventions1.allocatable_registers` -/
def allocatable_registers := @Conventions1.allocatableRegisters

/-- `RTL.instr_defs` -/
def instr_defs := @RTL.instrDefs
/-- `RTL.instr_uses` -/
def instr_uses := @RTL.instrUses

/-- `Machregs.mregs_for_operation` -/
def mregs_for_operation := @mregsForOperation
/-- `Machregs.mregs_for_builtin` -/
def mregs_for_builtin := @mregsForBuiltin
/-- `Machregs.two_address_op` -/
def two_address_op := @twoAddressOp
/-- `Machregs.is_stack_reg` -/
def is_stack_reg := @Mreg.isStackReg
/-- `Machregs.destroyed_at_indirect_call` -/
def destroyed_at_indirect_call := destroyedAtIndirectCall

/-- `AST.signature_main` -/
def signature_main := CC.signature_main

/-- `Floats.Float32.from_parsed` -/
def float32_from_parsed := @Floats.Float32.from_parsed
/-- `Floats.Float.from_parsed` -/
def float_from_parsed := @Floats.Float.from_parsed

/-- `Globalenvs.Senv.invert_symbol` -/
def invert_symbol := @Genv.invertSymbol

/-- `Parser.translation_unit_file` -/
def translation_unit_file := @Parser.translation_unit_file

/-! ## Correctness of the executable compiler

The oracles bound above are untrusted, so semantic preservation holds for
`transf_c_program` exactly as for any configuration
(`Compiler.transfCProgram_correct`, `driver/Compiler.v`'s
`transf_c_program_correct`), under the same assumptions on external
functions and inline assembly. -/

example : defaultConfig.abi = .AAPCS64 := by decide

/-- `transf_c_program_correct` for the executable AArch64 compiler. -/
theorem transf_c_program_correct (sym : Asm.SymbolSplit) (p : Csyntax.Program)
    (tp : Asm.Program) (h : transf_c_program p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)
    (hrec : ExternalsReceptive (Csem.globalenv p).genv_genv.toSenv) :
    Smallstep.BackwardSimulation (Csem.semantics p) (Asm.semantics sym .AAPCS64 tp) :=
  Compiler.transfCProgram_correct defaultConfig sym p tp h hext hasm hextx hasmx hextw hasmw hextp hasmp hrec

end Extraction
end CC
