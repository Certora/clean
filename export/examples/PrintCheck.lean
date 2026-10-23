/-
  Checks of the intermediate-language printers (`PrintClight`,
  `PrintCsyntax`, `PrintCminor`, `PrintRTL`, `PrintLTL`, `PrintMach`,
  `PrintOp`): the `swap` Clight example is compiled pass by pass with the
  options of `Extraction.defaultConfig` (AArch64) and each intermediate
  program is printed.  The `#guard`s run when this file is built.
-/
import CCLib.extraction.extraction
import CCLib.cfrontend.PrintCsyntax
import CCLib.cfrontend.PrintClight
import CCLib.backend.PrintCminor
import CCLib.backend.PrintRTL
import CCLib.backend.PrintLTL
import CCLib.backend.PrintMach
import CCLib.backend.PrintXTL
import AsmTestPrograms

namespace PrintCheck
open CC AsmTestPrograms Compiler

def c : Compiler.Config := Extraction.defaultConfig

def toCminor (p : Program) : Res Cminor.Program :=
  Res.OK p
  @@@ SimplLocals.transfProgram c.simplLocalsOptions
  @@@ Cshmgen.translProgram (Conventions1.returnValueNeedsNormalization c.abi)
  @@@ Cminorgen.translProgram

def toRTL (p : Program) : Res RTL.Program :=
  toCminor p @@@ Selection.selProgram c.selectionOptions @@@ RTLgen.translProgram c.moreLikely

def toLTL (p : Program) : Res LTL.Program :=
  toRTL p @@@ Allocation.transfProgram c.abi c.regalloc

def swapProg : Program := match clightPrograms.lookup "swap" with
  | some p => p
  | none => mkprogram [] [] [] .xH

def toMach (p : Program) : Res Mach.Program :=
  toLTL p
   @@ Tunneling.tunnelProgram
  @@@ Linearize.transfProgram c.enumerateAux
   @@ CleanupLabels.transfProgram
  @@@ Stacking.transfProgram c.abi

def resText {A : Type} (r : Res A) (pr : A → String) : String :=
  match r with
  | .OK p => pr p
  | .Error _ => "<error>"

def lines (s : String) : List String := s.splitOn "\n"
def hasLine (s line : String) : Bool := (lines s).contains line

def clightText : String := PrintClight.printProgram .Clight2 swapProg
def cminorText : String := resText (toCminor swapProg) PrintCminor.printProgram
def rtlText : String := resText (toRTL swapProg) PrintRTL.printProgram
def ltlText : String := resText (toLTL swapProg) PrintLTL.printProgram
def machText : String := resText (toMach swapProg) PrintMach.printProgram
def csyntaxText : String := PrintCsyntax.printProgram CSwitch.prog


-- Clight (Clight2: parameters are temporaries)
#guard hasLine clightText "void swap(unsigned int *, unsigned int *);"
#guard hasLine clightText "void swap(unsigned int *$a, unsigned int *$b)"
#guard hasLine clightText "  register unsigned int $t;"
#guard hasLine clightText "  $t = *$a;"
#guard hasLine clightText "  *$b = $t;"
-- Cminor (the `Format` boxes break the long `extern` declarations)
#guard hasLine cminorText "\"swap\"(a, b) : ptr -> ptr -> void"
#guard hasLine cminorText "  t = int32[a];"
#guard hasLine cminorText "  int32[b] = t;"
#guard hasLine cminorText
  "extern \"__compcert_va_float64\" = runtime \"__compcert_va_float64\" : ptr ->"
#guard hasLine cminorText "         float"
-- RTL
#guard hasLine rtlText "swap(x2, x1) {"
#guard hasLine rtlText "    5:\tx4 = int32[x2 + 0]"
#guard hasLine rtlText "    1:\treturn"
-- LTL (after register allocation)
#guard hasLine ltlText "swap() {"
#guard hasLine ltlText "    1:\treturn"
#guard hasLine ltlText "    5:\tX3 = int32[X0 + 0]; "
#guard hasLine ltlText "    2:\tint32[X1 + 0] = X3; "
-- Mach
#guard hasLine machText "swap() {"
#guard hasLine machText "\treturn"
#guard hasLine machText "\tX3 = int32[X0 + 0]"
#guard hasLine machText "\tint32[X1 + 0] = X3"
-- XTL (register allocator), with and without an allocation
def xtlFun : XTL.XFunction :=
  { fn_sig := mksignature [] .Xint cc_default, fn_stacksize := 0, fn_entrypoint := .xH,
    fn_code := PTree.empty.set .xH [.Xmove (.V .xH .Tint) (.L (.R .R0)), .Xreturn [.L (.R .R0)]] }
#guard PrintXTL.printFunction none none xtlFun = "f() {\n    1:\tX0 = x1; return X0\n}\n\n"
#guard PrintXTL.printFunction (some fun _ => .S .Local 8 .Tint) none xtlFun =
  "f() {\n    1:\tX0 = x1{Li8}; return X0\n}\n\n"
-- CompCert C: the `switch` and the `for` loop
#guard hasLine csyntaxText "int main(void)"
#guard hasLine csyntaxText "  for (i = 0; i < 10; i++) {"
#guard hasLine csyntaxText "    switch (i) {"
#guard hasLine csyntaxText "      case 8:"
#guard hasLine csyntaxText "        x += 64;"
#guard hasLine csyntaxText "      default:"
-- `PrintOp` (AArch64) on its own
#guard PrintOp.printOperation (fun (n : Nat) => s!"x{n}") (.Oaddimm (Integers.Int.repr (-4))) [1] =
  "x1 + -4"
#guard PrintOp.printCondition (fun (n : Nat) => s!"x{n}") (.Cmaskzero (Integers.Int.repr 255)) [3] =
  "x3 & 0xff == 0"
#guard PrintOp.printAddressing (fun (n : Nat) => s!"x{n}") (.Aindexed (Integers.Int64.repr 8)) [2] =
  "x2 + 8"

end PrintCheck
