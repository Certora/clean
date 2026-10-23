/-
  Printing AArch64 assembly code — port of `aarch64/TargetPrinter.ml`.

  The OCaml module has a module type `SYSTEM` with two implementations
  (`ELF_System` for Linux, `MacOS_System`) and a functor `Target` producing
  the `PrintAsmaux.TARGET` used by `PrintAsm`.  Here `System` is a structure
  with the values `elfSystem` and `macosSystem`, and `target` builds a
  `PrintAsm.Target Asm.Function`; `selSystem` is `sel_target`.

  Not ported: `-g` (`print_file_line`, the `.file` directives of
  `print_epilogue`).
-/
import CCLib.aarch64.Asm
import CCLib.backend.PrintAsm

namespace CC
namespace TargetPrinter

open Asm Sections PrintAsmaux

/-! ## Immediate floating-point operands of `fmov` -/

/-- `TargetPrinter.is_immediate_float64`: "a normalized binary floating
    point encoding with 1 sign bit, 4 bits of fraction and a 3-bit
    exponent". -/
def isImmediateFloat64 (bits : Nat) : Bool :=
  let exp : Int := (bits / 2 ^ 52 % 2 ^ 11 : Nat) - 1023
  let mant := bits % 2 ^ 52
  decide (-3 ≤ exp) && decide (exp ≤ 4) && mant % 2 ^ 48 == 0

/-- `TargetPrinter.is_immediate_float32` -/
def isImmediateFloat32 (bits : Nat) : Bool :=
  let exp : Int := (bits / 2 ^ 23 % 2 ^ 8 : Nat) - 127
  let mant := bits % 2 ^ 23
  decide (-3 ≤ exp) && decide (exp ≤ 4) && mant % 2 ^ 19 == 0

/-- `%.7f` of an immediate float: `sign`, unbiased exponent `exp`
    (`-3 ≤ exp ≤ 4`) and 4-bit fraction `m`.  The value is a multiple of
    `1/128`, so seven decimals are exact. -/
def immFloatString (sign : Bool) (exp : Int) (m : Nat) : String :=
  -- |value| * 10^7 = (16 + m) * 2^(exp+3) * 10^7 / 128
  let k := (16 + m) * 2 ^ (exp + 3).toNat * 78125
  let ip := k / 10 ^ 7
  let fp := k % 10 ^ 7
  let fs := toString fp
  let fs := String.ofList (List.replicate (7 - fs.length) '0') ++ fs
  (if sign then "-" else "") ++ s!"{ip}.{fs}"

/-- `%.7f` of the 64-bit float with bits `bits` (assumed immediate). -/
def immFloat64String (bits : Nat) : String :=
  immFloatString (bits / 2 ^ 63 = 1) ((bits / 2 ^ 52 % 2 ^ 11 : Nat) - 1023) (bits / 2 ^ 48 % 16)

/-- `%.7f` of the 32-bit float with bits `bits` (assumed immediate). -/
def immFloat32String (bits : Nat) : String :=
  immFloatString (bits / 2 ^ 31 = 1) ((bits / 2 ^ 23 % 2 ^ 8 : Nat) - 127) (bits / 2 ^ 19 % 16)

#guard immFloat64String 0x3FF0000000000000 = "1.0000000"
#guard immFloat64String 0xC002000000000000 = "-2.2500000"
#guard immFloat64String 0x3FC0000000000000 = "0.1250000"
#guard isImmediateFloat64 0x3FF0000000000000 && !isImmediateFloat64 0x3FB999999999999A

/-! ## Registers -/

/-- `TargetPrinter.xreg_name` -/
def xregName : Ireg → String
  | .X0 => "x0" | .X1 => "x1" | .X2 => "x2" | .X3 => "x3"
  | .X4 => "x4" | .X5 => "x5" | .X6 => "x6" | .X7 => "x7"
  | .X8 => "x8" | .X9 => "x9" | .X10 => "x10" | .X11 => "x11"
  | .X12 => "x12" | .X13 => "x13" | .X14 => "x14" | .X15 => "x15"
  | .X16 => "x16" | .X17 => "x17" | .X18 => "x18" | .X19 => "x19"
  | .X20 => "x20" | .X21 => "x21" | .X22 => "x22" | .X23 => "x23"
  | .X24 => "x24" | .X25 => "x25" | .X26 => "x26" | .X27 => "x27"
  | .X28 => "x28" | .X29 => "x29" | .X30 => "x30"

/-- `TargetPrinter.wreg_name` -/
def wregName (r : Ireg) : String := "w" ++ (xregName r).drop 1

/-- `TargetPrinter.xreg0_name` -/
def xreg0Name : Ireg0 → String | .RR0 r => xregName r | .XZR => "xzr"
/-- `TargetPrinter.wreg0_name` -/
def wreg0Name : Ireg0 → String | .RR0 r => wregName r | .XZR => "wzr"
/-- `TargetPrinter.xregsp_name` -/
def xregspName : Iregsp → String | .RR1 r => xregName r | .XSP => "sp"
/-- `TargetPrinter.wregsp_name` -/
def wregspName : Iregsp → String | .RR1 r => wregName r | .XSP => "wsp"

/-- `TargetPrinter.dreg_name` -/
def dregName : Freg → String
  | .D0 => "d0" | .D1 => "d1" | .D2 => "d2" | .D3 => "d3"
  | .D4 => "d4" | .D5 => "d5" | .D6 => "d6" | .D7 => "d7"
  | .D8 => "d8" | .D9 => "d9" | .D10 => "d10" | .D11 => "d11"
  | .D12 => "d12" | .D13 => "d13" | .D14 => "d14" | .D15 => "d15"
  | .D16 => "d16" | .D17 => "d17" | .D18 => "d18" | .D19 => "d19"
  | .D20 => "d20" | .D21 => "d21" | .D22 => "d22" | .D23 => "d23"
  | .D24 => "d24" | .D25 => "d25" | .D26 => "d26" | .D27 => "d27"
  | .D28 => "d28" | .D29 => "d29" | .D30 => "d30" | .D31 => "d31"

/-- `TargetPrinter.sreg_name` -/
def sregName (r : Freg) : String := "s" ++ (dregName r).drop 1

#guard wregName .X17 = "w17" && sregName .D31 = "s31"

/-- `TargetPrinter.ireg` -/
def ireg : Isize → Ireg → String | .X, r => xregName r | .W, r => wregName r
/-- `TargetPrinter.ireg0` -/
def ireg0 : Isize → Ireg0 → String | .X, r => xreg0Name r | .W, r => wreg0Name r
/-- `TargetPrinter.iregsp` -/
def iregsp : Isize → Iregsp → String | .X, r => xregspName r | .W, r => wregspName r
/-- `TargetPrinter.freg` -/
def freg : Fsize → Freg → String | .D, r => dregName r | .S, r => sregName r

/-- `TargetPrinter.intsz`: an immediate printed as a 64-bit or 32-bit
    signed number. -/
def intsz : Isize → Int → String
  | .X, n => coqint64 (Integers.Int64.repr n)
  | .W, n => coqint (Integers.Int.repr n)

/-- `TargetPrinter.preg_asm` -/
def pregAsm (ty : ATyp) : Preg → M Unit
  | .IR r => out (if ty = .Tint then wregName r else xregName r)
  | .FR r => out (if ty = .Tsingle then sregName r else dregName r)
  | _ => fail "preg_asm"

/-- `TargetPrinter.preg_annot` -/
def pregAnnot : Preg → String
  | .IR r => xregName r
  | .FR r => dregName r
  | _ => "<bad register>"

/-! ## Systems (`SYSTEM`) -/

/-- `TargetPrinter.SYSTEM` -/
structure System where
  comment : String
  rawSymbol : String → String
  symbol : Ident → String
  symbolOffsetHigh : Ident → Integers.Ptrofs → String
  symbolOffsetLow : Ident → Integers.Ptrofs → String
  label : Nat → String
  labelHigh : Nat → String
  labelLow : Nat → String
  loadSymbolAddress : Ireg → Ident → M Unit
  nameOfSection : SectionName → String
  printFunInfo : Ident → M Unit
  printVarInfo : Ident → M Unit
  printCommDecl : Ident → Int → Nat → M Unit
  printLcommDecl : Ident → Int → Nat → M Unit
  /-- `Configuration.system` -/
  system : String

/-- `TargetPrinter.ELF_System` -/
def elfSystem : System :=
  let symbol := elfSymbol
  { comment := "//"
    rawSymbol := id
    symbol
    symbolOffsetHigh := elfSymbolOffset
    symbolOffsetLow := fun id ofs => "#:lo12:" ++ elfSymbolOffset id ofs
    label := elfLabel
    labelHigh := elfLabel
    labelLow := fun lbl => "#:lo12:" ++ elfLabel lbl
    loadSymbolAddress := fun rd id => do
      out s!"\tadrp\t{xregName rd}, :got:{symbol id}\n"
      out s!"\tldr\t{xregName rd}, [{xregName rd}, #:got_lo12:{symbol id}]\n"
    nameOfSection := fun
      | .Section_text => ".text"
      | .Section_data i | .Section_small_data i =>
        variableSection ".data" (bss := some ".bss") (i := i)
      | .Section_const i | .Section_small_const i =>
        variableSection ".section      .rodata"
          (reloc := some ".section    .data.rel.ro,\"aw\",@progbits") (i := i)
      | .Section_string sz => elfMergeableStringSection sz ".section\t.rodata"
      | .Section_literal sz => elfMergeableLiteralSection sz ".section\t.rodata"
      | .Section_jumptable => ".section\t.rodata"
      | .Section_debug_info _ => ".section\t.debug_info,\"\",%progbits"
      | .Section_debug_loc => ".section\t.debug_loc,\"\",%progbits"
      | .Section_debug_abbrev => ".section\t.debug_abbrev,\"\",%progbits"
      | .Section_debug_line _ => ".section\t.debug_line,\"\",%progbits"
      | .Section_debug_ranges => ".section\t.debug_ranges,\"\",%progbits"
      | .Section_debug_str => ".section\t.debug_str,\"MS\",%progbits,1"
      | .Section_user s wr ex =>
        s!".section\t\"{s}\",\"a{if wr then "w" else ""}{if ex then "x" else ""}\",%progbits"
      | .Section_ais_annotation => ".section\t\"__compcert_ais_annotations\",\"\",@note"
    printFunInfo := elfPrintFunInfo
    printVarInfo := elfPrintVarInfo
    printCommDecl := fun name sz al => out s!"\t.comm\t{symbol name}, {sz}, {al}\n"
    printLcommDecl := fun name sz al => do
      out s!"\t.local\t{symbol name}\n"
      out s!"\t.comm\t{symbol name}, {sz}, {al}\n"
    system := "linux" }

/-- `TargetPrinter.MacOS_System` -/
def macosSystem : System :=
  let rawSymbol := fun s => "_" ++ s
  let symbol := fun id => rawSymbol (Camlcoq.externAtom id)
  let symbolOffsetGen := fun (kind : String) id (ofs : Integers.Ptrofs) =>
    let o := Integers.Int64.signed (Integers.Int64.repr (Integers.Ptrofs.unsigned ofs))
    s!"{symbol id}@{kind}" ++ (if o ≠ 0 then s!" + {o}" else "")
  let label := fun (lbl : Nat) => s!"L{lbl}"
  { comment := ";"
    rawSymbol
    symbol
    symbolOffsetHigh := symbolOffsetGen "PAGE"
    symbolOffsetLow := symbolOffsetGen "PAGEOFF"
    label
    labelHigh := fun lbl => label lbl ++ "@PAGE"
    labelLow := fun lbl => label lbl ++ "@PAGEOFF"
    loadSymbolAddress := fun rd id => do
      out s!"\tadrp\t{xregName rd}, {symbol id}@GOTPAGE\n"
      out s!"\tldr\t{xregName rd}, [{xregName rd}, {symbol id}@GOTPAGEOFF]\n"
    nameOfSection := fun
      | .Section_text => ".text"
      | .Section_data i | .Section_small_data i => variableSection ".data" (i := i)
      | .Section_const i | .Section_small_const i =>
        variableSection ".const" (reloc := some ".const_data") (i := i)
      | .Section_string sz => macosMergeableStringSection sz
      | .Section_literal sz => macosMergeableLiteralSection sz
      | .Section_jumptable => ".text"
      | .Section_user s wr ex =>
        s!".section\t\"{if wr then "__DATA" else "__TEXT"}\", {s}, {if ex then "regular, pure_instructions" else "regular"}"
      | .Section_debug_info _ => ".section\t__DWARF,__debug_info,regular,debug"
      | .Section_debug_loc => ".section\t__DWARF,__debug_loc,regular,debug"
      | .Section_debug_line _ => ".section\t__DWARF,__debug_line,regular,debug"
      | .Section_debug_str => ".section\t__DWARF,__debug_str,regular,debug"
      | .Section_debug_ranges => ".section\t__DWARF,__debug_ranges,regular,debug"
      | .Section_debug_abbrev => ".section\t__DWARF,__debug_abbrev,regular,debug"
      | .Section_ais_annotation => ".text"
    printFunInfo := fun _ => pure ()
    printVarInfo := fun _ => pure ()
    printCommDecl := fun name sz al => out s!"\t.comm\t{symbol name}, {sz}, {Nat.log2 al}\n"
    printLcommDecl := fun name sz al => out s!"\t.lcomm\t{symbol name}, {sz}, {Nat.log2 al}\n"
    system := "macos" }

/-! ## The target printer (`Target(System)`) -/

section Target

variable (S : System)

/-- `Target.print_label` -/
def printLabel (lbl : Positive) : M String := return S.label (← translLabel lbl)

/-- `Target.section` -/
def printSection (sec : SectionName) : M Unit := out s!"\t{S.nameOfSection sec}\n"

/-- `Target.condition_name` -/
def conditionName : Testcond → String
  | .TCeq => "eq" | .TCne => "ne" | .TChs => "hs" | .TClo => "lo"
  | .TCmi => "mi" | .TCpl => "pl" | .TChi => "hi" | .TCls => "ls"
  | .TCge => "ge" | .TClt => "lt" | .TCgt => "gt" | .TCle => "le"

/-- `Target.addressing` -/
def addressing : Addressing → String
  | .ADimm base n => s!"[{xregspName base}, #{coqint64 n}]"
  | .ADreg base r => s!"[{xregspName base}, {xregName r}]"
  | .ADlsl base r n => s!"[{xregspName base}, {xregName r}, lsl #{coqint n}]"
  | .ADsxt base r n => s!"[{xregspName base}, {wregName r}, sxtw #{coqint n}]"
  | .ADuxt base r n => s!"[{xregspName base}, {wregName r}, uxtw #{coqint n}]"
  | .ADadr base id ofs => s!"[{xregspName base}, {S.symbolOffsetLow id ofs}]"
  | .ADpostincr base n => s!"[{xregspName base}], #{coqint64 n}"
  | .ADpreincr base n => s!"[{xregspName base}, #{coqint64 n}]!"

/-- `Target.shiftop` -/
def shiftop : ShiftOp → String
  | .SOnone => ""
  | .SOlsl n => s!", lsl #{coqint n}"
  | .SOlsr n => s!", lsr #{coqint n}"
  | .SOasr n => s!", asr #{coqint n}"
  | .SOror n => s!", ror #{coqint n}"

/-- `Target.regextend` -/
def regextend (r : Ireg) : ExtendOp → String
  | .EOsxtb n => s!"{wregName r}, sxtb #{coqint n}"
  | .EOsxth n => s!"{wregName r}, sxth #{coqint n}"
  | .EOsxtw n => s!"{wregName r}, sxtw #{coqint n}"
  | .EOuxtb n => s!"{wregName r}, uxtb #{coqint n}"
  | .EOuxth n => s!"{wregName r}, uxth #{coqint n}"
  | .EOuxtw n => s!"{wregName r}, uxtw #{coqint n}"
  | .EOuxtx n => s!"{xregName r}, uxtx #{coqint n}"

/-- `Target.print_instruction` -/
def printInstruction (cfi : Bool) (i : Instruction) : M Unit :=
  let p := fun s => out s
  let ad := addressing S
  let x := xregName
  let w := wregName
  match i with
  -- Branches
  | .Pb lbl => do p s!"\tb\t{← printLabel S lbl}\n"
  | .Pbc c lbl => do p s!"\tb.{conditionName c}\t{← printLabel S lbl}\n"
  | .Pbl id _ => p s!"\tbl\t{S.symbol id}\n"
  | .Pbs id _ => p s!"\tb\t{S.symbol id}\n"
  | .Pblr r _ => p s!"\tblr\t{x r}\n"
  | .Pbr r _ => p s!"\tbr\t{x r}\n"
  | .Pret r => p s!"\tret\t{x r}\n"
  | .Pcbnz sz r lbl => do p s!"\tcbnz\t{ireg sz r}, {← printLabel S lbl}\n"
  | .Pcbz sz r lbl => do p s!"\tcbz\t{ireg sz r}, {← printLabel S lbl}\n"
  | .Ptbnz sz r n lbl => do p s!"\ttbnz\t{ireg sz r}, #{coqint n}, {← printLabel S lbl}\n"
  | .Ptbz sz r n lbl => do p s!"\ttbz\t{ireg sz r}, #{coqint n}, {← printLabel S lbl}\n"
  -- Memory loads and stores
  | .Pldrw rd a | .Pldrw_a rd a => p s!"\tldr\t{w rd}, {ad a}\n"
  | .Pldrx rd a | .Pldrx_a rd a => p s!"\tldr\t{x rd}, {ad a}\n"
  | .Pldrb _ rd a => p s!"\tldrb\t{w rd}, {ad a}\n"
  | .Pldrsb sz rd a => p s!"\tldrsb\t{ireg sz rd}, {ad a}\n"
  | .Pldrh _ rd a => p s!"\tldrh\t{w rd}, {ad a}\n"
  | .Pldrsh sz rd a => p s!"\tldrsh\t{ireg sz rd}, {ad a}\n"
  | .Pldrzw rd a => p s!"\tldr\t{w rd}, {ad a}\n"
  | .Pldrsw rd a => p s!"\tldrsw\t{x rd}, {ad a}\n"
  | .Pldp rd1 rd2 a => p s!"\tldp\t{x rd1}, {x rd2}, {ad a}\n"
  | .Pstrw rs a | .Pstrw_a rs a => p s!"\tstr\t{w rs}, {ad a}\n"
  | .Pstrx rs a | .Pstrx_a rs a => p s!"\tstr\t{x rs}, {ad a}\n"
  | .Pstrb rs a => p s!"\tstrb\t{w rs}, {ad a}\n"
  | .Pstrh rs a => p s!"\tstrh\t{w rs}, {ad a}\n"
  | .Pstp rs1 rs2 a => p s!"\tstp\t{x rs1}, {x rs2}, {ad a}\n"
  -- Integer arithmetic, immediate
  | .Paddimm sz rd r1 n => p s!"\tadd\t{iregsp sz rd}, {iregsp sz r1}, #{intsz sz n}\n"
  | .Psubimm sz rd r1 n => p s!"\tsub\t{iregsp sz rd}, {iregsp sz r1}, #{intsz sz n}\n"
  | .Pcmpimm sz r1 n => p s!"\tcmp\t{ireg sz r1}, #{intsz sz n}\n"
  | .Pcmnimm sz r1 n => p s!"\tcmn\t{ireg sz r1}, #{intsz sz n}\n"
  -- Move integer register
  | .Pmov rd r1 => p s!"\tmov\t{xregspName rd}, {xregspName r1}\n"
  -- Logical, immediate
  | .Pandimm sz rd r1 n => p s!"\tand\t{ireg sz rd}, {ireg0 sz r1}, #{intsz sz n}\n"
  | .Peorimm sz rd r1 n => p s!"\teor\t{ireg sz rd}, {ireg0 sz r1}, #{intsz sz n}\n"
  | .Porrimm sz rd r1 n => p s!"\torr\t{ireg sz rd}, {ireg0 sz r1}, #{intsz sz n}\n"
  | .Ptstimm sz r1 n => p s!"\ttst\t{ireg sz r1}, #{intsz sz n}\n"
  -- Move wide immediate
  | .Pmovz sz rd n pos => p s!"\tmovz\t{ireg sz rd}, #{n}, lsl #{pos}\n"
  | .Pmovn sz rd n pos => p s!"\tmovn\t{ireg sz rd}, #{n}, lsl #{pos}\n"
  | .Pmovk sz rd n pos => p s!"\tmovk\t{ireg sz rd}, #{n}, lsl #{pos}\n"
  -- PC-relative addressing
  | .Padrp rd id ofs => p s!"\tadrp\t{x rd}, {S.symbolOffsetHigh id ofs}\n"
  | .Paddadr rd r1 id ofs => p s!"\tadd\t{x rd}, {x r1}, {S.symbolOffsetLow id ofs}\n"
  -- Bit-field operations
  | .Psbfiz sz rd r1 r s => p s!"\tsbfiz\t{ireg sz rd}, {ireg sz r1}, {coqint r}, {s}\n"
  | .Psbfx sz rd r1 r s => p s!"\tsbfx\t{ireg sz rd}, {ireg sz r1}, {coqint r}, {s}\n"
  | .Pubfiz sz rd r1 r s => p s!"\tubfiz\t{ireg sz rd}, {ireg sz r1}, {coqint r}, {s}\n"
  | .Pubfx sz rd r1 r s => p s!"\tubfx\t{ireg sz rd}, {ireg sz r1}, {coqint r}, {s}\n"
  -- Integer arithmetic, shifted register
  | .Padd sz rd r1 r2 s => p s!"\tadd\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Psub sz rd r1 r2 s => p s!"\tsub\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Pcmp sz r1 r2 s => p s!"\tcmp\t{ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Pcmn sz r1 r2 s => p s!"\tcmn\t{ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  -- Integer arithmetic, extending register
  | .Paddext rd r1 r2 e => p s!"\tadd\t{xregspName rd}, {xregspName r1}, {regextend r2 e}\n"
  | .Psubext rd r1 r2 e => p s!"\tsub\t{xregspName rd}, {xregspName r1}, {regextend r2 e}\n"
  | .Pcmpext r1 r2 e => p s!"\tcmp\t{x r1}, {regextend r2 e}\n"
  | .Pcmnext r1 r2 e => p s!"\tcmn\t{x r1}, {regextend r2 e}\n"
  -- Logical, shifted register
  | .Pand sz rd r1 r2 s => p s!"\tand\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Pbic sz rd r1 r2 s => p s!"\tbic\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Peon sz rd r1 r2 s => p s!"\teon\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Peor sz rd r1 r2 s => p s!"\teor\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Porr sz rd r1 r2 s => p s!"\torr\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Porn sz rd r1 r2 s => p s!"\torn\t{ireg sz rd}, {ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  | .Ptst sz r1 r2 s => p s!"\ttst\t{ireg0 sz r1}, {ireg sz r2}{shiftop s}\n"
  -- Variable shifts
  | .Pasrv sz rd r1 r2 => p s!"\tasr\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}\n"
  | .Plslv sz rd r1 r2 => p s!"\tlsl\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}\n"
  | .Plsrv sz rd r1 r2 => p s!"\tlsr\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}\n"
  | .Prorv sz rd r1 r2 => p s!"\tror\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}\n"
  -- Bit operations
  | .Pcls sz rd r1 => p s!"\tcls\t{ireg sz rd}, {ireg sz r1}\n"
  | .Pclz sz rd r1 => p s!"\tclz\t{ireg sz rd}, {ireg sz r1}\n"
  | .Prev sz rd r1 => p s!"\trev\t{ireg sz rd}, {ireg sz r1}\n"
  | .Prev16 sz rd r1 => p s!"\trev16\t{ireg sz rd}, {ireg sz r1}\n"
  | .Prbit sz rd r1 => p s!"\trbit\t{ireg sz rd}, {ireg sz r1}\n"
  -- Conditional data processing
  | .Pcsel rd r1 r2 c => p s!"\tcsel\t{x rd}, {x r1}, {x r2}, {conditionName c}\n"
  | .Pcset rd c => p s!"\tcset\t{x rd}, {conditionName c}\n"
  -- Integer multiply/divide
  | .Pmadd sz rd r1 r2 r3 => p s!"\tmadd\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}, {ireg0 sz r3}\n"
  | .Pmsub sz rd r1 r2 r3 => p s!"\tmsub\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}, {ireg0 sz r3}\n"
  | .Psmulh rd r1 r2 => p s!"\tsmulh\t{x rd}, {x r1}, {x r2}\n"
  | .Pumulh rd r1 r2 => p s!"\tumulh\t{x rd}, {x r1}, {x r2}\n"
  | .Psdiv sz rd r1 r2 => p s!"\tsdiv\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}\n"
  | .Pudiv sz rd r1 r2 => p s!"\tudiv\t{ireg sz rd}, {ireg sz r1}, {ireg sz r2}\n"
  -- Floating-point loads and stores
  | .Pldrs rd a => p s!"\tldr\t{sregName rd}, {ad a}\n"
  | .Pldrd rd a | .Pldrd_a rd a => p s!"\tldr\t{dregName rd}, {ad a}\n"
  | .Pstrs rd a => p s!"\tstr\t{sregName rd}, {ad a}\n"
  | .Pstrd rd a | .Pstrd_a rd a => p s!"\tstr\t{dregName rd}, {ad a}\n"
  -- Floating-point move
  | .Pfmov rd r1 => p s!"\tfmov\t{dregName rd}, {dregName r1}\n"
  | .Pfmovimmd rd f => do
    let d := (Integers.Int64.unsigned (Floats.Float.toBits f)).toNat
    if isImmediateFloat64 d then p s!"\tfmov\t{dregName rd}, #{immFloat64String d}\n"
    else do
      let lbl ← labelLiteral64 d
      p s!"\tadrp\tx16, {S.labelHigh lbl}\n"
      p s!"\tldr\t{dregName rd}, [x16, {S.labelLow lbl}] {S.comment} {floatString f}\n"
  | .Pfmovimms rd f => do
    let d := (Integers.Int.unsigned (Floats.Float32.toBits f)).toNat
    if isImmediateFloat32 d then p s!"\tfmov\t{sregName rd}, #{immFloat32String d}\n"
    else do
      let lbl ← labelLiteral32 d
      p s!"\tadrp\tx16, {S.labelHigh lbl}\n"
      p s!"\tldr\t{sregName rd}, [x16, {S.labelLow lbl}] {S.comment} {float32String f}\n"
  | .Pfmovi .D rd r1 => p s!"\tfmov\t{dregName rd}, {xreg0Name r1}\n"
  | .Pfmovi .S rd r1 => p s!"\tfmov\t{sregName rd}, {wreg0Name r1}\n"
  -- Floating-point conversions
  | .Pfcvtds rd r1 => p s!"\tfcvt\t{dregName rd}, {sregName r1}\n"
  | .Pfcvtsd rd r1 => p s!"\tfcvt\t{sregName rd}, {dregName r1}\n"
  | .Pfcvtzs isz fsz rd r1 => p s!"\tfcvtzs  {ireg isz rd}, {freg fsz r1}\n"
  | .Pfcvtzu isz fsz rd r1 => p s!"\tfcvtzu  {ireg isz rd}, {freg fsz r1}\n"
  | .Pscvtf fsz isz rd r1 => p s!"\tscvtf\t{freg fsz rd}, {ireg isz r1}\n"
  | .Pucvtf fsz isz rd r1 => p s!"\tucvtf\t{freg fsz rd}, {ireg isz r1}\n"
  -- Floating-point arithmetic
  | .Pfabs sz rd r1 => p s!"\tfabs\t{freg sz rd}, {freg sz r1}\n"
  | .Pfneg sz rd r1 => p s!"\tfneg\t{freg sz rd}, {freg sz r1}\n"
  | .Pfsqrt sz rd r1 => p s!"\tfsqrt\t{freg sz rd}, {freg sz r1}\n"
  | .Pfadd sz rd r1 r2 => p s!"\tfadd\t{freg sz rd}, {freg sz r1}, {freg sz r2}\n"
  | .Pfdiv sz rd r1 r2 => p s!"\tfdiv\t{freg sz rd}, {freg sz r1}, {freg sz r2}\n"
  | .Pfmul sz rd r1 r2 => p s!"\tfmul\t{freg sz rd}, {freg sz r1}, {freg sz r2}\n"
  | .Pfnmul sz rd r1 r2 => p s!"\tfnmul\t{freg sz rd}, {freg sz r1}, {freg sz r2}\n"
  | .Pfsub sz rd r1 r2 => p s!"\tfsub\t{freg sz rd}, {freg sz r1}, {freg sz r2}\n"
  | .Pfmadd sz rd r1 r2 r3 =>
    p s!"\tfmadd\t{freg sz rd}, {freg sz r1}, {freg sz r2}, {freg sz r3}\n"
  | .Pfmsub sz rd r1 r2 r3 =>
    p s!"\tfmsub\t{freg sz rd}, {freg sz r1}, {freg sz r2}, {freg sz r3}\n"
  | .Pfnmadd sz rd r1 r2 r3 =>
    p s!"\tfnmadd\t{freg sz rd}, {freg sz r1}, {freg sz r2}, {freg sz r3}\n"
  | .Pfnmsub sz rd r1 r2 r3 =>
    p s!"\tfnmsub\t{freg sz rd}, {freg sz r1}, {freg sz r2}, {freg sz r3}\n"
  | .Pfmax sz rd r1 r2 => p s!"\tfmax\t{freg sz rd}, {freg sz r1}, {freg sz r2}\n"
  | .Pfmin sz rd r1 r2 => p s!"\tfmin\t{freg sz rd}, {freg sz r1}, {freg sz r2}\n"
  -- Floating-point comparison
  | .Pfcmp sz r1 r2 => p s!"\tfcmp\t{freg sz r1}, {freg sz r2}\n"
  | .Pfcmp0 sz r1 => p s!"\tfcmp\t{freg sz r1}, #0.0\n"
  -- Floating-point conditional select
  | .Pfsel rd r1 r2 c =>
    p s!"\tfcsel\t{dregName rd}, {dregName r1}, {dregName r2}, {conditionName c}\n"
  -- No-op
  | .Pnop => p "\tnop\n"
  -- Pseudo-instructions expanded in Asmexpand
  | .Pallocframe _ _ _ | .Pfreeframe _ _ | .Pcvtx2w _ =>
    fail "Pallocframe/Pfreeframe/Pcvtx2w must be expanded by Asmexpand"
  -- Pseudo-instructions not yet expanded
  | .Plabel lbl => do p s!"{← printLabel S lbl}:\n"
  | .Ploadsymbol rd id => S.loadSymbolAddress rd id
  | .Pcvtsw2x rd r1 => p s!"\tsxtw\t{x rd}, {w r1}\n"
  | .Pcvtuw2x rd r1 => p s!"\tuxtw\t{x rd}, {w r1}\n"
  | .Pbtbl r1 tbl => do
    let lbl ← newLabel
    p s!"\tadr\tx16, {S.label lbl}\n"
    p s!"\tadd\tx16, x16, {w r1}, uxtw #2\n"
    p "\tbr\tx16\n"
    p s!"{S.label lbl}:"
    for l in tbl do p s!"\tb\t{← printLabel S l}\n"
  | .Pcfi_adjust sz => cfiAdjust cfi (Integers.Int.signed sz)
  | .Pcfi_rel_offset ofs => cfiRelOffset cfi "x30" (Integers.Int.signed ofs)
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_annot kind txt _ =>
      match kind.toNat with
      | 1 => p s!"{S.comment} annotation: {quoteString (annotText pregAnnot "sp" txt args)}\n"
      | 2 => do
        let lbl ← newLabel
        p s!"{S.label lbl}:\n"
        addAisAnnot lbl pregAnnot "sp" txt args
      | _ => fail "print_instruction: bad annotation kind"
    | .EF_debug kind txt _ =>
      printDebugInfo S.comment pregAnnot "sp" kind.toNat (Camlcoq.externAtom txt) args
    | .EF_inline_asm txt sg _ => do
      p s!"{S.comment} begin inline assembly\n\t"
      printInlineAsm pregAsm txt sg args res
      p s!"{S.comment} end inline assembly\n"
    | _ => fail "print_instruction: builtin not expanded"

/-- `Target.print_align` -/
def printAlign (alignment : Nat) : M Unit := out s!"\t.balign {alignment}\n"

/-- `Target.print_jumptable` -/
def printJumptable : M Unit := do
  let jts := (← get).jumptables
  if !jts.isEmpty then
    printSection S .Section_jumptable
    out "\t.balign 4\n"
    for (lbl, tbl) in jts do
      out s!"{S.label lbl}:\n"
      for l in tbl do out s!"\t.long\t{← printLabel S l} - {S.label lbl}\n"
    modify fun st => { st with jumptables := [] }

/-- `TargetPrinter.Target(System)`.  `isStatic` is `C2C.atom_is_static` and
    `cfi` is `Configuration.asm_supports_cfi`. -/
def target (isStatic : Ident → Bool) (cfi : Bool := true) : PrintAsm.Target Asm.Function where
  printPrologue := pure ()
  printEpilogue := pure ()
  printAlign := printAlign
  printCommSymb sz name align :=
    if isStatic name then S.printLcommDecl name sz align else S.printCommDecl name sz align
  printVarInfo := S.printVarInfo
  printFunInfo := S.printFunInfo
  printOptionalFunInfo := pure ()
  printInstructions fn := do
    modify fun st => { st with currentFunctionSig := fn.fn_sig }
    for i in fn.fn_code do printInstruction S cfi i
  printJumptable _ := printJumptable S
  printSection := printSection S
  nameOfSection := S.nameOfSection
  comment := S.comment
  symbol := S.symbol
  defaultFalignment := 4
  label := S.label
  address := ".quad"
  bigEndian := false
  cfi := cfi
  system := S.system

end Target

/-- `TargetPrinter.sel_target`: the system printer for
    `Configuration.system` (`"linux"` or `"macos"`). -/
def selSystem (system : String) : Except String System :=
  match system with
  | "linux" => .ok elfSystem
  | "macos" => .ok macosSystem
  | _ => .error s!"System {system} not supported"

end TargetPrinter
end CC
