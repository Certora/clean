/-
  Printing ARM assembly code — port of `arm/TargetPrinter.ml`.

  The OCaml functor `Target(Opt : PRINTER_OPTIONS)` producing the
  `PrintAsmaux.TARGET` used by `PrintAsm` becomes the function `target`,
  which builds a `PrintAsm.Target Asm.Function` from an explicit
  `TargetPrinter.Options` record.  This record gathers what the OCaml code
  reads from global configuration: `Opt.vfpv3`, `Clflags.option_mthumb`,
  `Archi.hardware_idiv`, `Configuration.model`, `Configuration.abi`,
  `C2C.atom_is_static` and `Configuration.asm_supports_cfi`.

  The code printed is the code produced by `arm/Asmexpand.lean` (in
  particular `Constantexpand` must have eliminated `Pflid`, `Pflis` and
  `Ploadsymbol`; printing them is an error, as in OCaml).

  Differences from OCaml:
  * `%.15F` of an immediate float (`Pflid_imm`, `Pflis_imm`) is computed
    exactly (these floats are multiples of 1/128); the `%.12g` comments of
    `Pflid_lbl`/`Pflis_lbl` use Lean's float printing, as the other ported
    printers do for comments.
  * Not ported: `-g` (`print_file_line`, the `.file` directives of
    `print_epilogue`, `cfi_section` in `print_prologue`).
-/
import CCLib.arm.Asm
import CCLib.backend.PrintAsm

namespace CC
namespace Arm
namespace TargetPrinter

open Asm Sections PrintAsmaux

/-! ## Registers and conditions -/

/-- `TargetPrinter.int_reg_name` -/
def intRegName : Ireg → String
  | .IR0 => "r0" | .IR1 => "r1" | .IR2 => "r2" | .IR3 => "r3"
  | .IR4 => "r4" | .IR5 => "r5" | .IR6 => "r6" | .IR7 => "r7"
  | .IR8 => "r8" | .IR9 => "r9" | .IR10 => "r10" | .IR11 => "r11"
  | .IR12 => "r12" | .IR13 => "sp" | .IR14 => "lr"

/-- `TargetPrinter.float_reg_name` -/
def floatRegName : Freg → String
  | .FR0 => "d0" | .FR1 => "d1" | .FR2 => "d2" | .FR3 => "d3"
  | .FR4 => "d4" | .FR5 => "d5" | .FR6 => "d6" | .FR7 => "d7"
  | .FR8 => "d8" | .FR9 => "d9" | .FR10 => "d10" | .FR11 => "d11"
  | .FR12 => "d12" | .FR13 => "d13" | .FR14 => "d14" | .FR15 => "d15"

/-- `TargetPrinter.single_float_reg_name`: the single-precision register
    overlapping the low half of a double register. -/
def singleFloatRegName : Freg → String
  | .FR0 => "s0" | .FR1 => "s2" | .FR2 => "s4" | .FR3 => "s6"
  | .FR4 => "s8" | .FR5 => "s10" | .FR6 => "s12" | .FR7 => "s14"
  | .FR8 => "s16" | .FR9 => "s18" | .FR10 => "s20" | .FR11 => "s22"
  | .FR12 => "s24" | .FR13 => "s26" | .FR14 => "s28" | .FR15 => "s30"

/-- `TargetPrinter.single_param_reg_name` -/
def singleParamRegName : Sreg → String
  | .SR0 => "s0" | .SR1 => "s1" | .SR2 => "s2" | .SR3 => "s3"
  | .SR4 => "s4" | .SR5 => "s5" | .SR6 => "s6" | .SR7 => "s7"
  | .SR8 => "s8" | .SR9 => "s9" | .SR10 => "s10" | .SR11 => "s11"
  | .SR12 => "s12" | .SR13 => "s13" | .SR14 => "s14" | .SR15 => "s15"
  | .SR16 => "s16" | .SR17 => "s17" | .SR18 => "s18" | .SR19 => "s19"
  | .SR20 => "s20" | .SR21 => "s21" | .SR22 => "s22" | .SR23 => "s23"
  | .SR24 => "s24" | .SR25 => "s25" | .SR26 => "s26" | .SR27 => "s27"
  | .SR28 => "s28" | .SR29 => "s29" | .SR30 => "s30" | .SR31 => "s31"

/-- `TargetPrinter.preg_annot` -/
def pregAnnot : Preg → String
  | .IR r => intRegName r
  | .FR r => floatRegName r
  | _ => "<bad register>"

/-- `TargetPrinter.condition_name` -/
def conditionName : Testcond → String
  | .TCeq => "eq" | .TCne => "ne" | .TChs => "hs" | .TClo => "lo"
  | .TCmi => "mi" | .TCpl => "pl" | .TChi => "hi" | .TCls => "ls"
  | .TCge => "ge" | .TClt => "lt" | .TCgt => "gt" | .TCle => "le"

/-- `TargetPrinter.neg_condition_name` -/
def negConditionName : Testcond → String
  | .TCeq => "ne" | .TCne => "eq" | .TChs => "lo" | .TClo => "hs"
  | .TCmi => "pl" | .TCpl => "mi" | .TChi => "ls" | .TCls => "hi"
  | .TCge => "lt" | .TClt => "ge" | .TCgt => "le" | .TCle => "gt"

/-! ## Numbers -/

/-- `%lx`/`%Lx`: lower-case hexadecimal. -/
def hexLower (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- `%.15F` of a float that `vmov` can encode as an immediate: `sign`,
    unbiased exponent `exp` (`-3 ≤ exp ≤ 4`) and 4-bit fraction `m`.  OCaml's
    `%F` is `%g` followed by a `.` if the result has none; the value is a
    multiple of 1/128 below 32, so `%.15g` is its exact decimal expansion
    without trailing zeros. -/
def immFloatString (sign : Bool) (exp : Int) (m : Nat) : String :=
  -- |value| * 10^15 = (16 + m) * 2^(exp+3) * 10^15 / 128
  let k := (16 + m) * 2 ^ (exp + 3).toNat * 7812500000000
  let ip := k / 10 ^ 15
  let fp := k % 10 ^ 15
  let fs := toString fp
  let fs := String.ofList (List.replicate (15 - fs.length) '0') ++ fs
  let fs := String.ofList (fs.toList.reverse.dropWhile (· == '0')).reverse
  (if sign then "-" else "") ++ s!"{ip}." ++ fs

/-- `%.15F` of the double with bits `bits` (assumed immediate). -/
def immFloat64String (bits : Nat) : String :=
  immFloatString (bits / 2 ^ 63 = 1) ((bits / 2 ^ 52 % 2 ^ 11 : Nat) - 1023) (bits / 2 ^ 48 % 16)

/-- `%.15F` of the single with bits `bits` (assumed immediate). -/
def immFloat32String (bits : Nat) : String :=
  immFloatString (bits / 2 ^ 31 = 1) ((bits / 2 ^ 23 % 2 ^ 8 : Nat) - 127) (bits / 2 ^ 19 % 16)

#guard immFloat64String 0x3FF0000000000000 = "1."
#guard immFloat64String 0xC002000000000000 = "-2.25"
#guard immFloat64String 0x3FC0000000000000 = "0.125"
#guard immFloat32String 0x3E000000 = "0.125"

/-! ## The target printer (`Target(Opt)`) -/

/-- What `TargetPrinter.ml` reads from the global configuration. -/
structure Options where
  /-- `Opt.vfpv3` (`Configuration.model >= "armv7"`) -/
  vfpv3 : Bool := true
  /-- `Clflags.option_mthumb` -/
  thumb : Bool := false
  /-- `Archi.hardware_idiv ()` -/
  hardwareIdiv : Bool := true
  /-- `Configuration.model` -/
  model : String := "armv7a"
  /-- `Configuration.abi = "hardfloat"` -/
  hardfloat : Bool := true
  /-- `C2C.atom_is_static` -/
  isStatic : Ident → Bool := fun _ => false
  /-- `Configuration.asm_supports_cfi` -/
  cfi : Bool := true

section Target

variable (o : Options)

/-- `Target.label` -/
def label : Nat → String := elfLabel

/-- `Target.print_label` -/
def printLabel (lbl : Positive) : M String := return elfLabel (← translLabel lbl)

/-- `Target.comment` -/
def comment : String := "@"

/-- `Target.symbol` -/
def symbol : Ident → String := elfSymbol

/-- `Target.symbol_paren`: symbols starting with `$` are parenthesized. -/
def symbolParen (symb : Ident) : String :=
  let s := Camlcoq.externAtom symb
  if s.startsWith "$" then s!"({s})" else s

/-- `Target.symbol_offset` -/
def symbolOffset (symb : Ident) (ofs : Integers.Ptrofs) : String :=
  let o := Integers.Int64.signed (Integers.Int64.repr (Integers.Ptrofs.unsigned ofs))
  if o = 0 then symbolParen symb else s!"({symbol symb} + {o})"

/-- `Target.preg_asm` -/
def pregAsm (ty : ATyp) : Preg → M Unit
  | .IR r => out (intRegName r)
  | .FR r => out (if ty = .Tsingle then singleFloatRegName r else floatRegName r)
  | _ => fail "preg_asm"

/-- `Target.thumbS`: in Thumb2 mode, some arithmetic instructions have a
    shorter encoding with the `S` flag. -/
def thumbS : String := if o.thumb then "s" else ""

/-- `Target.name_of_section` -/
def nameOfSection : SectionName → String
  | .Section_text => ".text"
  | .Section_data i | .Section_small_data i => variableSection ".data" (bss := some ".bss") (i := i)
  | .Section_const i | .Section_small_const i =>
    variableSection ".section      .rodata"
      (reloc := some ".section    .data.rel.ro,\"aw\",%progbits") (i := i)
  | .Section_string _ => ".section\t.rodata"
  | .Section_literal _ => ".text"
  | .Section_jumptable => ".text"
  | .Section_user s wr ex =>
    s!".section\t\"{s}\",\"a{if wr then "w" else ""}{if ex then "x" else ""}\",%progbits"
  | .Section_debug_info _ => ".section\t.debug_info,\"\",%progbits"
  | .Section_debug_loc => ".section\t.debug_loc,\"\",%progbits"
  | .Section_debug_abbrev => ".section\t.debug_abbrev,\"\",%progbits"
  | .Section_debug_line _ => ".section\t.debug_line,\"\",%progbits"
  | .Section_debug_ranges => ".section\t.debug_ranges,\"\",%progbits"
  | .Section_debug_str => ".section\t.debug_str,\"MS\",%progbits,1"
  | .Section_ais_annotation => ".section\t\"__compcert_ais_annotations\",\"\",%note"

/-- `Target.section` -/
def printSection (sec : SectionName) : M Unit := out s!"\t{nameOfSection sec}\n"

/-- `Target.print_literal64` (`Archi.big_endian` is false: the ARM port is
    little-endian, as `PrintAsm.Target.bigEndian` below). -/
def printLiteral64 (n : Nat) (lbl : Nat) : M Unit :=
  let bfhi := n / 2 ^ 32 % 2 ^ 32
  let bflo := n % 2 ^ 32
  out s!".L{lbl}:\t.word\t0x{hexLower bflo}, 0x{hexLower bfhi}\n"

/-- `Target.print_constants` -/
def printConstants : CodeConstant → M Unit
  | .Float32 lbl c => do
    let c := (Integers.Int.unsigned (Floats.Float32.toBits c)).toNat
    out s!"{← printLabel lbl}:\t.word\t0x{hexLower c}\n"
  | .Float64 lbl bf => do
    let bf := (Integers.Int64.unsigned (Floats.Float.toBits bf)).toNat
    printLiteral64 bf (← translLabel lbl)
  | .Symbol lbl id ofs => do
    out s!"{← printLabel lbl}:\t.word\t{symbolOffset id ofs}\n"

/-- `Target.shift_op` -/
def shiftOp : ShiftOp → String
  | .SOimm n => s!"#{coqint n}"
  | .SOreg r => intRegName r
  | .SOlsl r n => s!"{intRegName r}, lsl #{coqint n}"
  | .SOlsr r n => s!"{intRegName r}, lsr #{coqint n}"
  | .SOasr r n => s!"{intRegName r}, asr #{coqint n}"
  | .SOror r n => s!"{intRegName r}, ror #{coqint n}"

/-- `Target.print_instruction` -/
def printInstruction (i : Instruction) : M Unit :=
  let p := fun s => out s
  let ir := intRegName
  let fr := floatRegName
  let fs := singleFloatRegName
  let so := shiftOp
  let tS := thumbS o
  let vmrs := "\tvmrs APSR_nzcv, FPSCR\n"
  match i with
  -- Core instructions
  | .Padc r1 r2 s => p s!"\tadc\t{ir r1}, {ir r2}, {so s}\n"
  | .Padd r1 r2 s =>
    p s!"\tadd{if o.thumb && r2 ≠ .IR13 then "s" else ""}\t{ir r1}, {ir r2}, {so s}\n"
  | .Padds r1 r2 s => p s!"\tadds\t{ir r1}, {ir r2}, {so s}\n"
  | .Pand r1 r2 s => p s!"\tand{tS}\t{ir r1}, {ir r2}, {so s}\n"
  | .Pasr r1 r2 r3 => p s!"\tasr{tS}\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pb lbl => do p s!"\tb\t{← printLabel lbl}\n"
  | .Pbc bit lbl => do p s!"\tb{conditionName bit}\t{← printLabel lbl}\n"
  | .Pbne lbl => do p s!"\tbne\t{← printLabel lbl}\n"
  | .Pbsymb id _ => p s!"\tb\t{symbolParen id}\n"
  | .Pbreg r _ => p s!"\tbx\t{ir r}\n"
  | .Pblsymb id _ => p s!"\tbl\t{symbolParen id}\n"
  | .Pblreg r _ => p s!"\tblx\t{ir r}\n"
  | .Pbic r1 r2 s => p s!"\tbic{tS}\t{ir r1}, {ir r2}, {so s}\n"
  | .Pclz r1 r2 => p s!"\tclz\t{ir r1}, {ir r2}\n"
  | .Pcmp r1 s => p s!"\tcmp\t{ir r1}, {so s}\n"
  | .Pcmn r1 s => p s!"\tcmn\t{ir r1}, {so s}\n"
  | .Pdmb => p "\tdmb\n"
  | .Pdsb => p "\tdsb\n"
  | .Peor r1 r2 s => p s!"\teor{tS}\t{ir r1}, {ir r2}, {so s}\n"
  | .Pisb => p "\tisb\n"
  | .Pldr r1 r2 sa | .Pldr_a r1 r2 sa => p s!"\tldr\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Pldrb r1 r2 sa => p s!"\tldrb\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Pldrh r1 r2 sa => p s!"\tldrh\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Pldr_p r1 r2 sa => p s!"\tldr\t{ir r1}, [{ir r2}], {so sa}\n"
  | .Pldrb_p r1 r2 sa => p s!"\tldrb\t{ir r1}, [{ir r2}], {so sa}\n"
  | .Pldrh_p r1 r2 sa => p s!"\tldrh\t{ir r1}, [{ir r2}], {so sa}\n"
  | .Pldrsb r1 r2 sa => p s!"\tldrsb\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Pldrsh r1 r2 sa => p s!"\tldrsh\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Plsl r1 r2 r3 => p s!"\tlsl{tS}\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Plsr r1 r2 r3 => p s!"\tlsr{tS}\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmla r1 r2 r3 r4 => p s!"\tmla\t{ir r1}, {ir r2}, {ir r3}, {ir r4}\n"
  | .Pmov r1 (.SOreg reg) =>
    -- No S flag even in Thumb2 mode
    p s!"\tmov\t{ir r1}, {ir reg}\n"
  | .Pmov r1 s => p s!"\tmov{tS}\t{ir r1}, {so s}\n"
  | .Pmovw r1 n => p s!"\tmovw\t{ir r1}, #{coqint n}\n"
  | .Pmovt r1 n => p s!"\tmovt\t{ir r1}, #{coqint n}\n"
  | .Pmul r1 r2 r3 => p s!"\tmul\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmvn r1 s => p s!"\tmvn{tS}\t{ir r1}, {so s}\n"
  | .Porr r1 r2 s => p s!"\torr{tS}\t{ir r1}, {ir r2}, {so s}\n"
  | .Prev r1 r2 => p s!"\trev\t{ir r1}, {ir r2}\n"
  | .Prev16 r1 r2 => p s!"\trev16\t{ir r1}, {ir r2}\n"
  | .Prsb r1 r2 s => p s!"\trsb{tS}\t{ir r1}, {ir r2}, {so s}\n"
  | .Prsbs r1 r2 s => p s!"\trsbs\t{ir r1}, {ir r2}, {so s}\n"
  | .Prsc r1 r2 s => p s!"\trsc\t{ir r1}, {ir r2}, {so s}\n"
  | .Pfsqrt f1 f2 => p s!"\tvsqrt.f64 {fr f1}, {fr f2}\n"
  | .Psbc r1 r2 sa => p s!"\tsbc\t{ir r1}, {ir r2}, {so sa}\n"
  | .Pnop => p "\tnop\n"
  | .Pstr r1 r2 sa | .Pstr_a r1 r2 sa => p s!"\tstr\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Pstrb r1 r2 sa => p s!"\tstrb\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Pstrh r1 r2 sa => p s!"\tstrh\t{ir r1}, [{ir r2}, {so sa}]\n"
  | .Pstr_p r1 r2 sa => p s!"\tstr\t{ir r1}, [{ir r2}], {so sa}\n"
  | .Pstrb_p r1 r2 sa => p s!"\tstrb\t{ir r1}, [{ir r2}], {so sa}\n"
  | .Pstrh_p r1 r2 sa => p s!"\tstrh\t{ir r1}, [{ir r2}], {so sa}\n"
  | .Psdiv r r1 r2 =>
    if o.hardwareIdiv then p s!"\tsdiv\t{ir r}, {ir r1}, {ir r2}\n"
    else p "\tbl\t__aeabi_idiv\n"
  | .Psbfx r1 r2 lsb sz => p s!"\tsbfx\t{ir r1}, {ir r2}, #{coqint lsb}, #{coqint sz}\n"
  | .Psmull r1 r2 r3 r4 => p s!"\tsmull\t{ir r1}, {ir r2}, {ir r3}, {ir r4}\n"
  | .Psub r1 r2 s =>
    p s!"\tsub{if o.thumb && r2 ≠ .IR13 then "s" else ""}\t{ir r1}, {ir r2}, {so s}\n"
  | .Psubs r1 r2 s => p s!"\tsubs\t{ir r1}, {ir r2}, {so s}\n"
  | .Pudiv r r1 r2 =>
    if o.hardwareIdiv then p s!"\tudiv\t{ir r}, {ir r1}, {ir r2}\n"
    else p "\tbl\t__aeabi_uidiv\n"
  | .Pumull r1 r2 r3 r4 => p s!"\tumull\t{ir r1}, {ir r2}, {ir r3}, {ir r4}\n"
  -- Floating-point VFD instructions
  | .Pfcpyd r1 r2 => p s!"\tvmov.f64 {fr r1}, {fr r2}\n"
  | .Pfabsd r1 r2 => p s!"\tvabs.f64 {fr r1}, {fr r2}\n"
  | .Pfnegd r1 r2 => p s!"\tvneg.f64 {fr r1}, {fr r2}\n"
  | .Pfaddd r1 r2 r3 => p s!"\tvadd.f64 {fr r1}, {fr r2}, {fr r3}\n"
  | .Pfdivd r1 r2 r3 => p s!"\tvdiv.f64 {fr r1}, {fr r2}, {fr r3}\n"
  | .Pfmuld r1 r2 r3 => p s!"\tvmul.f64 {fr r1}, {fr r2}, {fr r3}\n"
  | .Pfsubd r1 r2 r3 => p s!"\tvsub.f64 {fr r1}, {fr r2}, {fr r3}\n"
  | .Pflid _ _ => fail "Pflid should be eliminated by Constantexpand"
  | .Pfcmpd r1 r2 => do p s!"\tvcmp.f64 {fr r1}, {fr r2}\n"; p vmrs
  | .Pfcmpzd r1 => do p s!"\tvcmp.f64 {fr r1}, #0\n"; p vmrs
  | .Pfsitod r1 r2 => do
    p s!"\tvmov\t{fs r1}, {ir r2}\n"; p s!"\tvcvt.f64.s32 {fr r1}, {fs r1}\n"
  | .Pfuitod r1 r2 => do
    p s!"\tvmov\t{fs r1}, {ir r2}\n"; p s!"\tvcvt.f64.u32 {fr r1}, {fs r1}\n"
  | .Pftosizd r1 r2 => do
    p s!"\tvcvt.s32.f64 {fs .FR6}, {fr r2}\n"; p s!"\tvmov\t{ir r1}, {fs .FR6}\n"
  | .Pftouizd r1 r2 => do
    p s!"\tvcvt.u32.f64 {fs .FR6}, {fr r2}\n"; p s!"\tvmov\t{ir r1}, {fs .FR6}\n"
  | .Pfabss r1 r2 => p s!"\tvabs.f32 {fs r1}, {fs r2}\n"
  | .Pfnegs r1 r2 => p s!"\tvneg.f32 {fs r1}, {fs r2}\n"
  | .Pfadds r1 r2 r3 => p s!"\tvadd.f32 {fs r1}, {fs r2}, {fs r3}\n"
  | .Pfdivs r1 r2 r3 => p s!"\tvdiv.f32 {fs r1}, {fs r2}, {fs r3}\n"
  | .Pfmuls r1 r2 r3 => p s!"\tvmul.f32 {fs r1}, {fs r2}, {fs r3}\n"
  | .Ppush rl => p s!"\tpush\t\{{", ".intercalate (rl.map ir)}}\n"
  | .Pfsubs r1 r2 r3 => p s!"\tvsub.f32 {fs r1}, {fs r2}, {fs r3}\n"
  | .Pflis _ _ => fail "Pflis should be eliminated by Constantexpand"
  | .Pfcmps r1 r2 => do p s!"\tvcmp.f32 {fs r1}, {fs r2}\n"; p vmrs
  | .Pfcmpzs r1 => do p s!"\tvcmp.f32 {fs r1}, #0\n"; p vmrs
  | .Pfsitos r1 r2 => do
    p s!"\tvmov\t{fs r1}, {ir r2}\n"; p s!"\tvcvt.f32.s32 {fs r1}, {fs r1}\n"
  | .Pfuitos r1 r2 => do
    p s!"\tvmov\t{fs r1}, {ir r2}\n"; p s!"\tvcvt.f32.u32 {fs r1}, {fs r1}\n"
  | .Pftosizs r1 r2 => do
    p s!"\tvcvt.s32.f32 {fs .FR6}, {fs r2}\n"; p s!"\tvmov\t{ir r1}, {fs .FR6}\n"
  | .Pftouizs r1 r2 => do
    p s!"\tvcvt.u32.f32 {fs .FR6}, {fs r2}\n"; p s!"\tvmov\t{ir r1}, {fs .FR6}\n"
  | .Pfcvtsd r1 r2 => p s!"\tvcvt.f32.f64 {fs r1}, {fr r2}\n"
  | .Pfcvtds r1 r2 => p s!"\tvcvt.f64.f32 {fr r1}, {fs r2}\n"
  | .Pfldd r1 r2 n | .Pfldd_a r1 r2 n => p s!"\tvldr\t{fr r1}, [{ir r2}, #{coqint n}]\n"
  | .Pflds r1 r2 n => p s!"\tvldr\t{fs r1}, [{ir r2}, #{coqint n}]\n"
  | .Pfstd r1 r2 n | .Pfstd_a r1 r2 n => p s!"\tvstr\t{fr r1}, [{ir r2}, #{coqint n}]\n"
  | .Pfsts r1 r2 n => p s!"\tvstr\t{fs r1}, [{ir r2}, #{coqint n}]\n"
  -- Pseudo-instructions
  | .Pallocframe _ _ | .Pfreeframe _ _ =>
    fail "Pallocframe/Pfreeframe must be expanded by Asmexpand"
  | .Plabel lbl => do p s!"{← printLabel lbl}:\n"
  | .Ploadsymbol _ _ _ => fail "Ploadsymbol should be eliminated by Constantexpand"
  | .Pmovite cond r1 ifso ifnot => do
    p s!"\tite\t{conditionName cond}\n"
    p s!"\tmov{conditionName cond}\t{ir r1}, {so ifso}\n"
    p s!"\tmov{negConditionName cond}\t{ir r1}, {so ifnot}\n"
  | .Pfmovite cond r1 ifso ifnot => do
    p s!"\tite\t{conditionName cond}\n"
    p s!"\tvmov{conditionName cond}.f64\t{fr r1}, {fr ifso}\n"
    p s!"\tvmov{negConditionName cond}.f64\t{fr r1}, {fr ifnot}\n"
  | .Pbtbl r tbl => do
    if o.thumb then
      p s!"\tlsl\tr14, {ir r}, #2\n"
      p "\tadd\tpc, r14\n"   -- 16-bit encoding
      p "\tnop\n"            -- 16-bit encoding
      for l in tbl do p s!"\tb.w\t{← printLabel l}\n"
    else
      p s!"\tadd\tpc, pc, {ir r}, lsl #2\n"
      p "\tnop\n"
      for l in tbl do p s!"\tb\t{← printLabel l}\n"
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_annot kind txt _ =>
      match kind.toNat with
      | 1 => p s!"{comment} annotation: {quoteString (annotText pregAnnot "sp" txt args)}\n"
      | 2 => do
        let lbl ← newLabel
        p s!"{label lbl}:\n"
        addAisAnnot lbl pregAnnot "r13" txt args
      | _ => fail "print_instruction: bad annotation kind"
    | .EF_debug kind txt _ =>
      printDebugInfo comment pregAnnot "sp" kind.toNat (Camlcoq.externAtom txt) args
    | .EF_inline_asm txt sg _ => do
      p s!"{comment} begin inline assembly\n\t"
      printInlineAsm pregAsm txt sg args res
      p s!"{comment} end inline assembly\n"
    | _ => fail "print_instruction: builtin not expanded"
  | .Pcfi_adjust sz => cfiAdjust o.cfi (Integers.Int.signed sz)
  | .Pcfi_rel_offset ofs => cfiRelOffset o.cfi "lr" (Integers.Int.signed ofs)
  -- Fixup instructions for calling conventions
  | .Pfcpy_fs r1 r2 => p s!"\tvmov.f32\t{fs r1}, {singleParamRegName r2}\n"
  | .Pfcpy_sf r1 r2 => p s!"\tvmov.f32\t{singleParamRegName r1}, {fs r2}\n"
  | .Pfcpy_fii r1 r2 r3 => p s!"\tvmov\t{fr r1}, {ir r2}, {ir r3}\n"
  | .Pfcpy_fi r1 r2 => p s!"\tvmov\t{fs r1}, {ir r2}\n"
  | .Pfcpy_iif r1 r2 r3 => p s!"\tvmov\t{ir r1}, {ir r2}, {fr r3}\n"
  | .Pfcpy_if r1 r2 => p s!"\tvmov\t{ir r1}, {fs r2}\n"
  -- Constants
  | .Pconstants consts => do
    p "\t.balign\t4\n"
    for c in consts do printConstants c
  | .Ploadsymbol_imm r1 id ofs => do
    p s!"\tmovw\t{ir r1}, #:lower16:{symbolOffset id ofs}\n"
    p s!"\tmovt\t{ir r1}, #:upper16:{symbolOffset id ofs}\n"
  | .Pflid_lbl r1 lbl f => do
    p s!"\tvldr\t{fr r1}, {← printLabel lbl} {comment} {floatString f}\n"
  | .Pflis_lbl r1 lbl f => do
    p s!"\tvldr\t{fs r1}, {← printLabel lbl} {comment} {float32String f}\n"
  | .Pflid_imm r1 f =>
    let d := (Integers.Int64.unsigned (Floats.Float.toBits f)).toNat
    p s!"\tvmov.f64 {fr r1}, #{immFloat64String d}\n"
  | .Pflis_imm r1 f =>
    let d := (Integers.Int.unsigned (Floats.Float32.toBits f)).toNat
    p s!"\tvmov.f32 {fs r1}, #{immFloat32String d}\n"
  | .Ploadsymbol_lbl r1 lbl id ofs => do
    p s!"\tldr\t{ir r1}, {← printLabel lbl} {comment} {symbolOffset id ofs}\n"

/-- `Target.print_align` -/
def printAlign (alignment : Nat) : M Unit := out s!"\t.balign {alignment}\n"

/-- `Target.print_optional_fun_info` -/
def printOptionalFunInfo : M Unit := if o.thumb then out "\t.thumb_func\n" else pure ()

/-- `Target.print_fun_info` -/
def printFunInfo (name : Ident) : M Unit := do
  out s!"\t.type\t{symbol name}, %function\n"
  out s!"\t.size\t{symbol name}, . - {symbol name}\n"

/-- `Target.print_var_info` -/
def printVarInfo (name : Ident) : M Unit := do
  out s!"\t.type\t{symbol name}, %object\n"
  out s!"\t.size\t{symbol name}, . - {symbol name}\n"

/-- `Target.print_comm_symb` -/
def printCommSymb (sz : Int) (name : Ident) (align : Nat) : M Unit := do
  if o.isStatic name then out s!"\t.local\t{symbol name}\n"
  out s!"\t.comm\t{symbol name}, {sz}, {align}\n"

/-- `Target.print_prologue` (without `-g`) -/
def printPrologue : M Unit := do
  out "\t.syntax\tunified\n"
  let arch := match o.model with
    | "armv6" => "armv6" | "armv6t2" => "armv6t2" | "armv7a" => "armv7-a"
    | "armv7r" => "armv7-r" | "armv7m" => "armv7-m" | _ => "armv7"
  out s!"\t.arch\t{arch}\n"
  out s!"\t.fpu\t{if o.vfpv3 then "vfpv3-d16" else "vfpv2"}\n"
  out s!"\t.eabi_attribute Tag_ABI_VFP_args, {if o.hardfloat then 1 else 0}\n"
  out s!"\t.{if o.thumb then "thumb" else "arm"}\n"

/-- `TargetPrinter.Target(Opt)` -/
def target : PrintAsm.Target Asm.Function where
  printPrologue := printPrologue o
  printEpilogue := pure ()
  printAlign := printAlign
  printCommSymb := printCommSymb o
  printVarInfo := printVarInfo
  printFunInfo := printFunInfo
  printOptionalFunInfo := printOptionalFunInfo o
  printInstructions fn := do
    modify fun st => { st with currentFunctionSig := fn.fn_sig }
    for i in fn.fn_code do printInstruction o i
  printJumptable _ := pure ()
  printSection := printSection
  nameOfSection := nameOfSection
  comment := comment
  symbol := symbol
  defaultFalignment := 4
  label := label
  address := ".4byte"
  bigEndian := false
  cfi := o.cfi
  system := "linux"
  ptr64 := false

end Target

/-- `TargetPrinter.sel_target`: `vfpv3` is `Configuration.model >= "armv7"`
    (string comparison, as in OCaml). -/
def selTarget (o : Options) : PrintAsm.Target Asm.Function :=
  target { o with vfpv3 := decide (o.model ≥ "armv7") }

end TargetPrinter
end Arm
end CC
