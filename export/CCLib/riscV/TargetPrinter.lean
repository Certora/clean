/-
  Printing RISC-V assembly code — port of `riscV/TargetPrinter.ml`.

  The OCaml module is a single `Target : TARGET` (ELF only).  Here `target`
  builds a `PrintAsm.Target Asm.Function`.  As the Lean port's RISC-V back
  end is RV64, the printer is the one for `Archi.ptr64 = true` (the
  `assert Archi.ptr64` checks always hold; the RV32-only `Pmulhw`/`Pmulhuw`
  are rejected).  `SelectOp.symbol_is_relocatable` (which decides between
  `la`/`lla` and adds `@plt` to call targets) and the `-fpic`/`-fpie` flag
  are arguments, collected in the structure `Options`.

  Not ported: `-g` (`print_file_line`, the `.file` directives of
  `print_epilogue`) and the assertion that an
  `Ofslow` offset follows the matching `Ploadsymbol_high` (`latest_auipc`).
-/
import CCLib.riscV.Asm
import CCLib.backend.PrintAsm

namespace CC
namespace RiscV
namespace TargetPrinter

open Asm Sections PrintAsmaux

/-- Settings read by the OCaml printer from `SelectOp` and `Clflags`. -/
structure Options where
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false
  /-- `Clflags.option_fpic || Clflags.option_fpie` -/
  pic : Bool := false
  /-- `Configuration.asm_supports_cfi` -/
  cfi : Bool := true

/-- `Target.comment` -/
def comment : String := "#"
/-- `Target.symbol` -/
def symbol : Ident → String := elfSymbol
/-- `Target.symbol_offset` -/
def symbolOffset : Ident → Integers.Ptrofs → String := elfSymbolOffset
/-- `Target.label` -/
def label : Nat → String := elfLabel

/-- `Target.int_reg_name` -/
def intRegName (r : Ireg) : String :=
  match r with
  | .X1 => "x1" | .X2 => "x2" | .X3 => "x3" | .X4 => "x4" | .X5 => "x5" | .X6 => "x6"
  | .X7 => "x7" | .X8 => "x8" | .X9 => "x9" | .X10 => "x10" | .X11 => "x11" | .X12 => "x12"
  | .X13 => "x13" | .X14 => "x14" | .X15 => "x15" | .X16 => "x16" | .X17 => "x17"
  | .X18 => "x18" | .X19 => "x19" | .X20 => "x20" | .X21 => "x21" | .X22 => "x22"
  | .X23 => "x23" | .X24 => "x24" | .X25 => "x25" | .X26 => "x26" | .X27 => "x27"
  | .X28 => "x28" | .X29 => "x29" | .X30 => "x30" | .X31 => "x31"

/-- `Target.float_reg_name` -/
def floatRegName (r : Freg) : String :=
  match r with
  | .F0 => "f0" | .F1 => "f1" | .F2 => "f2" | .F3 => "f3" | .F4 => "f4" | .F5 => "f5"
  | .F6 => "f6" | .F7 => "f7" | .F8 => "f8" | .F9 => "f9" | .F10 => "f10" | .F11 => "f11"
  | .F12 => "f12" | .F13 => "f13" | .F14 => "f14" | .F15 => "f15" | .F16 => "f16"
  | .F17 => "f17" | .F18 => "f18" | .F19 => "f19" | .F20 => "f20" | .F21 => "f21"
  | .F22 => "f22" | .F23 => "f23" | .F24 => "f24" | .F25 => "f25" | .F26 => "f26"
  | .F27 => "f27" | .F28 => "f28" | .F29 => "f29" | .F30 => "f30" | .F31 => "f31"

/-- `Target.ireg` -/
abbrev ireg := intRegName
/-- `Target.freg` -/
abbrev freg := floatRegName
/-- `Target.ireg0` -/
def ireg0 : Ireg0 → String | .X0 => "x0" | .X r => ireg r

/-- `Target.preg_asm` -/
def pregAsm (_ty : ATyp) : Preg → M Unit
  | .IR r => out (ireg r)
  | .FR r => out (freg r)
  | _ => fail "preg_asm"

/-- `Target.preg_annot` -/
def pregAnnot : Preg → String
  | .IR r => intRegName r
  | .FR r => floatRegName r
  | _ => "<bad register>"

/-- `Target.name_of_section` -/
def nameOfSection : SectionName → String
  | .Section_text => ".text"
  | .Section_data i | .Section_small_data i => variableSection ".data" (bss := some ".bss") (i := i)
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

/-- `Target.section` -/
def printSection (sec : SectionName) : M Unit := out s!"\t{nameOfSection sec}\n"

section Target

variable (S : Options)

/-- `Target.print_label` -/
def printLabel (lbl : Positive) : M String := return label (← translLabel lbl)

/-- `Target.loadsymbol`: load the address of `id + ofs` in `r`. -/
def loadsymbol (r : Ireg) (id : Ident) (ofs : Integers.Ptrofs) : M Unit :=
  if S.symbolIsRelocatable id then
    if ofs ≠ Integers.Ptrofs.zero then fail "loadsymbol: offset of a relocatable symbol"
    else out s!"\tla\t{ireg r}, {Camlcoq.externAtom id}\n"
  else out s!"\tlla\t{ireg r}, {symbolOffset id ofs}\n"

/-- `Target.offset` -/
def offset : Offset → String
  | .Ofsimm n => ptrofs n
  | .Ofslow _ _ => "%pcrel_lo(1b)"

/-- `Target.symbol_plt` -/
def symbolPlt (s : Ident) : String :=
  if S.symbolIsRelocatable s then symbol s ++ "@plt" else symbol s

/-- `Target.print_instruction` -/
def printInstruction (i : Instruction) : M Unit :=
  let p := fun s => out s
  match i with
  | .Pmv rd rs => p s!"\tmv\t{ireg rd}, {ireg rs}\n"
  | .Paddiw rd rs imm => p s!"\taddiw\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Psltiw rd rs imm => p s!"\tslti\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Psltiuw rd rs imm => p s!"\tsltiu\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Pandiw rd rs imm => p s!"\tandi\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Poriw rd rs imm => p s!"\tori\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Pxoriw rd rs imm => p s!"\txori\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Pslliw rd rs imm => p s!"\tslliw\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Psrliw rd rs imm => p s!"\tsrliw\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Psraiw rd rs imm => p s!"\tsraiw\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Pluiw rd imm => p s!"\tlui\t{ireg rd}, {coqint imm}\n"
  | .Paddw rd rs1 rs2 => p s!"\taddw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psubw rd rs1 rs2 => p s!"\tsubw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pmulw rd rs1 rs2 => p s!"\tmulw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pdivw rd rs1 rs2 => p s!"\tdivw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pdivuw rd rs1 rs2 => p s!"\tdivuw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Premw rd rs1 rs2 => p s!"\tremw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Premuw rd rs1 rs2 => p s!"\tremuw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psltw rd rs1 rs2 => p s!"\tslt\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psltuw rd rs1 rs2 => p s!"\tsltu\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pandw rd rs1 rs2 => p s!"\tand\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Porw rd rs1 rs2 => p s!"\tor\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pxorw rd rs1 rs2 => p s!"\txor\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psllw rd rs1 rs2 => p s!"\tsllw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psrlw rd rs1 rs2 => p s!"\tsrlw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psraw rd rs1 rs2 => p s!"\tsraw\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pmulhw _ _ _ | .Pmulhuw _ _ _ => fail "Pmulhw/Pmulhuw: 32-bit only"
  | .Paddil rd rs imm => p s!"\taddi\t{ireg rd}, {ireg0 rs}, {coqint64 imm}\n"
  | .Psltil rd rs imm => p s!"\tslti\t{ireg rd}, {ireg0 rs}, {coqint64 imm}\n"
  | .Psltiul rd rs imm => p s!"\tsltiu\t{ireg rd}, {ireg0 rs}, {coqint64 imm}\n"
  | .Pandil rd rs imm => p s!"\tandi\t{ireg rd}, {ireg0 rs}, {coqint64 imm}\n"
  | .Poril rd rs imm => p s!"\tori\t{ireg rd}, {ireg0 rs}, {coqint64 imm}\n"
  | .Pxoril rd rs imm => p s!"\txori\t{ireg rd}, {ireg0 rs}, {coqint64 imm}\n"
  | .Psllil rd rs imm => p s!"\tslli\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Psrlil rd rs imm => p s!"\tsrli\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Psrail rd rs imm => p s!"\tsrai\t{ireg rd}, {ireg0 rs}, {coqint imm}\n"
  | .Pluil rd imm => p s!"\tlui\t{ireg rd}, {coqint64 imm}\n"
  | .Paddl rd rs1 rs2 => p s!"\tadd\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psubl rd rs1 rs2 => p s!"\tsub\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pmull rd rs1 rs2 => p s!"\tmul\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pmulhl rd rs1 rs2 => p s!"\tmulh\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pmulhul rd rs1 rs2 => p s!"\tmulhu\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pdivl rd rs1 rs2 => p s!"\tdiv\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pdivul rd rs1 rs2 => p s!"\tdivu\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Preml rd rs1 rs2 => p s!"\trem\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Premul rd rs1 rs2 => p s!"\tremu\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psltl rd rs1 rs2 => p s!"\tslt\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psltul rd rs1 rs2 => p s!"\tsltu\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pandl rd rs1 rs2 => p s!"\tand\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Porl rd rs1 rs2 => p s!"\tor\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pxorl rd rs1 rs2 => p s!"\txor\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Pslll rd rs1 rs2 => p s!"\tsll\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psrll rd rs1 rs2 => p s!"\tsrl\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  | .Psral rd rs1 rs2 => p s!"\tsra\t{ireg rd}, {ireg0 rs1}, {ireg0 rs2}\n"
  -- Unconditional jumps.  Links are always to X1/RA.
  | .Pj_l l => do p s!"\tj\t{← printLabel l}\n"
  | .Pj_s s _ => p s!"\ttail\t{symbolPlt S s}\n"
  | .Pj_r r _ => p s!"\tjr\t{ireg r}\n"
  | .Pjal_s s _ => p s!"\tcall\t{symbolPlt S s}\n"
  | .Pjal_r r _ => p s!"\tjalr\t{ireg r}\n"
  -- Conditional branches
  | .Pbeqw rs1 rs2 l => do p s!"\tbeq\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbnew rs1 rs2 l => do p s!"\tbne\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbltw rs1 rs2 l => do p s!"\tblt\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbltuw rs1 rs2 l => do p s!"\tbltu\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbgew rs1 rs2 l => do p s!"\tbge\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbgeuw rs1 rs2 l => do p s!"\tbgeu\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbeql rs1 rs2 l => do p s!"\tbeq\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbnel rs1 rs2 l => do p s!"\tbne\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbltl rs1 rs2 l => do p s!"\tblt\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbltul rs1 rs2 l => do p s!"\tbltu\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbgel rs1 rs2 l => do p s!"\tbge\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  | .Pbgeul rs1 rs2 l => do p s!"\tbgeu\t{ireg0 rs1}, {ireg0 rs2}, {← printLabel l}\n"
  -- Loads and stores
  | .Plb rd ra ofs => p s!"\tlb\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Plbu rd ra ofs => p s!"\tlbu\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Plh rd ra ofs => p s!"\tlh\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Plhu rd ra ofs => p s!"\tlhu\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Plw rd ra ofs | .Plw_a rd ra ofs => p s!"\tlw\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Pld rd ra ofs | .Pld_a rd ra ofs => p s!"\tld\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Psb rd ra ofs => p s!"\tsb\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Psh rd ra ofs => p s!"\tsh\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Psw rd ra ofs | .Psw_a rd ra ofs => p s!"\tsw\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Psd rd ra ofs | .Psd_a rd ra ofs => p s!"\tsd\t{ireg rd}, {offset ofs}({ireg ra})\n"
  | .Pfence => p "\tfence\n"
  -- `fmv.d` preserves single-precision contents: used for both precisions
  | .Pfmv fd fs => p s!"\tfmv.d\t{freg fd}, {freg fs}\n"
  | .Pfmvxs rd fs => p s!"\tfmv.x.s\t{ireg rd}, {freg fs}\n"
  | .Pfmvsx fd rs => p s!"\tfmv.s.x\t{freg fd}, {ireg rs}\n"
  | .Pfmvxd rd fs => p s!"\tfmv.x.d\t{ireg rd}, {freg fs}\n"
  | .Pfmvdx fd rs => p s!"\tfmv.d.x\t{freg fd}, {ireg rs}\n"
  | .Pfls fd ra ofs => p s!"\tflw\t{freg fd}, {offset ofs}({ireg ra})\n"
  | .Pfss fs ra ofs => p s!"\tfsw\t{freg fs}, {offset ofs}({ireg ra})\n"
  | .Pfnegs fd fs => p s!"\tfneg.s\t{freg fd}, {freg fs}\n"
  | .Pfabss fd fs => p s!"\tfabs.s\t{freg fd}, {freg fs}\n"
  | .Pfadds fd fs1 fs2 => p s!"\tfadd.s\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfsubs fd fs1 fs2 => p s!"\tfsub.s\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfmuls fd fs1 fs2 => p s!"\tfmul.s\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfdivs fd fs1 fs2 => p s!"\tfdiv.s\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfmins fd fs1 fs2 => p s!"\tfmin.s\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfmaxs fd fs1 fs2 => p s!"\tfmax.s\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfeqs rd fs1 fs2 => p s!"\tfeq.s\t{ireg rd}, {freg fs1}, {freg fs2}\n"
  | .Pflts rd fs1 fs2 => p s!"\tflt.s\t{ireg rd}, {freg fs1}, {freg fs2}\n"
  | .Pfles rd fs1 fs2 => p s!"\tfle.s\t{ireg rd}, {freg fs1}, {freg fs2}\n"
  | .Pfsqrts fd fs => p s!"\tfsqrt.s {freg fd}, {freg fs}\n"
  | .Pfmadds fd fs1 fs2 fs3 => p s!"\tfmadd.s\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfmsubs fd fs1 fs2 fs3 => p s!"\tfmsub.s\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfnmadds fd fs1 fs2 fs3 => p s!"\tfnmadd.s\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfnmsubs fd fs1 fs2 fs3 => p s!"\tfnmsub.s\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfcvtws rd fs => p s!"\tfcvt.w.s\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtsw fd rs => p s!"\tfcvt.s.w\t{freg fd}, {ireg0 rs}\n"
  | .Pfcvtwus rd fs => p s!"\tfcvt.wu.s\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtswu fd rs => p s!"\tfcvt.s.wu\t{freg fd}, {ireg0 rs}\n"
  | .Pfcvtls rd fs => p s!"\tfcvt.l.s\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtsl fd rs => p s!"\tfcvt.s.l\t{freg fd}, {ireg0 rs}\n"
  | .Pfcvtlus rd fs => p s!"\tfcvt.lu.s\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtslu fd rs => p s!"\tfcvt.s.lu\t{freg fd}, {ireg0 rs}\n"
  | .Pfld fd ra ofs | .Pfld_a fd ra ofs => p s!"\tfld\t{freg fd}, {offset ofs}({ireg ra})\n"
  | .Pfsd fs ra ofs | .Pfsd_a fs ra ofs => p s!"\tfsd\t{freg fs}, {offset ofs}({ireg ra})\n"
  | .Pfnegd fd fs => p s!"\tfneg.d\t{freg fd}, {freg fs}\n"
  | .Pfabsd fd fs => p s!"\tfabs.d\t{freg fd}, {freg fs}\n"
  | .Pfaddd fd fs1 fs2 => p s!"\tfadd.d\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfsubd fd fs1 fs2 => p s!"\tfsub.d\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfmuld fd fs1 fs2 => p s!"\tfmul.d\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfdivd fd fs1 fs2 => p s!"\tfdiv.d\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfmind fd fs1 fs2 => p s!"\tfmin.d\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfmaxd fd fs1 fs2 => p s!"\tfmax.d\t{freg fd}, {freg fs1}, {freg fs2}\n"
  | .Pfeqd rd fs1 fs2 => p s!"\tfeq.d\t{ireg rd}, {freg fs1}, {freg fs2}\n"
  | .Pfltd rd fs1 fs2 => p s!"\tflt.d\t{ireg rd}, {freg fs1}, {freg fs2}\n"
  | .Pfled rd fs1 fs2 => p s!"\tfle.d\t{ireg rd}, {freg fs1}, {freg fs2}\n"
  | .Pfsqrtd fd fs => p s!"\tfsqrt.d\t{freg fd}, {freg fs}\n"
  | .Pfmaddd fd fs1 fs2 fs3 => p s!"\tfmadd.d\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfmsubd fd fs1 fs2 fs3 => p s!"\tfmsub.d\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfnmaddd fd fs1 fs2 fs3 => p s!"\tfnmadd.d\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfnmsubd fd fs1 fs2 fs3 => p s!"\tfnmsub.d\t{freg fd}, {freg fs1}, {freg fs2}, {freg fs3}\n"
  | .Pfcvtwd rd fs => p s!"\tfcvt.w.d\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtdw fd rs => p s!"\tfcvt.d.w\t{freg fd}, {ireg0 rs}\n"
  | .Pfcvtwud rd fs => p s!"\tfcvt.wu.d\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtdwu fd rs => p s!"\tfcvt.d.wu\t{freg fd}, {ireg0 rs}\n"
  | .Pfcvtld rd fs => p s!"\tfcvt.l.d\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtdl fd rs => p s!"\tfcvt.d.l\t{freg fd}, {ireg0 rs}\n"
  | .Pfcvtlud rd fs => p s!"\tfcvt.lu.d\t{ireg rd}, {freg fs}, rtz\n"
  | .Pfcvtdlu fd rs => p s!"\tfcvt.d.lu\t{freg fd}, {ireg0 rs}\n"
  | .Pfcvtds fd fs => p s!"\tfcvt.d.s\t{freg fd}, {freg fs}\n"
  | .Pfcvtsd fd fs => p s!"\tfcvt.s.d\t{freg fd}, {freg fs}\n"
  -- Pseudo-instructions expanded in Asmexpand
  | .Pallocframe _ _ | .Pfreeframe _ _ | .Pcsel _ _ _ _ | .Pseqw _ _ _ | .Psnew _ _ _
  | .Pseql _ _ _ | .Psnel _ _ _ | .Pcvtl2w _ _ | .Pcvtw2l _ =>
    fail "pseudo-instruction must be expanded by Asmexpand"
  -- Pseudo-instructions that remain
  | .Plabel lbl => do p s!"{← printLabel lbl}:\n"
  | .Ploadsymbol rd id ofs => loadsymbol S rd id ofs
  | .Ploadsymbol_high rd id ofs => p s!"1:\tauipc\t{ireg rd}, %pcrel_hi({symbolOffset id ofs})\n"
  | .Ploadli rd n => do
    let d := (Integers.Int64.unsigned n).toNat
    let lbl ← labelLiteral64 d
    p s!"\tld\t{ireg rd}, {label lbl} {comment} {hex d}\n"
  | .Ploadfi rd f => do
    let lbl ← labelLiteral64 (Integers.Int64.unsigned (Floats.Float.toBits f)).toNat
    p s!"\tfld\t{freg rd}, {label lbl}, x31 {comment} {floatString f}\n"
  | .Ploadsi rd f => do
    let lbl ← labelLiteral32 (Integers.Int.unsigned (Floats.Float32.toBits f)).toNat
    p s!"\tflw\t{freg rd}, {label lbl}, x31 {comment} {float32String f}\n"
  | .Pbtbl r tbl => do
    if tbl.length > 0x80000000 then fail "Pbtbl: table too large"
    let lbl ← newLabel
    p s!"{comment} jumptable [ "
    for l in tbl do p s!"{← printLabel l} "
    p "]\n"
    p s!"\tsll\tx6, {ireg r}, 2\n"
    p s!"\tlla\tx31, {label lbl}\n"
    p "\tadd\tx6, x31, x6\n"
    p "\tlw\tx6, 0(x6)\n"
    p "\tadd\tx6, x31, x6\n"
    p "\tjr\tx6\n"
    addJumptable lbl tbl
    p s!"{comment} end pseudoinstr btbl\n"
  | .Pnop => p "\tnop\n"
  | .Pcfi_adjust sz => cfiAdjust S.cfi (Integers.Int.signed sz)
  | .Pcfi_rel_offset ofs => cfiRelOffset S.cfi "x1" (Integers.Int.signed ofs)
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_annot kind txt _ =>
      match kind.toNat with
      | 1 => p s!"{comment} annotation: {quoteString (annotText pregAnnot "x2" txt args)}\n"
      | 2 => do
        let lbl ← newLabel
        p s!"{label lbl}:\n"
        addAisAnnot lbl pregAnnot "x2" txt args
      | _ => fail "print_instruction: bad annotation kind"
    | .EF_debug kind txt _ =>
      printDebugInfo comment pregAnnot "sp" kind.toNat (Camlcoq.externAtom txt) args
    | .EF_inline_asm txt sg _ => do
      p s!"{comment} begin inline assembly\n\t"
      printInlineAsm pregAsm txt sg args res
      p s!"{comment} end inline assembly\n"
    | _ => fail "print_instruction: builtin not expanded"

/-- `Target.print_align` -/
def printAlign (alignment : Nat) : M Unit := out s!"\t.balign {alignment}\n"

/-- `Target.print_jumptable` -/
def printJumptable : M Unit := do
  let jts := (← get).jumptables
  if !jts.isEmpty then
    printSection .Section_jumptable
    out "\t.balign 4\n"
    for (lbl, tbl) in jts do
      out s!"{label lbl}:\n"
      for l in tbl do out s!"\t.long\t{← printLabel l} - {label lbl}\n"
    modify fun st => { st with jumptables := [] }

/-- `TargetPrinter.Target`.  `isStatic` is `C2C.atom_is_static`. -/
def target (isStatic : Ident → Bool) : PrintAsm.Target Asm.Function where
  printPrologue := out s!"\t.option {if S.pic then "pic" else "nopic"}\n"
  printEpilogue := pure ()
  printAlign := printAlign
  printCommSymb sz name align := do
    if isStatic name then out s!"\t.local\t{symbol name}\n"
    out s!"\t.comm\t{symbol name}, {sz}, {align}\n"
  printVarInfo := elfPrintVarInfo
  printFunInfo := elfPrintFunInfo
  printOptionalFunInfo := pure ()
  printInstructions fn := do
    modify fun st => { st with currentFunctionSig := fn.fn_sig }
    for i in fn.fn_code do printInstruction S i
  printJumptable _ := printJumptable
  printSection := printSection
  nameOfSection := nameOfSection
  comment := comment
  symbol := symbol
  defaultFalignment := 2
  label := label
  address := ".quad"
  bigEndian := false
  cfi := S.cfi
  system := "linux"

end Target

end TargetPrinter
end RiscV
end CC
