/-
  Printing PowerPC assembly code — port of `powerpc/TargetPrinter.ml`.

  The OCaml module type `SYSTEM` has two implementations (`Linux_System`
  for the GNU tools, `Diab_System` for the Wind River Diab tools) and the
  functor `Target(System)` produces the `PrintAsmaux.TARGET` used by
  `PrintAsm`.  Here `System` is a structure with the values `linuxSystem`
  and `diabSystem`, and `target` builds a `PrintAsm.Target Asm.Function`;
  `selSystem` is `sel_target`.

  What the OCaml code reads from global configuration is the record
  `Options`: `Clflags.option_faligncondbranchs`,
  `Clflags.option_falignbranchtargets`, `C2C.atom_is_static` and
  `Configuration.asm_supports_cfi`.

  Differences from OCaml:
  * The `assert false` of `rolm_mask`/`rolm64_mask` (a mask that `rlwinm`
    or `rldic` cannot encode) and of the pseudo-instructions that
    `Asmexpand` must have removed are failures of the printing monad.
  * The Diab section names `Section_debug_ranges` and `Section_debug_str`
    (an `assert false` in OCaml: they are not used with Diab) are printed as
    `<unsupported section>`.
  * Not ported: `-g` (`print_file_line`, the `.file` directives and the
    Diab `.d2_line` directives of `print_epilogue`, `debug_section`).  With
    the default debug hooks of `debug/Debug.ml` (no `-g`), `debug_section`
    and `compute_diab_file_enum` print nothing, which is what this port
    does.
-/
import CCLib.powerpc.Asm
import CCLib.backend.PrintAsm

namespace CC
namespace PowerPC
namespace TargetPrinter

open Asm Sections PrintAsmaux

/-! ## Registers -/

/-- `TargetPrinter.int_reg_name` -/
def intRegName : Ireg → String
  | .GPR0 => "0" | .GPR1 => "1" | .GPR2 => "2" | .GPR3 => "3"
  | .GPR4 => "4" | .GPR5 => "5" | .GPR6 => "6" | .GPR7 => "7"
  | .GPR8 => "8" | .GPR9 => "9" | .GPR10 => "10" | .GPR11 => "11"
  | .GPR12 => "12" | .GPR13 => "13" | .GPR14 => "14" | .GPR15 => "15"
  | .GPR16 => "16" | .GPR17 => "17" | .GPR18 => "18" | .GPR19 => "19"
  | .GPR20 => "20" | .GPR21 => "21" | .GPR22 => "22" | .GPR23 => "23"
  | .GPR24 => "24" | .GPR25 => "25" | .GPR26 => "26" | .GPR27 => "27"
  | .GPR28 => "28" | .GPR29 => "29" | .GPR30 => "30" | .GPR31 => "31"

/-- `TargetPrinter.float_reg_name` -/
def floatRegName : Freg → String
  | .FPR0 => "0" | .FPR1 => "1" | .FPR2 => "2" | .FPR3 => "3"
  | .FPR4 => "4" | .FPR5 => "5" | .FPR6 => "6" | .FPR7 => "7"
  | .FPR8 => "8" | .FPR9 => "9" | .FPR10 => "10" | .FPR11 => "11"
  | .FPR12 => "12" | .FPR13 => "13" | .FPR14 => "14" | .FPR15 => "15"
  | .FPR16 => "16" | .FPR17 => "17" | .FPR18 => "18" | .FPR19 => "19"
  | .FPR20 => "20" | .FPR21 => "21" | .FPR22 => "22" | .FPR23 => "23"
  | .FPR24 => "24" | .FPR25 => "25" | .FPR26 => "26" | .FPR27 => "27"
  | .FPR28 => "28" | .FPR29 => "29" | .FPR30 => "30" | .FPR31 => "31"

/-- `TargetPrinter.num_crbit` -/
def numCrbit : Crbit → Nat
  | .CRbit_0 => 0 | .CRbit_1 => 1 | .CRbit_2 => 2 | .CRbit_3 => 3 | .CRbit_6 => 6

/-- `TargetPrinter.symbol` -/
def symbol : Ident → String := elfSymbol

/-- `TargetPrinter.symbol_fragment` -/
def symbolFragment (s : Ident) (n : Integers.Ptrofs) (op : String) : String :=
  s!"({elfSymbolOffset s n}){op}"

/-- `TargetPrinter.label` -/
def label : Nat → String := elfLabel

/-- `TargetPrinter.preg_annot`: full register names `rN`, `fN`. -/
def pregAnnot : Preg → String
  | .IR r => "r" ++ intRegName r
  | .FR r => "f" ++ floatRegName r
  | _ => "<bad register>"

/-! ## Systems (`SYSTEM`) -/

/-- `TargetPrinter.SYSTEM` (without the `-g` functions) -/
structure System where
  comment : String
  constant : Constant → String
  ireg : Ireg → String
  freg : Freg → String
  nameOfSection : SectionName → String
  creg : Nat → String
  /-- whether `.cfi` directives are printed (`cfi_adjust`, `cfi_rel_offset`) -/
  cfiDirectives : Bool
  printPrologue : M Unit
  /-- `System.section` -/
  printSec : SectionName → M Unit
  address : String
  /-- `Configuration.system` -/
  system : String

/-- `TargetPrinter.Linux_System` -/
def linuxSystem : System :=
  let nameOfSection : SectionName → String := fun
    | .Section_text => ".text"
    | .Section_data i => variableSection ".data" (bss := some ".section\t.bss") (i := i)
    | .Section_small_data i =>
      variableSection ".section\t.sdata,\"aw\",@progbits"
        (bss := some ".section\t.sbss,\"aw\",@nobits") (i := i)
    | .Section_const i => variableSection ".rodata" (i := i)
    | .Section_small_const i => variableSection ".section\t.sdata2,\"a\",@progbits" (i := i)
    | .Section_string sz => elfMergeableStringSection sz ".section\t.rodata"
    | .Section_literal sz => elfMergeableLiteralSection sz ".section\t.rodata"
    | .Section_jumptable => ".section\t.rodata"
    | .Section_user s wr ex =>
      s!".section\t\"{s}\",\"a{if wr then "w" else ""}{if ex then "x" else ""}\",@progbits"
    | .Section_debug_info _ => ".section\t.debug_info,\"\",@progbits"
    | .Section_debug_abbrev => ".section\t.debug_abbrev,\"\",@progbits"
    | .Section_debug_loc => ".section\t.debug_loc,\"\",@progbits"
    | .Section_debug_line _ => ".section\t.debug_line,\"\",@progbits"
    | .Section_debug_ranges => ".section\t.debug_ranges,\"\",@progbits"
    | .Section_debug_str => ".section\t.debug_str,\"MS\",@progbits,1"
    | .Section_ais_annotation => ".section\t\"__compcert_ais_annotations\",\"\",@note"
  { comment := "#"
    constant := fun
      | .Cint n => coqint n
      | .Csymbol_low s n => symbolFragment s n "@l"
      | .Csymbol_high s n => symbolFragment s n "@ha"
      | .Csymbol_sda s n => symbolFragment s n "@sda21"
      -- 32-bit relative addressing is not supported by GNU binutils: treated
      -- as absolute addressing (the default base register being GPR0)
      | .Csymbol_rel_low s n => symbolFragment s n "@l"
      | .Csymbol_rel_high s n => symbolFragment s n "@ha"
    ireg := intRegName
    freg := floatRegName
    nameOfSection
    creg := fun r => toString r
    cfiDirectives := true
    printPrologue := pure ()
    printSec := fun sec => do
      let name := nameOfSection sec
      if name = "COMM" then fail "section: COMM"
      out s!"\t{name}\n"
    address := ".4byte"
    system := "linux" }

/-- `TargetPrinter.Diab_System` -/
def diabSystem : System :=
  let nameOfSection : SectionName → String := fun
    | .Section_text => ".text"
    | .Section_data i => variableSection ".data" (bss := some ".bss") (i := i)
    | .Section_small_data i =>
      variableSection ".sdata" (bss := some ".sbss") (common := false) (i := i)
    | .Section_const _ => ".text"
    | .Section_small_const _ => ".sdata2"
    | .Section_string _ => ".text"
    | .Section_literal _ => ".text"
    | .Section_jumptable => ".text"
    | .Section_user s wr ex =>
      let c := match wr, ex with
        | true, true => 'm'     -- text+data
        | true, false => 'd'    -- data
        | false, true => 'c'    -- text
        | false, false => 'r'   -- const
      s!".section\t\"{s}\",,{c}"
    | .Section_debug_info (some s) => s!".section\t.debug_info{s},,n"
    | .Section_debug_info none => ".section\t.debug_info,,n"
    | .Section_debug_abbrev => ".section\t.debug_abbrev,,n"
    | .Section_debug_loc => ".section\t.debug_loc,,n"
    | .Section_debug_line (some s) => s!".section\t.debug_line.{s},,n\n"
    | .Section_debug_line none => ".section\t.debug_line,,n\n"
    | .Section_debug_ranges | .Section_debug_str => "<unsupported section>"
    | .Section_ais_annotation => ".section\t\"__compcert_ais_annotations\",,n"
  { comment := ";"
    constant := fun
      | .Cint n => coqint n
      | .Csymbol_low s n => symbolFragment s n "@l"
      | .Csymbol_high s n => symbolFragment s n "@ha"
      | .Csymbol_sda s n => symbolFragment s n "@sdarx"
      | .Csymbol_rel_low s n => symbolFragment s n "@sdax@l"
      | .Csymbol_rel_high s n => symbolFragment s n "@sdarx@ha"
    ireg := fun r => "r" ++ intRegName r
    freg := fun r => "f" ++ floatRegName r
    nameOfSection
    creg := fun r => s!"cr{r}"
    cfiDirectives := false
    printPrologue := out "\t.xopt\talign-fill-text=0x60000000\n"
    printSec := fun sec => do
      let name := nameOfSection sec
      if name = "COMM" then fail "section: COMM"
      match sec with
      | .Section_debug_info (some _) =>
        out s!"\t{name}\n"
        out "\t.sectionlink\t.debug_info\n"
      | _ => out s!"\t{name}\n"
    address := ".4byte"
    system := "diab" }

/-! ## Masks of `rlwinm` and `rldic` -/

/-- `Target.rolm_mask`: the bit positions `(mb, me)` of a 32-bit mask made
    of one run of ones (possibly wrapping around). -/
def rolmMask (n : Nat) : Except String (Nat × Nat) := Id.run do
  let mut mb := 0
  let mut me := 32
  let mut last := n % 2 == 1
  let mut count := 0
  for mx in List.range 32 do
    let bit := n / 2 ^ (31 - mx) % 2 == 1
    if bit then
      if !last then
        count := count + 1; mb := mx; last := true
    else
      if last then
        count := count + 1; me := mx; last := false
  if me = 0 then me := 32
  if count = 2 || (count = 0 && last) then return .ok (mb, me - 1)
  else return .error "rolm_mask: mask not encodable"

#guard (rolmMask 0x0000FF00).toOption == some (16, 23)
#guard (rolmMask 0xFFFFFFFF).toOption == some (0, 31)

/-- `Target.rolm64_mask`: the positions of the leftmost and rightmost ones
    of a 64-bit mask made of one run of ones. -/
def rolm64Mask (n : Nat) : Except String (Nat × Nat) :=
  leftmost 0
where
  bitAt (pos : Nat) : Bool := n / 2 ^ (63 - pos) % 2 = 1
  rightmost (pos : Nat) : Except String Nat :=
    if h : pos ≥ 64 then .ok 63
    else if bitAt pos then rightmost (pos + 1)
    else if n % 2 ^ (63 - pos) = 0 then .ok (pos - 1)
    else .error "rolm64_mask: mask not encodable"
  termination_by 64 - pos
  leftmost (pos : Nat) : Except String (Nat × Nat) :=
    if h : pos ≥ 64 then .error "rolm64_mask: zero mask"
    else if !bitAt pos then leftmost (pos + 1)
    else do return (pos, ← rightmost (pos + 1))
  termination_by 64 - pos

#guard (rolm64Mask 0xFFFFFFFF00000000).toOption == some (0, 31)
#guard (rolm64Mask 0x00000000FFFFFFFF).toOption == some (32, 63)

/-! ## The target printer (`Target(System)`) -/

/-- What `TargetPrinter.ml` reads from the global configuration. -/
structure Options where
  /-- `Clflags.option_faligncondbranchs` -/
  falignCondBranchs : Nat := 0
  /-- `Clflags.option_falignbranchtargets` -/
  falignBranchTargets : Nat := 0
  /-- `C2C.atom_is_static` -/
  isStatic : Ident → Bool := fun _ => false
  /-- `Configuration.asm_supports_cfi` -/
  cfi : Bool := true

section Target

variable (S : System) (o : Options)

/-- `Target.label_low` -/
def labelLow (lbl : Nat) : String := s!".L{lbl}@l"
/-- `Target.label_high` -/
def labelHigh (lbl : Nat) : String := s!".L{lbl}@ha"

/-- `label (transl_label lbl)` -/
def printLabel (lbl : Positive) : M String := return label (← translLabel lbl)

/-- `Target.ireg_or_zero` -/
def iregOrZero (r : Ireg) : String := if r == .GPR0 then "0" else S.ireg r

/-- `Target.preg_asm` -/
def pregAsm (_ty : ATyp) : Preg → M Unit
  | .IR r => out (S.ireg r)
  | .FR r => out (S.freg r)
  | _ => fail "preg_asm"

/-- `%Ld` -/
def int64S (n : Integers.Int64) : String := coqint64 n

/-- `0x%lx` / `0x%Lx` -/
def hex0x (n : Int) : String := "0x" ++ hex n.toNat

/-- `Target.print_instruction` -/
def printInstruction (fallthrough : Bool) (i : Instruction) : M Unit :=
  let p := fun s => out s
  let ir := S.ireg
  let fr := S.freg
  let cst := S.constant
  let crbit := fun (b : Crbit) => toString (numCrbit b)
  let cr0 := S.creg 0
  let alignCond : M Unit :=
    if o.falignCondBranchs > 0 then p s!"\t.balign\t{o.falignCondBranchs}\n" else pure ()
  let expanded := fun (n : String) => (fail s!"{n} must be expanded by Asmexpand" : M Unit)
  match i with
  | .Padd r1 r2 r3 | .Padd64 r1 r2 r3 => p s!"\tadd\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Paddc r1 r2 r3 => p s!"\taddc\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Padde r1 r2 r3 => p s!"\tadde\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Paddi r1 r2 c => p s!"\taddi\t{ir r1}, {iregOrZero S r2}, {cst c}\n"
  | .Paddi64 r1 r2 n => p s!"\taddi\t{ir r1}, {iregOrZero S r2}, {int64S n}\n"
  | .Paddic r1 r2 c => p s!"\taddic\t{ir r1}, {iregOrZero S r2}, {cst c}\n"
  | .Paddis r1 r2 c => p s!"\taddis\t{ir r1}, {iregOrZero S r2}, {cst c}\n"
  | .Paddis64 r1 r2 n => p s!"\taddis\t{ir r1}, {iregOrZero S r2}, {int64S n}\n"
  | .Paddze r1 r2 | .Paddze64 r1 r2 => p s!"\taddze\t{ir r1}, {ir r2}\n"
  | .Pallocframe _ _ _ => expanded "Pallocframe"
  | .Pand_ r1 r2 r3 | .Pand_64 r1 r2 r3 => p s!"\tand.\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pandc r1 r2 r3 => p s!"\tandc\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pandi_ r1 r2 c => p s!"\tandi.\t{ir r1}, {ir r2}, {cst c}\n"
  | .Pandi_64 r1 r2 n => p s!"\tandi.\t{ir r1}, {ir r2}, {int64S n}\n"
  | .Pandis_ r1 r2 c => p s!"\tandis.\t{ir r1}, {ir r2}, {cst c}\n"
  | .Pandis_64 r1 r2 n => p s!"\tandis.\t{ir r1}, {ir r2}, {int64S n}\n"
  | .Pb lbl => do p s!"\tb\t{← printLabel lbl}\n"
  | .Pbctr _ => p "\tbctr\n"
  | .Pbctrl _ => p "\tbctrl\n"
  | .Pbdnz lbl => do p s!"\tbdnz\t{← printLabel lbl}\n"
  | .Pbf bit lbl => do alignCond; p s!"\tbf\t{crbit bit}, {← printLabel lbl}\n"
  | .Pbl s _ => p s!"\tbl\t{symbol s}\n"
  | .Pbs s _ => p s!"\tb\t{symbol s}\n"
  | .Pblr => p "\tblr\n"
  | .Pbt bit lbl => do alignCond; p s!"\tbt\t{crbit bit}, {← printLabel lbl}\n"
  | .Pbtbl r tbl => do
    let lbl ← newLabel
    p s!"{S.comment} begin pseudoinstr btbl({ir r})\n"
    p s!"{S.comment} jumptable [ "
    for l in tbl do p s!"{← printLabel l} "
    p "]\n"
    p s!"\tslwi    {ir .GPR12}, {ir r}, 2\n"
    p s!"\taddis\t{ir .GPR12}, {ir .GPR12}, {labelHigh lbl}\n"
    p s!"\tlwz\t{ir .GPR12}, {labelLow lbl}({ir .GPR12})\n"
    p s!"\tmtctr\t{ir .GPR12}\n"
    p "\tbctr\n"
    addJumptable lbl tbl
    p s!"{S.comment} end pseudoinstr btbl\n"
  | .Pcmpb r1 r2 r3 => p s!"\tcmpb\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pcmpld r1 r2 => p s!"\tcmpld\t{cr0}, {ir r1}, {ir r2}\n"
  | .Pcmpldi r1 n => p s!"\tcmpldi\t{cr0}, {ir r1}, {int64S n}\n"
  | .Pcmplw r1 r2 => p s!"\tcmplw\t{cr0}, {ir r1}, {ir r2}\n"
  | .Pcmplwi r1 c => p s!"\tcmplwi\t{cr0}, {ir r1}, {cst c}\n"
  | .Pcmpd r1 r2 => p s!"\tcmpd\t{cr0}, {ir r1}, {ir r2}\n"
  | .Pcmpdi r1 n => p s!"\tcmpdi\t{cr0}, {ir r1}, {int64S n}\n"
  | .Pcmpw r1 r2 => p s!"\tcmpw\t{cr0}, {ir r1}, {ir r2}\n"
  | .Pcmpwi r1 c => p s!"\tcmpwi\t{cr0}, {ir r1}, {cst c}\n"
  | .Pcntlzd r1 r2 => p s!"\tcntlzd\t{ir r1}, {ir r2}\n"
  | .Pcntlzw r1 r2 => p s!"\tcntlzw\t{ir r1}, {ir r2}\n"
  | .Pcreqv c1 c2 c3 => p s!"\tcreqv\t{crbit c1}, {crbit c2}, {crbit c3}\n"
  | .Pcror c1 c2 c3 => p s!"\tcror\t{crbit c1}, {crbit c2}, {crbit c3}\n"
  | .Pcrxor c1 c2 c3 => p s!"\tcrxor\t{crbit c1}, {crbit c2}, {crbit c3}\n"
  | .Pdcbf r1 r2 => p s!"\tdcbf\t{ir r1}, {ir r2}\n"
  | .Pdcbi r1 r2 => p s!"\tdcbi\t{ir r1}, {ir r2}\n"
  | .Pdcbt c r1 r2 => p s!"\tdcbt\t{coqint c}, {ir r1}, {ir r2}\n"
  | .Pdcbtst c r1 r2 => p s!"\tdcbtst\t{coqint c}, {ir r1}, {ir r2}\n"
  | .Pdcbtls c r1 r2 => p s!"\tdcbtls\t{coqint c}, {ir r1}, {ir r2}\n"
  | .Pdcbz r1 r2 => p s!"\tdcbz\t{ir r1}, {ir r2}\n"
  | .Pdivw r1 r2 r3 => p s!"\tdivw\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pdivwu r1 r2 r3 => p s!"\tdivwu\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pdivd r1 r2 r3 => p s!"\tdivd\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pdivdu r1 r2 r3 => p s!"\tdivdu\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Peieio => p "\teieio\n"
  | .Peqv r1 r2 r3 => p s!"\teqv\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pextsb r1 r2 => p s!"\textsb\t{ir r1}, {ir r2}\n"
  | .Pextsh r1 r2 => p s!"\textsh\t{ir r1}, {ir r2}\n"
  | .Pextsw r1 r2 => p s!"\textsw\t{ir r1}, {ir r2}\n"
  | .Pextzw _ _ => expanded "Pextzw"
  | .Pfreeframe _ _ => expanded "Pfreeframe"
  | .Pfabs r1 r2 | .Pfabss r1 r2 => p s!"\tfabs\t{fr r1}, {fr r2}\n"
  | .Pfadd r1 r2 r3 => p s!"\tfadd\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfadds r1 r2 r3 => p s!"\tfadds\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfcmpu r1 r2 => p s!"\tfcmpu\t{cr0}, {fr r1}, {fr r2}\n"
  | .Pfcfl _ _ => expanded "Pfcfl"
  | .Pfcfid r1 r2 => p s!"\tfcfid\t{fr r1}, {fr r2}\n"
  | .Pfcti _ _ => expanded "Pfcti"
  | .Pfctid _ _ => expanded "Pfctid"
  | .Pfctidz r1 r2 => p s!"\tfctidz\t{fr r1}, {fr r2}\n"
  | .Pfctiw r1 r2 => p s!"\tfctiw\t{fr r1}, {fr r2}\n"
  | .Pfctiwz r1 r2 => p s!"\tfctiwz\t{fr r1}, {fr r2}\n"
  | .Pfdiv r1 r2 r3 => p s!"\tfdiv\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfdivs r1 r2 r3 => p s!"\tfdivs\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfmake _ _ _ => expanded "Pfmake"
  | .Pfmr r1 r2 => p s!"\tfmr\t{fr r1}, {fr r2}\n"
  | .Pfmul r1 r2 r3 => p s!"\tfmul\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfmuls r1 r2 r3 => p s!"\tfmuls\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfneg r1 r2 | .Pfnegs r1 r2 => p s!"\tfneg\t{fr r1}, {fr r2}\n"
  | .Pfrsp r1 r2 => p s!"\tfrsp\t{fr r1}, {fr r2}\n"
  | .Pfxdp _ _ => expanded "Pfxdp"
  | .Pfsub r1 r2 r3 => p s!"\tfsub\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfsubs r1 r2 r3 => p s!"\tfsubs\t{fr r1}, {fr r2}, {fr r3}\n"
  | .Pfmadd r1 r2 r3 r4 => p s!"\tfmadd\t{fr r1}, {fr r2}, {fr r3}, {fr r4}\n"
  | .Pfmsub r1 r2 r3 r4 => p s!"\tfmsub\t{fr r1}, {fr r2}, {fr r3}, {fr r4}\n"
  | .Pfnmadd r1 r2 r3 r4 => p s!"\tfnmadd\t{fr r1}, {fr r2}, {fr r3}, {fr r4}\n"
  | .Pfnmsub r1 r2 r3 r4 => p s!"\tfnmsub\t{fr r1}, {fr r2}, {fr r3}, {fr r4}\n"
  | .Pfsqrt r1 r2 => p s!"\tfsqrt\t{fr r1}, {fr r2}\n"
  | .Pfrsqrte r1 r2 => p s!"\tfrsqrte\t{fr r1}, {fr r2}\n"
  | .Pfres r1 r2 => p s!"\tfres\t{fr r1}, {fr r2}\n"
  | .Pfsel r1 r2 r3 r4 => p s!"\tfsel\t{fr r1}, {fr r2}, {fr r3}, {fr r4}\n"
  | .Pisel r1 r2 r3 c => p s!"\tisel\t{ir r1}, {ir r2}, {ir r3}, {crbit c}\n"
  | .Pfsel_gen _ _ _ _ => expanded "Pfsel_gen"
  | .Picbi r1 r2 => p s!"\ticbi\t{ir r1}, {ir r2}\n"
  | .Picbtls n r1 r2 => p s!"\ticbtls\t{coqint n}, {ir r1}, {ir r2}\n"
  | .Pisync => p "\tisync\n"
  | .Plwsync => p "\tlwsync\n"
  | .Plbz r1 c r2 => p s!"\tlbz\t{ir r1}, {cst c}({ir r2})\n"
  | .Plbzx r1 r2 r3 => p s!"\tlbzx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pld r1 c r2 | .Pld_a r1 c r2 => p s!"\tld\t{ir r1}, {cst c}({ir r2})\n"
  | .Pldbrx r1 r2 r3 => p s!"\tldbrx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pldx r1 r2 r3 | .Pldx_a r1 r2 r3 => p s!"\tldx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Plfd r1 c r2 | .Plfd_a r1 c r2 => p s!"\tlfd\t{fr r1}, {cst c}({ir r2})\n"
  | .Plfdx r1 r2 r3 | .Plfdx_a r1 r2 r3 => p s!"\tlfdx\t{fr r1}, {ir r2}, {ir r3}\n"
  | .Plfs r1 c r2 => p s!"\tlfs\t{fr r1}, {cst c}({ir r2})\n"
  | .Plfsx r1 r2 r3 => p s!"\tlfsx\t{fr r1}, {ir r2}, {ir r3}\n"
  | .Plha r1 c r2 => p s!"\tlha\t{ir r1}, {cst c}({ir r2})\n"
  | .Plhax r1 r2 r3 => p s!"\tlhax\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Plhbrx r1 r2 r3 => p s!"\tlhbrx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Plhz r1 c r2 => p s!"\tlhz\t{ir r1}, {cst c}({ir r2})\n"
  | .Plhzx r1 r2 r3 => p s!"\tlhzx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pldi r1 c => do
    let lbl ← labelLiteral64 (Integers.Int64.unsigned c).toNat
    p s!"\taddis\t{ir .GPR12}, 0, {labelHigh lbl}\n"
    p s!"\tld\t{ir r1}, {labelLow lbl}({ir .GPR12}) {S.comment} {int64S c}\n"
  | .Plmake _ _ _ => expanded "Plmake"
  | .Pllo _ => expanded "Pllo"
  | .Plhi _ _ => expanded "Plhi"
  | .Plfi r1 c => do
    let lbl ← labelLiteral64 (Integers.Int64.unsigned (Floats.Float.toBits c)).toNat
    p s!"\taddis\t{ir .GPR12}, 0, {labelHigh lbl}\n"
    p s!"\tlfd\t{fr r1}, {labelLow lbl}({ir .GPR12}) {S.comment} {floatString c}\n"
  | .Plfis r1 c => do
    let lbl ← labelLiteral32 (Integers.Int.unsigned (Floats.Float32.toBits c)).toNat
    p s!"\taddis\t{ir .GPR12}, 0, {labelHigh lbl}\n"
    p s!"\tlfs\t{fr r1}, {labelLow lbl}({ir .GPR12}) {S.comment} {float32String c}\n"
  | .Plwarx r1 r2 r3 => p s!"\tlwarx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Plwbrx r1 r2 r3 => p s!"\tlwbrx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Plwz r1 c r2 | .Plwz_a r1 c r2 => p s!"\tlwz\t{ir r1}, {cst c}({ir r2})\n"
  | .Plwzu r1 c r2 => p s!"\tlwzu\t{ir r1}, {cst c}({ir r2})\n"
  | .Plwzx r1 r2 r3 | .Plwzx_a r1 r2 r3 => p s!"\tlwzx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmbar mo => p s!"\tmbar\t{coqint mo}\n"
  | .Pmfcr r1 => p s!"\tmfcr\t{ir r1}\n"
  | .Pmfcrbit _ _ => expanded "Pmfcrbit"
  | .Pmflr r1 => p s!"\tmflr\t{ir r1}\n"
  | .Pmr r1 r2 => p s!"\tmr\t{ir r1}, {ir r2}\n"
  | .Pmtctr r1 => p s!"\tmtctr\t{ir r1}\n"
  | .Pmtlr r1 => p s!"\tmtlr\t{ir r1}\n"
  | .Pmfspr rd spr => p s!"\tmfspr\t{ir rd}, {coqint spr}\n"
  | .Pmtspr spr rs => p s!"\tmtspr\t{coqint spr}, {ir rs}\n"
  | .Pmulld r1 r2 r3 => p s!"\tmulld\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmulli r1 r2 c => p s!"\tmulli\t{ir r1}, {ir r2}, {cst c}\n"
  | .Pmullw r1 r2 r3 => p s!"\tmullw\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmulhw r1 r2 r3 => p s!"\tmulhw\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmulhwu r1 r2 r3 => p s!"\tmulhwu\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmulhd r1 r2 r3 => p s!"\tmulhd\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pmulhdu r1 r2 r3 => p s!"\tmulhdu\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pnand r1 r2 r3 => p s!"\tnand\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pnor r1 r2 r3 | .Pnor64 r1 r2 r3 => p s!"\tnor\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Por r1 r2 r3 | .Por64 r1 r2 r3 => p s!"\tor\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Porc r1 r2 r3 => p s!"\torc\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pori r1 r2 c => p s!"\tori\t{ir r1}, {ir r2}, {cst c}\n"
  | .Pori64 r1 r2 n => p s!"\tori\t{ir r1}, {ir r2}, {int64S n}\n"
  | .Poris r1 r2 c => p s!"\toris\t{ir r1}, {ir r2}, {cst c}\n"
  | .Poris64 r1 r2 n => p s!"\toris\t{ir r1}, {ir r2}, {int64S n}\n"
  | .Prldicl r1 r2 c1 c2 => p s!"\trldicl\t{ir r1}, {ir r2}, {coqint c1}, {coqint c2}\n"
  | .Prldinm r1 r2 c1 c2 => do
    let amount := Integers.Int.signed c1
    let mask := (Integers.Int64.unsigned c2).toNat
    match rolm64Mask mask with
    | .error e => fail e
    | .ok (first, last) =>
      if last = 63 then
        p s!"\trldicl\t{ir r1}, {ir r2}, {amount}, {first} {S.comment} 0x{hex mask}\n"
      else if first = 0 then
        p s!"\trldicr\t{ir r1}, {ir r2}, {amount}, {last} {S.comment} 0x{hex mask}\n"
      else if (last : Int) = 63 - amount then
        p s!"\trldic\t{ir r1}, {ir r2}, {amount}, {first} {S.comment} 0x{hex mask}\n"
      else fail "Prldinm: mask not encodable"
  | .Prldimi r1 r2 c1 c2 => do
    let amount := Integers.Int.signed c1
    let mask := (Integers.Int64.unsigned c2).toNat
    match rolm64Mask mask with
    | .error e => fail e
    | .ok (first, last) =>
      if (last : Int) ≠ 63 - amount then fail "Prldimi: mask not encodable"
      p s!"\trldimi\t{ir r1}, {ir r2}, {amount}, {first} {S.comment} 0x{hex mask}\n"
  | .Prlwinm r1 r2 c1 c2 => do
    let m := (Integers.Int.unsigned c2).toNat
    match rolmMask m with
    | .error e => fail e
    | .ok (mb, me) =>
      p s!"\trlwinm\t{ir r1}, {ir r2}, {coqint c1}, {mb}, {me} {S.comment} 0x{hex m}\n"
  | .Prlwimi r1 r2 c1 c2 => do
    let m := (Integers.Int.unsigned c2).toNat
    match rolmMask m with
    | .error e => fail e
    | .ok (mb, me) =>
      p s!"\trlwimi\t{ir r1}, {ir r2}, {coqint c1}, {mb}, {me} {S.comment} 0x{hex m}\n"
  | .Psld r1 r2 r3 => p s!"\tsld\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pslw r1 r2 r3 => p s!"\tslw\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psrad r1 r2 r3 => p s!"\tsrad\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psradi r1 r2 c => p s!"\tsradi\t{ir r1}, {ir r2}, {coqint c}\n"
  | .Psraw r1 r2 r3 => p s!"\tsraw\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psrawi r1 r2 c => p s!"\tsrawi\t{ir r1}, {ir r2}, {coqint c}\n"
  | .Psrd r1 r2 r3 => p s!"\tsrd\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psrw r1 r2 r3 => p s!"\tsrw\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pstb r1 c r2 => p s!"\tstb\t{ir r1}, {cst c}({ir r2})\n"
  | .Pstbx r1 r2 r3 => p s!"\tstbx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pstd r1 c r2 | .Pstd_a r1 c r2 => p s!"\tstd\t{ir r1}, {cst c}({ir r2})\n"
  | .Pstdbrx r1 r2 r3 => p s!"\tstdbrx  {ir r1}, {ir r2}, {ir r3}\n"
  | .Pstdx r1 r2 r3 | .Pstdx_a r1 r2 r3 => p s!"\tstdx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pstdu r1 c r2 => p s!"\tstdu\t{ir r1}, {cst c}({ir r2})\n"
  | .Pstfd r1 c r2 | .Pstfd_a r1 c r2 => p s!"\tstfd\t{fr r1}, {cst c}({ir r2})\n"
  | .Pstfdu r1 c r2 => p s!"\tstfdu\t{fr r1}, {cst c}({ir r2})\n"
  | .Pstfdx r1 r2 r3 | .Pstfdx_a r1 r2 r3 => p s!"\tstfdx\t{fr r1}, {ir r2}, {ir r3}\n"
  | .Pstfs r1 c r2 => p s!"\tstfs\t{fr r1}, {cst c}({ir r2})\n"
  | .Pstfsx r1 r2 r3 => p s!"\tstfsx\t{fr r1}, {ir r2}, {ir r3}\n"
  | .Psth r1 c r2 => p s!"\tsth\t{ir r1}, {cst c}({ir r2})\n"
  | .Psthx r1 r2 r3 => p s!"\tsthx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psthbrx r1 r2 r3 => p s!"\tsthbrx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pstw r1 c r2 | .Pstw_a r1 c r2 => p s!"\tstw\t{ir r1}, {cst c}({ir r2})\n"
  | .Pstwu r1 c r2 => p s!"\tstwu\t{ir r1}, {cst c}({ir r2})\n"
  | .Pstwx r1 r2 r3 | .Pstwx_a r1 r2 r3 => p s!"\tstwx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pstwux r1 r2 r3 => p s!"\tstwux\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pstwbrx r1 r2 r3 => p s!"\tstwbrx\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pstwcx_ r1 r2 r3 => p s!"\tstwcx.\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psubfc r1 r2 r3 | .Psubfc64 r1 r2 r3 => p s!"\tsubfc\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psubfe r1 r2 r3 => p s!"\tsubfe\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Psubfze r1 r2 => p s!"\tsubfze\t{ir r1}, {ir r2}\n"
  | .Psubfic r1 r2 c => p s!"\tsubfic\t{ir r1}, {ir r2}, {cst c}\n"
  | .Psubfic64 r1 r2 n => p s!"\tsubfic\t{ir r1}, {ir r2}, {int64S n}\n"
  | .Psync => p "\tsync\n"
  | .Ptrap => p "\ttrap\n"
  | .Pxor r1 r2 r3 | .Pxor64 r1 r2 r3 => p s!"\txor\t{ir r1}, {ir r2}, {ir r3}\n"
  | .Pxori r1 r2 c => p s!"\txori\t{ir r1}, {ir r2}, {cst c}\n"
  | .Pxori64 r1 r2 n => p s!"\txori\t{ir r1}, {ir r2}, {int64S n}\n"
  | .Pxoris r1 r2 c => p s!"\txoris\t{ir r1}, {ir r2}, {cst c}\n"
  | .Pxoris64 r1 r2 n => p s!"\txoris\t{ir r1}, {ir r2}, {int64S n}\n"
  | .Plabel lbl => do
    if !fallthrough && o.falignBranchTargets > 0 then
      p s!"\t.balign\t{o.falignBranchTargets}\n"
    p s!"{← printLabel lbl}:\n"
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_annot kind txt _ =>
      match kind.toNat with
      | 1 => p s!"{S.comment} annotation: {quoteString (annotText pregAnnot "sp" txt args)}\n"
      | 2 => do
        let lbl ← newLabel
        p s!"{label lbl}:\n"
        addAisAnnot lbl pregAnnot "r1" txt args
      | _ => fail "print_instruction: bad annotation kind"
    | .EF_debug kind txt _ =>
      printDebugInfo S.comment pregAnnot "r1" kind.toNat (Camlcoq.externAtom txt) args
    | .EF_inline_asm txt sg _ => do
      p s!"{S.comment} begin inline assembly\n\t"
      printInlineAsm (pregAsm S) txt sg args res
      p s!"{S.comment} end inline assembly\n"
    | _ => fail "print_instruction: builtin not expanded"
  | .Pcfi_adjust n => cfiAdjust (o.cfi && S.cfiDirectives) (Integers.Int.signed n)
  | .Pcfi_rel_offset n => cfiRelOffset (o.cfi && S.cfiDirectives) "lr" (Integers.Int.signed n)

/-- `Target.instr_fall_through` -/
def instrFallThrough : Instruction → Bool
  | .Pb _ | .Pbctr _ | .Pbs _ _ | .Pblr => false
  | _ => true

/-- `Target.print_instructions` -/
def printInstructions (code : List Instruction) : M Unit :=
  go true code
where
  go (fallthrough : Bool) : List Instruction → M Unit
    | [] => pure ()
    | i :: c => do
      printInstruction S o fallthrough i
      go (instrFallThrough i) c

/-- `Target.print_comm_symb` -/
def printCommSymb (sz : Int) (name : Ident) (align : Nat) : M Unit :=
  out s!"\t{if o.isStatic name then ".lcomm" else ".comm"}\t{symbol name}, {sz}, {align}\n"

/-- `Target.print_jumptable` -/
def printJumptable (jmptbl : SectionName) : M Unit := do
  let jts := (← get).jumptables
  if !jts.isEmpty then
    S.printSec jmptbl
    out "\t.balign 4\n"
    for (lbl, tbl) in jts do
      out s!"{label lbl}:"
      for l in tbl do out s!"\t.long\t{← printLabel l}\n"
    modify fun st => { st with jumptables := [] }

/-- `TargetPrinter.Target(System)` -/
def target : PrintAsm.Target Asm.Function where
  printPrologue := S.printPrologue
  printEpilogue := pure ()
  printAlign align := out s!"\t.balign\t{align}\n"
  printCommSymb := printCommSymb o
  printVarInfo := elfPrintVarInfo
  printFunInfo := elfPrintFunInfo
  printOptionalFunInfo := pure ()
  printInstructions fn := do
    modify fun st => { st with currentFunctionSig := fn.fn_sig }
    printInstructions S o fn.fn_code
  printJumptable := printJumptable S
  printSection := S.printSec
  nameOfSection := S.nameOfSection
  comment := S.comment
  symbol := symbol
  defaultFalignment := 4
  label := label
  address := S.address
  bigEndian := true
  cfi := o.cfi && S.cfiDirectives
  system := S.system
  ptr64 := false

end Target

/-- `TargetPrinter.sel_target`: the system printer for
    `Configuration.system` (`"linux"` or `"diab"`). -/
def selSystem (system : String) : Except String System :=
  match system with
  | "linux" => .ok linuxSystem
  | "diab" => .ok diabSystem
  | _ => .error s!"System {system} not supported"

end TargetPrinter
end PowerPC
end CC
