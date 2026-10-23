/-
  Printing x86-64 assembly code in AT&T syntax — port of
  `x86/TargetPrinter.ml`.

  The OCaml module has a module type `SYSTEM` with three implementations
  (`ELF_System`, `MacOS_System`, `Cygwin_System`) and a functor `Target`
  producing the `PrintAsmaux.TARGET` used by `PrintAsm`.  Here `System` is a
  structure with the values `elfSystem`, `macosSystem`, `cygwinSystem`, and
  `target` builds a `PrintAsm.Target Asm.Function`; `selTarget` is
  `sel_target`, choosing the system from `Configuration.system`.

  As the Lean port's x86 back end is x86-64, the printer is the one for
  `Archi.ptr64 = true`.  `SelectOp.symbol_is_relocatable` (which decides
  whether calls go through the PLT on ELF) is an argument, as in
  `X86.Compiler.Config`.

  Not ported: `-g` (`print_file_line`, the `.file` directives of
  `print_epilogue`).
-/
import CCLib.x86.Asm
import CCLib.backend.PrintAsm

namespace CC
namespace X86
namespace TargetPrinter

open Asm Sections PrintAsmaux

/-! ## Register names -/

/-- `TargetPrinter.int64_reg_name` -/
def int64RegName : Ireg → String
  | .RAX => "%rax" | .RBX => "%rbx" | .RCX => "%rcx" | .RDX => "%rdx"
  | .RSI => "%rsi" | .RDI => "%rdi" | .RBP => "%rbp" | .RSP => "%rsp"
  | .R8 => "%r8" | .R9 => "%r9" | .R10 => "%r10" | .R11 => "%r11"
  | .R12 => "%r12" | .R13 => "%r13" | .R14 => "%r14" | .R15 => "%r15"

/-- `TargetPrinter.int32_reg_name` -/
def int32RegName : Ireg → String
  | .RAX => "%eax" | .RBX => "%ebx" | .RCX => "%ecx" | .RDX => "%edx"
  | .RSI => "%esi" | .RDI => "%edi" | .RBP => "%ebp" | .RSP => "%esp"
  | .R8 => "%r8d" | .R9 => "%r9d" | .R10 => "%r10d" | .R11 => "%r11d"
  | .R12 => "%r12d" | .R13 => "%r13d" | .R14 => "%r14d" | .R15 => "%r15d"

/-- `TargetPrinter.int8_reg_name` -/
def int8RegName : Ireg → String
  | .RAX => "%al" | .RBX => "%bl" | .RCX => "%cl" | .RDX => "%dl"
  | .RSI => "%sil" | .RDI => "%dil" | .RBP => "%bpl" | .RSP => "%spl"
  | .R8 => "%r8b" | .R9 => "%r9b" | .R10 => "%r10b" | .R11 => "%r11b"
  | .R12 => "%r12b" | .R13 => "%r13b" | .R14 => "%r14b" | .R15 => "%r15b"

/-- `TargetPrinter.int16_reg_name` -/
def int16RegName : Ireg → String
  | .RAX => "%ax" | .RBX => "%bx" | .RCX => "%cx" | .RDX => "%dx"
  | .RSI => "%si" | .RDI => "%di" | .RBP => "%bp" | .RSP => "%sp"
  | .R8 => "%r8w" | .R9 => "%r9w" | .R10 => "%r10w" | .R11 => "%r11w"
  | .R12 => "%r12w" | .R13 => "%r13w" | .R14 => "%r14w" | .R15 => "%r15w"

/-- `TargetPrinter.float_reg_name` -/
def floatRegName : Freg → String
  | .XMM0 => "%xmm0" | .XMM1 => "%xmm1" | .XMM2 => "%xmm2" | .XMM3 => "%xmm3"
  | .XMM4 => "%xmm4" | .XMM5 => "%xmm5" | .XMM6 => "%xmm6" | .XMM7 => "%xmm7"
  | .XMM8 => "%xmm8" | .XMM9 => "%xmm9" | .XMM10 => "%xmm10" | .XMM11 => "%xmm11"
  | .XMM12 => "%xmm12" | .XMM13 => "%xmm13" | .XMM14 => "%xmm14" | .XMM15 => "%xmm15"

/-- `TargetPrinter.ireg8` -/
abbrev ireg8 := int8RegName
/-- `TargetPrinter.ireg16` -/
abbrev ireg16 := int16RegName
/-- `TargetPrinter.ireg32` -/
abbrev ireg32 := int32RegName
/-- `TargetPrinter.ireg64` -/
abbrev ireg64 := int64RegName
/-- `TargetPrinter.ireg` (64-bit) -/
abbrev ireg := int64RegName
/-- `TargetPrinter.freg` -/
abbrev freg := floatRegName

/-- `TargetPrinter.preg_asm` -/
def pregAsm (ty : ATyp) : Preg → M Unit
  | .IR r => out (if ty = .Tlong then ireg64 r else ireg32 r)
  | .FR r => out (freg r)
  | _ => fail "preg_asm"

/-- `TargetPrinter.ais_int64_reg_name` -/
def aisInt64RegName : Ireg → String
  | .RAX => "rax" | .RBX => "rbx" | .RCX => "rcx" | .RDX => "rdx"
  | .RSI => "rsi" | .RDI => "rdi" | .RBP => "rbp" | .RSP => "rsp"
  | .R8 => "r8" | .R9 => "r9" | .R10 => "r10" | .R11 => "r11"
  | .R12 => "r12" | .R13 => "r13" | .R14 => "r14" | .R15 => "r15"

/-- `TargetPrinter.preg_ais_annot` (for `Archi.ptr64 = true`) -/
def pregAisAnnot : Preg → String
  | .IR r => aisInt64RegName r
  | .FR r => floatRegName r
  | _ => "<bad register>"

/-- `TargetPrinter.preg_annot` -/
def pregAnnot : Preg → String
  | .IR r => int64RegName r
  | .FR r => floatRegName r
  | _ => "<bad register>"

/-- `TargetPrinter.data_pointer` -/
def dataPointer : String := ".quad"

/-- `TargetPrinter.log2` -/
def log2 (n : Nat) : Nat := Nat.log2 n

/-! ## Systems (`SYSTEM`) -/

/-- `TargetPrinter.SYSTEM` -/
structure System where
  comment : String
  rawSymbol : String → String
  symbol : Ident → String
  symbolParen : Ident → String
  symbolFunction : Ident → String
  label : Nat → String
  nameOfSection : SectionName → String
  stackAlignment : Nat
  printAlign : Nat → M Unit
  printMovRs : Ireg → Ident → M Unit
  printFunInfo : Ident → M Unit
  printVarInfo : Ident → M Unit
  printEpilogue : M Unit
  printCommDecl : Ident → Int → Nat → M Unit
  printLcommDecl : Ident → Int → Nat → M Unit
  /-- `Configuration.system` -/
  system : String

/-- Parenthesize symbols starting with `$` (`symbol_paren`). -/
def parenDollar (s : String) : String :=
  if s.startsWith "$" then s!"({s})" else s

/-- `TargetPrinter.ELF_System`.  `symbolIsRelocatable` is
    `SelectOp.symbol_is_relocatable`. -/
def elfSystem (symbolIsRelocatable : Ident → Bool := fun _ => false) : System :=
  let symbol := elfSymbol
  let symbolParen := fun id => parenDollar (Camlcoq.externAtom id)
  { comment := "#"
    rawSymbol := id
    symbol
    symbolParen
    symbolFunction := fun id =>
      symbolParen id ++ (if symbolIsRelocatable id then "@PLT" else "")
    label := elfLabel
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
      | .Section_user s wr ex =>
        s!".section\t\"{s}\",\"a{if wr then "w" else ""}{if ex then "x" else ""}\",@progbits"
      | .Section_debug_info _ => ".section\t.debug_info,\"\",@progbits"
      | .Section_debug_loc => ".section\t.debug_loc,\"\",@progbits"
      | .Section_debug_line _ => ".section\t.debug_line,\"\",@progbits"
      | .Section_debug_abbrev => ".section\t.debug_abbrev,\"\",@progbits"
      | .Section_debug_ranges => ".section\t.debug_ranges,\"\",@progbits"
      | .Section_debug_str => ".section\t.debug_str,\"MS\",@progbits,1"
      | .Section_ais_annotation => ".section\t\"__compcert_ais_annotations\",\"\",@note"
    stackAlignment := 16
    printAlign := fun n => out s!"\t.align\t{n}\n"
    printMovRs := fun rd id => out s!"\tmovq    {symbolParen id}@GOTPCREL(%rip), {ireg64 rd}\n"
    printFunInfo := elfPrintFunInfo
    printVarInfo := elfPrintVarInfo
    printEpilogue := pure ()
    printCommDecl := fun name sz al => out s!"\t.comm\t{symbol name}, {sz}, {al}\n"
    printLcommDecl := fun name sz al => do
      out s!"\t.local\t{symbol name}\n"
      out s!"\t.comm\t{symbol name}, {sz}, {al}\n"
    system := "linux" }

/-- `TargetPrinter.MacOS_System` -/
def macosSystem : System :=
  let rawSymbol := fun s => "_" ++ s
  let symbol := fun id => rawSymbol (Camlcoq.externAtom id)
  { comment := "##"
    rawSymbol
    symbol
    symbolParen := symbol
    symbolFunction := symbol
    label := fun lbl => s!"L{lbl}"
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
    stackAlignment := 16
    printAlign := fun n => out s!"\t.align\t{log2 n}\n"
    printMovRs := fun rd id => out s!"\tmovq    {symbol id}@GOTPCREL(%rip), {ireg64 rd}\n"
    printFunInfo := fun _ => pure ()
    printVarInfo := fun _ => pure ()
    printEpilogue := pure ()
    printCommDecl := fun name sz al => out s!"\t.comm\t{symbol name}, {sz}, {log2 al}\n"
    printLcommDecl := fun name sz al => out s!"\t.lcomm\t{symbol name}, {sz}, {log2 al}\n"
    system := "macos" }

/-- `Cygwin_System.declare_indirect_symbol` -/
def declareIndirectSymbol (s : String) : M Unit := do
  out s!"\t.section\t.rdata$.refptr.{s}, \"dr\"\n"
  out s!"\t.globl\t.refptr.{s}\n"
  out "\t.linkonce\tdiscard\n"
  out s!".refptr.{s}:\n"
  out s!"\t.quad\t{s}\n"

/-- `TargetPrinter.Cygwin_System` -/
def cygwinSystem : System :=
  let rawSymbol := fun (s : String) => s
  let symbol := fun id => rawSymbol (Camlcoq.externAtom id)
  let symbolParen := fun id => parenDollar (Camlcoq.externAtom id)
  { comment := "#"
    rawSymbol
    symbol
    symbolParen
    symbolFunction := symbolParen
    label := fun lbl => s!"L{lbl}"
    nameOfSection := fun
      | .Section_text => ".text"
      | .Section_data i | .Section_small_data i =>
        variableSection ".data" (bss := some ".bss") (i := i)
      | .Section_const i | .Section_small_const i =>
        variableSection ".section\t.rdata,\"dr\"" (i := i)
      | .Section_string _ => ".section\t.rdata,\"dr\""
      | .Section_literal _ => ".section\t.rdata,\"dr\""
      | .Section_jumptable => ".text"
      | .Section_user s wr ex =>
        s!".section\t{s}, \"{if ex then "xr" else if wr then "d" else "dr"}\"\n"
      | .Section_debug_info _ => ".section\t.debug_info,\"dr\""
      | .Section_debug_loc => ".section\t.debug_loc,\"dr\""
      | .Section_debug_line _ => ".section\t.debug_line,\"dr\""
      | .Section_debug_abbrev => ".section\t.debug_abbrev,\"dr\""
      | .Section_debug_ranges => ".section\t.debug_ranges,\"dr\""
      | .Section_debug_str => ".section\t.debug_str,\"dr\""
      | .Section_ais_annotation => ".text"
    stackAlignment := 8
    printAlign := fun n => out s!"\t.balign\t{n}\n"
    printMovRs := fun rd id => do
      let s := Camlcoq.externAtom id
      modify fun st => { st with indirectSymbols :=
        if st.indirectSymbols.contains s then st.indirectSymbols else s :: st.indirectSymbols }
      out s!"\tmovq\t.refptr.{s}(%rip), {ireg rd}\n"
    printFunInfo := fun _ => pure ()
    printVarInfo := fun _ => pure ()
    printEpilogue := do
      -- `StringSet.iter` visits the symbols in increasing order
      let syms := (← get).indirectSymbols.toArray.qsort (· < ·)
      for s in syms do declareIndirectSymbol s
      modify fun st => { st with indirectSymbols := [] }
    printCommDecl := fun name sz al => out s!"\t.comm   {symbol name}, {sz}, {log2 al}\n"
    printLcommDecl := fun name sz al => out s!"\t.lcomm   {symbol name}, {sz}, {al}\n"
    system := "cygwin" }

/-! ## The target printer (`Target(System)`) -/

section Target

variable (S : System)

/-- `Target.addressing_gen` (64-bit: symbols are RIP-relative) -/
def addressingGen (iregName : Ireg → String) : Addrmode → String
  | .Addrmode base shift cst =>
    let c := match cst with
      | .inl n => toString n
      | .inr (id, ofs) =>
        let o := Integers.Ptrofs.signed ofs
        if o = 0 then s!"{S.symbolParen id}(%rip)" else s!"({S.symbol id} + {o})(%rip)"
    let b := match base, shift with
      | none, none => ""
      | some r1, none => s!"({iregName r1})"
      | none, some (r2, sc) => s!"(,{iregName r2},{sc})"
      | some r1, some (r2, sc) => s!"({iregName r1},{iregName r2},{sc})"
    c ++ b

/-- `Target.addressing32` -/
def addressing32 := addressingGen S ireg32
/-- `Target.addressing64` -/
def addressing64 := addressingGen S ireg64
/-- `Target.addressing` -/
def addressing := addressingGen S ireg

/-- `Target.name_of_condition` -/
def nameOfCondition : Testcond → String
  | .Cond_e => "e" | .Cond_ne => "ne"
  | .Cond_b => "b" | .Cond_be => "be" | .Cond_ae => "ae" | .Cond_a => "a"
  | .Cond_l => "l" | .Cond_le => "le" | .Cond_ge => "ge" | .Cond_g => "g"
  | .Cond_p => "p" | .Cond_np => "np"

/-- `Target.name_of_neg_condition` -/
def nameOfNegCondition : Testcond → String
  | .Cond_e => "ne" | .Cond_ne => "e"
  | .Cond_b => "ae" | .Cond_be => "a" | .Cond_ae => "b" | .Cond_a => "be"
  | .Cond_l => "ge" | .Cond_le => "g" | .Cond_ge => "l" | .Cond_g => "le"
  | .Cond_p => "np" | .Cond_np => "p"

/-- `Target.section` -/
def printSection (sec : SectionName) : M Unit := out s!"\t{S.nameOfSection sec}\n"

/-- `Target.rip_rel` -/
def ripRel : String := "(%rip)"

/-- `Target.intconst64`: immediates that do not fit in 32 signed bits are
    turned into memory operands. -/
def intconst64 (n : Integers.Int64) : M String := do
  let n1 := Integers.Int64.signed n
  if -2147483648 ≤ n1 ∧ n1 < 2147483648 then return s!"${n1}"
  else
    let lbl ← labelLiteral64 (Integers.Int64.unsigned n).toNat
    return s!"{S.label lbl}(%rip)"

/-- `Target.print_instruction`.  AT&T syntax: `op src, dst`. -/
def printInstruction (cfi : Bool) (i : Instruction) : M Unit :=
  let p := fun s => out s
  let ad := addressing S
  match i with
  -- Moves
  | .Pmov_rr rd r1 => p s!"\tmovq\t{ireg64 r1}, {ireg64 rd}\n"
  | .Pmovl_ri rd n => p s!"\tmovl\t${coqint n}, {ireg32 rd}\n"
  | .Pmovq_ri rd n =>
    let n1 := Integers.Int64.signed n
    if 0 ≤ n1 ∧ n1 < 4294967296 then p s!"\tmovl\t${n1}, {ireg32 rd}\n"
    else if -2147483648 ≤ n1 ∧ n1 < 2147483648 then p s!"\tmovq\t${n1}, {ireg64 rd}\n"
    else p s!"\tmovabsq\t${n1}, {ireg64 rd}\n"
  | .Pmov_rs rd id => S.printMovRs rd id
  | .Pmovl_rm rd a => p s!"\tmovl\t{ad a}, {ireg32 rd}\n"
  | .Pmovq_rm rd a => p s!"\tmovq\t{ad a}, {ireg64 rd}\n"
  | .Pmov_rm_a rd a => p s!"\tmovq\t{ad a}, {ireg64 rd}\n"
  | .Pmovl_mr a r1 => p s!"\tmovl\t{ireg32 r1}, {ad a}\n"
  | .Pmovq_mr a r1 => p s!"\tmovq\t{ireg64 r1}, {ad a}\n"
  | .Pmov_mr_a a r1 => p s!"\tmovq\t{ireg64 r1}, {ad a}\n"
  | .Pmovsd_ff rd r1 => p s!"\tmovapd\t{freg r1}, {freg rd}\n"
  | .Pmovsd_fi rd n => do
    let lbl ← labelLiteral64 (Integers.Int64.unsigned (Floats.Float.toBits n)).toNat
    p s!"\tmovsd\t{S.label lbl}{ripRel}, {freg rd} {S.comment} {floatString n}\n"
  | .Pmovsd_fm rd a | .Pmovsd_fm_a rd a => p s!"\tmovsd\t{ad a}, {freg rd}\n"
  | .Pmovsd_mf a r1 | .Pmovsd_mf_a a r1 => p s!"\tmovsd\t{freg r1}, {ad a}\n"
  | .Pmovss_fi rd n => do
    let lbl ← labelLiteral32 (Integers.Int.unsigned (Floats.Float32.toBits n)).toNat
    p s!"\tmovss\t{S.label lbl}{ripRel}, {freg rd} {S.comment} {float32String n}\n"
  | .Pmovss_fm rd a => p s!"\tmovss\t{ad a}, {freg rd}\n"
  | .Pmovss_mf a r1 => p s!"\tmovss\t{freg r1}, {ad a}\n"
  | .Pfldl_m a => p s!"\tfldl\t{ad a}\n"
  | .Pfstpl_m a => p s!"\tfstpl\t{ad a}\n"
  | .Pflds_m a => p s!"\tflds\t{ad a}\n"
  | .Pfstps_m a => p s!"\tfstps\t{ad a}\n"
  -- Moves with conversion
  | .Pmovb_mr a r1 => p s!"\tmovb\t{ireg8 r1}, {ad a}\n"
  | .Pmovw_mr a r1 => p s!"\tmovw\t{ireg16 r1}, {ad a}\n"
  | .Pmovzb_rr rd r1 => p s!"\tmovzbl\t{ireg8 r1}, {ireg32 rd}\n"
  | .Pmovzb_rm rd a => p s!"\tmovzbl\t{ad a}, {ireg32 rd}\n"
  | .Pmovsb_rr rd r1 => p s!"\tmovsbl\t{ireg8 r1}, {ireg32 rd}\n"
  | .Pmovsb_rm rd a => p s!"\tmovsbl\t{ad a}, {ireg32 rd}\n"
  | .Pmovzw_rr rd r1 => p s!"\tmovzwl\t{ireg16 r1}, {ireg32 rd}\n"
  | .Pmovzw_rm rd a => p s!"\tmovzwl\t{ad a}, {ireg32 rd}\n"
  | .Pmovsw_rr rd r1 => p s!"\tmovswl\t{ireg16 r1}, {ireg32 rd}\n"
  | .Pmovsw_rm rd a => p s!"\tmovswl\t{ad a}, {ireg32 rd}\n"
  | .Pmovzl_rr rd r1 => p s!"\tmovl\t{ireg32 r1}, {ireg32 rd}\n"
  | .Pmovsl_rr rd r1 => p s!"\tmovslq\t{ireg32 r1}, {ireg64 rd}\n"
  | .Pmovls_rr _ => pure ()
  | .Pcvtsd2ss_ff rd r1 => p s!"\tcvtsd2ss {freg r1}, {freg rd}\n"
  | .Pcvtss2sd_ff rd r1 => p s!"\tcvtss2sd {freg r1}, {freg rd}\n"
  | .Pcvttsd2si_rf rd r1 => p s!"\tcvttsd2si {freg r1}, {ireg32 rd}\n"
  | .Pcvtsi2sd_fr rd r1 => p s!"\tcvtsi2sd {ireg32 r1}, {freg rd}\n"
  | .Pcvttss2si_rf rd r1 => p s!"\tcvttss2si {freg r1}, {ireg32 rd}\n"
  | .Pcvtsi2ss_fr rd r1 => p s!"\tcvtsi2ss {ireg32 r1}, {freg rd}\n"
  | .Pcvttsd2sl_rf rd r1 => p s!"\tcvttsd2si {freg r1}, {ireg64 rd}\n"
  | .Pcvtsl2sd_fr rd r1 => p s!"\tcvtsi2sdq {ireg64 r1}, {freg rd}\n"
  | .Pcvttss2sl_rf rd r1 => p s!"\tcvttss2si {freg r1}, {ireg64 rd}\n"
  | .Pcvtsl2ss_fr rd r1 => p s!"\tcvtsi2ssq {ireg64 r1}, {freg rd}\n"
  -- Integer arithmetic and logical operations
  | .Pleal rd a => p s!"\tleal\t{addressing32 S a}, {ireg32 rd}\n"
  | .Pleaq rd a => p s!"\tleaq\t{addressing64 S a}, {ireg64 rd}\n"
  | .Pnegl rd => p s!"\tnegl\t{ireg32 rd}\n"
  | .Pnegq rd => p s!"\tnegq\t{ireg64 rd}\n"
  | .Paddl_ri rd n => p s!"\taddl\t${coqint n}, {ireg32 rd}\n"
  | .Paddq_ri rd n => do p s!"\taddq\t{← intconst64 S n}, {ireg64 rd}\n"
  | .Psubl_rr rd r1 => p s!"\tsubl\t{ireg32 r1}, {ireg32 rd}\n"
  | .Psubq_rr rd r1 => p s!"\tsubq\t{ireg64 r1}, {ireg64 rd}\n"
  | .Pimull_rr rd r1 => p s!"\timull\t{ireg32 r1}, {ireg32 rd}\n"
  | .Pimulq_rr rd r1 => p s!"\timulq\t{ireg64 r1}, {ireg64 rd}\n"
  | .Pimull_ri rd n => p s!"\timull\t${coqint n}, {ireg32 rd}\n"
  | .Pimulq_ri rd n => do p s!"\timulq\t{← intconst64 S n}, {ireg64 rd}\n"
  | .Pimull_r r1 => p s!"\timull\t{ireg32 r1}\n"
  | .Pimulq_r r1 => p s!"\timulq\t{ireg64 r1}\n"
  | .Pmull_r r1 => p s!"\tmull\t{ireg32 r1}\n"
  | .Pmulq_r r1 => p s!"\tmulq\t{ireg64 r1}\n"
  | .Pcltd => p "\tcltd\n"
  | .Pcqto => p "\tcqto\n"
  | .Pdivl r1 => p s!"\tdivl\t{ireg32 r1}\n"
  | .Pdivq r1 => p s!"\tdivq\t{ireg64 r1}\n"
  | .Pidivl r1 => p s!"\tidivl\t{ireg32 r1}\n"
  | .Pidivq r1 => p s!"\tidivq\t{ireg64 r1}\n"
  | .Pandl_rr rd r1 => p s!"\tandl\t{ireg32 r1}, {ireg32 rd}\n"
  | .Pandq_rr rd r1 => p s!"\tandq\t{ireg64 r1}, {ireg64 rd}\n"
  | .Pandl_ri rd n => p s!"\tandl\t${coqint n}, {ireg32 rd}\n"
  | .Pandq_ri rd n => do p s!"\tandq\t{← intconst64 S n}, {ireg64 rd}\n"
  | .Porl_rr rd r1 => p s!"\torl\t{ireg32 r1}, {ireg32 rd}\n"
  | .Porq_rr rd r1 => p s!"\torq\t{ireg64 r1}, {ireg64 rd}\n"
  | .Porl_ri rd n => p s!"\torl\t${coqint n}, {ireg32 rd}\n"
  | .Porq_ri rd n => do p s!"\torq\t{← intconst64 S n}, {ireg64 rd}\n"
  | .Pxorl_r rd => p s!"\txorl\t{ireg32 rd}, {ireg32 rd}\n"
  | .Pxorq_r rd => p s!"\txorq\t{ireg64 rd}, {ireg64 rd}\n"
  | .Pxorl_rr rd r1 => p s!"\txorl\t{ireg32 r1}, {ireg32 rd}\n"
  | .Pxorq_rr rd r1 => p s!"\txorq\t{ireg64 r1}, {ireg64 rd}\n"
  | .Pxorl_ri rd n => p s!"\txorl\t${coqint n}, {ireg32 rd}\n"
  | .Pxorq_ri rd n => do p s!"\txorq\t{← intconst64 S n}, {ireg64 rd}\n"
  | .Pnotl rd => p s!"\tnotl\t{ireg32 rd}\n"
  | .Pnotq rd => p s!"\tnotq\t{ireg64 rd}\n"
  | .Psall_rcl rd => p s!"\tsall\t%cl, {ireg32 rd}\n"
  | .Psalq_rcl rd => p s!"\tsalq\t%cl, {ireg64 rd}\n"
  | .Psall_ri rd n => p s!"\tsall\t${coqint n}, {ireg32 rd}\n"
  | .Psalq_ri rd n => p s!"\tsalq\t${coqint n}, {ireg64 rd}\n"
  | .Pshrl_rcl rd => p s!"\tshrl\t%cl, {ireg32 rd}\n"
  | .Pshrq_rcl rd => p s!"\tshrq\t%cl, {ireg64 rd}\n"
  | .Pshrl_ri rd n => p s!"\tshrl\t${coqint n}, {ireg32 rd}\n"
  | .Pshrq_ri rd n => p s!"\tshrq\t${coqint n}, {ireg64 rd}\n"
  | .Psarl_rcl rd => p s!"\tsarl\t%cl, {ireg32 rd}\n"
  | .Psarq_rcl rd => p s!"\tsarq\t%cl, {ireg64 rd}\n"
  | .Psarl_ri rd n => p s!"\tsarl\t${coqint n}, {ireg32 rd}\n"
  | .Psarq_ri rd n => p s!"\tsarq\t${coqint n}, {ireg64 rd}\n"
  | .Pshld_ri rd r1 n => p s!"\tshldl\t${coqint n}, {ireg32 r1}, {ireg32 rd}\n"
  | .Prorl_ri rd n => p s!"\trorl\t${coqint n}, {ireg32 rd}\n"
  | .Prorq_ri rd n => p s!"\trorq\t${coqint n}, {ireg64 rd}\n"
  | .Pcmpl_rr r1 r2 => p s!"\tcmpl\t{ireg32 r2}, {ireg32 r1}\n"
  | .Pcmpq_rr r1 r2 => p s!"\tcmpq\t{ireg64 r2}, {ireg64 r1}\n"
  | .Pcmpl_ri r1 n => p s!"\tcmpl\t${coqint n}, {ireg32 r1}\n"
  | .Pcmpq_ri r1 n => do p s!"\tcmpq\t{← intconst64 S n}, {ireg64 r1}\n"
  | .Ptestl_rr r1 r2 => p s!"\ttestl\t{ireg32 r2}, {ireg32 r1}\n"
  | .Ptestq_rr r1 r2 => p s!"\ttestq\t{ireg64 r2}, {ireg64 r1}\n"
  | .Ptestl_ri r1 n => p s!"\ttestl\t${coqint n}, {ireg32 r1}\n"
  -- as in OCaml (`testl` with 64-bit operands)
  | .Ptestq_ri r1 n => do p s!"\ttestl\t{← intconst64 S n}, {ireg64 r1}\n"
  | .Pcmov c rd r1 => p s!"\tcmov{nameOfCondition c}\t{ireg r1}, {ireg rd}\n"
  | .Psetcc c rd => do
    p s!"\tset{nameOfCondition c}\t{ireg8 rd}\n"
    p s!"\tmovzbl\t{ireg8 rd}, {ireg32 rd}\n"
  -- Floating-point arithmetic
  | .Paddd_ff rd r1 => p s!"\taddsd\t{freg r1}, {freg rd}\n"
  | .Psubd_ff rd r1 => p s!"\tsubsd\t{freg r1}, {freg rd}\n"
  | .Pmuld_ff rd r1 => p s!"\tmulsd\t{freg r1}, {freg rd}\n"
  | .Pdivd_ff rd r1 => p s!"\tdivsd\t{freg r1}, {freg rd}\n"
  | .Pnegd rd => do
    modify fun st => { st with needMasks := true }
    p s!"\txorpd\t{S.rawSymbol "__negd_mask"}{ripRel}, {freg rd}\n"
  | .Pabsd rd => do
    modify fun st => { st with needMasks := true }
    p s!"\tandpd\t{S.rawSymbol "__absd_mask"}{ripRel}, {freg rd}\n"
  | .Pcomisd_ff r1 r2 => p s!"\tcomisd\t{freg r2}, {freg r1}\n"
  | .Pxorpd_f rd => p s!"\txorpd\t{freg rd}, {freg rd}\n"
  | .Padds_ff rd r1 => p s!"\taddss\t{freg r1}, {freg rd}\n"
  | .Psubs_ff rd r1 => p s!"\tsubss\t{freg r1}, {freg rd}\n"
  | .Pmuls_ff rd r1 => p s!"\tmulss\t{freg r1}, {freg rd}\n"
  | .Pdivs_ff rd r1 => p s!"\tdivss\t{freg r1}, {freg rd}\n"
  | .Pnegs rd => do
    modify fun st => { st with needMasks := true }
    p s!"\txorpd\t{S.rawSymbol "__negs_mask"}{ripRel}, {freg rd}\n"
  | .Pabss rd => do
    modify fun st => { st with needMasks := true }
    p s!"\tandpd\t{S.rawSymbol "__abss_mask"}{ripRel}, {freg rd}\n"
  | .Pcomiss_ff r1 r2 => p s!"\tcomiss\t{freg r2}, {freg r1}\n"
  | .Pxorps_f rd => p s!"\txorpd\t{freg rd}, {freg rd}\n"
  -- Branches and calls
  | .Pjmp_l l => do p s!"\tjmp\t{S.label (← translLabel l)}\n"
  | .Pjmp_s f _ => p s!"\tjmp\t{S.symbolFunction f}\n"
  | .Pjmp_r r _ => p s!"\tjmp\t*{ireg r}\n"
  | .Pjcc c l => do p s!"\tj{nameOfCondition c}\t{S.label (← translLabel l)}\n"
  | .Pjcc2 c1 c2 l => do
    let l ← translLabel l
    let l' ← newLabel
    p s!"\tj{nameOfNegCondition c1}\t{S.label l'}\n"
    p s!"\tj{nameOfCondition c2}\t{S.label l}\n"
    p s!"{S.label l'}:\n"
  | .Pjmptbl r tbl => do
    let l ← newLabel
    addJumptable l tbl
    let (tmp1, tmp2) : Ireg × Ireg := if r = .RAX then (.RDX, .RAX) else (.RAX, .RDX)
    p s!"\tleaq\t{S.label l}(%rip), {ireg tmp1}\n"
    -- normalize r to 32-bit unsigned
    p s!"\tmovl\t{ireg32 r}, {ireg32 tmp2}\n"
    p s!"\tmovslq\t({ireg tmp1}, {ireg tmp2}, 4), {ireg tmp2}\n"
    p s!"\taddq\t{ireg tmp2}, {ireg tmp1}\n"
    p s!"\tjmp\t*{ireg tmp1}\n"
  | .Pcall_s f _ => p s!"\tcall\t{S.symbolFunction f}\n"
  | .Pcall_r r _ => p s!"\tcall\t*{ireg r}\n"
  | .Pret => p "\tret\n"
  -- Instructions produced by Asmexpand
  | .Padcl_ri rd n => p s!"  \tadcl\t${coqint n}, {ireg32 rd}\n"
  | .Padcl_rr rd a1 => p s!"  \tadcl\t{ireg32 a1}, {ireg32 rd}\n"
  | .Paddl_rr rd a1 => p s!"\taddl\t{ireg32 a1}, {ireg32 rd}\n"
  | .Paddl_mi a n => p s!"\taddl\t${coqint n}, {ad a}\n"
  | .Pbsfl rd a1 => p s!"\tbsfl\t{ireg32 a1}, {ireg32 rd}\n"
  | .Pbsfq rd a1 => p s!"\tbsfq\t{ireg64 a1}, {ireg64 rd}\n"
  | .Pbsrl rd a1 => p s!"\tbsrl\t{ireg32 a1}, {ireg32 rd}\n"
  | .Pbsrq rd a1 => p s!"\tbsrq\t{ireg64 a1}, {ireg64 rd}\n"
  | .Pbswap64 rd => p s!"\tbswap\t{ireg64 rd}\n"
  | .Pbswap32 rd => p s!"\tbswap\t{ireg32 rd}\n"
  | .Pbswap16 rd => p s!"\trolw\t$8, {ireg16 rd}\n"
  | .Pcfi_adjust sz => cfiAdjust cfi (Integers.Int.signed sz)
  | .Pfmadd132 rd a1 a2 => p s!"\tvfmadd132sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfmadd213 rd a1 a2 => p s!"\tvfmadd213sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfmadd231 rd a1 a2 => p s!"\tvfmadd231sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfmsub132 rd a1 a2 => p s!"\tvfmsub132sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfmsub213 rd a1 a2 => p s!"\tvfmsub213sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfmsub231 rd a1 a2 => p s!"\tvfmsub231sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfnmadd132 rd a1 a2 => p s!"\tvfnmadd132sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfnmadd213 rd a1 a2 => p s!"\tvfnmadd213sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfnmadd231 rd a1 a2 => p s!"\tvfnmadd231sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfnmsub132 rd a1 a2 => p s!"\tvfnmsub132sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfnmsub213 rd a1 a2 => p s!"\tvfnmsub213sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pfnmsub231 rd a1 a2 => p s!"\tvfnmsub231sd\t{freg a2}, {freg a1}, {freg rd}\n"
  | .Pmaxsd rd a1 => p s!"\tmaxsd\t{freg a1}, {freg rd}\n"
  | .Pminsd rd a1 => p s!"\tminsd\t{freg a1}, {freg rd}\n"
  | .Pmovb_rm rd a => p s!"\tmovb\t{ad a}, {ireg8 rd}\n"
  | .Pmovq_rf rd r1 => p s!"\tmovq\t{freg r1}, {ireg64 rd}\n"
  | .Pmovsq_mr a rs => p s!"\tmovq\t{freg rs}, {ad a}\n"
  | .Pmovsq_rm rd a => p s!"\tmovq\t{ad a}, {freg rd}\n"
  | .Pmovsb => p "\tmovsb\n"
  | .Pmovsw => p "\tmovsw\n"
  | .Pmovw_rm rd a => p s!"\tmovw\t{ad a}, {ireg16 rd}\n"
  | .Pnop => p "\tnop\n"
  | .Prep_movsl => p "\trep\tmovsl\n"
  | .Psbbl_rr rd a1 => p s!"\tsbbl\t{ireg32 a1}, {ireg32 rd}\n"
  | .Psqrtsd rd a1 => p s!"\tsqrtsd\t{freg a1}, {freg rd}\n"
  | .Psubl_ri rd n => p s!"\tsubl\t${coqint n}, {ireg32 rd}\n"
  | .Psubq_ri rd n => do p s!"\tsubq\t{← intconst64 S n}, {ireg64 rd}\n"
  -- Pseudo-instructions
  | .Plabel l => do p s!"{S.label (← translLabel l)}:\n"
  | .Pallocframe _ _ _ | .Pfreeframe _ _ _ =>
    fail "Pallocframe/Pfreeframe must be expanded by Asmexpand"
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_annot kind txt _ =>
      match kind.toNat with
      | 1 => p s!"{S.comment} annotation: {quoteString (annotText pregAnnot "esp" txt args)}\n"
      | 2 => do
        let lbl ← newLabel
        p s!"{S.label lbl}:\n"
        addAisAnnot lbl pregAisAnnot "rsp" txt args
      | _ => fail "print_instruction: bad annotation kind"
    | .EF_debug kind txt _ =>
      printDebugInfo S.comment pregAnnot "%esp" kind.toNat (Camlcoq.externAtom txt) args
    | .EF_inline_asm txt sg _ => do
      p s!"{S.comment} begin inline assembly\n\t"
      printInlineAsm pregAsm txt sg args res
      p s!"{S.comment} end inline assembly\n"
    | _ => fail "print_instruction: builtin not expanded"

/-- `Target.print_jumptable` -/
def printJumptable (jmptbl : SectionName) : M Unit := do
  let jts := (← get).jumptables
  if !jts.isEmpty then
    printSection S jmptbl
    S.printAlign 4
    for (lbl, tbl) in jts do
      out s!"{S.label lbl}:"
      for l in tbl do
        out s!"\t.long\t{S.label (← translLabel l)} - {S.label lbl}\n"
    modify fun st => { st with jumptables := [] }

/-- `Target.print_epilogue` -/
def printEpilogue : M Unit := do
  if (← get).needMasks then
    printSection S (.Section_literal 16)
    S.printAlign 16
    out s!"{S.rawSymbol "__negd_mask"}:\t.quad   0x8000000000000000, 0\n"
    out s!"{S.rawSymbol "__absd_mask"}:\t.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n"
    out s!"{S.rawSymbol "__negs_mask"}:\t.long   0x80000000, 0, 0, 0\n"
    out s!"{S.rawSymbol "__abss_mask"}:\t.long   0x7FFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF\n"
  S.printEpilogue

/-- `TargetPrinter.Target(System)`: the target printer for system `S`.
    `isStatic` is `C2C.atom_is_static` (used by `print_comm_symb`) and `cfi`
    is `Configuration.asm_supports_cfi`. -/
def target (isStatic : Ident → Bool) (cfi : Bool := true) : PrintAsm.Target Asm.Function where
  printPrologue := modify fun st => { st with needMasks := false }
  printEpilogue := printEpilogue S
  printAlign := S.printAlign
  printCommSymb sz name align :=
    if isStatic name then S.printLcommDecl name sz align else S.printCommDecl name sz align
  printVarInfo := S.printVarInfo
  printFunInfo := S.printFunInfo
  printOptionalFunInfo := pure ()
  printInstructions fn := do
    modify fun st => { st with currentFunctionSig := fn.fn_sig }
    for i in fn.fn_code do printInstruction S cfi i
  printJumptable := printJumptable S
  printSection := printSection S
  nameOfSection := S.nameOfSection
  comment := S.comment
  symbol := S.symbol
  defaultFalignment := 16
  label := S.label
  address := ".quad"
  bigEndian := false
  cfi := cfi
  system := S.system

end Target

/-- `TargetPrinter.sel_target`: the system printer for
    `Configuration.system` (`"linux"`, `"bsd"`, `"macos"` or `"cygwin"`). -/
def selSystem (system : String) (symbolIsRelocatable : Ident → Bool := fun _ => false) :
    Except String System :=
  match system with
  | "linux" => .ok (elfSystem symbolIsRelocatable)
  | "bsd" => .ok { elfSystem symbolIsRelocatable with system := "bsd" }
  | "macos" => .ok macosSystem
  | "cygwin" => .ok cygwinSystem
  | _ => .error s!"System {system} not supported"

end TargetPrinter
end X86
end CC
