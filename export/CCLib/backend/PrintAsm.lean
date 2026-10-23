/-
  Printing assembly code — port of `backend/PrintAsm.ml`.

  `PrintAsm.ml` is a functor over the target printer (`PrintAsmaux.TARGET`).
  Here the target printer is the structure `PrintAsm.Target F`, generic in
  the type `F` of the target's `Asm` functions, and `PrintAsm.printProgram`
  plays the role of `print_program`.

  The OCaml printer reads properties of global symbols from the C front end
  (`C2C.atom_is_static`, `atom_sections`, `atom_alignof`, `atom_literal`,
  `atom_is_iso_inline_definition`).  The Lean port has no `C2C` (the C
  elaborator is not ported), so these are the fields of a structure
  `AtomInfo`; `AtomInfo.ofProgram` derives them from the program itself: a
  symbol is static when it is not in `prog_public`, a variable goes to the
  section given by `Sections.forVariable` (read-only or not, classified by
  its initializer), and alignments default to 8, as in `print_var`.

  Ported: `splitlong`, `emit_constants`, `get_section_names`,
  `print_function`, `print_init`, `print_init_data`, `print_var`,
  `print_globdef`, `print_program`.

  Not ported: the printing of debug information (`-g`: the calls of the
  `Debug` hooks and of `DwarfPrinter` — both ported in `debug/` — from the
  `DebugPrinter` submodule, `print_debug_label`, `print_location`).
  `print_ais_annot` prints the aiT annotations recorded by the target
  printers (`PrintAsmaux.addAisAnnot`, module `AisAnnot`).  String
  literals are printed with `.byte` like other data (OCaml prints the
  initializers of literals recognized by `C2C.atom_literal` with `.ascii`;
  the bytes are the same).
-/
import CCLib.backend.PrintAsmaux
import CCLib.backend.Cminor

namespace CC
namespace PrintAsm

open Sections PrintAsmaux

/-- The properties of global symbols that the OCaml printer obtains from
    `C2C`. -/
structure AtomInfo where
  /-- `C2C.atom_is_static` -/
  isStatic : Ident → Bool
  /-- `C2C.atom_sections`: `[text; literal; jumptable]` for a function,
      `[section]` for a variable, `[]` if unknown -/
  sections : Ident → List SectionName
  /-- `C2C.atom_alignof` -/
  alignof : Ident → Option Nat := fun _ => none
  /-- `C2C.atom_is_iso_inline_definition` -/
  isIsoInlineDefinition : Ident → Bool := fun _ => false

/-- The atom information of a program, without the C front end: see the
    header. -/
def AtomInfo.ofProgram {F V : Type} (p : ASTProgram F V) : AtomInfo where
  isStatic id := !(p.prog_public.contains id)
  sections id :=
    match p.prog_defs.lookup id with
    | some (.Gvar v) => [forVariable v.gvar_readonly v.gvar_init]
    | some (.Gfun _) =>
      let (t, l, j) := forFunction
      [t, l, j]
    | none => []

/-- `PrintAsmaux.TARGET` -/
structure Target (F : Type) where
  printPrologue : M Unit
  printEpilogue : M Unit
  printAlign : Nat → M Unit
  printCommSymb : Int → Ident → Nat → M Unit
  printVarInfo : Ident → M Unit
  printFunInfo : Ident → M Unit
  printOptionalFunInfo : M Unit
  printInstructions : F → M Unit
  printJumptable : SectionName → M Unit
  printSection : SectionName → M Unit
  nameOfSection : SectionName → String
  comment : String
  symbol : Ident → String
  defaultFalignment : Nat
  label : Nat → String
  address : String
  /-- `Archi.big_endian` -/
  bigEndian : Bool := false
  /-- `Configuration.asm_supports_cfi` -/
  cfi : Bool := true
  /-- `Configuration.system` -/
  system : String := "linux"
  /-- `Archi.ptr64` (size of the addresses in the aiT annotations) -/
  ptr64 : Bool := true

variable {F : Type} (T : Target F) (info : AtomInfo)

/-- `PrintAsm.splitlong`: the two 32-bit halves of a 64-bit number, in
    memory order. -/
def splitlong (b : Nat) : Nat × Nat :=
  if T.bigEndian then (b / 2 ^ 32 % 2 ^ 32, b % 2 ^ 32) else (b % 2 ^ 32, b / 2 ^ 32 % 2 ^ 32)

/-- `PrintAsm.emit_constants` -/
def emitConstants (lit : SectionName) : M Unit := do
  let st ← get
  if st.literal64.size > 0 then
    T.printSection (withSize 8 lit)
    T.printAlign 8
    for (n, lbl) in st.literal64 do
      let (hi, lo) := splitlong T n
      out s!"{T.label lbl}:\t.long\t0x{hex hi}, 0x{hex lo}\n"
  if st.literal32.size > 0 then
    T.printSection (withSize 4 lit)
    T.printAlign 4
    for (n, lbl) in st.literal32 do
      out s!"{T.label lbl}:\t.long\t0x{hex n}\n"
  resetLiterals

/-- `PrintAsm.get_section_names` -/
def getSectionNames (name : Ident) : SectionName × SectionName × SectionName :=
  match info.sections name with
  | [t, l, j] => (t, l, j)
  | _ => (.Section_text, .Section_literal 0, .Section_jumptable)

/-- `PrintAsm.print_function` -/
def printFunction (name : Ident) (fn : F) : M Unit := do
  clearFunctionLabels
  let (text, lit, jmptbl) := getSectionNames info name
  T.printSection text
  T.printAlign T.defaultFalignment
  if !info.isStatic name then out s!"\t.globl {T.symbol name}\n"
  T.printOptionalFunInfo
  out s!"{T.symbol name}:\n"
  cfiStartproc T.cfi
  T.printInstructions fn
  cfiEndproc T.cfi
  T.printFunInfo name
  emitConstants T lit
  T.printJumptable jmptbl

/-- `PrintAsm.print_init` -/
def printInit : InitData → M Unit
  | .Init_int8 n => out s!"\t.byte\t{coqint n}\n"
  | .Init_int16 n => out s!"\t.short\t{coqint n}\n"
  | .Init_int32 n => out s!"\t.long\t{coqint n}\n"
  | .Init_int64 n =>
    let (hi, lo) := splitlong T (Integers.Int64.unsigned n).toNat
    out s!"\t.long\t0x{hex hi}, 0x{hex lo}\n"
  | .Init_float32 n =>
    out s!"\t.long\t0x{hex (Integers.Int.unsigned (Floats.Float32.toBits n)).toNat} {T.comment} {float32String n}\n"
  | .Init_float64 n =>
    let (hi, lo) := splitlong T (Integers.Int64.unsigned (Floats.Float.toBits n)).toNat
    out s!"\t.long\t0x{hex hi}, 0x{hex lo} {T.comment} {floatString n}\n"
  | .Init_space n => if n > 0 then out s!"\t.space\t{n}\n" else pure ()
  | .Init_addrof symb ofs =>
    let o := Integers.Int64.signed (Integers.Int64.repr (Integers.Ptrofs.unsigned ofs))
    out s!"\t{T.address}\t{T.symbol symb}{if o ≠ 0 then s!" + {o}" else ""}\n"

/-- `PrintAsm.print_init_data` -/
def printInitData (il : List InitData) : M Unit :=
  for i in il do printInit T i

/-- `PrintAsm.print_var` -/
def printVar {V : Type} (name : Ident) (v : GlobVar V) : M Unit := do
  match v.gvar_init with
  | [] => pure ()
  | _ =>
    let sec := match info.sections name with
      | [s] => s
      | _ => .Section_data .Init
    let align := (info.alignof name).getD 8
    let nameSec := T.nameOfSection sec
    if nameSec ≠ "COMM" then
      out s!"\t{nameSec}\n"
      T.printAlign align
      if !info.isStatic name then out s!"\t.globl\t{T.symbol name}\n"
      out s!"{T.symbol name}:\n"
      printInitData T v.gvar_init
      T.printVarInfo name
    else
      match v.gvar_init with
      | [.Init_space sz] => T.printCommSymb sz name align
      | _ => fail "print_var: common symbol with an initializer"

/-- `PrintAsm.print_globdef` -/
def printGlobdef {V : Type} : Ident × GlobDef (ASTFundef F) V → M Unit
  | (name, .Gfun (.Internal code)) =>
    if !info.isIsoInlineDefinition name then printFunction T info name code else pure ()
  | (_, .Gfun (.External _)) => pure ()
  | (name, .Gvar v) => printVar T info name v

/-- `PrintAsm.print_ais_annot`: the section of the recorded aiT
    annotations. -/
def printAisAnnot : M Unit := do
  let annots ← getAisAnnots
  if !annots.isEmpty then
    T.printSection .Section_ais_annotation
    let printAddr (addr : String) : M Unit := do
      out s!"\t.byte 7,{if T.ptr64 then 8 else 4}\n"
      out s!"\t{T.address} {addr}\n"
    for annot in annots do
      for part in annot do
        match part with
        | .Label lbl => printAddr (T.label lbl)
        | .Symbol symb => printAddr (T.symbol symb)
        | .String a => out s!"\t.ascii {quoteString a}\n"

/-- `PrintAsm.print_program` -/
def printProgramM {V : Type} (p : ASTProgram (ASTFundef F) V) : M Unit := do
  printVersionAndOptions T.comment
  T.printPrologue
  for d in p.prog_defs do printGlobdef T info d
  T.printEpilogue
  printAisAnnot T
  printNonexecStackNote T.system

/-- `PrintAsm.print_program`, returning the assembly text.  The atom
    information defaults to `AtomInfo.ofProgram p`. -/
def printProgram {V : Type} (p : ASTProgram (ASTFundef F) V)
    (info : AtomInfo := AtomInfo.ofProgram p) : Except String String :=
  run (printProgramM T info p)

end PrintAsm
end CC
