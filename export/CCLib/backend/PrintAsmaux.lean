/-
  Auxiliary functions for printing assembly code — port of
  `backend/PrintAsmaux.ml`.

  The OCaml printers write to an `out_channel` and keep their state (label
  renaming, literal pools, jump tables, …) in global references and hash
  tables shared between `PrintAsm` and the target's `TargetPrinter`.  Here the
  output buffer and that state are a single record `PrintAsmaux.State`, and
  printing functions live in the monad `PrintAsmaux.M` (a state monad over
  `Except String`; the OCaml printers fail with `assert false` or
  `invalid_arg`).

  Ported: label renaming (`new_label`, `transl_label`, `elf_label`), literal
  pools (`label_literal32`, `label_literal64`, `iter_literal32/64`,
  `reset_literals`), `jumptables`, `current_function_stacksize`,
  `current_function_sig`, `elf_symbol`, `elf_symbol_offset`,
  `elf_print_fun_info`, `elf_print_var_info`, the `.cfi` directives,
  `coqint`, `coqint64`, `ptrofs`, `annot_arg`, `annot_text`,
  `print_debug_info` (except line numbers, see below), `print_asm_argument`,
  `builtin_arg_of_res`, `print_inline_asm`, `quote_string`,
  `quote_argument`, `print_version_and_options`, `variable_section`,
  `elf_mergeable_literal_section`, `elf_mergeable_string_section`,
  `macos_mergeable_literal_section`, `macos_mergeable_string_section`,
  `print_nonexec_stack_note`.  The module type `TARGET` is the structure
  `Target` of `CCLib/backend/PrintAsm.lean`.

  Differences:
  * Strings are formatted directly instead of through `Printf`.  Floating
    point numbers appear only in comments (`%.18g` in OCaml); they are
    printed with Lean's `Float.toString`.
  * `print_debug_info` ignores line-number annotations (kind 1), which need
    the `Fileinfo` module and `-g`.
  * `print_version_and_options` has no command line to print.
-/
import CCLib.common.Sections
import CCLib.lib.Camlcoq
import CCLib.common.Memdata
import CCLib.backend.AisAnnot

namespace CC
namespace PrintAsmaux

open Sections

/-- The state of the printers. -/
structure State where
  /-- the text printed so far, in pieces -/
  out : Array String := #[]
  /-- `next_label` -/
  nextLabel : Nat := 100
  /-- `current_function_labels` -/
  fnLabels : List (Positive × Nat) := []
  /-- `literal32_labels`, in order of creation -/
  literal32 : Array (Nat × Nat) := #[]
  /-- `literal64_labels`, in order of creation -/
  literal64 : Array (Nat × Nat) := #[]
  /-- `jumptables` (most recent first, as in OCaml) -/
  jumptables : List (Nat × List Positive) := []
  /-- `current_function_stacksize` -/
  currentFunctionStacksize : Int := 0
  /-- `current_function_sig` -/
  currentFunctionSig : Signature := { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }
  /-- x86 `TargetPrinter.need_masks` (the masks for `abs` and `neg`) -/
  needMasks : Bool := false
  /-- Cygwin `indirect_symbols` (x86 `TargetPrinter`) -/
  indirectSymbols : List String := []
  /-- `AisAnnot.ais_annot_list`: the recorded aiT annotations, most recent
      first -/
  aisAnnots : List (List AisAnnot.T) := []
  /-- warnings emitted while printing (`Wrong_ais_parameter`) -/
  warnings : Array AisAnnot.Warning := #[]

/-- The printing monad. -/
abbrev M := StateT State (Except String)

/-- `output_string oc s` -/
def out (s : String) : M Unit := modify fun st => { st with out := st.out.push s }

/-- `assert false` / `invalid_arg` -/
def fail {α : Type} (msg : String) : M α := throw msg

/-- Run a printer and return the printed text. -/
def run (p : M Unit) (st : State := {}) : Except String String :=
  match (p.run st) with
  | .ok ((), st') => .ok (String.join st'.out.toList)
  | .error e => .error e

/-! ## On-the-fly label renaming -/

/-- `PrintAsmaux.new_label` -/
def newLabel : M Nat := do
  let st ← get
  set { st with nextLabel := st.nextLabel + 1 }
  return st.nextLabel

/-- `PrintAsmaux.transl_label` -/
def translLabel (lbl : Positive) : M Nat := do
  match (← get).fnLabels.lookup lbl with
  | some l => return l
  | none =>
    let l ← newLabel
    modify fun st => { st with fnLabels := (lbl, l) :: st.fnLabels }
    return l

/-- Forget the labels of the previous function
    (`Hashtbl.clear current_function_labels`). -/
def clearFunctionLabels : M Unit := modify fun st => { st with fnLabels := [] }

/-- `PrintAsmaux.elf_label` -/
def elfLabel (lbl : Nat) : String := s!".L{lbl}"

/-! ## Literals and jump tables -/

/-- `PrintAsmaux.label_literal32` (the key is the bit pattern, as an
    unsigned number) -/
def labelLiteral32 (n : Nat) : M Nat := do
  match (← get).literal32.find? (·.1 == n) with
  | some (_, l) => return l
  | none =>
    let l ← newLabel
    modify fun st => { st with literal32 := st.literal32.push (n, l) }
    return l

/-- `PrintAsmaux.label_literal64` -/
def labelLiteral64 (n : Nat) : M Nat := do
  match (← get).literal64.find? (·.1 == n) with
  | some (_, l) => return l
  | none =>
    let l ← newLabel
    modify fun st => { st with literal64 := st.literal64.push (n, l) }
    return l

/-- `PrintAsmaux.reset_literals` -/
def resetLiterals : M Unit := modify fun st => { st with literal32 := #[], literal64 := #[] }

/-- Record a jump table (`jumptables := (l, tbl) :: !jumptables`). -/
def addJumptable (l : Nat) (tbl : List Positive) : M Unit :=
  modify fun st => { st with jumptables := (l, tbl) :: st.jumptables }

/-! ## Numbers -/

/-- Lower-case hexadecimal digits of a natural number (`%x`). -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- `PrintAsmaux.coqint`: a 32-bit integer, signed (`%ld`). -/
def coqint (n : Integers.Int) : String := toString (Integers.Int.signed n)

/-- `PrintAsmaux.coqint64`: a 64-bit integer, signed (`%Ld`). -/
def coqint64 (n : Integers.Int64) : String := toString (Integers.Int64.signed n)

/-- `PrintAsmaux.ptrofs` (`%Ld` of `camlint64_of_ptrofs`). -/
def ptrofs (n : Integers.Ptrofs) : String :=
  toString (Integers.Int64.signed (Integers.Int64.repr (Integers.Ptrofs.unsigned n)))

/-- A 64-bit float, for comments (`%.18g` of `camlfloat_of_coqfloat`). -/
def floatString (f : Floats.Float) : String :=
  toString (Float.ofBits (UInt64.ofNat (Integers.Int64.unsigned (Floats.Float.toBits f)).toNat))

/-- A 32-bit float, for comments (`%.18g` of `camlfloat_of_coqfloat32`). -/
def float32String (f : Floats.Float32) : String :=
  toString (Float32.ofBits (UInt32.ofNat (Integers.Int.unsigned (Floats.Float32.toBits f)).toNat))

/-! ## Symbols -/

/-- `PrintAsmaux.elf_symbol` -/
def elfSymbol (symb : Ident) : String := Camlcoq.externAtom symb

/-- `PrintAsmaux.elf_symbol_offset` -/
def elfSymbolOffset (symb : Ident) (ofs : Integers.Ptrofs) : String :=
  let o := Integers.Int64.signed (Integers.Int64.repr (Integers.Ptrofs.unsigned ofs))
  elfSymbol symb ++ (if o ≠ 0 then s!" + {o}" else "")

/-- `PrintAsmaux.elf_print_fun_info` -/
def elfPrintFunInfo (name : Ident) : M Unit := do
  out s!"\t.type\t{elfSymbol name}, @function\n"
  out s!"\t.size\t{elfSymbol name}, . - {elfSymbol name}\n"

/-- `PrintAsmaux.elf_print_var_info` -/
def elfPrintVarInfo (name : Ident) : M Unit := do
  out s!"\t.type\t{elfSymbol name}, @object\n"
  out s!"\t.size\t{elfSymbol name}, . - {elfSymbol name}\n"

/-! ## `.cfi` directives

`Configuration.asm_supports_cfi` is an argument. -/

/-- `PrintAsmaux.cfi_startproc` -/
def cfiStartproc (cfi : Bool) : M Unit := if cfi then out "\t.cfi_startproc\n" else pure ()
/-- `PrintAsmaux.cfi_endproc` -/
def cfiEndproc (cfi : Bool) : M Unit := if cfi then out "\t.cfi_endproc\n" else pure ()
/-- `PrintAsmaux.cfi_adjust` -/
def cfiAdjust (cfi : Bool) (delta : Int) : M Unit :=
  if cfi then out s!"\t.cfi_adjust_cfa_offset\t{delta}\n" else pure ()
/-- `PrintAsmaux.cfi_rel_offset` -/
def cfiRelOffset (cfi : Bool) (reg : String) (ofs : Int) : M Unit :=
  if cfi then out s!"\t.cfi_rel_offset\t{reg}, {ofs}\n" else pure ()
/-- `PrintAsmaux.cfi_section` -/
def cfiSection (cfi : Bool) : M Unit := if cfi then out "\t.cfi_sections\t.debug_frame\n" else pure ()

/-! ## Annotations (`__builtin_annot`) -/

/-- `PrintAsmaux.annot_arg` -/
def annotArg {A : Type} (pregString : A → String) (spRegName : String) : BuiltinArg A → String
  | .BA x => pregString x
  | .BA_int n => coqint n
  | .BA_long n => coqint64 n
  | .BA_float n => floatString n
  | .BA_single n => float32String n
  | .BA_loadstack chunk ofs =>
    s!"mem({spRegName} + {ptrofs ofs}, {sizeChunk chunk})"
  | .BA_addrstack ofs => s!"({spRegName} + {ptrofs ofs})"
  | .BA_loadglobal chunk id ofs =>
    s!"mem(\"{Camlcoq.externAtom id}\" + {ptrofs ofs}, {sizeChunk chunk})"
  | .BA_addrglobal id ofs => s!"(\"{Camlcoq.externAtom id}\" + {ptrofs ofs})"
  | .BA_splitlong hi lo =>
    s!"({annotArg pregString spRegName hi} * 0x100000000 + {annotArg pregString spRegName lo})"
  | .BA_addptr a1 a2 =>
    s!"({annotArg pregString spRegName a1} + {annotArg pregString spRegName a2})"

/-- A fragment of an annotation or inline-assembly text: literal text, or a
    parameter `%N` (with an optional modifier `Q`/`R` for inline assembly);
    `%%` is the literal text `%`. -/
inductive Fragment where
  | text (s : String)
  | param (modifier : String) (n : Nat)

/-- Split `txt` at the parameters `%N` (`allowMod`: also `%QN`, `%RN`; and
    `%0` is a parameter only when `allowMod`, as in the regular expressions
    `%%|%[1-9][0-9]*` and `%%|%[QR]?[0-9]+`). -/
def splitParams (allowMod : Bool) (txt : String) : List Fragment :=
  let rec digits : List Char → List Char × List Char
    | c :: cs => if c.isDigit then let (d, r) := digits cs; (c :: d, r) else ([], c :: cs)
    | [] => ([], [])
  let rec go (fuel : Nat) (acc : List Char) (cs : List Char) : List Fragment :=
    let flush := if acc.isEmpty then [] else [Fragment.text (String.ofList acc.reverse)]
    match fuel with
    | 0 => flush
    | fuel + 1 =>
      match cs with
      | [] => flush
      | '%' :: '%' :: rest => go fuel ('%' :: acc) rest
      | '%' :: rest =>
        let (modifier, rest') := match rest with
          | 'Q' :: r => if allowMod then ("Q", r) else ("", rest)
          | 'R' :: r => if allowMod then ("R", r) else ("", rest)
          | _ => ("", rest)
        let (d, rest'') := digits rest'
        let ok := !d.isEmpty && (allowMod || d.head? != some '0')
        if ok then
          flush ++ Fragment.param modifier (String.ofList d).toNat! :: go fuel [] rest''
        else go fuel ('%' :: acc) rest
      | c :: rest => go fuel (c :: acc) rest
  go (txt.length + 1) [] txt.toList

/-- `PrintAsmaux.annot_text` -/
def annotText {A : Type} (pregString : A → String) (spRegName : String) (txt : String)
    (args : List (BuiltinArg A)) : String :=
  String.join <| (splitParams false txt).map fun
    | .text s => s
    | .param _ n =>
      match args[n - 1]? with
      | some a => annotArg pregString spRegName a
      | none => s!"<bad parameter %{n}>"

/-- `AisAnnot.add_ais_annot`: record the aiT annotation of label `lbl`
    (a `Wrong_ais_parameter` warning is recorded in `warnings`). -/
def addAisAnnot {A : Type} (lbl : Nat) (pregString : A → String) (spRegName : String)
    (txt : String) (args : List (BuiltinArg A)) : M Unit := do
  match AisAnnot.aisAnnotTxt true lbl pregString spRegName txt args with
  | .error e => fail e
  | .ok (annot, w) =>
    if let some w := w then modify fun st => { st with warnings := st.warnings.push w }
    if !annot.isEmpty then modify fun st => { st with aisAnnots := annot :: st.aisAnnots }

/-- `AisAnnot.get_ais_annots`: the recorded annotations, in order, and reset
    the list. -/
def getAisAnnots : M (List (List AisAnnot.T)) := do
  let annots := (← get).aisAnnots
  modify fun st => { st with aisAnnots := [] }
  return annots.reverse

/-- `PrintAsmaux.print_debug_info` (line numbers, kind 1, are ignored: see
    the header) -/
def printDebugInfo {A : Type} (comment : String) (pregString : A → String) (spName : String)
    (kind : Nat) (txt : String) (args : List (BuiltinArg A)) : M Unit :=
  let debugArgs := String.join (args.map fun a => " " ++ annotArg pregString spName a)
  match kind with
  | 3 => out s!"{comment} debug: start live range {txt} ={debugArgs}\n"
  | 4 => out s!"{comment} debug: end live range {txt}\n"
  | 5 => out s!"{comment} debug: {txt} resides at{debugArgs}\n"
  | 6 => out s!"{comment} debug: current scopes{debugArgs}\n"
  | _ => pure ()

/-! ## Inline assembly -/

/-- `PrintAsmaux.print_asm_argument` -/
def printAsmArgument {A : Type} (printPreg : ATyp → A → M Unit) (modifier : String) (typ : ATyp) :
    BuiltinArg A → M Unit
  | .BA r => printPreg typ r
  | .BA_splitlong (.BA hi) (.BA lo) =>
    match modifier with
    | "R" => printPreg .Tint hi
    | "Q" => printPreg .Tint lo
    | _ => do printPreg .Tint hi; out ":"; printPreg .Tint lo
  | _ => fail "bad asm argument"

/-- `PrintAsmaux.builtin_arg_of_res` -/
def builtinArgOfRes {A : Type} : BuiltinRes A → M (BuiltinArg A)
  | .BR r => return .BA r
  | .BR_splitlong (.BR hi) (.BR lo) => return .BA_splitlong (.BA hi) (.BA lo)
  | _ => fail "builtin_arg_of_res"

/-- `PrintAsmaux.print_inline_asm` -/
def printInlineAsm {A : Type} (printPreg : ATyp → A → M Unit) (txt : String) (sg : Signature)
    (args : List (BuiltinArg A)) (res : BuiltinRes A) : M Unit := do
  let (operands, tyOperands) ← match sg.sig_res with
    | .Xvoid => pure (args, sg.sig_args.map XType.proj)
    | tres => do
      let r ← builtinArgOfRes res
      pure (r :: args, tres.proj :: sg.sig_args.map XType.proj)
  for f in splitParams true txt do
    match f with
    | .text s => out s
    | .param modifier n =>
      match tyOperands[n]?, operands[n]? with
      | some ty, some a => printAsmArgument printPreg modifier ty a
      | _, _ => out s!"<bad parameter %{modifier}{n}>"
  out "\n"

/-! ## Strings -/

/-- Three octal digits. -/
def octal3 (n : Nat) : String :=
  String.ofList [Char.ofNat (48 + n / 64 % 8), Char.ofNat (48 + n / 8 % 8), Char.ofNat (48 + n % 8)]

/-- `PrintAsmaux.quote_string` -/
def quoteString (s : String) : String :=
  let body := s.toList.map fun c =>
    if c = '"' || c = '\\' then String.ofList ['\\', c]
    else if c = '\n' then "\\n"
    else if c = '\t' then "\\t"
    else if c.toNat < 0x20 then "\\" ++ octal3 c.toNat
    else c.toString
  "\"" ++ String.join body ++ "\""

/-- `PrintAsmaux.quote_argument` -/
def quoteArgument (s : String) : String :=
  if s.toList.any (fun c => c.toNat < 0x20 || c = ' ' || c = '"') then quoteString s else s

/-- `PrintAsmaux.print_version_and_options` -/
def printVersionAndOptions (comment : String) (version : String := "3.17") : M Unit := do
  out s!"{comment} File generated by CompCert {version} (Lean port)\n"
  out s!"{comment} Command line:\n"

/-! ## Sections -/

/-- `PrintAsmaux.variable_section` (`common` defaults to
    `Clflags.option_fcommon`, which is `true` by default). -/
def variableSection (sec : String) (bss reloc : Option String := none) (common : Bool := true)
    (i : Initialized) : String :=
  match i with
  | .Uninit => if common then "COMM" else bss.getD sec
  | .Init => sec
  | .Init_reloc => reloc.getD sec

/-- `PrintAsmaux.elf_mergeable_literal_section` -/
def elfMergeableLiteralSection (sz : Nat) (sec : String) : String :=
  if sz = 4 || sz = 8 || sz = 16 then s!"{sec}.cst{sz},\"aM\",@progbits,{sz}" else sec

/-- `PrintAsmaux.elf_mergeable_string_section` -/
def elfMergeableStringSection (sz : Nat) (sec : String) : String :=
  if sz = 1 || sz = 2 || sz = 4 then s!"{sec}.str{sz}.{sz},\"aMS\",@progbits,{sz}" else sec

/-- `PrintAsmaux.macos_mergeable_literal_section` -/
def macosMergeableLiteralSection (sz : Nat) : String :=
  if sz = 4 || sz = 8 || sz = 16 then s!".literal{sz}" else ".const"

/-- `PrintAsmaux.macos_mergeable_string_section` -/
def macosMergeableStringSection (sz : Nat) : String :=
  if sz = 1 then ".cstring" else ".const"

/-- `PrintAsmaux.print_nonexec_stack_note` (`Configuration.system` is an
    argument) -/
def printNonexecStackNote (system : String) : M Unit :=
  if system = "linux" || system = "bsd" then
    out "\n\t.section .note.GNU-stack,\"\",%progbits\n"
  else pure ()

#guard quoteString "a\"b\\c\n\x01" = "\"a\\\"b\\\\c\\n\\001\""
#guard annotText (fun (n : Nat) => s!"r{n}") "sp" "x=%1, y=%2, %% %3"
    [.BA 4, .BA_int (Integers.Int.repr 7)] = "x=r4, y=7, % <bad parameter %3>"
#guard hex 255 = "ff"

end PrintAsmaux
end CC
