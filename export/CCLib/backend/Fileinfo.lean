/-
  Port of `backend/Fileinfo.ml`: the source-file information of the assembly
  printers (`-g`): numbering the source files for the `.file` directives,
  the `.loc` (GNU) and `.d2line` (Diab) line directives, and, with `-S` /
  `-dasm`, the source line itself as an assembly comment
  (`CCLib.lib.Printlines`).

  Differences from OCaml: the global hash table `filename_info` and the
  reference `last_file` are a `State` threaded through `StateT State IO`;
  the command-line flags (`option_g`, `option_S || option_dasm`) are
  arguments; the functions return the text to print instead of writing to an
  output channel.
-/
import CCLib.lib.Printlines
import CCLib.backend.PrintAsmaux

namespace CC
namespace Fileinfo

/-- `filename_info` and `last_file`. -/
structure State where
  /-- each source file seen so far: its number and, if kept, its contents -/
  files : List (String × Nat × Option Printlines.FileBuf) := []
  lastFile : String := ""

/-- `reset_filenames` (also `close_filenames`: there is no channel to close). -/
def State.reset : State := {}

/-- `enter_filename`: number the file `f`, reading its contents if the source
    is to be printed (`keepSource` = `option_S || option_dasm`). -/
def enterFilename (keepSource : Bool) (f : String) :
    StateT State IO (Nat × Option Printlines.FileBuf) := do
  let st ← get
  let num := st.files.length + 1
  let fb ← if keepSource then
      (try some <$> Printlines.FileBuf.openFile f catch _ => pure none : IO _)
    else pure none
  set { st with files := st.files ++ [(f, num, fb)] }
  return (num, fb)

/-- `print_file`: the number of `file`, and its `.file` directive if it is
    new. -/
def printFile (keepSource : Bool) (file : String) :
    StateT State IO (String × Nat × Option Printlines.FileBuf) := do
  match (← get).files.find? (·.1 == file) with
  | some (_, num, fb) => return ("", num, fb)
  | none =>
    let (num, fb) ← enterFilename keepSource file
    return (s!"\t.file\t{num} {PrintAsmaux.quoteString file}\n", num, fb)

/-- `print_file_line`: GNU-style DWARF2 location of `file:line`, followed by
    the source line prefixed by `pref`. -/
def printFileLine (optionG keepSource : Bool) (pref file : String) (line : Nat) :
    StateT State IO String := do
  if optionG && file != "" then
    let (out, num, fb) ← printFile keepSource file
    let src := match fb with
      | none => ""
      | some b => Printlines.copy pref b line line
    return out ++ s!"\t.loc\t{num} {line}\n" ++ src
  else return ""

/-- `print_file_line_d2`: Diab-style DWARF2 location of `file:line`. -/
def printFileLineD2 (optionG keepSource : Bool) (pref file : String) (line : Nat) :
    StateT State IO String := do
  if optionG && file != "" then
    let fb ← match (← get).files.find? (·.1 == file) with
      | some (_, _, fb) => pure fb
      | none => do let r ← enterFilename keepSource file; pure r.2
    let st ← get
    let out := if file != st.lastFile then s!"\t.d2file\t{PrintAsmaux.quoteString file}\n" else ""
    set { st with lastFile := file }
    let src := match fb with
      | none => ""
      | some b => Printlines.copy pref b line line
    return out ++ s!"\t.d2line\t{line}\n" ++ src
  else return ""

end Fileinfo
end CC
