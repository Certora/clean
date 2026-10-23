/-
  Port of `driver/Driveraux.ml`: auxiliary functions of the compiler
  driver — temporary files, invocation of external tools, names of output
  files, recording of the actions to perform on the input files — and the
  driver monad `DM` in which they run.

  Differences from OCaml:
  * OCaml's global state (the references of `Clflags`, `Driveraux.actions`,
    `Timing.timers`, the files to remove `at_exit`, the configuration and
    the state of the front end's `Diagnostics`) is the state `DState` of
    the monad `DM := StateRefT DState (ExceptT Stop IO)`.  As with OCaml's
    references, the state is kept when an exception is raised.
  * The exceptions that stop the driver (`Commandline.CmdError`,
    `Diagnostics.Abort`, `exit n`) are the values of `Stop`.
  * The messages that the front end (`CParser.M`) prints are collected in
    its state; `runFront` runs a front-end computation and writes them to
    standard error.
  * `actions` records which processing function to apply to a file
    (`FileAction`), not a closure; the driver interprets it.
  * `command ?stdout args`: when the output goes to a file, the standard
    output of the tool is read by the driver and written to the file.
  * `print_error` (printing of `Errors.errmsg`) is not needed: the
    verified compiler's errors are strings in the Lean port.
-/
import CCLib.driver.Configuration
import CCLib.driver.Clflags
import CCLib.lib.Commandline
import CCLib.cparser.Env

namespace CC
namespace Driveraux

/-- The ways the driver stops. -/
inductive Stop where
  /-- `Commandline.CmdError msg` -/
  | CmdError (msg : String)
  /-- `Diagnostics.Abort` -/
  | Abort
  /-- `exit n` -/
  | Exit (n : UInt32)
  deriving Inhabited

/-- The processing of an input file recorded by `push_action`. -/
inductive FileAction where
  | process_c_file
  | process_i_file
  | process_s_file
  | process_S_file
  | process_h_file
  /-- `push_linker_arg`: the file is passed to the linker -/
  | linker_arg
  deriving BEq, Inhabited, Repr

/-- `Interp.mode`: how the reference interpreter chooses among the
    possible reductions (`-random`, `-all`). -/
inductive InterpMode where
  | First | Random | All
  deriving BEq, Repr, Inhabited

/-- The state of the driver. -/
structure DState where
  /-- `Commandline.argv` (with the response files expanded) -/
  argv : Array String := #[]
  /-- the configuration (`Configuration`) -/
  config : Configuration.Config := Configuration.x86_64_linux
  /-- the flags (`Clflags`) -/
  flags : Clflags.Flags := {}
  /-- the state of the front end (`Diagnostics`, `Machine.config`, …) -/
  diag : CParser.State := {}
  /-- `actions`, most recent first -/
  actions : List (FileAction × String) := []
  /-- the number of source files on the command line -/
  num_source_files : Nat := 0
  /-- the number of input files on the command line -/
  num_input_files : Nat := 0
  /-- the temporary files to remove at exit -/
  tmp_files : List String := []
  /-- `Timing.timers` -/
  timers : List (String × Float) := []
  /-- `Driver.sdump_suffix` (option `-sdump-suffix`) -/
  sdump_suffix : String := ".json"
  /-- `Interp.trace`: verbosity of the reference interpreter (0: `-quiet`,
      2: `-trace`) -/
  interp_trace : Nat := 1
  /-- `Interp.mode` -/
  interp_mode : InterpMode := .First
  deriving Inhabited

/-- The driver monad. -/
abbrev DM := StateRefT DState (ExceptT Stop IO)

/-- Run an `IO` action. -/
def io {α} (x : IO α) : DM α := liftM x

def getFlags : DM Clflags.Flags := return (← get).flags
def getConfig : DM Configuration.Config := return (← get).config
def modifyFlags (f : Clflags.Flags → Clflags.Flags) : DM Unit :=
  modify fun st => { st with flags := f st.flags }

/-- Run a front-end computation; the messages it prints are written to
    standard error.  `Diagnostics.Abort` becomes `Stop.Abort`. -/
def runFront {α} (x : CParser.M α) : DM α := do
  let st ← get
  let r := x.run { st.diag with messages := #[] }
  let (res, s) : Except CParser.Exn α × CParser.State := match r with
    | .ok a s => (.ok a, s)
    | .error e s => (.error e, s)
  set { st with diag := { s with messages := #[] } }
  for m in s.messages do io (IO.eprintln m)
  match res with
  | .ok a => return a
  | .error .Abort => throwThe Stop .Abort
  | .error (.EnvError e) =>
    io (IO.eprintln s!"internal error: {CParser.Env.error_message e}")
    throwThe Stop .Abort
  | .error .Not_found =>
    io (IO.eprintln "internal error: Not_found")
    throwThe Stop .Abort
  | .error (.Failure msg) =>
    io (IO.eprintln s!"internal error: {msg}")
    throwThe Stop .Abort

/-- `Diagnostics.error no_loc msg` -/
def error (msg : String) : DM Unit :=
  runFront (CParser.Diagnostics.error CParser.Diagnostics.no_loc msg)

/-- `Diagnostics.warning no_loc Unnamed msg` -/
def warning (msg : String) : DM Unit :=
  runFront (CParser.Diagnostics.warning CParser.Diagnostics.no_loc .Unnamed msg)

/-- `Diagnostics.fatal_error no_loc msg` -/
def fatal_error {α} (msg : String) : DM α :=
  runFront (CParser.Diagnostics.fatal_error CParser.Diagnostics.no_loc msg)

/-! ### Temporary files -/

/-- Safe removal of files -/
def safe_remove (file : String) : DM Unit :=
  io (try IO.FS.removeFile file catch _ => pure ())

/-- `tmp_file suff`: a fresh temporary file name ending in `suff`, removed
    at exit (`remove_tmp_files`). -/
def tmp_file (suff : String) : DM String := do
  let (_, p) ← io IO.FS.createTempFile
  let name := p.toString ++ suff
  io (IO.FS.writeFile name "")
  safe_remove p.toString
  modify fun st => { st with tmp_files := name :: st.tmp_files }
  return name

/-- Remove the temporary files (OCaml: `at_exit`). -/
def remove_tmp_files : DM Unit := do
  for f in (← get).tmp_files do safe_remove f
  modify fun st => { st with tmp_files := [] }

/-! ### Invocation of external tools -/

/-- `command stdout args` (without response files): the exit code of the
    command, or `-1` if it could not be run. -/
def command_raw (args : List String) (stdout : Option String) : DM Int := do
  match args with
  | [] => fatal_error "assertion failed in Driveraux.command"
  | cmd :: rest =>
    let r ← io (try
        match stdout with
        | none =>
          let child ← IO.Process.spawn { cmd, args := rest.toArray }
          pure (Except.ok (← child.wait))
        | some f =>
          let child ← IO.Process.spawn
            { cmd, args := rest.toArray, stdout := .piped, stderr := .inherit }
          let out ← child.stdout.readToEnd
          let rc ← child.wait
          IO.FS.writeFile f out
          pure (Except.ok rc)
      catch e => pure (Except.error (toString e)))
    match r with
    | .ok rc => return Int.ofNat rc.toNat
    | .error msg =>
      error s!"executing '{cmd}': {msg}"
      return -1

/-- `command ?stdout args` -/
def command (args : List String) (stdout : Option String := none) : DM Int := do
  if (← getFlags).option_v then
    let out := match stdout with | none => "" | some f => s!" > {f}"
    io (IO.eprintln s!"+ {" ".intercalate args}{out}")
  let cfg ← getConfig
  let resp := System.Platform.isWindows && cfg.response_file_style != .Unsupported
  if resp && args.foldl (fun len arg => len + arg.length + 1) 0 > 7000 then
    let (quote, prefix_) := match cfg.response_file_style with
      | .Diab => (Responsefile.diab_quote, "-@")
      | _ => (Responsefile.gnu_quote, "@")
    match args with
    | [] => fatal_error "assertion failed in Driveraux.command"
    | cmd :: args =>
      let file ← tmp_file ""
      io (IO.FS.writeFile file (String.join (args.map fun a => quote a ++ " ")))
      let ret ← command_raw [cmd, prefix_ ++ file] stdout
      safe_remove file
      return ret
  else command_raw args stdout

/-- `command_error n exc` -/
def command_error {α} (n : String) (exc : Int) : DM α :=
  fatal_error s!"{n} command failed with exit code {exc} (use -v to see invocation)\n"

/-! ### Names of output files -/

/-- `Filename.basename file` -/
def basename (file : String) : String :=
  let cs := (file.toList.reverse.dropWhile (· == '/')).reverse
  if cs.isEmpty then (if file.isEmpty then "" else "/")
  else String.ofList (cs.reverse.takeWhile (· != '/')).reverse

/-- `Filename.remove_extension file` -/
def remove_extension (file : String) : String :=
  let base := basename file
  -- the extension is the part of the base name after its last dot, if
  -- that dot is not the first character of the base name
  match (base.toList.reverse.dropWhile (· != '.')) with
  | [] | ['.'] => file
  | _ :: _ =>
    let extLen := (base.toList.reverse.takeWhile (· != '.')).length + 1
    (file.dropEnd extLen).toString

/-- Determine names for output files.  We use -o option if specified and if
    this is the final destination file (not a dump file).  Otherwise, we
    generate a file in the current directory. -/
def output_filename (source_file suffix : String) (final : Bool := false) : DM String := do
  match (← getFlags).option_o with
  | some file => if final then return file else return basename (remove_extension source_file) ++ suffix
  | none => return basename (remove_extension source_file) ++ suffix

/-- A variant of `output_filename` where the default output name is fixed -/
def output_filename_default (default_file : String) : DM String := do
  return (← getFlags).option_o.getD default_file

/-- All input files should exist -/
def ensure_inputfile_exists (name : String) : DM Unit := do
  if !(← io (System.FilePath.pathExists name)) then
    fatal_error s!"no such file or directory: '{name}'"

/-! ### Command-line parsing -/

/-- `explode_comma_option s`: the comma-separated words after the first
    (`Str.split` drops empty words). -/
def explode_comma_option (s : String) : List String :=
  match (s.splitOn ",").filter (· != "") with
  | [] => []
  | _ :: tl => tl

/-- `Commandline.parse_cmdline spec`, on the command line `argv`. -/
def parse_cmdline (spec : List (Commandline.Pattern × Commandline.Action DM))
    (argv : Array String) : DM Unit :=
  Commandline.parse_array (fun msg => throwThe Stop (.CmdError msg)) spec argv 1 (argv.size - 1)

/-- `Commandline.longopt_int key f` in the driver monad -/
def longopt_int (key : String) (f : Int → DM Unit) :
    Commandline.Pattern × Commandline.Action DM :=
  Commandline.longopt_int (fun msg => throwThe Stop (.CmdError msg)) key f

/-! ### Record actions to be performed after parsing the command line -/

def push_action (fn : FileAction) (arg : String) : DM Unit :=
  modify fun st => { st with actions := (fn, arg) :: st.actions }

def push_linker_arg (arg : String) : DM Unit := push_action .linker_arg arg

end Driveraux
end CC
