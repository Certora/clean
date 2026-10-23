/-
  Port of `driver/Frontend.ml`: the front-end functions common to `ccomp`
  and `clightgen` — preprocessing (by an external C preprocessor), parsing
  and elaboration (`Parse.preprocessed_file`), and the translation to
  CompCert C (`C2C.convertProgram`).

  Differences from OCaml:
  * The flags are the explicit value `Clflags.Flags`, and the
    target-dependent parameters of `C2C` (`C2C.Target`) and the machine
    configuration (`Machine.config`, set by `init` from
    `Configuration.arch`/`model`/`abi`) are explicit arguments.
  * `init` returns the initial environment with the builtins (OCaml's
    global `Env.set_builtins C2C.builtins`), which `parse_c_file` takes as
    argument.
  * `parse_c_file` reads the preprocessed text as a `ByteArray` and also
    returns the table of atoms built by `C2C` (`C2C.decl_atom`).
  * `preprocess` returns the preprocessed text and uses a fixed GCC
    command; the driver uses `preprocessFile`, which follows OCaml
    (`Configuration.prepro`, output to a file or to standard output).
  * `machine_of_config` is the choice of `Machine.config` made by OCaml's
    `init` from the configuration.
  * The command-line option tables (`prepro_actions`,
    `gnu_prepro_actions`) and help texts run in the driver monad
    `Driveraux.DM`.
  * The `-dparse`/`-dc` dumps are done by the driver
    (`Driver.compile_c_file`); `Debug.init_compile_unit` is not called
    (the debug hooks are not wired into the driver yet).
-/
import CCLib.cparser.Parse
import CCLib.cfrontend.C2C
import CCLib.driver.Driveraux

namespace CC
namespace Frontend

open CParser (M)

/-- `Version.version` -/
def version : String := "3.17"

/-- Split the version number into major.minor -/
def v_major_minor : Nat × Nat :=
  match version.splitOn "." with
  | a :: b :: _ => (a.toNat!, b.toNat!)
  | _ => (0, 0)

def v_number : Nat := 100 * v_major_minor.1 + v_major_minor.2

/-- Predefined macros: version numbers, C11 features -/
def predefined_macros : List String := [
  "-D__COMPCERT__",
  s!"-D__COMPCERT_MAJOR__={v_major_minor.1}",
  s!"-D__COMPCERT_MINOR__={v_major_minor.2}",
  s!"-D__COMPCERT_VERSION__={v_number}",
  "-U__STDC_IEC_559_COMPLEX__",
  "-D__STDC_NO_ATOMICS__",
  "-D__STDC_NO_COMPLEX__",
  "-D__STDC_NO_THREADS__",
  "-D__STDC_NO_VLA__" ]

/-- We define the type wchar_t since it is dependent on the system and we
    want to avoid more ifdefs in the stddef header file. -/
def abi_macros (cfg : CParser.Machine.T) : List String :=
  [s!"-D__COMPCERT_WCHAR_TYPE__={CParser.Cprint.name_of_ikind cfg.wchar_ikind}"]

/-- The preprocessor command, `Configuration.prepro` (with
    `Configuration.gnu_toolchain`): GCC's preprocessor.  The GNU predefined
    macros `__GNUC__`/`__GNUC_MINOR__` are undefined so that system headers
    do not use GCC-only extensions. -/
def prepro : List String := ["gcc", "-E", "-U__GNUC__", "-U__GNUC_MINOR__"]

/-- `preprocess ifile`: run the C preprocessor on `ifile` and return its
    output. -/
def preprocess (flags : Clflags.Flags) (cfg : CParser.Machine.T) (ifile : String) :
    IO String := do
  let cmd := prepro ++ ["-std=" ++ flags.option_std] ++ predefined_macros ++ abi_macros cfg ++
    (if flags.use_standard_headers && flags.stdlib_path != "" then
      ["-I" ++ flags.stdlib_path ++ "/include"] else []) ++
    flags.prepro_options.reverse ++ [ifile]
  let out ← IO.Process.output { cmd := cmd.head!, args := cmd.tail.toArray }
  if out.exitCode != 0 then
    throw (IO.userError s!"Error during preprocessor (exit code {out.exitCode}):\n{out.stderr}")
  return out.stdout

/-- `init ()`: set the machine configuration, the builtins and the known
    attributes.  Returns the initial environment of the elaborator. -/
def init (cfg : CParser.Machine.T) (tgt : C2C.Target) : M CParser.Env.InitEnv := do
  modify fun s => { s with config := cfg }
  let i ← CParser.Env.set_builtins (C2C.builtins tgt)
  CParser.Cutil.declare_attributes C2C.attributes
  return i

/-- From preprocessed C to Csyntax: `parse_c_file sourcename ifile`. -/
def parse_c_file (flags : Clflags.Flags) (tgt : C2C.Target) (initEnv : CParser.Env.InitEnv)
    (sourcename : String) (text : ByteArray) :
    M (Csyntax.Program × List (Nat × C2C.AtomInfo)) := do
  -- Parsing and production of a simplified C AST
  let ast ← CParser.Parse.preprocessed_file
    { unblock := true
      switch_norm := if flags.option_funstructured_switch then .Full else .Partial
      struct_passing := flags.option_fstruct_passing
      packed_structs := flags.option_fpacked_structs
      option_g := flags.option_g
      option_interp := flags.option_interp
      option_Obranchless := flags.option_Obranchless }
    initEnv sourcename text
  -- Conversion to Csyntax
  C2C.convertProgram flags tgt initEnv ast

/-- Run a front-end computation, returning its result (or `none` after a
    fatal error) and the diagnostics it printed. -/
def runM {α} (x : M α) (st : CParser.State := {}) : Option α × Array String :=
  match x.run st with
  | .ok a s => (some a, s.messages)
  | .error _ s => (none, s.messages)

/-! ### The driver part of `Frontend.ml` -/

open Commandline Driveraux

/-- The machine configuration selected by `init` from
    `Configuration.arch`/`model`/`abi`/`system`. -/
def machine_of_config (c : Configuration.Config) : CParser.Machine.T :=
  match c.arch with
  | "powerpc" =>
    if c.model == "e5500" || c.model == "ppc64" then
      if c.abi == "linux" then CParser.Machine.ppc_32_r64_linux_bigendian
      else if c.gnu_toolchain then CParser.Machine.ppc_32_r64_bigendian
      else CParser.Machine.ppc_32_r64_diab_bigendian
    else if c.abi == "linux" then CParser.Machine.ppc_32_linux_bigendian
    else if c.gnu_toolchain then CParser.Machine.ppc_32_bigendian
    else CParser.Machine.ppc_32_diab_bigendian
  | "arm" => if c.is_big_endian then CParser.Machine.arm_bigendian else CParser.Machine.arm_littleendian
  | "x86" =>
    if c.model == "64" then CParser.Machine.x86_64
    else if c.abi == "macos" then CParser.Machine.x86_32_macos
    else if c.system == "bsd" then CParser.Machine.x86_32_bsd
    else CParser.Machine.x86_32
  | "riscV" => if c.model == "64" then CParser.Machine.rv64 else CParser.Machine.rv32
  | "aarch64" => if c.abi == "apple" then CParser.Machine.aarch64_apple else CParser.Machine.aarch64
  | _ => CParser.Machine.undef

/-- `preprocess ifile ofile`: run the preprocessor of the configuration on
    `ifile`, writing to `ofile` (`"-"`: standard output). -/
def preprocessFile (ifile ofile : String) : DM Unit := do
  runFront CParser.Diagnostics.raise_on_errors
  let cfg ← getConfig
  let fl ← getFlags
  let output := if ofile == "-" then none else some ofile
  let cmd := cfg.prepro ++
    (if cfg.gnu_toolchain then ["-std=" ++ fl.option_std] else []) ++
    predefined_macros ++ abi_macros (machine_of_config cfg) ++
    (if fl.use_standard_headers then ["-I" ++ Configuration.concat fl.stdlib_path "include"] else []) ++
    fl.prepro_options.reverse ++ [ifile]
  let exc ← command cmd output
  if exc != 0 then
    if ofile != "-" then safe_remove ofile
    command_error "preprocessor" exc

private def addPrepro (opts : List String) : DM Unit :=
  modifyFlags fun f => { f with prepro_options := opts ++ f.prepro_options }

/-- `gnu_prepro_opt_key key s` -/
def gnu_prepro_opt_key (key s : String) : DM Unit := addPrepro [s, key]
/-- `gnu_prepro_opt s` -/
def gnu_prepro_opt (s : String) : DM Unit := addPrepro [s]
/-- `gnu_prepro_opt_e s`: add the option and the implicit `-E` -/
def gnu_prepro_opt_e (s : String) : DM Unit := do
  addPrepro [s]
  modifyFlags fun f => { f with option_E := true }

/-- `gnu_prepro_actions` -/
def gnu_prepro_actions : List (Pattern × Action DM) :=
  [ (.Exact "-M", .Self gnu_prepro_opt_e),
    (.Exact "-MM", .Self gnu_prepro_opt_e),
    (.Exact "-MF", .String (gnu_prepro_opt_key "-MF")),
    (.Exact "-MG", .Self gnu_prepro_opt),
    (.Exact "-MP", .Self gnu_prepro_opt),
    (.Exact "-MT", .String (gnu_prepro_opt_key "-MT")),
    (.Exact "-MQ", .String (gnu_prepro_opt_key "-MQ")),
    (.Exact "-MD", .Self gnu_prepro_opt),
    (.Exact "-MMD", .Self gnu_prepro_opt),
    (.Exact "-nostdinc", .Self fun s => do
      gnu_prepro_opt s
      modifyFlags fun f => { f with use_standard_headers := false }),
    (.Exact "-imacros", .String (gnu_prepro_opt_key "-imacros")),
    (.Exact "-idirafter", .String (gnu_prepro_opt_key "-idirafter")),
    (.Exact "-isystem", .String (gnu_prepro_opt_key "-isystem")),
    (.Exact "-iquote", .String (gnu_prepro_opt_key "-iquote")),
    (.Exact "-P", .Self gnu_prepro_opt),
    (.Exact "-C", .Self gnu_prepro_opt),
    (.Exact "-CC", .Self gnu_prepro_opt),
    (.Prefix "-finput-charset=", .Self gnu_prepro_opt) ]

/-- `prepro_actions` -/
def prepro_actions (cfg : Configuration.Config) : List (Pattern × Action DM) :=
  [ (.Exact "-I", .String fun s => modifyFlags fun f =>
      { f with prepro_options := s :: "-I" :: f.prepro_options,
               assembler_options := s :: "-I" :: f.assembler_options }),
    (.Prefix "-I", .Self fun s => modifyFlags fun f =>
      { f with prepro_options := s :: f.prepro_options,
               assembler_options := s :: f.assembler_options }),
    (.Exact "-D", .String fun s => addPrepro [s, "-D"]),
    (.Prefix "-D", .Self fun s => addPrepro [s]),
    (.Exact "-U", .String fun s => addPrepro [s, "-U"]),
    (.Prefix "-U", .Self fun s => addPrepro [s]),
    (.Prefix "-Wp,", .Self fun s => addPrepro (explode_comma_option s).reverse),
    (.Exact "-Xpreprocessor", .String fun s => addPrepro [s]),
    (.Exact "-include", .String fun s => addPrepro [s, "-include"]) ] ++
  (if cfg.gnu_toolchain then gnu_prepro_actions else [])

/-- `gnu_prepro_help` -/
def gnu_prepro_help : String :=
"  -M            Output a rule suitable for make describing the
                 dependencies of the main source file
  -MM            Like -M but do not mention system header files
  -MD            Like -M but writes output to a .d file as a side-
                 effect of compilation
  -MMD           Like -MD but do not mention system header files
  -MF <file>     Specifies file <file> as output file for -M or -MM
  -MG            Assumes missing header files are generated for -M
  -MP            Add a phony target for each dependency other than
                 the main file
  -MT <target>   Change the target of the rule emitted by dependency
                 generation
  -MQ <target>   Like -MT but quotes <target>
  -nostdinc      Do not search the standard system directories for
                 header files
  -imacros <file> Like -include but throws output produced by
                  preprocessing of <file> away
  -idirafter <dir> Search <dir> for header files after all directories
                   specified with -I and the standard system directories
  -isystem <dir>  Search <dir> for header files after all directories
                  specified by -I but before the standard system directories
  -iquote <dir>   Like -isystem but only for headers included with
                  quotes
  -P              Do not generate linemarkers
  -C              Do not discard comments
  -CC             Do not discard comments, including during macro
                  expansion
  -finput-charset=<charset>
                  Set the input character set, used for reading source files.
"

/-- `prepro_help` -/
def prepro_help (cfg : Configuration.Config) : String :=
"Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -include <file> Process <file> as if #include \"<file>\" appears at the first
                  line of the primary source file.
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
  -Wp,<opt>      Pass option <opt> to the preprocessor
  -Xpreprocessor <opt> Pass option <opt> to the preprocessor
" ++ (if cfg.gnu_toolchain then gnu_prepro_help else "")

end Frontend
end CC
