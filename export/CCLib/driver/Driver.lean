/-
  From a program to AArch64 assembly text — the part of `driver/Driver.ml`
  that turns a CompCert C (or Clight) program into an assembly file:

    `Compiler.transf_c_program` → `Asmexpand.expand_program` →
    `PrintAsm.print_program`.

  As for `driver/Compiler.lean`, the target of these functions is AArch64;
  the x86-64 version is `x86/Driver.lean`.

  The second part of the file is the command-line driver of `Driver.ml`
  (the program `ccomp`): option table, processing of `.c`, `.i`, `.s`,
  `.S`, `.h` files, preprocessing, assembling and linking through the
  external tools of the configuration (`Configuration.lean`).  It is
  generic in the target: a `Target` record supplies the parameters of the
  front end (`C2C.Target`), the back end (verified compiler, `Asmexpand`,
  printer) and the reference interpreter (`-interp`).  `x86/Driver.lean`
  instantiates it for x86-64; the executable is `ccomp`
  (`export/examples/CComp.lean`).

  Differences from OCaml:
  * the dumps `-dclight`, `-dcminor`, `-drtl`, `-dltl`, `-dalloctrace`,
    `-dmach` and `-sdump` are accepted but produce no file (the verified
    compiler is run as a whole); `-dparse`, `-dc`, `-dprepro` and `-dasm`
    work;
  * debugging information (`-g`) is not generated: the collection,
    generation and printing are ported (`debug/`), but the driver does not
    install the hooks (see `debug/DebugInit.lean`);
  * the Gc settings and back-traces of OCaml have no equivalent.
-/
import CCLib.extraction.extraction
import CCLib.aarch64.Asmexpand
import CCLib.aarch64.TargetPrinter
import CCLib.aarch64.CBuiltins
import CCLib.aarch64.Machregsaux
import CCLib.driver.Frontend
import CCLib.driver.CommonOptions
import CCLib.driver.Timing
import CCLib.driver.Assembler
import CCLib.driver.Linker
import CCLib.debug.DebugInit
import CCLib.cfrontend.PrintCsyntax
import CCLib.driver.Interp

namespace CC
namespace Driver

/-- Print an `Asm` program (after `Asmexpand`) for `Configuration.system`
    (`"linux"` or `"macos"`). -/
def printAsm (system : String) (p : Asm.Program) : Res String :=
  match TargetPrinter.selSystem system with
  | .error e => .Error e
  | .ok S =>
    let info := PrintAsm.AtomInfo.ofProgram p
    match PrintAsm.printProgram (TargetPrinter.target S info.isStatic) p info with
    | .ok s => .OK s
    | .error e => .Error e

/-- The target settings for a system: Apple's ABI on macOS. -/
def targetFor (system : String) : ExtractionMachdep.Target :=
  { abi := if system = "macos" then "apple" else "standard" }

/-- Expand and print an `Asm` program produced by the verified compiler. -/
def asmToText (t : ExtractionMachdep.Target) (system : String) (p : Asm.Program) : Res String :=
  match Asmexpand.expandProgram (ExtractionMachdep.abi t.abi) p with
  | .Error e => .Error e
  | .OK p' => printAsm system p'

/-- Compile a CompCert C program to assembly text. -/
def compileCProgram (p : Csyntax.Program) (system : String := "linux") : Res String :=
  let t := targetFor system
  match Compiler.transfCProgram (Extraction.configFor t) p with
  | .Error e => .Error e
  | .OK tp => asmToText t system tp

/-- Compile a Clight program to assembly text. -/
def compileClightProgram (p : Program) (system : String := "linux") : Res String :=
  let t := targetFor system
  match Compiler.transfClightProgram (Extraction.configFor t) p with
  | .Error e => .Error e
  | .OK tp => asmToText t system tp


/-! ## The command-line driver -/

open Commandline Driveraux

/-- What the driver needs to know about the target. -/
structure Target where
  /-- the parameters of `C2C` for a configuration -/
  c2c : Configuration.Config → C2C.Target
  /-- from CompCert C to assembly text: `Compiler.transf_c_program`,
      `Asmexpand.expand_program`, `PrintAsm.print_program`; the atom table
      of `C2C` gives the properties of symbols -/
  backend : Clflags.Flags → Configuration.Config → Csyntax.Program →
    List (Nat × C2C.AtomInfo) → Except String String
  /-- the reference interpreter (`Interp.execute`), if available -/
  interp : Option (Csyntax.Program → DM Unit) := none

/-- Name used for version string etc. -/
def tool_name : String := "C verified compiler"

/-- `nolink ()` -/
def nolink : DM Bool := do
  let f ← getFlags
  return f.option_c || f.option_S || f.option_E || f.option_interp

/-- `object_filename sourcename` -/
def object_filename (sourcename : String) : DM String := do
  if ← nolink then output_filename sourcename ".o" (final := (← getFlags).option_c)
  else tmp_file ".o"

/-- `parse_c_file sourcename ifile` (`Frontend.ml`), with the `-dparse` and
    `-dc` dumps. -/
def parse_c_file (tgt : Target) (sourcename ifile : String) :
    DM (Csyntax.Program × List (Nat × C2C.AtomInfo)) := do
  let text ← io (IO.FS.readBinFile ifile)
  let fl ← getFlags
  let cfg ← getConfig
  let ctgt := tgt.c2c cfg
  let machine := Frontend.machine_of_config cfg
  let machine := if fl.option_interp then CParser.Machine.compcert_interpreter machine else machine
  let initEnv ← runFront (Frontend.init machine ctgt)
  let ast ← runFront (CParser.Parse.preprocessed_file
    { unblock := true
      switch_norm := if fl.option_funstructured_switch then .Full else .Partial
      struct_passing := fl.option_fstruct_passing
      packed_structs := fl.option_fpacked_structs
      option_g := fl.option_g
      option_interp := fl.option_interp
      option_Obranchless := fl.option_Obranchless }
    initEnv sourcename text)
  if fl.option_dparse then
    let dest ← output_filename sourcename ".parsed.c"
    io (IO.FS.writeFile dest (CParser.Cprint.toText (CParser.Cprint.program {} ast)))
  let (p, tbl) ← Timing.time "CompCert C generation"
    (runFront (C2C.convertProgram fl ctgt initEnv ast))
  if fl.option_dcmedium then
    let dest ← output_filename sourcename ".compcert.c"
    io (IO.FS.writeFile dest (PrintCsyntax.printProgram p))
  return (p, tbl)

/-- `compile_c_file sourcename ifile ofile`: from preprocessed C to an
    assembly file. -/
def compile_c_file (tgt : Target) (sourcename ifile ofile : String) : DM Unit := do
  let (p, tbl) ← parse_c_file tgt sourcename ifile
  match tgt.backend (← getFlags) (← getConfig) p tbl with
  | .ok asm => io (IO.FS.writeFile ofile asm)
  | .error msg =>
    runFront (CParser.Diagnostics.fatal_error (CParser.Diagnostics.file_loc sourcename) msg)

/-- `compile_i_file sourcename preproname` -/
def compile_i_file (tgt : Target) (sourcename preproname : String) : DM String := do
  let fl ← getFlags
  if fl.option_interp then
    let (p, _) ← parse_c_file tgt sourcename preproname
    match tgt.interp with
    | some run => run p
    | none => fatal_error "the reference interpreter is not available for this target"
    return ""
  else if fl.option_S then
    compile_c_file tgt sourcename preproname (← output_filename sourcename ".s" (final := true))
    return ""
  else
    let asmname ← if fl.option_dasm then output_filename sourcename ".s" else tmp_file ".s"
    compile_c_file tgt sourcename preproname asmname
    let objname ← object_filename sourcename
    Assembler.assemble asmname objname
    return objname

/-- Processing of a `.c` file -/
def process_c_file (tgt : Target) (sourcename : String) : DM String := do
  ensure_inputfile_exists sourcename
  if (← getFlags).option_E then
    Frontend.preprocessFile sourcename (← output_filename_default "-")
    return ""
  else
    let preproname ← if (← getFlags).option_dprepro then output_filename sourcename ".i"
      else tmp_file ".i"
    Frontend.preprocessFile sourcename preproname
    compile_i_file tgt sourcename preproname

/-- Processing of a `.i` / `.p` file (preprocessed C) -/
def process_i_file (tgt : Target) (sourcename : String) : DM String := do
  ensure_inputfile_exists sourcename
  compile_i_file tgt sourcename sourcename

/-- Processing of `.s` files -/
def process_s_file (sourcename : String) : DM String := do
  ensure_inputfile_exists sourcename
  let objname ← object_filename sourcename
  Assembler.assemble sourcename objname
  return objname

/-- Processing of `.S` and `.sx` files -/
def process_S_file (sourcename : String) : DM String := do
  ensure_inputfile_exists sourcename
  if (← getFlags).option_E then
    Frontend.preprocessFile sourcename (← output_filename_default "-")
    return ""
  else
    let preproname ← tmp_file ".s"
    Frontend.preprocessFile sourcename preproname
    let objname ← object_filename sourcename
    Assembler.assemble preproname objname
    return objname

/-- Processing of `.h` files -/
def process_h_file (sourcename : String) : DM String := do
  if (← getFlags).option_E then
    ensure_inputfile_exists sourcename
    Frontend.preprocessFile sourcename (← output_filename_default "-")
    return ""
  else
    fatal_error s!"input file {sourcename} ignored (not in -E mode)\n"

/-- `perform_actions ()`: process the files in command-line order; the
    results are the arguments of the linker. -/
def perform_actions (tgt : Target) : DM (List String) := do
  let mut res := []
  for (fn, arg) in (← get).actions.reverse do
    let r ← match fn with
      | .process_c_file => process_c_file tgt arg
      | .process_i_file => process_i_file tgt arg
      | .process_s_file => process_s_file arg
      | .process_S_file => process_S_file arg
      | .process_h_file => process_h_file arg
      | .linker_arg => pure arg
    res := r :: res
  return res.reverse

/-- `target_help` -/
def target_help (cfg : Configuration.Config) : String :=
  if cfg.arch == "arm" && cfg.model != "armv6" then
"Target processor options:
  -mthumb        Use Thumb2 instruction encoding
  -marm          Use classic ARM instruction encoding
"
  else ""

/-- `toolchain_help` -/
def toolchain_help (cfg : Configuration.Config) : String :=
  if !cfg.gnu_toolchain then
"Toolchain options:
  -t tof:env     Select target processor for the diab toolchain
"
  else ""

/-- `usage_string` -/
def usage_string (cfg : Configuration.Config) : String :=
  CommonOptions.version_string tool_name ++
"Usage: ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .i or .p       C source file that should not be preprocessed
  .s             Assembly file
  .S or .sx      Assembly file that must be preprocessed
  .o             Object file
  .a             Library file
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -E             Preprocess only, send result to standard output
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
" ++
  Frontend.prepro_help cfg ++
  CommonOptions.language_support_help ++
  DebugInit.debugging_help cfg ++
"Optimization options: (use -fno-<opt> to turn off -f<opt>)
  -O             Optimize the compiled code [on by default]
  -O0            Do not optimize the compiled code
  -O1 -O2 -O3    Synonymous for -O
  -Os            Optimize for code size in preference to code speed
  -Obranchless   Optimize to generate fewer conditional branches; try to produce
                 branch-free instruction sequences as much as possible
  -ftailcalls    Optimize function calls in tail position [on]
  -fconst-prop   Perform global constant propagation  [on]
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -fcse          Perform common subexpression elimination [on]
  -fredundancy   Perform redundancy elimination [on]
  -finline       Perform inlining of functions [on]
  -finline-functions-called-once Integrate functions only required by their
                 single caller [on]
  -fif-conversion Perform if-conversion (generation of conditional moves) [on]
Code generation options: (use -fno-<opt> to turn off -f<opt>)
  -fpic / -fPIC  Generate position-independent code [off]
  -fpie / -fPIE  Generate position-independent executables [on if supported]
  -ffpu          Use FP registers for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
  -fcommon       Put uninitialized globals in the common section [on].
" ++
  target_help cfg ++
  toolchain_help cfg ++
  Assembler.assembler_help ++
  Linker.linker_help cfg ++
"Tracing options:
  -dprepro       Save C file after preprocessing in <file>.i
  -dparse        Save C file after parsing and elaboration in <file>.parsed.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save RTL at various optimization points in <file>.rtl.<n>
  -dltl          Save LTL after register allocation in <file>.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -dall          Save all generated intermediate files in <file>.<ext>
  -sdump         Save info for post-linking validation in <file>.json
" ++
  CommonOptions.general_help ++
  CommonOptions.warning_help ++
"Interpreter mode:
  -interp        Execute given .c files using the reference interpreter
  -quiet         Suppress diagnostic messages for the interpreter
  -trace         Have the interpreter produce a detailed trace of reductions
  -random        Randomize execution order
  -all           Simulate all possible execution orders
  -main <name>   Start executing at function <name> instead of main()
"

/-- `print_usage_and_exit ()` -/
def print_usage_and_exit : DM Unit := do
  io (IO.print (usage_string (← getConfig)))
  throwThe Stop (.Exit 0)

/-- `optimization_options` -/
def optimization_options : List CommonOptions.FlagRef :=
  [ ⟨fun f b => { f with option_ftailcalls := b }⟩,
    ⟨fun f b => { f with option_fifconversion := b }⟩,
    ⟨fun f b => { f with option_fconstprop := b }⟩,
    ⟨fun f b => { f with option_fcse := b }⟩,
    ⟨fun f b => { f with option_fredundancy := b }⟩,
    ⟨fun f b => { f with option_finline := b }⟩,
    ⟨fun f b => { f with option_finline_functions_called_once := b }⟩ ]

/-- Register an input file. -/
def push_file (fn : FileAction) (source : Bool) (s : String) : DM Unit := do
  push_action fn s
  modify fun st => { st with
    num_source_files := st.num_source_files + (if source then 1 else 0),
    num_input_files := st.num_input_files + 1 }

/-- `cmdline_actions` -/
def cmdline_actions (cfg : Configuration.Config) : List (Pattern × Action DM) :=
  let f_opt := CommonOptions.f_opt
  let flag (set : Clflags.Flags → Bool → Clflags.Flags) : Bool → DM Unit :=
    fun b => modifyFlags (set · b)
  let check_align (n : Int) : DM Unit :=
    if n ≤ 0 || (n.toNat &&& (n.toNat - 1)) != 0 then
      error s!"requested alignment {n} is not a power of 2"
    else pure ()
  let set_pic_mode : DM Unit :=
    if cfg.pic_supported then modifyFlags fun f => { f with option_fpic := true }
    else warning "option -fpic not supported on this platform, ignored"
  let set_pie_mode : DM Unit :=
    if cfg.pic_supported then modifyFlags fun f => { f with option_fpie := true }
    else warning "option -fpie not supported on this platform, ignored"
  -- Getting help
  [ (.Exact "-help", .Unit print_usage_and_exit),
    (.Exact "--help", .Unit print_usage_and_exit) ] ++
  -- Getting version info
  CommonOptions.version_options tool_name ++
  -- Processing options
  [ (.Exact "-c", .Set (flag fun f b => { f with option_c := b })),
    (.Exact "-E", .Set (flag fun f b => { f with option_E := b })),
    (.Exact "-S", .Set (flag fun f b => { f with option_S := b })),
    (.Exact "-o", .String fun s => modifyFlags fun f => { f with option_o := some s }),
    (.Prefix "-o", .Self fun s => modifyFlags fun f => { f with option_o := some (s.drop 2).toString }) ] ++
  -- Preprocessing options
  Frontend.prepro_actions cfg ++
  -- Language support options
  CommonOptions.language_support_options ++
  -- Debugging options
  DebugInit.debugging_actions cfg ++
  -- Code generation options -- more below
  [ (.Exact "-O0", .Unit (CommonOptions.unset_all optimization_options)),
    (.Exact "-O", .Unit (CommonOptions.set_all optimization_options)),
    (.Regexp (fun s => s == "-O1" || s == "-O2" || s == "-O3"),
      .Unit (CommonOptions.set_all optimization_options)),
    (.Exact "-Os", .Set (flag fun f b => { f with option_Osize := b })),
    (.Exact "-Obranchless", .Set (flag fun f b => { f with option_Obranchless := b })),
    (.Exact "-fsmall-data", .Integer fun n => modifyFlags fun f => { f with option_small_data := n }),
    (.Exact "-fsmall-const", .Integer fun n => modifyFlags fun f => { f with option_small_const := n }),
    (.Exact "-ffloat-const-prop", .Integer fun n =>
      modifyFlags fun f => { f with option_ffloatconstprop := n.toNat }),
    (.Exact "-falign-functions", .Integer fun n => do
      check_align n; modifyFlags fun f => { f with option_falignfunctions := some n.toNat }),
    (.Exact "-falign-branch-targets", .Integer fun n => do
      check_align n; modifyFlags fun f => { f with option_falignbranchtargets := n.toNat }),
    (.Exact "-falign-cond-branches", .Integer fun n => do
      check_align n; modifyFlags fun f => { f with option_faligncondbranchs := n.toNat }),
    (.Exact "-fpic", .Unit set_pic_mode),
    (.Exact "-fPIC", .Unit set_pic_mode),
    (.Exact "-fno-pic", .Unset (flag fun f b => { f with option_fpic := b })),
    (.Exact "-fno-PIC", .Unset (flag fun f b => { f with option_fpic := b })),
    (.Exact "-fpie", .Unit set_pie_mode),
    (.Exact "-fPIE", .Unit set_pie_mode),
    (.Exact "-fno-pie", .Unset (flag fun f b => { f with option_fpie := b })),
    (.Exact "-fno-PIE", .Unset (flag fun f b => { f with option_fpie := b })) ] ++
  f_opt "common" ⟨fun f b => { f with option_fcommon := b }⟩ ++
  -- Target processor options
  (if cfg.arch == "arm" then
    if cfg.model == "armv6" then [(.Exact "-marm", .Ignore)]  -- Thumb needs ARMv6T2 or ARMv7
    else [ (.Exact "-mthumb", .Set (flag fun f b => { f with option_mthumb := b })),
           (.Exact "-marm", .Unset (flag fun f b => { f with option_mthumb := b })) ]
   else []) ++
  -- Toolchain options
  (if !cfg.gnu_toolchain then
    [ (.Exact "-t", .String fun arg => do
        push_linker_arg "-t"; push_linker_arg arg
        modifyFlags fun f => { f with prepro_options := arg :: "-t" :: f.prepro_options,
                                      assembler_options := arg :: "-t" :: f.assembler_options }) ]
   else []) ++
  -- Assembling options
  Assembler.assembler_actions cfg ++
  -- Linking options
  Linker.linker_actions cfg ++
  -- Tracing options
  [ (.Exact "-dprepro", .Set (flag fun f b => { f with option_dprepro := b })),
    (.Exact "-dparse", .Set (flag fun f b => { f with option_dparse := b })),
    (.Exact "-dc", .Set (flag fun f b => { f with option_dcmedium := b })),
    (.Exact "-dclight", .Set (flag fun f b => { f with option_dclight := b })),
    (.Exact "-dcminor", .Set (flag fun f b => { f with option_dcminor := b })),
    (.Exact "-drtl", .Set (flag fun f b => { f with option_drtl := b })),
    (.Exact "-dltl", .Set (flag fun f b => { f with option_dltl := b })),
    (.Exact "-dalloctrace", .Set (flag fun f b => { f with option_dalloctrace := b })),
    (.Exact "-dmach", .Set (flag fun f b => { f with option_dmach := b })),
    (.Exact "-dasm", .Set (flag fun f b => { f with option_dasm := b })),
    (.Exact "-dall", .Self fun _ => modifyFlags fun f =>
      { f with option_dprepro := true, option_dparse := true, option_dcmedium := true,
               option_dclight := true, option_dcminor := true, option_drtl := true,
               option_dltl := true, option_dalloctrace := true, option_dmach := true,
               option_dasm := true }),
    (.Exact "-sdump", .Set (flag fun f b => { f with option_sdump := b })),
    (.Exact "-sdump-suffix", .String fun s => do
      modifyFlags fun f => { f with option_sdump := true }
      modify fun st => { st with sdump_suffix := s }),
    (.Exact "-sdump-folder", .String fun _ => pure ()) ] ++
  -- General options
  CommonOptions.general_options ++
  -- Diagnostic options
  CommonOptions.warning_options ++
  -- Interpreter mode
  [ (.Exact "-interp", .Set (flag fun f b => { f with option_interp := b })),
    (.Exact "-quiet", .Unit (modify fun st => { st with interp_trace := 0 })),
    (.Exact "-trace", .Unit (modify fun st => { st with interp_trace := 2 })),
    (.Exact "-random", .Unit (modify fun st => { st with interp_mode := .Random })),
    (.Exact "-all", .Unit (modify fun st => { st with interp_mode := .All })),
    (.Exact "-main", .String fun s => modifyFlags fun f => { f with main_function_name := s }) ] ++
  -- Optimization options
  -- -f options: come in -f and -fno- variants
  f_opt "tailcalls" ⟨fun f b => { f with option_ftailcalls := b }⟩ ++
  f_opt "if-conversion" ⟨fun f b => { f with option_fifconversion := b }⟩ ++
  f_opt "const-prop" ⟨fun f b => { f with option_fconstprop := b }⟩ ++
  f_opt "cse" ⟨fun f b => { f with option_fcse := b }⟩ ++
  f_opt "redundancy" ⟨fun f b => { f with option_fredundancy := b }⟩ ++
  f_opt "inline" ⟨fun f b => { f with option_finline := b }⟩ ++
  f_opt "inline-functions-called-once" ⟨fun f b => { f with option_finline_functions_called_once := b }⟩ ++
  -- Code generation options
  f_opt "fpu" ⟨fun f b => { f with option_ffpu := b }⟩ ++
  f_opt "sse" ⟨fun f b => { f with option_ffpu := b }⟩ ++  -- backward compatibility
  [ -- Catch options that are not handled
    (.Prefix "-", .Self fun s => fatal_error s!"Unknown option `{s}'"),
    -- File arguments
    (.Suffix ".c", .Self (push_file .process_c_file true)),
    (.Suffix ".i", .Self (push_file .process_i_file true)),
    (.Suffix ".p", .Self (push_file .process_i_file true)),
    (.Suffix ".s", .Self (push_file .process_s_file true)),
    (.Suffix ".S", .Self (push_file .process_S_file true)),
    (.Suffix ".sx", .Self (push_file .process_S_file true)),
    (.Suffix ".o", .Self (push_file .linker_arg false)),
    (.Suffix ".a", .Self (push_file .linker_arg false)),
    -- GCC compatibility: .o.ext files and .so files are also object files
    (.Regexp (fun s => (s.splitOn ".o.").length > 1), .Self (push_file .linker_arg false)),
    (.Suffix ".so", .Self (push_file .linker_arg false)),
    -- GCC compatibility: .h files can be preprocessed with -E
    (.Suffix ".h", .Self (push_file .process_h_file true)) ]

/-- The initial flags for a configuration (the OCaml initial values of
    `Clflags` that depend on `Configuration`). -/
def initialFlags (cfg : Configuration.Config) : Clflags.Flags :=
  { option_fpie := cfg.pic_supported
    option_mthumb := cfg.model == "armv7m"
    option_gdwarf := if cfg.system == "diab" then 2 else 3
    option_small_data :=
      if cfg.arch == "powerpc" && cfg.abi == "eabi" && cfg.system == "diab" then 8 else 0
    option_small_const :=
      if cfg.arch == "powerpc" && cfg.abi == "eabi" && cfg.system == "diab" then 8 else 0
    stdlib_path := cfg.stdlib_path
    use_standard_headers := cfg.has_standard_headers }

/-- The body of `Driver.ml`'s main program, after the configuration is
    read. -/
def run (tgt : Target) : DM Unit := do
  let cfg ← getConfig
  parse_cmdline (cmdline_actions cfg) (← get).argv
  -- Any error for command line arguments?
  runFront CParser.Diagnostics.raise_on_errors
  -- Initialize the debug functions
  DebugInit.init
  let st ← get
  if (← nolink) && st.flags.option_o.isSome && st.num_source_files ≥ 2 then
    fatal_error "ambiguous '-o' option (multiple source files)"
  if st.num_input_files == 0 then
    fatal_error "no input file"
  if !st.flags.option_interp && st.flags.main_function_name != "main" then
    fatal_error "option '-main' requires option '-interp'"
  let linker_args ← Timing.time "Total compilation time" (perform_actions tgt)
  if !(← nolink) && !linker_args.isEmpty then
    Linker.linker (← output_filename_default "a.out") linker_args
  runFront CParser.Diagnostics.check_errors

/-- The main program of `ccomp` for a target: the exit code. -/
def main (tgt : Target) (progName : String) (args : List String)
    (defaultConfig : Configuration.Config := Configuration.x86_64_linux) : IO UInt32 := do
  let argv ← try Commandline.argv progName args catch e => do
    IO.eprintln s!"Error while processing the command line: {e}"
    return 2
  let cfg ← match ← Configuration.load argv defaultConfig with
    | .ok c => pure c
    | .error msg => do IO.eprintln msg; return 2
  let st0 : DState :=
    { argv, config := cfg, flags := initialFlags cfg
      diag := { config := Frontend.machine_of_config cfg } }
  let finish : DM Unit := do remove_tmp_files; Timing.print_timers
  let body : DM UInt32 := do
    let r ← tryCatchThe Stop (do run tgt; pure none) (fun e => pure (some e))
    let code ← match r with
      | none => pure 0
      | some (.CmdError msg) =>
        tryCatchThe Stop (error msg) (fun _ => pure ())
        pure 2
      | some .Abort =>
        tryCatchThe Stop (runFront CParser.Diagnostics.error_summary) (fun _ => pure ())
        pure 2
      | some (.Exit n) => pure n
    finish
    return code
  match ← (body.run' st0).run with
  | .ok code => return code
  | .error (.Exit n) => return n
  | .error _ => return 2

/-! ## The AArch64 target -/

/-- The configuration written by `./configure aarch64-linux`, without the
    run-time library and the standard headers (as `Configuration.x86_64_linux`). -/
def aarch64_linux : Configuration.Config :=
  { arch := "aarch64", model := "default", abi := "standard", is_big_endian := false,
    system := "linux",
    prepro := ["gcc", "-U__GNUC__", "-E"],
    asm := ["gcc", "-c"],
    linker := ["gcc"],
    asm_supports_cfi := true, stdlib_path := "", has_runtime_lib := false,
    has_standard_headers := false, response_file_style := .Gnu, pic_supported := true }

/-- The compiler options of `Compopts.v` (read from `Clflags` in OCaml). -/
def compilerConfig (fl : Clflags.Flags) (c : Compiler.Config) : Compiler.Config :=
  { c with
    optimTailcalls := fl.option_ftailcalls
    optimConstprop := fl.option_fconstprop
    optimCSE := fl.option_fcse
    optimRedundancy := fl.option_fredundancy
    optimForSize := fl.option_Osize
    debug := fl.option_g
    propagateFloatConstants := decide (fl.option_ffloatconstprop ≥ 1)
    generateFloatConstants := decide (fl.option_ffloatconstprop ≥ 2) }

/-- The target settings of `aarch64/extractionMachdep.v` for a configuration
    and the atom table of `C2C`. -/
def targetOfConfig (fl : Clflags.Flags) (cfg : Configuration.Config)
    (tbl : List (Nat × C2C.AtomInfo)) : ExtractionMachdep.Target :=
  { abi := cfg.abi, system := cfg.system
    atomIsExternal := C2C.atom_is_external fl tbl
    atomNeedsGOTAccess := C2C.atom_needs_GOT_access fl tbl
    atomIsAligned := C2C.atom_is_aligned tbl }

/-- The information on `inline`/`static` functions given to `Inliningaux`. -/
def inliningOptions (fl : Clflags.Flags) (tbl : List (Nat × C2C.AtomInfo)) :
    Inliningaux.Options :=
  { option_finline := fl.option_finline
    option_finline_functions_called_once := fl.option_finline_functions_called_once
    atomIsStatic := C2C.atom_is_static tbl
    atomInline := C2C.atom_inline tbl }

/-- The driver's view of the AArch64 target: the front-end parameters of
    `aarch64/CBuiltins.ml` and `Machregsaux.ml`, and the back end
    `Compiler.transf_c_program` → `Asmexpand.expand_program` →
    `PrintAsm.print_program`, and the reference interpreter `Interp.execute`
    (option `-interp`). -/
def aarch64Target : Target where
  c2c cfg :=
    let apple := cfg.abi == "apple"
    let macos := cfg.system == "macos"
    { builtins := AArch64.CBuiltins.builtins apple macos
      va_list_scalar := AArch64.CBuiltins.va_list_scalar apple
      size_va_list := AArch64.CBuiltins.size_va_list apple
      asm := { asm_mem_argument := AArch64.CBuiltins.asm_mem_argument
               is_register_name := fun s => (Machregsaux.registerByName s).isSome
               is_scratch_register := Machregsaux.isScratchRegister }
      elf_target := cfg.elf_target }
  backend fl cfg p tbl :=
    let t := targetOfConfig fl cfg tbl
    let c := compilerConfig fl (Extraction.configFor t (inliningOptions fl tbl))
    match Compiler.transfCProgram c p with
    | .Error e => .error e
    | .OK tp =>
      match asmToText t cfg.system tp with
      | .OK s => .ok s
      | .Error e => .error e
  interp := some Interp.execute

end Driver
end CC
