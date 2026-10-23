/-
  Port of `cparser/Diagnostics.ml`: management of errors and warnings of the
  C front end.

  The OCaml front end keeps its state in global references (the error and
  warning counters and settings here, `Env.gensym`, `Machine.config`, the
  attribute table of `Cutil`) and signals errors with exceptions
  (`Diagnostics.Abort`, `Env.Error`, `Not_found`, …).  Lean has neither, so
  this file also defines
  * `State`, the record of all these global references;
  * `Exn`, the exceptions that escape front-end functions;
  * the monad `M := EStateM Exn State` in which the front end runs.
  As OCaml's references, the state survives exceptions (`EStateM` keeps the
  state on `throw`).

  Messages are not printed on `stderr` but appended to `State.messages`
  (one entry per message, without the trailing newline).  Colors are never
  used (OCaml enables them only when `stderr` is a terminal).
-/
import CCLib.cparser.Machine

namespace CC
namespace CParser

open C

/-- Errors raised by the environment functions (`Env.error`).  Declared here
    because Lean's exception type `Exn` must list them. -/
inductive Env.Error where
  | Unbound_identifier (s : String)
  | Unbound_tag (s kind : String)
  | Tag_mismatch (s expected actual : String)
  | Unbound_typedef (s : String)
  | No_member (comp kind mem : String)
  deriving BEq, Inhabited, Repr

/-- Classification of attributes (`Cutil.attribute_class`). Declared here
    because the attribute table is part of the global state. -/
inductive AttributeClass where
  /-- applies to the object being declared (function, variable) -/
  | Attr_object
  /-- applies to the name being declared (object, member, tag) -/
  | Attr_name
  /-- applies to types -/
  | Attr_type
  /-- applies to struct, union and enum -/
  | Attr_struct
  /-- applies to function types and decls -/
  | Attr_function
  /-- unknown attribute -/
  | Attr_unknown
  deriving BEq, DecidableEq, Inhabited, Repr

namespace Diagnostics

inductive WarningType where
  | Unnamed
  | Unknown_attribute
  | Zero_length_array
  | Celeven_extension
  | Gnu_empty_struct
  | Missing_declarations
  | Constant_conversion
  | Int_conversion
  | Varargs
  | Implicit_function_declaration
  | Pointer_type_mismatch
  | Compare_distinct_pointer_types
  | Implicit_int
  | Main_return_type
  | Invalid_noreturn
  | Return_type
  | Literal_range
  | Unknown_pragmas
  | CompCert_conformance
  | Inline_asm_sdump
  | Unused_variable
  | Unused_parameter
  | Wrong_ais_parameter
  | Unused_ais_parameter
  | Ignored_attributes
  | Extern_after_definition
  | Static_in_inline
  | Flexible_array_extensions
  | Tentative_incomplete_static
  | Reduced_alignment
  | Non_linear_cond_expr
  | Invalid_UTF8
  | Dollar_in_identifier
  | Unknown_warning
  deriving BEq, DecidableEq, Inhabited, Repr

open WarningType in
/-- List of all warnings with default status (`true`: active by default). -/
def all_warnings : List (WarningType × Bool) :=
  [ (Unnamed, true), (Unknown_attribute, true), (Zero_length_array, false),
    (Celeven_extension, false), (Gnu_empty_struct, true),
    (Missing_declarations, true), (Constant_conversion, true),
    (Int_conversion, true), (Varargs, true),
    (Implicit_function_declaration, true), (Pointer_type_mismatch, true),
    (Compare_distinct_pointer_types, true), (Implicit_int, true),
    (Main_return_type, true), (Invalid_noreturn, true), (Return_type, true),
    (Literal_range, true), (Unknown_pragmas, false),
    (CompCert_conformance, false), (Inline_asm_sdump, true),
    (Unused_variable, false), (Unused_parameter, false),
    (Wrong_ais_parameter, true), (Unused_ais_parameter, true),
    (Ignored_attributes, true), (Extern_after_definition, true),
    (Static_in_inline, true), (Flexible_array_extensions, false),
    (Tentative_incomplete_static, false), (Reduced_alignment, false),
    (Non_linear_cond_expr, false), (Invalid_UTF8, true),
    (Dollar_in_identifier, false), (Unknown_warning, true) ]

open WarningType in
/-- Conversion from warning type to string -/
def string_of_warning : WarningType → String
  | Unnamed => ""
  | Unknown_attribute => "unknown-attributes"
  | Zero_length_array => "zero-length-array"
  | Celeven_extension => "c11-extensions"
  | Gnu_empty_struct => "gnu-empty-struct"
  | Missing_declarations => "missing-declarations"
  | Constant_conversion => "constant-conversion"
  | Int_conversion => "int-conversion"
  | Varargs => "varargs"
  | Implicit_function_declaration => "implicit-function-declaration"
  | Pointer_type_mismatch => "pointer-type-mismatch"
  | Compare_distinct_pointer_types => "compare-distinct-pointer-types"
  | Implicit_int => "implicit-int"
  | Main_return_type => "main-return-type"
  | Invalid_noreturn => "invalid-noreturn"
  | Return_type => "return-type"
  | Literal_range => "literal-range"
  | Unknown_pragmas => "unknown-pragmas"
  | CompCert_conformance => "compcert-conformance"
  | Inline_asm_sdump => "inline-asm-sdump"
  | Unused_variable => "unused-variable"
  | Unused_parameter => "unused-parameter"
  | Wrong_ais_parameter => "wrong-ais-parameter"
  | Unused_ais_parameter => "unused-ais-parameter"
  | Ignored_attributes => "ignored-attributes"
  | Extern_after_definition => "extern-after-definition"
  | Static_in_inline => "static-in-inline"
  | Flexible_array_extensions => "flexible-array-extensions"
  | Tentative_incomplete_static => "tentative-incomplete-static"
  | Reduced_alignment => "reduced-alignment"
  | Non_linear_cond_expr => "non-linear-cond-expr"
  | Invalid_UTF8 => "invalid-utf8"
  | Dollar_in_identifier => "dollar-in-identifier-extension"
  | Unknown_warning => "unknown-warning-option"

inductive MsgClass where
  | WarningMsg | ErrorMsg | FatalErrorMsg | SuppressedMsg
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Different loc output formats -/
inductive LocFormat where
  | Default | MSVC | Vi
  deriving BEq, DecidableEq, Inhabited, Repr

end Diagnostics

open Diagnostics in
/-- The global state of the C front end (the OCaml global references). -/
structure State where
  /-- `Diagnostics.error_fatal` -/
  error_fatal : Bool := false
  /-- `Diagnostics.max_error` (0 means unlimited) -/
  max_error : Nat := 0
  /-- `Diagnostics.diagnostics_show_option` -/
  diagnostics_show_option : Bool := true
  /-- `Diagnostics.num_errors` -/
  num_errors : Nat := 0
  /-- `Diagnostics.num_warnings` -/
  num_warnings : Nat := 0
  /-- `Diagnostics.active_warnings` -/
  active_warnings : List WarningType :=
    (all_warnings.filter (·.2)).map (·.1)
  /-- `Diagnostics.error_warnings` -/
  error_warnings : List WarningType := []
  /-- `Diagnostics.diagnostics_format` -/
  diagnostics_format : LocFormat := .Default
  /-- the messages written to `stderr`, in order -/
  messages : Array String := #[]
  /-- `Env.gensym` -/
  gensym : Int := 0
  /-- `Machine.config` -/
  config : Machine.T := Machine.undef
  /-- `Cutil.attr_class`, keyed by normalized attribute name -/
  attr_class : List (String × AttributeClass) := []
  /-- `Transform.temporaries` (most recent first) -/
  temporaries : List Decl := []
  deriving Inhabited

/-- The exceptions of the OCaml front end that can escape its functions. -/
inductive Exn where
  /-- `Diagnostics.Abort`: compilation aborted after a fatal error -/
  | Abort
  /-- `Env.Error` -/
  | EnvError (e : Env.Error)
  /-- `Not_found` -/
  | Not_found
  /-- `Failure msg`, `Invalid_argument msg` and failed assertions -/
  | Failure (msg : String)
  deriving Inhabited, Repr

/-- The monad of the C front end. -/
abbrev M := EStateM Exn State

/-- `assert false` -/
def assertFalse {α} (where_ : String) : M α :=
  throw (.Failure s!"assertion failed in {where_}")

/-- The current machine configuration (`!Machine.config`). -/
def getConfig : M Machine.T := return (← get).config

namespace Diagnostics

open WarningType

def error_limit_reached : M Bool := do
  let s ← get
  return s.max_error != 0 && s.num_errors + 1 ≥ s.max_error

def reset : M Unit := modify fun s => { s with num_errors := 0, num_warnings := 0 }

def no_loc : Location := ("", -1)
def file_loc (file : String) : Location := (file, -10)

/-- Print a message to "stderr". -/
def emit (msg : String) : M Unit :=
  modify fun s => { s with messages := s.messages.push msg }

/-- `fatal_error_raw` -/
def fatal_error_raw {α} (msg : String) : M α := do
  modify fun s => { s with num_errors := s.num_errors + 1 }
  emit (msg ++ "Fatal error; compilation aborted.")
  throw .Abort

def activate_warning (w : WarningType) : M Unit :=
  modify fun s =>
    if s.active_warnings.contains w then s
    else { s with active_warnings := w :: s.active_warnings }

def deactivate_warning (w : WarningType) : M Unit :=
  modify fun s => { s with active_warnings := s.active_warnings.filter (· != w),
                           error_warnings := s.error_warnings.filter (· != w) }

def warning_as_error (w : WarningType) : M Unit := do
  activate_warning w
  modify fun s =>
    if s.error_warnings.contains w then s
    else { s with error_warnings := w :: s.error_warnings }

def warning_not_as_error (w : WarningType) : M Unit :=
  modify fun s => { s with error_warnings := s.error_warnings.filter (· != w) }

def wall : M Unit := modify fun s => { s with active_warnings := all_warnings.map (·.1) }
def wnothing : M Unit := modify fun s => { s with active_warnings := [] }
def werror : M Unit := modify fun s => { s with error_warnings := all_warnings.map (·.1) }

/-- Generate the warning key for the message -/
def key_of_warning (w : WarningType) : M (Option String) := do
  match w with
  | Unnamed => return none
  | _ => if (← get).diagnostics_show_option then
           return some ("-W" ++ string_of_warning w) else return none

/-- Add `-Werror` to the printed keys -/
def key_add_werror (w : Option String) : M (Option String) := do
  if (← get).diagnostics_show_option then
    match w with
    | none => return some "-Werror"
    | some s => return some ("-Werror," ++ s)
  else return none

/-- Lookup how to print the warning -/
def classify_warning (w : WarningType) : M (MsgClass × Option String) := do
  let key ← key_of_warning w
  let s ← get
  if s.active_warnings.contains w then
    if s.error_warnings.contains w then
      let key ← key_add_werror key
      if s.error_fatal then return (.FatalErrorMsg, key)
      else return (.ErrorMsg, key)
    else return (.WarningMsg, key)
  else return (.SuppressedMsg, none)

def pp_key (key : Option String) : String :=
  match key with
  | none => ""
  | some s => " [" ++ s ++ "]"

/-- Parse the option string `-fdiagnostics-format=...` -/
def parse_loc_format (s : String) : M Unit := do
  let s := (s.drop 21).toString
  let f ← match s with
    | "ccomp" => pure LocFormat.Default
    | "msvc" => pure .MSVC
    | "vi" => pure .Vi
    | s => do emit s!"Invalid value '{s}' in '-fdiagnostics-format={s}'"; throw .Abort
  modify fun st => { st with diagnostics_format := f }

/-- Print the location or `ccomp` for the case of unknown loc -/
def pp_loc (loc : Location) : M String := do
  let (filename, lineno) := loc
  let fmt := (← get).diagnostics_format
  let lineno :=
    if lineno = -10 then "" else
    match fmt with
    | .Default => s!":{lineno}"
    | .MSVC => s!"({lineno})"
    | .Vi => s!" +{lineno}"
  if filename != "" && filename != "cabs loc unknown" then
    return s!"{filename}{lineno}: "
  else return "ccomp: "

private def error_key (key : Option String) (loc : Location) (msg : String) : M Unit := do
  modify fun s => { s with num_errors := s.num_errors + 1 }
  emit s!"{← pp_loc loc}error: {msg}{pp_key key}"

private def fatal_error_key {α} (key : Option String) (loc : Location) (msg : String) : M α := do
  error_key key loc msg
  throw .Abort

/-- `Diagnostics.warning loc ty msg` -/
def warning (loc : Location) (ty : WarningType) (msg : String) : M Unit := do
  let (kind, key) ← classify_warning ty
  match kind with
  | .ErrorMsg => error_key key loc msg
  | .FatalErrorMsg => fatal_error_key key loc msg
  | .WarningMsg =>
      modify fun s => { s with num_warnings := s.num_warnings + 1 }
      emit s!"{← pp_loc loc}warning: {msg}{pp_key key}"
  | .SuppressedMsg => pure ()

/-- `Diagnostics.error loc msg` -/
def error (loc : Location) (msg : String) : M Unit := do
  if (← get).error_fatal || (← error_limit_reached) then
    fatal_error_key none loc msg
  else error_key none loc msg

/-- `Diagnostics.fatal_error loc msg` -/
def fatal_error {α} (loc : Location) (msg : String) : M α :=
  fatal_error_key none loc msg

private def errorsDetected (n : Nat) : String :=
  s!"{n} error{if n = 1 then "" else "s"} detected."

def error_summary : M Unit := do
  let n := (← get).num_errors
  if n > 0 then
    emit (errorsDetected n)
    modify fun s => { s with num_errors := 0 }

def check_errors : M Unit := do
  let n := (← get).num_errors
  if n > 0 then
    emit (errorsDetected n)
    modify fun s => { s with num_errors := 0 }
    throw .Abort

def unknown_warning (w : String) : M Unit :=
  warning no_loc Unknown_warning s!"Unknown warning option {w}, ignored."

/-- The command-line options of `warning_options`.  Returns `false` if the
    option is not a diagnostic option.  (OCaml builds a `Commandline` table;
    the patterns are tried in the same order.) -/
def warning_option (opt : String) : M Bool := do
  for (w, _) in all_warnings do
    let key := string_of_warning w
    if opt == "-W" ++ key then activate_warning w; return true
    if opt == "-Wno-" ++ key then deactivate_warning w; return true
    if opt == "-Werror=" ++ key then warning_as_error w; return true
    if opt == "-Wno-error=" ++ key then warning_not_as_error w; return true
  match opt with
  | "-Wfatal-errors" => modify fun s => { s with error_fatal := true }; return true
  | "-fdiagnostics-color" => return true
  | "-fno-diagnostics-color" => return true
  | "-Werror" => werror; return true
  | "-Wall" => wall; return true
  | "-w" => wnothing; return true
  | "-fno-diagnostics-show-option" =>
      modify fun s => { s with diagnostics_show_option := false }; return true
  | "-fdiagnostics-show-option" =>
      modify fun s => { s with diagnostics_show_option := true }; return true
  | _ =>
    if opt.startsWith "-Wno-" then return true
    if opt.startsWith "-W" then unknown_warning opt; return true
    if opt.startsWith "-fmax-errors=" then
      match (opt.drop 13).toString.toNat? with
      | some n => modify fun s => { s with max_error := n }; return true
      | none => return false
    if opt == "-fdiagnostics-format=ccomp" || opt == "-fdiagnostics-format=msvc"
        || opt == "-fdiagnostics-format=vi" then
      parse_loc_format opt; return true
    return false

def warning_help : String := "Diagnostic options:
  -Wall              Enable all warnings
  -W<warning>        Enable the specific <warning>
  -Wno-<warning>     Disable the specific <warning>
  -Werror            Make all warnings into errors
  -Werror=<warning>  Turn <warning> into an error
  -Wno-error=<warning> Turn <warning> into a warning even if -Werror is
                       specified
  -Wfatal-errors     Turn all errors into fatal errors aborting the compilation
  -fdiagnostics-color Turn on colored diagnostics
  -fno-diagnostics-color Turn of colored diagnostics
  -fmax-errors=<n>   Maximum number of errors to report
  -fdiagnostics-show-option Print the option name with mappable diagnostics
  -fno-diagnostics-show-option Turn of printing of options with mappable
                               diagnostics
"

def raise_on_errors : M Unit := do
  if (← get).num_errors > 0 then throw .Abort

def active_warning (ty : WarningType) : M Bool := do
  return (← classify_warning ty).1 != .SuppressedMsg

end Diagnostics
end CParser
end CC
