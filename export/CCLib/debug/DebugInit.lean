/-
  Port of `debug/DebugInit.ml`: the debugging options of the command line
  (`-g`, `-g<n>`, `-gdwarf-<n>`) and their help text.

  OCaml's `init` assigns the global reference `Debug.implem`.  The Lean
  port has no global hook reference (the wrappers of `Debug` take the
  implementation as an argument), so the choice of the implementation is
  the function `implem_of_options` (`init_debug` / `init_none`), which
  returns the hook record; `init` in the driver monad has no effect.  The
  driver and the assembly printers do not call the hooks yet, so no
  debugging sections are emitted.
-/
import CCLib.driver.Driveraux
import CCLib.debug.Dwarfgen

namespace CC
namespace DebugInit

open Commandline Driveraux

/-- `gnu_debugging_help` -/
def gnu_debugging_help : String :=
"  -gdwarf-2     Generate debug information in DWARF v2 format
  -gdwarf-3     Generate debug information in DWARF v3 format
"

/-- `debugging_help` -/
def debugging_help (cfg : Configuration.Config) : String :=
"Debugging options:
  -g             Generate debugging information
  -g<n>          Control generation of debugging information
                 (<n>=0: none, <n>=1: only globals,
                  <n>=2: globals + locals without locations, <n>=3: full)
" ++ (if cfg.gnu_toolchain then gnu_debugging_help else "")

/-- `gnu_debugging_actions` -/
def gnu_debugging_actions : List (Pattern × Action DM) :=
  let version (v : Nat) : DM Unit := modifyFlags fun f => { f with option_g := true, option_gdwarf := v }
  [ (.Exact "-gdwarf-2", .Unit (version 2)),
    (.Exact "-gdwarf-3", .Unit (version 3)) ]

/-- `debugging_actions` -/
def debugging_actions (cfg : Configuration.Config) : List (Pattern × Action DM) :=
  let depth (d : Nat) : DM Unit := modifyFlags fun f => { f with option_g := true, option_gdepth := d }
  [ (.Exact "-g", .Unit (depth 3)),
    (.Exact "-g0", .Unset fun b => modifyFlags fun f => { f with option_g := b }),
    (.Exact "-g1", .Unit (depth 1)),
    (.Exact "-g2", .Unit (depth 2)),
    (.Exact "-g3", .Unit (depth 3)) ] ++
  (if cfg.gnu_toolchain then gnu_debugging_actions else [])

/-- `init_debug`: the hooks of `DebugInformation`, with the DWARF
    generator of `Dwarfgen` for the GNU or the Diab toolchain.  The states
    of the hooks are held in `ref` and `gref`; `gcfg` reads the settings
    of `Dwarfgen` when the debug information is generated. -/
def init_debug (conf : Configuration.Config) (ref : IO.Ref DebugInformation.Full)
    (gref : IO.Ref Dwarfgen.GenSt) (gcfg : IO Dwarfgen.GenConfig) : Debug.Implem :=
  let d := DebugInformation.default_debug ref
  if conf.gnu_toolchain then
    { d with
      generate_debug_info := fun a b => do
        some <$> Dwarfgen.runIO ref gref (← gcfg) (Dwarfgen.gen_gnu_debug_info a b)
      add_fun_addr := fun n s a => DebugInformation.runIO ref (DebugInformation.gnu_add_fun_addr n s a) }
  else
    { d with
      generate_debug_info := fun a b => do
        some <$> Dwarfgen.runIO ref gref (← gcfg) (Dwarfgen.gen_diab_debug_info a b)
      add_diab_info := fun s l d p => DebugInformation.runIO ref (DebugInformation.add_diab_info s l d p)
      add_fun_addr := fun n s a => DebugInformation.runIO ref (DebugInformation.diab_add_fun_addr n s a) }

/-- `init_none` -/
def init_none : Debug.Implem := Debug.default_implem

/-- The implementation that `init ()` installs: `init_debug` if `-g` is
    given, `init_none` otherwise. -/
def implem_of_options (option_g : Bool) (conf : Configuration.Config)
    (ref : IO.Ref DebugInformation.Full) (gref : IO.Ref Dwarfgen.GenSt)
    (gcfg : IO Dwarfgen.GenConfig) : Debug.Implem :=
  if option_g then init_debug conf ref gref gcfg else init_none

/-- `init ()` in the driver monad: nothing to assign (see the header and
    `implem_of_options`). -/
def init : DM Unit := pure ()

end DebugInit
end CC
