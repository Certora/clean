/-
  Checks of the ported debug-information collection (`debug/DebugInformation`)
  and DWARF generation (`debug/Dwarfgen`): a small C program goes through the
  ported front end, its global declarations are recorded as the elaborator
  does with `-g`, and the GNU and Diab DWARF entries are generated and
  printed with `DwarfPrinter`.  The `#guard`s run when this file is built.
-/
import CCLib.cparser.Parse
import CCLib.x86.CBuiltins
import CCLib.debug.DebugInit
import CCLib.debug.DwarfPrinter

namespace DebugInfoCheck
open CC CParser C DebugInformation DwarfTypes

def src : String := "
typedef unsigned int uint;
struct point { int x; uint y; };
enum color { RED, GREEN = 4 };
const char *names[3];
static struct point origin;
int dist(struct point *p, int k) { return p->x + (int) p->y + k; }
"

/-- The program and the final environment (typedefs and globals). -/
def frontend : Except String (C.Program × Env.T) :=
  let x : M (C.Program × Env.T) := do
    let init ← Env.set_builtins (X86.CBuiltins.builtins true false)
    let p ← Parse.preprocessed_file {} init "t.c" src.toUTF8
    let user := p.filter (fun g => g.gloc.1 == "t.c")
    let env := user.foldl (fun env g =>
      match g.gdesc with
      | .Gtypedef id t => Env.add_typedef env id t
      | .Gdecl (.mk sto id ty _) => Env.add_ident env id sto ty
      | _ => env) init.env
    return (user, env)
  match x.run { config := Machine.x86_64 } with
  | .ok r _ => .ok r
  | .error e st => .error s!"{repr e} {st.messages}"

/-- The atom of a C identifier (as `C2C` would assign it). -/
def atomOf (id : CParser.C.Ident) : CC.Ident := identOfString id.name

/-- Record the declarations as `Elab` and `C2C` do with `-g`, then mark
    the symbols as printed and give `dist` an address range. -/
def collect (p : C.Program) (env : Env.T) : DM Unit := do
  init "t.c"
  for g in p do insert_global_declaration env g
  for g in p do
    match g.gdesc with
    | .Gfundef f => atom_global f.fd_name (atomOf f.fd_name); symbol_printed f.fd_name.name
    | .Gdecl (.mk _ id _ _) => atom_global id (atomOf id); symbol_printed id.name
    | _ => pure ()
  gnu_add_fun_addr (identOfString "dist") .Section_text (11, 10)

def genCfg : Dwarfgen.GenConfig :=
  { cwd := "/tmp", extern_atom := fun a => toString a.toNat,
    gnu_filenum := fun f => if f == "t.c" then some 1 else none }

def run (gen : Dwarfgen.GM DebugEntries) : Except String DebugEntries :=
  match frontend with
  | .error e => .error e
  | .ok (p, env) =>
    let x : Dwarfgen.GM DebugEntries := do
      Dwarfgen.liftDI (collect p env)
      gen
    match (x genCfg).run { full := { fe := { config := Machine.x86_64 } } } with
    | .ok r _ => .ok r
    | .error e _ => .error s!"{repr e}"

def gnu : Except String DebugEntries :=
  run (Dwarfgen.gen_gnu_debug_info (fun _ => ".text") ".data")

/-- The tags of an entry tree, in prefix order. -/
def tags (e : DwEntry) : List String :=
  DwarfUtil.entry_fold (fun acc t => acc ++ [DwarfUtil.string_of_dw_tag t]) [] e

def strName : StringConst → String
  | .Simple_string s => s
  | .Offset_string _ s => s

/-- The names of the variables, subprograms and members. -/
def names (e : DwEntry) : List String :=
  DwarfUtil.entry_fold (fun acc t =>
    match t with
    | .DW_TAG_variable v => acc ++ [strName v.variable_name]
    | .DW_TAG_subprogram s => acc ++ [strName s.subprogram_name]
    | .DW_TAG_member m => acc ++ (m.member_name.map strName).toList
    | .DW_TAG_typedef t => acc ++ [strName t.typedef_name]
    | .DW_TAG_enumerator t => acc ++ [strName t.enumerator_name]
    | _ => acc) [] e

def gnuEntry : Option GnuEntries :=
  match gnu with
  | .ok (.Gnu e) => some e
  | _ => none

#guard gnuEntry.isSome
#guard (gnuEntry.map (tags ·.gnu_entry |>.head?)).join == some "DW_TAG_compile_unit"
-- every global definition and every type used is described
-- (the unused static `origin` is removed by the front end)
#guard (gnuEntry.map (fun e => names e.gnu_entry)) == some ["x", "y", "uint", "dist", "names"]
#guard (gnuEntry.map (fun e => tags e.gnu_entry)).all fun ts =>
  ["DW_TAG_structure_type", "DW_TAG_pointer_type", "DW_TAG_array_type",
   "DW_TAG_subrange_type", "DW_TAG_const_type", "DW_TAG_typedef",
   "DW_TAG_formal_parameter", "DW_TAG_base_type"].all ts.contains
-- the enum is not used by any definition, so it is not emitted
#guard (gnuEntry.map (fun e => tags e.gnu_entry)).all fun ts =>
  !ts.contains "DW_TAG_enumeration_type"
-- strings of 4 bytes or more go to the string table (GNU, Linux)
#guard (gnuEntry.map (fun e => e.string_table.map (·.2))).all fun st =>
  st.contains "dist" && st.contains "names" && st.contains "/tmp" && !st.contains "int"

/-- The DWARF printer target of the x86 GNU assembler. -/
def x86Target : DwarfTarget where
  label n := s!".L{n}"
  printSec s := "\t" ++ (match s with
    | .Section_debug_info _ => ".section\t.debug_info,\"\",@progbits"
    | .Section_debug_abbrev => ".section\t.debug_abbrev,\"\",@progbits"
    | .Section_debug_loc => ".section\t.debug_loc,\"\",@progbits"
    | .Section_debug_line _ => ".section\t.debug_line,\"\",@progbits"
    | .Section_debug_ranges => ".section\t.debug_ranges,\"\",@progbits"
    | .Section_debug_str => ".section\t.debug_str,\"MS\",@progbits,1"
    | _ => ".text") ++ "\n"
  symbol a := s!"sym{a.toNat}"
  comment := "#"
  address := ".quad"

def printed : Except String String := do
  let e ← gnu
  PrintAsmaux.run (DwarfPrinter.printDebug { target := x86Target } e)

#guard match printed with
  | .ok s => (s.splitOn "DW_TAG_subprogram").length ≥ 1 && (s.splitOn ".debug_info").length > 1
      && (s.splitOn ".debug_str").length > 1
  | .error _ => false

/-! The Diab variant: one compilation unit per section. -/

def diab : Except String DebugEntries :=
  run (do
    Dwarfgen.liftDI (do
      add_diab_info .Section_text 1 2 10
      add_diab_info (.Section_user ".data" true false) 3 4 20
      compute_diab_file_enum (m := DM) (fun _ => pure 30) (fun _ => pure 40) (fun _ => pure ()))
    Dwarfgen.gen_diab_debug_info (fun _ => ".text") ".data")

#guard match diab with
  | .ok (.Diab es) => es.map (·.section_name) == [".text", ".data"]
  | _ => false

end DebugInfoCheck
