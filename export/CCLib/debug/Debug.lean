/-
  Port of `debug/Debug.ml`: the interface for generating and printing
  debug information.

  The OCaml record `implem` of hook functions becomes the structure
  `Implem`, whose hooks run in `IO` (the OCaml hooks have side effects).
  The global reference `implem` (installed by `DebugInit.init` when `-g` is
  given) is not a global here: the wrapper functions take the
  implementation as an explicit argument.  Only `default_implem` (all
  hooks do nothing, `exists_section` is always `true`, and
  `generate_debug_info` returns `none`) is defined here; the collecting
  hooks are `DebugInformation.default_debug` and the DWARF generator is
  `Dwarfgen`.  `exists_section` reads the state of the hooks, so it runs in
  `IO` (it is a pure function in the OCaml record type, reading a global
  table).

  Naming: OCaml `ident` (C identifiers) is `CParser.C.Ident`, `atom` is
  `Ident`, `positive` is `Positive`.
-/
import CCLib.debug.DwarfTypes
import CCLib.cparser.Env

namespace CC
namespace Debug

open DwarfTypes Sections
open CParser (Env.T)
open CParser.C (Storage Typ Globdecl Location StructOrUnion)

/-- C identifiers (`C.ident`). -/
abbrev CIdent := CParser.C.Ident

/-- `implem`: references to the actual implementation functions. -/
structure Implem where
  init : String → IO Unit
  atom_global : CIdent → Ident → IO Unit
  set_composite_size : CIdent → Ident → StructOrUnion → Option Int → IO Unit
  set_member_atom : (str_id : Ident) → String → (fld_id : Ident) → IO Unit
  set_member_offset : (str_id : Ident) → (fld_id : Ident) → Int → IO Unit
  set_bitfield_offset : (str_id : Ident) → (fld_id : Ident) → (bit_ofs : Int) →
    (byte_ofs : Int) → (size : Int) → IO Unit
  insert_global_declaration : Env.T → Globdecl → IO Unit
  add_fun_addr : Ident → SectionName → Int × Int → IO Unit
  generate_debug_info : (Ident → String) → String → IO (Option DebugEntries)
  all_files_iter : (String → IO Unit) → IO Unit
  insert_local_declaration : Storage → CIdent → Typ → Location → IO Unit
  atom_local_variable : CIdent → Ident → IO Unit
  enter_scope : Int → Int → Int → IO Unit
  enter_function_scope : Int → Int → IO Unit
  add_lvar_scope : Int → CIdent → Int → IO Unit
  open_scope : Ident → Int → Positive → IO Unit
  close_scope : Ident → Int → Positive → IO Unit
  start_live_range : Ident × Ident → Positive → Int × BuiltinArg Int → IO Unit
  end_live_range : Ident × Ident → Positive → IO Unit
  stack_variable : Ident × Ident → Int × BuiltinArg Int → IO Unit
  add_label : Ident → Positive → Int → IO Unit
  atom_parameter : CIdent → CIdent → Ident → IO Unit
  compute_diab_file_enum : (SectionName → IO Int) → (String → IO Int) → (Unit → IO Unit) → IO Unit
  compute_gnu_file_enum : (String → IO Unit) → IO Unit
  exists_section : SectionName → IO Bool
  remove_unused : CIdent → IO Unit
  remove_unused_function : CIdent → IO Unit
  symbol_printed : String → IO Unit
  add_diab_info : SectionName → Int → Int → Int → IO Unit

/-- `default_implem`: no debugging information. -/
def default_implem : Implem where
  init _ := pure ()
  atom_global _ _ := pure ()
  set_composite_size _ _ _ _ := pure ()
  set_member_atom _ _ _ := pure ()
  set_member_offset _ _ _ := pure ()
  set_bitfield_offset _ _ _ _ _ := pure ()
  insert_global_declaration _ _ := pure ()
  add_fun_addr _ _ _ := pure ()
  generate_debug_info _ _ := pure none
  all_files_iter _ := pure ()
  insert_local_declaration _ _ _ _ := pure ()
  atom_local_variable _ _ := pure ()
  enter_scope _ _ _ := pure ()
  enter_function_scope _ _ := pure ()
  add_lvar_scope _ _ _ := pure ()
  open_scope _ _ _ := pure ()
  close_scope _ _ _ := pure ()
  start_live_range _ _ _ := pure ()
  end_live_range _ _ := pure ()
  stack_variable _ _ := pure ()
  add_label _ _ _ := pure ()
  atom_parameter _ _ _ := pure ()
  compute_diab_file_enum _ _ _ := pure ()
  compute_gnu_file_enum _ := pure ()
  exists_section _ := pure true
  remove_unused _ := pure ()
  remove_unused_function _ := pure ()
  symbol_printed _ := pure ()
  add_diab_info _ _ _ _ := pure ()

instance : Inhabited Implem := ⟨default_implem⟩

section Wrappers
variable (implem : Implem)

def init_compile_unit (name : String) : IO Unit := implem.init name
def atom_global (id : CIdent) (atom : Ident) : IO Unit := implem.atom_global id atom
def set_composite_size (id : CIdent) (atom : Ident) (sou : StructOrUnion) (size : Option Int) : IO Unit :=
  implem.set_composite_size id atom sou size
def set_member_atom (str_id : Ident) (field : String) (fld_id : Ident) : IO Unit :=
  implem.set_member_atom str_id field fld_id
def set_member_offset (str_id fld_id : Ident) (off : Int) : IO Unit :=
  implem.set_member_offset str_id fld_id off
def set_bitfield_offset (str_id fld_id : Ident) (bit_ofs byte_ofs size : Int) : IO Unit :=
  implem.set_bitfield_offset str_id fld_id bit_ofs byte_ofs size
def insert_global_declaration (env : Env.T) (dec : Globdecl) : IO Unit :=
  implem.insert_global_declaration env dec
def add_fun_addr (atom : Ident) (sec : SectionName) (addr : Int × Int) : IO Unit :=
  implem.add_fun_addr atom sec addr
def generate_debug_info (fun_s : Ident → String) (var_s : String) : IO (Option DebugEntries) :=
  implem.generate_debug_info fun_s var_s
def all_files_iter (f : String → IO Unit) : IO Unit := implem.all_files_iter f
def insert_local_declaration (sto : Storage) (id : CIdent) (ty : Typ) (loc : Location) : IO Unit :=
  implem.insert_local_declaration sto id ty loc
def atom_local_variable (id : CIdent) (atom : Ident) : IO Unit := implem.atom_local_variable id atom
def enter_scope (p_id id s : Int) : IO Unit := implem.enter_scope p_id id s
def enter_function_scope (fun_id sc_id : Int) : IO Unit := implem.enter_function_scope fun_id sc_id
def add_lvar_scope (fun_id : Int) (var_id : CIdent) (s_id : Int) : IO Unit :=
  implem.add_lvar_scope fun_id var_id s_id
def open_scope (atom : Ident) (id : Int) (lbl : Positive) : IO Unit := implem.open_scope atom id lbl
def close_scope (atom : Ident) (id : Int) (lbl : Positive) : IO Unit := implem.close_scope atom id lbl
def start_live_range (atom : Ident × Ident) (lbl : Positive) (loc : Int × BuiltinArg Int) : IO Unit :=
  implem.start_live_range atom lbl loc
def end_live_range (atom : Ident × Ident) (lbl : Positive) : IO Unit := implem.end_live_range atom lbl
def stack_variable (atom : Ident × Ident) (loc : Int × BuiltinArg Int) : IO Unit :=
  implem.stack_variable atom loc
def add_label (atom : Ident) (p : Positive) (lbl : Int) : IO Unit := implem.add_label atom p lbl
def atom_parameter (fid pid : CIdent) (atom : Ident) : IO Unit := implem.atom_parameter fid pid atom
def exists_section (sec : SectionName) : IO Bool := implem.exists_section sec
def compute_diab_file_enum (end_l : SectionName → IO Int) (entry_l : String → IO Int)
    (line_e : Unit → IO Unit) : IO Unit :=
  implem.compute_diab_file_enum end_l entry_l line_e
def compute_gnu_file_enum (f : String → IO Unit) : IO Unit := implem.compute_gnu_file_enum f
def remove_unused (ident : CIdent) : IO Unit := implem.remove_unused ident
def remove_unused_function (ident : CIdent) : IO Unit := implem.remove_unused_function ident
def symbol_printed (ident : String) : IO Unit := implem.symbol_printed ident
def add_diab_info (sec : SectionName) (line_start debug_info low_pc : Int) : IO Unit :=
  implem.add_diab_info sec line_start debug_info low_pc

end Wrappers


end Debug
end CC
