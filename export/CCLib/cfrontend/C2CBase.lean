/-
  Port of `cfrontend/C2C.ml`, part 1 of 2 (state, atom table, builtins,
  types, string literals and floating-point constants; the rest is
  `C2C.lean`): translation of the elaborated C syntax of the
  untrusted front end (`CParser.C`) into CompCert C (`Csyntax`).

  Differences from OCaml:
  * The global state of `C2C.ml` (`decl_atom`, `comp_env`,
    `currentLocation`, `currentFunction`, `stringNum`, `stringTable`,
    `wstringTable`) and the section table of `Sections`/`CPragmas` form the
    state `C2C.State`, threaded by the monad `CM := StateT State CParser.M`
    (`CParser.M` provides diagnostics and the machine configuration).
  * The flags of `Clflags` are the explicit value `Clflags.Flags`; the
    target-dependent parts (`CBuiltins.builtins`,
    `CBuiltins.va_list_scalar`, `CBuiltins.size_va_list`, the extended-asm
    target of `ExtendedAsm`, `Configuration.elf_target`, and the pragma hook
    `process_pragma_hook` set by `CPragmas`) are the structure
    `C2C.Target`.
  * `intern_string` is `identOfString` (identifiers are an injective
    encoding of names); the set of names interned so far, used by
    `gensym_string_literal`, is part of the state.
  * The `atom_*` queries are functions on the final table `decl_atom`, and
    `atomInfo` turns it into the `PrintAsm.AtomInfo` used by the assembly
    printers.
  * The calls of the debug hooks (`Debug.*`, `debug_set_struct_ofs`; the
    hooks themselves are in `debug/`) are omitted.
  * Hash tables are association lists, most recent first, so that the
    string-literal globals are produced in a deterministic order.
-/
import CCLib.cparser.Cutil
import CCLib.cparser.Env
import CCLib.cparser.ExtendedAsm
import CCLib.cfrontend.Ctyping
import CCLib.cfrontend.Initializers
import CCLib.common.Sections
import CCLib.common.MemoryInject
import CCLib.lib.FloatsParsed
import CCLib.backend.PrintAsm
import CCLib.driver.Clflags

namespace CC
namespace C2C

open CParser (M)
open Csyntax

/-! ## Information about global variables, recorded per atom -/

inductive InlineStatus where
  /-- No inline specifier and no noinline attribute -/
  | No_specifier
  /-- The atom is declared with the noinline attribute -/
  | Noinline
  /-- The atom is declared inline -/
  | Inline
  deriving BEq, DecidableEq, Inhabited, Repr

inductive LiteralStatus where
  | No_literal
  | String_literal
  | Wide_string_literal
  deriving BEq, DecidableEq, Inhabited, Repr

structure AtomInfo where
  /-- storage class -/
  a_storage : CParser.C.Storage
  /-- defined in the current comp. unit? -/
  a_defined : Bool
  /-- size in bytes -/
  a_size : Option Int
  /-- alignment -/
  a_alignment : Option Int
  /-- in which section to put it: 1 section for data, 3 sections
      (code/lit/jumptbl) for functions -/
  a_sections : List Sections.SectionName
  /-- access mode, e.g. small data area -/
  a_access : Sections.AccessMode
  /-- function declared inline? -/
  a_inline : InlineStatus
  /-- is this a string literal? -/
  a_literal : LiteralStatus
  /-- source location -/
  a_loc : CParser.C.Location

/-- The target-dependent parameters of `C2C`. -/
structure Target where
  /-- `CBuiltins.builtins` -/
  builtins : CParser.C.Builtins
  /-- `CBuiltins.va_list_scalar` -/
  va_list_scalar : Bool
  /-- `CBuiltins.size_va_list` -/
  size_va_list : Int
  /-- the target of `ExtendedAsm.transf_asm` -/
  asm : CParser.ExtendedAsm.TargetAsm
  /-- `Configuration.elf_target` -/
  elf_target : Bool := true
  /-- `process_pragma_hook` (set by `CPragmas`): returns `true` for a
      recognized pragma, and the updated section table -/
  process_pragma : CParser.C.Location → String → Sections.Table →
    M (Bool × Sections.Table) := fun _ _ t => pure (false, t)

/-- The global state of `C2C.ml`. -/
structure State where
  flags : Clflags.Flags
  target : Target
  /-- `decl_atom`, keyed by `Positive.toNat` of the atom, most recent first -/
  decl_atom : List (Nat × AtomInfo) := []
  /-- `comp_env` -/
  comp_env : CompositeEnv := PTree.empty
  /-- the tables of `Sections` (set by `#pragma section`) -/
  sections : Sections.Table := Sections.«initialize»
  currentLocation : CParser.C.Location := CParser.Cutil.no_loc
  currentFunction : String := ""
  /-- `stringNum`: number of the last global for string literals -/
  stringNum : Nat := 0
  stringTable : List (String × Ident) := []
  wstringTable : List ((List Int64 × CParser.C.IKind) × Ident) := []
  /-- the names interned so far (`Camlcoq.atom_of_string`) -/
  interned : Std.HashSet String := {}

abbrev CM := StateT State M

abbrev Expr := Csyntax.Expr
abbrev ExprList := Csyntax.ExprList
abbrev Stmt := Csyntax.Stmt
abbrev LStmts := Csyntax.LStmts
abbrev Program := Csyntax.Program
abbrev FunDef := Csyntax.FunDef

/-! ### Queries on the atom table -/

def find_atom (tbl : List (Nat × AtomInfo)) (a : Ident) : Option AtomInfo :=
  tbl.lookup a.toNat

def atom_is_static (tbl : List (Nat × AtomInfo)) (a : Ident) : Bool :=
  match find_atom tbl a with
  | some i => i.a_storage == .Storage_static
  | none => false

/-- Is it possible for symbol `a` to be defined in a DLL?  Yes, unless `a`
    is defined in the current compilation unit, or is static. -/
def atom_is_external (fl : Clflags.Flags) (tbl : List (Nat × AtomInfo)) (a : Ident) : Bool :=
  match find_atom tbl a with
  | some i =>
    if i.a_defined then false
    else if i.a_storage == .Storage_static then false
    else if i.a_storage == .Storage_default && i.a_size.isSome then !fl.option_fcommon
    else true
  | none => true

/-- In ELF PIC code, all non-static symbols must be accessed through the
    GOT; in PIE code, only the external ones; otherwise the GOT is unused. -/
def atom_needs_GOT_access (fl : Clflags.Flags) (tbl : List (Nat × AtomInfo)) (a : Ident) : Bool :=
  if fl.option_fpic then !atom_is_static tbl a
  else if fl.option_fpie then atom_is_external fl tbl a
  else false

def atom_alignof (tbl : List (Nat × AtomInfo)) (a : Ident) : Option Int :=
  (find_atom tbl a).bind (·.a_alignment)

def atom_is_aligned (tbl : List (Nat × AtomInfo)) (a : Ident) (sz : Int) : Bool :=
  match atom_alignof tbl a with
  | none => false
  | some align => align % sz == 0

def atom_sections (tbl : List (Nat × AtomInfo)) (a : Ident) : List Sections.SectionName :=
  match find_atom tbl a with
  | some i => i.a_sections
  | none => []

def atom_is_small_data (tbl : List (Nat × AtomInfo)) (a : Ident) (ofs : Int) : Bool :=
  match find_atom tbl a with
  | some info =>
    info.a_access == .Access_near &&
      (match info.a_size with
       | none => false
       | some sz => 0 ≤ ofs && ofs < sz)
  | none => false

def atom_is_rel_data (tbl : List (Nat × AtomInfo)) (a : Ident) : Bool :=
  match find_atom tbl a with
  | some i => i.a_access == .Access_far
  | none => false

def atom_inline (tbl : List (Nat × AtomInfo)) (a : Ident) : InlineStatus :=
  match find_atom tbl a with
  | some i => i.a_inline
  | none => .No_specifier

/-- ISO C99 inline definitions: functions with inline specifier and without
    extern, which do not provide an external definition. -/
def atom_is_iso_inline_definition (tbl : List (Nat × AtomInfo)) (a : Ident) : Bool :=
  match find_atom tbl a with
  | some i => i.a_storage == .Storage_default && i.a_inline == .Inline
  | none => false

def atom_location (tbl : List (Nat × AtomInfo)) (a : Ident) : CParser.C.Location :=
  match find_atom tbl a with
  | some i => i.a_loc
  | none => CParser.Cutil.no_loc

def atom_literal (tbl : List (Nat × AtomInfo)) (a : Ident) : LiteralStatus :=
  match find_atom tbl a with
  | some i => i.a_literal
  | none => .No_literal

/-- The atom information in the form used by the assembly printers. -/
def atomInfo (tbl : List (Nat × AtomInfo)) : PrintAsm.AtomInfo where
  isStatic := atom_is_static tbl
  sections := atom_sections tbl
  alignof a := (atom_alignof tbl a).map Int.toNat
  isIsoInlineDefinition := atom_is_iso_inline_definition tbl

/-! ### Error handling -/

def updateLoc (l : CParser.C.Location) : CM Unit :=
  modify fun s => { s with currentLocation := l }

def updateFunction (f : String) : CM Unit :=
  modify fun s => { s with currentFunction := f }

def error (msg : String) : CM Unit := do
  (CParser.Diagnostics.error (← get).currentLocation msg : M Unit)

def fatal_error {α} (msg : String) : CM α := do
  (CParser.Diagnostics.fatal_error (← get).currentLocation msg : M α)

def unsupported (msg : String) : CM Unit := do
  (CParser.Diagnostics.error (← get).currentLocation s!"unsupported feature: {msg}" : M Unit)

def warning (t : CParser.Diagnostics.WarningType) (msg : String) : CM Unit := do
  (CParser.Diagnostics.warning (← get).currentLocation t msg : M Unit)

/-- `Camlcoq.intern_string` -/
def intern_string (s : String) : CM Ident := do
  modify fun st => { st with interned := st.interned.insert s }
  return identOfString s

def add_atom (id : Ident) (i : AtomInfo) : CM Unit :=
  modify fun s => { s with decl_atom := (id.toNat, i) :: s.decl_atom }

/-! ## The builtin environment -/

section Builtins
open CParser.C

def ais_annot_functions (elf_target : Bool) : List (String × (Typ × List Typ × Bool)) :=
  if elf_target then
    -- Ais Annotations, only available for ELF targets
    [("__builtin_ais_annot", (.TVoid [], [.TPtr (.TInt .IChar [.AConst]) []], true))]
  else []

def builtins_generic (elf_target : Bool) : Builtins where
  builtin_typedefs := []
  builtin_functions :=
    ais_annot_functions elf_target ++ [
    -- Integer arithmetic
    ("__builtin_bswap64", (.TInt .IULongLong [], [.TInt .IULongLong []], false)),
    ("__builtin_bswap", (.TInt .IUInt [], [.TInt .IUInt []], false)),
    ("__builtin_bswap32", (.TInt .IUInt [], [.TInt .IUInt []], false)),
    ("__builtin_bswap16", (.TInt .IUShort [], [.TInt .IUShort []], false)),
    ("__builtin_clz", (.TInt .IInt [], [.TInt .IUInt []], false)),
    ("__builtin_clzl", (.TInt .IInt [], [.TInt .IULong []], false)),
    ("__builtin_clzll", (.TInt .IInt [], [.TInt .IULongLong []], false)),
    ("__builtin_ctz", (.TInt .IInt [], [.TInt .IUInt []], false)),
    ("__builtin_ctzl", (.TInt .IInt [], [.TInt .IULong []], false)),
    ("__builtin_ctzll", (.TInt .IInt [], [.TInt .IULongLong []], false)),
    -- Floating-point absolute value
    ("__builtin_fabs", (.TFloat .FDouble [], [.TFloat .FDouble []], false)),
    ("__builtin_fabsf", (.TFloat .FFloat [], [.TFloat .FFloat []], false)),
    -- Float arithmetic
    ("__builtin_fsqrt", (.TFloat .FDouble [], [.TFloat .FDouble []], false)),
    ("__builtin_sqrt", (.TFloat .FDouble [], [.TFloat .FDouble []], false)),
    -- Block copy
    ("__builtin_memcpy_aligned",
      (.TVoid [], [.TPtr (.TVoid []) [], .TPtr (.TVoid [.AConst]) [], .TInt .IULong [],
                   .TInt .IULong []], false)),
    -- Selection
    ("__builtin_sel", (.TVoid [], [.TInt .IBool []], true)),
    -- Annotations
    ("__builtin_annot", (.TVoid [], [.TPtr (.TInt .IChar [.AConst]) []], true)),
    ("__builtin_annot_intval",
      (.TInt .IInt [], [.TPtr (.TInt .IChar [.AConst]) [], .TInt .IInt []], false)),
    -- Software memory barrier
    ("__builtin_membar", (.TVoid [], [], false)),
    -- Variable arguments
    ("__builtin_va_start", (.TVoid [], [.TPtr (.TVoid []) []], false)),
    ("__builtin_va_arg", (.TVoid [], [.TPtr (.TVoid []) [], .TInt .IUInt []], false)),
    ("__builtin_va_copy", (.TVoid [], [.TPtr (.TVoid []) [], .TPtr (.TVoid []) []], false)),
    ("__builtin_va_end", (.TVoid [], [.TPtr (.TVoid []) []], false)),
    -- Optimization hints
    ("__builtin_unreachable", (.TVoid [], [], false)),
    ("__builtin_expect", (.TInt .ILong [], [.TInt .ILong [], .TInt .ILong []], false)) ]

/-- `C2C.builtins`: the generic builtins and the processor-dependent ones -/
def builtins (tgt : Target) : Builtins where
  builtin_typedefs :=
    (builtins_generic tgt.elf_target).builtin_typedefs ++ tgt.builtins.builtin_typedefs
  builtin_functions :=
    (builtins_generic tgt.elf_target).builtin_functions ++ tgt.builtins.builtin_functions

end Builtins

/-- The known attributes -/
def attributes : List (String × CParser.AttributeClass) := [
  -- struct-related
  ("packed", .Attr_struct),
  -- function-related
  ("noreturn", .Attr_function),
  ("noinline", .Attr_function),
  -- name-related
  ("aligned", .Attr_name),
  -- object-related
  ("section", .Attr_object),
  ("unused", .Attr_object) ]

/-! ## Handling of inlined memcpy functions -/

def constant_size_t (a : Expr) : CM (Option Int) := do
  match Initializers.constvalCast (← get).comp_env a Ctyping.size_t with
  | .OK (.Vint n) => return some (Integers.Int.unsigned n)
  | .OK (.Vlong n) => return some (Integers.Int64.unsigned n)
  | _ => return none

def is_power2 (n : Int) : Bool :=
  n > 0 && (n.toNat &&& (n.toNat - 1)) == 0

def make_builtin_memcpy (args : ExprList) : CM Expr := do
  match args with
  | .Econs dst (.Econs src (.Econs sz (.Econs al .Enil))) =>
    let sz1 ← match ← constant_size_t sz with
      | some n => pure n
      | none =>
        error "size argument of '__builtin_memcpy_aligned' must be a constant"
        pure 0
    let al1 ← match ← constant_size_t al with
      | some n => pure n
      | none =>
        error "alignment argument of '__builtin_memcpy_aligned' must be a constant"
        pure 1
    if !is_power2 al1 then
      error "alignment argument of '__builtin_memcpy_aligned' must be a power of 2"
    if al1 == 0 || sz1 % al1 != 0 then
      error "alignment argument of '__builtin_memcpy_aligned' must be a divisor of the size"
    -- Issue #28: must decay array types to pointer types
    return .Ebuiltin (.EF_memcpy sz1 al1) [typeconv (Csyntax.typeof dst), typeconv (Csyntax.typeof src)]
      (.Econs dst (.Econs src .Enil)) .Tvoid
  | _ => throw (.Failure "assert false: make_builtin_memcpy")

/-! ## Translation of `va_arg` for variadic functions -/

def va_list_ptr (e : Expr) : CM Expr := do
  if !(← get).target.va_list_scalar then return e
  match e with
  | .Evalof e' _ => return .Eaddrof e' (.Tpointer (Csyntax.typeof e) noattr)
  | _ =>
    error "bad use of a va_list object"
    return e

def make_builtin_va_arg_by_val (helper : String) (ty ty_ret : Ty) (arg : Expr) : CM Expr := do
  let ty_fun := Ty.Tfunction [.Tpointer .Tvoid noattr] ty_ret cc_default
  return .Ecast
    (.Ecall (.Evalof (.Evar (← intern_string helper) ty_fun) ty_fun)
      (.Econs (← va_list_ptr arg) .Enil) ty_ret)
    ty

def make_builtin_va_arg_by_ref (helper : String) (ty : Ty) (arg : Expr) : CM Expr := do
  let ty_fun := Ty.Tfunction [.Tpointer .Tvoid noattr, Ctyping.size_t]
    (.Tpointer .Tvoid noattr) cc_default
  let ty_ptr := Ty.Tpointer ty noattr
  let call := Expr.Ecall (.Evalof (.Evar (← intern_string helper) ty_fun) ty_fun)
    (.Econs (← va_list_ptr arg) (.Econs (.Esizeof ty Ctyping.size_t) .Enil))
    (.Tpointer .Tvoid noattr)
  return .Evalof (.Ederef (.Ecast call ty_ptr) ty) ty

def ezero : Expr := .Eval (.Vint (Integers.Int.repr 0)) type_int32s

def make_builtin_va_arg (ty : Ty) (e : Expr) : CM Expr := do
  match ty with
  | .Tint .. =>
    make_builtin_va_arg_by_val "__compcert_va_int32" ty (.Tint .I32 .Unsigned noattr) e
  | .Tpointer .. =>
    if Archi.ptr64 then
      make_builtin_va_arg_by_val "__compcert_va_int64" ty (.Tlong .Unsigned noattr) e
    else
      make_builtin_va_arg_by_val "__compcert_va_int32" ty (.Tint .I32 .Unsigned noattr) e
  | .Tlong .. =>
    make_builtin_va_arg_by_val "__compcert_va_int64" ty (.Tlong .Unsigned noattr) e
  | .Tfloat .. =>
    make_builtin_va_arg_by_val "__compcert_va_float64" ty (.Tfloat .F64 noattr) e
  | .Tstruct .. | .Tunion .. =>
    make_builtin_va_arg_by_ref "__compcert_va_composite" ty e
  | _ =>
    unsupported "va_arg at this type"
    return ezero

/-! ## Translation functions -/

/-! ### Constants -/

def convertInt32 (n : Int64) : Integers.Int := Integers.Int.repr n.toInt
def convertInt64 (n : Int64) : Integers.Int64 := Integers.Int64.repr n.toInt
def convertIntZ (n : Int64) : Int := n.toInt

/-! ### Attributes -/

def log2 (n : Nat) : Nat := if n ≤ 1 then 0 else 1 + log2 (n / 2)

def convertAttr (a : CParser.C.Attributes) : Attr :=
  { attr_volatile := a.contains .AVolatile
    attr_alignas :=
      let n := CParser.Cutil.alignas_attribute a
      if n > 0 then some (log2 n.toNat) else none }

def convertCallconv (targs : Option (List α)) (va : Bool) (attr : CParser.C.Attributes) :
    CallConv :=
  let vararg := match targs with
    | none => none
    | some tl => if va then some (tl.length : Int) else none
  let sr := CParser.Cutil.find_custom_attributes ["structreturn", "__structreturn"] attr
  { cc_vararg := vararg, cc_unproto := targs.isNone, cc_structret := !sr.isEmpty }

/-! ### Types -/

def convertIkind (k : CParser.C.IKind) (a : Attr) : CM Ty := do
  let cfg ← (CParser.getConfig : M _)
  return match k with
  | .IBool => .Tint .IBool .Unsigned a
  | .IChar => .Tint .I8 (if cfg.char_signed then .Signed else .Unsigned) a
  | .ISChar => .Tint .I8 .Signed a
  | .IUChar => .Tint .I8 .Unsigned a
  | .IInt => .Tint .I32 .Signed a
  | .IUInt => .Tint .I32 .Unsigned a
  | .IShort => .Tint .I16 .Signed a
  | .IUShort => .Tint .I16 .Unsigned a
  | .ILong => if cfg.sizeof_long == 8 then .Tlong .Signed a else .Tint .I32 .Signed a
  | .IULong => if cfg.sizeof_long == 8 then .Tlong .Unsigned a else .Tint .I32 .Unsigned a
  | .ILongLong => .Tlong .Signed a
  | .IULongLong => .Tlong .Unsigned a

def convertFkind (k : CParser.C.FKind) (a : Attr) : CM Ty := do
  match k with
  | .FFloat16 =>
    unsupported "'_Float16' type"
    return .Tfloat .F32 a
  | .FFloat => return .Tfloat .F32 a
  | .FDouble => return .Tfloat .F64 a
  | .FLongDouble =>
    if !(← get).flags.option_flongdouble then unsupported "'long double' type"
    return .Tfloat .F64 a

def checkResultType (env : CParser.Env.T) (ty : CParser.C.Typ) : CM Unit := do
  if !(← get).flags.option_fstruct_passing && (← (CParser.Cutil.is_composite_type env ty : M Bool)) then
    unsupported "function returning a struct or union (consider adding option [-fstruct-passing])"

def checkArgumentType (env : CParser.Env.T) (ty : CParser.C.Typ) : CM Unit := do
  if !(← get).flags.option_fstruct_passing && (← (CParser.Cutil.is_composite_type env ty : M Bool)) then
    unsupported "function parameter of struct or union type (consider adding option [-fstruct-passing])"

def checkFunctionType (env : CParser.Env.T) (tres : CParser.C.Typ)
    (targs : Option (List (CParser.C.Ident × CParser.C.Typ))) : CM Unit := do
  checkResultType env tres
  match targs with
  | none => pure ()
  | some l => for (_, ty) in l do checkArgumentType env ty

partial def convertTyp (env : CParser.Env.T) (t : CParser.C.Typ) (bitwidth : Option Int := none) :
    CM Ty := do
  match t with
  | .TVoid _ => return .Tvoid
  | .TInt ik a => convertIkind ik (convertAttr a)
  | .TFloat fk a => convertFkind fk (convertAttr a)
  | .TPtr ty a => return .Tpointer (← convertTyp env ty) (convertAttr a)
  | .TArray ty none a =>
    -- Cparser verified that the type ty[] occurs only in contexts that are
    -- safe for Clight, so just treat as ty[0].
    return .Tarray (← convertTyp env ty) 0 (convertAttr a)
  | .TArray ty (some sz) a =>
    return .Tarray (← convertTyp env ty) (convertIntZ sz) (convertAttr a)
  | .TFun tres targs va a =>
    checkFunctionType env tres targs
    let args ← match targs with
      | none => pure []
      | some tl => tl.mapM fun (_, ty) => convertTyp env ty
    return .Tfunction args (← convertTyp env tres) (convertCallconv targs va a)
  | .TNamed .. => convertTyp env (← (CParser.Cutil.unroll env t : M _)) bitwidth
  | .TStruct id a => return .Tstruct (← intern_string id.name) (convertAttr a)
  | .TUnion id a => return .Tunion (← intern_string id.name) (convertAttr a)
  | .TEnum id a =>
    let ik ← match bitwidth with
      | none => pure CParser.Cutil.enum_ikind
      | some w => do
        let info ← (CParser.Env.find_enum env id : M _)
        let representable (sg : Bool) : Bool :=
          info.ei_members.all fun (_, v, _) => CParser.Cutil.int_representable v w sg
        if representable false then
          pure (CParser.Cutil.unsigned_ikind_of CParser.Cutil.enum_ikind)
        else if representable true then
          pure (CParser.Cutil.signed_ikind_of CParser.Cutil.enum_ikind)
        else pure CParser.Cutil.enum_ikind
    convertIkind ik (convertAttr a)

def convertParams (env : CParser.Env.T) (l : List (CParser.C.Ident × CParser.C.Typ)) :
    CM (List Ty) :=
  l.mapM fun (_, ty) => convertTyp env ty

/-- Convert types for the arguments to a function call.  The types for fixed
    arguments are taken from the function prototype; the types for other
    arguments are taken from the types of the function arguments, after
    default argument conversion. -/
def convertTypArgs (env : CParser.Env.T) :
    List (CParser.C.Ident × CParser.C.Typ) → List CParser.C.Exp → CM (List Ty)
  | _, [] => return []
  | [], e1 :: el => do
    let t ← convertTyp env (← (CParser.Cutil.default_argument_conversion env e1.etyp : M _))
    return t :: (← convertTypArgs env [] el)
  | (_, t1) :: tl, _ :: el => do
    return (← convertTyp env t1) :: (← convertTypArgs env tl el)

/-- Convert types for the arguments to inline asm statements and to the
    special built-in functions `__builtin_annot`, `__builtin_ais_annot` and
    `__builtin_debug`: the types of the arguments after the usual unary
    conversions. -/
def convertTypAnnotArgs (env : CParser.Env.T) (el : List CParser.C.Exp) : CM (List Ty) :=
  el.mapM fun e1 => do convertTyp env (← (CParser.Cutil.unary_conversion env e1.etyp : M _))

def convertField (env : CParser.Env.T) (f : CParser.C.Field) : CM Member := do
  let id ← intern_string f.fld_name
  let ty ← convertTyp env f.fld_typ f.fld_bitfield
  match f.fld_bitfield with
  | none => return .Member_plain id ty
  | some w =>
    match ty with
    | .Tint sz sg attr => return .Member_bitfield id sz sg attr w (f.fld_name == "")
    | _ => fatal_error "bitfield must have type int"

def convertCompositedef (env : CParser.Env.T) (su : CParser.C.StructOrUnion)
    (id : CParser.C.Ident) (attr : CParser.C.Attributes) (members : List CParser.C.Field) :
    CM CompositeDef := do
  if !(CParser.Cutil.find_custom_attributes ["packed", "__packed__"] attr).isEmpty then
    unsupported "packed struct (consider adding option [-fpacked-structs])"
  let intern_name ← intern_string id.name
  let su' : SU := match su with
    | .Struct => .Struct
    | .Union => .Union
  let ms ← members.mapM (convertField env)
  return .Composite intern_name su' ms (convertAttr attr)

partial def projFunType (env : CParser.Env.T) (ty : CParser.C.Typ) :
    CM (Option (CParser.C.Typ × Option (List (CParser.C.Ident × CParser.C.Typ)) × Bool)) := do
  match ← (CParser.Cutil.unroll env ty : M _) with
  | .TFun res args vararg _ => return some (res, args, vararg)
  | .TPtr ty' _ => projFunType env ty'
  | _ => return none

def is_int64 (env : CParser.Env.T) (ty : CParser.C.Typ) : CM Bool := do
  match ← (CParser.Cutil.unroll env ty : M _) with
  | .TInt k _ => return (← (CParser.Cutil.sizeof_ikind k : M Int)) == 8
  | .TEnum .. => return false
  | _ => throw (.Failure "assert false: is_int64")

/-! ### String literals -/

partial def gensym_string_literal : CM String := do
  modify fun s => { s with stringNum := s.stringNum + 1 }
  let name := s!"__stringlit_{(← get).stringNum}"
  -- Make sure the name is not already used in the source program
  if (← get).interned.contains name then gensym_string_literal else return name

def is_C_string (s : String) : Bool := !s.contains '\x00'

def name_for_string_literal (s : String) : CM Ident := do
  match (← get).stringTable.lookup s with
  | some id => return id
  | none =>
    let name ← gensym_string_literal
    let id ← intern_string name
    let mergeable := if is_C_string s then 1 else 0
    let sec := match Sections.for_stringlit (← get).sections mergeable with
      | some sec => [sec]
      | none => []
    add_atom id
      { a_storage := .Storage_static, a_defined := true, a_alignment := some 1
        a_size := some (s.utf8ByteSize + 1)
        a_sections := sec, a_access := .Access_default, a_inline := .No_specifier
        a_literal := .String_literal, a_loc := CParser.Cutil.no_loc }
    modify fun st => { st with stringTable := (s, id) :: st.stringTable }
    return id

def typeStringLiteral (s : String) : CM Ty := do
  let sg : Signedness := if (← (CParser.getConfig : M _)).char_signed then .Signed else .Unsigned
  return .Tarray (.Tint .I8 sg noattr) (s.utf8ByteSize + 1 : Nat) noattr

def global_for_string (s : String) (id : Ident) : CM (Ident × GlobDef FunDef Ty) := do
  let init := (s.toUTF8.toList ++ [(0 : UInt8)]).map fun (c : UInt8) => InitData.Init_int8 (Integers.Int.repr c.toNat)
  return (id, .Gvar { gvar_info := ← typeStringLiteral s, gvar_init := init,
                      gvar_readonly := true, gvar_volatile := false })

def is_C_wide_string (s : List Int64) : Bool := !s.contains 0

def name_for_wide_string_literal (s : List Int64) (ik : CParser.C.IKind) : CM Ident := do
  match (← get).wstringTable.lookup (s, ik) with
  | some id => return id
  | none =>
    let name ← gensym_string_literal
    let id ← intern_string name
    let wchar_size ← (CParser.Cutil.sizeof_ikind ik : M Int)
    let mergeable := if is_C_wide_string s then wchar_size.toNat else 0
    let sec := match Sections.for_stringlit (← get).sections mergeable with
      | some sec => [sec]
      | none => []
    add_atom id
      { a_storage := .Storage_static, a_defined := true, a_alignment := some wchar_size
        a_size := some ((s.length + 1 : Nat) * wchar_size)
        a_sections := sec, a_access := .Access_default, a_inline := .No_specifier
        a_literal := .Wide_string_literal, a_loc := CParser.Cutil.no_loc }
    modify fun st => { st with wstringTable := ((s, ik), id) :: st.wstringTable }
    return id

def typeWideStringLiteral (s : List Int64) (ik : CParser.C.IKind) : CM Ty := do
  return .Tarray (← convertIkind ik noattr) (s.length + 1 : Nat) noattr

def global_for_wide_string (s : List Int64) (ik : CParser.C.IKind) (id : Ident) :
    CM (Ident × GlobDef FunDef Ty) := do
  let init_of_char ← match ← (CParser.Cutil.sizeof_ikind ik : M Int) with
    | 2 => pure fun (z : Int) => InitData.Init_int16 (Integers.Int.repr z)
    | 4 => pure fun (z : Int) => InitData.Init_int32 (Integers.Int.repr z)
    | _ => throw (.Failure "assert false: global_for_wide_string")
  let init := (s ++ [(0 : Int64)]).map fun (c : Int64) => init_of_char c.toUInt64.toNat
  return (id, .Gvar { gvar_info := ← typeWideStringLiteral s ik, gvar_init := init,
                      gvar_readonly := true, gvar_volatile := false })

def globals_for_strings (globs : List (Ident × GlobDef FunDef Ty)) :
    CM (List (Ident × GlobDef FunDef Ty)) := do
  let st ← get
  let mut globs := globs
  for ((s, ik), id) in st.wstringTable.reverse do
    globs := (← global_for_wide_string s ik id) :: globs
  for (s, id) in st.stringTable.reverse do
    globs := (← global_for_string s id) :: globs
  return globs

/-! ### Floating point constants -/

def z_of_str (hex : Bool) (str : String) (fst : Nat) : CM Int := do
  let base : Int := if hex then 16 else 10
  let mut res : Int := 0
  for c in (str.toList.drop fst) do
    let d : Int :=
      if hex && 'a' ≤ c && c ≤ 'f' then (c.toNat - 'a'.toNat + 10 : Nat)
      else if hex && 'A' ≤ c && c ≤ 'F' then (c.toNat - 'A'.toNat + 10 : Nat)
      else (c.toNat : Int) - ('0'.toNat : Int)
    if !(0 ≤ d && d < base) then throw (.Failure "assert false: z_of_str")
    res := base * res + d
  return res

def checkFloatOverflow (cls : Nat) (typ : String) : CM Unit := do
  match cls with
  | 0 => pure ()
  | 1 => warning .Literal_range s!"magnitude of floating-point constant too small for type '{typ}'"
  | 2 => warning .Literal_range s!"magnitude of floating-point constant too large for type '{typ}'"
  | _ => warning .Literal_range "floating-point converts converts to 'NaN'"

/-- Classification of a binary float: 0 finite, 1 zero, 2 infinity, 3 NaN
    (OCaml: the constructor of Flocq's `binary_float`; here read off the
    exact IEEE-754 model's `unpack`). -/
def classifyBits (spec : FloatModel.Format) (b : BitVec spec.numBits) : Nat :=
  match FloatModel.UnpackedFloat.unpack spec b with
  | .finite .. => 0
  | .zero _ => 1
  | .infinity _ => 2
  | .notANumber => 3

def classifyB64 (f : Floats.Float) : Nat :=
  classifyBits FloatModel.Format.binary64 f.bits

def classifyB32 (f : Floats.Float32) : Nat :=
  classifyBits FloatModel.Format.binary32 f.bits

def convertFloat (f : CParser.C.FloatCst) (kind : CParser.C.FKind) : CM Expr := do
  let mant ← z_of_str f.hex (f.intPart ++ f.fracPart) 0
  if mant == 0 then
    match kind with
    | .FFloat16 =>
      unsupported "'_Float16' type"
      return Ctyping.econstSingle Floats.Float32.zero
    | .FFloat => return Ctyping.econstSingle Floats.Float32.zero
    | .FDouble | .FLongDouble => return Ctyping.econstFloat Floats.Float.zero
  else
    let c0 := f.exp.toList.headD ' '
    let sgExp := c0 == '+' || c0 == '-'
    let exp ← z_of_str false f.exp (if sgExp then 1 else 0)
    let exp := if c0 == '-' then -exp else exp
    let shift_exp := (if f.hex then 4 else 1) * f.fracPart.length
    let exp := exp - shift_exp
    let base := Positive.ofNat (if f.hex then 2 else 10)
    let mant := Positive.ofNat mant.toNat
    match kind with
    | .FFloat16 =>
      unsupported "'_Float16' type"
      return Ctyping.econstSingle Floats.Float32.zero
    | .FFloat =>
      let f := Floats.Float32.from_parsed base mant exp
      checkFloatOverflow (classifyB32 f) "float"
      return Ctyping.econstSingle f
    | .FDouble | .FLongDouble =>
      let f := Floats.Float.from_parsed base mant exp
      checkFloatOverflow (classifyB64 f) "double"
      return Ctyping.econstFloat f

end C2C
end CC
