/-
  Port of `cparser/Elab.ml`, part 1 of 5: utilities, declarations and
  redeclarations, constants, static assertions and attributes.

  `Elab.ml` (3360 lines of OCaml: elaboration from the `Cabs` parse tree to
  the typed C syntax tree of `C.lean`) is split into
  * `ElabBase.lean`  — this file (`Elab.ml` up to `check_bitfield`);
  * `ElabTypes.lean` — type specifiers and declarators, structs, unions,
    enums (`elab_specifier` … `elab_type`);
  * `ElabInit.lean`  — initializers (`init_char_array_string` …
    `elab_initializer`);
  * `ElabExpr.lean`  — expressions (`elab_expr`);
  * `Elab.lean`      — declarations, function definitions, statements and
    the entry point `elab_file`.

  Differences from OCaml:
  * The global references of `Elab.ml` (`top_declarations`,
    `top_environment`, `global_defines`) form the state `ElabState`, threaded
    by the monad `EM := StateT ElabState M` on top of the front-end monad `M`
    (diagnostics, fresh identifiers, machine configuration).
  * The forward reference `elab_expr_f` (set to `elab_expr ctx_constexp` once
    expressions are defined) is the type class `ElabExprFwd`, an instance
    argument of the functions that elaborate types, attributes and
    initializers; `elab_funbody_f` is not needed since the functions on
    declarations and statements are in one mutual block (`Elab.lean`).
  * `emit_elab` does not call `Debug.insert_global_declaration` (the hook
    is ported in `debug/DebugInformation.lean`, but the debug hooks run in
    `IO` and are not threaded through the front end yet).
  * Exceptions `Env.Error` turned into fatal errors by `wrap` are caught
    with `tryCatch`; the local exceptions `Overflow`, `Bad_digit` and
    `Wrong_attr_arg` are `Except`/`Option` results.
-/
import CCLib.cparser.Ceval
import CCLib.cparser.Cleanup
import CCLib.cparser.Cabs

namespace CC
namespace CParser
namespace Elab

open C Cutil Diagnostics
open CC.Cabs (Loc)

/-! ### State -/

/-- The global state of `Elab.ml`. -/
structure ElabState where
  /-- `top_declarations`: the top declarations, most recent first -/
  top_declarations : List Globdecl := []
  /-- `top_environment`: the top declarations of functions and variables
      with external or internal linkage -/
  top_environment : Env.T := Env.empty
  /-- `global_defines`: the globals with a definition -/
  global_defines : Std.HashSet String := {}
  /-- the initial environment (with the builtins), for `Env.is_builtin` -/
  initial_env : Env.T := Env.empty
  deriving Inhabited

abbrev EM := StateT ElabState M

/-- The forward reference `elab_expr_f`. -/
class ElabExprFwd where
  elabExpr : Loc → Env.T → Cabs.Expression → EM (Exp × Env.T)

/-! ### Error reporting -/

/-- `elab_loc` -/
def elab_loc (l : Loc) : Location := (l.filename, l.lineno)

def fatal_error {α} (loc : Loc) (msg : String) : EM α :=
  (Diagnostics.fatal_error (elab_loc loc) msg : M α)

def error (loc : Loc) (msg : String) : EM Unit :=
  (Diagnostics.error (elab_loc loc) msg : M Unit)

def warning (loc : Loc) (w : WarningType) (msg : String) : EM Unit :=
  (Diagnostics.warning (elab_loc loc) w msg : M Unit)

/-- `Cprint.typ_raw` as a string -/
def typ_raw (ty : Typ) : String := Cprint.toText (Cprint.typ_raw {} ty)

/-- `print_typ env ty` -/
def print_typ (env : Env.T) (ty : Typ) : EM String := do
  match ty with
  | .TNamed _ _ =>
    let ty' ← (unroll env ty : M Typ)
    if !is_anonymous_type ty' then
      return s!"'{typ_raw ty}' (aka '{typ_raw ty'}')"
    else return s!"'{typ_raw ty}'"
  | .TStruct id _ => if id.name == "" then return "'struct <anonymous>'" else return s!"'{typ_raw ty}'"
  | .TUnion id _ => if id.name == "" then return "'union <anonymous>'" else return s!"'{typ_raw ty}'"
  | .TEnum id _ => if id.name == "" then return "'enum <anonymous>'" else return s!"'{typ_raw ty}'"
  | _ => return s!"'{typ_raw ty}'"

/-- `pp_field` -/
def pp_field (id : String) : String := if id != "" then id else "<anonymous>"

/-- `wrap fn loc env arg`: `Env.Error` becomes a fatal error. -/
def wrap {α} (x : M α) (loc : Loc) : EM α := do
  match ← ((tryCatch (Except.ok <$> x) fun e => pure (Except.error e)) : M (Except Exn α)) with
  | .ok v => return v
  | .error (.EnvError msg) => fatal_error loc (Env.error_message msg)
  | .error e => throw e

/-- `previous_def fn env arg`: `none` if `fn` raises `Env.Error`. -/
def previous_def {α} (x : M α) : EM (Option α) := do
  match ← ((tryCatch (Except.ok <$> x) fun e => pure (Except.error e)) : M (Except Exn α)) with
  | .ok v => return some v
  | .error (.EnvError _) => return none
  | .error e => throw e

/-- `redef fn env arg` -/
def redef {α} (x : M (Ident × α)) (env : Env.T) : EM Bool := do
  match ← previous_def x with
  | none => return false
  | some (id, _) => return Env.in_current_scope env id

/-! ### Buffering of the result -/

def add_global_define (loc : Loc) (name : String) : EM Unit := do
  if (← get).global_defines.contains name then
    error loc s!"redefinition of '{name}'"
  modify fun s => { s with global_defines := s.global_defines.insert name }

def is_global_defined (name : String) : EM Bool :=
  return (← get).global_defines.contains name

/-- `emit_elab ?linkage env loc td` -/
def emit_elab (linkage : Bool := false) (loc : Loc) (td : GlobdeclDesc) : EM Unit := do
  let dec : Globdecl := { gdesc := td, gloc := elab_loc loc }
  modify fun s => { s with top_declarations := dec :: s.top_declarations }
  if linkage then
    match td with
    | .Gdecl (.mk sto id ty _) =>
      modify fun s => { s with top_environment := Env.add_ident s.top_environment id sto ty }
    | .Gfundef f =>
      modify fun s =>
        let te := Env.add_ident s.top_environment f.fd_name f.fd_storage (fundef_typ f)
        { s with top_environment := te }
    | _ => pure ()

/-- `reset ()` -/
def reset : EM Unit := set ({} : ElabState)

/-- `elaborated_program ()` -/
def elaborated_program : EM Program := do
  let p := (← get).top_declarations
  modify fun s => { s with top_declarations := [] }
  -- Reverse it and eliminate unreferenced declarations
  (Cleanup.program p : M Program)

/-- Monadic map for functions `env -> 'a -> 'b * env` -/
def mmap {α β} (f : Env.T → α → EM (β × Env.T)) (env : Env.T) : List α → EM (List β × Env.T)
  | [] => return ([], env)
  | hd :: tl => do
    let (hd', env1) ← f env hd
    let (tl', env2) ← mmap f env1 tl
    return (hd' :: tl', env2)

def mmap2_filter {α β γ} (f : Env.T → α → β → EM (Option γ × Env.T)) (env : Env.T) :
    List α → List β → EM (List γ × Env.T)
  | [], [] => return ([], env)
  | a1 :: l1, a2 :: l2 => do
    let (opt_hd, env1) ← f env a1 a2
    let (tl, env2) ← mmap2_filter f env1 l1 l2
    return ((match opt_hd with | some hd => hd :: tl | none => tl), env2)
  | _, _ => throw (.Failure "mmap2_filter")

/-! ### Declarations and redeclarations -/

def name_of_storage_class : Storage → String
  | .Storage_default => "<default>"
  | .Storage_extern => "'extern'"
  | .Storage_static => "'static'"
  | .Storage_auto => "'auto'"
  | .Storage_register => "'register'"

def combine_toplevel_definitions (loc : Loc) (env : Env.T) (s : String)
    (old_sto : Storage) (old_ty : Typ) (sto : Storage) (ty : Typ) : EM (Storage × Typ) := do
  let new_ty ← match ← (combine_types .AttrCompat env old_ty ty : M _) with
    | some new_ty => pure new_ty
    | none =>
      error loc s!"redefinition of '{s}' with a different type: {← print_typ env old_ty} vs {← print_typ env ty}"
      pure ty
  if ← is_global_defined s then
    let old_attrs ← (attributes_of_type env old_ty : M _)
    let new_attrs ← (attributes_of_type env ty : M _)
    if !incl_attributes new_attrs old_attrs then
      warning loc .Ignored_attributes "attribute declaration must precede definition"
  let new_sto ← match old_sto, sto with
    | .Storage_static, .Storage_static
    | .Storage_extern, .Storage_extern
    | .Storage_default, .Storage_default => pure sto
    | .Storage_auto, _ | .Storage_register, _ | _, .Storage_auto | _, .Storage_register =>
      error loc s!"unexpected {name_of_storage_class sto} declaration of '{s}'"
      pure sto
    | _, .Storage_static =>
      error loc s!"static declaration of '{s}' follows non-static declaration"
      pure sto
    | .Storage_static, _ => pure .Storage_static
    | .Storage_extern, _ =>
      if ← (is_function_type env new_ty : M Bool) then pure .Storage_extern else pure sto
    | .Storage_default, .Storage_extern =>
      if (← is_global_defined s) && (← (is_function_type env ty : M Bool)) then
        warning loc .Extern_after_definition
          "this extern declaration follows a non-extern definition and is ignored"
      pure .Storage_extern
  return (new_sto, new_ty)

def enter_or_refine_ident_base (local_ : Bool) (loc : Loc) (env : Env.T) (new_id : Ident)
    (sto : Storage) (ty : Typ) : EM (Ident × Storage × Env.T × Typ × Bool) := do
  let s := new_id.name
  if ← redef (Env.lookup_typedef env s) env then
    error loc s!"redefinition of '{s}' as different kind of symbol"
  match ← previous_def (Env.lookup_ident env s) with
  | some (old_id, .II_ident old_sto _) =>
    if local_ && Env.in_current_scope env old_id &&
       !(sto == .Storage_extern && old_sto == .Storage_extern) then
      error loc s!"redefinition of '{s}'"
  | some (old_id, .II_enum _) =>
    if Env.in_current_scope env old_id then
      error loc s!"redefinition of '{s}' as different kind of symbol"
  | _ => pure ()
  if local_ && (sto == .Storage_auto || sto == .Storage_register || sto == .Storage_static) then
    return (new_id, sto, Env.add_ident env new_id sto ty, ty, false)
  else
    match ← previous_def (Env.lookup_ident (← get).top_environment s) with
    | some (old_id, .II_ident old_sto old_ty) =>
      let (new_sto, new_ty) ← combine_toplevel_definitions loc env s old_sto old_ty sto ty
      return (old_id, new_sto, Env.add_ident env old_id new_sto new_ty, new_ty, true)
    | _ =>
      return (new_id, sto, Env.add_ident env new_id sto ty, ty, true)

def enter_or_refine_ident (local_ : Bool) (loc : Loc) (env : Env.T) (s : String)
    (sto : Storage) (ty : Typ) : EM (Ident × Storage × Env.T × Typ × Bool) := do
  enter_or_refine_ident_base local_ loc env (← (Env.fresh_ident s : M Ident)) sto ty

def enter_or_refine_function (loc : Loc) (env : Env.T) (id : Ident) (sto : Storage)
    (ty : Typ) : EM (Ident × Storage × Env.T × Typ × Bool) :=
  enter_or_refine_ident_base false loc env id sto ty

/-! ### Elaboration of constants - C99 section 6.4.4 -/

def has_suffix (s suff : String) : Bool := s.endsWith suff
def chop_last (s : String) (n : Nat) : String := (s.dropEnd n).toString
def has_prefix (s pref : String) : Bool := s.startsWith pref
def chop_first (s : String) (n : Nat) : String := (s.drop n).toString

inductive ParseIntError where
  | Overflow
  | Bad_digit

/-- `parse_int base s` (on unsigned 64-bit values) -/
def parse_int (base : Nat) (s : String) : Except ParseIntError Int64 := do
  -- (2^64-1) / base, unsigned
  let max_val : Nat := (2 ^ 64 - 1) / base
  let mut v : Nat := 0
  for c in s.toList do
    let digit ←
      if c ≥ '0' && c ≤ '9' then pure (c.toNat - 48)
      else if c ≥ 'A' && c ≤ 'F' then pure (c.toNat - 55)
      else throw .Bad_digit
    if digit ≥ base then throw .Bad_digit
    -- `!v < 0L` in OCaml: the value does not fit in 63 bits
    if v ≥ 2 ^ 63 || v > max_val then throw .Overflow
    -- because (2^64 - 1) % 10 = 5, not 9
    if base == 10 && v == max_val && digit > 5 then throw .Overflow
    v := (v * base + digit) % 2 ^ 64
  return Int64.ofNat v

/-- `integer_representable v ik` -/
def integer_representable (v : Int64) (ik : IKind) : EM Bool := do
  let bitsize := (← (sizeof_ikind ik : M Int)) * 8
  let signed ← (is_signed_ikind ik : M Bool)
  if bitsize ≥ 64 then
    return !signed || (v ≥ 0 && v ≤ 0x7FFF_FFFF_FFFF_FFFF)
  else if !signed then
    return v ≥ 0 && v.toInt < 2 ^ bitsize.toNat
  else
    return v ≥ 0 && v.toInt < 2 ^ (bitsize - 1).toNat

def elab_int_constant (loc : Loc) (s0 : String) : EM (Int64 × IKind) := do
  let s := s0.toUpper
  -- Determine possible types and chop type suffix
  let (s, dec_kinds, hex_kinds) :=
    if has_suffix s "ULL" || has_suffix s "LLU" then
      (chop_last s 3, [IKind.IULongLong], [IKind.IULongLong])
    else if has_suffix s "LL" then
      (chop_last s 2, [.ILongLong], [.ILongLong, .IULongLong])
    else if has_suffix s "UL" || has_suffix s "LU" then
      (chop_last s 2, [.IULong, .IULongLong], [.IULong, .IULongLong])
    else if has_suffix s "L" then
      (chop_last s 1, [.ILong, .ILongLong], [.ILong, .IULong, .ILongLong, .IULongLong])
    else if has_suffix s "U" then
      (chop_last s 1, [.IUInt, .IULong, .IULongLong], [.IUInt, .IULong, .IULongLong])
    else
      (s, [.IInt, .ILong, .ILongLong], [.IInt, .IUInt, .ILong, .IULong, .ILongLong, .IULongLong])
  -- Determine base
  let (s, base) :=
    if has_prefix s "0X" then (chop_first s 2, 16)
    else if has_prefix s "0" then (chop_first s 1, 8)
    else (s, 10)
  -- Parse digits
  let v ← match parse_int base s with
    | .ok v => pure v
    | .error .Overflow =>
      error loc s!"integer literal '{s0}' is too large to be represented in any integer type"
      pure 0
    | .error .Bad_digit => pure 0
  -- Find smallest allowable type that fits
  let kinds := if base == 10 then dec_kinds else hex_kinds
  let mut ty : Option IKind := none
  for k in kinds do
    if ty.isNone && (← integer_representable v k) then ty := some k
  match ty with
  | some k => return (v, k)
  | none =>
    error loc s!"integer literal '{s0}' is too large to be represented in a signed integer type.  Consider marking it as unsigned, or writing it in hexadecimal."
    return (v, .IInt)

def elab_float_constant (f : Cabs.FloatInfo) : EM (FloatCst × FKind) := do
  let ty ← match f.suffix_FI with
    | some "l" | some "L" => pure FKind.FLongDouble
    | some "f" | some "F" => pure .FFloat
    | none => pure .FDouble
    | _ => assertFalse "Elab.elab_float_constant"
  let v : FloatCst :=
    { hex := f.isHex_FI, intPart := f.integer_FI.getD "0",
      fracPart := f.fraction_FI.getD "0", exp := f.exponent_FI.getD "0" }
  return (v, ty)

/-- `%LX` of an `int64` -/
def hexInt64 (c : Int64) : String :=
  String.ofList ((Nat.toDigits 16 c.toUInt64.toNat).map Char.toUpper)

def check_char_range (loc : Loc) (ikind : IKind) (chars : List Int64) : EM Unit := do
  let bits := (← (sizeof_ikind ikind : M Int)) * 8
  for c in chars do
    -- OCaml: `c >= Int64.shift_left 1L bits` (signed comparison)
    let max : Int64 := (1 : Int64) <<< (Int64.ofInt bits)
    if c ≥ max then error loc s!"escape sequence 0x{hexInt64 c} is out of range"

def ikind_of_encoding : Cabs.Encoding → EM IKind
  | .EncNone => return .IChar
  | .EncWide => (wchar_ikind : M IKind)
  | .EncU16 => return .IUShort
  | .EncU32 => return .IUInt
  | .EncUTF8 => return .IChar

def elab_char_constant (loc : Loc) (enc : Cabs.Encoding) (chars : List Int64) :
    EM (Int64 × IKind) := do
  let len := chars.length
  -- We support multi-character constants for EncNone character literals only.
  -- We treat them as big-endian numbers in base 256.
  let v ← match chars, enc with
    | [], _ => error loc "empty character constant"; pure 0
    | [c], _ => pure c
    | _, .EncNone =>
      if (len : Int) > (← getConfig).sizeof_int then
        error loc s!"{len}-character constant too long, overflows its type"
        pure 0
      else
        check_char_range loc .IUChar chars
        pure (chars.foldl (fun acc d => (acc <<< 8) + d) 0)
    | _, _ =>
      error loc s!"{len}-character constant not supported"; pure 0
  let ik ← if enc == .EncNone && len > 1 then pure IKind.IInt else ikind_of_encoding enc
  let v' ← (Ceval.normalize_int v ik : M Int64)
  if v' != v then
    warning loc .Constant_conversion
      s!"overflow in character constant, changes value from {v} to {v'}"
  return (v', ik)

def elab_string_literal (loc : Loc) (enc : Cabs.Encoding) (chars : List Int64) :
    EM Constant := do
  let ik ← ikind_of_encoding enc
  check_char_range loc ik chars
  match enc with
  | .EncNone | .EncUTF8 =>
    -- the bytes of the string, as characters 0..255
    return .CStr (String.ofList (chars.map fun c => Char.ofNat (c.toUInt64.toNat % 256)))
  | .EncWide | .EncU16 | .EncU32 => return .CWStr chars ik

def warn_C11_literals (loc : Loc) (enc : Cabs.Encoding) (kind : String) : EM Unit := do
  let warn := fun (e : String) =>
    warning loc .Celeven_extension s!"'{e}' {kind} are a C11 extension"
  match enc with
  | .EncNone | .EncWide => pure ()
  | .EncUTF8 => warn "u8"
  | .EncU16 => warn "u"
  | .EncU32 => warn "U"

def elab_constant (loc : Loc) : Cabs.Constant → EM Constant
  | .CONST_INT s => do
    let (v, ik) ← elab_int_constant loc s
    return .CInt v ik s
  | .CONST_FLOAT f => do
    let (v, fk) ← elab_float_constant f
    return .CFloat v fk
  | .CONST_CHAR enc s => do
    warn_C11_literals loc enc "character constants"
    let ikind ← match enc with
      | .EncNone => pure IKind.IInt
      | .EncWide => (wchar_ikind : M IKind)
      | .EncU16 => pure .IUShort
      | .EncU32 => pure .IUInt
      | .EncUTF8 => assertFalse "Elab.elab_constant"
    return .CInt (← elab_char_constant loc enc s).1 ikind ""
  | .CONST_STRING wide s => do
    warn_C11_literals loc wide "string literals"
    elab_string_literal loc wide s

def elab_simple_string (loc : Loc) (enc : Cabs.Encoding) (chars : List Int64) : EM String := do
  match ← elab_string_literal loc enc chars with
  | .CStr s => return s
  | _ => error loc "cannot use wide string literal in 'asm'"; return ""

/-! ### Elaboration and checking of static assertions -/

def elab_static_assert [ElabExprFwd] (env : Env.T) (exp : Cabs.Expression) (loc_exp : Loc)
    (msg : Cabs.Constant) (loc_msg : Loc) (loc : Loc) : EM Unit := do
  let (exp, env) ← ElabExprFwd.elabExpr loc_exp env exp
  match ← (Ceval.integer_expr env exp : M _) with
  | none => error loc_exp "expression in static assertion is not an integer constant"
  | some n =>
    if n == 0 then
      match ← elab_constant loc_msg msg with
      | .CStr s => error loc s!"static assertion failed: \"{s}\""
      | _ => error loc "static assertion failed (cannot display associated message)"

/-! ### Elaboration of attributes -/

/-- `elab_attr_arg loc env a`; `none` for the exception `Wrong_attr_arg`. -/
def elab_attr_arg [ElabExprFwd] (loc : Loc) (env : Env.T) (a : Cabs.Expression) :
    EM (Option AttrArg) := do
  match a with
  | .VARIABLE s =>
    match ← previous_def (Env.lookup_ident env s) with
    | some (_, .II_ident _ _) => return some (.AIdent s)
    | some (_, .II_enum v) => return some (.AInt v)
    | none => return some (.AIdent s)
  | _ =>
    let (b, env) ← ElabExprFwd.elabExpr loc env a
    match ← (Ceval.constant_expr env b.etyp b : M _) with
    | some (.CInt n _ _) => return some (.AInt n)
    | some (.CStr s) => return some (.AString s)
    | _ => return none

def elab_gcc_attr_word : Cabs.GccAttributeWord → String
  | .GCC_ATTR_IDENT s => s
  | .GCC_ATTR_CONST => "const"
  | .GCC_ATTR_PACKED => "__packed__"

def elab_gcc_attr [ElabExprFwd] (loc : Loc) (env : Env.T) : Cabs.GccAttribute → EM (List Attribute)
  | .GCC_ATTR_EMPTY => return []
  | .GCC_ATTR_NOARGS w => return [.Attr (elab_gcc_attr_word w) []]
  | .GCC_ATTR_ARGS w args => do
    let v := elab_gcc_attr_word w
    let args' ← args.mapM (elab_attr_arg loc env)
    if args'.all Option.isSome then
      return [.Attr v (args'.filterMap id)]
    else
      warning loc .Unknown_attribute s!"unknown attribute '{v}' ignored"
      return []

def is_power_of_two (n : Int64) : Bool := n > 0 && (n &&& (n - 1)) == 0

/-- Check alignment parameter -/
def check_alignment (loc : Loc) (n : Int64) : EM Bool := do
  if !(is_power_of_two n || n == 0) then
    error loc s!"requested alignment {n} is not a power of 2"; return false
  -- OCaml's `int` has 63 bits
  else if n.toInt ≥ 2 ^ 62 || n.toInt < -(2 ^ 62) then
    error loc s!"requested alignment {n} is too large"; return false
  else return true

/-- Process GCC attributes that have special significance: "aligned" and
    "packed". -/
def enter_gcc_attr (loc : Loc) (a : Attribute) : EM (List Attribute) := do
  match a with
  | .Attr name args =>
    if name == "aligned" || name == "__aligned__" then
      match args with
      | [.AInt n] => return if ← check_alignment loc n then [a] else []
      | [_] => error loc "requested alignment is not an integer constant"; return []
      | [] => return []  -- Use default alignment, like gcc does
      | _ => error loc "'aligned' attribute takes no more than 1 argument"; return []
    else if name == "packed" || name == "__packed__" then
      match args with
      | [] => return [a]
      | [.AInt n] => return if ← check_alignment loc n then [a] else []
      | [.AInt n, .AInt p] =>
        return if (← check_alignment loc n) && (← check_alignment loc p) then [a] else []
      | [.AInt n, .AInt p, .AInt q] =>
        if q == 0 || q == 1 then
          return if (← check_alignment loc n) && (← check_alignment loc p) then [a] else []
        else error loc "ill-formed 'packed' attribute"; return []
      | _ => error loc "ill-formed 'packed' attribute"; return []
    else return [a]
  | _ => return [a]

def elab_attribute [ElabExprFwd] (env : Env.T) : Cabs.Attribute → EM Attributes
  | .GCC_ATTR l loc => do
    let mut acc : Attributes := []
    for ga in l do
      for a in ← elab_gcc_attr loc env ga do
        acc := add_attributes acc (← enter_gcc_attr loc a)
    return acc
  | .PACKED_ATTR args loc => do
    let args' ← args.mapM (elab_attr_arg loc env)
    if args'.all Option.isSome then
      enter_gcc_attr loc (.Attr "__packed__" (args'.filterMap id))
    else
      error loc "ill-formed 'packed' attribute"; return []
  | .ALIGNAS_ATTR [a] loc => do
    warning loc .Celeven_extension "'_Alignas' is a C11 extension"
    match ← elab_attr_arg loc env a with
    | some (.AInt n) =>
      return if ← check_alignment loc n then [.AAlignas n.toInt] else []
    | some _ => error loc "requested alignment is not an integer constant"; return []
    | none => error loc "bad _Alignas value"; return []
  | .ALIGNAS_ATTR _ loc => do
    error loc "_Alignas takes no more than 1 argument"; return []

def elab_attributes [ElabExprFwd] (env : Env.T) (al : List Cabs.Attribute) : EM Attributes := do
  let mut acc : Attributes := []
  for a in al do acc := add_attributes acc (← elab_attribute env a)
  return acc

/-- Warning for alignment requests that reduce the alignment below the
    natural alignment. -/
def warn_if_reduced_alignment (loc : Loc) (actual natural : Option Int) : EM Unit := do
  match actual, natural with
  | some act, some nat =>
    if act < nat then
      warning loc .Reduced_alignment
        s!"requested alignment ({act}) is less than natural alignment ({nat})"
  | _, _ => pure ()

def check_reduced_alignment (loc : Loc) (env : Env.T) (typ : Typ) : EM Unit := do
  let actual ← wrap (alignof env typ) loc
  let natural ← wrap (do alignof env (← erase_attributes_type env typ)) loc
  warn_if_reduced_alignment loc actual natural

/-! ### Auxiliaries for type specifiers and declarators -/

/-- `typespec_rank` (don't change this) -/
def typespec_rank : Cabs.TypeSpecifier → Nat
  | .Tvoid => 0
  | .Tsigned => 1
  | .Tunsigned => 2
  | .Tchar => 3
  | .Tshort => 4
  | .Tlong => 5
  | .Tint => 6
  | .Tfloat => 8
  | .Tdouble => 9
  | .T_Bool => 10
  | _ => 11  -- There should be at most one of the others

/-- Remove the non-type-related attributes from the given type and return
    those attributes separately.  If the type is a function type, keep
    function-related attributes attached to the type. -/
def get_nontype_attrs (env : Env.T) (ty : Typ) : EM (Typ × Attributes) := do
  let isFun ← (is_function_type env ty : M Bool)
  let nta ← (attributes_of_type_no_expand ty).filterM fun a => do
    match ← (class_of_attribute a : M AttributeClass) with
    | .Attr_type => return false
    | .Attr_function => return !isFun
    | _ => return true
  return (← (remove_attributes_type env nta ty : M Typ), nta)

/-- Auxiliary for elaborating bitfield declarations. -/
def check_bitfield (loc : Loc) (env : Env.T) (id : String) (ty : Typ) (ik : IKind) (n : Int64) :
    EM (Option Int) := do
  let max : Int64 := Int64.ofInt ((← (sizeof_ikind ik : M Int)) * 8)
  if n < 0 then
    error loc s!"bit-field '{pp_field id}' has negative width ({n})"
    return none
  else if n > max then
    error loc s!"size of bit-field '{pp_field id}' ({n} bits) exceeds its type ({max} bits)"
    return none
  else if n == 0 && id != "" then
    error loc s!"named bit-field '{pp_field id}' has zero width"
    return none
  else
    match ← (unroll env ty : M Typ) with
    | .TEnum eid _ =>
      let info ← wrap (Env.find_enum env eid) loc
      let w := n.toInt
      let representable := fun (sg : Bool) =>
        info.ei_members.all fun (_, v, _) => int_representable v w sg
      if !(representable false || representable true) then
        warning loc .Unnamed
          s!"not all values of type 'enum {eid.name}' can be represented in bit-field '{pp_field id}' ({w} bits are not enough)"
    | _ => pure ()
    return some n.toInt

end Elab
end CParser
end CC
