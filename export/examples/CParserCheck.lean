/-
  Checks of the port of CompCert's untrusted C front end (`cparser/`):
  `Machine`, `Env`, `Cutil` (sizes, alignments, layout, conversions),
  `Ceval` (constant evaluation), `Cprint` (printing), and the
  source-to-source passes `Unblock`, `SwitchNorm`, `StructPassing`,
  `PackedStructs`, `Rename` and `Cleanup`, run on small hand-built
  elaborated programs.  The `#guard`s run when this file is built.
-/
import CCLib.cparser.Cleanup
import CCLib.cparser.Unblock
import CCLib.cparser.SwitchNorm
import CCLib.cparser.StructPassing
import CCLib.cparser.PackedStructs
import CCLib.cparser.Rename
import CCLib.cparser.Checks
import CCLib.cparser.Cflow
import CCLib.cparser.GCC
import CCLib.cparser.ExtendedAsm
import CCLib.x86.CBuiltins

namespace CParserCheck
open CC CParser C Cutil

/-- Run a front-end computation with the given machine configuration. -/
def run {α} (cfg : Machine.T) (x : M α) : Option α × Array String :=
  match x.run { config := cfg } with
  | .ok a s => (some a, s.messages)
  | .error _ s => (none, s.messages)

def runV {α} [Inhabited α] (cfg : Machine.T) (x : M α) : α := (run cfg x).1.getD default

def tint : Typ := .TInt .IInt []
def tchar : Typ := .TInt .IChar []
def tdouble : Typ := .TFloat .FDouble []
def tlong : Typ := .TInt .ILong []

/-! ### Attributes are kept sorted as in OCaml's polymorphic order -/

#guard add_attributes [.AVolatile, .Attr "aligned" [.AInt 8]] [.AConst, .AAlignas 4] ==
  [.AConst, .AVolatile, .AAlignas 4, .Attr "aligned" [.AInt 8]]
#guard remove_attributes [.AConst, .AVolatile] [.AConst] == [.AVolatile]
#guard incl_attributes [.AConst] [.AConst, .AVolatile]
#guard normalize_attrname "__packed__" == "packed"
#guard normalize_attrname "packed" == "packed"
#guard alignas_attribute [.AAlignas 4, .Attr "aligned" [.AInt 16]] == 16

/-! ### Sizes, alignments, struct layout -/

/-- `struct s { char c; double d; int i; }` and `union u { char c; int i; }`
    entered in an environment. -/
def envWithS : M (Env.T × Ident × Ident) := do
  let flds : List Field :=
    [{ fld_name := "c", fld_typ := tchar, fld_bitfield := none, fld_anonymous := false },
     { fld_name := "d", fld_typ := tdouble, fld_bitfield := none, fld_anonymous := false },
     { fld_name := "i", fld_typ := tint, fld_bitfield := none, fld_anonymous := false }]
  let ci ← composite_info_def Env.empty .Struct [] flds
  let (sid, env) ← Env.enter_composite Env.empty "s" ci
  let uflds : List Field :=
    [{ fld_name := "c", fld_typ := tchar, fld_bitfield := none, fld_anonymous := false },
     { fld_name := "i", fld_typ := tint, fld_bitfield := none, fld_anonymous := false }]
  let uci ← composite_info_def env .Union [] uflds
  let (uid, env) ← Env.enter_composite env "u" uci
  return (env, sid, uid)

def sizes (cfg : Machine.T) : List (Option Int) := runV cfg do
  let (env, sid, uid) ← envWithS
  return [← sizeof env (.TStruct sid []), ← alignof env (.TStruct sid []),
          ← sizeof env (.TUnion uid []), ← sizeof env tlong,
          ← sizeof env (.TArray tint (some 10) []), ← sizeof env (.TArray tint none [])]

#guard sizes Machine.x86_64 == [some 24, some 8, some 4, some 8, some 40, none]
#guard sizes Machine.x86_32 == [some 16, some 4, some 4, some 4, some 40, none]
#guard sizes Machine.win64 == [some 24, some 8, some 4, some 4, some 40, none]

/- Offsets of the members of `struct s`. -/
#guard runV Machine.x86_64 (do
  let (env, sid, _) ← envWithS
  let ci ← Env.find_struct env sid
  struct_layout env ci.ci_attr ci.ci_members) == [("i", 16), ("d", 8), ("c", 0)]

/- A packed struct: `struct __attribute__((packed)) p { char c; int i; }`. -/
#guard runV Machine.x86_64 (do
  let flds : List Field :=
    [{ fld_name := "c", fld_typ := tchar, fld_bitfield := none, fld_anonymous := false },
     { fld_name := "i", fld_typ := tint, fld_bitfield := none, fld_anonymous := false }]
  let ci ← composite_info_def Env.empty .Struct [.Attr "packed" []] flds
  return (ci.ci_sizeof, ci.ci_alignof)) == (some 5, some 1)

/- Bit fields: `struct b { unsigned a : 3; unsigned b : 30; }` is 8 bytes. -/
#guard runV Machine.x86_64 (do
  let ui : Typ := .TInt .IUInt []
  let flds : List Field :=
    [{ fld_name := "a", fld_typ := ui, fld_bitfield := some 3, fld_anonymous := false },
     { fld_name := "b", fld_typ := ui, fld_bitfield := some 30, fld_anonymous := false }]
  let ci ← composite_info_def Env.empty .Struct [] flds
  return ci.ci_sizeof) == some 8

/-! ### Conversions -/

#guard runV Machine.x86_64 (binary_conversion Env.empty (.TInt .IUInt []) tlong) == tlong
#guard runV Machine.x86_32 (binary_conversion Env.empty (.TInt .IUInt []) tlong) ==
  .TInt .IULong []
#guard runV Machine.x86_64 (binary_conversion Env.empty tchar (.TInt .IShort [])) == tint
#guard runV Machine.x86_64 (binary_conversion Env.empty tint tdouble) == tdouble
#guard runV Machine.x86_64 (is_signed_ikind .IChar) == true
#guard runV Machine.aarch64 (is_signed_ikind .IChar) == false
#guard runV Machine.x86_64 size_t_ikind == .IULong
#guard runV Machine.win64 size_t_ikind == .IULongLong

/-! ### Constant evaluation -/

def ic (n : Int64) (ik : IKind := .IInt) : Exp := intconst n ik
def bin (op : BinaryOperator) (a b : Exp) (ty : Typ := tint) : Exp := .mk (.EBinop op a b ty) ty

#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty
  (bin .Oadd (ic 40) (bin .Omul (ic 1) (ic 2)))) == some 42
/- Unsigned arithmetic wraps: `0u - 1u == 4294967295`. -/
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty
  (bin .Osub (ic 0 .IUInt) (ic 1 .IUInt) (.TInt .IUInt []))) == some 4294967295
/- Signed division truncates toward zero. -/
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty (bin .Odiv (ic (-7)) (ic 2))) == some (-3)
/- Division by zero is not a constant. -/
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty (bin .Odiv (ic 7) (ic 0))) == none
/- `(char) 300 == 44`, `(unsigned char) -1 == 255`. -/
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty (ecast tchar (ic 300))) == some 44
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty
  (ecast (.TInt .IUChar []) (ic (-1)))) == some 255
/- `sizeof(long)` and comparisons. -/
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty (.mk (.ESizeof tlong) tlong)) == some 8
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty (bin .Olt (ic (-1)) (ic 1))) == some 1
#guard runV Machine.x86_64 (Ceval.integer_expr Env.empty
  (bin .Olt (ic (-1) .IUInt) (ic 1 .IUInt) (.TInt .IUInt []))) == some 0
#guard Ceval.int64_unsigned_div (-1) 10 == 1844674407370955161
#guard Ceval.int64_unsigned_mod (-1) 10 == 5

/-! ### Printing -/

def pr (d : Format.Doc) : String := Cprint.toText d

#guard pr (Cprint.typ {} (.TPtr (.TArray tint (some 3) []) [])) == "int (*)[3]"
#guard pr (Cprint.typ {} (.TFun tint (some [({ name := "x", stamp := 1 }, tchar)]) true []))
  == "int(char x, ...)"
#guard pr (Cprint.exp {} 0 (bin .Omul (bin .Oadd (ic 1) (ic 2)) (ic 3))) == "(1 + 2) * 3"
#guard pr (Cprint.exp {} 0 (bin .Oadd (ic 1) (bin .Omul (ic 2) (ic 3)))) == "1 + 2 * 3"
#guard pr (Cprint.const {} (.CStr "a\"b\n")) == "\"a\\\"b\\n\""
#guard pr (Cprint.const {} (.CInt 5 .IULong "")) == "5UL"

/-! ### Source-to-source passes on a small program -/

def loc : Location := ("t.c", 1)
def mkS (d : StmtDesc) : Stmt := .mk d loc
def var (id : Ident) (ty : Typ) : Exp := .mk (.EVar id) ty

/-- `struct pt { int x; int y; };`
    `struct pt mk(int a) { struct pt r = { a, 2 }; return r; }`
    `int f(int n) { switch (n) { case 1: { int k = n + 1; return k; } default: return 0; } }`
    `static int unused_g;` -/
def prog : M Program := do
  let pt ← Env.fresh_ident "pt"
  let fx : Field := { fld_name := "x", fld_typ := tint, fld_bitfield := none, fld_anonymous := false }
  let fy : Field := { fld_name := "y", fld_typ := tint, fld_bitfield := none, fld_anonymous := false }
  let tpt : Typ := .TStruct pt []
  let mkId ← Env.fresh_ident "mk"
  let a ← Env.fresh_ident "a"
  let r ← Env.fresh_ident "r"
  let body_mk := mkS (.Sblock [
    mkS (.Sdecl (.mk .Storage_auto r tpt
      (some (.Init_struct pt [(fx, .Init_single (var a tint)), (fy, .Init_single (ic 2))])))),
    mkS (.Sreturn (some (var r tpt)))])
  let fmk : Fundef :=
    { fd_storage := .Storage_default, fd_inline := false, fd_name := mkId, fd_attrib := [],
      fd_ret := tpt, fd_params := [(a, tint)], fd_vararg := false, fd_locals := [],
      fd_body := body_mk }
  let f ← Env.fresh_ident "f"
  let n ← Env.fresh_ident "n"
  let k ← Env.fresh_ident "k"
  let body_f := mkS (.Sblock [mkS (.Sswitch (var n tint) (mkS (.Sblock [
    mkS (.Slabeled (.Scase (ic 1) 1) (mkS (.Sblock [
      mkS (.Sdecl (.mk .Storage_auto k tint (some (.Init_single (bin .Oadd (var n tint) (ic 1)))))),
      mkS (.Sreturn (some (var k tint)))]))),
    mkS (.Slabeled .Sdefault (mkS (.Sreturn (some (ic 0)))))])))])
  let ff : Fundef :=
    { fd_storage := .Storage_default, fd_inline := false, fd_name := f, fd_attrib := [],
      fd_ret := tint, fd_params := [(n, tint)], fd_vararg := false, fd_locals := [],
      fd_body := body_f }
  let g ← Env.fresh_ident "unused_g"
  return [{ gdesc := .Gcompositedecl .Struct pt [], gloc := loc },
          { gdesc := .Gcompositedef .Struct pt [] [fx, fy], gloc := loc },
          { gdesc := .Gfundef fmk, gloc := loc },
          { gdesc := .Gfundef ff, gloc := loc },
          { gdesc := .Gdecl (.mk .Storage_static g tint none), gloc := loc }]

/-- The pipeline of `Parse.transform_program` (Unblock, SwitchNorm full,
    StructPassing, Rename) after `Cleanup`, printed. -/
def pipeline (cfg : Machine.T) : Option String × Array String :=
  run cfg do
    let p ← prog
    let p ← Cleanup.program p.reverse
    let p ← Unblock.program false Env.empty p
    let p ← SwitchNorm.program true p
    let p ← StructPassing.program false Env.empty p
    let p ← Rename.program [] p
    return pr (Cprint.program {} p)

/- On x86-64 (`SR_ref`) `mk` returns its result through a pointer; the
   unused static `unused_g` is removed by `Cleanup`; the block-scoped `k` and
   the initializer of `r` are moved out of the blocks by `Unblock`. -/
#guard pipeline Machine.x86_64 == (some "extern void __builtin_debug(int kind, ...);\n\nstruct pt;\n\nstruct pt {\n  int x;\n  int y;\n};\n\nvoid __attribute__((__structreturn)) mk(struct pt * _res, int a)\n{\n  struct pt r;\n  r.x = a;\n  r.y = 2;\n  *_res = r;\n  return;\n}\n\nint f(int n)\n{\n  int k;\n  switch (n) {\n    case 1:\n    k = n + 1;\n    return k;\n    default:\n    return 0;\n  }\n}\n\n\n", #[])

/- On 32-bit macOS (`SR_int1248`, unaligned accesses allowed) the 8-byte
   struct is returned as an `unsigned long long`. -/
#guard pipeline Machine.x86_32_macos == (some "extern void __builtin_debug(int kind, ...);\n\nstruct pt;\n\nstruct pt {\n  int x;\n  int y;\n};\n\nunsigned long long mk(int a)\n{\n  struct pt r;\n  unsigned char * _res;\n  r.x = a;\n  r.y = 2;\n  _res = (unsigned char *) &r;\n  return *((unsigned long long *) _res);\n}\n\nint f(int n)\n{\n  int k;\n  switch (n) {\n    case 1:\n    k = n + 1;\n    return k;\n    default:\n    return 0;\n  }\n}\n\n\n", #[])

/-! ### Unstructured `switch` (Duff's device style) -/

/-- `switch (n) { case 0: while (n) { n--; case 1: n++; } }` -/
def duff (unstructured : Bool) : Option String × Array String := run Machine.x86_64 do
  let n ← Env.fresh_ident "n"
  let f ← Env.fresh_ident "g"
  let vn := var n tint
  let body := mkS (.Sswitch vn (mkS (.Slabeled (.Scase (ic 0) 0)
    (mkS (.Swhile vn (mkS (.Sseq (mkS (.Sdo (.mk (.EUnop .Opostdecr vn) tint)))
      (mkS (.Slabeled (.Scase (ic 1) 1) (mkS (.Sdo (.mk (.EUnop .Opostincr vn) tint))))))))))))
  let fd : Fundef :=
    { fd_storage := .Storage_default, fd_inline := false, fd_name := f, fd_attrib := [],
      fd_ret := .TVoid [], fd_params := [(n, tint)], fd_vararg := false, fd_locals := [],
      fd_body := body }
  let p ← SwitchNorm.program unstructured [{ gdesc := .Gfundef fd, gloc := loc }]
  return pr (Cprint.program {} p)

/- As in OCaml, the synthesized `default` case comes first. -/
#guard duff true == (some "void g(int n)\n{\n  switch (n) {\n    default:\n    goto @3;\n    case 0:\n    goto @1;\n    case 1:\n    goto @2;\n  }\n  @1:\n  while (n) {\n    n--;\n    @2:\n    n++;\n  }\n  @3:\n  /*skip*/;\n}\n\n\n", #[])
#guard (duff false).2 == #["t.c:1: error: unsupported feature: non-structured 'switch' statement (consider adding option [-funstructured-switch])"]

/-! ### Control-flow analysis -/

def returns (s : Stmt) : Option (Bool × Bool) :=
  (run Machine.x86_64 (Cflow.function_returns Env.empty s)).1

#guard returns (mkS (.Sreturn (some (ic 0)))) == some (true, false)
#guard returns (mkS .Sskip) == some (true, true)
/- `while (1) ;` never returns -/
#guard returns (mkS (.Swhile (ic 1) (mkS .Sskip))) == some (false, false)
/- `while (1) { break; }` falls through -/
#guard returns (mkS (.Swhile (ic 1) (mkS .Sbreak))) == some (true, true)

/-! ### Extended asm -/

def tgtX86 : ExtendedAsm.TargetAsm :=
  { asm_mem_argument := X86.CBuiltins.asm_mem_argument,
    is_register_name := fun s => s == "rax" || s == "rbx",
    is_scratch_register := fun _ => false }

#guard (run Machine.x86_64 do
  let x ← Env.fresh_ident "x"
  let y ← Env.fresh_ident "y"
  ExtendedAsm.transf_asm tgtX86 loc Env.empty "mov %1, %0; add %[c], %0; lea %3, %%rax"
    [(none, "=r", var x tint)] [(none, "r", var y tint), (some "c", "i", ic 5),
                                 (none, "m", var y tint)] ["rax", "memory"]).1.map (·.1)
  == some "mov %1, %0; add 5, %0; lea 0(%2), %%rax"

/-! ### Builtins and the initial environment -/

#guard runV Machine.x86_64 (do
  let b ← GCC.builtins
  let i ← Env.set_builtins b
  return (b.builtin_functions.length, i.is_builtin "__builtin_memcpy_aligned",
    i.is_builtin "__builtin_sqrt", (i.initial_declarations).length)) == (136, false, true, 137)

/-! ### Warnings of `Checks` -/

#guard (run Machine.x86_64 do
  let f ← Env.fresh_ident "h"
  let u ← Env.fresh_ident "u"
  let fd : Fundef :=
    { fd_storage := .Storage_default, fd_inline := false, fd_name := f,
      fd_attrib := [.Attr "frobnicate" []], fd_ret := .TVoid [], fd_params := [(u, tint)],
      fd_vararg := false, fd_locals := [], fd_body := mkS .Sskip }
  let p : Program := [{ gdesc := .Gfundef fd, gloc := loc }]
  Diagnostics.wall
  Checks.unused_variables Env.empty p
  Checks.unknown_attrs_program Env.empty p).2 ==
  #["t.c:1: warning: unused variable 'u' [-Wunused-variable]",
    "t.c:1: warning: unknown attribute 'frobnicate' ignored [-Wunknown-attributes]"]

/- `%2` names the constant operand, which is only reachable as `%[c]`. -/
#guard (run Machine.x86_64 do
  let x ← Env.fresh_ident "x"
  let y ← Env.fresh_ident "y"
  ExtendedAsm.transf_asm tgtX86 loc Env.empty "mov %2, %0"
    [(none, "=r", var x tint)] [(none, "r", var y tint), (some "c", "i", ic 5)] []).2
  == #["t.c:1: error: '%2' in asm text does not designate any operand"]

end CParserCheck
