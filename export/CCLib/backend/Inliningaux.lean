/-
  Port of `backend/Inliningaux.ml`: the heuristics that decide which
  functions are inlined (the untrusted parameters `inlining_info`,
  `inlining_analysis` and `should_inline` of `Inlining`; any answer is
  correct, see `CCLib.backend.InliningproofMain`).

  A function is inlined if it is declared `inline`; a function without
  inline specifier is inlined if it is `static`, called (directly) at most
  once and its address is never taken.

  Differences from OCaml:
  * The flags `Clflags.option_finline` and
    `Clflags.option_finline_functions_called_once`, and the information
    that OCaml reads from the atom table of `C2C` (`C2C.atom_inline`,
    `C2C.atom_is_static`) are the fields of `Options`.  By default no atom
    is `static` and none has an inline specifier, so nothing is inlined;
    the driver fills these fields from the result of `C2C`.
  * The set of address-taken globals (`PSet`, an AVL set of positives in
    OCaml) is a `PTree Unit`.
  * `Compiler.Config.shouldInline` takes the program, the result of
    `inlining_analysis`, as its first argument; `shouldInlineProgram`
    composes the analysis and `should_inline`.
-/
import CCLib.backend.Inlining
import CCLib.common.ASTTheory
import CCLib.cfrontend.C2CBase

namespace CC
namespace Inliningaux

open RTL

/-- The flags and the `C2C` information read by the heuristics. -/
structure Options where
  /-- `Clflags.option_finline` -/
  option_finline : Bool := true
  /-- `Clflags.option_finline_functions_called_once` -/
  option_finline_functions_called_once : Bool := true
  /-- `C2C.atom_is_static` -/
  atomIsStatic : Ident → Bool := fun _ => false
  /-- `C2C.atom_inline` -/
  atomInline : Ident → C2C.InlineStatus := fun _ => .No_specifier

/-- `inlining_info` -/
structure InliningInfo where
  /-- Count the number of direct calls to a function -/
  call_cnt : PTree Nat
  /-- The set of globals which have their address taken -/
  addr_taken : PTree Unit

/-- `empty_inlining_info` -/
def empty_inlining_info : InliningInfo :=
  { call_cnt := PTree.empty, addr_taken := PTree.empty }

/-- `call_count` -/
def call_count (id : Ident) (io : InliningInfo) : Nat :=
  (io.call_cnt.get id).getD 0

/-- `called` -/
def called (id : Ident) (io : InliningInfo) : InliningInfo :=
  { io with call_cnt := io.call_cnt.set id (1 + call_count id io) }

/-- `address_taken` -/
def address_taken (id : Ident) (io : InliningInfo) : Bool :=
  (io.addr_taken.get id).isSome

/-- `used_id` -/
def used_id (io : InliningInfo) : List Ident → InliningInfo
  | [] => io
  | id :: ids => used_id { io with addr_taken := io.addr_taken.set id () } ids

/-- `used_in_globvar` -/
def used_in_globvar (io : InliningInfo) (gv : GlobVar Unit) : InliningInfo :=
  gv.gvar_init.foldl (fun io d =>
    match d with
    | .Init_addrof id _ => used_id io [id]
    | _ => io) io

/-- The effect of one instruction on the analysis (`inst` of
    `fun_inline_analysis`). -/
def inst (io : InliningInfo) (_nid : Node) : Instruction → InliningInfo
  | .Iop op _ _ _ => used_id io (Op.globalsOperation op)
  | .Iload _ addr _ _ _ => used_id io (Op.globalsAddressing addr)
  | .Istore _ addr _ _ _ => used_id io (Op.globalsAddressing addr)
  | .Ibuiltin _ args _ _ => used_id io (BuiltinArg.globalsList args)
  | .Icall _ (.inr cid) _ _ _ => called cid io
  | .Itailcall _ (.inr cid) _ => called cid io
  | _ => io

/-- `fun_inline_analysis` -/
def fun_inline_analysis (_id : Ident) (io : InliningInfo) (fn : RTL.Function) : InliningInfo :=
  PTree.fold inst fn.fn_code io

/-- `inlining_analysis`: gather information about the program used for the
    inlining heuristic. -/
def inlining_analysis (o : Options) (p : RTL.Program) : InliningInfo :=
  if o.option_finline && o.option_finline_functions_called_once then
    p.prog_defs.foldl (fun io idg =>
      match idg with
      | (fid, .Gfun (.Internal f)) => fun_inline_analysis fid io f
      | (_, .Gvar gv) => used_in_globvar io gv
      | _ => io) empty_inlining_info
  else empty_inlining_info

/-- `static_called_once`: is a function static and called only once? -/
def static_called_once (o : Options) (id : Ident) (io : InliningInfo) : Bool :=
  if o.option_finline_functions_called_once then
    o.atomIsStatic id && decide (call_count id io ≤ 1) && !address_taken id io
  else false

/-- `should_inline` -/
def should_inline (o : Options) (io : InliningInfo) (id : Ident) (_f : RTL.Function) : Bool :=
  if o.option_finline then
    match o.atomInline id with
    | .Inline => true
    | .Noinline => false
    | .No_specifier => static_called_once o id io
  else false

/-- `should_inline (inlining_analysis p)`, the form expected by
    `Compiler.Config.shouldInline`. -/
def shouldInlineProgram (o : Options) (p : RTL.Program) (id : Ident) (f : RTL.Function) : Bool :=
  should_inline o (inlining_analysis o p) id f

/-! ## Basic properties -/

/-- With `-fno-inline`, nothing is inlined. -/
theorem should_inline_no_finline (o : Options) (h : o.option_finline = false)
    (io : InliningInfo) (id : Ident) (f : RTL.Function) : should_inline o io id f = false := by
  simp [should_inline, h]

/-- A function declared `noinline` is never inlined. -/
theorem should_inline_noinline (o : Options) (io : InliningInfo) (id : Ident) (f : RTL.Function)
    (h : o.atomInline id = .Noinline) : should_inline o io id f = false := by
  unfold should_inline; split <;> simp [h]

/-- With the default options, nothing is inlined. -/
theorem shouldInlineProgram_default (p : RTL.Program) (id : Ident) (f : RTL.Function) :
    shouldInlineProgram {} p id f = false := by
  simp [shouldInlineProgram, should_inline, static_called_once]

/-- A function whose address is taken is inlined only if declared
    `inline`. -/
theorem should_inline_address_taken (o : Options) (io : InliningInfo) (id : Ident)
    (f : RTL.Function) (h : address_taken id io = true) (hi : o.atomInline id ≠ .Inline) :
    should_inline o io id f = false := by
  unfold should_inline static_called_once
  split
  · cases hk : o.atomInline id <;> simp_all
  · rfl

end Inliningaux
end CC
