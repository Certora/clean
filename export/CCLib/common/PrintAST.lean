/-
  Useful functions for pretty-printers — port of `common/PrintAST.ml`.

  The OCaml functions print to a formatter (`fprintf oc ...`); here they
  return strings.  A printer argument `px : out_channel -> 'a -> unit`
  becomes a function `px : A → String`.
-/
import CCLib.lib.Camlcoq

namespace CC
namespace PrintAST

open Camlcoq

/-- `comparison_name`, which `backend/PrintCminor.ml` and every target's
    `PrintOp.ml` define identically. -/
def comparisonName : Comparison → String
  | .Ceq => "=="
  | .Cne => "!="
  | .Clt => "<"
  | .Cle => "<="
  | .Cgt => ">"
  | .Cge => ">="

/-- `PrintAST.name_of_type` -/
def nameOfType : ATyp → String
  | .Tint => "int"
  | .Tfloat => "float"
  | .Tlong => "long"
  | .Tsingle => "single"
  | .Tany32 => "any32"
  | .Tany64 => "any64"

/-- `PrintAST.name_of_xtype` -/
def nameOfXtype : XType → String
  | .Xbool => "bool"
  | .Xint8signed => "int8s"
  | .Xint8unsigned => "int8u"
  | .Xint16signed => "int16s"
  | .Xint16unsigned => "int16u"
  | .Xint => "int"
  | .Xfloat => "float"
  | .Xlong => "long"
  | .Xsingle => "single"
  | .Xany32 => "any32"
  | .Xany64 => "any64"
  | .Xptr => "ptr"
  | .Xvoid => "void"

/-- `PrintAST.name_of_chunk` -/
def nameOfChunk : Chunk → String
  | .Mbool => "bool"
  | .Mint8signed => "int8s"
  | .Mint8unsigned => "int8u"
  | .Mint16signed => "int16s"
  | .Mint16unsigned => "int16u"
  | .Mint32 => "int32"
  | .Mint64 => "int64"
  | .Mfloat32 => "float32"
  | .Mfloat64 => "float64"
  | .Many32 => "any32"
  | .Many64 => "any64"

/-- `PrintAST.name_of_external` -/
def nameOfExternal : ExtFun → String
  | .EF_external name _ => s!"extern {escapedString name}"
  | .EF_builtin name _ => s!"builtin {escapedString name}"
  | .EF_runtime name _ => s!"runtime {escapedString name}"
  | .EF_vload chunk => s!"volatile load {nameOfChunk chunk}"
  | .EF_vstore chunk => s!"volatile store {nameOfChunk chunk}"
  | .EF_malloc => "malloc"
  | .EF_free => "free"
  | .EF_memcpy sz al => s!"memcpy size {sz} align {al} "
  | .EF_annot _ text _ => s!"annot {escapedString text}"
  | .EF_annot_val _ text _ => s!"annot_val {escapedString text}"
  | .EF_inline_asm text _ _ => s!"inline_asm {escapedString text}"
  | .EF_debug kind text _ => s!"debug{kind.toNat} {escapedString (externAtom text)}"

/-- `%ld` of `camlint_of_coqint` -/
def int32 (n : Integers.Int) : String := toString (Integers.Int.signed n)
/-- `%Ld` of `camlint64_of_coqint` -/
def int64 (n : Integers.Int64) : String := toString (Integers.Int64.signed n)
/-- `%Ld` of `camlint64_of_ptrofs` -/
def ptrofs (n : Integers.Ptrofs) : String :=
  toString (Integers.Int64.signed (Integers.Int64.repr (Integers.Ptrofs.unsigned n)))
/-- `%ld` of `camlint_of_coqint` applied to a `ptrofs` (as in the
    `BA_loadstack` … cases of `print_builtin_arg`, where OCaml reads the
    offset as a 32-bit integer). -/
def ptrofs32 (n : Integers.Ptrofs) : String :=
  toString (Integers.Int.signed (Integers.Int.repr (Integers.Ptrofs.unsigned n)))

/-- `PrintAST.print_builtin_arg` -/
def printBuiltinArg {A : Type} (px : A → String) : BuiltinArg A → String
  | .BA x => px x
  | .BA_int n => s!"int {int32 n}"
  | .BA_long n => s!"long {int64 n}"
  | .BA_float n => s!"float {floatF n 15}"
  | .BA_single n => s!"single {float32F n 15}"
  | .BA_loadstack chunk ofs => s!"{nameOfChunk chunk}[sp + {ptrofs32 ofs}]"
  | .BA_addrstack ofs => s!"sp + {ptrofs32 ofs}"
  | .BA_loadglobal chunk id ofs =>
    s!"{nameOfChunk chunk}[&{externAtom id} + {ptrofs32 ofs}]"
  | .BA_addrglobal id ofs => s!"&{externAtom id} + {ptrofs32 ofs}"
  | .BA_splitlong hi lo => s!"splitlong({printBuiltinArg px hi}, {printBuiltinArg px lo})"
  | .BA_addptr a1 a2 => s!"addptr({printBuiltinArg px a1}, {printBuiltinArg px a2})"

/-- `PrintAST.print_builtin_args` -/
def printBuiltinArgs {A : Type} (px : A → String) (al : List (BuiltinArg A)) : String :=
  ", ".intercalate (al.map (printBuiltinArg px))

/-- `PrintAST.print_builtin_res` -/
def printBuiltinRes {A : Type} (px : A → String) : BuiltinRes A → String
  | .BR x => px x
  | .BR_none => "_"
  | .BR_splitlong hi lo => s!"splitlong({printBuiltinRes px hi}, {printBuiltinRes px lo})"

#guard nameOfExternal (.EF_memcpy 8 4) = "memcpy size 8 align 4 "
#guard nameOfExternal (.EF_external "printf" default) = "extern \"printf\""
#guard printBuiltinArgs (fun (n : Nat) => s!"x{n}")
  [.BA 1, .BA_int (Integers.Int.repr (-3)), .BA_splitlong (.BA 2) (.BA 3)] =
  "x1, int -3, splitlong(x2, x3)"
#guard printBuiltinRes (fun (n : Nat) => s!"x{n}") .BR_none = "_"

end PrintAST
end CC
