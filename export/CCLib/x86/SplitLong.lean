/-
  The parts of `backend/SplitLong.vp` used by instruction selection on
  x86-64, instantiated with the x86 operators.

  On x86-64 (`Archi.splitlong = false`) the x86 `SelectLong` implements the
  64-bit operations natively, but it does not define the unsigned 64-bit
  integer / float conversions, nor `lowlong`.  In Rocq, `Selection.v`
  therefore picks up `SplitLong.longuoffloat`, `SplitLong.floatoflongu`,
  `SplitLong.longuofsingle`, `SplitLong.singleoflongu` (calls to the runtime
  helper functions `__compcert_i64_dtou`, `__compcert_i64_utod`,
  `__compcert_i64_utof`) and `SplitLong.lowlong` (used by `sel_switch_long`).
  This file ports exactly those functions over the x86 `CminorSel`.

  The target-independent parts — the record `helper_functions`
  (`SplitLong.HelperFunctions`) and the helper signatures `sig_*` — are
  shared with `CCLib/backend/SplitLong.lean`.
-/
import CCLib.backend.SplitLong
import CCLib.x86.SelectOp

namespace CC
namespace X86
namespace SplitLong

open Op CminorSel SelectOp
open CC.SplitLong (HelperFunctions sigFL sigLF sigLS)

/-- CminorSel expressions (x86). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists (x86). -/
abbrev Exprlist := CminorSel.Exprlist

open CminorSel.Expr CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `SplitLong.lowlong` -/
def lowlong (e : Expr) : Expr :=
  match e with
  | Eop .Omakelong (_ ::: e2 ::: Enil) => e2
  | _ => Eop .Olowlong (e ::: Enil)

section SELECT
variable (hf : HelperFunctions)

/-- `SplitLong.longuoffloat` -/
def longuoffloat (arg : Expr) : Expr := Eexternal hf.i64_dtou sigFL (arg ::: Enil)
/-- `SplitLong.floatoflongu` -/
def floatoflongu (arg : Expr) : Expr := Eexternal hf.i64_utod sigLF (arg ::: Enil)
/-- `SplitLong.longuofsingle` -/
def longuofsingle (arg : Expr) : Expr := longuoffloat hf (floatofsingle arg)
/-- `SplitLong.singleoflongu` -/
def singleoflongu (arg : Expr) : Expr := Eexternal hf.i64_utof sigLS (arg ::: Enil)

end SELECT

end SplitLong
end X86
end CC
