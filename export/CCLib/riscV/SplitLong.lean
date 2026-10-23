/-
  The part of `backend/SplitLong.vp` used by instruction selection on RV64,
  instantiated with the RISC-V operators.

  On RV64 (`Archi.splitlong = false`) the RISC-V `SelectLong` implements all
  64-bit operations natively (including the unsigned conversions), but it
  does not define `lowlong`.  In Rocq, `Selection.sel_switch_long` therefore
  uses `SplitLong.lowlong`; this file ports that function over the RISC-V
  `CminorSel`.
-/
import CCLib.riscV.SelectOp

namespace CC
namespace RiscV
namespace SplitLong

open Op CminorSel SelectOp

/-- CminorSel expressions (RISC-V). -/
abbrev Expr := CminorSel.Expr

open CminorSel.Expr CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `SplitLong.lowlong` -/
def lowlong (e : Expr) : Expr :=
  match e with
  | Eop .Omakelong (_ ::: e2 ::: Enil) => e2
  | _ => Eop .Olowlong (e ::: Enil)

end SplitLong
end RiscV
end CC
