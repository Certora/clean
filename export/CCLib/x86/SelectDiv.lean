/-
  Instruction selection for division and modulus, x86 instance — port of
  `backend/SelectDiv.vp` (whole file) instantiated with the x86 operators
  (`CCLib/x86/SelectOp.lean`, `CCLib/x86/SelectLong.lean`).

  In this port `CCLib/backend/SelectDiv.lean` is the aarch64 instance.  The
  target-independent parameter computations (`find_div_mul_params`,
  `divs_mul_params`, `divu_mul_params`, `divls_mul_params`,
  `divlu_mul_params`) are reused from there.

  As in Rocq, `is_longconst` is the one of the target's `SelectLong` (on x86-64
  it recognises `Eop (Olongconst n) Enil`).

  Differences from Rocq: the OCaml parameter `Compopts.optim_for_size` is an
  explicit argument `optimForSize`; the section variable `hf` is dropped (on
  x86-64, `Archi.splitlong = false`, so `SelectLong` does not use helper
  functions).
-/
import CCLib.backend.SelectDiv
import CCLib.x86.SelectLong

namespace CC
namespace X86
namespace SelectDiv

open Op CminorSel SelectOp SelectLong
open CC.SelectDiv (divsMulParams divuMulParams divlsMulParams divluMulParams)

/-- CminorSel expressions (x86). -/
abbrev Expr := CminorSel.Expr

open CminorSel.Expr CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `SelectDiv.is_intconst` -/
def isIntconst (e : Expr) : Option Integers.Int :=
  match e with
  | Eop (.Ointconst n) _ => some n
  | _ => none

section SELECT
variable (optimForSize : Bool)

/-! ## 32-bit integer division -/

/-- `SelectDiv.divu_mul` -/
def divuMul (p m : Z) : Expr :=
  shruimm (mulhu (Eletvar 0) (Eop (.Ointconst (Integers.Int.repr m)) Enil)) (Integers.Int.repr p)

/-- `SelectDiv.divuimm` -/
def divuimm (e1 : Expr) (n2 : Integers.Int) : Expr :=
  match Integers.Int.is_power2 n2 with
  | some l => shruimm e1 l
  | none =>
      if optimForSize then divuBase e1 (Eop (.Ointconst n2) Enil)
      else match divuMulParams (Integers.Int.unsigned n2) with
        | none => divuBase e1 (Eop (.Ointconst n2) Enil)
        | some (p, m) => Elet e1 (divuMul p m)

/-- `SelectDiv.divu` -/
def divu (e1 e2 : Expr) : Expr :=
  match isIntconst e2, isIntconst e1 with
  | some n2, some n1 =>
      if Integers.Int.eq n2 Integers.Int.zero then divuBase e1 e2
      else Eop (.Ointconst (Integers.Int.divu n1 n2)) Enil
  | some n2, _ => divuimm optimForSize e1 n2
  | _, _ => divuBase e1 e2

/-- `SelectDiv.mod_from_div` -/
def modFromDiv (equo : Expr) (n : Integers.Int) : Expr :=
  Eop .Osub (Eletvar 0 ::: mulimm n equo ::: Enil)

/-- `SelectDiv.moduimm` -/
def moduimm (e1 : Expr) (n2 : Integers.Int) : Expr :=
  match Integers.Int.is_power2 n2 with
  | some _ => andimm (Integers.Int.sub n2 Integers.Int.one) e1
  | none =>
      if optimForSize then moduBase e1 (Eop (.Ointconst n2) Enil)
      else match divuMulParams (Integers.Int.unsigned n2) with
        | none => moduBase e1 (Eop (.Ointconst n2) Enil)
        | some (p, m) => Elet e1 (modFromDiv (divuMul p m) n2)

/-- `SelectDiv.modu` -/
def modu (e1 e2 : Expr) : Expr :=
  match isIntconst e2, isIntconst e1 with
  | some n2, some n1 =>
      if Integers.Int.eq n2 Integers.Int.zero then moduBase e1 e2
      else Eop (.Ointconst (Integers.Int.modu n1 n2)) Enil
  | some n2, _ => moduimm optimForSize e1 n2
  | _, _ => moduBase e1 e2

/-- `SelectDiv.divs_mul` -/
def divsMul (p m : Z) : Expr :=
  let e2 := mulhs (Eletvar 0) (Eop (.Ointconst (Integers.Int.repr m)) Enil)
  let e3 := if m < Integers.Int.half_modulus then e2 else add e2 (Eletvar 0)
  add (shrimm e3 (Integers.Int.repr p))
      (shruimm (Eletvar 0) (Integers.Int.repr (Integers.Int.zwordsize - 1)))

/-- `SelectDiv.divsimm` -/
def divsimm (e1 : Expr) (n2 : Integers.Int) : Expr :=
  match Integers.Int.is_power2 n2 with
  | some l =>
      if Integers.Int.ltu l (Integers.Int.repr 31) then shrximm e1 l
      else divsBase e1 (Eop (.Ointconst n2) Enil)
  | none =>
      if optimForSize then divsBase e1 (Eop (.Ointconst n2) Enil)
      else match divsMulParams (Integers.Int.signed n2) with
        | none => divsBase e1 (Eop (.Ointconst n2) Enil)
        | some (p, m) => Elet e1 (divsMul p m)

/-- `SelectDiv.divs` -/
def divs (e1 e2 : Expr) : Expr :=
  match isIntconst e2, isIntconst e1 with
  | some n2, some n1 =>
      if Integers.Int.eq n2 Integers.Int.zero then divsBase e1 e2
      else Eop (.Ointconst (Integers.Int.divs n1 n2)) Enil
  | some n2, _ => divsimm optimForSize e1 n2
  | _, _ => divsBase e1 e2

/-- `SelectDiv.modsimm` -/
def modsimm (e1 : Expr) (n2 : Integers.Int) : Expr :=
  match Integers.Int.is_power2 n2 with
  | some l =>
      if Integers.Int.ltu l (Integers.Int.repr 31)
      then Elet e1 (modFromDiv (shrximm (Eletvar 0) l) n2)
      else modsBase e1 (Eop (.Ointconst n2) Enil)
  | none =>
      if optimForSize then modsBase e1 (Eop (.Ointconst n2) Enil)
      else match divsMulParams (Integers.Int.signed n2) with
        | none => modsBase e1 (Eop (.Ointconst n2) Enil)
        | some (p, m) => Elet e1 (modFromDiv (divsMul p m) n2)

/-- `SelectDiv.mods` -/
def mods (e1 e2 : Expr) : Expr :=
  match isIntconst e2, isIntconst e1 with
  | some n2, some n1 =>
      if Integers.Int.eq n2 Integers.Int.zero then modsBase e1 e2
      else Eop (.Ointconst (Integers.Int.mods n1 n2)) Enil
  | some n2, _ => modsimm optimForSize e1 n2
  | _, _ => modsBase e1 e2

/-! ## 64-bit integer division -/

/-- `SelectDiv.modl_from_divl` -/
def modlFromDivl (equo : Expr) (n : Integers.Int64) : Expr := subl (Eletvar 0) (mullimm n equo)

/-- `SelectDiv.divlu_mull` -/
def divluMull (p m : Z) : Expr :=
  shrluimm (mullhu (Eletvar 0) (Integers.Int64.repr m)) (Integers.Int.repr p)

/-- `SelectDiv.divlu` -/
def divlu (e1 e2 : Expr) : Expr :=
  match isLongconst e2, isLongconst e1 with
  | some n2, some n1 => longconst (Integers.Int64.divu n1 n2)
  | some n2, _ =>
      match Integers.Int64.is_power2' n2 with
      | some l => shrluimm e1 l
      | none =>
          if optimForSize then divluBase e1 e2
          else match divluMulParams (Integers.Int64.unsigned n2) with
            | none => divluBase e1 e2
            | some (p, m) => Elet e1 (divluMull p m)
  | _, _ => divluBase e1 e2

/-- `SelectDiv.modlu` -/
def modlu (e1 e2 : Expr) : Expr :=
  match isLongconst e2, isLongconst e1 with
  | some n2, some n1 => longconst (Integers.Int64.modu n1 n2)
  | some n2, _ =>
      match Integers.Int64.is_power2 n2 with
      | some _ => andl e1 (longconst (Integers.Int64.sub n2 Integers.Int64.one))
      | none =>
          if optimForSize then modluBase e1 e2
          else match divluMulParams (Integers.Int64.unsigned n2) with
            | none => modluBase e1 e2
            | some (p, m) => Elet e1 (modlFromDivl (divluMull p m) n2)
  | _, _ => modluBase e1 e2

/-- `SelectDiv.divls_mull` -/
def divlsMull (p m : Z) : Expr :=
  let e2 := mullhs (Eletvar 0) (Integers.Int64.repr m)
  let e3 := if m < Integers.Int64.half_modulus then e2 else addl e2 (Eletvar 0)
  addl (shrlimm e3 (Integers.Int.repr p))
       (shrluimm (Eletvar 0) (Integers.Int.repr (Integers.Int64.zwordsize - 1)))

/-- `SelectDiv.divls` -/
def divls (e1 e2 : Expr) : Expr :=
  match isLongconst e2, isLongconst e1 with
  | some n2, some n1 => longconst (Integers.Int64.divs n1 n2)
  | some n2, _ =>
      match Integers.Int64.is_power2' n2 with
      | some l =>
          if Integers.Int.ltu l (Integers.Int.repr 63) then shrxlimm e1 l else divlsBase e1 e2
      | none =>
          if optimForSize then divlsBase e1 e2
          else match divlsMulParams (Integers.Int64.signed n2) with
            | none => divlsBase e1 e2
            | some (p, m) => Elet e1 (divlsMull p m)
  | _, _ => divlsBase e1 e2

/-- `SelectDiv.modls` -/
def modls (e1 e2 : Expr) : Expr :=
  match isLongconst e2, isLongconst e1 with
  | some n2, some n1 => longconst (Integers.Int64.mods n1 n2)
  | some n2, _ =>
      match Integers.Int64.is_power2' n2 with
      | some l =>
          if Integers.Int.ltu l (Integers.Int.repr 63)
          then Elet e1 (modlFromDivl (shrxlimm (Eletvar 0) l) n2)
          else modlsBase e1 e2
      | none =>
          if optimForSize then modlsBase e1 e2
          else match divlsMulParams (Integers.Int64.signed n2) with
            | none => modlsBase e1 e2
            | some (p, m) => Elet e1 (modlFromDivl (divlsMull p m) n2)
  | _, _ => modlsBase e1 e2

end SELECT

/-! ## Floating-point division -/

/-- `SelectDiv.divfimm` -/
def divfimm (e : Expr) (n : Floats.Float) : Expr :=
  match Floats.Float.exactInverse n with
  | some n' => Eop .Omulf (e ::: Eop (.Ofloatconst n') Enil ::: Enil)
  | none => Eop .Odivf (e ::: Eop (.Ofloatconst n) Enil ::: Enil)

/-- `SelectDiv.divf` -/
def divf (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ofloatconst n2) Enil => divfimm e1 n2
  | _ => Eop .Odivf (e1 ::: e2 ::: Enil)

/-- `SelectDiv.divfsimm` -/
def divfsimm (e : Expr) (n : Floats.Float32) : Expr :=
  match Floats.Float32.exactInverse n with
  | some n' => Eop .Omulfs (e ::: Eop (.Osingleconst n') Enil ::: Enil)
  | none => Eop .Odivfs (e ::: Eop (.Osingleconst n) Enil ::: Enil)

/-- `SelectDiv.divfs` -/
def divfs (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Osingleconst n2) Enil => divfsimm e1 n2
  | _ => Eop .Odivfs (e1 ::: e2 ::: Enil)

end SelectDiv
end X86
end CC
