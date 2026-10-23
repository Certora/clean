/-
  Instruction selection for 64-bit integer operations (RISC-V) — port of
  `riscV/SelectLong.vp`.

  In Rocq most functions start with `if Archi.splitlong then SplitLong.f …
  else …`: on RV32 the 64-bit operations are split into pairs of 32-bit
  operations by `backend/SplitLong.vp`.  The port's configuration is RV64,
  where `Archi.splitlong = false` (see `CCLib/targets/Archi.lean`), and
  `SplitLong.vp` is not ported, so only the `splitlong = false` branch of
  each function is ported here; the `helper_functions` section variable,
  which is used only by the `SplitLong` branches, is dropped.

  As in `SelectOp.lean`, each `Nondetfunction` is a first-match Lean `match`
  (the file has no guarded cases).
-/
import CCLib.riscV.SelectOp

namespace CC
namespace RiscV
namespace SelectLong

open Op CminorSel SelectOp

/-- CminorSel expressions (RISC-V). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists (RISC-V). -/
abbrev Exprlist := CminorSel.Exprlist

open CminorSel.Expr CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `SplitLong.is_intconst` -/
def isIntconst (e : Expr) : Option Integers.Int :=
  match e with
  | Eop (.Ointconst n) Enil => some n
  | _ => none

/-- `SelectLong.longconst` -/
def longconst (n : Integers.Int64) : Expr := Eop (.Olongconst n) Enil

/-- `SelectLong.is_longconst` -/
def isLongconst (e : Expr) : Option Integers.Int64 :=
  match e with
  | Eop (.Olongconst n) Enil => some n
  | _ => none

/-! ## Conversions -/

/-- `SelectLong.intoflong` -/
def intoflong (e : Expr) : Expr :=
  match isLongconst e with
  | some n => Eop (.Ointconst (Integers.Int.repr (Integers.Int64.unsigned n))) Enil
  | none => Eop .Olowlong (e ::: Enil)

/-- `SelectLong.longofint` -/
def longofint (e : Expr) : Expr :=
  match isIntconst e with
  | some n => longconst (Integers.Int64.repr (Integers.Int.signed n))
  | none => Eop .Ocast32signed (e ::: Enil)

/-- `SelectLong.longofintu` -/
def longofintu (e : Expr) : Expr :=
  match isIntconst e with
  | some n => longconst (Integers.Int64.repr (Integers.Int.unsigned n))
  | none => Eop .Ocast32unsigned (e ::: Enil)

/-! ## Addition, subtraction, negation -/

/-- `SelectLong.addlimm` -/
def addlimm (n : Integers.Int64) (e : Expr) : Expr :=
  if Integers.Int64.eq n Integers.Int64.zero then e else
  match e with
  | Eop (.Olongconst m) Enil => longconst (Integers.Int64.add n m)
  | Eop (.Oaddrsymbol s m) Enil =>
      Eop (.Oaddrsymbol s (Integers.Ptrofs.add (Integers.Ptrofs.of_int64 n) m)) Enil
  | Eop (.Oaddrstack m) Enil =>
      Eop (.Oaddrstack (Integers.Ptrofs.add (Integers.Ptrofs.of_int64 n) m)) Enil
  | Eop (.Oaddlimm m) (t ::: Enil) => Eop (.Oaddlimm (Integers.Int64.add n m)) (t ::: Enil)
  | _ => Eop (.Oaddlimm n) (e ::: Enil)

/-- `SelectLong.addl` -/
def addl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => addlimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => addlimm n2 t1
  | Eop (.Oaddlimm n1) (t1 ::: Enil), Eop (.Oaddlimm n2) (t2 ::: Enil) =>
      addlimm (Integers.Int64.add n1 n2) (Eop .Oaddl (t1 ::: t2 ::: Enil))
  | Eop (.Oaddlimm n1) (t1 ::: Enil), Eop (.Oaddrstack n2) Enil =>
      Eop .Oaddl (Eop (.Oaddrstack (Integers.Ptrofs.add (Integers.Ptrofs.of_int64 n1) n2)) Enil
        ::: t1 ::: Enil)
  | Eop (.Oaddrstack n1) Enil, Eop (.Oaddlimm n2) (t2 ::: Enil) =>
      Eop .Oaddl (Eop (.Oaddrstack (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 n2))) Enil
        ::: t2 ::: Enil)
  | Eop (.Oaddlimm n1) (t1 ::: Enil), t2 => addlimm n1 (Eop .Oaddl (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oaddlimm n2) (t2 ::: Enil) => addlimm n2 (Eop .Oaddl (t1 ::: t2 ::: Enil))
  | _, _ => Eop .Oaddl (e1 ::: e2 ::: Enil)

/-- `SelectLong.subl` -/
def subl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | t1, Eop (.Olongconst n2) Enil => addlimm (Integers.Int64.neg n2) t1
  | Eop (.Oaddlimm n1) (t1 ::: Enil), Eop (.Oaddlimm n2) (t2 ::: Enil) =>
      addlimm (Integers.Int64.sub n1 n2) (Eop .Osubl (t1 ::: t2 ::: Enil))
  | Eop (.Oaddlimm n1) (t1 ::: Enil), t2 => addlimm n1 (Eop .Osubl (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oaddlimm n2) (t2 ::: Enil) =>
      addlimm (Integers.Int64.neg n2) (Eop .Osubl (t1 ::: t2 ::: Enil))
  | _, _ => Eop .Osubl (e1 ::: e2 ::: Enil)

/-- `SelectLong.negl` -/
def negl (e : Expr) : Expr :=
  match isLongconst e with
  | some n => longconst (Integers.Int64.neg n)
  | none => Eop .Onegl (e ::: Enil)

/-! ## Shifts -/

/-- `SelectLong.shllimm` -/
def shllimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int64.iwordsize') then
    Eop .Oshll (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Olongconst n1) Enil => longconst (Integers.Int64.shl' n1 n)
    | Eop (.Oshllimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int64.iwordsize'
        then Eop (.Oshllimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshllimm n) (e1 ::: Enil)
    | _ => Eop (.Oshllimm n) (e1 ::: Enil)

/-- `SelectLong.shrluimm` -/
def shrluimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1 else
  if !(Integers.Int.ltu n Integers.Int64.iwordsize') then
    Eop .Oshrlu (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else
    match e1 with
    | Eop (.Olongconst n1) Enil => longconst (Integers.Int64.shru' n1 n)
    | Eop (.Oshrluimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int64.iwordsize'
        then Eop (.Oshrluimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshrluimm n) (e1 ::: Enil)
    | _ => Eop (.Oshrluimm n) (e1 ::: Enil)

/-- `SelectLong.shrlimm` -/
def shrlimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1 else
  if !(Integers.Int.ltu n Integers.Int64.iwordsize') then
    Eop .Oshrl (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else
    match e1 with
    | Eop (.Olongconst n1) Enil => longconst (Integers.Int64.shr' n1 n)
    | Eop (.Oshrlimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int64.iwordsize'
        then Eop (.Oshrlimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshrlimm n) (e1 ::: Enil)
    | _ => Eop (.Oshrlimm n) (e1 ::: Enil)

/-- `SelectLong.shll` -/
def shll (e1 e2 : Expr) : Expr :=
  match isIntconst e2 with
  | some n2 => shllimm e1 n2
  | none => Eop .Oshll (e1 ::: e2 ::: Enil)

/-- `SelectLong.shrl` -/
def shrl (e1 e2 : Expr) : Expr :=
  match isIntconst e2 with
  | some n2 => shrlimm e1 n2
  | none => Eop .Oshrl (e1 ::: e2 ::: Enil)

/-- `SelectLong.shrlu` -/
def shrlu (e1 e2 : Expr) : Expr :=
  match isIntconst e2 with
  | some n2 => shrluimm e1 n2
  | none => Eop .Oshrlu (e1 ::: e2 ::: Enil)

/-! ## Multiplication -/

/-- `SelectLong.mullimm_base` -/
def mullimmBase (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  match Integers.Int64.one_bits' n1 with
  | [i] => shllimm e2 i
  | [i, j] => Elet e2 (addl (shllimm (Eletvar 0) i) (shllimm (Eletvar 0) j))
  | _ => Eop .Omull (e2 ::: longconst n1 ::: Enil)

/-- `SelectLong.mullimm` -/
def mullimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then longconst Integers.Int64.zero
  else if Integers.Int64.eq n1 Integers.Int64.one then e2
  else match e2 with
    | Eop (.Olongconst n2) Enil => longconst (Integers.Int64.mul n1 n2)
    | Eop (.Oaddlimm n2) (t2 ::: Enil) => addlimm (Integers.Int64.mul n1 n2) (mullimmBase n1 t2)
    | _ => mullimmBase n1 e2

/-- `SelectLong.mull` -/
def mull (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => mullimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => mullimm n2 t1
  | _, _ => Eop .Omull (e1 ::: e2 ::: Enil)

/-- `SelectLong.mullhu` -/
def mullhu (e1 : Expr) (n2 : Integers.Int64) : Expr := Eop .Omullhu (e1 ::: longconst n2 ::: Enil)
/-- `SelectLong.mullhs` -/
def mullhs (e1 : Expr) (n2 : Integers.Int64) : Expr := Eop .Omullhs (e1 ::: longconst n2 ::: Enil)

/-! ## Bitwise operations -/

/-- `SelectLong.andlimm` -/
def andlimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then longconst Integers.Int64.zero else
  if Integers.Int64.eq n1 Integers.Int64.mone then e2 else
  match e2 with
  | Eop (.Olongconst n2) Enil => longconst (Integers.Int64.and n1 n2)
  | Eop (.Oandlimm n2) (t2 ::: Enil) => Eop (.Oandlimm (Integers.Int64.and n1 n2)) (t2 ::: Enil)
  | _ => Eop (.Oandlimm n1) (e2 ::: Enil)

/-- `SelectLong.andl` -/
def andl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => andlimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => andlimm n2 t1
  | _, _ => Eop .Oandl (e1 ::: e2 ::: Enil)

/-- `SelectLong.orlimm` -/
def orlimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then e2 else
  if Integers.Int64.eq n1 Integers.Int64.mone then longconst Integers.Int64.mone else
  match e2 with
  | Eop (.Olongconst n2) Enil => longconst (Integers.Int64.or n1 n2)
  | Eop (.Oorlimm n2) (t2 ::: Enil) => Eop (.Oorlimm (Integers.Int64.or n1 n2)) (t2 ::: Enil)
  | _ => Eop (.Oorlimm n1) (e2 ::: Enil)

/-- `SelectLong.orl` -/
def orl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => orlimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => orlimm n2 t1
  | _, _ => Eop .Oorl (e1 ::: e2 ::: Enil)

/-- `SelectLong.xorlimm` -/
def xorlimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then e2 else
  match e2 with
  | Eop (.Olongconst n2) Enil => longconst (Integers.Int64.xor n1 n2)
  | Eop (.Oxorlimm n2) (t2 ::: Enil) =>
      let n := Integers.Int64.xor n1 n2
      if Integers.Int64.eq n Integers.Int64.zero then t2 else Eop (.Oxorlimm n) (t2 ::: Enil)
  | _ => Eop (.Oxorlimm n1) (e2 ::: Enil)

/-- `SelectLong.xorl` -/
def xorl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => xorlimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => xorlimm n2 t1
  | _, _ => Eop .Oxorl (e1 ::: e2 ::: Enil)

/-- `SelectLong.notl` -/
def notl (e : Expr) : Expr := xorlimm Integers.Int64.mone e

/-! ## Division and modulus -/

/-- `SelectLong.divlu_base` -/
def divluBase (e1 e2 : Expr) : Expr := Eop .Odivlu (e1 ::: e2 ::: Enil)
/-- `SelectLong.modlu_base` -/
def modluBase (e1 e2 : Expr) : Expr := Eop .Omodlu (e1 ::: e2 ::: Enil)
/-- `SelectLong.divls_base` -/
def divlsBase (e1 e2 : Expr) : Expr := Eop .Odivl (e1 ::: e2 ::: Enil)
/-- `SelectLong.modls_base` -/
def modlsBase (e1 e2 : Expr) : Expr := Eop .Omodl (e1 ::: e2 ::: Enil)

/-- `SelectLong.shrxlimm` -/
def shrxlimm (e : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e else Eop (.Oshrxlimm n) (e ::: Enil)

/-! ## Comparisons -/

/-- `SelectLong.cmplu` -/
def cmplu (c : Comparison) (e1 e2 : Expr) : Expr :=
  match isLongconst e1, isLongconst e2 with
  | some n1, some n2 =>
      Eop (.Ointconst (if Integers.Int64.cmpu c n1 n2 then Integers.Int.one else Integers.Int.zero))
        Enil
  | some n1, none => Eop (.Ocmp (.Ccompluimm c.swap n1)) (e2 ::: Enil)
  | none, some n2 => Eop (.Ocmp (.Ccompluimm c n2)) (e1 ::: Enil)
  | none, none => Eop (.Ocmp (.Ccomplu c)) (e1 ::: e2 ::: Enil)

/-- `SelectLong.cmpl` -/
def cmpl (c : Comparison) (e1 e2 : Expr) : Expr :=
  match isLongconst e1, isLongconst e2 with
  | some n1, some n2 =>
      Eop (.Ointconst (if Integers.Int64.cmp c n1 n2 then Integers.Int.one else Integers.Int.zero))
        Enil
  | some n1, none => Eop (.Ocmp (.Ccomplimm c.swap n1)) (e2 ::: Enil)
  | none, some n2 => Eop (.Ocmp (.Ccomplimm c n2)) (e1 ::: Enil)
  | none, none => Eop (.Ocmp (.Ccompl c)) (e1 ::: e2 ::: Enil)

/-! ## Floating-point conversions -/

def longoffloat (e : Expr) : Expr := Eop .Olongoffloat (e ::: Enil)
def longuoffloat (e : Expr) : Expr := Eop .Olonguoffloat (e ::: Enil)
def floatoflong (e : Expr) : Expr := Eop .Ofloatoflong (e ::: Enil)
def floatoflongu (e : Expr) : Expr := Eop .Ofloatoflongu (e ::: Enil)
def longofsingle (e : Expr) : Expr := Eop .Olongofsingle (e ::: Enil)
def longuofsingle (e : Expr) : Expr := Eop .Olonguofsingle (e ::: Enil)
def singleoflong (e : Expr) : Expr := Eop .Osingleoflong (e ::: Enil)
def singleoflongu (e : Expr) : Expr := Eop .Osingleoflongu (e ::: Enil)

end SelectLong
end RiscV
end CC
