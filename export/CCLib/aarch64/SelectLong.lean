/-
  Instruction selection for 64-bit integer operations (aarch64) — port of
  `aarch64/SelectLong.vp` (whole file).

  As in `SelectOp.lean`, each `Nondetfunction` is a first-match Lean
  `match`; a case guarded by `?? arith_shift s` is an `if` whose `else`
  branch continues with the remaining cases (auxiliary functions with
  suffix `Rest`).
-/
import CCLib.aarch64.SelectOp

namespace CC
namespace SelectLong

open Op CminorSel SelectOp

/-- CminorSel expressions (disambiguated from Clight's `Expr`). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists. -/
abbrev Exprlist := CminorSel.Exprlist

open CminorSel.Expr CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `SelectLong.longconst` -/
def longconst (n : Integers.Int64) : Expr := Eop (.Olongconst n) Enil

/-! ## Conversions -/

/-- `SelectLong.intoflong` -/
def intoflong (e : Expr) : Expr :=
  match e with
  | Eop (.Olongconst n) Enil => Eop (.Ointconst (Integers.Int.repr (Integers.Int64.unsigned n))) Enil
  | _ => Eop .Olowlong (e ::: Enil)

/-- `SelectLong.longofint` -/
def longofint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => longconst (Integers.Int64.repr (Integers.Int.signed n))
  | _ => Eop (.Oextend .Xsgn32 (mkAmount64 Integers.Int.zero)) (e ::: Enil)

/-- `SelectLong.longofintu` -/
def longofintu (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => longconst (Integers.Int64.repr (Integers.Int.unsigned n))
  | _ => Eop (.Oextend .Xuns32 (mkAmount64 Integers.Int.zero)) (e ::: Enil)

/-! ## Integer addition and pointer addition -/

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

/-- The cases of `addl` after the second shift case. -/
def addlRest2 (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Oextend x a) (t1 ::: Enil), t2 => Eop (.Oaddlext x a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Oextend x a) (t2 ::: Enil) => Eop (.Oaddlext x a) (t1 ::: t2 ::: Enil)
  | Eop .Omull (t1 ::: t2 ::: Enil), t3 => Eop .Omulladd (t3 ::: t1 ::: t2 ::: Enil)
  | t1, Eop .Omull (t2 ::: t3 ::: Enil) => Eop .Omulladd (t1 ::: t2 ::: t3 ::: Enil)
  | _, _ => Eop .Oaddl (e1 ::: e2 ::: Enil)

/-- The cases of `addl` after the first shift case. -/
def addlRest1 (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Oshiftl s a) (t2 ::: Enil) =>
      if arithShift s then Eop (.Oaddlshift s a) (e1 ::: t2 ::: Enil) else addlRest2 e1 e2
  | _ => addlRest2 e1 e2

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
  | Eop (.Oshiftl s a) (t1 ::: Enil), t2 =>
      if arithShift s then Eop (.Oaddlshift s a) (t2 ::: t1 ::: Enil) else addlRest1 e1 e2
  | _, _ => addlRest1 e1 e2

/-! ## Opposite -/

/-- `SelectLong.negl` -/
def negl (e : Expr) : Expr :=
  match e with
  | Eop (.Olongconst n) Enil => Eop (.Olongconst (Integers.Int64.neg n)) Enil
  | Eop (.Oshiftl s a) (t1 ::: Enil) =>
      if arithShift s then Eop (.Oneglshift s a) (t1 ::: Enil) else Eop .Onegl (e ::: Enil)
  | _ => Eop .Onegl (e ::: Enil)

/-! ## Integer and pointer subtraction -/

/-- The cases of `subl` after the shift case. -/
def sublRest (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | t1, Eop (.Oextend x a) (t2 ::: Enil) => Eop (.Osublext x a) (t1 ::: t2 ::: Enil)
  | t1, Eop .Omull (t2 ::: t3 ::: Enil) => Eop .Omullsub (t1 ::: t2 ::: t3 ::: Enil)
  | _, _ => Eop .Osubl (e1 ::: e2 ::: Enil)

/-- `SelectLong.subl` -/
def subl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | t1, Eop (.Olongconst n2) Enil => addlimm (Integers.Int64.neg n2) t1
  | Eop (.Oaddlimm n1) (t1 ::: Enil), Eop (.Oaddlimm n2) (t2 ::: Enil) =>
      addlimm (Integers.Int64.sub n1 n2) (Eop .Osubl (t1 ::: t2 ::: Enil))
  | Eop (.Oaddlimm n1) (t1 ::: Enil), t2 => addlimm n1 (Eop .Osubl (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oaddlimm n2) (t2 ::: Enil) =>
      addlimm (Integers.Int64.neg n2) (Eop .Osubl (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oshiftl s a) (t2 ::: Enil) =>
      if arithShift s then Eop (.Osublshift s a) (t1 ::: t2 ::: Enil) else sublRest e1 e2
  | _, _ => sublRest e1 e2

/-! ## Immediate shifts -/

/-- `SelectLong.shllimm_base` -/
def shllimmBase (e1 : Expr) (n : Integers.Int) : Expr :=
  Eop (.Oshiftl .Slsl (mkAmount64 n)) (e1 ::: Enil)

/-- `SelectLong.shllimm` -/
def shllimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int64.iwordsize') then
    Eop .Oshll (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Olongconst n1) Enil => Eop (.Olongconst (Integers.Int64.shl' n1 n)) Enil
    | Eop (.Oshiftl .Slsl a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a64_amount n) Integers.Int64.iwordsize'
        then shllimmBase t1 (Integers.Int.add a.a64_amount n)
        else shllimmBase e1 n
    | Eop (.Ozextl s) (t1 ::: Enil) => Eop (.Oshllzext s (mkAmount64 n)) (t1 ::: Enil)
    | Eop (.Osextl s) (t1 ::: Enil) => Eop (.Oshllsext s (mkAmount64 n)) (t1 ::: Enil)
    | Eop (.Oshllzext s a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a64_amount n) Integers.Int64.iwordsize'
        then Eop (.Oshllzext s (mkAmount64 (Integers.Int.add a.a64_amount n))) (t1 ::: Enil)
        else shllimmBase e1 n
    | Eop (.Oshllsext s a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a64_amount n) Integers.Int64.iwordsize'
        then Eop (.Oshllsext s (mkAmount64 (Integers.Int.add a.a64_amount n))) (t1 ::: Enil)
        else shllimmBase e1 n
    | Eop (.Oextend x a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a64_amount n) Integers.Int64.iwordsize'
        then Eop (.Oextend x (mkAmount64 (Integers.Int.add a.a64_amount n))) (t1 ::: Enil)
        else shllimmBase e1 n
    | _ => shllimmBase e1 n

/-- `SelectLong.shrluimm_base` -/
def shrluimmBase (e1 : Expr) (n : Integers.Int) : Expr :=
  Eop (.Oshiftl .Slsr (mkAmount64 n)) (e1 ::: Enil)

/-- `SelectLong.shrluimm` -/
def shrluimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int64.iwordsize') then
    Eop .Oshrlu (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Olongconst n1) Enil => Eop (.Olongconst (Integers.Int64.shru' n1 n)) Enil
    | Eop (.Oshiftl .Slsl a) (t1 ::: Enil) =>
        if Integers.Int.ltu n a.a64_amount
        then Eop (.Oshllzext (Integers.Int64.zwordsize - Integers.Int.unsigned a.a64_amount)
                (mkAmount64 (Integers.Int.sub a.a64_amount n))) (t1 ::: Enil)
        else Eop (.Ozextshrl (mkAmount64 (Integers.Int.sub n a.a64_amount))
                (Integers.Int64.zwordsize - Integers.Int.unsigned n)) (t1 ::: Enil)
    | Eop (.Oshiftl .Slsr a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a64_amount n) Integers.Int64.iwordsize'
        then shrluimmBase t1 (Integers.Int.add a.a64_amount n)
        else shrluimmBase e1 n
    | Eop (.Ozextl s) (t1 ::: Enil) =>
        if Integers.Int.unsigned n < s
        then Eop (.Ozextshrl (mkAmount64 n) (s - Integers.Int.unsigned n)) (t1 ::: Enil)
        else Eop (.Olongconst Integers.Int64.zero) Enil
    | _ => shrluimmBase e1 n

/-- `SelectLong.shrlimm_base` -/
def shrlimmBase (e1 : Expr) (n : Integers.Int) : Expr :=
  Eop (.Oshiftl .Sasr (mkAmount64 n)) (e1 ::: Enil)

/-- `SelectLong.shrlimm` -/
def shrlimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int64.iwordsize') then
    Eop .Oshrl (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Olongconst n1) Enil => Eop (.Olongconst (Integers.Int64.shr' n1 n)) Enil
    | Eop (.Oshiftl .Slsl a) (t1 ::: Enil) =>
        if Integers.Int.ltu n a.a64_amount
        then Eop (.Oshllsext (Integers.Int64.zwordsize - Integers.Int.unsigned a.a64_amount)
                (mkAmount64 (Integers.Int.sub a.a64_amount n))) (t1 ::: Enil)
        else Eop (.Osextshrl (mkAmount64 (Integers.Int.sub n a.a64_amount))
                (Integers.Int64.zwordsize - Integers.Int.unsigned n)) (t1 ::: Enil)
    | Eop (.Oshiftl .Sasr a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a64_amount n) Integers.Int64.iwordsize'
        then shrlimmBase t1 (Integers.Int.add a.a64_amount n)
        else shrlimmBase e1 n
    | Eop (.Osextl s) (t1 ::: Enil) =>
        if decide (Integers.Int.unsigned n < s) && decide (s < Integers.Int64.zwordsize)
        then Eop (.Osextshrl (mkAmount64 n) (s - Integers.Int.unsigned n)) (t1 ::: Enil)
        else shrlimmBase e1 n
    | _ => shrlimmBase e1 n

/-! ## Integer multiply -/

/-- `SelectLong.mullimm_base` -/
def mullimmBase (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  match Integers.Int64.one_bits' n1 with
  | [i] => shllimm e2 i
  | [i, j] => Elet e2 (addl (shllimm (Eletvar 0) i) (shllimm (Eletvar 0) j))
  | _ => Eop .Omull (Eop (.Olongconst n1) Enil ::: e2 ::: Enil)

/-- `SelectLong.mullimm` -/
def mullimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then Eop (.Olongconst Integers.Int64.zero) Enil
  else if Integers.Int64.eq n1 Integers.Int64.one then e2
  else match e2 with
    | Eop (.Olongconst n2) Enil => Eop (.Olongconst (Integers.Int64.mul n1 n2)) Enil
    | Eop (.Oaddlimm n2) (t2 ::: Enil) => addlimm (Integers.Int64.mul n1 n2) (mullimmBase n1 t2)
    | _ => mullimmBase n1 e2

/-- `SelectLong.mull` -/
def mull (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => mullimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => mullimm n2 t1
  | _, _ => Eop .Omull (e1 ::: e2 ::: Enil)

/-- `SelectLong.mullhs` -/
def mullhs (e1 : Expr) (n2 : Integers.Int64) : Expr := Eop .Omullhs (e1 ::: longconst n2 ::: Enil)
/-- `SelectLong.mullhu` -/
def mullhu (e1 : Expr) (n2 : Integers.Int64) : Expr := Eop .Omullhu (e1 ::: longconst n2 ::: Enil)

/-! ## Integer conversions -/

/-- `SelectLong.zero_ext_l` -/
def zeroExtL (sz : Z) (e : Expr) : Expr :=
  match e with
  | Eop (.Olongconst n) Enil => Eop (.Olongconst (Integers.Int64.zero_ext sz.toNat n)) Enil
  | Eop (.Oshiftl .Slsr a) (t1 ::: Enil) => Eop (.Ozextshrl a sz) (t1 ::: Enil)
  | Eop (.Oshiftl .Slsl a) (t1 ::: Enil) =>
      if Integers.Int.unsigned a.a64_amount < sz
      then Eop (.Oshllzext (sz - Integers.Int.unsigned a.a64_amount) a) (t1 ::: Enil)
      else Eop (.Ozextl sz) (e ::: Enil)
  | _ => Eop (.Ozextl sz) (e ::: Enil)

/-! ## Bitwise operations -/

/-- `SelectLong.notl` -/
def notl (e : Expr) : Expr :=
  match e with
  | Eop (.Olongconst n) Enil => Eop (.Olongconst (Integers.Int64.not n)) Enil
  | Eop (.Oshiftl s a) (t1 ::: Enil) => Eop (.Onotlshift s a) (t1 ::: Enil)
  | Eop .Onotl (t1 ::: Enil) => t1
  | Eop (.Onotlshift s a) (t1 ::: Enil) => Eop (.Oshiftl s a) (t1 ::: Enil)
  | Eop .Obicl (t1 ::: t2 ::: Enil) => Eop .Oornl (t2 ::: t1 ::: Enil)
  | Eop .Oornl (t1 ::: t2 ::: Enil) => Eop .Obicl (t2 ::: t1 ::: Enil)
  | Eop .Oxorl (t1 ::: t2 ::: Enil) => Eop .Oeqvl (t1 ::: t2 ::: Enil)
  | Eop .Oeqvl (t1 ::: t2 ::: Enil) => Eop .Oxorl (t1 ::: t2 ::: Enil)
  | _ => Eop .Onotl (e ::: Enil)

/-- `SelectLong.andlimm_base` -/
def andlimmBase (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then Eop (.Olongconst Integers.Int64.zero) Enil else
  if Integers.Int64.eq n1 Integers.Int64.mone then e2 else
  match zIsPower2m1 (Integers.Int64.unsigned n1) with
  | some s => zeroExtL s e2
  | none => Eop (.Oandlimm n1) (e2 ::: Enil)

/-- `SelectLong.andlimm` -/
def andlimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Olongconst n2) Enil => Eop (.Olongconst (Integers.Int64.and n1 n2)) Enil
  | Eop (.Oandlimm n2) (t2 ::: Enil) => andlimmBase (Integers.Int64.and n1 n2) t2
  | Eop (.Ozextl s) (t2 ::: Enil) =>
      if 0 ≤ s then andlimmBase (Integers.Int64.and n1 (Integers.Int64.repr (twoP s - 1))) t2
      else andlimmBase n1 e2
  | _ => andlimmBase n1 e2

/-- `SelectLong.andl` -/
def andl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => andlimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => andlimm n2 t1
  | Eop .Onotl (t1 ::: Enil), t2 => Eop .Obicl (t2 ::: t1 ::: Enil)
  | t1, Eop .Onotl (t2 ::: Enil) => Eop .Obicl (t1 ::: t2 ::: Enil)
  | Eop (.Onotlshift s a) (t1 ::: Enil), t2 => Eop (.Obiclshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Onotlshift s a) (t2 ::: Enil) => Eop (.Obiclshift s a) (t1 ::: t2 ::: Enil)
  | Eop (.Oshiftl s a) (t1 ::: Enil), t2 => Eop (.Oandlshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Oshiftl s a) (t2 ::: Enil) => Eop (.Oandlshift s a) (t1 ::: t2 ::: Enil)
  | _, _ => Eop .Oandl (e1 ::: e2 ::: Enil)

/-- `SelectLong.orlimm` -/
def orlimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then e2
  else if Integers.Int64.eq n1 Integers.Int64.mone then Eop (.Olongconst Integers.Int64.mone) Enil
  else match e2 with
    | Eop (.Olongconst n2) Enil => Eop (.Olongconst (Integers.Int64.or n1 n2)) Enil
    | Eop (.Oorlimm n2) (t2 ::: Enil) => Eop (.Oorlimm (Integers.Int64.or n1 n2)) (t2 ::: Enil)
    | _ => Eop (.Oorlimm n1) (e2 ::: Enil)

/-- `SelectLong.orl` -/
def orl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => orlimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => orlimm n2 t1
  | Eop .Onotl (t1 ::: Enil), t2 => Eop .Oornl (t2 ::: t1 ::: Enil)
  | t1, Eop .Onotl (t2 ::: Enil) => Eop .Oornl (t1 ::: t2 ::: Enil)
  | Eop (.Onotlshift s a) (t1 ::: Enil), t2 => Eop (.Oornlshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Onotlshift s a) (t2 ::: Enil) => Eop (.Oornlshift s a) (t1 ::: t2 ::: Enil)
  | Eop (.Oshiftl .Slsl a1) (t1 ::: Enil), Eop (.Oshiftl .Slsr a2) (t2 ::: Enil) =>
      if Integers.Int.eq (Integers.Int.add a1.a64_amount a2.a64_amount) Integers.Int64.iwordsize'
          && sameExprPure t1 t2
      then Eop (.Oshiftl .Sror a2) (t2 ::: Enil)
      else Eop (.Oorlshift .Slsr a2) (Eop (.Oshiftl .Slsl a1) (t1 ::: Enil) ::: t2 ::: Enil)
  | Eop (.Oshiftl .Slsr a1) (t1 ::: Enil), Eop (.Oshiftl .Slsl a2) (t2 ::: Enil) =>
      if Integers.Int.eq (Integers.Int.add a2.a64_amount a1.a64_amount) Integers.Int64.iwordsize'
          && sameExprPure t1 t2
      then Eop (.Oshiftl .Sror a1) (t1 ::: Enil)
      else Eop (.Oorlshift .Slsl a2) (Eop (.Oshiftl .Slsr a1) (t1 ::: Enil) ::: t2 ::: Enil)
  | Eop (.Oshiftl s a) (t1 ::: Enil), t2 => Eop (.Oorlshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Oshiftl s a) (t2 ::: Enil) => Eop (.Oorlshift s a) (t1 ::: t2 ::: Enil)
  | _, _ => Eop .Oorl (e1 ::: e2 ::: Enil)

/-- `SelectLong.xorlimm_base` -/
def xorlimmBase (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  if Integers.Int64.eq n1 Integers.Int64.zero then e2 else
  if Integers.Int64.eq n1 Integers.Int64.mone then notl e2 else
  Eop (.Oxorlimm n1) (e2 ::: Enil)

/-- `SelectLong.xorlimm` -/
def xorlimm (n1 : Integers.Int64) (e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Olongconst n2) Enil => Eop (.Olongconst (Integers.Int64.xor n1 n2)) Enil
  | Eop (.Oxorlimm n2) (t2 ::: Enil) => xorlimmBase (Integers.Int64.xor n1 n2) t2
  | _ => xorlimmBase n1 e2

/-- `SelectLong.xorl` -/
def xorl (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => xorlimm n1 t2
  | t1, Eop (.Olongconst n2) Enil => xorlimm n2 t1
  | Eop .Onotl (t1 ::: Enil), t2 => Eop .Oeqvl (t2 ::: t1 ::: Enil)
  | t1, Eop .Onotl (t2 ::: Enil) => Eop .Oeqvl (t1 ::: t2 ::: Enil)
  | Eop (.Onotlshift s a) (t1 ::: Enil), t2 => Eop (.Oeqvlshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Onotlshift s a) (t2 ::: Enil) => Eop (.Oeqvlshift s a) (t1 ::: t2 ::: Enil)
  | Eop (.Oshiftl s a) (t1 ::: Enil), t2 => Eop (.Oxorlshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Oshiftl s a) (t2 ::: Enil) => Eop (.Oxorlshift s a) (t1 ::: t2 ::: Enil)
  | _, _ => Eop .Oxorl (e1 ::: e2 ::: Enil)

/-! ## Integer division and modulus -/

/-- `SelectLong.modl_aux` -/
def modlAux (divop : Operation) (e1 e2 : Expr) : Expr :=
  Elet e1
    (Elet (lift e2)
      (Eop .Omullsub (Eletvar 1 ::: Eop divop (Eletvar 1 ::: Eletvar 0 ::: Enil) :::
                      Eletvar 0 ::: Enil)))

/-- `SelectLong.divls_base` -/
def divlsBase (e1 e2 : Expr) : Expr := Eop .Odivl (e1 ::: e2 ::: Enil)
/-- `SelectLong.modls_base` -/
def modlsBase : Expr → Expr → Expr := modlAux .Odivl
/-- `SelectLong.divlu_base` -/
def divluBase (e1 e2 : Expr) : Expr := Eop .Odivlu (e1 ::: e2 ::: Enil)
/-- `SelectLong.modlu_base` -/
def modluBase : Expr → Expr → Expr := modlAux .Odivlu

/-- `SelectLong.shrxlimm` -/
def shrxlimm (e1 : Expr) (n2 : Integers.Int) : Expr :=
  if Integers.Int.eq n2 Integers.Int.zero then e1 else Eop (.Oshrlximm n2) (e1 ::: Enil)

/-! ## General shifts -/

/-- `SelectLong.shll` -/
def shll (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => shllimm e1 n2
  | _ => Eop .Oshll (e1 ::: e2 ::: Enil)

/-- `SelectLong.shrl` -/
def shrl (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => shrlimm e1 n2
  | _ => Eop .Oshrl (e1 ::: e2 ::: Enil)

/-- `SelectLong.shrlu` -/
def shrlu (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => shrluimm e1 n2
  | _ => Eop .Oshrlu (e1 ::: e2 ::: Enil)

/-! ## Comparisons -/

/-- `SelectLong.complimm` -/
def complimm (default : Comparison → Integers.Int64 → Condition)
    (sem : Comparison → Integers.Int64 → Integers.Int64 → Bool)
    (c : Comparison) (e1 : Expr) (n2 : Integers.Int64) : Expr :=
  match c, e1 with
  | c, Eop (.Olongconst n1) Enil =>
      Eop (.Ointconst (if sem c n1 n2 then Integers.Int.one else Integers.Int.zero)) Enil
  | .Ceq, Eop (.Oandlimm m) (t1 ::: Enil) =>
      if Integers.Int64.eq n2 Integers.Int64.zero
      then Eop (.Ocmp (.Cmasklzero m)) (t1 ::: Enil)
      else Eop (.Ocmp (default c n2)) (e1 ::: Enil)
  | .Cne, Eop (.Oandlimm m) (t1 ::: Enil) =>
      if Integers.Int64.eq n2 Integers.Int64.zero
      then Eop (.Ocmp (.Cmasklnotzero m)) (t1 ::: Enil)
      else Eop (.Ocmp (default c n2)) (e1 ::: Enil)
  | _, _ => Eop (.Ocmp (default c n2)) (e1 ::: Enil)

/-- The cases of `cmpl`/`cmplu` after the first shift case. -/
def cmplRest (shiftcond : Comparison → Shift → Amount64 → Condition)
    (basecond : Comparison → Condition) (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Oshiftl s a) (t2 ::: Enil) =>
      if arithShift s then Eop (.Ocmp (shiftcond c s a)) (e1 ::: t2 ::: Enil)
      else Eop (.Ocmp (basecond c)) (e1 ::: e2 ::: Enil)
  | _ => Eop (.Ocmp (basecond c)) (e1 ::: e2 ::: Enil)

/-- `SelectLong.cmpl` -/
def cmpl (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => complimm .Ccomplimm Integers.Int64.cmp c.swap t2 n1
  | t1, Eop (.Olongconst n2) Enil => complimm .Ccomplimm Integers.Int64.cmp c t1 n2
  | Eop (.Oshiftl s a) (t1 ::: Enil), t2 =>
      if arithShift s then Eop (.Ocmp (.Ccomplshift c.swap s a)) (t2 ::: t1 ::: Enil)
      else cmplRest .Ccomplshift .Ccompl c e1 e2
  | _, _ => cmplRest .Ccomplshift .Ccompl c e1 e2

/-- `SelectLong.cmplu` -/
def cmplu (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Olongconst n1) Enil, t2 => complimm .Ccompluimm Integers.Int64.cmpu c.swap t2 n1
  | t1, Eop (.Olongconst n2) Enil => complimm .Ccompluimm Integers.Int64.cmpu c t1 n2
  | Eop (.Oshiftl s a) (t1 ::: Enil), t2 =>
      if arithShift s then Eop (.Ocmp (.Ccomplushift c.swap s a)) (t2 ::: t1 ::: Enil)
      else cmplRest .Ccomplushift .Ccomplu c e1 e2
  | _, _ => cmplRest .Ccomplushift .Ccomplu c e1 e2

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
end CC
