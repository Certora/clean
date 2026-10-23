/-
  Instruction selection for operators (aarch64) — port of
  `aarch64/SelectOp.vp` (whole file), plus `Op.mk_amount32` /
  `Op.mk_amount64` (with `mk_amount_range`) and `Zbits.Z_is_power2m1`.

  `SelectOp.vp` is written with CompCert's `Nondetfunction` notation: a
  `match` whose cases are tried in order, some guarded with `?? cond`
  (a guarded case that fails falls through to the next case).  Here every
  such function is an ordinary first-match Lean `match`; a guarded case is
  an `if` whose `else` branch calls an auxiliary function (suffix `Rest`)
  that performs the remaining cases, so that the order of the cases is
  exactly Rocq's.

  Differences from Rocq: the OCaml parameter `symbol_is_relocatable` is an
  explicit argument of `addressing`; `Compopts` flags are not used here.
-/
import CCLib.backend.CminorSel
import CCLib.lib.IntegersInt

namespace CC

namespace Op

/-- `Op.mk_amount_range` (for `amount32`) -/
theorem mkAmount32_range (n : Integers.Int) :
    Integers.Int.ltu (Integers.Int.zero_ext 5 n) Integers.Int.iwordsize = true := by
  rw [Integers.Int.ltu_iff]
  have h := Integers.Int.zero_ext_range 5 n
  have h2 : Integers.Int.unsigned Integers.Int.iwordsize = 32 := by decide
  rw [h2]; exact Int.lt_of_lt_of_le h (by decide)

/-- `Op.mk_amount_range` (for `amount64`) -/
theorem mkAmount64_range (n : Integers.Int) :
    Integers.Int.ltu (Integers.Int.zero_ext 6 n) Integers.Int64.iwordsize' = true := by
  rw [Integers.Int.ltu_iff]
  have h := Integers.Int.zero_ext_range 6 n
  have h2 : Integers.Int.unsigned Integers.Int64.iwordsize' = 64 := by decide
  rw [h2]; exact Int.lt_of_lt_of_le h (by decide)

/-- `Op.mk_amount32` -/
def mkAmount32 (n : Integers.Int) : Amount32 := ⟨Integers.Int.zero_ext 5 n, mkAmount32_range n⟩

/-- `Op.mk_amount64` -/
def mkAmount64 (n : Integers.Int) : Amount64 := ⟨Integers.Int.zero_ext 6 n, mkAmount64_range n⟩

end Op

/-- `Zbits.Z_is_power2m1` -/
def zIsPower2m1 (x : Z) : Option Z := Integers.Z_is_power2 (x + 1)

namespace SelectOp

open Op CminorSel Expr Exprlist

/-- CminorSel expressions (disambiguated from Clight's `Expr`). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists. -/
abbrev Exprlist := CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `SelectOp.arith_shift` -/
def arithShift (s : Shift) : Bool :=
  match s with
  | .Sror => false
  | _ => true

/-! ## Constants -/

/-- `SelectOp.addrsymbol` -/
def addrsymbol (id : Ident) (ofs : Integers.Ptrofs) : Expr := Eop (.Oaddrsymbol id ofs) Enil

/-- `SelectOp.addrstack` -/
def addrstack (ofs : Integers.Ptrofs) : Expr := Eop (.Oaddrstack ofs) Enil

/-! ## Integer addition -/

/-- `SelectOp.addimm` -/
def addimm (n : Integers.Int) (e : Expr) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e else
  match e with
  | Eop (.Ointconst m) Enil => Eop (.Ointconst (Integers.Int.add n m)) Enil
  | Eop (.Oaddimm m) (t ::: Enil) => Eop (.Oaddimm (Integers.Int.add n m)) (t ::: Enil)
  | _ => Eop (.Oaddimm n) (e ::: Enil)

/-- The cases of `add` after the second shift case. -/
def addRest2 (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop .Omul (t1 ::: t2 ::: Enil), t3 => Eop .Omuladd (t3 ::: t1 ::: t2 ::: Enil)
  | t1, Eop .Omul (t2 ::: t3 ::: Enil) => Eop .Omuladd (t1 ::: t2 ::: t3 ::: Enil)
  | _, _ => Eop .Oadd (e1 ::: e2 ::: Enil)

/-- The cases of `add` after the first shift case. -/
def addRest1 (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Oshift s a) (t2 ::: Enil) =>
      if arithShift s then Eop (.Oaddshift s a) (e1 ::: t2 ::: Enil) else addRest2 e1 e2
  | _ => addRest2 e1 e2

/-- `SelectOp.add` -/
def add (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => addimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => addimm n2 t1
  | Eop (.Oaddimm n1) (t1 ::: Enil), Eop (.Oaddimm n2) (t2 ::: Enil) =>
      addimm (Integers.Int.add n1 n2) (Eop .Oadd (t1 ::: t2 ::: Enil))
  | Eop (.Oaddimm n1) (t1 ::: Enil), t2 => addimm n1 (Eop .Oadd (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oaddimm n2) (t2 ::: Enil) => addimm n2 (Eop .Oadd (t1 ::: t2 ::: Enil))
  | Eop (.Oshift s a) (t1 ::: Enil), t2 =>
      if arithShift s then Eop (.Oaddshift s a) (t2 ::: t1 ::: Enil) else addRest1 e1 e2
  | _, _ => addRest1 e1 e2

/-! ## Opposite -/

/-- `SelectOp.negint` -/
def negint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.neg n)) Enil
  | Eop (.Oshift s a) (t1 ::: Enil) =>
      if arithShift s then Eop (.Onegshift s a) (t1 ::: Enil) else Eop .Oneg (e ::: Enil)
  | _ => Eop .Oneg (e ::: Enil)

/-! ## Integer and pointer subtraction -/

/-- The cases of `sub` after the shift case. -/
def subRest (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | t1, Eop .Omul (t2 ::: t3 ::: Enil) => Eop .Omulsub (t1 ::: t2 ::: t3 ::: Enil)
  | _, _ => Eop .Osub (e1 ::: e2 ::: Enil)

/-- `SelectOp.sub` -/
def sub (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | t1, Eop (.Ointconst n2) Enil => addimm (Integers.Int.neg n2) t1
  | Eop (.Oaddimm n1) (t1 ::: Enil), Eop (.Oaddimm n2) (t2 ::: Enil) =>
      addimm (Integers.Int.sub n1 n2) (Eop .Osub (t1 ::: t2 ::: Enil))
  | Eop (.Oaddimm n1) (t1 ::: Enil), t2 => addimm n1 (Eop .Osub (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oaddimm n2) (t2 ::: Enil) =>
      addimm (Integers.Int.neg n2) (Eop .Osub (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oshift s a) (t2 ::: Enil) =>
      if arithShift s then Eop (.Osubshift s a) (t1 ::: t2 ::: Enil) else subRest e1 e2
  | _, _ => subRest e1 e2

/-! ## Immediate shifts -/

/-- `SelectOp.shlimm_base` -/
def shlimmBase (e1 : Expr) (n : Integers.Int) : Expr :=
  Eop (.Oshift .Slsl (mkAmount32 n)) (e1 ::: Enil)

/-- `SelectOp.shlimm` -/
def shlimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshl (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shl n1 n)) Enil
    | Eop (.Oshift .Slsl a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a32_amount n) Integers.Int.iwordsize
        then shlimmBase t1 (Integers.Int.add a.a32_amount n)
        else shlimmBase e1 n
    | Eop (.Ozext s) (t1 ::: Enil) => Eop (.Oshlzext s (mkAmount32 n)) (t1 ::: Enil)
    | Eop (.Osext s) (t1 ::: Enil) => Eop (.Oshlsext s (mkAmount32 n)) (t1 ::: Enil)
    | Eop (.Oshlzext s a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a32_amount n) Integers.Int.iwordsize
        then Eop (.Oshlzext s (mkAmount32 (Integers.Int.add a.a32_amount n))) (t1 ::: Enil)
        else shlimmBase e1 n
    | Eop (.Oshlsext s a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a32_amount n) Integers.Int.iwordsize
        then Eop (.Oshlsext s (mkAmount32 (Integers.Int.add a.a32_amount n))) (t1 ::: Enil)
        else shlimmBase e1 n
    | _ => shlimmBase e1 n

/-- `SelectOp.shruimm_base` -/
def shruimmBase (e1 : Expr) (n : Integers.Int) : Expr :=
  Eop (.Oshift .Slsr (mkAmount32 n)) (e1 ::: Enil)

/-- `SelectOp.shruimm` -/
def shruimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshru (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shru n1 n)) Enil
    | Eop (.Oshift .Slsl a) (t1 ::: Enil) =>
        if Integers.Int.ltu n a.a32_amount
        then Eop (.Oshlzext (Integers.Int.zwordsize - Integers.Int.unsigned a.a32_amount)
                (mkAmount32 (Integers.Int.sub a.a32_amount n))) (t1 ::: Enil)
        else Eop (.Ozextshr (mkAmount32 (Integers.Int.sub n a.a32_amount))
                (Integers.Int.zwordsize - Integers.Int.unsigned n)) (t1 ::: Enil)
    | Eop (.Oshift .Slsr a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a32_amount n) Integers.Int.iwordsize
        then shruimmBase t1 (Integers.Int.add a.a32_amount n)
        else shruimmBase e1 n
    | Eop (.Ozext s) (t1 ::: Enil) =>
        if Integers.Int.unsigned n < s
        then Eop (.Ozextshr (mkAmount32 n) (s - Integers.Int.unsigned n)) (t1 ::: Enil)
        else Eop (.Ointconst Integers.Int.zero) Enil
    | _ => shruimmBase e1 n

/-- `SelectOp.shrimm_base` -/
def shrimmBase (e1 : Expr) (n : Integers.Int) : Expr :=
  Eop (.Oshift .Sasr (mkAmount32 n)) (e1 ::: Enil)

/-- `SelectOp.shrimm` -/
def shrimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshr (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shr n1 n)) Enil
    | Eop (.Oshift .Slsl a) (t1 ::: Enil) =>
        if Integers.Int.ltu n a.a32_amount
        then Eop (.Oshlsext (Integers.Int.zwordsize - Integers.Int.unsigned a.a32_amount)
                (mkAmount32 (Integers.Int.sub a.a32_amount n))) (t1 ::: Enil)
        else Eop (.Osextshr (mkAmount32 (Integers.Int.sub n a.a32_amount))
                (Integers.Int.zwordsize - Integers.Int.unsigned n)) (t1 ::: Enil)
    | Eop (.Oshift .Sasr a) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add a.a32_amount n) Integers.Int.iwordsize
        then shrimmBase t1 (Integers.Int.add a.a32_amount n)
        else shrimmBase e1 n
    | Eop (.Osext s) (t1 ::: Enil) =>
        if decide (Integers.Int.unsigned n < s) && decide (s < Integers.Int.zwordsize)
        then Eop (.Osextshr (mkAmount32 n) (s - Integers.Int.unsigned n)) (t1 ::: Enil)
        else shrimmBase e1 n
    | _ => shrimmBase e1 n

/-! ## Integer multiply -/

/-- `SelectOp.mulimm_base` -/
def mulimmBase (n1 : Integers.Int) (e2 : Expr) : Expr :=
  match Integers.Int.one_bits n1 with
  | [i] => shlimm e2 i
  | [i, j] => Elet e2 (add (shlimm (Eletvar 0) i) (shlimm (Eletvar 0) j))
  | _ => Eop .Omul (Eop (.Ointconst n1) Enil ::: e2 ::: Enil)

/-- `SelectOp.mulimm` -/
def mulimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then Eop (.Ointconst Integers.Int.zero) Enil
  else if Integers.Int.eq n1 Integers.Int.one then e2
  else match e2 with
    | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.mul n1 n2)) Enil
    | Eop (.Oaddimm n2) (t2 ::: Enil) => addimm (Integers.Int.mul n1 n2) (mulimmBase n1 t2)
    | _ => mulimmBase n1 e2

/-- `SelectOp.mul` -/
def mul (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => mulimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => mulimm n2 t1
  | _, _ => Eop .Omul (e1 ::: e2 ::: Enil)

/-- `SelectOp.mulhs` -/
def mulhs (e1 e2 : Expr) : Expr :=
  Eop .Olowlong
    (Eop (.Oshiftl .Sasr (mkAmount64 (Integers.Int.repr 32)))
      (Eop .Omull (Eop (.Oextend .Xsgn32 (mkAmount64 Integers.Int.zero)) (e1 ::: Enil) :::
                   Eop (.Oextend .Xsgn32 (mkAmount64 Integers.Int.zero)) (e2 ::: Enil) ::: Enil)
        ::: Enil) ::: Enil)

/-- `SelectOp.mulhu` -/
def mulhu (e1 e2 : Expr) : Expr :=
  Eop .Olowlong
    (Eop (.Oshiftl .Slsr (mkAmount64 (Integers.Int.repr 32)))
      (Eop .Omull (Eop (.Oextend .Xuns32 (mkAmount64 Integers.Int.zero)) (e1 ::: Enil) :::
                   Eop (.Oextend .Xuns32 (mkAmount64 Integers.Int.zero)) (e2 ::: Enil) ::: Enil)
        ::: Enil) ::: Enil)

/-! ## Integer conversions -/

/-- `SelectOp.zero_ext` -/
def zeroExt (sz : Z) (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.zero_ext sz.toNat n)) Enil
  | Eop (.Oshift .Slsr a) (t1 ::: Enil) => Eop (.Ozextshr a sz) (t1 ::: Enil)
  | Eop (.Oshift .Slsl a) (t1 ::: Enil) =>
      if Integers.Int.unsigned a.a32_amount < sz
      then Eop (.Oshlzext (sz - Integers.Int.unsigned a.a32_amount) a) (t1 ::: Enil)
      else Eop (.Ozext sz) (e ::: Enil)
  | _ => Eop (.Ozext sz) (e ::: Enil)

/-- `SelectOp.sign_ext` -/
def signExt (sz : Z) (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.sign_ext sz.toNat n)) Enil
  | Eop (.Oshift .Sasr a) (t1 ::: Enil) => Eop (.Osextshr a sz) (t1 ::: Enil)
  | Eop (.Oshift .Slsl a) (t1 ::: Enil) =>
      if Integers.Int.unsigned a.a32_amount < sz
      then Eop (.Oshlsext (sz - Integers.Int.unsigned a.a32_amount) a) (t1 ::: Enil)
      else Eop (.Osext sz) (e ::: Enil)
  | _ => Eop (.Osext sz) (e ::: Enil)

/-- `SelectOp.cast8unsigned` -/
def cast8unsigned (e : Expr) : Expr := zeroExt 8 e
/-- `SelectOp.cast8signed` -/
def cast8signed (e : Expr) : Expr := signExt 8 e
/-- `SelectOp.cast16unsigned` -/
def cast16unsigned (e : Expr) : Expr := zeroExt 16 e
/-- `SelectOp.cast16signed` -/
def cast16signed (e : Expr) : Expr := signExt 16 e

/-! ## Bitwise operations -/

/-- `SelectOp.notint` -/
def notint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.not n)) Enil
  | Eop (.Oshift s a) (t1 ::: Enil) => Eop (.Onotshift s a) (t1 ::: Enil)
  | Eop .Onot (t1 ::: Enil) => t1
  | Eop (.Onotshift s a) (t1 ::: Enil) => Eop (.Oshift s a) (t1 ::: Enil)
  | Eop .Obic (t1 ::: t2 ::: Enil) => Eop .Oorn (t2 ::: t1 ::: Enil)
  | Eop .Oorn (t1 ::: t2 ::: Enil) => Eop .Obic (t2 ::: t1 ::: Enil)
  | Eop .Oxor (t1 ::: t2 ::: Enil) => Eop .Oeqv (t1 ::: t2 ::: Enil)
  | Eop .Oeqv (t1 ::: t2 ::: Enil) => Eop .Oxor (t1 ::: t2 ::: Enil)
  | _ => Eop .Onot (e ::: Enil)

/-- `Coqlib.two_p` -/
def twoP (x : Z) : Z := if 0 ≤ x then (2 : Z) ^ x.toNat else 0

/-- `SelectOp.andimm_base` -/
def andimmBase (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then Eop (.Ointconst Integers.Int.zero) Enil else
  if Integers.Int.eq n1 Integers.Int.mone then e2 else
  match zIsPower2m1 (Integers.Int.unsigned n1) with
  | some s => zeroExt s e2
  | none => Eop (.Oandimm n1) (e2 ::: Enil)

/-- `SelectOp.andimm` -/
def andimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.and n1 n2)) Enil
  | Eop (.Oandimm n2) (t2 ::: Enil) => andimmBase (Integers.Int.and n1 n2) t2
  | Eop (.Ozext s) (t2 ::: Enil) =>
      if 0 ≤ s then andimmBase (Integers.Int.and n1 (Integers.Int.repr (twoP s - 1))) t2
      else andimmBase n1 e2
  | _ => andimmBase n1 e2

/-- `SelectOp.and` -/
def and (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => andimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => andimm n2 t1
  | Eop .Onot (t1 ::: Enil), t2 => Eop .Obic (t2 ::: t1 ::: Enil)
  | t1, Eop .Onot (t2 ::: Enil) => Eop .Obic (t1 ::: t2 ::: Enil)
  | Eop (.Onotshift s a) (t1 ::: Enil), t2 => Eop (.Obicshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Onotshift s a) (t2 ::: Enil) => Eop (.Obicshift s a) (t1 ::: t2 ::: Enil)
  | Eop (.Oshift s a) (t1 ::: Enil), t2 => Eop (.Oandshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Oshift s a) (t2 ::: Enil) => Eop (.Oandshift s a) (t1 ::: t2 ::: Enil)
  | _, _ => Eop .Oand (e1 ::: e2 ::: Enil)

/-- `SelectOp.orimm` -/
def orimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then e2
  else if Integers.Int.eq n1 Integers.Int.mone then Eop (.Ointconst Integers.Int.mone) Enil
  else match e2 with
    | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.or n1 n2)) Enil
    | Eop (.Oorimm n2) (t2 ::: Enil) => Eop (.Oorimm (Integers.Int.or n1 n2)) (t2 ::: Enil)
    | _ => Eop (.Oorimm n1) (e2 ::: Enil)

/-- `SelectOp.same_expr_pure` -/
def sameExprPure (e1 e2 : Expr) : Bool :=
  match e1, e2 with
  | .Evar v1, .Evar v2 => decide (v1 = v2)
  | _, _ => false

/-- `SelectOp.or` -/
def or (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => orimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => orimm n2 t1
  | Eop .Onot (t1 ::: Enil), t2 => Eop .Oorn (t2 ::: t1 ::: Enil)
  | t1, Eop .Onot (t2 ::: Enil) => Eop .Oorn (t1 ::: t2 ::: Enil)
  | Eop (.Onotshift s a) (t1 ::: Enil), t2 => Eop (.Oornshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Onotshift s a) (t2 ::: Enil) => Eop (.Oornshift s a) (t1 ::: t2 ::: Enil)
  | Eop (.Oshift .Slsl a1) (t1 ::: Enil), Eop (.Oshift .Slsr a2) (t2 ::: Enil) =>
      if Integers.Int.eq (Integers.Int.add a1.a32_amount a2.a32_amount) Integers.Int.iwordsize
          && sameExprPure t1 t2
      then Eop (.Oshift .Sror a2) (t2 ::: Enil)
      else Eop (.Oorshift .Slsr a2) (Eop (.Oshift .Slsl a1) (t1 ::: Enil) ::: t2 ::: Enil)
  | Eop (.Oshift .Slsr a1) (t1 ::: Enil), Eop (.Oshift .Slsl a2) (t2 ::: Enil) =>
      if Integers.Int.eq (Integers.Int.add a2.a32_amount a1.a32_amount) Integers.Int.iwordsize
          && sameExprPure t1 t2
      then Eop (.Oshift .Sror a1) (t1 ::: Enil)
      else Eop (.Oorshift .Slsl a2) (Eop (.Oshift .Slsr a1) (t1 ::: Enil) ::: t2 ::: Enil)
  | Eop (.Oshift s a) (t1 ::: Enil), t2 => Eop (.Oorshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Oshift s a) (t2 ::: Enil) => Eop (.Oorshift s a) (t1 ::: t2 ::: Enil)
  | _, _ => Eop .Oor (e1 ::: e2 ::: Enil)

/-- `SelectOp.xorimm_base` -/
def xorimmBase (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then e2 else
  if Integers.Int.eq n1 Integers.Int.mone then notint e2 else
  Eop (.Oxorimm n1) (e2 ::: Enil)

/-- `SelectOp.xorimm` -/
def xorimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.xor n1 n2)) Enil
  | Eop (.Oxorimm n2) (t2 ::: Enil) => xorimmBase (Integers.Int.xor n1 n2) t2
  | _ => xorimmBase n1 e2

/-- `SelectOp.xor` -/
def xor (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => xorimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => xorimm n2 t1
  | Eop .Onot (t1 ::: Enil), t2 => Eop .Oeqv (t2 ::: t1 ::: Enil)
  | t1, Eop .Onot (t2 ::: Enil) => Eop .Oeqv (t1 ::: t2 ::: Enil)
  | Eop (.Onotshift s a) (t1 ::: Enil), t2 => Eop (.Oeqvshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Onotshift s a) (t2 ::: Enil) => Eop (.Oeqvshift s a) (t1 ::: t2 ::: Enil)
  | Eop (.Oshift s a) (t1 ::: Enil), t2 => Eop (.Oxorshift s a) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Oshift s a) (t2 ::: Enil) => Eop (.Oxorshift s a) (t1 ::: t2 ::: Enil)
  | _, _ => Eop .Oxor (e1 ::: e2 ::: Enil)

/-! ## Integer division and modulus -/

/-- `SelectOp.mod_aux` -/
def modAux (divop : Operation) (e1 e2 : Expr) : Expr :=
  Elet e1
    (Elet (lift e2)
      (Eop .Omulsub (Eletvar 1 ::: Eop divop (Eletvar 1 ::: Eletvar 0 ::: Enil) :::
                     Eletvar 0 ::: Enil)))

/-- `SelectOp.divs_base` -/
def divsBase (e1 e2 : Expr) : Expr := Eop .Odiv (e1 ::: e2 ::: Enil)
/-- `SelectOp.mods_base` -/
def modsBase : Expr → Expr → Expr := modAux .Odiv
/-- `SelectOp.divu_base` -/
def divuBase (e1 e2 : Expr) : Expr := Eop .Odivu (e1 ::: e2 ::: Enil)
/-- `SelectOp.modu_base` -/
def moduBase : Expr → Expr → Expr := modAux .Odivu

/-- `SelectOp.shrximm` -/
def shrximm (e1 : Expr) (n2 : Integers.Int) : Expr :=
  if Integers.Int.eq n2 Integers.Int.zero then e1 else Eop (.Oshrximm n2) (e1 ::: Enil)

/-! ## General shifts -/

/-- `SelectOp.shl` -/
def shl (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => shlimm e1 n2
  | _ => Eop .Oshl (e1 ::: e2 ::: Enil)

/-- `SelectOp.shr` -/
def shr (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => shrimm e1 n2
  | _ => Eop .Oshr (e1 ::: e2 ::: Enil)

/-- `SelectOp.shru` -/
def shru (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Ointconst n2) Enil => shruimm e1 n2
  | _ => Eop .Oshru (e1 ::: e2 ::: Enil)

/-! ## Floating-point arithmetic -/

def negf (e : Expr) : Expr := Eop .Onegf (e ::: Enil)
def absf (e : Expr) : Expr := Eop .Oabsf (e ::: Enil)
def addf (e1 e2 : Expr) : Expr := Eop .Oaddf (e1 ::: e2 ::: Enil)
def subf (e1 e2 : Expr) : Expr := Eop .Osubf (e1 ::: e2 ::: Enil)
def mulf (e1 e2 : Expr) : Expr := Eop .Omulf (e1 ::: e2 ::: Enil)
def negfs (e : Expr) : Expr := Eop .Onegfs (e ::: Enil)
def absfs (e : Expr) : Expr := Eop .Oabsfs (e ::: Enil)
def addfs (e1 e2 : Expr) : Expr := Eop .Oaddfs (e1 ::: e2 ::: Enil)
def subfs (e1 e2 : Expr) : Expr := Eop .Osubfs (e1 ::: e2 ::: Enil)
def mulfs (e1 e2 : Expr) : Expr := Eop .Omulfs (e1 ::: e2 ::: Enil)

/-! ## Comparisons -/

/-- `SelectOp.compimm` -/
def compimm (default : Comparison → Integers.Int → Condition)
    (sem : Comparison → Integers.Int → Integers.Int → Bool)
    (c : Comparison) (e1 : Expr) (n2 : Integers.Int) : Expr :=
  match c, e1 with
  | c, Eop (.Ointconst n1) Enil =>
      Eop (.Ointconst (if sem c n1 n2 then Integers.Int.one else Integers.Int.zero)) Enil
  | .Ceq, Eop (.Ocmp c) el =>
      if n2 = Integers.Int.zero then Eop (.Ocmp (negateCondition c)) el
      else if n2 = Integers.Int.one then Eop (.Ocmp c) el
      else Eop (.Ointconst Integers.Int.zero) Enil
  | .Cne, Eop (.Ocmp c) el =>
      if n2 = Integers.Int.zero then Eop (.Ocmp c) el
      else if n2 = Integers.Int.one then Eop (.Ocmp (negateCondition c)) el
      else Eop (.Ointconst Integers.Int.one) Enil
  | .Ceq, Eop (.Oandimm m) (t1 ::: Enil) =>
      if Integers.Int.eq n2 Integers.Int.zero
      then Eop (.Ocmp (.Cmaskzero m)) (t1 ::: Enil)
      else Eop (.Ocmp (default c n2)) (e1 ::: Enil)
  | .Cne, Eop (.Oandimm m) (t1 ::: Enil) =>
      if Integers.Int.eq n2 Integers.Int.zero
      then Eop (.Ocmp (.Cmasknotzero m)) (t1 ::: Enil)
      else Eop (.Ocmp (default c n2)) (e1 ::: Enil)
  | _, _ => Eop (.Ocmp (default c n2)) (e1 ::: Enil)

/-- The cases of `comp`/`compu` after the first shift case. -/
def compRest (shiftcond : Comparison → Shift → Amount32 → Condition) (basecond : Comparison → Condition)
    (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e2 with
  | Eop (.Oshift s a) (t2 ::: Enil) =>
      if arithShift s then Eop (.Ocmp (shiftcond c s a)) (e1 ::: t2 ::: Enil)
      else Eop (.Ocmp (basecond c)) (e1 ::: e2 ::: Enil)
  | _ => Eop (.Ocmp (basecond c)) (e1 ::: e2 ::: Enil)

/-- `SelectOp.comp` -/
def comp (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => compimm .Ccompimm Integers.Int.cmp c.swap t2 n1
  | t1, Eop (.Ointconst n2) Enil => compimm .Ccompimm Integers.Int.cmp c t1 n2
  | Eop (.Oshift s a) (t1 ::: Enil), t2 =>
      if arithShift s then Eop (.Ocmp (.Ccompshift c.swap s a)) (t2 ::: t1 ::: Enil)
      else compRest .Ccompshift .Ccomp c e1 e2
  | _, _ => compRest .Ccompshift .Ccomp c e1 e2

/-- `SelectOp.compu` -/
def compu (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => compimm .Ccompuimm Integers.Int.cmpu c.swap t2 n1
  | t1, Eop (.Ointconst n2) Enil => compimm .Ccompuimm Integers.Int.cmpu c t1 n2
  | Eop (.Oshift s a) (t1 ::: Enil), t2 =>
      if arithShift s then Eop (.Ocmp (.Ccompushift c.swap s a)) (t2 ::: t1 ::: Enil)
      else compRest .Ccompushift .Ccompu c e1 e2
  | _, _ => compRest .Ccompushift .Ccompu c e1 e2

/-- `SelectOp.compf` -/
def compf (c : Comparison) (e1 e2 : Expr) : Expr := Eop (.Ocmp (.Ccompf c)) (e1 ::: e2 ::: Enil)
/-- `SelectOp.compfs` -/
def compfs (c : Comparison) (e1 e2 : Expr) : Expr := Eop (.Ocmp (.Ccompfs c)) (e1 ::: e2 ::: Enil)

/-! ## Floating-point conversions -/

def intoffloat (e : Expr) : Expr := Eop .Ointoffloat (e ::: Enil)
def intuoffloat (e : Expr) : Expr := Eop .Ointuoffloat (e ::: Enil)

/-- `SelectOp.floatofintu` -/
def floatofintu (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ofloatconst (Floats.Float.ofIntu n)) Enil
  | _ => Eop .Ofloatofintu (e ::: Enil)

/-- `SelectOp.floatofint` -/
def floatofint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ofloatconst (Floats.Float.ofInt n)) Enil
  | _ => Eop .Ofloatofint (e ::: Enil)

def intofsingle (e : Expr) : Expr := Eop .Ointofsingle (e ::: Enil)
def intuofsingle (e : Expr) : Expr := Eop .Ointuofsingle (e ::: Enil)

/-- `SelectOp.singleofint` -/
def singleofint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Osingleconst (Floats.Float32.ofInt n)) Enil
  | _ => Eop .Osingleofint (e ::: Enil)

/-- `SelectOp.singleofintu` -/
def singleofintu (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Osingleconst (Floats.Float32.ofIntu n)) Enil
  | _ => Eop .Osingleofintu (e ::: Enil)

def singleoffloat (e : Expr) : Expr := Eop .Osingleoffloat (e ::: Enil)
def floatofsingle (e : Expr) : Expr := Eop .Ofloatofsingle (e ::: Enil)

/-! ## Selection -/

/-- `SelectOp.select_supported` -/
def selectSupported (ty : ATyp) : Bool :=
  match ty with
  | .Tint | .Tlong | .Tfloat | .Tsingle => true
  | _ => false

/-- `SelectOp.select` -/
def select (ty : ATyp) (cond : Condition) (args : Exprlist) (e1 e2 : Expr) : Expr :=
  Eop (.Osel cond ty) (e1 ::: e2 ::: args)

/-! ## Addressing modes -/

/-- `SelectOp.addressing` -/
def addressing (symbolIsRelocatable : Ident → Bool) (_chunk : Chunk) (e : Expr) :
    Addressing × Exprlist :=
  match e with
  | Eop (.Oaddrstack n) Enil => (.Ainstack n, Enil)
  | Eop (.Oaddrsymbol id ofs) Enil =>
      if symbolIsRelocatable id
      then (.Aindexed (Integers.Ptrofs.to_int64 ofs),
            Eop (.Oaddrsymbol id Integers.Ptrofs.zero) Enil ::: Enil)
      else (.Aglobal id ofs, Enil)
  | Eop (.Oaddlimm n) (e1 ::: Enil) => (.Aindexed n, e1 ::: Enil)
  | Eop (.Oaddlshift .Slsl a) (e1 ::: e2 ::: Enil) => (.Aindexed2shift a, e1 ::: e2 ::: Enil)
  | Eop (.Oaddlext x a) (e1 ::: e2 ::: Enil) => (.Aindexed2ext x a, e1 ::: e2 ::: Enil)
  | Eop .Oaddl (e1 ::: e2 ::: Enil) => (.Aindexed2, e1 ::: e2 ::: Enil)
  | _ => (.Aindexed Integers.Int64.zero, e ::: Enil)

/-! ## Arguments of builtins -/

/-- `SelectOp.builtin_arg` -/
def builtinArg (e : Expr) : BuiltinArg Expr :=
  match e with
  | Eop (.Ointconst n) Enil => .BA_int n
  | Eop (.Olongconst n) Enil => .BA_long n
  | Eop (.Oaddrsymbol id ofs) Enil => .BA_addrglobal id ofs
  | Eop (.Oaddrstack ofs) Enil => .BA_addrstack ofs
  | Eload chunk (.Ainstack ofs) Enil => .BA_loadstack chunk ofs
  | Eop (.Oaddlimm n) (e1 ::: Enil) => .BA_addptr (.BA e1) (.BA_long n)
  | _ => .BA e

/-- `SelectOp.platform_builtin`: aarch64 has no platform-specific built-ins. -/
def platformBuiltin (_b : Builtins.PlatformBuiltin) (_args : Exprlist) : Option Expr := none

end SelectOp
end CC
