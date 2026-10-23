/-
  Instruction selection for operators (x86) — port of `x86/SelectOp.vp`
  (whole file).

  `SelectOp.vp` is written with CompCert's `Nondetfunction` notation: a
  `match` whose cases are tried in order.  The x86 file has no guarded
  (`??`) cases, so every such function is an ordinary first-match Lean
  `match` with the cases in exactly Rocq's order.

  Differences from Rocq:
  * the OCaml parameter `symbol_is_relocatable` is an explicit argument of
    `addrsymbol`;
  * the port's `Builtins.PlatformBuiltin` type is the (empty) aarch64 one, so
    the x86 platform built-ins `__builtin_fmax`/`__builtin_fmin` are given by
    the local type `PlatformBuiltinX86` and `platformBuiltinX86`, while
    `platformBuiltin` (on the shared, empty type) returns `none`.
-/
import CCLib.x86.CminorSel

namespace CC
namespace X86
namespace SelectOp

open Op CminorSel Expr Exprlist Condexpr

/-- CminorSel expressions (x86). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists (x86). -/
abbrev Exprlist := CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `Float.ox8000_0000` -/
def ox8000_0000 : Integers.Int := Integers.Int.repr 0x80000000

/-- `SelectOp.Olea_ptr` -/
def oleaPtr (a : Addressing) : Operation := if Archi.ptr64 then .Oleal a else .Olea a

/-! ## Constants -/

/-- `SelectOp.addrsymbol` -/
def addrsymbol (symbolIsRelocatable : Ident → Bool) (id : Ident) (ofs : Integers.Ptrofs) : Expr :=
  if symbolIsRelocatable id then
    if Integers.Ptrofs.eq ofs Integers.Ptrofs.zero
    then Eop (.Oindirectsymbol id) Enil
    else Eop (oleaPtr (.Aindexed (Integers.Ptrofs.unsigned ofs)))
           (Eop (.Oindirectsymbol id) Enil ::: Enil)
  else Eop (oleaPtr (.Aglobal id ofs)) Enil

/-- `SelectOp.addrstack` -/
def addrstack (ofs : Integers.Ptrofs) : Expr := Eop (oleaPtr (.Ainstack ofs)) Enil

/-! ## Integer logical negation -/

/-- `SelectOp.notint` -/
def notint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.not n)) Enil
  | Eop (.Oxorimm n) (e1 ::: Enil) => Eop (.Oxorimm (Integers.Int.not n)) (e1 ::: Enil)
  | _ => Eop .Onot (e ::: Enil)

/-! ## Integer addition and pointer addition -/

/-- `SelectOp.addimm` -/
def addimm (n : Integers.Int) (e : Expr) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e else
  match e with
  | Eop (.Ointconst m) Enil => Eop (.Ointconst (Integers.Int.add n m)) Enil
  | Eop (.Olea addr) args => Eop (.Olea (offsetAddressingTotal addr (Integers.Int.signed n))) args
  | _ => Eop (.Olea (.Aindexed (Integers.Int.signed n))) (e ::: Enil)

/-- `SelectOp.add` -/
def add (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => addimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => addimm n2 t1
  | Eop (.Olea (.Aindexed n1)) (t1 ::: Enil), Eop (.Olea (.Aindexed n2)) (t2 ::: Enil) =>
      Eop (.Olea (.Aindexed2 (n1 + n2))) (t1 ::: t2 ::: Enil)
  | Eop (.Olea (.Aindexed n1)) (t1 ::: Enil), Eop (.Olea (.Ascaled sc n2)) (t2 ::: Enil) =>
      Eop (.Olea (.Aindexed2scaled sc (n1 + n2))) (t1 ::: t2 ::: Enil)
  | Eop (.Olea (.Ascaled sc n1)) (t1 ::: Enil), Eop (.Olea (.Aindexed n2)) (t2 ::: Enil) =>
      Eop (.Olea (.Aindexed2scaled sc (n1 + n2))) (t2 ::: t1 ::: Enil)
  | Eop (.Olea (.Aindexed n1)) (t1 ::: Enil), Eop (.Olea (.Aglobal id ofs)) Enil =>
      Eop (.Olea (.Abased id (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr n1)))) (t1 ::: Enil)
  | Eop (.Olea (.Aglobal id ofs)) Enil, Eop (.Olea (.Aindexed n2)) (t2 ::: Enil) =>
      Eop (.Olea (.Abased id (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr n2)))) (t2 ::: Enil)
  | Eop (.Olea (.Ascaled sc n1)) (t1 ::: Enil), Eop (.Olea (.Aglobal id ofs)) Enil =>
      Eop (.Olea (.Abasedscaled sc id (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr n1))))
        (t1 ::: Enil)
  | Eop (.Olea (.Aglobal id ofs)) Enil, Eop (.Olea (.Ascaled sc n2)) (t2 ::: Enil) =>
      Eop (.Olea (.Abasedscaled sc id (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr n2))))
        (t2 ::: Enil)
  | Eop (.Olea (.Ascaled sc n)) (t1 ::: Enil), t2 =>
      Eop (.Olea (.Aindexed2scaled sc n)) (t2 ::: t1 ::: Enil)
  | t1, Eop (.Olea (.Ascaled sc n)) (t2 ::: Enil) =>
      Eop (.Olea (.Aindexed2scaled sc n)) (t1 ::: t2 ::: Enil)
  | Eop (.Olea (.Aindexed n)) (t1 ::: Enil), t2 =>
      Eop (.Olea (.Aindexed2 n)) (t1 ::: t2 ::: Enil)
  | t1, Eop (.Olea (.Aindexed n)) (t2 ::: Enil) =>
      Eop (.Olea (.Aindexed2 n)) (t1 ::: t2 ::: Enil)
  | _, _ => Eop (.Olea (.Aindexed2 0)) (e1 ::: e2 ::: Enil)

/-! ## Opposite -/

/-- `SelectOp.negint` -/
def negint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.neg n)) Enil
  | _ => Eop .Oneg (e ::: Enil)

/-! ## Integer and pointer subtraction -/

/-- `SelectOp.sub` -/
def sub (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | t1, Eop (.Ointconst n2) Enil => addimm (Integers.Int.neg n2) t1
  | Eop (.Olea (.Aindexed n1)) (t1 ::: Enil), Eop (.Olea (.Aindexed n2)) (t2 ::: Enil) =>
      addimm (Integers.Int.repr (n1 - n2)) (Eop .Osub (t1 ::: t2 ::: Enil))
  | Eop (.Olea (.Aindexed n1)) (t1 ::: Enil), t2 =>
      addimm (Integers.Int.repr n1) (Eop .Osub (t1 ::: t2 ::: Enil))
  | t1, Eop (.Olea (.Aindexed n2)) (t2 ::: Enil) =>
      addimm (Integers.Int.repr (-n2)) (Eop .Osub (t1 ::: t2 ::: Enil))
  | _, _ => Eop .Osub (e1 ::: e2 ::: Enil)

/-! ## Immediate shifts -/

/-- `SelectOp.shift_is_scale` -/
def shiftIsScale (n : Integers.Int) : Bool :=
  Integers.Int.eq n (Integers.Int.repr 1) || Integers.Int.eq n (Integers.Int.repr 2) ||
  Integers.Int.eq n (Integers.Int.repr 3)

/-- `SelectOp.shlimm` -/
def shlimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1 else
  if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshl (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else
    match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shl n1 n)) Enil
    | Eop (.Oshlimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int.iwordsize
        then Eop (.Oshlimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshlimm n) (e1 ::: Enil)
    | Eop (.Olea (.Aindexed n1)) (t1 ::: Enil) =>
        if shiftIsScale n
        then Eop (.Olea (.Ascaled (Integers.Int.unsigned (Integers.Int.shl Integers.Int.one n))
                                  (Integers.Int.unsigned
                                    (Integers.Int.shl (Integers.Int.repr n1) n)))) (t1 ::: Enil)
        else Eop (.Oshlimm n) (e1 ::: Enil)
    | _ =>
        if shiftIsScale n
        then Eop (.Olea (.Ascaled (Integers.Int.unsigned (Integers.Int.shl Integers.Int.one n)) 0))
               (e1 ::: Enil)
        else Eop (.Oshlimm n) (e1 ::: Enil)

/-- `SelectOp.shruimm` -/
def shruimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1 else
  if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshru (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else
    match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shru n1 n)) Enil
    | Eop (.Oshruimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int.iwordsize
        then Eop (.Oshruimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshruimm n) (e1 ::: Enil)
    | _ => Eop (.Oshruimm n) (e1 ::: Enil)

/-- `SelectOp.shrimm` -/
def shrimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1 else
  if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshr (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else
    match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shr n1 n)) Enil
    | Eop (.Oshrimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int.iwordsize
        then Eop (.Oshrimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshrimm n) (e1 ::: Enil)
    | _ => Eop (.Oshrimm n) (e1 ::: Enil)

/-! ## Integer multiply -/

/-- `SelectOp.mulimm_base` -/
def mulimmBase (n1 : Integers.Int) (e2 : Expr) : Expr :=
  match Integers.Int.one_bits n1 with
  | [i] => shlimm e2 i
  | [i, j] => Elet e2 (add (shlimm (Eletvar 0) i) (shlimm (Eletvar 0) j))
  | _ => Eop (.Omulimm n1) (e2 ::: Enil)

/-- `SelectOp.mulimm` -/
def mulimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then Eop (.Ointconst Integers.Int.zero) Enil
  else if Integers.Int.eq n1 Integers.Int.one then e2
  else match e2 with
    | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.mul n1 n2)) Enil
    | Eop (.Olea (.Aindexed n2)) (t2 ::: Enil) =>
        addimm (Integers.Int.mul n1 (Integers.Int.repr n2)) (mulimmBase n1 t2)
    | _ => mulimmBase n1 e2

/-- `SelectOp.mul` -/
def mul (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => mulimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => mulimm n2 t1
  | _, _ => Eop .Omul (e1 ::: e2 ::: Enil)

/-- `SelectOp.mulhs` -/
def mulhs (e1 e2 : Expr) : Expr := Eop .Omulhs (e1 ::: e2 ::: Enil)
/-- `SelectOp.mulhu` -/
def mulhu (e1 e2 : Expr) : Expr := Eop .Omulhu (e1 ::: e2 ::: Enil)

/-! ## Bitwise and, or, xor -/

/-- `SelectOp.andimm` -/
def andimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then Eop (.Ointconst Integers.Int.zero) Enil
  else if Integers.Int.eq n1 Integers.Int.mone then e2
  else match e2 with
    | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.and n1 n2)) Enil
    | Eop (.Oandimm n2) (t2 ::: Enil) => Eop (.Oandimm (Integers.Int.and n1 n2)) (t2 ::: Enil)
    | Eop .Ocast8unsigned (t2 ::: Enil) =>
        Eop (.Oandimm (Integers.Int.and n1 (Integers.Int.repr 255))) (t2 ::: Enil)
    | Eop .Ocast16unsigned (t2 ::: Enil) =>
        Eop (.Oandimm (Integers.Int.and n1 (Integers.Int.repr 65535))) (t2 ::: Enil)
    | _ => Eop (.Oandimm n1) (e2 ::: Enil)

/-- `SelectOp.and` -/
def and (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => andimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => andimm n2 t1
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
  | Eop (.Oshlimm n1) (t1 ::: Enil), Eop (.Oshruimm n2) (t2 ::: Enil) =>
      if Integers.Int.eq (Integers.Int.add n1 n2) Integers.Int.iwordsize then
        if sameExprPure t1 t2
        then Eop (.Ororimm n2) (t1 ::: Enil)
        else Eop (.Oshldimm n1) (t1 ::: t2 ::: Enil)
      else Eop .Oor (e1 ::: e2 ::: Enil)
  | Eop (.Oshruimm n2) (t2 ::: Enil), Eop (.Oshlimm n1) (t1 ::: Enil) =>
      if Integers.Int.eq (Integers.Int.add n1 n2) Integers.Int.iwordsize then
        if sameExprPure t1 t2
        then Eop (.Ororimm n2) (t1 ::: Enil)
        else Eop (.Oshldimm n1) (t1 ::: t2 ::: Enil)
      else Eop .Oor (e1 ::: e2 ::: Enil)
  | _, _ => Eop .Oor (e1 ::: e2 ::: Enil)

/-- `SelectOp.xorimm` -/
def xorimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then e2
  else match e2 with
    | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.xor n1 n2)) Enil
    | Eop (.Oxorimm n2) (t2 ::: Enil) => Eop (.Oxorimm (Integers.Int.xor n1 n2)) (t2 ::: Enil)
    | Eop .Onot (t2 ::: Enil) => Eop (.Oxorimm (Integers.Int.not n1)) (t2 ::: Enil)
    | _ => Eop (.Oxorimm n1) (e2 ::: Enil)

/-- `SelectOp.xor` -/
def xor (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => xorimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => xorimm n2 t1
  | _, _ => Eop .Oxor (e1 ::: e2 ::: Enil)

/-! ## Integer division and modulus -/

/-- `SelectOp.divu_base` -/
def divuBase (e1 e2 : Expr) : Expr := Eop .Odivu (e1 ::: e2 ::: Enil)
/-- `SelectOp.modu_base` -/
def moduBase (e1 e2 : Expr) : Expr := Eop .Omodu (e1 ::: e2 ::: Enil)
/-- `SelectOp.divs_base` -/
def divsBase (e1 e2 : Expr) : Expr := Eop .Odiv (e1 ::: e2 ::: Enil)
/-- `SelectOp.mods_base` -/
def modsBase (e1 e2 : Expr) : Expr := Eop .Omod (e1 ::: e2 ::: Enil)

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
  | .Ceq, Eop (.Oandimm n1) (t1 ::: Enil) =>
      if n2 = Integers.Int.zero then Eop (.Ocmp (.Cmaskzero n1)) (t1 ::: Enil)
      else Eop (.Ocmp (default c n2)) (e1 ::: Enil)
  | .Cne, Eop (.Oandimm n1) (t1 ::: Enil) =>
      if n2 = Integers.Int.zero then Eop (.Ocmp (.Cmasknotzero n1)) (t1 ::: Enil)
      else Eop (.Ocmp (default c n2)) (e1 ::: Enil)
  | _, _ => Eop (.Ocmp (default c n2)) (e1 ::: Enil)

/-- `SelectOp.comp` -/
def comp (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => compimm .Ccompimm Integers.Int.cmp c.swap t2 n1
  | t1, Eop (.Ointconst n2) Enil => compimm .Ccompimm Integers.Int.cmp c t1 n2
  | _, _ => Eop (.Ocmp (.Ccomp c)) (e1 ::: e2 ::: Enil)

/-- `SelectOp.compu` -/
def compu (c : Comparison) (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => compimm .Ccompuimm Integers.Int.cmpu c.swap t2 n1
  | t1, Eop (.Ointconst n2) Enil => compimm .Ccompuimm Integers.Int.cmpu c t1 n2
  | _, _ => Eop (.Ocmp (.Ccompu c)) (e1 ::: e2 ::: Enil)

/-- `SelectOp.compf` -/
def compf (c : Comparison) (e1 e2 : Expr) : Expr := Eop (.Ocmp (.Ccompf c)) (e1 ::: e2 ::: Enil)
/-- `SelectOp.compfs` -/
def compfs (c : Comparison) (e1 e2 : Expr) : Expr := Eop (.Ocmp (.Ccompfs c)) (e1 ::: e2 ::: Enil)

/-! ## Integer conversions -/

/-- `SelectOp.cast8unsigned` -/
def cast8unsigned (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.zero_ext 8 n)) Enil
  | Eop (.Oandimm n) (t ::: Enil) => andimm (Integers.Int.and (Integers.Int.repr 255) n) t
  | _ => Eop .Ocast8unsigned (e ::: Enil)

/-- `SelectOp.cast8signed` -/
def cast8signed (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.sign_ext 8 n)) Enil
  | _ => Eop .Ocast8signed (e ::: Enil)

/-- `SelectOp.cast16unsigned` -/
def cast16unsigned (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.zero_ext 16 n)) Enil
  | Eop (.Oandimm n) (t ::: Enil) => andimm (Integers.Int.and (Integers.Int.repr 65535) n) t
  | _ => Eop .Ocast16unsigned (e ::: Enil)

/-- `SelectOp.cast16signed` -/
def cast16signed (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.sign_ext 16 n)) Enil
  | _ => Eop .Ocast16signed (e ::: Enil)

/-! ## Selection -/

/-- `SelectOp.select_supported` -/
def selectSupported (ty : ATyp) : Bool :=
  match ty with
  | .Tint => true
  | .Tlong => Archi.ptr64
  | _ => false

/-- `SelectOp.select_swap`: the conditions that `Asmgen.mk_sel` cannot handle
directly (they are implemented as an "and" of two flags); for those the
negated condition is used and the arguments are swapped. -/
def selectSwap (cond : Condition) : Bool :=
  match cond with
  | .Ccompf .Cne | .Ccompfs .Cne | .Cnotcompf .Ceq | .Cnotcompfs .Ceq => true
  | _ => false

/-- `SelectOp.select` -/
def select (ty : ATyp) (cond : Condition) (args : Exprlist) (e1 e2 : Expr) : Expr :=
  if selectSwap cond
  then Eop (.Osel (negateCondition cond) ty) (e2 ::: e1 ::: args)
  else Eop (.Osel cond ty) (e1 ::: e2 ::: args)

/-! ## Floating-point conversions -/

def singleoffloat (e : Expr) : Expr := Eop .Osingleoffloat (e ::: Enil)
def floatofsingle (e : Expr) : Expr := Eop .Ofloatofsingle (e ::: Enil)
def intoffloat (e : Expr) : Expr := Eop .Ointoffloat (e ::: Enil)

/-- `SelectOp.floatofint` -/
def floatofint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ofloatconst (Floats.Float.ofInt n)) Enil
  | _ => Eop .Ofloatofint (e ::: Enil)

/-- `SelectOp.intuoffloat` -/
def intuoffloat (e : Expr) : Expr :=
  if Archi.splitlong then
    Elet e
      (Elet (Eop (.Ofloatconst (Floats.Float.ofIntu ox8000_0000)) Enil)
        (Econdition (CEcond (.Ccompf .Clt) (Eletvar 1 ::: Eletvar 0 ::: Enil))
          (intoffloat (Eletvar 1))
          (addimm ox8000_0000 (intoffloat (subf (Eletvar 1) (Eletvar 0))))))
  else
    Eop .Olowlong (Eop .Olongoffloat (e ::: Enil) ::: Enil)

/-- `SelectOp.floatofintu` -/
def floatofintu (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ofloatconst (Floats.Float.ofIntu n)) Enil
  | _ =>
    if Archi.splitlong then
      let f := Eop (.Ofloatconst (Floats.Float.ofIntu ox8000_0000)) Enil
      Elet e
        (Econdition (CEcond (.Ccompuimm .Clt ox8000_0000) (Eletvar 0 ::: Enil))
          (floatofint (Eletvar 0))
          (addf (floatofint (addimm (Integers.Int.neg ox8000_0000) (Eletvar 0))) f))
    else
      Eop .Ofloatoflong (Eop .Ocast32unsigned (e ::: Enil) ::: Enil)

def intofsingle (e : Expr) : Expr := Eop .Ointofsingle (e ::: Enil)

/-- `SelectOp.singleofint` -/
def singleofint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Osingleconst (Floats.Float32.ofInt n)) Enil
  | _ => Eop .Osingleofint (e ::: Enil)

/-- `SelectOp.intuofsingle` -/
def intuofsingle (e : Expr) : Expr := intuoffloat (floatofsingle e)

/-- `SelectOp.singleofintu` -/
def singleofintu (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Osingleconst (Floats.Float32.ofIntu n)) Enil
  | _ => singleoffloat (floatofintu e)

/-! ## Addressing modes -/

/-- `SelectOp.addressing` -/
def addressing (_chunk : Chunk) (e : Expr) : Addressing × Exprlist :=
  match e with
  | Eop (.Olea addr) args =>
      if !Archi.ptr64 && addressingValid addr then (addr, args) else (.Aindexed 0, e ::: Enil)
  | Eop (.Oleal addr) args =>
      if Archi.ptr64 && addressingValid addr then (addr, args) else (.Aindexed 0, e ::: Enil)
  | _ => (.Aindexed 0, e ::: Enil)

/-! ## Arguments of builtins -/

/-- `SelectOp.builtin_arg_addr` -/
def builtinArgAddr (addr : Addressing) (el : Exprlist) : BuiltinArg Expr :=
  match addr, el with
  | .Aindexed n, e1 ::: Enil =>
      .BA_addptr (.BA e1)
        (if Archi.ptr64 then .BA_long (Integers.Int64.repr n) else .BA_int (Integers.Int.repr n))
  | .Aglobal id ofs, Enil => .BA_addrglobal id ofs
  | .Ainstack ofs, Enil => .BA_addrstack ofs
  | _, _ => .BA (Eop (oleaPtr addr) el)

/-- `SelectOp.builtin_arg` -/
def builtinArg (e : Expr) : BuiltinArg Expr :=
  match e with
  | Eop (.Ointconst n) Enil => .BA_int n
  | Eop (.Olongconst n) Enil => .BA_long n
  | Eop (.Olea addr) el => if Archi.ptr64 then .BA e else builtinArgAddr addr el
  | Eop (.Oleal addr) el => if Archi.ptr64 then builtinArgAddr addr el else .BA e
  | Eop .Omakelong (Eop (.Ointconst h) Enil ::: Eop (.Ointconst l) Enil ::: Enil) =>
      .BA_long (Integers.Int64.ofwords h l)
  | Eop .Omakelong (h ::: l ::: Enil) => .BA_splitlong (.BA h) (.BA l)
  | Eload chunk (.Aglobal id ofs) Enil => .BA_loadglobal chunk id ofs
  | Eload chunk (.Ainstack ofs) Enil => .BA_loadstack chunk ofs
  | _ => .BA e

/-! ## Platform-specific known builtins -/

/-- `Builtins1.platform_builtin` (x86): `__builtin_fmax` and `__builtin_fmin`. -/
inductive PlatformBuiltinX86 where
  | BI_fmax
  | BI_fmin
  deriving DecidableEq

/-- `SelectOp.platform_builtin` (x86), on the x86 platform built-ins. -/
def platformBuiltinX86 (b : PlatformBuiltinX86) (args : Exprlist) : Option Expr :=
  match b, args with
  | .BI_fmax, e1 ::: e2 ::: Enil => some (Eop .Omaxf (e1 ::: e2 ::: Enil))
  | .BI_fmin, e1 ::: e2 ::: Enil => some (Eop .Ominf (e1 ::: e2 ::: Enil))
  | _, _ => none

/-- `SelectOp.platform_builtin` on the port's shared (empty) platform built-in type. -/
def platformBuiltin (b : Builtins.PlatformBuiltin) (_args : Exprlist) : Option Expr := nomatch b

end SelectOp
end X86
end CC
