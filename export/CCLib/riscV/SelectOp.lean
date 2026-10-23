/-
  Instruction selection for operators (RISC-V) — port of `riscV/SelectOp.vp`
  (whole file).

  `SelectOp.vp` is written with CompCert's `Nondetfunction` notation: a
  `match` whose cases are tried in order.  The RISC-V file has no guarded
  (`??`) cases, so every such function is an ordinary first-match Lean
  `match` with the cases in exactly Rocq's order.  (The commented-out
  alternative `shrximm` of the Rocq file is not ported.)

  Differences from Rocq: the OCaml parameter `symbol_is_relocatable` is an
  explicit argument of `addressing`.
-/
import CCLib.riscV.CminorSel

namespace CC
namespace RiscV
namespace SelectOp

open Op CminorSel Expr Exprlist Condexpr

/-- CminorSel expressions (RISC-V). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists (RISC-V). -/
abbrev Exprlist := CminorSel.Exprlist

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-! ## Constants -/

/-- `SelectOp.addrsymbol` -/
def addrsymbol (id : Ident) (ofs : Integers.Ptrofs) : Expr := Eop (.Oaddrsymbol id ofs) Enil

/-- `SelectOp.addrstack` -/
def addrstack (ofs : Integers.Ptrofs) : Expr := Eop (.Oaddrstack ofs) Enil

/-! ## Integer addition and pointer addition -/

/-- `SelectOp.addimm` -/
def addimm (n : Integers.Int) (e : Expr) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e else
  match e with
  | Eop (.Ointconst m) Enil => Eop (.Ointconst (Integers.Int.add n m)) Enil
  | Eop (.Oaddrsymbol s m) Enil =>
      Eop (.Oaddrsymbol s (Integers.Ptrofs.add (Integers.Ptrofs.of_int n) m)) Enil
  | Eop (.Oaddrstack m) Enil =>
      Eop (.Oaddrstack (Integers.Ptrofs.add (Integers.Ptrofs.of_int n) m)) Enil
  | Eop (.Oaddimm m) (t ::: Enil) => Eop (.Oaddimm (Integers.Int.add n m)) (t ::: Enil)
  | _ => Eop (.Oaddimm n) (e ::: Enil)

/-- `SelectOp.add` -/
def add (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => addimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => addimm n2 t1
  | Eop (.Oaddimm n1) (t1 ::: Enil), Eop (.Oaddimm n2) (t2 ::: Enil) =>
      addimm (Integers.Int.add n1 n2) (Eop .Oadd (t1 ::: t2 ::: Enil))
  | Eop (.Oaddimm n1) (t1 ::: Enil), Eop (.Oaddrstack n2) Enil =>
      Eop .Oadd (Eop (.Oaddrstack (Integers.Ptrofs.add (Integers.Ptrofs.of_int n1) n2)) Enil
        ::: t1 ::: Enil)
  | Eop (.Oaddrstack n1) Enil, Eop (.Oaddimm n2) (t2 ::: Enil) =>
      Eop .Oadd (Eop (.Oaddrstack (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int n2))) Enil
        ::: t2 ::: Enil)
  | Eop (.Oaddimm n1) (t1 ::: Enil), t2 => addimm n1 (Eop .Oadd (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oaddimm n2) (t2 ::: Enil) => addimm n2 (Eop .Oadd (t1 ::: t2 ::: Enil))
  | _, _ => Eop .Oadd (e1 ::: e2 ::: Enil)

/-! ## Integer and pointer subtraction -/

/-- `SelectOp.sub` -/
def sub (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | t1, Eop (.Ointconst n2) Enil => addimm (Integers.Int.neg n2) t1
  | Eop (.Oaddimm n1) (t1 ::: Enil), Eop (.Oaddimm n2) (t2 ::: Enil) =>
      addimm (Integers.Int.sub n1 n2) (Eop .Osub (t1 ::: t2 ::: Enil))
  | Eop (.Oaddimm n1) (t1 ::: Enil), t2 => addimm n1 (Eop .Osub (t1 ::: t2 ::: Enil))
  | t1, Eop (.Oaddimm n2) (t2 ::: Enil) =>
      addimm (Integers.Int.neg n2) (Eop .Osub (t1 ::: t2 ::: Enil))
  | _, _ => Eop .Osub (e1 ::: e2 ::: Enil)

/-- `SelectOp.negint` -/
def negint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.neg n)) Enil
  | _ => Eop .Oneg (e ::: Enil)

/-! ## Immediate shifts -/

/-- `SelectOp.shlimm` -/
def shlimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshl (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shl n1 n)) Enil
    | Eop (.Oshlimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int.iwordsize
        then Eop (.Oshlimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshlimm n) (e1 ::: Enil)
    | _ => Eop (.Oshlimm n) (e1 ::: Enil)

/-- `SelectOp.shruimm` -/
def shruimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshru (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (.Ointconst n1) Enil => Eop (.Ointconst (Integers.Int.shru n1 n)) Enil
    | Eop (.Oshruimm n1) (t1 ::: Enil) =>
        if Integers.Int.ltu (Integers.Int.add n n1) Integers.Int.iwordsize
        then Eop (.Oshruimm (Integers.Int.add n n1)) (t1 ::: Enil)
        else Eop (.Oshruimm n) (e1 ::: Enil)
    | _ => Eop (.Oshruimm n) (e1 ::: Enil)

/-- `SelectOp.shrimm` -/
def shrimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if !(Integers.Int.ltu n Integers.Int.iwordsize) then
    Eop .Oshr (e1 ::: Eop (.Ointconst n) Enil ::: Enil)
  else match e1 with
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
  if Archi.ptr64 then
    Eop .Olowlong
      (Eop (.Oshrlimm (Integers.Int.repr 32))
         (Eop .Omull (Eop .Ocast32signed (e1 ::: Enil) :::
                      Eop .Ocast32signed (e2 ::: Enil) ::: Enil) ::: Enil) ::: Enil)
  else Eop .Omulhs (e1 ::: e2 ::: Enil)

/-- `SelectOp.mulhu` -/
def mulhu (e1 e2 : Expr) : Expr :=
  if Archi.ptr64 then
    Eop .Olowlong
      (Eop (.Oshrluimm (Integers.Int.repr 32))
         (Eop .Omull (Eop .Ocast32unsigned (e1 ::: Enil) :::
                      Eop .Ocast32unsigned (e2 ::: Enil) ::: Enil) ::: Enil) ::: Enil)
  else Eop .Omulhu (e1 ::: e2 ::: Enil)

/-! ## Bitwise and, or, xor -/

/-- `SelectOp.andimm` -/
def andimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then Eop (.Ointconst Integers.Int.zero) Enil
  else if Integers.Int.eq n1 Integers.Int.mone then e2
  else match e2 with
    | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.and n1 n2)) Enil
    | Eop (.Oandimm n2) (t2 ::: Enil) => Eop (.Oandimm (Integers.Int.and n1 n2)) (t2 ::: Enil)
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

/-- `SelectOp.or` -/
def or (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => orimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => orimm n2 t1
  | _, _ => Eop .Oor (e1 ::: e2 ::: Enil)

/-- `SelectOp.xorimm` -/
def xorimm (n1 : Integers.Int) (e2 : Expr) : Expr :=
  if Integers.Int.eq n1 Integers.Int.zero then e2 else
  match e2 with
  | Eop (.Ointconst n2) Enil => Eop (.Ointconst (Integers.Int.xor n1 n2)) Enil
  | Eop (.Oxorimm n2) (t2 ::: Enil) =>
      let n := Integers.Int.xor n1 n2
      if Integers.Int.eq n Integers.Int.zero then t2 else Eop (.Oxorimm n) (t2 ::: Enil)
  | _ => Eop (.Oxorimm n1) (e2 ::: Enil)

/-- `SelectOp.xor` -/
def xor (e1 e2 : Expr) : Expr :=
  match e1, e2 with
  | Eop (.Ointconst n1) Enil, t2 => xorimm n1 t2
  | t1, Eop (.Ointconst n2) Enil => xorimm n2 t1
  | _, _ => Eop .Oxor (e1 ::: e2 ::: Enil)

/-- `SelectOp.notint` -/
def notint (e : Expr) : Expr := xorimm Integers.Int.mone e

/-! ## Integer division and modulus -/

/-- `SelectOp.divs_base` -/
def divsBase (e1 e2 : Expr) : Expr := Eop .Odiv (e1 ::: e2 ::: Enil)
/-- `SelectOp.mods_base` -/
def modsBase (e1 e2 : Expr) : Expr := Eop .Omod (e1 ::: e2 ::: Enil)
/-- `SelectOp.divu_base` -/
def divuBase (e1 e2 : Expr) : Expr := Eop .Odivu (e1 ::: e2 ::: Enil)
/-- `SelectOp.modu_base` -/
def moduBase (e1 e2 : Expr) : Expr := Eop .Omodu (e1 ::: e2 ::: Enil)

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
def cast8unsigned (e : Expr) : Expr := andimm (Integers.Int.repr 255) e

/-- `SelectOp.cast8signed` -/
def cast8signed (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.sign_ext 8 n)) Enil
  | _ => Eop .Ocast8signed (e ::: Enil)

/-- `SelectOp.cast16unsigned` -/
def cast16unsigned (e : Expr) : Expr := andimm (Integers.Int.repr 65535) e

/-- `SelectOp.cast16signed` -/
def cast16signed (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => Eop (.Ointconst (Integers.Int.sign_ext 16 n)) Enil
  | _ => Eop .Ocast16signed (e ::: Enil)

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
def singleofint (e : Expr) : Expr := Eop .Osingleofint (e ::: Enil)
def intuofsingle (e : Expr) : Expr := Eop .Ointuofsingle (e ::: Enil)
def singleofintu (e : Expr) : Expr := Eop .Osingleofintu (e ::: Enil)
def singleoffloat (e : Expr) : Expr := Eop .Osingleoffloat (e ::: Enil)
def floatofsingle (e : Expr) : Expr := Eop .Ofloatofsingle (e ::: Enil)

/-! ## Selection -/

/-- `SelectOp.select_supported` -/
def selectSupported (ty : ATyp) : Bool :=
  match ty with
  | .Tint => true
  | .Tlong => Archi.ptr64
  | _ => false

/-- `SelectOp.select_swap`: `>=` and `<=` comparisons are turned into their
negations, with the two arguments of the selection swapped. -/
def selectSwap (cond : Condition) : Bool :=
  match cond with
  | .Ccomp .Cge | .Ccomp .Cle => true
  | .Ccompu .Cge | .Ccompu .Cle => true
  | .Ccompimm .Cge _ | .Ccompimm .Cle _ => true
  | .Ccompuimm .Cge _ | .Ccompuimm .Cle _ => true
  | .Ccompl .Cge | .Ccompl .Cle => true
  | .Ccomplu .Cge | .Ccomplu .Cle => true
  | .Ccomplimm .Cge _ | .Ccomplimm .Cle _ => true
  | .Ccompluimm .Cge _ | .Ccompluimm .Cle _ => true
  | _ => false

/-- `SelectOp.select` -/
def select (ty : ATyp) (cond : Condition) (args : Exprlist) (e1 e2 : Expr) : Expr :=
  if selectSwap cond
  then Eop (.Osel (negateCondition cond) ty) (e2 ::: e1 ::: args)
  else Eop (.Osel cond ty) (e1 ::: e2 ::: args)

/-! ## Addressing modes -/

/-- `SelectOp.addressing` -/
def addressing (symbolIsRelocatable : Ident → Bool) (_chunk : Chunk) (e : Expr) :
    Addressing × Exprlist :=
  match e with
  | Eop (.Oaddrstack n) Enil => (.Ainstack n, Enil)
  | Eop (.Oaddrsymbol id ofs) Enil =>
      if symbolIsRelocatable id then (.Aindexed Integers.Ptrofs.zero, e ::: Enil)
      else (.Aglobal id ofs, Enil)
  | Eop (.Oaddimm n) (e1 ::: Enil) => (.Aindexed (Integers.Ptrofs.of_int n), e1 ::: Enil)
  | Eop (.Oaddlimm n) (e1 ::: Enil) => (.Aindexed (Integers.Ptrofs.of_int64 n), e1 ::: Enil)
  | _ => (.Aindexed Integers.Ptrofs.zero, e ::: Enil)

/-! ## Arguments of builtins -/

/-- `SelectOp.builtin_arg` -/
def builtinArg (e : Expr) : BuiltinArg Expr :=
  match e with
  | Eop (.Ointconst n) Enil => .BA_int n
  | Eop (.Oaddrsymbol id ofs) Enil => .BA_addrglobal id ofs
  | Eop (.Oaddrstack ofs) Enil => .BA_addrstack ofs
  | Eop .Omakelong (Eop (.Ointconst h) Enil ::: Eop (.Ointconst l) Enil ::: Enil) =>
      .BA_long (Integers.Int64.ofwords h l)
  | Eop .Omakelong (h ::: l ::: Enil) => .BA_splitlong (.BA h) (.BA l)
  | Eload chunk (.Ainstack ofs) Enil => .BA_loadstack chunk ofs
  | Eop (.Oaddimm n) (e1 ::: Enil) =>
      if Archi.ptr64 then .BA e else .BA_addptr (.BA e1) (.BA_int n)
  | Eop (.Oaddlimm n) (e1 ::: Enil) =>
      if Archi.ptr64 then .BA_addptr (.BA e1) (.BA_long n) else .BA e
  | _ => .BA e

/-- `SelectOp.platform_builtin`: RISC-V has no platform-specific built-ins. -/
def platformBuiltin (_b : Builtins.PlatformBuiltin) (_args : Exprlist) : Option Expr := none

end SelectOp
end RiscV
end CC
