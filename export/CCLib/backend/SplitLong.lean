/-
  Instruction selection for 64-bit integer operations on 32-bit targets —
  port of `backend/SplitLong.vp` (whole file).

  In Rocq, `SplitLong.vp` is compiled for every target, on top of that
  target's `Op` and `SelectOp`; the target's `SelectLong.vp` uses it only
  when `Archi.splitlong = true` (32-bit targets).  The configurations of this
  port are 64-bit, so — as in a Rocq build for aarch64 — the definitions are
  instantiated with the aarch64 operators (`CCLib.aarch64.SelectOp`), where
  `Omakelong`, `Olowlong` and `Ohighlong` also exist, and only
  `helper_functions`, the signatures `sig_*` and `lowlong` are used by
  `Selection`.

  Ported: `helper_functions` (the structure `HelperFunctions`, an explicit
  argument instead of a type-class instance), `sig_l_l` … `sig_ii_l`,
  `makelong`, `splitlong`, `splitlong2`, `lowlong`, `highlong`, `longconst`,
  `is_longconst`, `is_longconst_zero`, `intoflong`, `longofint`,
  `longofintu`, `negl`, `notl`, the float conversions, `andl`, `orl`,
  `xorl`, `shllimm`, `shrluimm`, `shrlimm`, `is_intconst`, `shll`, `shrlu`,
  `shrl`, `addl`, `subl`, `mull_base`, `mullimm`, `mull`, `mullhu`,
  `mullhs`, `shrxlimm`, `divlu_base`, `modlu_base`, `divls_base`,
  `modls_base`, `cmpl_eq_zero`, `cmpl_ne_zero`, `cmplu_gen`, `cmplu`,
  `cmpl_gen`, `cmpl`, `select_long`.

  Each `Nondetfunction` is a first-match Lean `match`, as in `SelectOp.lean`.
-/
import CCLib.aarch64.SelectOp

namespace CC
namespace SplitLong

open Op CminorSel SelectOp

/-- CminorSel expressions (disambiguated from Clight's `Expr`). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists. -/
abbrev Exprlist := CminorSel.Exprlist

open CminorSel.Expr CminorSel.Exprlist CminorSel.Condexpr

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `SplitLong.helper_functions`: the names of the runtime library functions
implementing some 64-bit operations. -/
structure HelperFunctions where
  i64_dtos : Ident
  i64_dtou : Ident
  i64_stod : Ident
  i64_utod : Ident
  i64_stof : Ident
  i64_utof : Ident
  i64_sdiv : Ident
  i64_udiv : Ident
  i64_smod : Ident
  i64_umod : Ident
  i64_shl : Ident
  i64_shr : Ident
  i64_sar : Ident
  i64_umulh : Ident
  i64_smulh : Ident

/-- `sig_l_l` -/
def sigLL : Signature := mksignature [.Xlong] .Xlong cc_default
/-- `sig_l_f` -/
def sigLF : Signature := mksignature [.Xlong] .Xfloat cc_default
/-- `sig_l_s` -/
def sigLS : Signature := mksignature [.Xlong] .Xsingle cc_default
/-- `sig_f_l` -/
def sigFL : Signature := mksignature [.Xfloat] .Xlong cc_default
/-- `sig_ll_l` -/
def sigLLL : Signature := mksignature [.Xlong, .Xlong] .Xlong cc_default
/-- `sig_li_l` -/
def sigLIL : Signature := mksignature [.Xlong, .Xint] .Xlong cc_default
/-- `sig_ii_l` -/
def sigIIL : Signature := mksignature [.Xint, .Xint] .Xlong cc_default

/-- `SplitLong.makelong` -/
def makelong (h l : Expr) : Expr := Eop .Omakelong (h ::: l ::: Enil)

/-- `SplitLong.splitlong` -/
def splitlong (e : Expr) (f : Expr → Expr → Expr) : Expr :=
  match e with
  | Eop .Omakelong (h ::: l ::: Enil) => f h l
  | _ => Elet e (f (Eop .Ohighlong (Eletvar 0 ::: Enil)) (Eop .Olowlong (Eletvar 0 ::: Enil)))

/-- `SplitLong.splitlong2` -/
def splitlong2 (e1 e2 : Expr) (f : Expr → Expr → Expr → Expr → Expr) : Expr :=
  match e1, e2 with
  | Eop .Omakelong (h1 ::: l1 ::: Enil), Eop .Omakelong (h2 ::: l2 ::: Enil) => f h1 l1 h2 l2
  | Eop .Omakelong (h1 ::: l1 ::: Enil), t2 =>
    Elet t2 (f (lift h1) (lift l1)
      (Eop .Ohighlong (Eletvar 0 ::: Enil)) (Eop .Olowlong (Eletvar 0 ::: Enil)))
  | t1, Eop .Omakelong (h2 ::: l2 ::: Enil) =>
    Elet t1 (f (Eop .Ohighlong (Eletvar 0 ::: Enil)) (Eop .Olowlong (Eletvar 0 ::: Enil))
      (lift h2) (lift l2))
  | _, _ =>
    Elet e1 (Elet (lift e2)
      (f (Eop .Ohighlong (Eletvar 1 ::: Enil)) (Eop .Olowlong (Eletvar 1 ::: Enil))
        (Eop .Ohighlong (Eletvar 0 ::: Enil)) (Eop .Olowlong (Eletvar 0 ::: Enil))))

/-- `SplitLong.lowlong` -/
def lowlong (e : Expr) : Expr :=
  match e with
  | Eop .Omakelong (_ ::: e2 ::: Enil) => e2
  | _ => Eop .Olowlong (e ::: Enil)

/-- `SplitLong.highlong` -/
def highlong (e : Expr) : Expr :=
  match e with
  | Eop .Omakelong (e1 ::: _ ::: Enil) => e1
  | _ => Eop .Ohighlong (e ::: Enil)

/-- `SplitLong.longconst` -/
def longconst (n : Integers.Int64) : Expr :=
  makelong (Eop (.Ointconst (Integers.Int64.hiword n)) Enil)
    (Eop (.Ointconst (Integers.Int64.loword n)) Enil)

/-- `SplitLong.is_longconst` -/
def is_longconst (e : Expr) : Option Integers.Int64 :=
  match e with
  | Eop .Omakelong (Eop (.Ointconst h) Enil ::: Eop (.Ointconst l) Enil ::: Enil) =>
    some (Integers.Int64.ofwords h l)
  | _ => none

/-- `SplitLong.is_longconst_zero` -/
def is_longconst_zero (e : Expr) : Bool :=
  match is_longconst e with
  | some n => Integers.Int64.eq n Integers.Int64.zero
  | none => false

/-- `SplitLong.intoflong` -/
def intoflong (e : Expr) : Expr := lowlong e

/-- `SplitLong.longofint` -/
def longofint (e : Expr) : Expr :=
  match e with
  | Eop (.Ointconst n) Enil => longconst (Integers.Int64.repr (Integers.Int.signed n))
  | _ => Elet e (makelong (shrimm (Eletvar 0) (Integers.Int.repr 31)) (Eletvar 0))

/-- `SplitLong.longofintu` -/
def longofintu (e : Expr) : Expr := makelong (Eop (.Ointconst Integers.Int.zero) Enil) e

/-- `SplitLong.negl` -/
def negl (e : Expr) : Expr :=
  match is_longconst e with
  | some n => longconst (Integers.Int64.neg n)
  | none => Ebuiltin (.EF_builtin "__builtin_negl" sigLL) (e ::: Enil)

/-- `SplitLong.notl` -/
def notl (e : Expr) : Expr := splitlong e (fun h l => makelong (notint h) (notint l))

section SELECT

variable (hf : HelperFunctions)

/-- `SplitLong.longoffloat` -/
def longoffloat (arg : Expr) : Expr := Eexternal hf.i64_dtos sigFL (arg ::: Enil)
/-- `SplitLong.longuoffloat` -/
def longuoffloat (arg : Expr) : Expr := Eexternal hf.i64_dtou sigFL (arg ::: Enil)
/-- `SplitLong.floatoflong` -/
def floatoflong (arg : Expr) : Expr := Eexternal hf.i64_stod sigLF (arg ::: Enil)
/-- `SplitLong.floatoflongu` -/
def floatoflongu (arg : Expr) : Expr := Eexternal hf.i64_utod sigLF (arg ::: Enil)
/-- `SplitLong.longofsingle` -/
def longofsingle (arg : Expr) : Expr := longoffloat hf (floatofsingle arg)
/-- `SplitLong.longuofsingle` -/
def longuofsingle (arg : Expr) : Expr := longuoffloat hf (floatofsingle arg)
/-- `SplitLong.singleoflong` -/
def singleoflong (arg : Expr) : Expr := Eexternal hf.i64_stof sigLS (arg ::: Enil)
/-- `SplitLong.singleoflongu` -/
def singleoflongu (arg : Expr) : Expr := Eexternal hf.i64_utof sigLS (arg ::: Enil)

end SELECT

/-- `SplitLong.andl` -/
def andl (e1 e2 : Expr) : Expr :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 => makelong (and h1 h2) (and l1 l2))

/-- `SplitLong.orl` -/
def orl (e1 e2 : Expr) : Expr :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 => makelong (or h1 h2) (or l1 l2))

/-- `SplitLong.xorl` -/
def xorl (e1 e2 : Expr) : Expr :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 => makelong (xor h1 h2) (xor l1 l2))

section SELECT

variable (hf : HelperFunctions)

/-- `SplitLong.shllimm` -/
def shllimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if Integers.Int.ltu n Integers.Int.iwordsize then
    splitlong e1 (fun h l =>
      makelong (or (shlimm h n) (shruimm l (Integers.Int.sub Integers.Int.iwordsize n)))
        (shlimm l n))
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then
    makelong (shlimm (lowlong e1) (Integers.Int.sub n Integers.Int.iwordsize))
      (Eop (.Ointconst Integers.Int.zero) Enil)
  else Eexternal hf.i64_shl sigLIL (e1 ::: Eop (.Ointconst n) Enil ::: Enil)

/-- `SplitLong.shrluimm` -/
def shrluimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if Integers.Int.ltu n Integers.Int.iwordsize then
    splitlong e1 (fun h l =>
      makelong (shruimm h n)
        (or (shruimm l n) (shlimm h (Integers.Int.sub Integers.Int.iwordsize n))))
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then
    makelong (Eop (.Ointconst Integers.Int.zero) Enil)
      (shruimm (highlong e1) (Integers.Int.sub n Integers.Int.iwordsize))
  else Eexternal hf.i64_shr sigLIL (e1 ::: Eop (.Ointconst n) Enil ::: Enil)

/-- `SplitLong.shrlimm` -/
def shrlimm (e1 : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e1
  else if Integers.Int.ltu n Integers.Int.iwordsize then
    splitlong e1 (fun h l =>
      makelong (shrimm h n)
        (or (shruimm l n) (shlimm h (Integers.Int.sub Integers.Int.iwordsize n))))
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then
    Elet (highlong e1)
      (makelong (shrimm (Eletvar 0) (Integers.Int.repr 31))
        (shrimm (Eletvar 0) (Integers.Int.sub n Integers.Int.iwordsize)))
  else Eexternal hf.i64_sar sigLIL (e1 ::: Eop (.Ointconst n) Enil ::: Enil)

/-- `SplitLong.is_intconst` -/
def is_intconst (e : Expr) : Option Integers.Int :=
  match e with
  | Eop (.Ointconst n) Enil => some n
  | _ => none

/-- `SplitLong.shll` -/
def shll (e1 e2 : Expr) : Expr :=
  match is_intconst e2 with
  | some n => shllimm hf e1 n
  | none => Eexternal hf.i64_shl sigLIL (e1 ::: e2 ::: Enil)

/-- `SplitLong.shrlu` -/
def shrlu (e1 e2 : Expr) : Expr :=
  match is_intconst e2 with
  | some n => shrluimm hf e1 n
  | none => Eexternal hf.i64_shr sigLIL (e1 ::: e2 ::: Enil)

/-- `SplitLong.shrl` -/
def shrl (e1 e2 : Expr) : Expr :=
  match is_intconst e2 with
  | some n => shrlimm hf e1 n
  | none => Eexternal hf.i64_sar sigLIL (e1 ::: e2 ::: Enil)

end SELECT

/-- `SplitLong.addl` -/
def addl (e1 e2 : Expr) : Expr :=
  let default := Ebuiltin (.EF_builtin "__builtin_addl" sigLLL) (e1 ::: e2 ::: Enil)
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 => longconst (Integers.Int64.add n1 n2)
  | some n1, _ => if Integers.Int64.eq n1 Integers.Int64.zero then e2 else default
  | _, some n2 => if Integers.Int64.eq n2 Integers.Int64.zero then e1 else default
  | _, _ => default

/-- `SplitLong.subl` -/
def subl (e1 e2 : Expr) : Expr :=
  let default := Ebuiltin (.EF_builtin "__builtin_subl" sigLLL) (e1 ::: e2 ::: Enil)
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 => longconst (Integers.Int64.sub n1 n2)
  | some n1, _ => if Integers.Int64.eq n1 Integers.Int64.zero then negl e2 else default
  | _, some n2 => if Integers.Int64.eq n2 Integers.Int64.zero then e1 else default
  | _, _ => default

/-- `SplitLong.mull_base` -/
def mull_base (e1 e2 : Expr) : Expr :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 =>
    Elet (Ebuiltin (.EF_builtin "__builtin_mull" sigIIL) (l1 ::: l2 ::: Enil))
      (makelong
        (add (add (Eop .Ohighlong (Eletvar 0 ::: Enil)) (mul (lift l1) (lift h2)))
          (mul (lift h1) (lift l2)))
        (Eop .Olowlong (Eletvar 0 ::: Enil))))

section SELECT

variable (hf : HelperFunctions)

/-- `SplitLong.mullimm` -/
def mullimm (n : Integers.Int64) (e : Expr) : Expr :=
  if Integers.Int64.eq n Integers.Int64.zero then longconst Integers.Int64.zero
  else if Integers.Int64.eq n Integers.Int64.one then e
  else
    match Integers.Int64.is_power2' n with
    | some l => shllimm hf e l
    | none => mull_base e (longconst n)

/-- `SplitLong.mull` -/
def mull (e1 e2 : Expr) : Expr :=
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 => longconst (Integers.Int64.mul n1 n2)
  | some n1, _ => mullimm hf n1 e2
  | _, some n2 => mullimm hf n2 e1
  | _, _ => mull_base e1 e2

/-- `SplitLong.mullhu` -/
def mullhu (e1 : Expr) (n2 : Integers.Int64) : Expr :=
  Eexternal hf.i64_umulh sigLLL (e1 ::: longconst n2 ::: Enil)
/-- `SplitLong.mullhs` -/
def mullhs (e1 : Expr) (n2 : Integers.Int64) : Expr :=
  Eexternal hf.i64_smulh sigLLL (e1 ::: longconst n2 ::: Enil)

/-- `SplitLong.shrxlimm` -/
def shrxlimm (e : Expr) (n : Integers.Int) : Expr :=
  if Integers.Int.eq n Integers.Int.zero then e
  else
    Elet e (shrlimm hf (addl (Eletvar 0)
        (shrluimm hf (shrlimm hf (Eletvar 0) (Integers.Int.repr 63))
          (Integers.Int.sub (Integers.Int.repr 64) n)))
      n)

/-- `SplitLong.divlu_base` -/
def divlu_base (e1 e2 : Expr) : Expr := Eexternal hf.i64_udiv sigLLL (e1 ::: e2 ::: Enil)
/-- `SplitLong.modlu_base` -/
def modlu_base (e1 e2 : Expr) : Expr := Eexternal hf.i64_umod sigLLL (e1 ::: e2 ::: Enil)
/-- `SplitLong.divls_base` -/
def divls_base (e1 e2 : Expr) : Expr := Eexternal hf.i64_sdiv sigLLL (e1 ::: e2 ::: Enil)
/-- `SplitLong.modls_base` -/
def modls_base (e1 e2 : Expr) : Expr := Eexternal hf.i64_smod sigLLL (e1 ::: e2 ::: Enil)

end SELECT

/-- `SplitLong.cmpl_eq_zero` -/
def cmpl_eq_zero (e : Expr) : Expr :=
  splitlong e (fun h l => comp .Ceq (or h l) (Eop (.Ointconst Integers.Int.zero) Enil))

/-- `SplitLong.cmpl_ne_zero` -/
def cmpl_ne_zero (e : Expr) : Expr :=
  splitlong e (fun h l => comp .Cne (or h l) (Eop (.Ointconst Integers.Int.zero) Enil))

/-- `SplitLong.cmplu_gen` -/
def cmplu_gen (ch cl : Comparison) (e1 e2 : Expr) : Expr :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 =>
    Econdition (CEcond (.Ccomp .Ceq) (h1 ::: h2 ::: Enil))
      (Eop (.Ocmp (.Ccompu cl)) (l1 ::: l2 ::: Enil))
      (Eop (.Ocmp (.Ccompu ch)) (h1 ::: h2 ::: Enil)))

/-- `SplitLong.cmplu` -/
def cmplu (c : Comparison) (e1 e2 : Expr) : Expr :=
  match c with
  | .Ceq => cmpl_eq_zero (xorl e1 e2)
  | .Cne => cmpl_ne_zero (xorl e1 e2)
  | .Clt => cmplu_gen .Clt .Clt e1 e2
  | .Cle => cmplu_gen .Clt .Cle e1 e2
  | .Cgt => cmplu_gen .Cgt .Cgt e1 e2
  | .Cge => cmplu_gen .Cgt .Cge e1 e2

/-- `SplitLong.cmpl_gen` -/
def cmpl_gen (ch cl : Comparison) (e1 e2 : Expr) : Expr :=
  splitlong2 e1 e2 (fun h1 l1 h2 l2 =>
    Econdition (CEcond (.Ccomp .Ceq) (h1 ::: h2 ::: Enil))
      (Eop (.Ocmp (.Ccompu cl)) (l1 ::: l2 ::: Enil))
      (Eop (.Ocmp (.Ccomp ch)) (h1 ::: h2 ::: Enil)))

/-- `SplitLong.cmpl` -/
def cmpl (c : Comparison) (e1 e2 : Expr) : Expr :=
  match c with
  | .Ceq => cmpl_eq_zero (xorl e1 e2)
  | .Cne => cmpl_ne_zero (xorl e1 e2)
  | .Clt =>
    if is_longconst_zero e2 then comp .Clt (highlong e1) (Eop (.Ointconst Integers.Int.zero) Enil)
    else cmpl_gen .Clt .Clt e1 e2
  | .Cle => cmpl_gen .Clt .Cle e1 e2
  | .Cgt => cmpl_gen .Cgt .Cgt e1 e2
  | .Cge =>
    if is_longconst_zero e2 then comp .Cge (highlong e1) (Eop (.Ointconst Integers.Int.zero) Enil)
    else cmpl_gen .Cgt .Cge e1 e2

/-- `SplitLong.select_long` -/
def select_long (cond : Condition) (args : Exprlist) (e1 e2 : Expr) : Expr :=
  if selectSupported .Tlong then select .Tlong cond args e1 e2
  else
    bindExprs (e1 ::: e2 ::: args) (fun al =>
      match al with
      | e1 ::: e2 ::: args =>
        makelong
          (select .Tint cond args (Eop .Ohighlong (e1 ::: Enil)) (Eop .Ohighlong (e2 ::: Enil)))
          (select .Tint cond args (Eop .Olowlong (e1 ::: Enil)) (Eop .Olowlong (e2 ::: Enil)))
      | _ => longconst Integers.Int64.zero)

end SplitLong
end CC
