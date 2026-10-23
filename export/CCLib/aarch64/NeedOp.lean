/-
  Neededness analysis for AArch64 operators — port of `aarch64/NeedOp.v`
  (definitions: `needs_of_shift`, `needs_of_shiftl`, `needs_of_extend`,
  `zero_ext'`, `sign_ext'`, `op1`, `op2`, `op1shift`, `op1shiftl`,
  `op2shift`, `op2shiftl`, `op2extl`, `needs_of_condition`,
  `needs_of_operation`, `operation_is_redundant`).  The soundness lemmas
  (`needs_of_operation_sound`, `operation_is_redundant_sound`) are in
  `NeedOpProof.lean`.
-/
import CCLib.backend.NeedDomain
import CCLib.aarch64.Op

namespace CC
namespace NeedOp

open NeedDomain Op

/-- `needs_of_shift` -/
def needsOfShift (s : Shift) (a : Amount32) (nv : Nval) : Nval :=
  match s with
  | .Slsl => shlimm nv a.a32_amount
  | .Sasr => shrimm nv a.a32_amount
  | .Slsr => shruimm nv a.a32_amount
  | .Sror => ror nv a.a32_amount

/-- `needs_of_shiftl` -/
def needsOfShiftl (s : Shift) (a : Amount64) (nv : Nval) : Nval :=
  match s with
  | .Slsl => shllimm nv a.a64_amount
  | .Sasr => shrlimm nv a.a64_amount
  | .Slsr => shrluimm nv a.a64_amount
  | .Sror => rorl nv a.a64_amount

/-- `needs_of_extend` -/
def needsOfExtend (x : Extension) (a : Amount64) (nv : Nval) : Nval :=
  match x with
  | .Xuns32 => longofintu (shllimm nv a.a64_amount)
  | .Xsgn32 => longofint (shllimm nv a.a64_amount)

/-- `zero_ext'` -/
def zeroExt' (s : Z) (nv : Nval) : Nval := if 0 ≤ s then zeroExt s nv else default nv
/-- `sign_ext'` -/
def signExt' (s : Z) (nv : Nval) : Nval := if 0 < s then signExt s nv else default nv

def op1 (nv : Nval) : List Nval := [nv]
def op2 (nv : Nval) : List Nval := [nv, nv]
def op1shift (s : Shift) (a : Amount32) (nv : Nval) : List Nval := [needsOfShift s a nv]
def op1shiftl (s : Shift) (a : Amount64) (nv : Nval) : List Nval := [needsOfShiftl s a nv]
def op2shift (s : Shift) (a : Amount32) (nv : Nval) : List Nval := [nv, needsOfShift s a nv]
def op2shiftl (s : Shift) (a : Amount64) (nv : Nval) : List Nval := [nv, needsOfShiftl s a nv]
def op2extl (x : Extension) (a : Amount64) (nv : Nval) : List Nval := [nv, needsOfExtend x a nv]

/-- `needs_of_condition` -/
def needsOfCondition (_cond : Condition) : List Nval := []

/-- `needs_of_operation` -/
def needsOfOperation (op : Operation) (nv : Nval) : List Nval :=
  match op with
  | .Omove => [nv]
  | .Ointconst _ | .Olongconst _ | .Ofloatconst _ | .Osingleconst _
  | .Oaddrsymbol _ _ | .Oaddrstack _ => []
  | .Oshift s a => op1shift s a nv
  | .Oadd | .Osub | .Omul => op2 (modarith nv)
  | .Oaddshift s a | .Osubshift s a => op2shift s a (modarith nv)
  | .Oaddimm _ => op1 (modarith nv)
  | .Oneg => op1 (modarith nv)
  | .Onegshift s a => op1shift s a (modarith nv)
  | .Omuladd | .Omulsub => let n := modarith nv; [n, n, n]
  | .Odiv | .Odivu => op2 (default nv)
  | .Oand | .Oor | .Oxor => op2 (bitwise nv)
  | .Oandshift s a | .Oorshift s a | .Oxorshift s a => op2shift s a (bitwise nv)
  | .Oandimm n => op1 (andimm nv n)
  | .Oorimm n => op1 (orimm nv n)
  | .Oxorimm _ => op1 (bitwise nv)
  | .Onot => op1 (bitwise nv)
  | .Onotshift s a => [needsOfShift s a (bitwise nv)]
  | .Obic | .Oorn | .Oeqv => let n := bitwise nv; [n, bitwise n]
  | .Obicshift s a | .Oornshift s a | .Oeqvshift s a =>
      let n := bitwise nv; [n, needsOfShift s a (bitwise n)]
  | .Oshl | .Oshr | .Oshru => op2 (default nv)
  | .Oshrximm _ => op1 (default nv)
  | .Ozext s => op1 (zeroExt' s nv)
  | .Osext s => op1 (signExt' s nv)
  | .Oshlzext s a => op1 (zeroExt' s (shlimm nv a.a32_amount))
  | .Oshlsext s a => op1 (signExt' s (shlimm nv a.a32_amount))
  | .Ozextshr a s => op1 (shruimm (zeroExt' s nv) a.a32_amount)
  | .Osextshr a s => op1 (shrimm (signExt' s nv) a.a32_amount)
  | .Oshiftl s a => op1shiftl s a nv
  | .Oextend x a => op1 (needsOfExtend x a nv)
  | .Omakelong => [makelongHi nv, makelongLo nv]
  | .Olowlong => op1 (loword nv)
  | .Ohighlong => op1 (hiword nv)
  | .Oaddl | .Omull => op2 (modarith nv)
  | .Osubl => op2 (default nv)
  | .Oaddlshift s a => op2shiftl s a (modarith nv)
  | .Oaddlext x a => op2extl x a (modarith nv)
  | .Osublshift _ _ | .Osublext _ _ => op2 (default nv)
  | .Oaddlimm _ => op1 (modarith nv)
  | .Onegl => op1 (modarith nv)
  | .Oneglshift s a => op1shiftl s a (modarith nv)
  | .Omulladd => let n := modarith nv; [n, n, n]
  | .Omullsub | .Omullhs | .Omullhu | .Odivl | .Odivlu => op2 (default nv)
  | .Oandl | .Oorl | .Oxorl | .Obicl | .Oornl | .Oeqvl => op2 (bitwise nv)
  | .Oandlshift s a | .Oorlshift s a | .Oxorlshift s a => op2shiftl s a (bitwise nv)
  | .Obiclshift s a | .Oornlshift s a | .Oeqvlshift s a =>
      let n := bitwise nv; [n, needsOfShiftl s a (bitwise n)]
  | .Oandlimm n => op1 (andlimm nv n)
  | .Oorlimm n => op1 (orlimm nv n)
  | .Oxorlimm _ => op1 (bitwise nv)
  | .Onotl => op1 (bitwise nv)
  | .Onotlshift s a => [needsOfShiftl s a (bitwise nv)]
  | .Oshll | .Oshrl | .Oshrlu => op2 (default nv)
  | .Oshrlximm _ => op1 (default nv)
  | .Ozextl _ | .Osextl _
  | .Oshllzext _ _ | .Oshllsext _ _ | .Ozextshrl _ _ | .Osextshrl _ _ => op1 (default nv)
  | .Onegf | .Oabsf => op1 (default nv)
  | .Oaddf | .Osubf | .Omulf | .Odivf => op2 (default nv)
  | .Onegfs | .Oabsfs => op1 (default nv)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => op2 (default nv)
  | .Ofloatofsingle | .Osingleoffloat => op1 (default nv)
  | .Ointoffloat | .Ointuoffloat | .Ofloatofint | .Ofloatofintu => op1 (default nv)
  | .Olongoffloat | .Olonguoffloat | .Ofloatoflong | .Ofloatoflongu => op1 (default nv)
  | .Ointofsingle | .Ointuofsingle | .Osingleofint | .Osingleofintu => op1 (default nv)
  | .Olongofsingle | .Olonguofsingle | .Osingleoflong | .Osingleoflongu => op1 (default nv)
  | .Ocmp c => needsOfCondition c
  | .Osel c _ => nv :: nv :: needsOfCondition c

/-- `operation_is_redundant` -/
def operationIsRedundant (op : Operation) (nv : Nval) : Bool :=
  match op with
  | .Ozext s => decide (0 ≤ s) && zeroExtRedundant s nv
  | .Osext s => decide (0 < s) && signExtRedundant s nv
  | .Oandimm n => andimmRedundant nv n
  | .Oorimm n => orimmRedundant nv n
  | .Oandlimm n => andlimmRedundant nv n
  | .Oorlimm n => orlimmRedundant nv n
  | _ => false

end NeedOp
end CC
