/-
  Pretty-printing of operators, conditions and addressing modes for the
  PowerPC back end — port of `powerpc/PrintOp.ml`.

  The OCaml functions take a register printer `reg` and print to a
  formatter; here `reg : R → String` and the functions return strings.
  Numbers are formatted as by OCaml's `Printf` (see the `Printf` section of
  `CCLib/lib/Camlcoq.lean`); pointer offsets are printed with `%ld`, as in
  the OCaml file.  `comparison_name` is the shared `PrintAST.comparisonName`.
  Operators without a case in the OCaml file (`Omulhs`, `Omullhs`, ...)
  print as `<bad operator>`, as there.
-/
import CCLib.powerpc.Op
import CCLib.common.PrintAST

namespace CC
namespace PowerPC
namespace PrintOp

open Camlcoq Op PrintAST

/-- `PrintOp.print_condition` -/
def printCondition {R : Type} (reg : R → String) : Condition → List R → String
  | .Ccomp c, [r1, r2] => s!"{reg r1} {comparisonName c}s {reg r2}"
  | .Ccompu c, [r1, r2] => s!"{reg r1} {comparisonName c}u {reg r2}"
  | .Ccompimm c n, [r1] => s!"{reg r1} {comparisonName c}s {ci32 n}"
  | .Ccompuimm c n, [r1] => s!"{reg r1} {comparisonName c}u {ci32 n}"
  | .Ccompf c, [r1, r2] => s!"{reg r1} {comparisonName c}f {reg r2}"
  | .Cnotcompf c, [r1, r2] => s!"{reg r1} not({comparisonName c}f) {reg r2}"
  | .Cmaskzero n, [r1] => s!"{reg r1} & 0x{cx32 n} == 0"
  | .Cmasknotzero n, [r1] => s!"{reg r1} & 0x{cx32 n} != 0"
  | .Ccompl c, [r1, r2] => s!"{reg r1} {comparisonName c}ls {reg r2}"
  | .Ccomplu c, [r1, r2] => s!"{reg r1} {comparisonName c}lu {reg r2}"
  | .Ccomplimm c n, [r1] => s!"{reg r1} {comparisonName c}ls {ci64 n}"
  | .Ccompluimm c n, [r1] => s!"{reg r1} {comparisonName c}lu {ci64 n}"
  | _, _ => "<bad condition>"

/-- `PrintOp.print_operation` -/
def printOperation {R : Type} (reg : R → String) : Operation → List R → String
  | .Omove, [r1] => reg r1
  | .Ointconst n, [] => s!"{ci32 n}"
  | .Ofloatconst n, [] => s!"{floatF n 15}"
  | .Osingleconst n, [] => s!"{float32F n 15}f"
  | .Oaddrsymbol id ofs, [] => s!"\"{externAtom id}\" + {ci32 ofs}"
  | .Oaddrstack ofs, [] => s!"stack({ci32 ofs})"
  | .Ocast8signed, [r1] => s!"int8signed({reg r1})"
  | .Ocast16signed, [r1] => s!"int16signed({reg r1})"
  | .Oadd, [r1, r2] => s!"{reg r1} + {reg r2}"
  | .Oaddimm n, [r1] => s!"{reg r1} + {ci32 n}"
  | .Oaddsymbol id ofs, [r1] => s!"\"{externAtom id}\" + {ci32 ofs} + {reg r1}"
  | .Osub, [r1, r2] => s!"{reg r1} - {reg r2}"
  | .Osubimm n, [r1] => s!"{ci32 n} - {reg r1}"
  | .Omul, [r1, r2] => s!"{reg r1} * {reg r2}"
  | .Omulimm n, [r1] => s!"{reg r1} * {ci32 n}"
  | .Odiv, [r1, r2] => s!"{reg r1} /s {reg r2}"
  | .Odivu, [r1, r2] => s!"{reg r1} /u {reg r2}"
  | .Oand, [r1, r2] => s!"{reg r1} & {reg r2}"
  | .Oandimm n, [r1] => s!"{reg r1} & {ci32 n}"
  | .Oor, [r1, r2] => s!"{reg r1} | {reg r2}"
  | .Oorimm n, [r1] => s!"{reg r1} | {ci32 n}"
  | .Oxor, [r1, r2] => s!"{reg r1} ^ {reg r2}"
  | .Oxorimm n, [r1] => s!"{reg r1} ^ {ci32 n}"
  | .Onot, [r1] => s!"not({reg r1})"
  | .Onand, [r1, r2] => s!"not({reg r1} & {reg r2})"
  | .Onor, [r1, r2] => s!"not({reg r1} | {reg r2})"
  | .Onxor, [r1, r2] => s!"not({reg r1} ^ {reg r2})"
  | .Oandc, [r1, r2] => s!"{reg r1} & not {reg r2}"
  | .Oorc, [r1, r2] => s!"{reg r1} | not {reg r2}"
  | .Oshl, [r1, r2] => s!"{reg r1} << {reg r2}"
  | .Oshr, [r1, r2] => s!"{reg r1} >>s {reg r2}"
  | .Oshrimm n, [r1] => s!"{reg r1} >>s {ci32 n}"
  | .Oshrximm n, [r1] => s!"{reg r1} >>x {ci32 n}"
  | .Oshru, [r1, r2] => s!"{reg r1} >>u {reg r2}"
  | .Orolm n m, [r1] => s!"({reg r1} rol {ci32 n}) & 0x{cx32 m}"
  | .Oroli n m, [r1, r2] =>
    s!"({reg r1} & ~0x{cx32 m}) | (({reg r2} rol {ci32 n}) & 0x{cx32 m})"
  | .Onegf, [r1] => s!"negf({reg r1})"
  | .Oabsf, [r1] => s!"absf({reg r1})"
  | .Oaddf, [r1, r2] => s!"{reg r1} +f {reg r2}"
  | .Osubf, [r1, r2] => s!"{reg r1} -f {reg r2}"
  | .Omulf, [r1, r2] => s!"{reg r1} *f {reg r2}"
  | .Odivf, [r1, r2] => s!"{reg r1} /f {reg r2}"
  | .Onegfs, [r1] => s!"negfs({reg r1})"
  | .Oabsfs, [r1] => s!"absfs({reg r1})"
  | .Oaddfs, [r1, r2] => s!"{reg r1} +fs {reg r2}"
  | .Osubfs, [r1, r2] => s!"{reg r1} -fs {reg r2}"
  | .Omulfs, [r1, r2] => s!"{reg r1} *fs {reg r2}"
  | .Odivfs, [r1, r2] => s!"{reg r1} /fs {reg r2}"
  | .Osingleoffloat, [r1] => s!"singleoffloat({reg r1})"
  | .Ofloatofsingle, [r1] => s!"floatofsingle({reg r1})"
  | .Ointoffloat, [r1] => s!"intoffloat({reg r1})"
  | .Ofloatofwords, [r1, r2] => s!"floatofwords({reg r1},{reg r2})"
  | .Omakelong, [r1, r2] => s!"makelong({reg r1},{reg r2})"
  | .Olowlong, [r1] => s!"lowlong({reg r1})"
  | .Ohighlong, [r1] => s!"highlong({reg r1})"
  | .Ocmp c, args => printCondition reg c args
  | .Osel c ty, r1 :: r2 :: args =>
    s!"{printCondition reg c args} ?{nameOfType ty} {reg r1} : {reg r2}"
  | .Olongconst n, [] => s!"{ci64 n}L"
  | .Ocast32signed, [r1] => s!"int32signed({reg r1})"
  | .Ocast32unsigned, [r1] => s!"int32unsigned({reg r1})"
  | .Oaddl, [r1, r2] => s!"{reg r1} +l {reg r2}"
  | .Oaddlimm n, [r1] => s!"{reg r1} +l {ci64 n}"
  | .Osubl, [r1, r2] => s!"{reg r1} -l {reg r2}"
  | .Onegl, [r1] => s!"-l {reg r1}"
  | .Omull, [r1, r2] => s!"{reg r1} *l {reg r2}"
  | .Odivl, [r1, r2] => s!"{reg r1} /ls {reg r2}"
  | .Odivlu, [r1, r2] => s!"{reg r1} /lu {reg r2}"
  | .Oandl, [r1, r2] => s!"{reg r1} &l {reg r2}"
  | .Oandlimm n, [r1] => s!"{reg r1} &l {ci64 n}"
  | .Oorl, [r1, r2] => s!"{reg r1} |l {reg r2}"
  | .Oorlimm n, [r1] => s!"{reg r1} |l {ci64 n}"
  | .Oxorl, [r1, r2] => s!"{reg r1} ^l {reg r2}"
  | .Oxorlimm n, [r1] => s!"{reg r1} ^l {ci64 n}"
  | .Onotl, [r1] => s!"~l {reg r1}"
  | .Oshll, [r1, r2] => s!"{reg r1} <<l {reg r2}"
  | .Oshrl, [r1, r2] => s!"{reg r1} >>ls {reg r2}"
  | .Oshrlimm n, [r1] => s!"{reg r1} >>ls {ci32 n}"
  | .Oshrlu, [r1, r2] => s!"{reg r1} >>lu {reg r2}"
  | .Orolml n m, [r1] => s!"({reg r1} rol {ci64 n}) &l 0x{cx64 m}"
  | .Olongoffloat, [r1] => s!"longoffloat({reg r1})"
  | .Ofloatoflong, [r1] => s!"floatoflong({reg r1})"
  | _, _ => "<bad operator>"

/-- `PrintOp.print_addressing` -/
def printAddressing {R : Type} (reg : R → String) : Addressing → List R → String
  | .Aindexed n, [r1] => s!"{reg r1} + {ci32 n}"
  | .Aindexed2, [r1, r2] => s!"{reg r1} + {reg r2}"
  | .Aglobal id ofs, [] => s!"{externAtom id} + {ci32 ofs}"
  | .Abased id ofs, [r1] => s!"{externAtom id} + {ci32 ofs} + {reg r1}"
  | .Ainstack ofs, [] => s!"stack({ci32 ofs})"
  | _, _ => "<bad addressing>"

end PrintOp
end PowerPC
end CC
