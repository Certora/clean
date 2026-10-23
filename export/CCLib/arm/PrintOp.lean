/-
  Pretty-printing of operators, conditions and addressing modes for the
  ARM back end — port of `arm/PrintOp.ml`.

  The OCaml functions take a register printer `reg` and print to a
  formatter; here `reg : R → String` and the functions return strings.
  Numbers are formatted as by OCaml's `Printf` (see the `Printf` section of
  `CCLib/lib/Camlcoq.lean`); ARM is a 32-bit target, so pointer offsets are
  printed with `%ld` like the other 32-bit integers.  `comparison_name` is
  the shared `PrintAST.comparisonName`.  As in the OCaml file, `Omulhs` and
  `Omulhu` have no case and print as `<bad operator>`.
-/
import CCLib.arm.Op
import CCLib.common.PrintAST

namespace CC
namespace Arm
namespace PrintOp

open Camlcoq Op PrintAST

/-- `PrintOp.shift` -/
def shift : Shift → String
  | .Slsl a => s!"<< {ci32 a.s_amount}"
  | .Slsr a => s!">>u {ci32 a.s_amount}"
  | .Sasr a => s!">>s {ci32 a.s_amount}"
  | .Sror a => s!"ror {ci32 a.s_amount}"

/-- `PrintOp.print_condition` -/
def printCondition {R : Type} (reg : R → String) : Condition → List R → String
  | .Ccomp c, [r1, r2] => s!"{reg r1} {comparisonName c}s {reg r2}"
  | .Ccompu c, [r1, r2] => s!"{reg r1} {comparisonName c}u {reg r2}"
  | .Ccompshift c s, [r1, r2] => s!"{reg r1} {comparisonName c}s {reg r2} {shift s}"
  | .Ccompushift c s, [r1, r2] => s!"{reg r1} {comparisonName c}u {reg r2} {shift s}"
  | .Ccompimm c n, [r1] => s!"{reg r1} {comparisonName c}s {ci32 n}"
  | .Ccompuimm c n, [r1] => s!"{reg r1} {comparisonName c}u {ci32 n}"
  | .Ccompf c, [r1, r2] => s!"{reg r1} {comparisonName c}f {reg r2}"
  | .Cnotcompf c, [r1, r2] => s!"{reg r1} not({comparisonName c}f) {reg r2}"
  | .Ccompfzero c, [r1] => s!"{reg r1} {comparisonName c}f 0.0"
  | .Cnotcompfzero c, [r1] => s!"{reg r1} not({comparisonName c}f) 0.0"
  | .Ccompfs c, [r1, r2] => s!"{reg r1} {comparisonName c}fs {reg r2}"
  | .Cnotcompfs c, [r1, r2] => s!"{reg r1} not({comparisonName c}fs) {reg r2}"
  | .Ccompfszero c, [r1] => s!"{reg r1} {comparisonName c}fs 0.0"
  | .Cnotcompfszero c, [r1] => s!"{reg r1} not({comparisonName c}fs) 0.0"
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
  | .Oaddshift s, [r1, r2] => s!"{reg r1} + {reg r2} {shift s}"
  | .Oaddimm n, [r1] => s!"{reg r1} + {ci32 n}"
  | .Osub, [r1, r2] => s!"{reg r1} - {reg r2}"
  | .Osubshift s, [r1, r2] => s!"{reg r1} - {reg r2} {shift s}"
  | .Orsubshift s, [r1, r2] => s!"{reg r2} {shift s} - {reg r1}"
  | .Orsubimm n, [r1] => s!"{ci32 n} - {reg r1}"
  | .Omul, [r1, r2] => s!"{reg r1} * {reg r2}"
  | .Omla, [r1, r2, r3] => s!"{reg r1} * {reg r2} + {reg r3}"
  | .Odiv, [r1, r2] => s!"{reg r1} /s {reg r2}"
  | .Odivu, [r1, r2] => s!"{reg r1} /u {reg r2}"
  | .Oand, [r1, r2] => s!"{reg r1} & {reg r2}"
  | .Oandshift s, [r1, r2] => s!"{reg r1} & {reg r2} {shift s}"
  | .Oandimm n, [r1] => s!"{reg r1} & {ci32 n}"
  | .Oor, [r1, r2] => s!"{reg r1} | {reg r2}"
  | .Oorshift s, [r1, r2] => s!"{reg r1} | {reg r2} {shift s}"
  | .Oorimm n, [r1] => s!"{reg r1} | {ci32 n}"
  | .Oxor, [r1, r2] => s!"{reg r1} ^ {reg r2}"
  | .Oxorshift s, [r1, r2] => s!"{reg r1} ^ {reg r2} {shift s}"
  | .Oxorimm n, [r1] => s!"{reg r1} ^ {ci32 n}"
  | .Obic, [r1, r2] => s!"{reg r1} & not {reg r2}"
  | .Obicshift s, [r1, r2] => s!"{reg r1} & not({reg r2} {shift s})"
  | .Onot, [r1] => s!"not({reg r1})"
  | .Onotshift s, [r1] => s!"not({reg r1} {shift s})"
  | .Oshl, [r1, r2] => s!"{reg r1} << {reg r2}"
  | .Oshr, [r1, r2] => s!"{reg r1} >>s {reg r2}"
  | .Oshru, [r1, r2] => s!"{reg r1} >>u {reg r2}"
  | .Oshift s, [r1] => s!"{reg r1} {shift s}"
  | .Oshrximm n, [r1] => s!"{reg r1} >>x {ci32 n}"
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
  | .Ointoffloat, [r1] => s!"intoffloat({reg r1})"
  | .Ointuoffloat, [r1] => s!"intuoffloat({reg r1})"
  | .Ofloatofint, [r1] => s!"floatofint({reg r1})"
  | .Ofloatofintu, [r1] => s!"floatofintu({reg r1})"
  | .Ofloatofsingle, [r1] => s!"floatofsingle({reg r1})"
  | .Ointofsingle, [r1] => s!"intofsingle({reg r1})"
  | .Ointuofsingle, [r1] => s!"intuofsingle({reg r1})"
  | .Osingleofint, [r1] => s!"singleofint({reg r1})"
  | .Osingleofintu, [r1] => s!"singleofintu({reg r1})"
  | .Omakelong, [r1, r2] => s!"makelong({reg r1},{reg r2})"
  | .Olowlong, [r1] => s!"lowlong({reg r1})"
  | .Ohighlong, [r1] => s!"highlong({reg r1})"
  | .Ocmp c, args => printCondition reg c args
  | .Osel c ty, r1 :: r2 :: args =>
    s!"{printCondition reg c args} ?{nameOfType ty} {reg r1} : {reg r2}"
  | _, _ => "<bad operator>"

/-- `PrintOp.print_addressing` -/
def printAddressing {R : Type} (reg : R → String) : Addressing → List R → String
  | .Aindexed n, [r1] => s!"{reg r1} + {ci32 n}"
  | .Aindexed2, [r1, r2] => s!"{reg r1} + {reg r2}"
  | .Aindexed2shift s, [r1, r2] => s!"{reg r1} + {reg r2} {shift s}"
  | .Ainstack ofs, [] => s!"stack({ci32 ofs})"
  | _, _ => "<bad addressing>"

end PrintOp
end Arm
end CC
