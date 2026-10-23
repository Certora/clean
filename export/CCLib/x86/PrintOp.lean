/-
  Pretty-printing of operators, conditions and addressing modes for the
  x86-64 back end — port of `x86/PrintOp.ml`.

  The OCaml functions take a register printer `reg` and print to a
  formatter; here `reg : R → String` and the functions return strings.
  Numbers are formatted as by OCaml's `Printf` (see the `Printf` section of
  `CCLib/lib/Camlcoq.lean`).
-/
import CCLib.x86.Op
import CCLib.common.PrintAST

namespace CC
namespace X86
namespace PrintOp

open Camlcoq Op

/-- `PrintOp.comparison_name` -/
abbrev comparisonName : Comparison → String := PrintAST.comparisonName

/-- `PrintOp.print_condition` -/
def printCondition {R : Type} (reg : R → String) : Condition → List R → String
  | .Ccomp c, [r1, r2] => s!"{reg r1} {comparisonName c}s {reg r2}"
  | .Ccompu c, [r1, r2] => s!"{reg r1} {comparisonName c}u {reg r2}"
  | .Ccompimm c n, [r1] => s!"{reg r1} {comparisonName c}s {ci32 n}"
  | .Ccompuimm c n, [r1] => s!"{reg r1} {comparisonName c}u {cu32 n}"
  | .Ccompl c, [r1, r2] => s!"{reg r1} {comparisonName c}ls {reg r2}"
  | .Ccomplu c, [r1, r2] => s!"{reg r1} {comparisonName c}lu {reg r2}"
  | .Ccomplimm c n, [r1] => s!"{reg r1} {comparisonName c}ls {ci64 n}"
  | .Ccompluimm c n, [r1] => s!"{reg r1} {comparisonName c}lu {cu64 n}"
  | .Ccompf c, [r1, r2] => s!"{reg r1} {comparisonName c}f {reg r2}"
  | .Cnotcompf c, [r1, r2] => s!"{reg r1} not({comparisonName c}f) {reg r2}"
  | .Ccompfs c, [r1, r2] => s!"{reg r1} {comparisonName c}fs {reg r2}"
  | .Cnotcompfs c, [r1, r2] => s!"{reg r1} not({comparisonName c}fs) {reg r2}"
  | .Cmaskzero n, [r1] => s!"{reg r1} & 0x{cx32 n} == 0"
  | .Cmasknotzero n, [r1] => s!"{reg r1} & 0x{cx32 n} != 0"
  | _, _ => "<bad condition>"

/-- `PrintOp.print_addressing` -/
def printAddressing {R : Type} (reg : R → String) : Addressing → List R → String
  | .Aindexed n, [r1] => s!"{reg r1} + {zs n}"
  | .Aindexed2 n, [r1, r2] => s!"{reg r1} + {reg r2} + {zs n}"
  | .Ascaled sc n, [r1] => s!"{reg r1} * {zs sc} + {zs n}"
  | .Aindexed2scaled sc n, [r1, r2] => s!"{reg r1} + {reg r2} * {zs sc} + {zs n}"
  | .Aglobal id ofs, [] => s!"{externAtom id} + {zs ofs}"
  | .Abased id ofs, [r1] => s!"{externAtom id} + {zs ofs} + {reg r1}"
  | .Abasedscaled sc id ofs, [r1] => s!"{externAtom id} + {zs ofs} + {reg r1} * {ci32 sc}"
  | .Ainstack ofs, [] => s!"stack({zs ofs})"
  | _, _ => "<bad addressing>"

/-- `PrintOp.print_operation` -/
def printOperation {R : Type} (reg : R → String) : Operation → List R → String
  | .Omove, [r1] => reg r1
  | .Ointconst n, [] => s!"{ci32 n}"
  | .Olongconst n, [] => s!"{ci64 n}L"
  | .Ofloatconst n, [] => s!"{floatF n 15}"
  | .Osingleconst n, [] => s!"{float32F n 15}f"
  | .Oindirectsymbol id, [] => s!"&{externAtom id}"
  | .Ocast8signed, [r1] => s!"int8signed({reg r1})"
  | .Ocast8unsigned, [r1] => s!"int8unsigned({reg r1})"
  | .Ocast16signed, [r1] => s!"int16signed({reg r1})"
  | .Ocast16unsigned, [r1] => s!"int16unsigned({reg r1})"
  | .Oneg, [r1] => s!"(- {reg r1})"
  | .Osub, [r1, r2] => s!"{reg r1} - {reg r2}"
  | .Omul, [r1, r2] => s!"{reg r1} * {reg r2}"
  | .Omulimm n, [r1] => s!"{reg r1} * {ci32 n}"
  | .Omulhs, [r1, r2] => s!"mulhs({reg r1},{reg r2})"
  | .Omulhu, [r1, r2] => s!"mulhu({reg r1},{reg r2})"
  | .Odiv, [r1, r2] => s!"{reg r1} /s {reg r2}"
  | .Odivu, [r1, r2] => s!"{reg r1} /u {reg r2}"
  | .Omod, [r1, r2] => s!"{reg r1} %s {reg r2}"
  | .Omodu, [r1, r2] => s!"{reg r1} %u {reg r2}"
  | .Oand, [r1, r2] => s!"{reg r1} & {reg r2}"
  | .Oandimm n, [r1] => s!"{reg r1} & {ci32 n}"
  | .Oor, [r1, r2] => s!"{reg r1} | {reg r2}"
  | .Oorimm n, [r1] => s!"{reg r1} | {ci32 n}"
  | .Oxor, [r1, r2] => s!"{reg r1} ^ {reg r2}"
  | .Oxorimm n, [r1] => s!"{reg r1} ^ {ci32 n}"
  | .Onot, [r1] => s!"not({reg r1})"
  | .Oshl, [r1, r2] => s!"{reg r1} << {reg r2}"
  | .Oshlimm n, [r1] => s!"{reg r1} << {ci32 n}"
  | .Oshr, [r1, r2] => s!"{reg r1} >>s {reg r2}"
  | .Oshrimm n, [r1] => s!"{reg r1} >>s {ci32 n}"
  | .Oshrximm n, [r1] => s!"{reg r1} >>x {ci32 n}"
  | .Oshru, [r1, r2] => s!"{reg r1} >>u {reg r2}"
  | .Oshruimm n, [r1] => s!"{reg r1} >>u {ci32 n}"
  | .Ororimm n, [r1] => s!"{reg r1} ror {ci32 n}"
  | .Oshldimm n, [r1, r2] => s!"({reg r1}, {reg r2}) << {ci32 n}"
  | .Olea addr, args => printAddressing reg addr args ++ " (int)"
  | .Omakelong, [r1, r2] => s!"makelong({reg r1},{reg r2})"
  | .Olowlong, [r1] => s!"lowlong({reg r1})"
  | .Ohighlong, [r1] => s!"highlong({reg r1})"
  | .Ocast32signed, [r1] => s!"long32signed({reg r1})"
  | .Ocast32unsigned, [r1] => s!"long32unsigned({reg r1})"
  | .Onegl, [r1] => s!"(-l {reg r1})"
  | .Osubl, [r1, r2] => s!"{reg r1} -l {reg r2}"
  | .Omull, [r1, r2] => s!"{reg r1} *l {reg r2}"
  | .Omullimm n, [r1] => s!"{reg r1} *l {ci64 n}"
  | .Omullhs, [r1, r2] => s!"mullhs({reg r1},{reg r2})"
  | .Omullhu, [r1, r2] => s!"mullhu({reg r1},{reg r2})"
  | .Odivl, [r1, r2] => s!"{reg r1} /ls {reg r2}"
  | .Odivlu, [r1, r2] => s!"{reg r1} /lu {reg r2}"
  | .Omodl, [r1, r2] => s!"{reg r1} %ls {reg r2}"
  | .Omodlu, [r1, r2] => s!"{reg r1} %lu {reg r2}"
  | .Oandl, [r1, r2] => s!"{reg r1} &l {reg r2}"
  | .Oandlimm n, [r1] => s!"{reg r1} &l {ci64 n}"
  | .Oorl, [r1, r2] => s!"{reg r1} |l {reg r2}"
  | .Oorlimm n, [r1] => s!"{reg r1} |l {ci64 n}"
  | .Oxorl, [r1, r2] => s!"{reg r1} ^l {reg r2}"
  | .Oxorlimm n, [r1] => s!"{reg r1} ^l {ci64 n}"
  | .Onotl, [r1] => s!"notl({reg r1})"
  | .Oshll, [r1, r2] => s!"{reg r1} <<l {reg r2}"
  | .Oshllimm n, [r1] => s!"{reg r1} <<l {ci32 n}"
  | .Oshrl, [r1, r2] => s!"{reg r1} >>ls {reg r2}"
  | .Oshrlimm n, [r1] => s!"{reg r1} >>ls {ci32 n}"
  | .Oshrxlimm n, [r1] => s!"{reg r1} >>lx {ci32 n}"
  | .Oshrlu, [r1, r2] => s!"{reg r1} >>lu {reg r2}"
  | .Oshrluimm n, [r1] => s!"{reg r1} >>lu {ci32 n}"
  | .Ororlimm n, [r1] => s!"{reg r1} rorl {ci32 n}"
  | .Oleal addr, args => printAddressing reg addr args ++ " (long)"
  | .Onegf, [r1] => s!"negf({reg r1})"
  | .Oabsf, [r1] => s!"absf({reg r1})"
  | .Oaddf, [r1, r2] => s!"{reg r1} +f {reg r2}"
  | .Osubf, [r1, r2] => s!"{reg r1} -f {reg r2}"
  | .Omulf, [r1, r2] => s!"{reg r1} *f {reg r2}"
  | .Odivf, [r1, r2] => s!"{reg r1} /f {reg r2}"
  | .Omaxf, [r1, r2] => s!"max({reg r1}, {reg r2})"
  | .Ominf, [r1, r2] => s!"min({reg r1}, {reg r2})"
  | .Onegfs, [r1] => s!"negfs({reg r1})"
  | .Oabsfs, [r1] => s!"absfs({reg r1})"
  | .Oaddfs, [r1, r2] => s!"{reg r1} +fs {reg r2}"
  | .Osubfs, [r1, r2] => s!"{reg r1} -fs {reg r2}"
  | .Omulfs, [r1, r2] => s!"{reg r1} *fs {reg r2}"
  | .Odivfs, [r1, r2] => s!"{reg r1} /fs {reg r2}"
  | .Osingleoffloat, [r1] => s!"singleoffloat({reg r1})"
  | .Ofloatofsingle, [r1] => s!"floatofsingle({reg r1})"
  | .Ointoffloat, [r1] => s!"intoffloat({reg r1})"
  | .Ofloatofint, [r1] => s!"floatofint({reg r1})"
  | .Ointofsingle, [r1] => s!"intofsingle({reg r1})"
  | .Osingleofint, [r1] => s!"singleofint({reg r1})"
  | .Olongoffloat, [r1] => s!"longoffloat({reg r1})"
  | .Ofloatoflong, [r1] => s!"floatoflong({reg r1})"
  | .Olongofsingle, [r1] => s!"longofsingle({reg r1})"
  | .Osingleoflong, [r1] => s!"singleoflong({reg r1})"
  | .Ocmp c, args => printCondition reg c args
  | .Osel c ty, r1 :: r2 :: args => s!"{printCondition reg c args} ?{PrintAST.nameOfType ty} {reg r1} : {reg r2}"
  | _, _ => "<bad operator>"

end PrintOp
end X86
end CC
