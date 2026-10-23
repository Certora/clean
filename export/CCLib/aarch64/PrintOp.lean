/-
  Pretty-printing of operators, conditions and addressing modes for the
  AArch64 back end — port of `aarch64/PrintOp.ml`.

  The OCaml functions take a register printer `reg` and print to a
  formatter; here `reg : R → String` and the functions return strings.
  Numbers are formatted as by OCaml's `Printf` (see the `Printf` section of
  `CCLib/lib/Camlcoq.lean`).
-/
import CCLib.aarch64.Op
import CCLib.common.PrintAST

namespace CC
namespace PrintOp

open Camlcoq Op

instance : CamlNum Amount32 := ⟨fun a => Integers.Int.unsigned a.a32_amount⟩
instance : CamlNum Amount64 := ⟨fun a => Integers.Int.unsigned a.a64_amount⟩

/-- `PrintOp.comparison_name` -/
abbrev comparisonName : Comparison → String := PrintAST.comparisonName

/-- `PrintOp.shift` -/
def shift {α : Type} [CamlNum α] (s : Shift) (a : α) : String :=
  match s with
  | .Slsl => s!"<< {ci32 a}"
  | .Slsr => s!">>u {ci32 a}"
  | .Sasr => s!">>s {ci32 a}"
  | .Sror => s!"ror {ci32 a}"

/-- `PrintOp.shiftl` -/
def shiftl {α : Type} [CamlNum α] (s : Shift) (a : α) : String :=
  match s with
  | .Slsl => s!"<<l {ci32 a}"
  | .Slsr => s!">>lu {ci32 a}"
  | .Sasr => s!">>ls {ci32 a}"
  | .Sror => s!"rorl {ci32 a}"

/-- `PrintOp.extend_name` -/
def extendName : Extension → String
  | .Xsgn32 => "sext"
  | .Xuns32 => "zext"

/-- `PrintOp.print_condition` -/
def printCondition {R : Type} (reg : R → String) : Condition → List R → String
  | .Ccomp c, [r1, r2] => s!"{reg r1} {comparisonName c}s {reg r2}"
  | .Ccompu c, [r1, r2] => s!"{reg r1} {comparisonName c}u {reg r2}"
  | .Ccompimm c n, [r1] => s!"{reg r1} {comparisonName c}s {ci32 n}"
  | .Ccompuimm c n, [r1] => s!"{reg r1} {comparisonName c}u {ci32 n}"
  | .Ccompshift c s a, [r1, r2] => s!"{reg r1} {comparisonName c}s {reg r2} {shift s a}"
  | .Ccompushift c s a, [r1, r2] => s!"{reg r1} {comparisonName c}u {reg r2} {shift s a}"
  | .Cmaskzero n, [r1] => s!"{reg r1} & 0x{cx32 n} == 0"
  | .Cmasknotzero n, [r1] => s!"{reg r1} & 0x{cx32 n} != 0"
  | .Ccompl c, [r1, r2] => s!"{reg r1} {comparisonName c}ls {reg r2}"
  | .Ccomplu c, [r1, r2] => s!"{reg r1} {comparisonName c}lu {reg r2}"
  | .Ccomplimm c n, [r1] => s!"{reg r1} {comparisonName c}ls {ci64 n}"
  | .Ccompluimm c n, [r1] => s!"{reg r1} {comparisonName c}lu {ci64 n}"
  | .Ccomplshift c s a, [r1, r2] => s!"{reg r1} {comparisonName c}ls {reg r2} {shift s a}"
  | .Ccomplushift c s a, [r1, r2] => s!"{reg r1} {comparisonName c}lu {reg r2} {shift s a}"
  | .Cmasklzero n, [r1] => s!"{reg r1} &l 0x{cx64 n} == 0"
  | .Cmasklnotzero n, [r1] => s!"{reg r1} &l 0x{cx64 n} != 0"
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
  | .Olongconst n, [] => s!"{ci64 n}L"
  | .Ofloatconst n, [] => s!"{floatF n}"
  | .Osingleconst n, [] => s!"{float32F n}f"
  | .Oaddrsymbol id ofs, [] => s!"\"{externAtom id}\" + {ci64 ofs}"
  | .Oaddrstack ofs, [] => s!"stack({ci64 ofs})"
  | .Oshift s a, [r1] => s!"{reg r1} {shift s a}"
  | .Oadd, [r1, r2] => s!"{reg r1} + {reg r2}"
  | .Oaddshift s a, [r1, r2] => s!"{reg r1} + {reg r2} {shift s a}"
  | .Oaddimm n, [r1] => s!"{reg r1} + {ci32 n}"
  | .Oneg, [r1] => s!"- {reg r1}"
  | .Onegshift s a, [r1] => s!"- ({reg r1} {shift s a})"
  | .Osub, [r1, r2] => s!"{reg r1} - {reg r2}"
  | .Osubshift s a, [r1, r2] => s!"{reg r1} - {reg r2} {shift s a}"
  | .Omul, [r1, r2] => s!"{reg r1} * {reg r2}"
  | .Omuladd, [r1, r2, r3] => s!"{reg r3} + {reg r1} * {reg r2}"
  | .Omulsub, [r1, r2, r3] => s!"{reg r3} - {reg r1} * {reg r2}"
  | .Odiv, [r1, r2] => s!"{reg r1} /s {reg r2}"
  | .Odivu, [r1, r2] => s!"{reg r1} /u {reg r2}"
  | .Oand, [r1, r2] => s!"{reg r1} & {reg r2}"
  | .Oandshift s a, [r1, r2] => s!"{reg r1} & {reg r2} {shift s a}"
  | .Oandimm n, [r1] => s!"{reg r1} & {ci32 n}"
  | .Oor, [r1, r2] => s!"{reg r1} | {reg r2}"
  | .Oorshift s a, [r1, r2] => s!"{reg r1} | {reg r2} {shift s a}"
  | .Oorimm n, [r1] => s!"{reg r1} | {ci32 n}"
  | .Oxor, [r1, r2] => s!"{reg r1} ^ {reg r2}"
  | .Oxorshift s a, [r1, r2] => s!"{reg r1} ^ {reg r2} {shift s a}"
  | .Oxorimm n, [r1] => s!"{reg r1} ^ {ci32 n}"
  | .Onot, [r1] => s!"~ {reg r1}"
  | .Onotshift s a, [r1] => s!"~ ({reg r1} {shift s a})"
  | .Obic, [r1, r2] => s!"{reg r1} & ~ {reg r2}"
  | .Obicshift s a, [r1, r2] => s!"{reg r1} & ~ {reg r2} {shift s a}"
  | .Oorn, [r1, r2] => s!"{reg r1} | ~ {reg r2}"
  | .Oornshift s a, [r1, r2] => s!"{reg r1} | ~ {reg r2} {shift s a}"
  | .Oeqv, [r1, r2] => s!"{reg r1} ^ ~ {reg r2}"
  | .Oeqvshift s a, [r1, r2] => s!"{reg r1} ^ ~ {reg r2} {shift s a}"
  | .Oshl, [r1, r2] => s!"{reg r1} << {reg r2}"
  | .Oshr, [r1, r2] => s!"{reg r1} >>s {reg r2}"
  | .Oshru, [r1, r2] => s!"{reg r1} >>u {reg r2}"
  | .Oshrximm n, [r1] => s!"{reg r1} >>x {ci32 n}"
  | .Ozext s, [r1] => s!"zext({zs s}, {reg r1})"
  | .Osext s, [r1] => s!"sext({zs s}, {reg r1})"
  | .Oshlzext s a, [r1] => s!"zext({zs s}, {reg r1}) << {ci32 a}"
  | .Oshlsext s a, [r1] => s!"sext({zs s}, {reg r1}) << {ci32 a}"
  | .Ozextshr a s, [r1] => s!"zext({zs s}, {reg r1} >>u {ci32 a})"
  | .Osextshr a s, [r1] => s!"sext({zs s}, {reg r1} >>s {ci32 a})"
  | .Oshiftl s a, [r1] => s!"{reg r1} {shiftl s a}"
  | .Oextend x a, [r1] => s!"{extendName x}(32, {reg r1}) <<l {ci32 a}"
  | .Omakelong, [r1, r2] => s!"makelong({reg r1},{reg r2})"
  | .Olowlong, [r1] => s!"lowlong({reg r1})"
  | .Ohighlong, [r1] => s!"highlong({reg r1})"
  | .Oaddl, [r1, r2] => s!"{reg r1} +l {reg r2}"
  | .Oaddlshift s a, [r1, r2] => s!"{reg r1} +l {reg r2} {shiftl s a}"
  | .Oaddlext x a, [r1, r2] => s!"{reg r1} +l {extendName x}({reg r2}) << {ci32 a}"
  | .Oaddlimm n, [r1] => s!"{reg r1} +l {ci64 n}"
  | .Onegl, [r1] => s!"-l {reg r1}"
  | .Oneglshift s a, [r1] => s!"-l ({reg r1} {shiftl s a})"
  | .Osubl, [r1, r2] => s!"{reg r1} -l {reg r2}"
  | .Osublext x a, [r1, r2] => s!"{reg r1} +l {extendName x}({reg r2}) << {ci32 a}"
  | .Osublshift s a, [r1, r2] => s!"{reg r1} -l {reg r2} {shiftl s a}"
  | .Omull, [r1, r2] => s!"{reg r1} *l {reg r2}"
  | .Omulladd, [r1, r2, r3] => s!"{reg r3} +l {reg r1} *l {reg r2}"
  | .Omullsub, [r1, r2, r3] => s!"{reg r3} -l {reg r1} *l {reg r2}"
  | .Omullhs, [r1, r2] => s!"{reg r1} *hls {reg r2}"
  | .Omullhu, [r1, r2] => s!"{reg r1} *hlu {reg r2}"
  | .Odivl, [r1, r2] => s!"{reg r1} /ls {reg r2}"
  | .Odivlu, [r1, r2] => s!"{reg r1} /lu {reg r2}"
  | .Oandl, [r1, r2] => s!"{reg r1} &l {reg r2}"
  | .Oandlshift s a, [r1, r2] => s!"{reg r1} &l {reg r2} {shiftl s a}"
  | .Oandlimm n, [r1] => s!"{reg r1} &l {ci64 n}"
  | .Oorl, [r1, r2] => s!"{reg r1} |l {reg r2}"
  | .Oorlshift s a, [r1, r2] => s!"{reg r1} |l {reg r2} {shiftl s a}"
  | .Oorlimm n, [r1] => s!"{reg r1} |l {ci64 n}"
  | .Oxorl, [r1, r2] => s!"{reg r1} ^l {reg r2}"
  | .Oxorlshift s a, [r1, r2] => s!"{reg r1} ^l {reg r2} {shiftl s a}"
  | .Oxorlimm n, [r1] => s!"{reg r1} ^l {ci64 n}"
  | .Onotl, [r1] => s!"~l {reg r1}"
  | .Onotlshift s a, [r1] => s!"~l ({reg r1} {shiftl s a})"
  | .Obicl, [r1, r2] => s!"{reg r1} &l ~l {reg r2}"
  | .Obiclshift s a, [r1, r2] => s!"{reg r1} &l ~l {reg r2} {shiftl s a}"
  | .Oornl, [r1, r2] => s!"{reg r1} |l ~l {reg r2}"
  | .Oornlshift s a, [r1, r2] => s!"{reg r1} |l ~l {reg r2} {shiftl s a}"
  | .Oeqvl, [r1, r2] => s!"{reg r1} ^l ~l {reg r2}"
  | .Oeqvlshift s a, [r1, r2] => s!"{reg r1} ^l ~l {reg r2} {shift s a}"
  | .Oshll, [r1, r2] => s!"{reg r1} <<l {reg r2}"
  | .Oshrl, [r1, r2] => s!"{reg r1} >>ls {reg r2}"
  | .Oshrlu, [r1, r2] => s!"{reg r1} >>lu {reg r2}"
  | .Oshrlximm n, [r1] => s!"{reg r1} >>lx {ci32 n}"
  | .Ozextl s, [r1] => s!"zextl({zs s}, {reg r1})"
  | .Osextl s, [r1] => s!"sextl({zs s}, {reg r1})"
  | .Oshllzext s a, [r1] => s!"zextl({zs s}, {reg r1}) <<l {ci32 a}"
  | .Oshllsext s a, [r1] => s!"sextl({zs s}, {reg r1}) <<l {ci32 a}"
  | .Ozextshrl a s, [r1] => s!"zextl({zs s}, {reg r1} >>lu {ci32 a})"
  | .Osextshrl a s, [r1] => s!"sextl({zs s}, {reg r1} >>ls {ci32 a})"
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
  | .Ointuoffloat, [r1] => s!"intuoffloat({reg r1})"
  | .Ofloatofint, [r1] => s!"floatofint({reg r1})"
  | .Ofloatofintu, [r1] => s!"floatofintu({reg r1})"
  | .Olongoffloat, [r1] => s!"longoffloat({reg r1})"
  | .Olonguoffloat, [r1] => s!"longuoffloat({reg r1})"
  | .Ofloatoflong, [r1] => s!"floatoflong({reg r1})"
  | .Ofloatoflongu, [r1] => s!"floatoflongu({reg r1})"
  | .Ointofsingle, [r1] => s!"intofsingle({reg r1})"
  | .Ointuofsingle, [r1] => s!"intuofsingle({reg r1})"
  | .Osingleofint, [r1] => s!"singleofint({reg r1})"
  | .Osingleofintu, [r1] => s!"singleofintu({reg r1})"
  | .Olongofsingle, [r1] => s!"longofsingle({reg r1})"
  | .Olonguofsingle, [r1] => s!"longuofsingle({reg r1})"
  | .Osingleoflong, [r1] => s!"singleoflong({reg r1})"
  | .Osingleoflongu, [r1] => s!"singleoflongu({reg r1})"
  | .Ocmp c, args => printCondition reg c args
  | .Osel c ty, r1 :: r2 :: args => s!"{printCondition reg c args} ?{PrintAST.nameOfType ty} {reg r1} : {reg r2}"
  | _, _ => "<bad operator>"

/-- `PrintOp.print_addressing` -/
def printAddressing {R : Type} (reg : R → String) : Addressing → List R → String
  | .Aindexed n, [r1] => s!"{reg r1} + {ci64 n}"
  | .Aindexed2, [r1, r2] => s!"{reg r1} + {reg r2}"
  | .Aindexed2shift a, [r1, r2] => s!"{reg r1} + {reg r2} << {ci32 a}"
  | .Aindexed2ext x a, [r1, r2] => s!"{reg r1} + {extendName x}({reg r2}) << {ci32 a}"
  | .Aglobal id ofs, [] => s!"\"{externAtom id}\" + {ci64 ofs}"
  | .Ainstack ofs, [] => s!"stack({ci64 ofs})"
  | _, _ => "<bad addressing>"

end PrintOp
end CC
