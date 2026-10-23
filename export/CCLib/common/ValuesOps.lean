/-
  The remaining definitions of `common/Values.v`: the typing predicates
  (`has_type` as a `Prop`, `has_type_list`, `has_opttype`, `has_argtype`),
  `bool_of_val`, `maketotal`, the single-precision conversions, the
  backend-only integer operations (`mulhs`, `mulhu`, carries and overflows,
  `shrx`, rotations, `rolm`, …), their 64-bit counterparts, `cmpu`/`cmplu`,
  `maskzero_bool` and `select`.

  `Val.hasRettype` and `Val.mull'` were already ported in `Builtins.lean`
  (which needed them first) and are reused here.

  Everything is a direct transcription of the Rocq definitions; as in
  `Values.lean`, the bit-width argument of `zero_ext_l`/`sign_ext_l` is a
  `Nat` (CompCert's `Z`, which is always non-negative at use sites).
-/
import CCLib.common.Builtins
import CCLib.common.ASTTheory

namespace CC
namespace Val

/-! ## Typing -/

/-- `Values.has_type` as a proposition (the port's `hasType` is the `Bool`
    version; `hasTypeP_iff` relates them). -/
def HasType (v : Val) (t : ATyp) : Prop := hasType v t = true

instance (v : Val) (t : ATyp) : Decidable (HasType v t) :=
  inferInstanceAs (Decidable (hasType v t = true))

/-- `Values.has_type_list` -/
def HasTypeList : List Val → List ATyp → Prop
  | [], [] => True
  | v :: vs, t :: ts => HasType v t ∧ HasTypeList vs ts
  | _, _ => False

/-- `Values.has_opttype` -/
def HasOpttype (v : Val) : Option ATyp → Prop
  | none => v = .Vundef
  | some t => HasType v t

/-- `Values.has_argtype`: strict matching between values and extended types
    (`Vundef` only matches `Xvoid`). Used for function-call arguments. -/
def HasArgtype (v : Val) (x : XType) : Prop :=
  match x, v with
  | .Xbool, .Vint n => n = Integers.Int.zero ∨ n = Integers.Int.one
  | .Xint8signed, .Vint n => n = Integers.Int.sign_ext 8 n
  | .Xint8unsigned, .Vint n => n = Integers.Int.zero_ext 8 n
  | .Xint16signed, .Vint n => n = Integers.Int.sign_ext 16 n
  | .Xint16unsigned, .Vint n => n = Integers.Int.zero_ext 16 n
  | .Xint, .Vint _ => True
  | .Xint, .Vptr _ _ => Archi.ptr64 = false
  | .Xlong, .Vlong _ => True
  | .Xlong, .Vptr _ _ => Archi.ptr64 = true
  | .Xfloat, .Vfloat _ => True
  | .Xsingle, .Vsingle _ => True
  | .Xptr, .Vptr _ _ => True
  | .Xptr, .Vint _ => Archi.ptr64 = false
  | .Xptr, .Vlong _ => Archi.ptr64 = true
  | .Xany32, .Vint _ => True
  | .Xany32, .Vsingle _ => True
  | .Xany32, .Vptr _ _ => Archi.ptr64 = false
  | .Xany64, .Vint _ => True
  | .Xany64, .Vlong _ => True
  | .Xany64, .Vptr _ _ => True
  | .Xany64, .Vsingle _ => True
  | .Xany64, .Vfloat _ => True
  | .Xvoid, _ => True
  | _, _ => False

/-- `Values.has_argtype_list` (`list_forall2 has_argtype`). -/
def HasArgtypeList : List Val → List XType → Prop
  | [], [] => True
  | v :: vs, t :: ts => HasArgtype v t ∧ HasArgtypeList vs ts
  | _, _ => False

/-- `Values.bool_of_val`: non-zero integers are true, zero is false; other
    values are neither. -/
inductive BoolOfVal : Val → Bool → Prop where
  | int (n : Integers.Int) : BoolOfVal (.Vint n) (!Integers.Int.eq n Integers.Int.zero)

/-! ## Arithmetic -/

/-- `Values.maketotal` -/
def maketotal (ov : Option Val) : Val :=
  match ov with
  | some v => v
  | none => .Vundef

def intofsingle (v : Val) : Option Val :=
  match v with | .Vsingle f => (Floats.Float32.toInt f).map .Vint | _ => none
def intuofsingle (v : Val) : Option Val :=
  match v with | .Vsingle f => (Floats.Float32.toIntu f).map .Vint | _ => none
def singleofint (v : Val) : Option Val :=
  match v with | .Vint n => some (.Vsingle (Floats.Float32.ofInt n)) | _ => none
def singleofintu (v : Val) : Option Val :=
  match v with | .Vint n => some (.Vsingle (Floats.Float32.ofIntu n)) | _ => none

def negint (v : Val) : Val :=
  match v with | .Vint n => .Vint (Integers.Int.neg n) | _ => .Vundef

def mulhs (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.mulhs n1 n2)
  | _, _ => .Vundef

def mulhu (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.mulhu n1 n2)
  | _, _ => .Vundef

def add_carry (v1 v2 cin : Val) : Val :=
  match v1, v2, cin with
  | .Vint n1, .Vint n2, .Vint c => .Vint (Integers.Int.add_carry n1 n2 c)
  | _, _, _ => .Vundef

def sub_overflow (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.sub_overflow n1 n2 Integers.Int.zero)
  | _, _ => .Vundef

def negative (v : Val) : Val :=
  match v with | .Vint n => .Vint (Integers.Int.negative n) | _ => .Vundef

def shr_carry (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.ltu n2 Integers.Int.iwordsize then .Vint (Integers.Int.shr_carry n1 n2) else .Vundef
  | _, _ => .Vundef

/-- `Values.shrx`: signed division by `2^n`, rounding towards zero. -/
def shrx (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.ltu n2 (Integers.Int.repr 31) then some (.Vint (Integers.Int.shrx n1 n2)) else none
  | _, _ => none

def rol (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.rol n1 n2)
  | _, _ => .Vundef

def rolm (v : Val) (amount mask : Integers.Int) : Val :=
  match v with | .Vint n => .Vint (Integers.Int.rolm n amount mask) | _ => .Vundef

def ror (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.ror n1 n2)
  | _, _ => .Vundef

def floatofwords (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vfloat (Floats.Float.fromWords n1 n2)
  | _, _ => .Vundef

def longofsingle (v : Val) : Option Val :=
  match v with | .Vsingle f => (Floats.Float32.toLong f).map .Vlong | _ => none
def longuofsingle (v : Val) : Option Val :=
  match v with | .Vsingle f => (Floats.Float32.toLongu f).map .Vlong | _ => none
def singleoflong (v : Val) : Option Val :=
  match v with | .Vlong n => some (.Vsingle (Floats.Float32.ofLong n)) | _ => none
def singleoflongu (v : Val) : Option Val :=
  match v with | .Vlong n => some (.Vsingle (Floats.Float32.ofLongu n)) | _ => none

def mullhs (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.mulhs n1 n2)
  | _, _ => .Vundef

def mullhu (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.mulhu n1 n2)
  | _, _ => .Vundef

def addl_carry (v1 v2 cin : Val) : Val :=
  match v1, v2, cin with
  | .Vlong n1, .Vlong n2, .Vlong c => .Vlong (Integers.Int64.add_carry n1 n2 c)
  | _, _, _ => .Vundef

def subl_overflow (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      .Vint (Integers.Int.repr (Integers.Int64.unsigned (Integers.Int64.sub_overflow n1 n2 Integers.Int64.zero)))
  | _, _ => .Vundef

def negativel (v : Val) : Val :=
  match v with
  | .Vlong n => .Vint (Integers.Int.repr (Integers.Int64.unsigned (Integers.Int64.negative n)))
  | _ => .Vundef

def shrxl (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if Integers.Int.ltu n2 (Integers.Int.repr 63) then some (.Vlong (Integers.Int64.shrx' n1 n2)) else none
  | _, _ => none

def shrl_carry (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if Integers.Int.ltu n2 Integers.Int64.iwordsize' then .Vlong (Integers.Int64.shr_carry' n1 n2) else .Vundef
  | _, _ => .Vundef

def roll (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 => .Vlong (Integers.Int64.rol n1 (Integers.Int64.repr (Integers.Int.unsigned n2)))
  | _, _ => .Vundef

def rorl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 => .Vlong (Integers.Int64.ror n1 (Integers.Int64.repr (Integers.Int.unsigned n2)))
  | _, _ => .Vundef

def rolml (v : Val) (amount : Integers.Int) (mask : Integers.Int64) : Val :=
  match v with
  | .Vlong n => .Vlong (Integers.Int64.rolm n (Integers.Int64.repr (Integers.Int.unsigned amount)) mask)
  | _ => .Vundef

def zero_ext_l (nbits : Nat) (v : Val) : Val :=
  match v with | .Vlong n => .Vlong (Integers.Int64.zero_ext nbits n) | _ => .Vundef

def sign_ext_l (nbits : Nat) (v : Val) : Val :=
  match v with | .Vlong n => .Vlong (Integers.Int64.sign_ext nbits n) | _ => .Vundef

/-! ## Comparisons -/

/-- `Values.cmpu` -/
def cmpu (validPtr : Block → Z → Bool) (c : Comparison) (v1 v2 : Val) : Val :=
  ofOptbool (cmpu_bool validPtr c v1 v2)

/-- `Values.cmplu` (partial, like `Values.cmpl`). -/
def cmplu (validPtr : Block → Z → Bool) (c : Comparison) (v1 v2 : Val) : Option Val :=
  (cmplu_bool validPtr c v1 v2).map ofBool

/-- `Values.maskzero_bool` -/
def maskzero_bool (v : Val) (mask : Integers.Int) : Option Bool :=
  match v with
  | .Vint n => some (Integers.Int.eq (Integers.Int.and n mask) Integers.Int.zero)
  | _ => none

/-- `Values.select`: choose between two values according to a comparison
    result, normalizing to the given type. -/
def select (cmp : Option Bool) (v1 v2 : Val) (ty : ATyp) : Val :=
  match cmp with
  | some b => normalize (if b then v1 else v2) ty
  | none => .Vundef

end Val
end CC
