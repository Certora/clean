/-
  The remaining parts of `cfrontend/Cop.v`:

  * the trivial injection facts `val_inject_vtrue`/`vfalse`/`of_bool`/`vptrofs`;
  * `cast_bool_bool_val` (casting to `_Bool` is `bool_val`);
  * `val_casted_has_argtype`;
  * section `ArithConv`: the ISO C99 integer promotions and usual arithmetic
    conversions (§6.3.1.1, §6.3.1.8), stated independently of CompCert's
    classification functions, with the two theorems relating them to
    `typeconv` and `classify_binarith`.
-/
import CCLib.cfrontend.CopTheory
import CCLib.cfrontend.CopInject
import CCLib.common.ValuesOps

namespace CC
namespace Cop

/-! ## Injections of Boolean values -/

/-- `Cop.val_inject_vtrue` -/
theorem val_inject_vtrue (f : Val.Meminj) : Val.Inject f Val.Vtrue Val.Vtrue := .int _

/-- `Cop.val_inject_vfalse` -/
theorem val_inject_vfalse (f : Val.Meminj) : Val.Inject f Val.Vfalse Val.Vfalse := .int _

/-- `Cop.val_inject_of_bool` -/
theorem val_inject_of_bool (f : Val.Meminj) (b : Bool) :
    Val.Inject f (Val.ofBool b) (Val.ofBool b) := by
  cases b
  · exact val_inject_vfalse f
  · exact val_inject_vtrue f

/-- `Cop.val_inject_vptrofs` -/
theorem val_inject_vptrofs (f : Val.Meminj) (n : Integers.Ptrofs) :
    Val.Inject f (Val.Vptrofs n) (Val.Vptrofs n) := vptrofs_inject n

/-! ## Casting to `_Bool` -/

/-- `Cop.cast_bool_bool_val`: casting to `_Bool` computes `bool_val`. -/
theorem cast_bool_bool_val (v : Val) (t : Ty) (m : Mem) :
    semCast v t (.Tint .IBool .Signed noattr) m = (boolVal v t m).map Val.ofBool := by
  rcases t with _ | ⟨sz, si, a⟩ | ⟨si, a⟩ | ⟨_ | _, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;> (try cases sz) <;> cases v <;>
    simp [semCast, classifyCast, boolVal, classifyBool, typeconv, removeAttributes, tattr, tint,
      Archi.ptr64, Val.ofBool, Val.Vtrue, Val.Vfalse, Val.Vone] <;>
    (split <;> simp_all)

/-- `Cop.val_casted_has_argtype`: casted values belong to the machine argument
    type of their C type. -/
theorem val_casted_has_argtype {v : Val} {ty : Ty} (h : ValCasted v ty) :
    Val.HasArgtype v (argtypeOfType ty) := by
  cases h with
  | @int sz si attr n hn =>
    cases sz <;> cases si <;> simp only [argtypeOfType, Val.HasArgtype] <;>
      simp only [castIntInt] at hn <;>
      first
        | exact hn.symm
        | trivial
        | (split at hn
           · exact Or.inl hn.symm
           · exact Or.inr hn.symm)
  | _ => simp_all [argtypeOfType, Val.HasArgtype, Archi.ptr64]

/-! ## ISO C arithmetic conversions (section `ArithConv`) -/

/-- `Cop.int_type`: the ISO C integer types.  `_Bool` is spelled `Bool_`. -/
inductive IntType where
  | Bool_
  | Char | SChar | UChar
  | Short | UShort
  | Int | UInt
  | Long | ULong
  | Longlong | ULonglong
  deriving DecidableEq, Repr, Inhabited

/-- `Cop.arith_type`: the ISO C arithmetic types. -/
inductive ArithType where
  | I (it : IntType)
  | Float
  | Double
  | Longdouble
  deriving DecidableEq, Repr, Inhabited

/-- `Cop.is_unsigned` (plain `char` is signed, as in most of CompCert's ABIs). -/
def isUnsigned : IntType → Bool
  | .Bool_ => true
  | .Char => false
  | .SChar => false
  | .UChar => true
  | .Short => false
  | .UShort => true
  | .Int => false
  | .UInt => true
  | .Long => false
  | .ULong => true
  | .Longlong => false
  | .ULonglong => true

/-- `Cop.unsigned_type` -/
def unsignedType : IntType → IntType
  | .Char => .UChar
  | .SChar => .UChar
  | .Short => .UShort
  | .Int => .UInt
  | .Long => .ULong
  | .Longlong => .ULonglong
  | t => t

/-- `Cop.int_sizeof` -/
def intSizeof : IntType → _root_.Int
  | .Bool_ | .Char | .SChar | .UChar => 1
  | .Short | .UShort => 2
  | .Int | .UInt | .Long | .ULong => 4
  | .Longlong | .ULonglong => 8

/-- `Cop.rank`: integer conversion rank (§6.3.1.1 para 1). -/
def rank : IntType → _root_.Int
  | .Bool_ => 1
  | .Char | .SChar | .UChar => 2
  | .Short | .UShort => 3
  | .Int | .UInt => 4
  | .Long | .ULong => 5
  | .Longlong | .ULonglong => 6

/-- `Cop.integer_promotion` (§6.3.1.1 para 2). -/
def integerPromotion (t : IntType) : IntType :=
  if rank t < rank .Int then .Int else t

/-- `Cop.usual_arithmetic_conversion` (§6.3.1.8): the type both operands are
    converted to. -/
def usualArithmeticConversion (t1 t2 : ArithType) : ArithType :=
  match t1, t2 with
  | .Longdouble, _ | _, .Longdouble => .Longdouble
  | .Double, _ | _, .Double => .Double
  | .Float, _ | _, .Float => .Float
  | .I i1, .I i2 =>
      let j1 := integerPromotion i1
      let j2 := integerPromotion i2
      if j1 = j2 then .I j1 else
      match isUnsigned j1, isUnsigned j2 with
      | true, true | false, false =>
          if rank j1 < rank j2 then .I j2 else .I j1
      | true, false =>
          if rank j2 ≤ rank j1 then .I j1 else
          if intSizeof j1 < intSizeof j2 then .I j2 else
          .I (unsignedType j2)
      | false, true =>
          if rank j1 ≤ rank j2 then .I j2 else
          if intSizeof j2 < intSizeof j1 then .I j1 else
          .I (unsignedType j1)

/-- `Cop.proj_type`: CompCert's representation of an ISO arithmetic type on
    the target (`long` is 32 bits, `long double` is `double`). -/
def projType : ArithType → Ty
  | .I .Bool_ => .Tint .IBool .Unsigned noattr
  | .I .Char => .Tint .I8 .Unsigned noattr
  | .I .SChar => .Tint .I8 .Signed noattr
  | .I .UChar => .Tint .I8 .Unsigned noattr
  | .I .Short => .Tint .I16 .Signed noattr
  | .I .UShort => .Tint .I16 .Unsigned noattr
  | .I .Int => .Tint .I32 .Signed noattr
  | .I .UInt => .Tint .I32 .Unsigned noattr
  | .I .Long => .Tint .I32 .Signed noattr
  | .I .ULong => .Tint .I32 .Unsigned noattr
  | .I .Longlong => .Tlong .Signed noattr
  | .I .ULonglong => .Tlong .Unsigned noattr
  | .Float => .Tfloat .F32 noattr
  | .Double => .Tfloat .F64 noattr
  | .Longdouble => .Tfloat .F64 noattr

/-- `Cop.typeconv_integer_promotion` -/
theorem typeconv_integer_promotion (i : IntType) :
    typeconv (projType (.I i)) = projType (.I (integerPromotion i)) := by
  cases i <;> rfl

/-- `Cop.classify_binarith_arithmetic_conversion`: CompCert's
    `classify_binarith` implements the usual arithmetic conversions. -/
theorem classify_binarith_arithmetic_conversion (t1 t2 : ArithType) :
    binarithType (classifyBinarith (projType t1) (projType t2)) =
      projType (usualArithmeticConversion t1 t2) := by
  rcases t1 with i1 | _ | _ | _ <;> rcases t2 with i2 | _ | _ | _ <;>
    (try cases i1) <;> (try cases i2) <;> rfl

end Cop
end CC
