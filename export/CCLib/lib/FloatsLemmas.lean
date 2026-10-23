/-
  Theorems of `lib/Floats.v` about the exact float operations of
  `CCLib.lib.Floats`.
-/
import CCLib.lib.Floats
import CCLib.lib.FloatModelLemmas
import CCLib.lib.IntegersInt
import CCLib.lib.IntegersInt64

namespace CC
namespace Floats

open FloatModel FloatModel.UnpackedFloat

/-! ## `cmp_of_comparison` -/

theorem cmpOfComparison_swap (c : Comparison) (x : Option Ordering) :
    cmpOfComparison c.swap x = cmpOfComparison c (x.map Ordering.swap) := by
  cases c <;> rcases x with _ | ⟨_ | _ | _⟩ <;> rfl

theorem cmpOfComparison_ne_eq (x : Option Ordering) :
    cmpOfComparison .Cne x = !cmpOfComparison .Ceq x := by
  rcases x with _ | ⟨_ | _ | _⟩ <;> rfl

theorem cmpOfComparison_lt_eq_false (x : Option Ordering) :
    cmpOfComparison .Clt x = true → cmpOfComparison .Ceq x = true → False := by
  rcases x with _ | ⟨_ | _ | _⟩ <;> simp [cmpOfComparison]

theorem cmpOfComparison_le_lt_eq (x : Option Ordering) :
    cmpOfComparison .Cle x = (cmpOfComparison .Clt x || cmpOfComparison .Ceq x) := by
  rcases x with _ | ⟨_ | _ | _⟩ <;> rfl

theorem cmpOfComparison_gt_eq_false (x : Option Ordering) :
    cmpOfComparison .Cgt x = true → cmpOfComparison .Ceq x = true → False := by
  rcases x with _ | ⟨_ | _ | _⟩ <;> simp [cmpOfComparison]

theorem cmpOfComparison_ge_gt_eq (x : Option Ordering) :
    cmpOfComparison .Cge x = (cmpOfComparison .Cgt x || cmpOfComparison .Ceq x) := by
  rcases x with _ | ⟨_ | _ | _⟩ <;> rfl

theorem cmpOfComparison_lt_gt_false (x : Option Ordering) :
    cmpOfComparison .Clt x = true → cmpOfComparison .Cgt x = true → False := by
  rcases x with _ | ⟨_ | _ | _⟩ <;> simp [cmpOfComparison]

/-! ## Facts about the model operations -/

namespace Model

theorem sign_compare_swap (s₁ s₂ : Sign) : compare s₂ s₁ = (compare s₁ s₂).swap := by
  cases s₁ <;> cases s₂ <;> rfl

theorem then_swap (e₁ e₂ : Int) (m₁ m₂ : Nat) :
    (compare e₂ e₁).then (compare m₂ m₁) = ((compare e₁ e₂).then (compare m₁ m₂)).swap := by
  rw [Ordering.swap_then, ← Std.OrientedOrd.eq_swap, ← Std.OrientedOrd.eq_swap]

theorem compare_finite_swap (s₁ : Sign) (m₁ : Nat) (e₁ : Int) (h₁ : 0 < m₁)
    (s₂ : Sign) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) :
    UnpackedFloat.compare (.finite s₂ m₂ e₂ h₂) (.finite s₁ m₁ e₁ h₁) =
      (UnpackedFloat.compare (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂)).map Ordering.swap := by
  cases s₁ <;> cases s₂ <;> simp only [UnpackedFloat.compare, Option.map_some] <;>
    (try rw [then_swap e₁ e₂ m₁ m₂]) <;> simp <;> rfl

/-- `Bcompare_swap` -/
theorem compare_swap (a b : UnpackedFloat) :
    UnpackedFloat.compare b a = (UnpackedFloat.compare a b).map Ordering.swap := by
  rcases a with s₁ | _ | s₁ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with s₂ | _ | s₂ | ⟨s₂, m₂, e₂, h₂⟩
  all_goals first
    | exact compare_finite_swap _ _ _ _ _ _ _ _
    | ((try cases s₁) <;> (try cases s₂) <;> rfl)

theorem sign_mul_comm (s₁ s₂ : Sign) : s₁ * s₂ = s₂ * s₁ := by
  cases s₁ <;> cases s₂ <;> rfl

/-- `Bplus` is commutative (on the model, which has no NaN payloads). -/
theorem add_comm (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.add spec a b = UnpackedFloat.add spec b a := by
  rcases a with s₁ | _ | s₁ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with s₂ | _ | s₂ | ⟨s₂, m₂, e₂, h₂⟩ <;>
  (try cases s₁) <;> (try cases s₂) <;>
  simp [UnpackedFloat.add, Int.min_comm, Int.add_comm]

/-- `Bmult` is commutative (on the model). -/
theorem mul_comm (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.mul spec a b = UnpackedFloat.mul spec b a := by
  rcases a with s₁ | _ | s₁ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with s₂ | _ | s₂ | ⟨s₂, m₂, e₂, h₂⟩ <;>
  simp [UnpackedFloat.mul, sign_mul_comm, Nat.mul_comm, Int.add_comm]

end Model

/-! ## Format-generic theorems

Proved once for any IEEE format and NaN configuration, then restated for
`Float` and `Float32` under CompCert's names below. -/

namespace Gen

variable {spec : Format}

/-! ### `ZofB_range` -/

theorem toZRange_eq_some {b : BitVec spec.numBits} {lo hi z : Int} :
    toZRange spec b lo hi = some z ↔ toZ spec b = some z ∧ lo ≤ z ∧ z ≤ hi := by
  simp [toZRange, Option.filter_eq_some_iff]

theorem toZRange_widen {b : BitVec spec.numBits} {lo hi lo' hi' z : Int}
    (h : toZRange spec b lo hi = some z) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    toZRange spec b lo' hi' = some z := by
  rw [toZRange_eq_some] at *
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, Int.le_trans hlo h2, Int.le_trans h3 hhi⟩

/-- Generic `to_int_to_long`. -/
theorem to_int_to_long (b : BitVec spec.numBits) (n : Integers.Int)
    (h : (toZRange spec b Integers.Int.min_signed Integers.Int.max_signed).map
      Integers.Int.repr = some n) :
    (toZRange spec b Integers.Int64.min_signed Integers.Int64.max_signed).map
      Integers.Int64.repr = some (Integers.Int64.repr (Integers.Int.signed n)) := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  have hz' := toZRange_eq_some.mp hz
  rw [toZRange_widen hz (by decide) (by decide)]
  simp [Integers.Int.signed_repr hz'.2.1 hz'.2.2]

/-- Generic `to_intu_to_longu`. -/
theorem to_intu_to_longu (b : BitVec spec.numBits) (n : Integers.Int)
    (h : (toZRange spec b 0 Integers.Int.max_unsigned).map Integers.Int.repr = some n) :
    (toZRange spec b 0 Integers.Int64.max_unsigned).map Integers.Int64.repr =
      some (Integers.Int64.repr (Integers.Int.unsigned n)) := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  have hz' := toZRange_eq_some.mp hz
  rw [toZRange_widen hz (Int.le_refl _) (by decide)]
  simp [Integers.Int.unsigned_repr hz'.2.1 hz'.2.2]

/-- Generic `to_intu_to_long`. -/
theorem to_intu_to_long (b : BitVec spec.numBits) (n : Integers.Int)
    (h : (toZRange spec b 0 Integers.Int.max_unsigned).map Integers.Int.repr = some n) :
    (toZRange spec b Integers.Int64.min_signed Integers.Int64.max_signed).map
      Integers.Int64.repr = some (Integers.Int64.repr (Integers.Int.unsigned n)) := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  have hz' := toZRange_eq_some.mp hz
  rw [toZRange_widen hz (by decide) (by decide)]
  simp [Integers.Int.unsigned_repr hz'.2.1 hz'.2.2]

/-! ### Comparisons -/

theorem cmp_swap (c : Comparison) (x y : BitVec spec.numBits) :
    cmp spec c.swap x y = cmp spec c y x := by
  simp only [cmp, compare]
  rw [cmpOfComparison_swap, ← Model.compare_swap]

/-! ### Commutativity -/

theorem consPl_of_not_nan {x : BitVec spec.numBits} (h : isNan spec x = false)
    (l : List (Bool × Nat)) : consPl spec x l = l := by
  simp [consPl, h]

theorem binopNan_comm (nc : NanConfig spec) (x y : BitVec spec.numBits)
    (h : isNan spec x = false ∨ isNan spec y = false) :
    binopNan nc x y = binopNan nc y x := by
  unfold binopNan
  rcases h with h | h <;> simp only [consPl_of_not_nan h]

theorem add_commut (nc : NanConfig spec) (x y : BitVec spec.numBits)
    (h : isNan spec x = false ∨ isNan spec y = false) : add nc x y = add nc y x := by
  unfold add; rw [Model.add_comm, binopNan_comm nc x y h]

theorem mul_commut (nc : NanConfig spec) (x y : BitVec spec.numBits)
    (h : isNan spec x = false ∨ isNan spec y = false) : mul nc x y = mul nc y x := by
  unfold mul; rw [Model.mul_comm, binopNan_comm nc x y h]

/-! ### Sign operations -/

@[simp] theorem neg_neg (b : BitVec spec.numBits) : neg spec (neg spec b) = b := by
  simp [neg, BitVec.xor_assoc]

@[simp] theorem abs_abs (b : BitVec spec.numBits) : abs spec (abs spec b) = abs spec b := by
  simp [abs, BitVec.and_assoc]

@[simp] theorem abs_neg (b : BitVec spec.numBits) : abs spec (neg spec b) = abs spec b := by
  ext i hi
  simp only [abs, neg, signBit, BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not,
    BitVec.getElem_twoPow]
  by_cases h : i = spec.numBits - 1 <;> simp [h]

end Gen

/-! ## Integer range facts used by the `of_*` conversion lemmas -/

theorem signed_int_long (n : Integers.Int) :
    Integers.Int64.signed (Integers.Int64.repr (Integers.Int.signed n)) =
      Integers.Int.signed n := by
  have := Integers.Int.signed_range n
  exact Integers.Int64.signed_repr (Int.le_trans (by decide) this.1)
    (Int.le_trans this.2 (by decide))

theorem unsigned_intu_longu (n : Integers.Int) :
    Integers.Int64.unsigned (Integers.Int64.repr (Integers.Int.unsigned n)) =
      Integers.Int.unsigned n := by
  have := Integers.Int.unsigned_range_2 n
  exact Integers.Int64.unsigned_repr this.1 (Int.le_trans this.2 (by decide))

theorem signed_intu_long (n : Integers.Int) :
    Integers.Int64.signed (Integers.Int64.repr (Integers.Int.unsigned n)) =
      Integers.Int.unsigned n := by
  have := Integers.Int.unsigned_range_2 n
  exact Integers.Int64.signed_repr (Int.le_trans (by decide) this.1)
    (Int.le_trans this.2 (by decide))

theorem unsigned_eq_signed_int (x : Integers.Int)
    (h : Integers.Int.ltu x (Integers.Int.repr Integers.Int.half_modulus) = true) :
    Integers.Int.unsigned x = Integers.Int.signed x := by
  rw [Integers.Int.ltu_iff] at h
  have e : Integers.Int.unsigned (Integers.Int.repr Integers.Int.half_modulus) = 2147483648 := by
    decide
  have hm : Integers.Int.max_signed = 2147483647 := by decide
  rw [Integers.Int.signed_eq_unsigned x (by
    rw [e] at h; rw [hm]; exact Int.le_of_lt_add_one h)]

theorem unsigned_eq_signed_long (x : Integers.Int64)
    (h : Integers.Int64.ltu x (Integers.Int64.repr Integers.Int64.half_modulus) = true) :
    Integers.Int64.unsigned x = Integers.Int64.signed x := by
  rw [Integers.Int64.ltu_iff] at h
  have e : Integers.Int64.unsigned (Integers.Int64.repr Integers.Int64.half_modulus) =
      9223372036854775808 := by
    decide
  have hm : Integers.Int64.max_signed = 9223372036854775807 := by decide
  rw [Integers.Int64.signed_eq_unsigned x (by
    rw [e] at h; rw [hm]; exact Int.le_of_lt_add_one h)]

namespace Float

/-! ## Comparisons (`Floats.v`, module `Float`) -/

/-- `Float.cmp_swap` -/
theorem cmp_swap (c : Comparison) (x y : Float) : cmp c.swap x y = cmp c y x :=
  Gen.cmp_swap (spec := Format.binary64) c x.bits y.bits
/-- `Float.cmp_ne_eq` -/
theorem cmp_ne_eq (f1 f2 : Float) : cmp .Cne f1 f2 = !cmp .Ceq f1 f2 :=
  cmpOfComparison_ne_eq _
/-- `Float.cmp_lt_eq_false` -/
theorem cmp_lt_eq_false (f1 f2 : Float) :
    cmp .Clt f1 f2 = true → cmp .Ceq f1 f2 = true → False :=
  cmpOfComparison_lt_eq_false _
/-- `Float.cmp_le_lt_eq` -/
theorem cmp_le_lt_eq (f1 f2 : Float) :
    cmp .Cle f1 f2 = (cmp .Clt f1 f2 || cmp .Ceq f1 f2) :=
  cmpOfComparison_le_lt_eq _
/-- `Float.cmp_gt_eq_false` -/
theorem cmp_gt_eq_false (f1 f2 : Float) :
    cmp .Cgt f1 f2 = true → cmp .Ceq f1 f2 = true → False :=
  cmpOfComparison_gt_eq_false _
/-- `Float.cmp_ge_gt_eq` -/
theorem cmp_ge_gt_eq (f1 f2 : Float) :
    cmp .Cge f1 f2 = (cmp .Cgt f1 f2 || cmp .Ceq f1 f2) :=
  cmpOfComparison_ge_gt_eq _
/-- `Float.cmp_lt_gt_false` -/
theorem cmp_lt_gt_false (f1 f2 : Float) :
    cmp .Clt f1 f2 = true → cmp .Cgt f1 f2 = true → False :=
  cmpOfComparison_lt_gt_false _

/-! ## Bits -/

/-- `Float.of_to_bits` -/
@[simp] theorem of_to_bits (f : Float) : ofBits (toBits f) = f := rfl
/-- `Float.to_of_bits` -/
@[simp] theorem to_of_bits (b : Integers.Int64) : toBits (ofBits b) = b := rfl

/-! ## Commutativity -/

theorem consPl_of_not_nan {x : Float} (h : x.isNaN = false) (l : List (Bool × Nat)) :
    consPl x l = l :=
  Gen.consPl_of_not_nan (spec := Format.binary64) h l

theorem binopNan_comm (x y : Float) (h : x.isNaN = false ∨ y.isNaN = false) :
    binopNan x y = binopNan y x :=
  congrArg mk (Gen.binopNan_comm nanConfig x.bits y.bits h)

/-- `Float.add_commut` -/
theorem add_commut (x y : Float) (h : x.isNaN = false ∨ y.isNaN = false) :
    add x y = add y x :=
  congrArg mk (Gen.add_commut nanConfig x.bits y.bits h)

/-- `Float.mul_commut` -/
theorem mul_commut (x y : Float) (h : x.isNaN = false ∨ y.isNaN = false) :
    mul x y = mul y x :=
  congrArg mk (Gen.mul_commut nanConfig x.bits y.bits h)

/-! ## Conversions between integer types -/

/-- `Float.to_int_to_long` -/
theorem to_int_to_long (f : Float) (n : Integers.Int) (h : toInt f = some n) :
    toLong f = some (Integers.Int64.repr (Integers.Int.signed n)) :=
  Gen.to_int_to_long (spec := Format.binary64) f.bits n h
/-- `Float.to_intu_to_longu` -/
theorem to_intu_to_longu (f : Float) (n : Integers.Int) (h : toIntu f = some n) :
    toLongu f = some (Integers.Int64.repr (Integers.Int.unsigned n)) :=
  Gen.to_intu_to_longu (spec := Format.binary64) f.bits n h
/-- `Float.to_intu_to_long` -/
theorem to_intu_to_long (f : Float) (n : Integers.Int) (h : toIntu f = some n) :
    toLong f = some (Integers.Int64.repr (Integers.Int.unsigned n)) :=
  Gen.to_intu_to_long (spec := Format.binary64) f.bits n h

/-- `Float.of_int_of_long` -/
theorem of_int_of_long (n : Integers.Int) :
    ofInt n = ofLong (Integers.Int64.repr (Integers.Int.signed n)) := by
  simp only [ofInt, ofLong, signed_int_long]
/-- `Float.of_intu_of_longu` -/
theorem of_intu_of_longu (n : Integers.Int) :
    ofIntu n = ofLongu (Integers.Int64.repr (Integers.Int.unsigned n)) := by
  simp only [ofIntu, ofLongu, unsigned_intu_longu]
/-- `Float.of_intu_of_long` -/
theorem of_intu_of_long (n : Integers.Int) :
    ofIntu n = ofLong (Integers.Int64.repr (Integers.Int.unsigned n)) := by
  simp only [ofIntu, ofLong, signed_intu_long]
/-- `Float.of_intu_of_int_1` -/
theorem of_intu_of_int_1 (x : Integers.Int)
    (h : Integers.Int.ltu x (Integers.Int.repr Integers.Int.half_modulus) = true) :
    ofIntu x = ofInt x := by
  simp only [ofIntu, ofInt, unsigned_eq_signed_int x h]
/-- `Float.of_longu_of_long_1` -/
theorem of_longu_of_long_1 (x : Integers.Int64)
    (h : Integers.Int64.ltu x (Integers.Int64.repr Integers.Int64.half_modulus) = true) :
    ofLongu x = ofLong x := by
  simp only [ofLongu, ofLong, unsigned_eq_signed_long x h]

/-! ## Sign operations -/

@[simp] theorem neg_neg (f : Float) : neg (neg f) = f := congrArg mk (Gen.neg_neg (spec := Format.binary64) f.bits)
@[simp] theorem abs_neg (f : Float) : abs (neg f) = abs f := congrArg mk (Gen.abs_neg (spec := Format.binary64) f.bits)
@[simp] theorem abs_abs (f : Float) : abs (abs f) = abs f := congrArg mk (Gen.abs_abs (spec := Format.binary64) f.bits)

end Float

namespace Float32

/-! ## Comparisons (`Floats.v`, module `Float32`) -/

/-- `Float32.cmp_swap` -/
theorem cmp_swap (c : Comparison) (x y : Float32) : cmp c.swap x y = cmp c y x :=
  Gen.cmp_swap (spec := Format.binary32) c x.bits y.bits
/-- `Float32.cmp_ne_eq` -/
theorem cmp_ne_eq (f1 f2 : Float32) : cmp .Cne f1 f2 = !cmp .Ceq f1 f2 :=
  cmpOfComparison_ne_eq _
/-- `Float32.cmp_lt_eq_false` -/
theorem cmp_lt_eq_false (f1 f2 : Float32) :
    cmp .Clt f1 f2 = true → cmp .Ceq f1 f2 = true → False :=
  cmpOfComparison_lt_eq_false _
/-- `Float32.cmp_le_lt_eq` -/
theorem cmp_le_lt_eq (f1 f2 : Float32) :
    cmp .Cle f1 f2 = (cmp .Clt f1 f2 || cmp .Ceq f1 f2) :=
  cmpOfComparison_le_lt_eq _
/-- `Float32.cmp_gt_eq_false` -/
theorem cmp_gt_eq_false (f1 f2 : Float32) :
    cmp .Cgt f1 f2 = true → cmp .Ceq f1 f2 = true → False :=
  cmpOfComparison_gt_eq_false _
/-- `Float32.cmp_ge_gt_eq` -/
theorem cmp_ge_gt_eq (f1 f2 : Float32) :
    cmp .Cge f1 f2 = (cmp .Cgt f1 f2 || cmp .Ceq f1 f2) :=
  cmpOfComparison_ge_gt_eq _
/-- `Float32.cmp_lt_gt_false` -/
theorem cmp_lt_gt_false (f1 f2 : Float32) :
    cmp .Clt f1 f2 = true → cmp .Cgt f1 f2 = true → False :=
  cmpOfComparison_lt_gt_false _

/-! ## Bits -/

/-- `Float32.of_to_bits` -/
@[simp] theorem of_to_bits (f : Float32) : ofBits (toBits f) = f := rfl
/-- `Float32.to_of_bits` -/
@[simp] theorem to_of_bits (b : Integers.Int) : toBits (ofBits b) = b := rfl

/-! ## Commutativity -/

theorem consPl_of_not_nan {x : Float32} (h : x.isNaN = false) (l : List (Bool × Nat)) :
    consPl x l = l :=
  Gen.consPl_of_not_nan (spec := Format.binary32) h l

theorem binopNan_comm (x y : Float32) (h : x.isNaN = false ∨ y.isNaN = false) :
    binopNan x y = binopNan y x :=
  congrArg mk (Gen.binopNan_comm nanConfig x.bits y.bits h)

/-- `Float32.add_commut` -/
theorem add_commut (x y : Float32) (h : x.isNaN = false ∨ y.isNaN = false) :
    add x y = add y x :=
  congrArg mk (Gen.add_commut nanConfig x.bits y.bits h)

/-- `Float32.mul_commut` -/
theorem mul_commut (x y : Float32) (h : x.isNaN = false ∨ y.isNaN = false) :
    mul x y = mul y x :=
  congrArg mk (Gen.mul_commut nanConfig x.bits y.bits h)

/-! ## Conversions between integer types -/

/-- `Float32.to_int_to_long` -/
theorem to_int_to_long (f : Float32) (n : Integers.Int) (h : toInt f = some n) :
    toLong f = some (Integers.Int64.repr (Integers.Int.signed n)) :=
  Gen.to_int_to_long (spec := Format.binary32) f.bits n h
/-- `Float32.to_intu_to_longu` -/
theorem to_intu_to_longu (f : Float32) (n : Integers.Int) (h : toIntu f = some n) :
    toLongu f = some (Integers.Int64.repr (Integers.Int.unsigned n)) :=
  Gen.to_intu_to_longu (spec := Format.binary32) f.bits n h
/-- `Float32.to_intu_to_long` -/
theorem to_intu_to_long (f : Float32) (n : Integers.Int) (h : toIntu f = some n) :
    toLong f = some (Integers.Int64.repr (Integers.Int.unsigned n)) :=
  Gen.to_intu_to_long (spec := Format.binary32) f.bits n h

/-- `Float32.of_int_of_long` -/
theorem of_int_of_long (n : Integers.Int) :
    ofInt n = ofLong (Integers.Int64.repr (Integers.Int.signed n)) := by
  simp only [ofInt, ofLong, signed_int_long]
/-- `Float32.of_intu_of_longu` -/
theorem of_intu_of_longu (n : Integers.Int) :
    ofIntu n = ofLongu (Integers.Int64.repr (Integers.Int.unsigned n)) := by
  simp only [ofIntu, ofLongu, unsigned_intu_longu]
/-- `Float32.of_intu_of_long` -/
theorem of_intu_of_long (n : Integers.Int) :
    ofIntu n = ofLong (Integers.Int64.repr (Integers.Int.unsigned n)) := by
  simp only [ofIntu, ofLong, signed_intu_long]
/-- `Float32.of_intu_of_int_1` -/
theorem of_intu_of_int_1 (x : Integers.Int)
    (h : Integers.Int.ltu x (Integers.Int.repr Integers.Int.half_modulus) = true) :
    ofIntu x = ofInt x := by
  simp only [ofIntu, ofInt, unsigned_eq_signed_int x h]
/-- `Float32.of_longu_of_long_1` -/
theorem of_longu_of_long_1 (x : Integers.Int64)
    (h : Integers.Int64.ltu x (Integers.Int64.repr Integers.Int64.half_modulus) = true) :
    ofLongu x = ofLong x := by
  simp only [ofLongu, ofLong, unsigned_eq_signed_long x h]

/-! ## Sign operations -/

@[simp] theorem neg_neg (f : Float32) : neg (neg f) = f := congrArg mk (Gen.neg_neg (spec := Format.binary32) f.bits)
@[simp] theorem abs_neg (f : Float32) : abs (neg f) = abs f := congrArg mk (Gen.abs_neg (spec := Format.binary32) f.bits)
@[simp] theorem abs_abs (f : Float32) : abs (abs f) = abs f := congrArg mk (Gen.abs_abs (spec := Format.binary32) f.bits)

end Float32

end Floats
end CC
