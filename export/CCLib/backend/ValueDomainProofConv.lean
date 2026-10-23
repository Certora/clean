/-
  Soundness of the abstract conversion operators of the value analysis
  (`backend/ValueDomain.v`, from `zero_ext_sound` to `hiword_sound`).
  Continues `ValueDomainProofLong.lean`.

  Differences from Rocq: the bit-width argument of `Val.zeroExt` /
  `Val.signExt` is a `Nat` in the port, so the soundness statements use
  `nbits.toNat` for the concrete operation (CompCert's `Z` widths are never
  negative at use sites; for a negative width both sides agree anyway).
-/
import CCLib.backend.ValueDomainProofLong

namespace CC
namespace ValueDomain

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

section
variable {bc : BlockClassification}

/-! ## Zero and sign extension -/

theorem is_uns_zero_ext_toNat (nbits : Z) (i : Integers.Int) :
    IsUns (max 0 nbits) (Integers.Int.zero_ext nbits.toNat i) :=
  is_zero_ext_uns i nbits.toNat _ (.inr (by zomega))

/-- `ValueDomain.zero_ext_sound` -/
theorem zero_ext_sound (nbits : Z) {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.zeroExt nbits.toNat v) (zeroExt nbits x) := by
  cases h <;> simp only [Val.zeroExt, zeroExt] <;>
    first
    | constructor
    | exact vmatch_uns_undef _ _
    | exact vmatch_uns' _ _ _ (is_uns_zero_ext_toNat nbits _)
    | skip
  rename_i p i n hn hu
  apply vmatch_uns'
  intro k h1 h2
  rw [Integers.Int.bits_zero_ext]
  by_cases hk : k < nbits.toNat
  · simp only [hk, decide_true, Bool.true_and]
    exact hu k h1 (by zomega)
  · simp [hk]

theorem sign_ext_nonpos (nbits : Z) (h : nbits ≤ 0) (i : Integers.Int) :
    Integers.Int.sign_ext nbits.toNat i = Integers.Int.zero := by
  have : nbits.toNat = 0 := by zomega
  rw [this]; rfl

/-- `ValueDomain.sign_ext_sound` -/
theorem sign_ext_sound (nbits : Z) {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.signExt nbits.toNat v) (signExt nbits x) := by
  unfold signExt
  split
  · rename_i hle
    cases v <;> simp only [Val.signExt] <;> try exact .Uns_undef _ _
    rw [sign_ext_nonpos nbits hle]
    exact .Uns _ _ _ (by decide) (fun m _ _ => by
      show Integers.Int.testbit Integers.Int.zero m = false
      exact Integers.Int.bits_zero m)
  · rename_i hlt
    have hn : 0 < nbits.toNat := by zomega
    have hz : ((nbits.toNat : Nat) : Z) = nbits := by zomega
    have DFL : ∀ p i, Vmatch bc (.Vint (Integers.Int.sign_ext nbits.toNat i)) (sgn p nbits) := by
      intro p i
      apply vmatch_sgn
      apply is_sign_ext_sgn i _ _ hn (.inr (by zomega))
    cases h <;> simp only [Val.signExt] <;>
      first
      | constructor
      | exact vmatch_sgn_undef _ _
      | exact DFL _ _
      | skip
    · rename_i p i n hn0 hu
      split
      · rename_i hlt2
        exact .Uns _ _ _ hn0 (is_sign_ext_uns i _ _ hn0 (by zomega) hu)
      · exact DFL _ _
    · split
      · exact .Uns_undef _ _
      · exact vmatch_sgn_undef _ _
    · rename_i p i n hn0 hs
      apply vmatch_sgn
      apply is_sign_ext_sgn i _ _ hn
      by_cases hmin : n ≤ nbits
      · rw [Int.min_eq_left hmin]; exact .inl hs
      · rw [Int.min_eq_right (by zomega)]; exact .inr (by zomega)

theorem zero_ext_l_sound (s : Z) {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.zero_ext_l s.toNat v) (zeroExtL s x) := by
  have := unop_long_sound (Integers.Int64.zero_ext s.toNat) h
  cases v <;> exact this

theorem sign_ext_l_sound (s : Z) {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.sign_ext_l s.toNat v) (signExtL s x) := by
  have := unop_long_sound (Integers.Int64.sign_ext s.toNat) h
  cases v <;> exact this

/-! ## Integer and float conversions -/

theorem longofint_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.longofint v) (longofint x) := by
  cases h <;> simp only [Val.longofint, longofint, ntop1] <;> constructor

theorem longofintu_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.longofintu v) (longofintu x) := by
  cases h <;> simp only [Val.longofintu, longofintu, ntop1] <;> constructor

theorem singleoffloat_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.singleoffloat v) (singleoffloat x) := by
  cases h <;> simp only [Val.singleoffloat, singleoffloat, ntop1] <;> constructor

theorem floatofsingle_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.floatofsingle v) (floatofsingle x) := by
  cases h <;> simp only [Val.floatofsingle, floatofsingle, ntop1] <;> constructor

theorem intoffloat_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.intoffloat v = some u) : Vmatch bc u (intoffloat strict x) := by
  cases v <;> simp only [Val.intoffloat, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float.toInt f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [intoffloat, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem intuoffloat_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.intuoffloat v = some u) : Vmatch bc u (intuoffloat strict x) := by
  cases v <;> simp only [Val.intuoffloat, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float.toIntu f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [intuoffloat, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem intofsingle_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.intofsingle v = some u) : Vmatch bc u (intofsingle strict x) := by
  cases v <;> simp only [Val.intofsingle, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float32.toInt f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [intofsingle, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem intuofsingle_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.intuofsingle v = some u) : Vmatch bc u (intuofsingle strict x) := by
  cases v <;> simp only [Val.intuofsingle, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float32.toIntu f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [intuofsingle, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem longoffloat_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.longoffloat v = some u) : Vmatch bc u (longoffloat strict x) := by
  cases v <;> simp only [Val.longoffloat, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float.toLong f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [longoffloat, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem longuoffloat_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.longuoffloat v = some u) : Vmatch bc u (longuoffloat strict x) := by
  cases v <;> simp only [Val.longuoffloat, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float.toLongu f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [longuoffloat, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem longofsingle_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.longofsingle v = some u) : Vmatch bc u (longofsingle strict x) := by
  cases v <;> simp only [Val.longofsingle, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float32.toLong f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [longofsingle, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem longuofsingle_sound (strict : Bool) {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.longuofsingle v = some u) : Vmatch bc u (longuofsingle strict x) := by
  cases v <;> simp only [Val.longuofsingle, reduceCtorEq] at hv
  rename_i f
  cases hf : Floats.Float32.toLongu f <;> simp only [hf, Option.map, reduceCtorEq, Option.some.injEq] at hv
  subst hv
  cases h <;> simp only [longuofsingle, ntop1, hf] <;> first | exact .i _ | exact .l _ | constructor

theorem floatofint_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.floatofint v = some u) : Vmatch bc u (floatofint x) := by
  cases h <;> simp only [Val.floatofint, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [floatofint, ntop1] <;> constructor

theorem floatofintu_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.floatofintu v = some u) : Vmatch bc u (floatofintu x) := by
  cases h <;> simp only [Val.floatofintu, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [floatofintu, ntop1] <;> constructor

theorem singleofint_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.singleofint v = some u) : Vmatch bc u (singleofint x) := by
  cases h <;> simp only [Val.singleofint, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [singleofint, ntop1] <;> constructor

theorem singleofintu_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.singleofintu v = some u) : Vmatch bc u (singleofintu x) := by
  cases h <;> simp only [Val.singleofintu, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [singleofintu, ntop1] <;> constructor

theorem floatoflong_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.floatoflong v = some u) : Vmatch bc u (floatoflong x) := by
  cases h <;> simp only [Val.floatoflong, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [floatoflong, ntop1] <;> constructor

theorem floatoflongu_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.floatoflongu v = some u) : Vmatch bc u (floatoflongu x) := by
  cases h <;> simp only [Val.floatoflongu, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [floatoflongu, ntop1] <;> constructor

theorem singleoflong_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.singleoflong v = some u) : Vmatch bc u (singleoflong x) := by
  cases h <;> simp only [Val.singleoflong, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [singleoflong, ntop1] <;> constructor

theorem singleoflongu_sound {v u : Val} {x : Aval} (h : Vmatch bc v x)
    (hv : Val.singleoflongu v = some u) : Vmatch bc u (singleoflongu x) := by
  cases h <;> simp only [Val.singleoflongu, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
    simp only [singleoflongu, ntop1] <;> constructor

theorem floatofwords_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.floatofwords v w) (floatofwords x y) := by
  cases h1 <;> cases h2 <;> simp only [Val.floatofwords, floatofwords, ntop2] <;> constructor

theorem longofwords_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.longofwords v w) (longofwords x y) := by
  cases h1 <;> cases h2 <;> simp only [Val.longofwords, longofwords, ntop2] <;> constructor

theorem loword_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.loword v) (loword x) := by
  cases h <;> simp only [Val.loword, loword, ntop1] <;> constructor

theorem hiword_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.hiword v) (hiword x) := by
  cases h <;> simp only [Val.hiword, hiword, ntop1] <;> constructor

end

end ValueDomain
end CC
