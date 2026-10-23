/-
  Soundness of the abstract division and remainder operators and of `shrx`
  (`backend/ValueDomain.v`, `divs_sound` … `shrx_sound`).  Continues
  `ValueDomainProofDiv.lean`.

  Differences from Rocq: `Zdiv_unsigned_range` and `Zdiv_signed_range`
  (from `Zbits.v`) are proved here on Lean's `Int.tdiv` / `Int.natAbs`.
  The remainder bounds are proved directly from `Int.emod` / `Int.tmod`
  bounds instead of through `Zsize_monotone`.
-/
import CCLib.backend.ValueDomainProofDiv

namespace CC
namespace ValueDomain

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

/-! ## Quotients of bounded integers -/

theorem zlog2_nonneg (y : Z) : 0 ≤ zlog2 y := by
  unfold zlog2; split <;> zomega

theorem twoP_zlog2_le {y : Z} (hy : 0 < y) : twoP (zlog2 y) ≤ y := by
  unfold zlog2
  simp only [show ¬ (y ≤ 0) by zomega, if_false]
  rw [twoP_nat]
  have h := Nat.log2_self_le (n := y.toNat) (by zomega)
  have e : ((2 : Z) ^ y.toNat.log2) = ((2 ^ y.toNat.log2 : Nat) : Z) := by simp
  rw [e]
  have h' : ((2 ^ y.toNat.log2 : Nat) : Z) ≤ ((y.toNat : Nat) : Z) := Int.ofNat_le.mpr h
  rw [Int.toNat_of_nonneg (by zomega)] at h'
  exact h'

/-- `Zbits.Zdiv_unsigned_range` -/
theorem zdiv_unsigned_range {n x y : Z} (hn : 0 ≤ n) (hx : 0 ≤ x ∧ x < twoP n) (hy : 0 < y) :
    0 ≤ x / y ∧ x / y < twoP (max 0 (n - zlog2 y)) := by
  have hm := zlog2_nonneg y
  have hle := twoP_zlog2_le hy
  refine ⟨Int.ediv_nonneg hx.1 (by zomega), ?_⟩
  by_cases h : n < zlog2 y
  · rw [show max 0 (n - zlog2 y) = 0 by zomega]
    have := twoP_mono hn (show n ≤ zlog2 y by zomega)
    rw [Int.ediv_eq_zero_of_lt hx.1 (by zomega)]
    decide
  · rw [show max 0 (n - zlog2 y) = n - zlog2 y by zomega]
    rw [Int.ediv_lt_iff_lt_mul hy]
    have e := twoP_add (show 0 ≤ n - zlog2 y by zomega) hm
    rw [show n - zlog2 y + zlog2 y = n by zomega] at e
    have hp := twoP_pos (show 0 ≤ n - zlog2 y by zomega)
    have := Int.mul_le_mul_of_nonneg_left hle (Int.le_of_lt hp)
    zomega

/-- `Zbits.Zdiv_signed_range` (with the bound on `|x|` instead of on `x`). -/
theorem zdiv_signed_range {n x y : Z} (hn : 0 ≤ n) (hx : -twoP n ≤ x ∧ x < twoP n) (hy : y ≠ 0) :
    -twoP (max 0 (n + 1 - zlog2 (y.natAbs : Z))) < x.tdiv y ∧
      x.tdiv y < twoP (max 0 (n + 1 - zlog2 (y.natAbs : Z))) := by
  have hn1 := twoP_succ hn
  have hax : 0 ≤ (x.natAbs : Z) ∧ (x.natAbs : Z) < twoP (n + 1) := by
    have := twoP_pos hn
    constructor <;> zomega
  have Q := zdiv_unsigned_range (show 0 ≤ n + 1 by zomega) hax (show 0 < (y.natAbs : Z) by zomega)
  have e : ((x.tdiv y).natAbs : Z) = (x.natAbs : Z) / (y.natAbs : Z) := by
    rw [Int.natAbs_tdiv]; rfl
  generalize twoP (max 0 (n + 1 - zlog2 (y.natAbs : Z))) = K at *
  rw [← e] at Q
  constructor <;> zomega

section
variable {bc : BlockClassification}

theorem eq_zero_false {j : Integers.Int} (h : Integers.Int.eq j Integers.Int.zero = false) :
    j ≠ Integers.Int.zero := by
  intro e; subst e; rw [Integers.Int.eq_true] at h; cases h

theorem signed_ne_zero {j : Integers.Int} (h : j ≠ Integers.Int.zero) : Integers.Int.signed j ≠ 0 := by
  intro e; apply h
  rw [← Integers.Int.repr_signed j, e]; rfl

theorem unsigned_ne_zero {j : Integers.Int} (h : j ≠ Integers.Int.zero) :
    Integers.Int.unsigned j ≠ 0 := by
  intro e; apply h
  rw [← Integers.Int.repr_unsigned j, e]; rfl

theorem divs_range {i j : Integers.Int} {n : Z} (hn : 0 < n) (hi : IsSgn n i)
    (hj : j ≠ Integers.Int.zero) :
    IsSgn (max 1 (n + 1 - zlog2 ((Integers.Int.signed j).natAbs : Z))) (Integers.Int.divs i j) := by
  rw [Integers.Int.divs_signed]
  have R := range_is_sgn hn hi
  have Q := zdiv_signed_range (show 0 ≤ n - 1 by zomega) R (signed_ne_zero hj)
  rw [show n - 1 + 1 = n by zomega] at Q
  apply is_sgn_range (by zomega) <;>
    rw [show max 1 (n + 1 - zlog2 ((Integers.Int.signed j).natAbs : Z)) - 1 =
      max 0 (n - zlog2 ((Integers.Int.signed j).natAbs : Z)) by zomega] <;> zomega

set_option maxHeartbeats 1000000 in
/-- `ValueDomain.divs_sound` -/
theorem divs_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.divs v w = some u) : Vmatch bc u (divs strict x y) := by
  cases v <;> cases w <;> simp only [Val.divs, reduceCtorEq] at h
  rename_i i j
  split at h
  · cases h
  rename_i hE
  cases h
  have E' : Integers.Int.eq j Integers.Int.zero = false := by
    have := Bool.of_not_eq_true hE
    simp only [Bool.or_eq_false_iff] at this; exact this.1
  have hj := eq_zero_false E'
  have hq : Vmatch bc (.Vint (Integers.Int.divs i j))
      (sgn (provenance x) (srange x + 1 - zlog2 ((Integers.Int.signed j).natAbs : Z))) := by
    obtain ⟨A, B⟩ := srange_sound h1
    exact vmatch_sgn' _ _ _ (divs_range A B hj)
  cases h1 <;> cases h2 <;> simp only [divs] <;> first
    | constructor
    | (rw [if_neg hE]; constructor)
    | (simp only [E', Bool.false_eq_true, if_false]; exact hq)

/-- `ValueDomain.divu_sound` -/
theorem divu_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.divu v w = some u) : Vmatch bc u (divu strict x y) := by
  cases v <;> cases w <;> simp only [Val.divu, reduceCtorEq] at h
  rename_i i j
  split at h
  · cases h
  rename_i E
  cases h
  have hj := eq_zero_false (Bool.of_not_eq_true E)
  have hq : Vmatch bc (.Vint (Integers.Int.divu i j))
      (uns (provenance x) (urange x - zlog2 (Integers.Int.unsigned j))) := by
    obtain ⟨A, B⟩ := urange_sound h1
    apply vmatch_uns'
    rw [Integers.Int.divu_unsigned]
    have hu := unsigned_ne_zero hj
    have := Integers.Int.unsigned_range j
    have Q := zdiv_unsigned_range A (range_is_uns A B) (show 0 < Integers.Int.unsigned j by zomega)
    exact is_uns_range (by zomega) Q.1 Q.2
  cases h2 <;> simp only [divu] <;> try constructor
  all_goals (simp only [Bool.of_not_eq_true E]
             cases h1 <;> first | constructor | exact hq)

theorem mods_range (i : Integers.Int) {j : Integers.Int} (hj : j ≠ Integers.Int.zero) :
    IsSgn (ssize j) (Integers.Int.mods i j) := by
  rw [Integers.Int.mods_signed]
  have R := range_is_sgn (ssize_pos j) (is_sgn_ssize j)
  have hs := signed_ne_zero hj
  have e : (((Integers.Int.signed i).tmod (Integers.Int.signed j)).natAbs : Z) =
      ((Integers.Int.signed i).natAbs % (Integers.Int.signed j).natAbs : Nat) := by
    rw [Int.natAbs_tmod]
  have hlt : (Integers.Int.signed i).natAbs % (Integers.Int.signed j).natAbs <
      (Integers.Int.signed j).natAbs := Nat.mod_lt _ (by zomega)
  apply is_sgn_range (ssize_pos j) <;> zomega

/-- `ValueDomain.mods_sound` -/
theorem mods_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.mods v w = some u) : Vmatch bc u (mods strict x y) := by
  cases v <;> cases w <;> simp only [Val.mods, reduceCtorEq] at h
  rename_i i j
  split at h
  · cases h
  rename_i hE
  cases h
  have E' : Integers.Int.eq j Integers.Int.zero = false := by
    have := Bool.of_not_eq_true hE
    simp only [Bool.or_eq_false_iff] at this; exact this.1
  have hq : ∀ p, Vmatch bc (.Vint (Integers.Int.mods i j)) (sgn p (ssize j)) := fun p =>
    vmatch_sgn _ _ _ (mods_range i (eq_zero_false E'))
  cases h1 <;> cases h2 <;> simp only [mods] <;> first
    | constructor
    | (rw [if_neg hE]; constructor)
    | exact hq _

/-- `ValueDomain.modu_sound` -/
theorem modu_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.modu v w = some u) : Vmatch bc u (modu strict x y) := by
  cases v <;> cases w <;> simp only [Val.modu, reduceCtorEq] at h
  rename_i i j
  split at h
  · cases h
  rename_i E
  cases h
  have hj := eq_zero_false (Bool.of_not_eq_true E)
  have hq : ∀ p, Vmatch bc (.Vint (Integers.Int.modu i j)) (uns p (usize j)) := by
    intro p
    apply vmatch_uns
    have R := range_is_uns (usize_pos j) (is_uns_usize j)
    have hb := Integers.Int.modu_bound i j hj
    have := Integers.Int.unsigned_range (Integers.Int.modu i j)
    rw [← Integers.Int.repr_unsigned (Integers.Int.modu i j)]
    exact is_uns_range (usize_pos j) this.1 (by zomega)
  cases h2 <;> simp only [modu] <;> try constructor
  all_goals (cases h1 <;> simp only [Bool.of_not_eq_true E] <;>
    first | constructor | exact hq _)

/-- `ValueDomain.shrx_sound` -/
theorem shrx_sound {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y)
    (h : Val.shrx v w = some u) : Vmatch bc u (shrx x y) := by
  cases v <;> cases w <;> simp only [Val.shrx, reduceCtorEq] at h
  rename_i i j
  split at h
  · rename_i hlt
    cases h
    cases h1 <;> simp only [shrx, ntop1] <;> try constructor
    cases h2 <;> simp only [hlt, if_true] <;> constructor
  · cases h

end

end ValueDomain
end CC
