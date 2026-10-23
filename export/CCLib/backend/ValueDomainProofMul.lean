/-
  Soundness of the abstract multiplication, division and remainder
  operators of the value analysis — the lemmas of `backend/ValueDomain.v`
  from `urange_sound` / `srange_sound` to `shrx_sound`.  Continues
  `ValueDomainProofArith.lean`.

  Differences from Rocq: the product and quotient ranges
  (`Zmult_unsigned_range`, `Zmult_signed_range`, `Zdiv_unsigned_range`, …,
  from `Zbits.v`) are proved here directly with the integer lemmas of Lean
  core.
-/
import CCLib.backend.ValueDomainProofArith

namespace CC
namespace ValueDomain

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

/-! ## Products of bounded integers -/

theorem prod_uns_bound {a b n m : Z} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (ha : 0 ≤ a ∧ a < twoP n) (hb : 0 ≤ b ∧ b < twoP m) :
    0 ≤ a * b ∧ a * b < twoP (n + m) := by
  rw [twoP_add hn hm]
  refine ⟨Int.mul_nonneg ha.1 hb.1, ?_⟩
  have := twoP_pos hn
  exact Int.lt_of_le_of_lt (Int.mul_le_mul (Int.le_refl a) (Int.le_of_lt hb.2) hb.1 ha.1)
    (Int.mul_lt_mul_of_pos_right ha.2 (twoP_pos hm))

theorem abs_mul_bound {a b A B : Z} (ha : -A ≤ a ∧ a ≤ A) (hb : -B ≤ b ∧ b ≤ B) :
    -(A * B) ≤ a * b ∧ a * b ≤ A * B := by
  have hA : 0 ≤ A := by zomega
  have hB : 0 ≤ B := by zomega
  have h1 : a.natAbs ≤ A.toNat := by zomega
  have h2 : b.natAbs ≤ B.toNat := by zomega
  have h3 : (a * b).natAbs ≤ A.toNat * B.toNat := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul h1 h2
  have e : ((A.toNat * B.toNat : Nat) : Z) = A * B := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
  have h4 : (((a * b).natAbs : Nat) : Z) ≤ ((A.toNat * B.toNat : Nat) : Z) := Int.ofNat_le.mpr h3
  rw [e] at h4
  constructor <;> zomega

theorem prod_sgn_bound {a b n m : Z} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (ha : -twoP n ≤ a ∧ a < twoP n) (hb : -twoP m ≤ b ∧ b < twoP m) :
    -twoP (n + m) ≤ a * b ∧ a * b ≤ twoP (n + m) := by
  rw [twoP_add hn hm]
  exact abs_mul_bound ⟨ha.1, by zomega⟩ ⟨hb.1, by zomega⟩

section
variable {bc : BlockClassification}

/-! ## `urange` and `srange` -/

/-- `ValueDomain.urange_sound` -/
theorem urange_sound {i : Integers.Int} {a : Aval} (h : Vmatch bc (.Vint i) a) :
    0 ≤ urange a ∧ IsUns (urange a) i := by
  cases h <;> simp only [urange]
  · exact ⟨usize_pos _, is_uns_usize _⟩
  · exact ⟨usize_pos _, is_uns_usize _⟩
  · exact ⟨‹_›, ‹_›⟩
  all_goals exact ⟨by decide, is_uns_wordsize _⟩

/-- `ValueDomain.srange_sound` -/
theorem srange_sound {i : Integers.Int} {a : Aval} (h : Vmatch bc (.Vint i) a) :
    0 < srange a ∧ IsSgn (srange a) i := by
  cases h <;> simp only [srange]
  · exact ⟨ssize_pos _, is_sgn_ssize _⟩
  · exact ⟨ssize_pos _, is_sgn_ssize _⟩
  · exact ⟨by zomega, is_uns_sgn ‹_› (by zomega)⟩
  · exact ⟨‹_›, ‹_›⟩
  all_goals exact ⟨by decide, is_sgn_wordsize _⟩

/-! ## Multiplication -/

theorem mul_uns {i j : Integers.Int} {n m : Z} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hi : IsUns n i) (hj : IsUns m j) : IsUns (n + m) (Integers.Int.mul i j) := by
  rw [Integers.Int.mul_unsigned]
  have P := prod_uns_bound hn hm (range_is_uns hn hi) (range_is_uns hm hj)
  exact is_uns_range (by zomega) P.1 P.2

theorem mul_sgn {i j : Integers.Int} {n m : Z} (hn : 0 < n) (hm : 0 < m)
    (hi : IsSgn n i) (hj : IsSgn m j) : IsSgn (n + m) (Integers.Int.mul i j) := by
  rw [Integers.Int.mul_signed]
  have P := prod_sgn_bound (show 0 ≤ n - 1 by zomega) (show 0 ≤ m - 1 by zomega)
    (range_is_sgn hn hi) (range_is_sgn hm hj)
  have e := twoP_succ (show 0 ≤ n - 1 + (m - 1) by zomega)
  rw [show n - 1 + (m - 1) + 1 = n + m - 1 by zomega] at e
  have := twoP_pos (show 0 ≤ n - 1 + (m - 1) by zomega)
  apply is_sgn_range (by zomega) <;> zomega

theorem vmatch_undef_mulBase (x y : Aval) : Vmatch bc .Vundef (mulBase x y) := by
  cases x <;> cases y <;> delta mulBase <;> dsimp only <;>
    first | exact vmatch_uns_undef _ _ | exact vmatch_sgn_undef _ _ | constructor

local macro "mul_side" : tactic =>
  `(tactic| first
    | assumption
    | exact usize_pos _
    | exact is_uns_usize _
    | exact ssize_pos _
    | exact is_sgn_ssize _
    | exact is_uns_sgn ‹_› (by zomega)
    | zomega)

local macro "mul_close" : tactic =>
  `(tactic| first
    | constructor
    | (apply vmatch_uns; first
        | (apply mul_uns <;> mul_side)
        | (rw [Integers.Int.mul_commut]; apply mul_uns <;> mul_side))
    | (apply vmatch_sgn; first
        | (apply mul_sgn <;> mul_side)
        | (rw [Integers.Int.mul_commut]; apply mul_sgn <;> mul_side)))

set_option maxHeartbeats 4000000 in
/-- `ValueDomain.mul_base_sound` -/
theorem mul_base_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mul v w) (mulBase x y) := by
  cases v <;> cases w <;> simp only [Val.mul] <;> try exact vmatch_undef_mulBase x y
  rename_i i j
  cases h1 <;> cases h2 <;> delta mulBase <;> dsimp only <;> mul_close

set_option maxHeartbeats 4000000 in
/-- `ValueDomain.mul_sound` -/
theorem mul_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mul v w) (mul x y) := by
  have H : Vmatch bc (Val.mul v w)
      (if vincl x (.Uns .Ptop 0) || vincl y (.Uns .Ptop 0) then .IU Integers.Int.zero
       else mulBase x y) := by
    split
    · rename_i hc
      rcases Bool.or_eq_true_iff.mp hc with hc | hc
      · rcases vmatch_Uns_0 (vmatch_ge (vincl_ge hc) h1) with e | e <;> subst e
        · exact .iu_undef _
        · cases w <;> simp only [Val.mul] <;> try exact .iu_undef _
          rw [Integers.Int.mul_commut, Integers.Int.mul_zero]; exact .iu _
      · rcases vmatch_Uns_0 (vmatch_ge (vincl_ge hc) h2) with e | e <;> subst e
        · cases v <;> exact .iu_undef _
        · cases v <;> simp only [Val.mul] <;> try exact .iu_undef _
          rw [Integers.Int.mul_zero]; exact .iu _
    · exact mul_base_sound h1 h2
  cases x <;> cases y <;> first
    | exact H
    | (cases h1 <;> cases h2 <;> first | constructor | exact H)

end

end ValueDomain
end CC
