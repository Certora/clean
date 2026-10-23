/-
  Soundness of the abstract high-multiplication, division, remainder and
  `shrx` operators of the value analysis (`backend/ValueDomain.v`, from
  `mulhs_base_sound` to `shrx_sound`).  Continues
  `ValueDomainProofMul.lean`.
-/
import CCLib.backend.ValueDomainProofMul

namespace CC
namespace ValueDomain

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

theorem twoP_32 : twoP 32 = 4294967296 := by decide

theorem int_modulus_eq : Integers.MI.modulus 32 = 4294967296 := by decide

theorem mulhu_eq (i j : Integers.Int) :
    Integers.Int.mulhu i j =
      Integers.Int.repr ((Integers.Int.unsigned i * Integers.Int.unsigned j) / 4294967296) := by
  show Integers.MI.mulhu i j = _
  simp only [Integers.MI.mulhu, int_modulus_eq]; rfl

theorem mulhs_eq (i j : Integers.Int) :
    Integers.Int.mulhs i j =
      Integers.Int.repr ((Integers.Int.signed i * Integers.Int.signed j) / 4294967296) := by
  show Integers.MI.mulhs i j = _
  simp only [Integers.MI.mulhs, int_modulus_eq]; rfl

theorem mulhs_zero_l (j : Integers.Int) : Integers.Int.mulhs Integers.Int.zero j = Integers.Int.zero := by
  rw [mulhs_eq, Integers.Int.signed_zero, Int.zero_mul, Int.zero_ediv]; rfl

theorem mulhs_zero_r (j : Integers.Int) : Integers.Int.mulhs j Integers.Int.zero = Integers.Int.zero := by
  rw [mulhs_eq, Integers.Int.signed_zero, Int.mul_zero, Int.zero_ediv]; rfl

theorem mulhu_zero_l (j : Integers.Int) : Integers.Int.mulhu Integers.Int.zero j = Integers.Int.zero := by
  rw [mulhu_eq, Integers.Int.unsigned_zero, Int.zero_mul, Int.zero_ediv]; rfl

theorem mulhu_zero_r (j : Integers.Int) : Integers.Int.mulhu j Integers.Int.zero = Integers.Int.zero := by
  rw [mulhu_eq, Integers.Int.unsigned_zero, Int.mul_zero, Int.zero_ediv]; rfl

theorem mulhu_one_l (j : Integers.Int) : Integers.Int.mulhu Integers.Int.one j = Integers.Int.zero := by
  rw [mulhu_eq, Integers.Int.unsigned_one, Int.one_mul]
  have := Integers.Int.unsigned_range j
  simp only [Integers.Int.modulus, int_modulus_eq] at this
  rw [Int.ediv_eq_zero_of_lt this.1 this.2]; rfl

theorem mulhu_one_r (j : Integers.Int) : Integers.Int.mulhu j Integers.Int.one = Integers.Int.zero := by
  rw [mulhu_eq, Integers.Int.unsigned_one, Int.mul_one]
  have := Integers.Int.unsigned_range j
  simp only [Integers.Int.modulus, int_modulus_eq] at this
  rw [Int.ediv_eq_zero_of_lt this.1 this.2]; rfl

section
variable {bc : BlockClassification}

/-- `ValueDomain.mulhs_base_sound` -/
theorem mulhs_base_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mulhs v w) (mulhsBase x y) := by
  unfold mulhsBase
  cases v <;> cases w <;> simp only [Val.mulhs] <;> try exact vmatch_sgn_undef _ _
  rename_i i j
  obtain ⟨A1, B1⟩ := srange_sound h1
  obtain ⟨A2, B2⟩ := srange_sound h2
  have R1 := range_is_sgn A1 B1
  have R2 := range_is_sgn A2 B2
  generalize srange x = n at *
  generalize srange y = m at *
  have P := prod_sgn_bound (show 0 ≤ n - 1 by zomega) (show 0 ≤ m - 1 by zomega) R1 R2
  rw [mulhs_eq]
  apply vmatch_sgn'
  have hK : 0 ≤ max 1 (n + m - Integers.Int.zwordsize) - 1 := by zomega
  have T1 := twoP_mono (show 0 ≤ n - 1 + (m - 1) by zomega)
    (show n - 1 + (m - 1) ≤ (max 1 (n + m - Integers.Int.zwordsize) - 1) + 31 by zomega)
  rw [twoP_add hK (by decide)] at T1
  have T31 : twoP 31 = 2147483648 := by decide
  rw [T31] at T1
  have Tp := twoP_pos hK
  apply is_sgn_range (by zomega)
  all_goals generalize twoP (max 1 (n + m - Integers.Int.zwordsize) - 1) = K at *
  · rw [Int.le_ediv_iff_mul_le (by decide)]; zomega
  · rw [Int.ediv_lt_iff_lt_mul (by decide)]; zomega

/-- `ValueDomain.mulhu_base_sound` -/
theorem mulhu_base_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mulhu v w) (mulhuBase x y) := by
  unfold mulhuBase
  cases v <;> cases w <;> simp only [Val.mulhu] <;> try exact vmatch_uns_undef _ _
  rename_i i j
  obtain ⟨A1, B1⟩ := urange_sound h1
  obtain ⟨A2, B2⟩ := urange_sound h2
  have R1 := range_is_uns A1 B1
  have R2 := range_is_uns A2 B2
  generalize urange x = n at *
  generalize urange y = m at *
  have P := prod_uns_bound A1 A2 R1 R2
  rw [mulhu_eq]
  apply vmatch_uns'
  have hK : 0 ≤ max 0 (n + m - Integers.Int.zwordsize) := by zomega
  have T1 := twoP_mono (show 0 ≤ n + m by zomega)
    (show n + m ≤ max 0 (n + m - Integers.Int.zwordsize) + 32 by zomega)
  rw [twoP_add hK (by decide), twoP_32] at T1
  have Tp := twoP_pos hK
  apply is_uns_range hK
  all_goals generalize twoP (max 0 (n + m - Integers.Int.zwordsize)) = K at *
  · exact Int.ediv_nonneg P.1 (by decide)
  · rw [Int.ediv_lt_iff_lt_mul (by decide)]; zomega

set_option maxHeartbeats 4000000 in
/-- `ValueDomain.mulhs_sound` -/
theorem mulhs_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mulhs v w) (mulhs x y) := by
  have H : Vmatch bc (Val.mulhs v w)
      (if vincl x (.Uns .Ptop 0) || vincl y (.Uns .Ptop 0) then .IU Integers.Int.zero
       else mulhsBase x y) := by
    split
    · rename_i hc
      rcases Bool.or_eq_true_iff.mp hc with hc | hc
      · rcases vmatch_Uns_0 (vmatch_ge (vincl_ge hc) h1) with e | e <;> subst e
        · exact .iu_undef _
        · cases w <;> simp only [Val.mulhs] <;> try exact .iu_undef _
          rw [mulhs_zero_l]; exact .iu _
      · rcases vmatch_Uns_0 (vmatch_ge (vincl_ge hc) h2) with e | e <;> subst e
        · cases v <;> exact .iu_undef _
        · cases v <;> simp only [Val.mulhs] <;> try exact .iu_undef _
          rw [mulhs_zero_r]; exact .iu _
    · exact mulhs_base_sound h1 h2
  cases x <;> cases y <;> first
    | exact H
    | (cases h1 <;> cases h2 <;> first | constructor | exact H)

set_option maxHeartbeats 4000000 in
/-- `ValueDomain.mulhu_sound` -/
theorem mulhu_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mulhu v w) (mulhu x y) := by
  have H : Vmatch bc (Val.mulhu v w)
      (if vincl x (.Uns .Ptop 1) || vincl y (.Uns .Ptop 1) then .IU Integers.Int.zero
       else mulhuBase x y) := by
    split
    · rename_i hc
      rcases Bool.or_eq_true_iff.mp hc with hc | hc
      · rcases vmatch_Uns_1 (vmatch_ge (vincl_ge hc) h1) with e | e | e <;> subst e
        · exact .iu_undef _
        · cases w <;> simp only [Val.mulhu] <;> try exact .iu_undef _
          rw [mulhu_zero_l]; exact .iu _
        · cases w <;> simp only [Val.mulhu] <;> try exact .iu_undef _
          rw [mulhu_one_l]; exact .iu _
      · rcases vmatch_Uns_1 (vmatch_ge (vincl_ge hc) h2) with e | e | e <;> subst e
        · cases v <;> exact .iu_undef _
        · cases v <;> simp only [Val.mulhu] <;> try exact .iu_undef _
          rw [mulhu_zero_r]; exact .iu _
        · cases v <;> simp only [Val.mulhu] <;> try exact .iu_undef _
          rw [mulhu_one_r]; exact .iu _
    · exact mulhu_base_sound h1 h2
  cases x <;> cases y <;> first
    | exact H
    | (cases h1 <;> cases h2 <;> first | constructor | exact H)

end

end ValueDomain
end CC
