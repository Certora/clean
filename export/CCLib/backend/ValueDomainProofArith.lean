/-
  Soundness of the abstract integer arithmetic of the value analysis — the
  lemmas of `backend/ValueDomain.v` from `is_uns_range` / `range_is_uns` /
  `is_sgn_range` / `range_is_sgn` to the arithmetic operators (`rol`, `ror`,
  `rolm`, `neg`, `add`, `sub`, …).  Continues `ValueDomainProof.lean`.

  Differences from Rocq: the range lemmas are proved directly on the
  bit-vector representation of `Int` (`toNat`/`toInt` and `Nat.testBit`)
  instead of through `Zbits`.
-/
import CCLib.backend.ValueDomainProof
import CCLib.common.ValuesOps

namespace CC
namespace ValueDomain

open Integers (Ptrofs)

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

/-! ## Ranges of integers with bounded significant bits -/

theorem twoP_nat (k : Nat) : twoP (k : Z) = (2 : Z) ^ k := by
  unfold twoP; simp only [show ¬ ((k : Z) < 0) by zomega, if_false]; simp

theorem twoP_of_nonneg {n : Z} (h : 0 ≤ n) : twoP n = (2 : Z) ^ n.toNat := by
  unfold twoP; simp only [show ¬ (n < 0) by zomega, if_false]

/-- Bits of `x` at positions `≥ j` are zero iff `x < 2^j`. -/
theorem testbit_high_false_iff (x : Integers.Int) (j : Nat) :
    (∀ m : Nat, m < 32 → j ≤ m → Integers.Int.testbit x m = false) ↔ x.toNat < 2 ^ j := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases hi32 : i < 32
    · exact h i hi32 hi
    · apply Nat.testBit_lt_two_pow
      have := x.isLt
      have : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  · intro h m _ hm
    show x.toNat.testBit m = false
    apply Nat.testBit_lt_two_pow
    have : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    omega

theorem isUns_iff (n : Z) (x : Integers.Int) :
    IsUns n x ↔ x.toNat < 2 ^ n.toNat := by
  rw [← testbit_high_false_iff]
  unfold IsUns
  simp only [Integers.Int.zwordsize]
  constructor
  · intro h m h1 h2; exact h m (by zomega) (by zomega)
  · intro h m h1 h2; exact h m (by zomega) (by zomega)

/-- `ValueDomain.range_is_uns` -/
theorem range_is_uns {i : Integers.Int} {n : Z} (hn : 0 ≤ n) (h : IsUns n i) :
    0 ≤ Integers.Int.unsigned i ∧ Integers.Int.unsigned i < twoP n := by
  rw [isUns_iff] at h
  rw [twoP_of_nonneg hn]
  simp only [Integers.Int.unsigned, Integers.MI.unsigned]
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have h' : ((i.toNat : Nat) : _root_.Int) < ((2 ^ n.toNat : Nat) : _root_.Int) := Int.ofNat_lt.mpr h
  simpa using h'

/-- `ValueDomain.is_uns_range` -/
theorem is_uns_range {z n : Z} (hn : 0 ≤ n) (h1 : 0 ≤ z) (h2 : z < twoP n) :
    IsUns n (Integers.Int.repr z) := by
  rw [isUns_iff]
  rw [twoP_of_nonneg hn] at h2
  have e := Integers.Int.unsigned_repr_eq z
  simp only [Integers.Int.unsigned, Integers.MI.unsigned, Integers.Int.modulus,
    Integers.MI.modulus] at e
  have hp : ((2 : Z) ^ n.toNat) = ((2 ^ n.toNat : Nat) : Z) := by simp
  simp only [Z] at *
  omega

/-! ## Ranges of signed integers -/
theorem testbit_not_lt (x : Integers.Int) {m : Nat} (hm : m < 32) :
    Integers.Int.testbit (Integers.Int.not x) m = !Integers.Int.testbit x m := by
  show (~~~x).getLsbD m = !x.getLsbD m
  rw [BitVec.getLsbD_not]; simp [hm]

theorem isSgn_iff_uns {n : Z} (x : Integers.Int) (hn : 0 < n) (hn32 : n ≤ 32) :
    IsSgn n x ↔ IsUns (n - 1) x ∨ IsUns (n - 1) (Integers.Int.not x) := by
  unfold IsSgn IsUns
  constructor
  · intro h
    cases h31 : Integers.Int.testbit x 31
    · left; intro m hm1 hm2; rw [h m hm1 (by zomega), h31]
    · right; intro m hm1 hm2
      rw [testbit_not_lt x (by zomega), h m hm1 (by zomega), h31]; rfl
  · rintro (h | h) m hm1 hm2
    · rw [h m hm1 hm2, h 31 (by zomega) (by zomega)]
    · have a := h m hm1 hm2
      have b := h 31 (by zomega) (by zomega)
      rw [testbit_not_lt x (by zomega)] at a
      rw [testbit_not_lt x (by omega)] at b
      simp at a b; rw [a, b]



theorem signed_toInt_cases (x : Integers.Int) :
    (x.toNat < 2^31 ∧ Integers.Int.signed x = (x.toNat : Z)) ∨
    (2^31 ≤ x.toNat ∧ Integers.Int.signed x = (x.toNat : Z) - 2^32) := by
  have := x.isLt
  simp only [Integers.Int.signed, Integers.MI.signed, BitVec.toInt_eq_toNat_cond]
  by_cases h : 2 * x.toNat < 2^32
  · left; simp only [h, if_true]; exact ⟨by omega, by simp⟩
  · right; simp only [h, if_false]; refine ⟨by omega, ?_⟩; simp

/-- `ValueDomain.range_is_sgn` -/
theorem range_is_sgn {i : Integers.Int} {n : Z} (hn : 0 < n) (h : IsSgn n i) :
    -twoP (n - 1) ≤ Integers.Int.signed i ∧ Integers.Int.signed i < twoP (n - 1) := by
  have hlt := i.isLt
  simp only [Z] at *
  rw [twoP_of_nonneg (n := n - 1) (by zomega)]
  by_cases h32 : n ≤ 32
  · have hk : (n-1).toNat ≤ 31 := by zomega
    have hp : (2:Nat) ^ (n-1).toNat ≤ 2^31 := Nat.pow_le_pow_right (by zomega) hk
    have hpz : ((2:Z) ^ (n-1).toNat) = ((2 ^ (n-1).toNat : Nat) : Z) := by simp
    rw [hpz]
    rcases (isSgn_iff_uns i hn h32).1 h with hu | hu
    · rw [isUns_iff] at hu
      generalize 2 ^ (n-1).toNat = P at *
      rcases signed_toInt_cases i with ⟨h1, e⟩ | ⟨h1, e⟩ <;> rw [e] <;> zomega
    · rw [isUns_iff] at hu
      have : (Integers.Int.not i).toNat = 2^32 - 1 - i.toNat := BitVec.toNat_not
      rw [this] at hu
      generalize 2 ^ (n-1).toNat = P at *
      rcases signed_toInt_cases i with ⟨h1, e⟩ | ⟨h1, e⟩ <;> rw [e] <;> zomega
  · have hp : (2:Nat) ^ 31 ≤ 2 ^ (n-1).toNat := Nat.pow_le_pow_right (by zomega) (by zomega)
    have hpz : ((2:Z) ^ (n-1).toNat) = ((2 ^ (n-1).toNat : Nat) : Z) := by simp
    rw [hpz]
    generalize 2 ^ (n-1).toNat = P at *
    rcases signed_toInt_cases i with ⟨h1, e⟩ | ⟨h1, e⟩ <;> rw [e] <;> zomega

/-- `ValueDomain.is_sgn_range` -/
theorem is_sgn_range {z n : Z} (hn : 0 < n) (h1 : -twoP (n - 1) ≤ z) (h2 : z < twoP (n - 1)) :
    IsSgn n (Integers.Int.repr z) := by
  simp only [Z] at *
  rw [twoP_of_nonneg (n := n - 1) (by zomega)] at h1 h2
  by_cases h32 : n ≤ 32
  · have hk : (n-1).toNat ≤ 31 := by zomega
    have hp : (2:Nat) ^ (n-1).toNat ≤ 2^31 := Nat.pow_le_pow_right (by zomega) hk
    have hpz : ((2:Z) ^ (n-1).toNat) = ((2 ^ (n-1).toNat : Nat) : Z) := by simp
    rw [hpz] at h1 h2
    rw [isSgn_iff_uns _ hn h32, isUns_iff, isUns_iff]
    have : (Integers.Int.not (Integers.Int.repr z)).toNat = 2^32 - 1 - (Integers.Int.repr z).toNat :=
      BitVec.toNat_not
    rw [this]
    have e := Integers.Int.unsigned_repr_eq z
    simp only [Integers.Int.unsigned, Integers.MI.unsigned, Integers.Int.modulus,
      Integers.MI.modulus] at e
    generalize 2 ^ (n-1).toNat = P at *
    zomega
  · intro m hm1 hm2; exfalso; zomega

/-! ## Rotations, negation, addition, subtraction -/
section
variable {bc : BlockClassification}

theorem bits_rol (x y : Integers.Int) {i : Nat} (hi : i < 32) :
    Integers.Int.testbit (Integers.Int.rol x y) i =
      Integers.Int.testbit x ((i + 32 - y.toNat % 32) % 32) := by
  show (Integers.MI.rol x y).getLsbD i = x.getLsbD _
  simp only [Integers.MI.rol, show (32 = 0) = False from by decide, if_false]
  rw [BitVec.getLsbD_rotateLeft]
  have h := Nat.mod_lt y.toNat (show 32 > 0 by omega)
  simp only [Nat.mod_mod]
  by_cases hlt : i < y.toNat % 32
  · simp only [hlt, decide_true, cond_true]
    congr 1; omega
  · simp only [hlt, decide_false, cond_false, hi, decide_true, Bool.true_and]
    congr 1; omega

theorem rol_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.rol v w) (rol x y) := by
  have DEFAULT : ∀ p, Vmatch bc (Val.rol v w) (.Num p) := by
    intro p; cases v <;> cases w <;> simp only [Val.rol] <;> constructor
  cases y <;> simp only [rol] <;> try exact DEFAULT _
  rename_i j
  cases h2
  cases h1 <;> simp only [Val.rol]
  · constructor
  · constructor
  · constructor
  · rename_i p i n hn hu
    apply vmatch_uns
    intro m hm1 hm2
    have hj := Integers.Int.unsigned_range j
    rw [bits_rol _ _ (by zomega)]
    simp only [Integers.Int.unsigned, Integers.MI.unsigned] at hm2 hj
    apply hu <;> zomega
  · exact vmatch_uns_undef _ _
  · rename_i p i n hn hs
    split
    · apply vmatch_sgn
      intro m hm1 hm2
      simp only [Integers.Int.unsigned, Integers.MI.unsigned] at hm2
      rw [bits_rol _ _ (by zomega), bits_rol _ _ (by omega)]
      have hj := Integers.Int.unsigned_range j
      simp only [Integers.Int.unsigned, Integers.MI.unsigned] at hj
      rw [hs ((m + 32 - j.toNat % 32) % 32) (by zomega) (by zomega),
        hs ((31 + 32 - j.toNat % 32) % 32) (by zomega) (by zomega)]
    · exact DEFAULT _
  · split
    · exact vmatch_sgn_undef _ _
    · exact DEFAULT _
  all_goals exact DEFAULT _

theorem ror_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.ror v w) (ror x y) := by
  have DEFAULT : ∀ p, Vmatch bc (Val.ror v w) (.Num p) := by
    intro p; cases v <;> cases w <;> simp only [Val.ror] <;> constructor
  cases y <;> simp only [ror] <;> try exact DEFAULT _
  cases h2
  cases h1 <;> simp only [Val.ror] <;> first | constructor | exact DEFAULT _

theorem rolm_sound {v : Val} {x : Aval} (amount mask : Integers.Int) (h : Vmatch bc v x) :
    Vmatch bc (Val.rolm v amount mask) (rolm x amount mask) := by
  have e : Val.rolm v amount mask = Val.and (Val.rol v (.Vint amount)) (.Vint mask) := by
    cases v <;> rfl
  rw [e]
  exact and_sound (rol_sound h (.i _)) (.i _)

theorem neg_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.neg v) (neg x) := by
  cases h <;> simp only [Val.neg, neg, ntop1] <;>
    first | constructor | exact vmatch_sgn_undef _ _ | skip
  rename_i p i n hn hs
  have A : Integers.Int.neg i = Integers.Int.repr (- Integers.Int.signed i) := by
    conv => lhs; rw [← Integers.Int.repr_signed i]
    exact Integers.Int.neg_repr _
  rw [A]
  have B := range_is_sgn hn hs
  apply vmatch_sgn
  have h0 : 0 ≤ n - 1 := by zomega
  have e1 : twoP (n + 1 - 1) = twoP (n - 1) * 2 := by
    rw [twoP_of_nonneg h0, twoP_of_nonneg (by zomega)]
    rw [show (n + 1 - 1).toNat = (n - 1).toNat + 1 by zomega, Int.pow_succ]
  apply is_sgn_range (by zomega) <;> rw [e1] <;> zomega

theorem twoP_succ {a : Z} (h : 0 ≤ a) : twoP (a + 1) = twoP a * 2 := by
  rw [twoP_of_nonneg h, twoP_of_nonneg (by zomega),
    show (a + 1).toNat = a.toNat + 1 by zomega, Int.pow_succ]

theorem twoP_pos {a : Z} (h : 0 ≤ a) : 0 < twoP a := by
  rw [twoP_of_nonneg h]; exact Int.pow_pos (by decide)

theorem twoP_mono {a b : Z} (h0 : 0 ≤ a) (h : a ≤ b) : twoP a ≤ twoP b := by
  rw [twoP_of_nonneg h0, twoP_of_nonneg (by zomega)]
  have : (2:Nat) ^ a.toNat ≤ 2 ^ b.toNat := Nat.pow_le_pow_right (by omega) (by zomega)
  have e1 : ((2:Z) ^ a.toNat) = ((2 ^ a.toNat : Nat) : Z) := by simp
  have e2 : ((2:Z) ^ b.toNat) = ((2 ^ b.toNat : Nat) : Z) := by simp
  rw [e1, e2]; exact Int.ofNat_le.mpr this

theorem twoP_add {a b : Z} (ha : 0 ≤ a) (hb : 0 ≤ b) : twoP (a + b) = twoP a * twoP b := by
  rw [twoP_of_nonneg ha, twoP_of_nonneg hb, twoP_of_nonneg (by zomega),
    show (a + b).toNat = a.toNat + b.toNat by zomega, Int.pow_add]

theorem add_uns {n m : Z} {i j : Integers.Int} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hi : IsUns n i) (hj : IsUns m j) : IsUns (max n m + 1) (Integers.Int.add i j) := by
  have A := range_is_uns hn hi
  have B := range_is_uns hm hj
  rw [Integers.Int.add_unsigned]
  have h1 := twoP_mono hn (Int.le_max_left n m)
  have h2 := twoP_mono hm (Int.le_max_right n m)
  have h3 := twoP_succ (show 0 ≤ max n m by zomega)
  apply is_uns_range (by zomega) <;> zomega

theorem add_sgn {n m : Z} {i j : Integers.Int} (hn : 0 < n) (hm : 0 < m)
    (hi : IsSgn n i) (hj : IsSgn m j) : IsSgn (max n m + 1) (Integers.Int.add i j) := by
  have A := range_is_sgn hn hi
  have B := range_is_sgn hm hj
  rw [Integers.Int.add_signed]
  have h1 := twoP_mono (show 0 ≤ n - 1 by zomega) (show n - 1 ≤ max n m - 1 by zomega)
  have h2 := twoP_mono (show 0 ≤ m - 1 by zomega) (show m - 1 ≤ max n m - 1 by zomega)
  have h3 := twoP_succ (show 0 ≤ max n m - 1 by zomega)
  rw [show max n m - 1 + 1 = max n m + 1 - 1 by zomega] at h3
  apply is_sgn_range (by zomega) <;> zomega

theorem add_sgn' {n m : Z} {i j : Integers.Int} (hn : 0 < n) (hm : 0 < m)
    (hi : IsSgn n i) (hj : IsSgn m j) : IsSgn (max m n + 1) (Integers.Int.add i j) := by
  rw [Int.max_comm]; exact add_sgn hn hm hi hj

theorem add_uns' {n m : Z} {i j : Integers.Int} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hi : IsUns n i) (hj : IsUns m j) : IsUns (max m n + 1) (Integers.Int.add i j) := by
  rw [Int.max_comm]; exact add_uns hn hm hi hj

theorem sub_uns {n m : Z} {i j : Integers.Int} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hi : IsUns n i) (hj : IsUns m j) : IsSgn (max n m + 1) (Integers.Int.sub i j) := by
  have A := range_is_uns hn hi
  have B := range_is_uns hm hj
  rw [Integers.Int.sub_unsigned]
  have h1 := twoP_mono hn (Int.le_max_left n m)
  have h2 := twoP_mono hm (Int.le_max_right n m)
  apply is_sgn_range (by zomega) <;> rw [show max n m + 1 - 1 = max n m by zomega] <;> zomega

theorem sub_uns' {n m : Z} {i j : Integers.Int} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hi : IsUns n i) (hj : IsUns m j) : IsSgn (max m n + 1) (Integers.Int.sub i j) := by
  rw [Int.max_comm]; exact sub_uns hn hm hi hj

theorem sub_sgn {n m : Z} {i j : Integers.Int} (hn : 0 < n) (hm : 0 < m)
    (hi : IsSgn n i) (hj : IsSgn m j) : IsSgn (max n m + 1) (Integers.Int.sub i j) := by
  have A := range_is_sgn hn hi
  have B := range_is_sgn hm hj
  rw [Integers.Int.sub_signed]
  have h1 := twoP_mono (show 0 ≤ n - 1 by zomega) (show n - 1 ≤ max n m - 1 by zomega)
  have h2 := twoP_mono (show 0 ≤ m - 1 by zomega) (show m - 1 ≤ max n m - 1 by zomega)
  have h3 := twoP_succ (show 0 ≤ max n m - 1 by zomega)
  rw [show max n m - 1 + 1 = max n m + 1 - 1 by zomega] at h3
  apply is_sgn_range (by zomega) <;> zomega

theorem sub_sgn' {n m : Z} {i j : Integers.Int} (hn : 0 < n) (hm : 0 < m)
    (hi : IsSgn n i) (hj : IsSgn m j) : IsSgn (max m n + 1) (Integers.Int.sub i j) := by
  rw [Int.max_comm]; exact sub_sgn hn hm hi hj

end

section
variable {bc : BlockClassification}

local macro "arith_side" : tactic =>
  `(tactic| first
    | assumption
    | exact usize_pos _
    | exact ssize_pos _
    | exact is_uns_usize _
    | exact is_sgn_ssize _
    | (apply is_uns_sgn (by assumption) (by zomega))
    | zomega)

local macro "add_close" : tactic =>
  `(tactic| first
    | constructor
    | exact vmatch_uns_undef _ _
    | exact vmatch_sgn_undef _ _
    | (apply vmatch_uns; first
        | (apply add_uns <;> arith_side)
        | (apply add_uns' <;> arith_side))
    | (apply vmatch_sgn; first
        | (apply add_sgn <;> arith_side)
        | (apply add_sgn' <;> arith_side)))

local macro "sub_close" : tactic =>
  `(tactic| first
    | exact vmatch_sgn_undef _ _
    | (apply vmatch_sgn; first
        | (apply sub_sgn <;> arith_side)
        | (apply sub_sgn' <;> arith_side)
        | (apply sub_uns <;> arith_side))
    | constructor)

set_option maxHeartbeats 4000000 in
theorem add_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.add v w) (add x y) := by
  cases h1 <;> cases h2 <;> delta add <;> dsimp only <;>
    simp only [Val.add, Archi.ptr64, if_true, ntop2] <;> add_close


set_option maxHeartbeats 4000000 in
theorem sub_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.sub v w) (sub x y) := by
  cases h1 <;> cases h2 <;> delta sub <;> dsimp only <;>
    simp only [Val.sub, Archi.ptr64, if_true, ntop2] <;> sub_close

end

end ValueDomain
end CC
