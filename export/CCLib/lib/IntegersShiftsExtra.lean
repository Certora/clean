/-
  Shift lemmas of `lib/Integers.v` used by the correctness proof of
  instruction selection (`aarch64/SelectOpproof.v`) that the generic
  `Integers*` files do not provide: `Int.shru_shl`, `Int.shr_shl`,
  `Int.shru_zero_ext`, `Int.shru_zero_ext_0`, `Int.shr_sign_ext`, together
  with small facts about shift amounts.

  Shift amounts are stated with `BitVec.toNat` (`Int.unsigned` as a `Nat`),
  and the width arguments of `zero_ext`/`sign_ext` are `Nat`s, as in the rest
  of the port.
-/
import CCLib.lib.IntegersPow2
namespace CC.Integers.Int

theorem toNat_lt_of_ltu {y : Int} (h : ltu y iwordsize = true) : y.toNat < 32 := by
  have := (ltu_iff _ _).mp h
  have e : unsigned iwordsize = 32 := by decide
  rw [e] at this
  have : (y.toNat : _root_.Int) < 32 := this
  omega

theorem sub_toNat {y z : Int} (h : z.toNat ≤ y.toNat) : (sub y z).toNat = y.toNat - z.toNat := by
  show (y - z).toNat = _
  rw [BitVec.toNat_sub]
  have := y.isLt; have := z.isLt
  rw [show 2 ^ 32 - z.toNat + y.toNat = (y.toNat - z.toNat) + 2 ^ 32 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem ltu_toNat (y z : Int) : ltu z y = decide (z.toNat < y.toNat) := by
  rw [ltu_def]; simp only [decide_eq_decide]
  show ((z.toNat : _root_.Int) < (y.toNat : _root_.Int)) ↔ _
  omega

/-- `Int.shru_shl` -/
theorem shru_shl (x y z : Int) (hy : ltu y iwordsize = true) (hz : ltu z iwordsize = true) :
    shru (shl x y) z =
      if ltu z y then shl (zero_ext (32 - y.toNat) x) (sub y z)
      else zero_ext (32 - z.toNat) (shru x (sub z y)) := by
  have hy' := toNat_lt_of_ltu hy
  have hz' := toNat_lt_of_ltu hz
  rw [ltu_toNat]
  apply same_bits_eq; intro i hi
  by_cases hc : z.toNat < y.toNat
  · rw [if_pos (decide_eq_true hc), bits_shru _ _ hi, bits_shl _ _ hi, sub_toNat (by omega)]
    by_cases h1 : i + z.toNat < 32
    · rw [if_pos h1, bits_shl _ _ h1]
      by_cases h2 : i + z.toNat < y.toNat
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega), bits_zero_ext]
        rw [show i - (y.toNat - z.toNat) = i + z.toNat - y.toNat by omega]
        simp; omega
    · rw [if_neg h1, if_neg (by omega), bits_zero_ext]; simp; omega
  · rw [if_neg (by simpa using hc), bits_zero_ext, bits_shru _ _ hi, bits_shru _ _ hi, sub_toNat (by omega)]
    by_cases h1 : i + z.toNat < 32
    · rw [if_pos h1, bits_shl _ _ h1, if_neg (by omega), if_pos (by omega)]
      simp only [decide_eq_true (show i < 32 - z.toNat by omega), Bool.true_and]
      congr 1; omega
    · rw [if_neg h1]; simp; omega

end CC.Integers.Int
namespace CC.Integers.Int

/-- `Int.shr_shl` -/
theorem shr_shl (x y z : Int) (hy : ltu y iwordsize = true) (hz : ltu z iwordsize = true) :
    shr (shl x y) z =
      if ltu z y then shl (sign_ext (32 - y.toNat) x) (sub y z)
      else sign_ext (32 - z.toNat) (shr x (sub z y)) := by
  have hy' := toNat_lt_of_ltu hy
  have hz' := toNat_lt_of_ltu hz
  rw [ltu_toNat]
  apply same_bits_eq; intro i hi
  rw [bits_shr _ _ hi]
  by_cases hc : z.toNat < y.toNat
  · rw [if_pos (decide_eq_true hc), bits_shl _ _ hi, sub_toNat (by omega)]
    by_cases h1 : i + z.toNat < 32
    · rw [if_pos h1, bits_shl _ _ h1]
      by_cases h2 : i + z.toNat < y.toNat
      · rw [if_pos h2, if_pos (show i < y.toNat - z.toNat by omega)]
      · rw [if_neg h2, if_neg (show ¬ i < y.toNat - z.toNat by omega),
          bits_sign_ext (by omega) _ (by omega),
          if_pos (show i - (y.toNat - z.toNat) < 32 - y.toNat by omega)]
        congr 1; omega
    · rw [if_neg h1, bits_shl _ _ (by omega), if_neg (show ¬ 32 - 1 < y.toNat by omega),
        if_neg (show ¬ i < y.toNat - z.toNat by omega),
        bits_sign_ext (by omega) _ (by omega),
        if_neg (show ¬ i - (y.toNat - z.toNat) < 32 - y.toNat by omega)]
      congr 1; omega
  · rw [if_neg (show ¬ decide (z.toNat < y.toNat) = true by simpa using hc),
      bits_sign_ext (by omega) _ hi]
    by_cases h1 : i + z.toNat < 32
    · rw [if_pos h1, bits_shl _ _ h1, if_neg (show ¬ i + z.toNat < y.toNat by omega),
        if_pos (show i < 32 - z.toNat by omega),
        bits_shr _ _ hi, sub_toNat (by omega), if_pos (show i + (z.toNat - y.toNat) < 32 by omega)]
      congr 1; omega
    · rw [if_neg h1, bits_shl _ _ (by omega), if_neg (show ¬ 32 - 1 < y.toNat by omega),
        if_neg (show ¬ i < 32 - z.toNat by omega),
        bits_shr _ _ (by omega), sub_toNat (by omega),
        if_pos (show 32 - z.toNat - 1 + (z.toNat - y.toNat) < 32 by omega)]
      congr 1; omega

/-- `Int.shru_zero_ext` -/
theorem shru_zero_ext (x n : Int) (s : Nat) :
    shru (zero_ext (s + n.toNat) x) n = zero_ext s (shru x n) := by
  apply same_bits_eq; intro i hi
  rw [bits_shru _ _ hi, bits_zero_ext, bits_zero_ext, bits_shru _ _ hi]
  by_cases h1 : i + n.toNat < 32
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : i < s
    · simp [h2, show i + n.toNat < s + n.toNat by omega]
    · simp [h2, show ¬ (i + n.toNat < s + n.toNat) by omega]
  · rw [if_neg h1, if_neg h1]; simp

/-- `Int.shru_zero_ext_0` -/
theorem shru_zero_ext_0 (x n : Int) (s : Nat) (h : s ≤ n.toNat) :
    shru (zero_ext s x) n = zero := by
  apply same_bits_eq; intro i hi
  rw [bits_shru _ _ hi]
  have hz : testbit zero i = false := by
    show (0 : BitVec 32).getLsbD i = false; simp
  rw [hz]
  split
  · rw [bits_zero_ext]; simp; omega
  · rfl

/-- `Int.shr_sign_ext` -/
theorem shr_sign_ext (x n : Int) (s : Nat) (hs : 0 < s) (h : s + n.toNat < 32) :
    shr (sign_ext (s + n.toNat) x) n = sign_ext s (shr x n) := by
  apply same_bits_eq; intro i hi
  rw [bits_shr _ _ hi, bits_sign_ext hs _ hi]
  by_cases h2 : i < s
  · rw [if_pos h2, bits_shr _ _ hi, if_pos (show i + n.toNat < 32 by omega),
      bits_sign_ext (by omega) _ (by omega), if_pos (show i + n.toNat < s + n.toNat by omega)]
  · rw [if_neg h2, bits_shr _ _ (by omega), if_pos (show s - 1 + n.toNat < 32 by omega)]
    by_cases h1 : i + n.toNat < 32
    · rw [if_pos h1, bits_sign_ext (by omega) _ h1,
        if_neg (show ¬ i + n.toNat < s + n.toNat by omega)]
      congr 1; omega
    · rw [if_neg h1, bits_sign_ext (by omega) _ (by omega),
        if_neg (show ¬ 32 - 1 < s + n.toNat by omega)]
      congr 1; omega

end CC.Integers.Int
namespace CC.Integers.Int

/-- `Op.mk_amount32_eq` (arithmetic part): `zero_ext 5 n = n` for a valid shift amount. -/
theorem zero_ext_5_of_ltu {n : Int} (h : ltu n iwordsize = true) : zero_ext 5 n = n := by
  have hn := toNat_lt_of_ltu h
  apply same_bits_eq; intro i hi
  rw [bits_zero_ext]
  by_cases h5 : i < 5
  · simp [h5]
  · simp only [decide_eq_false h5, Bool.false_and]
    show false = n.getLsbD i
    rw [BitVec.getLsbD, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (show 32 ≤ 2 ^ i from Nat.le_trans (by decide : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by decide) (by omega))))]

end CC.Integers.Int

namespace CC.Integers

/-- `Z_one_bits` with exactly two one bits. -/
theorem Z_one_bits_double {n : Nat} {x i j1 j2 : Z} (h0 : 0 ≤ x) (h1 : x < 2 ^ n)
    (h : Z_one_bits n x i = [j1, j2]) :
    ∃ m1 m2 : Nat, j1 = i + m1 ∧ j2 = i + m2 ∧ m1 < n ∧ m2 < n ∧ x = 2 ^ m1 + 2 ^ m2 := by
  induction n generalizing x i with
  | zero => simp [Z_one_bits] at h
  | succ n ih =>
    have hp : (2 : Z) ^ (n + 1) = 2 ^ n * 2 := Int.pow_succ 2 n
    simp only [Z_one_bits] at h
    split at h
    · next hx =>
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨m, hj, hm, hxm⟩ := Z_one_bits_single (n := n) (x := x / 2) (by zomega) (by zomega) (by simpa using h)
      refine ⟨0, m + 1, by zomega, by zomega, by omega, by omega, ?_⟩
      have : (2 : Z) ^ 0 = 1 := rfl
      rw [Int.pow_succ]; zomega
    · next hx =>
      obtain ⟨m1, m2, hj1, hj2, hm1, hm2, hxm⟩ :=
        ih (x := x / 2) (i := i + 1) (by zomega) (by zomega) h
      refine ⟨m1 + 1, m2 + 1, by zomega, by zomega, by omega, by omega, ?_⟩
      rw [Int.pow_succ, Int.pow_succ]; zomega

namespace Int

theorem repr_toNat_small {k : Nat} (h : k < 32) : (repr (k : Z) : Int).toNat = k := by
  have := unsigned_repr (z := (k : Z)) (by zomega) (by
    have : @Eq _root_.Int max_unsigned (2 ^ 32 - 1) := by decide
    zomega)
  have e : ((repr (k : Z) : Int).toNat : _root_.Int) = k := this
  zomega

theorem eq_repr_two_pow {x : Int} {m : Nat} (h : unsigned x = 2 ^ m) : x = repr (2 ^ m) := by
  rw [← h, repr_unsigned]

/-- `Int.one_bits` with a single one bit: multiplication by `x` is a left shift. -/
theorem one_bits_single {x i : Int} (h : one_bits x = [i]) :
    ltu i iwordsize = true ∧ ∀ y, mul y x = shl y i := by
  have hr := unsigned_range x
  have hm : modulus = (2 ^ 32 : _root_.Int) := by decide
  rw [hm] at hr
  have h' : (Z_one_bits 32 (unsigned x) 0).map repr = [i] := h
  cases hz : Z_one_bits 32 (unsigned x) 0 with
  | nil => rw [hz] at h'; cases h'
  | cons k t =>
    cases t with
    | cons _ _ => rw [hz] at h'; simp at h'
    | nil =>
      rw [hz] at h'
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h'
      subst h'
      obtain ⟨m, rfl, hm, hx⟩ := Z_one_bits_single hr.1 hr.2 hz
      rw [Int.zero_add, show (repr (m : Z) : Int) = repr ((m : Nat) : Z) from rfl]
      have ht := repr_toNat_small hm
      refine ⟨ltu_iw_of_toNat' (by omega), fun y => ?_⟩
      rw [shl_mul_two_p, ht, eq_repr_two_pow hx]
where
  ltu_iw_of_toNat' {y : Int} (h : y.toNat < 32) : ltu y iwordsize = true := by
    rw [ltu_toNat]; exact decide_eq_true (by show y.toNat < (32 : BitVec 32).toNat; simp; omega)

/-- `Int.one_bits` with two one bits: multiplication by `x` is a sum of two left shifts. -/
theorem one_bits_double {x i j : Int} (h : one_bits x = [i, j]) :
    ltu i iwordsize = true ∧ ltu j iwordsize = true ∧
      ∀ y, mul y x = add (shl y i) (shl y j) := by
  have hr := unsigned_range x
  have hm : modulus = (2 ^ 32 : _root_.Int) := by decide
  rw [hm] at hr
  have h' : (Z_one_bits 32 (unsigned x) 0).map repr = [i, j] := h
  cases hz : Z_one_bits 32 (unsigned x) 0 with
  | nil => rw [hz] at h'; cases h'
  | cons k t =>
    cases t with
    | nil => rw [hz] at h'; simp at h'
    | cons k2 t =>
      cases t with
      | cons _ _ => rw [hz] at h'; simp at h'
      | nil =>
        rw [hz] at h'
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h'
        obtain ⟨rfl, rfl⟩ := h'
        obtain ⟨m1, m2, rfl, rfl, hm1, hm2, hx⟩ := Z_one_bits_double hr.1 hr.2 hz
        simp only [Int.zero_add]
        have ht1 := repr_toNat_small hm1
        have ht2 := repr_toNat_small hm2
        refine ⟨one_bits_single.ltu_iw_of_toNat' (by omega),
          one_bits_single.ltu_iw_of_toNat' (by omega), fun y => ?_⟩
        rw [shl_mul_two_p, shl_mul_two_p, ht1, ht2, ← mul_add_distr_r, ← repr_add, ← hx,
          repr_unsigned]

end Int
end CC.Integers

namespace CC.Integers.Int

/-- `Int.shl_zero_ext` -/
theorem shl_zero_ext (x m : Int) (n : Nat) (h : m.toNat ≤ n) :
    zero_ext n (shl x m) = shl (zero_ext (n - m.toNat) x) m := by
  apply same_bits_eq; intro i hi
  rw [bits_zero_ext, bits_shl _ _ hi, bits_shl _ _ hi]
  by_cases h1 : i < m.toNat
  · simp [h1]
  · rw [if_neg h1, if_neg h1, bits_zero_ext]
    by_cases h2 : i < n
    · simp [h2, show i - m.toNat < n - m.toNat by omega]
    · simp [h2, show ¬ i - m.toNat < n - m.toNat by omega]

/-- `Int.shl_sign_ext` -/
theorem shl_sign_ext (x m : Int) (n : Nat) (h : m.toNat < n) :
    sign_ext n (shl x m) = shl (sign_ext (n - m.toNat) x) m := by
  apply same_bits_eq; intro i hi
  rw [bits_sign_ext (by omega) _ hi, bits_shl _ _ hi]
  by_cases h2 : i < n
  · rw [if_pos h2, bits_shl _ _ hi]
    by_cases h1 : i < m.toNat
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, bits_sign_ext (by omega) _ (by omega),
        if_pos (show i - m.toNat < n - m.toNat by omega)]
  · rw [if_neg h2, bits_shl _ _ (by omega), if_neg (show ¬ n - 1 < m.toNat by omega),
      if_neg (show ¬ i < m.toNat by omega), bits_sign_ext (by omega) _ (by omega),
      if_neg (show ¬ i - m.toNat < n - m.toNat by omega)]
    congr 1; omega

/-- `Int.or_ror` -/
theorem or_ror (z x y : Int) (hx : x.toNat < 32) (hy : y.toNat < 32)
    (h : add x y = iwordsize) :
    ror z y = or (shl z x) (shru z y) := by
  have hs : x.toNat + y.toNat = 32 := by
    have := congrArg BitVec.toNat h
    simp [add, iwordsize, MI.add, MI.iwordsize] at this
    omega
  simp only [ror, MI.ror, or, MI.or, shl, MI.shl, shru, MI.shru]
  simp
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_rotateRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  rw [Nat.mod_eq_of_lt hy]
  by_cases hc : i < 32 - y.toNat
  · simp [hc, show i < x.toNat by omega]
  · simp [hc, show ¬ i < x.toNat by omega, show i - (32 - y.toNat) = i - x.toNat by omega,
      BitVec.getLsbD_of_ge z (y.toNat + i) (by omega)]

end CC.Integers.Int
