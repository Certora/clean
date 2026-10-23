/-
  Theorems of `lib/Integers.v`, part 4: powers of two (`is_power2`,
  `mul_pow2`, `divu_pow2`, `modu_and`), `zero_ext_and`, rotations
  (`rol_rol`, `rol_and`, `rolm_zero`, `or_rolm`, `rolm_rolm`, `shl_rolm`,
  `shru_rolm`) and signed division by a power of two (`shrx_shr`,
  `shrx_shr_2`, `shrx_carry`).

  Generic in the word size `w` (namespace `CC.Integers.MI`), then restated
  for `Int` and `Int64` under CompCert's names at the end of the file.
-/
import CCLib.lib.IntegersInt
import CCLib.lib.IntegersInt64

namespace CC
namespace Integers

/-! ## A fact about natural numbers -/

/-- A positive `n` with `n &&& (n - 1) = 0` is `2 ^ log2 n`. -/
theorem nat_eq_two_pow_log2 {n : Nat} (h0 : 0 < n) (h : n &&& (n - 1) = 0) :
    n = 2 ^ n.log2 := by
  have h1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp h0)
  have h2 := @Nat.lt_log2_self n
  apply Classical.byContradiction
  intro hne
  have h3 : 2 ^ n.log2 ≤ n - 1 := by omega
  have h4 : n - 1 < 2 ^ (n.log2 + 1) := by omega
  have e1 := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h1 h2
  have e2 := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h3 h4
  have := Nat.testBit_and n (n - 1) n.log2
  rw [h, Nat.zero_testBit, e1, e2] at this
  cases this


/-! ## Truncating vs. flooring division by a positive integer -/

theorem tdiv_eq_ediv_add {a d : _root_.Int} (hd : 0 < d) :
    a.tdiv d = a / d + (if a < 0 ∧ a % d ≠ 0 then 1 else 0) := by
  by_cases ha : 0 ≤ a
  · rw [Int.tdiv_eq_ediv_of_nonneg ha, if_neg (by omega)]; omega
  · have hb : 0 ≤ -a := by omega
    have e : a.tdiv d = -((-a) / d) := by
      have := Int.neg_tdiv (-a) d
      rw [Int.neg_neg, Int.tdiv_eq_ediv_of_nonneg hb] at this
      exact this
    rw [e]
    have hb1 := Int.emod_nonneg (-a) (by omega : d ≠ 0)
    have hb2 := Int.emod_lt_of_pos (-a) hd
    have hb3 := Int.emod_add_mul_ediv (-a) d
    by_cases hr : (-a) % d = 0
    · have := (Int.ediv_emod_unique (a := a) (r := 0) (q := -((-a) / d)) hd).mpr
        ⟨by rw [Int.mul_neg]; omega, by omega, hd⟩
      rw [this.1, if_neg (by omega)]; omega
    · have := (Int.ediv_emod_unique (a := a) (r := d - (-a) % d) (q := -((-a) / d) - 1) hd).mpr
        ⟨by rw [Int.mul_sub, Int.mul_neg]; omega, by omega, by omega⟩
      rw [this.1, if_pos ⟨by omega, by omega⟩]; omega

theorem add_pred_ediv {a d : _root_.Int} (hd : 0 < d) :
    (a + d - 1) / d = a / d + (if a % d ≠ 0 then 1 else 0) := by
  have h1 := Int.emod_nonneg a (by omega : d ≠ 0)
  have h2 := Int.emod_lt_of_pos a hd
  have h3 := Int.emod_add_mul_ediv a d
  by_cases hr : a % d = 0
  · have := (Int.ediv_emod_unique (a := a + d - 1) (r := d - 1) (q := a / d) hd).mpr
      ⟨by omega, by omega, by omega⟩
    rw [this.1, if_neg (by omega)]; omega
  · have := (Int.ediv_emod_unique (a := a + d - 1) (r := a % d - 1) (q := a / d + 1) hd).mpr
      ⟨by rw [Int.mul_add]; omega, by omega, by omega⟩
    rw [this.1, if_pos hr]

/-- `x % w` for `x < 3 * w`, without division. -/
theorem nat_mod_lt3 {x w : Nat} (h : x < 3 * w) :
    x % w = if x < w then x else if x < 2 * w then x - w else x - 2 * w := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega)]
    split
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

namespace MI

variable {w : Nat}

/-! ## `is_power2` -/

/-- `Int.is_power2_rng` and `Int.is_power2_correct`, combined. -/
theorem is_power2_spec {n logn : BitVec w} (h : is_power2 n = some logn) :
    logn.toNat < w ∧ n.toNat = 2 ^ logn.toNat := by
  simp only [is_power2, Option.map_eq_some_iff, Z_is_power2] at h
  obtain ⟨z, hz, rfl⟩ := h
  split at hz
  · next hc =>
    cases hz
    have hn : (unsigned n).toNat = n.toNat := by simp [unsigned]
    rw [hn] at hc ⊢
    have hpos : 0 < n.toNat := by have := hc.1; simp [unsigned] at this; omega
    have hpow := nat_eq_two_pow_log2 hpos hc.2
    have hlt : n.toNat.log2 < w :=
      (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hpos)).mpr n.isLt
    have hlw : n.toNat.log2 < 2 ^ w := Nat.lt_of_lt_of_le hlt (Nat.le_of_lt (Nat.lt_two_pow_self))
    have ht : (repr ((n.toNat.log2 : Nat) : Z) : BitVec w).toNat = n.toNat.log2 := by
      simp only [repr, BitVec.toNat_ofInt]
      rw [Int.toNat_emod (by omega) (by omega)]
      simp only [Int.toNat_natCast]
      exact Nat.mod_eq_of_lt hlw
    rw [ht]
    exact ⟨hlt, hpow⟩
  · cases hz

theorem toNat_iwordsize : (iwordsize w).toNat = w := by
  simp only [iwordsize, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt Nat.lt_two_pow_self

theorem ltu_iwordsize_iff (y : BitVec w) : ltu y (iwordsize w) = true ↔ y.toNat < w := by
  simp only [ltu, BitVec.ult, decide_eq_true_eq, toNat_iwordsize]

/-- `Int.is_power2_range` -/
theorem is_power2_range {n logn : BitVec w} (h : is_power2 n = some logn) :
    ltu logn (iwordsize w) = true :=
  (ltu_iwordsize_iff _).mpr (is_power2_spec h).1

/-- `Int.mul_pow2` -/
theorem mul_pow2 (x : BitVec w) {n logn : BitVec w} (h : is_power2 n = some logn) :
    mul x n = shl x logn := by
  apply BitVec.eq_of_toNat_eq
  simp only [mul, shl, BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    (is_power2_spec h).2]

/-- `Int.divu_pow2` -/
theorem divu_pow2 (x : BitVec w) {n logn : BitVec w} (h : is_power2 n = some logn) :
    divu x n = shru x logn := by
  apply BitVec.eq_of_toNat_eq
  simp only [divu, shru, BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    (is_power2_spec h).2]

/-- `Int.modu_and` -/
theorem modu_and (x : BitVec w) {n logn : BitVec w} (h : is_power2 n = some logn) :
    modu x n = and x (sub n one) := by
  obtain ⟨hlt, hn⟩ := is_power2_spec h
  have hw : 0 < w := by omega
  apply BitVec.eq_of_toNat_eq
  have h1 : (one : BitVec w).toNat = 1 := by
    simp [one]; omega
  have hsub : (sub n one).toNat = 2 ^ logn.toNat - 1 := by
    simp only [sub]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn, h1]; exact Nat.one_le_two_pow), hn, h1]
  simp only [modu, and, BitVec.toNat_umod, BitVec.toNat_and, hsub, hn,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ## `zero_ext` as a mask -/

theorem testbit_repr_two_pow_sub_one (n i : Nat) (hi : i < w) :
    testbit (repr ((2 : Z) ^ n - 1) : BitVec w) i = decide (i < n) := by
  have : ((2 : Z) ^ n - 1) = ((2 ^ n - 1 : Nat) : Z) := by
    rw [Int.natCast_sub Nat.one_le_two_pow, Int.natCast_pow]; rfl
  rw [this]
  simp only [testbit, repr, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    hi, decide_true, Bool.true_and]

/-- `Int.zero_ext_and` -/
theorem zero_ext_and (n : Nat) (x : BitVec w) :
    zero_ext n x = and x (repr ((2 : Z) ^ n - 1)) := by
  apply same_bits_eq
  intro i hi
  rw [bits_and, testbit_repr_two_pow_sub_one n i hi, bits_zero_ext]
  exact Bool.and_comm _ _

/-! ## Rotations -/

/-- Bit `i` of a left rotation, for `i < w`. -/
theorem testbit_rol (x y : BitVec w) {i : Nat} (hi : i < w) :
    testbit (rol x y) i = testbit x ((i + (w - y.toNat % w)) % w) := by
  have hw : 0 < w := by omega
  have hwne : w ≠ 0 := by omega
  simp only [rol, hwne, if_false, testbit, BitVec.getLsbD_rotateLeft, Nat.mod_mod]
  have hr := Nat.mod_lt y.toNat hw
  generalize y.toNat % w = r at *
  by_cases h : i < r
  · simp only [h, decide_true, cond_true]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [h, decide_false, cond_false, hi, decide_true, Bool.true_and]
    congr 1
    rw [show i + (w - r) = (i - r) + w * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

/-- `Int.rol_zero` is `rol_zero`; `Int.rol_and` -/
theorem rol_and (x y n : BitVec w) : rol (and x y) n = and (rol x n) (rol y n) := by
  apply same_bits_eq
  intro i hi
  rw [testbit_rol _ _ hi, bits_and, bits_and, testbit_rol _ _ hi, testbit_rol _ _ hi]

/-- `Int.rol_rol`. Rocq's side condition `Z.divide zwordsize modulus` is the
    hypothesis `w ∣ 2 ^ w`. -/
theorem rol_rol (hdiv : w ∣ 2 ^ w) (x n m : BitVec w) :
    rol (rol x n) m = rol x (modu (add n m) (iwordsize w)) := by
  apply same_bits_eq
  intro i hi
  have hw : 0 < w := by omega
  rw [testbit_rol _ _ hi, testbit_rol _ _ (Nat.mod_lt _ hw), testbit_rol _ _ hi]
  congr 1
  have hmod : (modu (add n m) (iwordsize w)).toNat % w = (n.toNat % w + m.toNat % w) % w := by
    simp only [modu, add, BitVec.toNat_umod, BitVec.toNat_add, toNat_iwordsize, Nat.mod_mod]
    rw [Nat.mod_mod_of_dvd _ hdiv, Nat.add_mod]
  rw [hmod]
  have ha := Nat.mod_lt n.toNat hw
  have hb := Nat.mod_lt m.toNat hw
  generalize n.toNat % w = a at *
  generalize m.toNat % w = b at *
  rw [Nat.mod_add_mod, nat_mod_lt3 (x := a + b) (by omega)]
  by_cases hs : a + b < w
  · simp only [hs, if_true]
    rw [nat_mod_lt3 (x := i + (w - b) + (w - a)) (by omega),
      nat_mod_lt3 (x := i + (w - (a + b))) (by omega)]
    repeat' split
    all_goals omega
  · simp only [hs, if_false, show a + b < 2 * w by omega, if_true]
    rw [nat_mod_lt3 (x := i + (w - b) + (w - a)) (by omega),
      nat_mod_lt3 (x := i + (w - (a + b - w))) (by omega)]
    repeat' split
    all_goals omega

/-- `Int.rolm_zero` -/
theorem rolm_zero (x m : BitVec w) : rolm x zero m = and x m := by
  simp only [rolm, rol_zero]

/-- `Int.or_rolm` -/
theorem or_rolm (x n m1 m2 : BitVec w) :
    or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2) := by
  apply same_bits_eq
  intro i _
  simp only [rolm, bits_or, bits_and]
  cases testbit (rol x n) i <;> simp

/-- `Int.rolm_rolm` -/
theorem rolm_rolm (hdiv : w ∣ 2 ^ w) (x n1 m1 n2 m2 : BitVec w) :
    rolm (rolm x n1 m1) n2 m2 =
      rolm x (modu (add n1 n2) (iwordsize w)) (and (rol m1 n2) m2) := by
  simp only [rolm, rol_and, rol_rol hdiv]
  apply same_bits_eq
  intro i _
  simp only [bits_and, Bool.and_assoc]

/-- `Int.shl_rolm` -/
theorem shl_rolm (x n : BitVec w) (h : ltu n (iwordsize w) = true) :
    shl x n = rolm x n (shl mone n) := by
  rw [ltu_iwordsize_iff] at h
  apply same_bits_eq
  intro i hi
  rw [rolm, bits_and, testbit_rol _ _ hi, bits_shl _ _ hi, bits_shl _ _ hi, Nat.mod_eq_of_lt h]
  by_cases hin : i < n.toNat
  · simp [hin]
  · simp only [hin, if_false, bits_mone (show i - n.toNat < w by omega), Bool.and_true]
    congr 1
    rw [show i + (w - n.toNat) = (i - n.toNat) + w * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

/-- `Int.shru_rolm` -/
theorem shru_rolm (x n : BitVec w) (h : ltu n (iwordsize w) = true) :
    shru x n = rolm x (sub (iwordsize w) n) (shru mone n) := by
  rw [ltu_iwordsize_iff] at h
  have hsub : (sub (iwordsize w) n).toNat = w - n.toNat := by
    simp only [sub]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_iwordsize]; omega), toNat_iwordsize]
  apply same_bits_eq
  intro i hi
  rw [rolm, bits_and, testbit_rol _ _ hi, bits_shru _ _ hi, bits_shru _ _ hi, hsub]
  by_cases hin : i + n.toNat < w
  · simp only [hin, if_true, bits_mone hin, Bool.and_true]
    congr 1
    rw [nat_mod_lt3 (x := w - n.toNat) (by omega)]
    by_cases h0 : n.toNat = 0
    · simp only [show w - n.toNat = w by omega, Nat.lt_irrefl, if_false,
        show w < 2 * w by omega, if_true, Nat.sub_self, Nat.sub_zero]
      rw [nat_mod_lt3 (x := i + w) (by omega)]
      repeat' split
      all_goals omega
    · simp only [show w - n.toNat < w by omega, if_true]
      rw [nat_mod_lt3 (x := i + (w - (w - n.toNat))) (by omega)]
      repeat' split
      all_goals omega
  · simp [hin]


/-! ## Signed division by a power of two (`shrx`) -/

theorem ltu_repr_pred {y : BitVec w} (h : ltu y (repr ((w : Z) - 1)) = true) :
    y.toNat + 1 < w := by
  rw [ltu_def, decide_eq_true_eq, unsigned_repr_eq] at h
  have hy := unsigned_range y
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [modulus] at h; zomega
  · have hlt : (w : Z) < modulus w := by
      rw [modulus_eq]
      have := @Nat.lt_two_pow_self w
      have : ((w : Nat) : Z) < ((2 ^ w : Nat) : Z) := Int.ofNat_lt.mpr this
      rw [Int.natCast_pow] at this; exact this
    rw [Int.emod_eq_of_lt (by zomega) (by zomega)] at h
    simp only [unsigned] at h; zomega

/-- The facts about `shl one y`, `shr` and `divs` used by the `shrx` lemmas,
    for a shift amount `k = y.toNat` with `k + 1 < w`. -/
theorem shrx_setup {y : BitVec w} (hk : y.toNat + 1 < w) :
    signed (shl one y : BitVec w) = ((2 ^ y.toNat : Nat) : Z) ∧
    signed (sub (shl one y) one : BitVec w) = ((2 ^ y.toNat : Nat) : Z) - 1 ∧
    ((2 ^ y.toNat : Nat) : Z) * 2 ≤ half_modulus w ∧
    (∀ v : BitVec w, shr v y = repr (signed v / ((2 ^ y.toNat : Nat) : Z))) ∧
    (∀ x : BitVec w, divs x (shl one y) = repr ((signed x).tdiv ((2 ^ y.toNat : Nat) : Z))) := by
  have hw : 0 < w := by omega
  have hpowN : 2 ^ y.toNat * 2 ≤ 2 ^ (w - 1) := by
    rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hhalf : half_modulus w = ((2 ^ (w - 1) : Nat) : Z) := by
    rw [half_modulus_eq hw, Int.natCast_pow]; rfl
  have hpow : ((2 ^ y.toNat : Nat) : Z) * 2 ≤ half_modulus w := by
    rw [hhalf]; exact_mod_cast hpowN
  have hpos : 1 ≤ 2 ^ y.toNat := Nat.one_le_two_pow
  have hltw : 2 ^ y.toNat < 2 ^ w := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) (show w - 1 < w by omega)
    omega
  have hone : (one : BitVec w).toNat = 1 := by simp [one]; omega
  have hshl : (shl one y : BitVec w).toNat = 2 ^ y.toNat := by
    simp only [shl, BitVec.toNat_shiftLeft, hone, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt hltw
  have hsub : (sub (shl one y) one : BitVec w).toNat = 2 ^ y.toNat - 1 := by
    simp only [sub]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hshl, hone]; exact hpos), hshl, hone]
  refine ⟨?_, ?_, hpow, ?_, ?_⟩
  · rw [signed_eq_unsigned hw _ (by rw [unsigned, hshl, max_signed_eq]; zomega), unsigned, hshl]
  · rw [signed_eq_unsigned hw _ (by rw [unsigned, hsub, max_signed_eq]; zomega), unsigned, hsub]
    zomega
  · intro v
    rw [← repr_signed (shr v y)]
    congr 1
    simp only [signed, shr, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  · intro x
    rw [divs_signed]
    congr 2
    rw [signed_eq_unsigned hw _ (by rw [unsigned, hshl, max_signed_eq]; zomega), unsigned, hshl]

/-- `Int.shrx_shr` -/
theorem shrx_shr (x y : BitVec w) (hy : ltu y (repr ((w : Z) - 1)) = true) :
    shrx x y = shr (if lt x zero then add x (sub (shl one y) one) else x) y := by
  have hk := ltu_repr_pred hy
  have hw : 0 < w := by omega
  obtain ⟨_, hsub, hpow, hshr, hdivs⟩ := shrx_setup hk
  have hd : (0 : Z) < ((2 ^ y.toNat : Nat) : Z) := Int.ofNat_lt.mpr (Nat.two_pow_pos _)
  generalize ((2 ^ y.toNat : Nat) : Z) = d at *
  rw [shrx, hdivs, tdiv_eq_ediv_add hd]
  have hr := signed_range hw x
  by_cases hlt : lt x zero = true
  · rw [if_pos hlt]
    rw [lt_iff, signed_zero] at hlt
    rw [hshr, add_signed, hsub, signed_repr hw (by zomega) (by rw [max_signed_eq]; zomega)]
    rw [show signed x + (d - 1) = signed x + d - 1 by zomega, add_pred_ediv hd]
    congr 2
    by_cases h0 : signed x % d = 0 <;> simp [h0, hlt]
  · rw [if_neg hlt]
    rw [lt_iff, signed_zero] at hlt
    rw [hshr, if_neg (by zomega)]; congr 1; zomega

/-- `Int.shrx_carry` -/
theorem shrx_carry (x y : BitVec w) (hy : ltu y (repr ((w : Z) - 1)) = true) :
    shrx x y = add (shr x y) (shr_carry x y) := by
  have hk := ltu_repr_pred hy
  have hw : 0 < w := by omega
  obtain ⟨_, hsub, hpow, hshr, hdivs⟩ := shrx_setup hk
  -- `and x (2^k - 1)` is zero iff `2^k` divides `signed x`
  have hmask : (and x (sub (shl one y) one) = zero) ↔ signed x % ((2 ^ y.toNat : Nat) : Z) = 0 := by
    have hone : (one : BitVec w).toNat = 1 := by simp [one]; omega
    have hltw : 2 ^ y.toNat < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
    have hshl : (shl one y : BitVec w).toNat = 2 ^ y.toNat := by
      simp only [shl, BitVec.toNat_shiftLeft, hone, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt hltw
    have hsubN : (sub (shl one y) one : BitVec w).toNat = 2 ^ y.toNat - 1 := by
      simp only [sub]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hshl, hone]; exact Nat.one_le_two_pow),
        hshl, hone]
    have hand : (and x (sub (shl one y) one)).toNat = x.toNat % 2 ^ y.toNat := by
      simp only [and, BitVec.toNat_and, hsubN, Nat.and_two_pow_sub_one_eq_mod]
    have hdvd : (2 ^ y.toNat : Nat) ∣ 2 ^ w := Nat.pow_dvd_pow 2 (by omega)
    have hsu : signed x % ((2 ^ y.toNat : Nat) : Z) = ((x.toNat % 2 ^ y.toNat : Nat) : Z) := by
      rw [signed_eq hw]
      split
      · simp [unsigned]
      · simp only [unsigned, modulus_eq]
        obtain ⟨c, hc⟩ := hdvd
        rw [show (2 : Z) ^ w = ((2 ^ w : Nat) : Z) by rw [Int.natCast_pow]; rfl, hc,
          Int.natCast_mul, Int.sub_eq_add_neg, ← Int.mul_neg, Int.add_mul_emod_self_left]
        exact (Int.natCast_emod _ _).symm
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [hand] at this
      rw [hsu, this]; rfl
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [hand, show (zero : BitVec w).toNat = 0 from rfl]
      rw [hsu] at h; exact_mod_cast h
  have hd : (0 : Z) < ((2 ^ y.toNat : Nat) : Z) := Int.ofNat_lt.mpr (Nat.two_pow_pos _)
  generalize ((2 ^ y.toNat : Nat) : Z) = d at *
  rw [shrx, hdivs, tdiv_eq_ediv_add hd, hshr, shr_carry, add_signed]
  have hr := signed_range hw x
  have hq : min_signed w ≤ signed x / d ∧ signed x / d ≤ max_signed w := by
    by_cases hx : 0 ≤ signed x
    · have h1 : 0 ≤ signed x / d := Int.ediv_nonneg hx (by zomega)
      have h2 : signed x / d ≤ signed x := Int.ediv_le_self _ hx
      have := min_signed_neg hw; zomega
    · have h1 : signed x ≤ signed x / d := by
        rw [Int.le_ediv_iff_mul_le hd]
        have := Int.mul_le_mul_of_nonpos_left (a := signed x) (b := d) (c := 1) (by zomega) (by zomega)
        zomega
      have h2 : signed x / d < 0 := Int.ediv_neg_of_neg_of_pos (by zomega) hd
      have := max_signed_pos (w := w) hw; zomega
  rw [signed_repr hw hq.1 hq.2]
  have h1 : signed (one : BitVec w) = 1 := by
    have := half_modulus_pos hw
    rw [signed_eq_unsigned hw _ (by rw [unsigned_one hw, max_signed_eq]; zomega), unsigned_one hw]
  by_cases hneg : signed x < 0
  · have hlt : lt x zero = true := by rw [lt_iff, signed_zero]; exact hneg
    by_cases h0 : signed x % d = 0
    · have hz : eq (and x (sub (shl one y) one)) zero = true := by
        rw [eq_spec]; exact hmask.mpr h0
      rw [hlt, hz]
      simp only [Bool.not_true, Bool.and_false]
      rw [if_neg Bool.false_ne_true, if_neg (fun h => h.2 h0), signed_zero]
    · have hz : eq (and x (sub (shl one y) one)) zero = false := by
        rw [Bool.eq_false_iff]; intro h; rw [eq_spec] at h; exact h0 (hmask.mp h)
      rw [hlt, hz]
      simp only [Bool.not_false, Bool.and_true]
      rw [if_pos trivial, if_pos ⟨hneg, h0⟩, h1]
  · have hlt : lt x zero = false := by
      rw [Bool.eq_false_iff]; intro h; rw [lt_iff, signed_zero] at h; exact hneg h
    rw [hlt]
    simp only [Bool.false_and]
    rw [if_neg Bool.false_ne_true, if_neg (fun h => hneg h.1), signed_zero]

/-- `shr x (w - 1)` is `mone` for negative `x` and `zero` otherwise. -/
theorem shr_wordsize_pred (hw : 0 < w) (x : BitVec w) :
    shr x (repr ((w : Z) - 1)) = if lt x zero then mone else zero := by
  have hn : (repr ((w : Z) - 1) : BitVec w).toNat = w - 1 := by
    have h := unsigned_repr_eq (w := w) ((w : Z) - 1)
    have hlt : (w : Z) < modulus w := by
      rw [modulus_eq]
      have : ((w : Nat) : Z) < ((2 ^ w : Nat) : Z) := Int.ofNat_lt.mpr Nat.lt_two_pow_self
      rw [Int.natCast_pow] at this; exact this
    have hlt' : (w : Z) < 2 ^ w := hlt
    rw [Int.emod_eq_of_lt (by zomega) (by rw [modulus_eq]; zomega)] at h
    simp only [unsigned] at h; zomega
  have hmsb : lt x zero = x.msb := by
    rw [lt_def, BitVec.msb_eq_toInt, signed_zero, signed]
  apply same_bits_eq
  intro i hi
  have hidx : (if i + (w - 1) < w then i + (w - 1) else w - 1) = w - 1 := by split <;> omega
  rw [bits_shr _ _ hi, hn, hidx, hmsb, BitVec.msb_eq_getLsbD_last]
  cases h : x.getLsbD (w - 1)
  · simp [testbit, h, zero]
  · simp [testbit, h, mone, hi]

/-- `Int.shrx_shr_2` -/
theorem shrx_shr_2 (x y : BitVec w) (hy : ltu y (repr ((w : Z) - 1)) = true) :
    shrx x y = shr (add x (shru (shr x (repr ((w : Z) - 1))) (sub (iwordsize w) y))) y := by
  have hk := ltu_repr_pred hy
  have hw : 0 < w := by omega
  rw [shrx_shr x y hy, shr_wordsize_pred hw]
  have hsubw : (sub (iwordsize w) y).toNat = w - y.toNat := by
    simp only [sub]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_iwordsize]; omega), toNat_iwordsize]
  split
  · congr 2
    have hone : (one : BitVec w).toNat = 1 := by simp [one]; omega
    have hltw : 2 ^ y.toNat < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
    have hshl : (shl one y : BitVec w).toNat = 2 ^ y.toNat := by
      simp only [shl, BitVec.toNat_shiftLeft, hone, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt hltw
    apply BitVec.eq_of_toNat_eq
    simp only [sub]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hshl, hone]; exact Nat.one_le_two_pow),
      hshl, hone]
    have hsubw' : (iwordsize w - y).toNat = w - y.toNat := hsubw
    simp only [shru, BitVec.toNat_ushiftRight, hsubw', mone, BitVec.toNat_allOnes,
      Nat.shiftRight_eq_div_pow]
    have hp : 2 ^ w = 2 ^ y.toNat * 2 ^ (w - y.toNat) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hp]
    have h1 : 0 < 2 ^ (w - y.toNat) := Nat.two_pow_pos _
    have h2 : 1 ≤ 2 ^ y.toNat := Nat.one_le_two_pow
    symm
    rw [Nat.div_eq_iff h1]
    have : 2 ^ (w - y.toNat) ≤ 2 ^ y.toNat * 2 ^ (w - y.toNat) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [Nat.sub_mul, Nat.one_mul]
    omega
  · rw [shru_zero_l, add_zero]


/-- `Int.divs_one` -/
theorem divs_one (x : BitVec w) : divs x one = x := by
  simp only [divs, one]; exact BitVec.sdiv_one

/-- `Int.shrx_zero` -/
theorem shrx_zero (x : BitVec w) : shrx x zero = x := by
  rw [shrx, shl_zero, divs_one]

end MI

/-! ## `Z_one_bits` with a single one bit -/

theorem Z_one_bits_nil {n : Nat} {x i : Z} (h0 : 0 ≤ x) (h1 : x < 2 ^ n)
    (h : Z_one_bits n x i = []) : x = 0 := by
  induction n generalizing x i with
  | zero => have : (2 : Z) ^ 0 = 1 := rfl; zomega
  | succ n ih =>
    simp only [Z_one_bits] at h
    split at h
    · cases h
    · next hx =>
      have hp : (2 : Z) ^ (n + 1) = 2 ^ n * 2 := Int.pow_succ 2 n
      have := ih (x := x / 2) (i := i + 1) (by zomega) (by zomega) h
      zomega

theorem Z_one_bits_single {n : Nat} {x i j : Z} (h0 : 0 ≤ x) (h1 : x < 2 ^ n)
    (h : Z_one_bits n x i = [j]) : ∃ m : Nat, j = i + m ∧ m < n ∧ x = 2 ^ m := by
  induction n generalizing x i with
  | zero => simp [Z_one_bits] at h
  | succ n ih =>
    have hp : (2 : Z) ^ (n + 1) = 2 ^ n * 2 := Int.pow_succ 2 n
    simp only [Z_one_bits] at h
    split at h
    · next hx =>
      simp only [List.cons.injEq] at h
      have := Z_one_bits_nil (x := x / 2) (by zomega) (by zomega) h.2
      refine ⟨0, by zomega, by omega, ?_⟩
      have : (2 : Z) ^ 0 = 1 := rfl
      zomega
    · next hx =>
      obtain ⟨m, hj, hm, hxm⟩ := ih (x := x / 2) (i := i + 1) (by zomega) (by zomega) h
      refine ⟨m + 1, by zomega, by omega, ?_⟩
      rw [Int.pow_succ]; zomega

namespace Int

theorem is_power2_range {n logn : Int} (h : is_power2 n = some logn) :
    ltu logn iwordsize = true := MI.is_power2_range h

/-- `Int.is_power2_correct` -/
theorem is_power2_correct {n logn : Int} (h : is_power2 n = some logn) :
    unsigned n = (2 : Z) ^ (unsigned logn).toNat := by
  have := (MI.is_power2_spec h).2
  simp only [unsigned, MI.unsigned, Int.toNat_natCast]
  rw [this, Int.natCast_pow]; rfl

theorem mul_pow2 (x : Int) {n logn : Int} (h : is_power2 n = some logn) :
    mul x n = shl x logn := MI.mul_pow2 x h

theorem divu_pow2 (x : Int) {n logn : Int} (h : is_power2 n = some logn) :
    divu x n = shru x logn := MI.divu_pow2 x h

theorem modu_and (x : Int) {n logn : Int} (h : is_power2 n = some logn) :
    modu x n = and x (sub n one) := MI.modu_and x h

theorem zero_ext_and (n : Nat) (x : Int) :
    zero_ext n x = and x (repr ((2 : Z) ^ n - 1)) := MI.zero_ext_and n x

theorem rol_and (x y n : Int) : rol (and x y) n = and (rol x n) (rol y n) := MI.rol_and x y n

theorem rol_rol (x n m : Int) : rol (rol x n) m = rol x (modu (add n m) iwordsize) :=
  MI.rol_rol (by decide) x n m

theorem rolm_zero (x m : Int) : rolm x zero m = and x m := MI.rolm_zero x m

theorem or_rolm (x n m1 m2 : Int) : or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2) :=
  MI.or_rolm x n m1 m2

theorem rolm_rolm (x n1 m1 n2 m2 : Int) :
    rolm (rolm x n1 m1) n2 m2 = rolm x (modu (add n1 n2) iwordsize) (and (rol m1 n2) m2) :=
  MI.rolm_rolm (by decide) x n1 m1 n2 m2

theorem shl_rolm (x n : Int) (h : ltu n iwordsize = true) :
    shl x n = rolm x n (shl mone n) := MI.shl_rolm x n h

theorem shru_rolm (x n : Int) (h : ltu n iwordsize = true) :
    shru x n = rolm x (sub iwordsize n) (shru mone n) := MI.shru_rolm x n h

theorem shrx_shr (x y : Int) (h : ltu y (repr 31) = true) :
    shrx x y = shr (if lt x zero then add x (sub (shl one y) one) else x) y :=
  MI.shrx_shr x y h

theorem shrx_shr_2 (x y : Int) (h : ltu y (repr 31) = true) :
    shrx x y = shr (add x (shru (shr x (repr 31)) (sub iwordsize y))) y :=
  MI.shrx_shr_2 x y h

theorem shrx_carry (x y : Int) (h : ltu y (repr 31) = true) :
    shrx x y = add (shr x y) (shr_carry x y) := MI.shrx_carry x y h

theorem divs_one (x : Int) : divs x one = x := MI.divs_one x

theorem shrx_zero (x : Int) : shrx x zero = x := MI.shrx_zero x

end Int

namespace Int64

theorem is_power2_range {n logn : Int64} (h : is_power2 n = some logn) :
    ltu logn iwordsize = true := MI.is_power2_range h

theorem is_power2_correct {n logn : Int64} (h : is_power2 n = some logn) :
    unsigned n = (2 : Z) ^ (unsigned logn).toNat := by
  have := (MI.is_power2_spec h).2
  simp only [unsigned, MI.unsigned, Int.toNat_natCast]
  rw [this, Int.natCast_pow]; rfl

theorem mul_pow2 (x : Int64) {n logn : Int64} (h : is_power2 n = some logn) :
    mul x n = shl x logn := MI.mul_pow2 x h

theorem divu_pow2 (x : Int64) {n logn : Int64} (h : is_power2 n = some logn) :
    divu x n = shru x logn := MI.divu_pow2 x h

theorem modu_and (x : Int64) {n logn : Int64} (h : is_power2 n = some logn) :
    modu x n = and x (sub n one) := MI.modu_and x h

theorem zero_ext_and (n : Nat) (x : Int64) :
    zero_ext n x = and x (repr ((2 : Z) ^ n - 1)) := MI.zero_ext_and n x

theorem rol_and (x y n : Int64) : rol (and x y) n = and (rol x n) (rol y n) := MI.rol_and x y n

theorem rol_rol (x n m : Int64) : rol (rol x n) m = rol x (modu (add n m) iwordsize) :=
  MI.rol_rol (by decide) x n m

theorem rolm_zero (x m : Int64) : rolm x zero m = and x m := MI.rolm_zero x m

theorem or_rolm (x n m1 m2 : Int64) : or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2) :=
  MI.or_rolm x n m1 m2

theorem shl_rolm (x n : Int64) (h : ltu n iwordsize = true) :
    shl x n = rolm x n (shl mone n) := MI.shl_rolm x n h

theorem shru_rolm (x n : Int64) (h : ltu n iwordsize = true) :
    shru x n = rolm x (sub iwordsize n) (shru mone n) := MI.shru_rolm x n h

theorem divs_one (x : Int64) : divs x one = x := MI.divs_one x

/-! ### Shift amounts given as 32-bit integers -/

theorem toNat_repr_unsigned (y : Int) : (repr (Int.unsigned y) : Int64).toNat = y.toNat := by
  simp only [repr, MI.repr, Int.unsigned, MI.unsigned, BitVec.toNat_ofInt]
  have := y.isLt
  rw [Int.toNat_emod (by omega) (by decide)]
  simp only [Int.toNat_natCast]
  exact Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
                             have : ((2 : Z) ^ 64).toNat = 2 ^ 64 := by decide
                             omega)

theorem shl'_eq (x : Int64) (y : Int) : shl' x y = shl x (repr (Int.unsigned y)) := by
  simp only [shl', shl, MI.shl, toNat_repr_unsigned]

theorem shru'_eq (x : Int64) (y : Int) : shru' x y = shru x (repr (Int.unsigned y)) := by
  simp only [shru', shru, MI.shru, toNat_repr_unsigned]

theorem shr'_eq (x : Int64) (y : Int) : shr' x y = shr x (repr (Int.unsigned y)) := by
  simp only [shr', shr, MI.shr, toNat_repr_unsigned]

theorem shrx'_eq (x : Int64) (y : Int) : shrx' x y = shrx x (repr (Int.unsigned y)) := by
  simp only [shrx', shrx, MI.shrx, shl'_eq]; rfl

theorem shr_carry'_eq (x : Int64) (y : Int) :
    shr_carry' x y = shr_carry x (repr (Int.unsigned y)) := by
  simp only [shr_carry', shr_carry, MI.shr_carry, shl'_eq]; rfl

theorem ltu63_toNat {y : Int} (h : Int.ltu y (Int.repr 63) = true) : y.toNat < 63 := by
  have h63 : (Int.repr 63 : Int).toNat = 63 := by decide
  simp only [Int.ltu, MI.ltu, BitVec.ult, decide_eq_true_eq, h63] at h
  exact h

theorem ltu_repr63 {y : Int} (h : Int.ltu y (Int.repr 63) = true) :
    MI.ltu (repr (Int.unsigned y) : Int64) (MI.repr ((64 : Nat) - 1 : Z)) = true := by
  have hy : y.toNat < 63 := ltu63_toNat h
  rw [MI.ltu_def, decide_eq_true_eq]
  simp only [MI.unsigned]
  rw [show (repr (Int.unsigned y) : Int64).toNat = y.toNat from toNat_repr_unsigned y]
  have : (MI.repr ((64 : Nat) - 1 : Z) : Int64).toNat = 63 := by decide
  rw [this]; zomega

/-- `Int64.shrx'_carry` -/
theorem shrx'_carry (x : Int64) (y : Int) (h : Int.ltu y (Int.repr 63) = true) :
    shrx' x y = add (shr' x y) (shr_carry' x y) := by
  rw [shrx'_eq, shr'_eq, shr_carry'_eq]; exact MI.shrx_carry x _ (ltu_repr63 h)

/-- `Int64.shrx'_shr_2` -/
theorem shrx'_shr_2 (x : Int64) (y : Int) (h : Int.ltu y (Int.repr 63) = true) :
    shrx' x y = shr' (add x (shru' (shr' x (Int.repr 63)) (Int.sub (Int.repr 64) y))) y := by
  have hy : y.toNat < 63 := ltu63_toNat h
  have e1 : (repr (Int.unsigned (Int.repr 63)) : Int64) = MI.repr ((64 : Nat) - 1 : Z) := by
    decide
  have h64 : (Int.repr 64 : Int).toNat = 64 := by decide
  have e2 : (repr (Int.unsigned (Int.sub (Int.repr 64) y)) : Int64) =
      MI.sub (MI.iwordsize 64) (repr (Int.unsigned y)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_repr_unsigned]
    simp only [MI.sub, Int.sub]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h64]; omega), h64,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_repr_unsigned, MI.toNat_iwordsize]; omega),
      toNat_repr_unsigned, MI.toNat_iwordsize]
  rw [shrx'_eq, show shrx x (repr (Int.unsigned y)) = _ from MI.shrx_shr_2 x _ (ltu_repr63 h),
    shr'_eq, shru'_eq, shr'_eq, e1, e2]
  rfl

/-- `Int64.is_power2'_range` and `is_power2'_correct`, combined. -/
theorem is_power2'_spec {n : Int64} {logn : Int} (h : is_power2' n = some logn) :
    logn.toNat < 64 ∧ n.toNat = 2 ^ logn.toNat := by
  simp only [is_power2'] at h
  split at h
  · next i hl =>
    cases h
    have hr := MI.unsigned_range n
    obtain ⟨m, hj, hm, hx⟩ := Z_one_bits_single hr.1 hr.2 hl
    have hi : (Int.repr i : Int).toNat = m := by
      subst hj
      simp only [Int.repr, MI.repr, BitVec.toNat_ofInt]
      rw [Int.toNat_emod (by omega) (by decide)]
      simp only [Int.zero_add, Int.toNat_natCast]
      exact Nat.mod_eq_of_lt (by have : 64 < 2 ^ 32 := by decide
                                 omega)
    rw [hi]
    refine ⟨hm, ?_⟩
    have : (n.toNat : Z) = ((2 ^ m : Nat) : Z) := by
      rw [Int.natCast_pow]; exact hx
    exact Int.ofNat.inj this
  · cases h

theorem mul_pow2' (x : Int64) {n : Int64} {logn : Int} (h : is_power2' n = some logn) :
    mul x n = shl' x logn := by
  apply BitVec.eq_of_toNat_eq
  simp only [mul, MI.mul, shl', BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    (is_power2'_spec h).2]

theorem divu_pow2' (x : Int64) {n : Int64} {logn : Int} (h : is_power2' n = some logn) :
    divu x n = shru' x logn := by
  apply BitVec.eq_of_toNat_eq
  simp only [divu, MI.divu, shru', BitVec.toNat_udiv, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, (is_power2'_spec h).2]

end Int64

end Integers
end CC
