/-
  Correctness of instruction selection for integer division — port of
  `backend/SelectDivproof.v` (arithmetic part).

  Main results: the Granlund–Montgomery approximation theorems
  (`zdiv_mul_pos`, `zdiv_mul_opp`, `zquot_mul`), the soundness of the
  division parameters computed by `SelectDiv` (`divs_mul_params_sound`,
  `divu_mul_params_sound`, `divls_mul_params_sound`,
  `divlu_mul_params_sound`), and the machine-integer identities that justify
  replacing a division by a constant with a multiply-high and shifts
  (`divs_mul_shift_1`, `divs_mul_shift_2`, `divu_mul_shift`, and their
  64-bit counterparts).

  Differences from Rocq: `two_p (N + l)` with `N, l ≥ 0` is stated as
  `2 ^ (N + l)` with `N l : Nat` in the approximation theorems; `Z.quot` is
  `Int.tdiv`.  Numeric binders are spelled `_root_.Int` rather than `Z`
  so that `omega` sees them (see the note in `MemdataLemmas.lean`).
-/
import CCLib.backend.SelectDiv
namespace CC
namespace SelectDivproof

theorem zdiv_eq_of (a b q r : Int) (hb : 0 < b) (h0 : 0 ≤ r) (h1 : r < b) (h : a = b * q + r) :
    a / b = q :=
  ((Int.ediv_emod_unique hb).2 ⟨by rw [h, Int.add_comm], h0, h1⟩).1

/-- `Zdiv_mul_pos` (Granlund–Montgomery, theorem 4.2). -/
theorem zdiv_mul_pos (N l : Nat) (d m : Int) (hd : 0 < d)
    (lo : (2:Int) ^ (N + l) ≤ m * d) (hi : m * d ≤ 2 ^ (N + l) + 2 ^ l)
    (n : Int) (hn0 : 0 ≤ n) (hn1 : n < 2 ^ N) :
    n / d = (m * n) / 2 ^ (N + l) := by
  have hP : (0:Int) < 2 ^ (N + l) := Int.pow_pos (by decide)
  have hL : (0:Int) < 2 ^ l := Int.pow_pos (by decide)
  have hsplit : (2:Int) ^ (N + l) = 2 ^ N * 2 ^ l := Int.pow_add 2 N l
  generalize hq : n / d = q
  have eucl : d * q + n % d = n := by rw [← hq]; exact Int.mul_ediv_add_emod n d
  generalize hr : n % d = r at eucl
  have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg n (by omega)
  have hr1 : r < d := hr ▸ Int.emod_lt_of_pos n hd
  generalize hPdef : (2:Int) ^ (N + l) = P at *
  generalize hk : m * d - P = k
  have key : (m * n - P * q) * d = k * n + P * r := by
    rw [← hk, ← eucl]; simp only [Int.sub_mul, Int.mul_add, Int.add_mul]; grind
  have hkn0 : 0 ≤ k * n := Int.mul_nonneg (by omega) hn0
  have hkn1 : k * n ≤ P - 2 ^ l := by
    have h1 : k * n ≤ 2 ^ l * n := Int.mul_le_mul_of_nonneg_right (by omega) hn0
    have h2 : 2 ^ l * n ≤ 2 ^ l * (2 ^ N - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h3 : (2:Int) ^ l * (2 ^ N - 1) = P - 2 ^ l := by
      rw [hsplit, Int.mul_sub, Int.mul_comm]; simp
    omega
  have hPr0 : 0 ≤ P * r := Int.mul_nonneg (by omega) hr0
  have hPr1 : P * r ≤ P * d - P := by
    have := Int.mul_le_mul_of_nonneg_left (show r ≤ d - 1 by omega) (Int.le_of_lt hP)
    rw [Int.mul_sub, Int.mul_one] at this; exact this
  have A0 : 0 ≤ m * n - P * q := Int.nonneg_of_mul_nonneg_left (by omega) hd
  have A1 : m * n - P * q < P := (Int.mul_lt_mul_right hd).mp (by
    rw [key]; have : P * d = P * d := rfl; omega)
  symm
  exact zdiv_eq_of _ _ _ _ hP A0 A1 (by omega)


/-- `Zdiv_mul_opp` -/
theorem zdiv_mul_opp (N l : Nat) (d m : Int) (hd : 0 < d)
    (lo : (2:Int) ^ (N + l) < m * d) (hi : m * d ≤ 2 ^ (N + l) + 2 ^ l)
    (n : Int) (hn0 : 0 < n) (hn1 : n ≤ 2 ^ N) :
    n / d = - ((m * (-n)) / 2 ^ (N + l)) - 1 := by
  have hP : (0:Int) < 2 ^ (N + l) := Int.pow_pos (by decide)
  have hL : (0:Int) < 2 ^ l := Int.pow_pos (by decide)
  have hsplit : (2:Int) ^ (N + l) = 2 ^ N * 2 ^ l := Int.pow_add 2 N l
  generalize hq : n / d = q
  have eucl : d * q + n % d = n := by rw [← hq]; exact Int.mul_ediv_add_emod n d
  generalize hr : n % d = r at eucl
  have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg n (by omega)
  have hr1 : r < d := hr ▸ Int.emod_lt_of_pos n hd
  generalize hPdef : (2:Int) ^ (N + l) = P at *
  generalize hk : m * d - P = k
  have key : (m * n - P * q) * d = k * n + P * r := by
    rw [← hk, ← eucl]; simp only [Int.sub_mul, Int.mul_add, Int.add_mul]; grind
  have hkn0 : 0 < k * n := Int.mul_pos (by omega) hn0
  have hkn1 : k * n ≤ P := by
    have h1 : k * n ≤ 2 ^ l * n := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have h2 : 2 ^ l * n ≤ 2 ^ l * 2 ^ N := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h3 : (2:Int) ^ l * 2 ^ N = P := by rw [hsplit, Int.mul_comm]
    omega
  have hPr0 : 0 ≤ P * r := Int.mul_nonneg (by omega) hr0
  have hPr1 : P * r ≤ P * d - P := by
    have := Int.mul_le_mul_of_nonneg_left (show r ≤ d - 1 by omega) (Int.le_of_lt hP)
    rw [Int.mul_sub, Int.mul_one] at this; exact this
  have A0 : 0 < m * n - P * q := by
    have : 0 * d < (m * n - P * q) * d := by rw [key]; omega
    exact (Int.mul_lt_mul_right hd).mp this
  have A1 : m * n - P * q ≤ P := by
    have : (m * n - P * q) * d ≤ P * d := by rw [key]; omega
    exact Int.le_of_mul_le_mul_right this hd
  have : (m * (-n)) / P = -q - 1 := by
    apply zdiv_eq_of _ _ _ (P - (m * n - P * q)) hP (by omega) (by omega)
    rw [Int.mul_neg, Int.mul_sub, Int.mul_neg, Int.mul_one]; omega
  omega

/-- `Zquot_mul` (Granlund–Montgomery, theorem 5.1). -/
theorem zquot_mul (N l : Nat) (d m : Int) (hd : 0 < d)
    (lo : (2:Int) ^ (N + l) < m * d) (hi : m * d ≤ 2 ^ (N + l) + 2 ^ l)
    (n : Int) (hn0 : -2 ^ N ≤ n) (hn1 : n < 2 ^ N) :
    n.tdiv d = (m * n) / 2 ^ (N + l) + (if n < 0 then 1 else 0) := by
  by_cases hneg : n < 0
  · rw [if_pos hneg]
    have h := zdiv_mul_opp N l d m hd lo hi (-n) (by omega) (by omega)
    rw [Int.neg_neg] at h
    have : n.tdiv d = - ((-n).tdiv d) := by rw [Int.neg_tdiv, Int.neg_neg]
    rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega), h]; omega
  · rw [if_neg hneg, Int.add_zero, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    exact zdiv_mul_pos N l d m hd (by omega) hi n (by omega) hn1

open Integers SelectOp SelectDiv

theorem twoP_eq {x : _root_.Int} (h : 0 ≤ x) : twoP x = 2 ^ x.toNat := by
  simp [twoP, h]


/-- `divs_mul_params_sound` -/
theorem divs_mul_params_sound {d m p : _root_.Int} (h : divsMulParams d = some (p, m)) :
    0 ≤ m ∧ m < Int.modulus ∧ 0 ≤ p ∧ p < 32 ∧
    ∀ n : _root_.Int, Int.min_signed ≤ n → n ≤ Int.max_signed →
      n.tdiv d = (m * n) / twoP (32 + p) + (if n < 0 then 1 else 0) := by
  unfold divsMulParams at h
  split at h
  · cases h
  · rename_i p0 m0 _
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
      cases h
      replace h1 : (0:_root_.Int) < d := h1
      replace h6 : (0:_root_.Int) ≤ p0 - 32 := h6
      replace h7 : (p0:_root_.Int) - 32 < 32 := h7
      refine ⟨h4, h5, h6, h7, fun n hn0 hn1 => ?_⟩
      have e1 : twoP (32 + (p0 - 32)) = (2:Z) ^ (31 + ((p0 - 32).toNat + 1)) := by
        have hx : (32 + (p0 - 32)).toNat = 31 + ((p0 - 32).toNat + 1) := by omega
        rw [twoP_eq (by omega), hx]
      have e2 : twoP (p0 - 32 + 1) = (2:Z) ^ ((p0 - 32).toNat + 1) := by
        have hx : (p0 - 32 + 1).toNat = (p0 - 32).toNat + 1 := by omega
        rw [twoP_eq (by omega), hx]
      rw [e1] at h2 h3 ⊢; rw [e2] at h3
      have hmin : @Eq _root_.Int Int.min_signed (-2^31) := by decide
      have hmax : @Eq _root_.Int Int.max_signed (2^31 - 1) := by decide
      replace hn0 : @LE.le _root_.Int _ Int.min_signed n := hn0
      replace hn1 : @LE.le _root_.Int _ n Int.max_signed := hn1
      exact zquot_mul 31 _ d m h1 h2 h3 n (by omega) (by omega)
    · cases h

/-- `divu_mul_params_sound` -/
theorem divu_mul_params_sound {d m p : _root_.Int} (h : divuMulParams d = some (p, m)) :
    0 ≤ m ∧ m < Int.modulus ∧ 0 ≤ p ∧ p < 32 ∧
    ∀ n : _root_.Int, 0 ≤ n → n < Int.modulus →
      n / d = (m * n) / twoP (32 + p) := by
  unfold divuMulParams at h
  split at h
  · cases h
  · rename_i p0 m0 _
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
      cases h
      replace h1 : (0:_root_.Int) < d := h1
      replace h6 : (0:_root_.Int) ≤ p0 - 32 := h6
      replace h7 : (p0:_root_.Int) - 32 < 32 := h7
      refine ⟨h4, h5, h6, h7, fun n hn0 hn1 => ?_⟩
      have e1 : twoP (32 + (p0 - 32)) = (2:Z) ^ (32 + (p0 - 32).toNat) := by
        have hx : (32 + (p0 - 32)).toNat = 32 + (p0 - 32).toNat := by omega
        rw [twoP_eq (by omega), hx]
      have e2 : twoP (p0 - 32) = (2:Z) ^ ((p0 - 32).toNat) := twoP_eq h6
      rw [e1] at h2 h3 ⊢; rw [e2] at h3
      have hmod : @Eq _root_.Int Int.modulus (2^32) := by decide
      replace hn1 : @LT.lt _root_.Int _ n Int.modulus := hn1
      exact zdiv_mul_pos 32 _ d m h1 h2 h3 n hn0 (by omega)
    · cases h

/-- `divls_mul_params_sound` -/
theorem divls_mul_params_sound {d m p : _root_.Int} (h : divlsMulParams d = some (p, m)) :
    0 ≤ m ∧ m < Int64.modulus ∧ 0 ≤ p ∧ p < 64 ∧
    ∀ n : _root_.Int, Int64.min_signed ≤ n → n ≤ Int64.max_signed →
      n.tdiv d = (m * n) / twoP (64 + p) + (if n < 0 then 1 else 0) := by
  unfold divlsMulParams at h
  split at h
  · cases h
  · rename_i p0 m0 _
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
      cases h
      replace h1 : (0:_root_.Int) < d := h1
      replace h6 : (0:_root_.Int) ≤ p0 - 64 := h6
      replace h7 : (p0:_root_.Int) - 64 < 64 := h7
      refine ⟨h4, h5, h6, h7, fun n hn0 hn1 => ?_⟩
      have e1 : twoP (64 + (p0 - 64)) = (2:Z) ^ (63 + ((p0 - 64).toNat + 1)) := by
        have hx : (64 + (p0 - 64)).toNat = 63 + ((p0 - 64).toNat + 1) := by omega
        rw [twoP_eq (by omega), hx]
      have e2 : twoP (p0 - 64 + 1) = (2:Z) ^ ((p0 - 64).toNat + 1) := by
        have hx : (p0 - 64 + 1).toNat = (p0 - 64).toNat + 1 := by omega
        rw [twoP_eq (by omega), hx]
      rw [e1] at h2 h3 ⊢; rw [e2] at h3
      have hmin : @Eq _root_.Int Int64.min_signed (-2^63) := by decide
      have hmax : @Eq _root_.Int Int64.max_signed (2^63 - 1) := by decide
      replace hn0 : @LE.le _root_.Int _ Int64.min_signed n := hn0
      replace hn1 : @LE.le _root_.Int _ n Int64.max_signed := hn1
      exact zquot_mul 63 _ d m h1 h2 h3 n (by omega) (by omega)
    · cases h

/-- `divlu_mul_params_sound` -/
theorem divlu_mul_params_sound {d m p : _root_.Int} (h : divluMulParams d = some (p, m)) :
    0 ≤ m ∧ m < Int64.modulus ∧ 0 ≤ p ∧ p < 64 ∧
    ∀ n : _root_.Int, 0 ≤ n → n < Int64.modulus →
      n / d = (m * n) / twoP (64 + p) := by
  unfold divluMulParams at h
  split at h
  · cases h
  · rename_i p0 m0 _
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
      cases h
      replace h1 : (0:_root_.Int) < d := h1
      replace h6 : (0:_root_.Int) ≤ p0 - 64 := h6
      replace h7 : (p0:_root_.Int) - 64 < 64 := h7
      refine ⟨h4, h5, h6, h7, fun n hn0 hn1 => ?_⟩
      have e1 : twoP (64 + (p0 - 64)) = (2:Z) ^ (64 + (p0 - 64).toNat) := by
        have hx : (64 + (p0 - 64)).toNat = 64 + (p0 - 64).toNat := by omega
        rw [twoP_eq (by omega), hx]
      have e2 : twoP (p0 - 64) = (2:Z) ^ ((p0 - 64).toNat) := twoP_eq h6
      rw [e1] at h2 h3 ⊢; rw [e2] at h3
      have hmod : @Eq _root_.Int Int64.modulus (2^64) := by decide
      replace hn1 : @LT.lt _root_.Int _ n Int64.modulus := hn1
      exact zdiv_mul_pos 64 _ d m h1 h2 h3 n hn0 (by omega)
    · cases h

/-! ### Machine-integer identities (32 bits) -/

theorem int_modulus_eq : @Eq _root_.Int Int.modulus (2 ^ 32) := by decide
theorem int_max_unsigned_eq : @Eq _root_.Int Int.max_unsigned (2 ^ 32 - 1) := by decide

theorem int_unsigned_repr' {z : _root_.Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ 32) :
    Int.unsigned (Integers.Int.repr z) = z :=
  Int.unsigned_repr h0 (by
    show @LE.le _root_.Int _ z Int.max_unsigned
    rw [int_max_unsigned_eq]; omega)

/-- The shift amount `Integers.Int.repr p`, for `0 ≤ p < 2 ^ 32`, is `p`. -/
theorem int_repr_toNat {p : _root_.Int} (h0 : 0 ≤ p) (h1 : p < 2 ^ 32) :
    (Integers.Int.repr p).toNat = p.toNat := by
  have := int_unsigned_repr' h0 (by omega)
  have e : ((Integers.Int.repr p).toNat : _root_.Int) = p := this
  omega

theorem unsigned_range' (x : Integers.Int) :
    (0 : _root_.Int) ≤ Int.unsigned x ∧ (Int.unsigned x : _root_.Int) < 2 ^ 32 := by
  have := Int.unsigned_range x; rw [int_modulus_eq] at this; exact this

/-- `divu_mul_shift` -/
theorem divu_mul_shift {x y : Integers.Int} {m p : _root_.Int}
    (h : divuMulParams (Int.unsigned y) = some (p, m)) :
    0 ≤ p ∧ p < 32 ∧
    Int.divu x y = Int.shru (Int.mulhu x (Integers.Int.repr m)) (Integers.Int.repr p) := by
  obtain ⟨hm0, hm1, hp0, hp1, C⟩ := divu_mul_params_sound h
  rw [int_modulus_eq] at hm1
  refine ⟨hp0, hp1, ?_⟩
  obtain ⟨hx0, hx1⟩ := unsigned_range' x
  rw [Int.shru_div_two_p, int_repr_toNat hp0 (by zomega), Int.divu_unsigned,
    C _ hx0 (by rw [int_modulus_eq]; exact hx1)]
  congr 1
  have hmu : Int.unsigned (Integers.Int.repr m) = m :=
    int_unsigned_repr' hm0 hm1
  have hmulhu : Int.mulhu x (Integers.Int.repr m) = Integers.Int.repr (Int.unsigned x * m / 2 ^ 32) := by
    show MI.repr _ = _
    show Integers.Int.repr (Int.unsigned x * Int.unsigned (Integers.Int.repr m) / Int.modulus) = _
    rw [hmu, int_modulus_eq]
  have hP : (0 : _root_.Int) < 2 ^ 32 := by decide
  have hq0 : 0 ≤ Int.unsigned x * m / 2 ^ 32 := Int.ediv_nonneg (Int.mul_nonneg hx0 hm0) (by omega)
  have hq1 : Int.unsigned x * m / 2 ^ 32 < 2 ^ 32 := by
    apply (Int.ediv_lt_iff_lt_mul hP).mpr
    have h1 : Int.unsigned x * m ≤ Int.unsigned x * 2 ^ 32 :=
      Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hm1) hx0
    have h2 : Int.unsigned x * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 :=
      Int.mul_lt_mul_of_pos_right hx1 hP
    unfold Z at *; omega
  rw [hmulhu, int_unsigned_repr' hq0 hq1,
    Int.ediv_ediv_of_nonneg (by omega), twoP_eq (by omega), ← Int.pow_add,
    Int.mul_comm m]
  congr 2; omega

theorem int_signed_repr' {z : _root_.Int} (h0 : -2 ^ 31 ≤ z) (h1 : z < 2 ^ 31) :
    Int.signed (Integers.Int.repr z) = z :=
  Int.signed_repr
    (by have : @Eq _root_.Int Int.min_signed (-2^31) := by decide
        zomega)
    (by have : @Eq _root_.Int Int.max_signed (2^31 - 1) := by decide
        zomega)

theorem signed_range' (x : Integers.Int) :
    (-2 ^ 31 : _root_.Int) ≤ Int.signed x ∧ (Int.signed x : _root_.Int) < 2 ^ 31 := by
  have := Int.signed_range x
  have : @Eq _root_.Int Int.min_signed (-2^31) := by decide
  have : @Eq _root_.Int Int.max_signed (2^31 - 1) := by decide
  zomega

/-- `Int.shru_lt_zero` -/
theorem shru_lt_zero (x : Integers.Int) :
    Int.shru x (Integers.Int.repr 31) =
      Integers.Int.repr (if Int.signed x < 0 then 1 else 0) := by
  rw [Int.shru_div_two_p, int_repr_toNat (by decide) (by decide)]
  have hs := MI.signed_eq (w := 32) (by decide) x
  have hh : @Eq _root_.Int (MI.half_modulus 32) (2^31) := by decide
  have hm : @Eq _root_.Int (MI.modulus 32) (2^32) := by decide
  obtain ⟨hx0, hx1⟩ := unsigned_range' x
  change Int.signed x = if Int.unsigned x < MI.half_modulus 32 then Int.unsigned x
    else Int.unsigned x - MI.modulus 32 at hs
  rw [hh, hm] at hs
  congr 1
  split at hs
  · rw [if_neg (by zomega)]; show Int.unsigned x / 2 ^ 31 = 0; zomega
  · rw [if_pos (by zomega)]; show Int.unsigned x / 2 ^ 31 = 1; zomega

/-- `divs_mul_shift_gen` -/
theorem divs_mul_shift_gen {x y : Integers.Int} {m p : _root_.Int}
    (h : divsMulParams (Int.signed y) = some (p, m)) :
    0 ≤ m ∧ m < 2 ^ 32 ∧ 0 ≤ p ∧ p < 32 ∧
    Int.divs x y = Integers.Int.add (Int.shr (Integers.Int.repr ((Int.signed x * m) / 2 ^ 32))
      (Integers.Int.repr p)) (Int.shru x (Integers.Int.repr 31)) := by
  obtain ⟨hm0, hm1, hp0, hp1, C⟩ := divs_mul_params_sound h
  rw [int_modulus_eq] at hm1
  refine ⟨hm0, hm1, hp0, hp1, ?_⟩
  obtain ⟨hn0, hn1⟩ := signed_range' x
  have hmin : @Eq _root_.Int Int.min_signed (-2^31) := by decide
  have hmax : @Eq _root_.Int Int.max_signed (2^31 - 1) := by decide
  rw [Int.divs_signed, C _ (by zomega) (by zomega), shru_lt_zero, Int.shr_div_two_p,
    int_repr_toNat hp0 (by zomega), ← Int.repr_add]
  have hP : (0 : _root_.Int) < 2 ^ 32 := by decide
  have hq0 : -2 ^ 31 ≤ Int.signed x * m / 2 ^ 32 := by
    apply Int.le_ediv_of_mul_le hP
    have h1 : -2 ^ 31 * m ≤ Int.signed x * m := Int.mul_le_mul_of_nonneg_right hn0 hm0
    have h2 : -2 ^ 31 * 2 ^ 32 ≤ -2 ^ 31 * m :=
      Int.mul_le_mul_of_nonpos_left (by decide) (Int.le_of_lt hm1)
    zomega
  have hq1 : Int.signed x * m / 2 ^ 32 < 2 ^ 31 := by
    apply (Int.ediv_lt_iff_lt_mul hP).mpr
    have h1 : Int.signed x * m ≤ (2 ^ 31 - 1) * m :=
      Int.mul_le_mul_of_nonneg_right (by zomega) hm0
    have h2 : (2 ^ 31 - 1) * m ≤ (2 ^ 31 - 1) * 2 ^ 32 :=
      Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hm1) (by decide)
    zomega
  have hx : (32 + p).toNat = 32 + p.toNat := by zomega
  rw [int_signed_repr' hq0 hq1, Int.ediv_ediv_of_nonneg (by decide), twoP_eq (by zomega),
    ← Int.pow_add, Int.mul_comm m, hx]

theorem mulhs_repr (x : Integers.Int) (m : _root_.Int) :
    Int.mulhs x (Integers.Int.repr m) =
      Integers.Int.repr (Int.signed x * Int.signed (Integers.Int.repr m) / 2 ^ 32) := by
  show Integers.Int.repr (Int.signed x * Int.signed (Integers.Int.repr m) / Int.modulus) = _
  rw [int_modulus_eq]

/-- `divs_mul_shift_1` -/
theorem divs_mul_shift_1 {x y : Integers.Int} {m p : _root_.Int}
    (h : divsMulParams (Int.signed y) = some (p, m)) (hm : m < 2 ^ 31) :
    0 ≤ p ∧ p < 32 ∧
    Int.divs x y = Integers.Int.add (Int.shr (Int.mulhs x (Integers.Int.repr m))
      (Integers.Int.repr p)) (Int.shru x (Integers.Int.repr 31)) := by
  obtain ⟨hm0, _, hp0, hp1, C⟩ := divs_mul_shift_gen (x := x) h
  refine ⟨hp0, hp1, ?_⟩
  rw [C, mulhs_repr, int_signed_repr' (by zomega) hm]

/-- `divs_mul_shift_2` -/
theorem divs_mul_shift_2 {x y : Integers.Int} {m p : _root_.Int}
    (h : divsMulParams (Int.signed y) = some (p, m)) (hm : 2 ^ 31 ≤ m) :
    0 ≤ p ∧ p < 32 ∧
    Int.divs x y = Integers.Int.add (Int.shr (Integers.Int.add (Int.mulhs x (Integers.Int.repr m)) x)
      (Integers.Int.repr p)) (Int.shru x (Integers.Int.repr 31)) := by
  obtain ⟨hm0, hm1, hp0, hp1, C⟩ := divs_mul_shift_gen (x := x) h
  refine ⟨hp0, hp1, ?_⟩
  rw [C, mulhs_repr]
  have hsm : Int.signed (Integers.Int.repr m) = m - 2 ^ 32 := by
    have e : Integers.Int.repr m = Integers.Int.repr (m - 2 ^ 32) := by
      apply Int.eqm_samerepr
      have : @Eq _root_.Int (MI.modulus 32) (2^32) := by decide
      exact ⟨1, by zomega⟩
    rw [e, int_signed_repr' (by zomega) (by zomega)]
  rw [hsm]
  congr 2
  have hadd : ∀ A : _root_.Int, Integers.Int.add (Integers.Int.repr A) x =
      Integers.Int.repr (A + Int.signed x) := fun A => by
    rw [Int.repr_add, Int.repr_signed]
  rw [hadd]
  congr 1
  have : Int.signed x * (m - 2 ^ 32) = Int.signed x * m + (-Int.signed x) * 2 ^ 32 := by
    rw [Int.mul_sub, Int.neg_mul, Int.sub_eq_add_neg]
  rw [this, Int.add_mul_ediv_right _ _ (by decide)]
  zomega

/-! ### 64-bit versions -/

theorem int64_modulus_eq : @Eq _root_.Int Int64.modulus (2 ^ 64) := by decide
theorem int64_max_unsigned_eq : @Eq _root_.Int Int64.max_unsigned (2 ^ 64 - 1) := by decide

theorem int64_unsigned_repr' {z : _root_.Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    Int64.unsigned (Int64.repr z) = z :=
  Int64.unsigned_repr h0 (by have := int64_max_unsigned_eq; zomega)

theorem int64_signed_repr' {z : _root_.Int} (h0 : -2 ^ 63 ≤ z) (h1 : z < 2 ^ 63) :
    Int64.signed (Int64.repr z) = z :=
  Int64.signed_repr
    (by have : @Eq _root_.Int Int64.min_signed (-2^63) := by decide
        zomega)
    (by have : @Eq _root_.Int Int64.max_signed (2^63 - 1) := by decide
        zomega)

theorem int64_unsigned_range' (x : Integers.Int64) :
    (0 : _root_.Int) ≤ Int64.unsigned x ∧ (Int64.unsigned x : _root_.Int) < 2 ^ 64 := by
  have := Int64.unsigned_range x; rw [int64_modulus_eq] at this; exact this

theorem int64_signed_range' (x : Integers.Int64) :
    (-2 ^ 63 : _root_.Int) ≤ Int64.signed x ∧ (Int64.signed x : _root_.Int) < 2 ^ 63 := by
  have := Int64.signed_range x
  have : @Eq _root_.Int Int64.min_signed (-2^63) := by decide
  have : @Eq _root_.Int Int64.max_signed (2^63 - 1) := by decide
  zomega

theorem ofNat_toNat_int (y : Integers.Int) : (BitVec.ofNat 64 y.toNat).toNat = y.toNat := by
  have := y.isLt
  rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega

/-- `int64_shru'_div_two_p` -/
theorem int64_shru'_div_two_p (x : Integers.Int64) (y : Integers.Int) :
    Int64.shru' x y = Int64.repr (Int64.unsigned x / 2 ^ y.toNat) := by
  unfold Int64.shru'; rw [← ofNat_toNat_int y]; exact Int64.shru_div_two_p x _

/-- `int64_shr'_div_two_p` -/
theorem int64_shr'_div_two_p (x : Integers.Int64) (y : Integers.Int) :
    Int64.shr' x y = Int64.repr (Int64.signed x / 2 ^ y.toNat) := by
  unfold Int64.shr'; rw [← ofNat_toNat_int y]; exact Int64.shr_div_two_p x _

/-- `Int64.shru_lt_zero` (with an `Int` shift amount) -/
theorem int64_shru'_lt_zero (x : Integers.Int64) :
    Int64.shru' x (Integers.Int.repr 63) = Int64.repr (if Int64.signed x < 0 then 1 else 0) := by
  rw [int64_shru'_div_two_p, int_repr_toNat (by decide) (by decide)]
  have hs := MI.signed_eq (w := 64) (by decide) x
  have hh : @Eq _root_.Int (MI.half_modulus 64) (2^63) := by decide
  have hm : @Eq _root_.Int (MI.modulus 64) (2^64) := by decide
  obtain ⟨hx0, hx1⟩ := int64_unsigned_range' x
  change Int64.signed x = if Int64.unsigned x < MI.half_modulus 64 then Int64.unsigned x
    else Int64.unsigned x - MI.modulus 64 at hs
  rw [hh, hm] at hs
  congr 1
  split at hs
  · rw [if_neg (by zomega)]; show Int64.unsigned x / 2 ^ 63 = 0; zomega
  · rw [if_pos (by zomega)]; show Int64.unsigned x / 2 ^ 63 = 1; zomega

/-- `divls_mul_shift_gen` -/
theorem divls_mul_shift_gen {x y : Integers.Int64} {m p : _root_.Int}
    (h : divlsMulParams (Int64.signed y) = some (p, m)) :
    0 ≤ m ∧ m < 2 ^ 64 ∧ 0 ≤ p ∧ p < 64 ∧
    Int64.divs x y = Integers.Int64.add (Int64.shr' (Int64.repr ((Int64.signed x * m) / 2 ^ 64))
      (Integers.Int.repr p)) (Int64.shru' x (Integers.Int.repr 63)) := by
  obtain ⟨hm0, hm1, hp0, hp1, C⟩ := divls_mul_params_sound h
  rw [int64_modulus_eq] at hm1
  refine ⟨hm0, hm1, hp0, hp1, ?_⟩
  obtain ⟨hn0, hn1⟩ := int64_signed_range' x
  have hmin : @Eq _root_.Int Int64.min_signed (-2^63) := by decide
  have hmax : @Eq _root_.Int Int64.max_signed (2^63 - 1) := by decide
  rw [Int64.divs_signed, C _ (by zomega) (by zomega), int64_shru'_lt_zero, int64_shr'_div_two_p,
    int_repr_toNat (by zomega) (by zomega), ← Int64.repr_add]
  have hP : (0 : _root_.Int) < 2 ^ 64 := by decide
  have hq0 : -2 ^ 63 ≤ Int64.signed x * m / 2 ^ 64 := by
    apply Int.le_ediv_of_mul_le hP
    have h1 : -2 ^ 63 * m ≤ Int64.signed x * m := Int.mul_le_mul_of_nonneg_right hn0 hm0
    have h2 : -2 ^ 63 * 2 ^ 64 ≤ -2 ^ 63 * m :=
      Int.mul_le_mul_of_nonpos_left (by decide) (Int.le_of_lt hm1)
    zomega
  have hq1 : Int64.signed x * m / 2 ^ 64 < 2 ^ 63 := by
    apply (Int.ediv_lt_iff_lt_mul hP).mpr
    have h1 : Int64.signed x * m ≤ (2 ^ 63 - 1) * m :=
      Int.mul_le_mul_of_nonneg_right (by zomega) hm0
    have h2 : (2 ^ 63 - 1) * m ≤ (2 ^ 63 - 1) * 2 ^ 64 :=
      Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hm1) (by decide)
    zomega
  have hx : (64 + p).toNat = 64 + p.toNat := by zomega
  rw [int64_signed_repr' hq0 hq1, Int.ediv_ediv_of_nonneg (by decide), twoP_eq (by zomega),
    ← Int.pow_add, Int.mul_comm m, hx]

theorem int64_mulhs_repr (x : Integers.Int64) (m : _root_.Int) :
    Int64.mulhs x (Int64.repr m) =
      Int64.repr (Int64.signed x * Int64.signed (Int64.repr m) / 2 ^ 64) := by
  show Int64.repr (Int64.signed x * Int64.signed (Int64.repr m) / Int64.modulus) = _
  rw [int64_modulus_eq]

/-- `divls_mul_shift_1` -/
theorem divls_mul_shift_1 {x y : Integers.Int64} {m p : _root_.Int}
    (h : divlsMulParams (Int64.signed y) = some (p, m)) (hm : m < 2 ^ 63) :
    0 ≤ p ∧ p < 64 ∧
    Int64.divs x y = Integers.Int64.add (Int64.shr' (Int64.mulhs x (Int64.repr m))
      (Integers.Int.repr p)) (Int64.shru' x (Integers.Int.repr 63)) := by
  obtain ⟨hm0, _, hp0, hp1, C⟩ := divls_mul_shift_gen (x := x) h
  refine ⟨hp0, hp1, ?_⟩
  rw [C, int64_mulhs_repr, int64_signed_repr' (by zomega) hm]

/-- `divls_mul_shift_2` -/
theorem divls_mul_shift_2 {x y : Integers.Int64} {m p : _root_.Int}
    (h : divlsMulParams (Int64.signed y) = some (p, m)) (hm : 2 ^ 63 ≤ m) :
    0 ≤ p ∧ p < 64 ∧
    Int64.divs x y = Integers.Int64.add (Int64.shr' (Integers.Int64.add (Int64.mulhs x (Int64.repr m)) x)
      (Integers.Int.repr p)) (Int64.shru' x (Integers.Int.repr 63)) := by
  obtain ⟨hm0, hm1, hp0, hp1, C⟩ := divls_mul_shift_gen (x := x) h
  refine ⟨hp0, hp1, ?_⟩
  rw [C, int64_mulhs_repr]
  have hsm : Int64.signed (Int64.repr m) = m - 2 ^ 64 := by
    have e : Int64.repr m = Int64.repr (m - 2 ^ 64) := by
      apply Int64.eqm_samerepr
      have : @Eq _root_.Int (MI.modulus 64) (2^64) := by decide
      exact ⟨1, by zomega⟩
    rw [e, int64_signed_repr' (by zomega) (by zomega)]
  rw [hsm]
  have hadd : ∀ A : _root_.Int, Integers.Int64.add (Int64.repr A) x =
      Int64.repr (A + Int64.signed x) := fun A => by
    rw [Int64.repr_add, Int64.repr_signed]
  rw [hadd]
  congr 3
  have : Int64.signed x * (m - 2 ^ 64) = Int64.signed x * m + (-Int64.signed x) * 2 ^ 64 := by
    rw [Int.mul_sub, Int.neg_mul, Int.sub_eq_add_neg]
  rw [this, Int.add_mul_ediv_right _ _ (by decide)]
  zomega

/-- `divlu_mul_shift` -/
theorem divlu_mul_shift {x y : Integers.Int64} {m p : _root_.Int}
    (h : divluMulParams (Int64.unsigned y) = some (p, m)) :
    0 ≤ p ∧ p < 64 ∧
    Int64.divu x y = Int64.shru' (Int64.mulhu x (Int64.repr m)) (Integers.Int.repr p) := by
  obtain ⟨hm0, hm1, hp0, hp1, C⟩ := divlu_mul_params_sound h
  rw [int64_modulus_eq] at hm1
  refine ⟨hp0, hp1, ?_⟩
  obtain ⟨hx0, hx1⟩ := int64_unsigned_range' x
  rw [int64_shru'_div_two_p, int_repr_toNat (by zomega) (by zomega), Int64.divu_unsigned,
    C _ hx0 (by rw [int64_modulus_eq]; exact hx1)]
  congr 1
  have hmu : Int64.unsigned (Int64.repr m) = m := int64_unsigned_repr' hm0 hm1
  have hmulhu : Int64.mulhu x (Int64.repr m) = Int64.repr (Int64.unsigned x * m / 2 ^ 64) := by
    show Int64.repr (Int64.unsigned x * Int64.unsigned (Int64.repr m) / Int64.modulus) = _
    rw [hmu, int64_modulus_eq]
  have hP : (0 : _root_.Int) < 2 ^ 64 := by decide
  have hq0 : 0 ≤ Int64.unsigned x * m / 2 ^ 64 :=
    Int.ediv_nonneg (Int.mul_nonneg hx0 hm0) (by decide)
  have hq1 : Int64.unsigned x * m / 2 ^ 64 < 2 ^ 64 := by
    apply (Int.ediv_lt_iff_lt_mul hP).mpr
    have h1 : Int64.unsigned x * m ≤ Int64.unsigned x * 2 ^ 64 :=
      Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hm1) hx0
    have h2 : Int64.unsigned x * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 :=
      Int.mul_lt_mul_of_pos_right hx1 hP
    zomega
  have hx : (64 + p).toNat = 64 + p.toNat := by zomega
  rw [hmulhu, int64_unsigned_repr' hq0 hq1, Int.ediv_ediv_of_nonneg (by decide),
    twoP_eq (by zomega), ← Int.pow_add, Int.mul_comm m, hx]

end SelectDivproof
end CC
