/-
  Correctness of the AArch64 code generator's constructor functions,
  part 1 — port of the beginning of `aarch64/Asmgenproof1.v`: properties of
  registers (`preg_of_iregsp_not_PC`, `preg_of_not_X16`, `ireg_of_not_X16`),
  the decomposition of integer literals (`decompose_int_correct`,
  `decompose_int_eqmod`, `decompose_notint_eqmod`, `recompose_int_negated`)
  and the loading of integer immediates (`exec_loadimm_k_w/x`,
  `exec_loadimm_z_w/x`, `exec_loadimm_n_w/x`, `exec_loadimm32`,
  `exec_loadimm64`).

  Differences from Rocq: the port's `decompose_int`, `negate_decomposition`
  and `Zinsert` are defined arithmetically (see `aarch64/Asmgen.lean` and
  `aarch64/Asm.lean`), so the bit-level proofs of Rocq (`Z.testbit`
  reasoning) are replaced by proofs about `/` and `%` by powers of two.
  The well-formedness predicate `wf_decomposition` becomes `WfDecomp w`,
  which also records that every fragment fits in a `w`-bit word.
-/
import CCLib.backend.Asmgenproof0

namespace CC
namespace Asmgenproof1

open Asm Asmgen Asmgenproof0 Smallstep Conventions1

/-- `omega` after unfolding the `Z` abbreviation. -/
local macro "zomega" : tactic => `(tactic| ((try simp only [Z] at *) <;> omega))

/-! ## Properties of registers -/

/-- `Asmgenproof1.preg_of_iregsp_not_PC` -/
theorem preg_of_iregsp_not_PC (r : Iregsp) : pregOfIregsp r ≠ .PC := by
  cases r <;> simp [pregOfIregsp]

/-- `Asmgenproof1.preg_of_not_X16` -/
theorem preg_of_not_X16 (r : Mreg) : pregOf r ≠ .IR .X16 := by
  cases r <;> simp [pregOf]

/-- `Asmgenproof1.ireg_of_not_X16` -/
theorem ireg_of_not_X16 {r : Mreg} {x : Ireg} (h : iregOf r = .OK x) : x ≠ .X16 := by
  rintro rfl; exact preg_of_not_X16 r (ireg_of_eq h)

/-- `Asmgenproof1.ireg_of_not_X16'` -/
theorem ireg_of_not_X16' {r : Mreg} {x : Ireg} (h : iregOf r = .OK x) : Preg.IR x ≠ .IR .X16 :=
  fun e => ireg_of_not_X16 h (Preg.IR.inj e)

/-! ## Arithmetic on powers of two -/

theorem pow2_pos (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

theorem emod_eq' (a b : Int) : Int.emod a b = a % b := rfl

theorem fdiv_pow2 (x : Int) (n : Nat) : x.fdiv (2 ^ n) = x / 2 ^ n := by
  rw [Int.fdiv_eq_ediv]; simp [Int.le_of_lt (pow2_pos n)]

/-- Unfolded form of `Zinsert x y p 16`. -/
theorem Zinsert_eq (x y p : Z) :
    Zinsert x y p 16 = y % 2 ^ 16 * 2 ^ p.toNat + (x - x / 2 ^ p.toNat % 2 ^ 16 * 2 ^ p.toNat) := by
  unfold Zinsert
  simp only [show (16 : Z).toNat = 16 from rfl, emod_eq', fdiv_pow2]

/-- Inserting into a number whose bits at and above `p` are zero. -/
theorem zinsert_low {accu y : Int} {p : Z} (h0 : 0 ≤ accu) (h1 : accu < 2 ^ p.toNat)
    (hy0 : 0 ≤ y) (hy1 : y < 2 ^ 16) : Zinsert accu y p 16 = y * 2 ^ p.toNat + accu := by
  rw [Zinsert_eq, Int.ediv_eq_zero_of_lt h0 h1, Int.emod_eq_of_lt hy0 hy1]
  simp

/-- `(-x-1) / P = -(x / P) - 1` -/
theorem lnot_ediv {x P : Int} (hP : 0 < P) : (-x - 1) / P = -(x / P) - 1 := by
  have h1 := Int.emod_def x P
  have h2 : 0 ≤ x % P := Int.emod_nonneg _ (by omega)
  have h3 : x % P < P := Int.emod_lt_of_pos _ hP
  have := (Int.ediv_emod_unique (a := -x - 1) (q := -(x / P) - 1) (r := P - x % P - 1) hP).2
    ⟨by grind, by omega, by omega⟩
  exact this.1

/-- `(-q-1) % B = B - 1 - q % B` -/
theorem lnot_emod {q B : Int} (hB : 0 < B) : (-q - 1) % B = B - 1 - q % B := by
  have h1 := Int.emod_def q B
  have h2 : 0 ≤ q % B := Int.emod_nonneg _ (by omega)
  have h3 : q % B < B := Int.emod_lt_of_pos _ hB
  have := (Int.ediv_emod_unique (a := -q - 1) (q := -(q / B) - 1) (r := B - 1 - q % B) hB).2
    ⟨by grind, by omega, by omega⟩
  exact this.2

/-- `Asmgenproof1.recompose_int_negated`, one step: inserting the complemented
    fragment into the complement. -/
theorem Zinsert_lnot (x f p : Z) (hf0 : 0 ≤ f) (hf1 : f < 2 ^ 16) :
    Zinsert (-x - 1) (65535 - f) p 16 = -(Zinsert x f p 16) - 1 := by
  have e16 : (2 : Int) ^ 16 = 65536 := rfl
  rw [e16] at hf1
  rw [Zinsert_eq, Zinsert_eq, lnot_ediv (pow2_pos _), lnot_emod (by decide),
    e16, Int.emod_eq_of_lt (b := 65536) (by zomega) (by zomega),
    Int.emod_eq_of_lt (b := 65536) hf0 hf1]
  grind

/-- `Zinsert` is compatible with congruence modulo `2^w` when the inserted
    field lies below bit `w`. -/
theorem Zinsert_eqm {w : Nat} {x1 x2 : Z} (y p : Z) (hp : 0 ≤ p) (hw : p.toNat + 16 ≤ w)
    (h : x1 % 2 ^ w = x2 % 2 ^ w) : Zinsert x1 y p 16 % 2 ^ w = Zinsert x2 y p 16 % 2 ^ w := by
  obtain ⟨k, hk⟩ : (2 : Int) ^ w ∣ x1 - x2 := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod, h, Int.sub_self, Int.zero_emod])
  have hw' : (2 : Int) ^ w = 2 ^ p.toNat * (2 ^ 16 * 2 ^ (w - p.toNat - 16)) := by
    rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
  have hx1 : x1 = x2 + 2 ^ p.toNat * (2 ^ 16 * (2 ^ (w - p.toNat - 16) * k)) := by
    rw [hw'] at hk; grind
  clear hk h
  generalize hP : (2 : Int) ^ p.toNat = P at *
  generalize hB : (2 : Int) ^ 16 = B at *
  generalize hC : (2 : Int) ^ (w - p.toNat - 16) = C at *
  have hPpos : 0 < P := hP ▸ pow2_pos _
  rw [Zinsert_eq, Zinsert_eq, hP, hB, hx1]
  have e1 : (x2 + P * (B * (C * k))) / P = x2 / P + B * (C * k) := by
    rw [Int.add_mul_ediv_left _ _ (by omega)]
  rw [e1, Int.add_mul_emod_self_left]
  have e2 : y % B * P + (x2 + P * (B * (C * k)) - x2 / P % B * P) =
      (y % B * P + (x2 - x2 / P % B * P)) + P * (B * C) * k := by grind
  rw [e2, hw', Int.add_mul_emod_self_left]

/-! ## Decomposition of integer literals -/

/-- `Asmgenproof1.recompose_int` -/
def recomposeInt : Z → List (Z × Z) → Z
  | accu, [] => accu
  | accu, (n, p) :: l => recomposeInt (Zinsert accu n p 16) l

theorem emod_sub_add {n f D K : Int} (hD : 0 < D) (hK : 0 < K) (hdvd : D ∣ n - f)
    (hf0 : 0 ≤ f) (hf1 : f < D) : (n - f) % (D * K) + f = n % (D * K) := by
  obtain ⟨t, ht⟩ := hdvd
  have h1 : 0 ≤ t % K := Int.emod_nonneg _ (by omega)
  have h2 : t % K < K := Int.emod_lt_of_pos _ hK
  have h4 : D * (t % K) ≤ D * (K - 1) :=
    Int.mul_le_mul_of_nonneg_left (show t % K ≤ K - 1 by omega) (Int.le_of_lt hD)
  have h5 : D * (K - 1) = D * K - D := by grind
  have h6 : 0 ≤ D * (t % K) := Int.mul_nonneg (Int.le_of_lt hD) h1
  have ht' : t = t % K + K * (t / K) := by have := Int.emod_def t K; omega
  have hn : n = (D * (t % K) + f) + (D * K) * (t / K) := by
    have : D * t = D * (t % K) + D * K * (t / K) := by
      conv => lhs; rw [ht']
      grind
    omega
  calc (n - f) % (D * K) + f = D * (t % K) + f := by rw [ht, Int.mul_emod_mul_of_pos _ _ hD]
    _ = (D * (t % K) + f) % (D * K) := (Int.emod_eq_of_lt (by omega) (by omega)).symm
    _ = n % (D * K) := by rw [hn, Int.add_mul_emod_self_left]

theorem decompose_step {n P B : Int} (hP : 0 < P) (hn : n % P = 0) :
    ∃ q, n = P * q ∧ n / P % B = q % B ∧ n - q % B * P = P * B * (q / B) := by
  obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hn
  refine ⟨q, hq, by rw [hq, Int.mul_ediv_cancel_left _ (by omega)], ?_⟩
  have := Int.emod_def q B
  rw [hq]; grind

theorem decompose_frag (n p : Z) :
    zzeroExt 16 (zshiftr n p) = n / 2 ^ p.toNat % 65536 := by
  simp only [zzeroExt, zshiftr, emod_eq', show ¬ ((16 : Z) ≤ 0) by decide, if_false,
    show (16 : Z).toNat = 16 from rfl, fdiv_pow2]
  rfl

/-- `Asmgenproof1.decompose_int_correct`, in arithmetic form. -/
theorem decompose_int_correct : ∀ (N : Nat) (n p accu : Z), 0 ≤ p → n % 2 ^ p.toNat = 0 →
    0 ≤ accu → accu < 2 ^ p.toNat →
    recomposeInt accu (decomposeInt N n p) = accu + n % 2 ^ (p.toNat + 16 * N)
  | 0, n, p, accu, hp, hn, h0, h1 => by simp [decomposeInt, recomposeInt, hn]
  | N + 1, n, p, accu, hp, hn, h0, h1 => by
    have hk : (p + 16).toNat = p.toNat + 16 := by zomega
    have hp16 : 0 ≤ p + 16 := by zomega
    have hfrag := decompose_frag n p
    generalize hPdef : (2:Int) ^ p.toNat = P at *
    have hP : 0 < P := hPdef ▸ pow2_pos _
    have hQ : (2:Int) ^ (p.toNat + 16) = P * 65536 := by rw [Int.pow_add, hPdef]; rfl
    have hM : (2:Int) ^ (p.toNat + 16 * (N+1)) = (P * 65536) * 2 ^ (16 * N) := by
      rw [← hQ, ← Int.pow_add]; congr 1; omega
    have hM' : (2:Int) ^ (p.toNat + 16 + 16 * N) = (P * 65536) * 2 ^ (16 * N) := by
      rw [← hQ, ← Int.pow_add]
    have hK := pow2_pos (16 * N)
    obtain ⟨q, hq, hfr, hsub⟩ := decompose_step (B := 65536) hP hn
    rw [hfr] at hfrag
    simp only [decomposeInt, hfrag]
    have hf0 : 0 ≤ q % 65536 := Int.emod_nonneg _ (by decide)
    have hf1 : q % 65536 < 65536 := Int.emod_lt_of_pos _ (by decide)
    have hacc : accu < P * 65536 := by
      have : P * 1 ≤ P * 65536 := Int.mul_le_mul_of_nonneg_left (by decide) (Int.le_of_lt hP)
      zomega
    split
    · rename_i hz
      have hz' : q % 65536 = 0 := by simpa using hz
      rw [decompose_int_correct N n (p + 16) accu hp16 ?_ h0 (by rw [hk, hQ]; exact hacc), hk,
        hM, hM']
      rw [hk, hQ]; rw [hz', Int.zero_mul, Int.sub_zero] at hsub
      rw [hsub]; exact Int.mul_emod_right _ _
    · simp only [recomposeInt]
      rw [zinsert_low h0 (by rw [hPdef]; exact h1) hf0 hf1, hPdef]
      have hf2 : q % 65536 * P ≤ 65535 * P :=
        Int.mul_le_mul_of_nonneg_right (show q % 65536 ≤ 65535 by omega) (Int.le_of_lt hP)
      have hf3 : 0 ≤ q % 65536 * P := Int.mul_nonneg hf0 (Int.le_of_lt hP)
      rw [decompose_int_correct N _ (p + 16) _ hp16 ?_ (by zomega) (by rw [hk, hQ]; zomega), hk,
        hM, hM']
      · have E := emod_sub_add (n := n) (f := q % 65536 * P) (D := P * 65536)
          (K := 2 ^ (16 * N)) (by omega) hK ⟨_, hsub⟩ hf3 (by omega)
        zomega
      · rw [hk, hQ, hsub]; exact Int.mul_emod_right _ _

/-- `Asmgenproof1.decompose_int_eqmod` -/
theorem decompose_int_eqmod (N : Nat) (n : Z) :
    recomposeInt 0 (decomposeInt N n 0) % 2 ^ (16 * N) = n % 2 ^ (16 * N) := by
  rw [decompose_int_correct N n 0 0 (Int.le_refl _) (Int.emod_one _) (Int.le_refl _) (by decide)]
  simp

/-- `Asmgenproof1.wf_decomposition`: fragments are 16-bit numbers inserted at
    nonnegative positions, below bit `w`. -/
def WfDecomp (w : Nat) (l : List (Z × Z)) : Prop :=
  ∀ np ∈ l, 0 ≤ np.1 ∧ np.1 < 2 ^ 16 ∧ 0 ≤ np.2 ∧ np.2.toNat + 16 ≤ w

/-- `Asmgenproof1.decompose_int_wf` -/
theorem decompose_int_wf : ∀ (N : Nat) (n p : Z) (w : Nat), 0 ≤ p → p.toNat + 16 * N ≤ w →
    WfDecomp w (decomposeInt N n p)
  | 0, _, _, _, _, _ => by simp [decomposeInt, WfDecomp]
  | N + 1, n, p, w, hp, hw => by
    have ih := fun n' => decompose_int_wf N n' (p + 16) w (by zomega) (by zomega)
    simp only [decomposeInt]
    split
    · exact ih n
    · intro np hnp
      rcases List.mem_cons.mp hnp with rfl | hnp
      · rw [decompose_frag]
        exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide), hp, by zomega⟩
      · exact ih _ np hnp

/-- `Asmgenproof1.negate_decomposition_wf` -/
theorem negate_decomposition_wf {w : Nat} {l : List (Z × Z)} (h : WfDecomp w l) :
    WfDecomp w (negateDecomposition l) := by
  intro np hnp
  obtain ⟨np', hm, rfl⟩ := List.mem_map.mp hnp
  obtain ⟨h1, h2, h3, h4⟩ := h np' hm
  exact ⟨by simp only [Z] at *; omega, by simp only [Z] at *; omega, h3, h4⟩

/-- `Asmgenproof1.recompose_int_negated` -/
theorem recompose_int_negated {w : Nat} : ∀ {l : List (Z × Z)}, WfDecomp w l → ∀ accu : Z,
    recomposeInt (-accu - 1) (negateDecomposition l) = -(recomposeInt accu l) - 1
  | [], _, _ => rfl
  | (n, p) :: l, h, accu => by
    obtain ⟨h1, h2, _, _⟩ := h (n, p) List.mem_cons_self
    show recomposeInt (Zinsert (-accu - 1) (65535 - n) p 16) (negateDecomposition l) = _
    rw [Zinsert_lnot _ _ _ h1 h2,
      recompose_int_negated (fun np hnp => h np (List.mem_cons_of_mem _ hnp))]
    rfl

/-! ## Loading integer immediates -/

theorem nextinstr_set_PC (rs : Regset) {r : Preg} (v : Val) (hr : r ≠ .PC) :
    nextinstr (rs.set r v) .PC = Val.offsetPtr (rs .PC) Integers.Ptrofs.one := by
  rw [nextinstr_pc, Regset.gso _ _ hr.symm]

theorem nextinstr_set_same (rs : Regset) {r : Preg} (v : Val) (hr : r ≠ .PC) :
    nextinstr (rs.set r v) r = v := by
  rw [nextinstr_inv _ hr, Regset.gss]

theorem nextinstr_set_other (rs : Regset) {r r' : Preg} (v : Val) (h1 : r' ≠ .PC) (h2 : r' ≠ r) :
    nextinstr (rs.set r v) r' = rs r' := by
  rw [nextinstr_inv _ h1, Regset.gso _ _ h2]

theorem int_modulus : Integers.Int.modulus = 2 ^ 32 := rfl
theorem int64_modulus : Integers.Int64.modulus = 2 ^ 64 := rfl

theorem int_repr_emod (z : Z) : Integers.Int.repr (z % 2 ^ 32) = Integers.Int.repr z :=
  Integers.Int.eqm_samerepr (Integers.Int.eqm_iff_emod.2 (by rw [int_modulus, Int.emod_emod]))

theorem int64_repr_emod (z : Z) : Integers.Int64.repr (z % 2 ^ 64) = Integers.Int64.repr z :=
  Integers.Int64.eqm_samerepr (Integers.Int64.eqm_iff_emod.2 (by rw [int64_modulus, Int.emod_emod]))

theorem int_repr_eq_of_emod {x y : Z} (h : x % 2 ^ 32 = y % 2 ^ 32) :
    Integers.Int.repr x = Integers.Int.repr y :=
  Integers.Int.eqm_samerepr (Integers.Int.eqm_iff_emod.2 (by rw [int_modulus]; exact h))

theorem int64_repr_eq_of_emod {x y : Z} (h : x % 2 ^ 64 = y % 2 ^ 64) :
    Integers.Int64.repr x = Integers.Int64.repr y :=
  Integers.Int64.eqm_samerepr (Integers.Int64.eqm_iff_emod.2 (by rw [int64_modulus]; exact h))

section CONSTRUCTORS
variable (sym : SymbolSplit) (ge : Asm.CGenv) (fn : Asm.Function)

/-- `Asmgenproof1.exec_loadimm_k_w` -/
theorem exec_loadimm_k_w (rd : Ireg) (k : Code) (m : Mem) :
    ∀ (l : List (Z × Z)), WfDecomp 32 l → ∀ (rs : Regset) (accu : Z),
      rs (.IR rd) = .Vint (Integers.Int.repr accu) →
      ∃ rs', ExecStraightOpt sym ge fn (loadimmK .W rd l k) rs m k rs' m ∧
        rs' (.IR rd) = .Vint (Integers.Int.repr (recomposeInt accu l)) ∧
        ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r
  | [], _, rs, accu, h => ⟨rs, .refl _ _ _, h, fun _ _ _ => rfl⟩
  | (n, p) :: l, hwf, rs, accu, h => by
    obtain ⟨_, _, hp, hw⟩ := hwf (n, p) List.mem_cons_self
    have hrd : Preg.IR rd ≠ .PC := by simp
    obtain ⟨rs', P, Q, R⟩ := exec_loadimm_k_w rd k m l
      (fun np hnp => hwf np (List.mem_cons_of_mem _ hnp))
      (nextinstr (rs.set (.IR rd) (insertInInt (rs (.IR rd)) n p 16))) (Zinsert accu n p 16)
      (by
        rw [nextinstr_set_same _ _ hrd, h]
        simp only [insertInInt, Integers.Int.unsigned_repr_eq, int_modulus]
        congr 1
        apply int_repr_eq_of_emod
        exact Zinsert_eqm n p hp hw (Int.emod_emod _ _))
    refine ⟨rs', exec_straight_opt_step_opt rfl (nextinstr_set_PC _ _ hrd) P, Q, fun r h1 h2 => ?_⟩
    rw [R r h1 h2, nextinstr_set_other _ _ h1 h2]

/-- `Asmgenproof1.exec_loadimm_k_x` -/
theorem exec_loadimm_k_x (rd : Ireg) (k : Code) (m : Mem) :
    ∀ (l : List (Z × Z)), WfDecomp 64 l → ∀ (rs : Regset) (accu : Z),
      rs (.IR rd) = .Vlong (Integers.Int64.repr accu) →
      ∃ rs', ExecStraightOpt sym ge fn (loadimmK .X rd l k) rs m k rs' m ∧
        rs' (.IR rd) = .Vlong (Integers.Int64.repr (recomposeInt accu l)) ∧
        ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r
  | [], _, rs, accu, h => ⟨rs, .refl _ _ _, h, fun _ _ _ => rfl⟩
  | (n, p) :: l, hwf, rs, accu, h => by
    obtain ⟨_, _, hp, hw⟩ := hwf (n, p) List.mem_cons_self
    have hrd : Preg.IR rd ≠ .PC := by simp
    obtain ⟨rs', P, Q, R⟩ := exec_loadimm_k_x rd k m l
      (fun np hnp => hwf np (List.mem_cons_of_mem _ hnp))
      (nextinstr (rs.set (.IR rd) (insertInLong (rs (.IR rd)) n p 16))) (Zinsert accu n p 16)
      (by
        rw [nextinstr_set_same _ _ hrd, h]
        simp only [insertInLong, Integers.Int64.unsigned_repr_eq, int64_modulus]
        congr 1
        apply int64_repr_eq_of_emod
        exact Zinsert_eqm n p hp hw (Int.emod_emod _ _))
    refine ⟨rs', exec_straight_opt_step_opt rfl (nextinstr_set_PC _ _ hrd) P, Q, fun r h1 h2 => ?_⟩
    rw [R r h1 h2, nextinstr_set_other _ _ h1 h2]

theorem emod_congr_lnot {x y M : Int} (h : x % M = y % M) : (-x - 1) % M = (-y - 1) % M := by
  obtain ⟨c, hc⟩ : M ∣ y - x := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod, h, Int.sub_self, Int.zero_emod])
  have : -x - 1 = (-y - 1) + M * c := by omega
  rw [this, Int.add_mul_emod_self_left]

theorem shiftLeft_zinsert {n p : Z} (h0 : 0 ≤ n) (h1 : n < 2 ^ 16) :
    n <<< p.toNat = Zinsert 0 n p 16 := by
  rw [zinsert_low (Int.le_refl _) (pow2_pos _) h0 h1, Int.shiftLeft_eq, Int.add_zero]

/-- `Asmgenproof1.exec_loadimm_z_w` -/
theorem exec_loadimm_z_w (rd : Ireg) (l : List (Z × Z)) (k : Code) (rs : Regset) (m : Mem)
    (hwf : WfDecomp 32 l) :
    ∃ rs', ExecStraight sym ge fn (loadimmZ .W rd l k) rs m k rs' m ∧
      rs' (.IR rd) = .Vint (Integers.Int.repr (recomposeInt 0 l)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  match l, hwf with
  | [], _ =>
    exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd),
      by rw [nextinstr_set_same _ _ hrd]; rfl, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
  | (n1, p1) :: l, hwf =>
    obtain ⟨h0, h1, _, _⟩ := hwf (n1, p1) List.mem_cons_self
    obtain ⟨rs', P, Q, R⟩ := exec_loadimm_k_w sym ge fn rd k m l
      (fun np hnp => hwf np (List.mem_cons_of_mem _ hnp))
      (nextinstr (rs.set (.IR rd) (.Vint (Integers.Int.repr (n1 <<< p1.toNat)))))
      (Zinsert 0 n1 p1 16)
      (by rw [nextinstr_set_same _ _ hrd, shiftLeft_zinsert h0 h1])
    exact ⟨rs', exec_straight_opt_step rfl (nextinstr_set_PC _ _ hrd) P, Q,
      fun r h1 h2 => by rw [R r h1 h2, nextinstr_set_other _ _ h1 h2]⟩

/-- `Asmgenproof1.exec_loadimm_n_w` -/
theorem exec_loadimm_n_w (rd : Ireg) (l : List (Z × Z)) (k : Code) (rs : Regset) (m : Mem)
    (hwf : WfDecomp 32 l) :
    ∃ rs', ExecStraight sym ge fn (loadimmN .W rd l k) rs m k rs' m ∧
      rs' (.IR rd) = .Vint (Integers.Int.repr (-(recomposeInt 0 l) - 1)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  match l, hwf with
  | [], _ =>
    exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd),
      by rw [nextinstr_set_same _ _ hrd]; rfl, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
  | (n1, p1) :: l, hwf =>
    obtain ⟨h0, h1, _, _⟩ := hwf (n1, p1) List.mem_cons_self
    have hwf' : WfDecomp 32 l := fun np hnp => hwf np (List.mem_cons_of_mem _ hnp)
    obtain ⟨rs', P, Q, R⟩ := exec_loadimm_k_w sym ge fn rd k m (negateDecomposition l)
      (negate_decomposition_wf hwf')
      (nextinstr (rs.set (.IR rd) (.Vint (Integers.Int.repr (-(n1 <<< p1.toNat) - 1)))))
      (-(Zinsert 0 n1 p1 16) - 1)
      (by rw [nextinstr_set_same _ _ hrd, shiftLeft_zinsert h0 h1])
    rw [recompose_int_negated hwf'] at Q
    exact ⟨rs', exec_straight_opt_step rfl (nextinstr_set_PC _ _ hrd) P, Q,
      fun r h1 h2 => by rw [R r h1 h2, nextinstr_set_other _ _ h1 h2]⟩

/-- `Asmgenproof1.exec_loadimm_z_x` -/
theorem exec_loadimm_z_x (rd : Ireg) (l : List (Z × Z)) (k : Code) (rs : Regset) (m : Mem)
    (hwf : WfDecomp 64 l) :
    ∃ rs', ExecStraight sym ge fn (loadimmZ .X rd l k) rs m k rs' m ∧
      rs' (.IR rd) = .Vlong (Integers.Int64.repr (recomposeInt 0 l)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  match l, hwf with
  | [], _ =>
    exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd),
      by rw [nextinstr_set_same _ _ hrd]; rfl, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
  | (n1, p1) :: l, hwf =>
    obtain ⟨h0, h1, _, _⟩ := hwf (n1, p1) List.mem_cons_self
    obtain ⟨rs', P, Q, R⟩ := exec_loadimm_k_x sym ge fn rd k m l
      (fun np hnp => hwf np (List.mem_cons_of_mem _ hnp))
      (nextinstr (rs.set (.IR rd) (.Vlong (Integers.Int64.repr (n1 <<< p1.toNat)))))
      (Zinsert 0 n1 p1 16)
      (by rw [nextinstr_set_same _ _ hrd, shiftLeft_zinsert h0 h1])
    exact ⟨rs', exec_straight_opt_step rfl (nextinstr_set_PC _ _ hrd) P, Q,
      fun r h1 h2 => by rw [R r h1 h2, nextinstr_set_other _ _ h1 h2]⟩

/-- `Asmgenproof1.exec_loadimm_n_x` -/
theorem exec_loadimm_n_x (rd : Ireg) (l : List (Z × Z)) (k : Code) (rs : Regset) (m : Mem)
    (hwf : WfDecomp 64 l) :
    ∃ rs', ExecStraight sym ge fn (loadimmN .X rd l k) rs m k rs' m ∧
      rs' (.IR rd) = .Vlong (Integers.Int64.repr (-(recomposeInt 0 l) - 1)) ∧
      ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  match l, hwf with
  | [], _ =>
    exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd),
      by rw [nextinstr_set_same _ _ hrd]; rfl, fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
  | (n1, p1) :: l, hwf =>
    obtain ⟨h0, h1, _, _⟩ := hwf (n1, p1) List.mem_cons_self
    have hwf' : WfDecomp 64 l := fun np hnp => hwf np (List.mem_cons_of_mem _ hnp)
    obtain ⟨rs', P, Q, R⟩ := exec_loadimm_k_x sym ge fn rd k m (negateDecomposition l)
      (negate_decomposition_wf hwf')
      (nextinstr (rs.set (.IR rd) (.Vlong (Integers.Int64.repr (-(n1 <<< p1.toNat) - 1)))))
      (-(Zinsert 0 n1 p1 16) - 1)
      (by rw [nextinstr_set_same _ _ hrd, shiftLeft_zinsert h0 h1])
    rw [recompose_int_negated hwf'] at Q
    exact ⟨rs', exec_straight_opt_step rfl (nextinstr_set_PC _ _ hrd) P, Q,
      fun r h1 h2 => by rw [R r h1 h2, nextinstr_set_other _ _ h1 h2]⟩

/-- `Asmgenproof1.exec_loadimm32` -/
theorem exec_loadimm32 (rd : Ireg) (n : Integers.Int) (k : Code) (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (loadimm32 rd n k) rs m k rs' m ∧
      rs' (.IR rd) = .Vint n ∧ ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  unfold loadimm32
  split
  · refine ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ hrd]
    simp only [ir0w, Val.or, Integers.Int.repr_unsigned, Integers.Int.or_zero_l]
  · unfold loadimm
    simp only
    split
    · obtain ⟨rs', P, Q, R⟩ := exec_loadimm_z_w sym ge fn rd (decomposeInt 2 (Integers.Int.unsigned n) 0)
        k rs m (decompose_int_wf 2 _ 0 32 (Int.le_refl _) (by decide))
      refine ⟨rs', P, ?_, R⟩
      rw [Q, int_repr_eq_of_emod (decompose_int_eqmod 2 _), Integers.Int.repr_unsigned]
    · obtain ⟨rs', P, Q, R⟩ := exec_loadimm_n_w sym ge fn rd
        (decomposeInt 2 (-Integers.Int.unsigned n - 1) 0)
        k rs m (decompose_int_wf 2 _ 0 32 (Int.le_refl _) (by decide))
      refine ⟨rs', P, ?_, R⟩
      rw [Q, int_repr_eq_of_emod (emod_congr_lnot (decompose_int_eqmod 2 _))]
      rw [show -(-Integers.Int.unsigned n - 1) - 1 = Integers.Int.unsigned n by zomega,
        Integers.Int.repr_unsigned]

/-- `Asmgenproof1.exec_loadimm64` -/
theorem exec_loadimm64 (rd : Ireg) (n : Integers.Int64) (k : Code) (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (loadimm64 rd n k) rs m k rs' m ∧
      rs' (.IR rd) = .Vlong n ∧ ∀ r, r ≠ .PC → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  unfold loadimm64
  split
  · refine ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ h1 h2⟩
    rw [nextinstr_set_same _ _ hrd]
    simp only [ir0x, Val.orl, Integers.Int64.repr_unsigned, Integers.Int64.or_zero_l]
  · unfold loadimm
    simp only
    split
    · obtain ⟨rs', P, Q, R⟩ := exec_loadimm_z_x sym ge fn rd
        (decomposeInt 4 (Integers.Int64.unsigned n) 0)
        k rs m (decompose_int_wf 4 _ 0 64 (Int.le_refl _) (by decide))
      refine ⟨rs', P, ?_, R⟩
      rw [Q, int64_repr_eq_of_emod (decompose_int_eqmod 4 _), Integers.Int64.repr_unsigned]
    · obtain ⟨rs', P, Q, R⟩ := exec_loadimm_n_x sym ge fn rd
        (decomposeInt 4 (-Integers.Int64.unsigned n - 1) 0)
        k rs m (decompose_int_wf 4 _ 0 64 (Int.le_refl _) (by decide))
      refine ⟨rs', P, ?_, R⟩
      rw [Q, int64_repr_eq_of_emod (emod_congr_lnot (decompose_int_eqmod 4 _))]
      rw [show -(-Integers.Int64.unsigned n - 1) - 1 = Integers.Int64.unsigned n by zomega,
        Integers.Int64.repr_unsigned]

theorem dataPreg_ne_PC {r : Preg} (h : dataPreg r = true) : r ≠ .PC := by
  rintro rfl; cases h

theorem dataPreg_ne_X16 {r : Preg} (h : dataPreg r = true) : r ≠ .IR .X16 := by
  rintro rfl; cases h

/-! ## Add immediate -/

/-- `Asmgenproof1.exec_addimm_aux_32` -/
theorem exec_addimm_aux_32 (insn : Iregsp → Iregsp → Z → Instruction) (sem : Val → Val → Val)
    (SEM : ∀ rd r1 n rs m, execInstr sym ge fn (insn rd r1 n) rs m =
      .Next (nextinstr (rs.set (pregOfIregsp rd) (sem (rs (pregOfIregsp r1))
        (.Vint (Integers.Int.repr n))))) m)
    (ASSOC : ∀ v n1 n2, sem (sem v (.Vint n1)) (.Vint n2) = sem v (.Vint (Integers.Int.add n1 n2)))
    (rd r1 : Iregsp) (n : Integers.Int) (k : Code) (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (addimmAux insn rd r1 (Integers.Int.unsigned n) k) rs m k rs' m ∧
      rs' (pregOfIregsp rd) = sem (rs (pregOfIregsp r1)) (.Vint n) ∧
      ∀ r, dataPreg r = true → r ≠ pregOfIregsp rd → rs' r = rs r := by
  have hrd := preg_of_iregsp_not_PC rd
  unfold addimmAux
  simp only
  generalize hlo : zzeroExt 12 (Integers.Int.unsigned n) = nlo
  have E : Integers.Int.unsigned n = (Integers.Int.unsigned n - nlo) + nlo := by zomega
  split
  · rename_i h0
    have : Integers.Int.unsigned n - nlo = 0 := by simpa using h0
    refine ⟨_, .one _ _ _ _ _ _ (SEM _ _ _ _ _) (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    rw [nextinstr_set_same _ _ hrd, show nlo = Integers.Int.unsigned n by zomega,
      Integers.Int.repr_unsigned]
  split
  · rename_i _ h0
    have : nlo = 0 := by simpa using h0
    refine ⟨_, .one _ _ _ _ _ _ (SEM _ _ _ _ _) (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    rw [nextinstr_set_same _ _ hrd, show Integers.Int.unsigned n - nlo = Integers.Int.unsigned n by
      zomega, Integers.Int.repr_unsigned]
  · refine ⟨_, exec_straight_two (SEM _ _ _ _ _) (SEM _ _ _ _ _) (nextinstr_set_PC _ _ hrd)
      (nextinstr_set_PC _ _ hrd), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd, nextinstr_set_same _ _ hrd, ASSOC,
        ← Integers.Int.repr_add, ← E, Integers.Int.repr_unsigned]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]

/-- `Asmgenproof1.exec_addimm_aux_64` -/
theorem exec_addimm_aux_64 (insn : Iregsp → Iregsp → Z → Instruction) (sem : Val → Val → Val)
    (SEM : ∀ rd r1 n rs m, execInstr sym ge fn (insn rd r1 n) rs m =
      .Next (nextinstr (rs.set (pregOfIregsp rd) (sem (rs (pregOfIregsp r1))
        (.Vlong (Integers.Int64.repr n))))) m)
    (ASSOC : ∀ v n1 n2, sem (sem v (.Vlong n1)) (.Vlong n2) =
      sem v (.Vlong (Integers.Int64.add n1 n2)))
    (rd r1 : Iregsp) (n : Integers.Int64) (k : Code) (rs : Regset) (m : Mem) :
    ∃ rs', ExecStraight sym ge fn (addimmAux insn rd r1 (Integers.Int64.unsigned n) k) rs m k rs' m ∧
      rs' (pregOfIregsp rd) = sem (rs (pregOfIregsp r1)) (.Vlong n) ∧
      ∀ r, dataPreg r = true → r ≠ pregOfIregsp rd → rs' r = rs r := by
  have hrd := preg_of_iregsp_not_PC rd
  unfold addimmAux
  simp only
  generalize hlo : zzeroExt 12 (Integers.Int64.unsigned n) = nlo
  have E : Integers.Int64.unsigned n = (Integers.Int64.unsigned n - nlo) + nlo := by zomega
  split
  · rename_i h0
    have : Integers.Int64.unsigned n - nlo = 0 := by simpa using h0
    refine ⟨_, .one _ _ _ _ _ _ (SEM _ _ _ _ _) (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    rw [nextinstr_set_same _ _ hrd, show nlo = Integers.Int64.unsigned n by zomega,
      Integers.Int64.repr_unsigned]
  split
  · rename_i _ h0
    have : nlo = 0 := by simpa using h0
    refine ⟨_, .one _ _ _ _ _ _ (SEM _ _ _ _ _) (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    rw [nextinstr_set_same _ _ hrd, show Integers.Int64.unsigned n - nlo =
      Integers.Int64.unsigned n by zomega, Integers.Int64.repr_unsigned]
  · refine ⟨_, exec_straight_two (SEM _ _ _ _ _) (SEM _ _ _ _ _) (nextinstr_set_PC _ _ hrd)
      (nextinstr_set_PC _ _ hrd), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd, nextinstr_set_same _ _ hrd, ASSOC,
        ← Integers.Int64.repr_add, ← E, Integers.Int64.repr_unsigned]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]

/-- `Asmgenproof1.exec_addimm32` -/
theorem exec_addimm32 (rd r1 : Ireg) (n : Integers.Int) (k : Code) (rs : Regset) (m : Mem)
    (hr1 : r1 ≠ .X16) :
    ∃ rs', ExecStraight sym ge fn (addimm32 rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = Val.add (rs (.IR r1)) (.Vint n) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  have hr1' : Preg.IR r1 ≠ .IR .X16 := fun e => hr1 (Preg.IR.inj e)
  unfold addimm32
  simp only
  split
  · exact exec_addimm_aux_32 sym ge fn _ Val.add (fun _ _ _ _ _ => rfl)
      (fun v _ _ => Val.add_assoc _ _ _) (.RR1 rd) (.RR1 r1) n k rs m
  split
  · rw [← Val.sub_opp_add]
    exact exec_addimm_aux_32 sym ge fn _ Val.sub (fun _ _ _ _ _ => rfl)
      (fun v _ _ => by
        rw [Val.sub_add_opp, Val.sub_add_opp, Val.sub_add_opp, Val.add_assoc,
          Integers.Int.neg_add_distr]; rfl) (.RR1 rd) (.RR1 r1) _ k rs m
  split
  · obtain ⟨rs1, A, B, C⟩ := exec_loadimm32 sym ge fn .X16 (Integers.Int.neg n) _ rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd)), ?_,
      fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      show Val.sub (rs1 (.IR r1)) (evalShiftOpInt (rs1 (.IR .X16)) .SOnone) = _
      rw [B, C _ (by simp) hr1', evalShiftOpInt, Val.sub_opp_add]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        C _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]
  · obtain ⟨rs1, A, B, C⟩ := exec_loadimm32 sym ge fn .X16 n _ rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd)), ?_,
      fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      show Val.add (rs1 (.IR r1)) (evalShiftOpInt (rs1 (.IR .X16)) .SOnone) = _
      rw [B, C _ (by simp) hr1', evalShiftOpInt]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        C _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]

theorem shll_zero (x : Integers.Int64) :
    Val.shll (.Vlong x) (.Vint Integers.Int.zero) = .Vlong x := by
  have : Val.shll (.Vlong x) (.Vint Integers.Int.zero) =
      .Vlong (Integers.Int64.shl x (Integers.Int64.repr (Integers.Int.unsigned Integers.Int.zero))) :=
    rfl
  rw [this, Integers.Int.unsigned_zero]
  exact congrArg _ (Integers.Int64.shl_zero x)

/-- `Asmgenproof1.exec_addimm64` -/
theorem exec_addimm64 (rd r1 : Iregsp) (n : Integers.Int64) (k : Code) (rs : Regset) (m : Mem)
    (hr1 : pregOfIregsp r1 ≠ .IR .X16) :
    ∃ rs', ExecStraight sym ge fn (addimm64 rd r1 n k) rs m k rs' m ∧
      rs' (pregOfIregsp rd) = Val.addl (rs (pregOfIregsp r1)) (.Vlong n) ∧
      ∀ r, dataPreg r = true → r ≠ pregOfIregsp rd → rs' r = rs r := by
  have hrd := preg_of_iregsp_not_PC rd
  unfold addimm64
  simp only
  split
  · exact exec_addimm_aux_64 sym ge fn _ Val.addl (fun _ _ _ _ _ => rfl)
      (fun v _ _ => Val.addl_assoc _ _ _) rd r1 n k rs m
  split
  · rw [← Val.subl_opp_addl]
    exact exec_addimm_aux_64 sym ge fn _ Val.subl (fun _ _ _ _ _ => rfl)
      (fun v _ _ => by
        rw [Val.subl_addl_opp, Val.subl_addl_opp, Val.subl_addl_opp, Val.addl_assoc,
          Integers.Int64.neg_add_distr]; rfl) rd r1 _ k rs m
  split
  · obtain ⟨rs1, A, B, C⟩ := exec_loadimm64 sym ge fn .X16 (Integers.Int64.neg n) _ rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd)), ?_,
      fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      show Val.subl (rs1 (pregOfIregsp r1)) (evalExtend (rs1 (.IR .X16)) _) = _
      rw [B, C _ (preg_of_iregsp_not_PC r1) hr1, evalExtend, shll_zero, Val.subl_opp_addl]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        C _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]
  · obtain ⟨rs1, A, B, C⟩ := exec_loadimm64 sym ge fn .X16 n _ rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd)), ?_,
      fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      show Val.addl (rs1 (pregOfIregsp r1)) (evalExtend (rs1 (.IR .X16)) _) = _
      rw [B, C _ (preg_of_iregsp_not_PC r1) hr1, evalExtend, shll_zero]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        C _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]

/-! ## Logical immediate -/

/-- `Asmgenproof1.exec_logicalimm32` -/
theorem exec_logicalimm32 (insn1 : Ireg → Ireg0 → Z → Instruction)
    (insn2 : Ireg → Ireg0 → Ireg → ShiftOp → Instruction) (sem : Val → Val → Val)
    (SEM1 : ∀ rd r1 n rs m, execInstr sym ge fn (insn1 rd r1 n) rs m =
      .Next (nextinstr (rs.set (.IR rd) (sem (ir0w rs r1) (.Vint (Integers.Int.repr n))))) m)
    (SEM2 : ∀ rd r1 r2 s rs m, execInstr sym ge fn (insn2 rd r1 r2 s) rs m =
      .Next (nextinstr (rs.set (.IR rd) (sem (ir0w rs r1) (evalShiftOpInt (rs (.IR r2)) s)))) m)
    (rd r1 : Ireg) (n : Integers.Int) (k : Code) (rs : Regset) (m : Mem) (hr1 : r1 ≠ .X16) :
    ∃ rs', ExecStraight sym ge fn (logicalimm32 insn1 insn2 rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = sem (rs (.IR r1)) (.Vint n) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  have hr1' : Preg.IR r1 ≠ .IR .X16 := fun e => hr1 (Preg.IR.inj e)
  unfold logicalimm32
  split
  · refine ⟨_, .one _ _ _ _ _ _ (SEM1 _ _ _ _ _) (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    rw [nextinstr_set_same _ _ hrd, Integers.Int.repr_unsigned]; rfl
  · obtain ⟨rs1, A, B, C⟩ := exec_loadimm32 sym ge fn .X16 n _ rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ (SEM2 _ _ _ _ _ _)
      (nextinstr_set_PC _ _ hrd)), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd, B]
      show sem (rs1 (.IR r1)) _ = _
      rw [C _ (by simp) hr1']; rfl
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        C _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]

/-- `Asmgenproof1.exec_logicalimm64` -/
theorem exec_logicalimm64 (insn1 : Ireg → Ireg0 → Z → Instruction)
    (insn2 : Ireg → Ireg0 → Ireg → ShiftOp → Instruction) (sem : Val → Val → Val)
    (SEM1 : ∀ rd r1 n rs m, execInstr sym ge fn (insn1 rd r1 n) rs m =
      .Next (nextinstr (rs.set (.IR rd) (sem (ir0x rs r1) (.Vlong (Integers.Int64.repr n))))) m)
    (SEM2 : ∀ rd r1 r2 s rs m, execInstr sym ge fn (insn2 rd r1 r2 s) rs m =
      .Next (nextinstr (rs.set (.IR rd) (sem (ir0x rs r1) (evalShiftOpLong (rs (.IR r2)) s)))) m)
    (rd r1 : Ireg) (n : Integers.Int64) (k : Code) (rs : Regset) (m : Mem) (hr1 : r1 ≠ .X16) :
    ∃ rs', ExecStraight sym ge fn (logicalimm64 insn1 insn2 rd r1 n k) rs m k rs' m ∧
      rs' (.IR rd) = sem (rs (.IR r1)) (.Vlong n) ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  have hr1' : Preg.IR r1 ≠ .IR .X16 := fun e => hr1 (Preg.IR.inj e)
  unfold logicalimm64
  split
  · refine ⟨_, .one _ _ _ _ _ _ (SEM1 _ _ _ _ _) (nextinstr_set_PC _ _ hrd), ?_,
      fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    rw [nextinstr_set_same _ _ hrd, Integers.Int64.repr_unsigned]; rfl
  · obtain ⟨rs1, A, B, C⟩ := exec_loadimm64 sym ge fn .X16 n _ rs m
    refine ⟨_, exec_straight_trans A (.one _ _ _ _ _ _ (SEM2 _ _ _ _ _ _)
      (nextinstr_set_PC _ _ hrd)), ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd, B]
      show sem (rs1 (.IR r1)) _ = _
      rw [C _ (by simp) hr1']; rfl
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        C _ (dataPreg_ne_PC h1) (dataPreg_ne_X16 h1)]

/-! ## Loading the address of a symbol -/

theorem ptrofs_of_int64_to_int64 (ofs : Integers.Ptrofs) :
    Integers.Ptrofs.of_int64 (Integers.Ptrofs.to_int64 ofs) = ofs := by
  show BitVec.ofInt 64 ((BitVec.zeroExtend 64 ofs).toNat : _root_.Int) = ofs
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  have := ofs.isLt
  have h2 : (2 : Nat) ^ Archi.ptrWordsize = 2 ^ 64 := rfl
  have h3 : ofs.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h3, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  simp

/-- `Asmgenproof1.exec_loadsymbol` -/
theorem exec_loadsymbol (o : Options) (rd : Ireg) (s : Ident) (ofs : Integers.Ptrofs) (k : Code)
    (rs : Regset) (m : Mem) (h : rd ≠ .X16 ∨ o.symbolIsRelocatable s = false) :
    ∃ rs', ExecStraight sym ge fn (loadsymbol o rd s ofs k) rs m k rs' m ∧
      rs' (.IR rd) = Genv.symbolAddress ge s ofs ∧
      ∀ r, dataPreg r = true → r ≠ .IR rd → rs' r = rs r := by
  have hrd : Preg.IR rd ≠ .PC := by simp
  unfold loadsymbol
  split
  · rename_i hrel
    split
    · rename_i he
      have := (Integers.Ptrofs.eq_spec ofs Integers.Ptrofs.zero).1 he
      subst this
      exact ⟨_, .one _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd), nextinstr_set_same _ _ hrd,
        fun r h1 h2 => nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2⟩
    · have hx : pregOfIregsp (.RR1 rd) ≠ .IR .X16 := by
        rcases h with h | h
        · exact fun e => h (Preg.IR.inj e)
        · rw [hrel] at h; cases h
      obtain ⟨rs1, A, B, C⟩ := exec_addimm64 sym ge fn (.RR1 rd) (.RR1 rd)
        (Integers.Ptrofs.to_int64 ofs) k
        (nextinstr (rs.set (.IR rd) (Genv.symbolAddress ge s Integers.Ptrofs.zero))) m hx
      refine ⟨rs1, .step _ _ _ _ _ _ _ _ _ rfl (nextinstr_set_PC _ _ hrd) A, ?_, fun r h1 h2 => ?_⟩
      · show rs1 (pregOfIregsp (.RR1 rd)) = _
        rw [B]
        show Val.addl (nextinstr (rs.set (.IR rd) _) (.IR rd)) _ = _
        rw [nextinstr_set_same _ _ hrd, ← Genv.shift_symbolAddress_64, ptrofs_of_int64_to_int64,
          Integers.Ptrofs.add_zero_l]
      · rw [C r h1 h2, nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]
  · refine ⟨_, exec_straight_two rfl rfl (nextinstr_set_PC _ _ hrd) (nextinstr_set_PC _ _ hrd),
      ?_, fun r h1 h2 => ?_⟩
    · rw [nextinstr_set_same _ _ hrd]
      show Val.addl (nextinstr (rs.set (.IR rd) _) (.IR rd)) _ = _
      rw [nextinstr_set_same _ _ hrd, sym.symbol_high_low]
    · rw [nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2,
        nextinstr_set_other _ _ (dataPreg_ne_PC h1) h2]

end CONSTRUCTORS

end Asmgenproof1
end CC
