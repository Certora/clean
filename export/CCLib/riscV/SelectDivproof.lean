/-
  Correctness of instruction selection for integer division, RISC-V instance —
  port of `backend/SelectDivproof.v` (`Section CMCONSTRS`) for the RISC-V
  operators: the smart constructors `divu`, `modu`, `divs`, `mods` (32 bits)
  and `divlu`, `modlu`, `divls`, `modls` (64 bits) of
  `CCLib/riscV/SelectDiv.lean` compute the quotient / remainder.

  The target-independent arithmetic part of `SelectDivproof.v`
  (Granlund–Montgomery approximation, soundness of the division parameters,
  the `div*_mul_shift` identities) is reused from
  `CCLib/backend/SelectDivproof.lean`.  This file follows
  `CCLib/backend/SelectDivproof2.lean` (the aarch64 instance).

  Differences from Rocq: `Compopts.optim_for_size` is the explicit Boolean
  argument `ofs`; the section variables `prog`/`hf` are not needed (on RV64
  the 64-bit operations do not call helper functions), so the global
  environment `ge` is arbitrary.  The floating-point part (`eval_divf`,
  `eval_divfs`) is in `CCLib/riscV/SelectionproofExpr.lean`.
-/
import CCLib.backend.SelectDivproof
import CCLib.riscV.SelectDiv
import CCLib.riscV.SelectLongproof2

namespace CC
namespace RiscV
namespace SelectDivproof

open CC.SelectDivproof
open Op CminorSel SelectOp SelectDiv SelectOpproof
open SelectLong hiding isIntconst
open SelectLongproof hiding isIntconst_sound isLongconst_sound
open CC.SelectDiv (divsMulParams divuMulParams divlsMulParams divluMulParams)

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

local macro "ld" : tactic => `(tactic| first | exact Val.Lessdef.refl _ | exact Val.Lessdef.undef _)

theorem lessdef_vint {a : Integers.Int} {v : Val} (h : Val.Lessdef (.Vint a) v) : v = .Vint a := by
  cases h; rfl

theorem lessdef_vlong {a : Integers.Int64} {v : Val} (h : Val.Lessdef (.Vlong a) v) :
    v = .Vlong a := by
  cases h; rfl

theorem ltu_iw_of_toNat {y : Integers.Int} (h : y.toNat < 32) :
    Integers.Int.ltu y Integers.Int.iwordsize = true := by
  rw [Integers.Int.ltu_toNat]; exact decide_eq_true (by
    show y.toNat < (32 : BitVec 32).toNat; simp; omega)

theorem ltu_iw64_of_toNat {y : Integers.Int} (h : y.toNat < 64) :
    Integers.Int.ltu y Integers.Int64.iwordsize' = true := by
  rw [Integers.Int.ltu_toNat]
  have : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  rw [this]; exact decide_eq_true h

theorem ltu_repr_iw {p : _root_.Int} (h0 : 0 ≤ p) (h1 : p < 32) :
    Integers.Int.ltu (Integers.Int.repr p) Integers.Int.iwordsize = true := by
  have hp : p = ((p.toNat : Nat) : _root_.Int) := by omega
  rw [hp]; apply ltu_iw_of_toNat; rw [Integers.Int.repr_toNat_small (by omega)]; omega

theorem ltu_repr_iw64 {p : _root_.Int} (h0 : 0 ≤ p) (h1 : p < 64) :
    Integers.Int.ltu (Integers.Int.repr p) Integers.Int64.iwordsize' = true := by
  have hp : p = ((p.toNat : Nat) : _root_.Int) := by omega
  rw [hp]; apply ltu_iw64_of_toNat; rw [Integers.Int.repr_toNat_lt64 (by omega)]; omega

/-! ### Inversion of the value-level division operators -/

theorem divu_inv {x z : Val} {n2 : Integers.Int} (h : Val.divu x (.Vint n2) = some z) :
    ∃ i, x = .Vint i ∧ z = .Vint (Integers.Int.divu i n2) := by
  cases x <;> simp only [Val.divu, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

theorem modu_inv {x z : Val} {n2 : Integers.Int} (h : Val.modu x (.Vint n2) = some z) :
    ∃ i, x = .Vint i ∧ z = .Vint (Integers.Int.modu i n2) := by
  cases x <;> simp only [Val.modu, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

theorem divs_inv {x z : Val} {n2 : Integers.Int} (h : Val.divs x (.Vint n2) = some z) :
    ∃ i, x = .Vint i ∧ z = .Vint (Integers.Int.divs i n2) := by
  cases x <;> simp only [Val.divs, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

theorem mods_inv {x z : Val} {n2 : Integers.Int} (h : Val.mods x (.Vint n2) = some z) :
    ∃ i, x = .Vint i ∧ z = .Vint (Integers.Int.mods i n2) := by
  cases x <;> simp only [Val.mods, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

theorem divlu_inv {x z : Val} {n2 : Integers.Int64} (h : Val.divlu x (.Vlong n2) = some z) :
    ∃ i, x = .Vlong i ∧ z = .Vlong (Integers.Int64.divu i n2) := by
  cases x <;> simp only [Val.divlu, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

theorem modlu_inv {x z : Val} {n2 : Integers.Int64} (h : Val.modlu x (.Vlong n2) = some z) :
    ∃ i, x = .Vlong i ∧ z = .Vlong (Integers.Int64.modu i n2) := by
  cases x <;> simp only [Val.modlu, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

theorem divls_inv {x z : Val} {n2 : Integers.Int64} (h : Val.divls x (.Vlong n2) = some z) :
    ∃ i, x = .Vlong i ∧ z = .Vlong (Integers.Int64.divs i n2) := by
  cases x <;> simp only [Val.divls, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

theorem modls_inv {x z : Val} {n2 : Integers.Int64} (h : Val.modls x (.Vlong n2) = some z) :
    ∃ i, x = .Vlong i ∧ z = .Vlong (Integers.Int64.mods i n2) := by
  cases x <;> simp only [Val.modls, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl, rfl⟩

section CMCONSTRS
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-- `is_intconst_sound` -/
theorem isIntconst_sound {le : Letenv} {a : SelectOp.Expr} {n : Integers.Int} {v : Val}
    (h : isIntconst a = some n) (ha : CminorSel.EvalExpr ge sp e m le a v) : v = .Vint n := by
  unfold isIntconst at h
  split at h
  · cases h
    cases ha with
    | Eop _ _ _ vl _ hl ho =>
      cases vl with
      | nil => exact (Option.some.inj ho).symm
      | cons _ _ => cases ho
  · cases h

/-- `is_longconst_sound` -/
theorem isLongconst_sound {le : Letenv} {a : SelectOp.Expr} {n : Integers.Int64} {v : Val}
    (h : isLongconst a = some n) (ha : CminorSel.EvalExpr ge sp e m le a v) : v = .Vlong n :=
  is_longconst_sound h ha

/-! ### 32-bit unsigned division and modulus -/

/-- `eval_divu_mul` -/
theorem eval_divu_mul {le : Letenv} {x y : Integers.Int} {p M : _root_.Int}
    (hp : divuMulParams (Integers.Int.unsigned y) = some (p, M)) (hle : le[0]? = some (.Vint x)) :
    CminorSel.EvalExpr ge sp e m le (divuMul p M) (.Vint (Integers.Int.divu x y)) := by
  obtain ⟨hp0, hp1, heq⟩ := divu_mul_shift (x := x) hp
  have C : CminorSel.EvalExpr ge sp e m le (.Eletvar 0) (.Vint x) := .Eletvar _ _ _ hle
  have D : CminorSel.EvalExpr ge sp e m le (.Eop (.Ointconst (Integers.Int.repr M)) .Enil)
      (.Vint (Integers.Int.repr M)) := eval_op0 rfl
  obtain ⟨v, hv, hl⟩ := eval_mulhu le _ _ _ _ C D
  obtain rfl := lessdef_vint (a := Integers.Int.mulhu x (Integers.Int.repr M)) hl
  obtain ⟨v', hv', hl'⟩ := eval_shruimm (Integers.Int.repr p) le _ _ hv
  have hlt := ltu_repr_iw hp0 hp1
  have hs : Val.shru (.Vint (Integers.Int.mulhu x (Integers.Int.repr M))) (.Vint (Integers.Int.repr p)) =
      .Vint (Integers.Int.shru (Integers.Int.mulhu x (Integers.Int.repr M)) (Integers.Int.repr p)) := by
    simp [Val.shru, hlt]
  dsimp only at hl'
  rw [hs] at hl'
  obtain rfl := lessdef_vint hl'
  rw [heq]; exact hv'

/-- `eval_divuimm` -/
theorem eval_divuimm (ofs : Bool) {le : Letenv} {e1 : SelectOp.Expr} {x z : Val} {n2 : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le e1 x) (hz : Val.divu x (.Vint n2) = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divuimm ofs e1 n2) v ∧ Val.Lessdef z v := by
  unfold divuimm
  split
  · next l hl =>
    rw [← Val.divu_pow2 hl hz]; exact eval_shruimm l le _ _ hx
  · split
    · exact eval_divuBase hx (eval_op0 rfl) hz
    · split
      · exact eval_divuBase hx (eval_op0 rfl) hz
      · next p M hp =>
        obtain ⟨i, rfl, rfl⟩ := divu_inv hz
        exact ⟨_, .Elet _ _ _ _ _ hx (eval_divu_mul hp rfl), .refl _⟩

/-- `eval_divu` -/
theorem eval_divu (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divu ofs a b) v ∧ Val.Lessdef z v := by
  unfold divu
  split
  · next n2 n1 hb ha =>
    obtain rfl := isIntconst_sound hb hy
    obtain rfl := isIntconst_sound ha hx
    split
    · exact eval_divuBase hx hy hz
    · obtain ⟨i, hi, rfl⟩ := divu_inv hz
      cases hi
      exact ⟨_, eval_op0 rfl, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isIntconst_sound hb hy
    exact eval_divuimm ofs hx hz
  · exact eval_divuBase hx hy hz

/-- `eval_mod_from_div` -/
theorem eval_mod_from_div {le : Letenv} {a : SelectOp.Expr} {n x y : Integers.Int}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vint y)) (hle : le[0]? = some (.Vint x)) :
    CminorSel.EvalExpr ge sp e m le (modFromDiv a n)
      (.Vint (Integers.Int.sub x (Integers.Int.mul y n))) := by
  unfold modFromDiv
  obtain ⟨v, hv, hl⟩ := eval_mulimm n le _ _ ha
  obtain rfl := lessdef_vint (a := Integers.Int.mul y n) hl
  exact eval_op2 (.Eletvar _ _ _ hle) hv rfl

/-- `eval_moduimm` -/
theorem eval_moduimm (ofs : Bool) {le : Letenv} {e1 : SelectOp.Expr} {x z : Val} {n2 : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le e1 x) (hz : Val.modu x (.Vint n2) = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (moduimm ofs e1 n2) v ∧ Val.Lessdef z v := by
  unfold moduimm
  split
  · next l hl =>
    rw [← Val.modu_pow2 hl hz]; exact eval_andimm _ le _ _ hx
  · split
    · exact eval_moduBase hx (eval_op0 rfl) hz
    · split
      · exact eval_moduBase hx (eval_op0 rfl) hz
      · next p M hp =>
        obtain ⟨i, rfl, rfl⟩ := modu_inv hz
        refine ⟨_, .Elet _ _ _ _ _ hx (eval_mod_from_div (eval_divu_mul hp rfl) rfl), ?_⟩
        rw [Integers.Int.modu_divu]; ld

/-- `eval_modu` -/
theorem eval_modu (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modu ofs a b) v ∧ Val.Lessdef z v := by
  unfold modu
  split
  · next n2 n1 hb ha =>
    obtain rfl := isIntconst_sound hb hy
    obtain rfl := isIntconst_sound ha hx
    split
    · exact eval_moduBase hx hy hz
    · obtain ⟨i, hi, rfl⟩ := modu_inv hz
      cases hi
      exact ⟨_, eval_op0 rfl, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isIntconst_sound hb hy
    exact eval_moduimm ofs hx hz
  · exact eval_moduBase hx hy hz

/-! ### 32-bit signed division and modulus -/

theorem int_half_modulus_eq : @Eq _root_.Int Integers.Int.half_modulus (2 ^ 31) := by decide

/-- `eval_divs_mul` -/
theorem eval_divs_mul {le : Letenv} {x y : Integers.Int} {p M : _root_.Int}
    (hp : divsMulParams (Integers.Int.signed y) = some (p, M)) (hle : le[0]? = some (.Vint x)) :
    CminorSel.EvalExpr ge sp e m le (divsMul p M) (.Vint (Integers.Int.divs x y)) := by
  unfold divsMul
  have C : CminorSel.EvalExpr ge sp e m le (.Eletvar 0) (.Vint x) := .Eletvar _ _ _ hle
  have D : CminorSel.EvalExpr ge sp e m le (.Eop (.Ointconst (Integers.Int.repr M)) .Enil)
      (.Vint (Integers.Int.repr M)) := eval_op0 rfl
  obtain ⟨v, X, F⟩ := eval_mulhs le _ _ _ _ C D
  obtain rfl := lessdef_vint (a := Integers.Int.mulhs x (Integers.Int.repr M)) F
  obtain ⟨v1, Y, LD⟩ := eval_shruimm (Integers.Int.repr (Integers.Int.zwordsize - 1)) le _ _ C
  have h31 : Integers.Int.repr (Integers.Int.zwordsize - 1) = Integers.Int.repr 31 := rfl
  have hs31 : Val.shru (.Vint x) (.Vint (Integers.Int.repr (Integers.Int.zwordsize - 1))) =
      .Vint (Integers.Int.shru x (Integers.Int.repr 31)) := by
    rw [h31]; simp [Val.shru, show Integers.Int.ltu (Integers.Int.repr 31) Integers.Int.iwordsize = true
      by decide]
  dsimp only at LD
  rw [hs31] at LD
  obtain rfl := lessdef_vint LD
  split
  · next hm =>
    rw [int_half_modulus_eq] at hm
    obtain ⟨hp0, hp1, B⟩ := divs_mul_shift_1 (x := x) hp hm
    obtain ⟨v2, Z, LD2⟩ := eval_shrimm (Integers.Int.repr p) le _ _ X
    have hs : Val.shr (.Vint (Integers.Int.mulhs x (Integers.Int.repr M))) (.Vint (Integers.Int.repr p)) =
        .Vint (Integers.Int.shr (Integers.Int.mulhs x (Integers.Int.repr M)) (Integers.Int.repr p)) := by
      simp [Val.shr, ltu_repr_iw hp0 hp1]
    dsimp only at LD2
    rw [hs] at LD2
    obtain rfl := lessdef_vint LD2
    obtain ⟨v3, W, LD3⟩ := eval_add le _ _ _ _ Z Y
    obtain rfl := lessdef_vint LD3
    rw [B]; exact W
  · next hm =>
    rw [int_half_modulus_eq] at hm
    obtain ⟨hp0, hp1, B⟩ := divs_mul_shift_2 (x := x) hp (Int.not_lt.mp hm)
    obtain ⟨v2, Z, LD2⟩ := eval_add le _ _ _ _ X C
    obtain rfl := lessdef_vint LD2
    obtain ⟨v3, U, LD3⟩ := eval_shrimm (Integers.Int.repr p) le _ _ Z
    have hs : ∀ a : Integers.Int, Val.shr (.Vint a) (.Vint (Integers.Int.repr p)) =
        .Vint (Integers.Int.shr a (Integers.Int.repr p)) := by
      intro a; simp [Val.shr, ltu_repr_iw hp0 hp1]
    dsimp only at LD3
    rw [hs] at LD3
    obtain rfl := lessdef_vint LD3
    obtain ⟨v4, W, LD4⟩ := eval_add le _ _ _ _ U Y
    obtain rfl := lessdef_vint LD4
    rw [B]; exact W

/-- `eval_divsimm` -/
theorem eval_divsimm (ofs : Bool) {le : Letenv} {e1 : SelectOp.Expr} {x z : Val} {n2 : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le e1 x) (hz : Val.divs x (.Vint n2) = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divsimm ofs e1 n2) v ∧ Val.Lessdef z v := by
  unfold divsimm
  split
  · next l hl =>
    split
    · next hlt => exact eval_shrximm hx (Val.divs_pow2 hl hlt hz)
    · exact eval_divsBase hx (eval_op0 rfl) hz
  · split
    · exact eval_divsBase hx (eval_op0 rfl) hz
    · split
      · exact eval_divsBase hx (eval_op0 rfl) hz
      · next p M hp =>
        obtain ⟨i, rfl, rfl⟩ := divs_inv hz
        exact ⟨_, .Elet _ _ _ _ _ hx (eval_divs_mul hp rfl), .refl _⟩

/-- `eval_divs` -/
theorem eval_divs (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divs x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divs ofs a b) v ∧ Val.Lessdef z v := by
  unfold divs
  split
  · next n2 n1 hb ha =>
    obtain rfl := isIntconst_sound hb hy
    obtain rfl := isIntconst_sound ha hx
    split
    · exact eval_divsBase hx hy hz
    · obtain ⟨i, hi, rfl⟩ := divs_inv hz
      cases hi
      exact ⟨_, eval_op0 rfl, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isIntconst_sound hb hy
    exact eval_divsimm ofs hx hz
  · exact eval_divsBase hx hy hz

theorem divs_of_mods {i n2 : Integers.Int} {z : Val} (hz : Val.mods (.Vint i) (.Vint n2) = some z) :
    Val.divs (.Vint i) (.Vint n2) = some (.Vint (Integers.Int.divs i n2)) := by
  simp only [Val.mods] at hz
  simp only [Val.divs]
  split at hz
  · cases hz
  · next hc => rw [if_neg hc]

/-- `eval_modsimm` -/
theorem eval_modsimm (ofs : Bool) {le : Letenv} {e1 : SelectOp.Expr} {x z : Val} {n2 : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le e1 x) (hz : Val.mods x (.Vint n2) = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modsimm ofs e1 n2) v ∧ Val.Lessdef z v := by
  unfold modsimm
  split
  · next l hl =>
    split
    · next hlt =>
      obtain ⟨i, rfl, rfl⟩ := mods_inv hz
      have hd := divs_of_mods hz
      have A : CminorSel.EvalExpr ge sp e m (.Vint i :: le) (.Eletvar 0) (.Vint i) := .Eletvar _ _ _ rfl
      obtain ⟨v1, X, LD⟩ := eval_shrximm A (Val.divs_pow2 hl hlt hd)
      obtain rfl := lessdef_vint LD
      refine ⟨_, .Elet _ _ _ _ _ hx (eval_mod_from_div X rfl), ?_⟩
      rw [Integers.Int.mods_divs]; ld
    · exact eval_modsBase hx (eval_op0 rfl) hz
  · split
    · exact eval_modsBase hx (eval_op0 rfl) hz
    · split
      · exact eval_modsBase hx (eval_op0 rfl) hz
      · next p M hp =>
        obtain ⟨i, rfl, rfl⟩ := mods_inv hz
        refine ⟨_, .Elet _ _ _ _ _ hx (eval_mod_from_div (eval_divs_mul hp rfl) rfl), ?_⟩
        rw [Integers.Int.mods_divs]; ld

/-- `eval_mods` -/
theorem eval_mods (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.mods x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (mods ofs a b) v ∧ Val.Lessdef z v := by
  unfold mods
  split
  · next n2 n1 hb ha =>
    obtain rfl := isIntconst_sound hb hy
    obtain rfl := isIntconst_sound ha hx
    split
    · exact eval_modsBase hx hy hz
    · obtain ⟨i, hi, rfl⟩ := mods_inv hz
      cases hi
      exact ⟨_, eval_op0 rfl, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isIntconst_sound hb hy
    exact eval_modsimm ofs hx hz
  · exact eval_modsBase hx hy hz

/-! ### 64-bit division and modulus -/

/-- `eval_modl_from_divl` -/
theorem eval_modl_from_divl {le : Letenv} {a : SelectOp.Expr} {n x y : Integers.Int64}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong y)) (hle : le[0]? = some (.Vlong x)) :
    CminorSel.EvalExpr ge sp e m le (modlFromDivl a n)
      (.Vlong (Integers.Int64.sub x (Integers.Int64.mul y n))) := by
  unfold modlFromDivl
  obtain ⟨v1, A1, B1⟩ := eval_mullimm n le _ _ ha
  obtain rfl := lessdef_vlong (a := Integers.Int64.mul y n) B1
  obtain ⟨v2, A2, B2⟩ := eval_subl le _ _ _ _ (.Eletvar _ _ _ hle) A1
  obtain rfl := lessdef_vlong B2
  exact A2

/-- `eval_divlu_mull` -/
theorem eval_divlu_mull {le : Letenv} {x y : Integers.Int64} {p M : _root_.Int}
    (hp : divluMulParams (Integers.Int64.unsigned y) = some (p, M))
    (hle : le[0]? = some (.Vlong x)) :
    CminorSel.EvalExpr ge sp e m le (divluMull p M) (.Vlong (Integers.Int64.divu x y)) := by
  obtain ⟨hp0, hp1, B⟩ := divlu_mul_shift (x := x) hp
  have A0 : CminorSel.EvalExpr ge sp e m le (.Eletvar 0) (.Vlong x) := .Eletvar _ _ _ hle
  obtain ⟨v1, A1, B1⟩ := eval_mullhu (Integers.Int64.repr M) le _ _ A0
  obtain rfl := lessdef_vlong (a := Integers.Int64.mulhu x (Integers.Int64.repr M)) B1
  obtain ⟨v2, A2, B2⟩ := eval_shrluimm (Integers.Int.repr p) le _ _ A1
  dsimp only at B2
  rw [val_shrlu_long _ (ltu_repr_iw64 hp0 hp1)] at B2
  obtain rfl := lessdef_vlong B2
  unfold divluMull
  rw [B]; exact A2

/-- `eval_divlu` -/
theorem eval_divlu (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divlu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divlu ofs a b) v ∧ Val.Lessdef z v := by
  unfold divlu
  split
  · next n2 n1 hb ha =>
    obtain rfl := isLongconst_sound hb hy
    obtain rfl := isLongconst_sound ha hx
    obtain ⟨i, hi, rfl⟩ := divlu_inv hz
    cases hi
    exact ⟨_, eval_longconst le _, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isLongconst_sound hb hy
    split
    · next l hl =>
      rw [← Val.divlu_pow2 hl hz]; exact eval_shrluimm l le _ _ hx
    · split
      · exact eval_divluBase hx hy hz
      · split
        · exact eval_divluBase hx hy hz
        · next p M hp =>
          obtain ⟨i, rfl, rfl⟩ := divlu_inv hz
          exact ⟨_, .Elet _ _ _ _ _ hx (eval_divlu_mull hp rfl), .refl _⟩
  · exact eval_divluBase hx hy hz

/-- `eval_modlu` -/
theorem eval_modlu (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modlu x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modlu ofs a b) v ∧ Val.Lessdef z v := by
  unfold modlu
  split
  · next n2 n1 hb ha =>
    obtain rfl := isLongconst_sound hb hy
    obtain rfl := isLongconst_sound ha hx
    obtain ⟨i, hi, rfl⟩ := modlu_inv hz
    cases hi
    exact ⟨_, eval_longconst le _, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isLongconst_sound hb hy
    split
    · next l hl =>
      rw [← Val.modlu_pow2 hl hz]; exact eval_andl le _ _ _ _ hx (eval_longconst le _)
    · split
      · exact eval_modluBase hx hy hz
      · split
        · exact eval_modluBase hx hy hz
        · next p M hp =>
          obtain ⟨i, rfl, rfl⟩ := modlu_inv hz
          refine ⟨_, .Elet _ _ _ _ _ hx (eval_modl_from_divl (eval_divlu_mull hp rfl) rfl), ?_⟩
          rw [Integers.Int64.modu_divu]; ld
  · exact eval_modluBase hx hy hz

theorem int64_half_modulus_eq : @Eq _root_.Int Integers.Int64.half_modulus (2 ^ 63) := by decide

/-- `eval_divls_mull` -/
theorem eval_divls_mull {le : Letenv} {x y : Integers.Int64} {p M : _root_.Int}
    (hp : divlsMulParams (Integers.Int64.signed y) = some (p, M))
    (hle : le[0]? = some (.Vlong x)) :
    CminorSel.EvalExpr ge sp e m le (divlsMull p M) (.Vlong (Integers.Int64.divs x y)) := by
  unfold divlsMull
  have A0 : CminorSel.EvalExpr ge sp e m le (.Eletvar 0) (.Vlong x) := .Eletvar _ _ _ hle
  obtain ⟨v1, A1, B1⟩ := eval_mullhs (Integers.Int64.repr M) le _ _ A0
  obtain rfl := lessdef_vlong (a := Integers.Int64.mulhs x (Integers.Int64.repr M)) B1
  obtain ⟨v3, A3, B3⟩ := eval_shrluimm (Integers.Int.repr (Integers.Int64.zwordsize - 1)) le _ _ A0
  dsimp only at B3
  rw [show Integers.Int.repr (Integers.Int64.zwordsize - 1) = Integers.Int.repr 63 from rfl,
    val_shrlu_long _ (ltu_repr_iw64 (p := 63) (by decide) (by decide))] at B3
  obtain rfl := lessdef_vlong B3
  have hsh : ∀ a : Integers.Int64, ∀ {q : _root_.Int}, 0 ≤ q → q < 64 →
      Val.shrl (.Vlong a) (.Vint (Integers.Int.repr q)) =
        .Vlong (Integers.Int64.shr' a (Integers.Int.repr q)) := by
    intro a q h0 h1; rw [val_shrl_long _ (ltu_repr_iw64 h0 h1)]; rfl
  split
  · next hm =>
    rw [int64_half_modulus_eq] at hm
    obtain ⟨hp0, hp1, B⟩ := divls_mul_shift_1 (x := x) hp hm
    obtain ⟨v5, A5, B5⟩ := eval_shrlimm (Integers.Int.repr p) le _ _ A1
    dsimp only at B5
    rw [hsh _ hp0 hp1] at B5
    obtain rfl := lessdef_vlong B5
    obtain ⟨v6, A6, B6⟩ := eval_addl le _ _ _ _ A5 A3
    obtain rfl := lessdef_vlong B6
    rw [B]; exact A6
  · next hm =>
    rw [int64_half_modulus_eq] at hm
    obtain ⟨hp0, hp1, B⟩ := divls_mul_shift_2 (x := x) hp (Int.not_lt.mp hm)
    obtain ⟨v2, A2, B2⟩ := eval_addl le _ _ _ _ A1 A0
    obtain rfl := lessdef_vlong B2
    obtain ⟨v5, A5, B5⟩ := eval_shrlimm (Integers.Int.repr p) le _ _ A2
    dsimp only at B5
    rw [hsh _ hp0 hp1] at B5
    obtain rfl := lessdef_vlong B5
    obtain ⟨v6, A6, B6⟩ := eval_addl le _ _ _ _ A5 A3
    obtain rfl := lessdef_vlong B6
    rw [B]; exact A6

/-- `eval_divls` -/
theorem eval_divls (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.divls x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (divls ofs a b) v ∧ Val.Lessdef z v := by
  unfold divls
  split
  · next n2 n1 hb ha =>
    obtain rfl := isLongconst_sound hb hy
    obtain rfl := isLongconst_sound ha hx
    obtain ⟨i, hi, rfl⟩ := divls_inv hz
    cases hi
    exact ⟨_, eval_longconst le _, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isLongconst_sound hb hy
    split
    · next l hl =>
      split
      · next hlt => exact eval_shrxlimm hx (Val.divls_pow2 hl hlt hz)
      · exact eval_divlsBase hx hy hz
    · split
      · exact eval_divlsBase hx hy hz
      · split
        · exact eval_divlsBase hx hy hz
        · next p M hp =>
          obtain ⟨i, rfl, rfl⟩ := divls_inv hz
          exact ⟨_, .Elet _ _ _ _ _ hx (eval_divls_mull hp rfl), .refl _⟩
  · exact eval_divlsBase hx hy hz

theorem divls_of_modls {i n2 : Integers.Int64} {z : Val}
    (hz : Val.modls (.Vlong i) (.Vlong n2) = some z) :
    Val.divls (.Vlong i) (.Vlong n2) = some (.Vlong (Integers.Int64.divs i n2)) := by
  simp only [Val.modls] at hz
  simp only [Val.divls]
  split at hz
  · cases hz
  · next hc => rw [if_neg hc]

/-- `eval_modls` -/
theorem eval_modls (ofs : Bool) {le : Letenv} {a b : SelectOp.Expr} {x y z : Val}
    (hx : CminorSel.EvalExpr ge sp e m le a x) (hy : CminorSel.EvalExpr ge sp e m le b y)
    (hz : Val.modls x y = some z) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (modls ofs a b) v ∧ Val.Lessdef z v := by
  unfold modls
  split
  · next n2 n1 hb ha =>
    obtain rfl := isLongconst_sound hb hy
    obtain rfl := isLongconst_sound ha hx
    obtain ⟨i, hi, rfl⟩ := modls_inv hz
    cases hi
    exact ⟨_, eval_longconst le _, .refl _⟩
  · next n2 hb _ =>
    obtain rfl := isLongconst_sound hb hy
    split
    · next l hl =>
      split
      · next hlt =>
        obtain ⟨i, rfl, rfl⟩ := modls_inv hz
        have hd := divls_of_modls hz
        have A : CminorSel.EvalExpr ge sp e m (.Vlong i :: le) (.Eletvar 0) (.Vlong i) :=
          .Eletvar _ _ _ rfl
        obtain ⟨v1, A1, B1⟩ := eval_shrxlimm A (Val.divls_pow2 hl hlt hd)
        obtain rfl := lessdef_vlong B1
        refine ⟨_, .Elet _ _ _ _ _ hx (eval_modl_from_divl A1 rfl), ?_⟩
        rw [Integers.Int64.mods_divs]; ld
      · exact eval_modlsBase hx hy hz
    · split
      · exact eval_modlsBase hx hy hz
      · split
        · exact eval_modlsBase hx hy hz
        · next p M hp =>
          obtain ⟨i, rfl, rfl⟩ := modls_inv hz
          refine ⟨_, .Elet _ _ _ _ _ hx (eval_modl_from_divl (eval_divls_mull hp rfl) rfl), ?_⟩
          rw [Integers.Int64.mods_divs]; ld
  · exact eval_modlsBase hx hy hz

end CMCONSTRS

end SelectDivproof
end RiscV
end CC
