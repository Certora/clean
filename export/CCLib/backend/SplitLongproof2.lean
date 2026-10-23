/-
  Correctness of instruction selection for 64-bit integer operations on
  32-bit targets, second part — port of `backend/SplitLongproof.v`, lines
  519-1164 (the first part is `CCLib.backend.SplitLongproof`).

  As in the first part, the proofs are carried out over the aarch64 operators
  and `SelectOp` correctness lemmas.

  Ported: the `Int64` word lemmas used by these proofs (`decompose_shl_1/2`,
  `decompose_shru_1/2`, `decompose_shr_1/2`, `decompose_ltu`, `decompose_leu`,
  `decompose_lt`, `decompose_le`, `decompose_mul`, which are in `Integers.v`
  in Rocq), `eval_shift_imm`, `eval_shllimm`, `eval_shll`, `eval_shrluimm`,
  `eval_shrlu`, `eval_shrlimm`, `eval_shrl`, `eval_addl`, `eval_subl`,
  `eval_mull_base`, `eval_mullimm`, `eval_mull`, `eval_shrxlimm`,
  `decompose_cmpl_eq_zero`, `eval_cmpl_eq_zero`, `eval_cmpl_ne_zero`,
  `eval_cmplu_gen`, `int64_eq_xor`, `eval_cmplu`, `eval_cmpl_gen`,
  `decompose_cmpl_lt_zero`, `eval_cmpl`, `eval_select_long`.

  Differences from Rocq:
  * `eval_addl`, `eval_subl`, `eval_shrxlimm` and `eval_cmplu` assume
    `Archi.ptr64 = false` in Rocq.  `eval_addl`, `eval_subl` and
    `eval_shrxlimm` hold here without it, because the port's
    `__builtin_addl` / `__builtin_subl` return `Val.addl` / `Val.subl`
    unchanged.  `eval_cmplu` keeps a hypothesis, stated as: both arguments
    are 64-bit integers (the only case where `Val.cmplu` is defined when
    `Archi.ptr64 = false`).
  * Most word lemmas are proved by bit-blasting (`bv_decide`) rather than
    bit-by-bit reasoning.
-/
import CCLib.backend.SplitLongproof
import CCLib.lib.IntegersPow2

namespace CC

namespace Integers.Int64

theorem decompose_shl_1 (xh xl y : Int) (hy : Int.unsigned y < 32) :
    shl' (ofwords xh xl) y =
      ofwords (Int.or (Int.shl xh y) (Int.shru xl (Int.sub Int.iwordsize y))) (Int.shl xl y) := by
  change (y.toNat : _root_.Int) < 32 at hy
  have hy' : y < 32#32 := by rw [BitVec.lt_def]; simp; omega
  simp only [shl', ofwords, Int.or, Int.shl, Int.shru, Int.sub, Int.iwordsize, MI.or, MI.shl,
    MI.shru, MI.sub, MI.iwordsize, ← BitVec.shiftLeft_eq', ← BitVec.ushiftRight_eq']
  bv_decide

theorem decompose_shl_2 (xh xl y : Int) (hy1 : 32 ≤ Int.unsigned y) (hy2 : Int.unsigned y < 64) :
    shl' (ofwords xh xl) y = ofwords (Int.shl xl (Int.sub y Int.iwordsize)) Int.zero := by
  change 32 ≤ (y.toNat : _root_.Int) at hy1
  change (y.toNat : _root_.Int) < 64 at hy2
  have h1 : 32#32 ≤ y := by rw [BitVec.le_def]; simp; omega
  have h2 : y < 64#32 := by rw [BitVec.lt_def]; simp; omega
  simp only [shl', ofwords, Int.zero, Int.shl, Int.sub, Int.iwordsize, MI.zero, MI.shl,
    MI.sub, MI.iwordsize, ← BitVec.shiftLeft_eq']
  bv_decide

theorem decompose_shru_1 (xh xl y : Int) (hy : Int.unsigned y < 32) :
    shru' (ofwords xh xl) y =
      ofwords (Int.shru xh y) (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y))) := by
  change (y.toNat : _root_.Int) < 32 at hy
  have hy' : y < 32#32 := by rw [BitVec.lt_def]; simp; omega
  simp only [shru', ofwords, Int.or, Int.shl, Int.shru, Int.sub, Int.iwordsize, MI.or, MI.shl,
    MI.shru, MI.sub, MI.iwordsize, ← BitVec.shiftLeft_eq', ← BitVec.ushiftRight_eq']
  bv_decide

theorem decompose_shru_2 (xh xl y : Int) (hy1 : 32 ≤ Int.unsigned y) (hy2 : Int.unsigned y < 64) :
    shru' (ofwords xh xl) y = ofwords Int.zero (Int.shru xh (Int.sub y Int.iwordsize)) := by
  change 32 ≤ (y.toNat : _root_.Int) at hy1
  change (y.toNat : _root_.Int) < 64 at hy2
  have h1 : 32#32 ≤ y := by rw [BitVec.le_def]; simp; omega
  have h2 : y < 64#32 := by rw [BitVec.lt_def]; simp; omega
  simp only [shru', ofwords, Int.zero, Int.shru, Int.sub, Int.iwordsize, MI.zero, MI.shru,
    MI.sub, MI.iwordsize, ← BitVec.ushiftRight_eq']
  bv_decide

theorem decompose_shr_1 (xh xl y : Int) (hy : Int.unsigned y < 32) :
    shr' (ofwords xh xl) y =
      ofwords (Int.shr xh y) (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y))) := by
  change (y.toNat : _root_.Int) < 32 at hy
  have hy' : y < 32#32 := by rw [BitVec.lt_def]; simp; omega
  simp only [shr', ofwords, Int.or, Int.shl, Int.shru, Int.shr, Int.sub, Int.iwordsize, MI.or, MI.shl,
    MI.shru, MI.shr, MI.sub, MI.iwordsize, ← BitVec.shiftLeft_eq', ← BitVec.ushiftRight_eq',
    ← BitVec.sshiftRight_eq']
  bv_decide

theorem decompose_shr_2 (xh xl y : Int) (hy1 : 32 ≤ Int.unsigned y) (hy2 : Int.unsigned y < 64) :
    shr' (ofwords xh xl) y =
      ofwords (Int.shr xh (Int.repr 31)) (Int.shr xh (Int.sub y Int.iwordsize)) := by
  change 32 ≤ (y.toNat : _root_.Int) at hy1
  change (y.toNat : _root_.Int) < 64 at hy2
  have h1 : 32#32 ≤ y := by rw [BitVec.le_def]; simp; omega
  have h2 : y < 64#32 := by rw [BitVec.lt_def]; simp; omega
  have h31 : Int.repr 31 = 31#32 := by decide
  simp only [shr', ofwords, h31, Int.shr, Int.sub, Int.iwordsize, MI.shr,
    MI.sub, MI.iwordsize, ← BitVec.sshiftRight_eq']
  bv_decide


theorem decompose_ltu (xh xl yh yl : Int) :
    ltu (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.ltu xh yh := by
  simp only [ltu, ofwords, Int.eq, Int.ltu, MI.eq, MI.ltu]
  split <;> rename_i h <;> revert h <;> bv_decide

theorem decompose_leu (xh xl yh yl : Int) :
    !(ltu (ofwords yh yl) (ofwords xh xl)) =
      if Int.eq xh yh then !(Int.ltu yl xl) else Int.ltu xh yh := by
  simp only [ltu, ofwords, Int.eq, Int.ltu, MI.eq, MI.ltu]
  split <;> rename_i h <;> revert h <;> bv_decide

theorem decompose_lt (xh xl yh yl : Int) :
    lt (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.lt xh yh := by
  simp only [lt, ofwords, Int.eq, Int.ltu, Int.lt, MI.eq, MI.ltu, MI.lt]
  split <;> rename_i h <;> revert h <;> bv_decide

theorem decompose_le (xh xl yh yl : Int) :
    !(lt (ofwords yh yl) (ofwords xh xl)) =
      if Int.eq xh yh then !(Int.ltu yl xl) else Int.lt xh yh := by
  simp only [lt, ofwords, Int.eq, Int.ltu, Int.lt, MI.eq, MI.ltu, MI.lt]
  split <;> rename_i h <;> revert h <;> bv_decide

theorem decompose_cmpl_eq_zero (h l : Int) :
    eq (ofwords h l) zero = Int.eq (Int.or h l) Int.zero := by
  simp only [eq, ofwords, zero, Int.eq, Int.or, Int.zero, MI.eq, MI.or, MI.zero]
  bv_decide

theorem decompose_cmpl_lt_zero (h l : Int) :
    lt (ofwords h l) zero = Int.lt h Int.zero := by
  simp only [lt, ofwords, zero, Int.lt, Int.zero, MI.lt, MI.zero]
  bv_decide

theorem int64_eq_xor (p q : Int64) : eq p q = eq (xor p q) zero := by
  simp only [eq, xor, zero, MI.eq, MI.xor, MI.zero]
  bv_decide


theorem ofwords_toNat (h l : Int) : (ofwords h l).toNat = h.toNat * 4294967296 + l.toNat := by
  have e : ofwords h l = h ++ l := by simp only [ofwords]; bv_decide
  rw [e, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt l.isLt, Nat.shiftLeft_eq]

theorem mul'_toNat (x y : Int) : (mul' x y).toNat = x.toNat * y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hp : x.toNat * y.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)) (by decide)
  simp only [mul', repr, MI.repr, Int.unsigned, MI.unsigned, BitVec.toNat_ofInt]
  rw [show ((x.toNat : _root_.Int) * (y.toNat : _root_.Int)) = ((x.toNat * y.toNat : Nat) : _root_.Int)
    by simp, Int.emod_eq_of_lt (by omega) (by simp; omega)]
  exact Int.toNat_natCast _

theorem hiword_toNat (z : Int64) : (hiword z).toNat = z.toNat / 4294967296 := by
  have := z.isLt
  simp only [hiword, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  have : z.toNat < 18446744073709551616 := this
  show z.toNat / 4294967296 < 4294967296
  omega

theorem loword_toNat (z : Int64) : (loword z).toNat = z.toNat % 4294967296 := by
  simp only [loword, BitVec.truncate, BitVec.toNat_setWidth]

/-- `Int64.decompose_mul` -/
theorem decompose_mul (xh xl yh yl : Int) :
    mul (ofwords xh xl) (ofwords yh yl) =
      ofwords (Int.add (Int.add (hiword (mul' xl yl)) (Int.mul xl yh)) (Int.mul xh yl))
        (loword (mul' xl yl)) := by
  apply BitVec.eq_of_toNat_eq
  have ha := xl.isLt
  have hb := yl.isLt
  have hp : xl.toNat * yl.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega)) (by decide)
  simp only [mul, Int.add, Int.mul, MI.mul, MI.add, BitVec.toNat_mul, BitVec.toNat_add,
    ofwords_toNat, hiword_toNat, loword_toNat, mul'_toNat]
  have e1 : xh.toNat*4294967296*(yh.toNat*4294967296) =
      xh.toNat*yh.toNat*(4294967296*4294967296) := Nat.mul_mul_mul_comm _ _ _ _
  have e2 : xh.toNat*4294967296*yl.toNat = xh.toNat*yl.toNat*4294967296 := Nat.mul_right_comm _ _ _
  have e3 : xl.toNat*(yh.toNat*4294967296) = xl.toNat*yh.toNat*4294967296 :=
    (Nat.mul_assoc _ _ _).symm
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, e1, e2, e3]
  generalize xh.toNat*yh.toNat = R at *
  generalize xl.toNat*yh.toNat = Q1 at *
  generalize xh.toNat*yl.toNat = Q2 at *
  generalize xl.toNat*yl.toNat = P at *
  simp only [show (2:Nat)^64 = 18446744073709551616 from rfl, show (2:Nat)^32 = 4294967296 from rfl] at *
  omega


/-- Unsigned 64-bit comparisons in terms of the words (from `decompose_ltu` /
`decompose_leu`). -/
theorem cmpu_split (c ch cl : Comparison)
    (hc : (c = .Clt ∧ ch = .Clt ∧ cl = .Clt) ∨ (c = .Cle ∧ ch = .Clt ∧ cl = .Cle) ∨
      (c = .Cgt ∧ ch = .Cgt ∧ cl = .Cgt) ∨ (c = .Cge ∧ ch = .Cgt ∧ cl = .Cge)) (x y : Int64) :
    cmpu c x y = if Int.eq (hiword x) (hiword y) then Int.cmpu cl (loword x) (loword y)
      else Int.cmpu ch (hiword x) (hiword y) := by
  rw [← ofwords_recompose x, ← ofwords_recompose y]
  simp only [hi_ofwords, lo_ofwords]
  generalize hiword x = a; generalize loword x = b; generalize hiword y = c'; generalize loword y = d
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  simp only [cmpu, Int.cmpu, MI.cmpu, Int.eq, MI.eq, MI.ltu, ofwords] <;>
  split <;> rename_i h <;> revert h <;> bv_decide

/-- Signed 64-bit comparisons in terms of the words (from `decompose_lt` /
`decompose_le`). -/
theorem cmp_split (c ch cl : Comparison)
    (hc : (c = .Clt ∧ ch = .Clt ∧ cl = .Clt) ∨ (c = .Cle ∧ ch = .Clt ∧ cl = .Cle) ∨
      (c = .Cgt ∧ ch = .Cgt ∧ cl = .Cgt) ∨ (c = .Cge ∧ ch = .Cgt ∧ cl = .Cge)) (x y : Int64) :
    cmp c x y = if Int.eq (hiword x) (hiword y) then Int.cmpu cl (loword x) (loword y)
      else Int.cmp ch (hiword x) (hiword y) := by
  rw [← ofwords_recompose x, ← ofwords_recompose y]
  simp only [hi_ofwords, lo_ofwords]
  generalize hiword x = a; generalize loword x = b; generalize hiword y = c'; generalize loword y = d
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  simp only [cmp, Int.cmpu, Int.cmp, MI.cmpu, MI.cmp, Int.eq, MI.eq, MI.ltu, MI.lt, ofwords] <;>
  split <;> rename_i h <;> revert h <;> bv_decide

end Integers.Int64

namespace SplitLongproof

open Op CminorSel SelectOp SplitLong SelectOpproof

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-! ## Auxiliary value lemmas -/

theorem lessdef_vint_inv {p : Integers.Int} {v : Val} (h : Val.Lessdef (.Vint p) v) : v = .Vint p := by
  cases h; rfl

theorem lessdef_vlong_inv {p : Integers.Int64} {v : Val} (h : Val.Lessdef (.Vlong p) v) :
    v = .Vlong p := by
  cases h; rfl

theorem val_shl_vint {p n : Integers.Int} (h : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    Val.shl (.Vint p) (.Vint n) = .Vint (Integers.Int.shl p n) := by
  simp [Val.shl, h]

theorem val_shru_vint {p n : Integers.Int} (h : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    Val.shru (.Vint p) (.Vint n) = .Vint (Integers.Int.shru p n) := by
  simp [Val.shru, h]

theorem val_shr_vint {p n : Integers.Int} (h : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    Val.shr (.Vint p) (.Vint n) = .Vint (Integers.Int.shr p n) := by
  simp [Val.shr, h]

theorem val_shll_vint {x : Integers.Int64} {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shll (.Vlong x) (.Vint n) = .Vlong (Integers.Int64.shl' x n) := by
  have h' : Integers.Int.ltu n (Integers.Int.repr 64) = true := h
  show (if Integers.Int.ltu n (Integers.Int.repr 64) then _ else _) = _
  rw [if_pos h', Integers.Int64.shl'_eq]

theorem val_shrlu_vint {x : Integers.Int64} {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shrlu (.Vlong x) (.Vint n) = .Vlong (Integers.Int64.shru' x n) := by
  have h' : Integers.Int.ltu n (Integers.Int.repr 64) = true := h
  show (if Integers.Int.ltu n (Integers.Int.repr 64) then _ else _) = _
  rw [if_pos h', Integers.Int64.shru'_eq]

theorem val_shrl_vint {x : Integers.Int64} {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shrl (.Vlong x) (.Vint n) = .Vlong (Integers.Int64.shr' x n) := by
  have h' : Integers.Int.ltu n (Integers.Int.repr 64) = true := h
  show (if Integers.Int.ltu n (Integers.Int.repr 64) then _ else _) = _
  rw [if_pos h', Integers.Int64.shr'_eq]

/-! ## Shifts -/

/-- `eval_shift_imm` -/
theorem eval_shift_imm (P : SplitLong.Expr → Prop) (n : Integers.Int)
    (a0 a1 a2 a3 : SplitLong.Expr)
    (A0 : n = Integers.Int.zero → P a0)
    (A1 : Integers.Int.unsigned n < 32 →
      Integers.Int.ltu n Integers.Int.iwordsize = true →
      Integers.Int.ltu (Integers.Int.sub Integers.Int.iwordsize n) Integers.Int.iwordsize = true →
      Integers.Int.ltu n Integers.Int64.iwordsize' = true → P a1)
    (A2 : 32 ≤ Integers.Int.unsigned n → Integers.Int.unsigned n < 64 →
      Integers.Int.ltu (Integers.Int.sub n Integers.Int.iwordsize) Integers.Int.iwordsize = true →
      Integers.Int.ltu n Integers.Int64.iwordsize' = true → P a2)
    (A3 : P a3) :
    P (if Integers.Int.eq n Integers.Int.zero then a0
       else if Integers.Int.ltu n Integers.Int.iwordsize then a1
       else if Integers.Int.ltu n Integers.Int64.iwordsize' then a2
       else a3) := by
  have hw : Integers.Int64.iwordsize' = 64#32 := by decide
  have hu : Integers.Int.unsigned n = (n.toNat : _root_.Int) := rfl
  simp only [hw, hu, Integers.Int.eq, Integers.Int.ltu, Integers.Int.sub, Integers.Int.iwordsize,
    Integers.Int.zero, Integers.MI.eq, Integers.MI.ltu, Integers.MI.sub, Integers.MI.iwordsize,
    Integers.MI.zero] at A0 A1 A2 ⊢
  split
  · rename_i h0; exact A0 (by simpa using h0)
  · rename_i h0
    split
    · rename_i h1
      have : n.toNat < 32 := by simpa [BitVec.ult] using h1
      exact A1 (by show ((n.toNat : Nat) : _root_.Int) < 32; omega) h1 (by revert h0 h1; bv_decide) (by revert h1; bv_decide)
    · rename_i h1
      split
      · rename_i h2
        have : ¬ n.toNat < 32 := by simpa [BitVec.ult] using h1
        have : n.toNat < 64 := by simpa [BitVec.ult] using h2
        exact A2 (by show (32 : _root_.Int) ≤ ((n.toNat : Nat) : _root_.Int); omega)
          (by show ((n.toNat : Nat) : _root_.Int) < 64; omega) (by revert h1 h2; bv_decide) h2
      · exact A3

/-! ## Addition, subtraction, multiplication -/

section CMCONSTR

variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-- `eval_builtin_2` -/
theorem eval_builtin_2 {le : Letenv} {name : String} {sg : Signature} {bf : Builtins.BuiltinFunction}
    {a1 a2 : SplitLong.Expr} {v1 v2 v : Val}
    (h1 : CminorSel.EvalExpr ge sp e m le a1 v1) (h2 : CminorSel.EvalExpr ge sp e m le a2 v2)
    (hl : Builtins.lookupBuiltinFunction name sg = some bf)
    (hs : (Builtins.builtinFunctionSem bf).sem [v1, v2] = some v) :
    CminorSel.EvalExpr ge sp e m le (.Ebuiltin (.EF_builtin name sg) (a1 ::: a2 ::: .Enil)) v := by
  refine .Ebuiltin _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 (.Enil _))) ?_
  show builtinOrExternalSem name sg _ _ _ _ _ _
  unfold builtinOrExternalSem
  rw [hl]
  exact .intro _ _ _ _ hs

theorem ptrofs_of_int64_zero : Integers.Ptrofs.of_int64 Integers.Int64.zero = Integers.Ptrofs.zero := by
  decide

/-- `eval_addl`.  (Rocq assumes `Archi.ptr64 = false`; not needed here, see the module
header.) -/
theorem eval_addl : BinarySound ge sp e m addl Val.addl := by
  intro le a x b y ha hb
  have DEFAULT : ∃ v, CminorSel.EvalExpr ge sp e m le
      (.Ebuiltin (.EF_builtin "__builtin_addl" sigLLL) (a ::: b ::: .Enil)) v ∧
      Val.Lessdef (Val.addl x y) v :=
    ⟨_, eval_builtin_2 ha hb (bf := .BI_standard .BI_addl) (by decide) rfl, .refl _⟩
  unfold addl
  cases hp : is_longconst a with
  | some p =>
    cases hq : is_longconst b with
    | some q =>
      obtain rfl := is_longconst_sound hp ha
      obtain rfl := is_longconst_sound hq hb
      exact ⟨_, eval_longconst _ _, .refl _⟩
    | none =>
      dsimp only
      split
      · rename_i hz
        obtain rfl := (Integers.Int64.eq_spec _ _).mp hz
        obtain rfl := is_longconst_sound hp ha
        refine ⟨y, hb, ?_⟩
        cases y <;> simp only [Val.addl, Archi.ptr64, ↓reduceIte] <;> try exact .undef _
        · rw [Integers.Int64.add_zero_l]; exact .refl _
        · rw [ptrofs_of_int64_zero, Integers.Ptrofs.add_zero]; exact .refl _
      · exact DEFAULT
  | none =>
    cases hq : is_longconst b with
    | some q =>
      dsimp only
      split
      · rename_i hz
        obtain rfl := (Integers.Int64.eq_spec _ _).mp hz
        obtain rfl := is_longconst_sound hq hb
        refine ⟨x, ha, ?_⟩
        cases x <;> simp only [Val.addl, Archi.ptr64, ↓reduceIte] <;> try exact .undef _
        · rw [Integers.Int64.add_zero]; exact .refl _
        · rw [ptrofs_of_int64_zero, Integers.Ptrofs.add_zero]; exact .refl _
      · exact DEFAULT
    | none => exact DEFAULT

/-- `eval_subl`.  (Rocq assumes `Archi.ptr64 = false`; not needed here, see the module
header.) -/
theorem eval_subl : BinarySound ge sp e m subl Val.subl := by
  intro le a x b y ha hb
  have DEFAULT : ∃ v, CminorSel.EvalExpr ge sp e m le
      (.Ebuiltin (.EF_builtin "__builtin_subl" sigLLL) (a ::: b ::: .Enil)) v ∧
      Val.Lessdef (Val.subl x y) v :=
    ⟨_, eval_builtin_2 ha hb (bf := .BI_standard .BI_subl) (by decide) rfl, .refl _⟩
  unfold subl
  cases hp : is_longconst a with
  | some p =>
    cases hq : is_longconst b with
    | some q =>
      obtain rfl := is_longconst_sound hp ha
      obtain rfl := is_longconst_sound hq hb
      exact ⟨_, eval_longconst _ _, .refl _⟩
    | none =>
      dsimp only
      split
      · rename_i hz
        obtain rfl := (Integers.Int64.eq_spec _ _).mp hz
        obtain rfl := is_longconst_sound hp ha
        obtain ⟨v, A, B⟩ := eval_negl le b y hb
        refine ⟨v, A, ?_⟩
        cases y <;> simp only [Val.subl] <;> try exact .undef _
        rw [Integers.Int64.sub_zero_l]; exact B
      · exact DEFAULT
  | none =>
    cases hq : is_longconst b with
    | some q =>
      dsimp only
      split
      · rename_i hz
        obtain rfl := (Integers.Int64.eq_spec _ _).mp hz
        obtain rfl := is_longconst_sound hq hb
        refine ⟨x, ha, ?_⟩
        cases x <;> simp only [Val.subl, Archi.ptr64, ↓reduceIte] <;> try exact .undef _
        · have h0 : ∀ z : BitVec 64, z - 0 = z := fun z => by simp
          simp only [Integers.Int64.sub, Integers.MI.sub, Integers.Int64.zero, Integers.MI.zero, h0]
          exact .refl _
        · have h0 : ∀ z : Integers.Ptrofs, z - 0 = z := fun z => BitVec.sub_zero z
          simp only [ptrofs_of_int64_zero, Integers.Ptrofs.sub, Integers.MI.sub,
            Integers.Ptrofs.zero, Integers.MI.zero, h0]
          exact .refl _
      · exact DEFAULT
    | none => exact DEFAULT

/-- `eval_mull_base` -/
theorem eval_mull_base : BinarySound ge sp e m mull_base Val.mull := by
  intro le a x b y ha hb
  unfold mull_base
  refine eval_splitlong2 (sem := Val.mull) ?_ (by cases x <;> cases y <;> first | trivial | rfl) ha hb
  intro le a1 a2 b1 b2 x1 x2 y1 y2 h1 h2 h3 h4
  have E0 : CminorSel.EvalExpr ge sp e m (Val.mull' x2 y2 :: le) (.Eletvar 0) (Val.mull' x2 y2) :=
    .Eletvar _ _ _ rfl
  have E1 : CminorSel.EvalExpr ge sp e m (Val.mull' x2 y2 :: le) (.Eop .Olowlong (.Eletvar 0 ::: .Enil))
      (Val.loword (Val.mull' x2 y2)) := eval_op1 E0 rfl
  have E2 : CminorSel.EvalExpr ge sp e m (Val.mull' x2 y2 :: le) (.Eop .Ohighlong (.Eletvar 0 ::: .Enil))
      (Val.hiword (Val.mull' x2 y2)) := eval_op1 E0 rfl
  obtain ⟨v3, E3, L3⟩ := eval_mul _ _ _ _ _ (eval_lift (w := Val.mull' x2 y2) h2)
    (eval_lift (w := Val.mull' x2 y2) h3)
  obtain ⟨v4, E4, L4⟩ := eval_mul _ _ _ _ _ (eval_lift (w := Val.mull' x2 y2) h1)
    (eval_lift (w := Val.mull' x2 y2) h4)
  obtain ⟨v5, E5, L5⟩ := eval_add _ _ _ _ _ E2 E3
  obtain ⟨v6, E6, L6⟩ := eval_add _ _ _ _ _ E5 E4
  refine ⟨Val.longofwords v6 (Val.loword (Val.mull' x2 y2)),
    .Elet _ _ _ _ _ (eval_builtin_2 h2 h4 (bf := .BI_standard .BI_mull) (by decide) rfl)
      (eval_op2 E6 E1 rfl), ?_⟩
  rintro p1 p2 q1 q2 rfl rfl rfl rfl
  obtain rfl := lessdef_vint_inv L3
  obtain rfl := lessdef_vint_inv L4
  obtain rfl := lessdef_vint_inv L5
  obtain rfl := lessdef_vint_inv L6
  show Val.Vlong _ = Val.Vlong _
  rw [Integers.Int64.decompose_mul]

end CMCONSTR

section HELPERS

variable {prog : CminorSel.Program} {hf : HelperFunctions}
  (HELPERS : helper_functions_declared prog hf) {sp : Val} {e : Cminor.Env} {m : Mem}

include HELPERS

/-- `eval_shllimm` -/
theorem eval_shllimm (n : Integers.Int) :
    UnarySound prog.globalenv sp e m (fun a => shllimm hf a n) (fun v => Val.shll v (.Vint n)) := by
  intro le a x ha
  unfold shllimm
  refine eval_shift_imm (fun a' => ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le a' v ∧
    Val.Lessdef (Val.shll x (.Vint n)) v) n _ _ _ _ ?_ ?_ ?_ ?_
  · -- n = 0
    rintro rfl
    refine ⟨x, ha, ?_⟩
    cases x <;> try exact .undef _
    rw [val_shll_vint (by decide)]
    simp [Integers.Int64.shl', Integers.Int.zero, Integers.MI.zero]
    exact .refl _
  · -- 0 < n < 32
    intro hn h1 h2 h3
    refine eval_splitlong (sem := fun v => Val.shll v (.Vint n)) ?_
      (by cases x <;> first | trivial | rfl) ha
    intro le a b x y hx hy
    obtain ⟨v1, A1, B1⟩ := eval_shlimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m) n le a x hx
    obtain ⟨v2, A2, B2⟩ := eval_shlimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m) n le b y hy
    obtain ⟨v3, A3, B3⟩ := eval_shruimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m)
      (Integers.Int.sub Integers.Int.iwordsize n) le b y hy
    obtain ⟨v4, A4, B4⟩ := eval_or le _ _ _ _ A1 A3
    refine ⟨Val.longofwords v4 v2, eval_op2 A4 A2 rfl, ?_⟩
    rintro p q rfl rfl
    dsimp only at B1 B2 B3
    rw [val_shl_vint h1] at B1 B2
    rw [val_shru_vint h2] at B3
    obtain rfl := lessdef_vint_inv B1
    obtain rfl := lessdef_vint_inv B2
    obtain rfl := lessdef_vint_inv B3
    obtain rfl := lessdef_vint_inv B4
    rw [val_shll_vint h3, Integers.Int64.decompose_shl_1 _ _ _ hn]
    rfl
  · -- 32 ≤ n < 64
    intro hn1 hn2 h1 h3
    obtain ⟨v1, A1, B1⟩ := eval_lowlong le a x ha
    obtain ⟨v2, A2, B2⟩ := eval_shlimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m)
      (Integers.Int.sub n Integers.Int.iwordsize) le _ v1 A1
    refine ⟨_, eval_op2 A2 (eval_op0 rfl) rfl, ?_⟩
    cases x with
    | Vlong i =>
      obtain rfl := lessdef_vint_inv B1
      dsimp only at B2
      rw [val_shl_vint h1] at B2
      obtain rfl := lessdef_vint_inv B2
      have key := Integers.Int64.decompose_shl_2 (Integers.Int64.hiword i) (Integers.Int64.loword i)
        n hn1 hn2
      rw [Integers.Int64.ofwords_recompose] at key
      rw [val_shll_vint h3, key]
      exact .refl _
    | _ => exact .undef _
  · -- n ≥ 64
    exact ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_shl) ha (eval_op0 rfl)
      HELPERS.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfl, .refl _⟩

/-- `eval_shll` -/
theorem eval_shll : BinarySound prog.globalenv sp e m (shll hf) Val.shll := by
  intro le a x b y ha hb
  unfold shll
  split
  · rename_i n hn
    obtain rfl := is_intconst_sound hn hb
    exact eval_shllimm HELPERS n le a x ha
  · exact ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_shl) ha hb
      HELPERS.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfl, .refl _⟩

/-- `eval_shrluimm` -/
theorem eval_shrluimm (n : Integers.Int) :
    UnarySound prog.globalenv sp e m (fun a => shrluimm hf a n) (fun v => Val.shrlu v (.Vint n)) := by
  intro le a x ha
  unfold shrluimm
  refine eval_shift_imm (fun a' => ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le a' v ∧
    Val.Lessdef (Val.shrlu x (.Vint n)) v) n _ _ _ _ ?_ ?_ ?_ ?_
  · -- n = 0
    rintro rfl
    refine ⟨x, ha, ?_⟩
    cases x <;> try exact .undef _
    rw [val_shrlu_vint (by decide)]
    simp [Integers.Int64.shru', Integers.Int.zero, Integers.MI.zero]
    exact .refl _
  · -- 0 < n < 32
    intro hn h1 h2 h3
    refine eval_splitlong (sem := fun v => Val.shrlu v (.Vint n)) ?_
      (by cases x <;> first | trivial | rfl) ha
    intro le a b x y hx hy
    obtain ⟨v1, A1, B1⟩ := eval_shruimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m) n le b y hy
    obtain ⟨v2, A2, B2⟩ := eval_shruimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m) n le a x hx
    obtain ⟨v3, A3, B3⟩ := eval_shlimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m)
      (Integers.Int.sub Integers.Int.iwordsize n) le a x hx
    obtain ⟨v4, A4, B4⟩ := eval_or le _ _ _ _ A1 A3
    refine ⟨Val.longofwords v2 v4, eval_op2 A2 A4 rfl, ?_⟩
    rintro p q rfl rfl
    dsimp only at B1 B2 B3
    rw [val_shru_vint h1] at B1 B2
    rw [val_shl_vint h2] at B3
    obtain rfl := lessdef_vint_inv B1
    obtain rfl := lessdef_vint_inv B2
    obtain rfl := lessdef_vint_inv B3
    obtain rfl := lessdef_vint_inv B4
    rw [val_shrlu_vint h3, Integers.Int64.decompose_shru_1 _ _ _ hn]
    rfl
  · -- 32 ≤ n < 64
    intro hn1 hn2 h1 h3
    obtain ⟨v1, A1, B1⟩ := eval_highlong le a x ha
    obtain ⟨v2, A2, B2⟩ := eval_shruimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m)
      (Integers.Int.sub n Integers.Int.iwordsize) le _ v1 A1
    refine ⟨_, eval_op2 (eval_op0 rfl) A2 rfl, ?_⟩
    cases x with
    | Vlong i =>
      obtain rfl := lessdef_vint_inv B1
      dsimp only at B2
      rw [val_shru_vint h1] at B2
      obtain rfl := lessdef_vint_inv B2
      have key := Integers.Int64.decompose_shru_2 (Integers.Int64.hiword i) (Integers.Int64.loword i)
        n hn1 hn2
      rw [Integers.Int64.ofwords_recompose] at key
      rw [val_shrlu_vint h3, key]
      exact .refl _
    | _ => exact .undef _
  · -- n ≥ 64
    exact ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_shr) ha (eval_op0 rfl)
      HELPERS.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfl, .refl _⟩

/-- `eval_shrlu` -/
theorem eval_shrlu : BinarySound prog.globalenv sp e m (shrlu hf) Val.shrlu := by
  intro le a x b y ha hb
  unfold shrlu
  split
  · rename_i n hn
    obtain rfl := is_intconst_sound hn hb
    exact eval_shrluimm HELPERS n le a x ha
  · exact ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_shr) ha hb
      HELPERS.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfl, .refl _⟩

/-- `eval_shrlimm` -/
theorem eval_shrlimm (n : Integers.Int) :
    UnarySound prog.globalenv sp e m (fun a => shrlimm hf a n) (fun v => Val.shrl v (.Vint n)) := by
  intro le a x ha
  unfold shrlimm
  refine eval_shift_imm (fun a' => ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le a' v ∧
    Val.Lessdef (Val.shrl x (.Vint n)) v) n _ _ _ _ ?_ ?_ ?_ ?_
  · -- n = 0
    rintro rfl
    refine ⟨x, ha, ?_⟩
    cases x <;> try exact .undef _
    rw [val_shrl_vint (by decide)]
    simp [Integers.Int64.shr', Integers.Int.zero, Integers.MI.zero]
    exact .refl _
  · -- 0 < n < 32
    intro hn h1 h2 h3
    refine eval_splitlong (sem := fun v => Val.shrl v (.Vint n)) ?_
      (by cases x <;> first | trivial | rfl) ha
    intro le a b x y hx hy
    obtain ⟨v1, A1, B1⟩ := eval_shruimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m) n le b y hy
    obtain ⟨v2, A2, B2⟩ := eval_shrimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m) n le a x hx
    obtain ⟨v3, A3, B3⟩ := eval_shlimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m)
      (Integers.Int.sub Integers.Int.iwordsize n) le a x hx
    obtain ⟨v4, A4, B4⟩ := eval_or le _ _ _ _ A1 A3
    refine ⟨Val.longofwords v2 v4, eval_op2 A2 A4 rfl, ?_⟩
    rintro p q rfl rfl
    dsimp only at B1 B2 B3
    rw [val_shru_vint h1] at B1
    rw [val_shr_vint h1] at B2
    rw [val_shl_vint h2] at B3
    obtain rfl := lessdef_vint_inv B1
    obtain rfl := lessdef_vint_inv B2
    obtain rfl := lessdef_vint_inv B3
    obtain rfl := lessdef_vint_inv B4
    rw [val_shrl_vint h3, Integers.Int64.decompose_shr_1 _ _ _ hn]
    rfl
  · -- 32 ≤ n < 64
    intro hn1 hn2 h1 h3
    obtain ⟨v1, A1, B1⟩ := eval_highlong le a x ha
    have E0 : CminorSel.EvalExpr prog.globalenv sp e m (v1 :: le) (.Eletvar 0) v1 :=
      .Eletvar _ _ _ rfl
    obtain ⟨v2, A2, B2⟩ := eval_shrimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m)
      (Integers.Int.sub n Integers.Int.iwordsize) _ _ v1 E0
    obtain ⟨v3, A3, B3⟩ := eval_shrimm (ge := prog.globalenv) (sp := sp) (e := e) (m := m)
      (Integers.Int.repr 31) _ _ v1 E0
    refine ⟨_, .Elet _ _ _ _ _ A1 (eval_op2 A3 A2 rfl), ?_⟩
    cases x with
    | Vlong i =>
      obtain rfl := lessdef_vint_inv B1
      dsimp only at B2 B3
      rw [val_shr_vint h1] at B2
      rw [val_shr_vint (by decide)] at B3
      obtain rfl := lessdef_vint_inv B2
      obtain rfl := lessdef_vint_inv B3
      have key := Integers.Int64.decompose_shr_2 (Integers.Int64.hiword i) (Integers.Int64.loword i)
        n hn1 hn2
      rw [Integers.Int64.ofwords_recompose] at key
      rw [val_shrl_vint h3, key]
      exact .refl _
    | _ => exact .undef _
  · -- n ≥ 64
    exact ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_sar) ha (eval_op0 rfl)
      HELPERS.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfl, .refl _⟩

/-- `eval_shrl` -/
theorem eval_shrl : BinarySound prog.globalenv sp e m (shrl hf) Val.shrl := by
  intro le a x b y ha hb
  unfold shrl
  split
  · rename_i n hn
    obtain rfl := is_intconst_sound hn hb
    exact eval_shrlimm HELPERS n le a x ha
  · exact ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_sar) ha hb
      HELPERS.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfl, .refl _⟩

/-- `eval_mullimm` -/
theorem eval_mullimm (n : Integers.Int64) :
    UnarySound prog.globalenv sp e m (mullimm hf n) (fun v => Val.mull v (.Vlong n)) := by
  intro le a x ha
  unfold mullimm
  split
  · rename_i hz
    obtain rfl := (Integers.Int64.eq_spec _ _).mp hz
    refine ⟨_, eval_longconst _ _, ?_⟩
    cases x <;> try exact .undef _
    show Val.Lessdef (.Vlong (Integers.Int64.mul _ Integers.Int64.zero)) _
    rw [Integers.Int64.mul_zero]; exact .refl _
  · split
    · rename_i _ ho
      obtain rfl := (Integers.Int64.eq_spec _ _).mp ho
      refine ⟨x, ha, ?_⟩
      cases x <;> try exact .undef _
      show Val.Lessdef (.Vlong (Integers.Int64.mul _ Integers.Int64.one)) _
      rw [Integers.Int64.mul_one]; exact .refl _
    · split
      · rename_i l hl
        obtain ⟨v, A, B⟩ := eval_shllimm HELPERS l le a x ha
        refine ⟨v, A, ?_⟩
        cases x <;> try exact .undef _
        have hr : Integers.Int.ltu l Integers.Int64.iwordsize' = true := by
          have h64 := (Integers.Int64.is_power2'_spec hl).1
          have hw : Integers.Int64.iwordsize' = 64#32 := by decide
          rw [hw]
          simpa [Integers.Int.ltu, Integers.MI.ltu, BitVec.ult] using h64
        dsimp only at B
        rw [val_shll_vint hr] at B
        show Val.Lessdef (.Vlong (Integers.Int64.mul _ n)) _
        rw [Integers.Int64.mul_pow2' _ hl]; exact B
      · exact eval_mull_base le a x _ _ ha (eval_longconst le n)

/-- `eval_mull` -/
theorem eval_mull : BinarySound prog.globalenv sp e m (mull hf) Val.mull := by
  intro le a x b y ha hb
  unfold mull
  cases hp : is_longconst a with
  | some p =>
    obtain rfl := is_longconst_sound hp ha
    cases hq : is_longconst b with
    | some q =>
      obtain rfl := is_longconst_sound hq hb
      exact ⟨_, eval_longconst _ _, .refl _⟩
    | none =>
      obtain ⟨v, A, B⟩ := eval_mullimm HELPERS p le b y hb
      refine ⟨v, A, ?_⟩
      cases y <;> try exact .undef _
      show Val.Lessdef (.Vlong (Integers.Int64.mul _ _)) _
      rw [Integers.Int64.mul_commut]; exact B
  | none =>
    cases hq : is_longconst b with
    | some q =>
      obtain rfl := is_longconst_sound hq hb
      exact eval_mullimm HELPERS q le a x ha
    | none => exact eval_mull_base le a x b y ha hb

/-- `eval_shrxlimm`.  (Rocq assumes `Archi.ptr64 = false`; not needed here, see the module
header.) -/
theorem eval_shrxlimm {le : Letenv} {a : SplitLong.Expr} {n : Integers.Int} {x z : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (hz : Val.shrxl x (.Vint n) = some z) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (shrxlimm hf a n) v ∧ Val.Lessdef z v := by
  have hz' := Val.shrxl_shrl_2 hz
  unfold shrxlimm
  split
  · rename_i h0
    rw [if_pos h0] at hz'
    rw [hz']
    exact ⟨x, ha, .refl _⟩
  · rename_i h0
    rw [if_neg h0] at hz'
    rw [hz']
    have E0 : CminorSel.EvalExpr prog.globalenv sp e m (x :: le) (.Eletvar 0) x := .Eletvar _ _ _ rfl
    obtain ⟨v1, A1, B1⟩ := eval_shrlimm HELPERS (Integers.Int.repr 63) _ _ x E0
    obtain ⟨v2, A2, B2⟩ := eval_shrluimm HELPERS (Integers.Int.sub (Integers.Int.repr 64) n) _ _ v1 A1
    obtain ⟨v3, A3, B3⟩ := eval_addl _ _ _ _ _ E0 A2
    obtain ⟨v4, A4, B4⟩ := eval_shrlimm HELPERS n _ _ v3 A3
    refine ⟨v4, .Elet _ _ _ _ _ ha A4, ?_⟩
    have X : ∀ {v1 v2 : Val} (k : Integers.Int), Val.Lessdef v1 v2 →
        Val.Lessdef (Val.shrl v1 (.Vint k)) (Val.shrl v2 (.Vint k)) := by
      intro v1 v2 k h; cases h
      · exact .refl _
      · exact .undef _
    have Y : ∀ {v1 v2 : Val} (k : Integers.Int), Val.Lessdef v1 v2 →
        Val.Lessdef (Val.shrlu v1 (.Vint k)) (Val.shrlu v2 (.Vint k)) := by
      intro v1 v2 k h; cases h
      · exact .refl _
      · exact .undef _
    exact Val.lessdef_trans (X n (Val.lessdef_trans (Val.addl_lessdef (.refl _)
      (Val.lessdef_trans (Y _ B1) B2)) B3)) B4

end HELPERS

/-! ## Comparisons -/

section CMP

variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

theorem lessdef_ofBool_inv {b : Bool} {v : Val} (h : Val.Lessdef (Val.ofBool b) v) :
    v = Val.ofBool b := by
  cases b <;> exact lessdef_vint_inv h

theorem eval_intzero {le : Letenv} :
    CminorSel.EvalExpr ge sp e m le (.Eop (.Ointconst Integers.Int.zero) .Enil)
      (.Vint Integers.Int.zero) :=
  eval_op0 rfl

/-- `eval_cmpl_eq_zero` -/
theorem eval_cmpl_eq_zero {le : Letenv} {a : SplitLong.Expr} {x : Integers.Int64}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong x)) :
    CminorSel.EvalExpr ge sp e m le (cmpl_eq_zero a)
      (Val.ofBool (Integers.Int64.eq x Integers.Int64.zero)) := by
  unfold cmpl_eq_zero
  refine eval_splitlong_strict ha ?_
  intro le a1 a2 h1 h2
  obtain ⟨v1, A1, B1⟩ := eval_or le _ _ _ _ h1 h2
  obtain rfl := lessdef_vint_inv B1
  obtain ⟨v2, A2, B2⟩ := eval_comp .Ceq le _ _ _ _ A1 eval_intzero
  have hv : Val.cmp .Ceq (.Vint (Integers.Int.or (Integers.Int64.hiword x) (Integers.Int64.loword x)))
      (.Vint Integers.Int.zero) = Val.ofBool (Integers.Int64.eq x Integers.Int64.zero) := by
    rw [← Integers.Int64.ofwords_recompose x, Integers.Int64.decompose_cmpl_eq_zero,
      Integers.Int64.hi_ofwords, Integers.Int64.lo_ofwords]
    rfl
  rw [hv] at B2
  rw [← lessdef_ofBool_inv B2]
  exact A2

/-- `eval_cmpl_ne_zero` -/
theorem eval_cmpl_ne_zero {le : Letenv} {a : SplitLong.Expr} {x : Integers.Int64}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong x)) :
    CminorSel.EvalExpr ge sp e m le (cmpl_ne_zero a)
      (Val.ofBool (!(Integers.Int64.eq x Integers.Int64.zero))) := by
  unfold cmpl_ne_zero
  refine eval_splitlong_strict ha ?_
  intro le a1 a2 h1 h2
  obtain ⟨v1, A1, B1⟩ := eval_or le _ _ _ _ h1 h2
  obtain rfl := lessdef_vint_inv B1
  obtain ⟨v2, A2, B2⟩ := eval_comp .Cne le _ _ _ _ A1 eval_intzero
  have hv : Val.cmp .Cne (.Vint (Integers.Int.or (Integers.Int64.hiword x) (Integers.Int64.loword x)))
      (.Vint Integers.Int.zero) = Val.ofBool (!(Integers.Int64.eq x Integers.Int64.zero)) := by
    rw [← Integers.Int64.ofwords_recompose x, Integers.Int64.decompose_cmpl_eq_zero,
      Integers.Int64.hi_ofwords, Integers.Int64.lo_ofwords]
    rfl
  rw [hv] at B2
  rw [← lessdef_ofBool_inv B2]
  exact A2

/-- `eval_cmplu_gen` -/
theorem eval_cmplu_gen (ch cl : Comparison) {a b : SplitLong.Expr} {le : Letenv}
    {x y : Integers.Int64}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong x))
    (hb : CminorSel.EvalExpr ge sp e m le b (.Vlong y)) :
    CminorSel.EvalExpr ge sp e m le (cmplu_gen ch cl a b)
      (Val.ofBool (if Integers.Int.eq (Integers.Int64.hiword x) (Integers.Int64.hiword y)
        then Integers.Int.cmpu cl (Integers.Int64.loword x) (Integers.Int64.loword y)
        else Integers.Int.cmpu ch (Integers.Int64.hiword x) (Integers.Int64.hiword y))) := by
  unfold cmplu_gen
  refine eval_splitlong2_strict ha hb ?_
  intro le a1 a2 b1 b2 h1 h2 h3 h4
  refine .Econdition _ _ _ _ (Integers.Int.eq (Integers.Int64.hiword x) (Integers.Int64.hiword y)) _
    (.CEcond _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h3 (.Enil _))) rfl) ?_
  cases Integers.Int.eq (Integers.Int64.hiword x) (Integers.Int64.hiword y)
  · exact eval_op2 h1 h3 rfl
  · exact eval_op2 h2 h4 rfl

/-- `eval_cmpl_gen` -/
theorem eval_cmpl_gen (ch cl : Comparison) {a b : SplitLong.Expr} {le : Letenv}
    {x y : Integers.Int64}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong x))
    (hb : CminorSel.EvalExpr ge sp e m le b (.Vlong y)) :
    CminorSel.EvalExpr ge sp e m le (cmpl_gen ch cl a b)
      (Val.ofBool (if Integers.Int.eq (Integers.Int64.hiword x) (Integers.Int64.hiword y)
        then Integers.Int.cmpu cl (Integers.Int64.loword x) (Integers.Int64.loword y)
        else Integers.Int.cmp ch (Integers.Int64.hiword x) (Integers.Int64.hiword y))) := by
  unfold cmpl_gen
  refine eval_splitlong2_strict ha hb ?_
  intro le a1 a2 b1 b2 h1 h2 h3 h4
  refine .Econdition _ _ _ _ (Integers.Int.eq (Integers.Int64.hiword x) (Integers.Int64.hiword y)) _
    (.CEcond _ _ _ _ _ (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h3 (.Enil _))) rfl) ?_
  cases Integers.Int.eq (Integers.Int64.hiword x) (Integers.Int64.hiword y)
  · exact eval_op2 h1 h3 rfl
  · exact eval_op2 h2 h4 rfl

/-- `eval_cmplu`.  Rocq assumes `Archi.ptr64 = false`, under which `Val.cmplu` is defined
only on two 64-bit integers; here this is stated directly. -/
theorem eval_cmplu (c : Comparison) {le : Letenv} {a b : SplitLong.Expr} {x y : Integers.Int64}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong x))
    (hb : CminorSel.EvalExpr ge sp e m le b (.Vlong y)) :
    CminorSel.EvalExpr ge sp e m le (cmplu c a b) (Val.ofBool (Integers.Int64.cmpu c x y)) := by
  cases c
  · obtain ⟨v, A, B⟩ := eval_xorl le a _ b _ ha hb
    obtain rfl := lessdef_vlong_inv B
    show CminorSel.EvalExpr ge sp e m le (cmpl_eq_zero (xorl a b)) (Val.ofBool (Integers.Int64.eq x y))
    rw [Integers.Int64.int64_eq_xor]
    exact eval_cmpl_eq_zero A
  · obtain ⟨v, A, B⟩ := eval_xorl le a _ b _ ha hb
    obtain rfl := lessdef_vlong_inv B
    show CminorSel.EvalExpr ge sp e m le (cmpl_ne_zero (xorl a b))
      (Val.ofBool (!(Integers.Int64.eq x y)))
    rw [Integers.Int64.int64_eq_xor]
    exact eval_cmpl_ne_zero A
  · rw [Integers.Int64.cmpu_split .Clt .Clt .Clt (by simp)]; exact eval_cmplu_gen _ _ ha hb
  · rw [Integers.Int64.cmpu_split .Cle .Clt .Cle (by simp)]; exact eval_cmplu_gen _ _ ha hb
  · rw [Integers.Int64.cmpu_split .Cgt .Cgt .Cgt (by simp)]; exact eval_cmplu_gen _ _ ha hb
  · rw [Integers.Int64.cmpu_split .Cge .Cgt .Cge (by simp)]; exact eval_cmplu_gen _ _ ha hb

/-- `eval_cmpl` -/
theorem eval_cmpl (c : Comparison) {le : Letenv} {a b : SplitLong.Expr} {x y v : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a x) (hb : CminorSel.EvalExpr ge sp e m le b y)
    (h : Val.cmpl c x y = some v) :
    CminorSel.EvalExpr ge sp e m le (cmpl c a b) v := by
  cases x <;> cases y <;> simp only [Val.cmpl, Val.cmpl_bool, Option.map] at h <;> try cases h
  rename_i p q
  have LT0 : ∀ (c' : Comparison), (c' = .Clt ∨ c' = .Cge) →
      Integers.Int64.eq q Integers.Int64.zero = true →
      CminorSel.EvalExpr ge sp e m le (comp c' (highlong a) (.Eop (.Ointconst Integers.Int.zero) .Enil))
        (Val.ofBool (Integers.Int64.cmp c' p q)) := by
    intro c' hc' hq
    obtain rfl := (Integers.Int64.eq_spec _ _).mp hq
    obtain ⟨v1, A1, B1⟩ := eval_highlong le a _ ha
    obtain rfl := lessdef_vint_inv B1
    obtain ⟨v2, A2, B2⟩ := eval_comp c' le _ _ _ _ A1 eval_intzero
    have hv : Val.cmp c' (.Vint (Integers.Int64.hiword p)) (.Vint Integers.Int.zero) =
        Val.ofBool (Integers.Int64.cmp c' p Integers.Int64.zero) := by
      rcases hc' with rfl | rfl
      · show Val.ofBool (Integers.Int.lt _ _) = Val.ofBool (Integers.Int64.lt _ _)
        rw [← Integers.Int64.ofwords_recompose p, Integers.Int64.decompose_cmpl_lt_zero,
          Integers.Int64.hi_ofwords]
      · show Val.ofBool (!(Integers.Int.lt _ _)) = Val.ofBool (!(Integers.Int64.lt _ _))
        rw [← Integers.Int64.ofwords_recompose p, Integers.Int64.decompose_cmpl_lt_zero,
          Integers.Int64.hi_ofwords]
    rw [hv] at B2
    rw [← lessdef_ofBool_inv B2]
    exact A2
  cases c
  · obtain ⟨v, A, B⟩ := eval_xorl le a _ b _ ha hb
    obtain rfl := lessdef_vlong_inv B
    show CminorSel.EvalExpr ge sp e m le (cmpl_eq_zero (xorl a b)) (Val.ofBool (Integers.Int64.eq p q))
    rw [Integers.Int64.int64_eq_xor]
    exact eval_cmpl_eq_zero A
  · obtain ⟨v, A, B⟩ := eval_xorl le a _ b _ ha hb
    obtain rfl := lessdef_vlong_inv B
    show CminorSel.EvalExpr ge sp e m le (cmpl_ne_zero (xorl a b))
      (Val.ofBool (!(Integers.Int64.eq p q)))
    rw [Integers.Int64.int64_eq_xor]
    exact eval_cmpl_ne_zero A
  · dsimp only [cmpl]
    split
    · rename_i hz
      exact LT0 .Clt (.inl rfl) (by
        have := is_longconst_zero_sound hz hb
        cases this; decide)
    · rw [Integers.Int64.cmp_split .Clt .Clt .Clt (by simp)]; exact eval_cmpl_gen _ _ ha hb
  · rw [Integers.Int64.cmp_split .Cle .Clt .Cle (by simp)]; exact eval_cmpl_gen _ _ ha hb
  · rw [Integers.Int64.cmp_split .Cgt .Cgt .Cgt (by simp)]; exact eval_cmpl_gen _ _ ha hb
  · dsimp only [cmpl]
    split
    · rename_i hz
      exact LT0 .Cge (.inr rfl) (by
        have := is_longconst_zero_sound hz hb
        cases this; decide)
    · rw [Integers.Int64.cmp_split .Cge .Cgt .Cge (by simp)]; exact eval_cmpl_gen _ _ ha hb

end CMP

/-! ## Selection -/

/-- `eval_select_long`.  With the aarch64 operators `select_supported Tlong = true`, so only
the first case of the Rocq proof arises. -/
theorem eval_select_long {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}
    {le : Letenv} (cond : Condition) {al : SplitLong.Exprlist} {vl : List Val}
    {a1 a2 : SplitLong.Expr} {v1 v2 : Val}
    (hl : CminorSel.EvalExprlist ge sp e m le al vl)
    (h1 : CminorSel.EvalExpr ge sp e m le a1 v1) (h2 : CminorSel.EvalExpr ge sp e m le a2 v2) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (select_long cond al a1 a2) v ∧
      Val.Lessdef (Val.select (evalCondition cond vl m) v1 v2 .Tlong) v := by
  unfold select_long
  rw [if_pos (show selectSupported .Tlong = true from rfl)]
  exact eval_select .Tlong cond hl h1 h2

end SplitLongproof

end CC
