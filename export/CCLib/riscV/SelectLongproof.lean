/-
  Correctness of instruction selection for 64-bit integer operators
  (RISC-V) — port of `riscV/SelectLongproof.v`, for the 64-bit
  configuration (`Archi.splitlong = false`) of `CCLib.riscV.SelectLong`.

  As in `SelectOpproof.lean`, every smart constructor of `SelectLong` is shown
  to compute (an approximation, in the sense of `Val.Lessdef`, of) the value
  of the operator it implements.
-/
import CCLib.riscV.SelectOpproof4
import CCLib.riscV.SelectLong
import CCLib.lib.IntegersShifts64

namespace CC
namespace RiscV
namespace SelectLongproof

open Op CminorSel SelectOp SelectLong SelectOpproof

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-! ### Shift amounts for 64-bit shifts -/

theorem toNat_lt_64_of_ltu {y : Integers.Int} (h : Integers.Int.ltu y Integers.Int64.iwordsize' = true) :
    y.toNat < 64 := by
  rw [Integers.Int.ltu_toNat] at h
  have : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  simp only [this, decide_eq_true_eq] at h
  exact h

theorem int_add_toNat {a n : Integers.Int} (ha : a.toNat < 64) (hn : n.toNat < 64) :
    (Integers.Int.add a n).toNat = a.toNat + n.toNat := by
  show (a + n).toNat = _
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)

theorem val_shll_long (x : Integers.Int64) {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shll (.Vlong x) (.Vint n) = .Vlong (x <<< n.toNat) := by
  simp only [Val.shll]
  split
  · rw [← Integers.Int64.shl'_eq]; rfl
  · rename_i hc; exact absurd h hc

theorem val_shrlu_long (x : Integers.Int64) {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shrlu (.Vlong x) (.Vint n) = .Vlong (x >>> n.toNat) := by
  simp only [Val.shrlu]
  split
  · rw [← Integers.Int64.shru'_eq]; rfl
  · rename_i hc; exact absurd h hc

theorem val_shrl_long (x : Integers.Int64) {n : Integers.Int}
    (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shrl (.Vlong x) (.Vint n) = .Vlong (x.sshiftRight n.toNat) := by
  simp only [Val.shrl]
  split
  · rw [← Integers.Int64.shr'_eq]; rfl
  · rename_i hc; exact absurd h hc

theorem val_shll_undef (x : Integers.Int64) {n : Integers.Int}
    (h : ¬ Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shll (.Vlong x) (.Vint n) = .Vundef := by
  simp only [Val.shll]
  split
  · rename_i hc; exact absurd hc h
  · rfl

theorem val_shrlu_undef (x : Integers.Int64) {n : Integers.Int}
    (h : ¬ Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shrlu (.Vlong x) (.Vint n) = .Vundef := by
  simp only [Val.shrlu]
  split
  · rename_i hc; exact absurd hc h
  · rfl

theorem val_shrl_undef (x : Integers.Int64) {n : Integers.Int}
    (h : ¬ Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    Val.shrl (.Vlong x) (.Vint n) = .Vundef := by
  simp only [Val.shrl]
  split
  · rename_i hc; exact absurd hc h
  · rfl

theorem val_shll_zero (x : Val) : Val.Lessdef (Val.shll x (.Vint Integers.Int.zero)) x := by
  cases x <;> try ld
  rw [val_shll_long _ (by decide), show (Integers.Int.zero : Integers.Int).toNat = 0 from rfl,
    BitVec.shiftLeft_zero]; ld

theorem val_shrlu_zero (x : Val) : Val.Lessdef (Val.shrlu x (.Vint Integers.Int.zero)) x := by
  cases x <;> try ld

theorem val_shrl_zero (x : Val) : Val.Lessdef (Val.shrl x (.Vint Integers.Int.zero)) x := by
  cases x <;> try ld
  rw [val_shrl_long _ (by decide), show (Integers.Int.zero : Integers.Int).toNat = 0 from rfl,
    BitVec.sshiftRight_zero]
  try ld

theorem val_shll_shll_ld (v : Val) {a n : Integers.Int}
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true)
    (h : Integers.Int.ltu (Integers.Int.add n a) Integers.Int64.iwordsize' = true) :
    Val.Lessdef (Val.shll (Val.shll v (.Vint a)) (.Vint n))
      (Val.shll v (.Vint (Integers.Int.add n a))) := by
  cases v <;> try ld
  by_cases ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true
  · rw [val_shll_long _ ha, val_shll_long _ hn, val_shll_long _ h, Integers.Int64.shl_shl_nat,
      int_add_toNat (toNat_lt_64_of_ltu hn) (toNat_lt_64_of_ltu ha), Nat.add_comm]; ld
  · rw [val_shll_undef _ ha]; ld

theorem val_shrlu_shrlu_ld (v : Val) {a n : Integers.Int}
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true)
    (h : Integers.Int.ltu (Integers.Int.add n a) Integers.Int64.iwordsize' = true) :
    Val.Lessdef (Val.shrlu (Val.shrlu v (.Vint a)) (.Vint n))
      (Val.shrlu v (.Vint (Integers.Int.add n a))) := by
  cases v <;> try ld
  by_cases ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true
  · rw [val_shrlu_long _ ha, val_shrlu_long _ hn, val_shrlu_long _ h, Integers.Int64.shru_shru_nat,
      int_add_toNat (toNat_lt_64_of_ltu hn) (toNat_lt_64_of_ltu ha), Nat.add_comm]; ld
  · rw [val_shrlu_undef _ ha]; ld

theorem val_shrl_shrl_ld (v : Val) {a n : Integers.Int}
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true)
    (h : Integers.Int.ltu (Integers.Int.add n a) Integers.Int64.iwordsize' = true) :
    Val.Lessdef (Val.shrl (Val.shrl v (.Vint a)) (.Vint n))
      (Val.shrl v (.Vint (Integers.Int.add n a))) := by
  cases v <;> try ld
  by_cases ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true
  · rw [val_shrl_long _ ha, val_shrl_long _ hn, val_shrl_long _ h, Integers.Int64.shr_shr_nat,
      int_add_toNat (toNat_lt_64_of_ltu hn) (toNat_lt_64_of_ltu ha), Nat.add_comm]; ld
  · rw [val_shrl_undef _ ha]; ld

/-! ### Recognisers -/

theorem isLongconst_sound {a : SelectOp.Expr} {n : Integers.Int64} (h : isLongconst a = some n) :
    a = .Eop (.Olongconst n) .Enil := by
  unfold isLongconst at h
  split at h
  · cases h; rfl
  · cases h

theorem isIntconst_sound {a : SelectOp.Expr} {n : Integers.Int} (h : isIntconst a = some n) :
    a = .Eop (.Ointconst n) .Enil := by
  unfold isIntconst at h
  split at h
  · cases h; rfl
  · cases h

section CMCONSTR
variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

/-! ### Constants -/

/-- `eval_longconst` -/
theorem eval_longconst (le : Letenv) (n : Integers.Int64) :
    CminorSel.EvalExpr ge sp e m le (longconst n) (.Vlong n) :=
  eval_op0 rfl

theorem inv_longconst {le : Letenv} {n : Integers.Int64} {v : Val}
    (h : CminorSel.EvalExpr ge sp e m le (.Eop (.Olongconst n) .Enil) v) : v = .Vlong n := by
  have : some (Val.Vlong n) = some v := inv_op0 h
  exact (Option.some.inj this).symm

/-- `is_longconst_sound` -/
theorem is_longconst_sound {le : Letenv} {a : SelectOp.Expr} {x : Val} {n : Integers.Int64}
    (h : isLongconst a = some n) (hx : CminorSel.EvalExpr ge sp e m le a x) : x = .Vlong n := by
  rw [isLongconst_sound h] at hx; exact inv_longconst hx

/-! ### Conversions -/

/-- `eval_intoflong` -/
theorem eval_intoflong : UnarySound ge sp e m intoflong Val.loword := by
  intro le a x hx
  unfold intoflong
  cases h : isLongconst a with
  | some n =>
    obtain rfl := is_longconst_sound h hx
    exact ⟨_, eval_op0 rfl, by simp [Val.loword, Integers.Int64.loword]; ld⟩
  | none => exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_longofintu` -/
theorem eval_longofintu : UnarySound ge sp e m longofintu Val.longofintu := by
  intro le a x hx
  unfold longofintu
  cases h : isIntconst a with
  | some n =>
    rw [isIntconst_sound h] at hx
    obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.longofintu]; ld⟩
  | none => exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_longofint` -/
theorem eval_longofint : UnarySound ge sp e m longofint Val.longofint := by
  intro le a x hx
  unfold longofint
  cases h : isIntconst a with
  | some n =>
    rw [isIntconst_sound h] at hx
    obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.longofint]; ld⟩
  | none => exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_negl` -/
theorem eval_negl : UnarySound ge sp e m negl Val.negl := by
  intro le a x hx
  unfold negl
  cases h : isLongconst a with
  | some n =>
    obtain rfl := is_longconst_sound h hx
    exact ⟨_, eval_op0 rfl, by simp [Val.negl]; ld⟩
  | none => exact ⟨_, eval_op1 hx rfl, by ld⟩

/-! ### Addition, subtraction -/

/-- `eval_addlimm` -/
theorem eval_addlimm (n : Integers.Int64) :
    UnarySound ge sp e m (addlimm n) (fun x => Val.addl x (.Vlong n)) := by
  intro le a x hx
  unfold addlimm
  by_cases hn : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos hn]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp hn
    refine ⟨x, hx, ?_⟩
    cases x <;> simp [Val.addl, Archi.ptr64, Integers.Int64.add_zero] <;> try ld
    rw [show Integers.Ptrofs.of_int64 Integers.Int64.zero = Integers.Ptrofs.zero by decide,
      Integers.Ptrofs.add_zero]; ld
  · rw [if_neg hn]
    split
    · obtain rfl := inv_longconst hx
      exact ⟨_, eval_op0 rfl, by simp [Val.addl, Integers.Int64.add_commut]; ld⟩
    · rename_i s ofs
      have hv : some (Genv.symbolAddress ge s ofs) = some x := inv_op0 hx
      cases hv
      refine ⟨_, eval_op0 rfl, ?_⟩
      show Val.Lessdef _ (Genv.symbolAddress ge s _)
      rw [Integers.Ptrofs.add_commut, Genv.shift_symbolAddress_64]; ld
    · rename_i ofs
      have hv : some (Val.offsetPtr sp ofs) = some x := inv_op0 hx
      cases hv
      refine ⟨_, eval_op0 rfl, ?_⟩
      show Val.Lessdef _ (Val.offsetPtr sp _)
      cases sp <;> simp [Val.offsetPtr, Val.addl, Archi.ptr64] <;> try ld
      rw [Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_commut ofs]; ld
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.addl (Val.addl v1 _) _) _
      rw [Val.addl_assoc]; simp [Val.addl, Integers.Int64.add_commut]; ld
    · exact ⟨_, eval_op1 hx rfl, .refl _⟩

theorem addl_stack_l (v1 sp : Val) (n1 : Integers.Int64) (n2 : Integers.Ptrofs) :
    Val.Lessdef (Val.addl (Val.addl v1 (.Vlong n1)) (Val.offsetPtr sp n2))
      (Val.addl (Val.offsetPtr sp (Integers.Ptrofs.add (Integers.Ptrofs.of_int64 n1) n2)) v1) := by
  cases sp <;> cases v1 <;> simp [Val.addl, Val.offsetPtr, Archi.ptr64] <;> try ld
  rw [Val.Ptrofs_of_int64_add]
  show Val.Lessdef (.Vptr _ (_ + _ + (_ + _))) (.Vptr _ (_ + (_ + _) + _))
  rw [show ∀ a b c d : Integers.Ptrofs, a + b + (c + d) = a + (d + b) + c from by
    intro a b c d; ac_rfl]; ld

theorem addl_stack_r (v2 sp : Val) (n1 : Integers.Ptrofs) (n2 : Integers.Int64) :
    Val.Lessdef (Val.addl (Val.offsetPtr sp n1) (Val.addl v2 (.Vlong n2)))
      (Val.addl (Val.offsetPtr sp (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 n2))) v2) := by
  rw [Val.addl_commut]
  have := addl_stack_l v2 sp n2 n1
  rwa [Integers.Ptrofs.add_commut] at this

/-- `eval_addl` -/
theorem eval_addl : BinarySound ge sp e m addl Val.addl := by
  intro le a x b y hx hy
  unfold addl
  split
  · obtain rfl := inv_longconst hx
    rw [Val.addl_commut]; exact eval_addlimm _ le _ _ hy
  · obtain rfl := inv_longconst hy
    exact eval_addlimm _ le _ _ hx
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho1; cases ho2
    rw [Val.addl_permut_4,
      show Val.addl (.Vlong _) (.Vlong _) = .Vlong (Integers.Int64.add _ _) from rfl]
    exact eval_addlimm _ le _ _ (eval_op2 (op := .Oaddl) h1 h2 rfl)
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    have hv : some (Val.offsetPtr sp _) = some y := inv_op0 hy
    cases ho1; cases hv
    exact ⟨_, eval_op2 (eval_op0 rfl) h1 rfl, addl_stack_l _ _ _ _⟩
  · have hv : some (Val.offsetPtr sp _) = some x := inv_op0 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2; cases hv
    exact ⟨_, eval_op2 (eval_op0 rfl) h2 rfl, addl_stack_r _ _ _ _⟩
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    rw [Val.addl_assoc, Val.addl_commut (.Vlong _) y, ← Val.addl_assoc]
    exact eval_addlimm _ le _ _ (eval_op2 (op := .Oaddl) h1 hy rfl)
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    rw [← Val.addl_assoc]
    exact eval_addlimm _ le _ _ (eval_op2 (op := .Oaddl) hx h2 rfl)
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_subl` -/
theorem eval_subl : BinarySound ge sp e m subl Val.subl := by
  intro le a x b y hx hy
  unfold subl
  split
  · obtain rfl := inv_longconst hy
    rw [Val.subl_addl_opp]; exact eval_addlimm _ le _ _ hx
  · rename_i n1 t1 n2 t2
    obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho1; cases ho2
    rw [Val.subl_addl_l, Val.subl_addl_r, Val.addl_assoc,
      show Val.addl (.Vlong (Integers.Int64.neg n2)) (.Vlong n1) = .Vlong (Integers.Int64.sub n1 n2) by
        simp [Val.addl, Integers.Int64.add_commut, Integers.Int64.sub_add_opp]]
    exact eval_addlimm _ le _ _ (eval_op2 (op := .Osubl) h1 h2 rfl)
  · obtain ⟨v1, h1, ho1⟩ := inv_op1 hx
    cases ho1
    rw [Val.subl_addl_l]
    exact eval_addlimm _ le _ _ (eval_op2 (op := .Osubl) h1 hy rfl)
  · obtain ⟨v2, h2, ho2⟩ := inv_op1 hy
    cases ho2
    rw [Val.subl_addl_r]
    exact eval_addlimm _ le _ _ (eval_op2 (op := .Osubl) hx h2 rfl)
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Immediate shifts -/

/-- `eval_shllimm` -/
theorem eval_shllimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shllimm a n) (fun x => Val.shll x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shllimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shll_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int64.iwordsize'
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by rw [val_shll_long _ L]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      exact ⟨_, eval_op1 h1 rfl, val_shll_shll_ld v1 L L2⟩
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_shrluimm` -/
theorem eval_shrluimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shrluimm a n) (fun x => Val.shrlu x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shrluimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shrlu_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int64.iwordsize'
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by rw [val_shrlu_long _ L]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      exact ⟨_, eval_op1 h1 rfl, val_shrlu_shrlu_ld v1 L L2⟩
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-- `eval_shrlimm` -/
theorem eval_shrlimm (n : Integers.Int) :
    UnarySound ge sp e m (fun a => shrlimm a n) (fun x => Val.shrl x (.Vint n)) := by
  intro le a x hx
  dsimp only
  unfold shrlimm
  by_cases hz : Integers.Int.eq n Integers.Int.zero = true
  · rw [if_pos hz]
    obtain rfl := (Integers.Int.eq_spec _ _).mp hz
    exact ⟨x, hx, val_shrl_zero x⟩
  rw [if_neg hz]
  cases L : Integers.Int.ltu n Integers.Int64.iwordsize'
  · rw [if_pos (by decide)]
    exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩
  rw [if_neg (by decide)]
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by rw [val_shrl_long _ L]; ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      exact ⟨_, eval_op1 h1 rfl, val_shrl_shrl_ld v1 L L2⟩
    · exact ⟨_, eval_op1 hx rfl, by ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

/-! ### General shifts -/

/-- `eval_shll` -/
theorem eval_shll : BinarySound ge sp e m shll Val.shll := by
  intro le a x b y hx hy
  unfold shll
  cases h : isIntconst b with
  | some n =>
    rw [isIntconst_sound h] at hy
    obtain rfl := inv_intconst hy
    exact eval_shllimm _ le _ _ hx
  | none => exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shrl` -/
theorem eval_shrl : BinarySound ge sp e m shrl Val.shrl := by
  intro le a x b y hx hy
  unfold shrl
  cases h : isIntconst b with
  | some n =>
    rw [isIntconst_sound h] at hy
    obtain rfl := inv_intconst hy
    exact eval_shrlimm _ le _ _ hx
  | none => exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_shrlu` -/
theorem eval_shrlu : BinarySound ge sp e m shrlu Val.shrlu := by
  intro le a x b y hx hy
  unfold shrlu
  cases h : isIntconst b with
  | some n =>
    rw [isIntconst_sound h] at hy
    obtain rfl := inv_intconst hy
    exact eval_shrluimm _ le _ _ hx
  | none => exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-! ### Multiplication -/

/-- `eval_mullimm_base` -/
theorem eval_mullimmBase (n : Integers.Int64) :
    UnarySound ge sp e m (mullimmBase n) (fun x => Val.mull x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold mullimmBase
  split
  · next i h =>
    obtain ⟨hi, hmul⟩ := Integers.Int64.one_bits'_single h
    obtain ⟨v, hv, hl⟩ := eval_shllimm i le a x hx
    refine ⟨v, hv, Val.lessdef_trans ?_ hl⟩
    cases x <;> try ld
    dsimp only; rw [val_shll_long _ hi]
    simp only [Val.mull]; rw [hmul]; ld
  · next i j h =>
    obtain ⟨hi, hj, hmul⟩ := Integers.Int64.one_bits'_double h
    have hx0 : CminorSel.EvalExpr ge sp e m (x :: le) (.Eletvar 0) x := .Eletvar _ _ _ rfl
    obtain ⟨v1, hv1, hl1⟩ := eval_shllimm i (x :: le) _ x hx0
    obtain ⟨v2, hv2, hl2⟩ := eval_shllimm j (x :: le) _ x hx0
    obtain ⟨v, hv, hl⟩ := eval_addl (x :: le) _ _ _ _ hv1 hv2
    refine ⟨v, .Elet _ _ _ _ _ hx hv,
      Val.lessdef_trans ?_ (Val.lessdef_trans (Val.addl_lessdef hl1 hl2) hl)⟩
    cases x <;> try ld
    dsimp only; rw [val_shll_long _ hi, val_shll_long _ hj]
    simp only [Val.mull, Val.addl]; rw [hmul]; ld
  · exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩

/-- `eval_mullimm` -/
theorem eval_mullimm (n : Integers.Int64) :
    UnarySound ge sp e m (mullimm n) (fun x => Val.mull x (.Vlong n)) := by
  intro le a x hx
  dsimp only
  unfold mullimm
  by_cases h0 : Integers.Int64.eq n Integers.Int64.zero = true
  · rw [if_pos h0]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h0
    exact ⟨_, eval_op0 rfl, by cases x <;> simp [Val.mull, Integers.Int64.mul_zero] <;> ld⟩
  rw [if_neg h0]
  by_cases h1 : Integers.Int64.eq n Integers.Int64.one = true
  · rw [if_pos h1]
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h1
    exact ⟨x, hx, by cases x <;> simp [Val.mull, Integers.Int64.mul_one] <;> ld⟩
  rw [if_neg h1]
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.mull, Integers.Int64.mul_commut]; ld⟩
  · next n2 t2 =>
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    obtain ⟨v', hv', hl'⟩ := eval_mullimmBase n le _ _ h1
    obtain ⟨v'', hv'', hl''⟩ := eval_addlimm (Integers.Int64.mul n n2) le _ _ hv'
    refine ⟨v'', hv'',
      Val.lessdef_trans ?_ (Val.lessdef_trans (Val.addl_lessdef hl' (.refl _)) hl'')⟩
    rw [Val.mull_addl_distr_l]
    show Val.Lessdef (Val.addl _ (Val.mull (.Vlong n2) (.Vlong n))) _
    rw [Val.mull_commut (.Vlong n2)]; ld
  · exact eval_mullimmBase n le _ _ hx

/-- `eval_mull` -/
theorem eval_mull : BinarySound ge sp e m mull Val.mull := by
  intro le a x b y hx hy
  unfold mull
  split
  · obtain rfl := inv_longconst hx
    rw [Val.mull_commut]; exact eval_mullimm _ le _ _ hy
  · obtain rfl := inv_longconst hy
    exact eval_mullimm _ le _ _ hx
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

/-- `eval_mullhu` -/
theorem eval_mullhu (n : Integers.Int64) :
    UnarySound ge sp e m (fun a => mullhu a n) (fun v => Val.mullhu v (.Vlong n)) := by
  intro le a x hx
  exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩

/-- `eval_mullhs` -/
theorem eval_mullhs (n : Integers.Int64) :
    UnarySound ge sp e m (fun a => mullhs a n) (fun v => Val.mullhs v (.Vlong n)) := by
  intro le a x hx
  exact ⟨_, eval_op2 hx (eval_op0 rfl) rfl, by ld⟩

end CMCONSTR

end SelectLongproof
end RiscV
end CC
