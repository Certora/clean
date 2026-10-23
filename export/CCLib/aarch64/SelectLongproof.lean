/-
  Correctness of instruction selection for 64-bit integer operators
  (aarch64) — port of `aarch64/SelectLongproof.v`.

  As in `SelectOpproof.lean`, every smart constructor of `SelectLong` is shown
  to compute (an approximation, in the sense of `Val.Lessdef`, of) the value
  of the operator it implements.
-/
import CCLib.aarch64.SelectOpproof3
import CCLib.aarch64.SelectLong
import CCLib.lib.IntegersShifts64

namespace CC
namespace SelectLongproof

open Op CminorSel SelectOp SelectLong SelectOpproof

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- Close a `Val.Lessdef` goal that holds by reflexivity or because the left side is
`Vundef`. -/
local macro "ld" : tactic => `(tactic| first | exact Val.Lessdef.refl _ | exact Val.Lessdef.undef _)

/-! ### Shift amounts for 64-bit shifts -/

theorem toNat_lt_64_of_ltu {y : Integers.Int} (h : Integers.Int.ltu y Integers.Int64.iwordsize' = true) :
    y.toNat < 64 := by
  rw [Integers.Int.ltu_toNat] at h
  have : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  simp only [this, decide_eq_true_eq] at h
  exact h

theorem ltu_iw64_of_toNat {y : Integers.Int} (h : y.toNat < 64) :
    Integers.Int.ltu y Integers.Int64.iwordsize' = true := by
  rw [Integers.Int.ltu_toNat]
  have : (Integers.Int64.iwordsize' : Integers.Int).toNat = 64 := by decide
  rw [this]; exact decide_eq_true h

/-- `Op.mk_amount64_eq` -/
theorem mkAmount64_eq {n : Integers.Int} (h : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    (mkAmount64 n).a64_amount = n := by
  have hn := toNat_lt_64_of_ltu h
  show Integers.Int.zero_ext 6 n = n
  apply Integers.Int.same_bits_eq; intro i hi
  rw [Integers.Int.bits_zero_ext]
  by_cases h6 : i < 6
  · simp [h6]
  · simp only [decide_eq_false h6, Bool.false_and]
    show false = n.getLsbD i
    rw [BitVec.getLsbD, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn
      (show 64 ≤ 2 ^ i from Nat.le_trans (by decide : 64 ≤ 2 ^ 6)
        (Nat.pow_le_pow_right (by decide) (by omega))))]

theorem a64_toNat (a : Amount64) : a.a64_amount.toNat < 64 := toNat_lt_64_of_ltu a.a64_range

/-- `Val.shll` of a long by a valid amount, as a `BitVec` shift. -/
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

/-! ### Conversions -/

/-- `eval_intoflong` -/
theorem eval_intoflong : UnarySound ge sp e m intoflong Val.loword := by
  intro le a x hx
  unfold intoflong
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.loword, Integers.Int64.loword]; ld⟩
  · exact ⟨_, eval_op1 hx rfl, by ld⟩

theorem extend_zero_uns (v : Val) :
    Val.Lessdef (Val.longofintu v) (evalExtend .Xuns32 v (mkAmount64 Integers.Int.zero)) := by
  unfold evalExtend
  rw [mkAmount64_eq (by decide)]
  cases v <;> simp only [Val.longofintu] <;> try ld
  rw [val_shll_long _ (by decide), show (Integers.Int.zero : Integers.Int).toNat = 0 from rfl,
    BitVec.shiftLeft_zero]; ld

theorem extend_zero_sgn (v : Val) :
    Val.Lessdef (Val.longofint v) (evalExtend .Xsgn32 v (mkAmount64 Integers.Int.zero)) := by
  unfold evalExtend
  rw [mkAmount64_eq (by decide)]
  cases v <;> simp only [Val.longofint] <;> try ld
  rw [val_shll_long _ (by decide), show (Integers.Int.zero : Integers.Int).toNat = 0 from rfl,
    BitVec.shiftLeft_zero]; ld

/-- `eval_longofintu` -/
theorem eval_longofintu : UnarySound ge sp e m longofintu Val.longofintu := by
  intro le a x hx
  unfold longofintu
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.longofintu]; ld⟩
  · exact ⟨_, eval_op1 hx rfl, extend_zero_uns _⟩

/-- `eval_longofint` -/
theorem eval_longofint : UnarySound ge sp e m longofint Val.longofint := by
  intro le a x hx
  unfold longofint
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_op0 rfl, by simp [Val.longofint]; ld⟩
  · exact ⟨_, eval_op1 hx rfl, extend_zero_sgn _⟩

/-! ### Addition, opposite, subtraction -/

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
    · rename_i k t
      obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.addl (Val.addl v1 _) _) _
      rw [Val.addl_assoc]; simp [Val.addl, Integers.Int64.add_commut]; ld
    · exact ⟨_, eval_op1 hx rfl, .refl _⟩

theorem eval_addlRest2 : BinarySound ge sp e m addlRest2 Val.addl := by
  intro le a x b y hx hy
  unfold addlRest2
  split
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.addl_commut]; ld⟩
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy
    cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx
    cases ho
    exact ⟨_, eval_op3 hy h1 h2 rfl, by rw [Val.addl_commut]; ld⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hy
    cases ho
    exact ⟨_, eval_op3 hx h1 h2 rfl, by ld⟩
  · exact ⟨_, eval_op2 hx hy rfl, by ld⟩

theorem eval_addlRest1 : BinarySound ge sp e m addlRest1 Val.addl := by
  intro le a x b y hx hy
  unfold addlRest1
  split
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hy
      cases ho
      exact ⟨_, eval_op2 hx h1 rfl, by ld⟩
    · exact eval_addlRest2 le _ _ _ _ hx hy
  · exact eval_addlRest2 le _ _ _ _ hx hy

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
    rw [Val.addl_permut_4, show Val.addl (.Vlong _) (.Vlong _) = .Vlong (Integers.Int64.add _ _) from rfl]
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
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      exact ⟨_, eval_op2 hy h1 rfl, by rw [Val.addl_commut]; ld⟩
    · exact eval_addlRest1 le _ _ _ _ hx hy
  · exact eval_addlRest1 le _ _ _ _ hx hy

/-- `eval_negl` -/
theorem eval_negl : UnarySound ge sp e m negl (fun v => Val.subl (.Vlong Integers.Int64.zero) v) := by
  intro le a x hx
  have hneg : ∀ v, Val.Lessdef (Val.subl (.Vlong Integers.Int64.zero) v) (Val.negl v) := by
    intro v; cases v <;> simp [Val.subl, Val.negl, Integers.Int64.sub_zero_l] <;> ld
  unfold negl
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by
      simp [Val.subl, Integers.Int64.sub_zero_l]; ld⟩
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
      cases ho
      exact ⟨_, eval_op1 h1 rfl, hneg _⟩
    · exact ⟨_, eval_op1 hx rfl, hneg _⟩
  · exact ⟨_, eval_op1 hx rfl, hneg _⟩

theorem eval_sublRest : BinarySound ge sp e m sublRest Val.subl := by
  intro le a x b y hx hy
  unfold sublRest
  split
  · obtain ⟨v2, h2, ho⟩ := inv_op1 hy
    cases ho
    exact ⟨_, eval_op2 hx h2 rfl, by ld⟩
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hy
    cases ho
    exact ⟨_, eval_op3 hx h1 h2 rfl, by ld⟩
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
  · split
    · obtain ⟨v1, h1, ho⟩ := inv_op1 hy
      cases ho
      exact ⟨_, eval_op2 hx h1 rfl, by ld⟩
    · exact eval_sublRest le _ _ _ _ hx hy
  · exact eval_sublRest le _ _ _ _ hx hy

/-! ### Immediate shifts -/

theorem int_add_toNat {a n : Integers.Int} (ha : a.toNat < 64) (hn : n.toNat < 64) :
    (Integers.Int.add a n).toNat = a.toNat + n.toNat := by
  show (a + n).toNat = _
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)

theorem unsigned_eq_toNat (a : Integers.Int) : Integers.Int.unsigned a = (a.toNat : _root_.Int) := rfl

theorem zw64_sub_toNat (a : Integers.Int) :
    (Integers.Int64.zwordsize - Integers.Int.unsigned a).toNat = 64 - a.toNat := by
  show ((64 : _root_.Int) - (a.toNat : _root_.Int)).toNat = _; omega

theorem mkAmount64_sub {a n : Integers.Int} (ha : a.toNat < 64) (h : n.toNat ≤ a.toNat) :
    (mkAmount64 (Integers.Int.sub a n)).a64_amount = Integers.Int.sub a n :=
  mkAmount64_eq (ltu_iw64_of_toNat (by rw [Integers.Int.sub_toNat h]; omega))

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

theorem val_shll_shll (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true)
    (h : Integers.Int.ltu (Integers.Int.add a n) Integers.Int64.iwordsize' = true) :
    Val.shll (Val.shll v (.Vint a)) (.Vint n) = Val.shll v (.Vint (Integers.Int.add a n)) := by
  cases v <;> try rfl
  rw [val_shll_long _ ha, val_shll_long _ hn, val_shll_long _ h, Integers.Int64.shl_shl_nat,
    int_add_toNat (toNat_lt_64_of_ltu ha) (toNat_lt_64_of_ltu hn)]

theorem val_shrlu_shrlu (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true)
    (h : Integers.Int.ltu (Integers.Int.add a n) Integers.Int64.iwordsize' = true) :
    Val.shrlu (Val.shrlu v (.Vint a)) (.Vint n) = Val.shrlu v (.Vint (Integers.Int.add a n)) := by
  cases v <;> try rfl
  rw [val_shrlu_long _ ha, val_shrlu_long _ hn, val_shrlu_long _ h, Integers.Int64.shru_shru_nat,
    int_add_toNat (toNat_lt_64_of_ltu ha) (toNat_lt_64_of_ltu hn)]

theorem val_shrl_shrl (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true)
    (h : Integers.Int.ltu (Integers.Int.add a n) Integers.Int64.iwordsize' = true) :
    Val.shrl (Val.shrl v (.Vint a)) (.Vint n) = Val.shrl v (.Vint (Integers.Int.add a n)) := by
  cases v <;> try rfl
  rw [val_shrl_long _ ha, val_shrl_long _ hn, val_shrl_long _ h, Integers.Int64.shr_shr_nat,
    int_add_toNat (toNat_lt_64_of_ltu ha) (toNat_lt_64_of_ltu hn)]

theorem val_shrlu_shll_lt (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true) (hlt : n.toNat < a.toNat) :
    Val.shrlu (Val.shll v (.Vint a)) (.Vint n) =
      Val.shll (Val.zero_ext_l (64 - a.toNat) v) (.Vint (Integers.Int.sub a n)) := by
  have ha' := toNat_lt_64_of_ltu ha
  have hn' := toNat_lt_64_of_ltu hn
  have hs : Integers.Int.ltu (Integers.Int.sub a n) Integers.Int64.iwordsize' = true :=
    ltu_iw64_of_toNat (by rw [Integers.Int.sub_toNat (by omega)]; omega)
  cases v <;> try rfl
  simp only [Val.zero_ext_l]
  rw [val_shll_long _ ha, val_shrlu_long _ hn, val_shll_long _ hs, Integers.Int64.shru_shl_nat _ ha' hn',
    if_pos hlt, Integers.Int.sub_toNat (by omega)]

theorem val_shrlu_shll_ge (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true) (hge : a.toNat ≤ n.toNat) :
    Val.shrlu (Val.shll v (.Vint a)) (.Vint n) =
      Val.zero_ext_l (64 - n.toNat) (Val.shrlu v (.Vint (Integers.Int.sub n a))) := by
  have ha' := toNat_lt_64_of_ltu ha
  have hn' := toNat_lt_64_of_ltu hn
  have hs : Integers.Int.ltu (Integers.Int.sub n a) Integers.Int64.iwordsize' = true :=
    ltu_iw64_of_toNat (by rw [Integers.Int.sub_toNat hge]; omega)
  cases v <;> try rfl
  rw [val_shll_long _ ha, val_shrlu_long _ hn, val_shrlu_long _ hs, Integers.Int64.shru_shl_nat _ ha' hn',
    if_neg (by omega), Integers.Int.sub_toNat hge]
  rfl

theorem val_shrl_shll_lt (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true) (hlt : n.toNat < a.toNat) :
    Val.shrl (Val.shll v (.Vint a)) (.Vint n) =
      Val.shll (Val.sign_ext_l (64 - a.toNat) v) (.Vint (Integers.Int.sub a n)) := by
  have ha' := toNat_lt_64_of_ltu ha
  have hn' := toNat_lt_64_of_ltu hn
  have hs : Integers.Int.ltu (Integers.Int.sub a n) Integers.Int64.iwordsize' = true :=
    ltu_iw64_of_toNat (by rw [Integers.Int.sub_toNat (by omega)]; omega)
  cases v <;> try rfl
  simp only [Val.sign_ext_l]
  rw [val_shll_long _ ha, val_shrl_long _ hn, val_shll_long _ hs, Integers.Int64.shr_shl_nat _ ha' hn',
    if_pos hlt, Integers.Int.sub_toNat (by omega)]

theorem val_shrl_shll_ge (v : Val) {a n : Integers.Int}
    (ha : Integers.Int.ltu a Integers.Int64.iwordsize' = true)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true) (hge : a.toNat ≤ n.toNat) :
    Val.shrl (Val.shll v (.Vint a)) (.Vint n) =
      Val.sign_ext_l (64 - n.toNat) (Val.shrl v (.Vint (Integers.Int.sub n a))) := by
  have ha' := toNat_lt_64_of_ltu ha
  have hn' := toNat_lt_64_of_ltu hn
  have hs : Integers.Int.ltu (Integers.Int.sub n a) Integers.Int64.iwordsize' = true :=
    ltu_iw64_of_toNat (by rw [Integers.Int.sub_toNat hge]; omega)
  cases v <;> try rfl
  rw [val_shll_long _ ha, val_shrl_long _ hn, val_shrl_long _ hs, Integers.Int64.shr_shl_nat _ ha' hn',
    if_neg (by omega), Integers.Int.sub_toNat hge]
  rfl

theorem eval_shllimmBase {le : Letenv} {a : SelectOp.Expr} {x : Val} {n : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le a x)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    CminorSel.EvalExpr ge sp e m le (shllimmBase a n) (Val.shll x (.Vint n)) := by
  unfold shllimmBase
  refine eval_op1 hx ?_
  show some (Val.shll x (.Vint (mkAmount64 n).a64_amount)) = _
  rw [mkAmount64_eq hn]

theorem eval_shrluimmBase {le : Letenv} {a : SelectOp.Expr} {x : Val} {n : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le a x)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    CminorSel.EvalExpr ge sp e m le (shrluimmBase a n) (Val.shrlu x (.Vint n)) := by
  unfold shrluimmBase
  refine eval_op1 hx ?_
  show some (Val.shrlu x (.Vint (mkAmount64 n).a64_amount)) = _
  rw [mkAmount64_eq hn]

theorem eval_shrlimmBase {le : Letenv} {a : SelectOp.Expr} {x : Val} {n : Integers.Int}
    (hx : CminorSel.EvalExpr ge sp e m le a x)
    (hn : Integers.Int.ltu n Integers.Int64.iwordsize' = true) :
    CminorSel.EvalExpr ge sp e m le (shrlimmBase a n) (Val.shrl x (.Vint n)) := by
  unfold shrlimmBase
  refine eval_op1 hx ?_
  show some (Val.shrl x (.Vint (mkAmount64 n).a64_amount)) = _
  rw [mkAmount64_eq hn]

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
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_shllimmBase h1 L2, ?_⟩
      show Val.Lessdef (Val.shll (Val.shll v1 _) _) _
      rw [val_shll_shll v1 a0.a64_range L L2]; ld
    · exact ⟨_, eval_shllimmBase hx L, by ld⟩
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    show Val.Lessdef _ (Val.shll _ (.Vint (mkAmount64 n).a64_amount))
    rw [mkAmount64_eq L]; ld
  · obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    refine ⟨_, eval_op1 h1 rfl, ?_⟩
    show Val.Lessdef _ (Val.shll _ (.Vint (mkAmount64 n).a64_amount))
    rw [mkAmount64_eq L]; ld
  · rename_i s0 a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shll (Val.shll _ _) _)
        (Val.shll _ (.Vint (mkAmount64 (Integers.Int.add a0.a64_amount n)).a64_amount))
      rw [mkAmount64_eq L2, val_shll_shll _ a0.a64_range L L2]; ld
    · exact ⟨_, eval_shllimmBase hx L, by ld⟩
  · rename_i s0 a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shll (Val.shll _ _) _)
        (Val.shll _ (.Vint (mkAmount64 (Integers.Int.add a0.a64_amount n)).a64_amount))
      rw [mkAmount64_eq L2, val_shll_shll _ a0.a64_range L L2]; ld
    · exact ⟨_, eval_shllimmBase hx L, by ld⟩
  · rename_i x0 a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shll (evalExtend _ _ _) _)
        (evalExtend _ _ (mkAmount64 (Integers.Int.add a0.a64_amount n)))
      unfold evalExtend
      rw [mkAmount64_eq L2, val_shll_shll _ a0.a64_range L L2]; ld
    · exact ⟨_, eval_shllimmBase hx L, by ld⟩
  · exact ⟨_, eval_shllimmBase hx L, by ld⟩

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
  have hn' := toNat_lt_64_of_ltu L
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by rw [val_shrlu_long _ L]; ld⟩
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    have ha' := a64_toNat a0
    split
    · rename_i L2
      have hlt : n.toNat < a0.a64_amount.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shrlu (Val.shll _ _) _) (Val.shll (Val.zero_ext_l _ _)
        (.Vint (mkAmount64 (Integers.Int.sub a0.a64_amount n)).a64_amount))
      rw [mkAmount64_sub ha' (by omega), val_shrlu_shll_lt _ a0.a64_range L hlt, zw64_sub_toNat]; ld
    · rename_i L2
      have hge : a0.a64_amount.toNat ≤ n.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shrlu (Val.shll _ _) _) (Val.zero_ext_l _ (Val.shrlu _
        (.Vint (mkAmount64 (Integers.Int.sub n a0.a64_amount)).a64_amount)))
      rw [mkAmount64_sub hn' hge, val_shrlu_shll_ge _ a0.a64_range L hge, zw64_sub_toNat]; ld
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_shrluimmBase h1 L2, ?_⟩
      show Val.Lessdef (Val.shrlu (Val.shrlu v1 _) _) _
      rw [val_shrlu_shrlu v1 a0.a64_range L L2]; ld
    · exact ⟨_, eval_shrluimmBase hx L, by ld⟩
  · rename_i s t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i hs
      rw [unsigned_eq_toNat] at hs
      have hs' : (n.toNat : _root_.Int) < (s : _root_.Int) := hs
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shrlu (Val.zero_ext_l _ _) _)
        (Val.zero_ext_l _ (Val.shrlu _ (.Vint (mkAmount64 n).a64_amount)))
      rw [mkAmount64_eq L]
      have hsn : s.toNat = (s - Integers.Int.unsigned n).toNat + n.toNat := by
        rw [unsigned_eq_toNat]; omega
      cases v1 <;> try ld
      simp only [Val.zero_ext_l]
      rw [val_shrlu_long _ L, val_shrlu_long _ L, hsn, Integers.Int64.shru_zero_ext_nat]; ld
    · rename_i hs
      rw [unsigned_eq_toNat] at hs
      have hs' : ¬ (n.toNat : _root_.Int) < (s : _root_.Int) := hs
      refine ⟨_, eval_op0 rfl, ?_⟩
      show Val.Lessdef (Val.shrlu (Val.zero_ext_l _ _) _) _
      cases v1 <;> try ld
      simp only [Val.zero_ext_l]
      rw [val_shrlu_long _ L, Integers.Int64.shru_zero_ext_0_nat _ (by omega)]; ld
  · exact ⟨_, eval_shrluimmBase hx L, by ld⟩

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
  have hn' := toNat_lt_64_of_ltu L
  split
  · obtain rfl := inv_longconst hx
    exact ⟨_, eval_op0 rfl, by rw [val_shrl_long _ L]; ld⟩
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    have ha' := a64_toNat a0
    split
    · rename_i L2
      have hlt : n.toNat < a0.a64_amount.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shrl (Val.shll _ _) _) (Val.shll (Val.sign_ext_l _ _)
        (.Vint (mkAmount64 (Integers.Int.sub a0.a64_amount n)).a64_amount))
      rw [mkAmount64_sub ha' (by omega), val_shrl_shll_lt _ a0.a64_range L hlt, zw64_sub_toNat]; ld
    · rename_i L2
      have hge : a0.a64_amount.toNat ≤ n.toNat := by
        rw [Integers.Int.ltu_toNat] at L2; simpa using L2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shrl (Val.shll _ _) _) (Val.sign_ext_l _ (Val.shrl _
        (.Vint (mkAmount64 (Integers.Int.sub n a0.a64_amount)).a64_amount)))
      rw [mkAmount64_sub hn' hge, val_shrl_shll_ge _ a0.a64_range L hge, zw64_sub_toNat]; ld
  · rename_i a0 t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i L2
      refine ⟨_, eval_shrlimmBase h1 L2, ?_⟩
      show Val.Lessdef (Val.shrl (Val.shrl v1 _) _) _
      rw [val_shrl_shrl v1 a0.a64_range L L2]; ld
    · exact ⟨_, eval_shrlimmBase hx L, by ld⟩
  · rename_i s t1
    obtain ⟨v1, h1, ho⟩ := inv_op1 hx
    cases ho
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hs1, hs2⟩ := hs
      rw [unsigned_eq_toNat] at hs1
      have hs2' : s < 64 := hs2
      refine ⟨_, eval_op1 h1 rfl, ?_⟩
      show Val.Lessdef (Val.shrl (Val.sign_ext_l _ _) _)
        (Val.sign_ext_l _ (Val.shrl _ (.Vint (mkAmount64 n).a64_amount)))
      rw [mkAmount64_eq L]
      rw [unsigned_eq_toNat]
      have hsn : s.toNat = (s - (n.toNat : Z)).toNat + n.toNat := by zomega
      have hpos : 0 < (s - (n.toNat : Z)).toNat := by zomega
      have hlt : (s - (n.toNat : Z)).toNat + n.toNat < 64 := by zomega
      cases v1 <;> try ld
      simp only [Val.sign_ext_l]
      rw [val_shrl_long _ L, val_shrl_long _ L, hsn, Integers.Int64.shr_sign_ext_nat _ hpos hlt]; ld
    · exact ⟨_, eval_shrlimmBase hx L, by ld⟩
  · exact ⟨_, eval_shrlimmBase hx L, by ld⟩

/-! ### Multiplication -/

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
  · exact ⟨_, eval_op2 (eval_op0 rfl) hx rfl, by rw [Val.mull_commut]; ld⟩

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
    refine ⟨v'', hv'', Val.lessdef_trans ?_ (Val.lessdef_trans (Val.addl_lessdef hl' (.refl _)) hl'')⟩
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
end CC
