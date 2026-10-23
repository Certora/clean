/-
  Translation from Clight to Csharpminor: semantic preservation — port of
  `cfrontend/Cshmgenproof.v`, part 2 (section `CONSTRUCTORS`, lines
  649–1056): correctness of the remaining binary-operator constructors
  (`make_sub_correct` … `make_cmp_correct`), of `transl_unop`/`transl_binop`,
  and of the memory-access constructors (`make_load_correct`,
  `make_store_correct`, `make_normalization_correct`).

  The port is specialised to the configured target (`Archi.ptr64 = true`).
-/
import CCLib.cfrontend.CshmgenproofOps
import CCLib.cfrontend.CtypesTheory
import CCLib.cfrontend.Ctyping

namespace CC
namespace Cshmgen

open Cminor (UnaryOperation BinaryOperation)
open Cminor.UnaryOperation Cminor.BinaryOperation

/-- `omega` after unfolding the `Z` abbreviation. -/
local macro "zomega" : tactic => `(tactic| ((try dsimp only [CC.Z] at *) <;> omega))

theorem int64_repr_ne_zero_mone {s : Z} (h1 : 0 < s) (h2 : s ≤ Integers.Ptrofs.max_signed) :
    (Integers.Int64.repr s).eq Integers.Int64.zero = false ∧
      (Integers.Int64.repr s).eq Integers.Int64.mone = false := by
  simp [Integers.Ptrofs.max_signed, Integers.MI.max_signed, Integers.MI.half_modulus,
    Archi.ptrWordsize, Integers.MI.modulus] at h2
  simp [Integers.Int64.eq, Integers.MI.eq, Integers.Int64.repr, Integers.MI.repr,
    Integers.Int64.zero, Integers.Int64.mone]
  have hb : (BitVec.ofInt 64 s).toInt = s := by
    rw [BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> zomega
  constructor <;> intro h <;> rw [h] at hb <;>
    simp [Integers.MI.zero, Integers.MI.mone] at hb <;> zomega

section CONSTRUCTORS
variable {ge : Csharpminor.CGenv} {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {m : Mem}

local notation "EV" => Csharpminor.EvalExpr ge e le m

/-- `Cshmgenproof.make_sub_correct` -/
theorem make_sub_correct {ce : CompositeEnv} {a b c : Csharpminor.Expr} {tya tyb : Ty}
    {va vb v : Val} (hs : Cop.semSub ce va tya vb tyb m = some v)
    (hmk : makeSub ce a tya b tyb = .OK c) (ha : EV a va) (hb : EV b vb) : EV c v := by
  unfold makeSub at hmk; unfold Cop.semSub at hs
  cases hc : Cop.classifySub tya tyb <;> rw [hc] at hmk hs <;> simp only at hmk hs
  · simp only [res_bind_eq_OK] at hmk
    obtain ⟨sz, hsz, hc⟩ := hmk
    rw [transl_sizeof hsz] at hc
    simp only [Archi.ptr64, if_true] at hc
    cases hc
    cases va <;> cases vb <;> simp [Archi.ptr64] at hs <;> subst hs
    · exact make_binop_correct ha (make_binop_correct (make_longconst_correct _)
        (make_longofint_correct _ hb) rfl) rfl
    · refine make_binop_correct ha (make_binop_correct (make_longconst_correct _)
        (make_longofint_correct _ hb) rfl) ?_
      simp [Cminor.evalBinop, Val.subl, Val.mull, Archi.ptr64, of_int64_id, ptrofsOfInt_eq]
      rfl
  · simp only [res_bind_eq_OK] at hmk
    obtain ⟨sz, hsz, hc⟩ := hmk
    rw [transl_sizeof hsz] at hc
    simp only [Archi.ptr64, if_true] at hc
    cases hc
    cases va <;> cases vb <;> simp at hs
    obtain ⟨rfl, ⟨h1, h2⟩, rfl⟩ := hs
    refine make_binop_correct (make_binop_correct ha hb rfl) (make_longconst_correct _) ?_
    simp [Cminor.evalBinop, Val.subl, Archi.ptr64, Val.divls, Val.Vptrofs]
    have hz := int64_repr_ne_zero_mone h1 h2
    refine ⟨⟨hz.1, fun _ => hz.2⟩, ?_⟩
    rfl
  · simp only [res_bind_eq_OK] at hmk
    obtain ⟨sz, hsz, hc⟩ := hmk
    rw [transl_sizeof hsz] at hc
    simp only [Archi.ptr64, if_true] at hc
    cases hc
    cases va <;> cases vb <;> simp [Archi.ptr64] at hs <;> subst hs
    · exact make_binop_correct ha (make_binop_correct (make_longconst_correct _) hb rfl) rfl
    · refine make_binop_correct ha (make_binop_correct (make_longconst_correct _) hb rfl) ?_
      simp [Cminor.evalBinop, Val.subl, Val.mull, Archi.ptr64, of_int64_id]
      rfl
  · exact make_binarith_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hs hmk ha hb

/-- `Cshmgenproof.make_mul_correct` -/
theorem make_mul_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semMul va tya vb tyb m = some v) (hmk : makeMul a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v :=
  make_binarith_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hs hmk ha hb

/-- `Cshmgenproof.make_div_correct` -/
theorem make_div_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semDiv va tya vb tyb m = some v) (hmk : makeDiv a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v :=
  make_binarith_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hs hmk ha hb

/-- `Cshmgenproof.make_mod_correct` -/
theorem make_mod_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semMod va tya vb tyb m = some v) (hmk : makeMod a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v :=
  make_binarith_int_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) hs hmk ha hb

/-- `Cshmgenproof.make_and_correct` -/
theorem make_and_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semAnd va tya vb tyb m = some v) (hmk : makeAnd a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v :=
  make_binarith_int_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) hs hmk ha hb

/-- `Cshmgenproof.make_or_correct` -/
theorem make_or_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semOr va tya vb tyb m = some v) (hmk : makeOr a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v :=
  make_binarith_int_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) hs hmk ha hb

/-- `Cshmgenproof.make_xor_correct` -/
theorem make_xor_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semXor va tya vb tyb m = some v) (hmk : makeXor a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v :=
  make_binarith_int_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) hs hmk ha hb

end CONSTRUCTORS

/-- `Cshmgenproof.small_shift_amount_1` -/
theorem small_shift_amount_1 {i : Integers.Int64}
    (h : Integers.Int64.ltu i Integers.Int64.iwordsize = true) :
    Integers.Int.ltu (Integers.Int64.loword i) (Integers.Int.repr 64) = true ∧
      Integers.Int64.repr (Integers.Int.unsigned (Integers.Int64.loword i)) = i := by
  simp [Integers.Int64.ltu, Integers.MI.ltu, Integers.Int64.iwordsize, Integers.MI.iwordsize,
    BitVec.ult] at h
  have hn : i.toNat < 64 := by simpa using h
  refine ⟨?_, ?_⟩
  · simp [Integers.Int.ltu, Integers.MI.ltu, Integers.Int64.loword, Integers.Int.repr,
      Integers.MI.repr, BitVec.ult]
    omega
  · simp [Integers.Int64.repr, Integers.MI.repr, Integers.Int.unsigned, Integers.MI.unsigned,
      Integers.Int64.loword]
    apply BitVec.eq_of_toNat_eq
    simp
    omega

/-- `Cshmgenproof.small_shift_amount_2` -/
theorem small_shift_amount_2 {i : Integers.Int64}
    (h : Integers.Int64.ltu i (Integers.Int64.repr 32) = true) :
    Integers.Int.ltu (Integers.Int64.loword i) Integers.Int.iwordsize = true := by
  simp [Integers.Int64.ltu, Integers.MI.ltu, Integers.Int64.repr, Integers.MI.repr,
    BitVec.ult] at h
  simp [Integers.Int.ltu, Integers.MI.ltu, Integers.Int64.loword, Integers.Int.iwordsize,
    Integers.MI.iwordsize, BitVec.ult]
  omega

section CONSTRUCTORS2
variable {ge : Csharpminor.CGenv} {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {m : Mem}

local notation "EV" => Csharpminor.EvalExpr ge e le m

/-- `Cshmgenproof.make_shl_correct` -/
theorem make_shl_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semShl va tya vb tyb = some v) (hmk : makeShl a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v := by
  unfold makeShl at hmk; unfold Cop.semShl Cop.semShift at hs
  cases hc : Cop.classifyShift tya tyb <;> rw [hc] at hmk hs <;> cases hmk <;>
    cases va <;> cases vb <;> simp at hs <;> obtain ⟨h1, rfl⟩ := hs
  · exact make_binop_correct ha hb (by simp [Cminor.evalBinop, Val.shl, h1])
  · obtain ⟨A, B⟩ := small_shift_amount_1 h1
    refine make_binop_correct ha (make_unop_correct hb rfl) ?_
    simp only [Cminor.evalBinop, Val.shll, Val.loword]
    split
    · rw [B]
    · exact absurd A ‹_›
  · refine make_binop_correct ha (make_unop_correct hb rfl) ?_
    simp [Cminor.evalBinop, Val.shl, Val.loword, small_shift_amount_2 h1]
  · exact make_binop_correct ha hb (by simp only [Cminor.evalBinop, Val.shll]; split <;> trivial)

/-- `Cshmgenproof.make_shr_correct` -/
theorem make_shr_correct {a b c : Csharpminor.Expr} {tya tyb : Ty} {va vb v : Val}
    (hs : Cop.semShr va tya vb tyb = some v) (hmk : makeShr a tya b tyb = .OK c)
    (ha : EV a va) (hb : EV b vb) : EV c v := by
  unfold makeShr at hmk; unfold Cop.semShr Cop.semShift at hs
  cases hc : Cop.classifyShift tya tyb with
  | default => rw [hc] at hmk; cases hmk
  | ii sg | ll sg | il sg | li sg =>
    rw [hc] at hmk hs
    cases sg <;> cases hmk <;> cases va <;> cases vb <;> simp at hs <;> obtain ⟨h1, rfl⟩ := hs
    all_goals first
      | (refine make_binop_correct ha hb ?_
         simp [Cminor.evalBinop, Val.shr, Val.shru, h1]; done)
      | (obtain ⟨A, B⟩ := small_shift_amount_1 h1
         refine make_binop_correct ha (make_unop_correct hb rfl) ?_
         simp only [Cminor.evalBinop, Val.shrl, Val.shrlu, Val.loword]
         split
         · rw [B]
         · exact absurd A ‹_›)
      | (refine make_binop_correct ha (make_unop_correct hb rfl) ?_
         simp [Cminor.evalBinop, Val.shr, Val.shru, Val.loword, small_shift_amount_2 h1])
      | (refine make_binop_correct ha hb ?_
         simp only [Cminor.evalBinop, Val.shrl, Val.shrlu]; split <;> trivial)

/-- `Cshmgenproof.make_cmp_ptr_correct` -/
theorem make_cmp_ptr_correct {cmp : Comparison} {a b : Csharpminor.Expr} {va vb v : Val}
    (hs : Cop.cmpPtr m cmp va vb = some v) (ha : EV a va) (hb : EV b vb) :
    EV (makeCmpPtr cmp a b) v :=
  make_binop_correct ha hb (by simpa [Cop.cmpPtr, Archi.ptr64, Cminor.evalBinop, Val.cmplu] using hs)

theorem vptrofs_ptrofsOfInt (si : Signedness) (n : Integers.Int) :
    Val.Vptrofs (Cop.ptrofsOfInt si n) = .Vlong (Cop.castIntLong si n) := by
  simp [Val.Vptrofs, Archi.ptr64, ptrofsOfInt_eq, to_int64_id]

theorem vptrofs_of_int64 (n : Integers.Int64) :
    Val.Vptrofs (Integers.Ptrofs.of_int64 n) = .Vlong n := by
  simp [Val.Vptrofs, Archi.ptr64, of_int64_id, to_int64_id]

/-- `Cshmgenproof.make_cmp_correct` -/
theorem make_cmp_correct {cmp : Comparison} {a b c : Csharpminor.Expr} {tya tyb : Ty}
    {va vb v : Val} (hs : Cop.semCmp cmp va tya vb tyb m = some v)
    (hmk : makeCmp cmp a tya b tyb = .OK c) (ha : EV a va) (hb : EV b vb) : EV c v := by
  unfold makeCmp at hmk; unfold Cop.semCmp at hs
  cases hc : Cop.classifyCmp tya tyb <;> rw [hc] at hmk hs <;> simp only [Archi.ptr64, if_true] at hmk hs
  · cases hmk; exact make_cmp_ptr_correct hs ha hb
  · cases hmk
    cases vb <;> simp at hs
    rw [vptrofs_ptrofsOfInt] at hs
    exact make_cmp_ptr_correct hs ha (make_longofint_correct _ hb)
  · cases hmk
    cases va <;> simp at hs
    rw [vptrofs_ptrofsOfInt] at hs
    exact make_cmp_ptr_correct hs (make_longofint_correct _ ha) hb
  · cases hmk
    cases vb <;> simp at hs
    · rw [vptrofs_of_int64] at hs
      exact make_cmp_ptr_correct hs ha hb
    · exact make_cmp_ptr_correct hs ha hb
  · cases hmk
    cases va <;> simp at hs
    · rw [vptrofs_of_int64] at hs
      exact make_cmp_ptr_correct hs ha hb
    · exact make_cmp_ptr_correct hs ha hb
  · exact make_binarith_correct (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hs hmk ha hb

/-- `Cshmgenproof.transl_unop_correct` -/
theorem transl_unop_correct {op : Unop} {a c : Csharpminor.Expr} {tya : Ty} {va v : Val}
    (hmk : translUnop op a tya = .OK c) (hs : Cop.semUnaryOperation op va tya m = some v)
    (ha : EV a va) : EV c v := by
  cases op <;> simp only [translUnop, Cop.semUnaryOperation] at hmk hs
  · exact make_notbool_correct hs hmk ha
  · exact make_notint_correct hs hmk ha
  · exact make_neg_correct hs hmk ha
  · exact make_absfloat_correct hs hmk ha

/-- `Cshmgenproof.transl_binop_correct` -/
theorem transl_binop_correct {ce : CompositeEnv} {op : Binop} {a b c : Csharpminor.Expr}
    {tya tyb : Ty} {va vb v : Val} (hmk : translBinop ce op a tya b tyb = .OK c)
    (hs : Cop.semBinaryOperation ce op va tya vb tyb m = some v)
    (ha : EV a va) (hb : EV b vb) : EV c v := by
  cases op <;> simp only [translBinop, Cop.semBinaryOperation] at hmk hs
  · exact make_add_correct hs hmk ha hb
  · exact make_sub_correct hs hmk ha hb
  · exact make_mul_correct hs hmk ha hb
  · exact make_div_correct hs hmk ha hb
  · exact make_mod_correct hs hmk ha hb
  · exact make_and_correct hs hmk ha hb
  · exact make_or_correct hs hmk ha hb
  · exact make_xor_correct hs hmk ha hb
  · exact make_shl_correct hs hmk ha hb
  · exact make_shr_correct hs hmk ha hb
  all_goals exact make_cmp_correct hs hmk ha hb

end CONSTRUCTORS2

/-! ### Bitfields -/

theorem repr_toNat32 (k : Nat) (hk : k < 2 ^ 32) :
    (Integers.MI.repr (w := 32) (k : _root_.Int)).toNat = k := by
  simp [Integers.MI.repr]; omega

/-- `Int.unsigned_bitfield_extract_by_shifts` (for `Int.zwordsize = 32`). -/
theorem unsigned_bitfield_extract_by_shifts (pos width : Nat) (n : Integers.Int)
    (h1 : 0 < width) (h2 : pos + width ≤ 32) :
    Integers.Int.unsigned_bitfield_extract pos width n =
      Integers.Int.shru (Integers.Int.shl n (Integers.Int.repr ((32 - pos - width : Nat) : Z)))
        (Integers.Int.repr ((32 - width : Nat) : Z)) := by
  simp only [Integers.Int.unsigned_bitfield_extract, Integers.Int.shru, Integers.Int.shl,
    Integers.Int.repr, Integers.MI.unsigned_bitfield_extract, Integers.MI.zero_ext,
    Integers.MI.shru, Integers.MI.shl]
  rw [repr_toNat32 _ (by omega), repr_toNat32 _ (by omega), repr_toNat32 _ (by omega)]
  obtain ⟨a, ha⟩ : ∃ a, a = 32 - pos - width := ⟨_, rfl⟩
  rw [← ha, show 32 - width = pos + a by omega]
  have hall : (4294967295#32) = BitVec.allOnes 32 := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e : pos + a + i - a = pos + i := by omega
  by_cases hc : pos + a + i < 32
  · have hpi : pos + i < 32 := by omega
    split <;> simp [BitVec.getLsbD_ushiftRight, hc, e, BitVec.getLsbD_eq_getElem hpi,
      show ¬ (pos + a + i < a) by omega]
    intro _; rw [hall, BitVec.getElem_allOnes]
  · split
    · exfalso; omega
    · simp [BitVec.getLsbD_ushiftRight, hc]
      intro _; exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- `Int.signed_bitfield_extract_by_shifts` (for `Int.zwordsize = 32`). -/
theorem signed_bitfield_extract_by_shifts (pos width : Nat) (n : Integers.Int)
    (h1 : 0 < width) (h2 : pos + width ≤ 32) :
    Integers.Int.signed_bitfield_extract pos width n =
      Integers.Int.shr (Integers.Int.shl n (Integers.Int.repr ((32 - pos - width : Nat) : Z)))
        (Integers.Int.repr ((32 - width : Nat) : Z)) := by
  simp only [Integers.Int.signed_bitfield_extract, Integers.Int.shr, Integers.Int.shl,
    Integers.Int.repr, Integers.MI.signed_bitfield_extract, Integers.MI.sign_ext,
    Integers.MI.shr, Integers.MI.shru, Integers.MI.shl]
  rw [repr_toNat32 _ (by omega), repr_toNat32 _ (by omega), repr_toNat32 _ (by omega)]
  obtain ⟨a, ha⟩ : ∃ a, a = 32 - pos - width := ⟨_, rfl⟩
  rw [← ha, show 32 - width = pos + a by omega]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e : pos + a + i - a = pos + i := by omega
  split
  · omega
  by_cases hc : pos + a + i < 32
  · have hpi : pos + i < 32 := by omega
    split <;> simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_sshiftRight, e, hc,
      BitVec.getLsbD_eq_getElem hpi, show ¬ 32 ≤ i by omega, show ¬ (pos + a + i < a) by omega,
      show ¬ (pos + a + i < pos + a) by omega]
  · split
    · exfalso; omega
    · simp [BitVec.getLsbD_sshiftRight, hc, show ¬ 32 ≤ i by omega,
        show pos + a < 32 by omega, show ¬ pos + a < pos by omega]

theorem repr_two_pow_sub_one_getLsbD (width j : Nat) :
    (Integers.MI.repr (w := 32) ((2 : _root_.Int) ^ width - 1)).getLsbD j =
      (decide (j < 32) && decide (j < width)) := by
  have : ((2 : _root_.Int) ^ width - 1) = ((2 ^ width - 1 : Nat) : _root_.Int) := by
    have : 1 ≤ 2 ^ width := Nat.one_le_two_pow
    rw [Int.ofNat_sub this]; simp
  simp only [Integers.MI.repr, this, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]

/-- `Int.bitfield_insert_alternative` (for `Int.zwordsize = 32`). -/
theorem bitfield_insert_alternative (pos width : Nat) (n p : Integers.Int)
    (h : pos + width ≤ 32) :
    Integers.Int.bitfield_insert pos width n p =
      Integers.Int.or
        (Integers.Int.and (Integers.Int.shl p (Integers.Int.repr (pos : Z)))
          (Integers.Int.shl (Integers.Int.repr ((2 : Z) ^ width - 1)) (Integers.Int.repr (pos : Z))))
        (Integers.Int.and n (Integers.Int.not
          (Integers.Int.shl (Integers.Int.repr ((2 : Z) ^ width - 1))
            (Integers.Int.repr (pos : Z))))) := by
  simp only [Integers.Int.bitfield_insert, Integers.MI.bitfield_insert, Integers.Int.or,
    Integers.Int.and, Integers.Int.shl, Integers.Int.not, Integers.Int.repr]
  congr 1
  simp only [Integers.MI.shl, Integers.MI.and, Integers.MI.zero_ext]
  rw [repr_toNat32 _ (by omega)]
  have hall : (4294967295#32) = BitVec.allOnes 32 := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hw : width ≥ 32
  · simp [hw, BitVec.getLsbD_shiftLeft, repr_two_pow_sub_one_getLsbD]
    intros; omega
  · simp [hw, BitVec.getLsbD_shiftLeft, repr_two_pow_sub_one_getLsbD, BitVec.getLsbD_ushiftRight]
    rw [hall, BitVec.getLsbD_allOnes]
    by_cases h1 : i < pos <;> simp [h1, hi, show i - pos < 32 by omega,
      show (32 - width + (i - pos) < 32) ↔ (i - pos < width) by omega]

/-- `Cshmgenproof.int_ltu_true` -/
theorem int_ltu_true {x : Z} (h0 : 0 ≤ x) (h1 : x < 32) :
    Integers.Int.ltu (Integers.Int.repr x) Integers.Int.iwordsize = true := by
  simp only [Integers.Int.ltu, Integers.MI.ltu, Integers.Int.repr, Integers.MI.repr,
    Integers.Int.iwordsize, Integers.MI.iwordsize, BitVec.ult]
  simp only [decide_eq_true_eq, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  dsimp only [CC.Z] at *
  omega

section MEMORY
variable {ge : Csharpminor.CGenv} {e : Csharpminor.Env} {le : Csharpminor.TempEnv} {m : Mem}

local notation "EV" => Csharpminor.EvalExpr ge e le m

/-- `Cshmgenproof.make_load_correct` -/
theorem make_load_correct {addr code : Csharpminor.Expr} {ty : Ty} {bf : Bitfield} {b : Block}
    {ofs : Integers.Ptrofs} {v : Val} (hmk : makeLoad addr ty bf = .OK code)
    (hev : EV addr (.Vptr b ofs)) (hd : DerefLoc ty m b ofs bf v) : EV code v := by
  cases hd with
  | value chunk v hm hl =>
    simp only [makeLoad, hm] at hmk; cases hmk; exact .Eload _ _ _ _ hev hl
  | reference hm => simp only [makeLoad, hm] at hmk; cases hmk; exact hev
  | copy hm => simp only [makeLoad, hm] at hmk; cases hmk; exact hev
  | bitfield sz sg pos width v hlb =>
    cases hlb with
    | intro sz sg1 attr sg pos width m addr' c hp hw hw1 hpw _ hl =>
    simp only [makeLoad, makeExtractBitfield] at hmk
    rw [if_pos ⟨hp, hw, hpw⟩] at hmk
    cases hmk
    have hc : Cop.bitsizeCarrier sz ≤ 32 := by cases sz <;> decide
    have hfb : Cop.firstBit sz pos width = pos := by simp [Cop.firstBit, Archi.big_endian]
    have E1 : EV (.Eload (Cop.chunkForCarrier sz) addr) (.Vint c) := .Eload _ _ _ _ hev hl
    have E2 : EV (.Ebinop Oshl (.Eload (Cop.chunkForCarrier sz) addr)
        (makeIntconst (Integers.Int.repr (Integers.Int.zwordsize - Cop.firstBit sz pos width - width))))
        (.Vint (Integers.Int.shl c
          (Integers.Int.repr (Integers.Int.zwordsize - Cop.firstBit sz pos width - width)))) := by
      refine make_binop_correct E1 (make_intconst_correct _) ?_
      rw [hfb]
      simp only [Cminor.evalBinop, Val.shl, Integers.Int.zwordsize]
      rw [int_ltu_true (by dsimp only [CC.Z] at *; omega) (by dsimp only [CC.Z] at *; omega)]
      rfl
    refine make_binop_correct E2 (make_intconst_correct _) ?_
    have hP : ((32 - pos.toNat - width.toNat : Nat) : Z) = Integers.Int.zwordsize - Cop.firstBit sz pos width - width := by
      rw [hfb]; simp only [Integers.Int.zwordsize]; dsimp only [CC.Z] at *; omega
    have hW : ((32 - width.toNat : Nat) : Z) = Integers.Int.zwordsize - width := by
      simp only [Integers.Int.zwordsize]; dsimp only [CC.Z] at *; omega
    have hlt := int_ltu_true (x := Integers.Int.zwordsize - width)
      (by simp only [Integers.Int.zwordsize]; dsimp only [CC.Z] at *; omega)
      (by simp only [Integers.Int.zwordsize]; dsimp only [CC.Z] at *; omega)
    simp only [Cop.bitfieldExtract, hfb] at *
    have h1 : 0 < width.toNat := by dsimp only [CC.Z] at *; omega
    have h2 : pos.toNat + width.toNat ≤ 32 := by dsimp only [CC.Z] at *; omega
    split
    · next hcond =>
      simp only [Cminor.evalBinop, Val.shru, hlt, if_true]
      rw [unsigned_bitfield_extract_by_shifts _ _ _ h1 h2, hP, hW]
    · next hcond =>
      simp only [Cminor.evalBinop, Val.shr, hlt, if_true]
      rw [signed_bitfield_extract_by_shifts _ _ _ h1 h2, hP, hW]

/-- `Cshmgenproof.make_store_bitfield_correct` -/
theorem make_store_bitfield_correct {f : Csharpminor.Function} {sz : IntSize} {sg : Signedness}
    {pos width : Z} {dst src : Csharpminor.Expr} {ce : CompositeEnv} {ty : Ty}
    {k : Csharpminor.Cont} {b : Block} {ofs : Integers.Ptrofs} {v : Val} {m' : Mem}
    {s : Csharpminor.Stmt}
    (hdst : EV dst (.Vptr b ofs)) (hsrc : EV src v)
    (hasg : AssignLoc ce ty m b ofs (.Bits sz sg pos width) v m')
    (hmk : makeStoreBitfield sz sg pos width dst src = .OK s) :
    Csharpminor.Step ge (.State f s k e le m) E0 (.State f .Sskip k e le m') := by
  cases hasg with
  | bitfield _ _ _ _ _ _ _ hsb =>
  cases hsb with
  | intro _ sg1 attr _ _ _ _ _ c n _ hp hw hw1 hpw _ hl hst =>
  simp only [makeStoreBitfield] at hmk
  rw [if_pos ⟨hp, hw, hpw⟩] at hmk
  cases hmk
  have hc : Cop.bitsizeCarrier sz ≤ 32 := by cases sz <;> decide
  have hfb : Cop.firstBit sz pos width = pos := by simp [Cop.firstBit, Archi.big_endian]
  have h2 : pos.toNat + width.toNat ≤ 32 := by dsimp only [CC.Z] at *; omega
  have hP : ((pos.toNat : Nat) : Z) = pos := by dsimp only [CC.Z] at *; omega
  have hT : twoP width = (2 : Z) ^ width.toNat := by
    simp only [twoP]; rw [if_pos (by dsimp only [CC.Z] at *; omega)]
  refine .store _ _ _ _ _ _ _ _ _ _ _ hdst ?_ hst
  rw [hfb, bitfield_insert_alternative _ _ _ _ h2, hP, hT]
  have E1 : EV (.Ebinop Oshl src (makeIntconst (Integers.Int.repr pos)))
      (.Vint (Integers.Int.shl n (Integers.Int.repr pos))) := by
    refine make_binop_correct hsrc (make_intconst_correct _) ?_
    simp only [Cminor.evalBinop, Val.shl]
    rw [int_ltu_true (by dsimp only [CC.Z] at *; omega) (by dsimp only [CC.Z] at *; omega)]
    rfl
  exact make_binop_correct (make_binop_correct E1 (make_intconst_correct _) rfl)
    (make_binop_correct (.Eload _ _ _ _ hdst hl) (make_intconst_correct _) rfl) rfl

/-- `Cshmgenproof.make_memcpy_correct` -/
theorem make_memcpy_correct {f : Csharpminor.Function} {dst src : Csharpminor.Expr}
    {ce : CompositeEnv} (hwf : ce.WF) {ty : Ty}
    {k : Csharpminor.Cont} {b : Block} {ofs : Integers.Ptrofs} {v : Val} {m' : Mem}
    {s : Csharpminor.Stmt}
    (hdst : EV dst (.Vptr b ofs)) (hsrc : EV src v)
    (hasg : AssignLoc ce ty m b ofs .Full v m') (hacc : accessMode ty = .By_copy)
    (hmk : makeMemcpy ce dst src ty = .OK s) :
    Csharpminor.Step ge (.State f s k e le m) E0 (.State f .Sskip k e le m') := by
  cases hasg with
  | value _ chunk _ hm _ => rw [hm] at hacc; cases hacc
  | copy b' ofs' bytes _ _ h1 h2 h3 h4 h5 =>
  simp only [makeMemcpy, res_bind_eq_OK] at hmk
  obtain ⟨sz, hsz, hc⟩ := hmk
  rw [transl_sizeof hsz] at hc
  cases hc
  have := Csharpminor.Step.builtin (ge := ge) f none
    (.EF_memcpy (CC.sizeof ce ty) (alignofBlockcopy ce ty)) [dst, src] k e le m
    [.Vptr b ofs, .Vptr b' ofs'] E0 .Vundef m'
    (.cons _ _ _ _ hdst (.cons _ _ _ _ hsrc .nil))
    (ExtcallMemcpySem.intro _ _ _ _ _ _ _ _ (alignofBlockcopy_1248 hwf ty) (sizeof_pos hwf ty)
      (Int.emod_eq_zero_of_dvd (sizeof_alignof_blockcopy_compat hwf ty))
      h1 h2 h3 h4 h5)
  exact this

/-- `Cshmgenproof.make_store_correct` -/
theorem make_store_correct {ce : CompositeEnv} (hwf : ce.WF) {addr rhs : Csharpminor.Expr}
    {ty : Ty} {bf : Bitfield} {code : Csharpminor.Stmt} {b : Block} {ofs : Integers.Ptrofs}
    {v : Val} {m' : Mem} {f : Csharpminor.Function} {k : Csharpminor.Cont}
    (hmk : makeStore ce addr ty bf rhs = .OK code) (hev1 : EV addr (.Vptr b ofs))
    (hev2 : EV rhs v) (hasg : AssignLoc ce ty m b ofs bf v m') :
    Csharpminor.Step ge (.State f code k e le m) E0 (.State f .Sskip k e le m') := by
  have hasg' := hasg
  cases hasg with
  | value _ chunk _ hm hs =>
    simp only [makeStore, hm] at hmk; cases hmk
    exact .store _ _ _ _ _ _ _ _ _ _ _ hev1 hev2 hs
  | copy b' ofs' bytes _ hm =>
    simp only [makeStore, hm] at hmk
    exact make_memcpy_correct hwf hev1 hev2 hasg' hm hmk
  | bitfield sz sg pos width _ _ _ _ =>
    simp only [makeStore] at hmk
    exact make_store_bitfield_correct hev1 hev2 hasg' hmk

/-- `Cshmgenproof.make_normalization_correct` -/
theorem make_normalization_correct {a : Csharpminor.Expr} {v : Val} {t : Ty}
    (hev : EV a v) (hwt : Ctyping.WtVal v t) : EV (makeNormalization t a) v := by
  cases t with
  | Tint sz sg attr =>
    cases hwt with
    | int n _ _ _ hwi =>
      cases sz <;> cases sg <;> simp only [makeNormalization, Ctyping.WtInt] at hwi ⊢ <;>
        first
          | exact hev
          | (refine make_unop_correct hev ?_
             simp [Cminor.evalUnop, Val.zeroExt, Val.signExt, hwi]; done)
          | (refine make_unop_correct hev ?_
             rcases hwi with rfl | rfl <;> simp [Cminor.evalUnop, Val.zeroExt] <;> decide)
    | ptr_int _ _ _ _ h => simp [Archi.ptr64] at h
    | undef =>
      cases sz <;> cases sg <;> simp only [makeNormalization] <;>
        first
          | exact hev
          | exact make_unop_correct hev (by simp [Cminor.evalUnop, Val.zeroExt, Val.signExt])
  | _ => exact hev

end MEMORY

end Cshmgen
end CC
