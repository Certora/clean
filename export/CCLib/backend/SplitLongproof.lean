/-
  Correctness of instruction selection for 64-bit integer operations on
  32-bit targets — port of `backend/SplitLongproof.v`.

  As `CCLib.backend.SplitLong`, the proofs are carried out over the aarch64
  operators and the aarch64 `SelectOp` correctness lemmas
  (`CCLib.aarch64.SelectOpproof*`); `UnarySound` / `BinarySound` are Rocq's
  `unary_constructor_sound` / `binary_constructor_sound`.

  Ported: the `Int64` word lemmas `ofwords_recompose`, `hi_ofwords`,
  `lo_ofwords`, `decompose_and`, `decompose_or`, `decompose_xor` (and the
  negation case); `helper_declared`, `helper_functions_declared`,
  `eval_helper`, `eval_helper_1`, `eval_helper_2`; `eval_splitlong`,
  `eval_splitlong_strict`, `eval_splitlong2`, `eval_splitlong2_strict`,
  `is_longconst_sound`, `is_longconst_zero_sound`, `eval_lowlong`,
  `eval_highlong`, `eval_longconst`, `eval_intoflong`, `eval_longofintu`,
  `eval_longofint`, `eval_negl`, `eval_notl`, `eval_longoffloat`,
  `eval_longuoffloat`, `eval_longofsingle`, `eval_longuofsingle`, `eval_floatoflong`, `eval_floatoflongu`,
  `eval_singleoflong`, `eval_singleoflongu`, `eval_andl`, `eval_orl`,
  `eval_xorl`, `is_intconst_sound`, `eval_mullhu`, `eval_mullhs`,
  `eval_divlu_base`, `eval_modlu_base`, `eval_divls_base`,
  `eval_modls_base`.

  The rest of the file (shifts, `addl`/`subl`, multiplication, `shrxlimm`,
  the comparisons and `select_long`) is in `CCLib.backend.SplitLongproof2`.

  `eval_longofsingle` / `eval_longuofsingle` use `Float32.to_long_double` /
  `Float32.to_longu_double` from `CCLib.lib.FloatsConv`.

  The built-ins `__builtin_negl`, `__compcert_i64_umulh` and
  `__compcert_i64_smulh` return `Vundef` on arguments of the wrong type, as
  in Rocq (`mkbuiltin_n1t` / `mkbuiltin_n2t`), so `eval_negl`, `eval_mullhu`
  and `eval_mullhs` have their Rocq statements.
-/
import CCLib.backend.SplitLong
import CCLib.aarch64.SelectOpproof3
import CCLib.lib.FloatsConv

namespace CC

namespace Integers.Int64

/-- `Int64.ofwords_recompose` -/
theorem ofwords_recompose (x : Int64) : ofwords (hiword x) (loword x) = x := by
  unfold ofwords hiword loword
  ext i hi
  simp
  by_cases h : i < 32
  · simp [h, BitVec.getLsbD_eq_getElem hi]
  · have e : 32 + (i - 32) = i := by omega
    have : i - 32 < 32 := by omega
    simp [h, e, this, BitVec.getLsbD_eq_getElem hi]

/-- `Int64.hi_ofwords` -/
theorem hi_ofwords (h l : Int) : hiword (ofwords h l) = h := by
  unfold ofwords hiword
  ext i hi
  simp
  have h1 : 32 + i < 64 := by omega
  have h2 : ¬ 32 + i < 32 := by omega
  have h3 : i < 64 := by omega
  simp [h1, h2, h3, BitVec.getLsbD_eq_getElem hi]

/-- `Int64.lo_ofwords` -/
theorem lo_ofwords (h l : Int) : loword (ofwords h l) = l := by
  unfold ofwords loword
  ext i hi
  simp

/-- Bits of `Int64.ofwords` (`Int64.bits_ofwords`). -/
theorem ofwords_bit (h l : Integers.Int) (i : Nat) (hi : i < 64) :
    (ofwords h l).getLsbD i = if i < 32 then l.getLsbD i else h.getLsbD (i - 32) := by
  simp only [ofwords]
  by_cases hh : i < 32
  · simp [hh]; intro; omega
  · have : 32 ≤ i := by omega
    simp [hh, hi, BitVec.getLsbD_of_ge l i this]
/-- `Int64.decompose_and` -/
theorem decompose_and (h1 l1 h2 l2 : Integers.Int) :
    and (ofwords h1 l1) (ofwords h2 l2) = ofwords (Int.and h1 h2) (Int.and l1 l2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [and, Int.and, MI.and, BitVec.getLsbD_and, ofwords_bit _ _ i hi]
  split <;> rfl
/-- `Int64.decompose_or` -/
theorem decompose_or (h1 l1 h2 l2 : Integers.Int) :
    or (ofwords h1 l1) (ofwords h2 l2) = ofwords (Int.or h1 h2) (Int.or l1 l2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [or, Int.or, MI.or, BitVec.getLsbD_or, ofwords_bit _ _ i hi]
  split <;> rfl
/-- `Int64.decompose_xor` -/
theorem decompose_xor (h1 l1 h2 l2 : Integers.Int) :
    xor (ofwords h1 l1) (ofwords h2 l2) = ofwords (Int.xor h1 h2) (Int.xor l1 l2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [xor, Int.xor, MI.xor, BitVec.getLsbD_xor, ofwords_bit _ _ i hi]
  split <;> rfl
/-- `Int64.decompose_xor` with `-1`, i.e. bitwise negation. -/
theorem decompose_not (h1 l1 : Integers.Int) :
    not (ofwords h1 l1) = ofwords (Int.not h1) (Int.not l1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [not, Int.not, MI.not, BitVec.getLsbD_not, ofwords_bit _ _ i hi]
  split <;> simp [hi] <;> omega
/-- Zero extension as `ofwords` (used by `eval_longofintu`). -/
theorem longofintu_ofwords (x : Integers.Int) : repr (Int.unsigned x) = ofwords Int.zero x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [ofwords_bit _ _ i hi]
  simp only [repr, Int.unsigned, MI.unsigned, MI.repr, Int.zero, MI.zero]
  split
  · simp [hi]
  · have : 32 ≤ i := by omega
    simp [hi, BitVec.getLsbD_of_ge x i this]
/-- Sign extension as `ofwords` (used by `eval_longofint`). -/
theorem longofint_ofwords (x : Integers.Int) :
    repr (Int.signed x) = ofwords (Int.shr x (Int.repr 31)) x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [ofwords_bit _ _ i hi]
  simp only [repr, Int.signed, MI.signed, MI.repr, Int.shr, MI.shr]
  rw [← BitVec.signExtend]
  have h31 : (Int.repr 31).toNat = 31 := by decide
  simp only [BitVec.getLsbD_sshiftRight, h31]
  rw [BitVec.getLsbD_signExtend]
  by_cases hh : i < 32
  · simp [hh, hi]
  · have h1 : ¬ 32 ≤ i - 32 := by omega
    simp only [hh, h1, hi, if_false, decide_false, decide_true, Bool.not_false, Bool.true_and]
    by_cases h2 : 31 + (i - 32) < 32
    · rw [if_pos h2]
      have : 31 + (i - 32) = 31 := by omega
      rw [this, BitVec.msb_eq_getLsbD_last]
    · rw [if_neg h2]

end Integers.Int64

namespace SplitLongproof

open Op CminorSel SelectOp SplitLong SelectOpproof

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-! ## Properties of the helper functions -/

/-- `helper_declared p id name sg`: the global `id` of `p` is the runtime
function `name` with signature `sg`. -/
def helper_declared {F V : Type} (p : ASTProgram (ASTFundef F) V) (id : Ident) (name : String)
    (sg : Signature) : Prop :=
  p.defmap.get id = some (GlobDef.Gfun (.External (.EF_runtime name sg)))

/-- `helper_functions_declared p hf`: all the helper functions of `hf` are
declared in `p` with their expected names and signatures. -/
def helper_functions_declared {F V : Type} (p : ASTProgram (ASTFundef F) V)
    (hf : HelperFunctions) : Prop :=
  helper_declared p hf.i64_dtos "__compcert_i64_dtos" sigFL ∧
  helper_declared p hf.i64_dtou "__compcert_i64_dtou" sigFL ∧
  helper_declared p hf.i64_stod "__compcert_i64_stod" sigLF ∧
  helper_declared p hf.i64_utod "__compcert_i64_utod" sigLF ∧
  helper_declared p hf.i64_stof "__compcert_i64_stof" sigLS ∧
  helper_declared p hf.i64_utof "__compcert_i64_utof" sigLS ∧
  helper_declared p hf.i64_sdiv "__compcert_i64_sdiv" sigLLL ∧
  helper_declared p hf.i64_udiv "__compcert_i64_udiv" sigLLL ∧
  helper_declared p hf.i64_smod "__compcert_i64_smod" sigLLL ∧
  helper_declared p hf.i64_umod "__compcert_i64_umod" sigLLL ∧
  helper_declared p hf.i64_shl "__compcert_i64_shl" sigLIL ∧
  helper_declared p hf.i64_shr "__compcert_i64_shr" sigLIL ∧
  helper_declared p hf.i64_sar "__compcert_i64_sar" sigLIL ∧
  helper_declared p hf.i64_umulh "__compcert_i64_umulh" sigLLL ∧
  helper_declared p hf.i64_smulh "__compcert_i64_smulh" sigLLL

/-! ## Correctness of the instruction selection functions for 64-bit operators -/

section CMCONSTR

variable {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem}

theorem eval_hiword_letvar0 {le : Letenv} {v : Val} :
    CminorSel.EvalExpr ge sp e m (v :: le) (.Eop .Ohighlong (.Eletvar 0 ::: .Enil)) (Val.hiword v) :=
  eval_op1 (.Eletvar _ _ _ rfl) rfl

theorem eval_loword_letvar0 {le : Letenv} {v : Val} :
    CminorSel.EvalExpr ge sp e m (v :: le) (.Eop .Olowlong (.Eletvar 0 ::: .Enil)) (Val.loword v) :=
  eval_op1 (.Eletvar _ _ _ rfl) rfl

theorem eval_hiword_letvar1 {le : Letenv} {v w : Val} :
    CminorSel.EvalExpr ge sp e m (w :: v :: le) (.Eop .Ohighlong (.Eletvar 1 ::: .Enil))
      (Val.hiword v) :=
  eval_op1 (.Eletvar _ _ _ rfl) rfl

theorem eval_loword_letvar1 {le : Letenv} {v w : Val} :
    CminorSel.EvalExpr ge sp e m (w :: v :: le) (.Eop .Olowlong (.Eletvar 1 ::: .Enil))
      (Val.loword v) :=
  eval_op1 (.Eletvar _ _ _ rfl) rfl

theorem longofwords_inv {v1 v2 : Val} {n : Integers.Int64} (h : Val.longofwords v1 v2 = .Vlong n) :
    v1 = .Vint (Integers.Int64.hiword n) ∧ v2 = .Vint (Integers.Int64.loword n) := by
  cases v1 <;> cases v2 <;> simp [Val.longofwords] at h
  subst h
  exact ⟨by rw [Integers.Int64.hi_ofwords], by rw [Integers.Int64.lo_ofwords]⟩

/-- `eval_splitlong` -/
theorem eval_splitlong {le : Letenv} {a : SplitLong.Expr} {f : SplitLong.Expr → SplitLong.Expr → SplitLong.Expr}
    {v : Val} {sem : Val → Val}
    (EXEC : ∀ le a b x y, CminorSel.EvalExpr ge sp e m le a x → CminorSel.EvalExpr ge sp e m le b y →
      ∃ v, CminorSel.EvalExpr ge sp e m le (f a b) v ∧
        ∀ p q, x = .Vint p → y = .Vint q → v = sem (.Vlong (Integers.Int64.ofwords p q)))
    (UNDEF : match v with | .Vlong _ => True | _ => sem v = .Vundef)
    (ha : CminorSel.EvalExpr ge sp e m le a v) :
    ∃ v', CminorSel.EvalExpr ge sp e m le (splitlong a f) v' ∧ Val.Lessdef (sem v) v' := by
  unfold splitlong
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    obtain ⟨v', A, B⟩ := EXEC le _ _ v1 v2 h1 h2
    refine ⟨v', A, ?_⟩
    cases ho
    cases v1 <;> cases v2 <;> simp only [Val.longofwords] at UNDEF ⊢ <;>
      first | (rw [UNDEF]; exact .undef _) | (rw [B _ _ rfl rfl]; exact .refl _)
  · obtain ⟨v', A, B⟩ := EXEC (v :: le) _ _ _ _ eval_hiword_letvar0 eval_loword_letvar0
    refine ⟨v', .Elet _ _ _ _ _ ha A, ?_⟩
    cases v with
    | Vlong n =>
      rw [B _ _ rfl rfl, Integers.Int64.ofwords_recompose]; exact .refl _
    | _ => rw [UNDEF]; exact .undef _

/-- `eval_splitlong_strict` -/
theorem eval_splitlong_strict {le : Letenv} {a : SplitLong.Expr}
    {f : SplitLong.Expr → SplitLong.Expr → SplitLong.Expr} {va : Integers.Int64} {v : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong va))
    (EXEC : ∀ le a1 a2,
      CminorSel.EvalExpr ge sp e m le a1 (.Vint (Integers.Int64.hiword va)) →
      CminorSel.EvalExpr ge sp e m le a2 (.Vint (Integers.Int64.loword va)) →
      CminorSel.EvalExpr ge sp e m le (f a1 a2) v) :
    CminorSel.EvalExpr ge sp e m le (splitlong a f) v := by
  unfold splitlong
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    have ho : Val.longofwords v1 v2 = .Vlong va := Option.some.inj ho
    obtain ⟨rfl, rfl⟩ := longofwords_inv ho
    exact EXEC _ _ _ h1 h2
  · exact .Elet _ _ _ _ _ ha (EXEC _ _ _ eval_hiword_letvar0 eval_loword_letvar0)

/-- `eval_splitlong2` -/
theorem eval_splitlong2 {le : Letenv} {a b : SplitLong.Expr}
    {f : SplitLong.Expr → SplitLong.Expr → SplitLong.Expr → SplitLong.Expr → SplitLong.Expr}
    {va vb : Val} {sem : Val → Val → Val}
    (EXEC : ∀ le a1 a2 b1 b2 x1 x2 y1 y2,
      CminorSel.EvalExpr ge sp e m le a1 x1 → CminorSel.EvalExpr ge sp e m le a2 x2 →
      CminorSel.EvalExpr ge sp e m le b1 y1 → CminorSel.EvalExpr ge sp e m le b2 y2 →
      ∃ v, CminorSel.EvalExpr ge sp e m le (f a1 a2 b1 b2) v ∧
        ∀ p1 p2 q1 q2, x1 = .Vint p1 → x2 = .Vint p2 → y1 = .Vint q1 → y2 = .Vint q2 →
          v = sem (.Vlong (Integers.Int64.ofwords p1 p2)) (.Vlong (Integers.Int64.ofwords q1 q2)))
    (UNDEF : match va, vb with | .Vlong _, .Vlong _ => True | _, _ => sem va vb = .Vundef)
    (ha : CminorSel.EvalExpr ge sp e m le a va) (hb : CminorSel.EvalExpr ge sp e m le b vb) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (splitlong2 a b f) v ∧ Val.Lessdef (sem va vb) v := by
  unfold splitlong2
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    obtain ⟨v3, v4, h3, h4, ho'⟩ := inv_op2 hb
    obtain ⟨v, A, B⟩ := EXEC le _ _ _ _ _ _ _ _ h1 h2 h3 h4
    refine ⟨v, A, ?_⟩
    cases ho; cases ho'
    cases v1 <;> cases v2 <;> cases v3 <;> cases v4 <;> simp only [Val.longofwords] at UNDEF ⊢ <;>
      first | (rw [UNDEF]; exact .undef _) | (rw [B _ _ _ _ rfl rfl rfl rfl]; exact .refl _)
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    obtain ⟨v, A, B⟩ := EXEC (vb :: le) _ _ _ _ _ _ _ _ (eval_lift h1) (eval_lift h2)
      eval_hiword_letvar0 eval_loword_letvar0
    refine ⟨v, .Elet _ _ _ _ _ hb A, ?_⟩
    cases ho
    cases v1 <;> cases v2 <;> simp only [Val.longofwords] at UNDEF ⊢ <;>
      first
      | (rw [UNDEF]; exact .undef _)
      | (cases vb with
         | Vlong n => rw [B _ _ _ _ rfl rfl rfl rfl, Integers.Int64.ofwords_recompose]; exact .refl _
         | _ => rw [UNDEF]; exact .undef _)
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hb
    obtain ⟨v, A, B⟩ := EXEC (va :: le) _ _ _ _ _ _ _ _ eval_hiword_letvar0 eval_loword_letvar0
      (eval_lift h1) (eval_lift h2)
    refine ⟨v, .Elet _ _ _ _ _ ha A, ?_⟩
    cases ho
    cases va with
    | Vlong n =>
      cases v1 <;> cases v2 <;> simp only [Val.longofwords] at UNDEF ⊢ <;>
        first
        | (rw [UNDEF]; exact .undef _)
        | (rw [B _ _ _ _ rfl rfl rfl rfl, Integers.Int64.ofwords_recompose]; exact .refl _)
    | _ => rw [UNDEF]; exact .undef _
  · obtain ⟨v, A, B⟩ := EXEC (vb :: va :: le) _ _ _ _ _ _ _ _ eval_hiword_letvar1 eval_loword_letvar1
      eval_hiword_letvar0 eval_loword_letvar0
    refine ⟨v, .Elet _ _ _ _ _ ha (.Elet _ _ _ _ _ (eval_lift hb) A), ?_⟩
    cases va <;> cases vb <;>
      first
      | (rw [B _ _ _ _ rfl rfl rfl rfl, Integers.Int64.ofwords_recompose,
          Integers.Int64.ofwords_recompose]; exact .refl _)
      | (rw [UNDEF]; exact .undef _)

/-- `eval_splitlong2_strict` -/
theorem eval_splitlong2_strict {le : Letenv} {a b : SplitLong.Expr}
    {f : SplitLong.Expr → SplitLong.Expr → SplitLong.Expr → SplitLong.Expr → SplitLong.Expr}
    {va vb : Integers.Int64} {v : Val}
    (ha : CminorSel.EvalExpr ge sp e m le a (.Vlong va))
    (hb : CminorSel.EvalExpr ge sp e m le b (.Vlong vb))
    (EXEC : ∀ le a1 a2 b1 b2,
      CminorSel.EvalExpr ge sp e m le a1 (.Vint (Integers.Int64.hiword va)) →
      CminorSel.EvalExpr ge sp e m le a2 (.Vint (Integers.Int64.loword va)) →
      CminorSel.EvalExpr ge sp e m le b1 (.Vint (Integers.Int64.hiword vb)) →
      CminorSel.EvalExpr ge sp e m le b2 (.Vint (Integers.Int64.loword vb)) →
      CminorSel.EvalExpr ge sp e m le (f a1 a2 b1 b2) v) :
    CminorSel.EvalExpr ge sp e m le (splitlong2 a b f) v := by
  unfold splitlong2
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    obtain ⟨v3, v4, h3, h4, ho'⟩ := inv_op2 hb
    obtain ⟨rfl, rfl⟩ := longofwords_inv (Option.some.inj ho)
    obtain ⟨rfl, rfl⟩ := longofwords_inv (Option.some.inj ho')
    exact EXEC _ _ _ _ _ h1 h2 h3 h4
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    obtain ⟨rfl, rfl⟩ := longofwords_inv (Option.some.inj ho)
    exact .Elet _ _ _ _ _ hb (EXEC _ _ _ _ _ (eval_lift h1) (eval_lift h2)
      eval_hiword_letvar0 eval_loword_letvar0)
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hb
    obtain ⟨rfl, rfl⟩ := longofwords_inv (Option.some.inj ho)
    exact .Elet _ _ _ _ _ ha (EXEC _ _ _ _ _ eval_hiword_letvar0 eval_loword_letvar0
      (eval_lift h1) (eval_lift h2))
  · exact .Elet _ _ _ _ _ ha (.Elet _ _ _ _ _ (eval_lift hb)
      (EXEC _ _ _ _ _ eval_hiword_letvar1 eval_loword_letvar1
        eval_hiword_letvar0 eval_loword_letvar0))

/-- `is_longconst_sound` -/
theorem is_longconst_sound {le : Letenv} {a : SplitLong.Expr} {x : Val} {n : Integers.Int64}
    (LC : is_longconst a = some n) (ha : CminorSel.EvalExpr ge sp e m le a x) : x = .Vlong n := by
  unfold is_longconst at LC
  split at LC
  · cases LC
    obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 ha
    obtain rfl := inv_intconst h1
    obtain rfl := inv_intconst h2
    exact (Option.some.inj ho).symm
  · cases LC

/-- `is_longconst_zero_sound` -/
theorem is_longconst_zero_sound {le : Letenv} {a : SplitLong.Expr} {x : Val}
    (h : is_longconst_zero a = true) (ha : CminorSel.EvalExpr ge sp e m le a x) :
    x = .Vlong Integers.Int64.zero := by
  unfold is_longconst_zero at h
  split at h
  · rename_i n hn
    obtain rfl := (Integers.Int64.eq_spec _ _).mp h
    exact is_longconst_sound hn ha
  · cases h

/-- `eval_lowlong` -/
theorem eval_lowlong : UnarySound ge sp e m lowlong Val.loword := by
  intro le a x hx
  unfold lowlong
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx
    cases ho
    refine ⟨v2, h2, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.longofwords, Val.loword, Integers.Int64.lo_ofwords] <;> ld
  · exact ⟨_, eval_op1 hx rfl, .refl _⟩

/-- `eval_highlong` -/
theorem eval_highlong : UnarySound ge sp e m highlong Val.hiword := by
  intro le a x hx
  unfold highlong
  split
  · obtain ⟨v1, v2, h1, h2, ho⟩ := inv_op2 hx
    cases ho
    refine ⟨v1, h1, ?_⟩
    cases v1 <;> cases v2 <;> simp [Val.longofwords, Val.hiword, Integers.Int64.hi_ofwords] <;> ld
  · exact ⟨_, eval_op1 hx rfl, .refl _⟩

/-- `eval_longconst` -/
theorem eval_longconst (le : Letenv) (n : Integers.Int64) :
    CminorSel.EvalExpr ge sp e m le (longconst n) (.Vlong n) := by
  refine eval_op2 (eval_op0 rfl) (eval_op0 rfl) ?_
  show some (Val.Vlong (Integers.Int64.ofwords _ _)) = _
  rw [Integers.Int64.ofwords_recompose]

/-- `eval_intoflong` -/
theorem eval_intoflong : UnarySound ge sp e m intoflong Val.loword := eval_lowlong

/-- `eval_longofintu` -/
theorem eval_longofintu : UnarySound ge sp e m longofintu Val.longofintu := by
  intro le a x hx
  refine ⟨_, eval_op2 (eval_op0 rfl) hx rfl, ?_⟩
  cases x <;> simp [Val.longofintu, Val.longofwords, Integers.Int64.longofintu_ofwords] <;> ld

/-- `eval_longofint` -/
theorem eval_longofint : UnarySound ge sp e m longofint Val.longofint := by
  intro le a x hx
  unfold longofint
  split
  · obtain rfl := inv_intconst hx
    exact ⟨_, eval_longconst _ _, .refl _⟩
  · obtain ⟨v1, A, B⟩ := eval_shrimm (ge := ge) (sp := sp) (e := e) (m := m)
      (Integers.Int.repr 31) (x :: le) (.Eletvar 0) x (.Eletvar _ _ _ rfl)
    refine ⟨_, .Elet _ _ _ _ _ hx (eval_op2 A (.Eletvar _ _ _ rfl) rfl), ?_⟩
    cases x with
    | Vint i =>
      have hs : Val.shr (.Vint i) (.Vint (Integers.Int.repr 31)) =
          .Vint (Integers.Int.shr i (Integers.Int.repr 31)) := rfl
      dsimp only at B
      rw [hs] at B
      cases B
      simp only [Val.longofint, Val.longofwords, Integers.Int64.longofint_ofwords]
      exact .refl _
    | _ => exact .undef _

/-- `eval_notl` -/
theorem eval_notl : UnarySound ge sp e m notl Val.notl := by
  intro le a x hx
  unfold notl
  refine eval_splitlong ?_ ?_ hx
  · intro le a b x y ha hb
    obtain ⟨va, A, B⟩ := eval_notint le a x ha
    obtain ⟨vb, C, D⟩ := eval_notint le b y hb
    refine ⟨Val.longofwords va vb, eval_op2 A C rfl, ?_⟩
    rintro p q rfl rfl
    cases B; cases D
    simp [Val.longofwords, Val.notl, Val.notint, Integers.Int64.decompose_not]
  · cases x <;> first | trivial | rfl

/-- `eval_andl` -/
theorem eval_andl : BinarySound ge sp e m andl Val.andl := by
  intro le a x b y hx hy
  unfold andl
  refine eval_splitlong2 ?_ ?_ hx hy
  · intro le a1 a2 b1 b2 x1 x2 y1 y2 h1 h2 h3 h4
    obtain ⟨va, A, B⟩ := eval_and le a1 x1 b1 y1 h1 h3
    obtain ⟨vb, C, D⟩ := eval_and le a2 x2 b2 y2 h2 h4
    refine ⟨Val.longofwords va vb, eval_op2 A C rfl, ?_⟩
    rintro p1 p2 q1 q2 rfl rfl rfl rfl
    cases B; cases D
    simp [Val.longofwords, Val.andl, Val.and, Integers.Int64.decompose_and]
  · cases x <;> cases y <;> first | trivial | rfl

/-- `eval_orl` -/
theorem eval_orl : BinarySound ge sp e m orl Val.orl := by
  intro le a x b y hx hy
  unfold orl
  refine eval_splitlong2 ?_ ?_ hx hy
  · intro le a1 a2 b1 b2 x1 x2 y1 y2 h1 h2 h3 h4
    obtain ⟨va, A, B⟩ := eval_or le a1 x1 b1 y1 h1 h3
    obtain ⟨vb, C, D⟩ := eval_or le a2 x2 b2 y2 h2 h4
    refine ⟨Val.longofwords va vb, eval_op2 A C rfl, ?_⟩
    rintro p1 p2 q1 q2 rfl rfl rfl rfl
    cases B; cases D
    simp [Val.longofwords, Val.orl, Val.or, Integers.Int64.decompose_or]
  · cases x <;> cases y <;> first | trivial | rfl

/-- `eval_xorl` -/
theorem eval_xorl : BinarySound ge sp e m xorl Val.xorl := by
  intro le a x b y hx hy
  unfold xorl
  refine eval_splitlong2 ?_ ?_ hx hy
  · intro le a1 a2 b1 b2 x1 x2 y1 y2 h1 h2 h3 h4
    obtain ⟨va, A, B⟩ := eval_xor le a1 x1 b1 y1 h1 h3
    obtain ⟨vb, C, D⟩ := eval_xor le a2 x2 b2 y2 h2 h4
    refine ⟨Val.longofwords va vb, eval_op2 A C rfl, ?_⟩
    rintro p1 p2 q1 q2 rfl rfl rfl rfl
    cases B; cases D
    simp [Val.longofwords, Val.xorl, Val.xor, Integers.Int64.decompose_xor]
  · cases x <;> cases y <;> first | trivial | rfl

/-- `is_intconst_sound` -/
theorem is_intconst_sound {le : Letenv} {a : SplitLong.Expr} {x : Val} {n : Integers.Int}
    (h : is_intconst a = some n) (ha : CminorSel.EvalExpr ge sp e m le a x) : x = .Vint n := by
  unfold is_intconst at h
  split at h
  · cases h; exact inv_intconst ha
  · cases h

/-- `eval_negl` -/
theorem eval_negl : UnarySound ge sp e m negl Val.negl := by
  intro le a x ha
  unfold negl
  split
  · rename_i n hn
    obtain ⟨⟩ := is_longconst_sound hn ha
    exact ⟨_, eval_longconst _ _, .refl _⟩
  · refine ⟨_, .Ebuiltin _ _ _ _ _ (.Econs _ _ _ _ _ ha (.Enil _)) ?_, .refl _⟩
    show builtinOrExternalSem "__builtin_negl" sigLL _ _ _ _ _ _
    unfold builtinOrExternalSem
    rw [show Builtins.lookupBuiltinFunction "__builtin_negl" sigLL =
      some (.BI_standard .BI_negl) by decide]
    exact .intro _ _ _ _ (by cases x <;> rfl)

end CMCONSTR

/-! ## Calls to helper functions -/

section HELPERS

variable {prog : CminorSel.Program} {hf : HelperFunctions}
  (HELPERS : helper_functions_declared prog hf) {sp : Val} {e : Cminor.Env} {m : Mem}

/-- `eval_helper` -/
theorem eval_helper {bf : Builtins.BuiltinFunction} {le : Letenv} {id : Ident} {name : String}
    {sg : Signature} {args : SplitLong.Exprlist} {vargs : List Val} {vres : Val}
    (hargs : CminorSel.EvalExprlist prog.globalenv sp e m le args vargs)
    (hd : helper_declared prog id name sg)
    (hl : Builtins.lookupBuiltinFunction name sg = some bf)
    (hs : (Builtins.builtinFunctionSem bf).sem vargs = some vres) :
    CminorSel.EvalExpr prog.globalenv sp e m le (.Eexternal id sg args) vres := by
  unfold helper_declared at hd
  rw [ASTProgram.defmap_eq, Genv.find_def_symbol] at hd
  obtain ⟨b, P, Q⟩ := hd
  refine .Eexternal _ _ _ _ b (.EF_runtime name sg) _ _ P ?_ rfl hargs ?_
  · rw [Genv.findFunctPtr_iff]; exact Q
  · show builtinOrExternalSem name sg _ _ _ _ _ _
    unfold builtinOrExternalSem
    rw [hl]
    exact .intro _ _ _ _ hs

/-- `eval_helper_1` -/
theorem eval_helper_1 {bf : Builtins.BuiltinFunction} {le : Letenv} {id : Ident} {name : String}
    {sg : Signature} {arg1 : SplitLong.Expr} {varg1 vres : Val}
    (h1 : CminorSel.EvalExpr prog.globalenv sp e m le arg1 varg1)
    (hd : helper_declared prog id name sg)
    (hl : Builtins.lookupBuiltinFunction name sg = some bf)
    (hs : (Builtins.builtinFunctionSem bf).sem [varg1] = some vres) :
    CminorSel.EvalExpr prog.globalenv sp e m le (.Eexternal id sg (arg1 ::: .Enil)) vres :=
  eval_helper (.Econs _ _ _ _ _ h1 (.Enil _)) hd hl hs

/-- `eval_helper_2` -/
theorem eval_helper_2 {bf : Builtins.BuiltinFunction} {le : Letenv} {id : Ident} {name : String}
    {sg : Signature} {arg1 arg2 : SplitLong.Expr} {varg1 varg2 vres : Val}
    (h1 : CminorSel.EvalExpr prog.globalenv sp e m le arg1 varg1)
    (h2 : CminorSel.EvalExpr prog.globalenv sp e m le arg2 varg2)
    (hd : helper_declared prog id name sg)
    (hl : Builtins.lookupBuiltinFunction name sg = some bf)
    (hs : (Builtins.builtinFunctionSem bf).sem [varg1, varg2] = some vres) :
    CminorSel.EvalExpr prog.globalenv sp e m le (.Eexternal id sg (arg1 ::: arg2 ::: .Enil)) vres :=
  eval_helper (.Econs _ _ _ _ _ h1 (.Econs _ _ _ _ _ h2 (.Enil _))) hd hl hs

include HELPERS

/-- `eval_longoffloat` -/
theorem eval_longoffloat {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.longoffloat x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (longoffloat hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_dtos) ha HELPERS.1 (by decide)
    (by rw [← h]; cases x <;> rfl), .refl _⟩

/-- `eval_longuoffloat` -/
theorem eval_longuoffloat {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.longuoffloat x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (longuoffloat hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_dtou) ha HELPERS.2.1 (by decide)
    (by rw [← h]; cases x <;> rfl), .refl _⟩

/-- `eval_longofsingle` -/
theorem eval_longofsingle {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.longofsingle x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (longofsingle hf a) v ∧ Val.Lessdef y v := by
  cases x <;> simp only [Val.longofsingle, reduceCtorEq] at h
  rename_i f
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨v, hv, hl⟩ := eval_floatofsingle _ _ _ ha
  cases hl
  have hd : Floats.Float.toLong (Floats.Float.ofSingle f) = some n := Floats.Float32.to_long_double f n hn
  exact eval_longoffloat (HELPERS := HELPERS) hv (by simp [Val.floatofsingle, Val.longoffloat, hd])

/-- `eval_longuofsingle` -/
theorem eval_longuofsingle {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.longuofsingle x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (longuofsingle hf a) v ∧ Val.Lessdef y v := by
  cases x <;> simp only [Val.longuofsingle, reduceCtorEq] at h
  rename_i f
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨v, hv, hl⟩ := eval_floatofsingle _ _ _ ha
  cases hl
  have hd : Floats.Float.toLongu (Floats.Float.ofSingle f) = some n := Floats.Float32.to_longu_double f n hn
  exact eval_longuoffloat (HELPERS := HELPERS) hv (by simp [Val.floatofsingle, Val.longuoffloat, hd])

/-- `eval_floatoflong` -/
theorem eval_floatoflong {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.floatoflong x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (floatoflong hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_stod) ha HELPERS.2.2.1 (by decide)
    (by cases x <;> first | (rw [← h]; rfl) | cases h), .refl _⟩

/-- `eval_floatoflongu` -/
theorem eval_floatoflongu {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.floatoflongu x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (floatoflongu hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_utod) ha HELPERS.2.2.2.1 (by decide)
    (by cases x <;> first | (rw [← h]; rfl) | cases h), .refl _⟩

/-- `eval_singleoflong` -/
theorem eval_singleoflong {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.singleoflong x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (singleoflong hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_stof) ha HELPERS.2.2.2.2.1 (by decide)
    (by cases x <;> first | (rw [← h]; rfl) | cases h), .refl _⟩

/-- `eval_singleoflongu` -/
theorem eval_singleoflongu {le : Letenv} {a : SplitLong.Expr} {x y : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x) (h : Val.singleoflongu x = some y) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (singleoflongu hf a) v ∧ Val.Lessdef y v :=
  ⟨y, eval_helper_1 (bf := .BI_standard .BI_i64_utof) ha HELPERS.2.2.2.2.2.1 (by decide)
    (by cases x <;> first | (rw [← h]; rfl) | cases h), .refl _⟩

/-- `eval_divls_base` -/
theorem eval_divls_base {le : Letenv} {a b : SplitLong.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x)
    (hb : CminorSel.EvalExpr prog.globalenv sp e m le b y) (h : Val.divls x y = some z) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (divls_base hf a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_helper_2 (bf := .BI_standard .BI_i64_sdiv) ha hb HELPERS.2.2.2.2.2.2.1 (by decide) h,
    .refl _⟩

/-- `eval_divlu_base` -/
theorem eval_divlu_base {le : Letenv} {a b : SplitLong.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x)
    (hb : CminorSel.EvalExpr prog.globalenv sp e m le b y) (h : Val.divlu x y = some z) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (divlu_base hf a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_helper_2 (bf := .BI_standard .BI_i64_udiv) ha hb HELPERS.2.2.2.2.2.2.2.1 (by decide) h,
    .refl _⟩

/-- `eval_modls_base` -/
theorem eval_modls_base {le : Letenv} {a b : SplitLong.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x)
    (hb : CminorSel.EvalExpr prog.globalenv sp e m le b y) (h : Val.modls x y = some z) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (modls_base hf a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_helper_2 (bf := .BI_standard .BI_i64_smod) ha hb HELPERS.2.2.2.2.2.2.2.2.1 (by decide)
    h, .refl _⟩

/-- `eval_modlu_base` -/
theorem eval_modlu_base {le : Letenv} {a b : SplitLong.Expr} {x y z : Val}
    (ha : CminorSel.EvalExpr prog.globalenv sp e m le a x)
    (hb : CminorSel.EvalExpr prog.globalenv sp e m le b y) (h : Val.modlu x y = some z) :
    ∃ v, CminorSel.EvalExpr prog.globalenv sp e m le (modlu_base hf a b) v ∧ Val.Lessdef z v :=
  ⟨z, eval_helper_2 (bf := .BI_standard .BI_i64_umod) ha hb HELPERS.2.2.2.2.2.2.2.2.2.1
    (by decide) h, .refl _⟩

/-- `eval_mullhu` -/
theorem eval_mullhu (n : Integers.Int64) :
    UnarySound prog.globalenv sp e m (fun a => mullhu hf a n) (fun v => Val.mullhu v (.Vlong n)) :=
  fun le _ x ha => ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_umulh) (vres := Val.mullhu x (.Vlong n))
    ha (eval_longconst le n) HELPERS.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by cases x <;> rfl),
    .refl _⟩

/-- `eval_mullhs` -/
theorem eval_mullhs (n : Integers.Int64) :
    UnarySound prog.globalenv sp e m (fun a => mullhs hf a n) (fun v => Val.mullhs v (.Vlong n)) :=
  fun le _ x ha => ⟨_, eval_helper_2 (bf := .BI_standard .BI_i64_smulh) (vres := Val.mullhs x (.Vlong n))
    ha (eval_longconst le n) HELPERS.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by decide) (by cases x <;> rfl),
    .refl _⟩

end HELPERS

end SplitLongproof
end CC
