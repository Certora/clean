/-
  Correctness of instruction selection for x86-64 (the x86 instance of
  `CCLib/backend/SelectionproofSwitch.lean`) — port of `backend/Selectionproof.v`,
  part 2: translation of `switch` statements (`Rint`, `Rlong`,
  `Section SEL_SWITCH`: `sel_switch_correct_rec`, `sel_switch_correct`;
  `Section SEL_SWITCH_INT`: `sel_switch_int_correct`,
  `sel_switch_long_correct`).

  Differences from Rocq: the hypotheses of `Section SEL_SWITCH` are the
  fields of the structure `SelSwitchHyps`; as in part 1 the global
  environment `ge` is arbitrary.
-/
import CCLib.x86.SelectionproofExpr
import CCLib.common.SwitchProof

namespace CC
namespace X86
namespace Selectionproof

open Op CminorSel SelectOp Selection Switch

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- `Selectionproof.Rint` -/
inductive Rint : Z → Val → Prop where
  | intro (n : Integers.Int) : Rint (Integers.Int.unsigned n) (.Vint n)

/-- `Selectionproof.Rlong` -/
inductive Rlong : Z → Val → Prop where
  | intro (n : Integers.Int64) : Rlong (Integers.Int64.unsigned n) (.Vlong n)

theorem Rint_inv {z : Z} {v : Val} (h : Rint z v) :
    ∃ n, v = .Vint n ∧ Integers.Int.unsigned n = z := by
  cases h; exact ⟨_, rfl, rfl⟩

theorem Rlong_inv {z : Z} {v : Val} (h : Rlong z v) :
    ∃ n, v = .Vlong n ∧ Integers.Int64.unsigned n = z := by
  cases h; exact ⟨_, rfl, rfl⟩

theorem boolOfVal_ofBool (b : Bool) : Val.BoolOfVal (Val.ofBool b) b := by
  cases b
  · exact Val.BoolOfVal.int Integers.Int.zero
  · exact Val.BoolOfVal.int Integers.Int.one

theorem listNthZ_eq {A : Type} (l : List A) (n : Z) :
    CminorSel.listNthZ l n = Switch.listNthZ l n := by
  induction l generalizing n with
  | nil => rfl
  | cons hd tl ih => simp only [CminorSel.listNthZ, Switch.listNthZ, ih]

section SEL_SWITCH
variable (ge : CminorSel.CGenv) (makeCmpEq makeCmpLtu : CminorSel.Expr → Z → CminorSel.Expr)
  (makeSub : CminorSel.Expr → Z → CminorSel.Expr) (makeToInt : CminorSel.Expr → CminorSel.Expr)
  (modulus : Z) (R : Z → Val → Prop)

/-- The hypotheses of `Section SEL_SWITCH`. -/
structure SelSwitchHyps : Prop where
  cmp_eq : ∀ sp e m le a v i n, CminorSel.EvalExpr ge sp e m le a v → R i v →
    0 ≤ n → n < modulus →
    CminorSel.EvalExpr ge sp e m le (makeCmpEq a n) (Val.ofBool (decide (i = n)))
  cmp_ltu : ∀ sp e m le a v i n, CminorSel.EvalExpr ge sp e m le a v → R i v →
    0 ≤ n → n < modulus →
    CminorSel.EvalExpr ge sp e m le (makeCmpLtu a n) (Val.ofBool (decide (i < n)))
  sub : ∀ sp e m le a v i n, CminorSel.EvalExpr ge sp e m le a v → R i v →
    0 ≤ n → n < modulus →
    ∃ v', CminorSel.EvalExpr ge sp e m le (makeSub a n) v' ∧ R ((i - n) % modulus) v'
  to_int : ∀ sp e m le a v i, CminorSel.EvalExpr ge sp e m le a v → R i v →
    ∃ v', CminorSel.EvalExpr ge sp e m le (makeToInt a) v' ∧ Rint (i % Integers.Int.modulus) v'

variable {ge makeCmpEq makeCmpLtu makeSub makeToInt modulus R}

/-- `Selectionproof.sel_switch_correct_rec` -/
theorem sel_switch_correct_rec (H : SelSwitchHyps ge makeCmpEq makeCmpLtu makeSub makeToInt modulus R)
    {sp : Val} {e : Cminor.Env} {m : Mem} {varg : Val} {i : Z} {x : Nat} (hR : R i varg)
    (t : Comptree) :
    ∀ (arg : Nat) (le : Letenv), WfComptree modulus t → le[arg]? = some varg →
    comptreeMatch modulus i t = some x →
    CminorSel.EvalExitexpr ge sp e m le (selSwitch makeCmpEq makeCmpLtu makeSub makeToInt arg t) x := by
  induction t with
  | CTaction act =>
    intro arg le _ _ hm
    cases hm
    exact .XEexit _ _
  | CTifeq key act t' ih =>
    intro arg le hwf harg hm
    cases hwf with
    | ifeq _ _ _ h0 h1 hwf =>
      have hc := H.cmp_eq sp e m le (.Eletvar arg) varg i key (.Eletvar _ _ _ harg) hR h0 h1
      refine .XEcondition _ _ _ _ (decide (i = key)) _
        (eval_condexpr_of_expr _ hc (boolOfVal_ofBool _)) ?_
      simp only [comptreeMatch] at hm
      by_cases hk : i = key
      · simp only [hk, if_true, decide_true] at hm ⊢
        cases hm
        exact .XEexit _ _
      · simp only [hk, if_false, decide_false] at hm ⊢
        exact ih arg le hwf harg hm
  | CTiflt key t1 t2 ih1 ih2 =>
    intro arg le hwf harg hm
    cases hwf with
    | iflt _ _ _ h0 h1 hwf1 hwf2 =>
      have hc := H.cmp_ltu sp e m le (.Eletvar arg) varg i key (.Eletvar _ _ _ harg) hR h0 h1
      refine .XEcondition _ _ _ _ (decide (i < key)) _
        (eval_condexpr_of_expr _ hc (boolOfVal_ofBool _)) ?_
      simp only [comptreeMatch] at hm
      by_cases hk : i < key
      · simp only [hk, if_true, decide_true] at hm ⊢
        exact ih1 arg le hwf1 harg hm
      · simp only [hk, if_false, decide_false] at hm ⊢
        exact ih2 arg le hwf2 harg hm
  | CTjumptable ofs sz tbl t' ih =>
    intro arg le hwf harg hm
    cases hwf with
    | jumptable _ _ _ _ h0 h1 h2 h3 hwf =>
      obtain ⟨v', hv', hR'⟩ :=
        H.sub sp e m le (.Eletvar arg) varg i ofs (.Eletvar _ _ _ harg) hR h0 h1
      have hc := H.cmp_ltu sp e m (v' :: le) (.Eletvar 0) v' ((i - ofs) % modulus) sz
        (.Eletvar _ _ _ rfl) hR' h2 h3
      refine .XElet _ _ _ v' _ hv' (.XEcondition _ _ _ _ (decide ((i - ofs) % modulus < sz)) _
        (eval_condexpr_of_expr _ hc (boolOfVal_ofBool _)) ?_)
      simp only [comptreeMatch] at hm
      by_cases hk : (i - ofs) % modulus < sz
      · simp only [hk, if_true, decide_true] at hm ⊢
        obtain ⟨v'', hv'', hRi⟩ :=
          H.to_int sp e m (v' :: le) (.Eletvar 0) v' _ (.Eletvar _ _ _ rfl) hR'
        obtain ⟨n, rfl, hn⟩ := Rint_inv hRi
        exact .XEjumptable _ _ _ n x hv'' (by rw [listNthZ_eq, hn]; exact hm)
      · simp only [hk, if_false, decide_false] at hm ⊢
        exact ih (arg + 1) (v' :: le) hwf (by simpa using harg) hm

/-- `Selectionproof.sel_switch_correct` -/
theorem sel_switch_correct (H : SelSwitchHyps ge makeCmpEq makeCmpLtu makeSub makeToInt modulus R)
    {dfl : Nat} {cases : Table} {arg : CminorSel.Expr} {sp : Val} {e : Cminor.Env} {m : Mem}
    {varg : Val} {i : Z} {t : Comptree} {le : Letenv}
    (hval : validateSwitch modulus dfl cases t = true)
    (ha : CminorSel.EvalExpr ge sp e m le arg varg) (hR : R i varg) (hi0 : 0 ≤ i)
    (hi1 : i < modulus) :
    CminorSel.EvalExitexpr ge sp e m le
      (.XElet arg (selSwitch makeCmpEq makeCmpLtu makeSub makeToInt 0 t)) (switchTarget i dfl cases) := by
  obtain ⟨hwf, hagree⟩ := validateSwitch_correct modulus (by zomega) dfl t cases hval
  exact .XElet _ _ _ _ _ ha
    (sel_switch_correct_rec H hR t 0 (varg :: le) hwf rfl (hagree i hi0 hi1))

end SEL_SWITCH

/-! ### `Section SEL_SWITCH_INT` -/

theorem lessdef_ofBool {b : Bool} {v : Val} (h : Val.Lessdef (Val.ofBool b) v) :
    v = Val.ofBool b := by
  cases b <;> cases h <;> rfl

theorem lessdef_vint' {n : Integers.Int} {v : Val} (h : Val.Lessdef (.Vint n) v) : v = .Vint n := by
  cases h; rfl

theorem lessdef_vlong' {n : Integers.Int64} {v : Val} (h : Val.Lessdef (.Vlong n) v) :
    v = .Vlong n := by
  cases h; rfl

theorem int_unsigned_repr_lt {n : Z} (h0 : 0 ≤ n) (h1 : n < Integers.Int.modulus) :
    Integers.Int.unsigned (Integers.Int.repr n) = n :=
  Integers.Int.unsigned_repr h0
    (by have : Integers.Int.max_unsigned = Integers.Int.modulus - 1 := rfl; zomega)

theorem int64_unsigned_repr_lt {n : Z} (h0 : 0 ≤ n) (h1 : n < Integers.Int64.modulus) :
    Integers.Int64.unsigned (Integers.Int64.repr n) = n :=
  Integers.Int64.unsigned_repr h0
    (by have : Integers.Int64.max_unsigned = Integers.Int64.modulus - 1 := rfl; zomega)

theorem int_eq_repr (n0 : Integers.Int) {n : Z} (h0 : 0 ≤ n) (h1 : n < Integers.Int.modulus) :
    Integers.Int.eq n0 (Integers.Int.repr n) = decide (Integers.Int.unsigned n0 = n) := by
  have hu := int_unsigned_repr_lt h0 h1
  by_cases h : Integers.Int.unsigned n0 = n
  · have : n0 = Integers.Int.repr n := by
      rw [← h, Integers.Int.repr_unsigned]
    rw [this, Integers.Int.eq_true]; simp [hu]
  · have : n0 ≠ Integers.Int.repr n := by
      intro heq; apply h; rw [heq, hu]
    rw [Integers.Int.eq_false this]; simp [h]

theorem int64_eq_repr (n0 : Integers.Int64) {n : Z} (h0 : 0 ≤ n) (h1 : n < Integers.Int64.modulus) :
    Integers.Int64.eq n0 (Integers.Int64.repr n) = decide (Integers.Int64.unsigned n0 = n) := by
  have hu := int64_unsigned_repr_lt h0 h1
  by_cases h : Integers.Int64.unsigned n0 = n
  · have : n0 = Integers.Int64.repr n := by
      rw [← h, Integers.Int64.repr_unsigned]
    rw [this, Integers.Int64.eq_true]; simp [hu]
  · have : n0 ≠ Integers.Int64.repr n := by
      intro heq; apply h; rw [heq, hu]
    rw [Integers.Int64.eq_false this]; simp [h]

theorem int64_lo_ofwords (hi lo : Integers.Int) :
    Integers.Int64.loword (Integers.Int64.ofwords hi lo) = lo := by
  unfold Integers.Int64.loword Integers.Int64.ofwords
  bv_decide

theorem int64_unsigned_loword (n : Integers.Int64) :
    Integers.Int.unsigned (Integers.Int64.loword n) =
      Integers.Int64.unsigned n % Integers.Int.modulus := by
  unfold Integers.Int64.loword Integers.Int.unsigned Integers.Int64.unsigned Integers.MI.unsigned
    Integers.Int.modulus Integers.MI.modulus
  simp

/-- Evaluation of `X86.SplitLong.lowlong` (Rocq's `eval_lowlong`, specialised to the
  x86 operators). -/
theorem eval_lowlong {ge : CminorSel.CGenv} {sp : Val} {e : Cminor.Env} {m : Mem} {le : Letenv}
    {a : CminorSel.Expr} {x : Val} (ha : CminorSel.EvalExpr ge sp e m le a x) :
    ∃ v, CminorSel.EvalExpr ge sp e m le (X86.SplitLong.lowlong a) v ∧ Val.Lessdef (Val.loword x) v := by
  unfold X86.SplitLong.lowlong
  split
  · next e1 e2 =>
    cases ha with
    | Eop _ _ _ vl _ hl ho =>
      cases hl with
      | Econs _ _ _ v1 _ h1 hl =>
        cases hl with
        | Econs _ _ _ v2 _ h2 hl =>
          cases hl
          have hx : some (Val.longofwords v1 v2) = some x := ho
          cases hx
          refine ⟨v2, h2, ?_⟩
          cases v1 <;> cases v2 <;>
            simp only [Val.longofwords, Val.loword, int64_lo_ofwords] <;>
            first | exact .refl _ | exact .undef _
  · exact ⟨_, SelectOpproof.eval_op1 ha rfl, .refl _⟩

section SEL_SWITCH_INT
variable {ge : CminorSel.CGenv}

/-- `Selectionproof.sel_switch_int_correct` -/
theorem sel_switch_int_correct {dfl : Nat} {cases : Table} {arg : CminorSel.Expr} {sp : Val}
    {e : Cminor.Env} {m : Mem} {i : Integers.Int} {t : Comptree} {le : Letenv}
    (hval : validateSwitch Integers.Int.modulus dfl cases t = true)
    (ha : CminorSel.EvalExpr ge sp e m le arg (.Vint i)) :
    CminorSel.EvalExitexpr ge sp e m le (.XElet arg (selSwitchInt 0 t))
      (switchTarget (Integers.Int.unsigned i) dfl cases) := by
  have hrange := Integers.Int.unsigned_range i
  unfold selSwitchInt
  refine sel_switch_correct (R := Rint) ⟨?_, ?_, ?_, ?_⟩ hval ha (.intro i) hrange.1 hrange.2
  · intro sp e m le a v i' n hev hR h0 h1
    obtain ⟨n0, rfl, rfl⟩ := Rint_inv hR
    obtain ⟨vb, hA, hB⟩ := SelectOpproof.eval_comp .Ceq _ _ _ _ _ hev
      (SelectOpproof.eval_op0 (op := .Ointconst (Integers.Int.repr n)) rfl)
    have hc : Val.cmp .Ceq (.Vint n0) (.Vint (Integers.Int.repr n)) =
        Val.ofBool (decide (Integers.Int.unsigned n0 = n)) := by
      show Val.ofOptbool (some (Integers.Int.eq n0 (Integers.Int.repr n))) = _
      rw [int_eq_repr n0 h0 h1]; rfl
    rw [hc] at hB
    rw [← lessdef_ofBool hB]; exact hA
  · intro sp e m le a v i' n hev hR h0 h1
    obtain ⟨n0, rfl, rfl⟩ := Rint_inv hR
    obtain ⟨vb, hA, hB⟩ := SelectOpproof.eval_compu .Clt _ _ _ _ _ hev
      (SelectOpproof.eval_op0 (op := .Ointconst (Integers.Int.repr n)) rfl)
    have hc : Val.cmpu (Mem.validPointer m) .Clt (.Vint n0) (.Vint (Integers.Int.repr n)) =
        Val.ofBool (decide (Integers.Int.unsigned n0 < n)) := by
      show Val.ofOptbool (some (Integers.Int.ltu n0 (Integers.Int.repr n))) = _
      rw [Integers.Int.ltu_def, int_unsigned_repr_lt h0 h1]; rfl
    rw [hc] at hB
    rw [← lessdef_ofBool hB]; exact hA
  · intro sp e m le a v i' n hev hR h0 h1
    obtain ⟨n0, rfl, rfl⟩ := Rint_inv hR
    obtain ⟨vb, hA, hB⟩ := SelectOpproof.eval_sub _ _ _ _ _ hev
      (SelectOpproof.eval_op0 (op := .Ointconst (Integers.Int.repr n)) rfl)
    have hB' := lessdef_vint' hB
    subst hB'
    refine ⟨_, hA, ?_⟩
    have : (Integers.Int.unsigned n0 - n) % Integers.Int.modulus =
        Integers.Int.unsigned (Integers.Int.sub n0 (Integers.Int.repr n)) := by
      rw [Integers.Int.sub_unsigned, Integers.Int.unsigned_repr_eq, int_unsigned_repr_lt h0 h1]
    rw [this]; exact .intro _
  · intro sp e m le a v i' hev hR
    obtain ⟨n0, rfl, rfl⟩ := Rint_inv hR
    have hr := Integers.Int.unsigned_range n0
    refine ⟨_, hev, ?_⟩
    rw [Int.emod_eq_of_lt hr.1 hr.2]; exact .intro _

/-- `Selectionproof.sel_switch_long_correct` -/
theorem sel_switch_long_correct {dfl : Nat} {cases : Table} {arg : CminorSel.Expr} {sp : Val}
    {e : Cminor.Env} {m : Mem} {i : Integers.Int64} {t : Comptree} {le : Letenv}
    (hval : validateSwitch Integers.Int64.modulus dfl cases t = true)
    (ha : CminorSel.EvalExpr ge sp e m le arg (.Vlong i)) :
    CminorSel.EvalExitexpr ge sp e m le (.XElet arg (selSwitchLong 0 t))
      (switchTarget (Integers.Int64.unsigned i) dfl cases) := by
  have hrange := Integers.Int64.unsigned_range i
  unfold selSwitchLong
  refine sel_switch_correct (R := Rlong) ⟨?_, ?_, ?_, ?_⟩ hval ha (.intro i) hrange.1 hrange.2
  · intro sp e m le a v i' n hev hR h0 h1
    obtain ⟨n0, rfl, rfl⟩ := Rlong_inv hR
    refine SelectLongproof.eval_cmpl .Ceq hev
      (SelectLongproof.eval_longconst _ (Integers.Int64.repr n)) ?_
    show some (Val.ofBool (Integers.Int64.eq n0 (Integers.Int64.repr n))) = _
    rw [int64_eq_repr n0 h0 h1]
  · intro sp e m le a v i' n hev hR h0 h1
    obtain ⟨n0, rfl, rfl⟩ := Rlong_inv hR
    refine SelectLongproof.eval_cmplu .Clt hev
      (SelectLongproof.eval_longconst _ (Integers.Int64.repr n)) ?_
    show some (Val.ofBool (Integers.Int64.ltu n0 (Integers.Int64.repr n))) = _
    rw [Integers.Int64.ltu_def, int64_unsigned_repr_lt h0 h1]
  · intro sp e m le a v i' n hev hR h0 h1
    obtain ⟨n0, rfl, rfl⟩ := Rlong_inv hR
    obtain ⟨vb, hA, hB⟩ := SelectLongproof.eval_subl _ _ _ _ _ hev
      (SelectLongproof.eval_longconst _ (Integers.Int64.repr n))
    have hB' := lessdef_vlong' hB
    subst hB'
    refine ⟨_, hA, ?_⟩
    have : (Integers.Int64.unsigned n0 - n) % Integers.Int64.modulus =
        Integers.Int64.unsigned (Integers.Int64.sub n0 (Integers.Int64.repr n)) := by
      rw [Integers.Int64.sub_unsigned, Integers.Int64.unsigned_repr_eq,
        int64_unsigned_repr_lt h0 h1]
    rw [this]; exact .intro _
  · intro sp e m le a v i' hev hR
    obtain ⟨n0, rfl, rfl⟩ := Rlong_inv hR
    obtain ⟨vb, hA, hB⟩ := eval_lowlong hev
    have hB' := lessdef_vint' hB
    subst hB'
    refine ⟨_, hA, ?_⟩
    rw [← int64_unsigned_loword]; exact .intro _

end SEL_SWITCH_INT

end Selectionproof
end X86
end CC
