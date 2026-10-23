/-
  Port of VST's `progs/verif_prod.v`: `product` (`vst/progs/prod.c`) meets
  its specification.

      typedef int64_t limb;  typedef int32_t s32;
      void product(limb out[19], const limb *a, const limb *b) {
        s32 t1, t2;  limb t3;
        t1 = a[0];  t2 = b[0];  t3 = t1 * t2;  out[0] = t3;
        return;
      }

  VST's specification (`product_spec`) claims that afterwards
  `out = product orig_a orig_b` (all ten element-wise products), and its
  proof (`product_sumarray`) is unfinished: it stops after the last
  `forward` without `Qed`.  The claim cannot be proved, since `product` only
  writes `out[0]`; moreover `t1 * t2` is a 32-bit `int` multiplication, which
  wraps for VST's bound `|a[i]|, |b[i]| < 2^27`.

  The specification proved here says exactly what the function does: `out[0]`
  becomes the sign-extended 32-bit product of the low 32 bits of `a[0]` and
  `b[0]` (`prodVal`), the other elements of `out` are unchanged, and `a`, `b`
  are given back.  `prodVal_eq_mul` shows that `prodVal` is the 64-bit
  product when that product fits in an `int`, and
  `prodVal_ne_mul_at_vst_bound` that VST's bound does not ensure this.

  `out` is owned at a writable permission `po` with arbitrary initial contents
  (VST's `data_at_`), `a`, `b` at a readable permission `p`; the arrays fit in
  the address space (VST's `field_compatible`).
-/
import VST.progs.prod
import CCLib
open CC CC.Sep CC.HProp
open Prod

namespace VST.Verif.Prod

/-! ## The value written -/

/-- `(long) ((int) x * (int) y)`, in C's (CompCert's) semantics. -/
def prodVal (x y : Integers.Int64) : Integers.Int64 :=
  Integers.Int64.repr (Integers.Int.signed
    (Integers.Int.mul (Integers.Int.repr (Integers.Int64.unsigned x))
      (Integers.Int.repr (Integers.Int64.unsigned y))))

/-- When the product of the signed values fits in an `int` (no overflow, so
    the C multiplication is defined), `prodVal` is the 64-bit product. -/
theorem prodVal_eq_mul (x y : Integers.Int64)
    (h1 : -2147483648 ≤ Integers.Int64.signed x * Integers.Int64.signed y)
    (h2 : Integers.Int64.signed x * Integers.Int64.signed y ≤ 2147483647) :
    prodVal x y = Integers.Int64.mul x y := by
  unfold prodVal
  rw [int_repr_unsigned64 x, int_repr_unsigned64 y, ← Integers.Int.repr_mul,
    Integers.Int.signed_repr h1 h2, Integers.Int64.mul_signed]

/-- VST's bound `|a[i]|, |b[i]| < 2^27` does not prevent the overflow:
    for `a[0] = b[0] = 2^27 - 1` the result is not the product. -/
theorem prodVal_ne_mul_at_vst_bound :
    prodVal (Integers.Int64.repr 134217727) (Integers.Int64.repr 134217727)
      ≠ Integers.Int64.mul (Integers.Int64.repr 134217727) (Integers.Int64.repr 134217727) := by
  decide

/-! ## The parts of the body -/

def elemOf (a : Ident) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar a (tptr tlong)) (.Econst_int (Integers.Int.repr 0) tint)
    (tptr tlong)) tlong
def mulExpr : Expr :=
  .Ecast (.Ebinop .Omul (.Etempvar _t1 tint) (.Etempvar _t2 tint) tint) tlong
def storeStmt : Stmt := .Sassign (elemOf _out) (.Etempvar _t3 tlong)
def readA : Stmt :=
  .Ssequence (.Sset _t'1 (elemOf _a)) (.Sset _t1 (.Ecast (.Etempvar _t'1 tlong) tint))
def readB : Stmt :=
  .Ssequence (.Sset _t'2 (elemOf _b)) (.Sset _t2 (.Ecast (.Etempvar _t'2 tlong) tint))
def fullBody : Stmt :=
  .Ssequence readA (.Ssequence readB
    (.Ssequence (.Sset _t3 mulExpr) (.Ssequence storeStmt (.Sreturn none))))

theorem body_eq : f_product.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (po p : Permission) (bo ba bb : Block) (oo oa ob : Integers.Ptrofs)
  (vo : Nat → Val) (fa fb : Nat → Integers.Int64)

/-- The source arrays. -/
def Src : HProp :=
  arrayL64 p ba (Integers.Ptrofs.unsigned oa) 10 fa ∗ arrayL64 p bb (Integers.Ptrofs.unsigned ob) 10 fb

/-- The parameters as passed. -/
def Params (e : Env) (le : TempEnv) : Prop :=
  e = emptyEnv
  ∧ le.get _out = some (.Vptr bo oo) ∧ le.get _a = some (.Vptr ba oa)
  ∧ le.get _b = some (.Vptr bb ob)

/-- The contents of `out` afterwards. -/
def outAfter (j : Nat) : Val :=
  if j = 0 then .Vlong (prodVal (fa 0) (fb 0)) else vo j

end

/-! ## The proof -/

section
variable (ge : CGenv) (fe : EntryRel) (po p : Permission) (bo ba bb : Block)
  (oo oa ob : Integers.Ptrofs) (vo : Nat → Val) (fa fb : Nat → Integers.Int64)
  (hpw : permOrder po .Writable = true) (hpr : permOrder p .Readable = true)
  (hnoo : Integers.Ptrofs.unsigned oo + 8 * 10 ≤ 18446744073709551616)
  (hnoa : Integers.Ptrofs.unsigned oa + 8 * 10 ≤ 18446744073709551616)
  (hnob : Integers.Ptrofs.unsigned ob + 8 * 10 ≤ 18446744073709551616)

/-- The heap throughout the reads. -/
abbrev Arrs (v : Nat → Val) : HProp :=
  arrayVL64 po bo (Integers.Ptrofs.unsigned oo) 10 v ∗ Src p ba bb oa ob fa fb

/-- After the two reads: `t1`, `t2` are the low words of `a[0]`, `b[0]`. -/
def Read (e : Env) (le : TempEnv) : Prop :=
  Params bo ba bb oo oa ob e le
  ∧ le.get _t1 = some (.Vint (Integers.Int.repr (Integers.Int64.unsigned (fa 0))))
  ∧ le.get _t2 = some (.Vint (Integers.Int.repr (Integers.Int64.unsigned (fb 0))))

/-- After `t3 = t1 * t2`. -/
def Multiplied (e : Env) (le : TempEnv) : Prop :=
  Params bo ba bb oo oa ob e le ∧ le.get _t3 = some (.Vlong (prodVal (fa 0) (fb 0)))

/-- After `t1 = a[0];`. -/
def ReadA (e : Env) (le : TempEnv) : Prop :=
  Params bo ba bb oo oa ob e le
  ∧ le.get _t1 = some (.Vint (Integers.Int.repr (Integers.Int64.unsigned (fa 0))))

include hpr hnoa in
/-- `t1 = a[0];` -/
theorem readA_triple :
    Sep.Triple ge fe f_product
      (fun e le hp => Params bo ba bb oo oa ob e le ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)
      readA
      (.only (fun e le hp => ReadA bo ba bb oo oa ob fa e le
        ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)) := by
  refine Sep.triple_seq_only ge fe f_product (Q := fun e le hp =>
      Params bo ba bb oo oa ob e le ∧ le.get _t'1 = some (.Vlong (fa 0))
      ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp) ?_ ?_
  · refine Sep.triple_set ge fe f_product _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, ho, ha, hb⟩, harr⟩ := hP
    obtain ⟨_, hsrc, hag1⟩ := sep_right_agrees harr hag
    obtain ⟨_, hA, hagA⟩ := sep_left_agrees hsrc hag1
    refine ⟨.Vlong (fa 0), eval_index_l64 (i := 0) hpr hA hagA (by omega)
      (EvalExpr.Etempvar _ _ _ ha) (EvalExpr.Econst_int _ tint) rfl (by omega) hnoa,
      ⟨he, ?_, ?_, ?_⟩, PTree.gss _ _ _, harr⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
  · refine Sep.triple_set ge fe f_product _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, ho, ha, hb⟩, ht, harr⟩ := hP
    refine ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ ht) (semCast_long_int m _),
      ⟨⟨he, ?_, ?_, ?_⟩, PTree.gss _ _ _⟩, harr⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)

include hpr hnob in
/-- `t2 = b[0];` -/
theorem readB_triple :
    Sep.Triple ge fe f_product
      (fun e le hp => ReadA bo ba bb oo oa ob fa e le ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)
      readB
      (.only (fun e le hp => Read bo ba bb oo oa ob fa fb e le
        ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)) := by
  refine Sep.triple_seq_only ge fe f_product (Q := fun e le hp =>
      ReadA bo ba bb oo oa ob fa e le ∧ le.get _t'2 = some (.Vlong (fb 0))
      ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp) ?_ ?_
  · refine Sep.triple_set ge fe f_product _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨⟨he, ho, ha, hb⟩, ht1⟩, harr⟩ := hP
    obtain ⟨_, hsrc, hag1⟩ := sep_right_agrees harr hag
    obtain ⟨_, hB, hagB⟩ := sep_right_agrees hsrc hag1
    refine ⟨.Vlong (fb 0), eval_index_l64 (i := 0) hpr hB hagB (by omega)
      (EvalExpr.Etempvar _ _ _ hb) (EvalExpr.Econst_int _ tint) rfl (by omega) hnob,
      ⟨⟨he, ?_, ?_, ?_⟩, ?_⟩, PTree.gss _ _ _, harr⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
  · refine Sep.triple_set ge fe f_product _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨⟨he, ho, ha, hb⟩, ht1⟩, ht, harr⟩ := hP
    refine ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ ht) (semCast_long_int m _),
      ⟨⟨he, ?_, ?_, ?_⟩, ?_, PTree.gss _ _ _⟩, harr⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)

/-- `t3 = t1 * t2;` -/
theorem mul_triple :
    Sep.Triple ge fe f_product
      (fun e le hp => Read bo ba bb oo oa ob fa fb e le ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)
      (.Sset _t3 mulExpr)
      (.only (fun e le hp => Multiplied bo ba bb oo oa ob fa fb e le
        ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)) := by
  refine Sep.triple_set ge fe f_product _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨⟨⟨he, ho, ha, hb⟩, ht1, ht2⟩, harr⟩ := hP
  refine ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop .Omul _ _ _ _ _ _
      (EvalExpr.Etempvar _ _ _ ht1) (EvalExpr.Etempvar _ _ _ ht2) (semBinop_mul_int _ _ _ _))
      (semCast_int_long m _), ⟨⟨he, ?_, ?_, ?_⟩, PTree.gss _ _ _⟩, harr⟩ <;>
  (rw [PTree.gso _ _ _ _ (by decide)]; assumption)

include hpw hnoo in
/-- `out[0] = t3;` -/
theorem store_triple :
    Sep.Triple ge fe f_product
      (fun e le hp => Multiplied bo ba bb oo oa ob fa fb e le
        ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)
      storeStmt
      (.only (fun e le hp => Multiplied bo ba bb oo oa ob fa fb e le
        ∧ Arrs po p bo ba bb oo oa ob fa fb (outAfter vo fa fb) hp)) := by
  have hst := triple_store_index_l64 ge fe f_product (Multiplied bo ba bb oo oa ob fa fb)
    (Src p ba bb oa ob fa fb) (.Etempvar _out (tptr tlong)) (.Econst_int (Integers.Int.repr 0) tint)
    (.Etempvar _t3 tlong) po bo oo 10 0 vo (prodVal (fa 0) (fb 0)) hpw (by omega) (by omega) hnoo
    (fun e le m h => EvalExpr.Etempvar _ _ _ h.1.2.1)
    (fun e le m h => EvalExpr.Econst_int _ tint)
    (fun e le m h => EvalExpr.Etempvar _ _ _ h.2) rfl rfl
  exact hst

include hpw hpr hnoo hnoa hnob in
theorem body_triple :
    Sep.Triple ge fe f_product
      (fun e le hp => Params bo ba bb oo oa ob e le ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp)
      fullBody
      { normal := fun e _ hp => e = emptyEnv
          ∧ Arrs po p bo ba bb oo oa ob fa fb (outAfter vo fa fb) hp,
        brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := fun _ hp => Arrs po p bo ba bb oo oa ob fa fb (outAfter vo fa fb) hp } := by
  refine Sep.triple_seq_only ge fe f_product
    (readA_triple ge fe po p bo ba bb oo oa ob vo fa fb hpr hnoa) ?_
  refine Sep.triple_seq_only ge fe f_product
    (readB_triple ge fe po p bo ba bb oo oa ob vo fa fb hpr hnob) ?_
  refine Sep.triple_seq_only ge fe f_product
    (mul_triple ge fe po p bo ba bb oo oa ob vo fa fb) ?_
  refine Sep.triple_seq_only ge fe f_product
    (store_triple ge fe po p bo ba bb oo oa ob vo fa fb hpw hnoo) ?_
  refine Sep.triple_conseq ge fe f_product (Sep.triple_return_none ge fe f_product _
    (fun _ hp => Arrs po p bo ba bb oo oa ob fa fb (outAfter vo fa fb) hp)
    (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  obtain ⟨⟨⟨he, -⟩, -⟩, harr⟩ := hP
  subst he
  exact ⟨m, hp, freeList_emptyEnv _ _, harr, fun _ hd hag => ⟨hd, hag⟩⟩

end

/-! ## As a function specification -/

/-- The specification of `product`: `out[0]` becomes `prodVal a[0] b[0]`,
    the rest of `out` and the arrays `a`, `b` are unchanged.  `vo` are the
    (arbitrary) initial contents of `out` (`data_at_`). -/
def productSpec (po p : Permission) (bo ba bb : Block) (oo oa ob : Integers.Ptrofs)
    (vo : Nat → Val) (fa fb : Nat → Integers.Int64) : Sep.FunSpec where
  tyargs := [tptr tlong, tptr tlong, tptr tlong]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr bo oo, .Vptr ba oa, .Vptr bb ob]
    ∧ (arrayVL64 po bo (Integers.Ptrofs.unsigned oo) 10 vo ∗ Src p ba bb oa ob fa fb) hp
  post := fun _ hp =>
    (arrayVL64 po bo (Integers.Ptrofs.unsigned oo) 10
      (fun j => if j = 0 then .Vlong (prodVal (fa 0) (fb 0)) else vo j)
      ∗ Src p ba bb oa ob fa fb) hp
  measure := fun _ => 0

/-- **`product` satisfies `productSpec`** (VST's `product_sumarray`). -/
theorem product_satisfies (ge : CGenv) (po p : Permission) (bo ba bb : Block)
    (oo oa ob : Integers.Ptrofs) (vo : Nat → Val) (fa fb : Nat → Integers.Int64)
    (hpw : permOrder po .Writable = true) (hpr : permOrder p .Readable = true)
    (hnoo : Integers.Ptrofs.unsigned oo + 8 * 10 ≤ 18446744073709551616)
    (hnoa : Integers.Ptrofs.unsigned oa + 8 * 10 ≤ 18446744073709551616)
    (hnob : Integers.Ptrofs.unsigned ob + 8 * 10 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_product)
      (productSpec po p bo ba bb oo oa ob vo fa fb) [.Vptr bo oo, .Vptr ba oa, .Vptr bb ob] := by
  refine satisfies_internal_noVars_void ge (FunctionEntry2 ge) f_product _ _
    (fun e le hp => Params bo ba bb oo oa ob e le
      ∧ Arrs po p bo ba bb oo oa ob fa fb vo hp) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨⟨rfl, rfl, rfl, rfl⟩, hpre.2⟩⟩
  · rw [body_eq]
    exact body_triple ge (FunctionEntry2 ge) po p bo ba bb oo oa ob vo fa fb hpw hpr hnoo hnoa hnob

end VST.Verif.Prod
