/-
  Theorems of `common/Values.v`: algebraic laws of the value operations, the
  comparison laws (`negate_cmp_bool`, `swap_cmpu_bool`, …), and the
  `lessdef` / `inject` relations with their basic properties.

  `Archi.ptr64` is `true` in this port (aarch64), so pointer + integer
  arithmetic on 32-bit `Vint`s is `Vundef`; the statements below hold for
  that configuration, as in Rocq (where several of them are proved by case
  analysis on `Archi.ptr64`).
-/
import CCLib.common.Values
import CCLib.lib.IntegersInt
import CCLib.lib.IntegersInt64
import CCLib.lib.IntegersPtrofs

namespace CC
namespace Val

/-! ## Booleans -/

theorem ofBool_true : ofBool true = Vtrue := rfl
theorem ofBool_false : ofBool false = Vfalse := rfl

/-- `Val.notbool_negb_1` -/
theorem notbool_negb_1 (b : Bool) : notbool (ofBool b) = ofBool (!b) := by
  cases b <;> decide

/-- `Val.notbool_negb_2` -/
theorem notbool_negb_2 (b : Bool) : ofBool b = notbool (ofBool (!b)) := by
  cases b <;> decide

/-- `Val.notbool_idem2` -/
theorem notbool_idem2 (b : Bool) : notbool (notbool (ofBool b)) = ofBool b := by
  cases b <;> decide

theorem boolval_ofBool (b : Bool) : boolval (ofBool b) = ofBool b := by
  cases b <;> decide

/-! ## Arithmetic laws (32-bit) -/

/-- `Val.add_commut` -/
theorem add_commut (x y : Val) : add x y = add y x := by
  cases x <;> cases y <;> simp [add, Integers.Int.add_commut]

/-- `Val.add_assoc` -/
theorem add_assoc (x y z : Val) : add (add x y) z = add x (add y z) := by
  cases x <;> cases y <;> cases z <;> simp [add, Integers.Int.add_assoc, Archi.ptr64]

/-- `Val.add_permut` -/
theorem add_permut (x y z : Val) : add x (add y z) = add y (add x z) := by
  rw [← add_assoc, add_commut x y, add_assoc]

/-- `Val.add_permut_4` -/
theorem add_permut_4 (x y z t : Val) : add (add x y) (add z t) = add (add x z) (add y t) := by
  rw [add_assoc, add_permut y, ← add_assoc]

/-- `Val.neg_add_distr` -/
theorem neg_add_distr (x y : Val) : neg (add x y) = add (neg x) (neg y) := by
  cases x <;> cases y <;> simp [add, neg, Integers.Int.neg_add_distr, Archi.ptr64]

/-- `Val.sub_zero_r` (for integer values). -/
theorem sub_zero_r (i : Integers.Int) : sub (.Vint i) Vzero = .Vint i := by
  simp [sub, Vzero, Integers.Int.sub_zero_r]

/-- `Val.sub_add_opp` -/
theorem sub_add_opp (x : Val) (i : Integers.Int) :
    sub x (.Vint i) = add x (.Vint (Integers.Int.neg i)) := by
  cases x <;> simp [sub, add, Integers.Int.sub_add_opp, Archi.ptr64]

/-- `Val.sub_opp_add` -/
theorem sub_opp_add (x : Val) (i : Integers.Int) :
    sub x (.Vint (Integers.Int.neg i)) = add x (.Vint i) := by
  rw [sub_add_opp, Integers.Int.neg_involutive]

/-- `Val.mul_commut` -/
theorem mul_commut (x y : Val) : mul x y = mul y x := by
  cases x <;> cases y <;> simp [mul, Integers.Int.mul_commut]

/-- `Val.mul_assoc` -/
theorem mul_assoc (x y z : Val) : mul (mul x y) z = mul x (mul y z) := by
  cases x <;> cases y <;> cases z <;> simp [mul, Integers.Int.mul_assoc]

/-- `Val.mul_add_distr_l` -/
theorem mul_add_distr_l (x y z : Val) : mul (add x y) z = add (mul x z) (mul y z) := by
  cases x <;> cases y <;> cases z <;>
    simp [mul, add, Integers.Int.mul_add_distr_l, Archi.ptr64]

/-- `Val.mul_add_distr_r` -/
theorem mul_add_distr_r (x y z : Val) : mul x (add y z) = add (mul x y) (mul x z) := by
  cases x <;> cases y <;> cases z <;>
    simp [mul, add, Integers.Int.mul_add_distr_r, Archi.ptr64]

/-- `Val.and_commut` -/
theorem and_commut (x y : Val) : and x y = and y x := by
  cases x <;> cases y <;> simp [and, Integers.Int.and_commut]

/-- `Val.and_assoc` -/
theorem and_assoc (x y z : Val) : and (and x y) z = and x (and y z) := by
  cases x <;> cases y <;> cases z <;> simp [and, Integers.Int.and_assoc]

/-- `Val.or_commut` -/
theorem or_commut (x y : Val) : or x y = or y x := by
  cases x <;> cases y <;> simp [or, Integers.Int.or_commut]

/-- `Val.or_assoc` -/
theorem or_assoc (x y z : Val) : or (or x y) z = or x (or y z) := by
  cases x <;> cases y <;> cases z <;> simp [or, Integers.Int.or_assoc]

/-- `Val.xor_commut` -/
theorem xor_commut (x y : Val) : xor x y = xor y x := by
  cases x <;> cases y <;> simp [xor, Integers.Int.xor_commut]

/-- `Val.xor_assoc` -/
theorem xor_assoc (x y z : Val) : xor (xor x y) z = xor x (xor y z) := by
  cases x <;> cases y <;> cases z <;> simp [xor, Integers.Int.xor_assoc]

/-- `Val.not_xor` -/
theorem not_xor (x : Val) : notint x = xor x Vmone := by
  cases x <;> simp [notint, xor, Vmone, Integers.Int.not_eq_xor_mone]

/-- `Val.shl_mul` -/
theorem shl_mul (x y : Val) : mul x (shl Vone y) = shl x y := by
  cases x <;> cases y <;> simp only [mul, shl, Vone]
  rename_i a b
  by_cases h : Integers.Int.ltu b Integers.Int.iwordsize = true
  · rw [if_pos h, if_pos h, Integers.Int.shl_mul a b]
  · rw [if_neg h, if_neg h]

/-! ## Arithmetic laws (64-bit) -/

/-- `Val.addl_commut` -/
theorem addl_commut (x y : Val) : addl x y = addl y x := by
  cases x <;> cases y <;> simp [addl, Integers.Int64.add_commut]

/-- `Val.mull_commut` -/
theorem mull_commut (x y : Val) : mull x y = mull y x := by
  cases x <;> cases y <;> simp [mull, Integers.Int64.mul_commut]

/-- `Val.andl_commut` -/
theorem andl_commut (x y : Val) : andl x y = andl y x := by
  cases x <;> cases y <;> simp [andl, Integers.Int64.and_commut]

/-- `Val.orl_commut` -/
theorem orl_commut (x y : Val) : orl x y = orl y x := by
  cases x <;> cases y <;> simp [orl, Integers.Int64.or_commut]

/-- `Val.xorl_commut` -/
theorem xorl_commut (x y : Val) : xorl x y = xorl y x := by
  cases x <;> cases y <;> simp [xorl, Integers.Int64.xor_commut]

/-! ## Comparisons -/

theorem cmpDifferentBlocks_negate (c : Comparison) :
    cmpDifferentBlocks c.negate = (cmpDifferentBlocks c).map (!·) := by
  cases c <;> rfl

theorem cmpDifferentBlocks_swap (c : Comparison) :
    cmpDifferentBlocks c.swap = cmpDifferentBlocks c := by
  cases c <;> rfl

/-- `Val.negate_cmp_bool` -/
theorem negate_cmp_bool (c : Comparison) (x y : Val) :
    cmp_bool c.negate x y = (cmp_bool c x y).map (!·) := by
  cases x <;> cases y <;> simp [cmp_bool, Integers.Int.negate_cmp]

/-- `Val.negate_cmpl_bool` -/
theorem negate_cmpl_bool (c : Comparison) (x y : Val) :
    cmpl_bool c.negate x y = (cmpl_bool c x y).map (!·) := by
  cases x <;> cases y <;> simp [cmpl_bool, Integers.Int64.negate_cmp]

/-- `Val.swap_cmp_bool` -/
theorem swap_cmp_bool (c : Comparison) (x y : Val) :
    cmp_bool c.swap x y = cmp_bool c y x := by
  cases x <;> cases y <;> simp [cmp_bool, Integers.Int.swap_cmp]

/-- `Val.swap_cmpl_bool` -/
theorem swap_cmpl_bool (c : Comparison) (x y : Val) :
    cmpl_bool c.swap x y = cmpl_bool c y x := by
  cases x <;> cases y <;> simp [cmpl_bool, Integers.Int64.swap_cmp]

/-- `Val.negate_cmpu_bool` -/
theorem negate_cmpu_bool (vp : Block → Z → Bool) (c : Comparison) (x y : Val) :
    cmpu_bool vp c.negate x y = (cmpu_bool vp c x y).map (!·) := by
  cases x <;> cases y <;> simp [cmpu_bool, Integers.Int.negate_cmpu, Archi.ptr64]

/-- `Val.negate_cmplu_bool` -/
theorem negate_cmplu_bool (vp : Block → Z → Bool) (c : Comparison) (x y : Val) :
    cmplu_bool vp c.negate x y = (cmplu_bool vp c x y).map (!·) := by
  cases x <;> cases y <;> simp only [cmplu_bool, Integers.Int64.negate_cmpu] <;>
    (try split) <;> (try split) <;> (try split) <;>
    simp [cmpDifferentBlocks_negate, Integers.Ptrofs.negate_cmpu]

/-- `Val.swap_cmpu_bool` -/
theorem swap_cmpu_bool (vp : Block → Z → Bool) (c : Comparison) (x y : Val) :
    cmpu_bool vp c.swap x y = cmpu_bool vp c y x := by
  cases x <;> cases y <;> simp [cmpu_bool, Integers.Int.swap_cmpu, Archi.ptr64]

/-- `Val.swap_cmplu_bool` -/
theorem swap_cmplu_bool (vp : Block → Z → Bool) (c : Comparison) (x y : Val) :
    cmplu_bool vp c.swap x y = cmplu_bool vp c y x := by
  cases x <;> cases y <;> simp only [cmplu_bool, Integers.Int64.swap_cmpu]
  all_goals first
    | rfl
    | (rename_i b1 o1 b2 o2
       by_cases hb : b1 = b2
       · subst hb; simp [Integers.Ptrofs.swap_cmpu, Bool.and_comm]
       · simp [hb, Ne.symm hb, cmpDifferentBlocks_swap, Bool.and_comm])
    | simp [cmpDifferentBlocks_swap]

theorem ofOptbool_map_not (ob : Option Bool) :
    ofOptbool (ob.map (!·)) = notbool (ofOptbool ob) := by
  cases ob with
  | none => rfl
  | some b => cases b <;> decide

/-- `Val.negate_cmp` -/
theorem negate_cmp (c : Comparison) (x y : Val) : cmp c.negate x y = notbool (cmp c x y) := by
  rw [cmp, cmp, negate_cmp_bool, ofOptbool_map_not]

/-- `Val.swap_cmp` -/
theorem swap_cmp (c : Comparison) (x y : Val) : cmp c.swap x y = cmp c y x := by
  rw [cmp, cmp, swap_cmp_bool]

/-! ## `lessdef`: "is less defined than" -/

/-- `Values.Val.lessdef v1 v2`: `v1` is `v2` or `Vundef`. -/
inductive Lessdef : Val → Val → Prop where
  | refl (v : Val) : Lessdef v v
  | undef (v : Val) : Lessdef .Vundef v

/-- `Values.Val.lessdef_list` -/
inductive LessdefList : List Val → List Val → Prop where
  | nil : LessdefList [] []
  | cons {v1 v2 vl1 vl2} : Lessdef v1 v2 → LessdefList vl1 vl2 →
      LessdefList (v1 :: vl1) (v2 :: vl2)

theorem lessdef_refl (v : Val) : Lessdef v v := .refl v

theorem lessdef_trans {v1 v2 v3 : Val} (h1 : Lessdef v1 v2) (h2 : Lessdef v2 v3) :
    Lessdef v1 v3 := by
  cases h1 with
  | refl => exact h2
  | undef => exact .undef _

theorem lessdef_list_refl (vl : List Val) : LessdefList vl vl := by
  induction vl with
  | nil => exact .nil
  | cons v vl ih => exact .cons (.refl v) ih

theorem lessdef_iff (v1 v2 : Val) : Lessdef v1 v2 ↔ v1 = v2 ∨ v1 = .Vundef := by
  constructor
  · intro h; cases h with
    | refl => exact Or.inl rfl
    | undef => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact .refl _
    · exact .undef _

/-- `Val.lessdef_undef` -/
theorem lessdef_undef {v : Val} (h : Lessdef v .Vundef) : v = .Vundef := by
  cases h <;> rfl

/-- If `v1` is defined, `lessdef v1 v2` means equality. -/
theorem lessdef_defined {v1 v2 : Val} (h : Lessdef v1 v2) (hd : v1 ≠ .Vundef) : v1 = v2 := by
  cases h with
  | refl => rfl
  | undef => exact absurd rfl hd

/-- A unary operation that is strict in `Vundef` is monotone for `lessdef`. -/
theorem unop_lessdef (f : Val → Val) (hf : f .Vundef = .Vundef) {v1 v2 : Val}
    (h : Lessdef v1 v2) : Lessdef (f v1) (f v2) := by
  cases h with
  | refl => exact .refl _
  | undef => rw [hf]; exact .undef _

/-- A binary operation that is strict in `Vundef` on both sides is monotone for
    `lessdef` (covers `add_lessdef`, `sub_lessdef`, `mul_lessdef`, …). -/
theorem binop_lessdef (f : Val → Val → Val) (hl : ∀ v, f .Vundef v = .Vundef)
    (hr : ∀ v, f v .Vundef = .Vundef) {a1 a2 b1 b2 : Val}
    (h1 : Lessdef a1 b1) (h2 : Lessdef a2 b2) : Lessdef (f a1 a2) (f b1 b2) := by
  cases h1 with
  | refl =>
    cases h2 with
    | refl => exact .refl _
    | undef => rw [hr]; exact .undef _
  | undef => rw [hl]; exact .undef _

/-- `Val.add_lessdef` -/
theorem add_lessdef {a1 a2 b1 b2 : Val} (h1 : Lessdef a1 b1) (h2 : Lessdef a2 b2) :
    Lessdef (add a1 a2) (add b1 b2) :=
  binop_lessdef add (fun v => by cases v <;> rfl) (fun v => by cases v <;> rfl) h1 h2

/-- `Val.sub_lessdef` -/
theorem sub_lessdef {a1 a2 b1 b2 : Val} (h1 : Lessdef a1 b1) (h2 : Lessdef a2 b2) :
    Lessdef (sub a1 a2) (sub b1 b2) :=
  binop_lessdef sub (fun v => by cases v <;> rfl) (fun v => by cases v <;> rfl) h1 h2

/-- `Val.mul_lessdef` -/
theorem mul_lessdef {a1 a2 b1 b2 : Val} (h1 : Lessdef a1 b1) (h2 : Lessdef a2 b2) :
    Lessdef (mul a1 a2) (mul b1 b2) :=
  binop_lessdef mul (fun v => by cases v <;> rfl) (fun v => by cases v <;> rfl) h1 h2

/-- `Val.addl_lessdef` -/
theorem addl_lessdef {a1 a2 b1 b2 : Val} (h1 : Lessdef a1 b1) (h2 : Lessdef a2 b2) :
    Lessdef (addl a1 a2) (addl b1 b2) :=
  binop_lessdef addl (fun v => by cases v <;> rfl) (fun v => by cases v <;> rfl) h1 h2

/-- `Val.load_result_lessdef` -/
theorem load_result_lessdef (chunk : Chunk) {v1 v2 : Val} (h : Lessdef v1 v2) :
    Lessdef (loadResult chunk v1) (loadResult chunk v2) :=
  unop_lessdef (loadResult chunk) (by cases chunk <;> rfl) h

/-- `Val.zero_ext_lessdef` -/
theorem zero_ext_lessdef (n : Nat) {v1 v2 : Val} (h : Lessdef v1 v2) :
    Lessdef (zeroExt n v1) (zeroExt n v2) :=
  unop_lessdef (zeroExt n) rfl h

/-- `Val.sign_ext_lessdef` -/
theorem sign_ext_lessdef (n : Nat) {v1 v2 : Val} (h : Lessdef v1 v2) :
    Lessdef (signExt n v1) (signExt n v2) :=
  unop_lessdef (signExt n) rfl h

/-- `Val.offset_ptr_lessdef` (named `offsetPtr` here). -/
theorem offset_ptr_lessdef (delta : Integers.Ptrofs) {v1 v2 : Val} (h : Lessdef v1 v2) :
    Lessdef (offsetPtr v1 delta) (offsetPtr v2 delta) :=
  unop_lessdef (offsetPtr · delta) rfl h

/-- `Val.cmp_bool_lessdef` -/
theorem cmp_bool_lessdef (c : Comparison) {v1 v2 v1' v2' : Val} {b : Bool}
    (h1 : Lessdef v1 v1') (h2 : Lessdef v2 v2') (h : cmp_bool c v1 v2 = some b) :
    cmp_bool c v1' v2' = some b := by
  cases h1 with
  | undef => simp [cmp_bool] at h
  | refl =>
    cases h2 with
    | refl => exact h
    | undef => cases v1 <;> simp [cmp_bool] at h

/-- `Val.has_type` of `Vundef`. -/
theorem hasType_undef (t : ATyp) : hasType .Vundef t = true := by cases t <;> rfl

/-- `Val.lessdef` preserves typing backwards. -/
theorem hasType_lessdef {v1 v2 : Val} {t : ATyp} (h : Lessdef v1 v2) (ht : hasType v2 t = true) :
    hasType v1 t = true := by
  cases h with
  | refl => exact ht
  | undef => exact hasType_undef t

/-! ## Memory injections on values -/

/-- `Values.meminj`: a partial map from blocks to (block, offset delta). -/
abbrev Meminj := Block → Option (Block × Z)

/-- `Values.inject_incr` -/
def inject_incr (f1 f2 : Meminj) : Prop :=
  ∀ b b' delta, f1 b = some (b', delta) → f2 b = some (b', delta)

/-- `Values.compose_meminj` -/
def compose_meminj (f f' : Meminj) : Meminj := fun b =>
  match f b with
  | none => none
  | some (b', delta) =>
    match f' b' with
    | none => none
    | some (b'', delta') => some (b'', delta + delta')

/-- `Values.Val.inject f v1 v2`: `v1` and `v2` are related through the
    memory injection `f` (pointers are relocated, `Vundef` matches anything). -/
inductive Inject (f : Meminj) : Val → Val → Prop where
  | int (i : Integers.Int) : Inject f (.Vint i) (.Vint i)
  | long (i : Integers.Int64) : Inject f (.Vlong i) (.Vlong i)
  | float (x : Floats.Float) : Inject f (.Vfloat x) (.Vfloat x)
  | single (x : Floats.Float32) : Inject f (.Vsingle x) (.Vsingle x)
  | ptr {b1 ofs1 b2 ofs2} (delta : Z) :
      f b1 = some (b2, delta) →
      ofs2 = Integers.Ptrofs.add ofs1 (Integers.Ptrofs.repr delta) →
      Inject f (.Vptr b1 ofs1) (.Vptr b2 ofs2)
  | undef (v : Val) : Inject f .Vundef v

/-- `Values.Val.inject_list` -/
inductive InjectList (f : Meminj) : List Val → List Val → Prop where
  | nil : InjectList f [] []
  | cons {v1 v2 vl1 vl2} : Inject f v1 v2 → InjectList f vl1 vl2 →
      InjectList f (v1 :: vl1) (v2 :: vl2)

theorem inject_incr_refl (f : Meminj) : inject_incr f f := fun _ _ _ h => h

theorem inject_incr_trans {f1 f2 f3 : Meminj} (h1 : inject_incr f1 f2) (h2 : inject_incr f2 f3) :
    inject_incr f1 f3 := fun b b' d h => h2 b b' d (h1 b b' d h)

/-- `Val.val_inject_incr` -/
theorem inject_incr_inject {f1 f2 : Meminj} {v1 v2 : Val} (hi : inject_incr f1 f2)
    (h : Inject f1 v1 v2) : Inject f2 v1 v2 := by
  cases h with
  | int => exact .int _
  | long => exact .long _
  | float => exact .float _
  | single => exact .single _
  | ptr delta hf ho => exact .ptr delta (hi _ _ _ hf) ho
  | undef => exact .undef _

/-- `Val.val_inject_list_incr` -/
theorem inject_incr_inject_list {f1 f2 : Meminj} {vl1 vl2 : List Val} (hi : inject_incr f1 f2)
    (h : InjectList f1 vl1 vl2) : InjectList f2 vl1 vl2 := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (inject_incr_inject hi hv) ih

/-- The identity injection: `Val.inject inject_id` is `Val.lessdef`. -/
def inject_id : Meminj := fun b => some (b, 0)

theorem lessdef_inject_id {v1 v2 : Val} : Lessdef v1 v2 ↔ Inject inject_id v1 v2 := by
  constructor
  · intro h
    cases h with
    | refl =>
      cases v1 with
      | Vundef => exact .undef _
      | Vint i => exact .int i
      | Vlong i => exact .long i
      | Vfloat x => exact .float x
      | Vsingle x => exact .single x
      | Vptr b ofs =>
        refine .ptr 0 rfl ?_
        rw [Integers.Ptrofs.repr_zero, Integers.Ptrofs.add_zero]
    | undef => exact .undef _
  · intro h
    cases h with
    | int => exact .refl _
    | long => exact .refl _
    | float => exact .refl _
    | single => exact .refl _
    | ptr delta hf ho =>
      simp only [inject_id, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [ho, Integers.Ptrofs.repr_zero, Integers.Ptrofs.add_zero]
      exact .refl _
    | undef => exact .undef _

/-- `Val.add_inject` (32-bit: on aarch64 only integer additions are defined). -/
theorem add_inject {f : Meminj} {v1 v1' v2 v2' : Val} (h1 : Inject f v1 v1')
    (h2 : Inject f v2 v2') : Inject f (add v1 v2) (add v1' v2') := by
  cases h1 <;> cases h2 <;> simp [add, Archi.ptr64] <;> first | exact .int _ | exact .undef _

/-- `Val.cmp_bool_inject` -/
theorem cmp_bool_inject {f : Meminj} (c : Comparison) {v1 v1' v2 v2' : Val} {b : Bool}
    (h1 : Inject f v1 v1') (h2 : Inject f v2 v2') (h : cmp_bool c v1 v2 = some b) :
    cmp_bool c v1' v2' = some b := by
  cases h1 <;> cases h2 <;> simp_all [cmp_bool]

end Val
end CC
