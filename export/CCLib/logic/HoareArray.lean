/-
  Support for reasoning about `unsigned int` arrays with the Hoare logic in
  `CCLib.logic.Hoare`: the bridge between CompCert's machine integers (`BitVec`) and
  `Z` arithmetic, and a points-to predicate for arrays of 32-bit words.
-/
import CCLib.logic.Hoare

namespace CC

/-! ## `BitVec` ↔ `Z` bridge

Only the non-negative, in-`int`-range case is covered — that is all a loop
counter and an array index need.  Note the binders are spelled `_root_.Int`, not
`Z`: `omega` does not see through the `abbrev`. -/

-- `2147483648` (= 2^31) is spelled as a literal throughout, not as a definition:
-- `omega` has to see it.

theorem toInt_repr (i : _root_.Int) (h1 : 0 ≤ i) (h2 : i < 2147483648) :
    (Integers.Int.repr i).toInt = i := by
  show (BitVec.ofInt 32 i).toInt = i
  rw [BitVec.toInt_ofInt, Int.bmod_eq_emod_of_lt (by simp; omega)]
  simp; omega

theorem repr_add (i j : _root_.Int) :
    Integers.Int.add (Integers.Int.repr i) (Integers.Int.repr j)
      = Integers.Int.repr (i + j) := by
  show BitVec.ofInt 32 i + BitVec.ofInt 32 j = BitVec.ofInt 32 (i + j)
  rw [BitVec.ofInt_add]

theorem repr_sub (i j : _root_.Int) :
    Integers.Int.sub (Integers.Int.repr i) (Integers.Int.repr j)
      = Integers.Int.repr (i - j) := by
  show BitVec.ofInt 32 i - BitVec.ofInt 32 j = BitVec.ofInt 32 (i - j)
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- Signed `<` on `repr` of two in-range non-negatives is `<` on `Z`. -/
theorem lt_repr (i j : _root_.Int) (hi1 : 0 ≤ i) (hi2 : i < 2147483648)
    (hj1 : 0 ≤ j) (hj2 : j < 2147483648) :
    Integers.Int.lt (Integers.Int.repr i) (Integers.Int.repr j) = decide (i < j) := by
  show BitVec.slt _ _ = _
  rw [BitVec.slt_eq_decide, toInt_repr i hi1 hi2, toInt_repr j hj1 hj2]

/-- `==` on `repr` of two in-range non-negatives is `=` on `Z`. -/
theorem eq_repr (i j : _root_.Int) (hi1 : 0 ≤ i) (hi2 : i < 2147483648)
    (hj1 : 0 ≤ j) (hj2 : j < 2147483648) :
    Integers.Int.eq (Integers.Int.repr i) (Integers.Int.repr j) = decide (i = j) := by
  show (Integers.Int.repr i == Integers.Int.repr j) = _
  by_cases h : i = j
  · subst h; simp
  · have : Integers.Int.repr i ≠ Integers.Int.repr j := fun he => h (by
      rw [← toInt_repr i hi1 hi2, ← toInt_repr j hj1 hj2, he])
    simp [this, h]

/-- `==` on `repr` of two values of the unsigned range is `=` on `Z`. -/
theorem eq_repr_unsigned (i j : _root_.Int) (hi1 : 0 ≤ i) (hi2 : i < 4294967296)
    (hj1 : 0 ≤ j) (hj2 : j < 4294967296) :
    Integers.Int.eq (Integers.Int.repr i) (Integers.Int.repr j) = decide (i = j) := by
  show (Integers.Int.repr i == Integers.Int.repr j) = _
  by_cases h : i = j
  · subst h; simp
  · have : Integers.Int.repr i ≠ Integers.Int.repr j := fun he => h (by
      have := congrArg BitVec.toNat he
      simp only [Integers.Int.repr, Integers.MI.repr, BitVec.toNat_ofInt] at this
      omega)
    simp [this, h]

/-! ## `unsigned int` arrays -/

/-- The offset `Cop.sem_add` computes for `base + iv` when the element type is
    `unsigned int`.  Stated as the semantics computes it, so the load lemma below
    needs no offset arithmetic. -/
def elemOfs (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (iv : Integers.Int) :
    Integers.Ptrofs :=
  Integers.Ptrofs.add ofs0
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv tuint))
      (Cop.ptrofsOfInt .Signed iv))

theorem semAdd_elem (cenv : CompositeEnv) (m : Mem) (b : Block)
    (ofs0 : Integers.Ptrofs) (iv : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vptr b ofs0) (tptr tuint) (.Vint iv) tint m
      = some (.Vptr b (elemOfs cenv ofs0 iv)) := by
  simp [Cop.semBinaryOperation, Cop.semAdd, Cop.classifyAdd, typeconv,
        removeAttributes, tattr, tptr, tuint, tint, Cop.semAddPtrInt, elemOfs]

/-- `ArrU32 cenv m b ofs0 n arr`: the `n` `unsigned int`s at `b + ofs0` hold
    `arr 0 … arr (n-1)` in `m`, and are readable.

    This is a plain predicate, not a separating one: there is no `∗` here, so it
    says nothing about what else `m` contains.  See the header of `CCLib.logic.Hoare`. -/
def ArrU32 (cenv : CompositeEnv) (m : Mem) (b : Block) (ofs0 : Integers.Ptrofs)
    (n : _root_.Int) (arr : _root_.Int → Integers.Int) : Prop :=
  ∀ i : _root_.Int, 0 ≤ i → i < n →
    Mem.loadv .Mint32 m (.Vptr b (elemOfs cenv ofs0 (Integers.Int.repr i)))
      = some (.Vint (arr i))

/-- Reading `base[idx]` where `base` is a temporary holding the array pointer and
    `idx` is any expression of type `int` evaluating to the index. -/
theorem eval_index (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem)
    (b : Block) (ofs0 : Integers.Ptrofs) (n : _root_.Int)
    (arr : _root_.Int → Integers.Int)
    (harr : ArrU32 ge.genv_cenv m b ofs0 n arr)
    (pid : Ident) (hp : le.get pid = some (.Vptr b ofs0))
    (idx : Expr) (hty : typeof idx = tint) (i : _root_.Int)
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (h0 : 0 ≤ i) (hn : i < n) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr tuint)) idx (tptr tuint)) tuint)
      (.Vint (arr i)) := by
  have hadd : Cop.semBinaryOperation ge.genv_cenv .Oadd (.Vptr b ofs0) (tptr tuint)
                (.Vint (Integers.Int.repr i)) (typeof idx) m
              = some (.Vptr b (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i))) := by
    rw [hty]; exact semAdd_elem _ _ _ _ _
  refine EvalExpr.Elvalue _ b (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i)) .Full _
    (EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop .Oadd _ _ _ (.Vptr b ofs0) (.Vint (Integers.Int.repr i)) _
        (EvalExpr.Etempvar pid (tptr tuint) _ hp) hidx hadd))
    ?_
  exact DerefLoc.value .Mint32 _ rfl (harr i h0 hn)

/-! ## Computing the operator semantics at `int` / `unsigned int`

`Cop`'s functions are heavily nested `match`es on classification results.  These
lemmas do that reduction once, so the program proofs never see it. -/

@[simp] theorem castIntInt_I32 (sg : Signedness) (i : Integers.Int) :
    Cop.castIntInt .I32 sg i = i := by cases sg <;> rfl

-- The simp set that reduces a `Cop.sem_*` call at scalar int types.
attribute [local simp] Cop.semBinaryOperation Cop.semCmp Cop.classifyCmp typeconv
  removeAttributes tattr tint tuint tbool Cop.semBinarith Cop.classifyBinarith
  Cop.binarithType Cop.semCast Cop.classifyCast Archi.ptr64 Integers.Int.cmp
  Integers.Int.cmpu Integers.MI.cmp Integers.MI.cmpu Cop.semSub Cop.semAdd
  Cop.classifySub Cop.classifyAdd Cop.boolVal Cop.classifyBool

theorem semBinop_lt_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Olt (.Vint x) tint (.Vint y) tint m
      = some (Val.ofBool (Integers.Int.lt x y)) := by simp [Integers.Int.lt]

theorem semBinop_le_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Ole (.Vint x) tint (.Vint y) tint m
      = some (Val.ofBool (!Integers.Int.lt y x)) := by simp [Integers.Int.lt]

theorem semBinop_eq_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tint (.Vint y) tint m
      = some (Val.ofBool (Integers.Int.eq x y)) := by
  simp [Integers.Int.eq, Integers.MI.eq]

theorem semBinop_gt_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Ogt (.Vint x) tint (.Vint y) tint m
      = some (Val.ofBool (Integers.Int.lt y x)) := by simp [Integers.Int.lt]

theorem semBinop_ltu_uint (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Olt (.Vint x) tuint (.Vint y) tuint m
      = some (Val.ofBool (Integers.Int.ltu x y)) := by simp [Integers.Int.ltu]

theorem semBinop_add_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tint (.Vint y) tint m
      = some (.Vint (Integers.Int.add x y)) := by simp [Integers.Int.add, Integers.MI.add]

theorem semBinop_sub_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vint x) tint (.Vint y) tint m
      = some (.Vint (Integers.Int.sub x y)) := by simp [Integers.Int.sub, Integers.MI.sub]

theorem semBinop_mul_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Omul (.Vint x) tint (.Vint y) tint m
      = some (.Vint (Integers.Int.mul x y)) := by
  simp [Cop.semMul, Integers.Int.mul, Integers.MI.mul]

/-! ### `unsigned int` operands -/

theorem semBinop_add_uint (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tuint (.Vint y) tuint m
      = some (.Vint (Integers.Int.add x y)) := by
  simp [Integers.Int.add, Integers.MI.add]

theorem semBinop_eq_uint_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tuint (.Vint y) tint m
      = some (Val.ofBool (Integers.Int.eq x y)) := by
  simp [Integers.Int.eq, Integers.MI.eq]

theorem semBinop_sub_uint_int (cenv m) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vint x) tuint (.Vint y) tint m
      = some (.Vint (Integers.Int.sub x y)) := by
  simp [Integers.Int.sub, Integers.MI.sub]

theorem semCast_uint (m : Mem) (v : Integers.Int) :
    Cop.semCast (.Vint v) tuint tuint m = some (.Vint v) := by
  simp

/-- A comparison result is a usable `int` truth value. -/
theorem boolVal_ofBool_int (m) (bb : Bool) : Cop.boolVal (Val.ofBool bb) tint m = some bb := by
  cases bb <;> simp [Val.ofBool, Val.Vtrue, Val.Vfalse] <;> decide

/-- `(_Bool)1` is `1`. -/
theorem semCast_one_bool (m) :
    Cop.semCast (.Vint (Integers.Int.repr 1)) tint tbool m
      = some (.Vint (Integers.Int.repr 1)) := by simp; decide

/-! ## From `elemOfs` to plain `Z`

`Cop.sem_add` computes an element address in `Ptrofs` (i.e. modulo 2^64), while
the separating `arrayU32` predicate indexes by `ofs + 4*i` over `Z`.  Bridging the
two needs a no-overflow side condition — the same one CompCert's own array
reasoning carries. -/

-- fresh Nat/Int binders so `omega` sees its own instances (the goal's `+`/`=`
-- sit at `CC.Z`, where omega is blind)
private theorem ptr_arith (A i : Nat)
    (hno : (A : _root_.Int) + 4 * (i : _root_.Int) < 18446744073709551616) :
    (((A + 4 * i % 18446744073709551616) % 18446744073709551616 : Nat) : _root_.Int)
      = (A : _root_.Int) + 4 * (i : _root_.Int) := by omega

theorem elemOfs_unsigned (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (i : Nat)
    (hi : (i : _root_.Int) < 2147483648)
    (hno : (Integers.Ptrofs.unsigned ofs0) + 4 * (i : _root_.Int) < 18446744073709551616) :
    Integers.Ptrofs.unsigned (elemOfs cenv ofs0 (Integers.Int.repr i))
      = Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int) := by
  have hsz : sizeof cenv tuint = 4 := by simp [sizeof, tuint]
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  simp only [elemOfs, hsz, Cop.ptrofsOfInt, Integers.Ptrofs.of_ints,
             Integers.Ptrofs.add, Integers.Ptrofs.mul, Integers.Ptrofs.unsigned,
             Integers.Ptrofs.repr, Integers.MI.add, Integers.MI.mul,
             Integers.MI.repr, Integers.MI.unsigned, Integers.MI.signed,
             BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt, hw] at hno ⊢
  rw [toInt_repr (i : _root_.Int) (by omega) hi]
  have h4 : ((4 : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = 4 := by
    omega
  have hii : (((i : Nat) : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = i := by
    omega
  rw [h4, hii]
  exact ptr_arith _ _ hno

private theorem padd_arith (A d : Nat) (hno : A + d < 18446744073709551616) :
    (((A + d) % 18446744073709551616 : Nat) : _root_.Int)
      = (A : _root_.Int) + (d : _root_.Int) := by omega
/-- Address of a struct field, over `Z`, given that the object does not straddle
    the end of the address space.  The bound is stated over `Nat` so that `omega`
    can see it: `Ptrofs.unsigned` returns `Z`, where it cannot. -/
theorem ptrofs_add_unsigned (ofs : Integers.Ptrofs) (d : Nat)
    (hno : ofs.toNat + d < 18446744073709551616) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr (d : _root_.Int)))
      = Integers.Ptrofs.unsigned ofs + (d : _root_.Int) := by
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  simp only [Integers.Ptrofs.add, Integers.Ptrofs.unsigned, Integers.Ptrofs.repr,
             Integers.MI.add, Integers.MI.repr, Integers.MI.unsigned,
             BitVec.toNat_add, BitVec.toNat_ofInt, hw]
  have hd : (((d : Nat) : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = d := by
    omega
  rw [hd]
  exact padd_arith _ _ hno

/-- `freeList` over the environment of a function with no `fn_vars` is a no-op. -/
theorem elements_empty {A : Type} : PTree.elements (PTree.empty : PTree A) = [] := rfl

theorem freeList_emptyEnv (cenv : CompositeEnv) (m : Mem) :
    Mem.freeList m (blocksOfEnv cenv emptyEnv) = some m := by
  simp [blocksOfEnv, emptyEnv, elements_empty, Mem.freeList]

end CC
