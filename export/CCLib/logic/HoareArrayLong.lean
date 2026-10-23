/-
  `int` arrays indexed by a **64-bit signed `long`**: reading `a[i]` and
  writing `a[i] = v` with `i : long` (VST's `progs/min64.c`), and the signed
  `long` arithmetic a loop counter of type `long` needs.

  The array lemmas are instances of the index-generic
  `Sep.eval_index_array_int_at` / `Sep.triple_store_index_int_at`; this module
  only supplies the element address `Cop.sem_add` computes for a `long` index
  (`elemOfsL`) and its value over `Z`.
-/
import CCLib.logic.ArrayStore
import CCLib.logic.HoareLong

namespace CC

/-! ## Signed 64-bit arithmetic on `repr` of naturals -/

/-- `Int64.repr` of a non-negative value of the signed range is that value
    (as `toInt`). -/
theorem toInt_repr64 (i : _root_.Int) (h1 : 0 ≤ i) (h2 : i < 9223372036854775808) :
    (Integers.Int64.repr i).toInt = i := by
  show (BitVec.ofInt 64 i).toInt = i
  rw [BitVec.toInt_ofInt, Int.bmod_eq_emod_of_lt (by simp; omega)]
  simp; omega

/-- Signed `<` on `Int64.repr` of two non-negative values of the signed range
    is `<` on `Z`. -/
theorem lt_repr64 (i j : _root_.Int) (hi1 : 0 ≤ i) (hi2 : i < 9223372036854775808)
    (hj1 : 0 ≤ j) (hj2 : j < 9223372036854775808) :
    Integers.Int64.lt (Integers.Int64.repr i) (Integers.Int64.repr j) = decide (i < j) := by
  show BitVec.slt _ _ = _
  rw [BitVec.slt_eq_decide, toInt_repr64 i hi1 hi2, toInt_repr64 j hj1 hj2]

theorem repr64_add (i j : _root_.Int) :
    Integers.Int64.add (Integers.Int64.repr i) (Integers.Int64.repr j)
      = Integers.Int64.repr (i + j) := by
  show BitVec.ofInt 64 i + BitVec.ofInt 64 j = BitVec.ofInt 64 (i + j)
  rw [BitVec.ofInt_add]

section Ops
variable (cenv : CompositeEnv) (m : Mem)

/-- `i < n` at `long`. -/
theorem semBinop_lt_long (x y : Integers.Int64) :
    Cop.semBinaryOperation cenv .Olt (.Vlong x) tlong (.Vlong y) tlong m
      = some (Val.ofBool (Integers.Int64.lt x y)) := rfl

/-- `i + c` with `i : long` and an `int` constant `c`. -/
theorem semBinop_add_long_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vlong x) tlong (.Vint c) tint m
      = some (.Vlong (Integers.Int64.add x (Integers.Int64.repr (Integers.Int.signed c)))) := rfl

/-- `(long) c` for an `int` value `c`. -/
theorem semCast_int_long (c : Integers.Int) :
    Cop.semCast (.Vint c) tint tlong m
      = some (.Vlong (Integers.Int64.repr (Integers.Int.signed c))) := rfl

end Ops

/-! ## The element address for a `long` index -/

/-- The offset `Cop.sem_add` computes for `a + i` with `a : int *` and
    `i : long`. -/
def elemOfsL (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (iv : Integers.Int64) :
    Integers.Ptrofs :=
  Integers.Ptrofs.add ofs0
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv tint)) (Integers.Ptrofs.of_int64 iv))

theorem semAdd_elem_long (cenv : CompositeEnv) (m : Mem) (b : Block)
    (ofs0 : Integers.Ptrofs) (iv : Integers.Int64) :
    Cop.semBinaryOperation cenv .Oadd (.Vptr b ofs0) (tptr tint) (.Vlong iv) tlong m
      = some (.Vptr b (elemOfsL cenv ofs0 iv)) := rfl

private theorem ptr_arith64' (A i : Nat)
    (hno : (A : _root_.Int) + 4 * (i : _root_.Int) < 18446744073709551616) :
    (((A + 4 * ((((i : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat
      : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat % 18446744073709551616)
      % 18446744073709551616 : Nat) : _root_.Int) = (A : _root_.Int) + 4 * (i : _root_.Int) := by
  omega

private theorem no_ovf_le64 (A : _root_.Int) (i n : Nat) (hin : i ≤ n)
    (h : A + 4 * (n : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

/-- Over `Z`, element `i` is at `ofs0 + 4 * i`, given that the array does not
    straddle the end of the address space. -/
theorem elemOfsL_unsigned (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (i : Nat)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int) < 18446744073709551616) :
    Integers.Ptrofs.unsigned (elemOfsL cenv ofs0 (Integers.Int64.repr i))
      = Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int) := by
  have hsz : sizeof cenv tint = 4 := by simp [sizeof, tint]
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  simp only [elemOfsL, hsz, Integers.Ptrofs.of_int64,
             Integers.Ptrofs.add, Integers.Ptrofs.mul, Integers.Ptrofs.unsigned,
             Integers.Ptrofs.repr, Integers.Int64.repr, Integers.MI.add, Integers.MI.mul,
             Integers.MI.repr, Integers.MI.unsigned,
             BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt, hw] at hno ⊢
  have h4 : ((4 : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = 4 := by
    omega
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [h4, h64]
  exact ptr_arith64' _ _ hno

namespace Sep

/-- Evaluating `base[idx]` for an `int` array the fragment owns, with a
    `long` index. -/
theorem eval_index_array_int_long {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Integers.Int} {h : Heap} {base idx : Expr} {i : Nat}
    (hpr : permOrder p .Readable = true)
    (harr : arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (n : _root_.Int) < 18446744073709551616)
    (hptr : EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vlong (Integers.Int64.repr i)))
    (htyb : typeof base = tptr tint) (hty : typeof idx = tlong) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd base idx (tptr tint)) tint) (.Vint (f i)) :=
  eval_index_array_int_at hpr harr hag hi hptr hidx
    (by rw [hty, htyb]; exact semAdd_elem_long _ _ _ _ _)
    (elemOfsL_unsigned ge.genv_cenv ofs0 i (no_ovf_le64 _ i n (by omega) hno))

/-- **Store into an `int` array with a `long` index**: `base[idx] = rhs;`
    replaces element `i` of the array by the value of `rhs`. -/
theorem triple_store_index_int_long (ge : CGenv) (fe : EntryRel) (f : Function)
    (Rl : Env → TempEnv → Prop) (base idx rhs : Expr)
    (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (n i : Nat)
    (g : Nat → Integers.Int) (v : Integers.Int)
    (hpw : permOrder p .Writable = true) (hi : i < n)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (n : _root_.Int) < 18446744073709551616)
    (hbase : ∀ e le m, Rl e le → EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : ∀ e le m, Rl e le → EvalExpr ge e le m idx (.Vlong (Integers.Int64.repr i)))
    (hrhs : ∀ e le m, Rl e le → EvalExpr ge e le m rhs (.Vint v))
    (htyb : typeof base = tptr tint) (hty : typeof idx = tlong) (htyr : typeof rhs = tint) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n g hp)
      (.Sassign (.Ederef (.Ebinop .Oadd base idx (tptr tint)) tint) rhs)
      (.only (fun e le hp => Rl e le
        ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n (fun j => if j = i then v else g j) hp)) :=
  triple_store_index_int_at ge fe f Rl base idx rhs p b ofs0 _ n i g v _ hpw hi hbase hidx hrhs
    (fun m => by rw [hty, htyb]; exact semAdd_elem_long _ _ _ _ _)
    (elemOfsL_unsigned ge.genv_cenv ofs0 i (no_ovf_le64 _ i n (by omega) hno)) htyr

end Sep
end CC
