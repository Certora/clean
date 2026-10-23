/-
  Arrays of `long`s (64-bit integers) in the separation logic.

  `arrayL64 p b ofs n f` is VST's `data_at sh (tarray tlong n)
  (map Vlong fl) (b, ofs)`: the `n` longs `f 0 … f (n-1)`, 8 bytes apart from
  `b + ofs`, the instance of the generic 8-byte arrays
  `CCLib.logic.HoareArray8` at `Mint64`.  `arrayVL64` holds arbitrary values
  (VST's `data_at_` when they are undefined).  The `semCast` lemmas are the
  `long ↔ int` conversions of `Cop`.
-/
import CCLib.logic.HoareArray8
import CCLib.logic.HoareArrayLong

namespace CC
namespace Sep

open HProp

/-- `data_at sh (tarray tlong n) vl (b, ofs)`, for arbitrary values `vl`. -/
abbrev arrayVL64 (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat) (v : Nat → Val) :
    HProp :=
  array8 .Mint64 p b ofs n v

/-- `data_at sh (tarray tlong n) (map Vlong fl) (b, ofs)` -/
def arrayL64 (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Integers.Int64) : HProp :=
  arrayVL64 p b ofs n (fun i => .Vlong (f i))

theorem sizeof_tlong (cenv : CompositeEnv) : sizeof cenv tlong = 8 := by
  simp [sizeof, tlong]

/-- `long` is an 8-byte element type. -/
theorem elem8_tlong : Elem8 tlong .Mint64 :=
  ⟨rfl, sizeof_tlong, rfl⟩

/-- Evaluating `base[idx]` for a `long` array the fragment owns. -/
theorem eval_index_l64 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Integers.Int64} {h : Heap} {base idx : Expr} {i : Nat}
    (hpr : permOrder p .Readable = true)
    (harr : arrayL64 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n)
    (hptr : EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx) = .pi tlong .Signed)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616) :
    EvalExpr ge e le m (.Ederef (.Ebinop .Oadd base idx (tptr tlong)) tlong)
      (.Vlong (f i)) :=
  eval_index8 elem8_tlong (v := fun i => .Vlong (f i)) hpr harr hag hi hptr hidx hcls hn hno

/-- `(int) x` for a `long` value `x`: the low 32 bits. -/
theorem semCast_long_int (m : Mem) (x : Integers.Int64) :
    Cop.semCast (.Vlong x) tlong tint m
      = some (.Vint (Integers.Int.repr (Integers.Int64.unsigned x))) := rfl

/-- The low 32 bits of a `long` are those of its signed value. -/
theorem int_repr_unsigned64 (x : Integers.Int64) :
    Integers.Int.repr (Integers.Int64.unsigned x) = Integers.Int.repr (Integers.Int64.signed x) := by
  unfold Integers.Int.repr Integers.Int64.unsigned Integers.Int64.signed
  simp only [Integers.MI.repr, Integers.MI.unsigned, Integers.MI.signed]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> omega

theorem semCast_long_long (m : Mem) (x : Integers.Int64) :
    Cop.semCast (.Vlong x) tlong tlong m = some (.Vlong x) := rfl

/-- **Store into a `long` array**, next to a frame `F`: `base[idx] = rhs;`
    replaces element `i` by the value of `rhs`.  `base`, `idx` and `rhs` are
    evaluated from the locals described by `Rl` (they do not read the heap). -/
theorem triple_store_index_l64 (ge : CGenv) (fe : EntryRel) (f : Function)
    (Rl : Env → TempEnv → Prop) (F : HProp) (base idx rhs : Expr)
    (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (n i : Nat)
    (v : Nat → Val) (x : Integers.Int64)
    (hpw : permOrder p .Writable = true) (hi : i < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616)
    (hbase : ∀ e le m, Rl e le → EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : ∀ e le m, Rl e le → EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hrhs : ∀ e le m, Rl e le → EvalExpr ge e le m rhs (.Vlong x))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx) = .pi tlong .Signed)
    (htyr : typeof rhs = tlong) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ (arrayVL64 p b (Integers.Ptrofs.unsigned ofs0) n v ∗ F) hp)
      (.Sassign (.Ederef (.Ebinop .Oadd base idx (tptr tlong)) tlong) rhs)
      (.only (fun e le hp => Rl e le
        ∧ (arrayVL64 p b (Integers.Ptrofs.unsigned ofs0) n
            (fun j => if j = i then .Vlong x else v j) ∗ F) hp)) :=
  triple_store_index8 elem8_tlong ge fe f Rl F base idx rhs .Signed p b ofs0 n i v _ _ hpw hi
    hn hno hbase hidx hrhs (fun m => by rw [htyr]; exact semCast_long_long m x) hcls

end Sep
end CC
