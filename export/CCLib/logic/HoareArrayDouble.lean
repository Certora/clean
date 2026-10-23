/-
  Arrays of `double`s in the separation logic.

  `arrayF64 p b ofs n f` is VST's `data_at sh (tarray tdouble n)
  (map Vfloat fl) (b, ofs)`: the `n` doubles `f 0 … f (n-1)`, 8 bytes apart
  from `b + ofs`, the instance of the generic 8-byte arrays
  `CCLib.logic.HoareArray8` at `Mfloat64`.  `eval_index_f64` reads element `i` through `base[idx]`, and the
  `semBinop_*_double` lemmas are the IEEE-754 operations of `Cop` on
  `double` operands (`Floats.Float.add` …, i.e. the exact model
  `CCLib.lib.FloatModel`).
-/
import CCLib.logic.HoareArray8

namespace CC
namespace Sep

open HProp

/-- `data_at sh (tarray tdouble n) vl (b, ofs)`, for arbitrary values `vl`
    (e.g. `data_at_`, whose elements are undefined). -/
abbrev arrayV64 (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat) (v : Nat → Val) : HProp :=
  array8 .Mfloat64 p b ofs n v

/-- `data_at sh (tarray tdouble n) (map Vfloat fl) (b, ofs)` -/
def arrayF64 (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Floats.Float) : HProp :=
  arrayV64 p b ofs n (fun i => .Vfloat (f i))

theorem sizeof_tdouble (cenv : CompositeEnv) : sizeof cenv tdouble = 8 := by
  simp [sizeof, tdouble]

/-- `double` is an 8-byte element type. -/
theorem elem8_tdouble : Elem8 tdouble .Mfloat64 :=
  ⟨rfl, sizeof_tdouble, rfl⟩

/-- Evaluating `base[idx]` for a `double` array the fragment owns. -/
theorem eval_index_f64 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Floats.Float} {h : Heap} {base idx : Expr} {i : Nat}
    (hpr : permOrder p .Readable = true)
    (harr : arrayF64 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n)
    (hptr : EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx) = .pi tdouble .Signed)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616) :
    EvalExpr ge e le m (.Ederef (.Ebinop .Oadd base idx (tptr tdouble)) tdouble)
      (.Vfloat (f i)) :=
  eval_index8 elem8_tdouble (v := fun i => .Vfloat (f i)) hpr harr hag hi hptr hidx hcls hn hno

theorem semBinop_add_double (cenv : CompositeEnv) (m : Mem) (x y : Floats.Float) :
    Cop.semBinaryOperation cenv .Oadd (.Vfloat x) tdouble (.Vfloat y) tdouble m
      = some (.Vfloat (Floats.Float.add x y)) := by
  rfl

theorem semBinop_mul_double (cenv : CompositeEnv) (m : Mem) (x y : Floats.Float) :
    Cop.semBinaryOperation cenv .Omul (.Vfloat x) tdouble (.Vfloat y) tdouble m
      = some (.Vfloat (Floats.Float.mul x y)) := by
  rfl

theorem semCast_double_double (m : Mem) (x : Floats.Float) :
    Cop.semCast (.Vfloat x) tdouble tdouble m = some (.Vfloat x) := by
  simp [Cop.semCast, Cop.classifyCast, tdouble]

/-- **Store into a `double` array**, next to a frame `F`: `base[idx] = rhs;`
    replaces element `i` by the value of `rhs`.  `base`, `idx` and `rhs` are
    evaluated from the locals described by `Rl` (they do not read the heap). -/
theorem triple_store_index_f64 (ge : CGenv) (fe : EntryRel) (f : Function)
    (Rl : Env → TempEnv → Prop) (F : HProp) (base idx rhs : Expr)
    (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (n i : Nat)
    (v : Nat → Val) (x : Floats.Float)
    (hpw : permOrder p .Writable = true) (hi : i < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616)
    (hbase : ∀ e le m, Rl e le → EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : ∀ e le m, Rl e le → EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hrhs : ∀ e le m, Rl e le → EvalExpr ge e le m rhs (.Vfloat x))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx) = .pi tdouble .Signed)
    (htyr : typeof rhs = tdouble) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ (arrayV64 p b (Integers.Ptrofs.unsigned ofs0) n v ∗ F) hp)
      (.Sassign (.Ederef (.Ebinop .Oadd base idx (tptr tdouble)) tdouble) rhs)
      (.only (fun e le hp => Rl e le
        ∧ (arrayV64 p b (Integers.Ptrofs.unsigned ofs0) n
            (fun j => if j = i then .Vfloat x else v j) ∗ F) hp)) :=
  triple_store_index8 elem8_tdouble ge fe f Rl F base idx rhs .Signed p b ofs0 n i v _ _ hpw hi
    hn hno hbase hidx hrhs (fun m => by rw [htyr]; exact semCast_double_double m x) hcls

end Sep
end CC
