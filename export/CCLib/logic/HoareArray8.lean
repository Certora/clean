/-
  Arrays of 8-byte scalars in the separation logic, generic in the memory
  chunk (`Mint64` for `long`, `Mfloat64` for `double`).

  `array8 chunk p b ofs n v` is VST's `data_at sh (tarray ty n) vl (b, ofs)`
  for an element type `ty` of size 8 accessed by value through `chunk`: the
  `n` values `v 0 … v (n-1)`, 8 bytes apart from `b + ofs`, as an `arrayOf`
  (`CCLib.logic.Aggregate`) of `chunk` cells.  `eval_index8` reads element
  `i` through `base[idx]`, `triple_store_index8` writes it.

  The `double` arrays (`CCLib.logic.HoareArrayDouble`) and the `long` arrays
  (`CCLib.logic.HoareArrayL64`) are the two instances.
-/
import CCLib.logic.Aggregate
import CCLib.logic.ExactTempsHeap

namespace CC
namespace Sep

open HProp

/-- The cell of element `i` of an array of `chunk` values `v`, at byte
    offset `off`. -/
def cell8 (chunk : Chunk) (p : Permission) (b : Block) (v : Nat → Val) :
    Nat → _root_.Int → HProp :=
  fun i off => mapsto chunk p b off (v i)

/-- `data_at sh (tarray ty n) vl (b, ofs)` for an 8-byte element type `ty`
    accessed through `chunk`. -/
def array8 (chunk : Chunk) (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (v : Nat → Val) : HProp :=
  arrayOf (cell8 chunk p b v) 8 ofs n

/-- An 8-byte element type: accessed by value through an 8-byte `chunk`. -/
structure Elem8 (ty : Ty) (chunk : Chunk) : Prop where
  acc : accessMode ty = .By_value chunk
  size : ∀ cenv, sizeof cenv ty = 8
  chunk_size : sizeChunk chunk = 8

/-- The address of element `i` of an array of 8-byte elements that fits in
    the address space. -/
theorem idxOfs8 {ty : Ty} (hsz : ∀ cenv, sizeof cenv ty = 8) (cenv : CompositeEnv)
    (si : Signedness) (ofs0 : Integers.Ptrofs) {n i : Nat} (hi : i < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616) :
    Integers.Ptrofs.unsigned
      (idxOfs cenv ty si ofs0 (Integers.Int.repr (i : _root_.Int)))
        = Integers.Ptrofs.unsigned ofs0 + 8 * (i : _root_.Int) := by
  have := idxOfs_unsigned cenv ty si ofs0 i 8 (hsz _) (by omega) (by zomega) (by zomega)
  simpa using this

/-- An element of such an array does not wrap around the address space. -/
theorem noWrap8 {chunk : Chunk} (hch : sizeChunk chunk = 8) (ofs0 : Integers.Ptrofs)
    {n i : Nat} (hi : i < n)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616) :
    Mem.ChunkNoWrap chunk (Integers.Ptrofs.unsigned ofs0 + 8 * (i : _root_.Int)) := by
  refine Or.inr ?_
  rw [Mem.ptrofs_modulus_eq, hch]
  zomega

/-- Updating element `i` of an array: the new array is the new cell next to
    the rest of the old one. -/
theorem array8_update (chunk : Chunk) (p : Permission) (b : Block) (ofs : _root_.Int)
    (n i : Nat) (v v' : Nat → Val) (hi : i < n)
    (hagree : ∀ j, j < n → j ≠ i → v' j = v j) :
    array8 chunk p b ofs n v'
      = mapsto chunk p b (ofs + 8 * (i : _root_.Int)) (v' i)
        ∗ arrayOfRest (cell8 chunk p b v) 8 ofs n i :=
  arrayOf_update _ _ 8 ofs n i hi (fun j hj hne => by unfold cell8; rw [hagree j hj hne])

/-- Evaluating `base[idx]` for an array of 8-byte elements the fragment
    owns: the value is element `i` (normalized by `loadResult`). -/
theorem eval_index8 {ty : Ty} {chunk : Chunk} (hel : Elem8 ty chunk)
    {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {v : Nat → Val} {h : Heap} {base idx : Expr} {i : Nat} {si : Signedness}
    (hpr : permOrder p .Readable = true)
    (harr : array8 chunk p b (Integers.Ptrofs.unsigned ofs0) n v h)
    (hag : Heap.Agrees h m) (hi : i < n)
    (hptr : EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx) = .pi ty si)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616) :
    EvalExpr ge e le m (.Ederef (.Ebinop .Oadd base idx (tptr ty)) ty)
      (Val.loadResult chunk (v i)) := by
  rw [array8, arrayOf_split _ _ _ _ _ hi] at harr
  obtain ⟨h1, hm, hag1⟩ := sep_left_agrees harr hag
  exact eval_lvalue_mapsto (a := .Ederef (.Ebinop .Oadd base idx (tptr ty)) ty)
    hel.acc hpr (eval_index_lvalue hptr hidx hcls) (idxOfs8 hel.size _ si ofs0 hi hn hno) hm hag1
    (noWrap8 hel.chunk_size ofs0 hi hno)

/-- **Store into an array of 8-byte elements**, next to a frame `F`:
    `base[idx] = rhs;` replaces element `i` by the value `x` of `rhs` cast to
    the element type.  `base`, `idx` and `rhs` are evaluated from the locals
    described by `Rl` (they do not read the heap). -/
theorem triple_store_index8 {ty : Ty} {chunk : Chunk} (hel : Elem8 ty chunk)
    (ge : CGenv) (fe : EntryRel) (f : Function)
    (Rl : Env → TempEnv → Prop) (F : HProp) (base idx rhs : Expr) (si : Signedness)
    (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (n i : Nat)
    (v : Nat → Val) (v2 x : Val)
    (hpw : permOrder p .Writable = true) (hi : i < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 8 * (n : _root_.Int) ≤ 18446744073709551616)
    (hbase : ∀ e le m, Rl e le → EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : ∀ e le m, Rl e le → EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hrhs : ∀ e le m, Rl e le → EvalExpr ge e le m rhs v2)
    (hcast : ∀ m, Cop.semCast v2 (typeof rhs) ty m = some x)
    (hcls : Cop.classifyAdd (typeof base) (typeof idx) = .pi ty si) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ (array8 chunk p b (Integers.Ptrofs.unsigned ofs0) n v ∗ F) hp)
      (.Sassign (.Ederef (.Ebinop .Oadd base idx (tptr ty)) ty) rhs)
      (.only (fun e le hp => Rl e le
        ∧ (array8 chunk p b (Integers.Ptrofs.unsigned ofs0) n
            (fun j => if j = i then x else v j) ∗ F) hp)) := by
  have haddr := idxOfs8 hel.size ge.genv_cenv si ofs0 hi hn hno
  refine triple_assign ge fe f _ _ _ _ chunk p b
    (idxOfs ge.genv_cenv ty si ofs0 (Integers.Int.repr (i : _root_.Int))) hpw hel.acc ?_
    (by rw [haddr]; exact noWrap8 hel.chunk_size ofs0 hi hno)
  intro e le hp m hP _
  obtain ⟨hR, harr⟩ := hP
  rw [array8, arrayOf_split _ _ _ _ _ hi, sep_assoc_eq] at harr
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := harr
  refine ⟨v i, x, h1, h2, hd12, heq, by rw [haddr]; exact hm1,
    eval_index_lvalue (hbase e le m hR) (hidx e le m hR) hcls,
    ⟨v2, hrhs e le m hR, hcast m⟩, ?_⟩
  intro h1' hm1' hd1'
  refine ⟨hR, ?_⟩
  rw [array8_update chunk p b _ n i v _ hi (fun j _ hne => if_neg hne), sep_assoc_eq]
  refine ⟨h1', h2, hd1', rfl, ?_, hrest⟩
  rw [haddr] at hm1'
  simpa using hm1'

end Sep
end CC
