/-
  Linked lists in the separation logic: VST's `lseg` / `listrep`
  (`floyd/list_dt.v`, `progs/verif_reverse.v`).

  The lists are generic in the node predicate: `node b X a u` is the node at
  `b + X` holding the data `a` and the link `u` (the value of its "next"
  field).  `lseg node l x y` is a segment of nodes from `x` to `y` holding the
  elements `l`; `listrep node l x` is a null-terminated list (`lseg … x
  nullval`).  A program instantiates `node` with the field `mapsto`s of its
  `struct` (e.g. `VST.Verif.Reverse.listNode`).

  The rules are the ones VST's list proofs use: unfolding a list at a
  non-null pointer (`listrep_ptr`), a null pointer is the empty list
  (`listrep_null`), and extending a segment by one node at its end
  (`lseg_snoc`).
-/
import CCLib.logic.PtrCompare

namespace CC
namespace Sep

open HProp

section
variable {α : Type} (node : Block → _root_.Int → α → Val → HProp)

/-- `lseg node l x y`: the nodes from `x` to `y` hold the elements `l`. -/
def lseg : List α → Val → Val → HProp
  | [], x, y => ⌜x = y⌝
  | a :: l, x, y => fun h => ∃ b o u, x = .Vptr b o
      ∧ (node b (Integers.Ptrofs.unsigned o) a u ∗ lseg l u y) h

/-- `listrep node l x`: the null-terminated list at `x` holds `l`. -/
def listrep (l : List α) (x : Val) : HProp := lseg node l x Val.Vnullptr

theorem lseg_nil {x y : Val} {h : Heap} : lseg node [] x y h ↔ x = y ∧ h = Heap.emp :=
  Iff.rfl

/-- Two segments joined end to end are a segment. -/
theorem lseg_append (l2 : List α) (y z : Val) :
    ∀ (l1 : List α) (x : Val) (h : Heap),
      (lseg node l1 x y ∗ lseg node l2 y z) h → lseg node (l1 ++ l2) x z h
  | [], x, h, hs => by
    obtain ⟨h1, h2, hd, rfl, ⟨rfl, rfl⟩, hl⟩ := hs
    rw [Heap.emp_union]; exact hl
  | c :: l, x, h, hs => by
    obtain ⟨h12, h3, hd, rfl, ⟨b', o', u', rfl, h1, h2, hd12, rfl, hn', hl⟩, hl2⟩ := hs
    have hd1 : Heap.disjoint h1 h3 := (Heap.disjoint_union_left.mp hd).1
    have hd2 : Heap.disjoint h2 h3 := (Heap.disjoint_union_left.mp hd).2
    exact ⟨b', o', u', rfl, h1, Heap.union h2 h3, Heap.disjoint_union_right.mpr ⟨hd12, hd1⟩,
      Heap.union_assoc _ _ _, hn', lseg_append l2 y z l u' _ ⟨h2, h3, hd2, rfl, hl, hl2⟩⟩

/-- A segment followed by a list is a list. -/
theorem lseg_listrep {l1 l2 : List α} {x y : Val} {h : Heap}
    (hs : (lseg node l1 x y ∗ listrep node l2 y) h) : listrep node (l1 ++ l2) x h :=
  lseg_append node l2 y _ l1 x h hs

/-- Extending a segment by the node its end points to. -/
theorem lseg_snoc (a : α) (u : Val) (b : Block) (o : Integers.Ptrofs) (l : List α) (x : Val)
    (h : Heap) (hs : (lseg node l x (.Vptr b o) ∗ node b (Integers.Ptrofs.unsigned o) a u) h) :
    lseg node (l ++ [a]) x u h := by
  obtain ⟨h1, h2, hd, rfl, hl, hn⟩ := hs
  exact lseg_append node [a] _ u l x _ ⟨h1, h2, hd, rfl, hl, b, o, u, rfl, h2, Heap.emp,
    Heap.disjoint_emp_right _, (Heap.union_emp _).symm, hn, rfl, rfl⟩

/-- The null pointer is the empty list. -/
theorem listrep_null {l : List α} {h : Heap} (hl : listrep node l Val.Vnullptr h) :
    l = [] ∧ h = Heap.emp := by
  cases l with
  | nil => exact ⟨rfl, hl.2⟩
  | cons a l =>
    obtain ⟨b, o, u, hx, _⟩ := hl
    exact absurd hx (by simp [Val.Vnullptr])

/-- A list at a pointer: its first node, and the rest of the list. -/
theorem listrep_ptr {l : List α} {b : Block} {o : Integers.Ptrofs} {h : Heap}
    (hl : listrep node l (.Vptr b o) h) :
    ∃ a l' u, l = a :: l' ∧ (node b (Integers.Ptrofs.unsigned o) a u ∗ listrep node l' u) h := by
  cases l with
  | nil => exact absurd hl.1 (by simp [Val.Vnullptr])
  | cons a l =>
    obtain ⟨b', o', u, hx, hs⟩ := hl
    cases hx
    exact ⟨a, l, u, rfl, hs⟩

/-- Folding the first node back into the list. -/
theorem listrep_cons {a : α} {l : List α} {b : Block} {o : Integers.Ptrofs} {u : Val} {h : Heap}
    (hs : (node b (Integers.Ptrofs.unsigned o) a u ∗ listrep node l u) h) :
    listrep node (a :: l) (.Vptr b o) h :=
  ⟨b, o, u, rfl, hs⟩

/-- A list is either null or a pointer. -/
theorem listrep_val {l : List α} {x : Val} {h : Heap} (hl : listrep node l x h) :
    (x = Val.Vnullptr ∧ l = []) ∨ ∃ b o, x = .Vptr b o ∧ l ≠ [] := by
  cases l with
  | nil => exact Or.inl ⟨hl.1, rfl⟩
  | cons a l =>
    obtain ⟨b, o, u, hx, _⟩ := hl
    exact Or.inr ⟨b, o, hx, List.cons_ne_nil _ _⟩

end

/-! ## Testing a pointer: `while (p)`

`Cop.bool_val` of a pointer asks the memory whether it is (weakly) valid. -/

/-- An owned cell is a weakly valid pointer. -/
theorem Heap.agrees_weakValidPointer {h : Heap} {m : Mem} (hag : Heap.Agrees h m) {b : Block}
    {ofs : _root_.Int} {c : Cell} (hc : h b ofs = some c) :
    Mem.weakValidPointer m b ofs = true := by
  simp [Mem.weakValidPointer, Heap.agrees_validPointer hag hc]

/-- `bool_val` of a valid pointer is `true`. -/
theorem boolVal_ptr_valid (m : Mem) (b : Block) (o : Integers.Ptrofs) (t : Ty) (a : Attr)
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.boolVal (.Vptr b o) (.Tpointer t a) m = some true := by
  simp [Cop.boolVal, Cop.classifyBool, typeconv, removeAttributes, tattr, Archi.ptr64, hv]

/-- `bool_val` of the null pointer is `false`. -/
theorem boolVal_null (m : Mem) (t : Ty) (a : Attr) :
    Cop.boolVal Val.Vnullptr (.Tpointer t a) m = some false := by
  simp [Cop.boolVal, Cop.classifyBool, typeconv, removeAttributes, tattr, Archi.ptr64, Val.Vnullptr]
  rfl

/-- A pointer-to-pointer cast leaves a pointer (or null) unchanged. -/
theorem semCast_ptr_ptr (m : Mem) (v : Val) (t1 t2 : Ty) (a1 a2 : Attr)
    (hv : v = Val.Vnullptr ∨ ∃ b o, v = .Vptr b o) :
    Cop.semCast v (.Tpointer t1 a1) (.Tpointer t2 a2) m = some v := by
  rcases hv with rfl | ⟨b, o, rfl⟩
  · simp [Cop.semCast, Cop.classifyCast, Val.Vnullptr, Archi.ptr64]
  · simp [Cop.semCast, Cop.classifyCast]

/-- `(void *) 0` is the null pointer. -/
theorem semCast_int0_null (m : Mem) :
    Cop.semCast (.Vint (Integers.Int.repr 0)) tint (tptr tvoid) m = some Val.Vnullptr := rfl

/-- A truth value (`0` or `1`) is unchanged by the conversion to `_Bool`. -/
theorem semCast_ofBool_bool (b : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool b) tint tbool m = some (Val.ofBool b) := by
  cases b <;> rfl

/-- The constant `0` is the truth value `false`. -/
theorem zero_eq_ofBool_false : Val.Vint (Integers.Int.repr 0) = Val.ofBool false := rfl

/-! ## Comparing a pointer with `NULL`: `p == NULL`, `p != NULL` -/

/-- `x == NULL` for `x` null or a weakly valid pointer. -/
theorem semBinop_eq_null (cenv : CompositeEnv) (m : Mem) (x : Val) (t1 t2 : Ty) (a1 a2 : Attr)
    (hx : x = Val.Vnullptr ∨ ∃ b o, x = .Vptr b o
      ∧ Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semBinaryOperation cenv .Oeq x (.Tpointer t1 a1) Val.Vnullptr (.Tpointer t2 a2) m
      = some (Val.ofBool (decide (x = Val.Vnullptr))) := by
  rcases hx with rfl | ⟨b, o, rfl, hv⟩
  · simp [Cop.semBinaryOperation, Cop.semCmp, Cop.classifyCmp, Cop.cmpPtr, Val.cmplu_bool,
      Archi.ptr64, Val.Vnullptr]
    rfl
  · have hv' : Val.weakValidPtr (Mem.validPointer m) b (Integers.Ptrofs.unsigned o) = true := hv
    simp [Cop.semBinaryOperation, Cop.semCmp, Cop.classifyCmp, Cop.cmpPtr, Val.cmplu_bool,
      Archi.ptr64, Val.Vnullptr, hv', Val.cmpDifferentBlocks]
    rfl

/-- `x != NULL` for `x` null or a weakly valid pointer. -/
theorem semBinop_ne_null (cenv : CompositeEnv) (m : Mem) (x : Val) (t1 t2 : Ty) (a1 a2 : Attr)
    (hx : x = Val.Vnullptr ∨ ∃ b o, x = .Vptr b o
      ∧ Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semBinaryOperation cenv .One x (.Tpointer t1 a1) Val.Vnullptr (.Tpointer t2 a2) m
      = some (Val.ofBool (!decide (x = Val.Vnullptr))) := by
  rcases hx with rfl | ⟨b, o, rfl, hv⟩
  · simp [Cop.semBinaryOperation, Cop.semCmp, Cop.classifyCmp, Cop.cmpPtr, Val.cmplu_bool,
      Archi.ptr64, Val.Vnullptr]
    rfl
  · have hv' : Val.weakValidPtr (Mem.validPointer m) b (Integers.Ptrofs.unsigned o) = true := hv
    simp [Cop.semBinaryOperation, Cop.semCmp, Cop.classifyCmp, Cop.cmpPtr, Val.cmplu_bool,
      Archi.ptr64, Val.Vnullptr, hv', Val.cmpDifferentBlocks]
    rfl

end Sep
end CC
