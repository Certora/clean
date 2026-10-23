/-
  The nodes of a singly linked list of 32-bit integers in C:

      struct list { int head; struct list *tail; };   // or `unsigned head`

  (VST's `list_cell` / `listspec` for such a struct, as in `progs/reverse.c`
  and `progs/append.c`.)  On the 64-bit target the `head` field is at offset 0
  and the `tail` pointer at offset 8; `ListLayout` packages the struct's name,
  field names and composite environment with the facts about the offsets
  that a program's composite environment proves by `decide`.

  `listNode p b X a u` is the node at `b + X` with `head = a`, `tail = u`,
  inside the address space (VST's `field_compatible`); with it `listrep
  (listNode p)` (`CCLib.logic.ListRep`) is VST's `lseg LS sh l x nullval`.
  The rules: reading `x->head` and `x->tail` (`eval_head`, `eval_tail`), and
  writing `x->tail = y` (`triple_store_tail`).
-/
import CCLib.logic.ListRep
import CCLib.logic.ExactTempsHeap

namespace CC
namespace Sep

open HProp

/-- `(void *) 0` evaluates to the null pointer. -/
theorem eval_null_cast {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} :
    EvalExpr ge e le m (.Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid))
      Val.Vnullptr :=
  EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ tint) (semCast_int0_null m)

/-- A `struct` with an `int`-sized `head` at offset 0 and a `tail` pointer at
    offset 8, in the composite environment `cenv`. -/
structure ListLayout where
  cenv : CompositeEnv
  sid : Ident
  head : Ident
  tail : Ident
  co : Composite
  get_co : cenv.get sid = some co
  off_head : fieldOffset cenv head co.co_members = .OK (0, .Full)
  off_tail : fieldOffset cenv tail co.co_members = .OK (8, .Full)

/-- `struct sid` -/
abbrev ListLayout.ty (L : ListLayout) : Ty := .Tstruct L.sid noattr
/-- `struct sid *` -/
abbrev ListLayout.ptr (L : ListLayout) : Ty := tptr L.ty

/-- The node at `b + X`: `head = a`, `tail = u`. -/
def listNode (p : Permission) (b : Block) (X : _root_.Int) (a : Integers.Int) (u : Val) : HProp :=
  ⌜X + 16 ≤ 18446744073709551616⌝ ∗ mapsto .Mint32 p b X (.Vint a) ∗ mapsto .Mint64 p b (X + 8) u

theorem listNode_head_front (p : Permission) (b : Block) (X : _root_.Int) (a : Integers.Int)
    (u : Val) (F : HProp) :
    (listNode p b X a u ∗ F) = mapsto .Mint32 p b X (.Vint a)
      ∗ (⌜X + 16 ≤ 18446744073709551616⌝ ∗ mapsto .Mint64 p b (X + 8) u ∗ F) := by
  rw [listNode, sep_assoc_eq, sep_assoc_eq, sep_left_comm_eq]

theorem listNode_tail_front (p : Permission) (b : Block) (X : _root_.Int) (a : Integers.Int)
    (u : Val) (F : HProp) :
    (listNode p b X a u ∗ F) = mapsto .Mint64 p b (X + 8) u
      ∗ (⌜X + 16 ≤ 18446744073709551616⌝ ∗ mapsto .Mint32 p b X (.Vint a) ∗ F) := by
  rw [listNode, sep_assoc_eq, sep_assoc_eq, sep_left_comm_eq (mapsto .Mint32 p b X _),
    sep_left_comm_eq]

/-- A link is null or a pointer (VST's `is_pointer_or_null`). -/
def IsLink (u : Val) : Prop := u = Val.Vnullptr ∨ ∃ b o, u = .Vptr b o

theorem isLink_of_listrep {α : Type} {node : Block → _root_.Int → α → Val → HProp}
    {l : List α} {u : Val} {h : Heap} (hl : listrep node l u h) : IsLink u := by
  rcases listrep_val _ hl with ⟨rfl, _⟩ | ⟨b, o, rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨b, o, rfl⟩

/-- A non-empty list next to a frame: its first node, the rest of the list,
    the frame. -/
theorem listrep_cons_front {α : Type} {node : Block → _root_.Int → α → Val → HProp}
    {a : α} {c : List α} {x : Val} {F : HProp} {h : Heap} (hl : (listrep node (a :: c) x ∗ F) h) :
    ∃ b o u, x = .Vptr b o ∧ IsLink u
      ∧ (node b (Integers.Ptrofs.unsigned o) a u ∗ (listrep node c u ∗ F)) h := by
  obtain ⟨h1, h2, hd, rfl, hl, hF⟩ := hl
  obtain ⟨b, o, u, rfl, hs⟩ := hl
  refine ⟨b, o, u, rfl, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, hl'⟩ := hs
    exact isLink_of_listrep hl'
  · rw [← sep_assoc_eq]
    exact ⟨_, _, hd, rfl, hs, hF⟩

theorem loadResult_link {u : Val} (hu : IsLink u) : Val.loadResult .Mint64 u = u := by
  rcases hu with rfl | ⟨b, o, rfl⟩ <;> rfl

/-- A node makes its address a valid pointer. -/
theorem node_valid {p : Permission} {b : Block} {X : _root_.Int} {a : Integers.Int} {u : Val}
    {F : HProp} {h : Heap} {m : Mem} (hn : (listNode p b X a u ∗ F) h) (hag : Heap.Agrees h m) :
    Mem.weakValidPointer m b X = true := by
  rw [listNode_head_front] at hn
  obtain ⟨h1, h2, hd, rfl, hm, _⟩ := hn
  obtain ⟨c, hc⟩ := mapsto_owns hm
  exact Heap.agrees_weakValidPointer (Heap.Agrees_union_left hag) hc

/-! ## Reading and writing the fields -/

section
variable (L : ListLayout) {ge : CGenv} (hcenv : ge.genv_cenv = L.cenv)
include hcenv

/-- `x->fld` as an l-value. -/
theorem lvalue_field {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {b : Block}
    {o : Integers.Ptrofs} (hx : le.get x = some (.Vptr b o)) {fld : Ident} {delta : Z}
    (hoff : fieldOffset L.cenv fld L.co.co_members = .OK (delta, .Full)) (ty : Ty) :
    EvalLvalue ge e le m (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) fld ty) b
      (Integers.Ptrofs.add o (Integers.Ptrofs.repr delta)) .Full :=
  EvalLvalue.Efield_struct _ fld ty b o L.sid L.co noattr delta .Full
    (EvalExpr.Elvalue _ b o .Full _ (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ hx))
      (DerefLoc.copy rfl))
    rfl (hcenv ▸ L.get_co) (hcenv ▸ hoff)

/-- `x->head`, read at an `int`-sized type `ty`. -/
theorem eval_head {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {p : Permission} {b : Block}
    {o : Integers.Ptrofs} {a : Integers.Int} {u : Val} {F : HProp} {h : Heap} {ty : Ty}
    (hty : accessMode ty = .By_value .Mint32)
    (hpr : permOrder p .Readable = true) (hx : le.get x = some (.Vptr b o))
    (hn : (listNode p b (Integers.Ptrofs.unsigned o) a u ∗ F) h) (hag : Heap.Agrees h m) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) L.head ty) (.Vint a) := by
  rw [listNode_head_front] at hn
  obtain ⟨h1, h2, hd, rfl, hm, hrest⟩ := hn
  have hno := (pure_sep_elim hrest).1
  exact eval_lvalue_mapsto (chunk := .Mint32) (v := .Vint a) hty hpr
    (lvalue_field L hcenv hx L.off_head ty)
    (by simpa using ptrofs_add_nonneg_unsigned o 0 (by omega) (by zomega)) hm
    (Heap.Agrees_union_left hag)

/-- `x->tail` -/
theorem eval_tail {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {p : Permission} {b : Block}
    {o : Integers.Ptrofs} {a : Integers.Int} {u : Val} {F : HProp} {h : Heap}
    (hpr : permOrder p .Readable = true) (hx : le.get x = some (.Vptr b o)) (hu : IsLink u)
    (hn : (listNode p b (Integers.Ptrofs.unsigned o) a u ∗ F) h) (hag : Heap.Agrees h m) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) L.tail L.ptr) u := by
  rw [listNode_tail_front] at hn
  obtain ⟨h1, h2, hd, rfl, hm, hrest⟩ := hn
  have hno := (pure_sep_elim hrest).1
  have := eval_lvalue_mapsto (e := e) (chunk := .Mint64) (v := u) rfl hpr
    (lvalue_field L hcenv hx L.off_tail L.ptr)
    (ptrofs_add_nonneg_unsigned o 8 (by omega) (by zomega)) hm (Heap.Agrees_union_left hag)
  rwa [loadResult_link hu] at this

/-- **`x->tail = a;`** for any right-hand side `a` that evaluates (after the
    conversion to the link type) to the link `w`, next to a frame `F`; the
    temporaries are described by `Rl`. -/
theorem triple_store_tail_expr (fe : EntryRel) (f : Function) (Rl : Env → TempEnv → Prop)
    (F : HProp) (x : Ident) (a : Expr) (p : Permission) (b : Block) (o : Integers.Ptrofs)
    (av : Integers.Int) (u w : Val) (hpw : permOrder p .Writable = true)
    (hx : ∀ e le, Rl e le → le.get x = some (.Vptr b o))
    (ha : ∀ e le m, Rl e le →
      ∃ v, EvalExpr ge e le m a v ∧ Cop.semCast v (typeof a) L.ptr m = some w) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ (listNode p b (Integers.Ptrofs.unsigned o) av u ∗ F) hp)
      (.Sassign (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) L.tail L.ptr) a)
      (.only (fun e le hp => Rl e le
        ∧ (listNode p b (Integers.Ptrofs.unsigned o) av w ∗ F) hp)) := by
  refine triple_assign ge fe f _ _ _ _ .Mint64 p b
    (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8)) hpw rfl (fun e le hp m hP _ => ?_)
  obtain ⟨hR, hH⟩ := hP
  rw [listNode_tail_front] at hH
  obtain ⟨h1, h2, hd, rfl, hm, hrest⟩ := hH
  have hno := (pure_sep_elim hrest).1
  have haddr : Integers.Ptrofs.unsigned (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8))
      = Integers.Ptrofs.unsigned o + 8 := ptrofs_add_nonneg_unsigned o 8 (by omega) (by zomega)
  refine ⟨u, w, h1, h2, hd, rfl, by rw [haddr]; exact hm,
    lvalue_field L hcenv (hx e le hR) L.off_tail L.ptr, ha e le m hR,
    fun h1' hm' hd' => ⟨hR, ?_⟩⟩
  rw [listNode_tail_front]
  exact ⟨h1', h2, hd', rfl, by rw [haddr] at hm'; exact hm', hrest⟩

/-- **`x->tail = y;`**: the node's link becomes the value of `y` (a link),
    next to a frame `F`; the temporaries are described by `Rl`. -/
theorem triple_store_tail (fe : EntryRel) (f : Function) (Rl : Env → TempEnv → Prop) (F : HProp)
    (x y : Ident) (p : Permission) (b : Block) (o : Integers.Ptrofs) (a : Integers.Int)
    (u w : Val) (hpw : permOrder p .Writable = true)
    (hx : ∀ e le, Rl e le → le.get x = some (.Vptr b o))
    (hy : ∀ e le, Rl e le → le.get y = some w) (hw : IsLink w) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ (listNode p b (Integers.Ptrofs.unsigned o) a u ∗ F) hp)
      (.Sassign (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) L.tail L.ptr) (.Etempvar y L.ptr))
      (.only (fun e le hp => Rl e le
        ∧ (listNode p b (Integers.Ptrofs.unsigned o) a w ∗ F) hp)) :=
  triple_store_tail_expr L hcenv fe f Rl F x _ p b o a u w hpw hx
    (fun e le m hR => ⟨w, EvalExpr.Etempvar _ _ _ (hy e le hR), semCast_ptr_ptr m w _ _ _ _ hw⟩)

/-- **`x->tail = NULL;`** (`NULL` written `(void *) 0`). -/
theorem triple_store_tail_null (fe : EntryRel) (f : Function) (Rl : Env → TempEnv → Prop)
    (F : HProp) (x : Ident) (p : Permission) (b : Block) (o : Integers.Ptrofs)
    (a : Integers.Int) (u : Val) (hpw : permOrder p .Writable = true)
    (hx : ∀ e le, Rl e le → le.get x = some (.Vptr b o)) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ (listNode p b (Integers.Ptrofs.unsigned o) a u ∗ F) hp)
      (.Sassign (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) L.tail L.ptr)
        (.Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))
      (.only (fun e le hp => Rl e le
        ∧ (listNode p b (Integers.Ptrofs.unsigned o) a Val.Vnullptr ∗ F) hp)) :=
  triple_store_tail_expr L hcenv fe f Rl F x _ p b o a u _ hpw hx
    (fun _ _ m _ => ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ tint) (semCast_int0_null m),
      semCast_ptr_ptr m _ _ _ _ _ (Or.inl rfl)⟩)

end

end Sep
end CC
