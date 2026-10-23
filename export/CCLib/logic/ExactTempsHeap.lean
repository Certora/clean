/-
  Straight-line code over an exactly known local state that owns memory.

  `CCLib.logic.ExactTemps` describes the local state of a function without
  addressable locals by the exact temporary environment `L` (`At L`), with an
  empty heap fragment.  `AtH L H` is the same with a heap fragment satisfying
  `H` — the shape of the VST tests whose functions read or write memory passed
  by pointer or held in globals (`verif_field_loadstore`, `verif_store_demo`,
  `verif_load_demo`).  This file has the rules for that shape, and the
  pointer-offset arithmetic the address computations of such functions need.
-/
import CCLib.logic.SepHoare
import CCLib.logic.ExactTemps
import CCLib.logic.HoareArray

namespace CC
namespace Sep

open HProp

/-! ## Pointer offsets -/

/-- `Ptrofs.add` of a non-negative offset that does not wrap around. -/
theorem ptrofs_add_nonneg_unsigned (o : Integers.Ptrofs) (d : _root_.Int) (hd : 0 ≤ d)
    (h : Integers.Ptrofs.unsigned o + d < 18446744073709551616) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add o (Integers.Ptrofs.repr d))
      = Integers.Ptrofs.unsigned o + d := by
  have hu : Integers.Ptrofs.unsigned o = (o.toNat : _root_.Int) := rfl
  have := ptrofs_add_unsigned o d.toNat (by rw [hu] at h; zomega)
  rwa [Int.toNat_of_nonneg hd] at this

/-- `Ptrofs.add` of a negative offset `-d` that does not wrap around. -/
theorem ptrofs_add_neg_unsigned (o : Integers.Ptrofs) (d : _root_.Int) (hd : 0 ≤ d)
    (h : d ≤ Integers.Ptrofs.unsigned o) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add o (Integers.Ptrofs.repr (-d)))
      = Integers.Ptrofs.unsigned o - d := by
  have hr := Integers.Ptrofs.unsigned_range_2 o
  rw [← Integers.Ptrofs.neg_repr, ← Integers.Ptrofs.sub_add_opp, Integers.Ptrofs.sub_unsigned,
    Integers.Ptrofs.unsigned_repr (z := d) hd (by zomega)]
  exact Integers.Ptrofs.unsigned_repr (by zomega) (by zomega)

/-! ## Rules -/

section
variable (ge : CGenv) (fe : EntryRel) (f : Function)

/-- `x = a;` where `a` evaluates to `v` in `L`, given the fragment, over any
    exactly known local environment `e0`. -/
theorem triple_set_atE (e0 : Env) (L : TempEnv) (H : HProp) (id : Ident) (a : Expr) (v : Val)
    (hev : ∀ m hp, H hp → Heap.Agrees hp m → EvalExpr ge e0 L m a v) :
    Triple ge fe f (AtE e0 L H) (.Sset id a) (.only (AtE e0 (L.set id v) H)) :=
  triple_set ge fe f _ _ _ _ (fun e le hp m hP hag => by
    obtain ⟨rfl, rfl, hH⟩ := hP
    exact ⟨v, hev m hp hH hag, rfl, rfl, hH⟩)

/-- `x = a;` where `a` evaluates to `v` in `L`, given the fragment. -/
theorem triple_set_atH (L : TempEnv) (H : HProp) (id : Ident) (a : Expr) (v : Val)
    (hev : ∀ m hp, H hp → Heap.Agrees hp m → EvalExpr ge emptyEnv L m a v) :
    Triple ge fe f (AtH L H) (.Sset id a) (.only (AtH (L.set id v) H)) :=
  triple_set_atE ge fe f emptyEnv L H id a v hev

/-- `return a;` where `a` evaluates to `v` in `L`, converted to the return
    type as `v'`; the fragment is returned to the caller. -/
theorem triple_return_atH (L : TempEnv) (H : HProp) (a : Expr) (v v' : Val)
    (hev : ∀ m hp, H hp → Heap.Agrees hp m → EvalExpr ge emptyEnv L m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) f.fn_return m = some v') :
    Triple ge fe f (AtH L H) (.Sreturn (some a))
      { normal := Assn.no, brk := Assn.no, cont := Assn.no,
        ret := fun r hp => r = v' ∧ H hp } := by
  refine triple_return ge fe f _ _ _ (fun e le hp m h hag => ?_)
  obtain ⟨rfl, rfl, hH⟩ := h
  exact ⟨v, v', m, hp, hev m hp hH hag, hcast m, freeList_emptyEnv _ _, ⟨rfl, hH⟩,
    fun _ hdj hag => ⟨hdj, hag⟩⟩

/-- `a1 = a2;` where `a1` designates the first cell of the fragment
    (`mapsto … ∗ F`), over any exactly known local environment `e0`. -/
theorem triple_assign_atE_front (e0 : Env) (L : TempEnv) (F : HProp) (a1 a2 : Expr)
    (chunk : Chunk) (perm : Permission) (b : Block) (Fo : Integers.Ptrofs) (X : _root_.Int)
    (vold vnew v2 : Val)
    (hpw : permOrder perm .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (hX : Integers.Ptrofs.unsigned Fo = X)
    (hlv : ∀ m, EvalLvalue ge e0 L m a1 b Fo .Full)
    (hev : ∀ m, EvalExpr ge e0 L m a2 v2)
    (hcast : ∀ m, Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew)
    (hw : Mem.ChunkNoWrap chunk X := by exact Or.inl rfl) :
    Triple ge fe f (AtE e0 L (mapsto chunk perm b X vold ∗ F)) (.Sassign a1 a2)
      (.only (AtE e0 L (mapsto chunk perm b X vnew ∗ F))) := by
  subst hX
  refine triple_assign ge fe f _ _ a1 a2 chunk perm b Fo hpw hacc
    (fun e le hp m hP _ => ?_) hw
  obtain ⟨rfl, rfl, h1, h2, hd, rfl, hm, hF⟩ := hP
  exact ⟨vold, vnew, h1, h2, hd, rfl, hm, hlv m, ⟨v2, hev m, hcast m⟩,
    fun h1' hm' hd' => ⟨rfl, rfl, h1', h2, hd', rfl, hm', hF⟩⟩

/-- `a1 = a2;` where the fragment is the single cell `a1` designates, over any
    exactly known local environment `e0`. -/
theorem triple_assign_atE (e0 : Env) (L : TempEnv) (a1 a2 : Expr) (chunk : Chunk)
    (perm : Permission) (b : Block) (F : Integers.Ptrofs) (X : _root_.Int) (vold vnew v2 : Val)
    (hpw : permOrder perm .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (hX : Integers.Ptrofs.unsigned F = X)
    (hlv : ∀ m, EvalLvalue ge e0 L m a1 b F .Full)
    (hev : ∀ m, EvalExpr ge e0 L m a2 v2)
    (hcast : ∀ m, Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew)
    (hw : Mem.ChunkNoWrap chunk X := by exact Or.inl rfl) :
    Triple ge fe f (AtE e0 L (mapsto chunk perm b X vold)) (.Sassign a1 a2)
      (.only (AtE e0 L (mapsto chunk perm b X vnew))) := by
  subst hX
  refine triple_assign ge fe f _ _ a1 a2 chunk perm b F hpw hacc
    (fun e le hp m hP _ => ?_) hw
  obtain ⟨rfl, rfl, hm⟩ := hP
  exact ⟨vold, vnew, hp, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm, hm,
    hlv m, ⟨v2, hev m, hcast m⟩, fun h1' hm' _ => ⟨rfl, rfl, by rw [Heap.union_emp]; exact hm'⟩⟩

/-- `a1 = a2;` where the fragment is the single cell `a1` designates. -/
theorem triple_assign_at (L : TempEnv) (a1 a2 : Expr) (chunk : Chunk) (perm : Permission)
    (b : Block) (F : Integers.Ptrofs) (X : _root_.Int) (vold vnew v2 : Val)
    (hpw : permOrder perm .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (hX : Integers.Ptrofs.unsigned F = X)
    (hlv : ∀ m, EvalLvalue ge emptyEnv L m a1 b F .Full)
    (hev : ∀ m, EvalExpr ge emptyEnv L m a2 v2)
    (hcast : ∀ m, Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew)
    (hw : Mem.ChunkNoWrap chunk X := by exact Or.inl rfl) :
    Triple ge fe f (AtH L (mapsto chunk perm b X vold)) (.Sassign a1 a2)
      (.only (AtH L (mapsto chunk perm b X vnew))) :=
  triple_assign_atE ge fe f emptyEnv L a1 a2 chunk perm b F X vold vnew v2 hpw hacc hX hlv hev
    hcast hw

end

/-- Reading a scalar through an l-value the fragment owns: `a` designates
    the cell `b + X`, which holds `v`. -/
theorem eval_lvalue_mapsto {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {a : Expr}
    {chunk : Chunk} {pm : Permission} {b : Block} {F : Integers.Ptrofs} {X : _root_.Int}
    {v : Val} {h : Heap}
    (hacc : accessMode (typeof a) = .By_value chunk)
    (hpr : permOrder pm .Readable = true)
    (hlv : EvalLvalue ge e le m a b F .Full)
    (hX : Integers.Ptrofs.unsigned F = X)
    (hm : mapsto chunk pm b X v h) (hag : Heap.Agrees h m)
    (hw : Mem.ChunkNoWrap chunk X := by exact Or.inl rfl) :
    EvalExpr ge e le m a (Val.loadResult chunk v) := by
  subst hX
  refine EvalExpr.Elvalue _ b F .Full _ hlv (DerefLoc.value chunk _ hacc ?_)
  rw [Mem.loadv_ptr _ _ _ _ hw]
  exact mapsto_load hpr hm hag

/-- The left part of a `∗` agrees with the memory the whole agrees with. -/
theorem sep_left_agrees {P Q : HProp} {h : Heap} {m : Mem} (hs : (P ∗ Q) h)
    (hag : Heap.Agrees h m) : ∃ h1, P h1 ∧ Heap.Agrees h1 m := by
  obtain ⟨h1, h2, _, rfl, hP, _⟩ := hs
  exact ⟨h1, hP, Heap.Agrees_union_left hag⟩

/-- The right part of a `∗` agrees with the memory the whole agrees with. -/
theorem sep_right_agrees {P Q : HProp} {h : Heap} {m : Mem} (hs : (P ∗ Q) h)
    (hag : Heap.Agrees h m) : ∃ h2, Q h2 ∧ Heap.Agrees h2 m := by
  obtain ⟨h1, h2, hd, rfl, _, hQ⟩ := hs
  exact ⟨h2, hQ, Heap.Agrees_union_right hd hag⟩

/-- A writable permission is readable. -/
theorem readable_of_writable {perm : Permission} (h : permOrder perm .Writable = true) :
    permOrder perm .Readable = true := by
  revert h; cases perm <;> decide

end Sep
end CC
