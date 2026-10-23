/-
  Reading and writing any field `x->fld` of a `struct` through a pointer
  temporary `x`, and the facts about `malloc`ed blocks that initialising a
  `struct` needs (VST's `field_at` / `data_at_` reasoning for `forward` on
  `x->fld = e;` and `y = x->fld;`).

  The struct is described by a `ListLayout` (`CCLib.logic.ListNode`), of which
  only the composite environment, the struct's name and its composite are used
  here: any field with a known offset `delta` can be read or written, not just
  the two fields `ListLayout` names.

  * `eval_field_mapsto`: reading `x->fld` where the fragment owns the field.
  * `triple_store_field`: `x->fld = a;` over an initialised field.
  * `triple_store_field_any`: `x->fld = a;` over raw bytes (a fresh `malloc`).
  * `mallocToken_weakValidPointer`: a `malloc`ed pointer is weakly valid even
    for a zero-sized block, so `if (!p)` is decided.
  * `anyBytes_of_mapsto`: forgetting a field's contents, which `free` needs.
-/
import CCLib.logic.ListNode
import CCLib.logic.ArrayInit

namespace CC
namespace Sep

open HProp

/-- A field's contents can be forgotten: a `mapsto` is `sizeChunk` raw bytes. -/
theorem anyBytes_of_mapsto {chunk : Chunk} {p : Permission} {b : Block} {ofs : _root_.Int}
    {v : Val} {h : Heap} (hm : mapsto chunk p b ofs v h) :
    anyBytes p b ofs (sizeChunkNat chunk) h := by
  have h' := anyBytes_of_bytesPtsTo (pure_sep_elim hm).2
  rwa [length_encodeVal] at h'

/-- The payload of a fresh `malloc` block is a run of `Undef` bytes. -/
theorem mallocPayload_undefBytes {b : Block} {sz : Integers.Ptrofs} :
    mallocPayload b sz = undefBytes .Freeable b 0 (Integers.Ptrofs.unsigned sz).toNat := rfl

/-- **A `malloc`ed pointer is weakly valid.**  The token owns the header cells
    just below the pointer, so the byte before it is valid even when the
    payload is empty. -/
theorem mallocToken_weakValidPointer {b : Block} {sz : Integers.Ptrofs} {h : Heap} {m : Mem}
    (ht : mallocToken b sz h) (hag : Heap.Agrees h m) :
    Mem.weakValidPointer m b 0 = true := by
  obtain ⟨-, hb⟩ := pure_sep_elim ht
  have hr := bytesPtsTo_ownsRange b .Freeable _ _ h hb 7
    (by rw [length_encodeVal]; decide)
  have hv := Heap.agrees_validPointer hag hr
  simp only [Mem.weakValidPointer]
  rw [show (0 : _root_.Int) - 1 = -sizeChunk Mptr + ((7 : Nat) : _root_.Int) from by decide, hv]
  simp

/-- `!x` for a weakly valid pointer `x`: false (`if (!p) exit(…);` after a
    `malloc`). -/
theorem eval_notbool_validptr {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {x : Ident}
    {t : Ty} {b : Block} {o : Integers.Ptrofs} (hle : le.get x = some (.Vptr b o))
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    EvalExpr ge e le m (.Eunop .Onotbool (.Etempvar x (tptr t)) tint) (Val.ofBool false) := by
  refine EvalExpr.Eunop .Onotbool _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) ?_
  simp only [Cop.semUnaryOperation, Cop.semNotbool, typeof]
  rw [show tptr t = Ty.Tpointer t noattr from rfl, boolVal_ptr_valid m b o t noattr hv]
  rfl

section
variable (L : ListLayout) {ge : CGenv} (hcenv : ge.genv_cenv = L.cenv)
include hcenv

/-- **Reading `x->fld`** where the fragment owns the field, at byte `delta` of
    the struct at `x`, in front of a frame `F`. -/
theorem eval_field_mapsto {e : Env} {le : TempEnv} {m : Mem} {x fld : Ident} {delta : _root_.Int}
    {chunk : Chunk} {ty : Ty} {pm : Permission} {b : Block} {o : Integers.Ptrofs} {v : Val}
    {F : HProp} {h : Heap}
    (hoff : fieldOffset L.cenv fld L.co.co_members = .OK (delta, .Full))
    (hd0 : 0 ≤ delta) (hno : Integers.Ptrofs.unsigned o + delta < 18446744073709551616)
    (hacc : accessMode ty = .By_value chunk) (hpr : permOrder pm .Readable = true)
    (hx : le.get x = some (.Vptr b o))
    (hm : (mapsto chunk pm b (Integers.Ptrofs.unsigned o + delta) v ∗ F) h)
    (hag : Heap.Agrees h m)
    (hw : Mem.ChunkNoWrap chunk (Integers.Ptrofs.unsigned o + delta) := by exact Or.inl rfl) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) fld ty)
      (Val.loadResult chunk v) := by
  obtain ⟨h1, h2, hd, rfl, hm1, _⟩ := hm
  exact eval_lvalue_mapsto hacc hpr (lvalue_field L hcenv hx hoff ty)
    (ptrofs_add_nonneg_unsigned o delta hd0 hno) hm1 (Heap.Agrees_union_left hag) hw

/-- **`x->fld = a;`** over an initialised field (at byte `delta` of the struct
    at `x`), in front of a frame `F`: the field afterwards holds the value of
    `a` converted to the field's type. -/
theorem triple_store_field (fe : EntryRel) (f : Function) (E : Env) (l : List (Ident × Val))
    (F : HProp) (x fld : Ident) (delta : _root_.Int) (chunk : Chunk) (ty : Ty) (a : Expr)
    (pm : Permission) (b : Block) (o : Integers.Ptrofs) (vold vnew : Val)
    (hoff : fieldOffset L.cenv fld L.co.co_members = .OK (delta, .Full))
    (hd0 : 0 ≤ delta) (hno : Integers.Ptrofs.unsigned o + delta < 18446744073709551616)
    (hacc : accessMode ty = .By_value chunk) (hpw : permOrder pm .Writable = true)
    (hx : ∀ le, TempsHold l le → le.get x = some (.Vptr b o))
    (ha : ∀ le m, TempsHold l le →
      ∃ v, EvalExpr ge E le m a v ∧ Cop.semCast v (typeof a) ty m = some vnew)
    (hw : Mem.ChunkNoWrap chunk (Integers.Ptrofs.unsigned o + delta) := by exact Or.inl rfl) :
    Triple ge fe f (LocalSt E l (mapsto chunk pm b (Integers.Ptrofs.unsigned o + delta) vold ∗ F))
      (.Sassign (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) fld ty) a)
      (.only (LocalSt E l (mapsto chunk pm b (Integers.Ptrofs.unsigned o + delta) vnew ∗ F))) := by
  have haddr := ptrofs_add_nonneg_unsigned o delta hd0 hno
  refine triple_assign ge fe f _ _ _ _ chunk pm b (Integers.Ptrofs.add o (Integers.Ptrofs.repr delta))
    hpw hacc (fun e le hp m hP _ => ?_) (by rw [haddr]; exact hw)
  obtain ⟨rfl, hT, h1, h2, hd, rfl, hm1, hF⟩ := hP
  refine ⟨vold, vnew, h1, h2, hd, rfl, by rw [haddr]; exact hm1,
    lvalue_field L hcenv (hx le hT) hoff ty, ha le m hT, fun h1' hm' hd' => ⟨rfl, hT, ?_⟩⟩
  exact ⟨h1', h2, hd', rfl, by rw [haddr] at hm'; exact hm', hF⟩

/-- **`x->fld = a;`** over raw bytes (a freshly `malloc`ed struct): the field
    afterwards holds the value of `a` converted to the field's type. -/
theorem triple_store_field_any (fe : EntryRel) (f : Function) (E : Env) (l : List (Ident × Val))
    (F : HProp) (x fld : Ident) (delta : _root_.Int) (chunk : Chunk) (ty : Ty) (a : Expr)
    (pm : Permission) (b : Block) (o : Integers.Ptrofs) (vnew : Val)
    (hoff : fieldOffset L.cenv fld L.co.co_members = .OK (delta, .Full))
    (hd0 : 0 ≤ delta) (hno : Integers.Ptrofs.unsigned o + delta < 18446744073709551616)
    (hal : (Integers.Ptrofs.unsigned o + delta) % alignChunk chunk = 0)
    (hacc : accessMode ty = .By_value chunk) (hpw : permOrder pm .Writable = true)
    (hx : ∀ le, TempsHold l le → le.get x = some (.Vptr b o))
    (ha : ∀ le m, TempsHold l le →
      ∃ v, EvalExpr ge E le m a v ∧ Cop.semCast v (typeof a) ty m = some vnew)
    (hw : Mem.ChunkNoWrap chunk (Integers.Ptrofs.unsigned o + delta) := by exact Or.inl rfl) :
    Triple ge fe f
      (LocalSt E l (anyBytes pm b (Integers.Ptrofs.unsigned o + delta) (sizeChunkNat chunk) ∗ F))
      (.Sassign (.Efield (.Ederef (.Etempvar x L.ptr) L.ty) fld ty) a)
      (.only (LocalSt E l (mapsto chunk pm b (Integers.Ptrofs.unsigned o + delta) vnew ∗ F))) := by
  have haddr := ptrofs_add_nonneg_unsigned o delta hd0 hno
  refine triple_assign_any ge fe f _ _ _ _ chunk pm b
    (Integers.Ptrofs.add o (Integers.Ptrofs.repr delta)) hpw hacc (fun e le hp m hP _ => ?_)
    (by rw [haddr]; exact hw)
  obtain ⟨rfl, hT, h1, h2, hd, rfl, hm1, hF⟩ := hP
  refine ⟨vnew, h1, h2, hd, rfl, by rw [haddr]; exact hm1, by rw [haddr]; exact hal,
    lvalue_field L hcenv (hx le hT) hoff ty, ha le m hT, fun h1' hm' hd' => ⟨rfl, hT, ?_⟩⟩
  exact ⟨h1', h2, hd', rfl, by rw [haddr] at hm'; exact hm', hF⟩

end

end Sep
end CC
