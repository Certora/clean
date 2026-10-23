/-
  Pointer comparison in the separation logic.

  Clight compares two pointers (`p == q`, `p != q`) with `Cop.cmp_ptr`, which
  requires both pointers to be valid in the current memory
  (`Mem.valid_pointer`, or `weak_valid_pointer` when they point into the same
  block).  Here validity comes from ownership: a cell owned by a fragment that
  agrees with the memory is valid (`Heap.agrees_validPointer`), and a `mapsto`
  owns its first byte (`mapsto_owns`).

  `semBinop_eq_ptr` evaluates `==` on two valid
  pointers to VST's `if eq_dec p q then 1 else 0`.
-/
import CCLib.logic.SepLogic
import CCLib.cfrontend.Cop
import CCLib.lib.IntegersLemmas

namespace CC

open HProp

/-- An owned cell is a valid pointer of a memory the fragment agrees with. -/
theorem Heap.agrees_validPointer {h : Heap} {m : Mem} (hag : Heap.Agrees h m) {b : Block}
    {ofs : Z} {c : Cell} (hc : h b ofs = some c) : Mem.validPointer m b ofs = true :=
  Mem.perm_implies (Heap.Agrees_perm hag hc .Cur) (by cases c.perm <;> rfl)

/-- A `mapsto` owns the first byte it points to. -/
theorem mapsto_owns {chunk : Chunk} {p : Permission} {b : Block} {ofs : Z} {v : Val} {h : Heap}
    (hm : mapsto chunk p b ofs v h) : ∃ c, h b ofs = some c := by
  obtain ⟨h1, h2, _, rfl, ⟨_, rfl⟩, hb⟩ := hm
  have hr := bytesPtsTo_ownsRange b p _ ofs h2 hb 0
    (by rw [length_encodeVal]; cases chunk <;> decide)
  rw [Int.ofNat_zero, Int.add_zero] at hr
  exact ⟨_, hr⟩

/-- A fragment owning a cell, inside a larger one, still owns it. -/
theorem Heap.union_owns_left {h1 h2 : Heap} {b : Block} {ofs : Z} {c : Cell}
    (hc : h1 b ofs = some c) : ∃ c', Heap.union h1 h2 b ofs = some c' :=
  ⟨c, Heap.union_of_left hc⟩

theorem Heap.union_owns_right {h1 h2 : Heap} {b : Block} {ofs : Z} {c : Cell}
    (hc : h2 b ofs = some c) : ∃ c', Heap.union h1 h2 b ofs = some c' := by
  unfold Heap.union
  cases h1 b ofs with
  | some c' => exact ⟨c', rfl⟩
  | none => exact ⟨c, hc⟩

/-- `p == q` on two valid pointers (both of pointer type): `1` if they are
    equal, `0` otherwise. -/
theorem semBinop_eq_ptr (cenv : CompositeEnv) (m : Mem) (b1 b2 : Block)
    (o1 o2 : Integers.Ptrofs) (t1 t2 : Ty) (a1 a2 : Attr)
    (hv1 : Mem.validPointer m b1 (Integers.Ptrofs.unsigned o1) = true)
    (hv2 : Mem.validPointer m b2 (Integers.Ptrofs.unsigned o2) = true) :
    Cop.semBinaryOperation cenv .Oeq (.Vptr b1 o1) (.Tpointer t1 a1) (.Vptr b2 o2)
        (.Tpointer t2 a2) m
      = some (.Vint (if Val.Vptr b1 o1 = Val.Vptr b2 o2 then Integers.Int.one
                     else Integers.Int.zero)) := by
  have hcl : Cop.classifyCmp (.Tpointer t1 a1) (.Tpointer t2 a2) = .pp := rfl
  simp only [Cop.semBinaryOperation, Cop.semCmp, hcl, Cop.cmpPtr, Archi.ptr64, if_true,
    Val.cmplu_bool, Bool.not_true, Bool.false_eq_true, if_false, Val.weakValidPtr, hv1, hv2,
    Bool.true_or, Bool.and_self]
  by_cases hb : b1 = b2
  · subst hb
    by_cases ho : o1 = o2
    · subst ho
      simp [Integers.Ptrofs.cmpu, Integers.MI.cmpu, Integers.MI.eq_true, Val.ofBool, Val.Vtrue]
    · have : Integers.MI.eq o1 o2 = false := by
        cases h : Integers.MI.eq o1 o2
        · rfl
        · exact absurd ((Integers.MI.eq_spec _ _).mp h) ho
      simp only [Integers.Ptrofs.cmpu, Integers.MI.cmpu, this]
      simp [ho, Val.ofBool, Val.Vfalse]
  · simp [hb, Val.cmpDifferentBlocks, Val.ofBool, Val.Vfalse]

end CC
