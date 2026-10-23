/-
  Filling a raw buffer as an array of `int`s, and handing it back to `free`.

  `malloc` returns raw bytes (`mallocPayload`, a run of `Undef`), and a loop
  then fills the buffer from the front.  The invariant of such a loop is VST's
  `data_at sh (tarray tint n) (map Vint l ++ Zrepeat Vundef (n - i)) p`:
  here, an initialised prefix and a raw suffix,

      arrayU32 p b ofs i g ∗ anyBytes p b (ofs + 4 i) (4 (n - i)).

  `triple_store_index_init` moves the boundary by one cell, and
  `arrayU32_anyBytes` forgets the contents again, which is what `free`
  (`freeSpec`) consumes.  `triple_store_index_int_frame` is the ordinary
  array store of `CCLib.logic.ArrayStore` with a frame next to the array.
-/
import CCLib.logic.Funspec
import CCLib.logic.ArrayStore
import CCLib.logic.Temps
import CCLib.logic.ListRep

namespace CC
open HProp

/-- **Append one element at the end of an `int` array** (the `arrayU32`
    form of `arrayOf_snoc`, oriented as `arrayU16_snoc`). -/
theorem arrayU32_snoc (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f : Nat → Integers.Int) (v : Integers.Int) :
    arrayU32 p b ofs n f ∗ mapsto .Mint32 p b (ofs + 4 * (n : _root_.Int)) (.Vint v)
      = arrayU32 p b ofs (n + 1) (fun j => if j = n then v else f j) := by
  rw [arrayU32_eq_arrayOf p b (n + 1), arrayOf_snoc,
      arrayOf_congr (elt' := u32elt p b f) 4 ofs n
        (fun j hj => by funext off; simp [u32elt, show j ≠ n from by omega]),
      ← arrayU32_eq_arrayOf]
  simp [u32elt]

/-- An array of `int`s is in particular `4 n` owned bytes. -/
theorem arrayU32_anyBytes (p : Permission) (b : Block) :
    ∀ (n : Nat) (f : Nat → Integers.Int) (ofs : _root_.Int) (h : Heap),
      arrayU32 p b ofs n f h → anyBytes p b ofs (4 * n) h := by
  intro n
  induction n with
  | zero =>
      intro f ofs h harr
      show anyBytes p b ofs 0 h
      rw [anyBytes_zero]
      exact harr
  | succ k ih =>
      intro f ofs h harr
      obtain ⟨h1, h2, hd, heq, hm, hr⟩ := harr
      rw [show 4 * (k + 1) = 4 + 4 * k from by omega, anyBytes_split]
      refine ⟨h1, h2, hd, heq, ?_, ?_⟩
      · have h4 := anyBytes_of_bytesPtsTo (pure_sep_elim hm).2
        rwa [length_encodeVal] at h4
      · rw [show ofs + ((4 : Nat) : _root_.Int) = ofs + 4 from by omega]
        exact ih _ _ _ hr

/-- The payload of a fresh `malloc` block is raw bytes. -/
theorem mallocPayload_anyBytes {b : Block} {sz : Integers.Ptrofs} {h : Heap}
    (hp : Sep.mallocPayload b sz h) :
    anyBytes .Freeable b 0 (Integers.Ptrofs.unsigned sz).toNat h := by
  have h' := anyBytes_of_bytesPtsTo hp
  rwa [List.length_replicate] at h'

/-- A non-empty run of owned bytes makes its start a weakly valid pointer
    (what `if (!p)` needs to know about a `malloc`ed `p`). -/
theorem anyBytes_weakValidPointer {p : Permission} {b : Block} {ofs : _root_.Int} {n : Nat}
    {h : Heap} {m : Mem} (hh : anyBytes p b ofs n h) (hn : 0 < n) (hag : Heap.Agrees h m) :
    Mem.weakValidPointer m b ofs = true := by
  obtain ⟨bytes, hb⟩ := hh
  obtain ⟨hlen, hbytes⟩ := pure_sep_elim hb
  have hc := bytesPtsTo_ownsRange b p bytes ofs h hbytes 0 (by omega)
  rw [show ofs + ((0 : Nat) : _root_.Int) = ofs from by omega] at hc
  exact Sep.Heap.agrees_weakValidPointer hag hc

namespace Sep

private theorem ofs_succ (A : _root_.Int) (i : Nat) :
    A + 4 * (i : _root_.Int) + ((4 : Nat) : _root_.Int) = A + 4 * ((i + 1 : Nat) : _root_.Int) := by
  push_cast; omega

private theorem ofs_align (A : _root_.Int) (i : Nat) (h : A % 4 = 0) :
    (A + 4 * (i : _root_.Int)) % 4 = 0 := by omega

private theorem no_ovf_le' (A : _root_.Int) (i n : Nat) (hin : i ≤ n)
    (h : A + 4 * (n : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

/-- **Store into the first raw cell of a partly filled `int` array.**
    `base[idx] = rhs;` at the boundary index `i` writes the value of `rhs` there
    and moves the boundary one cell up.  `base`, `idx` and `rhs` are evaluated
    from the temporaries only. -/
theorem triple_store_index_init (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (base idx rhs : Expr) (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (n i : Nat)
    (g : Nat → Integers.Int) (v : Integers.Int)
    (hpw : permOrder p .Writable = true) (hi : i < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (n : _root_.Int) < 18446744073709551616)
    (hal : Integers.Ptrofs.unsigned ofs0 % 4 = 0)
    (hbase : ∀ le m, TempsHold l le → EvalExpr ge E le m base (.Vptr b ofs0))
    (hidx : ∀ le m, TempsHold l le → EvalExpr ge E le m idx (.Vint (Integers.Int.repr i)))
    (hrhs : ∀ le m, TempsHold l le → EvalExpr ge E le m rhs (.Vint v))
    (htyb : typeof base = tptr tint) (hty : typeof idx = tint) (htyr : typeof rhs = tint) :
    Triple ge fe f
      (LocalSt E l ((arrayU32 p b (Integers.Ptrofs.unsigned ofs0) i g
          ∗ anyBytes p b (Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int)) (4 * (n - i)))
        ∗ R))
      (.Sassign (.Ederef (.Ebinop .Oadd base idx (tptr tint)) tint) rhs)
      (.only (LocalSt E l
        ((arrayU32 p b (Integers.Ptrofs.unsigned ofs0) (i + 1) (fun j => if j = i then v else g j)
          ∗ anyBytes p b (Integers.Ptrofs.unsigned ofs0 + 4 * ((i + 1 : Nat) : _root_.Int))
              (4 * (n - (i + 1))))
        ∗ R))) := by
  have haddr := elemOfs_unsigned ge.genv_cenv ofs0 i (by omega) (no_ovf_le' _ i n (by omega) hno)
  -- the cell at the boundary comes out in front
  have hpre : ((arrayU32 p b (Integers.Ptrofs.unsigned ofs0) i g
          ∗ anyBytes p b (Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int)) (4 * (n - i)))
        ∗ R)
      = anyBytes p b (Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int)) 4
        ∗ ((arrayU32 p b (Integers.Ptrofs.unsigned ofs0) i g
            ∗ anyBytes p b (Integers.Ptrofs.unsigned ofs0 + 4 * ((i + 1 : Nat) : _root_.Int))
                (4 * (n - (i + 1)))) ∗ R) := by
    rw [show 4 * (n - i) = 4 + 4 * (n - (i + 1)) from by omega, anyBytes_split,
      ofs_succ,
      sep_left_comm_eq, sep_assoc_eq]
  -- and goes back as the last element of the prefix
  have hpost : (mapsto .Mint32 p b (Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int)) (.Vint v)
        ∗ ((arrayU32 p b (Integers.Ptrofs.unsigned ofs0) i g
            ∗ anyBytes p b (Integers.Ptrofs.unsigned ofs0 + 4 * ((i + 1 : Nat) : _root_.Int))
                (4 * (n - (i + 1)))) ∗ R))
      = ((arrayU32 p b (Integers.Ptrofs.unsigned ofs0) (i + 1) (fun j => if j = i then v else g j)
          ∗ anyBytes p b (Integers.Ptrofs.unsigned ofs0 + 4 * ((i + 1 : Nat) : _root_.Int))
              (4 * (n - (i + 1))))
        ∗ R) := by
    rw [← arrayU32_snoc, ← sep_assoc_eq, ← sep_assoc_eq, sep_comm_eq (mapsto _ _ _ _ _),
      sep_assoc_eq (arrayU32 _ _ _ _ _), sep_comm_eq (mapsto _ _ _ _ _), ← sep_assoc_eq,
      sep_assoc_eq]
  refine triple_assign_any ge fe f _ _ _ _ .Mint32 p b (elemOfs ge.genv_cenv ofs0
    (Integers.Int.repr i)) hpw rfl (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  rw [hpre] at hH
  obtain ⟨hc, hrest, hdcr, rfl, hc', hrest'⟩ := hH
  refine ⟨.Vint v, hc, hrest, hdcr, rfl, by rw [haddr]; exact hc', ?_, ?_, ?_, ?_⟩
  · rw [haddr]
    exact ofs_align _ i hal
  · exact EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (hbase le m hT)
      (hidx le m hT) (by rw [hty, htyb]; exact semAdd_elem_int _ _ _ _ _))
  · exact ⟨.Vint v, hrhs le m hT, by rw [htyr]; exact semCast_int m v⟩
  · intro hc'' hm hd
    refine ⟨rfl, hT, ?_⟩
    rw [← hpost]
    rw [haddr] at hm
    exact ⟨hc'', hrest, hd, rfl, hm, hrest'⟩


/-- **Store into an `int` array next to a frame** — `triple_store_index_int`
    with the array as the first of two separated parts. -/
theorem triple_store_index_int_frame (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (base idx rhs : Expr) (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (n i : Nat)
    (g : Nat → Integers.Int) (v : Integers.Int)
    (hpw : permOrder p .Writable = true) (hi : i < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (n : _root_.Int) < 18446744073709551616)
    (hbase : ∀ le m, TempsHold l le → EvalExpr ge E le m base (.Vptr b ofs0))
    (hidx : ∀ le m, TempsHold l le → EvalExpr ge E le m idx (.Vint (Integers.Int.repr i)))
    (hrhs : ∀ le m, TempsHold l le → EvalExpr ge E le m rhs (.Vint v))
    (htyb : typeof base = tptr tint) (hty : typeof idx = tint) (htyr : typeof rhs = tint) :
    Triple ge fe f
      (LocalSt E l (arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n g ∗ R))
      (.Sassign (.Ederef (.Ebinop .Oadd base idx (tptr tint)) tint) rhs)
      (.only (LocalSt E l
        (arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n (fun j => if j = i then v else g j)
          ∗ R))) := by
  have haddr := elemOfs_unsigned ge.genv_cenv ofs0 i (by omega) (no_ovf_le' _ i n (by omega) hno)
  refine triple_assign ge fe f _ _ _ _ .Mint32 p b
    (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i)) hpw rfl (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  rw [arrayU32_split p b _ n g i hi, sep_assoc_eq] at hH
  obtain ⟨h1, h2, hd12, rfl, hm1, hrest⟩ := hH
  refine ⟨.Vint (g i), .Vint v, h1, h2, hd12, rfl, by rw [haddr]; exact hm1, ?_, ?_, ?_⟩
  · exact EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (hbase le m hT)
      (hidx le m hT) (by rw [hty, htyb]; exact semAdd_elem_int _ _ _ _ _))
  · exact ⟨.Vint v, hrhs le m hT, by rw [htyr]; exact semCast_int m v⟩
  · intro h1' hm1' hd1'
    refine ⟨rfl, hT, ?_⟩
    rw [arrayU32_update p b _ n g i v hi, sep_assoc_eq]
    rw [haddr] at hm1'
    exact ⟨h1', h2, hd1', rfl, hm1', hrest⟩

end Sep
end CC
