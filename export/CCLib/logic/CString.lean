/-
  C strings (VST's `cstring`): a byte buffer of non-zero characters followed
  by a terminating `0`, read through a `size_t` (`unsigned long`) index, as in
  the string functions of VST's `progs/strlib.c`.

  The bytes are those of `CC.arrayU8` (`CCLib.logic.HoareLong`), so this
  module only adds the address `Cop.sem_add` computes for `str + i` with an
  `unsigned long` index (`byteOfsL`), the read `str[i]`, and the comparison
  of a character with `0`.
-/
import CCLib.logic.HoareArrayLong

namespace CC

open HProp

/-! ## `str + i` with an `unsigned long` index -/

/-- The offset `Cop.sem_add` computes for `buf + i` at element type
    `unsigned char` and a 64-bit index `i`. -/
def byteOfsL (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (iv : Integers.Int64) :
    Integers.Ptrofs :=
  Integers.Ptrofs.add ofs0
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv tuchar)) (Integers.Ptrofs.of_int64 iv))

theorem semAdd_byte_ulong (cenv : CompositeEnv) (m : Mem) (b : Block)
    (ofs0 : Integers.Ptrofs) (iv : Integers.Int64) :
    Cop.semBinaryOperation cenv .Oadd (.Vptr b ofs0) (tptr tuchar) (.Vlong iv) tulong m
      = some (.Vptr b (byteOfsL cenv ofs0 iv)) := rfl

private theorem byte_arith64 (A i : Nat) (hno : A + i < 18446744073709551616) :
    (((A + 1 * ((((i : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat
      : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat % 18446744073709551616)
      % 18446744073709551616 : Nat) : _root_.Int) = (A : _root_.Int) + (i : _root_.Int) := by
  omega

/-- Over `Z`, byte `i` is at `ofs0 + i`, given that the buffer does not
    straddle the end of the address space. -/
theorem byteOfsL_unsigned (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (i : Nat)
    (hno : ofs0.toNat + i < 18446744073709551616) :
    Integers.Ptrofs.unsigned (byteOfsL cenv ofs0 (Integers.Int64.repr i))
      = Integers.Ptrofs.unsigned ofs0 + (i : _root_.Int) := by
  have hsz : sizeof cenv tuchar = 1 := by simp [sizeof, tuchar]
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  simp only [byteOfsL, hsz, Integers.Ptrofs.of_int64,
             Integers.Ptrofs.add, Integers.Ptrofs.mul, Integers.Ptrofs.unsigned,
             Integers.Ptrofs.repr, Integers.Int64.repr, Integers.MI.add, Integers.MI.mul,
             Integers.MI.repr, Integers.MI.unsigned,
             BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt, hw]
  have h1 : ((1 : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = 1 := by
    omega
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [h1, h64]
  exact byte_arith64 _ _ hno

/-- Reading `str[i]` out of an owned byte buffer, with an `unsigned long`
    index `i`. -/
theorem eval_index_bytes_ulong {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Nat} {h : Heap} {idx : Expr} {i : Nat} {pid : Ident}
    (hpr : permOrder p .Readable = true)
    (harr : arrayU8 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n) (hb : ∀ j, f j < 256)
    (hptr : le.get pid = some (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vlong (Integers.Int64.repr i)))
    (hty : typeof idx = tulong)
    (hno : ofs0.toNat + i < 18446744073709551616) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr tuchar)) idx (tptr tuchar)) tuchar)
      (.Vint (Integers.Int.repr ((f i : Nat)))) := by
  have hadd : Cop.semBinaryOperation ge.genv_cenv .Oadd (.Vptr b ofs0) (tptr tuchar)
                (.Vlong (Integers.Int64.repr i)) (typeof idx) m
              = some (.Vptr b (byteOfsL ge.genv_cenv ofs0 (Integers.Int64.repr i))) := by
    rw [hty]; exact semAdd_byte_ulong _ _ _ _ _
  refine EvalExpr.Elvalue _ b (byteOfsL ge.genv_cenv ofs0 (Integers.Int64.repr i)) .Full _
    (EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop .Oadd _ _ _ (.Vptr b ofs0) (.Vlong (Integers.Int64.repr i)) _
        (EvalExpr.Etempvar pid (tptr tuchar) _ hptr) hidx hadd)) ?_
  refine DerefLoc.value .Mint8unsigned _ rfl ?_
  rw [Mem.loadv_ptr _ _ _ _ (Or.inl rfl), byteOfsL_unsigned ge.genv_cenv ofs0 i hno]
  exact arrayU8_load p b hpr n f i hi hb _ h m harr hag

/-! ## Characters and the `size_t` counter -/

section Ops
variable (cenv : CompositeEnv) (m : Mem)

/-- `c == 0` for an `unsigned char` `c` against an `int` constant. -/
theorem semBinop_eq_uchar_int (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tuchar (.Vint y) tint m
      = some (Val.ofBool (Integers.Int.eq x y)) := rfl

/-- `i + c` with `i : size_t` and an `int` constant `c`. -/
theorem semBinop_add_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vlong x) tulong (.Vint c) tint m
      = some (.Vlong (Integers.Int64.add x (Integers.Int64.repr (Integers.Int.signed c)))) := rfl

end Ops

/-- 32-bit equality of two byte-sized naturals. -/
theorem int_eq_nat32 (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    Integers.Int.eq (Integers.Int.repr ((a : _root_.Int))) (Integers.Int.repr ((b : _root_.Int)))
      = decide (a = b) :=
  cmpu_eq_nat32 a b ha hb

/-- `x == a` for an `unsigned char` temporary `x` holding the byte `d` and an
    `int` expression `a` evaluating to the byte `c`. -/
theorem eval_eq_uchar {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {a : Expr} {x : Ident}
    {d c : Nat} (hd : d < 256) (hc : c < 256)
    (hev : EvalExpr ge e le m a (.Vint (Integers.Int.repr (c : _root_.Int))))
    (hta : typeof a = tint) (hx : le.get x = some (.Vint (Integers.Int.repr (d : _root_.Int)))) :
    EvalExpr ge e le m (.Ebinop .Oeq (.Etempvar x tuchar) a tint) (Val.ofBool (decide (d = c))) :=
  EvalExpr.Ebinop .Oeq _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx) hev (by
    simp only [typeof] at hta ⊢
    rw [hta, semBinop_eq_uchar_int, int_eq_nat32 d c (by omega) (by omega)])

/-- `x < y` for two `unsigned char` temporaries holding the bytes `d1`, `d2`. -/
theorem eval_lt_uchar {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {x y : Ident}
    {d1 d2 : Nat} (h1 : d1 < 256) (h2 : d2 < 256)
    (hx : le.get x = some (.Vint (Integers.Int.repr (d1 : _root_.Int))))
    (hy : le.get y = some (.Vint (Integers.Int.repr (d2 : _root_.Int)))) :
    EvalExpr ge e le m (.Ebinop .Olt (.Etempvar x tuchar) (.Etempvar y tuchar) tint)
      (Val.ofBool (decide (d1 < d2))) :=
  EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx) (EvalExpr.Etempvar _ _ _ hy) (by
    show some (Val.ofBool (Integers.Int.lt (Integers.Int.repr (d1 : _root_.Int))
      (Integers.Int.repr (d2 : _root_.Int)))) = _
    rw [lt_repr _ _ (by omega) (by omega) (by omega) (by omega)]
    simp)

/-- `x > y` for two `unsigned char` temporaries holding the bytes `d1`, `d2`. -/
theorem eval_gt_uchar {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {x y : Ident}
    {d1 d2 : Nat} (h1 : d1 < 256) (h2 : d2 < 256)
    (hx : le.get x = some (.Vint (Integers.Int.repr (d1 : _root_.Int))))
    (hy : le.get y = some (.Vint (Integers.Int.repr (d2 : _root_.Int)))) :
    EvalExpr ge e le m (.Ebinop .Ogt (.Etempvar x tuchar) (.Etempvar y tuchar) tint)
      (Val.ofBool (decide (d2 < d1))) :=
  EvalExpr.Ebinop .Ogt _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx) (EvalExpr.Etempvar _ _ _ hy) (by
    show some (Val.ofBool (Integers.Int.lt (Integers.Int.repr (d2 : _root_.Int))
      (Integers.Int.repr (d1 : _root_.Int)))) = _
    rw [lt_repr _ _ (by omega) (by omega) (by omega) (by omega)]
    simp)

/-- `(unsigned char) x` for a byte `x` (stored in an `unsigned char`). -/
theorem semCast_uchar_byte (m : Mem) (x : Nat) (hx : x < 256) :
    Cop.semCast (.Vint (Integers.Int.repr (x : _root_.Int))) tuchar tuchar m
      = some (.Vint (Integers.Int.repr (x : _root_.Int))) := by
  show some (Val.Vint (Integers.Int.zero_ext 8 (Integers.Int.repr (x : _root_.Int)))) = _
  rw [zero_ext8_repr _ hx]

/-! ## `cstring` -/

/-- VST's `cstring sh s p`: the characters `s` (bytes, none of them `0`),
    then a terminating `0`, at `b + X`. -/
def cstring (p : Permission) (b : Block) (X : Z) (s : List Nat) : HProp :=
  ⌜∀ c ∈ s, 0 < c ∧ c < 256⌝ ∗ arrayU8 p b X (s.length + 1) (fun i => s.getD i 0)

/-- The bytes of a C string are bytes. -/
theorem cstring_byte {s : List Nat} (hs : ∀ c ∈ s, 0 < c ∧ c < 256) (j : Nat) :
    s.getD j 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : s[j]? with
  | none => simp
  | some c => exact (hs c (List.mem_of_getElem? h)).2

/-- Character `i` of a C string is `0` exactly at the end. -/
theorem cstring_zero_iff {s : List Nat} (hs : ∀ c ∈ s, 0 < c ∧ c < 256) {i : Nat}
    (hi : i ≤ s.length) : s.getD i 0 = 0 ↔ i = s.length := by
  rw [List.getD_eq_getElem?_getD]
  constructor
  · intro h0
    refine (Nat.lt_or_eq_of_le hi).resolve_left fun hlt => ?_
    rw [List.getElem?_eq_getElem hlt] at h0
    exact absurd h0 (Nat.pos_iff_ne_zero.mp (hs _ (List.getElem_mem hlt)).1)
  · rintro rfl
    simp

/-- Two lists of characters with the same length and the same characters
    are equal. -/
theorem list_eq_of_getD {s1 s2 : List Nat} (hl : s1.length = s2.length)
    (h : ∀ j < s1.length, s1.getD j 0 = s2.getD j 0) : s1 = s2 := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2] at this

end CC
