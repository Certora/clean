/-
  **64-bit unsigned arithmetic for the program logic**, plus a byte-array
  assertion.

  `HoareArray.lean` gave the bridge between `Nat`/`Int` reasoning and Clight's
  32-bit *signed* `tint` arithmetic, which is what `is_sorted` needed.  zlib
  needs the other half: almost everything in it is `unsigned long` (`tulong`,
  64-bit here) and `unsigned` (`tuint`), read out of `unsigned char` buffers
  (`tuchar`).  This file supplies

  * a `Nat` ↔ `Integers.Int64` bridge (`u64_*`), including the mask/shift facts
    that C code uses to pack two 16-bit halves into one word;
  * `Cop.semBinaryOperation` reduction lemmas at `tulong`/`tuint`/`tuchar`, in
    the automation-friendly style of `HoareArray.semBinop_*`;
  * `arrayU8`, the byte-buffer analogue of `arrayU32`, with its load lemma.

  All of it is generic; nothing here mentions adler32.
-/
import CCLib.logic.SepHoare
import CCLib.logic.HoareArray

namespace CC
open Integers

/-! ## `Nat` ↔ 64-bit unsigned

The pattern is the one `HoareArray` established: state every lemma so that the
`Nat` side uses *fresh* `Nat` binders.  A goal phrased with `Int64.unsigned`
sits at `CC.Z`, where `omega` is blind (see the standing note in the plan), so
these lemmas exist to rewrite `unsigned` away rather than to reason under it. -/

theorem u64_toNat (n : Nat) (h : n < 18446744073709551616) :
    (Int64.repr ((n : _root_.Int))).toNat = n := by
  show (BitVec.ofInt 64 ((n : _root_.Int))).toNat = n
  rw [BitVec.toNat_ofInt]
  omega

theorem u64_unsigned (n : Nat) (h : n < 18446744073709551616) :
    Int64.unsigned (Int64.repr ((n : _root_.Int))) = (n : _root_.Int) := by
  show (((Int64.repr ((n : _root_.Int))).toNat : _root_.Int)) = (n : _root_.Int)
  rw [u64_toNat n h]

/-- Every lemma below goes through this normal form: a `Nat`-valued 64-bit word
    is `BitVec.ofNat`, whose `toNat` is `· % 2^64` by a core simp lemma.

    NOTE the `Integers.` qualification throughout: Lean core has its own
    `Int64`, and `Int64.add` would resolve to *that* one. -/
theorem u64_repr_ofNat (n : Nat) :
    Integers.Int64.repr ((n : _root_.Int)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofInt 64 ((n : _root_.Int))).toNat = _
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem u64_toNat_repr (n : Nat) :
    (Integers.Int64.repr ((n : _root_.Int))).toNat = n % 18446744073709551616 := by
  rw [u64_repr_ofNat, BitVec.toNat_ofNat]

theorem u64_add (a b : Nat) :
    Integers.Int64.add (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr ((b : _root_.Int)))
      = Integers.Int64.repr (((a + b : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show (_ + _ : BitVec 64).toNat = _
  rw [BitVec.toNat_add, u64_toNat_repr, u64_toNat_repr, u64_toNat_repr]
  omega

theorem u64_sub (a b : Nat) (h : b ≤ a) :
    Integers.Int64.sub (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr ((b : _root_.Int)))
      = Integers.Int64.repr (((a - b : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show (_ - _ : BitVec 64).toNat = _
  rw [BitVec.toNat_sub, u64_toNat_repr, u64_toNat_repr, u64_toNat_repr]
  omega

/-! ### Masks and shifts

C code that packs two half-words into one (`adler | (sum2 << 16)`, and the
inverse `(adler >> 16) & 0xffff`) needs these three plus `u64_or_pack`. -/

private theorem two64 : (18446744073709551616 : Nat) = 2 ^ 64 := by rfl

theorem u64_and_mask (a k : Nat) (hk : k <= 64) :
    Integers.Int64.and (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr (((2 ^ k - 1 : Nat) : _root_.Int)))
      = Integers.Int64.repr (((a % 2 ^ k : Nat) : _root_.Int)) := by
  have hdvd : (2 : Nat) ^ k ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hk
  have hle : (2 : Nat) ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk
  have hlt : (2 : Nat) ^ k - 1 < 18446744073709551616 := by rw [two64]; omega
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int64.and, Integers.MI.and]
  rw [BitVec.toNat_and, u64_toNat_repr, u64_toNat_repr, u64_toNat_repr,
      Nat.mod_eq_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ hdvd]
  have hp : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have : a % 2 ^ k < 18446744073709551616 := by
    have := Nat.mod_lt a hp; rw [two64]; omega
  exact (Nat.mod_eq_of_lt this).symm

theorem u64_shru (a k : Nat) (ha : a < 18446744073709551616)
    (hk : k < 18446744073709551616) :
    Integers.Int64.shru (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr ((k : _root_.Int)))
      = Integers.Int64.repr (((a / 2 ^ k : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int64.shru, Integers.MI.shru]
  rw [BitVec.toNat_ushiftRight, u64_toNat_repr, u64_toNat_repr, u64_toNat_repr,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
  have hq : a / 2 ^ k < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  exact (Nat.mod_eq_of_lt hq).symm

theorem u64_shl (a k : Nat) (hk : k < 18446744073709551616) :
    Integers.Int64.shl (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr ((k : _root_.Int)))
      = Integers.Int64.repr (((a * 2 ^ k : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int64.shl, Integers.MI.shl]
  rw [BitVec.toNat_shiftLeft, u64_toNat_repr, u64_toNat_repr, u64_toNat_repr,
      Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- Disjoint bitwise-or is addition.  Core has no such lemma, so it is proved
    here by splitting on the `2^k` boundary: the low half of `a ||| s*2^k` is
    `a`, the high half is `s`, and `Nat.div_add_mod` reassembles. -/
theorem Nat.lor_shift_eq_add (k a s : Nat) (ha : a < 2 ^ k) :
    a ||| s * 2 ^ k = a + s * 2 ^ k := by
  have hp : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have hlow : (a ||| s * 2 ^ k) % 2 ^ k = a := by
    rw [← Nat.and_two_pow_sub_one_eq_mod, Nat.and_or_distrib_right,
        Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt ha, Nat.mul_mod_left, Nat.or_zero]
  have hhigh : (a ||| s * 2 ^ k) / 2 ^ k = s := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib,
        Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt ha, Nat.mul_div_cancel _ hp, Nat.zero_or]
  have := Nat.div_add_mod (a ||| s * 2 ^ k) (2 ^ k)
  rw [hlow, hhigh, Nat.mul_comm] at this
  omega

/-- `adler | (sum2 << 16)`: the two halves are disjoint, so the C `|` is `+`. -/
theorem u64_or_pack (a s k : Nat) (ha : a < 2 ^ k)
    (hno : a + s * 2 ^ k < 18446744073709551616) :
    Integers.Int64.or (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr (((s * 2 ^ k : Nat) : _root_.Int)))
      = Integers.Int64.repr (((a + s * 2 ^ k : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int64.or, Integers.MI.or]
  rw [BitVec.toNat_or, u64_toNat_repr, u64_toNat_repr, u64_toNat_repr,
      Nat.mod_eq_of_lt (by omega : a < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : s * 2 ^ k < 18446744073709551616),
      Nat.mod_eq_of_lt hno, Nat.lor_shift_eq_add k a s ha]

theorem u64_modu (a b : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    Integers.Int64.modu (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr ((b : _root_.Int)))
      = Integers.Int64.repr (((a % b : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int64.modu, Integers.MI.modu]
  rw [BitVec.toNat_umod, u64_toNat_repr, u64_toNat_repr, u64_toNat_repr,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have : a % b ≤ a := Nat.mod_le _ _
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem u64_ltu (a b : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    Integers.Int64.ltu (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr ((b : _root_.Int))) = decide (a < b) := by
  simp only [Integers.Int64.ltu, Integers.MI.ltu, BitVec.ult,
             u64_toNat_repr, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem u64_eq (a b : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    Integers.Int64.eq (Integers.Int64.repr ((a : _root_.Int)))
        (Integers.Int64.repr ((b : _root_.Int))) = decide (a = b) := by
  simp only [Integers.Int64.eq, Integers.MI.eq]
  by_cases h : a = b
  · subst h; simp
  · have : Integers.Int64.repr ((a : _root_.Int)) ≠ Integers.Int64.repr ((b : _root_.Int)) := by
      intro hEq
      have := congrArg BitVec.toNat hEq
      rw [u64_toNat_repr, u64_toNat_repr, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      exact h this
    simp [this, h]

/-! ## Operator reduction at `tulong`

**Finding (Step-0 calibration):** every one of these holds by `rfl`.  The
operator layer is *executable* (`Cop.semBinaryOperation` is a function, not a
relation), and at concrete types the `classifyBinarith`/`semCast` dispatch
reduces away, so 64-bit unsigned arithmetic costs nothing to set up — unlike the
memory layer, which needed 833 lines of lemmas.  They are still named here so
that `rw`/`simp` can use them without re-elaborating the reduction each time. -/

section Ops
variable (cenv : CompositeEnv) (m : Mem)

theorem semBinop_and_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oand (.Vlong x) tulong (.Vint c) tint m
      = some (.Vlong (Integers.Int64.and x (Integers.Int64.repr (Integers.Int.signed c)))) := rfl

theorem semBinop_shr_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oshr (.Vlong x) tulong (.Vint c) tint m
      = (if Integers.Int.ltu c (Integers.Int.repr 64)
         then some (.Vlong (Integers.Int64.shru x (Integers.Int64.repr (Integers.Int.unsigned c))))
         else none) := rfl

theorem semBinop_shl_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oshl (.Vlong x) tulong (.Vint c) tint m
      = (if Integers.Int.ltu c (Integers.Int.repr 64)
         then some (.Vlong (Integers.Int64.shl x (Integers.Int64.repr (Integers.Int.unsigned c))))
         else none) := rfl

theorem semBinop_add_ulong_uchar (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vlong x) tulong (.Vint c) tuchar m
      = some (.Vlong (Integers.Int64.add x (Integers.Int64.repr (Integers.Int.unsigned c)))) := rfl

theorem semBinop_add_ulong_ulong (x y : Integers.Int64) :
    Cop.semBinaryOperation cenv .Oadd (.Vlong x) tulong (.Vlong y) tulong m
      = some (.Vlong (Integers.Int64.add x y)) := rfl

theorem semBinop_sub_ulong_uint (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vlong x) tulong (.Vint c) tuint m
      = some (.Vlong (Integers.Int64.sub x (Integers.Int64.repr (Integers.Int.unsigned c)))) := rfl

theorem semBinop_sub_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vlong x) tulong (.Vint c) tint m
      = some (.Vlong (Integers.Int64.sub x (Integers.Int64.repr (Integers.Int.signed c)))) := rfl

theorem semBinop_or_ulong (x y : Integers.Int64) :
    Cop.semBinaryOperation cenv .Oor (.Vlong x) tulong (.Vlong y) tulong m
      = some (.Vlong (Integers.Int64.or x y)) := rfl

theorem semBinop_mod_ulong_uint (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Omod (.Vlong x) tulong (.Vint c) tuint m
      = (if Integers.Int64.eq (Integers.Int64.repr (Integers.Int.unsigned c)) Integers.Int64.zero
         then none
         else some (.Vlong (Integers.Int64.modu x (Integers.Int64.repr (Integers.Int.unsigned c))))) := rfl

theorem semBinop_ge_ulong_uint (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oge (.Vlong x) tulong (.Vint c) tuint m
      = some (Val.ofBool (Integers.Int64.cmpu .Cge x
                (Integers.Int64.repr (Integers.Int.unsigned c)))) := rfl

theorem semBinop_ge_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oge (.Vlong x) tulong (.Vint c) tint m
      = some (Val.ofBool (Integers.Int64.cmpu .Cge x
                (Integers.Int64.repr (Integers.Int.signed c)))) := rfl

theorem semBinop_lt_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Olt (.Vlong x) tulong (.Vint c) tint m
      = some (Val.ofBool (Integers.Int64.cmpu .Clt x
                (Integers.Int64.repr (Integers.Int.signed c)))) := rfl

theorem semBinop_eq_ulong_int (x : Integers.Int64) (c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vlong x) tulong (.Vint c) tint m
      = some (Val.ofBool (Integers.Int64.cmpu .Ceq x
                (Integers.Int64.repr (Integers.Int.signed c)))) := rfl

end Ops

/-! ### `cmpu` in `Nat` terms

`Int64.ltu` is a *definition* equal to `MI.ltu`, and `MI.cmpu` is stated in terms
of the latter, so `u64_ltu`/`u64_eq` have to be unfolded to `MI` form before they
match.  That one-line `simp only [...] at h` is the whole trick. -/

theorem cmpu_ge_nat (a b : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    Integers.Int64.cmpu .Cge (Integers.Int64.repr ((a : _root_.Int)))
      (Integers.Int64.repr ((b : _root_.Int))) = decide (b ≤ a) := by
  have h := u64_ltu a b ha hb
  simp only [Integers.Int64.ltu] at h
  simp only [Integers.Int64.cmpu, Integers.MI.cmpu, h]
  by_cases h2 : a < b
  · simp [h2, show ¬ (b ≤ a) from by omega]
  · simp [h2, show b ≤ a from by omega]

theorem cmpu_lt_nat (a b : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    Integers.Int64.cmpu .Clt (Integers.Int64.repr ((a : _root_.Int)))
      (Integers.Int64.repr ((b : _root_.Int))) = decide (a < b) := by
  have h := u64_ltu a b ha hb
  simp only [Integers.Int64.ltu] at h
  simp only [Integers.Int64.cmpu, Integers.MI.cmpu, h]

theorem cmpu_eq_nat (a b : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    Integers.Int64.cmpu .Ceq (Integers.Int64.repr ((a : _root_.Int)))
      (Integers.Int64.repr ((b : _root_.Int))) = decide (a = b) := by
  have h := u64_eq a b ha hb
  simp only [Integers.Int64.eq] at h
  simp only [Integers.Int64.cmpu, Integers.MI.cmpu, h]

/-! ## 32-bit unsigned, and bytes

Byte loads come back `zero_ext`ed (`Val.loadResult .Mint8unsigned`), so a byte
buffer needs the 32-bit analogue of the bridge above, plus the fact that
zero-extending a value already below 256 does nothing. -/

theorem u32_repr_ofNat (n : Nat) :
    Integers.Int.repr ((n : _root_.Int)) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofInt 32 ((n : _root_.Int))).toNat = _
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem u32_toNat_repr (n : Nat) :
    (Integers.Int.repr ((n : _root_.Int))).toNat = n % 4294967296 := by
  rw [u32_repr_ofNat, BitVec.toNat_ofNat]

/-- 32-bit addition of two `Nat`s, mod 2^32 — the `unsigned int` analogue of
    `u64_add`.  A loop counter increment needs it. -/
theorem u32_add (a b : Nat) :
    Integers.Int.add (Integers.Int.repr ((a : _root_.Int)))
        (Integers.Int.repr ((b : _root_.Int)))
      = Integers.Int.repr (((a + b : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show (_ + _ : BitVec 32).toNat = _
  rw [BitVec.toNat_add, u32_toNat_repr, u32_toNat_repr, u32_toNat_repr]
  omega

theorem u32_unsigned (n : Nat) (h : n < 4294967296) :
    Integers.Int.unsigned (Integers.Int.repr ((n : _root_.Int))) = (n : _root_.Int) := by
  show (((Integers.Int.repr ((n : _root_.Int))).toNat : _root_.Int)) = _
  rw [u32_toNat_repr, Nat.mod_eq_of_lt h]

/-- A small non-negative literal is its own `Int.signed`.  Needed constantly:
    Clight's integer constants arrive as `Econst_int`, and the binary promotion
    to `unsigned long` goes through `Int.signed`. -/
theorem i32_signed_repr (c : Nat) (h : c < 2147483648) :
    Integers.Int.signed (Integers.Int.repr ((c : _root_.Int))) = ((c : _root_.Int)) := by
  show (Integers.Int.repr ((c : _root_.Int))).toInt = _
  rw [BitVec.toInt_eq_toNat_cond, u32_toNat_repr,
      Nat.mod_eq_of_lt (by omega : c < 4294967296)]
  omega

/-- Zero-extending a byte-sized value is the identity. -/
theorem zero_ext8_repr (c : Nat) (h : c < 256) :
    Integers.Int.zero_ext 8 (Integers.Int.repr ((c : _root_.Int)))
      = Integers.Int.repr ((c : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int.zero_ext, Integers.MI.zero_ext, ge_iff_le,
             show ¬ (32 ≤ 8) from by omega, if_false]
  rw [BitVec.toNat_and, u32_toNat_repr]
  show _ &&& (BitVec.allOnes 32 >>> (32 - 8)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_allOnes]
  rw [Nat.mod_eq_of_lt (by omega : c < 4294967296),
      show ((2 ^ 32 - 1 : Nat) >>> (32 - 8)) = 2 ^ 8 - 1 from by rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : c < 2 ^ 8)]

/-- 32-bit unsigned equality against a `Nat`.  The `Int64` analogues
    (`cmpu_eq_nat` and friends) were built for adler32's `unsigned long`
    arithmetic; this is the `unsigned int` version, which is what an `int`
    comparison in a C `if` reduces to. -/
theorem cmpu_eq_nat32 (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    Integers.Int.cmpu .Ceq (Integers.Int.repr ((a : _root_.Int)))
      (Integers.Int.repr ((b : _root_.Int))) = decide (a = b) := by
  show (Integers.MI.eq (Integers.Int.repr ((a : _root_.Int)))
          (Integers.Int.repr ((b : _root_.Int)))) = decide (a = b)
  by_cases h : a = b
  · subst h; simp [Integers.MI.eq]
  · simp only [h, decide_false, Integers.MI.eq, beq_eq_false_iff_ne, ne_eq]
    intro hc
    refine h ?_
    have hx := congrArg (fun x : Integers.Int => x.toNat) hc
    simpa [u32_toNat_repr, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hx

/-! ## `arrayU8` — an owned byte buffer

The byte-buffer analogue of `SepLogic.arrayU32`.  Elements are given as `Nat`s
below 256 rather than as `Integers.Int`, because that is how every model of a
byte stream wants to talk, and because `Mint8unsigned` loads come back
zero-extended — so restricting to real bytes is what makes the load lemma state
`f i` and not `zero_ext 8 (f i)`.

Alignment is free: `alignChunk .Mint8unsigned = 1`. -/

open HProp

/-- `n` owned bytes at `b + ofs`, holding `f 0 … f (n-1)`. -/
def arrayU8 (p : Permission) (b : Block) : Z → Nat → (Nat → Nat) → HProp
  | _, 0, _ => emp
  | ofs, n + 1, f =>
      mapsto .Mint8unsigned p b ofs (.Vint (Integers.Int.repr ((f 0 : Nat))))
        ∗ arrayU8 p b (ofs + 1) n (fun i => f (i + 1))

private theorem szc8 : ((sizeChunkNat .Mint8unsigned : Nat) : _root_.Int) = 1 := rfl

/-- A byte buffer owns exactly its own extent. -/
theorem arrayU8_none (p : Permission) (b : Block) :
    ∀ (n : Nat) (f : Nat → Nat) (ofs : _root_.Int) (h : Heap),
      arrayU8 p b ofs n f h → ∀ (b' : Block) (ofs' : _root_.Int),
        (b' ≠ b ∨ ofs' < ofs ∨ ofs + (n : _root_.Int) ≤ ofs') → h b' ofs' = none := by
  intro n
  induction n with
  | zero =>
      intro f ofs h harr b' ofs' _
      rw [show h = Heap.emp from harr]; rfl
  | succ k ih =>
      intro f ofs h harr b' ofs' hout
      obtain ⟨h1, h2, _, heq, hhead, htail⟩ := harr
      subst heq
      have e1 : h1 b' ofs' = none := by
        refine mapsto_none hhead b' ofs' ?_
        rw [szc8]
        rcases hout with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr (by push_cast at hh ⊢; omega))
      have e2 : h2 b' ofs' = none := by
        refine ih (fun i => f (i + 1)) (ofs + 1) h2 htail b' ofs' ?_
        rcases hout with hh | hh | hh
        · exact Or.inl hh
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by push_cast at hh ⊢; omega))
      simp [Heap.union, e1, e2]

/-- A byte buffer exists for any byte function — no alignment side condition. -/
theorem arrayU8_satisfiable (p : Permission) (b : Block) :
    ∀ (n : Nat) (f : Nat → Nat) (ofs : _root_.Int), ∃ h, arrayU8 p b ofs n f h := by
  intro n
  induction n with
  | zero => intro _ _; exact ⟨Heap.emp, rfl⟩
  | succ k ih =>
      intro f ofs
      obtain ⟨h2, h2m⟩ := ih (fun i => f (i + 1)) (ofs + 1)
      obtain ⟨h1, h1m⟩ :=
        bytesPtsTo_exists b p
          (encodeVal .Mint8unsigned (.Vint (Integers.Int.repr ((f 0 : Nat))))) ofs
      have h1mm : mapsto .Mint8unsigned p b ofs
                    (.Vint (Integers.Int.repr ((f 0 : Nat)))) h1 :=
        pure_sep_intro (by simp [alignChunk]) h1m
      refine ⟨Heap.union h1 h2, ⟨h1, h2, ?_, rfl, h1mm, h2m⟩⟩
      -- `window_split` (not a raw `by_cases oo = ofs`) is what makes the
      -- arithmetic omega-visible: its statement is at `_root_.Int`, so the facts
      -- it produces are too.  A hypothesis phrased at `CC.Z` is invisible to
      -- omega even when the goal is not.
      intro bb oo
      rcases window_split ofs oo (sizeChunkNat .Mint8unsigned) with ⟨i, hi, hoo⟩ | hout
      · by_cases hb : bb = b
        · refine Or.inr (arrayU8_none p b k (fun i => f (i + 1)) (ofs + 1) h2 h2m bb oo ?_)
          rw [hb]
          exact Or.inr (Or.inl (by subst hoo; simp [sizeChunkNat, sizeChunk] at hi; omega))
        · exact Or.inl (mapsto_none h1mm bb oo (Or.inl hb))
      · exact Or.inl (mapsto_none h1mm bb oo (Or.inr hout))

/-- Reading byte `i` out of an owned buffer.  The rest of the buffer is absorbed
    into `mapsto_load`'s frame, exactly as for `arrayU32`. -/
theorem arrayU8_load (p : Permission) (b : Block) (hpr : permOrder p .Readable = true) :
    ∀ (n : Nat) (f : Nat → Nat) (i : Nat), i < n → (∀ j, f j < 256) →
      ∀ (ofs : _root_.Int) (h : Heap) (m : Mem),
        arrayU8 p b ofs n f h → Heap.Agrees h m →
        Mem.load .Mint8unsigned m b (ofs + (i : _root_.Int))
          = some (.Vint (Integers.Int.repr ((f i : Nat)))) := by
  intro n
  induction n with
  | zero => intro _ i hi; simp at hi
  | succ k ih =>
      intro f i hi hb256 ofs h m harr hag
      obtain ⟨h1, h2, hd12, heq, hhead, htail⟩ := harr
      subst heq
      cases i with
      | zero =>
          have hl := mapsto_load hpr hhead (Heap.Agrees_union_left hag)
          simp only [Val.loadResult, zero_ext8_repr (f 0) (hb256 0)] at hl
          simpa using hl
      | succ j =>
          have hrec := ih (fun t => f (t + 1)) j (by omega) (fun t => hb256 (t + 1))
                    (ofs + 1) h2 m htail (Heap.Agrees_union_right hd12 hag)
          have harith : ofs + 1 + (j : _root_.Int) = ofs + ((j + 1 : Nat) : _root_.Int) := by
            push_cast; omega
          rw [harith] at hrec
          exact hrec

/-! ## Byte-buffer addressing

`buf[i]` for `unsigned char *buf`: stride 1, so the offset arithmetic is simpler
than `elemOfs`'s, but it needs the same no-overflow side condition. -/

/-- The offset `Cop.sem_add` computes for `buf + i` at element type
    `unsigned char`. -/
def byteOfs (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (iv : Integers.Int) :
    Integers.Ptrofs :=
  Integers.Ptrofs.add ofs0
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv tuchar))
      (Cop.ptrofsOfInt .Signed iv))

theorem semAdd_byte (cenv : CompositeEnv) (m : Mem) (b : Block)
    (ofs0 : Integers.Ptrofs) (iv : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vptr b ofs0) (tptr tuchar) (.Vint iv) tint m
      = some (.Vptr b (byteOfs cenv ofs0 iv)) := rfl

-- fresh binders so `omega` sees its own instances; see the `CC.Z` note above.
-- The bound is stated over `Nat`, not over `Ptrofs.unsigned … : Z`: a `Z`-typed
-- hypothesis is invisible to `omega` even when the goal is not.
private theorem byte_arith (A i : Nat)
    (hno : A + i < 18446744073709551616) :
    (((A + i % 18446744073709551616) % 18446744073709551616 : Nat) : _root_.Int)
      = (A : _root_.Int) + (i : _root_.Int) := by omega

theorem byteOfs_unsigned (cenv : CompositeEnv) (ofs0 : Integers.Ptrofs) (i : Nat)
    (hi : i < 2147483648) (hno : ofs0.toNat + i < 18446744073709551616) :
    Integers.Ptrofs.unsigned (byteOfs cenv ofs0 (Integers.Int.repr i))
      = Integers.Ptrofs.unsigned ofs0 + (i : _root_.Int) := by
  have hsz : sizeof cenv tuchar = 1 := by simp [sizeof, tuchar]
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  simp only [byteOfs, hsz, Cop.ptrofsOfInt, Integers.Ptrofs.of_ints,
             Integers.Ptrofs.add, Integers.Ptrofs.mul, Integers.Ptrofs.unsigned,
             Integers.Ptrofs.repr, Integers.MI.add, Integers.MI.mul,
             Integers.MI.repr, Integers.MI.unsigned, Integers.MI.signed,
             BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt, hw]
  rw [toInt_repr (i : _root_.Int) (by omega) (by omega)]
  have h1 : ((1 : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = 1 := by
    omega
  have hii : (((i : Nat) : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = i := by
    omega
  rw [h1, hii, Nat.one_mul]
  exact byte_arith _ _ hno

/-- A pointer offset is below 2^64, over `Nat` — the form `omega` can use. -/
theorem ptrofs_toNat_lt (ofs : Integers.Ptrofs) : ofs.toNat < 18446744073709551616 := by
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  have h := ofs.isLt
  omega

/-- A pointer offset is below 2^64 — stated over `Nat` so `omega` can use it
    (`Ptrofs.unsigned` returns `Z`, where it cannot). -/
theorem ptrofs_unsigned_lt (ofs : Integers.Ptrofs) :
    Integers.Ptrofs.unsigned ofs < (18446744073709551616 : _root_.Int) := by
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  have h := ofs.isLt
  rw [hw] at h
  show ((ofs.toNat : _root_.Int)) < _
  omega

/-- Reading `buf[idx]` out of an owned byte buffer. -/
theorem eval_index_bytes {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Nat} {h : Heap} {idx : Expr} {i : Nat} {pid : Ident}
    (hpr : permOrder p .Readable = true)
    (harr : arrayU8 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n) (hb : ∀ j, f j < 256)
    (hptr : le.get pid = some (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hty : typeof idx = tint)
    (hlt31 : i < 2147483648)
    (hno : ofs0.toNat + i < 18446744073709551616) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr tuchar)) idx (tptr tuchar)) tuchar)
      (.Vint (Integers.Int.repr ((f i : Nat)))) := by
  have hadd : Cop.semBinaryOperation ge.genv_cenv .Oadd (.Vptr b ofs0) (tptr tuchar)
                (.Vint (Integers.Int.repr i)) (typeof idx) m
              = some (.Vptr b (byteOfs ge.genv_cenv ofs0 (Integers.Int.repr i))) := by
    rw [hty]; exact semAdd_byte _ _ _ _ _
  refine EvalExpr.Elvalue _ b (byteOfs ge.genv_cenv ofs0 (Integers.Int.repr i)) .Full _
    (EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop .Oadd _ _ _ (.Vptr b ofs0) (.Vint (Integers.Int.repr i)) _
        (EvalExpr.Etempvar pid (tptr tuchar) _ hptr) hidx hadd)) ?_
  refine DerefLoc.value .Mint8unsigned _ rfl ?_
  rw [Mem.loadv_ptr _ _ _ _ (Or.inl rfl), byteOfs_unsigned ge.genv_cenv ofs0 i hlt31 hno]
  exact arrayU8_load p b hpr n f i hi hb _ h m harr hag

end CC
