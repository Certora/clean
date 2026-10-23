/-
  Lemmas about `encodeVal` / `decodeVal` — the byte-level round trip that the
  memory model's `load_store_same` rests on.  Port of the usable part of
  `common/Memdata.v`'s proof section (`decode_encode_val_*`).

  Phase 7.1 of the separation-logic plan.  `CCLib/common/Memdata.lean` shipped with one
  theorem (`length_encodeVal`); a separation logic needs the round trip.

  ## Two deliberate choices

  * **Concrete widths, not symbolic.**  Statements are given at the widths that
    actually occur (1, 2, 4, 8 bytes; 32- and 64-bit words).  CompCert proves
    `int_of_bytes (bytes_of_int n x) = x mod 2^(8n)` for symbolic `n`, which needs
    the `x % (a*b)` decomposition lemma; at concrete widths `omega` does the whole
    thing, so the general lemma is not worth its proof.
  * **No `bv_decide`.**  It would close several of these instantly, but it
    discharges through `Lean.ofReduceBool` — a native-evaluation axiom.  Putting
    that in the memory model would contaminate the axiom report of every theorem
    above it.  Everything here is axiom-free beyond Lean's standard three.

  ## The `omega` trap in this file

  `abbrev Z := _root_.Int` means arithmetic inside `Memdata`'s definitions
  elaborates its `HAdd`/`HMul`/`HDiv` instances at `CC.Z`, while `omega` matches
  instances *syntactically* at `Int` — so `omega` reports "no usable constraints"
  on a goal that looks perfectly linear.  The fix used throughout: state the
  arithmetic as a private lemma whose binders are `_root_.Int`, then discharge the
  real goal with `exact`, which bridges the two by definitional equality.
-/
import CCLib.common.Memdata

namespace CC

/-! ## Target parameters

`Archi`'s values are `Global Opaque` in CompCert and the port keeps that
discipline (see `CCLib/aarch64/Archi.lean`): unfold them only through named equations. -/

@[simp] theorem Archi.big_endian_eq : Archi.big_endian = false := rfl
@[simp] theorem Archi.ptr64_eq : Archi.ptr64 = true := rfl

/-- On a little-endian target `rev_if_be` is the identity. -/
@[simp] theorem revIfBe_id (l : List Byte) : revIfBe l = l := by
  simp [revIfBe]

/-! ## The byte round trip -/

/-- One byte of `bytes_of_int` is the low byte of the number. -/
theorem byte_unsigned_repr (x : _root_.Int) :
    Integers.Byte.unsigned (Integers.Byte.repr x) = x % 256 := by
  show ((BitVec.ofInt 8 x).toNat : _root_.Int) = x % 256
  rw [BitVec.toNat_ofInt]; omega

-- The arithmetic, at `_root_.Int` so `omega`'s instance matching applies.
private theorem arith1 (x : _root_.Int) : x % 256 + 0 * 256 = x % 256 := by omega
private theorem arith2 (x : _root_.Int) :
    x % 256 + (x / 256 % 256 + 0 * 256) * 256 = x % 65536 := by omega
private theorem arith4 (x : _root_.Int) :
    x % 256 + (x / 256 % 256 + (x / 256 / 256 % 256
      + (x / 256 / 256 / 256 % 256 + 0 * 256) * 256) * 256) * 256
    = x % 4294967296 := by omega
private theorem arith8 (x : _root_.Int) :
    x % 256 + (x / 256 % 256 + (x / 256 / 256 % 256 + (x / 256 / 256 / 256 % 256
      + (x / 256 / 256 / 256 / 256 % 256 + (x / 256 / 256 / 256 / 256 / 256 % 256
        + (x / 256 / 256 / 256 / 256 / 256 / 256 % 256
          + (x / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 256 + 0 * 256) * 256)
            * 256) * 256) * 256) * 256) * 256) * 256
    = x % 18446744073709551616 := by omega

/-- The simp set that unfolds one `decodeInt (encodeInt sz x)`. -/
private def decEncSimp : Unit := ()

theorem decodeInt_encodeInt_1 (x : _root_.Int) : decodeInt (encodeInt 1 x) = x % 256 := by
  simp only [decodeInt, encodeInt, revIfBe_id, bytesOfInt, intOfBytes, byte_unsigned_repr]
  exact arith1 x

theorem decodeInt_encodeInt_2 (x : _root_.Int) : decodeInt (encodeInt 2 x) = x % 65536 := by
  simp only [decodeInt, encodeInt, revIfBe_id, bytesOfInt, intOfBytes, byte_unsigned_repr]
  exact arith2 x

theorem decodeInt_encodeInt_4 (x : _root_.Int) :
    decodeInt (encodeInt 4 x) = x % 4294967296 := by
  simp only [decodeInt, encodeInt, revIfBe_id, bytesOfInt, intOfBytes, byte_unsigned_repr]
  exact arith4 x

theorem decodeInt_encodeInt_8 (x : _root_.Int) :
    decodeInt (encodeInt 8 x) = x % 18446744073709551616 := by
  simp only [decodeInt, encodeInt, revIfBe_id, bytesOfInt, intOfBytes, byte_unsigned_repr]
  exact arith8 x

/-! ## `repr` after a modulus

`Int.repr` already reduces modulo the word size, so a redundant modulus at the
word size is absorbed.  Stated at the two concrete widths that occur. -/

theorem repr32_emod (x : _root_.Int) :
    Integers.Int.repr (x % 4294967296) = Integers.Int.repr x := by
  show BitVec.ofInt 32 (x % 4294967296) = BitVec.ofInt 32 x
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  congr 1
  omega

theorem repr64_emod (x : _root_.Int) :
    Integers.Int64.repr (x % 18446744073709551616) = Integers.Int64.repr x := by
  show BitVec.ofInt 64 (x % 18446744073709551616) = BitVec.ofInt 64 x
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  congr 1
  omega

/-- `Int.repr (Int.unsigned n) = n`. -/
theorem repr32_unsigned (n : Integers.Int) :
    Integers.Int.repr (Integers.Int.unsigned n) = n := by
  show BitVec.ofInt 32 ((n.toNat : _root_.Int)) = n
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have h : n.toNat < 4294967296 := n.isLt
  omega

/-- `Int64.repr (Int64.unsigned n) = n`. -/
theorem repr64_unsigned (n : Integers.Int64) :
    Integers.Int64.repr (Integers.Int64.unsigned n) = n := by
  show BitVec.ofInt 64 ((n.toNat : _root_.Int)) = n
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have h : n.toNat < 18446744073709551616 := n.isLt
  omega

/-! ## Floats round-trip by construction

`Float`/`Float32` are structures wrapping their bit pattern
(`CCLib/lib/Floats.lean`), which is what made skipping Flocq possible.  The
consequence here is that the store/load round trip for floats is `rfl`. -/

@[simp] theorem Float_ofBits_toBits (f : Floats.Float) :
    Floats.Float.ofBits (Floats.Float.toBits f) = f := rfl

@[simp] theorem Float32_ofBits_toBits (f : Floats.Float32) :
    Floats.Float32.ofBits (Floats.Float32.toBits f) = f := rfl

/-! ## Projecting what was injected -/

@[simp] theorem projBytes_injBytes (bl : List Byte) : projBytes (injBytes bl) = some bl := by
  induction bl with
  | nil => rfl
  | cons b l ih =>
      show (projBytes (injBytes l)).map (b :: ·) = some (b :: l)
      rw [ih]; rfl

/-- `proj_bytes` fails at the first non-byte cell.  Stated on the *cons* rather
    than on `List.replicate`, because `simp` expands `replicate` at concrete
    lengths into a literal list, at which point a `replicate`-shaped lemma no
    longer matches. -/
@[simp] theorem projBytes_undef_cons (vl : List MemVal) :
    projBytes (MemVal.Undef :: vl) = none := rfl

@[simp] theorem projBytes_fragment_cons (v : Val) (q : Quantity) (i : Nat)
    (vl : List MemVal) : projBytes (MemVal.Fragment v q i :: vl) = none := rfl

/-- A run of `Undef` is not a byte string, so `proj_bytes` fails. -/
@[simp] theorem projBytes_replicate_undef (n : Nat) :
    projBytes (List.replicate (n + 1) MemVal.Undef) = none := by
  simp [List.replicate]

/-- Fragments are not bytes either. -/
@[simp] theorem projBytes_injValueRec (n : Nat) (v : Val) (q : Quantity) :
    projBytes (injValueRec (n + 1) v q) = none := by
  simp [injValueRec]

@[simp] theorem projBytes_injValue (q : Quantity) (v : Val) :
    projBytes (injValue q v) = none := by
  cases q <;> simp [injValue, sizeQuantityNat] <;>
    exact projBytes_injValueRec _ v _

/-- Every fragment written by `inj_value_rec` passes `check_value`. -/
theorem checkValue_injValueRec (n : Nat) (v : Val) (q : Quantity) :
    checkValue n v q (injValueRec n v q) = true := by
  induction n with
  | zero => rfl
  | succ m ih => simp [injValueRec, checkValue, ih]

/-- `proj_value` recovers exactly the value `inj_value` wrote. -/
@[simp] theorem projValue_injValue (q : Quantity) (v : Val) :
    projValue q (injValue q v) = v := by
  have hc := checkValue_injValueRec (sizeQuantityNat q) v q
  cases q <;>
    simp only [projValue, injValue, sizeQuantityNat, injValueRec] at hc ⊢ <;>
    simp [hc]

@[simp] theorem projValue_undef_cons (q : Quantity) (vl : List MemVal) :
    projValue q (MemVal.Undef :: vl) = Val.Vundef := rfl

/-! ## Low-bit agreement

`zero_ext k` and `sign_ext k` look only at the low `k` bits, so the redundant
`% 2^k` that `decodeInt (encodeInt sz …)` leaves behind is invisible to them.
This is the only genuinely bit-level reasoning the round trip needs, and it is
where `Nat.and_two_pow_sub_one_eq_mod` from core does the heavy lifting. -/

theorem toNat_zero_ext_8 (x : Integers.Int) :
    (Integers.MI.zero_ext 8 x).toNat = x.toNat % 256 := by
  show (x &&& (BitVec.allOnes 32 >>> (32 - 8))).toNat = x.toNat % 256
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 8

theorem toNat_zero_ext_16 (x : Integers.Int) :
    (Integers.MI.zero_ext 16 x).toNat = x.toNat % 65536 := by
  show (x &&& (BitVec.allOnes 32 >>> (32 - 16))).toNat = x.toNat % 65536
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 16

theorem repr_unsigned_emod_256 (n : Integers.Int) :
    (Integers.Int.repr (Integers.Int.unsigned n % 256)).toNat = n.toNat % 256 := by
  show (BitVec.ofInt 32 ((n.toNat : _root_.Int) % 256)).toNat = n.toNat % 256
  rw [BitVec.toNat_ofInt]; omega

theorem repr_unsigned_emod_65536 (n : Integers.Int) :
    (Integers.Int.repr (Integers.Int.unsigned n % 65536)).toNat = n.toNat % 65536 := by
  show (BitVec.ofInt 32 ((n.toNat : _root_.Int) % 65536)).toNat = n.toNat % 65536
  rw [BitVec.toNat_ofInt]; omega

@[simp] theorem zero_ext_8_repr (n : Integers.Int) :
    Integers.Int.zero_ext 8 (Integers.Int.repr (Integers.Int.unsigned n % 256))
      = Integers.Int.zero_ext 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [show Integers.Int.zero_ext = Integers.MI.zero_ext from rfl,
      toNat_zero_ext_8, toNat_zero_ext_8, repr_unsigned_emod_256]
  omega

@[simp] theorem zero_ext_16_repr (n : Integers.Int) :
    Integers.Int.zero_ext 16 (Integers.Int.repr (Integers.Int.unsigned n % 65536))
      = Integers.Int.zero_ext 16 n := by
  apply BitVec.eq_of_toNat_eq
  rw [show Integers.Int.zero_ext = Integers.MI.zero_ext from rfl,
      toNat_zero_ext_16, toNat_zero_ext_16, repr_unsigned_emod_65536]
  omega

-- `sign_ext` at a concrete width, with the two guards discharged.  Reducing the
-- guards by `show`/defeq instead blows the `whnf` heartbeat budget.
theorem sign_ext_8_eq (x : Integers.Int) :
    Integers.MI.sign_ext 8 x = (x <<< 24).sshiftRight 24 := by
  simp [Integers.MI.sign_ext]

theorem sign_ext_16_eq (x : Integers.Int) :
    Integers.MI.sign_ext 16 x = (x <<< 16).sshiftRight 16 := by
  simp [Integers.MI.sign_ext]

@[simp] theorem sign_ext_8_repr (n : Integers.Int) :
    Integers.Int.sign_ext 8 (Integers.Int.repr (Integers.Int.unsigned n % 256))
      = Integers.Int.sign_ext 8 n := by
  -- prove the shifted operands equal, then rewrite: `congr 1` on `sshiftRight`
  -- blows the heartbeat budget.
  have h : (Integers.Int.repr (Integers.Int.unsigned n % 256)) <<< 24 = n <<< 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, repr_unsigned_emod_256,
        Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  rw [show Integers.Int.sign_ext = Integers.MI.sign_ext from rfl,
      sign_ext_8_eq, sign_ext_8_eq, h]

@[simp] theorem sign_ext_16_repr (n : Integers.Int) :
    Integers.Int.sign_ext 16 (Integers.Int.repr (Integers.Int.unsigned n % 65536))
      = Integers.Int.sign_ext 16 n := by
  have h : (Integers.Int.repr (Integers.Int.unsigned n % 65536)) <<< 16 = n <<< 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, repr_unsigned_emod_65536,
        Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    omega
  rw [show Integers.Int.sign_ext = Integers.MI.sign_ext from rfl,
      sign_ext_16_eq, sign_ext_16_eq, h]

/-! ## The headline round trip -/

theorem decodeVal_encodeVal (chunk : Chunk) (v : Val) :
    decodeVal chunk (encodeVal chunk v) = Val.loadResult chunk v := by
  cases v <;> cases chunk <;>
    simp [encodeVal, decodeVal, Val.loadResult, sizeChunkNat, sizeChunk,
          decodeInt_encodeInt_1, decodeInt_encodeInt_2, decodeInt_encodeInt_4,
          decodeInt_encodeInt_8, repr32_emod, repr64_emod, repr32_unsigned,
          repr64_unsigned]

end CC
