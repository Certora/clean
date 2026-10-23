/-
  Checks for the theorems added from `common/Memdata.v` and the ISO C
  arithmetic conversions added from `cfrontend/Cop.v`.
-/
import CCLib.common.MemdataEncode
import CCLib.cfrontend.CopArith

open CC

namespace MemdataCheck

/-- Little-endian: `0x1234` is stored as `[0x34, 0x12]`. -/
example : bytesOfInt 2 0x1234 = [Integers.Byte.repr 0x34, Integers.Byte.repr 0x12] := by decide

/-- A 16-bit encoding only sees the low 16 bits. -/
example : encodeInt 2 0x51234 = encodeInt 2 0x1234 :=
  encodeInt_16_mod _ _ (by decide)

/-- Storing `-1` as a signed byte and reading it back as an unsigned byte gives
    255, as `decode_encode_val` predicts. -/
example : decodeVal .Mint8unsigned (encodeVal .Mint8signed (.Vint (Integers.Int.repr (-1)))) =
    .Vint (Integers.Int.repr 255) := by
  have h := decodeEncodeVal_general (.Vint (Integers.Int.repr (-1))) .Mint8signed .Mint8unsigned
  simp only [decodeEncodeVal] at h
  rw [h]; decide

/-- Reading a pointer back through a byte-sized chunk yields `Vundef`. -/
example (b : Block) (o : Integers.Ptrofs) :
    decodeVal .Mint8unsigned (encodeVal .Mint64 (.Vptr b o)) = .Vundef := by
  have h := decodeEncodeVal_general (.Vptr b o) .Mint64 .Mint8unsigned
  simpa [decodeEncodeVal] using h

/-- Pointers survive a `Many64` round trip. -/
example (b : Block) (o : Integers.Ptrofs) :
    decodeVal .Many64 (encodeVal .Many64 (.Vptr b o)) = .Vptr b o := by
  have h := decodeEncodeVal_general (.Vptr b o) .Many64 .Many64
  simpa [decodeEncodeVal] using h

/-- The usual arithmetic conversions: `unsigned int` and `long` (32 bits on
    CompCert's ISO model) meet at `unsigned long`. -/
example : Cop.usualArithmeticConversion (.I .UInt) (.I .Long) = .I .ULong := by decide

/-- `char` and `unsigned short` are both promoted to `int`. -/
example : Cop.usualArithmeticConversion (.I .Char) (.I .UShort) = .I .Int := by decide

/-- `unsigned int` and `long long` meet at `long long`. -/
example : Cop.usualArithmeticConversion (.I .UInt) (.I .Longlong) = .I .Longlong := by decide

end MemdataCheck
