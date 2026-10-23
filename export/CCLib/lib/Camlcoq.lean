/-
  The part of the OCaml file `lib/Camlcoq.ml` that the compiler needs:
  `first_unused_ident`, the implementation of the Rocq `Parameter`
  `SimplExpr.first_unused_ident` (bound in `extraction/extraction.v`).

  In OCaml, identifiers are interned atoms and `first_unused_ident` returns
  the next atom not yet allocated.

  Also `extern_atom` (`Camlcoq.externAtom`), which the assembly printers
  use to print symbol names.  Here it returns an identifier larger than
  every identifier the program declares (globals, public names, `main`,
  function parameters and local variables), so the temporaries created by
  `SimplExpr` are fresh.  The rest of `Camlcoq.ml` converts between OCaml
  and Rocq numbers and strings, which Lean does not need.
-/
import CCLib.cfrontend.Csyntax

namespace CC
namespace Camlcoq

/-- The identifiers declared by a program: globals, public names, `main`,
    and the parameters and local variables of its functions. -/
def declaredIdents (p : Csyntax.Program) : List Ident :=
  let ofDef : Ident × GlobDef Csyntax.FunDef Ty → List Ident := fun (id, gd) =>
    id :: match gd with
      | .Gfun (.Internal f) => f.fn_params.map (·.1) ++ f.fn_vars.map (·.1)
      | _ => []
  p.prog_main :: p.prog_public ++ p.prog_defs.flatMap ofDef

/-- The larger of two identifiers (`Pos.max`). -/
def identMax (p q : Ident) : Ident := if p.toNat ≤ q.toNat then q else p

/-- `Camlcoq.first_unused_ident` -/
def firstUnusedIdent (p : Csyntax.Program) : Ident :=
  ((declaredIdents p).foldl identMax .xH).succ

theorem le_foldl_max (l : List Positive) (a : Positive) :
    a.toNat ≤ (l.foldl identMax a).toNat ∧
    ∀ x ∈ l, x.toNat ≤ (l.foldl identMax a).toNat := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    have h := ih (identMax a y)
    have hay : a.toNat ≤ (identMax a y).toNat ∧ y.toNat ≤ (identMax a y).toNat := by
      unfold identMax; split <;> omega
    refine ⟨by simp only [List.foldl_cons]; omega, ?_⟩
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact h.2 x hx

/-- `first_unused_ident` is fresh: it is larger than every identifier the
    program declares. -/
theorem firstUnusedIdent_fresh (p : Csyntax.Program) (id : Ident)
    (h : id ∈ declaredIdents p) : id.toNat < (firstUnusedIdent p).toNat := by
  have := (le_foldl_max (declaredIdents p) .xH).2 id h
  simp only [firstUnusedIdent, Positive.toNat_succ]
  omega

/-! ## `extern_atom`

In OCaml, `extern_atom` looks the atom up in the table of interned strings
and returns `"$N"` for atoms that were never interned.  In the Lean port,
names are encoded into identifiers by `identOfString`
(`CCLib/lib/Positive.lean`), so `externAtom` decodes that encoding instead;
identifiers that are not the encoding of a string (for instance the
temporaries made by `firstUnusedIdent`) print as `"$N"`, as in OCaml. -/

/-- Number of constructors of a `Positive` (fuel for `decodeIdent`). -/
def posSize : Positive → Nat
  | .xH => 1
  | .xO p => posSize p + 1
  | .xI p => posSize p + 1

/-- Read `n` bits, least significant first, from the spine of `p`. -/
def readBits : Nat → Positive → Option (Nat × Positive)
  | 0, p => some (0, p)
  | n + 1, .xO p => (readBits n p).map fun (v, q) => (2 * v, q)
  | n + 1, .xI p => (readBits n p).map fun (v, q) => (2 * v + 1, q)
  | _ + 1, .xH => none

/-- Inverse of `identOfString`: the characters encoded by `p`, if `p` is the
    encoding of a string. -/
def decodeIdent : Nat → Positive → Option (List Char)
  | _, .xH => some []
  | 0, _ => none
  | fuel + 1, .xI (.xI (.xI (.xI (.xI (.xI p))))) =>
    match readBits 8 p with
    | some (v, q) =>
      -- bit 0 of the character is the outermost of the eight bits
      (decodeIdent fuel q).map (Char.ofNat v :: ·)
    | none => none
  | _, _ => none

/-- `Camlcoq.extern_atom` -/
def externAtom (id : Ident) : String :=
  match decodeIdent (posSize id) id with
  | some cs => String.ofList cs
  | none => "$" ++ toString id.toNat

#guard externAtom (identOfString "main") = "main"
#guard externAtom (identOfString "__compcert_va_saveregs") = "__compcert_va_saveregs"
#guard externAtom (identOfString "") = ""
#guard externAtom (Positive.ofNat 12) = "$12"

/-! ## `Printf` conversions used by the printers

The OCaml printers format numbers with `Printf`.  The functions below
reproduce the conversions they use, computed exactly from the bit patterns
(no host floating point), so that `#guard` can check them:
* `%ld`/`%Ld` of `camlint_of_coqint`/`camlint64_of_coqint`: `Int.signed`;
* `%lx`/`%Lx`: the unsigned value in hexadecimal (`hexOfNat`);
* `%.<p>g` (`formatG`), and OCaml's `%F`/`%.<p>F` (`formatF`), which is
  `%.12g` (resp. `%.<p>g`) with a `.` appended when the result looks like an
  integer, and `infinity`/`neg_infinity`/`nan` for the special values;
* `%S` (`escapedString`): an OCaml string literal (`String.escaped`). -/

/-- Lower-case hexadecimal digits of a natural number (`%x`). -/
def hexOfNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- A decoded IEEE value: `finite neg num den` is `±num/den`. -/
inductive IEEEValue where
  | finite (neg : Bool) (num den : Nat)
  | inf (neg : Bool)
  | nan

/-- Decode an IEEE bit pattern with `e` exponent bits and `m` mantissa bits. -/
def decodeIEEE (e m bits : Nat) : IEEEValue :=
  let neg := bits / 2 ^ (e + m) % 2 == 1
  let ex := bits / 2 ^ m % 2 ^ e
  let mant := bits % 2 ^ m
  let bias := 2 ^ (e - 1) - 1
  if ex == 2 ^ e - 1 then (if mant == 0 then .inf neg else .nan)
  else
    -- value = sig * 2^(exp) with `exp` an integer
    let (sig, exp) : Nat × Int :=
      if ex == 0 then (mant, (1 : Int) - bias - m) else (mant + 2 ^ m, (ex : Int) - bias - m)
    if exp ≥ 0 then .finite neg (sig * 2 ^ exp.toNat) 1
    else .finite neg sig (2 ^ (-exp).toNat)

/-- `10^x ≤ n/d` -/
def pow10Le (n d : Nat) (x : Int) : Bool :=
  if x ≥ 0 then d * 10 ^ x.toNat ≤ n else d ≤ n * 10 ^ (-x).toNat

/-- `⌊log10 (n/d)⌋` for `n, d > 0`. -/
def floorLog10 (n d : Nat) : Int :=
  let est : Int := ((n.log2 : Int) - (d.log2 : Int)) * 30103 / 100000
  let rec go : Nat → Int → Int
    | 0, x => x
    | fuel + 1, x =>
      if !pow10Le n d x then go fuel (x - 1)
      else if pow10Le n d (x + 1) then go fuel (x + 1)
      else x
  go 16 est

/-- `round(n/d * 10^s)`, rounding half to even (as C's `printf`). -/
def scaleRound (n d : Nat) (s : Int) : Nat :=
  let (num, den) := if s ≥ 0 then (n * 10 ^ s.toNat, d) else (n, d * 10 ^ (-s).toNat)
  let q := num / den
  let r := num % den
  if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q

/-- Remove trailing zeros (and then a trailing `.`) from a fractional part. -/
def stripFrac (s : String) : String :=
  let cs := (s.toList.reverse.dropWhile (· == '0')).reverse
  String.ofList cs

/-- Left-pad with zeros to `w` characters. -/
def padZeros (w : Nat) (s : String) : String :=
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- C's `%.<p>g` on a finite, non-negative rational `n/d`. -/
def formatGPos (p : Nat) (n d : Nat) : String :=
  let p := if p == 0 then 1 else p
  if n == 0 then "0" else
  let x0 := floorLog10 n d
  let sc0 := scaleRound n d ((p : Int) - 1 - x0)
  let (x, sc) := if sc0 ≥ 10 ^ p then (x0 + 1, sc0 / 10) else (x0, sc0)
  let digits := toString sc   -- exactly `p` digits
  if x < -4 || x ≥ (p : Int) then
    let frac := stripFrac (digits.drop 1).toString
    let mant := (digits.take 1).toString ++ (if frac.isEmpty then "" else "." ++ frac)
    let ex := if x < 0 then "-" ++ padZeros 2 (toString (-x).toNat)
      else "+" ++ padZeros 2 (toString x.toNat)
    mant ++ "e" ++ ex
  else if x ≥ 0 then
    let ip := (digits.take (x.toNat + 1)).toString
    let frac := stripFrac (digits.drop (x.toNat + 1)).toString
    ip ++ (if frac.isEmpty then "" else "." ++ frac)
  else
    let frac := stripFrac (String.ofList (List.replicate ((-x).toNat - 1) '0') ++ digits)
    "0." ++ frac

/-- C's `%.<p>g` of a decoded value. -/
def formatG (p : Nat) : IEEEValue → String
  | .nan => "nan"
  | .inf neg => if neg then "-inf" else "inf"
  | .finite neg n d => (if neg then "-" else "") ++ formatGPos p n d

/-- OCaml's `%.<p>F` (`%F` is `%.12F`). -/
def formatF (p : Nat := 12) : IEEEValue → String
  | .nan => "nan"
  | .inf neg => if neg then "neg_infinity" else "infinity"
  | v@(.finite ..) =>
    let s := formatG p v
    if s.toList.any (fun c => c == '.' || c == 'e') then s else s ++ "."

/-- `%F` of `camlfloat_of_coqfloat`. -/
def floatF (f : Floats.Float) (p : Nat := 12) : String :=
  formatF p (decodeIEEE 11 52 (Integers.Int64.unsigned f.toBits).toNat)

/-- `%F` of `camlfloat_of_coqfloat32` (the value converted to binary64,
    which is exact). -/
def float32F (f : Floats.Float32) (p : Nat := 12) : String :=
  formatF p (decodeIEEE 8 23 (Integers.Int.unsigned f.toBits).toNat)

/-- `String.escaped` on one byte. -/
def escapeByte (b : UInt8) : String :=
  match b.toNat with
  | 34 => "\\\""
  | 92 => "\\\\"
  | 10 => "\\n"
  | 9 => "\\t"
  | 13 => "\\r"
  | 8 => "\\b"
  | n => if n ≥ 32 && n < 127 then String.singleton (Char.ofNat n)
         else "\\" ++ padZeros 3 (toString n)

/-- OCaml's `%S`: the string as an OCaml literal, quotes included. -/
def escapedString (s : String) : String :=
  "\"" ++ String.join (s.toUTF8.toList.map escapeByte) ++ "\""

#guard formatGPos 12 1 3 = "0.333333333333"
#guard formatGPos 12 100 1 = "100"
#guard formatGPos 12 1 10000000 = "1e-07"
#guard formatGPos 3 12345 1 = "1.23e+04"
#guard formatGPos 15 15 10 = "1.5"
#guard formatGPos 2 95 1000 = "0.095"
#guard formatF 12 (.finite false 3 1) = "3."
#guard formatF 12 (.finite true 5 2) = "-2.5"
#guard formatF 12 (.inf true) = "neg_infinity"
#guard floatF (Floats.Float.ofBits (Integers.Int64.repr 0x3FF8000000000000)) = "1.5"
#guard floatF (Floats.Float.ofBits (Integers.Int64.repr 0x3FB999999999999A)) = "0.1"
#guard floatF (Floats.Float.ofBits (Integers.Int64.repr 0x8000000000000000)) = "-0."
#guard float32F (Floats.Float32.ofBits (Integers.Int.repr 0x3DCCCCCD)) = "0.10000000149"
#guard escapedString "a\"b\n\x01" = "\"a\\\"b\\n\\001\""

/-- A Rocq number as seen by the OCaml printers after extraction: machine
    integers (`int`, `int64`, `ptrofs`) are extracted to their unsigned
    value `intval`, a `Z`. -/
class CamlNum (α : Type) where
  toZ : α → Int

instance : CamlNum Int := ⟨id⟩
instance : CamlNum Integers.Int := ⟨Integers.Int.unsigned⟩
instance : CamlNum Integers.Int64 := ⟨Integers.Int64.unsigned⟩
instance : CamlNum Integers.Ptrofs := ⟨Integers.Ptrofs.unsigned⟩

/-- Wrap an integer to a signed `w`-bit value (OCaml `Int32`/`Int64`). -/
def wrapSigned (w : Nat) (z : Int) : Int :=
  let m := z % (2 ^ w : Nat)
  if m ≥ (2 ^ (w - 1) : Nat) then m - (2 ^ w : Nat) else m

/-- `Z.to_string`, `%d` of `Z.to_int` -/
def zs {α} [CamlNum α] (x : α) : String := toString (CamlNum.toZ x)
/-- `%ld` of `camlint_of_coqint` -/
def ci32 {α} [CamlNum α] (x : α) : String := toString (wrapSigned 32 (CamlNum.toZ x))
/-- `%lu` of `camlint_of_coqint` -/
def cu32 {α} [CamlNum α] (x : α) : String := toString (CamlNum.toZ x % (2 ^ 32 : Nat))
/-- `%lx` of `camlint_of_coqint` -/
def cx32 {α} [CamlNum α] (x : α) : String := hexOfNat (CamlNum.toZ x % (2 ^ 32 : Nat)).toNat
/-- `%Ld` of `camlint64_of_coqint` / `camlint64_of_ptrofs` -/
def ci64 {α} [CamlNum α] (x : α) : String := toString (wrapSigned 64 (CamlNum.toZ x))
/-- `%Lu` of `camlint64_of_coqint` -/
def cu64 {α} [CamlNum α] (x : α) : String := toString (CamlNum.toZ x % (2 ^ 64 : Nat))
/-- `%Lx` of `camlint64_of_coqint` -/
def cx64 {α} [CamlNum α] (x : α) : String := hexOfNat (CamlNum.toZ x % (2 ^ 64 : Nat)).toNat

#guard ci32 (Integers.Int.repr (-5)) = "-5"
#guard cu32 (Integers.Int.repr (-1)) = "4294967295"
#guard cx32 (Integers.Int.repr 255) = "ff"
#guard ci64 (Integers.Int64.repr (-7)) = "-7"
#guard zs (-3 : Int) = "-3"

/-- `%<w>d`: right-justify `s` in a field of `w` characters. -/
def lpad (w : Nat) (s : String) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

#guard lpad 5 "12" = "   12"

end Camlcoq
end CC
