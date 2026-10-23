/-
  Runtime values — port of the definitional part of `common/Values.v`
  (lines 1–1080, ~5 % proof; the remaining ~1650 lines are algebraic properties
  and the `lessdef`/`inject` relations used only by CompCert's pass proofs).

  `val` itself is a plain 6-constructor inductive — no dependent typing — so this
  is a direct transcription.  Every operation returns `Vundef` (or `none`) where
  CompCert does, which is how undefined behaviour is propagated.

  Pointer comparisons take the memory's validity predicates as *parameters*
  (`valid_ptr`, `weak_valid_ptr`), exactly as in CompCert: `Values.v` does not
  depend on `Memory.v`, and `Cop.cmp_ptr` supplies `Mem.valid_pointer`.  That
  keeps this layer memory-free and independently testable.
-/
import CCLib.common.AST

namespace CC

open Integers (Int Int64 Ptrofs)

/-- `Values.val` -/
inductive Val where
  | Vundef
  | Vint (n : Integers.Int)
  | Vlong (n : Integers.Int64)
  | Vfloat (f : Floats.Float)
  | Vsingle (f : Floats.Float32)
  | Vptr (b : Block) (ofs : Integers.Ptrofs)
  deriving DecidableEq, Repr, Inhabited

namespace Val

/-! ## Constants -/

def Vzero : Val := .Vint Integers.Int.zero
def Vone : Val := .Vint Integers.Int.one
def Vmone : Val := .Vint Integers.Int.mone
def Vtrue : Val := .Vint Integers.Int.one
def Vfalse : Val := .Vint Integers.Int.zero

/-- `Values.Vnullptr` -/
def Vnullptr : Val :=
  if Archi.ptr64 then .Vlong Integers.Int64.zero else .Vint Integers.Int.zero

/-- `Values.Vptrofs` — inject a pointer offset as an integer value. -/
def Vptrofs (n : Integers.Ptrofs) : Val :=
  if Archi.ptr64 then .Vlong (Integers.Ptrofs.to_int64 n)
  else .Vint (Integers.Ptrofs.to_int n)

/-- `Values.of_bool` -/
def ofBool (b : Bool) : Val := if b then Vtrue else Vfalse
/-- `Values.is_bool` -/
def isBool (v : Val) : Bool := v == Vtrue || v == Vfalse
/-- `Values.norm_bool` -/
def normBool (v : Val) : Val := if isBool v then v else .Vundef

/-! ## Typing -/

/-- `Values.has_type` (as a `Bool`; CompCert states it as a `Prop`). -/
def hasType (v : Val) (t : ATyp) : Bool :=
  match v, t with
  | .Vundef, _ => true
  | _, .Tany64 => true
  | .Vint _, .Tint => true
  | .Vlong _, .Tlong => true
  | .Vfloat _, .Tfloat => true
  | .Vsingle _, .Tsingle => true
  | .Vptr _ _, .Tint => !Archi.ptr64
  | .Vptr _ _, .Tlong => Archi.ptr64
  | .Vint _, .Tany32 => true
  | .Vsingle _, .Tany32 => true
  | .Vptr _ _, .Tany32 => !Archi.ptr64
  | _, _ => false

/-- `Values.normalize` -/
def normalize (v : Val) (ty : ATyp) : Val :=
  match v, ty with
  | .Vundef, _ => .Vundef
  | .Vint _, .Tint => v
  | .Vlong _, .Tlong => v
  | .Vfloat _, .Tfloat => v
  | .Vsingle _, .Tsingle => v
  | .Vptr _ _, .Tint => if Archi.ptr64 then .Vundef else v
  | .Vptr _ _, .Tany32 => if Archi.ptr64 then .Vundef else v
  | .Vptr _ _, .Tlong => if Archi.ptr64 then v else .Vundef
  | .Vint _, .Tany32 => v
  | .Vsingle _, .Tany32 => v
  | _, .Tany64 => v
  | _, _ => .Vundef

/-- `Values.load_result` — the value obtained by storing then reloading `v`
    with the given chunk. -/
def loadResult (chunk : Chunk) (v : Val) : Val :=
  match chunk, v with
  | .Mbool, .Vint n => normBool (.Vint (Integers.Int.zero_ext 8 n))
  | .Mint8signed, .Vint n => .Vint (Integers.Int.sign_ext 8 n)
  | .Mint8unsigned, .Vint n => .Vint (Integers.Int.zero_ext 8 n)
  | .Mint16signed, .Vint n => .Vint (Integers.Int.sign_ext 16 n)
  | .Mint16unsigned, .Vint n => .Vint (Integers.Int.zero_ext 16 n)
  | .Mint32, .Vint n => .Vint n
  | .Mint32, .Vptr b ofs => if Archi.ptr64 then .Vundef else .Vptr b ofs
  | .Mint64, .Vlong n => .Vlong n
  | .Mint64, .Vptr b ofs => if Archi.ptr64 then .Vptr b ofs else .Vundef
  | .Mfloat32, .Vsingle f => .Vsingle f
  | .Mfloat64, .Vfloat f => .Vfloat f
  | .Many32, .Vint _ => v
  | .Many32, .Vsingle _ => v
  | .Many32, .Vptr _ _ => if Archi.ptr64 then .Vundef else v
  | .Many64, _ => v
  | _, _ => .Vundef

/-! ## Pointer arithmetic -/

/-- `Values.offset_ptr` -/
def offsetPtr (v : Val) (delta : Integers.Ptrofs) : Val :=
  match v with
  | .Vptr b ofs => .Vptr b (Integers.Ptrofs.add ofs delta)
  | _ => .Vundef

/-! ## 32-bit integer operations -/

def neg (v : Val) : Val :=
  match v with | .Vint n => .Vint (Integers.Int.neg n) | _ => .Vundef

def notint (v : Val) : Val :=
  match v with | .Vint n => .Vint (Integers.Int.not n) | _ => .Vundef

/-- `Values.notbool`.  A pointer is always "true", so `!ptr` is `Vfalse` — not
    `Vundef`.  (Caught by the differential test against `common/Values.v`.) -/
def notbool (v : Val) : Val :=
  match v with
  | .Vint n => ofBool (Integers.Int.eq n Integers.Int.zero)
  | .Vptr _ _ => Vfalse
  | _ => .Vundef

/-- `Values.boolval` -/
def boolval (v : Val) : Val :=
  match v with
  | .Vint n => ofBool (!Integers.Int.eq n Integers.Int.zero)
  | .Vptr _ _ => Vtrue
  | _ => .Vundef

def add (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.add n1 n2)
  | .Vptr b1 ofs1, .Vint n2 =>
      if Archi.ptr64 then .Vundef
      else .Vptr b1 (Integers.Ptrofs.add ofs1 (Integers.Ptrofs.of_int n2))
  | .Vint n1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then .Vundef
      else .Vptr b2 (Integers.Ptrofs.add ofs2 (Integers.Ptrofs.of_int n1))
  | _, _ => .Vundef

def sub (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.sub n1 n2)
  | .Vptr b1 ofs1, .Vint n2 =>
      if Archi.ptr64 then .Vundef
      else .Vptr b1 (Integers.Ptrofs.sub ofs1 (Integers.Ptrofs.of_int n2))
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then .Vundef
      else if b1 = b2
           then .Vint (Integers.Ptrofs.to_int (Integers.Ptrofs.sub ofs1 ofs2))
           else .Vundef
  | _, _ => .Vundef

def mul (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.mul n1 n2)
  | _, _ => .Vundef

/-- `Values.divs` — signed division; `none` on division by zero and on the
    `min_signed / -1` overflow (both undefined behaviour in C). -/
def divs (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.eq n2 Integers.Int.zero
         || (Integers.Int.eq n1 (Integers.Int.repr Integers.Int.min_signed)
             && Integers.Int.eq n2 Integers.Int.mone)
      then none else some (.Vint (Integers.Int.divs n1 n2))
  | _, _ => none

def mods (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.eq n2 Integers.Int.zero
         || (Integers.Int.eq n1 (Integers.Int.repr Integers.Int.min_signed)
             && Integers.Int.eq n2 Integers.Int.mone)
      then none else some (.Vint (Integers.Int.mods n1 n2))
  | _, _ => none

def divu (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.eq n2 Integers.Int.zero then none
      else some (.Vint (Integers.Int.divu n1 n2))
  | _, _ => none

def modu (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.eq n2 Integers.Int.zero then none
      else some (.Vint (Integers.Int.modu n1 n2))
  | _, _ => none

def and (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.and n1 n2)
  | _, _ => .Vundef

def or (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.or n1 n2)
  | _, _ => .Vundef

def xor (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vint (Integers.Int.xor n1 n2)
  | _, _ => .Vundef

/-! Shifts: the `ltu amount wordsize` guard lives here (not in `Integers`),
exactly as in CompCert. -/

def shl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.ltu n2 Integers.Int.iwordsize
      then .Vint (Integers.Int.shl n1 n2) else .Vundef
  | _, _ => .Vundef

def shr (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.ltu n2 Integers.Int.iwordsize
      then .Vint (Integers.Int.shr n1 n2) else .Vundef
  | _, _ => .Vundef

def shru (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 =>
      if Integers.Int.ltu n2 Integers.Int.iwordsize
      then .Vint (Integers.Int.shru n1 n2) else .Vundef
  | _, _ => .Vundef

def zeroExt (nbits : Nat) (v : Val) : Val :=
  match v with
  | .Vint n => .Vint (Integers.Int.zero_ext nbits n)
  | _ => .Vundef

def signExt (nbits : Nat) (v : Val) : Val :=
  match v with
  | .Vint n => .Vint (Integers.Int.sign_ext nbits n)
  | _ => .Vundef

/-! ## 64-bit integer operations -/

def negl (v : Val) : Val :=
  match v with | .Vlong n => .Vlong (Integers.Int64.neg n) | _ => .Vundef

def notl (v : Val) : Val :=
  match v with | .Vlong n => .Vlong (Integers.Int64.not n) | _ => .Vundef

def addl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.add n1 n2)
  | .Vptr b1 ofs1, .Vlong n2 =>
      if Archi.ptr64
      then .Vptr b1 (Integers.Ptrofs.add ofs1 (Integers.Ptrofs.of_int64 n2))
      else .Vundef
  | .Vlong n1, .Vptr b2 ofs2 =>
      if Archi.ptr64
      then .Vptr b2 (Integers.Ptrofs.add ofs2 (Integers.Ptrofs.of_int64 n1))
      else .Vundef
  | _, _ => .Vundef

def subl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.sub n1 n2)
  | .Vptr b1 ofs1, .Vlong n2 =>
      if Archi.ptr64
      then .Vptr b1 (Integers.Ptrofs.sub ofs1 (Integers.Ptrofs.of_int64 n2))
      else .Vundef
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if !Archi.ptr64 then .Vundef
      else if b1 = b2
           then .Vlong (Integers.Ptrofs.to_int64 (Integers.Ptrofs.sub ofs1 ofs2))
           else .Vundef
  | _, _ => .Vundef

def mull (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.mul n1 n2)
  | _, _ => .Vundef

def divls (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if Integers.Int64.eq n2 Integers.Int64.zero
         || (Integers.Int64.eq n1 (Integers.Int64.repr Integers.Int64.min_signed)
             && Integers.Int64.eq n2 Integers.Int64.mone)
      then none else some (.Vlong (Integers.Int64.divs n1 n2))
  | _, _ => none

def modls (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if Integers.Int64.eq n2 Integers.Int64.zero
         || (Integers.Int64.eq n1 (Integers.Int64.repr Integers.Int64.min_signed)
             && Integers.Int64.eq n2 Integers.Int64.mone)
      then none else some (.Vlong (Integers.Int64.mods n1 n2))
  | _, _ => none

def divlu (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if Integers.Int64.eq n2 Integers.Int64.zero then none
      else some (.Vlong (Integers.Int64.divu n1 n2))
  | _, _ => none

def modlu (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 =>
      if Integers.Int64.eq n2 Integers.Int64.zero then none
      else some (.Vlong (Integers.Int64.modu n1 n2))
  | _, _ => none

def andl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.and n1 n2)
  | _, _ => .Vundef

def orl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.or n1 n2)
  | _, _ => .Vundef

def xorl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => .Vlong (Integers.Int64.xor n1 n2)
  | _, _ => .Vundef

/-- 64-bit shifts take a 32-bit shift amount, guarded by `Int64.iwordsize'`
    (i.e. 64 as a 32-bit integer). -/
private def ltu64 (n : Integers.Int) : Bool :=
  Integers.Int.ltu n (Integers.Int.repr 64)

def shll (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if ltu64 n2
      then .Vlong (Integers.Int64.shl n1 (Integers.Int64.repr (Integers.Int.unsigned n2)))
      else .Vundef
  | _, _ => .Vundef

def shrl (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if ltu64 n2
      then .Vlong (Integers.Int64.shr n1 (Integers.Int64.repr (Integers.Int.unsigned n2)))
      else .Vundef
  | _, _ => .Vundef

def shrlu (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vlong n1, .Vint n2 =>
      if ltu64 n2
      then .Vlong (Integers.Int64.shru n1 (Integers.Int64.repr (Integers.Int.unsigned n2)))
      else .Vundef
  | _, _ => .Vundef

/-! ## Word surgery and int/long conversions -/

def longofwords (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vlong (Integers.Int64.ofwords n1 n2)
  | _, _ => .Vundef

def loword (v : Val) : Val :=
  match v with | .Vlong n => .Vint (Integers.Int64.loword n) | _ => .Vundef

def hiword (v : Val) : Val :=
  match v with | .Vlong n => .Vint (Integers.Int64.hiword n) | _ => .Vundef

/-- `Values.longofint` — sign-extend a 32-bit int to 64 bits. -/
def longofint (v : Val) : Val :=
  match v with
  | .Vint n => .Vlong (Integers.Int64.repr (Integers.Int.signed n))
  | _ => .Vundef

/-- `Values.longofintu` — zero-extend a 32-bit int to 64 bits. -/
def longofintu (v : Val) : Val :=
  match v with
  | .Vint n => .Vlong (Integers.Int64.repr (Integers.Int.unsigned n))
  | _ => .Vundef

/-- `Values.loword`-style truncation of a long to an int. -/
def intoflong (v : Val) : Val :=
  match v with
  | .Vlong n => .Vint (Integers.Int.repr (Integers.Int64.unsigned n))
  | _ => .Vundef

/-! ## Floating-point operations -/

def negf (v : Val) : Val :=
  match v with | .Vfloat f => .Vfloat (Floats.Float.neg f) | _ => .Vundef
def absf (v : Val) : Val :=
  match v with | .Vfloat f => .Vfloat (Floats.Float.abs f) | _ => .Vundef
def addf (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (Floats.Float.add f1 f2) | _, _ => .Vundef
def subf (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (Floats.Float.sub f1 f2) | _, _ => .Vundef
def mulf (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (Floats.Float.mul f1 f2) | _, _ => .Vundef
def divf (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => .Vfloat (Floats.Float.div f1 f2) | _, _ => .Vundef

def negfs (v : Val) : Val :=
  match v with | .Vsingle f => .Vsingle (Floats.Float32.neg f) | _ => .Vundef
def absfs (v : Val) : Val :=
  match v with | .Vsingle f => .Vsingle (Floats.Float32.abs f) | _ => .Vundef
def addfs (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (Floats.Float32.add f1 f2) | _, _ => .Vundef
def subfs (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (Floats.Float32.sub f1 f2) | _, _ => .Vundef
def mulfs (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (Floats.Float32.mul f1 f2) | _, _ => .Vundef
def divfs (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => .Vsingle (Floats.Float32.div f1 f2) | _, _ => .Vundef

/-- `Values.singleoffloat` -/
def singleoffloat (v : Val) : Val :=
  match v with | .Vfloat f => .Vsingle (Floats.Float.toSingle f) | _ => .Vundef
/-- `Values.floatofsingle` -/
def floatofsingle (v : Val) : Val :=
  match v with | .Vsingle f => .Vfloat (Floats.Float.ofSingle f) | _ => .Vundef

/-! Float↔int conversions are partial: `none` when the value is NaN or out of
range, which is undefined behaviour in C. -/

def intoffloat (v : Val) : Option Val :=
  match v with | .Vfloat f => (Floats.Float.toInt f).map .Vint | _ => none
def intuoffloat (v : Val) : Option Val :=
  match v with | .Vfloat f => (Floats.Float.toIntu f).map .Vint | _ => none
def longoffloat (v : Val) : Option Val :=
  match v with | .Vfloat f => (Floats.Float.toLong f).map .Vlong | _ => none
def longuoffloat (v : Val) : Option Val :=
  match v with | .Vfloat f => (Floats.Float.toLongu f).map .Vlong | _ => none

def floatofint (v : Val) : Option Val :=
  match v with | .Vint n => some (.Vfloat (Floats.Float.ofInt n)) | _ => none
def floatofintu (v : Val) : Option Val :=
  match v with | .Vint n => some (.Vfloat (Floats.Float.ofIntu n)) | _ => none
def floatoflong (v : Val) : Option Val :=
  match v with | .Vlong n => some (.Vfloat (Floats.Float.ofLong n)) | _ => none
def floatoflongu (v : Val) : Option Val :=
  match v with | .Vlong n => some (.Vfloat (Floats.Float.ofLongu n)) | _ => none

/-! ## Comparisons

`cmp_bool`/`cmpl_bool` are pure; the unsigned ones take the memory validity
predicates as parameters (see the file header). -/

/-- `Values.cmp_different_blocks` -/
def cmpDifferentBlocks (c : Comparison) : Option Bool :=
  match c with
  | .Ceq => some false
  | .Cne => some true
  | _ => none

def cmp_bool (c : Comparison) (v1 v2 : Val) : Option Bool :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => some (Integers.Int.cmp c n1 n2)
  | _, _ => none

def cmpl_bool (c : Comparison) (v1 v2 : Val) : Option Bool :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => some (Integers.Int64.cmp c n1 n2)
  | _, _ => none

def cmpf_bool (c : Comparison) (v1 v2 : Val) : Option Bool :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 => some (Floats.Float.cmp c f1 f2)
  | _, _ => none

def cmpfs_bool (c : Comparison) (v1 v2 : Val) : Option Bool :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 => some (Floats.Float32.cmp c f1 f2)
  | _, _ => none

/-- `Values.weak_valid_ptr` — the `Let` bound inside CompCert's
    `Section COMPARISONS`: valid at `ofs`, or one-past-the-end at `ofs - 1`. -/
def weakValidPtr (validPtr : Block → Z → Bool) (b : Block) (ofs : Z) : Bool :=
  validPtr b ofs || validPtr b (ofs - 1)

/-- `Values.cmpu_bool` — unsigned/pointer comparison at 32 bits.  Takes the
    single `valid_ptr` predicate from the memory state, exactly as CompCert's
    `Section COMPARISONS` does; the weak variant is derived. -/
def cmpu_bool (validPtr : Block → Z → Bool)
    (c : Comparison) (v1 v2 : Val) : Option Bool :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => some (Integers.Int.cmpu c n1 n2)
  | .Vint n1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then none
      else if Integers.Int.eq n1 Integers.Int.zero
              && weakValidPtr validPtr b2 (Integers.Ptrofs.unsigned ofs2)
           then cmpDifferentBlocks c else none
  | .Vptr b1 ofs1, .Vint n2 =>
      if Archi.ptr64 then none
      else if Integers.Int.eq n2 Integers.Int.zero
              && weakValidPtr validPtr b1 (Integers.Ptrofs.unsigned ofs1)
           then cmpDifferentBlocks c else none
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if Archi.ptr64 then none
      else if b1 = b2 then
        if weakValidPtr validPtr b1 (Integers.Ptrofs.unsigned ofs1)
           && weakValidPtr validPtr b2 (Integers.Ptrofs.unsigned ofs2)
        then some (Integers.Ptrofs.cmpu c ofs1 ofs2) else none
      else
        if validPtr b1 (Integers.Ptrofs.unsigned ofs1)
           && validPtr b2 (Integers.Ptrofs.unsigned ofs2)
        then cmpDifferentBlocks c else none
  | _, _ => none

/-- `Values.cmplu_bool` — unsigned/pointer comparison at 64 bits. -/
def cmplu_bool (validPtr : Block → Z → Bool)
    (c : Comparison) (v1 v2 : Val) : Option Bool :=
  match v1, v2 with
  | .Vlong n1, .Vlong n2 => some (Integers.Int64.cmpu c n1 n2)
  | .Vlong n1, .Vptr b2 ofs2 =>
      if !Archi.ptr64 then none
      else if Integers.Int64.eq n1 Integers.Int64.zero
              && weakValidPtr validPtr b2 (Integers.Ptrofs.unsigned ofs2)
           then cmpDifferentBlocks c else none
  | .Vptr b1 ofs1, .Vlong n2 =>
      if !Archi.ptr64 then none
      else if Integers.Int64.eq n2 Integers.Int64.zero
              && weakValidPtr validPtr b1 (Integers.Ptrofs.unsigned ofs1)
           then cmpDifferentBlocks c else none
  | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
      if !Archi.ptr64 then none
      else if b1 = b2 then
        if weakValidPtr validPtr b1 (Integers.Ptrofs.unsigned ofs1)
           && weakValidPtr validPtr b2 (Integers.Ptrofs.unsigned ofs2)
        then some (Integers.Ptrofs.cmpu c ofs1 ofs2) else none
      else
        if validPtr b1 (Integers.Ptrofs.unsigned ofs1)
           && validPtr b2 (Integers.Ptrofs.unsigned ofs2)
        then cmpDifferentBlocks c else none
  | _, _ => none

/-- Lift an `option bool` comparison result to a value (`Values.of_optbool`). -/
def ofOptbool : Option Bool → Val
  | some b => ofBool b
  | none => .Vundef

def cmp (c : Comparison) (v1 v2 : Val) : Val := ofOptbool (cmp_bool c v1 v2)
/-- `Values.cmpl`: unlike `cmp`, it is partial (`none` when the comparison
    is undefined), as in CompCert. -/
def cmpl (c : Comparison) (v1 v2 : Val) : Option Val := (cmpl_bool c v1 v2).map ofBool
def cmpf (c : Comparison) (v1 v2 : Val) : Val := ofOptbool (cmpf_bool c v1 v2)
def cmpfs (c : Comparison) (v1 v2 : Val) : Val := ofOptbool (cmpfs_bool c v1 v2)

end Val
end CC
