/-
  Built-in functions — port of `common/Builtins0.v`, `aarch64/Builtins1.v` and
  `common/Builtins.v`.

  A built-in function has a semantics given by a partial function from
  argument values to a result value (`BuiltinSem`), which must agree with the
  declared result type and commute with memory injections.  The standard
  built-ins (`__builtin_fabs`, `__builtin_fsqrt`, `__builtin_bswap*`,
  `__builtin_sel`, the `__compcert_i64_*` runtime helpers, …) are listed in
  `standardBuiltinTable`; aarch64 has no platform-specific built-ins.

  Rocq builds each entry with generic constructors over dependent "numeric
  types" (`valty`, `valxty`); here each semantic function is written out
  directly on values and the two obligations are proved once, by case
  analysis, for the whole table.
-/
import CCLib.common.ValuesLemmas
import CCLib.common.Memdata
import CCLib.lib.FloatsLemmas

namespace CC

open Integers (Int Int64 Ptrofs)

/-! ## Typing and injection of optional results (`Builtins0.v`) -/

/-- `Values.Val.has_rettype` -/
def Val.hasRettype (v : Val) (r : XType) : Prop :=
  match r, v with
  | .Xbool, .Vint n => n = Integers.Int.zero ∨ n = Integers.Int.one
  | .Xint8signed, .Vint n => n = Integers.Int.sign_ext 8 n
  | .Xint8unsigned, .Vint n => n = Integers.Int.zero_ext 8 n
  | .Xint16signed, .Vint n => n = Integers.Int.sign_ext 16 n
  | .Xint16unsigned, .Vint n => n = Integers.Int.zero_ext 16 n
  | .Xint, .Vint _ => True
  | .Xint, .Vptr _ _ => Archi.ptr64 = false
  | .Xlong, .Vlong _ => True
  | .Xlong, .Vptr _ _ => Archi.ptr64 = true
  | .Xfloat, .Vfloat _ => True
  | .Xsingle, .Vsingle _ => True
  | .Xptr, .Vptr _ _ => True
  | .Xptr, .Vint _ => Archi.ptr64 = false
  | .Xptr, .Vlong _ => Archi.ptr64 = true
  | .Xany32, .Vint _ => True
  | .Xany32, .Vsingle _ => True
  | .Xany32, .Vptr _ _ => Archi.ptr64 = false
  | .Xany64, _ => True
  | _, .Vundef => True
  | _, _ => False

/-- `Values.Val.mull'`: full 32×32→64 unsigned product. -/
def Val.mull' (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .Vint n1, .Vint n2 => .Vlong (Integers.Int64.mul' n1 n2)
  | _, _ => .Vundef

namespace Builtins

/-- `Builtins0.val_opt_has_rettype` -/
def valOptHasRettype (ov : Option Val) (t : XType) : Prop :=
  match ov with
  | some v => Val.hasRettype v t
  | none => True

/-- `Builtins0.val_opt_inject` -/
def valOptInject (j : Val.Meminj) (ov ov' : Option Val) : Prop :=
  match ov, ov' with
  | none, _ => True
  | some v, some v' => Val.Inject j v v'
  | some _, none => False

/-- `Builtins0.builtin_sem`: the semantics of a built-in with result type
`tret`. -/
structure BuiltinSem (tret : XType) where
  sem : List Val → Option Val
  well_typed : ∀ vl, valOptHasRettype (sem vl) tret
  inject : ∀ j vl vl', Val.InjectList j vl vl' → valOptInject j (sem vl) (sem vl')

/-! ## Standard built-ins -/

/-- `Builtins0.standard_builtin` -/
inductive StandardBuiltin where
  | BI_select (t : ATyp)
  | BI_fabs
  | BI_fabsf
  | BI_fsqrt
  | BI_negl
  | BI_addl
  | BI_subl
  | BI_mull
  | BI_i16_bswap
  | BI_i32_bswap
  | BI_i64_bswap
  | BI_unreachable
  | BI_i64_umulh
  | BI_i64_smulh
  | BI_i64_sdiv
  | BI_i64_udiv
  | BI_i64_smod
  | BI_i64_umod
  | BI_i64_shl
  | BI_i64_shr
  | BI_i64_sar
  | BI_i64_dtos
  | BI_i64_dtou
  | BI_i64_stod
  | BI_i64_utod
  | BI_i64_stof
  | BI_i64_utof
  deriving DecidableEq, Repr

open StandardBuiltin

/-- `Builtins0.standard_builtin_table` -/
def standardBuiltinTable : List (String × StandardBuiltin) :=
  [ ("__builtin_sel", BI_select .Tint),
    ("__builtin_sel", BI_select .Tlong),
    ("__builtin_sel", BI_select .Tfloat),
    ("__builtin_sel", BI_select .Tsingle),
    ("__builtin_fabs", BI_fabs),
    ("__builtin_fabsf", BI_fabsf),
    ("__builtin_fsqrt", BI_fsqrt),
    ("__builtin_sqrt", BI_fsqrt),
    ("__builtin_negl", BI_negl),
    ("__builtin_addl", BI_addl),
    ("__builtin_subl", BI_subl),
    ("__builtin_mull", BI_mull),
    ("__builtin_bswap16", BI_i16_bswap),
    ("__builtin_bswap", BI_i32_bswap),
    ("__builtin_bswap32", BI_i32_bswap),
    ("__builtin_bswap64", BI_i64_bswap),
    ("__builtin_unreachable", BI_unreachable),
    ("__compcert_i64_umulh", BI_i64_umulh),
    ("__compcert_i64_smulh", BI_i64_smulh),
    ("__compcert_i64_sdiv", BI_i64_sdiv),
    ("__compcert_i64_udiv", BI_i64_udiv),
    ("__compcert_i64_smod", BI_i64_smod),
    ("__compcert_i64_umod", BI_i64_umod),
    ("__compcert_i64_shl", BI_i64_shl),
    ("__compcert_i64_shr", BI_i64_shr),
    ("__compcert_i64_sar", BI_i64_sar),
    ("__compcert_i64_dtos", BI_i64_dtos),
    ("__compcert_i64_dtou", BI_i64_dtou),
    ("__compcert_i64_stod", BI_i64_stod),
    ("__compcert_i64_utod", BI_i64_utod),
    ("__compcert_i64_stof", BI_i64_stof),
    ("__compcert_i64_utof", BI_i64_utof) ]

/-- `[args ---> res]` with the default calling convention. -/
abbrev sig (args : List XType) (res : XType) : Signature := mksignature args res cc_default

/-- `Builtins0.standard_builtin_sig` -/
def standardBuiltinSig : StandardBuiltin → Signature
  | BI_select t => sig [.Xint, t.inj, t.inj] t.inj
  | BI_fabs | BI_fsqrt => sig [.Xfloat] .Xfloat
  | BI_fabsf => sig [.Xsingle] .Xsingle
  | BI_negl => sig [.Xlong] .Xlong
  | BI_addl | BI_subl | BI_i64_umulh | BI_i64_smulh
  | BI_i64_sdiv | BI_i64_udiv | BI_i64_smod | BI_i64_umod => sig [.Xlong, .Xlong] .Xlong
  | BI_mull => sig [.Xint, .Xint] .Xlong
  | BI_i32_bswap => sig [.Xint] .Xint
  | BI_i64_bswap => sig [.Xlong] .Xlong
  | BI_i16_bswap => sig [.Xint16unsigned] .Xint16unsigned
  | BI_unreachable => sig [] .Xvoid
  | BI_i64_shl | BI_i64_shr | BI_i64_sar => sig [.Xlong, .Xint] .Xlong
  | BI_i64_dtos | BI_i64_dtou => sig [.Xfloat] .Xlong
  | BI_i64_stod | BI_i64_utod => sig [.Xlong] .Xfloat
  | BI_i64_stof | BI_i64_utof => sig [.Xlong] .Xsingle

/-- Byte swap of the low `n` bytes of `x`
(`decode_int (rev (encode_int n x))`). -/
def bswap (n : Nat) (x : Z) : Z := decodeInt (List.reverse (encodeInt n x))

/-- Built-ins of one, two or three arguments (Rocq's `mkbuiltin_v1p`, …): any
other number of arguments makes the built-in undefined. -/
def fn1 (f : Val → Option Val) : List Val → Option Val
  | [v] => f v
  | _ => none
def fn2 (f : Val → Val → Option Val) : List Val → Option Val
  | [v1, v2] => f v1 v2
  | _ => none
def fn3 (f : Val → Val → Val → Option Val) : List Val → Option Val
  | [v1, v2, v3] => f v1 v2 v3
  | _ => none

/-- `__builtin_sel` -/
def selectFn (t : ATyp) (v0 v1 v2 : Val) : Option Val :=
  match v0 with
  | .Vint n => some (Val.normalize (if Integers.Int.eq n Integers.Int.zero then v2 else v1) t)
  | _ => none

/-- A numeric function of one argument (Rocq's `mkbuiltin_n1t`/`mkbuiltin_n1p`,
through `proj_num`).  On an argument of the wrong type, the result is `dflt`:
`some Vundef` for the total built-ins (`mkbuiltin_n1t`, the default) and `none`
for the partial ones (`mkbuiltin_n1p`), as in Rocq. -/
def floatFn (f : Floats.Float → Option Val) (dflt : Option Val := some .Vundef) :
    Val → Option Val
  | .Vfloat x => f x | _ => dflt
def singleFn (f : Floats.Float32 → Option Val) (dflt : Option Val := some .Vundef) :
    Val → Option Val
  | .Vsingle x => f x | _ => dflt
def longFn (f : Integers.Int64 → Option Val) (dflt : Option Val := some .Vundef) :
    Val → Option Val
  | .Vlong x => f x | _ => dflt
def intFn (f : Integers.Int → Option Val) (dflt : Option Val := some .Vundef) :
    Val → Option Val
  | .Vint x => f x | _ => dflt
/-- A numeric function of two arguments (`mkbuiltin_n2t`): `Vundef` on
arguments of the wrong type. -/
def long2Fn (f : Integers.Int64 → Integers.Int64 → Option Val) : Val → Val → Option Val
  | .Vlong x, .Vlong y => f x y | _, _ => some .Vundef

/-- The semantic function of each standard built-in
(`Builtins0.standard_builtin_sem`, field `bs_sem`). -/
def standardBuiltinFn : StandardBuiltin → List Val → Option Val
  | BI_select t => fn3 (selectFn t)
  | BI_fabs => fn1 (floatFn fun f => some (.Vfloat (Floats.Float.abs f)))
  | BI_fabsf => fn1 (singleFn fun f => some (.Vsingle (Floats.Float32.abs f)))
  | BI_fsqrt => fn1 (floatFn fun f => some (.Vfloat (Floats.Float.sqrt f)))
  | BI_negl => fn1 (longFn fun n => some (.Vlong (Integers.Int64.neg n)))
  | BI_addl => fn2 fun v1 v2 => some (Val.addl v1 v2)
  | BI_subl => fn2 fun v1 v2 => some (Val.subl v1 v2)
  | BI_mull => fn2 fun v1 v2 => some (Val.mull' v1 v2)
  | BI_i16_bswap => fn1 (intFn fun n => some (.Vint (Integers.Int.repr (bswap 2 (Integers.Int.unsigned n)))))
  | BI_i32_bswap => fn1 (intFn fun n => some (.Vint (Integers.Int.repr (bswap 4 (Integers.Int.unsigned n)))))
  | BI_i64_bswap => fn1 (longFn fun n => some (.Vlong (Integers.Int64.repr (bswap 8 (Integers.Int64.unsigned n)))))
  | BI_unreachable => fun _ => none
  | BI_i64_umulh => fn2 (long2Fn fun n1 n2 => some (.Vlong (Integers.Int64.mulhu n1 n2)))
  | BI_i64_smulh => fn2 (long2Fn fun n1 n2 => some (.Vlong (Integers.Int64.mulhs n1 n2)))
  | BI_i64_sdiv => fn2 Val.divls
  | BI_i64_udiv => fn2 Val.divlu
  | BI_i64_smod => fn2 Val.modls
  | BI_i64_umod => fn2 Val.modlu
  | BI_i64_shl => fn2 fun v1 v2 => some (Val.shll v1 v2)
  | BI_i64_shr => fn2 fun v1 v2 => some (Val.shrlu v1 v2)
  | BI_i64_sar => fn2 fun v1 v2 => some (Val.shrl v1 v2)
  | BI_i64_dtos => fn1 (floatFn (fun f => (Floats.Float.toLong f).map .Vlong) none)
  | BI_i64_dtou => fn1 (floatFn (fun f => (Floats.Float.toLongu f).map .Vlong) none)
  | BI_i64_stod => fn1 (longFn fun n => some (.Vfloat (Floats.Float.ofLong n)))
  | BI_i64_utod => fn1 (longFn fun n => some (.Vfloat (Floats.Float.ofLongu n)))
  | BI_i64_stof => fn1 (longFn fun n => some (.Vsingle (Floats.Float32.ofLong n)))
  | BI_i64_utof => fn1 (longFn fun n => some (.Vsingle (Floats.Float32.ofLongu n)))

end Builtins
end CC

namespace CC
namespace Builtins
open StandardBuiltin

theorem hasRettype_normalize (v : Val) (t : ATyp) : Val.hasRettype (Val.normalize v t) t.inj := by
  cases v <;> cases t <;> simp [Val.normalize, Val.hasRettype, ATyp.inj, Archi.ptr64]

theorem normalize_inject {j : Val.Meminj} {v v' : Val} (h : Val.Inject j v v') (t : ATyp) :
    Val.Inject j (Val.normalize v t) (Val.normalize v' t) := by
  cases h <;> cases t <;> simp [Val.normalize, Archi.ptr64] <;>
    first | exact .int _ | exact .long _ | exact .float _ | exact .single _ | exact .undef _ | (apply Val.Inject.ptr <;> assumption)

theorem hasRettype_addl (v1 v2 : Val) : Val.hasRettype (Val.addl v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.addl] <;> (repeat' split) <;>
    simp_all [Val.hasRettype]
theorem hasRettype_subl (v1 v2 : Val) : Val.hasRettype (Val.subl v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.subl] <;> (repeat' split) <;>
    simp_all [Val.hasRettype]
theorem hasRettype_mull' (v1 v2 : Val) : Val.hasRettype (Val.mull' v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.mull'] <;> (repeat' split) <;>
    simp_all [Val.hasRettype]
theorem hasRettype_shll (v1 v2 : Val) : Val.hasRettype (Val.shll v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.shll] <;> (repeat' split) <;>
    simp_all [Val.hasRettype]
theorem hasRettype_shrl (v1 v2 : Val) : Val.hasRettype (Val.shrl v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.shrl] <;> (repeat' split) <;>
    simp_all [Val.hasRettype]
theorem hasRettype_shrlu (v1 v2 : Val) : Val.hasRettype (Val.shrlu v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.shrlu] <;> (repeat' split) <;>
    simp_all [Val.hasRettype]
theorem optRettype_divls (v1 v2 : Val) : valOptHasRettype (Val.divls v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.divls] <;> (repeat' split) <;>
    simp_all [valOptHasRettype, Val.hasRettype]
theorem optRettype_modls (v1 v2 : Val) : valOptHasRettype (Val.modls v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.modls] <;> (repeat' split) <;>
    simp_all [valOptHasRettype, Val.hasRettype]
theorem optRettype_divlu (v1 v2 : Val) : valOptHasRettype (Val.divlu v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.divlu] <;> (repeat' split) <;>
    simp_all [valOptHasRettype, Val.hasRettype]
theorem optRettype_modlu (v1 v2 : Val) : valOptHasRettype (Val.modlu v1 v2) .Xlong := by
  cases v1 <;> cases v2 <;> simp only [Val.modlu] <;> (repeat' split) <;>
    simp_all [valOptHasRettype, Val.hasRettype]
theorem optRettype_map_long (o : Option Integers.Int64) :
    valOptHasRettype (o.map .Vlong) .Xlong := by
  cases o <;> simp [valOptHasRettype, Val.hasRettype]

theorem byte_unsigned_bound (b : Integers.Byte) :
    0 ≤ Integers.Byte.unsigned b ∧ Integers.Byte.unsigned b < 256 :=
  Integers.MI.unsigned_range b

-- Arithmetic is stated over `_root_.Int` binders: `omega` does not see through
-- `abbrev Z := Int` (see the note in `CCLib/common/MemdataLemmas.lean`).
private theorem arith_bswap2 (a b : _root_.Int) (ha : 0 ≤ a ∧ a < 256) (hb : 0 ≤ b ∧ b < 256) :
    0 ≤ b + (a + 0 * 256) * 256 ∧ b + (a + 0 * 256) * 256 < 65536 := by omega

/-- `bswap 2` is a 16-bit quantity. -/
theorem bswap2_range (x : Z) : 0 ≤ bswap 2 x ∧ bswap 2 x < 65536 := by
  simp only [bswap, decodeInt, encodeInt, revIfBe, Archi.big_endian, bytesOfInt,
    Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, intOfBytes]
  exact arith_bswap2 _ _ (byte_unsigned_bound _) (byte_unsigned_bound _)

private theorem arith_le_max (z : _root_.Int) (h1 : z < 65536) : z ≤ 4294967295 := by omega
private theorem arith_mod16 (z : _root_.Int) (h0 : 0 ≤ z) (h1 : z < 65536) : z % 2 ^ 16 = z :=
  Int.emod_eq_of_lt h0 (by omega)

theorem zero_ext_16_of_range {z : Z} (h0 : 0 ≤ z) (h1 : z < 65536) :
    Integers.Int.repr z = Integers.Int.zero_ext 16 (Integers.Int.repr z) := by
  have hmax : Integers.Int.max_unsigned = 4294967295 := by decide
  have hu : Integers.Int.unsigned (Integers.Int.repr z) = z :=
    Integers.Int.unsigned_repr h0 (by rw [hmax]; exact arith_le_max z h1)
  apply Integers.MI.unsigned_inj
  show Integers.Int.unsigned _ = Integers.Int.unsigned _
  rw [Integers.Int.zero_ext_mod, hu, arith_mod16 z h0 h1]

theorem fn1_wt {f : Val → Option Val} {t : XType} (h : ∀ v, valOptHasRettype (f v) t)
    (vl : List Val) : valOptHasRettype (fn1 f vl) t := by
  unfold fn1; split
  · exact h _
  · trivial
theorem fn2_wt {f : Val → Val → Option Val} {t : XType}
    (h : ∀ v1 v2, valOptHasRettype (f v1 v2) t) (vl : List Val) :
    valOptHasRettype (fn2 f vl) t := by
  unfold fn2; split
  · exact h _ _
  · trivial
theorem fn3_wt {f : Val → Val → Val → Option Val} {t : XType}
    (h : ∀ v1 v2 v3, valOptHasRettype (f v1 v2 v3) t) (vl : List Val) :
    valOptHasRettype (fn3 f vl) t := by
  unfold fn3; split
  · exact h _ _ _
  · trivial

theorem standardBuiltinFn_wt (b : StandardBuiltin) (vl : List Val) :
    valOptHasRettype (standardBuiltinFn b vl) (standardBuiltinSig b).sig_res := by
  cases b <;> simp only [standardBuiltinFn, standardBuiltinSig, sig, mksignature]
  case BI_select t => exact fn3_wt (fun v0 v1 v2 => by
    cases v0 <;> first | trivial | exact hasRettype_normalize _ _) vl
  case BI_addl => apply fn2_wt; intro _ _; exact hasRettype_addl _ _
  case BI_subl => apply fn2_wt; intro _ _; exact hasRettype_subl _ _
  case BI_mull => apply fn2_wt; intro _ _; exact hasRettype_mull' _ _
  case BI_i64_shl => apply fn2_wt; intro _ _; exact hasRettype_shll _ _
  case BI_i64_shr => apply fn2_wt; intro _ _; exact hasRettype_shrlu _ _
  case BI_i64_sar => apply fn2_wt; intro _ _; exact hasRettype_shrl _ _
  case BI_i64_sdiv => exact fn2_wt optRettype_divls vl
  case BI_i64_udiv => exact fn2_wt optRettype_divlu vl
  case BI_i64_smod => exact fn2_wt optRettype_modls vl
  case BI_i64_umod => exact fn2_wt optRettype_modlu vl
  case BI_i16_bswap =>
    refine fn1_wt (fun v => ?_) vl
    cases v <;> try trivial
    obtain ⟨h0, h1⟩ := bswap2_range (Integers.Int.unsigned _)
    exact zero_ext_16_of_range h0 h1
  case BI_unreachable => trivial
  case BI_i64_umulh | BI_i64_smulh =>
    exact fn2_wt (fun v1 v2 => by cases v1 <;> cases v2 <;> trivial) vl
  case BI_i64_dtos | BI_i64_dtou =>
    exact fn1_wt (fun v => by cases v <;> first | trivial | exact optRettype_map_long _) vl
  all_goals exact fn1_wt (fun v => by cases v <;> trivial) vl

/-! ### Compatibility with memory injections -/

section Inject
variable {j : Val.Meminj}

theorem addl_inject {v1 v1' v2 v2' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2') :
    Val.Inject j (Val.addl v1 v2) (Val.addl v1' v2') := by
  cases h1 <;> cases h2 <;> simp only [Val.addl, Archi.ptr64, ↓reduceIte] <;>
    first
      | exact .long _ | exact .undef _
      | (subst_vars
         exact .ptr _ ‹_› (by
          rw [Integers.Ptrofs.add_assoc, Integers.Ptrofs.add_commut (Integers.Ptrofs.repr _),
            ← Integers.Ptrofs.add_assoc]))

theorem subl_inject {v1 v1' v2 v2' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2') :
    Val.Inject j (Val.subl v1 v2) (Val.subl v1' v2') := by
  cases h1 with
  | ptr d1 hf1 ho1 =>
    cases h2 with
    | long n =>
      simp only [Val.subl, Archi.ptr64, ↓reduceIte]
      exact .ptr d1 hf1 (by rw [ho1, Integers.Ptrofs.sub_add_l])
    | ptr d2 hf2 ho2 =>
      rename_i b1 o1 b1' o1' b2 o2 b2' o2'
      simp only [Val.subl, Archi.ptr64, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hb : b1 = b2
      · subst hb
        rw [hf1] at hf2
        cases hf2
        simp only [↓reduceIte]
        rw [ho1, ho2, Integers.Ptrofs.sub_shifted]
        exact .long _
      · simp only [hb, ↓reduceIte]; exact .undef _
    | _ => simp only [Val.subl]; exact .undef _
  | _ =>
    cases h2 <;> simp only [Val.subl, Archi.ptr64, ↓reduceIte] <;>
      first | exact .long _ | exact .undef _

/-- A value injected from a number is that number. -/
theorem inject_long_inv {n : Integers.Int64} {v : Val} (h : Val.Inject j (.Vlong n) v) :
    v = .Vlong n := by cases h; rfl
theorem inject_int_inv {n : Integers.Int} {v : Val} (h : Val.Inject j (.Vint n) v) :
    v = .Vint n := by cases h; rfl
theorem inject_float_inv {f : Floats.Float} {v : Val} (h : Val.Inject j (.Vfloat f) v) :
    v = .Vfloat f := by cases h; rfl
theorem inject_single_inv {f : Floats.Float32} {v : Val} (h : Val.Inject j (.Vsingle f) v) :
    v = .Vsingle f := by cases h; rfl

theorem valOptInject_map_long (o : Option Integers.Int64) :
    valOptInject j (o.map .Vlong) (o.map .Vlong) := by
  cases o
  · trivial
  · exact Val.Inject.long _

theorem valOptInject_ite_long (c : Prop) [Decidable c] (x : Integers.Int64) :
    valOptInject j (if c then none else some (.Vlong x)) (if c then none else some (.Vlong x)) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; trivial
  · simp only [hc, ↓reduceIte]; exact Val.Inject.long _

theorem divls_inject {v1 v1' v2 v2' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2') :
    valOptInject j (Val.divls v1 v2) (Val.divls v1' v2') := by
  cases h1 <;> cases h2 <;> first | trivial | exact valOptInject_ite_long _ _
theorem modls_inject {v1 v1' v2 v2' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2') :
    valOptInject j (Val.modls v1 v2) (Val.modls v1' v2') := by
  cases h1 <;> cases h2 <;> first | trivial | exact valOptInject_ite_long _ _
theorem divlu_inject {v1 v1' v2 v2' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2') :
    valOptInject j (Val.divlu v1 v2) (Val.divlu v1' v2') := by
  cases h1 <;> cases h2 <;> first | trivial | exact valOptInject_ite_long _ _
theorem modlu_inject {v1 v1' v2 v2' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2') :
    valOptInject j (Val.modlu v1 v2) (Val.modlu v1' v2') := by
  cases h1 <;> cases h2 <;> first | trivial | exact valOptInject_ite_long _ _

theorem fn1_inject {f : Val → Option Val}
    (h : ∀ v v', Val.Inject j v v' → valOptInject j (f v) (f v'))
    {vl vl' : List Val} (hl : Val.InjectList j vl vl') :
    valOptInject j (fn1 f vl) (fn1 f vl') := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, hl⟩⟩
  · trivial
  · exact h _ _ h1
  · trivial
theorem fn2_inject {f : Val → Val → Option Val}
    (h : ∀ v1 v1' v2 v2', Val.Inject j v1 v1' → Val.Inject j v2 v2' →
      valOptInject j (f v1 v2) (f v1' v2'))
    {vl vl' : List Val} (hl : Val.InjectList j vl vl') :
    valOptInject j (fn2 f vl) (fn2 f vl') := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, hl⟩⟩⟩
  · trivial
  · trivial
  · exact h _ _ _ _ h1 h2
  · trivial
theorem fn3_inject {f : Val → Val → Val → Option Val}
    (h : ∀ v1 v1' v2 v2' v3 v3', Val.Inject j v1 v1' → Val.Inject j v2 v2' →
      Val.Inject j v3 v3' → valOptInject j (f v1 v2 v3) (f v1' v2' v3'))
    {vl vl' : List Val} (hl : Val.InjectList j vl vl') :
    valOptInject j (fn3 f vl) (fn3 f vl') := by
  rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, hl⟩⟩⟩⟩
  · trivial
  · trivial
  · trivial
  · exact h _ _ _ _ _ _ h1 h2 h3
  · trivial

/-- Numeric one-argument built-ins: the argument injects only into itself. -/
theorem num1_inject {f : Val → Option Val}
    (hf : f .Vundef = none)
    (hnum : ∀ v, (∃ b o, v = .Vptr b o) → f v = none)
    (hself : ∀ v, valOptInject j (f v) (f v)) :
    ∀ v v', Val.Inject j v v' → valOptInject j (f v) (f v') := by
  intro v v' h
  cases h with
  | undef => rw [hf]; trivial
  | ptr => rw [hnum _ ⟨_, _, rfl⟩]; trivial
  | _ => exact hself _

theorem standardBuiltinFn_inject (b : StandardBuiltin) (vl vl' : List Val)
    (h : Val.InjectList j vl vl') :
    valOptInject j (standardBuiltinFn b vl) (standardBuiltinFn b vl') := by
  cases b <;> simp only [standardBuiltinFn]
  case BI_select t =>
    refine fn3_inject (fun v1 v1' v2 v2' v3 v3' h1 h2 h3 => ?_) h
    cases h1 with
    | int n =>
      exact normalize_inject (by
        by_cases hc : Integers.Int.eq n Integers.Int.zero = true <;>
          simp only [hc, ↓reduceIte, Bool.false_eq_true] <;> assumption) _
    | _ => trivial
  case BI_addl => apply fn2_inject _ h; intro _ _ _ _ h1 h2; exact addl_inject h1 h2
  case BI_subl => apply fn2_inject _ h; intro _ _ _ _ h1 h2; exact subl_inject h1 h2
  case BI_i64_sdiv => apply fn2_inject _ h; intro _ _ _ _ h1 h2; exact divls_inject h1 h2
  case BI_i64_udiv => apply fn2_inject _ h; intro _ _ _ _ h1 h2; exact divlu_inject h1 h2
  case BI_i64_smod => apply fn2_inject _ h; intro _ _ _ _ h1 h2; exact modls_inject h1 h2
  case BI_i64_umod => apply fn2_inject _ h; intro _ _ _ _ h1 h2; exact modlu_inject h1 h2
  case BI_unreachable => trivial
  case BI_mull | BI_i64_shl | BI_i64_shr | BI_i64_sar | BI_i64_umulh | BI_i64_smulh =>
    refine fn2_inject (fun v1 v1' v2 v2' h1 h2 => ?_) h
    cases h1 <;> cases h2 <;>
      simp only [Val.mull', Val.shll, Val.shrl, Val.shrlu, long2Fn] <;> (repeat' split) <;>
      first | trivial | exact .long _ | exact .undef _
  case BI_i64_dtos | BI_i64_dtou =>
    refine fn1_inject (fun v v' h1 => ?_) h
    cases h1 <;> first | trivial | exact valOptInject_map_long _
  all_goals
    refine fn1_inject (fun v v' h1 => ?_) h
    cases h1
    case undef =>
      cases v' <;> simp only [floatFn, singleFn, longFn, intFn, valOptInject] <;>
        exact Val.Inject.undef _
    all_goals (try simp only [floatFn, singleFn, longFn, intFn, valOptInject]) <;>
      first | trivial | constructor

end Inject

/-! ## Packaged semantics and lookup (`Builtins0.v`, `Builtins.v`) -/

/-- `Builtins0.standard_builtin_sem` -/
def standardBuiltinSem (b : StandardBuiltin) : BuiltinSem (standardBuiltinSig b).sig_res where
  sem := standardBuiltinFn b
  well_typed := standardBuiltinFn_wt b
  inject := fun _ vl vl' h => standardBuiltinFn_inject b vl vl' h

/-- `Builtins0.lookup_builtin` -/
def lookupBuiltin {A : Type} (sigOf : A → Signature) (name : String) (sg : Signature) :
    List (String × A) → Option A
  | [] => none
  | (n, b) :: l => if name = n ∧ sg = sigOf b then some b else lookupBuiltin sigOf name sg l

/-- `Builtins0.lookup_builtin_sig` -/
theorem lookupBuiltin_sig {A : Type} (sigOf : A → Signature) (name : String) (sg : Signature)
    (b : A) : ∀ l, lookupBuiltin sigOf name sg l = some b → sigOf b = sg
  | [] => by simp [lookupBuiltin]
  | (n, b') :: l => by
    unfold lookupBuiltin
    split
    · rename_i h; intro e; cases e; exact h.2.symm
    · exact lookupBuiltin_sig sigOf name sg b l

/-- `Builtins1.platform_builtin`: aarch64 has no platform-specific built-ins. -/
inductive PlatformBuiltin : Type
  deriving DecidableEq

def platformBuiltinTable : List (String × PlatformBuiltin) := []
def platformBuiltinSig (b : PlatformBuiltin) : Signature := nomatch b
def platformBuiltinSem (b : PlatformBuiltin) : BuiltinSem (platformBuiltinSig b).sig_res :=
  nomatch b

/-- `Builtins.builtin_function` -/
inductive BuiltinFunction where
  | BI_standard (b : StandardBuiltin)
  | BI_platform (b : PlatformBuiltin)
  deriving DecidableEq

/-- `Builtins.builtin_function_sig` -/
def builtinFunctionSig : BuiltinFunction → Signature
  | .BI_standard b => standardBuiltinSig b
  | .BI_platform b => platformBuiltinSig b

/-- `Builtins.builtin_function_sem` -/
def builtinFunctionSem : (b : BuiltinFunction) → BuiltinSem (builtinFunctionSig b).sig_res
  | .BI_standard b => standardBuiltinSem b
  | .BI_platform b => platformBuiltinSem b

/-- `Builtins.builtin_function_sem_inject` -/
theorem builtinFunctionSem_inject (b : BuiltinFunction) {vargs vargs' : List Val} {vres : Val}
    {j : Val.Meminj} (h : (builtinFunctionSem b).sem vargs = some vres)
    (hi : Val.InjectList j vargs vargs') :
    ∃ vres', (builtinFunctionSem b).sem vargs' = some vres' ∧ Val.Inject j vres vres' := by
  have := (builtinFunctionSem b).inject j vargs vargs' hi
  rw [h] at this
  revert this
  cases (builtinFunctionSem b).sem vargs' with
  | none => intro e; exact e.elim
  | some v' => intro e; exact ⟨v', rfl, e⟩

/-- `Builtins.builtin_function_sem_lessdef` -/
theorem builtinFunctionSem_lessdef (b : BuiltinFunction) {vargs vargs' : List Val} {vres : Val}
    (h : (builtinFunctionSem b).sem vargs = some vres) (hl : Val.LessdefList vargs vargs') :
    ∃ vres', (builtinFunctionSem b).sem vargs' = some vres' ∧ Val.Lessdef vres vres' := by
  have hi : Val.InjectList Val.inject_id vargs vargs' := by
    clear h
    induction hl with
    | nil => exact .nil
    | cons hv _ ih => exact .cons (Val.lessdef_inject_id.mp hv) ih
  obtain ⟨v', h1, h2⟩ := builtinFunctionSem_inject b h hi
  exact ⟨v', h1, Val.lessdef_inject_id.mpr h2⟩

/-- `Builtins.lookup_builtin_function` -/
def lookupBuiltinFunction (name : String) (sg : Signature) : Option BuiltinFunction :=
  match lookupBuiltin standardBuiltinSig name sg standardBuiltinTable with
  | some b => some (.BI_standard b)
  | none =>
    match lookupBuiltin platformBuiltinSig name sg platformBuiltinTable with
    | some b => some (.BI_platform b)
    | none => none

/-- `Builtins.lookup_builtin_function_sig` -/
theorem lookupBuiltinFunction_sig (name : String) (sg : Signature) (b : BuiltinFunction)
    (h : lookupBuiltinFunction name sg = some b) : builtinFunctionSig b = sg := by
  unfold lookupBuiltinFunction at h
  split at h
  · rename_i b' hb; cases h; exact lookupBuiltin_sig standardBuiltinSig name sg b' _ hb
  · split at h
    · rename_i b' hb; cases h; exact lookupBuiltin_sig platformBuiltinSig name sg b' _ hb
    · cases h

example : lookupBuiltinFunction "__builtin_fabs" (standardBuiltinSig .BI_fabs) =
    some (.BI_standard .BI_fabs) := by decide

end Builtins
end CC
