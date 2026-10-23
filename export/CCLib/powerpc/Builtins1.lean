/-
  Platform-specific built-in functions of the PowerPC back end — port of
  `powerpc/Builtins1.v`: `__builtin_isel`, `__builtin_uisel`,
  `__builtin_isel64`, `__builtin_uisel64`, `__builtin_bsel`,
  `__builtin_mulhw`, `__builtin_mulhwu`, `__builtin_mulhd`,
  `__builtin_mulhdu`, with their signatures and semantics (`BuiltinSem`,
  including the typing and memory-injection obligations).

  The port's `Builtins.PlatformBuiltin` is the (empty) aarch64 one, so, as for
  the x86 built-ins (`CCLib/x86/SelectOp.lean`), the PowerPC ones are the
  local type `PlatformBuiltin` of this module.  The argument handling is that
  of Rocq's `mkbuiltin_n2t`/`mkbuiltin_n3t`: exactly two (three) arguments,
  and `Vundef` when one of them is not a number of the expected type.
-/
import CCLib.common.Builtins

namespace CC
namespace PowerPC
namespace Builtins1

open Builtins

/-- `Builtins1.platform_builtin` (PowerPC) -/
inductive PlatformBuiltin where
  | BI_isel
  | BI_uisel
  | BI_isel64
  | BI_uisel64
  | BI_bsel
  | BI_mulhw
  | BI_mulhwu
  | BI_mulhd
  | BI_mulhdu
  deriving DecidableEq, Repr

open PlatformBuiltin

/-- `Builtins1.platform_builtin_table` -/
def platformBuiltinTable : List (String × PlatformBuiltin) :=
  [ ("__builtin_isel", BI_isel),
    ("__builtin_uisel", BI_uisel),
    ("__builtin_isel64", BI_isel64),
    ("__builtin_uisel64", BI_uisel64),
    ("__builtin_bsel", BI_bsel),
    ("__builtin_mulhw", BI_mulhw),
    ("__builtin_mulhwu", BI_mulhwu),
    ("__builtin_mulhd", BI_mulhd),
    ("__builtin_mulhdu", BI_mulhdu) ]

/-- `Builtins1.platform_builtin_sig` -/
def platformBuiltinSig : PlatformBuiltin → Signature
  | BI_isel | BI_uisel => sig [.Xint, .Xint, .Xint] .Xint
  | BI_isel64 | BI_uisel64 => sig [.Xint, .Xlong, .Xlong] .Xlong
  | BI_bsel => sig [.Xint, .Xint, .Xint] .Xbool
  | BI_mulhw | BI_mulhwu => sig [.Xint, .Xint] .Xint
  | BI_mulhd | BI_mulhdu => sig [.Xlong, .Xlong] .Xlong

/-- `Builtins1.isel`: `c ? n1 : n2`. -/
def isel {A : Type} (c : Integers.Int) (n1 n2 : A) : A :=
  if Integers.Int.eq c Integers.Int.zero then n2 else n1

/-- `Builtins1.bsel`: `isel` normalised to `0` / `1`. -/
def bsel (c n1 n2 : Integers.Int) : Integers.Int :=
  if Integers.Int.eq (isel c n1 n2) Integers.Int.zero then Integers.Int.zero else Integers.Int.one

theorem bsel_cases (c n1 n2 : Integers.Int) :
    bsel c n1 n2 = Integers.Int.zero ∨ bsel c n1 n2 = Integers.Int.one := by
  unfold bsel; split <;> simp

/-- Three `int` arguments (`mkbuiltin_n3t Tint Tint Tint`). -/
def int3Fn (f : Integers.Int → Integers.Int → Integers.Int → Val) : Val → Val → Val → Option Val
  | .Vint a, .Vint b, .Vint c => some (f a b c)
  | _, _, _ => some .Vundef

/-- An `int` and two `long` arguments (`mkbuiltin_n3t Tint Tlong Tlong`). -/
def intLong2Fn (f : Integers.Int → Integers.Int64 → Integers.Int64 → Val) :
    Val → Val → Val → Option Val
  | .Vint a, .Vlong b, .Vlong c => some (f a b c)
  | _, _, _ => some .Vundef

/-- Two `int` arguments (`mkbuiltin_n2t Tint Tint`). -/
def int2Fn (f : Integers.Int → Integers.Int → Val) : Val → Val → Option Val
  | .Vint a, .Vint b => some (f a b)
  | _, _ => some .Vundef

/-- The semantic function of each built-in (`platform_builtin_sem`, field
    `bs_sem`). -/
def platformBuiltinFn : PlatformBuiltin → List Val → Option Val
  | BI_isel | BI_uisel => fn3 (int3Fn fun c n1 n2 => .Vint (isel c n1 n2))
  | BI_isel64 | BI_uisel64 => fn3 (intLong2Fn fun c n1 n2 => .Vlong (isel c n1 n2))
  | BI_bsel => fn3 (int3Fn fun c n1 n2 => .Vint (bsel c n1 n2))
  | BI_mulhw => fn2 (int2Fn fun a b => .Vint (Integers.Int.mulhs a b))
  | BI_mulhwu => fn2 (int2Fn fun a b => .Vint (Integers.Int.mulhu a b))
  | BI_mulhd => fn2 (long2Fn fun a b => some (.Vlong (Integers.Int64.mulhs a b)))
  | BI_mulhdu => fn2 (long2Fn fun a b => some (.Vlong (Integers.Int64.mulhu a b)))

theorem platformBuiltinFn_wt (b : PlatformBuiltin) (vl : List Val) :
    valOptHasRettype (platformBuiltinFn b vl) (platformBuiltinSig b).sig_res := by
  cases b <;> simp only [platformBuiltinFn, platformBuiltinSig, sig, mksignature]
  case BI_bsel =>
    refine fn3_wt (fun v1 v2 v3 => ?_) vl
    cases v1 <;> cases v2 <;> cases v3 <;> try trivial
    rename_i a b c
    show Val.hasRettype (.Vint (bsel a b c)) .Xbool
    rcases bsel_cases a b c with h | h <;> rw [h] <;> simp [Val.hasRettype]
  all_goals first
    | exact fn3_wt (fun v1 v2 v3 => by cases v1 <;> cases v2 <;> cases v3 <;> trivial) vl
    | exact fn2_wt (fun v1 v2 => by cases v1 <;> cases v2 <;> trivial) vl

section Inject
variable {j : Val.Meminj}

theorem inject_undef_of_some {o : Option Val} (h : ∃ v, o = some v) :
    valOptInject j (some .Vundef) o := by
  obtain ⟨v, rfl⟩ := h
  exact .undef _

theorem int3Fn_some (f : Integers.Int → Integers.Int → Integers.Int → Val) (a b c : Val) :
    ∃ v, int3Fn f a b c = some v := by unfold int3Fn; split <;> exact ⟨_, rfl⟩
theorem intLong2Fn_some (f : Integers.Int → Integers.Int64 → Integers.Int64 → Val) (a b c : Val) :
    ∃ v, intLong2Fn f a b c = some v := by unfold intLong2Fn; split <;> exact ⟨_, rfl⟩
theorem int2Fn_some (f : Integers.Int → Integers.Int → Val) (a b : Val) :
    ∃ v, int2Fn f a b = some v := by unfold int2Fn; split <;> exact ⟨_, rfl⟩
theorem long2Fn_some (f : Integers.Int64 → Integers.Int64 → Integers.Int64) (a b : Val) :
    ∃ v, long2Fn (fun x y => some (.Vlong (f x y))) a b = some v := by
  unfold long2Fn; split <;> exact ⟨_, rfl⟩

theorem int3Fn_inject (f : Integers.Int → Integers.Int → Integers.Int → Val)
    {v1 v1' v2 v2' v3 v3' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2')
    (h3 : Val.Inject j v3 v3') (hf : ∀ a b c, Val.Inject j (f a b c) (f a b c)) :
    valOptInject j (int3Fn f v1 v2 v3) (int3Fn f v1' v2' v3') := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    first
    | exact inject_undef_of_some (int3Fn_some f _ _ _)
    | (rw [inject_int_inv h1, inject_int_inv h2, inject_int_inv h3]; exact hf _ _ _)

theorem intLong2Fn_inject (f : Integers.Int → Integers.Int64 → Integers.Int64 → Val)
    {v1 v1' v2 v2' v3 v3' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2')
    (h3 : Val.Inject j v3 v3') (hf : ∀ a b c, Val.Inject j (f a b c) (f a b c)) :
    valOptInject j (intLong2Fn f v1 v2 v3) (intLong2Fn f v1' v2' v3') := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    first
    | exact inject_undef_of_some (intLong2Fn_some f _ _ _)
    | (rw [inject_int_inv h1, inject_long_inv h2, inject_long_inv h3]; exact hf _ _ _)

theorem int2Fn_inject (f : Integers.Int → Integers.Int → Val) {v1 v1' v2 v2' : Val}
    (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2')
    (hf : ∀ a b, Val.Inject j (f a b) (f a b)) :
    valOptInject j (int2Fn f v1 v2) (int2Fn f v1' v2') := by
  cases v1 <;> cases v2 <;>
    first
    | exact inject_undef_of_some (int2Fn_some f _ _)
    | (rw [inject_int_inv h1, inject_int_inv h2]; exact hf _ _)

theorem long2Fn_inject (f : Integers.Int64 → Integers.Int64 → Integers.Int64)
    {v1 v1' v2 v2' : Val} (h1 : Val.Inject j v1 v1') (h2 : Val.Inject j v2 v2') :
    valOptInject j (long2Fn (fun a b => some (.Vlong (f a b))) v1 v2)
      (long2Fn (fun a b => some (.Vlong (f a b))) v1' v2') := by
  cases v1 <;> cases v2 <;>
    first
    | exact inject_undef_of_some (long2Fn_some f _ _)
    | (rw [inject_long_inv h1, inject_long_inv h2]; exact .long _)

theorem platformBuiltinFn_inject (b : PlatformBuiltin) {vl vl' : List Val}
    (hl : Val.InjectList j vl vl') :
    valOptInject j (platformBuiltinFn b vl) (platformBuiltinFn b vl') := by
  cases b <;> simp only [platformBuiltinFn]
  all_goals first
    | exact fn3_inject (fun _ _ _ _ _ _ h1 h2 h3 =>
        int3Fn_inject _ h1 h2 h3 (fun _ _ _ => .int _)) hl
    | exact fn3_inject (fun _ _ _ _ _ _ h1 h2 h3 =>
        intLong2Fn_inject _ h1 h2 h3 (fun _ _ _ => .long _)) hl
    | exact fn2_inject (fun _ _ _ _ h1 h2 => int2Fn_inject _ h1 h2 (fun _ _ => .int _)) hl
    | exact fn2_inject (fun _ _ _ _ h1 h2 => long2Fn_inject _ h1 h2) hl

end Inject

/-- `Builtins1.platform_builtin_sem` -/
def platformBuiltinSem (b : PlatformBuiltin) : BuiltinSem (platformBuiltinSig b).sig_res where
  sem := platformBuiltinFn b
  well_typed := platformBuiltinFn_wt b
  inject := fun _ _ _ hl => platformBuiltinFn_inject b hl

end Builtins1
end PowerPC
end CC
