/-
  Properties of the C operators from `cfrontend/Cop.v` (after the injection
  section): `notbool_bool_val`, `val_casted` with `cast_val_is_casted`,
  `cast_val_casted` and `cast_idempotent`, and `val_casted_has_type`.
  The port's target is 64-bit (`Archi.ptr64 = true`), so the `val_casted`
  constructors that require `Archi.ptr64 = false` can never be used; they are
  kept to mirror CompCert.
-/
import CCLib.cfrontend.Cop
import CCLib.lib.IntegersInt

namespace CC
namespace Cop

/-- `Cop.notbool_bool_val` -/
theorem notbool_boolVal (v : Val) (t : Ty) (m : Mem) :
    semNotbool v t m = match boolVal v t m with
      | none => none
      | some b => some (Val.ofBool (!b)) := by
  unfold semNotbool
  cases boolVal v t m <;> rfl

/-- `Cop.val_casted` -/
inductive ValCasted : Val → Ty → Prop where
  | int {sz si attr n} : castIntInt sz si n = n → ValCasted (.Vint n) (.Tint sz si attr)
  | float {attr n} : ValCasted (.Vfloat n) (.Tfloat .F64 attr)
  | single {attr n} : ValCasted (.Vsingle n) (.Tfloat .F32 attr)
  | long {si attr n} : ValCasted (.Vlong n) (.Tlong si attr)
  | ptr_ptr {b ofs ty attr} : ValCasted (.Vptr b ofs) (.Tpointer ty attr)
  | int_ptr {n ty attr} : Archi.ptr64 = false → ValCasted (.Vint n) (.Tpointer ty attr)
  | ptr_int {b ofs si attr} : Archi.ptr64 = false → ValCasted (.Vptr b ofs) (.Tint .I32 si attr)
  | long_ptr {n ty attr} : Archi.ptr64 = true → ValCasted (.Vlong n) (.Tpointer ty attr)
  | ptr_long {b ofs si attr} : Archi.ptr64 = true → ValCasted (.Vptr b ofs) (.Tlong si attr)
  | struct {id attr b ofs} : ValCasted (.Vptr b ofs) (.Tstruct id attr)
  | union {id attr b ofs} : ValCasted (.Vptr b ofs) (.Tunion id attr)
  | void {v} : ValCasted v .Tvoid

/-- `Cop.cast_int_int_idem` -/
theorem castIntInt_idem (sz : IntSize) (sg : Signedness) (i : Integers.Int) :
    castIntInt sz sg (castIntInt sz sg i) = castIntInt sz sg i := by
  cases sz <;> cases sg <;> simp only [castIntInt]
  · exact Integers.Int.sign_ext_idem (by decide) i
  · exact Integers.Int.zero_ext_idem 8 i
  · exact Integers.Int.sign_ext_idem (by decide) i
  · exact Integers.Int.zero_ext_idem 16 i
  all_goals (split <;> (rename_i h; first | (rw [if_pos (by decide)]) | (rw [if_neg (by decide)])))

theorem castIntInt_bool01 (sz : IntSize) (si : Signedness) (c : Bool)
    (hsz : sz = .IBool) :
    castIntInt sz si (if c then Integers.Int.zero else Integers.Int.one) =
      (if c then Integers.Int.zero else Integers.Int.one) := by
  subst hsz; cases si <;> cases c <;> decide

/-- `Cop.cast_val_is_casted` -/
theorem cast_val_is_casted {v : Val} {ty ty' : Ty} {v' : Val} {m : Mem}
    (h : semCast v ty ty' m = some v') : ValCasted v' ty' := by
  rcases ty' with _ | ⟨sz', si', a'⟩ | ⟨si', a'⟩ | ⟨_ | _, a'⟩ | ⟨t', a'⟩ | ⟨t', n', a'⟩ |
      ⟨ta', tr', cc'⟩ | ⟨id', a'⟩ | ⟨id', a'⟩ <;>
    rcases ty with _ | ⟨sz, si, a⟩ | ⟨si, a⟩ | ⟨_ | _, a⟩ | ⟨t, a⟩ | ⟨t, n, a⟩ |
      ⟨ta, tr, cc⟩ | ⟨id, a⟩ | ⟨id, a⟩ <;>
    (try cases sz') <;> cases v <;>
    simp [semCast, classifyCast, Archi.ptr64] at h <;>
    (try obtain ⟨_, h⟩ := h) <;>
    (try (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at *)) <;>
    (try subst v') <;>
    first
    | exact .void | exact .float | exact .single | exact .long | exact .ptr_ptr
    | exact .long_ptr rfl | exact .ptr_long rfl | exact .struct | exact .union
    | exact .int (castIntInt_idem _ _ _)
    | exact .int (castIntInt_bool01 .IBool _ _ rfl)
    | exact .int (by cases si' <;> decide)

/-- `Cop.cast_val_casted` -/
theorem cast_val_casted {v : Val} {ty : Ty} (m : Mem) (hc : ValCasted v ty) :
    semCast v ty ty m = some v := by
  cases hc with
  | @int sz si attr n hn =>
    cases sz <;> simp [semCast, classifyCast, Archi.ptr64] <;> simp_all [castIntInt]
  | int_ptr h => simp [Archi.ptr64] at h
  | ptr_int h => simp [Archi.ptr64] at h
  | @struct id attr b ofs => simp [semCast, classifyCast]
  | @union id attr b ofs => simp [semCast, classifyCast]
  | _ => simp [semCast, classifyCast, Archi.ptr64]

/-- `Cop.cast_idempotent` -/
theorem cast_idempotent {v : Val} {ty ty' : Ty} {v' : Val} {m : Mem}
    (h : semCast v ty ty' m = some v') : semCast v' ty' ty' m = some v' :=
  cast_val_casted m (cast_val_is_casted h)

/-- `Cop.val_casted_has_type` -/
theorem val_casted_hasType {v : Val} {ty : Ty} (hc : ValCasted v ty) (hty : ty ≠ .Tvoid) :
    Val.hasType v (typOfType ty) = true := by
  cases hc <;> first | exact absurd rfl hty | simp_all [Val.hasType, typOfType, Tptr, Archi.ptr64]

end Cop
end CC
