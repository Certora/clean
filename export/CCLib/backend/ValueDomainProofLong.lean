/-
  Soundness of the abstract 64-bit integer operators, pointer offsets,
  floating-point operators and conversions of the value analysis
  (`backend/ValueDomain.v`, from `shift_long_sound` to `hiword_sound`).
  Continues `ValueDomainProofDiv2.lean`.

  As everywhere in the port, `Archi.ptr64 = true` (aarch64), so the 32-bit
  pointer-arithmetic branches of `Val.add`/`Val.addl` are dead.
-/
import CCLib.backend.ValueDomainProofDiv2

namespace CC
namespace ValueDomain

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

section
variable {bc : BlockClassification}

/-! ## 64-bit shifts and rotations -/

theorem int64_repr_unsigned_toNat (j : Integers.Int) :
    (Integers.Int64.repr (Integers.Int.unsigned j)).toNat = j.toNat := by
  have h := Integers.Int64.unsigned_repr_eq (Integers.Int.unsigned j)
  have hj := j.isLt
  simp only [Integers.Int64.unsigned, Integers.MI.unsigned, Integers.Int.unsigned,
    Integers.Int64.modulus, Integers.MI.modulus] at h ⊢
  have : ((j.toNat : Z) % 2 ^ 64) = (j.toNat : Z) := Int.emod_eq_of_lt (by zomega) (by zomega)
  zomega

/-- The concrete counterpart of `shiftLong` (the value computed by `Val.shll` & co.). -/
def shiftLongVal (sem : Integers.Int64 → Integers.Int → Integers.Int64) (v w : Val) : Val :=
  match v, w with
  | .Vlong i, .Vint j =>
      if Integers.Int.ltu j Integers.Int64.iwordsize' then .Vlong (sem i j) else .Vundef
  | _, _ => .Vundef

/-- `ValueDomain.shift_long_sound` -/
theorem shift_long_sound (sem : Integers.Int64 → Integers.Int → Integers.Int64) {v w : Val}
    {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (shiftLongVal sem v w) (shiftLong sem x y) := by
  cases h1 <;> cases h2 <;> simp only [shiftLongVal, shiftLong, ntop1] <;> (repeat' split) <;>
    first | constructor | (exfalso; simp_all)

theorem shll_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.shll v w) (shll x y) := by
  have e : Val.shll v w = shiftLongVal Integers.Int64.shl' v w := by
    cases v <;> cases w <;> try rfl
    simp only [Val.shll, shiftLongVal]
    rename_i i j
    show (if Integers.Int.ltu j (Integers.Int.repr 64) then _ else _) = _
    congr 2
    show Integers.MI.shl _ _ = i <<< j.toNat
    simp only [Integers.MI.shl, int64_repr_unsigned_toNat]
  rw [e]; exact shift_long_sound _ h1 h2

theorem shrl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.shrl v w) (shrl x y) := by
  have e : Val.shrl v w = shiftLongVal Integers.Int64.shr' v w := by
    cases v <;> cases w <;> try rfl
    simp only [Val.shrl, shiftLongVal]
    rename_i i j
    show (if Integers.Int.ltu j (Integers.Int.repr 64) then _ else _) = _
    congr 2
    show Integers.MI.shr _ _ = i.sshiftRight j.toNat
    simp only [Integers.MI.shr, int64_repr_unsigned_toNat]
  rw [e]; exact shift_long_sound _ h1 h2

theorem shrlu_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.shrlu v w) (shrlu x y) := by
  have e : Val.shrlu v w = shiftLongVal Integers.Int64.shru' v w := by
    cases v <;> cases w <;> try rfl
    simp only [Val.shrlu, shiftLongVal]
    rename_i i j
    show (if Integers.Int.ltu j (Integers.Int.repr 64) then _ else _) = _
    congr 2
    show Integers.MI.shru _ _ = i >>> j.toNat
    simp only [Integers.MI.shru, int64_repr_unsigned_toNat]
  rw [e]; exact shift_long_sound _ h1 h2

theorem andl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.andl v w) (andl x y) := by
  have := binop_long_sound Integers.Int64.and h1 h2
  cases v <;> cases w <;> exact this

theorem orl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.orl v w) (orl x y) := by
  have := binop_long_sound Integers.Int64.or h1 h2
  cases v <;> cases w <;> exact this

theorem xorl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.xorl v w) (xorl x y) := by
  have := binop_long_sound Integers.Int64.xor h1 h2
  cases v <;> cases w <;> exact this

theorem notl_sound {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc (Val.notl v) (notl x) := by
  have := unop_long_sound Integers.Int64.not h
  cases v <;> exact this

/-- `ValueDomain.rotate_long_sound` -/
theorem rotate_long_sound (sem : Integers.Int64 → Integers.Int64 → Integers.Int64) {v w : Val}
    {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (match v, w with
      | .Vlong i, .Vint j => .Vlong (sem i (Integers.Int64.repr (Integers.Int.unsigned j)))
      | _, _ => .Vundef) (rotateLong sem x y) := by
  have DEFAULT : Vmatch bc (match v, w with
      | .Vlong i, .Vint j => .Vlong (sem i (Integers.Int64.repr (Integers.Int.unsigned j)))
      | _, _ => .Vundef) (ntop1 x) := by
    cases v <;> cases w <;> simp only [ntop1] <;> constructor
  unfold rotateLong
  cases x <;> cases y <;> try exact DEFAULT
  cases h1; cases h2; constructor

theorem roll_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.roll v w) (roll x y) := by
  have := rotate_long_sound Integers.Int64.rol h1 h2
  cases v <;> cases w <;> exact this

theorem rorl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.rorl v w) (rorl x y) := by
  have := rotate_long_sound Integers.Int64.ror h1 h2
  cases v <;> cases w <;> exact this

theorem negl_sound {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc (Val.negl v) (negl x) := by
  have := unop_long_sound Integers.Int64.neg h
  cases v <;> exact this

/-! ## 64-bit arithmetic -/

local macro "ptr_close" : tactic =>
  `(tactic| first
    | (constructor <;> first
        | exact padd_sound _ ‹_›
        | exact psub_sound _ ‹_›
        | exact poffset_sound _ ‹_›
        | exact pmatch_lub_l _ (poffset_sound _ ‹_›)
        | exact pmatch_lub_r _ (poffset_sound _ ‹_›)
        | skip)
    | constructor)

set_option maxHeartbeats 4000000 in
/-- `ValueDomain.addl_sound` -/
theorem addl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.addl v w) (addl x y) := by
  cases h1 <;> cases h2 <;> delta addl <;> dsimp only <;>
    simp only [Val.addl, Archi.ptr64, if_true, ntop2] <;> ptr_close

set_option maxHeartbeats 4000000 in
/-- `ValueDomain.subl_sound` -/
theorem subl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.subl v w) (subl x y) := by
  cases h1 <;> cases h2 <;> delta subl <;> dsimp only <;>
    simp only [Val.subl, Archi.ptr64, if_true, Bool.not_true, Bool.false_eq_true, if_false,
      ntop2] <;> (try split) <;> ptr_close

theorem mull_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mull v w) (mull x y) := by
  have := binop_long_sound Integers.Int64.mul h1 h2
  cases v <;> cases w <;> exact this

theorem mullhs_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mullhs v w) (mullhs x y) := by
  have := binop_long_sound Integers.Int64.mulhs h1 h2
  cases v <;> cases w <;> exact this

theorem mullhu_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mullhu v w) (mullhu x y) := by
  have := binop_long_sound Integers.Int64.mulhu h1 h2
  cases v <;> cases w <;> exact this

local macro "divl_tac" : tactic =>
  `(tactic| (
    cases h1 <;> cases h2 <;> simp only [ntop2] <;> try constructor
    all_goals (split <;> first | (cases h; done) | (cases h; constructor))))

theorem divls_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.divls v w = some u) : Vmatch bc u (divls strict x y) := by
  cases v <;> cases w <;> simp only [Val.divls, reduceCtorEq] at h
  split at h
  · cases h
  rename_i hE; cases h
  cases h1 <;> cases h2 <;> simp only [divls, ntop2] <;> first | constructor | (rw [if_neg hE]; constructor)

theorem divlu_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.divlu v w = some u) : Vmatch bc u (divlu strict x y) := by
  cases v <;> cases w <;> simp only [Val.divlu, reduceCtorEq] at h
  split at h
  · cases h
  rename_i hE; cases h
  cases h1 <;> cases h2 <;> simp only [divlu, ntop2] <;> first | constructor | (rw [if_neg hE]; constructor)

theorem modls_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.modls v w = some u) : Vmatch bc u (modls strict x y) := by
  cases v <;> cases w <;> simp only [Val.modls, reduceCtorEq] at h
  split at h
  · cases h
  rename_i hE; cases h
  cases h1 <;> cases h2 <;> simp only [modls, ntop2] <;> first | constructor | (rw [if_neg hE]; constructor)

theorem modlu_sound (strict : Bool) {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) (h : Val.modlu v w = some u) : Vmatch bc u (modlu strict x y) := by
  cases v <;> cases w <;> simp only [Val.modlu, reduceCtorEq] at h
  split at h
  · cases h
  rename_i hE; cases h
  cases h1 <;> cases h2 <;> simp only [modlu, ntop2] <;> first | constructor | (rw [if_neg hE]; constructor)

theorem shrxl_sound {v w u : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y)
    (h : Val.shrxl v w = some u) : Vmatch bc u (shrxl x y) := by
  cases v <;> cases w <;> simp only [Val.shrxl, reduceCtorEq] at h
  split at h
  · rename_i hlt
    cases h
    cases h1 <;> simp only [shrxl, ntop1] <;> try constructor
    cases h2 <;> simp only [hlt, if_true] <;> constructor
  · cases h

theorem rolml_sound {v : Val} {x : Aval} (amount : Integers.Int) (mask : Integers.Int64)
    (h : Vmatch bc v x) : Vmatch bc (Val.rolml v amount mask) (rolml x amount mask) := by
  have e : Val.rolml v amount mask = Val.andl (Val.roll v (.Vint amount)) (.Vlong mask) := by
    cases v <;> rfl
  rw [e]
  exact andl_sound (roll_sound h (.i _)) (.l _)

/-! ## Pointer offsets -/

theorem offset_ptr_sound {v : Val} {x : Aval} (n : Integers.Ptrofs) (h : Vmatch bc v x) :
    Vmatch bc (Val.offsetPtr v n) (offsetPtr x n) := by
  cases h <;> simp only [Val.offsetPtr, offsetPtr, ntop1] <;> ptr_close

/-! ## Floating-point arithmetic -/

theorem negf_sound {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc (Val.negf v) (negf x) := by
  have := unop_float_sound Floats.Float.neg h; cases v <;> exact this
theorem absf_sound {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc (Val.absf v) (absf x) := by
  have := unop_float_sound Floats.Float.abs h; cases v <;> exact this
theorem addf_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.addf v w) (addf x y) := by
  have := binop_float_sound Floats.Float.add h1 h2; cases v <;> cases w <;> exact this
theorem subf_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.subf v w) (subf x y) := by
  have := binop_float_sound Floats.Float.sub h1 h2; cases v <;> cases w <;> exact this
theorem mulf_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mulf v w) (mulf x y) := by
  have := binop_float_sound Floats.Float.mul h1 h2; cases v <;> cases w <;> exact this
theorem divf_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.divf v w) (divf x y) := by
  have := binop_float_sound Floats.Float.div h1 h2; cases v <;> cases w <;> exact this
theorem negfs_sound {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc (Val.negfs v) (negfs x) := by
  have := unop_single_sound Floats.Float32.neg h; cases v <;> exact this
theorem absfs_sound {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc (Val.absfs v) (absfs x) := by
  have := unop_single_sound Floats.Float32.abs h; cases v <;> exact this
theorem addfs_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.addfs v w) (addfs x y) := by
  have := binop_single_sound Floats.Float32.add h1 h2; cases v <;> cases w <;> exact this
theorem subfs_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.subfs v w) (subfs x y) := by
  have := binop_single_sound Floats.Float32.sub h1 h2; cases v <;> cases w <;> exact this
theorem mulfs_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.mulfs v w) (mulfs x y) := by
  have := binop_single_sound Floats.Float32.mul h1 h2; cases v <;> cases w <;> exact this
theorem divfs_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.divfs v w) (divfs x y) := by
  have := binop_single_sound Floats.Float32.div h1 h2; cases v <;> cases w <;> exact this

end

end ValueDomain
end CC
