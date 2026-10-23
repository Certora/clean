/-
  Abstract domain for neededness analysis — port of `backend/NeedDomain.v`
  (soundness lemmas, part 1): `vagree_same`, `vagree_lessdef`,
  `lessdef_vagree`, `vagree_list` and its properties, the order `nge`
  (`nge_refl`, `nge_trans`, `nge_agree`, `nge_lub_l`, `nge_lub_r`), the
  agreement lemmas `iagree_*` / `lagree_*` (instances of the generic ones of
  `NeedDomainBits.lean`), and the soundness of the transfer functions for
  bitwise operations, shifts, rotates and modular arithmetic
  (`andimm_sound` … `negl_sound`).

  The rest (conversions, `store_argument`, the redundancy tests, `default`,
  environments and memory) is in `NeedDomainProof2.lean`.
-/
import CCLib.backend.NeedDomainBits
import CCLib.common.ValuesLemmas
import CCLib.common.ValuesOps

namespace CC
namespace NeedDomain

open Nval Bits

/-! ### Agreement between values -/

theorem vagree_same (v : Val) (x : Nval) : vagree v v x := by
  cases x <;> cases v <;> simp only [vagree] <;>
    first | trivial | exact Or.inl rfl | exact Or.inl trivial | exact fun _ _ _ => rfl

theorem vagree_lessdef {v w : Val} (x : Nval) (h : Val.Lessdef v w) : vagree v w x := by
  rw [Val.lessdef_iff] at h
  rcases h with rfl | rfl
  · exact vagree_same v x
  · cases x <;> simp [vagree]

theorem lessdef_vagree {v w : Val} (h : vagree v w .All) : Val.Lessdef v w := by
  rw [Val.lessdef_iff]; exact h

/-- `vagree_list` -/
inductive VagreeList : List Val → List Val → List Nval → Prop where
  | nil (nvl : List Nval) : VagreeList [] [] nvl
  | default {v1 vl1 v2 vl2} : vagree v1 v2 .All → VagreeList vl1 vl2 [] →
      VagreeList (v1 :: vl1) (v2 :: vl2) []
  | cons {v1 vl1 v2 vl2 nv1 nvl} : vagree v1 v2 nv1 → VagreeList vl1 vl2 nvl →
      VagreeList (v1 :: vl1) (v2 :: vl2) (nv1 :: nvl)

theorem lessdef_vagree_list : ∀ {vl1 vl2 : List Val}, VagreeList vl1 vl2 [] →
    Val.LessdefList vl1 vl2
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
      cases h with
      | default h1 h2 => exact .cons (lessdef_vagree h1) (lessdef_vagree_list h2)

theorem vagree_lessdef_list {vl1 vl2 : List Val} (h : Val.LessdefList vl1 vl2) :
    ∀ nvl, VagreeList vl1 vl2 nvl := by
  induction h with
  | nil => intro nvl; exact .nil nvl
  | cons h1 _ ih =>
      intro nvl
      cases nvl with
      | nil => exact .default (vagree_lessdef _ h1) (ih [])
      | cons nv nvl => exact .cons (vagree_lessdef _ h1) (ih nvl)

/-! ### Ordering between value needs -/

/-- `nge` -/
inductive Nge : Nval → Nval → Prop where
  | nothing (x) : Nge .All x
  | all (x) : Nge x .Nothing
  | int {m1 m2 : I32} : (∀ i, i < 32 → Integers.Int.testbit m2 i = true →
      Integers.Int.testbit m1 i = true) → Nge (.I m1) (.I m2)
  | long {m1 m2 : I64} : (∀ i, i < 64 → Integers.Int64.testbit m2 i = true →
      Integers.Int64.testbit m1 i = true) → Nge (.L m1) (.L m2)

theorem nge_refl (x : Nval) : Nge x x := by
  cases x
  · exact .all _
  · exact .int fun _ _ h => h
  · exact .long fun _ _ h => h
  · exact .nothing _

theorem nge_trans {x y z : Nval} (h1 : Nge x y) (h2 : Nge y z) : Nge x z := by
  cases h1 with
  | nothing => exact .nothing _
  | all => cases h2; exact .all _
  | int h =>
      cases h2 with
      | all => exact .all _
      | int h' => exact .int fun i hi hb => h i hi (h' i hi hb)
  | long h =>
      cases h2 with
      | all => exact .all _
      | long h' => exact .long fun i hi hb => h i hi (h' i hi hb)

theorem nge_agree {v w : Val} {x y : Nval} (hge : Nge x y) (h : vagree v w x) : vagree v w y := by
  cases hge with
  | nothing =>
      have := vagree_lessdef y (lessdef_vagree h); exact this
  | all => trivial
  | int hb =>
      cases v <;> cases w <;> simp only [vagree] at h ⊢ <;> try trivial
      exact fun i hi hm => h i hi (hb i hi hm)
  | long hb =>
      cases v <;> cases w <;> simp only [vagree] at h ⊢ <;> try trivial
      exact fun i hi hm => h i hi (hb i hi hm)

theorem nge_lub_l (x y : Nval) : Nge (nlub x y) x := by
  cases x <;> cases y <;> simp only [nlub] <;>
    first
    | exact nge_refl _
    | exact .nothing _
    | exact .all _
    | exact .int fun i _ h => by
        show (BitVec.getLsbD _ i) = true
        simp [Integers.Int.or, Integers.MI.or, BitVec.getLsbD_or]
        exact Or.inl h
    | exact .long fun i _ h => by
        show (BitVec.getLsbD _ i) = true
        simp [Integers.Int64.or, Integers.MI.or, BitVec.getLsbD_or]
        exact Or.inl h

theorem nge_lub_r (x y : Nval) : Nge (nlub x y) y := by
  cases x <;> cases y <;> simp only [nlub] <;>
    first
    | exact nge_refl _
    | exact .nothing _
    | exact .all _
    | exact .int fun i _ h => by
        show (BitVec.getLsbD _ i) = true
        simp [Integers.Int.or, Integers.MI.or, BitVec.getLsbD_or]
        exact Or.inr h
    | exact .long fun i _ h => by
        show (BitVec.getLsbD _ i) = true
        simp [Integers.Int64.or, Integers.MI.or, BitVec.getLsbD_or]
        exact Or.inr h

/-! ### Agreement between 32-bit / 64-bit integers (instances of `Bits`) -/

theorem iagree_iff {p q m : I32} : iagree p q m ↔ bagree p q m := Iff.rfl
theorem lagree_iff {p q m : I64} : lagree p q m ↔ bagree p q m := Iff.rfl

theorem iagree_refl (p m : I32) : iagree p p m := bagree_refl p m
theorem lagree_refl (p m : I64) : lagree p p m := bagree_refl p m

theorem iagree_and_eq (x y m : I32) :
    iagree x y m ↔ Integers.Int.and x m = Integers.Int.and y m := bagree_and_eq x y m
theorem lagree_and_eq (x y m : I64) :
    lagree x y m ↔ Integers.Int64.and x m = Integers.Int64.and y m := bagree_and_eq x y m

theorem iagree_mone {p q : I32} (h : iagree p q Integers.Int.mone) : p = q := bagree_mone h
theorem lagree_mone {p q : I64} (h : lagree p q Integers.Int64.mone) : p = q := bagree_mone h

theorem min_signed_eq : Integers.Int.repr Integers.Int.min_signed = BitVec.twoPow 32 31 := by decide
theorem min_signed64_eq : Integers.Int64.repr Integers.Int64.min_signed = BitVec.twoPow 64 63 := by
  decide

theorem int_ror_eq (x y : I32) : Integers.Int.ror x y = x.rotateRight (y.toNat % 32) := rfl
theorem int_rol_eq (x y : I32) : Integers.Int.rol x y = x.rotateLeft (y.toNat % 32) := rfl
theorem long_ror_eq (x y : I64) : Integers.Int64.ror x y = x.rotateRight (y.toNat % 64) := rfl
theorem long_rol_eq (x y : I64) : Integers.Int64.rol x y = x.rotateLeft (y.toNat % 64) := rfl

theorem repr64_unsigned_toNat (n : I32) :
    (Integers.Int64.repr (Integers.Int.unsigned n)).toNat = n.toNat := by
  have h := n.isLt
  simp only [Integers.Int64.repr, Integers.MI.repr, Integers.Int.unsigned, Integers.MI.unsigned,
    BitVec.toNat_ofInt]
  omega

/-- Closes the trivial goals left after case analysis on `vagree`. -/
macro "vagree_triv" : tactic =>
  `(tactic| first
    | trivial
    | exact Or.inr trivial
    | exact Or.inr rfl
    | exact Or.inl rfl
    | exact Or.inl trivial)

/-! ### Bitwise operations -/

theorem andimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (andimm x n)) :
    vagree (Val.and v (.Vint n)) (Val.and w (.Vint n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [andimm, vagree, Val.and] at h ⊢ <;>
    first | vagree_triv | exact bagree_and h | exact Or.inl (by rw [(iagree_and_eq _ _ _).1 h])

theorem bagree_or_all {w : Nat} {x y n : BitVec w} (h : bagree x y (~~~n)) : x ||| n = y ||| n :=
  bagree_mone (bagree_or fun i hi hm => h i hi (by
    rw [BitVec.getLsbD_and, Bool.and_eq_true] at hm; exact hm.2))

theorem orimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (orimm x n)) :
    vagree (Val.or v (.Vint n)) (Val.or w (.Vint n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [orimm, vagree, Val.or] at h ⊢ <;>
    first
    | vagree_triv
    | exact bagree_or h
    | exact Or.inl (congrArg Val.Vint (bagree_or_all h))

theorem andlimm_sound {v w : Val} {x : Nval} {n : I64} (h : vagree v w (andlimm x n)) :
    vagree (Val.andl v (.Vlong n)) (Val.andl w (.Vlong n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [andlimm, vagree, Val.andl] at h ⊢ <;>
    first | vagree_triv | exact bagree_and h | exact Or.inl (by rw [(lagree_and_eq _ _ _).1 h])

theorem orlimm_sound {v w : Val} {x : Nval} {n : I64} (h : vagree v w (orlimm x n)) :
    vagree (Val.orl v (.Vlong n)) (Val.orl w (.Vlong n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [orlimm, vagree, Val.orl] at h ⊢ <;>
    first
    | vagree_triv
    | exact bagree_or h
    | exact Or.inl (congrArg Val.Vlong (bagree_or_all h))

theorem bitwise_idem (nv : Nval) : bitwise (bitwise nv) = bitwise nv := rfl

theorem and_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (bitwise x))
    (h2 : vagree v2 w2 (bitwise x)) : vagree (Val.and v1 v2) (Val.and w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [bitwise, vagree, Val.and] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_bitwise_binop (· && ·) (· &&& ·) (fun _ _ _ _ => BitVec.getLsbD_and ..) h1 h2
    | simp_all

theorem or_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (bitwise x))
    (h2 : vagree v2 w2 (bitwise x)) : vagree (Val.or v1 v2) (Val.or w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [bitwise, vagree, Val.or] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_bitwise_binop (· || ·) (· ||| ·) (fun _ _ _ _ => BitVec.getLsbD_or ..) h1 h2
    | simp_all

theorem xor_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (bitwise x))
    (h2 : vagree v2 w2 (bitwise x)) : vagree (Val.xor v1 v2) (Val.xor w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [bitwise, vagree, Val.xor] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_bitwise_binop (Bool.xor) (· ^^^ ·) (fun _ _ _ _ => BitVec.getLsbD_xor ..) h1 h2
    | simp_all

theorem andl_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (bitwise x))
    (h2 : vagree v2 w2 (bitwise x)) : vagree (Val.andl v1 v2) (Val.andl w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [bitwise, vagree, Val.andl] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_bitwise_binop (· && ·) (· &&& ·) (fun _ _ _ _ => BitVec.getLsbD_and ..) h1 h2
    | simp_all

theorem orl_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (bitwise x))
    (h2 : vagree v2 w2 (bitwise x)) : vagree (Val.orl v1 v2) (Val.orl w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [bitwise, vagree, Val.orl] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_bitwise_binop (· || ·) (· ||| ·) (fun _ _ _ _ => BitVec.getLsbD_or ..) h1 h2
    | simp_all

theorem xorl_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (bitwise x))
    (h2 : vagree v2 w2 (bitwise x)) : vagree (Val.xorl v1 v2) (Val.xorl w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [bitwise, vagree, Val.xorl] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_bitwise_binop (Bool.xor) (· ^^^ ·) (fun _ _ _ _ => BitVec.getLsbD_xor ..) h1 h2
    | simp_all

theorem notint_sound {v w : Val} {x : Nval} (h : vagree v w (bitwise x)) :
    vagree (Val.notint v) (Val.notint w) x := by
  cases x <;> cases v <;> cases w <;> simp only [bitwise, vagree, Val.notint] at h ⊢ <;>
    first | vagree_triv | exact bagree_not h | simp_all

theorem notl_sound {v w : Val} {x : Nval} (h : vagree v w (bitwise x)) :
    vagree (Val.notl v) (Val.notl w) x := by
  cases x <;> cases v <;> cases w <;> simp only [bitwise, vagree, Val.notl] at h ⊢ <;>
    first | vagree_triv | exact bagree_not h | simp_all

/-! ### Shifts and rotates -/

theorem shlimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (shlimm x n)) :
    vagree (Val.shl v (.Vint n)) (Val.shl w (.Vint n)) x := by
  cases hc : Integers.Int.ltu n Integers.Int.iwordsize <;>
    cases x <;> cases v <;> cases w <;>
    simp only [shlimm, vagree, Val.shl, hc, if_true, if_false, Bool.false_eq_true] at h ⊢ <;>
    first
    | vagree_triv
    | exact bagree_shl h
    | exact Or.inl (congrArg Val.Vint (bagree_mone (bagree_shl (m := BitVec.allOnes _) h)))

theorem shruimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (shruimm x n)) :
    vagree (Val.shru v (.Vint n)) (Val.shru w (.Vint n)) x := by
  cases hc : Integers.Int.ltu n Integers.Int.iwordsize <;>
    cases x <;> cases v <;> cases w <;>
    simp only [shruimm, vagree, Val.shru, hc, if_true, if_false, Bool.false_eq_true] at h ⊢ <;>
    first
    | vagree_triv
    | exact bagree_shru h
    | exact Or.inl (congrArg Val.Vint (bagree_mone (bagree_shru (m := BitVec.allOnes _) h)))

theorem shrimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (shrimm x n)) :
    vagree (Val.shr v (.Vint n)) (Val.shr w (.Vint n)) x := by
  cases hc : Integers.Int.ltu n Integers.Int.iwordsize <;>
    cases x <;> cases v <;> cases w <;>
    simp only [shrimm, vagree, Val.shr, hc, if_true, if_false, Bool.false_eq_true] at h ⊢ <;>
    first
    | vagree_triv
    | (rw [min_signed_eq] at h; exact Or.inl (congrArg Val.Vint (bagree_mone (bagree_shr (m := BitVec.allOnes _) h))))
    | (split at h
       · exact bagree_shr_1 ‹_› h
       · rw [min_signed_eq] at h; exact bagree_shr h)

theorem rol_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (rol x n)) :
    vagree (Val.rol v (.Vint n)) (Val.rol w (.Vint n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [rol, vagree, Val.rol] at h ⊢ <;>
    first
    | vagree_triv
    | (rw [int_rol_eq, int_rol_eq]; exact bagree_rotateLeft h)
    | simp_all

theorem ror_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (ror x n)) :
    vagree (Val.ror v (.Vint n)) (Val.ror w (.Vint n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [ror, vagree, Val.ror] at h ⊢ <;>
    first
    | vagree_triv
    | (rw [int_ror_eq, int_ror_eq]; exact bagree_rotateRight h)
    | simp_all

theorem rolm_sound {v w : Val} {x : Nval} {amount mask : I32} (h : vagree v w (rolm x amount mask)) :
    vagree (Val.rolm v amount mask) (Val.rolm w amount mask) x := by
  have e : ∀ u, Val.rolm u amount mask = Val.and (Val.rol u (.Vint amount)) (.Vint mask) := by
    intro u; cases u <;> rfl
  rw [e, e]
  exact andimm_sound (rol_sound h)

theorem long_shl_eq (p : I64) (n : I32) :
    Integers.Int64.shl p (Integers.Int64.repr (Integers.Int.unsigned n)) = Integers.Int64.shl' p n := by
  simp only [Integers.Int64.shl, Integers.MI.shl, Integers.Int64.shl', repr64_unsigned_toNat]
theorem long_shru_eq (p : I64) (n : I32) :
    Integers.Int64.shru p (Integers.Int64.repr (Integers.Int.unsigned n)) = Integers.Int64.shru' p n := by
  simp only [Integers.Int64.shru, Integers.MI.shru, Integers.Int64.shru', repr64_unsigned_toNat]
theorem long_shr_eq (p : I64) (n : I32) :
    Integers.Int64.shr p (Integers.Int64.repr (Integers.Int.unsigned n)) = Integers.Int64.shr' p n := by
  simp only [Integers.Int64.shr, Integers.MI.shr, Integers.Int64.shr', repr64_unsigned_toNat]

theorem Val.shll_eq (p : I64) (n : I32) : Val.shll (.Vlong p) (.Vint n) =
    if Integers.Int.ltu n (Integers.Int.repr 64) then .Vlong (Integers.Int64.shl' p n) else .Vundef := by
  rw [← long_shl_eq]; rfl
theorem Val.shrlu_eq (p : I64) (n : I32) : Val.shrlu (.Vlong p) (.Vint n) =
    if Integers.Int.ltu n (Integers.Int.repr 64) then .Vlong (Integers.Int64.shru' p n) else .Vundef := by
  rw [← long_shru_eq]; rfl
theorem Val.shrl_eq (p : I64) (n : I32) : Val.shrl (.Vlong p) (.Vint n) =
    if Integers.Int.ltu n (Integers.Int.repr 64) then .Vlong (Integers.Int64.shr' p n) else .Vundef := by
  rw [← long_shr_eq]; rfl

theorem shllimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (shllimm x n)) :
    vagree (Val.shll v (.Vint n)) (Val.shll w (.Vint n)) x := by
  cases hc : Integers.Int.ltu n (Integers.Int.repr 64) <;>
    cases x <;> cases v <;> cases w <;>
    simp only [shllimm, vagree, Val.shll_eq, hc, if_true, if_false, Bool.false_eq_true] at h ⊢ <;>
    first
    | vagree_triv
    | exact bagree_shl h
    | exact Or.inl (congrArg Val.Vlong (bagree_mone (bagree_shl (m := BitVec.allOnes _) h)))

theorem shrluimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (shrluimm x n)) :
    vagree (Val.shrlu v (.Vint n)) (Val.shrlu w (.Vint n)) x := by
  cases hc : Integers.Int.ltu n (Integers.Int.repr 64) <;>
    cases x <;> cases v <;> cases w <;>
    simp only [shrluimm, vagree, Val.shrlu_eq, hc, if_true, if_false, Bool.false_eq_true] at h ⊢ <;>
    first
    | vagree_triv
    | exact bagree_shru h
    | exact Or.inl (congrArg Val.Vlong (bagree_mone (bagree_shru (m := BitVec.allOnes _) h)))

theorem shrlimm_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (shrlimm x n)) :
    vagree (Val.shrl v (.Vint n)) (Val.shrl w (.Vint n)) x := by
  cases hc : Integers.Int.ltu n (Integers.Int.repr 64) <;>
    cases x <;> cases v <;> cases w <;>
    simp only [shrlimm, vagree, Val.shrl_eq, hc, if_true, if_false, Bool.false_eq_true] at h ⊢ <;>
    first
    | vagree_triv
    | (rw [min_signed64_eq] at h; exact Or.inl (congrArg Val.Vlong (bagree_mone (bagree_shr (m := BitVec.allOnes _) h))))
    | (split at h
       · exact bagree_shr_1 ‹_› h
       · rw [min_signed64_eq] at h; exact bagree_shr h)

theorem roll_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (roll x n)) :
    vagree (Val.roll v (.Vint n)) (Val.roll w (.Vint n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [roll, vagree, Val.roll] at h ⊢ <;>
    first
    | vagree_triv
    | (rw [long_rol_eq, long_rol_eq]; exact bagree_rotateLeft h)
    | simp_all

theorem rorl_sound {v w : Val} {x : Nval} {n : I32} (h : vagree v w (rorl x n)) :
    vagree (Val.rorl v (.Vint n)) (Val.rorl w (.Vint n)) x := by
  cases x <;> cases v <;> cases w <;> simp only [rorl, vagree, Val.rorl] at h ⊢ <;>
    first
    | vagree_triv
    | (rw [long_ror_eq, long_ror_eq]; exact bagree_rotateRight h)
    | simp_all

theorem rolml_sound {v w : Val} {x : Nval} {amount : I32} {mask : I64}
    (h : vagree v w (rolml x amount mask)) :
    vagree (Val.rolml v amount mask) (Val.rolml w amount mask) x := by
  have e : ∀ u, Val.rolml u amount mask = Val.andl (Val.roll u (.Vint amount)) (.Vlong mask) := by
    intro u; cases u <;> rfl
  rw [e, e]
  exact andlimm_sound (roll_sound h)

theorem add_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (modarith x))
    (h2 : vagree v2 w2 (modarith x)) : vagree (Val.add v1 v2) (Val.add w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [modarith, vagree, Val.add, Archi.ptr64, if_true] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_add h1 h2
    | simp_all

theorem sub_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (modarith x))
    (h2 : vagree v2 w2 (modarith x)) : vagree (Val.sub v1 v2) (Val.sub w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [modarith, vagree, Val.sub, Archi.ptr64, if_true] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_sub h1 h2
    | simp_all

theorem mul_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (modarith x))
    (h2 : vagree v2 w2 (modarith x)) : vagree (Val.mul v1 v2) (Val.mul w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [modarith, vagree, Val.mul] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_mul h1 h2
    | simp_all

theorem addl_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (modarith x))
    (h2 : vagree v2 w2 (modarith x)) : vagree (Val.addl v1 v2) (Val.addl w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [modarith, vagree, Val.addl, Archi.ptr64, if_true] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_add h1 h2
    | simp_all

theorem mull_sound {v1 w1 v2 w2 : Val} {x : Nval} (h1 : vagree v1 w1 (modarith x))
    (h2 : vagree v2 w2 (modarith x)) : vagree (Val.mull v1 v2) (Val.mull w1 w2) x := by
  cases x <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;>
    simp only [modarith, vagree, Val.mull] at h1 h2 ⊢ <;>
    first
    | vagree_triv
    | exact bagree_mul h1 h2
    | simp_all

theorem neg_sound {v w : Val} {x : Nval} (h : vagree v w (modarith x)) :
    vagree (Val.neg v) (Val.neg w) x := by
  cases x <;> cases v <;> cases w <;> simp only [modarith, vagree, Val.neg] at h ⊢ <;>
    first | vagree_triv | exact bagree_neg h | simp_all

theorem negl_sound {v w : Val} {x : Nval} (h : vagree v w (modarith x)) :
    vagree (Val.negl v) (Val.negl w) x := by
  cases x <;> cases v <;> cases w <;> simp only [modarith, vagree, Val.negl] at h ⊢ <;>
    first | vagree_triv | exact bagree_neg h | simp_all

theorem completeMask_idem (m : I32) : completeMask (completeMask m) = completeMask m := by
  show lowMask 32 (nsize (lowMask 32 (nsize m))) = lowMask 32 (nsize m)
  rw [nsize_lowMask (nsize_le m)]

theorem completeMask64_idem (m : I64) : completeMask64 (completeMask64 m) = completeMask64 m := by
  show lowMask 64 (nsize (lowMask 64 (nsize m))) = lowMask 64 (nsize m)
  rw [nsize_lowMask (nsize_le m)]

theorem modarith_idem (nv : Nval) : modarith (modarith nv) = modarith nv := by
  cases nv <;> simp only [modarith, completeMask_idem, completeMask64_idem]

end NeedDomain
end CC
