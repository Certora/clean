/-
  Soundness of the abstract comparisons of the value analysis
  (`backend/ValueDomain.v`, from `zcmp_intv_sound` to `resolve_branch_sound`
  and `add_undef_sound`).  Continues `ValueDomainProofConv.lean`.

  As `Archi.ptr64 = true` on aarch64, `Val.cmpu_bool` is `None` as soon as a
  pointer is involved, so the pointer cases of `cmpu_bool_sound` reduce to
  `cmp_intv_None` / `pcmp_none` / `cmp_different_blocks_none`.
-/
import CCLib.backend.ValueDomainProofConv

namespace CC
namespace ValueDomain

open Integers (Ptrofs)

local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

/-! ## Interval comparisons -/

/-- `ValueDomain.zcmp_intv_sound` -/
theorem zcmp_intv_sound (c : Comparison) (lo hi x n : Z) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    Cmatch (some (zcmp c x n)) (cmpIntv c (lo, hi) n) := by
  cases c <;> simp only [cmpIntv, zcmp]
  · by_cases a : n < lo
    · simp only [a, decide_true, Bool.true_or, if_true]
      rw [show decide (x = n) = false by simp; zomega]; constructor
    · by_cases b : hi < n
      · simp only [a, b, decide_true, decide_false, Bool.or_true, if_true]
        rw [show decide (x = n) = false by simp; zomega]; constructor
      · simp only [a, b, decide_false, Bool.or_false, Bool.false_eq_true, if_false]; constructor
  · by_cases a : n < lo
    · simp only [a, decide_true, Bool.true_or, if_true]
      rw [show decide (x = n) = false by simp; zomega]; constructor
    · by_cases b : hi < n
      · simp only [a, b, decide_true, decide_false, Bool.or_true, if_true]
        rw [show decide (x = n) = false by simp; zomega]; constructor
      · simp only [a, b, decide_false, Bool.or_false, Bool.false_eq_true, if_false]; constructor
  · by_cases a : hi < n
    · simp only [a, if_true]; rw [show decide (x < n) = true by simp; zomega]; constructor
    · by_cases b : n ≤ lo
      · simp only [a, b, if_true, if_false]
        rw [show decide (x < n) = false by simp; zomega]; constructor
      · simp only [a, b, if_false]; constructor
  · by_cases a : hi ≤ n
    · simp only [a, if_true]; rw [show decide (x ≤ n) = true by simp; zomega]; constructor
    · by_cases b : n < lo
      · simp only [a, b, if_true, if_false]
        rw [show decide (x ≤ n) = false by simp; zomega]; constructor
      · simp only [a, b, if_false]; constructor
  · by_cases a : n < lo
    · simp only [a, if_true]; rw [show decide (n < x) = true by simp; zomega]; constructor
    · by_cases b : hi ≤ n
      · simp only [a, b, if_true, if_false]
        rw [show decide (n < x) = false by simp; zomega]; constructor
      · simp only [a, b, if_false]; constructor
  · by_cases a : n ≤ lo
    · simp only [a, if_true]; rw [show decide (n ≤ x) = true by simp; zomega]; constructor
    · by_cases b : hi < n
      · simp only [a, b, if_true, if_false]
        rw [show decide (n ≤ x) = false by simp; zomega]; constructor
      · simp only [a, b, if_false]; constructor

/-- `ValueDomain.cmp_intv_None` -/
theorem cmp_intv_None (c : Comparison) (i : Z × Z) (n : Z) : Cmatch none (cmpIntv c i n) := by
  obtain ⟨lo, hi⟩ := i
  cases c <;> simp only [cmpIntv] <;> (repeat' split) <;> constructor

section
variable {bc : BlockClassification}

/-- `ValueDomain.uintv_sound` -/
theorem uintv_sound {n : Integers.Int} {v : Aval} (h : Vmatch bc (.Vint n) v) :
    (uintv v).1 ≤ Integers.Int.unsigned n ∧ Integers.Int.unsigned n ≤ (uintv v).2 := by
  have R := Integers.Int.unsigned_range n
  simp only [Integers.Int.modulus, Integers.MI.modulus] at R
  have hmu : Integers.Int.max_unsigned = 4294967295 := by decide
  cases h <;> simp only [uintv, hmu] <;> try (constructor <;> zomega)
  rename_i p n0 hn hu
  split
  · have := range_is_uns hn hu
    constructor <;> simp only <;> zomega
  · constructor <;> simp only <;> zomega

theorem signed_eq_unsigned_of_lt {n : Integers.Int} (h : n.toNat < 2 ^ 31) :
    Integers.Int.signed n = Integers.Int.unsigned n := by
  rcases signed_toInt_cases n with ⟨_, e⟩ | ⟨h1, _⟩
  · exact e
  · omega

/-- `ValueDomain.sintv_sound` -/
theorem sintv_sound {n : Integers.Int} {v : Aval} (h : Vmatch bc (.Vint n) v) :
    (sintv v).1 ≤ Integers.Int.signed n ∧ Integers.Int.signed n ≤ (sintv v).2 := by
  have R := Integers.Int.signed_range n
  have hmin : Integers.Int.min_signed = -2147483648 := by decide
  have hmax : Integers.Int.max_signed = 2147483647 := by decide
  rw [hmin, hmax] at R
  cases h <;> simp only [sintv, hmin, hmax] <;> try (constructor <;> zomega)
  · rename_i p n0 hn hu
    split
    · rename_i hlt
      have A := range_is_uns hn hu
      have T := twoP_mono hn (show n0 ≤ 31 by zomega)
      have T31 : twoP 31 = 2147483648 := by decide
      have e := signed_eq_unsigned_of_lt (n := n) (by
        simp only [Integers.Int.unsigned, Integers.MI.unsigned] at A; zomega)
      rw [e]
      constructor <;> simp only <;> zomega
    · constructor <;> simp only <;> zomega
  · rename_i p n0 hn hs
    split
    · have := range_is_sgn hn hs
      constructor <;> simp only <;> zomega
    · constructor <;> simp only <;> zomega

theorem cmpu_zcmp (c : Comparison) (n1 n2 : Integers.Int) :
    Integers.Int.cmpu c n1 n2 = zcmp c (Integers.Int.unsigned n1) (Integers.Int.unsigned n2) := by
  have hinj : (n1 = n2) ↔ (Integers.Int.unsigned n1 = Integers.Int.unsigned n2) :=
    ⟨fun h => h ▸ rfl, fun h => Integers.Int.unsigned_inj h⟩
  cases c <;>
    simp only [Integers.Int.cmpu, Integers.MI.cmpu, zcmp, Integers.MI.eq, Integers.MI.ltu,
      Integers.Int.unsigned, Integers.MI.unsigned, BitVec.ult, beq_iff_eq] <;>
    simp only [Integers.Int.unsigned, Integers.MI.unsigned] at hinj <;>
    (try rw [Bool.eq_iff_iff]) <;> simp [hinj] <;> omega

theorem cmp_zcmp (c : Comparison) (n1 n2 : Integers.Int) :
    Integers.Int.cmp c n1 n2 = zcmp c (Integers.Int.signed n1) (Integers.Int.signed n2) := by
  have hinj : (n1 = n2) ↔ (Integers.Int.signed n1 = Integers.Int.signed n2) :=
    ⟨fun h => h ▸ rfl, fun h => Integers.Int.signed_inj h⟩
  cases c <;>
    simp only [Integers.Int.cmp, Integers.MI.cmp, zcmp, Integers.MI.eq, Integers.MI.lt,
      Integers.Int.signed, Integers.MI.signed, BitVec.slt, beq_iff_eq] <;>
    simp only [Integers.Int.signed, Integers.MI.signed] at hinj <;>
    (try rw [Bool.eq_iff_iff]) <;> simp [hinj] <;> omega

theorem zcmp_swap (c : Comparison) (a b : Z) : zcmp c.swap a b = zcmp c b a := by
  cases c <;> simp only [zcmp, Comparison.swap] <;> simp only [eq_comm]

/-- `ValueDomain.cmpu_intv_sound` -/
theorem cmpu_intv_sound (c : Comparison) {n1 : Integers.Int} (n2 : Integers.Int) {v1 : Aval}
    (h : Vmatch bc (.Vint n1) v1) :
    Cmatch (some (Integers.Int.cmpu c n1 n2)) (cmpIntv c (uintv v1) (Integers.Int.unsigned n2)) := by
  rw [cmpu_zcmp]
  have := uintv_sound h
  exact zcmp_intv_sound c _ _ _ _ this.1 this.2

/-- `ValueDomain.cmpu_intv_sound_2` -/
theorem cmpu_intv_sound_2 (c : Comparison) {n1 : Integers.Int} (n2 : Integers.Int) {v1 : Aval}
    (h : Vmatch bc (.Vint n1) v1) :
    Cmatch (some (Integers.Int.cmpu c n2 n1))
      (cmpIntv c.swap (uintv v1) (Integers.Int.unsigned n2)) := by
  rw [cmpu_zcmp, ← zcmp_swap]
  have := uintv_sound h
  exact zcmp_intv_sound c.swap _ _ _ _ this.1 this.2

/-- `ValueDomain.cmp_intv_sound` -/
theorem cmp_intv_sound (c : Comparison) {n1 : Integers.Int} (n2 : Integers.Int) {v1 : Aval}
    (h : Vmatch bc (.Vint n1) v1) :
    Cmatch (some (Integers.Int.cmp c n1 n2)) (cmpIntv c (sintv v1) (Integers.Int.signed n2)) := by
  rw [cmp_zcmp]
  have := sintv_sound h
  exact zcmp_intv_sound c _ _ _ _ this.1 this.2

/-- `ValueDomain.cmp_intv_sound_2` -/
theorem cmp_intv_sound_2 (c : Comparison) {n1 : Integers.Int} (n2 : Integers.Int) {v1 : Aval}
    (h : Vmatch bc (.Vint n1) v1) :
    Cmatch (some (Integers.Int.cmp c n2 n1))
      (cmpIntv c.swap (sintv v1) (Integers.Int.signed n2)) := by
  rw [cmp_zcmp, ← zcmp_swap]
  have := sintv_sound h
  exact zcmp_intv_sound c.swap _ _ _ _ this.1 this.2

/-! ## Comparisons -/

theorem cmpu_bool_some {valid : Block → Z → Bool} {c : Comparison} {v w : Val} {b : Bool}
    (h : Val.cmpu_bool valid c v w = some b) :
    ∃ n1 n2, v = .Vint n1 ∧ w = .Vint n2 ∧ b = Integers.Int.cmpu c n1 n2 := by
  cases v <;> cases w <;> simp [Val.cmpu_bool, Archi.ptr64] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

set_option maxHeartbeats 2000000 in
/-- `ValueDomain.cmpu_bool_sound` -/
theorem cmpu_bool_sound (strict : Bool) (valid : Block → Z → Bool) (c : Comparison) {v w : Val}
    {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Cmatch (Val.cmpu_bool valid c v w) (cmpuBool strict c x y) := by
  cases hr : Val.cmpu_bool valid c v w with
  | none =>
    cases x <;> cases y <;> delta cmpuBool <;> dsimp only <;>
      first
      | exact cmp_intv_None _ _ _
      | exact pcmp_none _ _ _ _
      | exact cmatch_top _
      | (split <;> first | exact cmp_different_blocks_none _ _ | exact cmatch_top _)
      | constructor
      | (cases h1 <;> cases h2 <;> simp [Val.cmpu_bool] at hr)
  | some b =>
    obtain ⟨n1, n2, rfl, rfl, rfl⟩ := cmpu_bool_some hr
    have A := cmpu_intv_sound c n2 h1
    have B := cmpu_intv_sound_2 c n1 h2
    cases h1 <;> cases h2 <;> delta cmpuBool <;> dsimp only <;>
      first | constructor | exact A | exact B | exact cmatch_top _

set_option maxHeartbeats 2000000 in
/-- `ValueDomain.cmp_bool_sound` -/
theorem cmp_bool_sound (c : Comparison) {v w : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) : Cmatch (Val.cmp_bool c v w) (cmpBool c x y) := by
  cases v <;> cases w <;> simp only [Val.cmp_bool]
  case Vint.Vint n1 n2 =>
    have A := cmp_intv_sound c n2 h1
    have B := cmp_intv_sound_2 c n1 h2
    cases h1 <;> cases h2 <;> delta cmpBool <;> dsimp only <;>
      first | constructor | exact A | exact B | exact cmatch_top _
  all_goals
    cases x <;> cases y <;> delta cmpBool <;> dsimp only <;>
      first
      | exact cmp_intv_None _ _ _
      | exact cmatch_top _
      | (cases h1; done)
      | (cases h2; done)
      | constructor

/-- `ValueDomain.cmplu_bool_sound` -/
theorem cmplu_bool_sound (strict : Bool) (valid : Block → Z → Bool) (c : Comparison)
    {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Cmatch (Val.cmplu_bool valid c v w) (cmpluBool strict c x y) := by
  have IP : ∀ i b ofs, Cmatch (Val.cmplu_bool valid c (.Vlong i) (.Vptr b ofs))
      (if Integers.Int64.eq i Integers.Int64.zero then cmpDifferentBlocks strict c else .Btop) := by
    intro i b ofs
    simp only [Val.cmplu_bool, Archi.ptr64, Bool.not_true, Bool.false_eq_true, if_false]
    split
    · rename_i hh
      simp only [Bool.and_eq_true] at hh
      simp only [hh.1, if_true]; exact cmp_different_blocks_sound _ _
    · split
      · exact cmp_different_blocks_none _ _
      · exact cmatch_top _
  have PI : ∀ i b ofs, Cmatch (Val.cmplu_bool valid c (.Vptr b ofs) (.Vlong i))
      (if Integers.Int64.eq i Integers.Int64.zero then cmpDifferentBlocks strict c else .Btop) := by
    intro i b ofs
    simp only [Val.cmplu_bool, Archi.ptr64, Bool.not_true, Bool.false_eq_true, if_false]
    split
    · rename_i hh
      simp only [Bool.and_eq_true] at hh
      simp only [hh.1, if_true]; exact cmp_different_blocks_sound _ _
    · split
      · exact cmp_different_blocks_none _ _
      · exact cmatch_top _
  cases h1 <;> cases h2 <;> simp only [cmpluBool] <;>
    first
    | exact cmatch_top _
    | exact IP _ _ _
    | exact PI _ _ _
    | exact pcmp_sound_64 _ _ _ ‹_› ‹_›
    | (simp only [Val.cmplu_bool]; constructor)
    | (simp only [Val.cmplu_bool, Archi.ptr64, Bool.not_true, Bool.false_eq_true, if_false];
       first
       | exact pcmp_none _ _ _ _
       | (split <;> first | exact cmp_different_blocks_none _ _ | exact cmatch_top _)
       | constructor)

/-- `ValueDomain.cmpl_bool_sound` -/
theorem cmpl_bool_sound (c : Comparison) {v w : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) : Cmatch (Val.cmpl_bool c v w) (cmplBool c x y) := by
  cases h1 <;> cases h2 <;> simp only [Val.cmpl_bool, cmplBool] <;> constructor

/-- `ValueDomain.cmpf_bool_sound` -/
theorem cmpf_bool_sound (c : Comparison) {v w : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) : Cmatch (Val.cmpf_bool c v w) (cmpfBool c x y) := by
  cases h1 <;> cases h2 <;> simp only [Val.cmpf_bool, cmpfBool] <;> constructor

/-- `ValueDomain.cmpfs_bool_sound` -/
theorem cmpfs_bool_sound (c : Comparison) {v w : Val} {x y : Aval} (h1 : Vmatch bc v x)
    (h2 : Vmatch bc w y) : Cmatch (Val.cmpfs_bool c v w) (cmpfsBool c x y) := by
  cases h1 <;> cases h2 <;> simp only [Val.cmpfs_bool, cmpfsBool] <;> constructor

/-- `ValueDomain.of_optbool_sound` -/
theorem of_optbool_sound {ob : Option Bool} {ab : Abool} (h : Cmatch ob ab) :
    Vmatch bc (Val.ofOptbool ob) (ofOptbool ab) := by
  cases h <;> simp only [Val.ofOptbool, ofOptbool]
  · exact .Uns_undef _ _
  · rename_i b; cases b <;> exact .i _
  · exact .iu_undef _
  · rename_i b; cases b <;> exact .iu _
  · cases ob with
    | none => exact .Uns_undef _ _
    | some b =>
      cases b
      · exact .Uns _ _ _ (by decide) (fun m _ _ => Integers.Int.bits_zero m)
      · exact .Uns _ _ _ (by decide) (fun m h1 h2 => by
          rw [bits_one]; simp only [decide_eq_false_iff_not]; zomega)

/-- `ValueDomain.resolve_branch_sound` -/
theorem resolve_branch_sound {b b' : Bool} {ab : Abool} (h : Cmatch (some b) ab)
    (hr : resolveBranch ab = some b') : b' = b := by
  cases h <;> simp only [resolveBranch, Option.some.injEq, reduceCtorEq] at hr <;> exact hr.symm

/-- `ValueDomain.add_undef_sound` -/
theorem add_undef_sound {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc v (addUndef x) := by
  cases h <;> simp only [addUndef, ntop] <;>
    first | assumption | (constructor <;> assumption) | (constructor; done)

/-- `ValueDomain.add_undef_undef` -/
theorem add_undef_undef (x : Aval) : Vmatch bc .Vundef (addUndef x) := by
  cases x <;> simp only [addUndef, ntop] <;> constructor

end

end ValueDomain
end CC
