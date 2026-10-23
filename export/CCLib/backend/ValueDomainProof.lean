/-
  Soundness of the abstract domain of the value analysis — the lemmas of
  `backend/ValueDomain.v` about abstract booleans, abstract pointers and
  abstract values.  The definitions themselves are in `ValueDomain.lean`.

  Differences from Rocq:
  * `plub`, `pincl`, `pcmp` and `vlub` are large pattern matches whose
    equation lemmas are too expensive to generate; the proofs unfold them
    with `delta` and let `dsimp` reduce the match on constructors.
  * The bit-width arguments of `Int.zero_ext`/`Int.sign_ext` are `Nat` in
    the Lean port, so `is_uns_zero_ext` and friends take a `Nat` width.
  * `Int.size_range` and `Int.bits_size_2` (from `Integers.v`) are proved
    here, as `size_range` and `bits_size_2`.
  * `pcmp_sound` (32-bit comparisons) holds trivially on aarch64, where
    `Archi.ptr64 = true` makes `Val.cmpu_bool` undefined on pointers.
-/
import CCLib.backend.ValueDomain
import CCLib.lib.IntegersInt
import CCLib.common.ValuesLemmas

namespace CC
namespace ValueDomain

open Integers (Ptrofs)

/-- `omega` after unfolding the `Z` abbreviation (which `omega` does not see through). -/
local macro "zomega" : tactic =>
  `(tactic| ((try simp only [Z, Integers.Int.zwordsize] at *) <;> omega))

section
variable {bc : BlockClassification}

/-! ## Abstract booleans and abstract pointers -/

theorem cmatch_top (ob : Option Bool) : Cmatch ob .Btop := .top ob

theorem pge_refl (p : Aptr) : Pge p p := .refl p

theorem pmatch_top' {b : Block} {ofs : Ptrofs} {p : Aptr} (h : Pmatch bc b ofs p) :
    Pmatch bc b ofs .Ptop :=
  pmatch_ge (.top p) h

theorem plub_comm (p q : Aptr) : plub p q = plub q p := by
  cases p <;> cases q <;> delta plub <;> dsimp only <;> (try rfl) <;>
    (repeat' split) <;> subst_vars <;> simp_all

theorem pge_lub_l (p q : Aptr) : Pge (plub p q) p := by
  cases p <;> cases q <;> delta plub <;> dsimp only <;>
    (repeat' split) <;> (try subst_vars) <;> constructor

theorem pge_lub_r (p q : Aptr) : Pge (plub p q) q := by
  rw [plub_comm]; exact pge_lub_l q p

theorem pmatch_lub_l {b : Block} {ofs : Ptrofs} {p : Aptr} (q : Aptr)
    (h : Pmatch bc b ofs p) : Pmatch bc b ofs (plub p q) :=
  pmatch_ge (pge_lub_l p q) h

theorem pmatch_lub_r {b : Block} {ofs : Ptrofs} (p : Aptr) {q : Aptr}
    (h : Pmatch bc b ofs q) : Pmatch bc b ofs (plub p q) :=
  pmatch_ge (pge_lub_r p q) h

theorem plub_least {r p q : Aptr} (h1 : Pge r p) (h2 : Pge r q) : Pge r (plub p q) := by
  cases p <;> cases q <;> cases h1 <;> cases h2 <;> delta plub <;> (try dsimp only) <;>
    (repeat' split) <;> (try subst_vars) <;> first | constructor | simp_all

theorem pincl_ge {p q : Aptr} (h : pincl p q = true) : Pge q p := by
  cases p <;> cases q <;> delta pincl at h <;> (try dsimp only at h) <;> (try simp at h) <;>
    (try (obtain ⟨h1, h2⟩ := h; subst h1 h2)) <;> (try subst_vars) <;> first | constructor | cases h

theorem ge_pincl {p q : Aptr} (h : Pge p q) : pincl q p = true := by
  cases p <;> cases q <;> cases h <;> delta pincl <;> (try dsimp only) <;> simp

theorem pincl_sound {b : Block} {ofs : Ptrofs} {p q : Aptr} (h : pincl p q = true)
    (hm : Pmatch bc b ofs p) : Pmatch bc b ofs q := pmatch_ge (pincl_ge h) hm

theorem padd_sound {b : Block} {ofs : Ptrofs} {p : Aptr} (delta : Ptrofs) (hm : Pmatch bc b ofs p) :
    Pmatch bc b (Ptrofs.add ofs delta) (padd p delta) := by
  cases hm <;> simp only [padd] <;> constructor <;> assumption

theorem psub_sound {b : Block} {ofs : Ptrofs} {p : Aptr} (delta : Ptrofs) (hm : Pmatch bc b ofs p) :
    Pmatch bc b (Ptrofs.sub ofs delta) (psub p delta) := by
  cases hm <;> simp only [psub] <;> constructor <;> assumption

theorem poffset_sound {b : Block} {ofs1 : Ptrofs} (ofs2 : Ptrofs) {p : Aptr} (hm : Pmatch bc b ofs1 p) :
    Pmatch bc b ofs2 (poffset p) := by
  cases hm <;> simp only [poffset] <;> constructor <;> assumption

theorem cmp_different_blocks_none (strict : Bool) (c : Comparison) :
    Cmatch none (cmpDifferentBlocks strict c) := by
  cases c <;> cases strict <;> constructor

theorem cmp_different_blocks_sound (strict : Bool) (c : Comparison) :
    Cmatch (Val.cmpDifferentBlocks c) (cmpDifferentBlocks strict c) := by
  cases c <;> cases strict <;> constructor

theorem pcmp_none (strict : Bool) (c : Comparison) (p1 p2 : Aptr) :
    Cmatch none (pcmp strict c p1 p2) := by
  cases p1 <;> cases p2 <;> delta pcmp <;> (try dsimp only) <;> (try split) <;>
    first | constructor | exact cmp_different_blocks_none strict c

theorem pcmp_sound (strict : Bool) (valid : Block → Z → Bool) (c : Comparison)
    {b1 : Block} {ofs1 : Ptrofs} {p1 : Aptr} {b2 : Block} {ofs2 : Ptrofs} {p2 : Aptr}
    (_h1 : Pmatch bc b1 ofs1 p1) (_h2 : Pmatch bc b2 ofs2 p2) :
    Cmatch (Val.cmpu_bool valid c (.Vptr b1 ofs1) (.Vptr b2 ofs2)) (pcmp strict c p1 p2) := by
  simp only [Val.cmpu_bool, Archi.ptr64, if_true]
  exact pcmp_none strict c p1 p2

theorem pcmp_sound_64 (strict : Bool) (valid : Block → Z → Bool) (c : Comparison)
    {b1 : Block} {ofs1 : Ptrofs} {p1 : Aptr} {b2 : Block} {ofs2 : Ptrofs} {p2 : Aptr}
    (h1 : Pmatch bc b1 ofs1 p1) (h2 : Pmatch bc b2 ofs2 p2) :
    Cmatch (Val.cmplu_bool valid c (.Vptr b1 ofs1) (.Vptr b2 ofs2)) (pcmp strict c p1 p2) := by
  have DIFF : b1 ≠ b2 → Cmatch (Val.cmplu_bool valid c (.Vptr b1 ofs1) (.Vptr b2 ofs2))
      (cmpDifferentBlocks strict c) := by
    intro hne
    simp only [Val.cmplu_bool, Archi.ptr64, hne, Bool.not_true, Bool.false_eq_true, if_false]
    split
    · exact cmp_different_blocks_sound strict c
    · exact cmp_different_blocks_none strict c
  have SAME : b1 = b2 → Cmatch (Val.cmplu_bool valid c (.Vptr b1 ofs1) (.Vptr b2 ofs2))
      (.Maybe (Ptrofs.cmpu c ofs1 ofs2)) := by
    intro he
    subst he
    simp only [Val.cmplu_bool, Archi.ptr64, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    split <;> constructor
  cases h1 <;> cases h2 <;> delta pcmp <;> (try dsimp only) <;>
    first
    | exact cmatch_top _
    | (apply DIFF; intro he; subst he; simp_all)
    | skip
  all_goals first
    | (apply SAME; apply bc.bc_stack <;> assumption)
    | (split
       · subst_vars; apply SAME; apply bc.bc_glob <;> assumption
       · exact cmatch_top _)

/-! ## Abstract values: `is_uns`, `is_sgn`, `usize`, `ssize` -/

theorem vmatch_num (v : Val) (p : Aptr) (h : match v with | .Vptr _ _ => False | _ => True) :
    Vmatch bc v (.Num p) := by
  cases v <;> first | constructor | exact h.elim

theorem vmatch_ifptr (v : Val) (p : Aptr) (h : ∀ b ofs, v = .Vptr b ofs → Pmatch bc b ofs p) :
    Vmatch bc v (.Ifptr p) := by
  cases v <;> constructor; exact h _ _ rfl

theorem vmatch_top {v : Val} {x : Aval} (h : Vmatch bc v x) : Vmatch bc v Vtop := by
  apply vmatch_ifptr; intro b ofs he; subst he
  cases h <;> exact pmatch_ge (.top _) ‹_›

theorem is_uns_mon {n1 n2 : Z} {i : Integers.Int} (h : IsUns n1 i) (hle : n1 ≤ n2) : IsUns n2 i :=
  fun m h1 h2 => h m h1 (by zomega)

theorem is_sgn_mon {n1 n2 : Z} {i : Integers.Int} (h : IsSgn n1 i) (hle : n1 ≤ n2) : IsSgn n2 i :=
  fun m h1 h2 => h m h1 (by zomega)

theorem is_uns_sgn {n1 n2 : Z} {i : Integers.Int} (h : IsUns n1 i) (hlt : n1 < n2) : IsSgn n2 i :=
  fun m h1 h2 => by
    rw [h m h1 (by zomega), h 31 (by simp [Integers.Int.zwordsize]) (by zomega)]

theorem zsize_nonneg (x : Z) : 0 ≤ Integers.Zsize x := by
  unfold Integers.Zsize; split <;> zomega

theorem bits_size_2 (x : Integers.Int) (m : Nat) (h : Integers.Int.size x ≤ m) :
    Integers.Int.testbit x m = false := by
  show x.getLsbD m = false
  rw [← BitVec.testBit_toNat]
  apply Nat.testBit_lt_two_pow
  simp only [Integers.Int.size, Integers.MI.size, Integers.Zsize, Integers.MI.unsigned, Z, Int.toNat_natCast] at h
  split at h
  · have := @Nat.lt_log2_self x.toNat
    have : 2 ^ (x.toNat.log2 + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have : x.toNat = 0 := by omega
    rw [this]; exact Nat.two_pow_pos _

theorem size_range (x : Integers.Int) : 0 ≤ Integers.Int.size x ∧ Integers.Int.size x ≤ 32 := by
  simp only [Integers.Int.size, Integers.MI.size, Integers.Zsize, Integers.MI.unsigned, Z, Int.toNat_natCast]
  split
  · have h1 : x.toNat < 2 ^ 32 := x.isLt
    have : x.toNat.log2 < 32 := (Nat.log2_lt (by omega)).2 h1
    omega
  · omega

theorem usize_pos (n : Integers.Int) : 0 ≤ usize n := zsize_nonneg _

theorem ssize_pos (n : Integers.Int) : 0 < ssize n := by
  have := zsize_nonneg (Integers.MI.unsigned (if Integers.Int.lt n Integers.Int.zero then Integers.Int.not n else n))
  unfold ssize Integers.Int.size Integers.MI.size; zomega

theorem is_uns_usize (i : Integers.Int) : IsUns (usize i) i :=
  fun m _ h2 => bits_size_2 i m h2

theorem is_sgn_ssize (i : Integers.Int) : IsSgn (ssize i) i := by
  intro m h1 h2
  unfold ssize at h2
  simp only [Integers.Int.zwordsize] at h1
  cases hlt : Integers.Int.lt i Integers.Int.zero <;>
    simp only [hlt, Bool.false_eq_true, if_false, if_true] at h2
  · have := size_range i
    rw [bits_size_2 i m (by zomega), bits_size_2 i 31 (by zomega)]
  · have := size_range (Integers.Int.not i)
    have e1 := Integers.Int.bits_not i (i := m) (by zomega)
    have e2 := Integers.Int.bits_not i (i := 31) (by omega)
    rw [bits_size_2 _ m (by zomega)] at e1
    rw [bits_size_2 _ 31 (by zomega)] at e2
    revert e1 e2
    cases Integers.Int.testbit i m <;> cases Integers.Int.testbit i 31 <;> simp

theorem is_uns_zero_ext (n : Nat) (i : Integers.Int) :
    IsUns n i ↔ Integers.Int.zero_ext n i = i := by
  constructor
  · intro h
    apply Integers.Int.same_bits_eq; intro j hj
    rw [Integers.Int.bits_zero_ext]
    by_cases hjn : j < n
    · simp [hjn]
    · simp only [hjn, decide_false, Bool.false_and]
      exact (h j (by zomega) (by zomega)).symm
  · intro h m _ h2
    rw [← h, Integers.Int.bits_zero_ext]
    have : ¬ m < n := by zomega
    simp [this]

theorem is_sgn_sign_ext {n : Nat} (hn : 0 < n) (i : Integers.Int) :
    IsSgn n i ↔ Integers.Int.sign_ext n i = i := by
  constructor
  · intro h
    apply Integers.Int.same_bits_eq; intro j hj
    rw [Integers.Int.bits_sign_ext hn _ hj]
    by_cases hjn : j < n
    · simp [hjn]
    · simp only [hjn, if_false]
      rw [h (n - 1) (by zomega) (by zomega), h j (by zomega) (by zomega)]
  · intro h m h1 h2
    rw [← h, Integers.Int.bits_sign_ext hn _ (by zomega),
      Integers.Int.bits_sign_ext hn _ (by omega)]
    congr 1
    split <;> split <;> zomega

theorem is_zero_ext_uns (i : Integers.Int) (n : Nat) (m : Z) (h : IsUns m i ∨ (n : Z) ≤ m) :
    IsUns m (Integers.Int.zero_ext n i) := by
  intro k h1 h2
  rw [Integers.Int.bits_zero_ext]
  by_cases hk : k < n
  · rcases h with h | h
    · simp [h k h1 h2]
    · zomega
  · simp [hk]

theorem is_zero_ext_sgn (i : Integers.Int) (n : Nat) (m : Z) (h : (n : Z) < m) :
    IsSgn m (Integers.Int.zero_ext n i) := by
  intro k h1 h2
  rw [Integers.Int.bits_zero_ext, Integers.Int.bits_zero_ext]
  have a : ¬ k < n := by zomega
  have b : ¬ 31 < n := by zomega
  simp [a, b]

theorem is_sign_ext_uns (i : Integers.Int) (n : Nat) (m : Z) (hm : 0 ≤ m) (hmn : m < n)
    (h : IsUns m i) : IsUns m (Integers.Int.sign_ext n i) := by
  intro k h1 h2
  rw [Integers.Int.bits_sign_ext (by zomega) _ (by zomega)]
  split
  · exact h k h1 h2
  · exact h (n - 1) (by zomega) (by zomega)

theorem is_sign_ext_sgn (i : Integers.Int) (n : Nat) (m : Z) (hn : 0 < n)
    (h : IsSgn m i ∨ (n : Z) ≤ m) : IsSgn m (Integers.Int.sign_ext n i) := by
  intro k h1 h2
  rw [Integers.Int.bits_sign_ext hn _ (by zomega), Integers.Int.bits_sign_ext hn _ (by omega)]
  by_cases hk : k < n
  · rcases h with h | h
    · rw [if_pos hk, h k h1 h2]
      split
      · rfl
      · exact (h (n - 1) (by zomega) (by zomega)).symm
    · have : k = n - 1 := by zomega
      subst this
      rw [if_pos hk]
      split
      · congr 1; zomega
      · rfl
  · rw [if_neg hk]
    split
    · zomega
    · rfl

theorem is_uns_wordsize (i : Integers.Int) : IsUns Integers.Int.zwordsize i :=
  fun _ h1 h2 => by zomega

theorem is_sgn_wordsize (i : Integers.Int) : IsSgn Integers.Int.zwordsize i :=
  fun m h1 h2 => by
    have : m = 31 := by zomega
    subst this; rfl

theorem is_uns_0 {n : Integers.Int} (h : IsUns 0 n) : n = Integers.Int.zero := by
  apply Integers.Int.same_bits_eq; intro i hi
  rw [Integers.Int.bits_zero]; exact h i (by zomega) (by zomega)

theorem bits_one (i : Nat) : Integers.Int.testbit Integers.Int.one i = decide (i = 0) := by
  simp [Integers.Int.testbit, Integers.MI.testbit, Integers.Int.one, Integers.MI.one]

theorem is_uns_1 {n : Integers.Int} (h : IsUns 1 n) :
    n = Integers.Int.zero ∨ n = Integers.Int.one := by
  cases hb : Integers.Int.testbit n 0
  · left
    apply Integers.Int.same_bits_eq; intro i hi
    rw [Integers.Int.bits_zero]
    by_cases h0 : i = 0
    · subst h0; exact hb
    · exact h i (by zomega) (by zomega)
  · right
    apply Integers.Int.same_bits_eq; intro i hi
    rw [bits_one]
    by_cases h0 : i = 0
    · subst h0; simpa using hb
    · rw [h i (by zomega) (by zomega)]; simp [h0]

/-! ## Abstract values: smart constructors, ordering and least upper bound -/

local macro "va_close" : tactic =>
  `(tactic| first
    | assumption
    | exact pge_trans ‹_› ‹_›
    | exact pmatch_ge ‹_› ‹_›
    | zomega
    | exact is_uns_mon ‹_› (by zomega)
    | exact is_sgn_mon ‹_› (by zomega)
    | exact is_uns_sgn ‹_› (by zomega))

theorem vmatch_uns' (p : Aptr) (i : Integers.Int) (n : Z) (h : IsUns (max 0 n) i) :
    Vmatch bc (.Vint i) (uns p n) := by
  have A : ∀ n', n' ≥ 0 → n' ≥ n → IsUns n' i := fun n' h1 h2 =>
    is_uns_mon h (by simp only [Z] at *; omega)
  unfold uns
  repeat' split
  · have : max 0 n = 0 := by simp only [Z] at *; omega
    rw [this] at h; rw [is_uns_0 h]; constructor
  all_goals first
    | (constructor <;> (first | zomega | exact A _ (by zomega) (by zomega)))
    | constructor

theorem vmatch_uns (p : Aptr) (i : Integers.Int) (n : Z) (h : IsUns n i) :
    Vmatch bc (.Vint i) (uns p n) :=
  vmatch_uns' p i n (is_uns_mon h (by simp only [Z] at *; omega))

theorem vmatch_uns_undef (p : Aptr) (n : Z) : Vmatch bc .Vundef (uns p n) := by
  unfold uns; repeat' split
  all_goals constructor

theorem vmatch_sgn' (p : Aptr) (i : Integers.Int) (n : Z) (h : IsSgn (max 1 n) i) :
    Vmatch bc (.Vint i) (sgn p n) := by
  have A : ∀ n', n' ≥ 1 → n' ≥ n → IsSgn n' i := fun n' h1 h2 =>
    is_sgn_mon h (by simp only [Z] at *; omega)
  unfold sgn
  repeat' split
  all_goals first
    | (constructor <;> (first | zomega | exact A _ (by zomega) (by zomega)))
    | constructor

theorem vmatch_sgn (p : Aptr) (i : Integers.Int) (n : Z) (h : IsSgn n i) :
    Vmatch bc (.Vint i) (sgn p n) :=
  vmatch_sgn' p i n (is_sgn_mon h (by simp only [Z] at *; omega))

theorem vmatch_sgn_undef (p : Aptr) (n : Z) : Vmatch bc .Vundef (sgn p n) := by
  unfold sgn; repeat' split
  all_goals constructor

theorem vmatch_Uns_1 {p : Aptr} {v : Val} (h : Vmatch bc v (.Uns p 1)) :
    v = .Vundef ∨ v = .Vint Integers.Int.zero ∨ v = .Vint Integers.Int.one := by
  cases h with
  | Uns_undef => exact .inl rfl
  | Uns _ i _ _ hu =>
    rcases is_uns_1 hu with e | e <;> subst e <;> simp

theorem vmatch_Uns_0 {p : Aptr} {v : Val} (h : Vmatch bc v (.Uns p 0)) :
    v = .Vundef ∨ v = .Vint Integers.Int.zero := by
  cases h with
  | Uns_undef => exact .inl rfl
  | Uns _ i _ _ hu => exact .inr (by rw [is_uns_0 hu])

theorem vge_top (x : Aval) : Vge Vtop x := by
  unfold Vtop; cases x <;> constructor <;> exact .top _

theorem vge_refl (x : Aval) : Vge x x := by
  cases x <;> constructor <;> (first | exact .refl _ | zomega)

theorem vge_trans {x y z : Aval} (h1 : Vge x y) (h2 : Vge y z) : Vge x z := by
  cases h2 <;> cases h1 <;>
    first
    | (constructor <;> va_close <;> done)
    | skip

theorem vmatch_ge {v : Val} {x y : Aval} (hge : Vge x y) (hm : Vmatch bc v y) : Vmatch bc v x := by
  cases hge <;> cases hm <;>
    first
    | (constructor <;> va_close <;> done)
    | skip

theorem vlubInt_comm (cstr : Integers.Int → Aval) (i j : Integers.Int) :
    vlubInt cstr i j = vlubInt cstr j i := by
  unfold vlubInt
  by_cases h : i = j
  · subst h; rfl
  · have h1 : Integers.Int.eq i j = false := by simp [Integers.Int.eq, Integers.MI.eq, h]
    have h2 : Integers.Int.eq j i = false := by simp [Integers.Int.eq, Integers.MI.eq, Ne.symm h]
    simp only [h1, h2, Bool.false_eq_true, if_false, Bool.or_comm (Integers.Int.lt i _), Int.max_comm]

theorem vlub_comm (strict : Bool) (v w : Aval) : vlub strict v w = vlub strict w v := by
  cases v <;> cases w <;> delta vlub <;> dsimp only <;> (try rfl) <;>
    (try rw [vlubInt_comm]) <;> (try simp only [plub_comm, Int.max_comm]) <;>
    (repeat' split) <;> (try subst_vars) <;> (try rfl) <;>
    simp_all [Integers.Int64.eq, Integers.MI.eq]

theorem vge_uns_uns' (p : Aptr) (n : Z) : Vge (uns1 p n) (.Uns p n) := by
  unfold uns1; repeat' split
  all_goals constructor <;> (first | exact .refl _ | zomega)

theorem vge_uns_i' (p : Aptr) (n : Z) (i : Integers.Int) (h1 : 0 ≤ n) (h2 : IsUns n i) :
    Vge (uns1 p n) (.I i) :=
  vge_trans (vge_uns_uns' p n) (.uns_i p n i h1 h2)

theorem vge_uns_iu' (p : Aptr) (n : Z) (i : Integers.Int) (h1 : 0 ≤ n) (h2 : IsUns n i) :
    Vge (uns1 p n) (.IU i) :=
  vge_trans (vge_uns_uns' p n) (.uns_iu p n i h1 h2)

theorem vge_sgn_sgn' (p : Aptr) (n : Z) : Vge (sgn p n) (.Sgn p n) := by
  unfold sgn; repeat' split
  all_goals constructor <;> (first | exact .refl _ | zomega)

theorem vge_sgn_i' (p : Aptr) (n : Z) (i : Integers.Int) (h1 : 0 < n) (h2 : IsSgn n i) :
    Vge (sgn p n) (.I i) :=
  vge_trans (vge_sgn_sgn' p n) (.sgn_i p n i h1 h2)

theorem vge_sgn_iu' (p : Aptr) (n : Z) (i : Integers.Int) (h1 : 0 < n) (h2 : IsSgn n i) :
    Vge (sgn p n) (.IU i) :=
  vge_trans (vge_sgn_sgn' p n) (.sgn_iu p n i h1 h2)

theorem vlubInt_I_ge (i j : Integers.Int) : Vge (vlubInt .I i j) (.I i) := by
  unfold vlubInt
  split
  · constructor
  · split
    · exact vge_sgn_i' _ _ _ (by have := ssize_pos i; zomega)
        (is_sgn_mon (is_sgn_ssize i) (by zomega))
    · exact vge_uns_i' _ _ _ (by have := usize_pos i; zomega)
        (is_uns_mon (is_uns_usize i) (by zomega))

theorem vlubInt_IU_ge (i j : Integers.Int) : Vge (vlubInt .IU i j) (.IU i) := by
  unfold vlubInt
  split
  · constructor
  · split
    · exact vge_sgn_iu' _ _ _ (by have := ssize_pos i; zomega)
        (is_sgn_mon (is_sgn_ssize i) (by zomega))
    · exact vge_uns_iu' _ _ _ (by have := usize_pos i; zomega)
        (is_uns_mon (is_uns_usize i) (by zomega))

local macro "sgn_close" : tactic =>
  `(tactic| first
    | exact vge_trans (vge_sgn_sgn' _ _) (.sgn_sgn _ _ _ _ (by zomega) (pge_lub_l _ _))
    | exact vge_trans (vge_sgn_sgn' _ _) (.sgn_sgn _ _ _ _ (by zomega) (.refl _))
    | exact vge_trans (vge_sgn_sgn' _ _) (.sgn_uns _ _ _ _ (by zomega) (pge_lub_l _ _))
    | exact vge_trans (vge_sgn_sgn' _ _) (.sgn_uns _ _ _ _ (by zomega) (.refl _))
    | exact vge_trans (vge_uns_uns' _ _) (.uns_uns _ _ _ _ (by zomega) (.refl _))
    | exact vge_sgn_i' _ _ _ (by have := ssize_pos ‹Integers.Int›; zomega)
        (is_sgn_mon (is_sgn_ssize _) (by zomega))
    | exact vge_sgn_iu' _ _ _ (by have := ssize_pos ‹Integers.Int›; zomega)
        (is_sgn_mon (is_sgn_ssize _) (by zomega))
    | exact vge_uns_i' _ _ _ (by have := usize_pos ‹Integers.Int›; zomega)
        (is_uns_mon (is_uns_usize _) (by zomega))
    | exact vge_uns_iu' _ _ _ (by have := usize_pos ‹Integers.Int›; zomega)
        (is_uns_mon (is_uns_usize _) (by zomega)))

local macro "lub_close" : tactic =>
  `(tactic| first
    | (unfold ntop; constructor)
    | exact vlubInt_I_ge _ _
    | exact vlubInt_IU_ge _ _
    | exact vge_trans (vlubInt_IU_ge _ _) (.iu_i _)
    | (unfold vlubIUns; split <;> sgn_close)
    | sgn_close
    | (split <;> first | constructor | (unfold ntop; constructor))
    | (constructor <;> first | exact .refl _ | exact pge_lub_l _ _ | zomega))

theorem vge_lub_l (strict : Bool) (x y : Aval) : Vge (vlub strict x y) x := by
  cases x <;> cases y <;> delta vlub <;> dsimp only <;> lub_close

theorem vge_lub_r (strict : Bool) (x y : Aval) : Vge (vlub strict x y) y := by
  rw [vlub_comm]; exact vge_lub_l strict y x

theorem vmatch_lub_l (strict : Bool) {v : Val} {x : Aval} (y : Aval) (h : Vmatch bc v x) :
    Vmatch bc v (vlub strict x y) :=
  vmatch_ge (vge_lub_l strict x y) h

theorem vmatch_lub_r (strict : Bool) {v : Val} (x : Aval) {y : Aval} (h : Vmatch bc v y) :
    Vmatch bc v (vlub strict x y) :=
  vmatch_ge (vge_lub_r strict x y) h

/-! ## Inclusion, constants, and the generic operators -/

theorem match_aptr_of_aval (strict : Bool) {b : Block} {ofs : Ptrofs} {av : Aval}
    (h : Vmatch bc (.Vptr b ofs) av) : Pmatch bc b ofs (aptrOfAval strict av) := by
  cases h <;> simp only [aptrOfAval] <;> assumption

theorem vmatch_vplub_l {v : Val} {x : Aval} (p : Aptr) (h : Vmatch bc v x) :
    Vmatch bc v (.Ifptr (vplub x p)) := by
  cases h <;> simp only [vplub] <;> constructor <;> exact pmatch_lub_l _ ‹_›

theorem pmatch_vplub {b : Block} {ofs : Ptrofs} (x : Aval) {p : Aptr} (h : Pmatch bc b ofs p) :
    Pmatch bc b ofs (vplub x p) := by
  cases x <;> simp only [vplub] <;> first | exact h | exact pmatch_lub_r _ h

theorem vmatch_vplub_r {v : Val} (x : Aval) {p : Aptr} (h : Vmatch bc v (.Ifptr p)) :
    Vmatch bc v (.Ifptr (vplub x p)) := by
  apply vmatch_ifptr; intro b ofs he; subst he
  cases h with | ifptr_p _ _ _ hp => exact pmatch_vplub x hp

theorem vpincl_ge {x : Aval} {p : Aptr} (h : vpincl x p = true) : Vge (.Ifptr p) x := by
  cases x <;> simp only [vpincl] at h <;> constructor <;> exact pincl_ge h

theorem vpincl_sound {v : Val} {x : Aval} {p : Aptr} (h : vpincl x p = true)
    (hm : Vmatch bc v x) : Vmatch bc v (.Ifptr p) :=
  vmatch_ge (vpincl_ge h) hm

theorem is_uns_zero_ext_Z {n : Z} (hn : 0 ≤ n) (i : Integers.Int) :
    IsUns n i ↔ Integers.Int.zero_ext n.toNat i = i := by
  have := is_uns_zero_ext n.toNat i
  rwa [Int.toNat_of_nonneg hn] at this

theorem is_sgn_sign_ext_Z {n : Z} (hn : 0 < n) (i : Integers.Int) :
    IsSgn n i ↔ Integers.Int.sign_ext n.toNat i = i := by
  have := is_sgn_sign_ext (n := n.toNat) (by zomega) i
  rwa [Int.toNat_of_nonneg (by zomega)] at this

set_option hygiene false in
local macro "vincl_close" : tactic =>
  `(tactic| first
    | exact pincl_ge h
    | exact pincl_ge h.2
    | exact h.2
    | zomega
    | exact (is_uns_zero_ext_Z h.2 _).2 h.1
    | exact (is_sgn_sign_ext_Z h.2 _).2 h.1)

theorem vincl_ge {v w : Aval} (h : vincl v w = true) : Vge w v := by
  cases v <;> cases w <;> delta vincl at h <;> (try dsimp only at h) <;>
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at h) <;>
    first
    | (constructor; done)
    | (subst_vars; constructor; done)
    | (constructor <;> vincl_close; done)
    | cases h

local macro "ge_vincl_close" : tactic =>
  `(tactic| first
    | exact ge_pincl ‹_›
    | zomega
    | exact (is_uns_zero_ext_Z ‹_› _).1 ‹_›
    | exact (is_sgn_sign_ext_Z ‹_› _).1 ‹_›)

theorem ge_vincl {v w : Aval} (h : Vge v w) : vincl w v = true := by
  cases h <;> delta vincl <;> (try dsimp only) <;>
    (try simp only [Bool.and_eq_true, decide_eq_true_eq]) <;>
    first
    | trivial
    | (constructor <;> ge_vincl_close; done)
    | ge_vincl_close

theorem symbol_address_sound {F V : Type} {ge : Genv F V} (id : Ident) (ofs : Ptrofs)
    (hge : GenvMatch bc ge) : Vmatch bc (Genv.symbolAddress ge id ofs) (.Ptr (.Gl id ofs)) := by
  unfold Genv.symbolAddress
  cases hf : Genv.findSymbol ge id with
  | none => constructor
  | some b => exact .ptr _ _ _ (.gl _ ((hge.1 id b).1 hf))

theorem vmatch_ptr_gl {F V : Type} {ge : Genv F V} {v : Val} {id : Ident} {ofs : Ptrofs}
    (hge : GenvMatch bc ge) (h : Vmatch bc v (.Ptr (.Gl id ofs))) :
    Val.Lessdef v (Genv.symbolAddress ge id ofs) := by
  cases h with
  | ptr_undef => constructor
  | ptr b _ _ hp =>
    cases hp with
    | gl _ hb =>
      unfold Genv.symbolAddress
      rw [(hge.1 id b).2 hb]; constructor

theorem vmatch_ptr_stk {v : Val} {ofs : Ptrofs} {sp : Block}
    (h : Vmatch bc v (.Ptr (.Stk ofs))) (hsp : bc sp = .BCstack) :
    Val.Lessdef v (.Vptr sp ofs) := by
  cases h with
  | ptr_undef => constructor
  | ptr b _ _ hp =>
    cases hp with
    | stk hb => rw [bc.bc_stack _ _ hb hsp]; constructor

theorem unop_int_sound (sem : Integers.Int → Integers.Int) {v : Val} {x : Aval}
    (h : Vmatch bc v x) :
    Vmatch bc (match v with | .Vint i => .Vint (sem i) | _ => .Vundef) (unopInt sem x) := by
  cases h <;> simp only [unopInt, ntop1, provenance] <;> constructor

theorem binop_int_sound (sem : Integers.Int → Integers.Int → Integers.Int) {v w : Val} {x y : Aval}
    (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (match v, w with | .Vint i, .Vint j => .Vint (sem i j) | _, _ => .Vundef)
      (binopInt sem x y) := by
  cases h1 <;> cases h2 <;> simp only [binopInt, ntop2, provenance] <;> constructor

theorem unop_long_sound (sem : Integers.Int64 → Integers.Int64) {v : Val} {x : Aval}
    (h : Vmatch bc v x) :
    Vmatch bc (match v with | .Vlong i => .Vlong (sem i) | _ => .Vundef) (unopLong sem x) := by
  cases h <;> simp only [unopLong, ntop1, provenance] <;> constructor

theorem binop_long_sound (sem : Integers.Int64 → Integers.Int64 → Integers.Int64) {v w : Val}
    {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (match v, w with | .Vlong i, .Vlong j => .Vlong (sem i j) | _, _ => .Vundef)
      (binopLong sem x y) := by
  cases h1 <;> cases h2 <;> simp only [binopLong, ntop2, provenance] <;> constructor

theorem unop_float_sound (sem : Floats.Float → Floats.Float) {v : Val} {x : Aval}
    (h : Vmatch bc v x) :
    Vmatch bc (match v with | .Vfloat i => .Vfloat (sem i) | _ => .Vundef) (unopFloat sem x) := by
  cases h <;> simp only [unopFloat, ntop1, provenance] <;> constructor

theorem binop_float_sound (sem : Floats.Float → Floats.Float → Floats.Float) {v w : Val}
    {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (match v, w with | .Vfloat i, .Vfloat j => .Vfloat (sem i j) | _, _ => .Vundef)
      (binopFloat sem x y) := by
  cases h1 <;> cases h2 <;> simp only [binopFloat, ntop2, provenance] <;> constructor

theorem unop_single_sound (sem : Floats.Float32 → Floats.Float32) {v : Val} {x : Aval}
    (h : Vmatch bc v x) :
    Vmatch bc (match v with | .Vsingle i => .Vsingle (sem i) | _ => .Vundef)
      (unopSingle sem x) := by
  cases h <;> simp only [unopSingle, ntop1, provenance] <;> constructor

theorem binop_single_sound (sem : Floats.Float32 → Floats.Float32 → Floats.Float32) {v w : Val}
    {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (match v, w with | .Vsingle i, .Vsingle j => .Vsingle (sem i j) | _, _ => .Vundef)
      (binopSingle sem x y) := by
  cases h1 <;> cases h2 <;> simp only [binopSingle, ntop2, provenance] <;> constructor

/-! ## Shifts and bitwise logical operations -/

theorem int_unsigned_eq (n : Integers.Int) : Integers.Int.unsigned n = (n.toNat : Z) := rfl

theorem ltu_iwordsize {n : Integers.Int} (h : Integers.Int.ltu n Integers.Int.iwordsize = true) :
    n.toNat < 32 := by
  have := Integers.Int.ltu_inv h
  have e : Integers.Int.unsigned Integers.Int.iwordsize = 32 := by decide
  rw [e, int_unsigned_eq] at this
  zomega

theorem shl_uns {i n : Integers.Int} {n0 : Z} (hu : IsUns n0 i) :
    IsUns (max 0 (n0 + Integers.Int.unsigned n)) (Integers.Int.shl i n) := by
  intro m hm1 hm2
  rw [int_unsigned_eq] at hm2
  rw [Integers.Int.bits_shl _ _ (by zomega)]
  split
  · rfl
  · exact hu _ (by zomega) (by zomega)

theorem shl_sgn {i n : Integers.Int} {n0 : Z} (R : n.toNat < 32) (hn : 0 < n0) (hs : IsSgn n0 i) :
    IsSgn (max 1 (n0 + Integers.Int.unsigned n)) (Integers.Int.shl i n) := by
  intro m hm1 hm2
  rw [int_unsigned_eq] at hm2
  rw [Integers.Int.bits_shl _ _ (by zomega), Integers.Int.bits_shl _ _ (by zomega)]
  rw [if_neg (by zomega), if_neg (by zomega), hs (m - n.toNat) (by zomega) (by zomega),
    hs (31 - n.toNat) (by zomega) (by zomega)]

theorem shl_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.shl v w) (shl x y) := by
  have DEFAULT : Vmatch bc (Val.shl v w) (ntop1 x) := by
    cases v <;> cases w <;> simp only [Val.shl, ntop1] <;> (try split) <;> constructor
  cases y <;> simp only [shl] <;> try exact DEFAULT
  cases h2
  split
  · rename_i hlt
    have R := ltu_iwordsize hlt
    cases h1 <;> simp only [Val.shl, hlt, if_true] <;>
      first
      | constructor
      | exact vmatch_uns_undef _ _
      | exact vmatch_sgn_undef _ _
      | exact vmatch_uns' _ _ _ (shl_uns ‹_›)
      | exact vmatch_sgn' _ _ _ (shl_sgn R ‹_› ‹_›)
  · exact DEFAULT

theorem shru_uns_top (i n : Integers.Int) :
    IsUns (Integers.Int.zwordsize - Integers.Int.unsigned n) (Integers.Int.shru i n) := by
  intro m hm1 hm2
  rw [int_unsigned_eq] at hm2
  rw [Integers.Int.bits_shru _ _ (by zomega), if_neg (by zomega)]

theorem shru_uns {i n : Integers.Int} {n0 : Z} (hu : IsUns n0 i) :
    IsUns (max 0 (n0 - Integers.Int.unsigned n)) (Integers.Int.shru i n) := by
  intro m hm1 hm2
  rw [int_unsigned_eq] at hm2
  rw [Integers.Int.bits_shru _ _ (by zomega)]
  split
  · exact hu _ (by zomega) (by zomega)
  · rfl

theorem shru_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.shru v w) (shru x y) := by
  have DEFAULT : Vmatch bc (Val.shru v w) (ntop1 x) := by
    cases v <;> cases w <;> simp only [Val.shru, ntop1] <;> (try split) <;> constructor
  cases y <;> simp only [shru] <;> try exact DEFAULT
  cases h2
  split
  · rename_i hlt
    cases h1 <;> simp only [Val.shru, hlt, if_true] <;>
      first
      | constructor
      | exact vmatch_uns_undef _ _
      | exact vmatch_uns _ _ _ (shru_uns_top _ _)
      | exact vmatch_uns' _ _ _ (shru_uns ‹_›)
  · exact DEFAULT

theorem shr_sgn_top {i n : Integers.Int} (R : n.toNat < 32) :
    IsSgn (Integers.Int.zwordsize - Integers.Int.unsigned n) (Integers.Int.shr i n) := by
  intro m hm1 hm2
  rw [int_unsigned_eq] at hm2
  rw [Integers.Int.bits_shr _ _ (by zomega), Integers.Int.bits_shr _ _ (by zomega)]
  congr 1
  split <;> split <;> zomega

theorem shr_sgn {i n : Integers.Int} {p : Z} (R : n.toNat < 32) (hs : IsSgn p i) :
    IsSgn (max 1 (p - Integers.Int.unsigned n)) (Integers.Int.shr i n) := by
  intro m hm1 hm2
  rw [int_unsigned_eq] at hm2
  rw [Integers.Int.bits_shr _ _ (by zomega), Integers.Int.bits_shr _ _ (by zomega)]
  have e31 : (if 31 + n.toNat < 32 then 31 + n.toNat else 32 - 1) = 31 := by
    split <;> omega
  rw [e31]
  split
  · exact hs _ (by zomega) (by zomega)
  · rfl

theorem shr_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.shr v w) (shr x y) := by
  have DEFAULT : Vmatch bc (Val.shr v w) (ntop1 x) := by
    cases v <;> cases w <;> simp only [Val.shr, ntop1] <;> (try split) <;> constructor
  cases y <;> simp only [shr] <;> try exact DEFAULT
  cases h2
  split
  · rename_i hlt
    have R := ltu_iwordsize hlt
    cases h1 <;> simp only [Val.shr, hlt, if_true] <;>
      first
      | constructor
      | exact vmatch_sgn_undef _ _
      | exact vmatch_sgn _ _ _ (shr_sgn_top R)
      | exact vmatch_sgn' _ _ _ (shr_sgn R ‹_›)
      | (rw [show ∀ a b : Z, a + 1 - b = (a + 1) - b from fun _ _ => rfl]
         exact vmatch_sgn' _ _ _ (shr_sgn R (is_uns_sgn ‹_› (by zomega))))
  · exact DEFAULT

theorem and_uns_l {i j : Integers.Int} {n : Z} (h : IsUns n i) : IsUns n (Integers.Int.and i j) := by
  intro m hm1 hm2
  rw [Integers.Int.bits_and, h m hm1 hm2, Bool.false_and]

theorem and_uns_r {i j : Integers.Int} {n : Z} (h : IsUns n j) : IsUns n (Integers.Int.and i j) := by
  intro m hm1 hm2
  rw [Integers.Int.bits_and, h m hm1 hm2, Bool.and_false]

theorem and_uns_min {i j : Integers.Int} {n m : Z} (h1 : IsUns n i) (h2 : IsUns m j) :
    IsUns (min n m) (Integers.Int.and i j) := by
  by_cases hnm : n ≤ m
  · rw [Int.min_eq_left hnm]; exact and_uns_l h1
  · rw [Int.min_eq_right (by zomega)]; exact and_uns_r h2

theorem and_sgn_max {i j : Integers.Int} {n m : Z} (h1 : IsSgn n i) (h2 : IsSgn m j) :
    IsSgn (max n m) (Integers.Int.and i j) := by
  intro k hk1 hk2
  rw [Integers.Int.bits_and, Integers.Int.bits_and, h1 k hk1 (by zomega), h2 k hk1 (by zomega)]

theorem and_uns_min' {i j : Integers.Int} {n m : Z} (h1 : IsUns n j) (h2 : IsUns m i) :
    IsUns (min n m) (Integers.Int.and i j) := by
  rw [Int.min_comm]; exact and_uns_min h2 h1

local macro "and_close" : tactic =>
  `(tactic| first
    | constructor
    | exact vmatch_uns_undef _ _
    | exact vmatch_sgn_undef _ _
    | (apply vmatch_uns; apply and_uns_min <;> first | assumption | exact is_uns_usize _)
    | (apply vmatch_uns; apply and_uns_min' <;> first | assumption | exact is_uns_usize _)
    | (apply vmatch_uns; apply and_uns_l; first | assumption | exact is_uns_usize _)
    | (apply vmatch_uns; apply and_uns_r; first | assumption | exact is_uns_usize _)
    | (apply vmatch_sgn; apply and_sgn_max <;> assumption))

theorem and_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.and v w) (and x y) := by
  cases h1 <;> cases h2 <;> delta and <;> dsimp only <;> simp only [Val.and, ntop2] <;> and_close

theorem or_uns_max {i j : Integers.Int} {n m : Z} (h1 : IsUns n i) (h2 : IsUns m j) :
    IsUns (max n m) (Integers.Int.or i j) := by
  intro k hk1 hk2
  rw [Integers.Int.bits_or, h1 k hk1 (by zomega), h2 k hk1 (by zomega)]; rfl

theorem or_uns_max' {i j : Integers.Int} {n m : Z} (h1 : IsUns n j) (h2 : IsUns m i) :
    IsUns (max n m) (Integers.Int.or i j) := by
  rw [Int.max_comm]; exact or_uns_max h2 h1

theorem or_sgn_max {i j : Integers.Int} {n m : Z} (h1 : IsSgn n i) (h2 : IsSgn m j) :
    IsSgn (max n m) (Integers.Int.or i j) := by
  intro k hk1 hk2
  rw [Integers.Int.bits_or, Integers.Int.bits_or, h1 k hk1 (by zomega), h2 k hk1 (by zomega)]

theorem xor_uns_max {i j : Integers.Int} {n m : Z} (h1 : IsUns n i) (h2 : IsUns m j) :
    IsUns (max n m) (Integers.Int.xor i j) := by
  intro k hk1 hk2
  rw [Integers.Int.bits_xor, h1 k hk1 (by zomega), h2 k hk1 (by zomega)]; rfl

theorem xor_uns_max' {i j : Integers.Int} {n m : Z} (h1 : IsUns n j) (h2 : IsUns m i) :
    IsUns (max n m) (Integers.Int.xor i j) := by
  rw [Int.max_comm]; exact xor_uns_max h2 h1

theorem xor_sgn_max {i j : Integers.Int} {n m : Z} (h1 : IsSgn n i) (h2 : IsSgn m j) :
    IsSgn (max n m) (Integers.Int.xor i j) := by
  intro k hk1 hk2
  rw [Integers.Int.bits_xor, Integers.Int.bits_xor, h1 k hk1 (by zomega), h2 k hk1 (by zomega)]

local macro "orxor_close" : tactic =>
  `(tactic| first
    | constructor
    | exact vmatch_uns_undef _ _
    | exact vmatch_sgn_undef _ _
    | (apply vmatch_uns; first
        | (apply or_uns_max <;> first | assumption | exact is_uns_usize _)
        | (apply or_uns_max' <;> first | assumption | exact is_uns_usize _)
        | (apply xor_uns_max <;> first | assumption | exact is_uns_usize _)
        | (apply xor_uns_max' <;> first | assumption | exact is_uns_usize _))
    | (apply vmatch_sgn; first
        | (apply or_sgn_max <;> assumption)
        | (apply xor_sgn_max <;> assumption)))

theorem or_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.or v w) (or x y) := by
  cases h1 <;> cases h2 <;> delta or <;> dsimp only <;> simp only [Val.or, ntop2] <;> orxor_close

theorem xor_sound {v w : Val} {x y : Aval} (h1 : Vmatch bc v x) (h2 : Vmatch bc w y) :
    Vmatch bc (Val.xor v w) (xor x y) := by
  cases h1 <;> cases h2 <;> delta xor <;> dsimp only <;> simp only [Val.xor, ntop2] <;> orxor_close

theorem notint_uns {i : Integers.Int} {n : Z} (h : IsUns n i) :
    IsSgn (n + 1) (Integers.Int.not i) := by
  intro k hk1 hk2
  rw [Integers.Int.bits_not _ (by zomega), Integers.Int.bits_not _ (by omega),
    h k hk1 (by zomega), h 31 (by zomega) (by zomega)]

theorem notint_sgn {i : Integers.Int} {n : Z} (h : IsSgn n i) :
    IsSgn n (Integers.Int.not i) := by
  intro k hk1 hk2
  rw [Integers.Int.bits_not _ (by zomega), Integers.Int.bits_not _ (by omega), h k hk1 hk2]

theorem notint_sound {v : Val} {x : Aval} (h : Vmatch bc v x) :
    Vmatch bc (Val.notint v) (notint x) := by
  cases h <;> simp only [Val.notint, notint, ntop1] <;>
    first
    | (constructor <;> (first | assumption | exact notint_sgn ‹_›))
    | exact vmatch_sgn_undef _ _
    | exact vmatch_sgn _ _ _ (notint_uns ‹_›)

end

end ValueDomain
end CC
