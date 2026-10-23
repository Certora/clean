/-
  Port of `lib/Ordered.v`: constructions of ordered types.

  Rocq uses these modules as arguments of the `FSet`/`FMap` functors.  Here an
  ordered type is the class `OrderedType` below: a strict order `lt` together
  with a computable three-way comparison `compare` that agrees with it.
  Equality is Lean's equality, as in all the Rocq instances except
  `OrderedPair`, whose equality is componentwise and therefore also Lean's
  equality once the components use it.

  Ported: `OrderedPositive`, `OrderedZ`, `OrderedInt` (machine integers ordered
  by `Int.unsigned`), `OrderedIndexed` (types injecting into `Positive`), and
  `OrderedPair` (lexicographic product), each with `eq_refl`/`eq_sym`/
  `eq_trans` (trivial for Lean's equality), `lt_trans`, `lt_not_eq`, `compare`
  and `eq_dec`.

  Differences from Rocq: Rocq's `compare` returns the dependent
  `Compare lt eq x y`; here it returns an `Ordering` and `compare_spec` states
  which relation holds.  `OrderedIndexed` takes the index function and its
  injectivity proof as arguments instead of an `INDEXED_TYPE` module.
-/
import CCLib.lib.Integers
import CCLib.lib.Positive

namespace CC

/-- An ordered type: a strict order with a computable comparison. -/
class OrderedType (t : Type _) where
  lt : t → t → Prop
  lt_trans : ∀ x y z, lt x y → lt y z → lt x z
  lt_not_eq : ∀ x y, lt x y → x ≠ y
  compare : t → t → Ordering
  compare_spec : ∀ x y,
    match compare x y with
    | .lt => lt x y
    | .eq => x = y
    | .gt => lt y x

namespace OrderedType

variable {t : Type _} [OrderedType t]

theorem eq_refl (x : t) : x = x := rfl
theorem eq_sym {x y : t} (h : x = y) : y = x := h.symm
theorem eq_trans {x y z : t} (h1 : x = y) (h2 : y = z) : x = z := h1.trans h2

theorem lt_irrefl (x : t) : ¬ lt x x := fun h => lt_not_eq x x h rfl

theorem lt_asymm {x y : t} (h : lt x y) : ¬ lt y x := fun h' => lt_irrefl x (lt_trans _ _ _ h h')

theorem compare_lt_iff (x y : t) : compare x y = .lt ↔ lt x y := by
  have := compare_spec x y
  constructor
  · intro h; rw [h] at this; exact this
  · intro h
    revert this
    cases compare x y with
    | lt => intro; rfl
    | eq => intro e; subst e; exact absurd h (lt_irrefl _)
    | gt => intro h'; exact absurd h' (lt_asymm h)

theorem compare_eq_iff (x y : t) : compare x y = .eq ↔ x = y := by
  have := compare_spec x y
  constructor
  · intro h; rw [h] at this; exact this
  · intro e
    subst e
    revert this
    cases compare x x with
    | lt => intro h; exact absurd h (lt_irrefl _)
    | eq => intro; rfl
    | gt => intro h; exact absurd h (lt_irrefl _)

theorem compare_gt_iff (x y : t) : compare x y = .gt ↔ lt y x := by
  have := compare_spec x y
  constructor
  · intro h; rw [h] at this; exact this
  · intro h
    revert this
    cases compare x y with
    | lt => intro h'; exact absurd h' (lt_asymm h)
    | eq => intro e; subst e; exact absurd h (lt_irrefl _)
    | gt => intro; rfl

/-- `eq_dec`, derived from `compare`. -/
def eq_dec (x y : t) : Decidable (x = y) :=
  decidable_of_iff (compare x y = .eq) (compare_eq_iff x y)

end OrderedType

/-- `Positive.toNat` is injective. -/
theorem Positive.toNat_injective : ∀ {p q : Positive}, p.toNat = q.toNat → p = q
  | .xH, .xH, _ => rfl
  | .xH, .xO q, h => by have := Positive.toNat_pos q; simp only [Positive.toNat] at h; omega
  | .xH, .xI q, h => by have := Positive.toNat_pos q; simp only [Positive.toNat] at h; omega
  | .xO p, .xH, h => by have := Positive.toNat_pos p; simp only [Positive.toNat] at h; omega
  | .xI p, .xH, h => by have := Positive.toNat_pos p; simp only [Positive.toNat] at h; omega
  | .xO p, .xO q, h => by
    simp only [Positive.toNat] at h; rw [Positive.toNat_injective (p := p) (q := q) (by omega)]
  | .xI p, .xI q, h => by
    simp only [Positive.toNat] at h; rw [Positive.toNat_injective (p := p) (q := q) (by omega)]
  | .xO p, .xI q, h => by simp only [Positive.toNat] at h; omega
  | .xI p, .xO q, h => by simp only [Positive.toNat] at h; omega

/-- Build an ordered type from an injection into `Nat`, ordered by `<`. -/
def OrderedType.ofNatInj {t : Type _} (f : t → Nat) (inj : ∀ x y, f x = f y → x = y) :
    OrderedType t where
  lt x y := f x < f y
  lt_trans _ _ _ h1 h2 := Nat.lt_trans h1 h2
  lt_not_eq _ _ h e := by subst e; exact Nat.lt_irrefl _ h
  compare x y := Ord.compare (f x) (f y)
  compare_spec x y := by
    rcases Nat.lt_trichotomy (f x) (f y) with h | h | h
    · rw [Nat.compare_eq_lt.2 h]; exact h
    · rw [Nat.compare_eq_eq.2 h]; exact inj _ _ h
    · rw [Nat.compare_eq_gt.2 h]; exact h

/-- `OrderedPositive`: positives ordered by `Plt`. -/
instance OrderedPositive : OrderedType Positive :=
  OrderedType.ofNatInj Positive.toNat (fun _ _ h => Positive.toNat_injective h)

/-- `OrderedZ`: integers ordered by `<`. -/
instance OrderedZ : OrderedType Int where
  lt x y := x < y
  lt_trans _ _ _ h1 h2 := Int.lt_trans h1 h2
  lt_not_eq _ _ h e := by subst e; exact Int.lt_irrefl _ h
  compare x y := Ord.compare x y
  compare_spec x y := by
    rcases Int.lt_trichotomy x y with h | h | h
    · rw [Int.compare_eq_lt.2 h]; exact h
    · rw [Int.compare_eq_eq.2 h]; exact h
    · rw [Int.compare_eq_gt.2 h]; exact h

/-- `OrderedInt`: machine integers ordered by `Int.unsigned`. -/
instance OrderedInt : OrderedType Integers.Int :=
  OrderedType.ofNatInj BitVec.toNat (fun _ _ h => BitVec.eq_of_toNat_eq h)

/-- `OrderedInt.lt` is `Int.unsigned x < Int.unsigned y`, as in Rocq. -/
theorem OrderedInt_lt_iff (x y : Integers.Int) :
    OrderedType.lt x y ↔ Integers.Int.unsigned x < Integers.Int.unsigned y := by
  show x.toNat < y.toNat ↔ _
  simp [Integers.Int.unsigned, Integers.MI.unsigned]

/-- `OrderedIndexed`: a type with an injection `index` into `Positive`,
ordered by the order of the indices. -/
def OrderedIndexed {t : Type _} (index : t → Positive)
    (index_inj : ∀ x y, index x = index y → x = y) : OrderedType t :=
  OrderedType.ofNatInj (fun x => (index x).toNat)
    (fun x y h => index_inj x y (Positive.toNat_injective h))

/-- `OrderedPair`: lexicographic product of two ordered types. -/
instance OrderedPair {A B : Type _} [OrderedType A] [OrderedType B] : OrderedType (A × B) where
  lt x y := OrderedType.lt x.1 y.1 ∨ (x.1 = y.1 ∧ OrderedType.lt x.2 y.2)
  lt_trans x y z h1 h2 := by
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact .inl (OrderedType.lt_trans _ _ _ h1 h2)
    · exact .inl (e2 ▸ h1)
    · exact .inl (e1 ▸ h2)
    · exact .inr ⟨e1.trans e2, OrderedType.lt_trans _ _ _ h1 h2⟩
  lt_not_eq x y h e := by
    subst e
    rcases h with h | ⟨_, h⟩ <;> exact OrderedType.lt_irrefl _ h
  compare x y :=
    match OrderedType.compare x.1 y.1 with
    | .eq => OrderedType.compare x.2 y.2
    | o => o
  compare_spec x y := by
    have h1 := OrderedType.compare_spec x.1 y.1
    revert h1
    cases OrderedType.compare x.1 y.1 with
    | lt => intro h; exact .inl h
    | gt => intro h; exact .inl h
    | eq =>
      intro e1
      have h2 := OrderedType.compare_spec x.2 y.2
      simp only
      revert h2
      cases OrderedType.compare x.2 y.2 with
      | lt => intro h; exact .inr ⟨e1, h⟩
      | gt => intro h; exact .inr ⟨e1.symm, h⟩
      | eq => intro e2; exact Prod.ext e1 e2

end CC
