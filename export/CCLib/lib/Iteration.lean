/-
  Port of `lib/Iteration.v`: Bounded and unbounded iterators.

  Ported:
  * `WfIter`: iteration along a well-founded order (`iterate`, `iterate_prop`);
  * `PrimIter`: bounded iteration with `num_iterations` steps of fuel
    (`iterate`, `iterate_prop`), used by the dataflow solvers in
    `backend/Kildall.lean`;
  * `GenIter`: unbounded iteration defined classically (`F_iter`, `iter`,
    `iter_monot`, `iter_either`, `converges_to` and its properties,
    `iterate`, `converges_to_iterate`, `iterate_converges_to`, `iter_prop`,
    `iterate_prop`);
  * `CountedLoop`: folds over integer ranges (`up`, `down`, `unroll_up`,
    `up_split`, `unroll_up_rev`, `up_induction`, `unroll_down`, `down_split`,
    `unroll_down_rev`, `down_induction`).

  Differences from Rocq:
  * `WfIter.iterate` uses `WellFounded.fix` instead of a fixpoint over `Acc`.
  * `PrimIter` counts iterations with a `Nat` fuel instead of a `positive`
    and `Acc Plt` (same behaviour: `num_iterations` = 10^12 steps).
  * `GenIter` does not take the hypotheses `EM` and
    `ConstructiveDefiniteDescription`: Lean's classical logic provides them.
  * `CountedLoop.up`/`down` are defined by well-founded recursion on
    `hi - lo`, so `unroll_up`/`unroll_down` are their defining equations.
-/

namespace CC

/-! ## Iteration along a well-founded order -/

namespace WfIter

variable {A B : Type _} (step : A → B ⊕ A) (ord : A → A → Prop)
  (ord_wf : WellFounded ord) (step_decr : ∀ a a', step a = .inr a' → ord a' a)

/-- `WfIter.iterate` -/
noncomputable def iterate (a : A) : B :=
  ord_wf.fix (C := fun _ => B)
    (fun a rec =>
      match h : step a with
      | .inl b => b
      | .inr a' => rec a' (step_decr a a' h))
    a

/-- `WfIter.iterate_prop`: Hoare rule for `while` loops. -/
theorem iterate_prop (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a, P a → match step a with | .inl b => Q b | .inr a' => P a') :
    ∀ a, P a → Q (iterate step ord ord_wf step_decr a) := by
  intro a
  induction a using ord_wf.induction with
  | _ a ih =>
    intro ha
    unfold iterate
    rw [WellFounded.fix_eq]
    have hs := step_prop a ha
    split
    · next b h => rw [h] at hs; exact hs
    · next a' h => rw [h] at hs; exact ih a' (step_decr a a' h) hs

end WfIter

/-! ## Bounded iteration -/

namespace PrimIter

/-- `PrimIter.num_iterations` -/
def numIterations : Nat := 1000000000000

/-- Bounded iteration of `step`. -/
def iterateFuel {A B : Type} (step : A → B ⊕ A) : Nat → A → Option B
  | 0, _ => none
  | n + 1, a =>
      match step a with
      | .inl b => some b
      | .inr a' => iterateFuel step n a'

/-- `PrimIter.iterate` -/
def iterate {A B : Type} (step : A → B ⊕ A) (a : A) : Option B := iterateFuel step numIterations a

/-- `PrimIter.iterate_prop` -/
theorem iterate_prop {A B : Type} (step : A → B ⊕ A) (P : A → Prop) (Q : B → Prop)
    (hstep : ∀ a, P a → match step a with | .inl b => Q b | .inr a' => P a')
    (a : A) (b : B) (h : iterate step a = some b) (ha : P a) : Q b := by
  unfold iterate at h
  generalize numIterations = n at h
  induction n generalizing a with
  | zero => simp [iterateFuel] at h
  | succ n ih =>
    simp only [iterateFuel] at h
    have hs := hstep a ha
    split at h
    · next b' he => rw [he] at hs; cases h; exact hs
    · next a' he => rw [he] at hs; first | exact ih a' h hs | exact ih a' hs h

end PrimIter

/-! ## General (unbounded) iteration, defined classically -/

namespace GenIter

variable {A B : Type _} (step : A → B ⊕ A)

/-- `GenIter.B_le` -/
def B_le (x y : Option B) : Prop := x = none ∨ y = x

/-- `GenIter.F_le` -/
def F_le (x y : A → Option B) : Prop := ∀ a, B_le (x a) (y a)

/-- `GenIter.F_iter` -/
def F_iter (next : A → Option B) (a : A) : Option B :=
  match step a with
  | .inl b => some b
  | .inr a' => next a'

theorem F_iter_monot (f g : A → Option B) (h : F_le f g) :
    F_le (F_iter step f) (F_iter step g) := by
  intro a
  unfold F_iter
  cases step a with
  | inl b => exact .inr rfl
  | inr a' => exact h a'

/-- `GenIter.iter` -/
def iter : Nat → A → Option B
  | 0 => fun _ => none
  | m + 1 => F_iter step (iter m)

theorem iter_monot : ∀ p q, p ≤ q → F_le (iter step p) (iter step q)
  | 0, _, _ => fun _ => .inl rfl
  | p + 1, 0, h => absurd h (by omega)
  | p + 1, q + 1, h => F_iter_monot step _ _ (iter_monot p q (by omega))

theorem iter_either (a : A) :
    (∃ n b, iter step n a = some b) ∨ (∀ n, iter step n a = none) := by
  by_cases h : ∃ n, iter step n a ≠ none
  · left
    obtain ⟨n, hn⟩ := h
    cases e : iter step n a with
    | none => exact absurd e hn
    | some b => exact ⟨n, b, e⟩
  · right
    intro n
    cases e : iter step n a with
    | none => rfl
    | some b => exact absurd ⟨n, by simp [e]⟩ h

/-- `GenIter.converges_to` -/
def converges_to (a : A) (b : Option B) : Prop :=
  ∃ n, ∀ m, n ≤ m → iter step m a = b

theorem converges_to_Some (a : A) (n : Nat) (b : B) (h : iter step n a = some b) :
    converges_to step a (some b) := by
  refine ⟨n, fun m hm => ?_⟩
  rcases iter_monot step n m hm a with e | e
  · rw [h] at e; cases e
  · rw [e, h]

theorem converges_to_exists (a : A) : ∃ b, converges_to step a b := by
  rcases iter_either step a with ⟨n, b, e⟩ | h
  · exact ⟨some b, converges_to_Some step a n b e⟩
  · exact ⟨none, 0, fun m _ => h m⟩

theorem converges_to_unique (a : A) (b : Option B) (hb : converges_to step a b)
    (b' : Option B) (hb' : converges_to step a b') : b = b' := by
  obtain ⟨n, C⟩ := hb
  obtain ⟨n', C'⟩ := hb'
  rw [← C (max n n') (Nat.le_max_left _ _), ← C' (max n n') (Nat.le_max_right _ _)]

theorem converges_to_exists_uniquely (a : A) :
    ∃ b, converges_to step a b ∧ ∀ b', converges_to step a b' → b = b' := by
  obtain ⟨b, h⟩ := converges_to_exists step a
  exact ⟨b, h, converges_to_unique step a b h⟩

/-- `GenIter.iterate`: the limit of `iter n a`; `none` means non-termination. -/
noncomputable def iterate (a : A) : Option B :=
  Classical.choose (converges_to_exists step a)

theorem iterate_converges_to (a : A) : converges_to step a (iterate step a) :=
  Classical.choose_spec (converges_to_exists step a)

theorem converges_to_iterate (a : A) (b : Option B) (h : converges_to step a b) :
    iterate step a = b :=
  converges_to_unique step a _ (iterate_converges_to step a) b h

theorem iter_prop (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a, P a → match step a with | .inl b => Q b | .inr a' => P a') :
    ∀ n a b, P a → iter step n a = some b → Q b
  | 0, _, _, _, h => by cases h
  | n + 1, a, b, ha, h => by
    have hs := step_prop a ha
    simp only [iter, F_iter] at h
    revert hs h
    cases step a with
    | inl b' => intro h hs; cases h; exact hs
    | inr a' => intro h hs; exact iter_prop P Q step_prop n a' b hs h

theorem iterate_prop (P : A → Prop) (Q : B → Prop)
    (step_prop : ∀ a, P a → match step a with | .inl b => Q b | .inr a' => P a')
    (a : A) (b : B) (h : iterate step a = some b) (ha : P a) : Q b := by
  obtain ⟨n, IT⟩ := iterate_converges_to step a
  rw [h] at IT
  exact iter_prop step P Q step_prop n a b ha (IT n (Nat.le_refl _))

end GenIter

/-! ## Counted loops: folds over integer ranges -/

namespace CountedLoop

variable {A : Type _} (f : Int → A → A)

/-- `CountedLoop.up f lo hi a` is `a |> f lo |> f (lo+1) |> ... |> f (hi-1)`. -/
def up (lo hi : Int) (a : A) : A :=
  if lo < hi then up (lo + 1) hi (f lo a) else a
termination_by (hi - lo).toNat
decreasing_by omega

/-- `CountedLoop.down f hi lo a` is `a |> f (hi-1) |> ... |> f (lo+1) |> f lo`. -/
def down (hi lo : Int) (a : A) : A :=
  if lo < hi then down (hi - 1) lo (f (hi - 1) a) else a
termination_by (hi - lo).toNat
decreasing_by omega

theorem unroll_up (lo hi : Int) (a : A) :
    up f lo hi a = if lo < hi then up f (lo + 1) hi (f lo a) else a := by
  rw [up]

theorem up_split (lo mid hi : Int) (a : A) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    up f lo hi a = up f mid hi (up f lo mid a) := by
  induction h : (mid - lo).toNat generalizing lo a with
  | zero =>
    have : lo = mid := by omega
    subst this
    rw [unroll_up f lo lo a, if_neg (Int.lt_irrefl _)]
  | succ n ih =>
    rw [unroll_up f lo mid a, if_pos (by omega), unroll_up f lo hi a, if_pos (by omega)]
    exact ih (lo + 1) (f lo a) (by omega) (by omega)

theorem unroll_up_rev (lo hi : Int) (a : A) :
    up f lo hi a = if lo < hi then f (hi - 1) (up f lo (hi - 1) a) else a := by
  by_cases hlt : lo < hi
  · rw [if_pos hlt, up_split f lo (hi - 1) hi a (by omega) (by omega),
      unroll_up f (hi - 1) hi, if_pos (by omega), unroll_up f (hi - 1 + 1) hi,
      if_neg (by omega)]
  · rw [if_neg hlt, unroll_up, if_neg hlt]

theorem up_induction (P : Int → A → Prop) (lo hi : Int) (a : A)
    (hstep : ∀ i a, lo ≤ i → i < hi → P i a → P (i + 1) (f i a))
    (hinit : P (min lo hi) a) : P hi (up f lo hi a) := by
  by_cases hle : lo ≤ hi
  · rw [Int.min_eq_left hle] at hinit
    suffices REC : ∀ n x b, (hi - x).toNat = n → lo ≤ x → x ≤ hi → P x b →
        P hi (up f x hi b) from REC _ lo a rfl (Int.le_refl _) hle hinit
    intro n
    induction n with
    | zero =>
      intro x b hn h1 h2 hp
      have : x = hi := by omega
      subst this
      rw [unroll_up, if_neg (Int.lt_irrefl _)]; exact hp
    | succ n ih =>
      intro x b hn h1 h2 hp
      rw [unroll_up, if_pos (by omega)]
      exact ih (x + 1) (f x b) (by omega) (by omega) (by omega) (hstep x b h1 (by omega) hp)
  · rw [Int.min_eq_right (by omega)] at hinit
    rw [unroll_up, if_neg (by omega)]; exact hinit

theorem unroll_down (hi lo : Int) (a : A) :
    down f hi lo a = if lo < hi then down f (hi - 1) lo (f (hi - 1) a) else a := by
  rw [down]

theorem down_split (lo mid hi : Int) (a : A) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    down f hi lo a = down f mid lo (down f hi mid a) := by
  induction h : (hi - mid).toNat generalizing hi a with
  | zero =>
    have : hi = mid := by omega
    subst this
    rw [unroll_down f hi hi a, if_neg (Int.lt_irrefl _)]
  | succ n ih =>
    rw [unroll_down f hi mid a, if_pos (by omega), unroll_down f hi lo a, if_pos (by omega)]
    exact ih (hi - 1) (f (hi - 1) a) (by omega) (by omega)

theorem unroll_down_rev (hi lo : Int) (a : A) :
    down f hi lo a = if lo < hi then f lo (down f hi (lo + 1) a) else a := by
  by_cases hlt : lo < hi
  · rw [if_pos hlt, down_split f lo (lo + 1) hi a (by omega) (by omega),
      unroll_down f (lo + 1) lo, if_pos (by omega), unroll_down f (lo + 1 - 1) lo,
      if_neg (by omega), show lo + 1 - 1 = lo by omega]
  · rw [if_neg hlt, unroll_down, if_neg hlt]

theorem down_induction (P : Int → A → Prop) (lo hi : Int) (a : A)
    (hstep : ∀ i a, lo ≤ i → i < hi → P (i + 1) a → P i (f i a))
    (hinit : P (max lo hi) a) : P lo (down f hi lo a) := by
  by_cases hle : lo ≤ hi
  · rw [Int.max_eq_right hle] at hinit
    suffices REC : ∀ n x b, (x - lo).toNat = n → lo ≤ x → x ≤ hi → P x b →
        P lo (down f x lo b) from REC _ hi a rfl hle (Int.le_refl _) hinit
    intro n
    induction n with
    | zero =>
      intro x b hn h1 h2 hp
      have : x = lo := by omega
      subst this
      rw [unroll_down, if_neg (Int.lt_irrefl _)]; exact hp
    | succ n ih =>
      intro x b hn h1 h2 hp
      rw [unroll_down, if_pos (by omega)]
      refine ih (x - 1) (f (x - 1) b) (by omega) (by omega) (by omega)
        (hstep (x - 1) b (by omega) (by omega) ?_)
      rw [show x - 1 + 1 = x by omega]; exact hp
  · rw [Int.max_eq_left (by omega)] at hinit
    rw [unroll_down, if_neg (by omega)]; exact hinit

end CountedLoop

end CC
