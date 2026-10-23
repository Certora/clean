/-
  Lemmas about `Positive`, `ZIndexed` and `ZMap` that the memory-model proofs
  need — Phase 7.1 of the separation-logic plan.

  `CCLib/lib/Maps.lean` shipped the definitions plus `gi`/`gss`/`gso` for `PTree` and
  `PMap`, but `ZMap` got only `gi`/`gss`.  The missing `ZMap.gso` ("writing one
  offset does not disturb another") is what every `getN`/`setN` lemma rests on,
  and it needs `ZIndexed.index` to be injective — which in turn needs
  `Positive.ofNat` to be injective, which needs `toNat_ofNat`.  None of that
  chain existed, so it is built here.
-/
import CCLib.lib.Maps

namespace CC
namespace Positive

/-- `(ofNat n).toNat = n` for positive `n`.  `ofNatAux` recurses on a fuel
    argument (so that it reduces in the kernel), hence the `n ≤ fuel` invariant. -/
theorem toNat_ofNatAux : ∀ (fuel n : Nat), 0 < n → n ≤ fuel → (ofNatAux fuel n).toNat = n := by
  intro fuel
  induction fuel with
  | zero => intro n h1 h2; omega
  | succ f ih =>
      intro n h1 h2
      -- `cases`, not `match`: `match` in tactic mode does not substitute into
      -- the other hypotheses, so `h2` would keep mentioning `n`.
      cases n with
      | zero => omega
      | succ k =>
        cases k with
        | zero => rfl
        | succ j =>
          simp only [ofNatAux]
          split
          · next h =>
              simp only [beq_iff_eq] at h
              simp only [toNat, ih ((j+2)/2) (by omega) (by omega)]; omega
          · next h =>
              simp only [beq_iff_eq] at h
              simp only [toNat, ih ((j+2)/2) (by omega) (by omega)]; omega

theorem toNat_ofNat (n : Nat) (h : 0 < n) : (ofNat n).toNat = n :=
  toNat_ofNatAux n n h (Nat.le_refl n)

theorem ofNat_inj {a b : Nat} (ha : 0 < a) (hb : 0 < b) (h : ofNat a = ofNat b) : a = b := by
  have h1 := toNat_ofNat a ha
  have h2 := toNat_ofNat b hb
  rw [h] at h1; omega

end Positive

namespace ZIndexed

/-- A left inverse of `index`, which is the cheapest route to injectivity: the
    direct case analysis stalls because `cases` leaves the `Int` scrutinee in a
    form the `match` in `index` will not reduce against. -/
def unindex : Positive → Int
  | .xH => 0
  | .xO q => (q.toNat : Int)
  | .xI q => -(q.toNat : Int)

theorem unindex_index (z : Int) : unindex (index z) = z := by
  cases z with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ k =>
          show ((Positive.ofNat (k+1)).toNat : Int) = _
          rw [Positive.toNat_ofNat _ (by omega)]; rfl
  | negSucc n =>
      show -((Positive.ofNat (n+1)).toNat : Int) = _
      rw [Positive.toNat_ofNat _ (by omega)]; rfl

/-- `ZIndexed.index` is injective. -/
theorem index_inj {i j : Int} (h : index i = index j) : i = j := by
  rw [← unindex_index i, ← unindex_index j, h]

end ZIndexed

namespace ZMap
variable {A : Type}

/-- `ZMap.gso` — writing one offset does not disturb another. -/
theorem gso (i j : Int) (v : A) (m : ZMap A) (h : i ≠ j) :
    get j (set i v m) = get j m :=
  PMap.gso (ZIndexed.index i) (ZIndexed.index j) v m
    (fun heq => h (ZIndexed.index_inj heq))

end ZMap
end CC
