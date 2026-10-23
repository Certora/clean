/-
  Persistent union-find over positive identifiers — port of the `UF`
  functor of `lib/UnionFind.v`, instantiated with `PTree` (the only
  instantiation used by CompCert, in `Tunneling.v`).

  Ported: `order`, `unionfind`, `repr` (with `repr_unroll`, `repr_none`,
  `repr_some`, `repr_res_none`, `repr_canonical`), `sameclass` and its
  equivalence lemmas, `empty`, `identify`, `union` with `repr_union_1/2/3`
  and `sameclass_union_*`, `merge` with `repr_merge`/`sameclass_merge`.

  Differences from Rocq: `repr` uses `WellFounded.fix` on the well-founded
  link order carried by the structure, as in Rocq.  The path-length
  material (`pathlen`, `path_ord`), used only by the Rocq proofs of
  `Tunnelingproof.v`, is not ported.
-/
import CCLib.lib.MapsTheory

namespace CC
namespace UnionFind

/-- `UF.order m a a'`: `a'` is linked to `a`. -/
def Order (m : PTree Positive) (a a' : Positive) : Prop := m.get a' = some a

/-- `UF.unionfind` -/
structure UF where
  m : PTree Positive
  mwf : WellFounded (Order m)

namespace UF

/-- `UF.repr`: the canonical representative of an element. -/
def repr (uf : UF) (a : Positive) : Positive :=
  uf.mwf.fix (C := fun _ => Positive)
    (fun a rec => match h : uf.m.get a with
      | some a' => rec a' h
      | none => a) a

/-- `UF.repr_unroll` -/
theorem repr_unroll (uf : UF) (a : Positive) :
    uf.repr a = match uf.m.get a with | some a' => uf.repr a' | none => a := by
  unfold repr
  rw [WellFounded.fix_eq]
  split <;> simp_all

/-- `UF.repr_none` -/
theorem repr_none (uf : UF) {a : Positive} (h : uf.m.get a = none) : uf.repr a = a := by
  rw [repr_unroll, h]

/-- `UF.repr_some` -/
theorem repr_some (uf : UF) {a a' : Positive} (h : uf.m.get a = some a') :
    uf.repr a = uf.repr a' := by
  rw [repr_unroll, h]

/-- `UF.repr_res_none` -/
theorem repr_res_none (uf : UF) (a : Positive) : uf.m.get (uf.repr a) = none := by
  induction a using uf.mwf.induction with
  | h x ih =>
    rw [repr_unroll]
    cases hx : uf.m.get x with
    | none => exact hx
    | some y => exact ih y hx

/-- `UF.repr_canonical` -/
theorem repr_canonical (uf : UF) (a : Positive) : uf.repr (uf.repr a) = uf.repr a :=
  repr_none uf (repr_res_none uf a)

/-- `UF.repr_some_diff` -/
theorem repr_some_diff (uf : UF) {a a' : Positive} (h : uf.m.get a = some a') :
    a ≠ uf.repr a' := by
  intro he
  have h1 : uf.repr a = a := by rw [repr_some uf h]; exact he.symm
  have h2 := repr_res_none uf a
  rw [h1, h] at h2
  cases h2

/-- `UF.sameclass` -/
def Sameclass (uf : UF) (a b : Positive) : Prop := uf.repr a = uf.repr b

theorem sameclass_refl (uf : UF) (a : Positive) : uf.Sameclass a a := rfl
theorem sameclass_sym {uf : UF} {a b : Positive} (h : uf.Sameclass a b) : uf.Sameclass b a :=
  h.symm
theorem sameclass_trans {uf : UF} {a b c : Positive} (h1 : uf.Sameclass a b)
    (h2 : uf.Sameclass b c) : uf.Sameclass a c := h1.trans h2
theorem sameclass_repr (uf : UF) (a : Positive) : uf.Sameclass a (uf.repr a) :=
  (repr_canonical uf a).symm

/-- `UF.wf_empty` -/
theorem wf_empty : WellFounded (Order (PTree.empty : PTree Positive)) :=
  ⟨fun _ => ⟨_, fun b h => by simp [Order] at h⟩⟩

/-- `UF.empty` -/
def empty : UF := ⟨PTree.empty, wf_empty⟩

/-- `UF.repr_empty` -/
theorem repr_empty (a : Positive) : empty.repr a = a := repr_none _ (by simp [empty])

/-- `UF.sameclass_empty` -/
theorem sameclass_empty {a b : Positive} (h : empty.Sameclass a b) : a = b := by
  simpa [Sameclass, repr_empty] using h


/-- `UF.identify_order` -/
theorem identify_order' (uf : UF) {a b : Positive} (ha : uf.m.get a = none) (x y : Positive) :
    Order (uf.m.set a b) y x ↔ Order uf.m y x ∨ (x = a ∧ y = b) := by
  simp only [Order, PTree.gsspec]
  by_cases hx : x = a
  · subst hx
    simp only [if_true, true_and, ha]
    constructor
    · intro h; cases h; exact .inr rfl
    · rintro (h | h)
      · cases h
      · rw [h]
  · simp [hx]

theorem identify_Acc_b (uf : UF) {a b : Positive} (ha : uf.m.get a = none) (x : Positive)
    (hacc : Acc (Order uf.m) x) (hx : uf.repr x ≠ a) : Acc (Order (uf.m.set a b)) x := by
  induction hacc with
  | intro x _ ih =>
    constructor
    intro y hy
    rcases (identify_order' uf ha x y).mp hy with h | ⟨rfl, rfl⟩
    · exact ih y h (by rw [← repr_some uf h]; exact hx)
    · exact absurd (repr_none uf ha) hx

theorem identify_Acc (uf : UF) {a b : Positive} (ha : uf.m.get a = none)
    (hb : uf.repr b ≠ a) (x : Positive) (hacc : Acc (Order uf.m) x) :
    Acc (Order (uf.m.set a b)) x := by
  induction hacc with
  | intro x _ ih =>
    constructor
    intro y hy
    rcases (identify_order' uf ha x y).mp hy with h | ⟨rfl, rfl⟩
    · exact ih y h
    · exact identify_Acc_b uf ha _ (uf.mwf.apply _) hb

/-- `UF.identify_wf` -/
theorem identify_wf (uf : UF) {a b : Positive} (ha : uf.m.get a = none)
    (hb : uf.repr b ≠ a) : WellFounded (Order (uf.m.set a b)) :=
  ⟨fun x => identify_Acc uf ha hb x (uf.mwf.apply x)⟩

/-- `UF.identify` -/
def identify (uf : UF) (a b : Positive) (ha : uf.m.get a = none) (hb : uf.repr b ≠ a) : UF :=
  ⟨uf.m.set a b, identify_wf uf ha hb⟩

/-- `UF.repr_identify_1` -/
theorem repr_identify_1 (uf : UF) {a b : Positive} (ha : uf.m.get a = none)
    (hb : uf.repr b ≠ a) (x : Positive) (hx : uf.repr x ≠ a) :
    (identify uf a b ha hb).repr x = uf.repr x := by
  induction x using uf.mwf.induction with
  | h x ih =>
    have hxa : x ≠ a := by
      intro h; subst h; exact hx (repr_none uf ha)
    cases hgx : uf.m.get x with
    | some a' =>
      have hx' : uf.repr a' ≠ a := by rw [← repr_some uf hgx]; exact hx
      rw [repr_some uf hgx, ← ih a' hgx hx']
      apply repr_some
      simp [identify, PTree.gsspec, hxa, hgx]
    | none =>
      rw [repr_none uf hgx]
      apply repr_none
      simp [identify, PTree.gsspec, hxa, hgx]

/-- `UF.repr_identify_2` -/
theorem repr_identify_2 (uf : UF) {a b : Positive} (ha : uf.m.get a = none)
    (hb : uf.repr b ≠ a) (x : Positive) (hx : uf.repr x = a) :
    (identify uf a b ha hb).repr x = uf.repr b := by
  induction x using uf.mwf.induction with
  | h x ih =>
    cases hgx : uf.m.get x with
    | some a' =>
      have hx' : uf.repr a' = a := by rw [← repr_some uf hgx]; exact hx
      have hxa : x ≠ a := fun h => by subst h; rw [ha] at hgx; cases hgx
      rw [← ih a' hgx hx']
      apply repr_some
      simp [identify, PTree.gsspec, hxa, hgx]
    | none =>
      rw [repr_none uf hgx] at hx
      subst hx
      rw [repr_unroll]
      simp only [identify, PTree.gss]
      exact repr_identify_1 uf ha hb b hb

/-- `UF.union_not_same_class` -/
theorem union_not_same_class (uf : UF) {a b : Positive} (h : uf.repr a ≠ uf.repr b) :
    uf.repr (uf.repr b) ≠ uf.repr a := by
  rw [repr_canonical]; exact fun e => h e.symm

/-- `UF.union` -/
def union (uf : UF) (a b : Positive) : UF :=
  if h : uf.repr a = uf.repr b then uf
  else identify uf (uf.repr a) (uf.repr b) (repr_res_none uf a) (union_not_same_class uf h)

/-- `UF.repr_union_1` -/
theorem repr_union_1 (uf : UF) (a b x : Positive) (h : uf.repr x ≠ uf.repr a) :
    (uf.union a b).repr x = uf.repr x := by
  unfold union
  split
  · rfl
  · exact repr_identify_1 _ _ _ _ h

/-- `UF.repr_union_2` -/
theorem repr_union_2 (uf : UF) (a b x : Positive) (h : uf.repr x = uf.repr a) :
    (uf.union a b).repr x = uf.repr b := by
  unfold union
  split
  · next he => rw [h, he]
  · exact (repr_identify_2 _ _ _ _ h).trans (repr_canonical uf b)

/-- `UF.repr_union_3` -/
theorem repr_union_3 (uf : UF) (a b : Positive) : (uf.union a b).repr b = uf.repr b := by
  by_cases h : uf.repr b = uf.repr a
  · exact repr_union_2 uf a b b h
  · exact repr_union_1 uf a b b h

/-- `UF.sameclass_union_1` -/
theorem sameclass_union_1 (uf : UF) (a b : Positive) : (uf.union a b).Sameclass a b := by
  unfold Sameclass
  rw [repr_union_2 uf a b a rfl, repr_union_3]

/-- `UF.sameclass_union_2` -/
theorem sameclass_union_2 (uf : UF) (a b x y : Positive) (h : uf.Sameclass x y) :
    (uf.union a b).Sameclass x y := by
  unfold Sameclass at *
  by_cases hx : uf.repr x = uf.repr a
  · rw [repr_union_2 uf a b x hx, repr_union_2 uf a b y (h ▸ hx)]
  · rw [repr_union_1 uf a b x hx, repr_union_1 uf a b y (h ▸ hx), h]

/-- `UF.sameclass_union_3` -/
theorem sameclass_union_3 (uf : UF) (a b x y : Positive) (h : (uf.union a b).Sameclass x y) :
    uf.Sameclass x y ∨ (uf.Sameclass x a ∧ uf.Sameclass y b) ∨
      (uf.Sameclass x b ∧ uf.Sameclass y a) := by
  unfold Sameclass at *
  by_cases hx : uf.repr x = uf.repr a <;> by_cases hy : uf.repr y = uf.repr a
  · exact .inl (hx.trans hy.symm)
  · rw [repr_union_2 uf a b x hx, repr_union_1 uf a b y hy] at h
    exact .inr (.inl ⟨hx, h.symm⟩)
  · rw [repr_union_1 uf a b x hx, repr_union_2 uf a b y hy] at h
    exact .inr (.inr ⟨h, hy⟩)
  · rw [repr_union_1 uf a b x hx, repr_union_1 uf a b y hy] at h
    exact .inl h

/-- `UF.merge` -/
def merge (uf : UF) (a b : Positive) : UF :=
  if h : uf.repr a = uf.repr b then uf
  else identify uf (uf.repr a) b (repr_res_none uf a) (fun e => h e.symm)

/-- `UF.repr_merge` -/
theorem repr_merge (uf : UF) (a b x : Positive) : (uf.merge a b).repr x = (uf.union a b).repr x := by
  by_cases h : uf.repr a = uf.repr b
  · simp [merge, union, h]
  · by_cases hx : uf.repr x = uf.repr a
    · rw [repr_union_2 uf a b x hx]
      simp only [merge, h, dite_false]
      exact repr_identify_2 _ _ _ _ hx
    · rw [repr_union_1 uf a b x hx]
      simp only [merge, h, dite_false]
      exact repr_identify_1 _ _ _ _ hx

/-- `UF.sameclass_merge` -/
theorem sameclass_merge (uf : UF) (a b x y : Positive) (h : (uf.merge a b).Sameclass x y) :
    uf.Sameclass x y ∨ (uf.Sameclass x a ∧ uf.Sameclass y b) ∨
      (uf.Sameclass x b ∧ uf.Sameclass y a) := by
  apply sameclass_union_3
  unfold Sameclass at *
  rwa [← repr_merge, ← repr_merge]

end UF
end UnionFind
end CC
