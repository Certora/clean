/-
  More of `lib/Maps.v`: the `PTree` theorems about `remove`, `map1`, `map`,
  `filter1`, `combine`, `elements` and `fold`, plus `PMap`/`ZMap` additions.

  The `PTree` representation is the non-canonical one described in
  `Maps.lean`, so extensionality (`PTree.extensionality`, `beq_correct`) is
  still not available; everything here is about `get` and `elements`, which
  hold for any representation.
-/
import CCLib.lib.MapsLemmas

namespace CC
namespace PTree
variable {A B C : Type}

/-! ## `get` / `set` / `remove` -/

/-- `PTree.gsspec` -/
theorem gsspec (i j : Positive) (v : A) (m : PTree A) :
    get j (set i v m) = if j = i then some v else get j m := by
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg h, gso i j v m (Ne.symm h)]

/-- `PTree.gsident`: re-writing the current value changes no binding. -/
theorem gsident (i j : Positive) (v : A) (m : PTree A) (h : get i m = some v) :
    get j (set i v m) = get j m := by
  rw [gsspec]; split
  · subst j; exact h.symm
  · rfl

/-- `PTree.grs` -/
@[simp] theorem grs (i : Positive) (m : PTree A) : get i (remove i m) = none := by
  induction i generalizing m with
  | xH => cases m <;> rfl
  | xO ii ih => cases m <;> simp [get, remove, ih]
  | xI ii ih => cases m <;> simp [get, remove, ih]

/-- `PTree.gro` -/
theorem gro (i j : Positive) (m : PTree A) (h : i ≠ j) : get j (remove i m) = get j m := by
  induction i generalizing j m with
  | xH =>
    cases j with
    | xH => exact absurd rfl h
    | xO jj => cases m <;> simp [get, remove]
    | xI jj => cases m <;> simp [get, remove]
  | xO ii ih =>
    cases j with
    | xH => cases m <;> simp [get, remove]
    | xO jj =>
      have hne : ii ≠ jj := fun hh => h (by rw [hh])
      cases m <;> simp [get, remove, ih jj _ hne]
    | xI jj => cases m <;> simp [get, remove]
  | xI ii ih =>
    cases j with
    | xH => cases m <;> simp [get, remove]
    | xO jj => cases m <;> simp [get, remove]
    | xI jj =>
      have hne : ii ≠ jj := fun hh => h (by rw [hh])
      cases m <;> simp [get, remove, ih jj _ hne]

/-- `PTree.grspec` -/
theorem grspec (i j : Positive) (m : PTree A) :
    get j (remove i m) = if j = i then none else get j m := by
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg h, gro i j m (Ne.symm h)]

/-! ## Maps over the values -/

/-- `PTree.gmap1` -/
@[simp] theorem gmap1 (f : A → B) (i : Positive) (m : PTree A) :
    get i (map1 f m) = (get i m).map f := by
  induction m generalizing i with
  | Leaf => simp [map1]
  | Node l o r ihl ihr =>
    cases i with
    | xH => rfl
    | xO ii => exact ihl ii
    | xI ii => exact ihr ii

/-- `PTree.map` — map a function over all bindings, with access to the key. -/
def map (f : Positive → A → B) (m : PTree A) : PTree B := go id m
where
  go (k : Positive → Positive) : PTree A → PTree B
    | Leaf => Leaf
    | Node l o r => Node (go (fun p => k (.xO p)) l) (o.map (f (k .xH))) (go (fun p => k (.xI p)) r)

theorem gmap_go (f : Positive → A → B) (k : Positive → Positive) (i : Positive) (m : PTree A) :
    get i (map.go f k m) = (get i m).map (f (k i)) := by
  induction m generalizing k i with
  | Leaf => simp [map.go]
  | Node l o r ihl ihr =>
    cases i with
    | xH => rfl
    | xO ii => exact ihl _ ii
    | xI ii => exact ihr _ ii

/-- `PTree.gmap` -/
@[simp] theorem gmap (f : Positive → A → B) (i : Positive) (m : PTree A) :
    get i (map f m) = (get i m).map (f i) :=
  gmap_go f id i m

/-- `PTree.filter1` — keep the bindings whose value satisfies `p`. -/
def filter1 (p : A → Bool) : PTree A → PTree A
  | Leaf => Leaf
  | Node l o r =>
    Node (filter1 p l) (match o with | some a => if p a then some a else none | none => none)
      (filter1 p r)

/-- `PTree.gfilter1` -/
theorem gfilter1 (p : A → Bool) (i : Positive) (m : PTree A) :
    get i (filter1 p m) = match get i m with
      | some a => if p a then some a else none
      | none => none := by
  induction m generalizing i with
  | Leaf => simp [filter1]
  | Node l o r ihl ihr =>
    cases i with
    | xH => rfl
    | xO ii => exact ihl ii
    | xI ii => exact ihr ii

/-- `combine f Leaf`: the right-hand tree mapped through `f none`. -/
def combineLeafL (f : Option A → Option B → Option C) : PTree B → PTree C
  | Leaf => Leaf
  | Node l2 o2 r2 => Node (combineLeafL f l2) (f none o2) (combineLeafL f r2)

/-- `combine f · Leaf`: the left-hand tree mapped through `f · none`. -/
def combineLeafR (f : Option A → Option B → Option C) : PTree A → PTree C
  | Leaf => Leaf
  | Node l1 o1 r1 => Node (combineLeafR f l1) (f o1 none) (combineLeafR f r1)

/-- `PTree.combine` — pointwise combination of two trees with
    `f none none = none`.  Structural on the first tree (with the
    one-sided cases split out), so that it reduces in the kernel. -/
def combine (f : Option A → Option B → Option C) : PTree A → PTree B → PTree C
  | Leaf, m2 => combineLeafL f m2
  | Node l1 o1 r1, Leaf => combineLeafR f (Node l1 o1 r1)
  | Node l1 o1 r1, Node l2 o2 r2 =>
    Node (combine f l1 l2) (f o1 o2) (combine f r1 r2)

/-- `PTree.gcombine` -/
theorem gcombine (f : Option A → Option B → Option C) (hf : f none none = none)
    (m1 : PTree A) (m2 : PTree B) (i : Positive) :
    get i (combine f m1 m2) = f (get i m1) (get i m2) := by
  have hL : ∀ (m2 : PTree B) i, get i (combineLeafL f m2) = f none (get i m2) := by
    intro m2
    induction m2 with
    | Leaf => intro i; simp [combineLeafL, hf]
    | Node l2 o2 r2 ihl ihr =>
      intro i
      cases i with
      | xH => simp only [combineLeafL, get]
      | xO ii => simp only [combineLeafL, get]; exact ihl ii
      | xI ii => simp only [combineLeafL, get]; exact ihr ii
  have hR : ∀ (m1 : PTree A) i, get i (combineLeafR f m1) = f (get i m1) none := by
    intro m1
    induction m1 with
    | Leaf => intro i; simp [combineLeafR, hf]
    | Node l1 o1 r1 ihl ihr =>
      intro i
      cases i with
      | xH => simp only [combineLeafR, get]
      | xO ii => simp only [combineLeafR, get]; exact ihl ii
      | xI ii => simp only [combineLeafR, get]; exact ihr ii
  induction m1 generalizing m2 i with
  | Leaf => simp only [combine]; rw [hL]; simp
  | Node l1 o1 r1 ihl ihr =>
    cases m2 with
    | Leaf => simp only [combine]; rw [hR]; simp
    | Node l2 o2 r2 =>
      cases i with
      | xH => simp only [combine, get]
      | xO ii => simp only [combine, get]; exact ihl l2 ii
      | xI ii => simp only [combine, get]; exact ihr r2 ii

/-! ## `elements` -/

/-- The key reached from `j` after the (deepest-first) path `rp`. -/
def prependPath (rp : List Bool) (j : Positive) : Positive :=
  rp.foldl (fun acc b => if b then Positive.xI acc else Positive.xO acc) j

theorem keyOfRevPath_eq (rp : List Bool) : keyOfRevPath rp = prependPath rp .xH := rfl

theorem prependPath_cons (b : Bool) (rp : List Bool) (j : Positive) :
    prependPath (b :: rp) j = prependPath rp (if b then .xI j else .xO j) := rfl

theorem prependPath_inj (rp : List Bool) {i j : Positive}
    (h : prependPath rp i = prependPath rp j) : i = j := by
  induction rp generalizing i j with
  | nil => exact h
  | cons b rp ih =>
    rw [prependPath_cons, prependPath_cons] at h
    have := ih h
    cases b <;> simp at this <;> exact this

theorem mem_elemsAux (m : PTree A) (rp : List Bool) (acc : List (Positive × A))
    (k : Positive) (v : A) :
    (k, v) ∈ elemsAux m rp acc ↔ (∃ j, get j m = some v ∧ k = prependPath rp j) ∨ (k, v) ∈ acc := by
  induction m generalizing rp acc with
  | Leaf => simp [elemsAux]
  | Node l o r ihl ihr =>
    simp only [elemsAux]
    rw [ihl]
    constructor
    · rintro (⟨j, hj, rfl⟩ | h)
      · exact Or.inl ⟨.xO j, hj, rfl⟩
      · cases o with
        | none =>
          rw [ihr] at h
          rcases h with ⟨j, hj, rfl⟩ | h
          · exact Or.inl ⟨.xI j, hj, rfl⟩
          · exact Or.inr h
        | some a =>
          simp only [List.mem_cons, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩ | h
          · exact Or.inl ⟨.xH, rfl, rfl⟩
          · rw [ihr] at h
            rcases h with ⟨j, hj, rfl⟩ | h
            · exact Or.inl ⟨.xI j, hj, rfl⟩
            · exact Or.inr h
    · rintro (⟨j, hj, rfl⟩ | h)
      · cases j with
        | xH =>
          right
          cases o with
          | none => simp [get] at hj
          | some a =>
            simp only [get, Option.some.injEq] at hj
            subst hj
            exact List.mem_cons_self ..
        | xO jj => exact Or.inl ⟨jj, hj, rfl⟩
        | xI jj =>
          right
          have : (prependPath rp (.xI jj), v) ∈ elemsAux r (true :: rp) acc :=
            (ihr _ _).mpr (Or.inl ⟨jj, hj, rfl⟩)
          cases o with
          | none => exact this
          | some a => exact List.mem_cons_of_mem _ this
      · right
        have : (k, v) ∈ elemsAux r (true :: rp) acc := (ihr _ _).mpr (Or.inr h)
        cases o with
        | none => exact this
        | some a => exact List.mem_cons_of_mem _ this

/-- `PTree.elements_correct` -/
theorem elements_correct (m : PTree A) (i : Positive) (v : A) (h : get i m = some v) :
    (i, v) ∈ elements m :=
  (mem_elemsAux m [] [] i v).mpr (Or.inl ⟨i, h, rfl⟩)

/-- `PTree.elements_complete` -/
theorem elements_complete (m : PTree A) (i : Positive) (v : A) (h : (i, v) ∈ elements m) :
    get i m = some v := by
  rcases (mem_elemsAux m [] [] i v).mp h with ⟨j, hj, rfl⟩ | h
  · exact hj
  · simp at h

theorem mem_elements (m : PTree A) (i : Positive) (v : A) :
    (i, v) ∈ elements m ↔ get i m = some v :=
  ⟨elements_complete m i v, elements_correct m i v⟩

theorem nodup_keys_elemsAux (m : PTree A) (rp : List Bool) (acc : List (Positive × A))
    (hacc : (acc.map Prod.fst).Nodup)
    (hdisj : ∀ j v, get j m = some v → ∀ p ∈ acc, p.1 ≠ prependPath rp j) :
    ((elemsAux m rp acc).map Prod.fst).Nodup := by
  induction m generalizing rp acc with
  | Leaf => simpa [elemsAux] using hacc
  | Node l o r ihl ihr =>
    simp only [elemsAux]
    have hr : ((elemsAux r (true :: rp) acc).map Prod.fst).Nodup :=
      ihr _ _ hacc (fun j v hj p hp => hdisj (.xI j) v hj p hp)
    -- keys of the right part: either from `r` (under `xI`) or from `acc`
    have hrkeys : ∀ p ∈ elemsAux r (true :: rp) acc,
        (∃ j, p.1 = prependPath rp (.xI j)) ∨ p ∈ acc := by
      intro ⟨k, v⟩ hp
      rcases (mem_elemsAux r (true :: rp) acc k v).mp hp with ⟨j, _, rfl⟩ | h
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr h
    apply ihl
    · cases o with
      | none => exact hr
      | some a =>
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hr⟩
        intro hmem
        obtain ⟨⟨k, v⟩, hp, hk⟩ := List.mem_map.mp hmem
        simp only at hk
        subst hk
        rcases hrkeys _ hp with ⟨j, hj⟩ | hacc'
        · have := prependPath_inj rp (hj.symm.trans (keyOfRevPath_eq rp))
          cases this
        · exact hdisj .xH a rfl _ hacc' rfl
    · intro j v hj p hp
      have hp' : p ∈ elemsAux r (true :: rp) acc ∨ (o.isSome ∧ p.1 = prependPath rp .xH) := by
        cases o with
        | none => exact Or.inl hp
        | some a =>
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Or.inr ⟨rfl, keyOfRevPath_eq rp⟩
          · exact Or.inl hp
      intro heq
      rw [prependPath_cons] at heq
      simp only [Bool.false_eq_true, ite_false] at heq
      rcases hp' with hp' | ⟨_, hk⟩
      · rcases hrkeys _ hp' with ⟨j', hj'⟩ | hacc'
        · have := prependPath_inj rp (hj'.symm.trans heq)
          cases this
        · exact hdisj (.xO j) v hj p hacc' heq
      · have := prependPath_inj rp (hk.symm.trans heq)
        cases this

/-- `PTree.elements_keys_norepet`: `elements` lists every key once. -/
theorem elements_keys_norepet (m : PTree A) : ((elements m).map Prod.fst).Nodup :=
  nodup_keys_elemsAux m [] [] List.nodup_nil (fun _ _ _ _ hp => by simp at hp)

/-! ## `fold` -/

/-- `PTree.fold` (defined by Rocq's `fold_spec`). -/
def fold (f : B → Positive → A → B) (m : PTree A) (v : B) : B :=
  (elements m).foldl (fun a p => f a p.1 p.2) v

/-- `PTree.fold1` (defined by Rocq's `fold1_spec`). -/
def fold1 (f : B → A → B) (m : PTree A) (v : B) : B :=
  (elements m).foldl (fun a p => f a p.2) v

theorem fold_spec (f : B → Positive → A → B) (m : PTree A) (v : B) :
    fold f m v = (elements m).foldl (fun a p => f a p.1 p.2) v := rfl

theorem fold1_spec (f : B → A → B) (m : PTree A) (v : B) :
    fold1 f m v = (elements m).foldl (fun a p => f a p.2) v := rfl

end PTree

namespace PMap
variable {A B : Type}

/-- `PMap.map` -/
def map (f : A → B) (m : PMap A) : PMap B := ⟨f m.dflt, PTree.map1 f m.tree⟩

/-- `PMap.gmap` -/
@[simp] theorem gmap (f : A → B) (i : Positive) (m : PMap A) : get i (map f m) = f (get i m) := by
  simp only [get, map, PTree.gmap1]
  cases PTree.get i m.tree <;> rfl

/-- `PMap.gsident` -/
theorem gsident (i j : Positive) (m : PMap A) : get j (set i (get i m) m) = get j m := by
  rw [gsspec]; split
  · subst j; rfl
  · rfl

end PMap

namespace ZMap
variable {A B : Type}

/-- `ZMap.gsspec` -/
theorem gsspec (i j : Int) (v : A) (m : ZMap A) :
    get j (set i v m) = if j = i then v else get j m := by
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg h, gso i j v m (Ne.symm h)]

/-- `ZMap.gsident` -/
theorem gsident (i j : Int) (m : ZMap A) : get j (set i (get i m) m) = get j m := by
  rw [gsspec]; split
  · subst j; rfl
  · rfl

end ZMap
end CC
