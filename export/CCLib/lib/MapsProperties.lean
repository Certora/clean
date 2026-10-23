/-
  `PTree_Properties` of `lib/Maps.v`: `cardinal`, `of_list` and its
  properties, `for_all`, `exists_`, `beq`, and the fact that trees with
  related contents list their bindings in the same order
  (`elements_canonical_order'`, `elements_rel`).

  These used to be scattered over the modules that first needed them
  (`Postorder`, `Inlining`, `ASTTheory`, `LinkingTheory`, `CshmgenproofEnv`),
  partly in duplicate; they are gathered here.  Rocq's `option_rel` is core's
  `Option.Rel`.  The `PTree` representation is not canonical (see
  `CCLib.lib.Maps`), so `beq_correct` is stated on `get`, like Rocq's.
-/
import CCLib.lib.MapsTheory

namespace CC

/-! ## `Coqlib.list_forall2` -/

/-- `Coqlib.list_forall2`.  (Rocq's `option_rel` is core's `Option.Rel`.) -/
inductive ListForall2 {A B : Type} (R : A → B → Prop) : List A → List B → Prop where
  | nil : ListForall2 R [] []
  | cons {a b l1 l2} : R a b → ListForall2 R l1 l2 → ListForall2 R (a :: l1) (b :: l2)

namespace PTree
variable {A B : Type}

/-- Number of bound keys of a tree (`PTree_Properties.cardinal`, computed
    structurally). -/
def cardinal : PTree A → Nat
  | .Leaf => 0
  | .Node l o r => cardinal l + (if o.isSome then 1 else 0) + cardinal r

theorem cardinal_remove_lt : ∀ (i : Positive) (m : PTree A) {v : A}, get i m = some v →
    cardinal (remove i m) < cardinal m
  | _, .Leaf, _, h => by simp at h
  | .xH, .Node l o r, _, h => by
    simp only [get] at h; subst h; simp [remove, cardinal]
  | .xO ii, .Node l o r, _, h => by
    simp only [get] at h
    have := cardinal_remove_lt ii l h
    simp only [remove, cardinal]; omega
  | .xI ii, .Node l o r, _, h => by
    simp only [get] at h
    have := cardinal_remove_lt ii r h
    simp only [remove, cardinal]; omega

/-- `PTree_Properties.of_list`: the tree built by inserting the pairs of `l`
    in order (later bindings win). -/
def ofList (l : List (Positive × A)) : PTree A :=
  l.foldl (fun m kv => m.set kv.1 kv.2) empty

theorem get_foldl_set_not_mem (l : List (Positive × A)) (m : PTree A) (k : Positive)
    (h : k ∉ l.map Prod.fst) :
    get k (l.foldl (fun m kv => m.set kv.1 kv.2) m) = get k m := by
  induction l generalizing m with
  | nil => rfl
  | cons kv l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [ih _ h.2, gso _ _ _ _ (Ne.symm h.1)]

theorem get_foldl_set_mem (l : List (Positive × A)) (m : PTree A) (k : Positive) (g : A)
    (h : get k (l.foldl (fun m kv => m.set kv.1 kv.2) m) = some g) :
    (k, g) ∈ l ∨ get k m = some g := by
  induction l generalizing m with
  | nil => exact .inr h
  | cons kv l ih =>
    rcases ih _ h with h1 | h1
    · exact .inl (List.mem_cons_of_mem _ h1)
    · by_cases hk : kv.1 = k
      · subst hk; rw [gss] at h1; cases h1; exact .inl (by simp)
      · rw [gso _ _ _ _ hk] at h1; exact .inr h1

/-- `PTree_Properties.in_of_list` -/
theorem in_ofList {l : List (Positive × A)} {k : Positive} {g : A}
    (h : get k (ofList l) = some g) : (k, g) ∈ l := by
  rcases get_foldl_set_mem l empty k g h with h | h
  · exact h
  · simp at h

/-- `PTree_Properties.of_list_dom` -/
theorem ofList_dom {l : List (Positive × A)} {k : Positive} (h : k ∈ l.map Prod.fst) :
    ∃ g, get k (ofList l) = some g := by
  unfold ofList
  generalize (empty : PTree A) = m
  induction l generalizing m with
  | nil => simp at h
  | cons kv l ih =>
    simp only [List.foldl_cons]
    by_cases hk : k ∈ l.map Prod.fst
    · exact ih hk _
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨kv.2, by rw [get_foldl_set_not_mem _ _ _ hk, gss]⟩
      · exact absurd h hk

/-- `PTree_Properties.of_list_unique` -/
theorem ofList_unique {l1 l2 : List (Positive × A)} {k : Positive} {g : A}
    (h : k ∉ l2.map Prod.fst) : get k (ofList (l1 ++ (k, g) :: l2)) = some g := by
  unfold ofList
  rw [List.foldl_append, List.foldl_cons, get_foldl_set_not_mem _ _ _ h, gss]

/-- `PTree_Properties.of_list_norepet` -/
theorem ofList_norepet {l : List (Positive × A)} {k : Positive} {g : A}
    (hnd : (l.map Prod.fst).Nodup) (h : (k, g) ∈ l) : get k (ofList l) = some g := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem h
  apply ofList_unique
  simp only [List.map_append, List.map_cons] at hnd
  have := (List.nodup_append.mp hnd).2.1
  exact (List.nodup_cons.mp this).1

/-- `PTree_Properties.for_all` -/
def forAll (m : PTree A) (f : Positive → A → Bool) : Bool :=
  (elements m).all (fun p => f p.1 p.2)

/-- `PTree_Properties.for_all_correct` -/
theorem forAll_correct (m : PTree A) (f : Positive → A → Bool) :
    forAll m f = true ↔ ∀ x a, get x m = some a → f x a = true := by
  unfold forAll
  rw [List.all_eq_true]
  constructor
  · intro h x a hx
    exact h (x, a) (elements_correct m x a hx)
  · intro h ⟨x, a⟩ hx
    exact h x a (elements_complete m x a hx)

theorem get_ofList_none {l : List (Positive × A)} {k : Positive} (h : k ∉ l.map Prod.fst) :
    get k (ofList l) = none := by
  unfold ofList; rw [get_foldl_set_not_mem _ _ _ h]; exact gempty k

/-- `PTree_Properties.of_list_elements` -/
theorem ofList_elements (m : PTree A) (k : Positive) : get k (ofList (elements m)) = get k m := by
  cases hm : get k m with
  | some v => exact ofList_norepet (elements_keys_norepet m) (elements_correct m k v hm)
  | none =>
    cases hg : get k (ofList (elements m)) with
    | none => rfl
    | some g =>
      have := elements_complete m k g (in_ofList hg)
      rw [hm] at this; cases this

/-- `PTree_Properties.of_list_related` -/
theorem ofList_related {R : A → B → Prop} {l1 : List (Positive × A)} {l2 : List (Positive × B)}
    (h : ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) l1 l2) (k : Positive) :
    Option.Rel R (get k (ofList l1)) (get k (ofList l2)) := by
  unfold ofList
  suffices ∀ (m1 : PTree A) (m2 : PTree B), (∀ k, Option.Rel R (get k m1) (get k m2)) →
      ∀ k, Option.Rel R (get k (l1.foldl (fun m kv => m.set kv.1 kv.2) m1))
        (get k (l2.foldl (fun m kv => m.set kv.1 kv.2) m2)) by
    apply this
    intro k; simp only [gempty]; exact .none
  induction h with
  | nil => intro m1 m2 hm; exact hm
  | cons hab _ ih =>
    intro m1 m2 hm
    apply ih
    intro k
    obtain ⟨he, hr⟩ := hab
    simp only
    rw [he, gsspec, gsspec]
    split
    · exact .some hr
    · exact hm k

theorem elemsAux_empty (m : PTree A) (h : ∀ i, get i m = none) (rp : List Bool)
    (acc : List (Positive × A)) : elemsAux m rp acc = acc := by
  induction m generalizing rp acc with
  | Leaf => rfl
  | Node l o r ihl ihr =>
    have ho : o = none := h .xH
    subst ho
    simp only [elemsAux]
    rw [ihr (fun i => h (.xI i)), ihl (fun i => h (.xO i))]

theorem optionRel_none_left {R : A → B → Prop} {o : Option B} (h : Option.Rel R none o) :
    o = none := by cases h; rfl

theorem optionRel_none_right {R : A → B → Prop} {o : Option A} (h : Option.Rel R o none) :
    o = none := by cases h; rfl

theorem elemsAux_related {R : A → B → Prop} (m1 : PTree A) (m2 : PTree B)
    (h : ∀ i, Option.Rel R (get i m1) (get i m2)) (rp : List Bool)
    {acc1 : List (Positive × A)} {acc2 : List (Positive × B)}
    (hacc : ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) acc1 acc2) :
    ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) (elemsAux m1 rp acc1) (elemsAux m2 rp acc2) := by
  induction m1 generalizing m2 rp acc1 acc2 with
  | Leaf =>
    rw [elemsAux_empty m2 (fun i => optionRel_none_left (by simpa using h i))]
    exact hacc
  | Node l1 o1 r1 ihl ihr =>
    cases m2 with
    | Leaf =>
      rw [elemsAux_empty (.Node l1 o1 r1) (fun i => optionRel_none_right (by simpa using h i))]
      exact hacc
    | Node l2 o2 r2 =>
      simp only [elemsAux]
      apply ihl l2 (fun i => h (.xO i))
      have hr := ihr r2 (fun i => h (.xI i)) (true :: rp) hacc
      have ho : Option.Rel R o1 o2 := h .xH
      cases ho with
      | none => exact hr
      | some hab => exact .cons ⟨rfl, hab⟩ hr

/-- `PTree.elements_canonical_order'` (the port's trees are not canonical, but
    two trees with related contents still list their bindings in the same
    order). -/
theorem elements_canonical_order' {R : A → B → Prop} (m1 : PTree A) (m2 : PTree B)
    (h : ∀ i, Option.Rel R (get i m1) (get i m2)) :
    ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) (elements m1) (elements m2) :=
  elemsAux_related m1 m2 h [] .nil

/-- Two trees whose bindings are related by `R`, key by key, list them in the
    same order, seen through any pair of maps that agree on related bindings. -/
theorem elements_rel {C : Type} {R : A → B → Prop} (g1 : Positive × A → C) (g2 : Positive × B → C)
    (hg : ∀ k x y, R x y → g1 (k, x) = g2 (k, y)) (t1 : PTree A) (t2 : PTree B)
    (h12 : ∀ i x, get i t1 = some x → ∃ y, get i t2 = some y ∧ R x y)
    (h21 : ∀ i y, get i t2 = some y → ∃ x, get i t1 = some x ∧ R x y) :
    (elements t1).map g1 = (elements t2).map g2 := by
  have hrel : ∀ i, Option.Rel R (get i t1) (get i t2) := by
    intro i
    cases h1 : get i t1 with
    | none =>
      cases h2 : get i t2 with
      | none => exact .none
      | some y => obtain ⟨x, hx, _⟩ := h21 i y h2; rw [h1] at hx; cases hx
    | some x =>
      obtain ⟨y, hy, hxy⟩ := h12 i x h1
      rw [hy]; exact .some hxy
  have key : ∀ {l1 : List (Positive × A)} {l2 : List (Positive × B)},
      ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) l1 l2 → l1.map g1 = l2.map g2 := by
    intro l1 l2 h
    induction h with
    | nil => rfl
    | @cons a b _ _ hab _ ih =>
      obtain ⟨k, x⟩ := a; obtain ⟨k', y⟩ := b
      obtain ⟨rfl, hxy⟩ := hab
      simp only [List.map_cons, ih, hg _ _ _ hxy]
  exact key (elements_canonical_order' t1 t2 hrel)

/-- `PTree_Properties.exists_` -/
def exists_ (m : PTree A) (f : Positive → A → Bool) : Bool :=
  (elements m).any (fun p => f p.1 p.2)

/-- `PTree_Properties.exists_correct` -/
theorem exists_correct (m : PTree A) (f : Positive → A → Bool) :
    exists_ m f = true ↔ ∃ x a, get x m = some a ∧ f x a = true := by
  unfold exists_
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨x, a⟩, hx, hf⟩
    exact ⟨x, a, elements_complete m x a hx, hf⟩
  · rintro ⟨x, a, hx, hf⟩
    exact ⟨(x, a), elements_correct m x a hx, hf⟩

/-- `PTree_Properties.for_all_false` -/
theorem forAll_false (m : PTree A) (f : Positive → A → Bool) :
    forAll m f = false ↔ ∃ x a, get x m = some a ∧ f x a = false := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    have : forAll m f = true := (forAll_correct m f).mpr fun x a hx => by
      cases hf : f x a with
      | true => rfl
      | false => exact absurd ⟨x, a, hx, hf⟩ hne
    rw [h] at this; cases this
  · rintro ⟨x, a, hx, hf⟩
    cases h : forAll m f with
    | false => rfl
    | true => rw [(forAll_correct m f).mp h x a hx] at hf; cases hf

/-- `PTree_Properties.exists_false` -/
theorem exists_false (m : PTree A) (f : Positive → A → Bool) :
    exists_ m f = false ↔ ∀ x a, get x m = some a → f x a = false := by
  constructor
  · intro h x a hx
    cases hf : f x a with
    | false => rfl
    | true => rw [(exists_correct m f).mpr ⟨x, a, hx, hf⟩] at h; cases h
  · intro h
    cases he : exists_ m f with
    | false => rfl
    | true =>
      obtain ⟨x, a, hx, hf⟩ := (exists_correct m f).mp he
      rw [h x a hx] at hf; cases hf

/-- `PTree.beq`: equality of contents, comparing bound values with `f`. -/
def beq (f : A → B → Bool) (m1 : PTree A) (m2 : PTree B) : Bool :=
  forAll m1 (fun k a => match get k m2 with | some b => f a b | none => false)
  && forAll m2 (fun k _ => (get k m1).isSome)

/-- `PTree.beq_correct` -/
theorem beq_correct (f : A → B → Bool) (m1 : PTree A) (m2 : PTree B) :
    beq f m1 m2 = true ↔
      ∀ x, match get x m1, get x m2 with
        | none, none => True
        | some a, some b => f a b = true
        | _, _ => False := by
  unfold beq
  rw [Bool.and_eq_true, forAll_correct, forAll_correct]
  constructor
  · rintro ⟨h1, h2⟩ x
    cases hx1 : get x m1 with
    | none =>
      cases hx2 : get x m2 with
      | none => trivial
      | some b => have := h2 x b hx2; rw [hx1] at this; cases this
    | some a =>
      have := h1 x a hx1
      cases hx2 : get x m2 with
      | none => rw [hx2] at this; cases this
      | some b => rw [hx2] at this; exact this
  · intro h
    refine ⟨fun x a hx => ?_, fun x b hx => ?_⟩
    · have := h x; rw [hx] at this
      cases hx2 : get x m2 with
      | none => rw [hx2] at this; exact this.elim
      | some b => rw [hx2] at this; simpa using this
    · have := h x; rw [hx] at this
      cases hx1 : get x m1 with
      | none => rw [hx1] at this; exact this.elim
      | some a => rfl

end PTree
end CC
