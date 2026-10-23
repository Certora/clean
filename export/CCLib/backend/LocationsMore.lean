/-
  The rest of `backend/Locations.v` (complementing `CCLib.backend.Locations`):

  * the list lemmas `Loc.disjoint_cons_left`/`disjoint_cons_right` and
    `Locmap.gss_typed`;
  * the total orders `OrderedTyp`, `OrderedSlot` and `OrderedLoc` (instances
    of `CC.OrderedType`, `CCLib.lib.Ordered`), and the connection between the
    order on locations and `Loc.diff`: `OrderedLoc.outside_interval_diff` and
    `OrderedLoc.diff_outside_interval`, with the bounds `diff_low_bound` /
    `diff_high_bound`.

  Differences from Rocq: `OrderedTyp`/`OrderedSlot` are `OrderedType.ofNatInj`
  of the Rocq indices (`OrderedLoc.typIndex`/`slotIndex`, as `Nat`s, which is
  what `OrderedIndexed` reduces to), so their `lt` is `<` on the indices;
  `OrderedLoc.lt` is stated with these indices directly.  The register
  allocator (`CCLib.backend.Allocation`) uses `OrderedLoc.compare` and the
  bounds from here.  `compare` returns an `Ordering` (built with
  `Ordering.then`) and `compare_spec` replaces Rocq's dependent `Compare`.
-/
import CCLib.backend.Locations
import CCLib.lib.Ordered
import CCLib.common.ValuesOps

namespace CC

namespace Loc

theorem disjoint_cons_left {a : Loc} {l1 l2 : List Loc} (h : disjoint (a :: l1) l2) :
    disjoint l1 l2 :=
  fun x1 h1 => h x1 (List.mem_cons_of_mem _ h1)

theorem disjoint_cons_right {a : Loc} {l1 l2 : List Loc} (h : disjoint l1 (a :: l2)) :
    disjoint l1 l2 :=
  fun x1 h1 x2 h2 => h x1 h1 x2 (List.mem_cons_of_mem _ h2)

end Loc

namespace Locmap

/-- `Locmap.gss_typed` -/
theorem gss_typed (l : Loc) (v : Val) (m : Locmap) (h : Val.HasType v l.type) :
    set l v m l = v := by
  rw [gss]
  cases l with
  | R r => rfl
  | S sl pos ty =>
    show Val.loadResult (Chunk.ofTyp ty) v = v
    cases v <;> cases ty <;>
      simp_all [Val.loadResult, Chunk.ofTyp, Val.HasType, Val.hasType, Loc.type, Archi.ptr64]

end Locmap

/-! ## Orders -/

namespace OrderedLoc

/-- `IndexedSlot.index` -/
def slotIndex : Slot → Nat
  | .Local => 1
  | .Incoming => 2
  | .Outgoing => 3

/-- `IndexedTyp.index` -/
def typIndex : ATyp → Nat
  | .Tany32 => 1
  | .Tint => 2
  | .Tsingle => 3
  | .Tany64 => 4
  | .Tfloat => 5
  | .Tlong => 6

theorem typIndex_inj (x y : ATyp) (h : typIndex x = typIndex y) : x = y := by
  cases x <;> cases y <;> first | rfl | (simp [typIndex] at h)

theorem slotIndex_inj (x y : Slot) (h : slotIndex x = slotIndex y) : x = y := by
  cases x <;> cases y <;> first | rfl | (simp [slotIndex] at h)

end OrderedLoc

/-- `OrderedTyp` -/
instance OrderedTyp : OrderedType ATyp :=
  OrderedType.ofNatInj OrderedLoc.typIndex OrderedLoc.typIndex_inj

/-- `OrderedSlot` -/
instance OrderedSlot : OrderedType Slot :=
  OrderedType.ofNatInj OrderedLoc.slotIndex OrderedLoc.slotIndex_inj

namespace OrderedLoc

/-- The register index, as a `Nat` (`IndexedMreg.index`). -/
abbrev ridx (r : Mreg) : Nat := (Mreg.index r).toNat

theorem ridx_inj {r1 r2 : Mreg} (h : ridx r1 = ridx r2) : r1 = r2 :=
  Mreg.index_inj _ _ (Positive.toNat_injective h)

/-- `OrderedLoc.lt`: registers first, by index; then stack slots,
    lexicographically by slot kind, offset and type. -/
def lt : Loc → Loc → Prop
  | .R r1, .R r2 => ridx r1 < ridx r2
  | .R _, .S _ _ _ => True
  | .S _ _ _, .R _ => False
  | .S sl1 ofs1 ty1, .S sl2 ofs2 ty2 =>
      slotIndex sl1 < slotIndex sl2 ∨ (sl1 = sl2 ∧ (ofs1 < ofs2 ∨ (ofs1 = ofs2 ∧ typIndex ty1 < typIndex ty2)))

theorem lt_trans (x y z : Loc) (h1 : lt x y) (h2 : lt y z) : lt x z := by
  cases x <;> cases y <;> cases z <;> simp only [lt] at h1 h2 ⊢ <;> try trivial
  · omega
  · rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact .inl (Nat.lt_trans h1 h2)
    · exact .inl h1
    · exact .inl h2
    · refine .inr ⟨rfl, ?_⟩
      rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
      · exact .inl (Int.lt_trans h1 h2)
      · exact .inl h1
      · exact .inl h2
      · exact .inr ⟨rfl, Nat.lt_trans h1 h2⟩

theorem lt_not_eq (x y : Loc) (h : lt x y) : x ≠ y := by
  rintro rfl
  cases x with
  | R r => exact Nat.lt_irrefl _ h
  | S sl ofs ty =>
    rcases h with h | ⟨_, h | ⟨_, h⟩⟩
    · exact Nat.lt_irrefl _ h
    · exact Int.lt_irrefl _ h
    · exact Nat.lt_irrefl _ h

/-- `OrderedLoc.compare` -/
def compare : Loc → Loc → Ordering
  | .R r1, .R r2 => Ord.compare (Mreg.index r1).toNat (Mreg.index r2).toNat
  | .R _, .S .. => .lt
  | .S .., .R _ => .gt
  | .S sl1 ofs1 ty1, .S sl2 ofs2 ty2 =>
      (Ord.compare (slotIndex sl1) (slotIndex sl2)).then
        ((Ord.compare ofs1 ofs2).then (Ord.compare (typIndex ty1) (typIndex ty2)))

theorem compare_spec (x y : Loc) :
    match compare x y with
    | .lt => lt x y
    | .eq => x = y
    | .gt => lt y x := by
  cases x with
  | R r1 =>
    cases y with
    | R r2 =>
      simp only [compare, lt]
      rcases Nat.lt_trichotomy (ridx r1) (ridx r2) with h | h | h
      · rw [Nat.compare_eq_lt.2 h]; exact h
      · rw [Nat.compare_eq_eq.2 h, ridx_inj h]
      · rw [Nat.compare_eq_gt.2 h]; exact h
    | S _ _ _ => trivial
  | S sl1 ofs1 ty1 =>
    cases y with
    | R _ => trivial
    | S sl2 ofs2 ty2 =>
      simp only [compare, lt]
      rcases Nat.lt_trichotomy (slotIndex sl1) (slotIndex sl2) with h | h | h
      · rw [Nat.compare_eq_lt.2 h]; exact .inl h
      · rw [Nat.compare_eq_eq.2 h]
        have hs := slotIndex_inj _ _ h
        subst hs
        rcases Int.lt_trichotomy ofs1 ofs2 with h' | rfl | h'
        · rw [Int.compare_eq_lt.2 h']; exact .inr ⟨rfl, .inl h'⟩
        · rw [Int.compare_eq_eq.2 rfl]
          rcases Nat.lt_trichotomy (typIndex ty1) (typIndex ty2) with h'' | h'' | h''
          · rw [Nat.compare_eq_lt.2 h'']; exact .inr ⟨rfl, .inr ⟨rfl, h''⟩⟩
          · rw [Nat.compare_eq_eq.2 h'', typIndex_inj _ _ h'']; rfl
          · rw [Nat.compare_eq_gt.2 h'']; exact .inr ⟨rfl, .inr ⟨rfl, h''⟩⟩
        · rw [Int.compare_eq_gt.2 h']; exact .inr ⟨rfl, .inl h'⟩
      · rw [Nat.compare_eq_gt.2 h]; exact .inl h

end OrderedLoc

/-- `OrderedLoc` -/
instance OrderedLoc : OrderedType Loc where
  lt := OrderedLoc.lt
  lt_trans := OrderedLoc.lt_trans
  lt_not_eq := OrderedLoc.lt_not_eq
  compare := OrderedLoc.compare
  compare_spec := OrderedLoc.compare_spec

namespace OrderedLoc

/-! ## The order and `Loc.diff` -/

/-- `OrderedLoc.diff_low_bound` -/
def diffLowBound (l : Loc) : Loc :=
  match l with
  | .R _ => l
  | .S sl ofs _ => .S sl (ofs - 1) .Tany64

/-- `OrderedLoc.diff_high_bound` -/
def diffHighBound (l : Loc) : Loc :=
  match l with
  | .R _ => l
  | .S sl ofs ty => .S sl (ofs + typesize ty - 1) .Tlong

theorem typesize_range (ty : ATyp) : 1 ≤ typesize ty ∧ typesize ty ≤ 2 := by
  cases ty <;> decide

/-- `OrderedLoc.outside_interval_diff`: a location strictly below the low
    bound or strictly above the high bound of `l` does not overlap `l`. -/
theorem outside_interval_diff (l l' : Loc)
    (h : lt l' (diffLowBound l) ∨ lt (diffHighBound l) l') : Loc.diff l l' := by
  cases l with
  | R mr =>
    cases l' with
    | R mr' =>
      simp only [diffLowBound, diffHighBound, lt] at h
      show mr ≠ mr'
      rintro rfl; exact Nat.lt_irrefl _ (h.elim id id)
    | S _ _ _ => trivial
  | S sl ofs ty =>
    cases l' with
    | R _ => trivial
    | S sl' ofs' ty' =>
      simp only [diffLowBound, diffHighBound, lt] at h
      show sl ≠ sl' ∨ ofs + typesize ty ≤ ofs' ∨ ofs' + typesize ty' ≤ ofs
      have r := typesize_range ty
      have r' := typesize_range ty'
      rcases h with h | h
      · rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
        · exact .inl fun e => by subst e; exact Nat.lt_irrefl _ h
        · exact .inr (.inr (by zomega))
        · have : typesize ty' = 1 := by
            cases ty' <;> simp_all [typIndex, typesize]
          exact .inr (.inr (by zomega))
      · rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
        · exact .inl fun e => by subst e; exact Nat.lt_irrefl _ h
        · exact .inr (.inl (by zomega))
        · exfalso; cases ty' <;> simp [typIndex] at h

/-- `OrderedLoc.diff_outside_interval`: conversely, a location that does not
    overlap `l` is below its low bound or above its high bound. -/
theorem diff_outside_interval (l l' : Loc) (h : Loc.diff l l') :
    lt l' (diffLowBound l) ∨ lt (diffHighBound l) l' := by
  cases l with
  | R mr =>
    cases l' with
    | R mr' =>
      simp only [diffLowBound, diffHighBound, lt]
      have : ridx mr ≠ ridx mr' := fun e => h (ridx_inj e)
      omega
    | S _ _ _ => exact .inr trivial
  | S sl ofs ty =>
    cases l' with
    | R _ => exact .inl trivial
    | S sl' ofs' ty' =>
      simp only [diffLowBound, diffHighBound, lt]
      have r := typesize_range ty
      have r' := typesize_range ty'
      rcases Nat.lt_trichotomy (slotIndex sl) (slotIndex sl') with hs | hs | hs
      · exact .inr (.inl hs)
      · have hs' := slotIndex_inj _ _ hs
        subst hs'
        rcases h with h | h | h
        · exact absurd rfl h
        · exact .inr (.inr ⟨rfl, .inl (by zomega)⟩)
        · by_cases hlt : ofs' < ofs - 1
          · exact .inl (.inr ⟨rfl, .inl hlt⟩)
          · have : typesize ty' = 1 ∧ typIndex ty' < typIndex .Tany64 ∨ typesize ty' = 2 := by
              cases ty' <;> simp [typesize, typIndex]
            rcases this with ⟨h1, h2⟩ | h1
            · exact .inl (.inr ⟨rfl, .inr ⟨by zomega, h2⟩⟩)
            · zomega
      · exact .inl (.inl hs)

end OrderedLoc

end CC
