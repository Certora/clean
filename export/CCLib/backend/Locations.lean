/-
  Locations: machine registers and abstract stack slots — port of
  `backend/Locations.v` (`slot`, `typesize`, `typealign`, `loc`, module
  `Loc` with `diff`, `notin`, `disjoint`, `norepet`, `no_overlap`, and
  module `Locmap` with `set`, `undef`, `getpair`, `setpair`, `setres` and
  their "good variable" lemmas).

  Differences from Rocq: `Loc.diff`/`Loc.notin` are `Prop`s with
  `Decidable` instances (Rocq's `diff_dec`/`notin_dec`); the ordered-type
  modules (`OrderedLoc` …), used only for the register allocator's
  finite sets, are not ported.
-/
import CCLib.aarch64.Machregs
import CCLib.aarch64.Archi

namespace CC

/-- `Locations.slot` -/
inductive Slot where
  | Local | Incoming | Outgoing
  deriving DecidableEq, Repr

/-- `Locations.typesize` -/
def typesize : ATyp → Z
  | .Tint => 1 | .Tlong => 2 | .Tfloat => 2 | .Tsingle => 1 | .Tany32 => 1 | .Tany64 => 2

theorem typesize_pos (ty : ATyp) : typesize ty > 0 := by cases ty <;> decide

/-- `Locations.typealign` -/
def typealign : ATyp → Z
  | .Tint => 1
  | .Tlong => (Archi.align_int64 : Z) / 4
  | .Tfloat => (Archi.align_float64 : Z) / 4
  | .Tsingle => 1
  | .Tany32 => 1
  | .Tany64 => (max (Archi.align_int64 : Z) (Archi.align_float64 : Z)) / 4

theorem typealign_pos (ty : ATyp) : typealign ty > 0 := by cases ty <;> decide

theorem typealign_typesize (ty : ATyp) : typealign ty ∣ typesize ty := by
  cases ty <;> decide

/-- `Locations.loc` -/
inductive Loc where
  | R (r : Mreg)
  | S (sl : Slot) (pos : Z) (ty : ATyp)
  deriving DecidableEq, Repr

namespace Loc

/-- `Loc.type` -/
def type : Loc → ATyp
  | .R r => r.type
  | .S _ _ ty => ty

/-- `Loc.diff`: two locations that do not overlap. -/
def diff : Loc → Loc → Prop
  | .R r1, .R r2 => r1 ≠ r2
  | .S s1 d1 t1, .S s2 d2 t2 => s1 ≠ s2 ∨ d1 + typesize t1 ≤ d2 ∨ d2 + typesize t2 ≤ d1
  | _, _ => True

instance (l1 l2 : Loc) : Decidable (diff l1 l2) := by
  cases l1 <;> cases l2 <;> simp only [diff] <;> infer_instance

theorem same_not_diff (l : Loc) : ¬ diff l l := by
  cases l with
  | R r => simp [diff]
  | S sl pos ty =>
    have := typesize_pos ty
    intro h
    have key : ∀ a b : _root_.Int, b > 0 → ¬ (a + b ≤ a) := by intros; omega
    rcases h with h | h | h
    · exact h rfl
    · exact key _ _ this h
    · exact key _ _ this h

theorem diff_not_eq {l1 l2 : Loc} (h : diff l1 l2) : l1 ≠ l2 := by
  intro he; subst he; exact same_not_diff _ h

theorem diff_sym {l1 l2 : Loc} (h : diff l1 l2) : diff l2 l1 := by
  cases l1 <;> cases l2 <;> simp only [diff] at h ⊢
  · exact Ne.symm h
  · rcases h with h | h | h
    · exact .inl (Ne.symm h)
    · exact .inr (.inr h)
    · exact .inr (.inl h)

/-- `Loc.notin` -/
def notin (l : Loc) : List Loc → Prop
  | [] => True
  | l1 :: ls => diff l l1 ∧ notin l ls

instance instDecidableNotin (l : Loc) : (ll : List Loc) → Decidable (notin l ll)
  | [] => isTrue trivial
  | a :: ll =>
    have := instDecidableNotin l ll
    inferInstanceAs (Decidable (diff l a ∧ notin l ll))

theorem notin_iff {l : Loc} {ll : List Loc} : notin l ll ↔ ∀ l' ∈ ll, diff l l' := by
  induction ll with
  | nil => simp [notin]
  | cons a ll ih => simp [notin, ih]

theorem notin_not_in {l : Loc} {ll : List Loc} (h : notin l ll) : l ∉ ll := by
  intro hin; exact same_not_diff l (notin_iff.mp h l hin)

/-- `Loc.disjoint` -/
def disjoint (l1 l2 : List Loc) : Prop := ∀ x1 ∈ l1, ∀ x2 ∈ l2, diff x1 x2

theorem disjoint_sym {l1 l2 : List Loc} (h : disjoint l1 l2) : disjoint l2 l1 :=
  fun x2 h2 x1 h1 => diff_sym (h x1 h1 x2 h2)

theorem in_notin_diff {l1 l2 : Loc} {ll : List Loc} (h : notin l1 ll) (hin : l2 ∈ ll) :
    diff l1 l2 := notin_iff.mp h l2 hin

theorem notin_disjoint {l1 l2 : List Loc} (h : ∀ x ∈ l1, notin x l2) : disjoint l1 l2 :=
  fun x hx y hy => notin_iff.mp (h x hx) y hy

theorem disjoint_notin {l1 l2 : List Loc} {x : Loc} (h : disjoint l1 l2) (hx : x ∈ l1) :
    notin x l2 := notin_iff.mpr (h x hx)

/-- `Loc.norepet` -/
inductive Norepet : List Loc → Prop where
  | nil : Norepet []
  | cons (hd tl) : notin hd tl → Norepet tl → Norepet (hd :: tl)

instance instDecidableNorepet : (ll : List Loc) → Decidable (Norepet ll)
  | [] => isTrue .nil
  | a :: ll =>
    match inferInstanceAs (Decidable (notin a ll)), instDecidableNorepet ll with
    | isTrue h1, isTrue h2 => isTrue (.cons _ _ h1 h2)
    | isFalse h1, _ => isFalse (fun h => by cases h; contradiction)
    | _, isFalse h2 => isFalse (fun h => by cases h; contradiction)

/-- `Loc.no_overlap` -/
def NoOverlap (l1 l2 : List Loc) : Prop := ∀ r ∈ l1, ∀ s ∈ l2, r = s ∨ diff r s

end Loc

/-- `Locations.Locmap.t` -/
abbrev Locmap := Loc → Val

namespace Locmap

/-- `Locmap.init` -/
def init (x : Val) : Locmap := fun _ => x

/-- `Locmap.get` -/
def get (l : Loc) (m : Locmap) : Val := m l

/-- `Locmap.set`: overlapping locations become undefined, and stack slots
    normalise their content to the slot's type. -/
def set (l : Loc) (v : Val) (m : Locmap) : Locmap := fun p =>
  if l = p then
    match l with
    | .R _ => v
    | .S _ _ ty => Val.loadResult (Chunk.ofTyp ty) v
  else if Loc.diff l p then m p
  else .Vundef

theorem gss (l : Loc) (v : Val) (m : Locmap) :
    set l v m l = match l with
      | .R _ => v
      | .S _ _ ty => Val.loadResult (Chunk.ofTyp ty) v := by
  simp [set]

theorem gss_reg (r : Mreg) (v : Val) (m : Locmap) : set (.R r) v m (.R r) = v := by
  simp [set]

theorem gso {l : Loc} {v : Val} {m : Locmap} {p : Loc} (h : Loc.diff l p) : set l v m p = m p := by
  simp [set, Loc.diff_not_eq h, h]

/-- `Locmap.undef` -/
def undef : List Loc → Locmap → Locmap
  | [], m => m
  | l1 :: ll', m => undef ll' (set l1 .Vundef m)

theorem guo {ll : List Loc} {l : Loc} {m : Locmap} (h : Loc.notin l ll) : undef ll m l = m l := by
  induction ll generalizing m with
  | nil => rfl
  | cons a ll ih =>
    simp only [Loc.notin] at h
    simp only [undef]
    rw [ih h.2, gso (Loc.diff_sym h.1)]

theorem gus {ll : List Loc} {l : Loc} {m : Locmap} (h : l ∈ ll) : undef ll m l = .Vundef := by
  have P : ∀ ll l (m : Locmap), m l = .Vundef → undef ll m l = .Vundef := by
    intro ll
    induction ll with
    | nil => intro l m h; exact h
    | cons a ll ih =>
      intro l m hm
      apply ih
      simp only [set]
      split
      · rename_i he; subst he
        cases a with
        | R _ => rfl
        | S _ _ ty => cases ty <;> rfl
      · split
        · exact hm
        · rfl
  induction ll generalizing m with
  | nil => simp at h
  | cons a ll ih =>
    simp only [undef]
    rcases List.mem_cons.mp h with rfl | h
    · apply P
      simp only [set]
      cases l with
      | R _ => rfl
      | S _ _ ty => cases ty <;> rfl
    · exact ih h

/-- `Locmap.getpair` -/
def getpair (p : RPair Loc) (m : Locmap) : Val :=
  match p with
  | .One l => m l
  | .Twolong l1 l2 => Val.longofwords (m l1) (m l2)

/-- `Locmap.setpair` -/
def setpair (p : RPair Mreg) (v : Val) (m : Locmap) : Locmap :=
  match p with
  | .One r => set (.R r) v m
  | .Twolong hi lo => set (.R lo) (Val.loword v) (set (.R hi) (Val.hiword v) m)

theorem getpair_exten {p : RPair Loc} {ls1 ls2 : Locmap}
    (h : ∀ l ∈ p.regs, ls2 l = ls1 l) : getpair p ls2 = getpair p ls1 := by
  cases p with
  | One l => exact h l (by simp [RPair.regs])
  | Twolong l1 l2 =>
    simp only [getpair]
    rw [h l1 (by simp [RPair.regs]), h l2 (by simp [RPair.regs])]

theorem gpo {p : RPair Mreg} {v : Val} {m : Locmap} {l : Loc}
    (h : p.Forall (fun r => Loc.diff l (.R r))) : setpair p v m l = m l := by
  cases p with
  | One r => exact gso (Loc.diff_sym h)
  | Twolong hi lo =>
    simp only [RPair.Forall] at h
    simp only [setpair]
    rw [gso (Loc.diff_sym h.2), gso (Loc.diff_sym h.1)]

/-- `Locmap.setres` -/
def setres : BuiltinRes Mreg → Val → Locmap → Locmap
  | .BR r, v, m => set (.R r) v m
  | .BR_none, _, m => m
  | .BR_splitlong hi lo, v, m => setres lo (Val.loword v) (setres hi (Val.hiword v) m)

end Locmap
end CC
