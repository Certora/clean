/-
  The separation-logic assertion layer — Phase 7.3.

  `HProp` is a predicate on heap *fragments* (`CCLib/logic/Heap.lean`).  Separating
  conjunction is disjoint union, and the two payoff theorems at the bottom
  (`mapsto_load`, `mapsto_store`) are what let Phase 7.4 give `Sassign` and
  expression evaluation a rule that mentions only the footprint they touch.

  Deliberately kept free of `Env`/`TempEnv`: function specifications in Phase 7.5
  must be heap-only (a callee cannot mention its caller's temporaries), and the
  frame rule is stated for heap-only assertions too.  The `Env`/`TempEnv`-carrying
  `Assn` therefore lives in `CCLib/logic/Hoare.lean`, layered on top of this.
-/
import CCLib.logic.Heap

namespace CC

/-- A predicate on heap fragments. -/
abbrev HProp := Heap → Prop

namespace HProp

/-- Owns nothing. -/
def emp : HProp := fun h => h = Heap.emp

/-- A pure fact, owning nothing. -/
def pure (φ : Prop) : HProp := fun h => φ ∧ h = Heap.emp

/-- Separating conjunction: the fragment splits in two. -/
def sep (P Q : HProp) : HProp :=
  fun h => ∃ h1 h2, Heap.disjoint h1 h2 ∧ h = Heap.union h1 h2 ∧ P h1 ∧ Q h2

def hexists {α : Sort u} (f : α → HProp) : HProp := fun h => ∃ x, f x h

def entails (P Q : HProp) : Prop := ∀ h, P h → Q h

@[inherit_doc] infixr:64 " ∗ " => HProp.sep
notation "⌜" φ "⌝" => HProp.pure φ
@[inherit_doc] infix:50 " ⊢ " => HProp.entails

/-! ## Entailment is a preorder -/

theorem entails_refl (P : HProp) : P ⊢ P := fun _ h => h

theorem entails_trans {P Q R : HProp} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  fun h hp => h2 h (h1 h hp)

/-! ## The BI laws for `∗` -/

theorem sep_mono {P1 P2 Q1 Q2 : HProp} (h1 : P1 ⊢ Q1) (h2 : P2 ⊢ Q2) :
    P1 ∗ P2 ⊢ Q1 ∗ Q2 := by
  intro h ⟨ha, hb, hd, heq, hp1, hp2⟩
  exact ⟨ha, hb, hd, heq, h1 ha hp1, h2 hb hp2⟩

theorem sep_comm (P Q : HProp) : P ∗ Q ⊢ Q ∗ P := by
  intro h ⟨h1, h2, hd, heq, hp, hq⟩
  exact ⟨h2, h1, Heap.disjoint_comm hd, by rw [heq, Heap.union_comm hd], hq, hp⟩

theorem sep_emp (P : HProp) : P ∗ emp ⊢ P := by
  intro h ⟨h1, h2, _, heq, hp, he⟩
  rw [emp] at he; subst he
  rw [Heap.union_emp] at heq; subst heq; exact hp

theorem emp_sep (P : HProp) : P ⊢ P ∗ emp := by
  intro h hp
  exact ⟨h, Heap.emp, Heap.disjoint_emp_right h, (Heap.union_emp h).symm, hp, rfl⟩

theorem sep_assoc_l (P Q R : HProp) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by
  intro h ⟨hpq, hr, hd, heq, ⟨hp, hq, hdpq, heqpq, hP, hQ⟩, hR⟩
  subst heqpq
  rw [Heap.disjoint_union_left] at hd
  refine ⟨hp, Heap.union hq hr, ?_, ?_, hP, ⟨hq, hr, hd.2, rfl, hQ, hR⟩⟩
  · rw [Heap.disjoint_union_right]; exact ⟨hdpq, hd.1⟩
  · rw [heq, Heap.union_assoc]

theorem sep_assoc_r (P Q R : HProp) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by
  intro h ⟨hp, hqr, hd, heq, hP, ⟨hq, hr, hdqr, heqqr, hQ, hR⟩⟩
  subst heqqr
  rw [Heap.disjoint_union_right] at hd
  refine ⟨Heap.union hp hq, hr, ?_, ?_, ⟨hp, hq, hd.1, rfl, hP, hQ⟩, hR⟩
  · rw [Heap.disjoint_union_left]; exact ⟨hd.2, hdqr⟩
  · rw [heq, Heap.union_assoc]

/-- Pulling a pure fact out of a separating conjunction. -/
theorem pure_sep_elim {φ : Prop} {P : HProp} {h : Heap} (hs : (⌜φ⌝ ∗ P) h) : φ ∧ P h := by
  obtain ⟨h1, h2, _, heq, ⟨hφ, h1e⟩, hP⟩ := hs
  subst h1e
  rw [Heap.emp_union] at heq; subst heq
  exact ⟨hφ, hP⟩

theorem pure_sep_intro {φ : Prop} {P : HProp} {h : Heap} (hφ : φ) (hP : P h) :
    (⌜φ⌝ ∗ P) h :=
  ⟨Heap.emp, h, Heap.disjoint_emp_left h, (Heap.emp_union h).symm, ⟨hφ, rfl⟩, hP⟩

/-- A *true* pure conjunct drops out of a `∗` — it is `emp`.  Stated as an
    equality so it can be rewritten under anything. -/
theorem pure_true_sep_eq {φ : Prop} (hφ : φ) (P : HProp) : ⌜φ⌝ ∗ P = P := by
  funext h
  exact propext ⟨fun hs => (pure_sep_elim hs).2, fun hP => pure_sep_intro hφ hP⟩

/-! ## The AC laws as equalities

Entailments are not enough for `simp`; it needs `Eq`.  These follow from the
entailment versions in `CCLib/logic/SepLogic.lean` by `funext` + `propext`. -/

theorem sep_assoc_eq (P Q R : HProp) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := by
  funext h
  exact propext ⟨fun x => sep_assoc_l P Q R h x, fun x => sep_assoc_r P Q R h x⟩

theorem sep_comm_eq (P Q : HProp) : P ∗ Q = Q ∗ P := by
  funext h
  exact propext ⟨fun x => sep_comm P Q h x, fun x => sep_comm Q P h x⟩

/-- The third AC rule.  Without it `simp` can right-nest a chain but cannot
    *sort* it, which is the difference between normalizing and not. -/
theorem sep_left_comm_eq (P Q R : HProp) : P ∗ (Q ∗ R) = Q ∗ (P ∗ R) := by
  rw [← sep_assoc_eq, sep_comm_eq P Q, sep_assoc_eq]

theorem sep_emp_eq (P : HProp) : P ∗ emp = P := by
  funext h; exact propext ⟨fun x => sep_emp P h x, fun x => emp_sep P h x⟩

theorem emp_sep_eq (P : HProp) : emp ∗ P = P := by
  rw [sep_comm_eq]; exact sep_emp_eq P

/-! ## Cancellation, stated mathematically

`sep_cancel` below is the tactic; this is the theorem behind it — a `∗`-chain
depends only on the multiset of its conjuncts. -/

def sepList : List HProp → HProp
  | [] => emp
  | P :: Ps => P ∗ sepList Ps

theorem sepList_perm {l1 l2 : List HProp} (h : l1.Perm l2) : sepList l1 = sepList l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [sepList, ih]
  | swap x y l => simp only [sepList]; exact sep_left_comm_eq y x (sepList l)
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

end HProp

/-! ## Points-to -/


open HProp

/-- One owned byte. -/
def bytePtsTo (b : Block) (ofs : Z) (p : Permission) (mv : MemVal) : HProp :=
  fun h => h = Heap.single b ofs ⟨p, mv⟩

/-- A contiguous run of owned bytes, as a `∗`-chain. -/
def bytesPtsTo (b : Block) (p : Permission) : Z → List MemVal → HProp
  | _, [] => emp
  | ofs, v :: vl => bytePtsTo b ofs p v ∗ bytesPtsTo b p (ofs + 1) vl

/-- `mapsto chunk p b ofs v`: the bytes of `v` at `b + ofs`, correctly aligned,
    owned at permission `p`.  Mirrors VST's `mapsto`. -/
def mapsto (chunk : Chunk) (p : Permission) (b : Block) (ofs : Z) (v : Val) : HProp :=
  ⌜ofs % alignChunk chunk = 0⌝ ∗ bytesPtsTo b p ofs (encodeVal chunk v)

/-- **`mapsto` is a byte run**, once its alignment side condition is known.
    Definitional, but as an `Eq` it is the bridge a struct copy needs: the source
    of an aggregate assignment is owned as field `mapsto`s and consumed as raw
    bytes. -/
theorem mapsto_eq_bytes {chunk : Chunk} {p : Permission} {b : Block}
    {ofs : Z} {v : Val} (hal : ofs % alignChunk chunk = 0) :
    mapsto chunk p b ofs v = bytesPtsTo b p ofs (encodeVal chunk v) := by
  rw [mapsto, pure_true_sep_eq hal]

/-! ## From `bytesPtsTo` to `Heap.ownsRange`

`ownsRange` (Phase 7.2) is the form the `Agrees` bridge lemmas want. -/

theorem bytesPtsTo_ownsRange (b : Block) (p : Permission) :
    ∀ (vl : List MemVal) (ofs : _root_.Int) (h : Heap),
      bytesPtsTo b p ofs vl h → Heap.ownsRange h b ofs p vl := by
  intro vl
  induction vl with
  | nil => intro _ _ _ i hi; simp at hi
  | cons v vl' ih =>
      intro ofs h hb
      obtain ⟨h1, h2, hd, heq, hone, hrest⟩ := hb
      rw [bytePtsTo] at hone
      subst hone
      have hr := ih (ofs + 1) h2 hrest
      intro i hi
      cases i with
      | zero =>
          subst heq
          rw [show ofs + ((0 : Nat) : _root_.Int) = ofs from by omega]
          exact Heap.union_of_left (Heap.single_same b ofs ⟨p, v⟩)
      | succ j =>
          have hj : j < vl'.length := by simp only [List.length_cons] at hi; omega
          have hone := hr j hj
          subst heq
          rw [show ofs + ((j + 1 : Nat) : _root_.Int) = (ofs + 1) + (j : _root_.Int) from by
                push_cast; omega]
          refine Heap.union_of_right ?_ |>.trans (by simpa using hone)
          exact Heap.single_other b ofs ⟨p, v⟩ b ((ofs + 1) + (j : _root_.Int))
            (fun hc => by have : (ofs + 1) + (j : _root_.Int) = ofs := hc.2
                          omega)

/-- The bytes a `bytesPtsTo` fragment owns are exactly its range: outside it, the
    fragment is empty.  Needed to keep a frame disjoint across a store. -/
theorem bytesPtsTo_none (b : Block) (p : Permission) :
    ∀ (vl : List MemVal) (ofs : _root_.Int) (h : Heap),
      bytesPtsTo b p ofs vl h →
      ∀ (b' : Block) (ofs' : _root_.Int),
        (b' ≠ b ∨ ofs' < ofs ∨ ofs + (vl.length : _root_.Int) ≤ ofs') → h b' ofs' = none := by
  intro vl
  induction vl with
  | nil => intro _ _ hb _ _ _; rw [hb]; rfl
  | cons v vl' ih =>
      intro ofs h hb b' ofs' hout
      obtain ⟨h1, h2, _, heq, hone, hrest⟩ := hb
      rw [bytePtsTo] at hone; subst hone; subst heq
      have h1n : Heap.single b ofs ⟨p, v⟩ b' ofs' = none := by
        refine Heap.single_other b ofs ⟨p, v⟩ b' ofs' (fun hc => ?_)
        rcases hout with hb' | hlt | hge
        · exact hb' hc.1
        · have : ofs' = ofs := hc.2; omega
        · have : ofs' = ofs := hc.2
          simp only [List.length_cons] at hge
          omega
      rw [Heap.union_of_right h1n]
      refine ih (ofs + 1) h2 hrest b' ofs' ?_
      rcases hout with hb' | hlt | hge
      · exact Or.inl hb'
      · exact Or.inr (Or.inl (by omega))
      · simp only [List.length_cons] at hge
        exact Or.inr (Or.inr (by push_cast at hge ⊢; omega))

-- Order facts over fresh `_root_.Int` binders; see the abbrev-`Z` note in
-- `CCLib/common/MemdataLemmas.lean`.  An ascription on a `Z`-typed variable does not
-- move the operator, so `omega` needs its own binders.
private theorem eq_lt_succ (x y : _root_.Int) (h : x = y) : x < y + 1 := by omega

/-- Every offset is either inside a window `[base, base+n)` — at a definite index
    — or outside it.  All the index arithmetic of the store rule is concentrated
    here, over fresh `_root_.Int` binders, so no `omega` is needed at the use
    sites (where the offsets are `CC.Z`-typed and `omega` would be blind). -/
theorem window_split (base o : _root_.Int) (n : Nat) :
    (∃ i : Nat, i < n ∧ o = base + (i : _root_.Int))
    ∨ (o < base ∨ base + (n : _root_.Int) ≤ o) := by
  by_cases h1 : base ≤ o
  · by_cases h2 : o < base + (n : _root_.Int)
    · exact Or.inl ⟨(o - base).toNat, by omega, by omega⟩
    · exact Or.inr (Or.inr (by omega))
  · exact Or.inr (Or.inl (by omega))

/-- A `bytesPtsTo` fragment exists for any byte list: build it as the chain of
    singletons.  Needed to produce the *post*-state fragment of a store. -/
theorem bytesPtsTo_exists (b : Block) (p : Permission) :
    ∀ (vl : List MemVal) (ofs : _root_.Int), ∃ h, bytesPtsTo b p ofs vl h := by
  intro vl
  induction vl with
  | nil => intro _; exact ⟨Heap.emp, rfl⟩
  | cons v vl' ih =>
      intro ofs
      obtain ⟨h2, h2m⟩ := ih (ofs + 1)
      refine ⟨Heap.union (Heap.single b ofs ⟨p, v⟩) h2, ?_⟩
      refine ⟨Heap.single b ofs ⟨p, v⟩, h2, ?_, rfl, rfl, h2m⟩
      intro b' ofs'
      by_cases hc : b' = b ∧ ofs' = ofs
      · refine Or.inr (bytesPtsTo_none b p vl' (ofs + 1) h2 h2m b' ofs' ?_)
        exact Or.inr (Or.inl (eq_lt_succ ofs' ofs hc.2))
      · exact Or.inl (Heap.single_other b ofs ⟨p, v⟩ b' ofs' hc)

/-! ## The two theorems Phase 7.4 is built on -/

/-- **Reading through a `mapsto`.**  Owning the footprint at `Readable` or better
    is enough for `Mem.load` to succeed and return the value — whatever else the
    memory contains, and whatever the frame `hf` owns. -/
theorem mapsto_load {chunk : Chunk} {p : Permission} {b : Block} {ofs : _root_.Int}
    {v : Val} {h : Heap} {m : Mem}
    (hpr : permOrder p .Readable = true)
    (hm : mapsto chunk p b ofs v h)
    (hagh : Heap.Agrees h m) :
    Mem.load chunk m b ofs = some (Val.loadResult chunk v) := by
  obtain ⟨halign, hbytes⟩ := pure_sep_elim hm
  have hown := bytesPtsTo_ownsRange b p (encodeVal chunk v) ofs h hbytes
  have hsz : ((encodeVal chunk v).length : _root_.Int) = sizeChunk chunk := by
    rw [length_encodeVal]; cases chunk <;> simp [sizeChunkNat, sizeChunk]
  have hrp := Heap.Agrees_rangePerm hagh hown .Cur
  rw [hsz] at hrp
  have hva : Mem.validAccess m chunk b ofs .Readable = true := by
    simp only [Mem.validAccess, Bool.and_eq_true]
    exact ⟨Mem.rangePerm_implies hrp hpr, by simp [halign]⟩
  unfold Mem.load
  rw [hva]
  simp only [if_true]
  congr 1
  rw [show Mem.getN (sizeChunkNat chunk) ofs (PMap.get b m.contents)
        = encodeVal chunk v from ?_]
  · exact decodeVal_encodeVal chunk v
  · rw [show sizeChunkNat chunk = (encodeVal chunk v).length from
          (length_encodeVal chunk v).symm]
    exact Heap.Agrees_getN hagh (encodeVal chunk v) ofs hown

/-- **Writing through a `mapsto`.**  Owning the footprint at `Writable` or better
    lets the store succeed, replaces the fragment with one for the new value, and
    leaves any disjoint frame `hf` untouched — the last conjunct is the frame
    property, and it is why Phase 7.4 gets a frame rule for free. -/
theorem mapsto_store {chunk : Chunk} {p : Permission} {b : Block} {ofs : _root_.Int}
    {v v' : Val} {h hf : Heap} {m : Mem}
    (hpw : permOrder p .Writable = true)
    (hm : mapsto chunk p b ofs v h)
    (hd : Heap.disjoint h hf)
    (hag : Heap.Agrees (Heap.union h hf) m) :
    ∃ m' h', Mem.store chunk m b ofs v' = some m'
           ∧ mapsto chunk p b ofs v' h'
           ∧ Heap.disjoint h' hf
           ∧ Heap.Agrees (Heap.union h' hf) m' := by
  obtain ⟨halign, hbytes⟩ := pure_sep_elim hm
  have hown := bytesPtsTo_ownsRange b p (encodeVal chunk v) ofs h hbytes
  have hagh : Heap.Agrees h m := Heap.Agrees_union_left hag
  have hlen : (encodeVal chunk v).length = sizeChunkNat chunk := length_encodeVal chunk v
  have hlen' : (encodeVal chunk v').length = sizeChunkNat chunk := length_encodeVal chunk v'
  have hsz : ((sizeChunkNat chunk : Nat) : _root_.Int) = sizeChunk chunk := by
    cases chunk <;> simp [sizeChunkNat, sizeChunk]
  -- the store succeeds
  have hrp := Heap.Agrees_rangePerm hagh hown .Cur
  rw [hlen, hsz] at hrp
  have hvaW : Mem.validAccess m chunk b ofs .Writable = true := by
    simp only [Mem.validAccess, Bool.and_eq_true]
    exact ⟨Mem.rangePerm_implies hrp hpw, by simp [halign]⟩
  have hsome : (Mem.store chunk m b ofs v').isSome = true := by
    unfold Mem.store; rw [hvaW]; simp
  obtain ⟨m', hstore⟩ : ∃ m', Mem.store chunk m b ofs v' = some m' :=
    ⟨_, (Option.some_get hsome).symm⟩
  -- the frame owns nothing in the written window
  have hfnone : ∀ i : Nat, i < sizeChunkNat chunk → hf b (ofs + (i : _root_.Int)) = none := by
    intro i hi
    rcases hd b (ofs + (i : _root_.Int)) with hn | hn
    · rw [hown i (by omega)] at hn; exact absurd hn (by simp)
    · exact hn
  obtain ⟨h', h'm⟩ := bytesPtsTo_exists b p (encodeVal chunk v') ofs
  have hown' := bytesPtsTo_ownsRange b p (encodeVal chunk v') ofs h' h'm
  refine ⟨m', h', hstore, pure_sep_intro halign h'm, ?_, ?_⟩
  · -- `h'` has the same footprint as `h`, so it is still disjoint from `hf`
    intro bb oo
    by_cases hb : bb = b
    · rw [hb]
      rcases window_split ofs oo (sizeChunkNat chunk) with ⟨i, hi, hoo⟩ | hout
      · refine Or.inr ?_
        rw [hoo]
        exact hfnone i hi
      · refine Or.inl (bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm b oo ?_)
        rw [hlen']; exact Or.inr hout
    · exact Or.inl (bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm bb oo (Or.inl hb))
  · -- `Agrees`: the written cells hold the new bytes, the frame is untouched
    have hagf : Heap.Agrees hf m' := Heap.Agrees_store_frame hstore
      (Heap.Agrees_union_right hd hag) hfnone
    refine Heap.Agrees_union ?_ hagf
    intro bb oo c hc
    -- `hc` places `(bb, oo)` inside the written window
    by_cases hb : bb = b
    · rw [hb] at hc ⊢
      rcases window_split ofs oo (sizeChunkNat chunk) with ⟨i, hi, hoo⟩ | hout
      · subst hoo
        have hcell := hown' i (by rw [hlen']; exact hi)
        rw [hcell] at hc
        injection hc with hc
        subst hc
        have hpre := hagh b (ofs + (i : _root_.Int)) ⟨p, (encodeVal chunk v)[i]!⟩
          (hown i (by rw [hlen]; exact hi))
        refine ⟨?_, ?_, ?_⟩
        · rw [Mem.store_access hstore]; exact hpre.1
        · rw [Mem.store_access hstore]; exact hpre.2.1
        · rw [Mem.store_contents hstore, PMap.gss]
          exact Mem.setN_inside (encodeVal chunk v') ofs _ i (by rw [hlen']; exact hi)
      · exfalso
        rw [bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm b oo
              (by rw [hlen']; exact Or.inr hout)] at hc
        exact absurd hc (by simp)
    · exfalso
      rw [bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm bb oo (Or.inl hb)] at hc
      exact absurd hc (by simp)

/-- **Writing into a run of owned bytes**, whose *old* contents need not encode
    any value at all.  `mapsto_store` requires the window to be a `mapsto`, i.e.
    to already hold `encodeVal chunk v` for some `v`; a freshly handed-over output
    buffer is only `anyBytes`, and a `MemVal` run in general is not the encoding
    of anything (an `Undef` byte, or a pointer fragment, is not).  The store
    itself never looks at what was there, so the hypothesis is unnecessary — this
    is `mapsto_store` with `encodeVal chunk v` generalised to any equal-length
    byte list. -/
theorem bytesPtsTo_store {chunk : Chunk} {p : Permission} {b : Block} {ofs : _root_.Int}
    {bytes : List MemVal} {v' : Val} {h hf : Heap} {m : Mem}
    (hpw : permOrder p .Writable = true)
    (hal : ofs % alignChunk chunk = 0)
    (hlen : bytes.length = sizeChunkNat chunk)
    (hb : bytesPtsTo b p ofs bytes h)
    (hd : Heap.disjoint h hf)
    (hag : Heap.Agrees (Heap.union h hf) m) :
    ∃ m' h', Mem.store chunk m b ofs v' = some m'
           ∧ mapsto chunk p b ofs v' h'
           ∧ Heap.disjoint h' hf
           ∧ Heap.Agrees (Heap.union h' hf) m' := by
  have hown := bytesPtsTo_ownsRange b p bytes ofs h hb
  have hagh : Heap.Agrees h m := Heap.Agrees_union_left hag
  have hlen' : (encodeVal chunk v').length = sizeChunkNat chunk := length_encodeVal chunk v'
  have hsz : ((sizeChunkNat chunk : Nat) : _root_.Int) = sizeChunk chunk := by
    cases chunk <;> simp [sizeChunkNat, sizeChunk]
  have hrp := Heap.Agrees_rangePerm hagh hown .Cur
  rw [hlen, hsz] at hrp
  have hvaW : Mem.validAccess m chunk b ofs .Writable = true := by
    simp only [Mem.validAccess, Bool.and_eq_true]
    exact ⟨Mem.rangePerm_implies hrp hpw, by simp [hal]⟩
  have hsome : (Mem.store chunk m b ofs v').isSome = true := by
    unfold Mem.store; rw [hvaW]; simp
  obtain ⟨m', hstore⟩ : ∃ m', Mem.store chunk m b ofs v' = some m' :=
    ⟨_, (Option.some_get hsome).symm⟩
  have hfnone : ∀ i : Nat, i < sizeChunkNat chunk → hf b (ofs + (i : _root_.Int)) = none := by
    intro i hi
    rcases hd b (ofs + (i : _root_.Int)) with hn | hn
    · rw [hown i (by omega)] at hn; exact absurd hn (by simp)
    · exact hn
  obtain ⟨h', h'm⟩ := bytesPtsTo_exists b p (encodeVal chunk v') ofs
  have hown' := bytesPtsTo_ownsRange b p (encodeVal chunk v') ofs h' h'm
  refine ⟨m', h', hstore, pure_sep_intro hal h'm, ?_, ?_⟩
  · intro bb oo
    by_cases hbb : bb = b
    · rw [hbb]
      rcases window_split ofs oo (sizeChunkNat chunk) with ⟨i, hi, hoo⟩ | hout
      · refine Or.inr ?_
        rw [hoo]
        exact hfnone i hi
      · refine Or.inl (bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm b oo ?_)
        rw [hlen']; exact Or.inr hout
    · exact Or.inl (bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm bb oo (Or.inl hbb))
  · have hagf : Heap.Agrees hf m' := Heap.Agrees_store_frame hstore
      (Heap.Agrees_union_right hd hag) hfnone
    refine Heap.Agrees_union ?_ hagf
    intro bb oo c hc
    by_cases hbb : bb = b
    · rw [hbb] at hc ⊢
      rcases window_split ofs oo (sizeChunkNat chunk) with ⟨i, hi, hoo⟩ | hout
      · subst hoo
        have hcell := hown' i (by rw [hlen']; exact hi)
        rw [hcell] at hc
        injection hc with hc
        subst hc
        have hpre := hagh b (ofs + (i : _root_.Int)) ⟨p, bytes[i]!⟩
          (hown i (by rw [hlen]; exact hi))
        refine ⟨?_, ?_, ?_⟩
        · rw [Mem.store_access hstore]; exact hpre.1
        · rw [Mem.store_access hstore]; exact hpre.2.1
        · rw [Mem.store_contents hstore, PMap.gss]
          exact Mem.setN_inside (encodeVal chunk v') ofs _ i (by rw [hlen']; exact hi)
      · exfalso
        rw [bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm b oo
              (by rw [hlen']; exact Or.inr hout)] at hc
        exact absurd hc (by simp)
    · exfalso
      rw [bytesPtsTo_none b p (encodeVal chunk v') ofs h' h'm bb oo (Or.inl hbb)] at hc
      exact absurd hc (by simp)

/-- **Overwriting a byte range.**  The `storebytes` sibling of `mapsto_store`,
    generalised from one chunk's bytes to an arbitrary equal-length list.  Needed
    because `Events.ExtcallMemcpySem` is stated over `loadbytes`/`storebytes`, not
    `load`/`store`, and because a `memcpy` footprint is a byte count, not a chunk.

    (`mapsto_store` is the same argument at `encodeVal chunk v`; it is kept
    separate because `Mem.store` additionally demands alignment, so neither lemma
    is an instance of the other.) -/
theorem bytesPtsTo_storebytes {p : Permission} {b : Block} {ofs : _root_.Int}
    {old new : List MemVal} {h hf : Heap} {m : Mem}
    (hpw : permOrder p .Writable = true)
    (hlen : new.length = old.length)
    (hm : bytesPtsTo b p ofs old h)
    (hd : Heap.disjoint h hf)
    (hag : Heap.Agrees (Heap.union h hf) m) :
    ∃ m' h', Mem.storebytes m b ofs new = some m'
           ∧ bytesPtsTo b p ofs new h'
           ∧ Heap.disjoint h' hf
           ∧ Heap.Agrees (Heap.union h' hf) m' := by
  have hown := bytesPtsTo_ownsRange b p old ofs h hm
  have hagh : Heap.Agrees h m := Heap.Agrees_union_left hag
  -- the store succeeds: the fragment's permissions are realized by `m`
  have hrp := Heap.Agrees_rangePerm hagh hown .Cur
  obtain ⟨m', hstore⟩ : ∃ m', Mem.storebytes m b ofs new = some m' := by
    refine Mem.storebytes_isSome ?_
    rw [hlen]
    exact Mem.rangePerm_implies hrp hpw
  -- the frame owns nothing in the written window
  have hfnone : ∀ i : Nat, i < old.length → hf b (ofs + (i : _root_.Int)) = none := by
    intro i hi
    rcases hd b (ofs + (i : _root_.Int)) with hn | hn
    · rw [hown i hi] at hn; exact absurd hn (by simp)
    · exact hn
  obtain ⟨h', h'm⟩ := bytesPtsTo_exists b p new ofs
  have hown' := bytesPtsTo_ownsRange b p new ofs h' h'm
  refine ⟨m', h', hstore, h'm, ?_, ?_⟩
  · -- `h'` has the same footprint as `h`, so it is still disjoint from `hf`
    intro bb oo
    by_cases hb : bb = b
    · rw [hb]
      rcases window_split ofs oo old.length with ⟨i, hi, hoo⟩ | hout
      · exact Or.inr (by rw [hoo]; exact hfnone i hi)
      · exact Or.inl (bytesPtsTo_none b p new ofs h' h'm b oo (by rw [hlen]; exact Or.inr hout))
    · exact Or.inl (bytesPtsTo_none b p new ofs h' h'm bb oo (Or.inl hb))
  · -- `Agrees`: the written cells hold the new bytes, the frame is untouched
    have hagf : Heap.Agrees hf m' := Heap.Agrees_storebytes_frame hstore
      (Heap.Agrees_union_right hd hag) (by rw [hlen]; exact hfnone)
    refine Heap.Agrees_union ?_ hagf
    intro bb oo c hc
    by_cases hb : bb = b
    · rw [hb] at hc ⊢
      rcases window_split ofs oo old.length with ⟨i, hi, hoo⟩ | hout
      · subst hoo
        have hcell := hown' i (by rw [hlen]; exact hi)
        rw [hcell] at hc
        injection hc with hc
        subst hc
        have hpre := hagh b (ofs + (i : _root_.Int)) ⟨p, old[i]!⟩ (hown i hi)
        refine ⟨?_, ?_, ?_⟩
        · rw [Mem.storebytes_access hstore]; exact hpre.1
        · rw [Mem.storebytes_access hstore]; exact hpre.2.1
        · rw [Mem.storebytes_contents hstore, PMap.gss]
          exact Mem.setN_inside new ofs _ i (by rw [hlen]; exact hi)
      · exfalso
        rw [bytesPtsTo_none b p new ofs h' h'm b oo
              (by rw [hlen]; exact Or.inr hout)] at hc
        exact absurd hc (by simp)
    · exfalso
      rw [bytesPtsTo_none b p new ofs h' h'm bb oo (Or.inl hb)] at hc
      exact absurd hc (by simp)

/-- **Reading a byte range.**  The dual, and the other half of what `memcpy`
    needs: `loadbytes` returns exactly the owned bytes. -/
theorem bytesPtsTo_loadbytes {p : Permission} {b : Block} {ofs : _root_.Int}
    {bytes : List MemVal} {h : Heap} {m : Mem}
    (hpr : permOrder p .Readable = true)
    (hm : bytesPtsTo b p ofs bytes h) (hag : Heap.Agrees h m) :
    Mem.loadbytes m b ofs (bytes.length : _root_.Int) = some bytes := by
  have hown := bytesPtsTo_ownsRange b p bytes ofs h hm
  have hrp := Mem.rangePerm_implies (Heap.Agrees_rangePerm hag hown .Cur) hpr
  rw [Mem.loadbytes_result hrp,
      show ((bytes.length : _root_.Int)).toNat = bytes.length from by omega]
  exact congrArg some
    (Mem.getN_eq_of_agree bytes ofs _
      (fun i hi => (hag b (ofs + (i : _root_.Int)) _ (hown i hi)).2.2))

/-! ## A derived predicate: arrays of `unsigned int`

This replaces `ArrU32` from `CCLib/logic/HoareArray.lean`, which was a plain (non-
separating) predicate asserting a load for every index.  The separating version
below says the array *owns* its bytes, so the frame rule applies to it. -/

/-- `arrayU32 p b ofs n f`: `n` consecutive `unsigned int`s at `b + ofs`, holding
    `f 0 … f (n-1)`, owned at permission `p`. -/
def arrayU32 (p : Permission) (b : Block) : Z → Nat → (Nat → Integers.Int) → HProp
  | _, 0, _ => emp
  | ofs, n + 1, f =>
      mapsto .Mint32 p b ofs (.Vint (f 0)) ∗ arrayU32 p b (ofs + 4) n (fun i => f (i + 1))

private theorem step_offset (base : _root_.Int) (j : Nat) :
    (base + 4) + 4 * (j : _root_.Int) = base + 4 * ((j + 1 : Nat) : _root_.Int) := by
  push_cast; omega

/-- A `mapsto` owns exactly its chunk's bytes. -/
theorem mapsto_none {chunk : Chunk} {p : Permission} {b : Block} {ofs : _root_.Int}
    {v : Val} {h : Heap} (hm : mapsto chunk p b ofs v h) (b' : Block) (ofs' : _root_.Int)
    (hout : b' ≠ b ∨ ofs' < ofs ∨ ofs + (sizeChunkNat chunk : _root_.Int) ≤ ofs') :
    h b' ofs' = none := by
  obtain ⟨_, hbytes⟩ := pure_sep_elim hm
  exact bytesPtsTo_none b p (encodeVal chunk v) ofs h hbytes b' ofs'
    (by rw [length_encodeVal]; exact hout)

/-- An `arrayU32` owns exactly its `4 * n` bytes. -/
theorem arrayU32_none (p : Permission) (b : Block) :
    ∀ (n : Nat) (f : Nat → Integers.Int) (ofs : _root_.Int) (h : Heap),
      arrayU32 p b ofs n f h →
      ∀ (b' : Block) (ofs' : _root_.Int),
        (b' ≠ b ∨ ofs' < ofs ∨ ofs + 4 * (n : _root_.Int) ≤ ofs') → h b' ofs' = none := by
  intro n
  induction n with
  | zero => intro _ _ h harr _ _ _; rw [harr]; rfl
  | succ k ih =>
      intro f ofs h harr b' ofs' hout
      obtain ⟨h1, h2, _, heq, hhead, htail⟩ := harr
      subst heq
      have h1n : h1 b' ofs' = none := by
        refine mapsto_none hhead b' ofs' ?_
        rcases hout with hb | hlt | hge
        · exact Or.inl hb
        · exact Or.inr (Or.inl hlt)
        · exact Or.inr (Or.inr (by push_cast at hge ⊢; simp [sizeChunkNat, sizeChunk]; omega))
      rw [Heap.union_of_right h1n]
      refine ih (fun i => f (i + 1)) (ofs + 4) h2 htail b' ofs' ?_
      rcases hout with hb | hlt | hge
      · exact Or.inl hb
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by push_cast at hge ⊢; omega))

/-- `arrayU32` is satisfiable at any aligned base: not a vacuous predicate. -/
theorem arrayU32_satisfiable (p : Permission) (b : Block) :
    ∀ (n : Nat) (f : Nat → Integers.Int) (ofs : _root_.Int),
      ofs % 4 = 0 → ∃ h, arrayU32 p b ofs n f h := by
  intro n
  induction n with
  | zero => intro _ _ _; exact ⟨Heap.emp, rfl⟩
  | succ k ih =>
      intro f ofs halign
      obtain ⟨h2, h2m⟩ := ih (fun i => f (i + 1)) (ofs + 4) (by omega)
      obtain ⟨h1, h1m⟩ :=
        bytesPtsTo_exists b p (encodeVal .Mint32 (.Vint (f 0))) ofs
      have h1mm : mapsto .Mint32 p b ofs (.Vint (f 0)) h1 :=
        pure_sep_intro (by simpa [alignChunk] using halign) h1m
      refine ⟨Heap.union h1 h2, ⟨h1, h2, ?_, rfl, h1mm, h2m⟩⟩
      intro bb oo
      rcases window_split ofs oo (sizeChunkNat .Mint32) with ⟨i, hi, hoo⟩ | hout
      · by_cases hb : bb = b
        · refine Or.inr (arrayU32_none p b k (fun i => f (i + 1)) (ofs + 4) h2 h2m bb oo ?_)
          rw [hb]
          exact Or.inr (Or.inl (by subst hoo; simp [sizeChunkNat, sizeChunk] at hi; omega))
        · exact Or.inl (mapsto_none h1mm bb oo (Or.inl hb))
      · exact Or.inl (mapsto_none h1mm bb oo (Or.inr hout))

/-- **Reading an array element.**  Owning the array is enough to load any element,
    with the rest of the array absorbed into the frame — which is exactly what
    `mapsto_load`'s arbitrary frame is for. -/
theorem arrayU32_load (p : Permission) (b : Block) (hpr : permOrder p .Readable = true) :
    ∀ (n : Nat) (f : Nat → Integers.Int) (i : Nat), i < n →
      ∀ (ofs : _root_.Int) (h : Heap) (m : Mem),
        arrayU32 p b ofs n f h → Heap.Agrees h m →
        Mem.load .Mint32 m b (ofs + 4 * (i : _root_.Int)) = some (.Vint (f i)) := by
  intro n
  induction n with
  | zero => intro _ i hi; simp at hi
  | succ k ih =>
      intro f i hi ofs h m harr hag
      obtain ⟨h1, h2, hd12, heq, hhead, htail⟩ := harr
      subst heq
      cases i with
      | zero =>
          have := mapsto_load hpr hhead (Heap.Agrees_union_left hag)
          simpa [Val.loadResult] using this
      | succ j =>
          have hj : j < k := by omega
          have hrec := ih (fun i => f (i + 1)) j hj (ofs + 4) h2 m htail
            (Heap.Agrees_union_right hd12 hag)
          rwa [step_offset ofs j] at hrec

end CC
