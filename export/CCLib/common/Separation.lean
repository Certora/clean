/-
  Assertions on memory states, in the style of separation logic — port of
  `common/Separation.v`.

  An assertion (`MAssert`, Rocq `massert`) is a predicate over memory states
  together with a footprint (a set of `(block, offset)` locations), a proof
  that the predicate is invariant under changes outside the footprint, and a
  proof that the footprint only contains valid blocks.  Separating
  conjunction (`P ** Q`, Rocq `sepconj`) requires disjoint footprints.  As in
  CompCert, this is not a full separation logic (there is no program logic):
  it is the library `backend/Stackingproof.v` uses to describe stack frames.

  Notations (scoped in `CC.Separation`): `m ⊨ P` for `P.pred m` (Rocq
  `m |= P`) and `P ** Q` for `sepconj P Q`.

  Differences from Rocq:
  * `Mem.perm`, `Mem.validAccess` are boolean-valued, hence the `= true`.
  * `massert_imp` / `massert_eqv` are not registered as setoid relations;
    the rewriting lemmas are used through `MAssert.Imp.pred` / `sep_imp`.
-/
import CCLib.common.MemoryUnchanged
import CCLib.common.MemoryLemmas
import CCLib.cfrontend.CtypesTheory
import CCLib.common.MemoryInjections
import CCLib.common.EventsInject
import CCLib.common.EventsMem

namespace CC
namespace Separation

open Mem

/-- `Separation.massert` -/
structure MAssert where
  /-- the predicate over memory states (`m_pred`) -/
  pred : Mem → Prop
  /-- the footprint (`m_footprint`) -/
  footprint : Block → _root_.Int → Prop
  /-- invariance outside the footprint (`m_invar`) -/
  invar : ∀ m m', pred m → Mem.UnchangedOn footprint m m' → pred m'
  /-- the footprint only contains valid blocks (`m_valid`) -/
  valid : ∀ m b ofs, pred m → footprint b ofs → validBlock m b = true

/-- `m ⊨ P` (Rocq `m |= P`): memory state `m` satisfies the assertion `P`. -/
scoped notation:50 m:51 " ⊨ " P:51 => MAssert.pred P m

/-- `Separation.massert_imp` -/
def MAssert.Imp (P Q : MAssert) : Prop :=
  (∀ m, P.pred m → Q.pred m) ∧ (∀ b ofs, Q.footprint b ofs → P.footprint b ofs)

/-- `Separation.massert_eqv` -/
def MAssert.Eqv (P Q : MAssert) : Prop := P.Imp Q ∧ Q.Imp P

/-- `massert_imp_refl` -/
theorem MAssert.Imp.refl (P : MAssert) : P.Imp P := ⟨fun _ h => h, fun _ _ h => h⟩

/-- `massert_imp_trans` -/
theorem MAssert.Imp.trans {P Q R : MAssert} (h1 : P.Imp Q) (h2 : Q.Imp R) : P.Imp R :=
  ⟨fun m h => h2.1 m (h1.1 m h), fun b o h => h1.2 b o (h2.2 b o h)⟩

/-- `massert_eqv_refl` -/
theorem MAssert.Eqv.refl (P : MAssert) : P.Eqv P := ⟨.refl P, .refl P⟩

/-- `massert_eqv_sym` -/
theorem MAssert.Eqv.symm {P Q : MAssert} (h : P.Eqv Q) : Q.Eqv P := ⟨h.2, h.1⟩

/-- `massert_eqv_trans` -/
theorem MAssert.Eqv.trans {P Q R : MAssert} (h1 : P.Eqv Q) (h2 : Q.Eqv R) : P.Eqv R :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

/-- `m_pred_morph_1` -/
theorem MAssert.Imp.pred {P Q : MAssert} (h : P.Imp Q) {m : Mem} (hP : m ⊨ P) : m ⊨ Q :=
  h.1 m hP

/-- `m_pred_morph_2` -/
theorem MAssert.Eqv.pred {P Q : MAssert} (h : P.Eqv Q) {m : Mem} : (m ⊨ P) ↔ (m ⊨ Q) :=
  ⟨h.1.1 m, h.2.1 m⟩

/-! ## Separating conjunction -/

/-- `Separation.disjoint_footprint` -/
def disjointFootprint (P Q : MAssert) : Prop :=
  ∀ b ofs, P.footprint b ofs → Q.footprint b ofs → False

/-- `Separation.sepconj` -/
def sepconj (P Q : MAssert) : MAssert where
  pred m := P.pred m ∧ Q.pred m ∧ disjointFootprint P Q
  footprint b ofs := P.footprint b ofs ∨ Q.footprint b ofs
  invar m m' h hu :=
    ⟨P.invar m m' h.1 (hu.implies fun _ _ h _ => .inl h),
     Q.invar m m' h.2.1 (hu.implies fun _ _ h _ => .inr h), h.2.2⟩
  valid m b ofs h hf := hf.elim (P.valid m b ofs h.1) (Q.valid m b ofs h.2.1)

@[inherit_doc] scoped infixr:60 " ** " => sepconj

@[simp] theorem sepconj_pred (P Q : MAssert) (m : Mem) :
    (m ⊨ P ** Q) ↔ (m ⊨ P) ∧ (m ⊨ Q) ∧ disjointFootprint P Q := Iff.rfl

@[simp] theorem sepconj_footprint (P Q : MAssert) (b : Block) (ofs : _root_.Int) :
    (P ** Q).footprint b ofs ↔ P.footprint b ofs ∨ Q.footprint b ofs := Iff.rfl

/-- `sepconj_morph_1` -/
theorem sepconj_imp {P1 P2 Q1 Q2 : MAssert} (hP : P1.Imp P2) (hQ : Q1.Imp Q2) :
    (P1 ** Q1).Imp (P2 ** Q2) :=
  ⟨fun m ⟨a, b, c⟩ => ⟨hP.1 m a, hQ.1 m b, fun b o h1 h2 => c b o (hP.2 b o h1) (hQ.2 b o h2)⟩,
   fun b o h => h.elim (fun h => .inl (hP.2 b o h)) (fun h => .inr (hQ.2 b o h))⟩

/-- `sepconj_morph_2` -/
theorem sepconj_eqv {P1 P2 Q1 Q2 : MAssert} (hP : P1.Eqv P2) (hQ : Q1.Eqv Q2) :
    (P1 ** Q1).Eqv (P2 ** Q2) :=
  ⟨sepconj_imp hP.1 hQ.1, sepconj_imp hP.2 hQ.2⟩

/-- `Separation.sep_imp` -/
theorem sep_imp {P P' Q Q' : MAssert} {m : Mem} (h : m ⊨ P ** Q) (hP : P.Imp P')
    (hQ : Q.Imp Q') : m ⊨ P' ** Q' :=
  (sepconj_imp hP hQ).pred h

/-- `Separation.sep_comm_1` -/
theorem sep_comm_1 (P Q : MAssert) : (P ** Q).Imp (Q ** P) :=
  ⟨fun _ ⟨a, b, c⟩ => ⟨b, a, fun b o h1 h2 => c b o h2 h1⟩, fun _ _ h => h.symm⟩

/-- `Separation.sep_comm` -/
theorem sep_comm (P Q : MAssert) : (P ** Q).Eqv (Q ** P) := ⟨sep_comm_1 P Q, sep_comm_1 Q P⟩

/-- `Separation.sep_assoc_1` -/
theorem sep_assoc_1 (P Q R : MAssert) : ((P ** Q) ** R).Imp (P ** (Q ** R)) := by
  refine ⟨fun m ⟨⟨a, b, c⟩, d, e⟩ => ⟨a, ⟨b, d, fun x o h1 h2 => e x o (.inr h1) h2⟩, ?_⟩,
    fun x o h => ?_⟩
  · intro x o h1 h2
    rcases h2 with h2 | h2
    · exact c x o h1 h2
    · exact e x o (.inl h1) h2
  · rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h

/-- `Separation.sep_assoc_2` -/
theorem sep_assoc_2 (P Q R : MAssert) : (P ** (Q ** R)).Imp ((P ** Q) ** R) := by
  refine ⟨fun m ⟨a, ⟨b, d, e⟩, c⟩ => ⟨⟨a, b, fun x o h1 h2 => c x o h1 (.inl h2)⟩, d, ?_⟩,
    fun x o h => ?_⟩
  · intro x o h1 h2
    rcases h1 with h1 | h1
    · exact c x o h1 (.inr h2)
    · exact e x o h1 h2
  · rcases h with (h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

/-- `Separation.sep_assoc` -/
theorem sep_assoc (P Q R : MAssert) : ((P ** Q) ** R).Eqv (P ** (Q ** R)) :=
  ⟨sep_assoc_1 P Q R, sep_assoc_2 P Q R⟩

/-- `Separation.sep_swap` -/
theorem sep_swap (P Q R : MAssert) : (P ** Q ** R).Eqv (Q ** P ** R) :=
  ((sep_assoc P Q R).symm.trans (sepconj_eqv (sep_comm P Q) (.refl R))).trans (sep_assoc Q P R)

/-- `Separation.sep_swap12` -/
theorem sep_swap12 (P Q R : MAssert) : (P ** Q ** R).Eqv (Q ** P ** R) := sep_swap P Q R

/-- `Separation.sep_swap23` -/
theorem sep_swap23 (P Q R S : MAssert) : (P ** Q ** R ** S).Eqv (P ** R ** Q ** S) :=
  sepconj_eqv (.refl P) (sep_swap Q R S)

/-- `Separation.sep_swap34` -/
theorem sep_swap34 (P Q R S T : MAssert) :
    (P ** Q ** R ** S ** T).Eqv (P ** Q ** S ** R ** T) :=
  sepconj_eqv (.refl P) (sep_swap23 Q R S T)

/-- `Separation.sep_swap45` -/
theorem sep_swap45 (P Q R S T U : MAssert) :
    (P ** Q ** R ** S ** T ** U).Eqv (P ** Q ** R ** T ** S ** U) :=
  sepconj_eqv (.refl P) (sep_swap34 Q R S T U)

/-- `Separation.sep_swap2` -/
theorem sep_swap2 (P Q R : MAssert) : (P ** Q ** R).Eqv (Q ** P ** R) := sep_swap P Q R

/-- `Separation.sep_swap3` -/
theorem sep_swap3 (P Q R S : MAssert) : (P ** Q ** R ** S).Eqv (R ** Q ** P ** S) :=
  ((sep_swap P Q (R ** S)).trans (sepconj_eqv (.refl Q) (sep_swap P R S))).trans
    (sep_swap Q R (P ** S))

/-- `Separation.sep_swap4` -/
theorem sep_swap4 (P Q R S T : MAssert) :
    (P ** Q ** R ** S ** T).Eqv (S ** Q ** R ** P ** T) :=
  ((sep_swap P Q (R ** S ** T)).trans (sepconj_eqv (.refl Q) (sep_swap3 P R S T))).trans
    (sep_swap Q S (R ** P ** T))

/-- `Separation.sep_swap5` -/
theorem sep_swap5 (P Q R S T U : MAssert) :
    (P ** Q ** R ** S ** T ** U).Eqv (T ** Q ** R ** S ** P ** U) :=
  ((sep_swap P Q (R ** S ** T ** U)).trans (sepconj_eqv (.refl Q) (sep_swap4 P R S T U))).trans
    (sep_swap Q T (R ** S ** P ** U))

/-- `Separation.sep_drop` -/
theorem sep_drop {P Q : MAssert} {m : Mem} (h : m ⊨ P ** Q) : m ⊨ Q := h.2.1

/-- `Separation.sep_drop2` -/
theorem sep_drop2 {P Q R : MAssert} {m : Mem} (h : m ⊨ P ** Q ** R) : m ⊨ P ** R :=
  sep_drop ((sep_swap P Q R).1.pred h)

/-- `Separation.sep_proj1` -/
theorem sep_proj1 {P Q : MAssert} {m : Mem} (h : m ⊨ P ** Q) : m ⊨ P := h.1

/-- `Separation.sep_proj2` -/
theorem sep_proj2 {P Q : MAssert} {m : Mem} (h : m ⊨ P ** Q) : m ⊨ Q := h.2.1

/-- `Separation.sep_pick1` -/
theorem sep_pick1 {P Q : MAssert} {m : Mem} (h : m ⊨ P ** Q) : m ⊨ P := h.1

/-- `Separation.sep_pick2` -/
theorem sep_pick2 {P Q R : MAssert} {m : Mem} (h : m ⊨ P ** Q ** R) : m ⊨ Q := h.2.1.1

/-- `Separation.sep_pick3` -/
theorem sep_pick3 {P Q R S : MAssert} {m : Mem} (h : m ⊨ P ** Q ** R ** S) : m ⊨ R :=
  h.2.1.2.1.1

/-- `Separation.sep_pick4` -/
theorem sep_pick4 {P Q R S T : MAssert} {m : Mem} (h : m ⊨ P ** Q ** R ** S ** T) : m ⊨ S :=
  h.2.1.2.1.2.1.1

/-- `Separation.sep_pick5` -/
theorem sep_pick5 {P Q R S T U : MAssert} {m : Mem} (h : m ⊨ P ** Q ** R ** S ** T ** U) :
    m ⊨ T :=
  h.2.1.2.1.2.1.2.1.1

/-- `Separation.sep_preserved` -/
theorem sep_preserved {m m' : Mem} {P Q : MAssert} (h : m ⊨ P ** Q) (hP : (m ⊨ P) → m' ⊨ P)
    (hQ : (m ⊨ Q) → m' ⊨ Q) : m' ⊨ P ** Q :=
  ⟨hP h.1, hQ h.2.1, h.2.2⟩

/-! ## Basic memory assertions -/

/-- `Separation.pure`: a pure logical assertion. -/
def pure (P : Prop) : MAssert where
  pred _ := P
  footprint _ _ := False
  invar _ _ h _ := h
  valid _ _ _ _ h := h.elim

/-- `Separation.sep_pure` -/
theorem sep_pure (P : Prop) (Q : MAssert) (m : Mem) : (m ⊨ pure P ** Q) ↔ P ∧ (m ⊨ Q) :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun _ _ h _ => h⟩⟩

/-- `Separation.range`: a range of bytes, with full permissions and unspecified
contents. -/
def range (b : Block) (lo hi : _root_.Int) : MAssert where
  pred m := 0 ≤ lo ∧ hi ≤ Integers.Ptrofs.modulus ∧
    (∀ i k p, lo ≤ i → i < hi → Mem.perm m b i k p = true)
  footprint b' ofs' := b' = b ∧ lo ≤ ofs' ∧ ofs' < hi
  invar m m' h hu := ⟨h.1, h.2.1, fun i k p h1 h2 =>
    hu.perm_1 ⟨rfl, h1, h2⟩ (h.2.2 i k p h1 h2)⟩
  valid m b' ofs h hf := by
    obtain ⟨rfl, h1, h2⟩ := hf
    exact validBlock_of_perm (h.2.2 ofs .Cur .Freeable h1 h2)

/-- `Separation.alloc_rule` -/
theorem alloc_rule {m : Mem} {lo hi : _root_.Int} {b : Block} {m' : Mem} {P : MAssert}
    (ha : alloc m lo hi = (m', b)) (hlo : 0 ≤ lo) (hhi : hi ≤ Integers.Ptrofs.modulus)
    (hP : m ⊨ P) : m' ⊨ range b lo hi ** P := by
  have e1 : (alloc m lo hi).1 = m' := by rw [ha]
  have e2 : (alloc m lo hi).2 = b := by rw [ha]
  rw [alloc_result] at e2
  subst e1 e2
  refine ⟨⟨hlo, hhi, fun i k p h1 h2 => ?_⟩, P.invar _ _ hP (alloc_unchangedOn ha), ?_⟩
  · exact perm_implies (perm_alloc_same m lo hi i k h1 h2) (by cases p <;> decide)
  · intro b' ofs ⟨hb, _, _⟩ hf
    subst hb
    have := P.valid _ _ _ hP hf
    rw [fresh_block_alloc] at this
    cases this

/-- `Separation.range_split` -/
theorem range_split {b : Block} {lo hi : _root_.Int} {P : MAssert} {mid : _root_.Int} {m : Mem}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) (h : m ⊨ range b lo hi ** P) :
    m ⊨ range b lo mid ** range b mid hi ** P := by
  refine (sep_assoc _ _ _).1.pred (sep_imp h ⟨fun m hr => ?_, fun b' o hf => ?_⟩ (.refl P))
  · obtain ⟨a, c, d⟩ := hr
    refine ⟨⟨a, by omega, fun i k p h3 h4 => d i k p h3 (by omega)⟩,
      ⟨by omega, c, fun i k p h3 h4 => d i k p (by omega) h4⟩, ?_⟩
    intro x o ⟨_, _, h5⟩ ⟨_, h6, _⟩
    omega
  · rcases hf with ⟨e, h3, h4⟩ | ⟨e, h3, h4⟩
    · exact ⟨e, h3, by omega⟩
    · exact ⟨e, by omega, h4⟩

/-- `Separation.range_drop_left` -/
theorem range_drop_left {b : Block} {lo hi : _root_.Int} {P : MAssert} {mid : _root_.Int} {m : Mem}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) (h : m ⊨ range b lo hi ** P) :
    m ⊨ range b mid hi ** P :=
  sep_drop (range_split h1 h2 h)

/-- `Separation.range_drop_right` -/
theorem range_drop_right {b : Block} {lo hi : _root_.Int} {P : MAssert} {mid : _root_.Int} {m : Mem}
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) (h : m ⊨ range b lo hi ** P) :
    m ⊨ range b lo mid ** P :=
  sep_drop2 (range_split h1 h2 h)

/-- `Separation.range_split_2` -/
theorem range_split_2 {b : Block} {lo hi : _root_.Int} {P : MAssert} {mid al : _root_.Int}
    {m : Mem} (h1 : lo ≤ align mid al) (h2 : align mid al ≤ hi) (hal : al > 0)
    (h : m ⊨ range b lo hi ** P) :
    m ⊨ range b lo mid ** range b (align mid al) hi ** P := by
  have hm : mid ≤ align mid al := align_le mid al hal
  refine (sep_assoc _ _ _).1.pred (sep_imp h ⟨fun m hr => ?_, fun b' o hf => ?_⟩ (.refl P))
  · obtain ⟨a, c, d⟩ := hr
    refine ⟨⟨a, Int.le_trans hm (Int.le_trans h2 c),
        fun i k p h3 h4 => d i k p h3 (Int.lt_of_lt_of_le h4 (Int.le_trans hm h2))⟩,
      ⟨Int.le_trans a h1, c, fun i k p h3 h4 => d i k p (Int.le_trans h1 h3) h4⟩, ?_⟩
    intro x o ⟨_, _, h5⟩ ⟨_, h6, _⟩
    exact Int.lt_irrefl _ (Int.lt_of_lt_of_le h5 (Int.le_trans hm h6))
  · rcases hf with ⟨e, h3, h4⟩ | ⟨e, h3, h4⟩
    · exact ⟨e, h3, Int.lt_of_lt_of_le h4 (Int.le_trans hm h2)⟩
    · exact ⟨e, Int.le_trans h1 h3, h4⟩

/-- `Separation.range_preserved` -/
theorem range_preserved {m m' : Mem} {b : Block} {lo hi : _root_.Int} (h : m ⊨ range b lo hi)
    (hp : ∀ i k p, lo ≤ i → i < hi → Mem.perm m b i k p = true → Mem.perm m' b i k p = true) :
    m' ⊨ range b lo hi :=
  ⟨h.1, h.2.1, fun i k p h1 h2 => hp i k p h1 h2 (h.2.2 i k p h1 h2)⟩

/-- `Separation.contains`: a memory area that contains a value satisfying a
given predicate. -/
def contains (chunk : Chunk) (b : Block) (ofs : _root_.Int) (spec : Val → Prop) : MAssert where
  pred m := 0 ≤ ofs ∧ ofs + sizeChunk chunk ≤ Integers.Ptrofs.modulus ∧
    validAccess m chunk b ofs .Freeable = true ∧
    ∃ v, load chunk m b ofs = some v ∧ spec v
  footprint b' ofs' := b' = b ∧ ofs ≤ ofs' ∧ ofs' < ofs + sizeChunk chunk
  invar m m' h hu := by
    obtain ⟨h1, h2, h3, v, h4, h5⟩ := h
    refine ⟨h1, h2, ?_, v, hu.load (fun i a c => ⟨rfl, a, c⟩) h4, h5⟩
    simp only [validAccess, Bool.and_eq_true] at h3 ⊢
    exact ⟨hu.rangePerm (fun i a c => ⟨rfl, a, c⟩) h3.1, h3.2⟩
  valid m b' ofs' h hf := by
    obtain ⟨rfl, h1, h2⟩ := hf
    have h3 := h.2.2.1
    simp only [validAccess, Bool.and_eq_true] at h3
    exact validBlock_of_perm (rangePerm_perm m _ _ _ _ _ h3.1 ofs' h1 h2)

/-- `Separation.contains_no_overflow` -/
theorem contains_no_overflow {spec : Val → Prop} {m : Mem} {chunk : Chunk} {b : Block}
    {ofs : _root_.Int} (h : m ⊨ contains chunk b ofs spec) :
    0 ≤ ofs ∧ ofs ≤ Integers.Ptrofs.max_unsigned := by
  obtain ⟨h1, h2, _⟩ := h
  have := sizeChunk_pos chunk
  simp only [Integers.Ptrofs.max_unsigned, Integers.MI.max_unsigned] at *
  simp only [Integers.Ptrofs.modulus] at h2
  omega

/-- `Separation.load_rule` -/
theorem load_rule {spec : Val → Prop} {m : Mem} {chunk : Chunk} {b : Block} {ofs : _root_.Int}
    (h : m ⊨ contains chunk b ofs spec) : ∃ v, load chunk m b ofs = some v ∧ spec v :=
  h.2.2.2

/-- `Separation.loadv_rule` -/
theorem loadv_rule {spec : Val → Prop} {m : Mem} {chunk : Chunk} {b : Block} {ofs : _root_.Int}
    (h : m ⊨ contains chunk b ofs spec) :
    ∃ v, loadv chunk m (.Vptr b (Integers.Ptrofs.repr ofs)) = some v ∧ spec v := by
  have ⟨n1, n2⟩ := contains_no_overflow h
  have eq : Integers.Ptrofs.unsigned (Integers.Ptrofs.repr ofs) = ofs :=
    Integers.Ptrofs.unsigned_repr n1 n2
  obtain ⟨v, h1, h2⟩ := load_rule h
  refine ⟨v, ?_, h2⟩
  simp only [loadv, eq]
  rw [if_pos h.2.1]
  exact h1

/-- `Separation.store_rule` -/
theorem store_rule {chunk : Chunk} {m : Mem} {b : Block} {ofs : _root_.Int} {v : Val}
    {spec1 spec : Val → Prop} {P : MAssert} (h : m ⊨ contains chunk b ofs spec1 ** P)
    (hspec : spec (Val.loadResult chunk v)) :
    ∃ m', store chunk m b ofs v = some m' ∧ m' ⊨ contains chunk b ofs spec ** P := by
  obtain ⟨⟨d, e, e', _⟩, hP, c⟩ := h
  have hw : validAccess m chunk b ofs .Writable = true := validAccess_implies e' (by decide)
  obtain ⟨m', hs⟩ := valid_access_store v hw
  refine ⟨m', hs, ⟨d, e, ?_, _, load_store_same hs, hspec⟩, ?_, ?_⟩
  · rw [validAccess_store_eq hs]; exact e'
  · exact P.invar _ _ hP (store_unchangedOn hs fun i a b' hi => c _ _ ⟨rfl, a, b'⟩ hi)
  · exact c

/-- `Separation.storev_rule` -/
theorem storev_rule {chunk : Chunk} {m : Mem} {b : Block} {ofs : _root_.Int} {v : Val}
    {spec1 spec : Val → Prop} {P : MAssert} (h : m ⊨ contains chunk b ofs spec1 ** P)
    (hspec : spec (Val.loadResult chunk v)) :
    ∃ m', storev chunk m (.Vptr b (Integers.Ptrofs.repr ofs)) v = some m' ∧
      m' ⊨ contains chunk b ofs spec ** P := by
  obtain ⟨m', h1, h2⟩ := store_rule h hspec
  have ⟨n1, n2⟩ := contains_no_overflow (sep_pick1 h)
  have eq : Integers.Ptrofs.unsigned (Integers.Ptrofs.repr ofs) = ofs :=
    Integers.Ptrofs.unsigned_repr n1 n2
  refine ⟨m', ?_, h2⟩
  simp only [storev, eq]
  rw [if_pos (sep_pick1 h).2.1]
  exact h1

/-- `Separation.range_contains` -/
theorem range_contains {chunk : Chunk} {b : Block} {ofs : _root_.Int} {P : MAssert} {m : Mem}
    (h : m ⊨ range b ofs (ofs + sizeChunk chunk) ** P) (hal : alignChunk chunk ∣ ofs) :
    m ⊨ contains chunk b ofs (fun _ => True) ** P := by
  obtain ⟨⟨d, e, f⟩, hP, c⟩ := h
  have hva : validAccess m chunk b ofs .Freeable = true := by
    simp only [validAccess, Bool.and_eq_true, beq_iff_eq]
    exact ⟨rangePerm_intro m b _ _ _ _ fun i h1 h2 => f i _ _ h1 h2,
      Int.emod_eq_zero_of_dvd hal⟩
  obtain ⟨v, hl⟩ := valid_access_load (validAccess_implies hva (by decide))
  exact ⟨⟨d, e, hva, v, hl, trivial⟩, hP, c⟩

/-- `Separation.contains_imp` -/
theorem contains_imp {spec1 spec2 : Val → Prop} (chunk : Chunk) (b : Block) (ofs : _root_.Int)
    (h : ∀ v, spec1 v → spec2 v) : (contains chunk b ofs spec1).Imp (contains chunk b ofs spec2) :=
  ⟨fun _ ⟨a, c, d, v, e, f⟩ => ⟨a, c, d, v, e, h v f⟩, fun _ _ h => h⟩

/-- `Separation.hasvalue`: a memory area that contains a given value. -/
def hasvalue (chunk : Chunk) (b : Block) (ofs : _root_.Int) (v : Val) : MAssert :=
  contains chunk b ofs (fun v' => v' = v)

/-- `Separation.store_rule'` -/
theorem store_rule' {chunk : Chunk} {m : Mem} {b : Block} {ofs : _root_.Int} {v : Val}
    {spec1 : Val → Prop} {P : MAssert} (h : m ⊨ contains chunk b ofs spec1 ** P) :
    ∃ m', store chunk m b ofs v = some m' ∧
      m' ⊨ hasvalue chunk b ofs (Val.loadResult chunk v) ** P :=
  store_rule h rfl

/-- `Separation.storev_rule'` -/
theorem storev_rule' {chunk : Chunk} {m : Mem} {b : Block} {ofs : _root_.Int} {v : Val}
    {spec1 : Val → Prop} {P : MAssert} (h : m ⊨ contains chunk b ofs spec1 ** P) :
    ∃ m', storev chunk m (.Vptr b (Integers.Ptrofs.repr ofs)) v = some m' ∧
      m' ⊨ hasvalue chunk b ofs (Val.loadResult chunk v) ** P :=
  storev_rule h rfl

/-! ## Non-separating conjunction -/

/-- `Separation.mconj` -/
def mconj (P Q : MAssert) : MAssert where
  pred m := P.pred m ∧ Q.pred m
  footprint b ofs := P.footprint b ofs ∨ Q.footprint b ofs
  invar m m' h hu :=
    ⟨P.invar m m' h.1 (hu.implies fun _ _ h _ => .inl h),
     Q.invar m m' h.2 (hu.implies fun _ _ h _ => .inr h)⟩
  valid m b ofs h hf := hf.elim (P.valid m b ofs h.1) (Q.valid m b ofs h.2)

/-- `Separation.mconj_intro` -/
theorem mconj_intro {P Q R : MAssert} {m : Mem} (h1 : m ⊨ P ** R) (h2 : m ⊨ Q ** R) :
    m ⊨ mconj P Q ** R :=
  ⟨⟨h1.1, h2.1⟩, h1.2.1, fun b o hf hR => hf.elim (fun h => h1.2.2 b o h hR)
    (fun h => h2.2.2 b o h hR)⟩

/-- `Separation.mconj_proj1` -/
theorem mconj_proj1 {P Q R : MAssert} {m : Mem} (h : m ⊨ mconj P Q ** R) : m ⊨ P ** R :=
  ⟨h.1.1, h.2.1, fun b o hP hR => h.2.2 b o (.inl hP) hR⟩

/-- `Separation.mconj_proj2` -/
theorem mconj_proj2 {P Q R : MAssert} {m : Mem} (h : m ⊨ mconj P Q ** R) : m ⊨ Q ** R :=
  ⟨h.1.2, h.2.1, fun b o hQ hR => h.2.2 b o (.inr hQ) hR⟩

/-- `Separation.frame_mconj` -/
theorem frame_mconj {P P' Q R : MAssert} {m m' : Mem} (h : m ⊨ mconj P Q ** R)
    (h' : m' ⊨ P' ** R) (hQ : m' ⊨ Q) : m' ⊨ mconj P' Q ** R :=
  ⟨⟨h'.1, hQ⟩, h'.2.1, fun b o hf hR => hf.elim (fun hp => h'.2.2 b o hp hR)
    (fun hq => h.2.2 b o (.inr hq) hR)⟩

/-- `mconj_morph_1` -/
theorem mconj_imp {P1 P2 Q1 Q2 : MAssert} (hP : P1.Imp P2) (hQ : Q1.Imp Q2) :
    (mconj P1 Q1).Imp (mconj P2 Q2) :=
  ⟨fun m h => ⟨hP.1 m h.1, hQ.1 m h.2⟩,
   fun b o h => h.elim (fun h => .inl (hP.2 b o h)) (fun h => .inr (hQ.2 b o h))⟩

/-- `mconj_morph_2` -/
theorem mconj_eqv {P1 P2 Q1 Q2 : MAssert} (hP : P1.Eqv P2) (hQ : Q1.Eqv Q2) :
    (mconj P1 Q1).Eqv (mconj P2 Q2) :=
  ⟨mconj_imp hP.1 hQ.1, mconj_imp hP.2 hQ.2⟩

/-! ## The image of a memory injection -/

/-- `Separation.minjection`: memory states `m` such that `j` injects `m0` into
`m`; the footprint is the image of the nonempty locations of `m0`. -/
def minjection (j : Val.Meminj) (m0 : Mem) : MAssert where
  pred m := Inject j m0 m
  footprint b ofs := ∃ b0 delta, j b0 = some (b, delta) ∧
    Mem.perm m0 b0 (ofs - delta) .Max .Nonempty = true
  invar m m' h hu := by
    have img : ∀ {b1 b2 delta ofs k p}, j b1 = some (b2, delta) →
        Mem.perm m0 b1 ofs k p = true →
        ∃ b0 d, j b0 = some (b2, d) ∧ Mem.perm m0 b0 (ofs + delta - d) .Max .Nonempty = true :=
      fun {b1 b2 delta ofs k p} hj hp => ⟨b1, delta, hj, by
        rw [Int.add_sub_cancel]
        exact perm_max (perm_implies hp (by cases p <;> rfl))⟩
    refine ⟨⟨fun b1 b2 delta ofs k p hj hp => hu.perm_1 (img hj hp) (h.inj.perm _ _ _ _ _ _ hj hp),
      h.inj.align, fun b1 ofs b2 delta hj hp => ?_⟩, h.freeblocks,
      fun b b' d hj => hu.valid_block (h.mappedblocks b b' d hj), h.no_overlap, h.representable,
      fun b1 ofs b2 delta k p hj hp => ?_, h.metadata⟩
    · rw [hu.contents_eq _ _ (img hj hp) (h.inj.perm _ _ _ _ _ _ hj hp)]
      exact h.inj.memval _ _ _ _ hj hp
    · cases hne : Mem.perm m0 b1 ofs .Max .Nonempty
      · exact .inr rfl
      · rcases h.perm_inv _ _ _ _ _ _ hj (hu.perm_2 (img hj hne)
          (h.mappedblocks _ _ _ hj) hp) with h' | h'
        · exact .inl h'
        · rw [hne] at h'; cases h'
  valid m b ofs h hf := by
    obtain ⟨b0, d, hj, _⟩ := hf
    exact h.mappedblocks _ _ _ hj

/-- `Separation.loadv_parallel_rule` -/
theorem loadv_parallel_rule {j : Val.Meminj} {m1 m2 : Mem} {chunk : Chunk} {addr1 v1 addr2 : Val}
    (h : m2 ⊨ minjection j m1) (hl : loadv chunk m1 addr1 = some v1)
    (ha : Val.Inject j addr1 addr2) :
    ∃ v2, loadv chunk m2 addr2 = some v2 ∧ Val.Inject j v1 v2 :=
  loadv_inject h hl ha

/-- `Separation.storev_parallel_rule` -/
theorem storev_parallel_rule {j : Val.Meminj} {m1 m2 : Mem} {P : MAssert} {chunk : Chunk}
    {addr1 v1 : Val} {m1' : Mem} {addr2 v2 : Val}
    (h : m2 ⊨ minjection j m1 ** P) (hs : storev chunk m1 addr1 v1 = some m1')
    (ha : Val.Inject j addr1 addr2) (hv : Val.Inject j v1 v2) :
    ∃ m2', storev chunk m2 addr2 v2 = some m2' ∧ m2' ⊨ minjection j m1' ** P := by
  obtain ⟨A, B, C⟩ := h
  obtain ⟨m2', hs2, INJ⟩ := storev_mapped_inject A hs ha hv
  refine ⟨m2', hs2, INJ, ?_, ?_⟩
  · cases ha with
    | ptr delta hf ho =>
      subst ho
      simp only [storev] at hs hs2
      split at hs
      · split at hs2
        · have VALID := store_valid_access hs
          have EQ := address_inject' A VALID hf
          rw [EQ] at hs2
          refine P.invar _ _ B (store_unchangedOn hs2 fun i h1 h2 hi => C _ _ ⟨_, delta, hf, ?_⟩ hi)
          simp only [validAccess, Bool.and_eq_true] at VALID
          exact perm_cur_max (perm_implies (rangePerm_perm _ _ _ _ _ _ VALID.1 (i - delta)
            (by omega) (by omega)) (by decide))
        · cases hs2
      · cases hs
    | _ => simp [storev] at hs
  · intro b ofs ⟨b0, d0, hj, hp⟩ hP
    cases ha with
    | ptr delta hf ho =>
      simp only [storev] at hs
      split at hs
      · exact C b ofs ⟨b0, d0, hj, by rw [perm_store hs] at hp; exact hp⟩ hP
      · cases hs
    | _ => simp [storev] at hs

/-- `Separation.alloc_parallel_rule` -/
theorem alloc_parallel_rule {m1 : Mem} {sz1 : _root_.Int} {m1' : Mem} {b1 : Block} {m2 : Mem}
    {sz2 : _root_.Int} {m2' : Mem} {b2 : Block} {P : MAssert} {j : Val.Meminj}
    {lo hi delta : _root_.Int}
    (SEP : m2 ⊨ minjection j m1 ** P) (ALLOC1 : alloc m1 0 sz1 = (m1', b1))
    (ALLOC2 : alloc m2 0 sz2 = (m2', b2)) (ALIGN : (8 : _root_.Int) ∣ delta)
    (LO : lo = delta) (HI : hi = delta + max 0 sz1)
    (RANGE1 : 0 ≤ sz2 ∧ sz2 ≤ Integers.Ptrofs.max_unsigned) (RANGE2 : 0 ≤ delta)
    (RANGE3 : hi ≤ sz2) :
    ∃ j', (m2' ⊨ range b2 0 lo ** range b2 hi sz2 ** minjection j' m1' ** P) ∧
      Val.inject_incr j j' ∧ j' b1 = some (b2, delta) ∧ (∀ b, b ≠ b1 → j' b = j b) := by
  subst LO HI
  have hmax : @Eq _root_.Int Integers.Ptrofs.max_unsigned (Integers.Ptrofs.modulus - 1) :=
    max_unsigned_eq
  have hsz1 : sz1 ≤ max 0 sz1 := Int.le_max_right _ _
  have hsz0 : (0 : _root_.Int) ≤ max 0 sz1 := Int.le_max_left _ _
  obtain ⟨INJ, SP, DISJ⟩ := SEP
  obtain ⟨rfl, rfl⟩ := alloc_eq ALLOC2
  have FRESH2 : validBlock m2 m2.nextblock = false := fresh_block_alloc m2
  have notimg : ∀ b d, j b = some (m2.nextblock, d) → False := fun b d hj => by
    have := INJ.mappedblocks _ _ _ hj
    rw [FRESH2] at this; cases this
  have newperm : ∀ i k p, 0 ≤ i → i < sz2 →
      perm (alloc m2 0 sz2).1 m2.nextblock i k p = true := fun i k p h1 h2 =>
    perm_implies (perm_alloc_same m2 0 sz2 i k h1 h2) (by cases p <;> decide)
  obtain ⟨j', INJ', J1, J2, J3⟩ := alloc_left_mapped_inject (alloc_right_inject INJ ALLOC2)
    (b2 := m2.nextblock) (delta := lo) ALLOC1 (valid_new_block m2 0 sz2)
    ⟨RANGE2, by omega⟩ (.inr (Int.le_refl _))
    (fun ofs k p hp => by
      have := perm_alloc_inv hp
      rw [if_pos rfl] at this
      exact .inr ⟨this.1, by omega⟩)
    (fun ofs k p h1 h2 => newperm _ _ _ (by omega) (by omega))
    (Int.dvd_trans (minSafeAlignment_dvd_8 _) ALIGN)
    (fun b d' ofs k p hj _ _ _ => notimg b d' hj)
  obtain ⟨rfl, rfl⟩ := alloc_eq ALLOC1
  -- the footprint of `minjection j' m1'` in terms of that of `minjection j m1`
  have FP : ∀ b ofs, (minjection j' (alloc m1 0 sz1).1).footprint b ofs →
      (b = m2.nextblock ∧ lo ≤ ofs ∧ ofs < lo + sz1) ∨
        (minjection j m1).footprint b ofs := by
    intro b ofs ⟨b0, d0, hj, hp⟩
    by_cases hb : b0 = m1.nextblock
    · subst hb
      rw [J2] at hj; cases hj
      have := perm_alloc_inv hp
      rw [if_pos rfl] at this
      exact .inl ⟨rfl, by omega, by omega⟩
    · rw [J3 _ hb] at hj
      have := perm_alloc_inv hp
      rw [if_neg hb] at this
      exact .inr ⟨b0, d0, hj, this⟩
  refine ⟨j', ⟨⟨Int.le_refl _, by omega, fun i k p h1 h2 => newperm i k p h1 (by omega)⟩,
    ⟨⟨by omega, by omega, fun i k p h1 h2 => newperm i k p (by omega) h2⟩,
     ⟨INJ', P.invar _ _ SP (alloc_unchangedOn ALLOC2), ?_⟩, ?_⟩, ?_⟩, J1, J2, J3⟩
  · intro b ofs hf hP
    have hv := P.valid _ _ _ SP hP
    rcases FP b ofs hf with ⟨rfl, _, _⟩ | hf'
    · rw [FRESH2] at hv; cases hv
    · exact DISJ b ofs hf' hP
  · intro b ofs ⟨hb, h1, h2⟩ hf
    subst hb
    rcases hf with hf | hP
    · rcases FP _ ofs hf with ⟨_, _, h3⟩ | ⟨b0, d0, hj, _⟩
      · omega
      · exact notimg b0 d0 hj
    · have hv := P.valid _ _ _ SP hP
      rw [FRESH2] at hv; cases hv
  · intro b ofs ⟨hb, h1, h2⟩ hf
    subst hb
    rcases hf with ⟨_, _, h3⟩ | hf | hP
    · omega
    · rcases FP _ ofs hf with ⟨_, h3, _⟩ | ⟨b0, d0, hj, _⟩
      · omega
      · exact notimg b0 d0 hj
    · have hv := P.valid _ _ _ SP hP
      rw [FRESH2] at hv; cases hv

private theorem rw_free_result {m : Mem} {b : Block} {lo hi : _root_.Int} {m' : Mem}
    (hf : free m b lo hi = some m') {b' : Block} {ofs : _root_.Int} {k : PermKind}
    {p : Permission} (hp : perm m' b' ofs k p = true) :
    perm (uncheckedFree m b lo hi) b' ofs k p = true := by
  rw [← free_result hf]; exact hp

/-- `Separation.free_parallel_rule` -/
theorem free_parallel_rule {j : Val.Meminj} {m1 : Mem} {b1 : Block} {sz1 : _root_.Int}
    {m1' m2 : Mem} {b2 : Block} {sz2 lo hi delta : _root_.Int} {P : MAssert}
    (h : m2 ⊨ range b2 0 lo ** range b2 hi sz2 ** minjection j m1 ** P)
    (FREE1 : free m1 b1 0 sz1 = some m1') (hj : j b1 = some (b2, delta))
    (LO : lo = delta) (HI : hi = delta + max 0 sz1) :
    ∃ m2', free m2 b2 0 sz2 = some m2' ∧ m2' ⊨ minjection j m1' ** P := by
  obtain ⟨⟨_, _, J⟩, ⟨⟨_, _, K⟩, ⟨INJ, HP, DISJ3⟩, DISJ2⟩, DISJ1⟩ := h
  have hsz1 : sz1 ≤ max 0 sz1 := Int.le_max_right _ _
  have hmx : max 0 sz1 = 0 ∨ max 0 sz1 = sz1 := by
    rcases Int.le_total 0 sz1 with h | h
    · exact .inr (Int.max_eq_right h)
    · exact .inl (Int.max_eq_left h)
  have hr1 := free_rangePerm FREE1
  -- every offset of `b2` in `[lo, hi)` is in the image of `b1`
  have inimg : ∀ ofs, lo ≤ ofs → ofs < hi →
      0 ≤ ofs - delta ∧ ofs - delta < sz1 := fun ofs h1 h2 => by
    rcases hmx with e | e <;> rw [e] at HI <;> omega
  have hmid : ∀ ofs, lo ≤ ofs → ofs < hi → (minjection j m1).footprint b2 ofs :=
    fun ofs h1 h2 => ⟨b1, delta, hj, perm_cur_max (perm_implies
      (rangePerm_perm _ _ _ _ _ _ hr1 (ofs - delta) (inimg ofs h1 h2).1 (inimg ofs h1 h2).2)
      (by decide))⟩
  have PERM : rangePerm m2 b2 0 sz2 .Cur .Freeable = true := by
    refine rangePerm_intro _ _ _ _ _ _ fun ofs h1 h2 => ?_
    rcases Int.lt_or_le ofs lo with h3 | h3
    · exact J ofs _ _ h1 h3
    rcases Int.lt_or_le ofs hi with h4 | h4
    · have := perm_inject hj INJ (rangePerm_perm _ _ _ _ _ _ hr1 (ofs - delta)
        (inimg ofs h3 h4).1 (inimg ofs h3 h4).2)
      rwa [Int.sub_add_cancel] at this
    · exact K ofs _ _ h4 h2
  refine ⟨_, free_isSome PERM, ?_, ?_, ?_⟩
  · rw [free_result FREE1] at *
    refine free_right_inject (free_left_inject INJ FREE1) (free_isSome PERM) ?_
    intro b1' d ofs k p hj' hp h1 h2
    have himg : (minjection j m1).footprint b2 (ofs + d) :=
      ⟨b1', d, hj', by rw [Int.add_sub_cancel]; exact perm_max (perm_implies
        (perm_free_3 (rw_free_result FREE1 hp)) (by cases p <;> rfl))⟩
    rcases Int.lt_or_le (ofs + d) lo with h3 | h3
    · exact DISJ1 b2 (ofs + d) ⟨rfl, h1, h3⟩ (.inr (.inl himg))
    rcases Int.lt_or_le (ofs + d) hi with h4 | h4
    · by_cases hb : b1' = b1
      · subst hb
        rw [hj] at hj'; cases hj'
        have := inimg _ h3 h4
        rw [free_result FREE1, perm_free_inside m1 b1' 0 sz1 ofs k p (by omega) (by omega)]
          at hp
        cases hp
      · have hq := perm_cur_max (perm_implies (rangePerm_perm _ _ _ _ _ _ hr1 (ofs + d - delta)
          (inimg _ h3 h4).1 (inimg _ h3 h4).2) (show permOrder .Freeable .Nonempty = true by rfl))
        rcases INJ.no_overlap _ _ _ _ _ _ _ _ hb hj' hj
          (perm_max (perm_implies (perm_free_3 (rw_free_result FREE1 hp)) (by cases p <;> rfl)))
          hq with hc | hc
        · exact hc rfl
        · exact hc (by omega)
    · exact DISJ2 b2 (ofs + d) ⟨rfl, h4, h2⟩ (.inl himg)
  · refine P.invar _ _ HP (free_unchangedOn (free_isSome PERM) fun i h1 h2 hPi => ?_)
    rcases Int.lt_or_le i lo with h3 | h3
    · exact DISJ1 b2 i ⟨rfl, h1, h3⟩ (.inr (.inr hPi))
    rcases Int.lt_or_le i hi with h4 | h4
    · exact DISJ3 b2 i (hmid i h3 h4) hPi
    · exact DISJ2 b2 i ⟨rfl, h4, h2⟩ (.inr hPi)
  · intro b ofs ⟨b0, d0, hj0, hp⟩ hPf
    exact DISJ3 b ofs ⟨b0, d0, hj0, perm_free_3 (rw_free_result FREE1 hp)⟩ hPf

/-! ## Preservation of a global environment by a memory injection -/

/-- `Separation.globalenv_preserved` -/
structure GlobalenvPreserved {F V : Type} (ge : Genv F V) (j : Val.Meminj) (bound : Block) :
    Prop where
  /-- `DOMAIN` -/
  domain : ∀ b, b < bound → j b = some (b, 0)
  /-- `IMAGE` -/
  image : ∀ b1 b2 delta, j b1 = some (b2, delta) → b2 < bound → b1 = b2
  /-- `SYMBOLS` -/
  symbols : ∀ id b, Genv.findSymbol ge id = some b → b < bound
  /-- `FUNCTIONS` -/
  functions : ∀ b fd, Genv.findFunctPtr ge b = some fd → b < bound
  /-- `VARINFOS` -/
  varinfos : ∀ b gv, Genv.findVarInfo ge b = some gv → b < bound

/-- `Separation.globalenv_inject` -/
def globalenvInject {F V : Type} (ge : Genv F V) (j : Val.Meminj) : MAssert where
  pred m := ∃ bound, bound ≤ m.nextblock ∧ GlobalenvPreserved ge j bound
  footprint _ _ := False
  invar m m' h hu := by
    obtain ⟨bound, h1, h2⟩ := h
    exact ⟨bound, Nat.le_trans h1 hu.nextblock_le, h2⟩
  valid _ _ _ _ h := h.elim

/-- `Events.meminj_preserves_globals` -/
def MeminjPreservesGlobals {F V : Type} (ge : Genv F V) (f : Val.Meminj) : Prop :=
  (∀ id b, Genv.findSymbol ge id = some b → f b = some (b, 0)) ∧
  (∀ b gv, Genv.findVarInfo ge b = some gv → f b = some (b, 0)) ∧
  (∀ b1 b2 delta gv, Genv.findVarInfo ge b2 = some gv → f b1 = some (b2, delta) → b2 = b1)

/-- `Separation.globalenv_inject_preserves_globals` -/
theorem globalenvInject_preserves_globals {F V : Type} {ge : Genv F V} {j : Val.Meminj}
    {m : Mem} (h : m ⊨ globalenvInject ge j) : MeminjPreservesGlobals ge j := by
  obtain ⟨bound, _, E⟩ := h
  exact ⟨fun id b hs => E.domain b (E.symbols id b hs),
    fun b gv hv => E.domain b (E.varinfos b gv hv),
    fun b1 b2 delta gv hv hj => (E.image b1 b2 delta hj (E.varinfos b2 gv hv)).symm⟩

/-- The symbol-environment form of `globalenv_inject_preserves_globals` used by
the port's external calls (CompCert derives `symbols_inject` from
`meminj_preserves_globals` inside `external_call_mem_inject`). -/
theorem globalenvInject_symbolsInject {F V : Type} {ge : Genv F V} {j : Val.Meminj} {m : Mem}
    (h : m ⊨ globalenvInject ge j) : SymbolsInject j (Genv.toSenv ge) (Genv.toSenv ge) := by
  obtain ⟨bound, _, E⟩ := h
  exact {
    public_eq := fun _ => rfl
    find_mapped := fun id b1 b2 delta hf hs => by
      have := E.domain b1 (E.symbols id b1 hs)
      rw [hf] at this; cases this
      exact ⟨rfl, hs⟩
    find_public := fun id b1 _ hs => ⟨b1, E.domain b1 (E.symbols id b1 hs), hs⟩
    volatile_eq := fun b1 b2 delta hf => by
      show Genv.blockIsVolatile ge b2 = Genv.blockIsVolatile ge b1
      have none_of : ∀ b, ¬ b < bound → Genv.blockIsVolatile ge b = false := by
        intro b hb
        unfold Genv.blockIsVolatile
        cases e : Genv.findVarInfo ge b with
        | none => rfl
        | some gv => exact absurd (E.varinfos b gv e) hb
      by_cases hb2 : b2 < bound
      · rw [E.image b1 b2 delta hf hb2]
      · have hb1 : ¬ b1 < bound := fun hb1 => by
          have := E.domain b1 hb1
          rw [hf] at this; cases this; exact hb2 hb1
        rw [none_of b1 hb1, none_of b2 hb2] }

/-- `Separation.globalenv_inject_incr` -/
theorem globalenvInject_incr {j : Val.Meminj} {m0 : Mem} {F V : Type} {ge : Genv F V} {m : Mem}
    {j' : Val.Meminj} {P : MAssert} (hincr : Val.inject_incr j j')
    (hsep : InjectSeparated j j' m0 m) (h : m ⊨ globalenvInject ge j ** P) :
    m ⊨ globalenvInject ge j' ** P := by
  obtain ⟨⟨bound, D, E⟩, B, C⟩ := h
  refine ⟨⟨bound, D, ⟨fun b hb => hincr _ _ _ (E.domain b hb), ?_, E.symbols, E.functions,
    E.varinfos⟩⟩, B, fun _ _ h _ => h.elim⟩
  intro b1 b2 delta hj hb2
  cases hjb : j b1 with
  | some p =>
    obtain ⟨b0, d0⟩ := p
    rw [hincr _ _ _ hjb] at hj; cases hj
    exact E.image _ _ _ hjb hb2
  | none =>
    have := (hsep _ _ _ hjb hj).2
    simp only [validBlock, decide_eq_false_iff_not] at this
    exact absurd (Nat.lt_of_lt_of_le hb2 D) this

/-- `Separation.external_call_parallel_rule`.  The properties of external
functions and inline assembly that CompCert takes as axioms (`ec_mem_inject`,
`ec_max_perm`) are hypotheses here. -/
theorem external_call_parallel_rule {F V : Type} (ef : ExtFun) {ge : Genv F V}
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg, ExtcallMemProps (externalFunctionsSem name sg) (Genv.toSenv ge))
    (hasmp : ∀ name sg, ExtcallMemProps (inlineAssemblySem name sg) (Genv.toSenv ge))
    {vargs1 : List Val} {m1 : Mem} {t : Trace} {vres1 : Val} {m1' m2 : Mem} {j : Val.Meminj}
    {P : MAssert} {vargs2 : List Val}
    (CALL : externalCall ef (Genv.toSenv ge) vargs1 m1 t vres1 m1')
    (SEP : m2 ⊨ minjection j m1 ** globalenvInject ge j ** P)
    (ARGS : Val.InjectList j vargs1 vargs2) :
    ∃ j' vres2 m2', externalCall ef (Genv.toSenv ge) vargs2 m2 t vres2 m2' ∧
      Val.Inject j' vres1 vres2 ∧
      (m2' ⊨ minjection j' m1' ** globalenvInject ge j' ** P) ∧
      Val.inject_incr j j' ∧ InjectSeparated j j' m1 m2 := by
  obtain ⟨A, B, C⟩ := SEP
  obtain ⟨j', vres2, m2', CALL', RES, INJ', _, UNCH2, INCR, ISEP⟩ :=
    externalCall_memInject ef hext hasm _ _ _ _ _ _ _ _ _ _
      (globalenvInject_symbolsInject (sep_pick1 B)) CALL A ARGS
  have MAXPERMS : ∀ b ofs p, validBlock m1 b = true → perm m1' b ofs .Max p = true →
      perm m1 b ofs .Max p = true := fun b ofs p hv hp =>
    (externalCall_memProps ef (Genv.toSenv ge) hextp hasmp).maxPerm _ _ _ _ _ b ofs p CALL hv hp
  refine ⟨j', vres2, m2', CALL', RES, ⟨INJ', ?_, ?_⟩, INCR, ISEP⟩
  · refine (globalenvInject ge j' ** P).invar m2 m2' (globalenvInject_incr INCR ISEP B) ?_
    refine UNCH2.implies fun b ofs hf _ b0 delta hj hp => ?_
    exact C b ofs ⟨b0, delta, hj, hp⟩ hf
  · intro b ofs ⟨b0, delta, hj', hp⟩ hf
    cases hj : j b0 with
    | some q =>
      obtain ⟨b', d'⟩ := q
      rw [INCR _ _ _ hj] at hj'; cases hj'
      exact C b ofs ⟨b0, delta, hj, MAXPERMS _ _ _ (validBlock_inject_1 hj A) hp⟩ hf
    | none =>
      have hv := (globalenvInject ge j ** P).valid _ _ _ B hf
      rw [(ISEP _ _ _ hj hj').2] at hv; cases hv

/-- `Separation.alloc_parallel_rule_2` -/
theorem alloc_parallel_rule_2 {F V : Type} {ge : Genv F V} {m1 : Mem} {sz1 : _root_.Int}
    {m1' : Mem} {b1 : Block} {m2 : Mem} {sz2 : _root_.Int} {m2' : Mem} {b2 : Block} {P : MAssert}
    {j : Val.Meminj} {lo hi delta : _root_.Int}
    (SEP : m2 ⊨ minjection j m1 ** globalenvInject ge j ** P)
    (ALLOC1 : alloc m1 0 sz1 = (m1', b1)) (ALLOC2 : alloc m2 0 sz2 = (m2', b2))
    (ALIGN : (8 : _root_.Int) ∣ delta) (LO : lo = delta) (HI : hi = delta + max 0 sz1)
    (RANGE1 : 0 ≤ sz2 ∧ sz2 ≤ Integers.Ptrofs.max_unsigned) (RANGE2 : 0 ≤ delta)
    (RANGE3 : hi ≤ sz2) :
    ∃ j', (m2' ⊨ range b2 0 lo ** range b2 hi sz2 ** minjection j' m1' **
        globalenvInject ge j' ** P) ∧
      Val.inject_incr j j' ∧ j' b1 = some (b2, delta) := by
  obtain ⟨e1, e1'⟩ := alloc_eq ALLOC1
  obtain ⟨e2, e2'⟩ := alloc_eq ALLOC2
  let j1 : Val.Meminj := fun b => if b = b1 then some (b2, delta) else j b
  have X : Val.inject_incr j j1 := by
    intro b b' d hj
    show (if b = b1 then some (b2, delta) else j b) = some (b', d)
    by_cases hb : b = b1
    · subst hb
      have := validBlock_inject_1 hj (sep_pick1 SEP)
      rw [e1', fresh_block_alloc] at this; cases this
    · rw [if_neg hb]; exact hj
  have Y : InjectSeparated j j1 m1 m2 := by
    intro b0 b3 d0 hj hj1
    change (if b0 = b1 then some (b2, delta) else j b0) = some (b3, d0) at hj1
    by_cases hb : b0 = b1
    · rw [if_pos hb] at hj1; cases hj1
      subst hb
      rw [e1', e2']
      exact ⟨fresh_block_alloc m1, fresh_block_alloc m2⟩
    · rw [if_neg hb, hj] at hj1; cases hj1
  have H1 : m2 ⊨ globalenvInject ge j1 ** minjection j m1 ** P :=
    globalenvInject_incr X Y ((sep_swap _ _ _).1.pred SEP)
  have H2 : m2 ⊨ minjection j m1 ** globalenvInject ge j1 ** P := (sep_swap _ _ _).1.pred H1
  obtain ⟨j', A, B, C, D⟩ := alloc_parallel_rule H2 ALLOC1 ALLOC2 ALIGN LO HI RANGE1 RANGE2 RANGE3
  refine ⟨j', ?_, B, C⟩
  have A' := (sep_swap4 _ _ _ _ _).1.pred A
  refine (sep_swap4 _ _ _ _ _).1.pred (globalenvInject_incr (m0 := m1') ?_ ?_ A')
  · intro b b' d hj1
    change (if b = b1 then some (b2, delta) else j b) = some (b', d) at hj1
    by_cases hb : b = b1
    · rw [if_pos hb] at hj1; cases hj1; subst hb; exact C
    · rw [if_neg hb] at hj1; rw [D b hb]; exact hj1
  · intro b0 b3 d0 hj1 hj'
    change (if b0 = b1 then some (b2, delta) else j b0) = none at hj1
    by_cases hb : b0 = b1
    · rw [if_pos hb] at hj1; cases hj1
    · rw [if_neg hb] at hj1; rw [D b0 hb, hj1] at hj'; cases hj'

end Separation
end CC
