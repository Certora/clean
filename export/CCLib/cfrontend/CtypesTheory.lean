/-
  Theorems of `cfrontend/Ctypes.v`: alignments are powers of two, sizes are
  non-negative, sizes are multiples of alignments, the struct-layout lemmas
  (`next_field_incr`, `layout_field_range`, `layout_field_alignment`,
  `field_offset_in_range`, `field_offset_no_overlap`, `field_offset_aligned`,
  `union_field_offset_in_range`), the `alignof_blockcopy` lemmas, and
  `build_composite_env_consistent`.

  ## The invariants of `composite`

  CompCert's `composite` record carries three proofs (`co_sizeof_pos`,
  `co_alignof_two_p`, `co_sizeof_alignof`); the port's `Composite` carries only
  data (see the header of `CCLib/cfrontend/Ctypes.lean`).  Here the three facts are the
  predicate `Composite.WF`, and `CompositeEnv.WF env` says every composite of
  `env` satisfies it.  Theorems whose Rocq proof uses the three fields take
  `env.WF` as a hypothesis, and `buildCompositeEnv_wf` proves it for every
  environment `build_composite_env` produces — in particular for the
  environment of every program built by `mkprogram`.

  The alignment arithmetic of `lib/Coqlib.v` (`align_le`, `align_divides`,
  `floor_interval`, `floor_divides`) is proved here too, for the port's
  floor-division `align` / `floorZ`.
-/
import CCLib.cfrontend.Ctypes
import CCLib.lib.IntegersLemmas
import CCLib.lib.MapsTheory

namespace CC

/-! ## Alignment arithmetic (`Coqlib`) -/

theorem zdiv_eq (a b : _root_.Int) (hb : 0 < b) : zdiv a b = a / b :=
  Int.fdiv_eq_ediv_of_nonneg a (Int.le_of_lt hb)

/-- `Coqlib.align_le` -/
theorem align_le (x y : _root_.Int) (hy : 0 < y) : x ≤ align x y := by
  unfold align
  rw [zdiv_eq _ _ hy]
  have h1 := Int.mul_ediv_add_emod (x + y - 1) y
  have h2 := Int.emod_lt_of_pos (x + y - 1) hy
  have h3 := Int.emod_nonneg (x + y - 1) (Int.ne_of_gt hy)
  rw [Int.mul_comm]
  zomega

/-- `align x y < x + y` -/
theorem align_lt (x y : _root_.Int) (hy : 0 < y) : align x y < x + y := by
  unfold align
  rw [zdiv_eq _ _ hy]
  have h1 := Int.mul_ediv_add_emod (x + y - 1) y
  have h3 := Int.emod_nonneg (x + y - 1) (Int.ne_of_gt hy)
  rw [Int.mul_comm]
  zomega

/-- `Coqlib.align_divides` -/
theorem align_divides (x y : _root_.Int) : y ∣ align x y := by
  unfold align; exact Int.dvd_mul_left _ _

/-- `Coqlib.floor_interval` -/
theorem floor_interval (x y : _root_.Int) (hy : 0 < y) : floorZ x y ≤ x ∧ x < floorZ x y + y := by
  unfold floorZ
  rw [zdiv_eq _ _ hy]
  have h1 := Int.mul_ediv_add_emod x y
  have h2 := Int.emod_lt_of_pos x hy
  have h3 := Int.emod_nonneg x (Int.ne_of_gt hy)
  rw [Int.mul_comm]
  zomega

/-- `Coqlib.floor_divides` -/
theorem floor_divides (x y : _root_.Int) : y ∣ floorZ x y := by
  unfold floorZ; exact Int.dvd_mul_left _ _

/-- `align` of a multiple of `y` is itself. -/
theorem align_of_dvd (x y : _root_.Int) (hy : 0 < y) (h : y ∣ x) : align x y = x := by
  obtain ⟨k, rfl⟩ := h
  unfold align
  rw [zdiv_eq _ _ hy, show y * k + y - 1 = (y - 1) + k * y by rw [Int.mul_comm]; zomega,
    Int.add_mul_ediv_right _ _ (Int.ne_of_gt hy), Int.ediv_eq_zero_of_lt (by zomega) (by zomega),
    Int.zero_add, Int.mul_comm]

/-! ## Powers of two -/

/-- `exists n, x = two_power_nat n` -/
def IsTwoP (x : Z) : Prop := ∃ n : Nat, x = (2 : _root_.Int) ^ n

theorem IsTwoP.pos {x : Z} (h : IsTwoP x) : 0 < x := by
  obtain ⟨n, rfl⟩ := h
  exact Int.pow_pos (by decide)

theorem isTwoP_one : IsTwoP 1 := ⟨0, rfl⟩
theorem isTwoP_two : IsTwoP 2 := ⟨1, rfl⟩
theorem isTwoP_four : IsTwoP 4 := ⟨2, rfl⟩
theorem isTwoP_eight : IsTwoP 8 := ⟨3, rfl⟩

theorem IsTwoP.max {x y : Z} (hx : IsTwoP x) (hy : IsTwoP y) : IsTwoP (max x y) := by
  rcases Int.le_total x y with h | h
  · rw [Int.max_eq_right h]; exact hy
  · rw [Int.max_eq_left h]; exact hx

theorem two_pow_lt {n k : Nat} (h : k < n) : (2 : _root_.Int) ^ k < 2 ^ n := by
  have e : (2 : _root_.Int) ^ n = 2 ^ k * (2 ^ (n - k - 1) * 2) := by
    rw [← Int.pow_succ, ← Int.pow_add]; congr 1; zomega
  have hA : 0 < (2 : _root_.Int) ^ k := Int.pow_pos (by decide)
  have hB : 0 < (2 : _root_.Int) ^ (n - k - 1) := Int.pow_pos (by decide)
  have : (2 : _root_.Int) ^ k * 2 ≤ 2 ^ k * (2 ^ (n - k - 1) * 2) :=
    Int.mul_le_mul_of_nonneg_left (by zomega) (Int.le_of_lt hA)
  zomega

/-- Of two powers of two, the smaller divides the larger. -/
theorem IsTwoP.dvd_of_le {x y : Z} (hx : IsTwoP x) (hy : IsTwoP y) (h : x ≤ y) : x ∣ y := by
  obtain ⟨n, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  have hnk : n ≤ k := by
    apply Classical.byContradiction
    intro hc
    have := two_pow_lt (show k < n by zomega)
    zomega
  exact ⟨2 ^ (k - n), by rw [← Int.pow_add, Nat.add_sub_cancel' hnk]⟩

/-- `Ctypes.align_attr_two_p` -/
theorem alignAttr_two_p (a : Attr) {al : Z} (h : IsTwoP al) : IsTwoP (alignAttr a al) := by
  unfold alignAttr
  split
  · next l _ => exact ⟨l, rfl⟩
  · exact h

/-! ## Well-formed composite environments -/

/-- The three proof fields of CompCert's `composite` record
(`co_sizeof_pos`, `co_alignof_two_p`, `co_sizeof_alignof`). -/
structure Composite.WF (co : Composite) : Prop where
  sizeof_pos : co.co_sizeof ≥ 0
  alignof_two_p : IsTwoP co.co_alignof
  sizeof_alignof : co.co_alignof ∣ co.co_sizeof

/-- Every composite of the environment satisfies `Composite.WF`. -/
def CompositeEnv.WF (env : CompositeEnv) : Prop :=
  ∀ id co, env.get id = some co → co.WF

section Env
variable {env : CompositeEnv}

/-- `Ctypes.alignof_two_p` -/
theorem alignof_two_p (hwf : env.WF) : ∀ t : Ty, IsTwoP (alignof env t)
  | .Tvoid => alignAttr_two_p _ isTwoP_one
  | .Tint .I8 _ _ => alignAttr_two_p _ isTwoP_one
  | .Tint .I16 _ _ => alignAttr_two_p _ isTwoP_two
  | .Tint .I32 _ _ => alignAttr_two_p _ isTwoP_four
  | .Tint .IBool _ _ => alignAttr_two_p _ isTwoP_one
  | .Tlong _ _ => alignAttr_two_p _ isTwoP_eight
  | .Tfloat .F32 _ => alignAttr_two_p _ isTwoP_four
  | .Tfloat .F64 _ => alignAttr_two_p _ isTwoP_eight
  | .Tpointer _ _ => alignAttr_two_p _ isTwoP_eight
  | .Tarray t _ _ => alignAttr_two_p _ (alignof_two_p hwf t)
  | .Tfunction _ _ _ => alignAttr_two_p _ isTwoP_one
  | .Tstruct id _ => by
    simp only [alignof]
    apply alignAttr_two_p
    split
    · next co hco => exact (hwf id co hco).alignof_two_p
    · exact isTwoP_one
  | .Tunion id _ => by
    simp only [alignof]
    apply alignAttr_two_p
    split
    · next co hco => exact (hwf id co hco).alignof_two_p
    · exact isTwoP_one

/-- `Ctypes.alignof_pos` -/
theorem alignof_pos (hwf : env.WF) (t : Ty) : alignof env t > 0 := (alignof_two_p hwf t).pos

/-- `Ctypes.sizeof_pos` -/
theorem sizeof_pos (hwf : env.WF) : ∀ t : Ty, sizeof env t ≥ 0
  | .Tvoid => by simp [sizeof]
  | .Tint .I8 _ _ => by simp [sizeof]
  | .Tint .I16 _ _ => by simp [sizeof]
  | .Tint .I32 _ _ => by simp [sizeof]
  | .Tint .IBool _ _ => by simp [sizeof]
  | .Tlong _ _ => by simp [sizeof]
  | .Tfloat .F32 _ => by simp [sizeof]
  | .Tfloat .F64 _ => by simp [sizeof]
  | .Tpointer _ _ => by simp [sizeof, Archi.ptr64]
  | .Tarray t n _ => by
    simp only [sizeof]
    exact Int.mul_nonneg (sizeof_pos hwf t) (Int.le_max_left _ _)
  | .Tfunction _ _ _ => by simp [sizeof]
  | .Tstruct id _ => by
    simp only [sizeof]
    split
    · next co hco => exact (hwf id co hco).sizeof_pos
    · exact Int.le_refl 0
  | .Tunion id _ => by
    simp only [sizeof]
    split
    · next co hco => exact (hwf id co hco).sizeof_pos
    · exact Int.le_refl 0

/-- `Ctypes.naturally_aligned` -/
def naturallyAligned : Ty → Prop
  | t@(.Tarray t' _ _) => t.attr.attr_alignas = none ∧ naturallyAligned t'
  | t => t.attr.attr_alignas = none

/-- `Ctypes.sizeof_alignof_compat` -/
theorem sizeof_alignof_compat (hwf : env.WF) : ∀ t : Ty, naturallyAligned t →
    alignof env t ∣ sizeof env t
  | .Tvoid, h => by simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tint .I8 _ _, h => by simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tint .I16 _ _, h => by simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tint .I32 _ _, h => by simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tint .IBool _ _, h => by simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tlong _ _, h => by
    simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h, Archi.align_int64]
  | .Tfloat .F32 _, h => by simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tfloat .F64 _, h => by
    simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h, Archi.align_float64]
  | .Tpointer _ _, h => by simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tarray t n a, h => by
    simp only [naturallyAligned] at h
    simp only [alignof, sizeof, alignAttr, h.1]
    exact Int.dvd_trans (sizeof_alignof_compat hwf t h.2) (Int.dvd_mul_right _ _)
  | .Tfunction _ _ _, h => by
    simp only [naturallyAligned] at h; simp [alignof, sizeof, alignAttr, h]
  | .Tstruct id a, h => by
    simp only [naturallyAligned] at h
    simp only [alignof, sizeof, alignAttr, h]
    split
    · next co hco => exact (hwf id co hco).sizeof_alignof
    · exact Int.dvd_zero _
  | .Tunion id a, h => by
    simp only [naturallyAligned] at h
    simp only [alignof, sizeof, alignAttr, h]
    split
    · next co hco => exact (hwf id co hco).sizeof_alignof
    · exact Int.dvd_zero _

/-! ## Layout of struct fields (`LAYOUT`) -/

theorem zdiv_mul_cancel_of_dvd {q d : _root_.Int} (hd : 0 < d) (h : d ∣ q) : zdiv q d * d = q := by
  rw [zdiv_eq _ _ hd]; exact Int.ediv_mul_cancel h

/-- `Ctypes.bitalignof_intsize_pos` -/
theorem bitalignofIntsize_pos (sz : IntSize) : bitalignofIntsize sz > 0 := by
  cases sz <;> decide

theorem eight_dvd_bitalignofIntsize (sz : IntSize) : (8 : _root_.Int) ∣ bitalignofIntsize sz := by
  cases sz <;> decide

theorem bitalignof_pos (hwf : env.WF) (t : Ty) : bitalignof env t > 0 := by
  have := alignof_pos hwf t
  unfold bitalignof; zomega

theorem bitsizeof_nonneg (hwf : env.WF) (t : Ty) : bitsizeof env t ≥ 0 := by
  have := sizeof_pos hwf t
  unfold bitsizeof; zomega

/-- `Ctypes.next_field_incr` -/
theorem nextField_incr (hwf : env.WF) (pos : Z) (m : Member) : pos ≤ nextField env pos m := by
  cases m with
  | Member_plain id t =>
    have h1 := align_le pos (bitalignof env t) (bitalignof_pos hwf t)
    have h2 := bitsizeof_nonneg hwf t
    simp only [nextField]; zomega
  | Member_bitfield id sz sg a w p =>
    have hs := bitalignofIntsize_pos sz
    simp only [nextField]
    split
    · exact align_le _ _ hs
    · have := floor_interval pos (bitalignofIntsize sz) hs
      split <;> zomega

/-- `Ctypes.layout_field_range` -/
theorem layoutField_range (hwf : env.WF) {pos ofs : Z} {m : Member} {bf : Bitfield}
    (h : layoutField env pos m = .OK (ofs, bf)) :
    pos ≤ layoutStart ofs bf ∧
      layoutStart ofs bf + layoutWidth env m.type bf ≤ nextField env pos m := by
  cases m with
  | Member_plain id t =>
    simp only [layoutField, Res.OK.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hA := bitalignof_pos hwf t
    have hB := align_le pos (bitalignof env t) hA
    have hD : (8 : _root_.Int) ∣ align pos (bitalignof env t) :=
      Int.dvd_trans (Int.dvd_mul_left _ _) (align_divides pos (bitalignof env t))
    have hE := zdiv_mul_cancel_of_dvd (by decide) hD
    simp only [layoutStart, layoutWidth, Member.type, nextField]
    zomega
  | Member_bitfield id sz sg a w pd =>
    simp only [layoutField] at h
    split at h
    · cases h
    split at h
    · cases h
    have hs := bitalignofIntsize_pos sz
    have hB := floor_interval pos (bitalignofIntsize sz) hs
    have hC := floor_divides pos (bitalignofIntsize sz)
    have hD := eight_dvd_bitalignofIntsize sz
    have hE : (8 : _root_.Int) ∣ floorZ pos (bitalignofIntsize sz) := Int.dvd_trans hD hC
    have hF : (8 : _root_.Int) ∣ floorZ pos (bitalignofIntsize sz) + bitalignofIntsize sz :=
      Int.dvd_add hE hD
    have hG := zdiv_mul_cancel_of_dvd (by decide) hE
    have hH := zdiv_mul_cancel_of_dvd (by decide) hF
    simp only [nextField]
    rename_i hw _
    rw [if_neg hw]
    split at h
    · simp only [Res.OK.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [layoutStart, layoutWidth]
      rw [if_pos (by assumption)]
      zomega
    · simp only [Res.OK.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [layoutStart, layoutWidth]
      rw [if_neg (by assumption)]
      zomega

/-- `Ctypes.layout_alignment` -/
def layoutAlignment (env : CompositeEnv) (t : Ty) : Bitfield → Z
  | .Full => alignof env t
  | .Bits sz _ _ _ => zdiv (bitalignofIntsize sz) 8

theorem zdiv8_dvd {s n : _root_.Int} (hs : (8 : _root_.Int) ∣ s) (h : s ∣ n) :
    zdiv s 8 ∣ zdiv n 8 := by
  obtain ⟨n1, rfl⟩ := h
  obtain ⟨n2, rfl⟩ := hs
  rw [zdiv_eq _ _ (by decide), zdiv_eq _ _ (by decide), Int.mul_assoc,
    Int.mul_ediv_cancel_left _ (by decide), Int.mul_ediv_cancel_left _ (by decide)]
  exact Int.dvd_mul_right _ _

/-- `Ctypes.layout_field_alignment` -/
theorem layoutField_alignment {pos ofs : Z} {m : Member} {bf : Bitfield}
    (h : layoutField env pos m = .OK (ofs, bf)) : layoutAlignment env m.type bf ∣ ofs := by
  cases m with
  | Member_plain id t =>
    simp only [layoutField, Res.OK.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [layoutAlignment, Member.type]
    obtain ⟨n, hn⟩ := align_divides pos (bitalignof env t)
    rw [hn, zdiv_eq _ _ (by decide)]
    simp only [bitalignof]
    rw [show alignof env t * 8 * n = 8 * (alignof env t * n) by
      rw [Int.mul_comm (alignof env t) 8, Int.mul_assoc], Int.mul_ediv_cancel_left _ (by decide)]
    exact Int.dvd_mul_right _ _
  | Member_bitfield id sz sg a w pd =>
    simp only [layoutField] at h
    split at h
    · cases h
    split at h
    · cases h
    have hC := floor_divides pos (bitalignofIntsize sz)
    have hD := eight_dvd_bitalignofIntsize sz
    split at h
    · simp only [Res.OK.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact zdiv8_dvd hD hC
    · simp only [Res.OK.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact zdiv8_dvd hD (Int.dvd_add hC (Int.dvd_refl _))

/-! ## Composite sizes and alignments -/

/-- `Ctypes.alignof_composite_two_p` -/
theorem alignofComposite_two_p (hwf : env.WF) : ∀ m : List Member, IsTwoP (alignofComposite env m)
  | [] => isTwoP_one
  | a :: m => by
    simp only [alignofComposite]
    split
    · exact alignofComposite_two_p hwf m
    · exact (alignof_two_p hwf _).max (alignofComposite_two_p hwf m)

/-- `Ctypes.alignof_composite_pos` -/
theorem alignofComposite_pos (hwf : env.WF) (m : List Member) (a : Attr) :
    alignAttr a (alignofComposite env m) > 0 :=
  (alignAttr_two_p a (alignofComposite_two_p hwf m)).pos

/-- `Ctypes.bitsizeof_struct_incr` -/
theorem bitsizeofStruct_incr (hwf : env.WF) : ∀ (m : List Member) (cur : Z),
    cur ≤ bitsizeofStruct env cur m
  | [], cur => Int.le_refl cur
  | a :: m, cur => by
    have h1 := nextField_incr hwf cur a
    have h2 := bitsizeofStruct_incr hwf m (nextField env cur a)
    simp only [bitsizeofStruct]; zomega

/-- `Ctypes.sizeof_union_pos` -/
theorem sizeofUnion_pos : ∀ m : List Member, 0 ≤ sizeofUnion env m
  | [] => Int.le_refl 0
  | a :: m => by
    have := sizeofUnion_pos m
    simp only [sizeofUnion]
    exact Int.le_trans this (Int.le_max_right _ _)

/-! ## Field offsets -/

/-- `Ctypes.field_offset_rec_in_range` -/
theorem fieldOffsetRec_in_range (hwf : env.WF) {id : Ident} {ofs : Z} {bf : Bitfield} {ty : Ty} :
    ∀ (ms : List Member) (pos : Z), fieldOffsetRec env id pos ms = .OK (ofs, bf) →
    fieldType id ms = .OK ty →
    pos ≤ layoutStart ofs bf ∧ layoutStart ofs bf + layoutWidth env ty bf ≤ bitsizeofStruct env pos ms
  | [], _, h, _ => by simp [fieldOffsetRec] at h
  | m :: ms, pos, h, ht => by
    simp only [fieldOffsetRec, fieldType] at h ht
    split at h
    · rw [if_pos (by assumption)] at ht
      simp only [Res.OK.injEq] at ht
      subst ht
      have := layoutField_range hwf h
      have := bitsizeofStruct_incr hwf ms (nextField env pos m)
      simp only [bitsizeofStruct]
      zomega
    · rw [if_neg (by assumption)] at ht
      have := fieldOffsetRec_in_range hwf ms _ h ht
      have := nextField_incr hwf pos m
      simp only [bitsizeofStruct]
      zomega

/-- `Ctypes.field_offset_in_range_gen` -/
theorem fieldOffset_in_range_gen (hwf : env.WF) {ms : List Member} {id : Ident} {ofs : Z}
    {bf : Bitfield} {ty : Ty} (h : fieldOffset env id ms = .OK (ofs, bf))
    (ht : fieldType id ms = .OK ty) :
    0 ≤ layoutStart ofs bf ∧ layoutStart ofs bf + layoutWidth env ty bf ≤ bitsizeofStruct env 0 ms :=
  fieldOffsetRec_in_range hwf ms 0 h ht

/-- `Ctypes.field_offset_in_range` -/
theorem fieldOffset_in_range (hwf : env.WF) {ms : List Member} {id : Ident} {ofs : Z} {ty : Ty}
    (h : fieldOffset env id ms = .OK (ofs, .Full)) (ht : fieldType id ms = .OK ty) :
    0 ≤ ofs ∧ ofs + sizeof env ty ≤ sizeofStruct env ms := by
  have ⟨hA, hB⟩ := fieldOffset_in_range_gen hwf h ht
  simp only [layoutStart, layoutWidth, bitsizeof] at hA hB
  simp only [sizeofStruct, bytesOfBits]
  rw [zdiv_eq _ _ (by decide)]
  zomega

/-- `Ctypes.field_offset_no_overlap` -/
theorem fieldOffset_no_overlap (hwf : env.WF) {id1 id2 : Ident} {ofs1 ofs2 : Z}
    {bf1 bf2 : Bitfield} {ty1 ty2 : Ty} {fld : List Member}
    (h1 : fieldOffset env id1 fld = .OK (ofs1, bf1)) (ht1 : fieldType id1 fld = .OK ty1)
    (h2 : fieldOffset env id2 fld = .OK (ofs2, bf2)) (ht2 : fieldType id2 fld = .OK ty2)
    (hne : id1 ≠ id2) :
    layoutStart ofs1 bf1 + layoutWidth env ty1 bf1 ≤ layoutStart ofs2 bf2 ∨
      layoutStart ofs2 bf2 + layoutWidth env ty2 bf2 ≤ layoutStart ofs1 bf1 := by
  unfold fieldOffset at h1 h2
  generalize (0 : Z) = pos at h1 h2
  induction fld generalizing pos with
  | nil => simp [fieldOffsetRec] at h1
  | cons m fld ih =>
    simp only [fieldOffsetRec] at h1 h2
    simp only [fieldType] at ht1 ht2
    by_cases e1 : id1 = m.name <;> by_cases e2 : id2 = m.name
    · exact absurd (e1.trans e2.symm) hne
    · rw [if_pos e1] at h1 ht1
      rw [if_neg e2] at h2 ht2
      simp only [Res.OK.injEq] at ht1
      subst ht1
      have := fieldOffsetRec_in_range hwf fld _ h2 ht2
      have := layoutField_range hwf h1
      zomega
    · rw [if_neg e1] at h1 ht1
      rw [if_pos e2] at h2 ht2
      simp only [Res.OK.injEq] at ht2
      subst ht2
      have := fieldOffsetRec_in_range hwf fld _ h1 ht1
      have := layoutField_range hwf h2
      zomega
    · rw [if_neg e1] at h1 ht1
      rw [if_neg e2] at h2 ht2
      exact ih ht1 ht2 _ h1 h2

/-- `Ctypes.field_offset_prefix` -/
theorem fieldOffset_prefix {id : Ident} {ofs : Z} {bf : Bitfield} (fld2 : List Member)
    {fld1 : List Member} (h : fieldOffset env id fld1 = .OK (ofs, bf)) :
    fieldOffset env id (fld1 ++ fld2) = .OK (ofs, bf) := by
  unfold fieldOffset at h ⊢
  generalize (0 : Z) = pos at h ⊢
  induction fld1 generalizing pos with
  | nil => simp [fieldOffsetRec] at h
  | cons m fld1 ih =>
    simp only [fieldOffsetRec, List.cons_append] at h ⊢
    split
    · rw [if_pos (by assumption)] at h; exact h
    · rw [if_neg (by assumption)] at h; exact ih _ h

/-- `Ctypes.field_offset_aligned_gen` -/
theorem fieldOffset_aligned_gen {id : Ident} {fld : List Member} {ofs : Z} {bf : Bitfield}
    {ty : Ty} (h : fieldOffset env id fld = .OK (ofs, bf)) (ht : fieldType id fld = .OK ty) :
    layoutAlignment env ty bf ∣ ofs := by
  unfold fieldOffset at h
  generalize (0 : Z) = pos at h
  induction fld generalizing pos with
  | nil => simp [fieldOffsetRec] at h
  | cons m fld ih =>
    simp only [fieldOffsetRec] at h
    simp only [fieldType] at ht
    split at h
    · rw [if_pos (by assumption)] at ht
      simp only [Res.OK.injEq] at ht
      subst ht
      exact layoutField_alignment h
    · rw [if_neg (by assumption)] at ht
      exact ih ht _ h

/-- `Ctypes.field_offset_aligned` -/
theorem fieldOffset_aligned {id : Ident} {fld : List Member} {ofs : Z} {ty : Ty}
    (h : fieldOffset env id fld = .OK (ofs, .Full)) (ht : fieldType id fld = .OK ty) :
    alignof env ty ∣ ofs :=
  fieldOffset_aligned_gen h ht

/-- `Ctypes.union_field_offset_in_range_gen` -/
theorem unionFieldOffset_in_range_gen (hwf : env.WF) {id : Ident} {ofs : Z} {bf : Bitfield}
    {ty : Ty} : ∀ (ms : List Member), unionFieldOffset env id ms = .OK (ofs, bf) →
    fieldType id ms = .OK ty →
    ofs = 0 ∧ 0 ≤ layoutStart ofs bf ∧ layoutStart ofs bf + layoutWidth env ty bf ≤ sizeofUnion env ms * 8
  | [], h, _ => by simp [unionFieldOffset] at h
  | m :: ms, h, ht => by
    simp only [unionFieldOffset, fieldType] at h ht
    split at h
    · rw [if_pos (by assumption)] at ht
      simp only [Res.OK.injEq] at ht
      subst ht
      have hu := sizeofUnion_pos (env := env) ms
      have hmax : sizeof env m.type ≤ sizeofUnion env (m :: ms) := by
        simp only [sizeofUnion]; exact Int.le_max_left _ _
      cases m with
      | Member_plain i t =>
        simp only [layoutField, Res.OK.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hal := bitalignof_pos hwf t
        rw [align_of_dvd 0 _ hal (Int.dvd_zero _)]
        simp only [layoutStart, layoutWidth, bitsizeof, Member.type, zdiv_eq 0 8 (by decide)] at hmax ⊢
        have := sizeof_pos hwf t
        refine ⟨rfl, ?_, ?_⟩ <;> zomega
      | Member_bitfield i sz sg a w pd =>
        simp only [layoutField] at h
        split at h
        · cases h
        split at h
        · cases h
        rename_i hw hsz
        have hA : bitsizeIntsize sz ≤ bitalignofIntsize sz ∧
            bitalignofIntsize sz ≤ sizeof env (Member.Member_bitfield i sz sg a w pd).type * 8 := by
          simp only [Member.type]; cases sz <;> simp [bitsizeIntsize, bitalignofIntsize, sizeof]
        have hfl : floorZ 0 (bitalignofIntsize sz) = 0 := by
          simp only [floorZ]; rw [zdiv_eq _ _ (bitalignofIntsize_pos sz)]; simp
        rw [hfl] at h
        rw [if_pos (by zomega)] at h
        simp only [Res.OK.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [layoutStart, layoutWidth, zdiv_eq 0 8 (by decide)]
        refine ⟨by decide, by zomega, ?_⟩
        zomega
    · rw [if_neg (by assumption)] at ht
      have := unionFieldOffset_in_range_gen hwf ms h ht
      have : sizeofUnion env ms ≤ sizeofUnion env (m :: ms) := by
        simp only [sizeofUnion]; exact Int.le_max_right _ _
      refine ⟨by zomega, by zomega, by zomega⟩

/-- `Ctypes.union_field_offset_in_range` -/
theorem unionFieldOffset_in_range (hwf : env.WF) {ms : List Member} {id : Ident} {ofs : Z}
    {ty : Ty} (h : unionFieldOffset env id ms = .OK (ofs, .Full)) (ht : fieldType id ms = .OK ty) :
    ofs = 0 ∧ sizeof env ty ≤ sizeofUnion env ms := by
  have ⟨hA, hB, hC⟩ := unionFieldOffset_in_range_gen hwf ms h ht
  simp only [layoutStart, layoutWidth, bitsizeof] at hB hC
  exact ⟨hA, by zomega⟩

/-! ## `alignof_blockcopy` -/

theorem min8_1248 {x : Z} (h : IsTwoP x) :
    min 8 x = 1 ∨ min 8 x = 2 ∨ min 8 x = 4 ∨ min 8 x = 8 := by
  obtain ⟨n, rfl⟩ := h
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 =>
    right; right; right
    have : (8 : _root_.Int) ≤ 2 ^ (n + 3) := by
      rw [Int.pow_add]
      have : (1 : _root_.Int) ≤ 2 ^ n := Int.pow_pos (by decide)
      have : (2 : _root_.Int) ^ 3 = 8 := by decide
      zomega
    exact Int.min_eq_left this

theorem isTwoP_of_1248 {a : Z} (h : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8) : IsTwoP a := by
  rcases h with rfl | rfl | rfl | rfl
  · exact isTwoP_one
  · exact isTwoP_two
  · exact isTwoP_four
  · exact isTwoP_eight

/-- `Ctypes.alignof_blockcopy_1248` -/
theorem alignofBlockcopy_1248 (hwf : env.WF) : ∀ ty : Ty,
    alignofBlockcopy env ty = 1 ∨ alignofBlockcopy env ty = 2 ∨
      alignofBlockcopy env ty = 4 ∨ alignofBlockcopy env ty = 8
  | .Tvoid => by simp [alignofBlockcopy]
  | .Tint .I8 _ _ => by simp [alignofBlockcopy]
  | .Tint .I16 _ _ => by simp [alignofBlockcopy]
  | .Tint .I32 _ _ => by simp [alignofBlockcopy]
  | .Tint .IBool _ _ => by simp [alignofBlockcopy]
  | .Tlong _ _ => by simp [alignofBlockcopy, Archi.align_int64]
  | .Tfloat .F32 _ => by simp [alignofBlockcopy]
  | .Tfloat .F64 _ => by simp [alignofBlockcopy, Archi.align_float64]
  | .Tpointer _ _ => by simp [alignofBlockcopy, Archi.ptr64]
  | .Tarray t _ _ => alignofBlockcopy_1248 hwf t
  | .Tfunction _ _ _ => by simp [alignofBlockcopy]
  | .Tstruct id _ => by
    simp only [alignofBlockcopy]
    split
    · next co hco => exact min8_1248 (hwf id co hco).alignof_two_p
    · simp
  | .Tunion id _ => by
    simp only [alignofBlockcopy]
    split
    · next co hco => exact min8_1248 (hwf id co hco).alignof_two_p
    · simp

/-- `Ctypes.alignof_blockcopy_pos` -/
theorem alignofBlockcopy_pos (hwf : env.WF) (ty : Ty) : alignofBlockcopy env ty > 0 := by
  rcases alignofBlockcopy_1248 hwf ty with h | h | h | h <;> rw [h] <;> decide

theorem min8_dvd {x : Z} (h : IsTwoP x) : min 8 x ∣ x :=
  IsTwoP.dvd_of_le (isTwoP_of_1248 (min8_1248 h)) h (Int.min_le_right _ _)

/-- `Ctypes.sizeof_alignof_blockcopy_compat` -/
theorem sizeof_alignof_blockcopy_compat (hwf : env.WF) : ∀ ty : Ty,
    alignofBlockcopy env ty ∣ sizeof env ty
  | .Tvoid => by simp [alignofBlockcopy, sizeof]
  | .Tint .I8 _ _ => by simp [alignofBlockcopy, sizeof]
  | .Tint .I16 _ _ => by simp [alignofBlockcopy, sizeof]
  | .Tint .I32 _ _ => by simp [alignofBlockcopy, sizeof]
  | .Tint .IBool _ _ => by simp [alignofBlockcopy, sizeof]
  | .Tlong _ _ => by simp [alignofBlockcopy, sizeof, Archi.align_int64]
  | .Tfloat .F32 _ => by simp [alignofBlockcopy, sizeof]
  | .Tfloat .F64 _ => by simp [alignofBlockcopy, sizeof, Archi.align_float64]
  | .Tpointer _ _ => by simp [alignofBlockcopy, sizeof, Archi.ptr64]
  | .Tarray t _ _ => by
    simp only [alignofBlockcopy, sizeof]
    exact Int.dvd_trans (sizeof_alignof_blockcopy_compat hwf t) (Int.dvd_mul_right _ _)
  | .Tfunction _ _ _ => by simp [alignofBlockcopy, sizeof]
  | .Tstruct id _ => by
    simp only [alignofBlockcopy, sizeof]
    split
    · next co hco =>
      exact Int.dvd_trans (min8_dvd (hwf id co hco).alignof_two_p) (hwf id co hco).sizeof_alignof
    · exact Int.dvd_zero _
  | .Tunion id _ => by
    simp only [alignofBlockcopy, sizeof]
    split
    · next co hco =>
      exact Int.dvd_trans (min8_dvd (hwf id co hco).alignof_two_p) (hwf id co hco).sizeof_alignof
    · exact Int.dvd_zero _

/-- `Ctypes.alignof_alignof_blockcopy_compat` -/
theorem alignof_alignof_blockcopy_compat : ∀ ty : Ty, naturallyAligned ty →
    alignofBlockcopy env ty = min 8 (alignof env ty)
  | .Tvoid, h => by simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Int.min_def]
  | .Tint .I8 _ _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Int.min_def]
  | .Tint .I16 _ _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Int.min_def]
  | .Tint .I32 _ _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Int.min_def]
  | .Tint .IBool _ _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Int.min_def]
  | .Tlong _ _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Archi.align_int64]
  | .Tfloat .F32 _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Int.min_def]
  | .Tfloat .F64 _, h => by
    simp only [naturallyAligned] at h
    simp [alignofBlockcopy, alignof, alignAttr, h, Archi.align_float64]
  | .Tpointer _ _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Archi.ptr64]
  | .Tarray t _ _, h => by
    simp only [naturallyAligned] at h
    simp only [alignofBlockcopy, alignof, alignAttr, h.1]
    exact alignof_alignof_blockcopy_compat t h.2
  | .Tfunction _ _ _, h => by
    simp only [naturallyAligned] at h; simp [alignofBlockcopy, alignof, alignAttr, h, Int.min_def]
  | .Tstruct id _, h => by
    simp only [naturallyAligned] at h
    simp only [alignofBlockcopy, alignof, alignAttr, h]
    split <;> simp [Int.min_def]
  | .Tunion id _, h => by
    simp only [naturallyAligned] at h
    simp only [alignofBlockcopy, alignof, alignAttr, h]
    split <;> simp [Int.min_def]

/-! ## Building the composite environment -/

/-- `Ctypes.sizeof_composite_pos` -/
theorem sizeofComposite_pos (hwf : env.WF) (su : SU) (m : List Member) :
    0 ≤ sizeofComposite env su m := by
  cases su with
  | Struct =>
    have := bitsizeofStruct_incr hwf m 0
    simp only [sizeofComposite, sizeofStruct, bytesOfBits]
    rw [zdiv_eq _ _ (by decide)]
    exact Int.ediv_nonneg (by zomega) (by decide)
  | Union => exact sizeofUnion_pos m

/-- `Ctypes.complete_member` -/
theorem complete_member {m : Member} : ∀ {ms : List Member}, m ∈ ms →
    completeMembers env ms = true → completeType env m.type = true
  | m1 :: ms, hin, h => by
    simp only [completeMembers, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hin with rfl | hin
    · exact h.1
    · exact complete_member hin h.2

/-- A composite produced by `composite_of_def` in a well-formed environment
satisfies the three invariants of CompCert's `composite` record (the three
obligations of `Program Definition composite_of_def`). -/
theorem compositeOfDef_wf (hwf : env.WF) {id : Ident} {su : SU} {m : List Member} {a : Attr}
    {co : Composite} (h : compositeOfDef env id su m a = .OK co) : co.WF := by
  unfold compositeOfDef at h
  split at h
  · cases h
  split at h
  · cases h
  simp only [Res.OK.injEq] at h
  subst h
  have htp := alignAttr_two_p a (alignofComposite_two_p hwf m)
  have hpos := htp.pos
  refine ⟨?_, htp, align_divides _ _⟩
  have := align_le (sizeofComposite env su m) _ hpos
  have := sizeofComposite_pos hwf su m
  show align _ _ ≥ 0
  zomega

theorem compositeEnv_wf_empty : CompositeEnv.WF PTree.empty := by
  intro id co h; simp at h

theorem addCompositeDefinitions_wf : ∀ (defs : List CompositeDef) {env0 env : CompositeEnv},
    addCompositeDefinitions env0 defs = .OK env → env0.WF → env.WF
  | [], _, _, h, hwf => by simp only [addCompositeDefinitions, Res.OK.injEq] at h; subst h; exact hwf
  | .Composite id su m a :: defs, env0, env, h, hwf => by
    simp only [addCompositeDefinitions] at h
    split at h
    · next co hco =>
      refine addCompositeDefinitions_wf defs h ?_
      intro id1 co1 h1
      rw [PTree.gsspec] at h1
      split at h1
      · cases h1; exact compositeOfDef_wf hwf hco
      · exact hwf id1 co1 h1
    · cases h

/-- `Ctypes.build_composite_env_consistent`, for the invariants the port keeps
outside the `Composite` record: every environment `build_composite_env` produces
is well formed. -/
theorem buildCompositeEnv_wf {defs : List CompositeDef} {env : CompositeEnv}
    (h : buildCompositeEnv defs = .OK env) : env.WF :=
  addCompositeDefinitions_wf defs h compositeEnv_wf_empty

/-- `Ctypes.add_composite_definitions_incr` -/
theorem addCompositeDefinitions_incr {id : Ident} {co : Composite} :
    ∀ (defs : List CompositeDef) {env1 env2 : CompositeEnv},
    addCompositeDefinitions env1 defs = .OK env2 → env1.get id = some co → env2.get id = some co
  | [], _, _, h, h1 => by simp only [addCompositeDefinitions, Res.OK.injEq] at h; subst h; exact h1
  | .Composite id' su m a :: defs, env1, env2, h, h1 => by
    simp only [addCompositeDefinitions] at h
    split at h
    · next co' hco =>
      refine addCompositeDefinitions_incr defs h ?_
      have hne : id ≠ id' := by
        intro he; subst he
        unfold compositeOfDef at hco
        rw [h1] at hco
        cases hco
      rw [PTree.gso _ _ _ _ (Ne.symm hne)]; exact h1
    · cases h

/-- `Ctypes.build_composite_env_charact` -/
theorem buildCompositeEnv_charact {id : Ident} {su : SU} {m : List Member} {a : Attr}
    {defs : List CompositeDef} {env : CompositeEnv} (h : buildCompositeEnv defs = .OK env)
    (hin : CompositeDef.Composite id su m a ∈ defs) :
    ∃ co, env.get id = some co ∧ co.co_members = m ∧ co.co_attr = a ∧ co.co_su = su := by
  unfold buildCompositeEnv at h
  generalize (PTree.empty : CompositeEnv) = env0 at h
  induction defs generalizing env0 with
  | nil => exact absurd hin List.not_mem_nil
  | cons d defs ih =>
    obtain ⟨id', su', m', a'⟩ := d
    simp only [addCompositeDefinitions] at h
    split at h
    · next co hco =>
      rcases List.mem_cons.mp hin with he | hin'
      · cases he
        refine ⟨co, addCompositeDefinitions_incr defs h (PTree.gss _ _ _), ?_⟩
        unfold compositeOfDef at hco
        split at hco
        · cases hco
        split at hco
        · cases hco
        simp only [Res.OK.injEq] at hco
        subst hco
        exact ⟨rfl, rfl, rfl⟩
      · exact ih hin' _ h
    · cases h

/-- `Ctypes.build_composite_env_domain` -/
theorem buildCompositeEnv_domain {defs : List CompositeDef} {env : CompositeEnv} {id : Ident}
    {co : Composite} (h : buildCompositeEnv defs = .OK env) (hco : env.get id = some co) :
    CompositeDef.Composite id co.co_su co.co_members co.co_attr ∈ defs := by
  have hrec : ∀ (l : List CompositeDef) (e e' : CompositeEnv), addCompositeDefinitions e l = .OK e' →
      e'.get id = some co →
      e.get id = some co ∨ CompositeDef.Composite id co.co_su co.co_members co.co_attr ∈ l := by
    intro l
    induction l with
    | nil => intro e e' h1 h2; simp only [addCompositeDefinitions, Res.OK.injEq] at h1; subst h1; exact Or.inl h2
    | cons d l ih =>
      intro e e' h1 h2
      obtain ⟨id', su', m', a'⟩ := d
      simp only [addCompositeDefinitions] at h1
      split at h1
      · next co' hco' =>
        rcases ih _ _ h1 h2 with h3 | h3
        · rw [PTree.gsspec] at h3
          split at h3
          · next he =>
            subst he
            cases h3
            unfold compositeOfDef at hco'
            split at hco'
            · cases hco'
            split at hco'
            · cases hco'
            simp only [Res.OK.injEq] at hco'
            subst hco'
            exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h3
        · exact Or.inr (List.mem_cons_of_mem _ h3)
      · cases h1
  rcases hrec defs _ _ h hco with h1 | h1
  · simp at h1
  · exact h1

end Env

end CC
