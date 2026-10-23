/-
  `drop_perm` and the remaining injection lemmas of `common/Memory.v`:

  * the `DROP` section (`perm_drop_2`, `perm_drop_4`, `valid_access_drop_1/2`,
    `load_drop`, `loadbytes_drop`);
  * `storebytes_empty_inj` / `storebytes_empty_inject`;
  * `drop_unmapped_inj`, `drop_mapped_inj`, `drop_outside_inj`,
    `drop_outside_inject` and `drop_inject_neutral`;
  * `disjoint_or_equal_inject` and `aligned_area_inject`.
-/
import CCLib.common.MemoryInjections

namespace CC
namespace Mem

/-! ## The `DROP` section -/

section Drop
variable {m : Mem} {b : Block} {lo hi : _root_.Int} {p : Permission} {m' : Mem}

/-- `drop_perm` leaves the contents alone. -/
theorem dropPerm_contents (h : dropPerm m b lo hi p = some m') : m'.contents = m.contents := by
  unfold dropPerm at h; split at h
  · cases h; rfl
  · cases h

/-- Exact description of the permissions after `drop_perm`. -/
theorem perm_dropPerm (h : dropPerm m b lo hi p = some m') (b' : Block) (ofs : _root_.Int)
    (k : PermKind) (p' : Permission) :
    perm m' b' ofs k p' =
      if b' = b ∧ lo ≤ ofs ∧ ofs < hi then permOrder p p' else perm m b' ofs k p' := by
  unfold dropPerm at h; split at h
  · cases h
    simp only [perm]
    rw [PMap.gsspec]
    by_cases hb : b' = b
    · subst hb
      simp only [if_true, true_and]
      by_cases hr : lo ≤ ofs ∧ ofs < hi
      · simp only [hr, if_true, and_self, permOrder']
      · simp only [hr, if_false]
    · simp only [hb, if_false, false_and]
  · cases h

/-- `Mem.perm_drop_2` -/
theorem perm_drop_2 (h : dropPerm m b lo hi p = some m') {ofs : _root_.Int} {k : PermKind}
    {p' : Permission} (h1 : lo ≤ ofs) (h2 : ofs < hi) (hp : perm m' b ofs k p' = true) :
    permOrder p p' = true := by
  rw [perm_dropPerm h, if_pos ⟨rfl, h1, h2⟩] at hp; exact hp

/-- `Mem.perm_drop_4` -/
theorem perm_drop_4 (h : dropPerm m b lo hi p = some m') {b' : Block} {ofs : _root_.Int}
    {k : PermKind} {p' : Permission} (hp : perm m' b' ofs k p' = true) :
    perm m b' ofs k p' = true := by
  rw [perm_dropPerm h] at hp
  split at hp
  · next hr =>
    obtain ⟨rfl, h1, h2⟩ := hr
    have hf := rangePerm_perm _ _ _ _ _ _ (range_perm_drop_1 h) ofs h1 h2
    exact perm_implies (perm_cur (k := k) hf) (permOrder_trans (by cases p <;> rfl) hp)
  · exact hp

/-- `Mem.perm_drop_3` in the implication form of `Memory.v`. -/
theorem perm_drop_3' (h : dropPerm m b lo hi p = some m') {b' : Block} {ofs : _root_.Int}
    {k : PermKind} {p' : Permission} (hout : b' ≠ b ∨ ofs < lo ∨ hi ≤ ofs)
    (hp : perm m b' ofs k p' = true) : perm m' b' ofs k p' = true := by
  rw [perm_drop_3 h b' ofs k p' hout]; exact hp

/-- `Mem.valid_access_drop_1` -/
theorem validAccess_drop_1 (h : dropPerm m b lo hi p = some m') {chunk : Chunk} {b' : Block}
    {ofs : _root_.Int} {p' : Permission}
    (hc : b' ≠ b ∨ ofs + sizeChunk chunk ≤ lo ∨ hi ≤ ofs ∨ permOrder p p' = true)
    (hv : validAccess m chunk b' ofs p' = true) : validAccess m' chunk b' ofs p' = true := by
  simp only [validAccess, Bool.and_eq_true] at hv ⊢
  refine ⟨rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => ?_, hv.2⟩
  have hpo := rangePerm_perm _ _ _ _ _ _ hv.1 o h1 h2
  rw [perm_dropPerm h]
  split
  · next hr =>
    obtain ⟨rfl, h3, h4⟩ := hr
    rcases hc with hc | hc | hc | hc
    · exact absurd rfl hc
    · omega
    · omega
    · exact hc
  · exact hpo

/-- `Mem.valid_access_drop_2` -/
theorem validAccess_drop_2 (h : dropPerm m b lo hi p = some m') {chunk : Chunk} {b' : Block}
    {ofs : _root_.Int} {p' : Permission} (hv : validAccess m' chunk b' ofs p' = true) :
    validAccess m chunk b' ofs p' = true := by
  simp only [validAccess, Bool.and_eq_true] at hv ⊢
  exact ⟨rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
    perm_drop_4 h (rangePerm_perm _ _ _ _ _ _ hv.1 o h1 h2), hv.2⟩

/-- `Mem.load_drop` -/
theorem load_drop (h : dropPerm m b lo hi p = some m') {chunk : Chunk} {b' : Block}
    {ofs : _root_.Int}
    (hc : b' ≠ b ∨ ofs + sizeChunk chunk ≤ lo ∨ hi ≤ ofs ∨ permOrder p .Readable = true) :
    load chunk m' b' ofs = load chunk m b' ofs := by
  unfold load
  rw [dropPerm_contents h]
  cases hv : validAccess m chunk b' ofs .Readable
  · cases hv' : validAccess m' chunk b' ofs .Readable
    · rfl
    · rw [validAccess_drop_2 h hv'] at hv; cases hv
  · rw [validAccess_drop_1 h hc hv]

/-- `Mem.loadbytes_drop` -/
theorem loadbytes_drop (h : dropPerm m b lo hi p = some m') {b' : Block} {ofs n : _root_.Int}
    (hc : b' ≠ b ∨ ofs + n ≤ lo ∨ hi ≤ ofs ∨ permOrder p .Readable = true) :
    loadbytes m' b' ofs n = loadbytes m b' ofs n := by
  unfold loadbytes
  rw [dropPerm_contents h]
  cases hr : rangePerm m b' ofs (ofs + n) .Cur .Readable
  · cases hr' : rangePerm m' b' ofs (ofs + n) .Cur .Readable
    · rfl
    · rw [rangePerm_intro _ _ _ _ _ _ fun o h1 h2 =>
        perm_drop_4 h (rangePerm_perm _ _ _ _ _ _ hr' o h1 h2)] at hr
      cases hr
  · have hr' : rangePerm m' b' ofs (ofs + n) .Cur .Readable = true := by
      refine rangePerm_intro _ _ _ _ _ _ fun o h1 h2 => ?_
      have hpo := rangePerm_perm _ _ _ _ _ _ hr o h1 h2
      rw [perm_dropPerm h]
      split
      · next hq =>
        obtain ⟨rfl, h3, h4⟩ := hq
        rcases hc with hc | hc | hc | hc
        · exact absurd rfl hc
        · omega
        · omega
        · exact hc
      · exact hpo
    rw [hr']

end Drop

/-- `Mem.range_perm_drop_2` -/
theorem dropPerm_isSome {m : Mem} {b : Block} {lo hi : Z} {p : Permission}
    (h : rangePerm m b lo hi .Cur .Freeable = true) : ∃ m', dropPerm m b lo hi p = some m' := by
  unfold dropPerm; rw [dif_pos h]; exact ⟨_, rfl⟩

/-! ## Generic injections: `storebytes` of an empty list and `drop_perm` -/

section MemInj
variable {f : Val.Meminj} {m1 m2 : Mem}

/-- Writing no bytes leaves every block's contents unchanged. -/
theorem storebytes_nil_get {m : Mem} {b : Block} {ofs : Z} {m' : Mem}
    (h : storebytes m b ofs [] = some m') (b' : Block) :
    PMap.get b' m'.contents = PMap.get b' m.contents := by
  rw [storebytes_contents h, PMap.gsspec]
  split
  · next hb => subst hb; rfl
  · rfl

/-- `Memory.storebytes_empty_inj` -/
theorem storebytes_empty_inj (h : MemInj f m1 m2) {b1 b2 : Block} {ofs1 ofs2 : Z}
    {m1' m2' : Mem} (hs1 : storebytes m1 b1 ofs1 [] = some m1')
    (hs2 : storebytes m2 b2 ofs2 [] = some m2') : MemInj f m1' m2' := by
  refine ⟨?_, ?_, ?_⟩
  · intro c1 c2 d o k q hf hp
    rw [perm_storebytes hs1] at hp
    rw [perm_storebytes hs2]
    exact h.perm _ _ _ _ _ _ hf hp
  · intro c1 c2 d o sz q hf hsz hr
    rw [rangePerm_congr (fun o => perm_storebytes hs1 c1 o .Max q)] at hr
    exact h.align _ _ _ _ _ _ hf hsz hr
  · intro c1 o c2 d hf hp
    rw [perm_storebytes hs1] at hp
    rw [storebytes_nil_get hs1, storebytes_nil_get hs2]
    exact h.memval _ _ _ _ hf hp

/-- `Memory.drop_unmapped_inj`.  CompCert also assumes `f b = None`; the proof
does not need it, so it is dropped here. -/
theorem drop_unmapped_inj (h : MemInj f m1 m2) {b : Block} {lo hi : _root_.Int}
    {p : Permission} {m1' : Mem} (hd : dropPerm m1 b lo hi p = some m1') :
    MemInj f m1' m2 := by
  refine ⟨fun c1 c2 d o k q hf hp => h.perm _ _ _ _ _ _ hf (perm_drop_4 hd hp), ?_, ?_⟩
  · intro c1 c2 d o sz q hf hsz hr
    exact h.align _ _ _ _ _ _ hf hsz
      (rangePerm_intro _ _ _ _ _ _ fun i h1 h2 => perm_drop_4 hd (rangePerm_perm _ _ _ _ _ _ hr i h1 h2))
  · intro c1 o c2 d hf hp
    rw [dropPerm_contents hd]
    exact h.memval _ _ _ _ hf (perm_drop_4 hd hp)

/-- `Memory.drop_mapped_inj` -/
theorem drop_mapped_inj (h : MemInj f m1 m2) {b1 b2 : Block} {delta lo hi : _root_.Int}
    {p : Permission} {m1' : Mem} (hd : dropPerm m1 b1 lo hi p = some m1')
    (hno : MeminjNoOverlap f m1) (hf : f b1 = some (b2, delta)) :
    ∃ m2', dropPerm m2 b2 (lo + delta) (hi + delta) p = some m2' ∧ MemInj f m1' m2' := by
  have hr1 := range_perm_drop_1 hd
  obtain ⟨m2', hd2⟩ := dropPerm_isSome (p := p) (rangePerm_inj h hr1 hf)
  refine ⟨m2', hd2, ?_, ?_, ?_⟩
  · intro c1 c2 d o k q hfc hp
    have hp1 := perm_drop_4 hd hp
    have hp2 := h.perm _ _ _ _ _ _ hfc hp1
    rw [perm_dropPerm hd2]
    split
    · next hr =>
      obtain ⟨rfl, h3, h4⟩ := hr
      by_cases hc : c1 = b1
      · subst hc
        rw [hf] at hfc; cases hfc
        exact perm_drop_2 hd (by omega) (by omega) hp
      · have hq1 : perm m1 c1 o .Max .Nonempty = true :=
          perm_max (perm_implies hp1 (by cases q <;> rfl))
        have hq2 : perm m1 b1 (o + d - delta) .Max .Nonempty = true :=
          perm_cur_max (perm_implies (rangePerm_perm _ _ _ _ _ _ hr1 (o + d - delta)
            (by omega) (by omega)) (by rfl))
        rcases hno _ _ _ _ _ _ _ _ hc hfc hf hq1 hq2 with hc' | hc'
        · exact absurd rfl hc'
        · exact absurd (by omega) hc'
    · exact hp2
  · intro c1 c2 d o sz q hfc hsz hr
    exact h.align _ _ _ _ _ _ hfc hsz
      (rangePerm_intro _ _ _ _ _ _ fun i h1 h2 => perm_drop_4 hd (rangePerm_perm _ _ _ _ _ _ hr i h1 h2))
  · intro c1 o c2 d hfc hp
    rw [dropPerm_contents hd, dropPerm_contents hd2]
    exact h.memval _ _ _ _ hfc (perm_drop_4 hd hp)

/-- `Memory.drop_outside_inj` -/
theorem drop_outside_inj (h : MemInj f m1 m2) {b : Block} {lo hi : _root_.Int}
    {p : Permission} {m2' : Mem} (hd : dropPerm m2 b lo hi p = some m2')
    (hout : ∀ b' delta (ofs : _root_.Int) k q, f b' = some (b, delta) →
      perm m1 b' ofs k q = true → lo ≤ ofs + delta → ofs + delta < hi → False) :
    MemInj f m1 m2' := by
  refine ⟨?_, h.align, ?_⟩
  · intro c1 c2 d o k q hfc hp
    have hp2 := h.perm _ _ _ _ _ _ hfc hp
    rw [perm_dropPerm hd]
    split
    · next hr =>
      obtain ⟨rfl, h3, h4⟩ := hr
      exact (hout _ _ _ _ _ hfc hp h3 h4).elim
    · exact hp2
  · intro c1 o c2 d hfc hp
    rw [dropPerm_contents hd]
    exact h.memval _ _ _ _ hfc hp

end MemInj

/-! ## Full injections -/

section Inject
variable {f : Val.Meminj} {m1 m2 : Mem}

/-- `Memory.storebytes_empty_inject` -/
theorem storebytes_empty_inject (h : Inject f m1 m2) {b1 b2 : Block} {ofs1 ofs2 : Z}
    {m1' m2' : Mem} (hs1 : storebytes m1 b1 ofs1 [] = some m1')
    (hs2 : storebytes m2 b2 ofs2 [] = some m2') : Inject f m1' m2' :=
  h.of_perm_eq (storebytes_empty_inj h.inj hs1 hs2) (storebytes_nextblock hs1)
    (storebytes_nextblock hs2) (fun b o k p => perm_storebytes hs1 b o k p)
    (fun b o k p => perm_storebytes hs2 b o k p)

/-- `Memory.drop_outside_inject` -/
theorem drop_outside_inject (h : Inject f m1 m2) {b : Block} {lo hi : _root_.Int}
    {p : Permission} {m2' : Mem} (hd : dropPerm m2 b lo hi p = some m2')
    (hout : ∀ b' delta (ofs : _root_.Int) k q, f b' = some (b, delta) →
      perm m1 b' ofs k q = true → lo ≤ ofs + delta → ofs + delta < hi → False) :
    Inject f m1 m2' := by
  refine ⟨drop_outside_inj h.inj hd hout, h.freeblocks, ?_, h.no_overlap, h.representable, ?_,
    h.metadata⟩
  · intro b1 b' d hf; rw [valid_block_drop hd]; exact h.mappedblocks _ _ _ hf
  · intro b1 o b2 d k q hf hp
    exact h.perm_inv _ _ _ _ _ _ hf (perm_drop_4 hd hp)

/-- `Memory.disjoint_or_equal_inject` -/
theorem disjoint_or_equal_inject (h : Inject f m1 m2) {b1 b1' b2 b2' : Block}
    {delta1 delta2 ofs1 ofs2 sz : _root_.Int}
    (hf1 : f b1 = some (b1', delta1)) (hf2 : f b2 = some (b2', delta2))
    (hr1 : rangePerm m1 b1 ofs1 (ofs1 + sz) .Max .Nonempty = true)
    (hr2 : rangePerm m1 b2 ofs2 (ofs2 + sz) .Max .Nonempty = true) (hsz : sz > 0)
    (hd : b1 ≠ b2 ∨ ofs1 = ofs2 ∨ ofs1 + sz ≤ ofs2 ∨ ofs2 + sz ≤ ofs1) :
    b1' ≠ b2' ∨ ofs1 + delta1 = ofs2 + delta2 ∨ ofs1 + delta1 + sz ≤ ofs2 + delta2 ∨
      ofs2 + delta2 + sz ≤ ofs1 + delta1 := by
  by_cases hb : b1 = b2
  · subst hb
    rw [hf1] at hf2; cases hf2
    rcases hd with hd | hd | hd | hd
    · exact absurd rfl hd
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  by_cases hb' : b1' = b2'
  · subst hb'
    refine Or.inr (Or.inr ?_)
    by_cases hc : ofs1 + delta1 + sz ≤ ofs2 + delta2 ∨ ofs2 + delta2 + sz ≤ ofs1 + delta1
    · exact hc
    · exfalso
      have hx : ∃ x : _root_.Int, ofs1 + delta1 ≤ x ∧ x < ofs1 + delta1 + sz ∧
          ofs2 + delta2 ≤ x ∧ x < ofs2 + delta2 + sz := by
        by_cases hle : ofs1 + delta1 ≤ ofs2 + delta2
        · exact ⟨ofs2 + delta2, by omega, by omega, by omega, by omega⟩
        · exact ⟨ofs1 + delta1, by omega, by omega, by omega, by omega⟩
      obtain ⟨x, hx1, hx2, hx3, hx4⟩ := hx
      have hq1 := rangePerm_perm _ _ _ _ _ _ hr1 (x - delta1) (by omega) (by omega)
      have hq2 := rangePerm_perm _ _ _ _ _ _ hr2 (x - delta2) (by omega) (by omega)
      rcases h.no_overlap _ _ _ _ _ _ _ _ hb hf1 hf2 hq1 hq2 with hc' | hc'
      · exact hc' rfl
      · exact hc' (by omega)
  · exact Or.inl hb'

/-- `Memory.aligned_area_inject` -/
theorem aligned_area_inject (h : Inject f m1 m2) {b b' : Block} {ofs al sz delta : _root_.Int}
    (hal : al = 1 ∨ al = 2 ∨ al = 4 ∨ al = 8) (hsz : sz > 0) (hdsz : al ∣ sz)
    (hr : rangePerm m1 b ofs (ofs + sz) .Cur .Nonempty = true) (hdofs : al ∣ ofs)
    (hf : f b = some (b', delta)) : al ∣ ofs + delta := by
  have hA : minSafeAlignment sz ∣ delta := h.inj.align _ _ _ _ _ _ hf hsz (rangePerm_max hr)
  have hB : minSafeAlignment al = al := by
    rcases hal with rfl | rfl | rfl | rfl <;> rfl
  have hQ : al ≤ sz := Int.le_of_dvd hsz hdsz
  refine Int.dvd_add hdofs ?_
  rw [← hB]
  exact Int.dvd_trans (minSafeAlignment_mono hQ) hA

/-- `Memory.drop_inject_neutral` -/
theorem drop_inject_neutral {m : Mem} {b : Block} {lo hi : _root_.Int} {p : Permission}
    {m' : Mem} {thr : Block} (hd : dropPerm m b lo hi p = some m') (h : InjectNeutral thr m)
    (hlt : b < thr) : InjectNeutral thr m' := by
  obtain ⟨m'', hd2, hi⟩ := drop_mapped_inj h hd (flatInj_no_overlap thr m)
    (show flatInj thr b = some (b, 0) by simp only [flatInj, if_pos hlt])
  rw [Int.add_zero, Int.add_zero, hd] at hd2
  cases hd2
  exact hi

end Inject

end Mem
end CC
