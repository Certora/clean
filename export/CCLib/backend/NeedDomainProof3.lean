/-
  Abstract domain for neededness analysis — port of `backend/NeedDomain.v`
  (soundness lemmas, part 3): neededness for register environments
  (`nreg_agree`, `eagree_ge`, `eagree_bot`, `eagree_same`,
  `eagree_update_1`, `eagree_update`, `eagree_update_dead`), neededness for
  memory locations (`nlive_all`, `nlive_add`, `incl_nmem_add`,
  `nlive_remove`, `nlive_contains`, `nlive_dead_stack`, `nlive_lub_l`,
  `nlive_lub_r`, `nmem_beq_sound`) and the order of the lattice `NA`.

  Difference from Rocq: the lattices `NE` and `NA` of `NeedDomain.lean` are
  built with `Semilattice.free`; their order here is CompCert's (`NE.ge` is
  the pointwise `nge`, `NA.ge` adds the inclusion of live locations), and
  `NAge_of_free` shows that the free order is included in it, so the
  solver's results can be read with CompCert's order.
-/
import CCLib.backend.NeedDomainProof
import CCLib.backend.ValueDomainMmatch
import CCLib.lib.LatticeFree

namespace CC
namespace NeedDomain

open Nval ValueDomain

/-! ### Register environments -/

theorem NE.get_set (p r : Positive) (v : Nval) (x : Nenv) :
    NE.get r (NE.set p v x) = if r = p then v else NE.get r x := by
  unfold NE.get NE.set
  split
  · rw [PTree.grspec]; split <;> simp_all
  · rw [PTree.gsspec]; split <;> simp_all

theorem NE.get_bot (r : Positive) : NE.get r NE.bot = .Nothing := by
  simp [NE.get, NE.bot]

theorem NE.get_lub (r : Positive) (x y : Nenv) :
    NE.get r (NE.lub x y) = nlub (NE.get r x) (NE.get r y) := by
  unfold NE.get NE.lub
  rw [PTree.gcombine _ rfl]
  cases x.get r <;> cases y.get r <;> simp [NE.optLub, nlub]
  · rename_i a; cases a <;> rfl

theorem NE.get_beq {x y : Nenv} (h : NE.beq x y = true) (r : Positive) :
    NE.get r x = NE.get r y := by
  rcases ptreeBeq_correct _ x y h r with ⟨h1, h2⟩ | ⟨a, b, h1, h2, h3⟩
  · simp [NE.get, h1, h2]
  · simp only [decide_eq_true_eq] at h3; simp [NE.get, h1, h2, h3]

/-- `NE.ge`: pointwise `nge`. -/
def NEge (x y : Nenv) : Prop := ∀ r, Nge (NE.get r x) (NE.get r y)

theorem nreg_agree {rs1 rs2 : RTL.Regset} {ne : Nenv} (h : eagree rs1 rs2 ne) (r : Reg) :
    vagree (rs1.get r) (rs2.get r) (nreg ne r) := h r

theorem eagree_ge {e1 e2 : RTL.Regset} {ne ne' : Nenv} (h : eagree e1 e2 ne) (hge : NEge ne ne') :
    eagree e1 e2 ne' := fun r => nge_agree (hge r) (h r)

theorem eagree_bot (e1 e2 : RTL.Regset) : eagree e1 e2 NE.bot := by
  intro r; rw [NE.get_bot]; trivial

theorem eagree_same (e : RTL.Regset) (ne : Nenv) : eagree e e ne := fun _ => vagree_same _ _

theorem eagree_update_1 {e1 e2 : RTL.Regset} {ne : Nenv} {v1 v2 : Val} {nv : Nval} (r : Reg)
    (h : eagree e1 e2 ne) (hv : vagree v1 v2 nv) :
    eagree (e1.set r v1) (e2.set r v2) (NE.set r nv ne) := by
  intro r0
  rw [NE.get_set, PMap.gsspec, PMap.gsspec]
  split
  · exact hv
  · exact h r0

theorem eagree_update {e1 e2 : RTL.Regset} {ne : Nenv} {v1 v2 : Val} (r : Reg)
    (hv : vagree v1 v2 (nreg ne r)) (h : eagree e1 e2 (NE.set r .Nothing ne)) :
    eagree (e1.set r v1) (e2.set r v2) ne := by
  intro r0
  have h0 := h r0
  rw [NE.get_set] at h0
  rw [PMap.gsspec, PMap.gsspec]
  split
  · subst r0; exact hv
  · rename_i hne; rw [if_neg hne] at h0; exact h0

theorem eagree_update_dead {e1 e2 : RTL.Regset} {ne : Nenv} {v1 : Val} (r : Reg)
    (hn : nreg ne r = .Nothing) (h : eagree e1 e2 ne) : eagree (e1.set r v1) e2 ne := by
  intro r0
  rw [PMap.gsspec]
  split
  · subst r0; unfold nreg at hn; rw [hn]; trivial
  · exact h r0

/-! ### Memory locations -/

section LOCATIONS
variable {F V : Type} (ge : Genv F V) (sp : Block)

theorem nlive_all (b : Block) (ofs : Z) : nlive ge sp nmemAll b ofs := by
  refine ⟨fun _ => ISet.In_empty ofs, fun id iv _ h => ?_⟩
  simp at h

private theorem findSymbol_inj {bc : BlockClassification} (hg : GenvMatch bc ge) {id id' : Ident}
    {b : Block} (h1 : Genv.findSymbol ge id = some b) (h2 : Genv.findSymbol ge id' = some b) :
    id = id' := by
  have e1 := (hg.1 id b).1 h1
  have e2 := (hg.1 id' b).1 h2
  rw [e1] at e2; cases e2; rfl

/-- `nlive_add` -/
theorem nlive_add {bc : BlockClassification} {b : Block} {ofs : Integers.Ptrofs} {p : Aptr}
    (nm : Nmem) {sz i : Z} (hg : GenvMatch bc ge) (hsp : bc sp = .BCstack)
    (hp : Pmatch bc b ofs p)
    (hi : Integers.Ptrofs.unsigned ofs ≤ i ∧ i < Integers.Ptrofs.unsigned ofs + sz) :
    nlive ge sp (nmemAdd nm p sz) b i := by
  cases nm with
  | NMemDead => exact nlive_all ge sp b i
  | NMem stk gl => ?_
  cases hp with
  | gl id hb =>
      have hfs : Genv.findSymbol ge id = some b := (hg.1 id b).2 hb
      unfold nmemAdd
      cases hgl : gl.get id with
      | some iv =>
          dsimp only; rw [hgl]
          refine ⟨fun h => ?_, fun id0 iv0 h1 h2 => ?_⟩
          · subst h; rw [hsp] at hb; cases hb
          · have := findSymbol_inj ge hg h1 hfs; subst this
            rw [PTree.gss] at h2; cases h2
            rw [ISet.In_remove]; intro ⟨hn, _⟩; exact hn hi
      | none =>
          dsimp only; rw [hgl]
          refine ⟨fun h => ?_, fun id0 iv0 h1 h2 => ?_⟩
          · subst h; rw [hsp] at hb; cases hb
          · have := findSymbol_inj ge hg h1 hfs; subst this
            rw [hgl] at h2; cases h2
  | glo id hb =>
      have hfs : Genv.findSymbol ge id = some b := (hg.1 id b).2 hb
      unfold nmemAdd
      refine ⟨fun h => ?_, fun id0 iv0 h1 h2 => ?_⟩
      · subst h; rw [hsp] at hb; cases hb
      · have := findSymbol_inj ge hg h1 hfs; subst this
        rw [PTree.grs] at h2; cases h2
  | glob id hb => exact nlive_all ge sp b i
  | stk hb =>
      unfold nmemAdd
      refine ⟨fun _ => ?_, fun id0 iv0 h1 _ => ?_⟩
      · rw [ISet.In_remove]; intro ⟨hn, _⟩; exact hn hi
      · have := (hg.1 id0 b).1 h1; rw [hb] at this; cases this
  | stack hb =>
      unfold nmemAdd
      refine ⟨fun _ => ISet.In_empty i, fun id0 iv0 h1 _ => ?_⟩
      have := (hg.1 id0 b).1 h1; rw [hb] at this; cases this
  | nonstack _ _ => exact nlive_all ge sp b i
  | top _ => exact nlive_all ge sp b i

/-- `incl_nmem_add` -/
theorem incl_nmem_add {nm : Nmem} {b : Block} {i : Z} (p : Aptr) (sz : Z)
    (h : nlive ge sp nm b i) : nlive ge sp (nmemAdd nm p sz) b i := by
  cases nm with
  | NMemDead => exact absurd h id
  | NMem stk gl =>
  obtain ⟨STK, GL⟩ := h
  cases p <;> unfold nmemAdd <;> try exact nlive_all ge sp b i
  · -- `Gl id ofs`
    rename_i id ofs
    cases hgl : gl.get id with
    | some iv =>
        dsimp only; rw [hgl]
        refine ⟨STK, fun id0 iv0 h1 h2 => ?_⟩
        rw [PTree.gsspec] at h2
        split at h2
        · cases h2; subst id0
          rw [ISet.In_remove]; intro ⟨_, hin⟩; exact GL _ _ h1 hgl hin
        · exact GL _ _ h1 h2
    | none => dsimp only; rw [hgl]; exact ⟨STK, GL⟩
  · -- `Glo id`
    refine ⟨STK, fun id0 iv0 h1 h2 => ?_⟩
    rw [PTree.grspec] at h2
    split at h2
    · cases h2
    · exact GL _ _ h1 h2
  · -- `Stk ofs`
    refine ⟨fun hb => ?_, GL⟩
    rw [ISet.In_remove]; intro ⟨_, hin⟩; exact STK hb hin
  · -- `Stack`
    exact ⟨fun _ => ISet.In_empty i, GL⟩

/-- `nlive_remove` -/
theorem nlive_remove {bc : BlockClassification} {b : Block} {ofs : Integers.Ptrofs} {p : Aptr}
    {nm : Nmem} {sz : Z} {b' : Block} {i : Z} (hg : GenvMatch bc ge) (hsp : bc sp = .BCstack)
    (hp : Pmatch bc b ofs p) (h : nlive ge sp nm b' i)
    (hout : b' ≠ b ∨ i < Integers.Ptrofs.unsigned ofs ∨ Integers.Ptrofs.unsigned ofs + sz ≤ i) :
    nlive ge sp (nmemRemove nm p sz) b' i := by
  cases nm with
  | NMemDead => exact absurd h id
  | NMem stk gl =>
  obtain ⟨STK, GL⟩ := h
  cases hp with
  | gl id hb =>
      have hfs : Genv.findSymbol ge id = some b := (hg.1 id b).2 hb
      unfold nmemRemove
      refine ⟨STK, fun id0 iv0 h1 h2 => ?_⟩
      rw [PTree.gsspec] at h2
      split at h2
      · cases h2; subst id0
        rcases hout with hne | hout
        · have h1' := (hg.1 id b').1 h1
          exact absurd (bc.bc_glob _ _ id h1' hb) hne
        · cases hgl : gl.get id with
          | some iv =>
              dsimp only
              rw [ISet.In_add]; rintro (⟨h3, h4⟩ | hin)
              · simp only [NeedDomain.pu, Z] at h3 h4 hout; omega
              · exact GL _ _ h1 hgl hin
          | none =>
              dsimp only
              rw [ISet.In_interval]; intro ⟨h3, h4⟩; simp only [NeedDomain.pu, Z] at h3 h4 hout; omega
      · exact GL _ _ h1 h2
  | stk hb =>
      unfold nmemRemove
      refine ⟨fun hb' => ?_, GL⟩
      rw [ISet.In_add]
      rintro (⟨h3, h4⟩ | hin)
      · rcases hout with hne | hout
        · subst hb'; exact hne (bc.bc_stack _ _ hsp hb)
        · simp only [NeedDomain.pu, Z] at h3 h4 hout; omega
      · exact STK hb' hin
  | glo _ _ => exact ⟨STK, GL⟩
  | glob _ _ => exact ⟨STK, GL⟩
  | stack _ => exact ⟨STK, GL⟩
  | nonstack _ _ => exact ⟨STK, GL⟩
  | top _ => exact ⟨STK, GL⟩

/-- `nlive_contains` -/
theorem nlive_contains {bc : BlockClassification} {b : Block} {ofs : Integers.Ptrofs} {p : Aptr}
    {nm : Nmem} {sz i : Z} (hg : GenvMatch bc ge) (hsp : bc sp = .BCstack)
    (hp : Pmatch bc b ofs p) (hc : nmemContains nm p sz = false)
    (hi : Integers.Ptrofs.unsigned ofs ≤ i ∧ i < Integers.Ptrofs.unsigned ofs + sz) :
    ¬ nlive ge sp nm b i := by
  intro hl
  cases nm with
  | NMemDead => exact hl
  | NMem stk gl =>
  obtain ⟨STK, GL⟩ := hl
  cases hp with
  | gl id hb =>
      have hfs : Genv.findSymbol ge id = some b := (hg.1 id b).2 hb
      simp only [nmemContains] at hc
      cases hgl : gl.get id with
      | some iv =>
          rw [hgl] at hc
          simp only [Bool.not_eq_false'] at hc
          exact GL _ _ hfs hgl ((ISet.contains_spec _ _ _).1 hc i hi.1 hi.2)
      | none => rw [hgl] at hc; cases hc
  | stk hb =>
      simp only [nmemContains, Bool.not_eq_false'] at hc
      have := bc.bc_stack _ _ hb hsp
      exact STK this ((ISet.contains_spec _ _ _).1 hc i hi.1 hi.2)
  | glo _ _ => simp [nmemContains] at hc
  | glob _ _ => simp [nmemContains] at hc
  | stack _ => simp [nmemContains] at hc
  | nonstack _ _ => simp [nmemContains] at hc
  | top _ => simp [nmemContains] at hc

/-- `nlive_dead_stack` -/
theorem nlive_dead_stack (sz : Z) (b' : Block) (i : Z) (h : b' ≠ sp ∨ ¬ (0 ≤ i ∧ i < sz)) :
    nlive ge sp (nmemDeadStack sz) b' i := by
  refine ⟨fun hb => ?_, fun id iv _ h2 => ?_⟩
  · rw [ISet.In_interval]; rcases h with h | h
    · exact absurd hb h
    · exact h
  · simp at h2

/-- `nlive_lub_l` -/
theorem nlive_lub_l {nm1 : Nmem} (nm2 : Nmem) {b : Block} {i : Z} (h : nlive ge sp nm1 b i) :
    nlive ge sp (nmemLub nm1 nm2) b i := by
  cases nm1 with
  | NMemDead => exact absurd h id
  | NMem stk1 gl1 =>
  obtain ⟨STK, GL⟩ := h
  cases nm2 with
  | NMemDead => exact ⟨STK, GL⟩
  | NMem stk2 gl2 =>
  refine ⟨fun hb => ?_, fun id iv h1 h2 => ?_⟩
  · rw [ISet.In_inter]; intro ⟨hin, _⟩; exact STK hb hin
  · rw [PTree.gcombine _ rfl] at h2
    cases hg1 : gl1.get id <;> cases hg2 : gl2.get id <;> simp only [hg1, hg2] at h2 <;>
      try cases h2
    rw [ISet.In_inter]; intro ⟨hin, _⟩; exact GL _ _ h1 hg1 hin

/-- `nlive_lub_r` -/
theorem nlive_lub_r (nm1 : Nmem) {nm2 : Nmem} {b : Block} {i : Z} (h : nlive ge sp nm2 b i) :
    nlive ge sp (nmemLub nm1 nm2) b i := by
  cases nm2 with
  | NMemDead => exact absurd h id
  | NMem stk2 gl2 =>
  obtain ⟨STK, GL⟩ := h
  cases nm1 with
  | NMemDead => exact ⟨STK, GL⟩
  | NMem stk1 gl1 =>
  refine ⟨fun hb => ?_, fun id iv h1 h2 => ?_⟩
  · rw [ISet.In_inter]; intro ⟨_, hin⟩; exact STK hb hin
  · rw [PTree.gcombine _ rfl] at h2
    cases hg1 : gl1.get id <;> cases hg2 : gl2.get id <;> simp only [hg1, hg2] at h2 <;>
      try cases h2
    rw [ISet.In_inter]; intro ⟨_, hin⟩; exact GL _ _ h1 hg2 hin

/-- `nmem_beq_sound` -/
theorem nmem_beq_sound {nm1 nm2 : Nmem} (h : nmemBeq nm1 nm2 = true) (b : Block) (ofs : Z) :
    nlive ge sp nm1 b ofs ↔ nlive ge sp nm2 b ofs := by
  cases nm1 <;> cases nm2 <;> simp only [nmemBeq, Bool.false_eq_true] at h
  · exact Iff.rfl
  · rename_i stk1 gl1 stk2 gl2
    simp only [Bool.and_eq_true] at h
    obtain ⟨hs, hgl⟩ := h
    have hgl' := ptreeBeq_correct _ gl1 gl2 hgl
    constructor
    · rintro ⟨STK, GL⟩
      refine ⟨fun hb hin => STK hb ((ISet.beq_sound hs _).2 hin), fun id iv h1 h2 hin => ?_⟩
      rcases hgl' id with ⟨_, h3⟩ | ⟨x, y, h3, h4, h5⟩
      · rw [h3] at h2; cases h2
      · rw [h4] at h2; cases h2
        exact GL _ _ h1 h3 ((ISet.beq_sound h5 _).2 hin)
    · rintro ⟨STK, GL⟩
      refine ⟨fun hb hin => STK hb ((ISet.beq_sound hs _).1 hin), fun id iv h1 h2 hin => ?_⟩
      rcases hgl' id with ⟨h3, _⟩ | ⟨x, y, h3, h4, h5⟩
      · rw [h3] at h2; cases h2
      · rw [h3] at h2; cases h2
        exact GL _ _ h1 h4 ((ISet.beq_sound h5 _).1 hin)

end LOCATIONS

/-! ### The lattice `NA` -/

/-- `NA.ge`: CompCert's order on the abstract states of the analysis. -/
def NAge (x y : NAT) : Prop :=
  NEge x.1 y.1 ∧
    ∀ {F V : Type} (ge : Genv F V) sp b ofs, nlive ge sp y.2 b ofs → nlive ge sp x.2 b ofs

/-- The order of the free lattice `NA.lat` is included in `NA.ge`. -/
theorem NAge_of_free {x y : NAT} (h : NA.lat.ge x y) : NAge x y := by
  refine Semilattice.freeGe_le NA.beq NA.bot NA.lub NAge ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro x; exact ⟨fun r => nge_refl _, fun _ _ _ _ h => h⟩
  · intro x y hb
    simp only [NA.beq, Bool.and_eq_true] at hb
    obtain ⟨h1, h2⟩ := hb
    exact ⟨⟨fun r => by rw [NE.get_beq h1 r]; exact nge_refl _,
            fun ge sp b ofs h => (nmem_beq_sound ge sp h2 b ofs).2 h⟩,
           ⟨fun r => by rw [NE.get_beq h1 r]; exact nge_refl _,
            fun ge sp b ofs h => (nmem_beq_sound ge sp h2 b ofs).1 h⟩⟩
  · intro x y z hxy hyz
    exact ⟨fun r => nge_trans (hxy.1 r) (hyz.1 r), fun ge sp b ofs h => hxy.2 ge sp b ofs (hyz.2 ge sp b ofs h)⟩
  · intro x
    exact ⟨fun r => by rw [show NA.bot.1 = NE.bot from rfl, NE.get_bot]; exact .all _,
      fun _ _ _ _ h => absurd h id⟩
  · intro x y
    exact ⟨fun r => by rw [show (NA.lub x y).1 = NE.lub x.1 y.1 from rfl, NE.get_lub]; exact nge_lub_l _ _,
      fun ge sp b ofs h => nlive_lub_l ge sp _ h⟩
  · intro x y
    exact ⟨fun r => by rw [show (NA.lub x y).1 = NE.lub x.1 y.1 from rfl, NE.get_lub]; exact nge_lub_r _ _,
      fun ge sp b ofs h => nlive_lub_r ge sp _ h⟩

end NeedDomain
end CC
