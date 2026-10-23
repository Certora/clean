/-
  Matching and memory injections — port of the `inj_of_bc` part of
  `backend/ValueDomain.v`.

  Ported: `inj_of_bc_valid`, `inj_of_bc_inv`, `pmatch_inj`, `vmatch_inj`,
  `vmatch_list_inj`, `mmatch_inj`, `inj_of_bc_preserves_globals`,
  `pmatch_inj_top`, `vmatch_inj_top`, `mmatch_inj_top`.

  Differences from Rocq: `mmatch_inj` drops the hypothesis
  `bc_below bc (Mem.nextblock m)`, which is already a field of `mmatch`;
  `inj_of_bc_preserves_globals` takes `Genv.DefsBelow ge` (an invariant of
  `Genv.t` in Rocq, proved here for every `globalenv` by
  `Genv.defsBelow_globalenv`).
-/
import CCLib.backend.ValueDomainMmatch
import CCLib.common.MemoryInjections
import CCLib.common.Separation
import CCLib.common.LinkingTheory

namespace CC
namespace ValueDomain

open Integers (Ptrofs)

/-- `ValueDomain.inj_of_bc_valid` -/
theorem inj_of_bc_valid (bc : BlockClassification) {b : Block} (h : bc b ≠ .BCinvalid) :
    injOfBc bc b = some (b, 0) := by
  unfold injOfBc; split
  · rename_i e; exact absurd e h
  · rfl

/-- `ValueDomain.inj_of_bc_inv` -/
theorem inj_of_bc_inv (bc : BlockClassification) {b b' : Block} {delta : Z}
    (h : injOfBc bc b = some (b', delta)) : bc b ≠ .BCinvalid ∧ b' = b ∧ delta = 0 := by
  unfold injOfBc at h; split at h
  · cases h
  · rename_i hne; cases h; exact ⟨hne, rfl, rfl⟩

variable {bc : BlockClassification}

/-- `ValueDomain.pmatch_inj` -/
theorem pmatch_inj {b : Block} {ofs : Ptrofs} {p : Aptr} (h : Pmatch bc b ofs p) :
    injOfBc bc b = some (b, 0) := by
  apply inj_of_bc_valid
  cases h <;> simp_all

/-- `ValueDomain.vmatch_inj` -/
theorem vmatch_inj {v : Val} {x : Aval} (h : Vmatch bc v x) : Val.Inject (injOfBc bc) v v := by
  cases h with
  | ptr b ofs p hp => exact .ptr 0 (pmatch_inj hp) (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])
  | ifptr_p b ofs p hp => exact .ptr 0 (pmatch_inj hp) (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])
  | _ => constructor

/-- `ValueDomain.vmatch_list_inj` -/
theorem vmatch_list_inj {vl : List Val} {xl : List Aval} (h : ListForall2 (Vmatch bc) vl xl) :
    Val.InjectList (injOfBc bc) vl vl := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (vmatch_inj h) ih

/-- A readable byte can be loaded alone. -/
private theorem loadbytes_one {m : Mem} {b : Block} {ofs : _root_.Int}
    (hp : Mem.perm m b ofs .Cur .Readable = true) :
    Mem.loadbytes m b ofs 1 = some [ZMap.get ofs (PMap.get b m.contents)] := by
  unfold Mem.loadbytes
  rw [if_pos (Mem.rangePerm_intro _ _ _ _ _ _ (fun o h1 h2 => by
    have : o = ofs := by omega
    subst this; exact hp))]
  rfl

/-- `ValueDomain.mmatch_inj` -/
theorem mmatch_inj {m : Mem} {am : Amem} (hm : Mmatch bc m am) : Mem.Inject (injOfBc bc) m m := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b1 b2 delta ofs k p hf hp
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc hf
    rw [Int.add_zero]; exact hp
  · intro b1 b2 delta ofs sz p hf _ _
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc hf
    exact Int.dvd_zero _
  · intro b1 ofs b2 delta hf hp
    obtain ⟨A, rfl, rfl⟩ := inj_of_bc_inv bc hf
    rw [Int.add_zero]
    have L := loadbytes_one hp
    generalize ZMap.get ofs (PMap.get b2 m.contents) = mv at L ⊢
    cases mv with
    | Undef => exact .undef _
    | Byte n => exact .byte n
    | Fragment v q n =>
      refine .frag q n ?_
      cases v with
      | Vptr b i =>
        have PM : Pmatch bc b i .Ptop := pmatch_top' ((hm.mmatch_top _ A).2 ofs b i q n L)
        exact .ptr 0 (pmatch_inj PM) (by rw [Ptrofs.repr_zero, Ptrofs.add_zero])
      | _ => constructor
  · intro b hv
    unfold injOfBc
    split
    · rfl
    · rename_i hne
      have := hm.mmatch_below b hne
      rw [← Bool.not_eq_true, Mem.validBlock_iff] at hv
      exact absurd this hv
  · intro b b' delta hf
    obtain ⟨A, rfl, rfl⟩ := inj_of_bc_inv bc hf
    rw [Mem.validBlock_iff]; exact hm.mmatch_below _ A
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne h1 h2 _ _
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc h1
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc h2
    exact .inl hne
  · intro b b' delta ofs hf _
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc hf
    have := Ptrofs.unsigned_range_2 ofs
    exact ⟨Int.le_refl _, by rw [Int.add_zero]; exact this.1, by rw [Int.add_zero]; exact this.2⟩
  · intro b1 ofs b2 delta k p hf hp
    obtain ⟨_, rfl, rfl⟩ := inj_of_bc_inv bc hf
    rw [Int.add_zero] at hp; exact .inl hp
  · intro b b' delta ofs hf _ _
    exact (inj_of_bc_inv bc hf).2.2

/-- `ValueDomain.inj_of_bc_preserves_globals` -/
theorem inj_of_bc_preserves_globals {F V : Type} {ge : Genv F V} (hg : GenvMatch bc ge)
    (hdefs : Genv.DefsBelow ge) : Separation.MeminjPreservesGlobals ge (injOfBc bc) := by
  obtain ⟨A, B⟩ := hg
  refine ⟨fun id b h => inj_of_bc_valid bc (by rw [(A id b).1 h]; simp), fun b gv h => ?_,
    fun b1 b2 delta gv _ hf => (inj_of_bc_inv bc hf).2.1⟩
  exact inj_of_bc_valid bc (B b (hdefs b _ ((Genv.findVarInfo_iff ge b gv).1 h))).1

/-- `ValueDomain.pmatch_inj_top` -/
theorem pmatch_inj_top {b b' : Block} {delta : Z} (ofs : Ptrofs)
    (h : injOfBc bc b = some (b', delta)) : Pmatch bc b ofs .Ptop :=
  .top (inj_of_bc_inv bc h).1

/-- `ValueDomain.vmatch_inj_top` -/
theorem vmatch_inj_top {v v' : Val} (h : Val.Inject (injOfBc bc) v v') : Vmatch bc v Vtop := by
  cases h with
  | ptr delta hf _ => exact .ifptr_p _ _ _ (pmatch_inj_top _ hf)
  | _ => constructor

/-- `ValueDomain.mmatch_inj_top` -/
theorem mmatch_inj_top {m m' : Mem} (h : Mem.Inject (injOfBc bc) m m') : Mmatch bc m mtop := by
  have SM : ∀ b, bc b ≠ .BCinvalid → Smatch bc m b .Ptop := by
    intro b hb
    refine ⟨fun chunk ofs v hl => ?_, fun ofs b' ofs' q i hl => ?_⟩
    · obtain ⟨v', _, B⟩ := Mem.load_inject h hl (inj_of_bc_valid bc hb)
      exact vmatch_inj_top B
    · obtain ⟨bytes', _, B⟩ := Mem.loadbytes_inject h hl (inj_of_bc_valid bc hb)
      cases B with
      | cons hmv _ =>
        cases hmv with
        | frag _ _ hv =>
          cases hv with
          | ptr delta hf _ => exact pmatch_inj_top _ hf
  refine ⟨fun b hb => ?_, fun id ab b _ hg => ?_, fun b _ h2 => SM b h2, fun b hb => SM b hb, ?_⟩
  · exact ablock_init_sound (SM b (by rw [hb]; simp))
  · simp [mtop, minit] at hg
  · intro b hb
    exact (Mem.validBlock_iff m b).1 (Mem.validBlock_inject_1 (inj_of_bc_valid bc hb) h)

end ValueDomain
end CC
