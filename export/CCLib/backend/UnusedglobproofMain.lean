/-
  Elimination of unreferenced static definitions: semantic preservation —
  port of `backend/Unusedglobproof.v`, part 4 (lines 1052–1252): relating
  the initial memory states (`init_meminj_invert_strong`,
  `bytes_of_init_inject`, `init_mem_inj_1/2`, `init_mem_exists`,
  `init_mem_inject`), initial and final states, and the main theorem
  `transf_program_correct`.
-/
import CCLib.backend.UnusedglobproofStep
import CCLib.common.GlobalenvsInitChar

namespace CC
namespace Unusedglob

open Op RTL Smallstep
open Integers (Ptrofs)

theorem memvalInjectList_append {f : Val.Meminj} {l1 l1' l2 l2' : List MemVal}
    (h1 : MemvalInjectList f l1 l1') (h2 : MemvalInjectList f l2 l2') :
    MemvalInjectList f (l1 ++ l2) (l1' ++ l2') := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem memvalInjectList_refl_bytes {f : Val.Meminj} (n : Nat) (x : Integers.Byte) :
    MemvalInjectList f (List.replicate n (MemVal.Byte x)) (List.replicate n (MemVal.Byte x)) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (.byte _) ih

theorem memvalInjectList_undef {f : Val.Meminj} (n : Nat) :
    MemvalInjectList f (List.replicate n MemVal.Undef) (List.replicate n MemVal.Undef) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (.undef _) ih

/-- `Unusedglobproof.Mem_getN_forall2` (for `memval_inject`). -/
theorem getN_forall2 {f : Val.Meminj} {c1 c2 : ZMap MemVal} {i : Z} :
    ∀ (n : Nat) (q : Z), MemvalInjectList f (Mem.getN n q c1) (Mem.getN n q c2) →
      q ≤ i → i < q + n → MemvalInject f (ZMap.get i c1) (ZMap.get i c2)
  | 0, q, _, h1, h2 => by simp only [CC.Z] at *; omega
  | n + 1, q, h, h1, h2 => by
    simp only [Mem.getN] at h
    cases h with
    | cons ha hl =>
      by_cases e : i = q
      · subst e; exact ha
      · exact getN_forall2 n (q + 1) hl (by simp only [CC.Z] at *; omega)
          (by simp only [CC.Z] at *; omega)

section SOUNDNESS
variable {p tp : RTL.Program} {used : IS}
variable (TRANSF : MatchProg1 used p tp) (USED : ValidUsedSet p used)

include TRANSF USED in
/-- `Unusedglobproof.init_meminj_invert_strong` -/
theorem init_meminj_invert_strong {b b' : Block} {delta : Z}
    (h : initMeminj p tp b = some (b', delta)) :
    delta = 0 ∧ ∃ id gd, Genv.findSymbol p.globalenv id = some b ∧
      Genv.findSymbol tp.globalenv id = some b' ∧
      Genv.findDef p.globalenv b = some gd ∧ Genv.findDef tp.globalenv b' = some gd ∧
      ∀ i, RefDef gd i → i ∈ used := by
  obtain ⟨A, id, B, C⟩ := init_meminj_invert h
  obtain ⟨gd, DM⟩ := ASTProgram.defmap_dom (Genv.findSymbol_inversion B)
  rw [ASTProgram.defmap_eq, Genv.find_def_symbol] at DM
  obtain ⟨b'', P, Q⟩ := DM
  have : b'' = b := by
    have := P.symm.trans B
    cases this; rfl
  subst this
  obtain ⟨X, _, Y⟩ := (init_meminj_preserves_globals TRANSF USED).defs_inject _ _ _ _ h Q
  exact ⟨A, id, gd, B, C, Q, X, Y⟩

include TRANSF USED in
/-- `Unusedglobproof.bytes_of_init_inject` -/
theorem bytes_of_init_inject : ∀ (il : List InitData), (∀ id, RefInit il id → id ∈ used) →
    MemvalInjectList (initMeminj p tp) (Genv.bytesOfInitDataList p.globalenv il)
      (Genv.bytesOfInitDataList tp.globalenv il)
  | [], _ => .nil
  | i1 :: il, hk => by
    simp only [Genv.bytesOfInitDataList]
    refine memvalInjectList_append ?_
      (bytes_of_init_inject il fun id ⟨o, hin⟩ => hk id ⟨o, List.mem_cons_of_mem _ hin⟩)
    have G := init_meminj_preserves_globals TRANSF USED
    cases i1 with
    | Init_int8 n => exact injBytes_inject _
    | Init_int16 n => exact injBytes_inject _
    | Init_int32 n => exact injBytes_inject _
    | Init_int64 n => exact injBytes_inject _
    | Init_float32 n => exact injBytes_inject _
    | Init_float64 n => exact injBytes_inject _
    | Init_space n => exact memvalInjectList_refl_bytes _ _
    | Init_addrof i o =>
      simp only [Genv.bytesOfInitData]
      cases FS : Genv.findSymbol p.globalenv i with
      | some b =>
        have hki : i ∈ used := hk i ⟨o, List.mem_cons_self ..⟩
        obtain ⟨b', A, B⟩ := G.symbols_inject_2 i b hki FS
        simp only [A]
        exact injValue_inject _ (.ptr _ B (by rw [Ptrofs.repr_zero, Ptrofs.add_zero]))
      | none =>
        cases FS' : Genv.findSymbol tp.globalenv i with
        | some b' =>
          obtain ⟨b, A, _⟩ := G.symbols_inject_3 i b' FS'
          rw [FS] at A; cases A
        | none => exact memvalInjectList_undef _

section INIT_MEM
variable {m tm : Mem} (IM : p.initMem = some m) (TIM : tp.initMem = some tm)

theorem getN_of_loadbytes {m : Mem} {b : Block} {n : Z} {bytes : List MemVal}
    (h : Mem.loadbytes m b 0 n = some bytes) :
    Mem.getN n.toNat 0 (PMap.get b m.contents) = bytes := by
  unfold Mem.loadbytes at h
  split at h
  · cases h; rfl
  · cases h

theorem not_volatile_of_permOrder {V : Type} {v : GlobVar V} {q : Permission}
    (hq : q ≠ .Nonempty) (h : permOrder (Genv.permGlobvar v) q = true) : v.gvar_volatile = false := by
  cases hv : v.gvar_volatile with
  | false => rfl
  | true =>
    simp only [Genv.permGlobvar, hv, if_true] at h
    exact absurd (Genv.permOrder_nonempty h) hq

include TRANSF USED IM TIM in
/-- `Unusedglobproof.init_mem_inj_1` -/
theorem init_mem_inj_1 : Mem.MemInj (initMeminj p tp) m tm where
  perm b1 b2 delta ofs k q hf hp := by
    obtain ⟨A, id, gd, B, C, D, E, F⟩ := init_meminj_invert_strong TRANSF USED hf
    subst A
    have H1 := Genv.initMem_characterization_gen IM b1 gd D
    have H2 := Genv.initMem_characterization_gen TIM b2 gd E
    rw [Int.add_zero]
    cases gd with
    | Gfun f =>
      obtain ⟨rfl, rfl⟩ := H1.2 ofs k q hp
      exact Mem.perm_cur H2.1
    | Gvar v =>
      obtain ⟨h1, h2, h3⟩ := H1.2.1 ofs k q hp
      exact Mem.perm_cur (Mem.perm_implies (Mem.rangePerm_perm _ _ _ _ _ _ H2.1 ofs h1 h2) h3)
  align b1 b2 delta ofs sz q hf _ _ := by
    obtain ⟨A, _⟩ := init_meminj_invert hf
    subst A; exact Int.dvd_zero _
  memval b1 ofs b2 delta hf hp := by
    obtain ⟨A, id, gd, B, C, D, E, F⟩ := init_meminj_invert_strong TRANSF USED hf
    subst A
    have H1 := Genv.initMem_characterization_gen IM b1 gd D
    have H2 := Genv.initMem_characterization_gen TIM b2 gd E
    rw [Int.add_zero]
    cases gd with
    | Gfun f =>
      have := (H1.2 ofs _ _ hp).2; cases this
    | Gvar v =>
      obtain ⟨h1, h2, h3⟩ := H1.2.1 ofs _ _ hp
      have NO := not_volatile_of_permOrder (by decide) h3
      have L1 := getN_of_loadbytes (H1.2.2 NO)
      have L2 := getN_of_loadbytes (H2.2.2 NO)
      have hsz := Genv.InitData.listSize_nonneg v.gvar_init
      refine getN_forall2 (InitData.listSize v.gvar_init).toNat 0 ?_ h1
        (by simp only [CC.Z] at *; omega)
      rw [L1, L2]
      exact bytes_of_init_inject TRANSF USED _ F

include TRANSF USED IM TIM in
/-- `Unusedglobproof.init_mem_inj_2` -/
theorem init_mem_inj_2 : Mem.Inject (initMeminj p tp) m tm where
  inj := init_mem_inj_1 TRANSF USED IM TIM
  freeblocks b hv := by
    cases hf : initMeminj p tp b with
    | none => rfl
    | some x =>
      obtain ⟨b', delta⟩ := x
      obtain ⟨_, id, B, _⟩ := init_meminj_invert hf
      rw [Genv.findSymbol_not_fresh IM B] at hv; cases hv
  mappedblocks b b' delta hf := by
    obtain ⟨_, id, _, C⟩ := init_meminj_invert hf
    exact Genv.findSymbol_not_fresh TIM C
  no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hne h1 h2 _ _ := by
    obtain ⟨_, id1, B1, C1⟩ := init_meminj_invert h1
    obtain ⟨_, id2, B2, C2⟩ := init_meminj_invert h2
    by_cases e : id1 = id2
    · subst e; rw [B1] at B2; cases B2; exact absurd rfl hne
    · exact .inl (Genv.global_addresses_distinct (symbInjective_prog tp) e C1 C2)
  representable b b' delta ofs hf _ := by
    obtain ⟨A, _⟩ := init_meminj_invert hf
    subst A
    have := Ptrofs.unsigned_range_2 ofs
    refine ⟨Int.le_refl _, ?_, ?_⟩ <;> rw [Int.add_zero]
    · exact this.1
    · exact this.2
  perm_inv b1 ofs b2 delta k q hf hp := by
    obtain ⟨A, id, gd, B, C, D, E, F⟩ := init_meminj_invert_strong TRANSF USED hf
    subst A
    have H1 := Genv.initMem_characterization_gen IM b1 gd D
    have H2 := Genv.initMem_characterization_gen TIM b2 gd E
    rw [Int.add_zero] at hp
    left
    cases gd with
    | Gfun f =>
      obtain ⟨rfl, rfl⟩ := H2.2 ofs k q hp
      exact Mem.perm_cur H1.1
    | Gvar v =>
      obtain ⟨h1, h2, h3⟩ := H2.2.1 ofs k q hp
      exact Mem.perm_cur (Mem.perm_implies (Mem.rangePerm_perm _ _ _ _ _ _ H1.1 ofs h1 h2) h3)
  metadata b b' delta ofs hf _ _ := (init_meminj_invert hf).1

end INIT_MEM

include TRANSF USED in
/-- `Unusedglobproof.init_mem_exists` -/
theorem init_mem_exists {m : Mem} (IM : p.initMem = some m) : ∃ tm, tp.initMem = some tm := by
  refine Genv.initMem_exists _ _ fun id v hin => ?_
  have P : tp.defmap.get id = some (.Gvar v) := ASTProgram.defmap_norepet TRANSF.unique hin
  rw [TRANSF.defs id] at P
  split at P
  · next hm =>
    have hk := IS.mem_iff.1 hm
    obtain ⟨AL, FV⟩ := Genv.initMem_inversion IM (ASTProgram.in_defmap P)
    refine ⟨AL, fun i o hio => ?_⟩
    obtain ⟨b, FS⟩ := FV i o hio
    exact transform_find_symbol_1 TRANSF FS (USED.closed id (.Gvar v) i hk P ⟨o, hio⟩)
  · cases P

include TRANSF USED in
/-- `Unusedglobproof.init_mem_inject` -/
theorem init_mem_inject {m : Mem} (IM : p.initMem = some m) :
    ∃ f tm, tp.initMem = some tm ∧ Mem.Inject f m tm ∧ MeminjPreservesGlobals p tp used f := by
  obtain ⟨tm, TIM⟩ := init_mem_exists TRANSF USED IM
  exact ⟨initMeminj p tp, tm, TIM, init_mem_inj_2 TRANSF USED IM TIM,
    init_meminj_preserves_globals TRANSF USED⟩

include TRANSF USED in
/-- `Unusedglobproof.transf_initial_states` -/
theorem transf_initial_states {S1 : RTL.State} (h : RTL.InitialState p S1) :
    ∃ S2, RTL.InitialState tp S2 ∧ MatchStates p tp used S1 S2 := by
  cases h with
  | intro b f m hm hs hf hsig =>
    obtain ⟨j, tm, A, B, C⟩ := init_mem_inject TRANSF USED hm
    obtain ⟨tb, P, Q⟩ := C.symbols_inject_2 _ b USED.main hs
    rw [Genv.findFunctPtr_iff] at hf
    obtain ⟨R, _, T⟩ := C.defs_inject _ _ _ _ Q hf
    rw [← Genv.findFunctPtr_iff] at R
    refine ⟨_, .intro tb f tm A (by rw [TRANSF.main_eq]; exact P) R hsig, ?_⟩
    refine .call _ _ _ _ _ _ _ _ (.nil _ _ C ?_ ?_) T .nil B
    · rw [← Genv.initMem_genv_next hm]; exact Nat.le_refl _
    · rw [← Genv.initMem_genv_next A]; exact Nat.le_refl _

/-- `Unusedglobproof.transf_final_states` -/
theorem transf_final_states {S1 S2 : RTL.State} {r : Integers.Int}
    (hm : MatchStates p tp used S1 S2) (h : RTL.FinalState S1 r) : RTL.FinalState S2 r := by
  cases h with
  | intro r m =>
    cases hm with
    | ret _ _ _ ts tres tm j STACKS RESINJ _ =>
      cases STACKS
      cases RESINJ
      exact .intro _ _

include TRANSF USED in
/-- `Unusedglobproof.transf_program_correct_1` -/
theorem transf_program_correct_1
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg)) :
    ForwardSimulation (RTL.semantics p) (RTL.semantics tp) :=
  forward_simulation_plus (L1 := RTL.semantics p) (L2 := RTL.semantics tp)
    (MatchStates p tp used)
    (fun id => (globals_symbols_inject TRANSF USED
      (init_meminj_preserves_globals TRANSF USED)).public_eq id)
    (fun _ h => transf_initial_states TRANSF USED h)
    (fun _ _ _ hm h => transf_final_states hm h)
    (fun _ _ _ hst _ hm => by
      obtain ⟨S2', A, B⟩ := step_simulation TRANSF USED hext hasm hst hm
      exact ⟨S2', plus_one A, B⟩)

end SOUNDNESS

/-- `Unusedglobproof.transf_program_correct`: removing unreferenced static
    definitions preserves the semantics of RTL programs (forward simulation).

    `hext` / `hasm` state that external functions and inline assembly are
    compatible with memory injections (`ec_mem_inject`); CompCert assumes this
    by axiom (`external_functions_properties`, `inline_assembly_properties`). -/
theorem transf_program_correct (p tp : RTL.Program) (h : transformProgram p = .OK tp)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg)) :
    ForwardSimulation (RTL.semantics p) (RTL.semantics tp) := by
  obtain ⟨used, USED, TRANSF⟩ := transf_program_match h
  exact transf_program_correct_1 TRANSF USED hext hasm

end Unusedglob
end CC
