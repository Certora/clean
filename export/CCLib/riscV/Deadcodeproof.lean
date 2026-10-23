/-
  [RISC-V instance of `CCLib/backend/Deadcodeproof.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Elimination of unneeded computations over RTL: correctness proof — port of
  `backend/Deadcodeproof.v`, part 2: properties of the need environment
  (`add_need_all_eagree` … `add_ros_need_eagree`, `eagree_init_regs`),
  `is_dead_sound_1/2`, `is_int_zero_sound`, builtin arguments
  (`eagree_set_res`, `transfer_builtin_arg_sound`,
  `transfer_builtin_args_sound`, `can_eval_builtin_arg(s)`), volatile stores
  (`transf_volatile_store`), `eagree_set_undef` and external calls
  (`transf_external_call`).

  The memory relation `magree` is in `DeadcodeproofMem.lean`; the simulation
  proof is in `DeadcodeproofStep.lean`.
-/
import CCLib.riscV.DeadcodeproofMem
import CCLib.backend.NeedDomainProof3
import CCLib.riscV.Deadcode
import CCLib.riscV.NeedOp
import CCLib.common.EventsExtends

namespace CC
namespace RiscV
namespace Deadcodeproof

open ValueDomain ValueAnalysis RTL NeedDomain NeedOp Deadcode Op
open Integers (Ptrofs)

/-! ## Properties of the need environment -/

/-- `Deadcodeproof.add_need_all_eagree` -/
theorem add_need_all_eagree {e e' : RTL.Regset} {r : Reg} {ne : Nenv}
    (h : eagree e e' (addNeedAll r ne)) : eagree e e' ne := by
  intro r0
  have h0 := h r0
  unfold addNeedAll at h0
  rw [NE.get_set] at h0
  split at h0
  · exact vagree_lessdef _ (lessdef_vagree h0)
  · exact h0

/-- `Deadcodeproof.add_need_all_lessdef` -/
theorem add_need_all_lessdef {e e' : RTL.Regset} {r : Reg} {ne : Nenv}
    (h : eagree e e' (addNeedAll r ne)) : Val.Lessdef (e.get r) (e'.get r) := by
  have h0 := h r
  unfold addNeedAll at h0
  rw [NE.get_set, if_pos rfl] at h0
  exact lessdef_vagree h0

/-- `Deadcodeproof.add_need_eagree` -/
theorem add_need_eagree {e e' : RTL.Regset} {r : Reg} {nv : Nval} {ne : Nenv}
    (h : eagree e e' (addNeed r nv ne)) : eagree e e' ne := by
  intro r0
  have h0 := h r0
  unfold addNeed at h0
  rw [NE.get_set] at h0
  split at h0
  · subst r0; exact nge_agree (nge_lub_r _ _) h0
  · exact h0

/-- `Deadcodeproof.add_need_vagree` -/
theorem add_need_vagree {e e' : RTL.Regset} {r : Reg} {nv : Nval} {ne : Nenv}
    (h : eagree e e' (addNeed r nv ne)) : vagree (e.get r) (e'.get r) nv := by
  have h0 := h r
  unfold addNeed at h0
  rw [NE.get_set, if_pos rfl] at h0
  exact nge_agree (nge_lub_l _ _) h0

/-- `Deadcodeproof.add_needs_all_eagree` -/
theorem add_needs_all_eagree : ∀ {rl : List Reg} {e e' : RTL.Regset} {ne : Nenv},
    eagree e e' (addNeedsAll rl ne) → eagree e e' ne
  | [], _, _, _, h => h
  | _ :: rl, _, _, _, h => add_needs_all_eagree (rl := rl) (add_need_all_eagree h)

/-- `Deadcodeproof.add_needs_all_lessdef` -/
theorem add_needs_all_lessdef : ∀ {rl : List Reg} {e e' : RTL.Regset} {ne : Nenv},
    eagree e e' (addNeedsAll rl ne) → Val.LessdefList (e.getList rl) (e'.getList rl)
  | [], _, _, _, _ => .nil
  | _ :: rl, _, _, _, h =>
    .cons (add_need_all_lessdef h) (add_needs_all_lessdef (rl := rl) (add_need_all_eagree h))

/-- `Deadcodeproof.add_needs_eagree` -/
theorem add_needs_eagree : ∀ {rl : List Reg} {nvl : List Nval} {e e' : RTL.Regset} {ne : Nenv},
    eagree e e' (addNeeds rl nvl ne) → eagree e e' ne
  | [], _, _, _, _, h => h
  | _ :: _, [], _, _, _, h => add_needs_all_eagree h
  | _ :: rl, _ :: nvl, _, _, _, h => add_needs_eagree (rl := rl) (nvl := nvl) (add_need_eagree h)

/-- `Deadcodeproof.add_needs_vagree` -/
theorem add_needs_vagree : ∀ {rl : List Reg} {nvl : List Nval} {e e' : RTL.Regset} {ne : Nenv},
    eagree e e' (addNeeds rl nvl ne) → VagreeList (e.getList rl) (e'.getList rl) nvl
  | [], nvl, _, _, _, _ => .nil nvl
  | r :: rl, [], _, _, _, h =>
    vagree_lessdef_list (add_needs_all_lessdef (rl := r :: rl) h) []
  | _ :: rl, _ :: nvl, _, _, _, h =>
    .cons (add_need_vagree h) (add_needs_vagree (rl := rl) (nvl := nvl) (add_need_eagree h))

/-- `Deadcodeproof.add_ros_need_eagree` -/
theorem add_ros_need_eagree {e e' : RTL.Regset} {ros : Sum Reg Ident} {ne : Nenv}
    (h : eagree e e' (addRosNeedAll ros ne)) : eagree e e' ne := by
  cases ros with
  | inl r => exact add_need_all_eagree h
  | inr _ => exact h

/-- `Deadcodeproof.eagree_init_regs` -/
theorem eagree_init_regs : ∀ (rl : List Reg) {vl1 vl2 : List Val} (ne : Nenv),
    Val.LessdefList vl1 vl2 → eagree (initRegs vl1 rl) (initRegs vl2 rl) ne
  | [], vl1, vl2, ne, _ => by
    cases vl1 <;> cases vl2 <;> exact eagree_same _ _
  | r :: rl, _, _, ne, .nil => eagree_same _ _
  | r :: rl, _, _, ne, .cons h hl =>
    eagree_update r (vagree_lessdef _ h) (eagree_init_regs rl _ hl)

/-! ## Basic properties of the translation -/

/-- `Deadcodeproof.is_dead_sound_1` -/
theorem is_dead_sound_1 {nv : Nval} (h : isDead nv = true) : nv = .Nothing := by
  cases nv <;> first | rfl | cases h

/-- `Deadcodeproof.is_dead_sound_2` -/
theorem is_dead_sound_2 {nv : Nval} (h : isDead nv = false) : nv ≠ .Nothing := by
  rintro rfl; cases h

/-- `Deadcodeproof.is_int_zero_sound` -/
theorem is_int_zero_sound {nv : Nval} (h : isIntZero nv = true) : nv = .I Integers.Int.zero := by
  cases nv with
  | I m =>
    simp only [isIntZero] at h
    rw [Integers.Int.same_if_eq h]
  | _ => cases h

/-! ## Builtin arguments and results -/

/-- `Deadcodeproof.eagree_set_res` -/
theorem eagree_set_res {e1 e2 : RTL.Regset} {v1 v2 : Val} {res : BuiltinRes Reg} {ne : Nenv}
    (hv : Val.Lessdef v1 v2) (h : eagree e1 e2 (killBuiltinRes res ne)) :
    eagree (regmapSetres res v1 e1) (regmapSetres res v2 e2) ne := by
  cases res with
  | BR r => exact eagree_update r (vagree_lessdef _ hv) h
  | _ => exact h

section BUILTINS
variable {F V : Type} (ge : Genv F V)

/-- `Deadcodeproof.transfer_builtin_arg_sound` -/
theorem transfer_builtin_arg_sound {bc : BlockClassification} {e e' : RTL.Regset} {sp : Block}
    {m m' : Mem} {a : BuiltinArg Reg} {v : Val}
    (hev : EvalBuiltinArg ge.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m a v)
    (GM : GenvMatch bc ge) (SPM : bc sp = .BCstack) :
    ∀ {nv : Nval} {ne1 : Nenv} {nm1 : Nmem} {ne2 : Nenv} {nm2 : Nmem},
    transferBuiltinArg nv (ne1, nm1) a = (ne2, nm2) →
    eagree e e' ne2 → Magree m m' (nlive ge sp nm2) →
    ∃ v', EvalBuiltinArg ge.toSenv (fun r => e'.get r) (.Vptr sp Ptrofs.zero) m' a v' ∧
      vagree v v' nv ∧ eagree e e' ne1 ∧ Magree m m' (nlive ge sp nm1) := by
  induction hev with
  | BA x =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨_, .BA x, add_need_vagree EA, add_need_eagree EA, MA⟩
  | BA_int n =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨_, .BA_int n, vagree_same _ _, EA, MA⟩
  | BA_long n =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨_, .BA_long n, vagree_same _ _, EA, MA⟩
  | BA_float n =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨_, .BA_float n, vagree_same _ _, EA, MA⟩
  | BA_single n =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨_, .BA_single n, vagree_same _ _, EA, MA⟩
  | BA_loadstack chunk ofs v hl =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    have E : Val.offsetPtr (.Vptr sp Ptrofs.zero) ofs = .Vptr sp ofs := by
      simp only [Val.offsetPtr, Ptrofs.add_zero_l]
    rw [E] at hl
    obtain ⟨v', A, B⟩ := magree_loadv MA hl (fun i h1 h2 =>
      nlive_add ge sp nm1 GM SPM (.stk SPM) ⟨h1, h2⟩)
    exact ⟨v', .BA_loadstack _ _ _ (by rw [E]; exact A), vagree_lessdef _ B, EA,
      magree_monotone MA fun _ _ h => incl_nmem_add ge sp _ _ h⟩
  | BA_addrstack ofs =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨_, .BA_addrstack ofs, vagree_same _ _, EA, MA⟩
  | BA_loadglobal chunk id ofs v hl =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    simp only [Senv.symbolAddress, Genv.toSenv] at hl
    cases FS : Genv.findSymbol ge id with
    | none => rw [FS] at hl; simp [Mem.loadv] at hl
    | some b =>
      rw [FS] at hl
      obtain ⟨v', A, B⟩ := magree_loadv MA hl (fun i h1 h2 =>
        nlive_add ge sp nm1 GM SPM (.gl id ((GM.1 id b).1 FS)) ⟨h1, h2⟩)
      refine ⟨v', .BA_loadglobal _ _ _ _ ?_, vagree_lessdef _ B, EA,
        magree_monotone MA fun _ _ h => incl_nmem_add ge sp _ _ h⟩
      simp only [Senv.symbolAddress, Genv.toSenv]; rw [FS]; exact A
  | BA_addrglobal id ofs =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨_, .BA_addrglobal id ofs, vagree_same _ _, EA, MA⟩
  | BA_splitlong hi lo vhi vlo _ _ IH1 IH2 =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg] at TR
    rcases TR1 : transferBuiltinArg .All (ne1, nm1) hi with ⟨ne', nm'⟩
    rw [TR1] at TR
    obtain ⟨vlo', A, B, C, D⟩ := IH2 TR EA MA
    obtain ⟨vhi', P, Q, R, S⟩ := IH1 TR1 C D
    exact ⟨_, .BA_splitlong _ _ _ _ P A,
      vagree_lessdef _ (Val.longofwords_lessdef (lessdef_vagree Q) (lessdef_vagree B)), R, S⟩
  | BA_addptr a1 a2 v1 v2 _ _ IH1 IH2 =>
    intro nv ne1 nm1 ne2 nm2 TR EA MA
    simp only [transferBuiltinArg] at TR
    rcases TR1 : transferBuiltinArg .All (ne1, nm1) a1 with ⟨ne', nm'⟩
    rw [TR1] at TR
    obtain ⟨v2', A, B, C, D⟩ := IH2 TR EA MA
    obtain ⟨v1', P, Q, R, S⟩ := IH1 TR1 C D
    refine ⟨_, .BA_addptr _ _ _ _ P A, ?_, R, S⟩
    simp only [Archi.ptr64, if_true]
    exact vagree_lessdef _ (Val.addl_lessdef (lessdef_vagree Q) (lessdef_vagree B))

/-- `Deadcodeproof.transfer_builtin_args_sound` -/
theorem transfer_builtin_args_sound {bc : BlockClassification} {e e' : RTL.Regset} {sp : Block}
    {m m' : Mem} (GM : GenvMatch bc ge) (SPM : bc sp = .BCstack) :
    ∀ {al : List (BuiltinArg Reg)} {vl : List Val},
    EvalBuiltinArgs ge.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m al vl →
    ∀ {ne1 : Nenv} {nm1 : Nmem} {ne2 : Nenv} {nm2 : Nmem},
    transferBuiltinArgs (ne1, nm1) al = (ne2, nm2) →
    eagree e e' ne2 → Magree m m' (nlive ge sp nm2) →
    ∃ vl', EvalBuiltinArgs ge.toSenv (fun r => e'.get r) (.Vptr sp Ptrofs.zero) m' al vl' ∧
      Val.LessdefList vl vl' ∧ eagree e e' ne1 ∧ Magree m m' (nlive ge sp nm1)
  | [], [], .nil, ne1, nm1, ne2, nm2, TR, EA, MA => by
    simp only [transferBuiltinArgs, List.foldl, Prod.mk.injEq] at TR
    obtain ⟨rfl, rfl⟩ := TR
    exact ⟨[], .nil, .nil, EA, MA⟩
  | a1 :: al, v1 :: vl, .cons h1 hl, ne1, nm1, ne2, nm2, TR, EA, MA => by
    simp only [transferBuiltinArgs, List.foldl] at TR
    rcases TR1 : transferBuiltinArg .All (ne1, nm1) a1 with ⟨ne', nm'⟩
    rw [TR1] at TR
    obtain ⟨vs', A1, B1, C1, D1⟩ :=
      transfer_builtin_args_sound GM SPM hl (ne1 := ne') (nm1 := nm') TR EA MA
    obtain ⟨v1', A2, B2, C2, D2⟩ := transfer_builtin_arg_sound ge h1 GM SPM TR1 C1 D1
    exact ⟨v1' :: vs', .cons A2 A1, .cons (lessdef_vagree B2) B1, C2, D2⟩

/-- `Deadcodeproof.can_eval_builtin_arg` -/
theorem can_eval_builtin_arg {gs gs' : Senv} {sp : Val} {e e' : RTL.Regset} {m m' : Mem} {P : Locset}
    (hsym : ∀ id, gs'.find_symbol id = gs.find_symbol id) (MA : Magree m m' P)
    {a : BuiltinArg Reg} {v : Val}
    (h : EvalBuiltinArg gs (fun r => e.get r) sp m a v) :
    ∃ v', EvalBuiltinArg gs' (fun r => e'.get r) sp m' a v' := by
  have LD : ∀ chunk addr v, Mem.loadv chunk m addr = some v →
      ∃ v', Mem.loadv chunk m' addr = some v' := by
    intro chunk addr v hl
    cases addr with
    | Vptr b ofs =>
      simp only [Mem.loadv] at hl ⊢
      split at hl
      · rw [if_pos ‹_›]
        exact Mem.valid_access_load (magree_valid_access MA (Mem.load_valid_access hl))
      · cases hl
    | _ => simp [Mem.loadv] at hl
  have hsa : ∀ id ofs, gs'.symbolAddress id ofs = gs.symbolAddress id ofs := by
    intro id ofs; simp only [Senv.symbolAddress, hsym]
  induction h with
  | BA x => exact ⟨_, .BA x⟩
  | BA_int n => exact ⟨_, .BA_int n⟩
  | BA_long n => exact ⟨_, .BA_long n⟩
  | BA_float n => exact ⟨_, .BA_float n⟩
  | BA_single n => exact ⟨_, .BA_single n⟩
  | BA_loadstack chunk ofs v hl =>
    obtain ⟨v', A⟩ := LD _ _ _ hl
    exact ⟨v', .BA_loadstack _ _ _ A⟩
  | BA_addrstack ofs => exact ⟨_, .BA_addrstack ofs⟩
  | BA_loadglobal chunk id ofs v hl =>
    obtain ⟨v', A⟩ := LD _ _ _ hl
    exact ⟨v', .BA_loadglobal _ _ _ _ (by rw [hsa]; exact A)⟩
  | BA_addrglobal id ofs => exact ⟨_, .BA_addrglobal id ofs⟩
  | BA_splitlong hi lo vhi vlo _ _ IH1 IH2 =>
    obtain ⟨v1', A1⟩ := IH1
    obtain ⟨v2', A2⟩ := IH2
    exact ⟨_, .BA_splitlong _ _ _ _ A1 A2⟩
  | BA_addptr a1 a2 v1 v2 _ _ IH1 IH2 =>
    obtain ⟨v1', A1⟩ := IH1
    obtain ⟨v2', A2⟩ := IH2
    exact ⟨_, .BA_addptr _ _ _ _ A1 A2⟩

/-- `Deadcodeproof.can_eval_builtin_args` -/
theorem can_eval_builtin_args {gs gs' : Senv} {sp : Val} {e e' : RTL.Regset} {m m' : Mem}
    {P : Locset} (hsym : ∀ id, gs'.find_symbol id = gs.find_symbol id) (MA : Magree m m' P) :
    ∀ {al : List (BuiltinArg Reg)} {vl : List Val},
    EvalBuiltinArgs gs (fun r => e.get r) sp m al vl →
    ∃ vl', EvalBuiltinArgs gs' (fun r => e'.get r) sp m' al vl'
  | [], [], .nil => ⟨[], .nil⟩
  | _ :: _, _ :: _, .cons h1 hl => by
    obtain ⟨v', A⟩ := can_eval_builtin_arg (e' := e') hsym MA h1
    obtain ⟨vl', B⟩ := can_eval_builtin_args (e' := e') hsym MA hl
    exact ⟨v' :: vl', .cons A B⟩

/-! ## Properties of volatile memory accesses -/

/-- `Deadcodeproof.transf_volatile_store` -/
theorem transf_volatile_store {v1 v2 v1' v2' : Val} {m tm : Mem} {chunk : Chunk} {sp : Block}
    {nm : Nmem} {t : Trace} {v : Val} {m' : Mem}
    (hs : VolatileStoreSem chunk ge.toSenv [v1, v2] m t v m')
    (h1 : Val.Lessdef v1 v1') (h2 : vagree v2 v2' (storeArgument chunk))
    (MA : Magree m tm (nlive ge sp nm)) :
    v = .Vundef ∧ ∃ tm', VolatileStoreSem chunk ge.toSenv [v1', v2'] tm t .Vundef tm' ∧
      Magree m' tm' (nlive ge sp nm) := by
  cases hs with
  | intro _ b ofs _ _ _ _ hvs =>
    refine ⟨rfl, ?_⟩
    cases h1
    cases hvs with
    | vol id ev _ hv hf hm =>
      exact ⟨tm, .intro _ _ _ _ _ _ _ (.vol _ _ _ _ id ev _ hv hf
        (EventsExtends.eventValMatch_lessdef hm (store_argument_load_result chunk h2))), MA⟩
    | nonvol _ _ hv hst =>
      obtain ⟨tm', A, B⟩ := magree_store_parallel MA hst h2 (fun _ _ h _ => h)
      exact ⟨tm', .intro _ _ _ _ _ _ _ (.nonvol _ _ _ _ _ _ hv A), B⟩

/-! ## Preservation of external calls -/

/-- `Deadcodeproof.transf_external_call` -/
theorem transf_external_call {bc : BlockClassification} {e te : RTL.Regset} {sp : Block}
    {m tm : Mem} {args : List (BuiltinArg Reg)} {vargs : List Val} {ef : ExtFun} {t : Trace}
    {vres : Val} {m' : Mem} {res : BuiltinRes Reg} {ne2 : Nenv} {nm2 : Nmem} {ne1 : Nenv}
    {nm1 : Nmem}
    (hec : ExtcallMemExtends (externalCall ef) ge.toSenv)
    (hargs : EvalBuiltinArgs ge.toSenv (fun r => e.get r) (.Vptr sp Ptrofs.zero) m args vargs)
    (hcall : externalCall ef ge.toSenv vargs m t vres m')
    (TR : transferBuiltinArgs (killBuiltinRes res ne2, nmemAll) args = (ne1, nm1))
    (EA : eagree e te ne1) (MA : Magree m tm (nlive ge sp nm1))
    (GM : GenvMatch bc ge) (SPM : bc sp = .BCstack) :
    ∃ tvargs tvres tm',
      EvalBuiltinArgs ge.toSenv (fun r => te.get r) (.Vptr sp Ptrofs.zero) tm args tvargs ∧
      externalCall ef ge.toSenv tvargs tm t tvres tm' ∧
      eagree (regmapSetres res vres e) (regmapSetres res tvres te) ne2 ∧
      Magree m' tm' (nlive ge sp nm2) := by
  obtain ⟨tvargs, A, B, C, D⟩ := transfer_builtin_args_sound ge GM SPM hargs TR EA MA
  obtain ⟨vres', tm', P, Q, R, _⟩ :=
    hec _ _ _ _ _ _ _ hcall (magree_extends (nlive_all ge sp) D) B
  exact ⟨tvargs, vres', tm', A, P, eagree_set_res Q C, mextends_agree R _⟩

end BUILTINS

/-- `Deadcodeproof.eagree_set_undef` -/
theorem eagree_set_undef {e1 e2 : RTL.Regset} {ne : Nenv} (r : Reg) (h : eagree e1 e2 ne) :
    eagree (e1.set r .Vundef) e2 ne := by
  intro r0
  rw [PMap.gsspec]
  split
  · exact vagree_lessdef _ (.undef _)
  · exact h r0

end Deadcodeproof
end RiscV
end CC
