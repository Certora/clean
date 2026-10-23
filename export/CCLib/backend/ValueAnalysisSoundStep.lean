/-
  Soundness of the value analysis, part 5 — the cases of `sound_step_base`
  (`backend/ValueAnalysis.v`) for calls, tail calls, returns and function
  entry/exit.  The builtin case and the theorem itself are in
  `ValueAnalysisSoundBuiltin.lean`.

  Each lemma is one bullet of Rocq's proof of `sound_step_base`, with the
  inverted `RTL.step` and `sound_state_base` hypotheses passed explicitly.
-/
import CCLib.backend.ValueAnalysisSoundStack

namespace CC
namespace ValueAnalysis

open ValueDomain RTL
open Integers (Ptrofs)

section SOUNDNESS
variable {o : ValueAOp.Options} {abi : Conventions1.AbiKind} {rm : Romem} {ge : RTL.CGenv}

/-- Arguments of a call are register values. -/
theorem mem_getList {rs : RTL.Regset} {args : List Reg} {v : Val} (h : v ∈ rs.getList args) :
    ∃ r, r ∈ args ∧ v = rs.get r := by
  simp only [Regmap.getList, List.mem_map] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r, hr, rfl⟩

/-- An external call only grows the set of valid blocks. -/
theorem nextblock_le_of_validBlock {m m' : Mem}
    (H : ∀ b, Mem.validBlock m b = true → Mem.validBlock m' b = true) :
    m.nextblock ≤ m'.nextblock := by
  apply Nat.le_of_not_lt; intro hlt
  have := H m'.nextblock ((Mem.validBlock_iff m _).2 hlt)
  rw [Mem.validBlock_iff] at this
  exact Nat.lt_irrefl _ this

/-- `sound_step_base`, case `Icall`. -/
theorem sound_step_call {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block} {pc : Node}
    {rs : RTL.Regset} {m : Mem} {ae : Aenv} {am : Amem} {bc : BlockClassification}
    {sig : Signature} {ros : Sum Reg Ident} {args : List Reg} {res : Reg} {pc' : Node}
    {fd : RTL.Fundef}
    (hcode : f.fn_code.get pc = some (.Icall sig ros args res pc'))
    (STK : SoundStack o abi rm ge bc s m sp) (AN : (analyze o abi rm f).get pc = .State ae am)
    (EM : Ematch bc rs ae) (RO : Romatch bc m rm) (MM : Mmatch bc m am) (GE : GenvMatch bc ge)
    (SP : bc sp = .BCstack) :
    SoundStateBase o abi rm ge
      (.Callstate (.Stackframe res f (.Vptr sp Ptrofs.zero) pc' rs :: s) fd (rs.getList args) m) := by
  have TR : transfer o f rm pc ae am = transferCall ae am args res := by
    unfold transfer; rw [hcode]
  have hs : pc' ∈ successorsInstr (.Icall sig ros args res pc') := by simp [successorsInstr]
  simp only [transferCall, analyzeCall] at TR
  split at TR
  · -- private call
    rename_i NOLEAK
    simp only [Bool.and_eq_true, List.all_eq_true] at NOLEAK
    obtain ⟨N1, N2⟩ := NOLEAK
    have SUCC := analyze_successor o abi AN hcode hs TR
    rw [TR] at SUCC
    obtain ⟨bc', A, B, C, D, E, F, G⟩ := hide_stack GE RO MM SP (pincl_ge N1)
    refine .call ?_ (fun v hv => ?_) F G E A
    · exact .private_call (bc' := bc) (bound' := m.nextblock) STK (Nat.le_refl _) MM.mmatch_below
        B SP (fun b _ hne => C b hne) GE SUCC EM (MM.mmatch_stack sp SP)
    · obtain ⟨r, hr, rfl⟩ := mem_getList hv
      exact D _ (areg ae r) (vpincl_ge (N2 _ (List.mem_map_of_mem hr))) (EM r)
  · -- public call
    have SUCC := analyze_successor o abi AN hcode hs TR
    rw [TR] at SUCC
    obtain ⟨bc', A, B, C, D, E, F, G⟩ := anonymize_stack GE RO MM SP
    refine .call ?_ (fun v hv => ?_) F G E A
    · exact .public_call (bc' := bc) (bound' := m.nextblock) STK (Nat.le_refl _) MM.mmatch_below
        B SP (fun b _ hne => C b hne) GE SUCC EM
    · obtain ⟨r, hr, rfl⟩ := mem_getList hv
      exact D _ _ (EM r)

/-- `sound_step_base`, case `Itailcall`. -/
theorem sound_step_tailcall {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block}
    {rs : RTL.Regset} {m : Mem} {ae : Aenv} {am : Amem} {bc : BlockClassification}
    {args : List Reg} {fd : RTL.Fundef} {m' : Mem}
    (hfree : Mem.free m sp 0 f.fn_stacksize = some m')
    (STK : SoundStack o abi rm ge bc s m sp)
    (EM : Ematch bc rs ae) (RO : Romatch bc m rm) (MM : Mmatch bc m am) (GE : GenvMatch bc ge)
    (SP : bc sp = .BCstack) :
    SoundStateBase o abi rm ge (.Callstate s fd (rs.getList args) m') := by
  obtain ⟨bc', A, B, C, D, E, F, G⟩ := anonymize_stack GE RO MM SP
  refine .call ?_ (fun v hv => ?_) (romatch_free hfree F) (mmatch_free hfree G) E A
  · rw [Mem.nextblock_free hfree]
    refine sound_stack_new_bound (sound_stack_exten (sound_stack_free hfree STK)
      fun b hb => C b fun e => by subst e; exact Nat.lt_irrefl _ hb) ?_
    exact Nat.le_of_lt (MM.mmatch_below sp (by rw [SP]; simp))
  · obtain ⟨r, hr, rfl⟩ := mem_getList hv
    exact D _ _ (EM r)

/-- `sound_step_base`, case `Ireturn`. -/
theorem sound_step_return {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block}
    {rs : RTL.Regset} {m : Mem} {ae : Aenv} {am : Amem} {bc : BlockClassification}
    {or : Option Reg} {m' : Mem}
    (hfree : Mem.free m sp 0 f.fn_stacksize = some m')
    (STK : SoundStack o abi rm ge bc s m sp)
    (EM : Ematch bc rs ae) (RO : Romatch bc m rm) (MM : Mmatch bc m am) (GE : GenvMatch bc ge)
    (SP : bc sp = .BCstack) :
    SoundStateBase o abi rm ge (.Returnstate s (regmapOptget or .Vundef rs) m') := by
  obtain ⟨bc', A, B, C, D, E, F, G⟩ := anonymize_stack GE RO MM SP
  refine .ret ?_ ?_ (romatch_free hfree F) (mmatch_free hfree G) E A
  · rw [Mem.nextblock_free hfree]
    refine sound_stack_new_bound (sound_stack_exten (sound_stack_free hfree STK)
      fun b hb => C b fun e => by subst e; exact Nat.lt_irrefl _ hb) ?_
    exact Nat.le_of_lt (MM.mmatch_below sp (by rw [SP]; simp))
  · cases or with
    | none => exact .ifptr_undef _
    | some r => exact D _ _ (EM r)

/-- `sound_step_base`, case `exec_function_internal`. -/
theorem sound_step_internal {s : List RTL.Stackframe} {f : RTL.Function} {args : List Val}
    {m m' : Mem} {stk : Block} {bc : BlockClassification}
    (hty : Val.HasArgtypeList args f.fn_sig.sig_args) (halloc : Mem.alloc m 0 f.fn_stacksize = (m', stk))
    (STK : SoundStack o abi rm ge bc s m m.nextblock)
    (ARGS : ∀ v, v ∈ args → Vmatch bc v Vtop) (RO : Romatch bc m rm)
    (MM : Mmatch bc m mtop) (GE : GenvMatch bc ge) (NOSTK : BcNostack bc) :
    SoundStateBase o abi rm ge
      (.State s f (.Vptr stk Ptrofs.zero) f.fn_entrypoint (initRegs args f.fn_params) m') := by
  obtain ⟨bc', A, B, C, D, E, F, G⟩ := allocate_stack halloc GE RO MM NOSTK
  obtain ⟨ae, am, AN, EM, MM'⟩ :=
    analyze_entrypoint o abi rm f (fun v hv => G v _ (ARGS v hv)) hty E
  have hstk : stk = m.nextblock := by
    have : (Mem.alloc m 0 f.fn_stacksize).2 = stk := by rw [halloc]
    rw [← this]; rfl
  refine .regular ?_ AN EM D MM' C B
  rw [hstk]
  refine sound_stack_exten (sound_stack_inv STK fun b ofs n hb _ _ => ?_) (fun b hb => F b (hstk ▸ hb))
  exact Mem.loadbytes_alloc_unchanged halloc ((Mem.validBlock_iff m b).2 hb) ofs n

/-- `sound_step_base`, case `exec_function_external`. -/
theorem sound_step_external {s : List RTL.Stackframe} {ef : ExtFun} {args : List Val} {res : Val}
    {t : Trace} {m m' : Mem} {bc : BlockClassification}
    (hinj : ExtcallMemInject (externalCall ef))
    (hprops : ExtcallMemProps (externalCall ef) (Genv.toSenv ge))
    (hec : externalCall ef ge.toSenv args m t res m')
    (STK : SoundStack o abi rm ge bc s m m.nextblock)
    (ARGS : ∀ v, v ∈ args → Vmatch bc v Vtop) (RO : Romatch bc m rm)
    (MM : Mmatch bc m mtop) (GE : GenvMatch bc ge) (NOSTK : BcNostack bc) :
    SoundStateBase o abi rm ge (.Returnstate s res m') := by
  obtain ⟨bc', A, B, C, D, E, F, G, K⟩ := external_call_match ef ge hinj hprops hec GE ARGS RO MM NOSTK
  refine .ret ?_ C E F D G
  refine sound_stack_new_bound (sound_stack_exten (sound_stack_inv STK fun b ofs n hb hi _ => ?_) B)
    (nextblock_le_of_validBlock fun b hb => hprops.validBlock _ _ _ _ _ _ hec hb)
  exact K b ofs n ((Mem.validBlock_iff m b).2 hb) hi

/-- `sound_step_base`, case `exec_return`. -/
theorem sound_step_return_state {res : Reg} {f : RTL.Function} {sp : Val} {pc : Node}
    {rs : RTL.Regset} {s : List RTL.Stackframe} {vres : Val} {m : Mem} {bc : BlockClassification}
    (STK : SoundStack o abi rm ge bc (.Stackframe res f sp pc rs :: s) m m.nextblock)
    (RES : Vmatch bc vres Vtop) (RO : Romatch bc m rm)
    (MM : Mmatch bc m mtop) (GE : GenvMatch bc ge) (NOSTK : BcNostack bc) :
    SoundStateBase o abi rm ge (.State s f sp pc (rs.set res vres) m) := by
  cases STK with
  | @public_call _ _ _ sp _ _ _ _ _ bc' bound' ae STK INCR BELOW SP SP' SAME GE' AN EM =>
    obtain ⟨bc1, A, B, C, D, E, F, G⟩ := return_from_public_call BELOW SP SP'
      (fun b hb hne => (SAME b hb hne).symm) GE' EM RES RO MM GE NOSTK
    cases hA : (analyze o abi rm f).get pc with
    | Bot => rw [hA] at AN; exact AN.elim
    | State ae' am' =>
      rw [hA] at AN
      exact .regular (sound_stack_exten STK G) hA
        (ematch_ge (ematch_update res B A) AN.1) C (AN.2 _ _ D) E F
  | @private_call _ _ _ sp _ _ _ _ _ bc' bound' ae am STK INCR BELOW SP SP' SAME GE' AN EM
      CONTENTS =>
    obtain ⟨bc1, A, B, C, D, E, F, G⟩ := return_from_private_call BELOW SP SP'
      (fun b hb hne => (SAME b hb hne).symm) EM CONTENTS
      (Nat.le_trans INCR (Nat.le_refl _)) RES RO MM GE NOSTK
    cases hA : (analyze o abi rm f).get pc with
    | Bot => rw [hA] at AN; exact AN.elim
    | State ae' am' =>
      rw [hA] at AN
      exact .regular (sound_stack_exten STK G) hA
        (ematch_ge (ematch_update res B A) AN.1) C (AN.2 _ _ D) E F

end SOUNDNESS

end ValueAnalysis
end CC
