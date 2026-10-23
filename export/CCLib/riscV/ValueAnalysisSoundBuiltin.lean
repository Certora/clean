/-
  [RISC-V instance of `CCLib/backend/ValueAnalysisSoundBuiltin.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Soundness of the value analysis, part 6 — the builtin case of
  `sound_step_base` (`backend/ValueAnalysis.v`) and the theorem
  `sound_step_base` itself.

  Differences from Rocq: the properties of external calls that CompCert
  takes as axioms for uninterpreted externals are hypotheses
  (`hinj`, `hprops`); `externalCall_memInject` and `externalCall_memProps`
  discharge them for every external call whose semantics is defined.
-/
import CCLib.riscV.ValueAnalysisSoundStep

namespace CC
namespace RiscV
namespace ValueAnalysis

open ValueDomain RTL
open Integers (Ptrofs)

section SOUNDNESS
variable {o : ValueAOp.Options} {rm : Romem} {ge : RTL.CGenv}

theorem listForall2_in_left {A B : Type} {P : A → B → Prop} :
    ∀ {l1 : List A} {l2 : List B}, ListForall2 P l1 l2 → ∀ {x}, x ∈ l1 → ∃ y, y ∈ l2 ∧ P x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hp hl, _, h => by
    cases h with
    | head => exact ⟨_, List.mem_cons_self .., hp⟩
    | tail _ h =>
      obtain ⟨y, hy, hxy⟩ := listForall2_in_left hl h
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

/-- `sound_step_base`, case `Ibuiltin`, when the transfer function treats the
    builtin as an arbitrary external call (`transfer_builtin_default`). -/
theorem sound_step_builtin_default {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block}
    {pc : Node} {rs : RTL.Regset} {m : Mem} {ae : Aenv} {am : Amem} {bc : BlockClassification}
    {ef : ExtFun} {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {pc' : Node}
    {vargs : List Val} {t : Trace} {vres : Val} {m' : Mem}
    (hinj : ExtcallMemInject (externalCall ef))
    (hprops : ExtcallMemProps (externalCall ef) (Genv.toSenv ge))
    (hcode : f.fn_code.get pc = some (.Ibuiltin ef args res pc'))
    (hargs : EvalBuiltinArgs ge.toSenv (fun r => rs.get r) (.Vptr sp Ptrofs.zero) m args vargs)
    (hec : externalCall ef ge.toSenv vargs m t vres m')
    (STK : SoundStack o  rm ge bc s m sp) (AN : (analyze o  rm f).get pc = .State ae am)
    (EM : Ematch bc rs ae) (RO : Romatch bc m rm) (MM : Mmatch bc m am) (GE : GenvMatch bc ge)
    (SP : bc sp = .BCstack)
    (TR : transfer o f rm pc ae am = transferBuiltinDefault o ae am rm args res) :
    SoundStateBase o  rm ge (.State s f (.Vptr sp Ptrofs.zero) pc' (regmapSetres res vres rs) m') := by
  have SPVALID : sp < m.nextblock := MM.mmatch_below sp (by rw [SP]; simp)
  have hs : pc' ∈ successorsInstr (.Ibuiltin ef args res pc') := by simp [successorsInstr]
  have ARGS := abuiltin_args_sound o EM RO MM GE SP hargs
  have NB : m.nextblock ≤ m'.nextblock :=
    nextblock_le_of_validBlock fun b hb => hprops.validBlock _ _ _ _ _ _ hec hb
  simp only [transferBuiltinDefault, analyzeCall] at TR
  split at TR
  · -- private builtin call
    rename_i NOLEAK
    simp only [Bool.and_eq_true, List.all_eq_true] at NOLEAK
    obtain ⟨N1, N2⟩ := NOLEAK
    obtain ⟨bc1, A, B, C, D, E, F, G⟩ := hide_stack GE RO MM SP (pincl_ge N1)
    obtain ⟨bc2, J, K, L, M, N, O, P, Q⟩ := external_call_match ef ge hinj hprops hec E
      (fun v hv => by
        obtain ⟨av, U, V⟩ := listForall2_in_left ARGS hv
        exact D _ _ (vpincl_ge (N2 av U)) V) F G A
    obtain ⟨bc3, U, V, W, X, Y, Z, AA⟩ := return_from_private_call (caller := bc) (callee := bc2)
      (bound := m.nextblock) MM.mmatch_below (by rw [K sp SPVALID]; exact B) SP
      (fun b hb hne => by rw [K b hb, C b hne]) EM
      (bmatch_inv (MM.mmatch_stack sp SP) fun ofs n _ =>
        Q sp ofs n ((Mem.validBlock_iff m sp).2 SPVALID) B)
      NB L N O M P
    refine sound_succ_state AN hcode hs TR (set_builtin_res_sound res V U) X W Y Z ?_
    refine sound_stack_exten (sound_stack_inv STK fun b ofs n hb hi _ => ?_) AA
    have hne : b ≠ sp := fun e => by subst e; exact Nat.lt_irrefl _ hb
    exact Q b ofs n ((Mem.validBlock_iff m b).2 (Nat.lt_trans hb SPVALID)) (by rw [C b hne]; exact hi)
  · -- public builtin call
    obtain ⟨bc1, A, B, C, D, E, F, G⟩ := anonymize_stack GE RO MM SP
    obtain ⟨bc2, J, K, L, M, N, O, P, Q⟩ := external_call_match ef ge hinj hprops hec E
      (fun v hv => by
        obtain ⟨av, U, V⟩ := listForall2_in_left ARGS hv
        exact D _ _ V) F G A
    obtain ⟨bc3, U, V, W, X, Y, Z, AA⟩ := return_from_public_call (caller := bc) (callee := bc2)
      (bound := m.nextblock) MM.mmatch_below (by rw [K sp SPVALID]; exact B) SP
      (fun b hb hne => by rw [K b hb, C b hne]) GE EM L N O M P
    refine sound_succ_state AN hcode hs TR (set_builtin_res_sound res V U) X W Y Z ?_
    refine sound_stack_exten (sound_stack_inv STK fun b ofs n hb hi _ => ?_) AA
    have hne : b ≠ sp := fun e => by subst e; exact Nat.lt_irrefl _ hb
    exact Q b ofs n ((Mem.validBlock_iff m b).2 (Nat.lt_trans hb SPVALID)) (by rw [C b hne]; exact hi)

/-- Stores through a pointer that matches an abstract value preserve the stack invariant. -/
theorem sound_stack_store {chunk : Chunk} {m : Mem} {b : Block} {ofs : Ptrofs} {v : Val}
    {m' : Mem} {bc : BlockClassification} {aaddr : Aval} {stk : List RTL.Stackframe}
    {bound : Block} (hs : Mem.store chunk m b (Ptrofs.unsigned ofs) v = some m')
    (ha : Vmatch bc (.Vptr b ofs) aaddr)
    (h : SoundStack o  rm ge bc stk m bound) : SoundStack o  rm ge bc stk m' bound := by
  have A : Pmatch bc b ofs .Ptop := vmatch_ptr_top ha
  cases A with
  | top hb =>
    refine sound_stack_inv h fun b' ofs' n _ hi _ => ?_
    exact Mem.loadbytes_store_other hs b' ofs' n (.inl fun e => by subst e; exact hb hi)

/-- Values received from the outside world point only to globals. -/
theorem eventval_match_glob {bc : BlockClassification} {ev : EventVal} {ty : ATyp} {v : Val}
    (GE : GenvMatch bc ge) (h : EventValMatch ge.toSenv ev ty v) : Vmatch bc v (.Ifptr .Glob) := by
  cases h with
  | ev_match_ptr id b ofs _ hf => exact .ifptr_p _ _ _ (.glob id ((GE.1 id b).1 hf))
  | _ => constructor

/-- `sound_step_base`, case `Ibuiltin`. -/
theorem sound_step_builtin {s : List RTL.Stackframe} {f : RTL.Function} {sp : Block}
    {pc : Node} {rs : RTL.Regset} {m : Mem} {ae : Aenv} {am : Amem} {bc : BlockClassification}
    {ef : ExtFun} {args : List (BuiltinArg Reg)} {res : BuiltinRes Reg} {pc' : Node}
    {vargs : List Val} {t : Trace} {vres : Val} {m' : Mem}
    (hinj : ExtcallMemInject (externalCall ef))
    (hprops : ExtcallMemProps (externalCall ef) (Genv.toSenv ge))
    (hcode : f.fn_code.get pc = some (.Ibuiltin ef args res pc'))
    (hargs : EvalBuiltinArgs ge.toSenv (fun r => rs.get r) (.Vptr sp Ptrofs.zero) m args vargs)
    (hec : externalCall ef ge.toSenv vargs m t vres m')
    (STK : SoundStack o  rm ge bc s m sp) (AN : (analyze o  rm f).get pc = .State ae am)
    (EM : Ematch bc rs ae) (RO : Romatch bc m rm) (MM : Mmatch bc m am) (GE : GenvMatch bc ge)
    (SP : bc sp = .BCstack) :
    SoundStateBase o  rm ge (.State s f (.Vptr sp Ptrofs.zero) pc' (regmapSetres res vres rs) m') := by
  have DEFAULT := sound_step_builtin_default hinj hprops hcode hargs hec STK AN EM RO MM GE SP
  have TR : transfer o f rm pc ae am = transferBuiltin o ae am rm ef args res := by
    unfold transfer; rw [hcode]
  have hs : pc' ∈ successorsInstr (.Ibuiltin ef args res pc') := by simp [successorsInstr]
  cases ef with
  | EF_vload chunk =>
    rcases args with _ | ⟨a, _ | ⟨a2, l⟩⟩
    · exact DEFAULT (TR.trans rfl)
    · change VolatileLoadSem chunk _ _ _ _ _ _ at hec
      cases hec with
      | intro _ b ofs _ _ _ hvl =>
      cases hargs with
      | cons ha _ =>
      have VM1 := abuiltin_arg_sound o EM RO MM GE SP ha
      refine sound_succ_state AN hcode hs TR (set_builtin_res_sound res EM ?_) MM RO GE SP STK
      cases hvl with
      | vol id ev v hvol hfind hev =>
        have V : Vmatch bc v (.Ifptr .Glob) := eventval_match_glob GE hev
        show Vmatch bc _ (if o.strict then _ else _)
        split
        · exact vmatch_lub_r _ _ (vnormalize_sound chunk V)
        · exact vnormalize_sound chunk (vmatch_ge (vge_top _) V)
      | nonvol v hvol hl =>
        have V := load_sound o.strict hl RO MM (match_aptr_of_aval o.strict VM1)
        show Vmatch bc _ (if o.strict then _ else _)
        split
        · exact vmatch_lub_l _ _ V
        · exact vnormalize_cast hl (vmatch_top V)
    · exact DEFAULT (TR.trans rfl)
  | EF_vstore chunk =>
    rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩
    · exact DEFAULT (TR.trans rfl)
    · exact DEFAULT (TR.trans rfl)
    · change VolatileStoreSem chunk _ _ _ _ _ _ at hec
      cases hec with
      | intro _ b ofs _ v _ _ hvs =>
      cases hargs with
      | cons ha1 hl =>
      cases hl with
      | cons ha2 _ =>
      have VM1 := abuiltin_arg_sound o EM RO MM GE SP ha1
      have VM2 := abuiltin_arg_sound o EM RO MM GE SP ha2
      cases hvs with
      | vol =>
        exact sound_succ_state AN hcode hs TR (set_builtin_res_sound res EM (.num_undef _))
          (mmatch_lub_l _ _ MM) RO GE SP STK
      | nonvol _ _ _ hst =>
        exact sound_succ_state AN hcode hs TR (set_builtin_res_sound res EM (.num_undef _))
          (mmatch_lub_r _ _ (store_sound hst MM (match_aptr_of_aval o.strict VM1) VM2))
          (romatch_store hst RO) GE SP (sound_stack_store hst VM1 STK)
    · exact DEFAULT (TR.trans rfl)
  | EF_memcpy sz al =>
    rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l⟩⟩⟩
    · exact DEFAULT (TR.trans rfl)
    · exact DEFAULT (TR.trans rfl)
    · change ExtcallMemcpySem sz al _ _ _ _ _ _ at hec
      cases hec with
      | intro _ bdst odst bsrc osrc _ bytes _ _ _ _ _ _ _ hlb hsb =>
      cases hargs with
      | cons ha1 hl =>
      cases hl with
      | cons ha2 _ =>
      have VM1 := abuiltin_arg_sound o EM RO MM GE SP ha1
      have VM2 := abuiltin_arg_sound o EM RO MM GE SP ha2
      exact sound_succ_state AN hcode hs TR (set_builtin_res_sound res EM (.num_undef _))
        (storebytes_sound hsb MM (match_aptr_of_aval o.strict VM1) (Mem.loadbytes_length hlb)
          (loadbytes_sound o.strict hlb RO MM (match_aptr_of_aval o.strict VM2)))
        (romatch_storebytes hsb RO) GE SP (sound_stack_storebytes hsb VM1 STK)
    · exact DEFAULT (TR.trans rfl)
  | EF_annot k txt targs =>
    change ExtcallAnnotSem txt targs _ _ _ _ _ _ at hec
    cases hec with
    | intro =>
    exact sound_succ_state AN hcode hs TR (set_builtin_res_sound res EM (.num_undef _)) MM RO GE
      SP STK
  | EF_annot_val k txt targ =>
    rcases args with _ | ⟨a, _ | ⟨a2, l⟩⟩
    · exact DEFAULT (TR.trans rfl)
    · change ExtcallAnnotValSem txt targ _ _ _ _ _ _ at hec
      cases hec with
      | intro =>
      cases hargs with
      | cons ha _ =>
      exact sound_succ_state AN hcode hs TR
        (set_builtin_res_sound res EM (abuiltin_arg_sound o EM RO MM GE SP ha)) MM RO GE SP STK
    · exact DEFAULT (TR.trans rfl)
  | EF_debug k txt targs =>
    change ExtcallDebugSem _ _ _ _ _ _ at hec
    cases hec with
    | intro =>
    exact sound_succ_state AN hcode hs TR (set_builtin_res_sound res EM (.num_undef _)) MM RO GE
      SP STK
  | EF_builtin name sg =>
    cases hlk : Builtins.lookupBuiltinFunction name sg with
    | none => exact DEFAULT (TR.trans (by simp only [transferBuiltin, hlk]))
    | some bf =>
      cases hes : evalStaticBuiltinFunction o ae am rm bf args with
      | none => exact DEFAULT (TR.trans (by simp only [transferBuiltin, hlk, hes]))
      | some av =>
        have TR' : transfer o f rm pc ae am = .State (setBuiltinRes res av ae) am :=
          TR.trans (by simp only [transferBuiltin, hlk, hes])
        change builtinOrExternalSem name sg _ _ _ _ _ _ at hec
        unfold builtinOrExternalSem at hec
        rw [hlk] at hec
        cases hec with
        | intro _ _ _ _ hb =>
        exact sound_succ_state AN hcode hs TR'
          (set_builtin_res_sound res EM (eval_static_builtin_function_sound o EM RO MM GE SP hargs hes hb))
          MM RO GE SP STK
  | EF_external => exact DEFAULT (TR.trans rfl)
  | EF_runtime => exact DEFAULT (TR.trans rfl)
  | EF_malloc => exact DEFAULT (TR.trans rfl)
  | EF_free => exact DEFAULT (TR.trans rfl)
  | EF_inline_asm => exact DEFAULT (TR.trans rfl)

end SOUNDNESS

/-! ## Preservation of the semantic invariant by one step of execution -/

section STEP
variable {o : ValueAOp.Options} {rm : Romem} {ge : RTL.CGenv}

private theorem listNthZ_mem' {A : Type} : ∀ {l : List A} {n : Z} {x : A},
    CminorSel.listNthZ l n = some x → x ∈ l
  | [], _, _, h => by simp [CminorSel.listNthZ] at h
  | _ :: _, _, _, h => by
      simp only [CminorSel.listNthZ] at h
      split at h
      · cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (listNthZ_mem' h)

theorem romatch_storev {bc : BlockClassification} {chunk : Chunk} {m : Mem} {addr v : Val}
    {m' : Mem} (hst : Mem.storev chunk m addr v = some m') (RO : Romatch bc m rm) :
    Romatch bc m' rm := by
  cases addr with
  | Vptr b ofs =>
    simp only [Mem.storev] at hst
    split at hst
    · exact romatch_store hst RO
    · cases hst
  | _ => cases hst

/-- `ValueAnalysis.sound_step_base`: every step of the RTL semantics preserves
    the semantic invariant `sound_state_base`.  `hinj` and `hprops` are the
    properties CompCert assumes (by axiom) of all external calls. -/
theorem sound_step_base
    (hinj : ∀ ef, ExtcallMemInject (externalCall ef))
    (hprops : ∀ ef, ExtcallMemProps (externalCall ef) (Genv.toSenv ge))
    {st : RTL.State} {t : Trace} {st' : RTL.State} (hstep : RTL.Step ge st t st')
    (hs : SoundStateBase o  rm ge st) : SoundStateBase o  rm ge st' := by
  cases hstep with
  | Inop s f sp pc rs m pc' hcode =>
    cases hs with
    | regular STK AN EM RO MM GE SP =>
      exact sound_succ_state AN hcode (by simp [successorsInstr])
        (by unfold transfer; rw [hcode]) EM MM RO GE SP STK
  | Iop s f sp pc rs m op args res pc' v hcode hev =>
    cases hs with
    | regular STK AN EM RO MM GE SP =>
      exact sound_succ_state AN hcode (by simp [successorsInstr])
        (by unfold transfer; rw [hcode])
        (ematch_update res EM (ValueAOp.eval_static_operation_sound o GE SP op hev
          (aregs_sound EM args))) MM RO GE SP STK
  | Iload s f sp pc rs m chunk addr args dst pc' a v hcode hea hl =>
    cases hs with
    | regular STK AN EM RO MM GE SP =>
      exact sound_succ_state AN hcode (by simp [successorsInstr])
        (by unfold transfer; rw [hcode])
        (ematch_update dst EM (loadv_sound o.strict hl RO MM
          (ValueAOp.eval_static_addressing_sound GE SP addr hea (aregs_sound EM args))))
        MM RO GE SP STK
  | Istore s f sp pc rs m chunk addr args src pc' a m' hcode hea hst =>
    cases hs with
    | regular STK AN EM RO MM GE SP =>
      have VMADDR := ValueAOp.eval_static_addressing_sound GE SP addr hea (aregs_sound EM args)
      exact sound_succ_state AN hcode (by simp [successorsInstr])
        (by unfold transfer; rw [hcode]; rfl) EM (storev_sound o.strict hst MM VMADDR (EM src))
        (romatch_storev hst RO) GE SP (sound_stack_storev hst VMADDR STK)
  | Icall s f sp pc rs m sig ros args res pc' fd hcode =>
    cases hs with
    | regular STK AN EM RO MM GE SP => exact sound_step_call hcode STK AN EM RO MM GE SP
  | Itailcall s f stk pc rs m sig ros args fd m' hcode _ _ hfree =>
    cases hs with
    | regular STK AN EM RO MM GE SP => exact sound_step_tailcall hfree STK EM RO MM GE SP
  | Ibuiltin s f sp pc rs m ef args res pc' vargs t vres m' hcode hargs hec =>
    cases hs with
    | regular STK AN EM RO MM GE SP =>
      exact sound_step_builtin (hinj ef) (hprops ef) hcode hargs hec STK AN EM RO MM GE SP
  | Icond s f sp pc rs m cond args ifso ifnot b pc' hcode _ hpc =>
    cases hs with
    | regular STK AN EM RO MM GE SP =>
      exact sound_succ_state AN hcode (by subst hpc; cases b <;> simp [successorsInstr])
        (by unfold transfer; rw [hcode]) EM MM RO GE SP STK
  | Ijumptable s f sp pc rs m arg tbl n pc' hcode _ hnth =>
    cases hs with
    | regular STK AN EM RO MM GE SP =>
      exact sound_succ_state AN hcode (listNthZ_mem' hnth)
        (by unfold transfer; rw [hcode]) EM MM RO GE SP STK
  | Ireturn s f stk pc rs m or m' hcode hfree =>
    cases hs with
    | regular STK AN EM RO MM GE SP => exact sound_step_return hfree STK EM RO MM GE SP
  | function_internal s f args m m' stk hty halloc =>
    cases hs with
    | call STK ARGS RO MM GE NOSTK => exact sound_step_internal hty halloc STK ARGS RO MM GE NOSTK
  | function_external s ef args res t m m' hec =>
    cases hs with
    | call STK ARGS RO MM GE NOSTK =>
      exact sound_step_external (hinj ef) (hprops ef) hec STK ARGS RO MM GE NOSTK
  | «return» res f sp pc rs s vres m =>
    cases hs with
    | ret STK RES RO MM GE NOSTK => exact sound_step_return_state STK RES RO MM GE NOSTK

end STEP

end ValueAnalysis
end RiscV
end CC
