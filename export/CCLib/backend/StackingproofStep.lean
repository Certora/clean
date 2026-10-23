/-
  Correctness proof for the layout of activation records, part 5 — port of
  the end of `backend/Stackingproof.v`: the simulation relation
  `match_states`, the simulation diagram `transf_step_correct`, initial and
  final states, and the main theorem `transf_program_correct`.

  Differences from Rocq: the return-address oracle `return_address_offset`
  and its property `return_address_offset_exists` (Rocq's section `Variable`
  and `Hypothesis`) are explicit parameters `rao` and `rao_exists`.  The
  properties of external functions and inline assembly that CompCert takes as
  axioms (`external_functions_properties`, `inline_assembly_properties`) are
  hypotheses here: well-typedness of results (used by the Linear type system)
  and compatibility with memory injections.
-/
import CCLib.backend.StackingproofMatch
import CCLib.backend.CleanupLabelsproof
import CCLib.aarch64.OpInject
import CCLib.common.LinkingFundef

namespace CC
namespace Stackingproof

open Linear Mach Conventions1 Conventions Stacklayout Stacking Bounds Separation
open Lineartyping Smallstep

/-! ## The simulation relation -/

/-- `Stackingproof.match_states` -/
inductive MatchStates (abi : AbiKind) (ge : Linear.CGenv) (tge : Mach.CGenv) :
    Linear.State → Mach.State → Prop where
  | intro (cs : List Linear.Stackframe) (f : Linear.Function) (sp : Block) (c : Linear.Code)
      (ls : LTL.Locset) (m : Mem) (cs' : List Mach.Stackframe) (fb : Block) (sp' : Block)
      (rs : Regset) (m' : Mem) (j : Val.Meminj) (tf : Mach.Function) :
      MatchStacks abi tge j cs cs' f.fn_sig →
      transfFunction abi f = .OK tf →
      Genv.findFunctPtr tge fb = some (.Internal tf) →
      AgreeRegs j ls rs →
      AgreeLocs abi f ls (Linear.parentLocset cs) →
      j sp = some (sp', (fenv abi f).fe_stack_data) →
      c <:+ f.fn_code →
      (m' ⊨ frameContents abi f j sp' ls (Linear.parentLocset cs) (Mach.parentSp cs')
          (Mach.parentRa cs') ** stackContents abi j cs cs' ** minjection j m **
          globalenvInject ge j) →
      MatchStates abi ge tge (.State cs f (.Vptr sp Integers.Ptrofs.zero) c ls m)
        (.State cs' fb (.Vptr sp' Integers.Ptrofs.zero) (translCode (fenv abi f) c) rs m')
  | call (cs : List Linear.Stackframe) (f : Linear.Fundef) (ls : LTL.Locset) (m : Mem)
      (cs' : List Mach.Stackframe) (fb : Block) (rs : Regset) (m' : Mem) (j : Val.Meminj)
      (tf : Mach.Fundef) :
      MatchStacks abi tge j cs cs' (Linear.funsig f) →
      Stacking.transfFundef abi f = .OK tf →
      Genv.findFunctPtr tge fb = some tf →
      AgreeRegs j ls rs →
      (m' ⊨ stackContents abi j cs cs' ** minjection j m ** globalenvInject ge j) →
      MatchStates abi ge tge (.Callstate cs f ls m) (.Callstate cs' fb rs m')
  | ret (cs : List Linear.Stackframe) (ls : LTL.Locset) (m : Mem) (cs' : List Mach.Stackframe)
      (rs : Regset) (m' : Mem) (j : Val.Meminj) (sg : Signature) :
      MatchStacks abi tge j cs cs' sg →
      AgreeRegs j ls rs →
      (m' ⊨ stackContents abi j cs cs' ** minjection j m ** globalenvInject ge j) →
      MatchStates abi ge tge (.Returnstate cs ls m) (.Returnstate cs' rs m')

/-! ## Semantic preservation -/

section PRESERVATION
variable (abi : AbiKind) (rao : Mach.Function → Mach.Code → Integers.Ptrofs → Prop)
  {prog : Linear.Program} {tprog : Mach.Program} (TRANSF : MatchProg abi prog tprog)
  (rao_exists : ∀ (f : Mach.Function) (sg : Signature) (ros : Sum Mreg Ident) (c : Mach.Code),
    (Mach.Instruction.Mcall sg ros :: c) <:+ f.fn_code → ∃ ofs, rao f c ofs)
  (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
  (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
  (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
  (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)

private theorem inject_stack_pointer {j : Val.Meminj} {sp sp' : Block} {d : Z}
    (h : j sp = some (sp', d)) :
    Val.Inject j (.Vptr sp Integers.Ptrofs.zero) (.Vptr sp' (Integers.Ptrofs.repr d)) :=
  .ptr d h (Integers.Ptrofs.add_zero_l _).symm

private theorem head_mem_of_suffix {α : Type} {a : α} {l l' : List α} (h : a :: l <:+ l') :
    a ∈ l' :=
  h.subset List.mem_cons_self

private theorem lessdef_inject {j : Val.Meminj} {v v' v'' : Val} (h1 : Val.Inject j v v')
    (h2 : Val.Lessdef v' v'') : Val.Inject j v v'' := by
  cases h2 with
  | refl => exact h1
  | undef => cases h1; exact .undef _

include TRANSF rao_exists hext hasm hextp hasmp in
set_option maxHeartbeats 2000000 in
/-- `Stackingproof.transf_step_correct` -/
theorem transf_step_correct {s1 t s2} (hst : Linear.Step abi prog.globalenv s1 t s2)
    (WTS : WtState abi s1) {s1'} (MS : MatchStates abi prog.globalenv tprog.globalenv s1 s1') :
    ∃ s2', Smallstep.Plus (Mach.Step abi rao tprog.globalenv) s1' t s2' ∧
      MatchStates abi prog.globalenv tprog.globalenv s2 s2' := by
  have hsym := symbols_preserved TRANSF
  have hsenv := senv_preserved TRANSF
  cases hst with
  | Lgetstack s f sp sl ofs ty dst b rs m rs' e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have BOUND := function_is_within_bounds abi f _ (head_mem_of_suffix TAIL)
      obtain ⟨B1, B2⟩ := BOUND
      have SV := wt_state_getstack WTS
      have TAIL' : b <:+ f.fn_code := (List.suffix_cons _ _).trans TAIL
      cases sl with
      | Local =>
        obtain ⟨v, A, B⟩ := frame_get_local SEP B1 SV
        exact ⟨_, plus_one (.Mgetstack _ _ _ _ _ _ _ _ _ _ A),
          .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND (agree_regs_set_reg dst AGREGS B)
            (agree_locs_set_reg _ AGLOCS B2) INJSP TAIL' (frame_set_reg dst _ SEP)⟩
      | Outgoing =>
        obtain ⟨v, A, B⟩ := frame_get_outgoing SEP B1 SV
        exact ⟨_, plus_one (.Mgetstack _ _ _ _ _ _ _ _ _ _ A),
          .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND (agree_regs_set_reg dst AGREGS B)
            (agree_locs_set_reg _ AGLOCS B2) INJSP TAIL' (frame_set_reg dst _ SEP)⟩
      | Incoming =>
        have SV' : Loc.S .Incoming ofs ty ∈ RPair.regsList (locParameters abi f.fn_sig) := by
          simp only [slotValid, Bool.and_eq_true, decide_eq_true_eq] at SV
          exact SV.1
        have IN_ARGS := incoming_slot_in_parameters abi ofs ty f.fn_sig SV'
        cases STACKS with
        | empty _ htp => exact absurd (htp _ IN_ARGS) id
        | cons f0 sp0 ls0 c0 cs0 fb0 sp0' ra c0' cs0' _ trf0 _ _ _ _ _ _ _ ARGS STK =>
          have SEP2 : m' ⊨ frameContents abi f0 j sp0' ls0 (Linear.parentLocset cs0)
              (Mach.parentSp cs0') (Mach.parentRa cs0') **
              (stackContents abi j cs0 cs0' ** minjection j m ** globalenvInject prog.globalenv j) :=
            (sep_assoc _ _ _).pred.1 (sep_proj2 SEP)
          obtain ⟨v, A, B⟩ := frame_get_outgoing SEP2 (ARGS _ _ IN_ARGS)
            (slot_outgoing_argument_valid abi f0 ofs ty _ IN_ARGS)
          refine ⟨_, plus_one (.Mgetparam _ _ _ _ _ _ _ _ _ _ _ _ FIND ?_ A rfl), ?_⟩
          · rw [unfold_transf_function TRANSL]; exact frame_get_parent SEP
          · refine .intro _ _ _ _ _ _ _ _ _ _ _ j tf (.cons f0 sp0 ls0 c0 cs0 fb0 sp0' ra c0' cs0'
              _ trf0 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ARGS STK) TRANSL FIND
              (agree_regs_set_reg dst (agree_regs_set_reg tempForParentFrame AGREGS (.undef _)) ?_)
              (agree_locs_set_reg _ (agree_locs_undef_locs _ AGLOCS rfl) B2) INJSP TAIL'
              (frame_set_reg dst _ (frame_undef_regs _ SEP))
            show Val.Inject j (rs (.S .Incoming ofs ty)) v
            rw [AGLOCS.agree_incoming ofs ty SV']
            exact B
  | Lsetstack s f sp src sl ofs ty b rs m rs' e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have BOUND := function_is_within_bounds abi f _ (head_mem_of_suffix TAIL)
      obtain ⟨SV, SW⟩ := wt_state_setstack WTS
      have TAIL' : b <:+ f.fn_code := (List.suffix_cons _ _).trans TAIL
      cases sl with
      | Local =>
        obtain ⟨m'', STORE, SEP'⟩ := frame_set_local SEP BOUND SV (AGREGS src)
        exact ⟨_, plus_one (.Msetstack _ _ _ _ _ _ _ _ _ _ _ STORE rfl),
          .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND
            (agree_regs_set_slot _ _ _ _ AGREGS) (agree_locs_set_slot _ _ _ AGLOCS rfl) INJSP TAIL'
            SEP'⟩
      | Outgoing =>
        obtain ⟨m'', STORE, SEP'⟩ := frame_set_outgoing SEP BOUND SV (AGREGS src)
        exact ⟨_, plus_one (.Msetstack _ _ _ _ _ _ _ _ _ _ _ STORE rfl),
          .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND
            (agree_regs_set_slot _ _ _ _ AGREGS) (agree_locs_set_slot _ _ _ AGLOCS rfl) INJSP TAIL'
            SEP'⟩
      | Incoming => simp [slotWritable] at SW
  | Lop s f sp op args res b rs m v rs' hev e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have BOUND := function_is_within_bounds abi f _ (head_mem_of_suffix TAIL)
      have TAIL' : b <:+ f.fn_code := (List.suffix_cons _ _).trans TAIL
      have GI := sep_proj2 (sep_proj2 (sep_proj2 SEP))
      have MINJ := sep_proj1 (sep_proj2 (sep_proj2 SEP))
      obtain ⟨v', A, B⟩ := Op.evalOperation_inject prog.globalenv
        (symbolAddress_inject_of_globalenvInject GI) (inject_stack_pointer INJSP)
        (agree_reglist args AGREGS) MINJ hev
      have A' : Op.evalOperation tprog.globalenv (.Vptr sp' Integers.Ptrofs.zero)
          (translOp (fenv abi f) op) (args.map rs0) m' = some v' := by
        rw [evalOperation_preserved prog.globalenv tprog.globalenv hsym]
        simp only [translOp]
        rw [Op.evalOperation_shiftStack]; exact A
      refine ⟨_, plus_one (.Mop _ _ _ _ _ _ _ _ _ _ _ A' rfl),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND ?_
          (agree_locs_set_reg _ (agree_locs_undef_locs _ AGLOCS (destroyed_by_op_caller_save op))
            BOUND) INJSP TAIL' (frame_set_reg res _ (frame_undef_regs _ SEP))⟩
      rw [transl_destroyed_by_op]
      exact agree_regs_set_reg res (agree_regs_undef_regs _ AGREGS) B
  | Lload s f sp chunk addr args dst b rs m a v rs' hea hl e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have BOUND := function_is_within_bounds abi f _ (head_mem_of_suffix TAIL)
      have TAIL' : b <:+ f.fn_code := (List.suffix_cons _ _).trans TAIL
      have GI := sep_proj2 (sep_proj2 (sep_proj2 SEP))
      have MINJ := sep_proj1 (sep_proj2 (sep_proj2 SEP))
      obtain ⟨a', A, B⟩ := Op.evalAddressing_inject prog.globalenv
        (symbolAddress_inject_of_globalenvInject GI) (inject_stack_pointer INJSP)
        (agree_reglist args AGREGS) hea
      have A' : Op.evalAddressing tprog.globalenv (.Vptr sp' Integers.Ptrofs.zero)
          (translAddr (fenv abi f) addr) (args.map rs0) = some a' := by
        rw [evalAddressing_preserved prog.globalenv tprog.globalenv hsym]
        simp only [translAddr]
        rw [Op.evalAddressing_shiftStack]; exact A
      obtain ⟨v', C, D⟩ := loadv_parallel_rule MINJ hl B
      obtain ⟨v'', E, F⟩ := simplify_load_correct chunk m' a' v' C
      exact ⟨_, plus_one (.Mload _ _ _ _ _ _ _ _ _ _ _ _ _ A' E rfl),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND
          (agree_regs_set_reg dst (agree_regs_undef_regs _ AGREGS) (lessdef_inject D F))
          (agree_locs_set_reg _ (agree_locs_undef_locs _ AGLOCS
            (destroyed_by_load_caller_save chunk addr)) BOUND) INJSP TAIL'
          (frame_set_reg dst _ (frame_undef_regs _ SEP))⟩
  | Lstore s f sp chunk addr args src b rs m m'' a rs' hea hs e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have TAIL' : b <:+ f.fn_code := (List.suffix_cons _ _).trans TAIL
      have GI := sep_proj2 (sep_proj2 (sep_proj2 SEP))
      obtain ⟨a', A, B⟩ := Op.evalAddressing_inject prog.globalenv
        (symbolAddress_inject_of_globalenvInject GI) (inject_stack_pointer INJSP)
        (agree_reglist args AGREGS) hea
      have A' : Op.evalAddressing tprog.globalenv (.Vptr sp' Integers.Ptrofs.zero)
          (translAddr (fenv abi f) addr) (args.map rs0) = some a' := by
        rw [evalAddressing_preserved prog.globalenv tprog.globalenv hsym]
        simp only [translAddr]
        rw [Op.evalAddressing_shiftStack]; exact A
      obtain ⟨m1', C, SEP1⟩ := storev_parallel_rule ((sep_swap3 _ _ _ _).pred.1 SEP) hs B
        (AGREGS src)
      have SEP2 := (sep_swap3 _ _ _ _).pred.1 SEP1
      exact ⟨_, plus_one (.Mstore _ _ _ _ _ _ _ _ _ _ _ _ _ A'
          (simplify_store_correct _ _ _ _ _ C) rfl),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND
          (agree_regs_undef_regs (destroyedByStore chunk addr) AGREGS)
          (agree_locs_undef_locs (destroyedByStore chunk addr) AGLOCS
            (destroyed_by_store_caller_save chunk addr)) INJSP TAIL'
          (frame_undef_regs (destroyedByStore chunk addr) SEP2)⟩
  | Lcall s f sp sig ros b rs m f' hff hsig =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      have BOUND : sizeArguments abi sig ≤ (bnds abi f).bound_outgoing :=
        function_is_within_bounds abi f _ (head_mem_of_suffix TAIL)
      have TAIL' : b <:+ f.fn_code := (List.suffix_cons _ _).trans TAIL
      have GI := sep_proj2 (sep_proj2 (sep_proj2 SEP))
      obtain ⟨bf, tf', A, B, C⟩ := find_function_translated TRANSF AGREGS GI hff
      have IST := is_tail_transf_function TRANSL TAIL
      obtain ⟨ra, D⟩ := rao_exists tf sig ros _ IST
      refine ⟨_, plus_one (.Mcall _ _ _ _ _ _ _ _ _ _ _ A FIND D),
        .call _ _ _ _ _ _ _ _ j tf' ?_ C B AGREGS ((sep_assoc _ _ _).pred.2 SEP)⟩
      refine .cons f sp0 rs b s fb sp' _ _ cs' _ tf TAIL' FIND TRANSL rfl INJSP
        (Val.Vptr_has_type _ _) AGLOCS ?_ STACKS
      intro ofs ty hin
      have := locArguments_bounded abi _ ofs ty hin
      subst hsig
      show ofs + typesize ty ≤ (bnds abi f).bound_outgoing
      exact Int.le_trans this BOUND
  | Ltailcall s f stk sig ros b rs m rs' f' m'' e hff hsig hfree =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      obtain ⟨rs1, m1', P, Q, R, S, T, U, SEP3⟩ := function_epilogue_correct abi rao
        tprog.globalenv TRANSL m' j sp' rs (Linear.parentLocset s) (Mach.parentSp cs')
        (Mach.parentRa cs') _ m rs0 stk m'' _ cs' fb ((sep_swap23 _ _ _ _).pred.1 SEP) AGREGS AGLOCS
        INJSP hfree
      have SEP4 := (sep_swap _ _ _).pred.1 SEP3
      obtain ⟨bf, tf', A, B, C⟩ :=
        find_function_translated TRANSF T (sep_proj2 (sep_proj2 SEP3)) hff
      refine ⟨_, plus_right S (.Mtailcall _ _ _ _ _ _ _ _ _ _ _ _ A FIND P Q R) rfl,
        .call _ _ _ _ _ _ _ _ j tf' (match_stacks_change_sig STACKS ?_) C B T SEP4⟩
      apply zero_size_arguments_tailcall_possible
      rw [← hsig]
      exact wt_state_tailcall WTS
  | Lbuiltin s f sp rs m ef args res b vargs t vres rs' m'' hargs hcall e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      obtain ⟨BND1, BND2⟩ := function_is_within_bounds abi f _ (head_mem_of_suffix TAIL)
      have TAIL' : b <:+ f.fn_code := (List.suffix_cons _ _).trans TAIL
      have VALID : ∀ l ∈ BuiltinArg.paramsList args, locValid abi f l = true :=
        List.all_eq_true.1 (wt_state_builtin WTS)
      obtain ⟨vargs', P, Q⟩ := transl_builtin_args_correct INJSP AGREGS
        (sep_proj2 ((sep_swap _ _ _).pred.1 SEP)) hargs VALID BND2
      have SEPc := (sep_assoc _ _ _).pred.1 ((sep_comm _ _).pred.1 ((sep_assoc _ _ _).pred.2 SEP))
      obtain ⟨j', res', m1', EC, RES, SEP4, INCR, _⟩ := external_call_parallel_rule ef hext hasm
        (fun n sg => hextp n sg _) (fun n sg => hasmp n sg _) hcall SEPc Q
      have SEP5 := (sep_assoc _ _ _).pred.1 ((sep_comm _ _).pred.1 ((sep_assoc _ _ _).pred.2 SEP4))
      have SEP6 := frame_contents_incr SEP5 INCR
      have SEP7 := (sep_swap _ _ _).pred.1
        (stack_contents_change_meminj INCR _ _ _ ((sep_swap _ _ _).pred.1 SEP6))
      refine ⟨_, plus_one (.Mbuiltin _ _ _ _ _ _ _ _ _ vargs' t res' _ m1' ?_ ?_ rfl),
        .intro _ _ _ _ _ _ _ _ _ _ _ j' tf (match_stacks_change_meminj INCR STACKS) TRANSL FIND
          (agree_regs_set_res res (agree_regs_undef_regs _ (agree_regs_inject_incr AGREGS INCR)) RES)
          (agree_locs_set_res res _ (agree_locs_undef_regs _ AGLOCS (fun r hr => BND1 r (.inr hr)))
            (fun r hr => BND1 r (.inl hr)))
          (INCR _ _ _ INJSP) TAIL' (frame_set_res res _ (frame_undef_regs _ SEP7))⟩
      · rw [hsenv]; exact P
      · rw [hsenv]; exact EC
  | Llabel s f sp lbl b rs m =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      exact ⟨_, plus_one (.Mlabel _ _ _ _ _ _ _),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP
          ((List.suffix_cons _ _).trans TAIL) SEP⟩
  | Lgoto s f sp lbl b rs m b' hfl =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      exact ⟨_, plus_one (.Mgoto _ _ _ _ _ _ _ _ _ FIND (transl_find_label TRANSL hfl)),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP
          (find_label_tail hfl) SEP⟩
  | Lcond_true s f sp cond args lbl b rs m rs' b' hc e hfl =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have MINJ := sep_proj1 (sep_proj2 (sep_proj2 SEP))
      exact ⟨_, plus_one (.Mcond_true _ _ _ _ _ _ _ _ _ _ _ _
          (Op.evalCondition_inject (agree_reglist args AGREGS) MINJ hc) FIND
          (transl_find_label TRANSL hfl) rfl),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND
          (agree_regs_undef_regs (destroyedByCond cond) AGREGS)
          (agree_locs_undef_locs (destroyedByCond cond) AGLOCS (destroyed_by_cond_caller_save cond))
          INJSP (find_label_tail hfl) (frame_undef_regs (destroyedByCond cond) SEP)⟩
  | Lcond_false s f sp cond args lbl b rs m rs' hc e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have MINJ := sep_proj1 (sep_proj2 (sep_proj2 SEP))
      exact ⟨_, plus_one (.Mcond_false _ _ _ _ _ _ _ _ _ _
          (Op.evalCondition_inject (agree_reglist args AGREGS) MINJ hc) rfl),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND
          (agree_regs_undef_regs (destroyedByCond cond) AGREGS)
          (agree_locs_undef_locs (destroyedByCond cond) AGLOCS (destroyed_by_cond_caller_save cond))
          INJSP ((List.suffix_cons _ _).trans TAIL) (frame_undef_regs (destroyedByCond cond) SEP)⟩
  | Ljumptable s f sp arg tbl b rs m n lbl b' rs' harg hnth hfl e =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      subst e
      have H : rs0 arg = .Vint n := by
        have := AGREGS arg
        rw [harg] at this
        generalize rs0 arg = v at this ⊢
        cases this; rfl
      exact ⟨_, plus_one (.Mjumptable _ _ _ _ _ _ _ _ _ _ _ _ _ H hnth FIND
          (transl_find_label TRANSL hfl) rfl),
        .intro _ _ _ _ _ _ _ _ _ _ _ j tf STACKS TRANSL FIND
          (agree_regs_undef_regs destroyedByJumptable AGREGS)
          (agree_locs_undef_locs destroyedByJumptable AGLOCS destroyed_by_jumptable_caller_save)
          INJSP (find_label_tail hfl) (frame_undef_regs destroyedByJumptable SEP)⟩
  | Lreturn s f stk b rs m m'' hfree =>
    cases MS with
    | intro _ _ sp0 _ _ _ cs' fb sp' rs0 m' j tf STACKS TRANSL FIND AGREGS AGLOCS INJSP TAIL SEP =>
      obtain ⟨rs1, m1', P, Q, R, S, T, U, SEP3⟩ := function_epilogue_correct abi rao
        tprog.globalenv TRANSL m' j sp' rs (Linear.parentLocset s) (Mach.parentSp cs')
        (Mach.parentRa cs') _ m rs0 stk m'' _ cs' fb ((sep_swap23 _ _ _ _).pred.1 SEP) AGREGS AGLOCS
        INJSP hfree
      exact ⟨_, plus_right S (.Mreturn _ _ _ _ _ _ _ _ _ FIND P Q R) rfl,
        .ret _ _ _ _ _ _ j _ STACKS T ((sep_swap _ _ _).pred.1 SEP3)⟩
  | function_internal s f rs m rs' m'' stk halloc e =>
    cases MS with
    | call _ _ _ _ cs' fb rs0 m' j tf STACKS TRANSL FIND AGREGS SEP =>
      simp only [Stacking.transfFundef, ASTFundef.transfPartial] at TRANSL
      cases TF : transfFunction abi f with
      | Error _ => rw [TF] at TRANSL; cases TRANSL
      | OK tfn =>
        rw [TF] at TRANSL
        cases TRANSL
        obtain ⟨AGCS, AGARGS⟩ := wt_callstate_agree WTS
        have SEP' := (sep_assoc _ _ _).pred.1 ((sep_comm _ _).pred.1 SEP)
        obtain ⟨j', rs'', m2', sp', m3', m4', m5', A, B, C, D, E, F, SEP2, J, K⟩ :=
          function_prologue_correct abi rao tprog.globalenv prog.globalenv TF j rs
            (Linear.parentLocset s) rs' rs0 _ m m' m'' stk (Mach.parentSp cs') (Mach.parentRa cs')
            cs' fb (translCode (fenv abi f) f.fn_code) _ AGREGS AGCS AGARGS e rfl halloc
            (match_stacks_type_sp STACKS) (match_stacks_type_retaddr STACKS) SEP'
        have SEP3 := sep_imp SEP2 (.refl _)
          ((sepconj_imp (.refl _) (sep_comm _ _).1).trans (sep_swap _ _ _).1)
        have SEP4 := (sep_swap _ _ _).pred.1
          (stack_contents_change_meminj K _ _ _ ((sep_swap _ _ _).pred.1 SEP3))
        have hcode : tfn.fn_code = saveCalleeSave (fenv abi f) (translCode (fenv abi f) f.fn_code) := by
          rw [unfold_transf_function TF]; rfl
        refine ⟨_, plus_left (.function_internal _ _ _ _ _ _ _ _ _ _ FIND A B C rfl) ?_ rfl,
          .intro _ _ _ _ _ _ _ _ _ _ _ j' tfn (match_stacks_change_meminj K STACKS) TF FIND E F J
            (List.suffix_refl _) SEP4⟩
        rw [hcode]; exact D
  | function_external s ef args res rs1 rs2 m t m'' hargs hcall e =>
    cases MS with
    | call _ _ _ _ cs' fb rs0 m' j tf STACKS TRANSL FIND AGREGS SEP =>
      simp only [Stacking.transfFundef, ASTFundef.transfPartial] at TRANSL
      cases TRANSL
      subst hargs e
      obtain ⟨_, AGARGS⟩ := wt_callstate_agree WTS
      obtain ⟨vl, ARGS, VINJ⟩ := transl_external_arguments STACKS AGREGS AGARGS (sep_proj1 SEP)
      have SEP' := (sep_assoc _ _ _).pred.1 ((sep_comm _ _).pred.1 SEP)
      obtain ⟨j', res', m1', A, B, C, D, _⟩ := external_call_parallel_rule ef hext hasm
        (fun n sg => hextp n sg _) (fun n sg => hasmp n sg _) hcall SEP' VINJ
      have SEP2 := (sep_comm _ _).pred.1 ((sep_assoc _ _ _).pred.2 C)
      refine ⟨_, plus_one (.function_external _ _ _ _ _ _ _ _ _ _ FIND ARGS ?_ rfl),
        .ret _ _ _ _ _ _ j' _ (match_stacks_change_meminj D STACKS)
          (agree_regs_set_pair _ (agree_regs_undef_caller_save_regs
            (agree_regs_inject_incr AGREGS D)) B)
          (stack_contents_change_meminj D _ _ _ SEP2)⟩
      rw [hsenv]; exact A
  | «return» f sp rs0 c s rs m =>
    cases MS with
    | ret _ _ _ cs' rs1 m' j sg STACKS AGREGS SEP =>
      cases STACKS with
      | cons _ sp0 _ _ _ fb sp' ra c' cs0' _ trf TAIL FIND TRF TRC INJ _ AGL _ STK =>
        subst TRC
        obtain ⟨AGCS, OUTU⟩ := wt_returnstate_agree WTS
        have SEP' := (sep_assoc _ _ _).pred.1 SEP
        refine ⟨_, plus_one (.return _ _ _ _ _ _ _),
          .intro _ _ _ _ _ _ _ _ _ _ _ j trf STK TRF FIND AGREGS (agree_locs_return AGL AGCS) INJ
            TAIL (frame_contents_exten ?_ ?_ (fun _ _ => rfl) SEP')⟩
        · intro ofs ty
          rw [AGCS (.S .Local ofs ty) (by simp [CalleeSaveLoc])]
          exact .refl _
        · intro ofs ty
          rw [OUTU ty ofs]
          exact .undef _

/-! ## Initial and final states -/

include TRANSF in
/-- `Stackingproof.transf_initial_states` -/
theorem transf_initial_states {st1 : Linear.State} (h : Linear.InitialState prog st1) :
    ∃ st2, Mach.InitialState tprog st2 ∧
      MatchStates abi prog.globalenv tprog.globalenv st1 st2 := by
  cases h with
  | intro b f m0 hm hs hf hsig =>
    obtain ⟨tf, FIND, TR⟩ := function_ptr_translated TRANSF hf
    have INJ : Mem.Inject (Mem.flatInj m0.nextblock) m0 m0 := Genv.initmem_inject hm
    have GP : GlobalenvPreserved prog.globalenv (Mem.flatInj m0.nextblock) m0.nextblock :=
      { domain := fun b hb => by simp [Mem.flatInj, hb]
        image := fun b1 b2 delta h _ => by
          simp only [Mem.flatInj] at h
          split at h
          · cases h; rfl
          · cases h
        symbols := fun id b hs => by
          have := Genv.findSymbol_not_fresh hm hs
          simpa [Mem.validBlock] using this
        functions := fun b fd hf => by
          have := Genv.findFunctPtr_not_fresh hm hf
          simpa [Mem.validBlock] using this
        varinfos := fun b gv hv => by
          have := Genv.findVarInfo_not_fresh hm hv
          simpa [Mem.validBlock] using this }
    refine ⟨_, .intro b m0 ?_ ?_, .call [] f _ m0 [] b _ m0 (Mem.flatInj m0.nextblock) tf
      (.empty _ ?_) TR FIND ?_ ?_⟩
    · exact (init_mem_transf_partial TRANSF).trans hm
    · rw [(match_transform_partial_program TRANSF).main_eq, symbols_preserved TRANSF]; exact hs
    · intro l hl
      rw [hsig, locArguments_main] at hl
      cases hl
    · intro r; exact .undef _
    · exact (sep_pure _ _ _).2 ⟨trivial, INJ, ⟨m0.nextblock, Nat.le_refl _, GP⟩,
        fun _ _ _ h => h.elim⟩

/-- `Stackingproof.transf_final_states` -/
theorem transf_final_states {st1 : Linear.State} {st2 : Mach.State} {r : Integers.Int}
    (hm : MatchStates abi prog.globalenv tprog.globalenv st1 st2)
    (h : Linear.FinalState st1 r) : Mach.FinalState st2 r := by
  cases h with
  | intro rs m retcode hr =>
    cases hm with
    | ret _ _ _ cs' rs' m' j sg STACKS AGREGS _ =>
      cases STACKS
      cases e : locResult signature_main with
      | One rres =>
        rw [e] at hr
        have A := AGREGS rres
        simp only [RPair.map, Locmap.getpair] at hr
        rw [hr] at A
        have hv : rs' rres = .Vint r := by
          generalize rs' rres = v at A
          cases A; rfl
        exact .intro _ _ rres r e hv
      | Twolong r1 r2 =>
        have := locResult_type signature_main
        rw [e] at this
        cases this

/-! ## The main theorem -/

include TRANSF in
/-- `Stackingproof.wt_prog`: every function of a program accepted by
    `transf_program` is well typed. -/
theorem wt_prog : ∀ i fd, (i, GlobDef.Gfun fd) ∈ prog.prog_defs → WtFundef abi fd := by
  have hdefs := (match_transform_partial_program TRANSF).defs
  generalize prog.prog_defs = l1 at hdefs
  generalize tprog.prog_defs = l2 at hdefs
  induction hdefs with
  | nil => intro _ _ h; cases h
  | cons hg _ ih =>
    intro i fd h
    cases h with
    | head =>
      cases hg with
      | gfun hr =>
        cases fd with
        | Internal f =>
          simp only [Stacking.transfFundef, ASTFundef.transfPartial] at hr
          cases e : transfFunction abi f with
          | Error _ => rw [e] at hr; cases hr
          | OK tf => exact transf_function_well_typed e
        | External _ => trivial
    | tail _ h => exact ih i fd h

include TRANSF rao_exists hext hasm hextp hasmp in
/-- `Stackingproof.transf_program_correct`: the layout of activation records
    preserves the semantics — a forward simulation from Linear to Mach.

    Besides the hypotheses of the section (memory-injection properties of
    external calls and inline assembly), it assumes that their results are
    well typed (`hextw`, `hasmw`), as CompCert's
    `external_functions_properties` axiom does. -/
theorem transf_program_correct
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ForwardSimulation (Linear.semantics abi prog) (Mach.semantics abi rao tprog) :=
  forward_simulation_plus (L1 := Linear.semantics abi prog) (L2 := Mach.semantics abi rao tprog)
    (fun s s' => WtState abi s ∧ MatchStates abi prog.globalenv tprog.globalenv s s')
    (fun id => by
      show (Genv.toSenv tprog.globalenv).public_symbol id =
        (Genv.toSenv prog.globalenv).public_symbol id
      rw [senv_preserved TRANSF])
    (fun _ h => by
      obtain ⟨st2, A, B⟩ := transf_initial_states abi TRANSF h
      exact ⟨st2, A, wt_initial_state abi prog (wt_prog abi TRANSF) h, B⟩)
    (fun _ _ _ hm h => transf_final_states abi hm.2 h)
    (fun _ _ _ hst _ hm => by
      obtain ⟨s2', A, B⟩ := transf_step_correct abi rao TRANSF rao_exists hext hasm hextp hasmp
        hst hm.1 hm.2
      exact ⟨s2', A, step_type_preservation abi prog (wt_prog abi TRANSF) hextw hasmw hst hm.1, B⟩)

end PRESERVATION

/-! ## Linking (`match_prog`, `transf_program_match`, `TransfStackingLink`) -/

/-- `Stackingproof.match_prog`, as a relation that commutes with linking
    (`MatchProg` is the whole-program equation). -/
def MatchProgLink (abi : AbiKind) (p : Linear.Program) (tp : Mach.Program) : Prop :=
  Linking.MatchProgramCtx (fun _ f tf => Stacking.transfFundef abi f = .OK tf) Eq p tp

/-- `Stackingproof.transf_program_match` -/
theorem transf_program_match (abi : AbiKind) {p : Linear.Program} {tp : Mach.Program}
    (h : Stacking.transfProgram abi p = .OK tp) : MatchProgLink abi p tp :=
  Linking.match_transform_partial_program h

/-- `Stackingproof.TransfStackingLink` -/
instance transfStackingLink (abi : AbiKind) : Linking.TransfLink (MatchProgLink abi) :=
  Linking.transfPartialLinkAST _

/-- `Stackingproof.transf_program_correct`, stated for `match_prog`. -/
theorem transf_program_correct_match (abi : AbiKind)
    (rao : Mach.Function → Mach.Code → Integers.Ptrofs → Prop)
    {p : Linear.Program} {tp : Mach.Program} (h : MatchProgLink abi p tp)
    (hrao : ∀ (f : Mach.Function) (sg : Signature) (ros : Mreg ⊕ Ident) (c : Mach.Code),
        Mach.Instruction.Mcall sg ros :: c <:+ f.fn_code → ∃ ofs, rao f c ofs)
    (hext : ∀ name sg, ExtcallMemInject (externalFunctionsSem name sg))
    (hasm : ∀ name sg, ExtcallMemInject (inlineAssemblySem name sg))
    (hextp : ∀ name sg ge, ExtcallMemProps (externalFunctionsSem name sg) ge)
    (hasmp : ∀ name sg ge, ExtcallMemProps (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg) :
    ForwardSimulation (Linear.semantics abi p) (Mach.semantics abi rao tp) :=
  transf_program_correct abi rao (Linking.transformPartialProgram_of_match h) hrao
    hext hasm hextp hasmp hextw hasmw

end Stackingproof
end CC
