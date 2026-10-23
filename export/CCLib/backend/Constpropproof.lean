/-
  Correctness proof for constant propagation — port of
  `backend/Constpropproof.v`, part 1: preservation of the global
  environment, `transf_ros_correct`, `match_pc` and `match_successor`, the
  `builtin_*_strength_reduction_correct` lemmas, and the simulation
  invariants `match_stackframes` / `match_states`.  The simulation itself
  (`transf_step_correct`, `transf_program_correct`) is in
  `ConstpropproofStep.lean`.

  As in Rocq, the proof is stated for `match_prog prog tprog`
  (`MatchProgLink`): every function of `tprog` is the transformation of the
  corresponding function of `prog` with the read-only memory abstraction
  `romem_for cu` of *some* compilation unit `cu` with `linkorder cu prog`
  (Rocq's `transform_program_contextual`), so that the result also applies to
  separately compiled and linked programs.  The value analysis is used
  through `ValueAnalysis.SoundStateLink`, which is sound for every such unit.
-/
import CCLib.backend.Constprop
import CCLib.aarch64.ConstpropOpproof2
import CCLib.backend.ValueAnalysisSoundInit
import CCLib.backend.Tailcallproof
import CCLib.common.LinkingFundef

namespace CC
namespace Constpropproof

open RTL Constprop ConstpropOp ValueDomain ValueAnalysis Smallstep
open Integers (Ptrofs)

/-- `Constpropproof.match_prog` -/
def MatchProgLink (o : ConstpropOp.Options) (abi : Conventions1.AbiKind) (p tp : RTL.Program) :
    Prop :=
  Linking.MatchProgramCtx
    (fun cu f tf => tf = Constprop.transfFundef o abi (romemFor o.toOptions cu) f) Eq p tp

/-- `Constpropproof.transf_program_match` -/
theorem transf_program_match (o : ConstpropOp.Options) (abi : Conventions1.AbiKind)
    (p : RTL.Program) : MatchProgLink o abi p (Constprop.transfProgram o abi p) :=
  Linking.match_transform_program_contextual _ _ p (fun _ => rfl)

/-- `Constpropproof.TransfConstpropLink` -/
instance transfConstpropLink (o : ConstpropOp.Options) (abi : Conventions1.AbiKind) :
    Linking.TransfLink (MatchProgLink o abi) :=
  Linking.transfTotalContextualLinkAST (fun rm => Constprop.transfFundef o abi rm)
    (fun rm => Constprop.transfFunction o abi rm) (fun _ => ⟨fun _ => rfl, fun _ => rfl⟩)
    (fun cu => romemFor o.toOptions cu)

section PRESERVATION
variable {o : ConstpropOp.Options} {abi : Conventions1.AbiKind} {prog tprog : RTL.Program}

theorem symbols_preserved (TRANSL : MatchProgLink o abi prog tprog) (id : Ident) :
    Genv.findSymbol tprog.globalenv id = Genv.findSymbol prog.globalenv id :=
  (Linking.MatchProgramGen.toMatchProgram TRANSL).find_symbol id

theorem senv_preserved (TRANSL : MatchProgLink o abi prog tprog) :
    Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv :=
  (Linking.MatchProgramGen.toMatchProgram TRANSL).senv

theorem functions_translated (TRANSL : MatchProgLink o abi prog tprog) {v : Val} {f : RTL.Fundef}
    (h : Genv.findFunct prog.globalenv v = some f) :
    ∃ cu, Genv.findFunct tprog.globalenv v =
      some (Constprop.transfFundef o abi (romemFor o.toOptions cu) f) ∧
      Linker.linkorder cu prog := by
  obtain ⟨tf, A, cu, B, C⟩ := (Linking.MatchProgramGen.toMatchProgram TRANSL).find_funct h
  subst C; exact ⟨cu, A, B⟩

theorem function_ptr_translated (TRANSL : MatchProgLink o abi prog tprog) {b : Block}
    {f : RTL.Fundef} (h : Genv.findFunctPtr prog.globalenv b = some f) :
    ∃ cu, Genv.findFunctPtr tprog.globalenv b =
      some (Constprop.transfFundef o abi (romemFor o.toOptions cu) f) ∧
      Linker.linkorder cu prog := by
  obtain ⟨tf, A, cu, B, C⟩ := (Linking.MatchProgramGen.toMatchProgram TRANSL).find_funct_ptr h
  subst C; exact ⟨cu, A, B⟩

/-- `Constpropproof.sig_function_translated` -/
theorem sig_function_translated (rm' : Romem) (f : RTL.Fundef) :
    RTL.funsig (Constprop.transfFundef o abi rm' f) = RTL.funsig f := by
  cases f <;> rfl

/-- `Constpropproof.transf_ros_correct` -/
theorem transf_ros_correct (TRANSL : MatchProgLink o abi prog tprog) {bc : BlockClassification}
    {rs : RTL.Regset} {ae : Aenv}
    {ros : Sum Reg Ident} {f : RTL.Fundef} {rs' : RTL.Regset}
    (GE : GenvMatch bc prog.globalenv) (EM : Ematch bc rs ae)
    (FF : RTL.findFunction prog.globalenv ros rs = some f) (RLD : RegsLessdef rs rs') :
    ∃ cu, RTL.findFunction tprog.globalenv (transfRos ae ros) rs' =
      some (Constprop.transfFundef o abi (romemFor o.toOptions cu) f) ∧
      Linker.linkorder cu prog := by
  cases ros with
  | inl r =>
    have DEFAULT : ∃ cu, RTL.findFunction tprog.globalenv (.inl r) rs' =
        some (Constprop.transfFundef o abi (romemFor o.toOptions cu) f) ∧
        Linker.linkorder cu prog := by
      simp only [RTL.findFunction] at FF ⊢
      have hl := RLD r
      generalize rs.get r = v at hl FF
      generalize rs'.get r = v' at hl ⊢
      cases hl with
      | refl => exact functions_translated TRANSL FF
      | undef => cases FF
    simp only [transfRos]
    split
    · rename_i symb ofs hA
      split
      · rename_i hofs
        have hz : ofs = Ptrofs.zero := (Integers.Ptrofs.eq_spec _ _).1 hofs
        subst hz
        have VM := EM r
        change Vmatch bc (rs.get r) (areg ae r) at VM
        rw [hA] at VM
        have LD := vmatch_ptr_gl GE VM
        simp only [RTL.findFunction] at FF ⊢
        rw [symbols_preserved TRANSL]
        unfold Genv.symbolAddress at LD
        cases hs : Genv.findSymbol prog.globalenv symb with
        | none =>
          rw [hs] at LD
          generalize rs.get r = v at LD FF
          cases LD <;> cases FF
        | some b =>
          rw [hs] at LD
          generalize rs.get r = v at LD FF
          cases LD with
          | refl =>
            simp only [Genv.findFunct, show Integers.Ptrofs.eq Ptrofs.zero Ptrofs.zero = true from
              (Integers.Ptrofs.eq_spec _ _).2 rfl, ↓reduceIte] at FF
            exact function_ptr_translated TRANSL FF
          | undef => cases FF
      · exact DEFAULT
    · exact DEFAULT
  | inr id =>
    simp only [transfRos, RTL.findFunction, symbols_preserved TRANSL] at FF ⊢
    cases e : Genv.findSymbol prog.globalenv id with
    | none => rw [e] at FF; cases FF
    | some b => rw [e] at FF; exact function_ptr_translated TRANSL FF

/-! ### Skipping over resolved conditional branches -/

/-- `Constpropproof.match_pc` -/
inductive MatchPc (f : RTL.Function) (rs : RTL.Regset) (m : Mem) : Nat → Node → Node → Prop where
  | base (n pc) : MatchPc f rs m n pc pc
  | nop (n pc s pcx) : f.fn_code.get pc = some (.Inop s) → MatchPc f rs m n s pcx →
      MatchPc f rs m (n + 1) pc pcx
  | cond (n pc cond args s1 s2 pcx) : f.fn_code.get pc = some (.Icond cond args s1 s2) →
      (∀ b, Op.evalCondition cond (rs.getList args) m = some b →
        MatchPc f rs m n (if b then s1 else s2) pcx) →
      MatchPc f rs m (n + 1) pc pcx

/-- `Constpropproof.match_successor_rec` -/
theorem match_successor_rec (f : RTL.Function) {rs : RTL.Regset} (m : Mem)
    {bc : BlockClassification} {ae : Aenv} (EM : Ematch bc rs ae) :
    ∀ (n : Nat) (pc : Node), MatchPc f rs m n pc (successorRec o n f ae pc)
  | 0, pc => .base _ _
  | n + 1, pc => by
    simp only [successorRec]
    split
    · rename_i s hc
      exact .nop _ _ _ _ hc (match_successor_rec f m EM n s)
    · rename_i cond args s1 s2 hc
      split
      · rename_i b STATIC
        refine .cond _ _ _ _ _ _ _ hc fun b' DYNAMIC => ?_
        have hb : b = b' := resolve_branch_sound (by
          rw [← DYNAMIC]
          exact ValueAOp.eval_static_condition_sound o.toOptions cond m (aregs_sound EM args)) STATIC
        subst hb
        exact match_successor_rec f m EM n _
      · exact .base _ _
    · exact .base _ _

/-- `Constpropproof.match_successor` -/
theorem match_successor (f : RTL.Function) {rs : RTL.Regset} (m : Mem)
    {bc : BlockClassification} {ae : Aenv} (pc : Node) (EM : Ematch bc rs ae) :
    MatchPc f rs m numIter pc (successor o f ae pc) :=
  match_successor_rec f m EM _ _

/-! ### Builtin arguments -/

section BUILTIN
variable {ge : Senv} {bc : BlockClassification} {sp : Val} {m : Mem} {rs : RTL.Regset}
  {ae : Aenv}

/-- `Constpropproof.builtin_arg_reduction_correct` -/
theorem builtin_arg_reduction_correct (EM : Ematch bc rs ae) {a : BuiltinArg Reg} {v : Val}
    (h : EvalBuiltinArg ge (fun r => rs.get r) sp m a v) :
    EvalBuiltinArg ge (fun r => rs.get r) sp m (builtinArgReduction o ae a) v := by
  induction h with
  | BA x =>
    have VM := EM x
    change Vmatch bc (rs.get x) (areg ae x) at VM
    simp only [builtinArgReduction]
    split
    · rename_i n hA; rw [hA] at VM
      generalize rs.get x = w at VM ⊢; cases VM; exact .BA_int _
    · rename_i n hA; rw [hA] at VM
      generalize rs.get x = w at VM ⊢; cases VM; exact .BA_long _
    · rename_i n hA
      split
      · rw [hA] at VM; generalize rs.get x = w at VM ⊢; cases VM; exact .BA_float _
      · exact .BA _
    · rename_i n hA
      split
      · rw [hA] at VM; generalize rs.get x = w at VM ⊢; cases VM; exact .BA_single _
      · exact .BA _
    · exact .BA _
  | BA_int n => exact .BA_int n
  | BA_long n => exact .BA_long n
  | BA_float n => exact .BA_float n
  | BA_single n => exact .BA_single n
  | BA_loadstack chunk ofs v hl => exact .BA_loadstack _ _ _ hl
  | BA_addrstack ofs => exact .BA_addrstack _
  | BA_loadglobal chunk id ofs v hl => exact .BA_loadglobal _ _ _ _ hl
  | BA_addrglobal id ofs => exact .BA_addrglobal _ _
  | BA_splitlong hi lo vhi vlo _ _ IH1 IH2 =>
    simp only [builtinArgReduction]
    split
    · rename_i nhi nlo E1 E2
      rw [E1] at IH1; rw [E2] at IH2
      cases IH1; cases IH2
      exact .BA_long _
    · exact .BA_splitlong _ _ _ _ IH1 IH2
  | BA_addptr a1 a2 v1 v2 _ _ IH1 IH2 => exact .BA_addptr _ _ _ _ IH1 IH2

/-- `Constpropproof.builtin_arg_strength_reduction_correct` -/
theorem builtin_arg_strength_reduction_correct (EM : Ematch bc rs ae) {a : BuiltinArg Reg}
    {v : Val} (c : BuiltinArgConstraint) (h : EvalBuiltinArg ge (fun r => rs.get r) sp m a v) :
    EvalBuiltinArg ge (fun r => rs.get r) sp m (builtinArgStrengthReduction o ae a c) v := by
  simp only [builtinArgStrengthReduction]
  split
  · exact builtin_arg_reduction_correct EM h
  · exact h

/-- `Constpropproof.builtin_args_strength_reduction_correct` -/
theorem builtin_args_strength_reduction_correct (EM : Ematch bc rs ae) :
    ∀ {al : List (BuiltinArg Reg)} {vl : List Val} (cl : List BuiltinArgConstraint),
    EvalBuiltinArgs ge (fun r => rs.get r) sp m al vl →
    EvalBuiltinArgs ge (fun r => rs.get r) sp m (builtinArgsStrengthReduction o ae al cl) vl
  | [], _, _, .nil => .nil
  | _ :: _, _, cl, .cons h hl =>
    .cons (builtin_arg_strength_reduction_correct EM _ h)
      (builtin_args_strength_reduction_correct EM cl.tail hl)

/-- `Constpropproof.debug_strength_reduction_correct` -/
theorem debug_strength_reduction_correct (EM : Ematch bc rs ae) :
    ∀ {al : List (BuiltinArg Reg)} {vl : List Val},
    EvalBuiltinArgs ge (fun r => rs.get r) sp m al vl →
    ∃ vl', EvalBuiltinArgs ge (fun r => rs.get r) sp m (debugStrengthReduction o ae al) vl'
  | [], _, .nil => ⟨[], .nil⟩
  | a1 :: al, b1 :: _, .cons h hl => by
    obtain ⟨vl', A⟩ := debug_strength_reduction_correct EM hl
    have B : EvalBuiltinArgs ge (fun r => rs.get r) sp m (a1 :: debugStrengthReduction o ae al)
        (b1 :: vl') := .cons h A
    have C := builtin_arg_reduction_correct (o := o) EM h
    simp only [debugStrengthReduction]
    split
    · exact ⟨_, .cons C B⟩
    · exact ⟨_, .cons C B⟩
    · exact ⟨_, .cons C B⟩
    · exact ⟨_, .cons C B⟩
    · exact ⟨_, B⟩

/-- `Constpropproof.builtin_strength_reduction_correct` -/
theorem builtin_strength_reduction_correct (EM : Ematch bc rs ae) {ef : ExtFun}
    {args : List (BuiltinArg Reg)} {vargs : List Val} {t : Trace} {vres : Val} {m' : Mem}
    (hargs : EvalBuiltinArgs ge (fun r => rs.get r) sp m args vargs)
    (hcall : externalCall ef ge vargs m t vres m') :
    ∃ vargs', EvalBuiltinArgs ge (fun r => rs.get r) sp m (builtinStrengthReduction o ae ef args)
      vargs' ∧ externalCall ef ge vargs' m t vres m' := by
  cases ef with
  | EF_debug k txt targs =>
    obtain ⟨vargs', P⟩ := debug_strength_reduction_correct (o := o) EM hargs
    refine ⟨vargs', P, ?_⟩
    change ExtcallDebugSem _ _ _ _ _ _ at hcall
    cases hcall with
    | intro => exact .intro _ _ _
  | _ => exact ⟨vargs, builtin_args_strength_reduction_correct EM _ hargs, hcall⟩

end BUILTIN

/-! ### The simulation invariants -/

variable (o abi prog)

/-- `Constpropproof.match_stackframes` -/
inductive MatchStackframes : RTL.Stackframe → RTL.Stackframe → Prop where
  | intro (res f sp pc rs rs' cu) : Linker.linkorder cu prog → RegsLessdef rs rs' →
      MatchStackframes (.Stackframe res f sp pc rs)
        (.Stackframe res (Constprop.transfFunction o abi (romemFor o.toOptions cu) f) sp pc rs')

/-- `Constpropproof.match_states` -/
inductive MatchStates : Nat → RTL.State → RTL.State → Prop where
  | intro (s sp pc rs m f s' pc' rs' m' cu n) :
      Linker.linkorder cu prog →
      ListForall2 (MatchStackframes o abi prog) s s' → MatchPc f rs m n pc pc' →
      RegsLessdef rs rs' → Mem.Extends m m' →
      MatchStates n (.State s f sp pc rs m)
        (.State s' (Constprop.transfFunction o abi (romemFor o.toOptions cu) f) sp pc' rs' m')
  | call (s f args m s' args' m' cu) :
      Linker.linkorder cu prog →
      ListForall2 (MatchStackframes o abi prog) s s' → Val.LessdefList args args' →
      Mem.Extends m m' →
      MatchStates 0 (.Callstate s f args m)
        (.Callstate s' (Constprop.transfFundef o abi (romemFor o.toOptions cu) f) args' m')
  | ret (s v m s' v' m') :
      ListForall2 (MatchStackframes o abi prog) s s' → Val.Lessdef v v' → Mem.Extends m m' →
      MatchStates 0 (.Returnstate s v m) (.Returnstate s' v' m')

variable {o abi prog}

/-- `Constpropproof.match_states_succ` -/
theorem match_states_succ {s : List RTL.Stackframe} {f : RTL.Function} {sp : Val} {pc : Node}
    {rs : RTL.Regset} {m : Mem} {s' : List RTL.Stackframe} {rs' : RTL.Regset} {m' : Mem}
    {cu : RTL.Program} (LINK : Linker.linkorder cu prog)
    (STK : ListForall2 (MatchStackframes o abi prog) s s') (RLD : RegsLessdef rs rs')
    (MLD : Mem.Extends m m') :
    MatchStates o abi prog 0 (.State s f sp pc rs m)
      (.State s' (Constprop.transfFunction o abi (romemFor o.toOptions cu) f) sp pc rs' m') :=
  .intro _ _ _ _ _ _ _ _ _ _ _ _ LINK STK (.base _ _) RLD MLD

/-- `Constpropproof.transf_instr_at` -/
theorem transf_instr_at (rm' : Romem) {f : RTL.Function} {pc : Node} {i : RTL.Instruction}
    (h : f.fn_code.get pc = some i) :
    (Constprop.transfFunction o abi rm' f).fn_code.get pc =
      some (transfInstr o f (ValueAnalysis.analyze o.toOptions abi rm' f) rm' pc i) := by
  simp [Constprop.transfFunction, RTL.transfFunction, PTree.gmap, h]

end PRESERVATION

end Constpropproof
end CC
