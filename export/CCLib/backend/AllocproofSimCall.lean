/-
  Correctness of register allocation, part 7 — the cases of
  `Allocproof.step_simulation` (`backend/Allocproof.v`) for `Icall`,
  `Itailcall`, `Ibuiltin` and `Ireturn`.
-/
import CCLib.backend.AllocproofSimOp

namespace CC
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions Smallstep
open Allocation.Eqs (add remove)

section PRESERVATION
variable (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function)
  {prog : RTL.Program} {tprog : LTL.Program}
  (TRANSF : Allocation.transfProgram abi regalloc prog = .OK tprog)
include TRANSF

/-- `step_simulation`, case `Icall`. -/
theorem step_simulation_call {s f sp pc rs m sig ros args res pc' fd}
    (hc : f.fn_code.get pc = some (.Icall sig ros args res pc'))
    (hff : RTL.findFunction prog.globalenv ros rs = some fd) (hsig : RTL.funsig fd = sig)
    {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv
        (.Callstate (.Stackframe res f sp pc' rs :: s) fd (rs.getList args) m) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, WTI⟩ := invert_code WTF hc TR
  cases hexp with
  | call _ _ _ _ mv1 ros' mv2 _ k WF1 WF2 =>
  simp only [transferAux] at htr
  obtain ⟨e1, h1, htr⟩ := obind_some htr
  obtain ⟨e2, h2, htr⟩ := obind_some htr
  split at htr
  · cases htr
  next hcond =>
  have hcond := bnot_not_true hcond
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨hu, hn⟩ := hcond
  obtain ⟨e3, h3, htr⟩ := obind_some htr
  obtain ⟨e4, h4, htr⟩ := obind_some htr
  obtain ⟨ls1, A1, B1⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF1 SAT
  have S3 := add_equations_args_satisf h4 B1
  obtain ⟨tfd, E, F⟩ := find_function_translated abi regalloc TRANSF hff h3 S3
  have SIG : LTL.funsig tfd = sig := (sig_function_translated abi regalloc F).trans hsig
  obtain ⟨enext, U, V⟩ := analyze_successors (s := pc') AN hb (by simp [successorsBlockShape]) he
  cases WTI with
  | Icall _ _ _ _ _ _ hargs hres _ =>
  refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
      (star_right A1 (.Lcall _ _ _ _ _ _ _ _ _ E SIG) rfl) rfl, ?_⟩
  refine .call _ _ _ _ _ _ _ _ ?_ F ?_ (fun _ _ => rfl) EXT ?_
  · refine .cons res f sp pc' rs s tf _ ls1 ts _ an enext env STK TF AN U WTF WTR
      (by rw [SIG]; exact hres) ?_
    intro v ls2 m2 hv hvt hagree
    rw [SIG] at hv
    have R := function_return_satisf h2 (add_equation_ros_satisf h3 S3) hu hn hv hagree
    obtain ⟨ls3, A2, B2⟩ := exec_moves abi tprog.globalenv ts tf sp m2
      (wt_regset_assign WTR hvt) h1 WF2 R
    exact ⟨ls3, star_right A2 (.Lbranch _ _ _ _ _ _ _) rfl, satisf_incr B2 V⟩
  · rw [SIG]; exact add_equations_args_lessdef h4 B1
  · rw [SIG, ← hargs]; exact wt_regset_list WTR args

/-- `step_simulation`, case `Itailcall`. -/
theorem step_simulation_tailcall {s f stk pc rs m sig ros args fd m1}
    (hc : f.fn_code.get pc = some (.Itailcall sig ros args))
    (hff : RTL.findFunction prog.globalenv ros rs = some fd) (hsig : RTL.funsig fd = sig)
    (hfree : Mem.free m stk 0 f.fn_stacksize = some m1)
    {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv
      (.State s f (.Vptr stk Integers.Ptrofs.zero) pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv (.Callstate s fd (rs.getList args) m1) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, WTI⟩ := invert_code WTF hc TR
  cases hexp with
  | tailcall _ _ _ mv1 ros' k WF1 =>
  simp only [transferAux] at htr
  split at htr
  rotate_left
  · cases htr
  next hcond =>
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨⟨htp, hres⟩, hros⟩ := hcond
  obtain ⟨e1, h1, htr⟩ := obind_some htr
  obtain ⟨e2, h2, htr⟩ := obind_some htr
  obtain ⟨ls1, A1, B1⟩ := exec_moves abi tprog.globalenv ts tf _ m' WTR htr WF1 SAT
  have S3 := add_equations_args_satisf h2 B1
  obtain ⟨tfd, E, F⟩ := find_function_translated abi regalloc TRANSF hff h1 S3
  have SIG : LTL.funsig tfd = sig := (sig_function_translated abi regalloc F).trans hsig
  obtain ⟨m'', P, Q⟩ := Mem.free_parallel_extends EXT hfree
  cases transf_function_inv TF with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsz hsg =>
  cases WTI with
  | Itailcall _ _ _ _ hargs _ _ =>
  refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
      (star_right A1 (.Ltailcall _ _ _ _ _ _ _ _ _ _ _ rfl
        (by rw [find_function_tailcall _ _ _ hros]; exact E) SIG (hsz ▸ P)) rfl) rfl, ?_⟩
  refine .call _ _ _ _ _ _ _ _ ?_ F ?_ (return_regs_agree_callee_save _ _) Q ?_
  · exact match_stackframes_change_sig abi regalloc STK (by rw [SIG, hres, hsg])
  · rw [SIG, return_regs_arg_values _ _ htp]; exact add_equations_args_lessdef h2 B1
  · rw [SIG, ← hargs]; exact wt_regset_list WTR args

omit TRANSF in
/-- The result registers are caller-save, so `return_regs` takes their value
    from the callee. -/
theorem getpair_returnRegs_result (sg : Signature) (caller callee : Locset) :
    Locmap.getpair ((locResult sg).map Loc.R) (LTL.returnRegs caller callee) =
      Locmap.getpair ((locResult sg).map Loc.R) callee := by
  obtain ⟨mr, h⟩ := locResult_one sg
  have hc := locResult_callerSave sg
  rw [h] at hc ⊢
  simp only [RPair.Forall] at hc
  simp [RPair.map, Locmap.getpair, LTL.returnRegs, hc]

/-- `step_simulation`, case `Ibuiltin`.  The hypotheses `hextx`, `hasmx`,
    `hextw`, `hasmw` are CompCert's axioms `external_call_mem_extends` and
    `external_call_well_typed` for the uninterpreted external functions. -/
theorem step_simulation_builtin
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    {s f sp pc rs m ef args res pc' vargs t vres m1}
    (hc : f.fn_code.get pc = some (.Ibuiltin ef args res pc'))
    (hargs : EvalBuiltinArgs prog.globalenv.toSenv (fun r => rs.get r) sp m args vargs)
    (hcall : externalCall ef prog.globalenv.toSenv vargs m t vres m1) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' t S2' ∧
      MatchStates abi regalloc tprog.globalenv
        (.State s f sp pc' (regmapSetres res vres rs) m1) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, WTI⟩ := invert_code WTF hc TR
  cases hexp with
  | builtin _ _ _ mv1 args' res' mv2 _ k WF1 WF2 =>
  simp only [transferAux] at htr
  obtain ⟨e1, h1, htr⟩ := obind_some htr
  obtain ⟨e2, h2, htr⟩ := obind_some htr
  split at htr
  · cases htr
  next hcond =>
  have hcond := bnot_not_true hcond
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨⟨hu1, hu2⟩, hcu⟩ := hcond
  have : ∃ e3, (match ef with
      | .EF_debug _ _ _ => addEquationsDebugArgs env args args' e2
      | _ => addEquationsBuiltinArgs env args args' e2) = some e3 ∧
      trackMoves env mv1 e3 = some e := by
    cases ef <;> exact obind_some htr
  obtain ⟨e3, h3, htr⟩ := this
  obtain ⟨ls1, A1, B1⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF1 SAT
  have hec : ExtcallMemExtends (externalCall ef) prog.globalenv.toSenv :=
    externalCall_memExtends ef _ (fun n sg => hextx n sg _) (fun n sg => hasmx n sg _)
  obtain ⟨C, vargs', vres', m'', D, E, F, G⟩ := add_equations_builtin_eval (env := env) (args := args)
    (args' := args') (e1 := e2) (e2 := e3) hec (by cases ef <;> exact h3) EXT B1 hargs hcall
  have WTR' := wt_exec_Ibuiltin (externalCall_wellTyped ef hextw hasmw) WTI hcall WTR
  have SAT2 := parallel_set_builtin_res_satisf h2 hu1 hu2 (can_undef_satisf hcu C) F
  obtain ⟨ls3, A3, B3⟩ := exec_moves abi tprog.globalenv ts tf sp m'' WTR' h1 WF2 SAT2
  have hsenv := senv_preserved abi regalloc TRANSF
  refine ⟨_, plus_left (t1 := E0) (t2 := t) (.start_block _ _ _ _ _ _ _ hbb)
      (star_trans (t1 := E0) (t2 := t) A1
        (star_left (t1 := t) (t2 := E0) (.Lbuiltin _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hsenv ▸ D)
          (hsenv ▸ E) rfl)
          (star_right A3 (.Lbranch _ _ _ _ _ _ _) rfl) (E0_right t).symm) rfl) rfl,
    match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he B3 G WTF WTR'⟩

omit TRANSF in
/-- `step_simulation`, case `Ireturn`. -/
theorem step_simulation_return {s f stk pc rs m or m1}
    (hc : f.fn_code.get pc = some (.Ireturn or))
    (hfree : Mem.free m stk 0 f.fn_stacksize = some m1) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv
      (.State s f (.Vptr stk Integers.Ptrofs.zero) pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv
        (.Returnstate s (regmapOptget or .Vundef rs) m1) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, WTI⟩ := invert_code WTF hc TR
  obtain ⟨m'', P, Q⟩ := Mem.free_parallel_extends EXT hfree
  cases transf_function_inv TF with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsz hsg =>
  cases hexp with
  | ret _ mv k WF =>
  cases WTI with
  | Ireturn_none hv =>
    simp only [transferAux] at htr
    obtain ⟨ls1, A1, B1⟩ := exec_moves abi tprog.globalenv ts tf _ m' WTR htr WF SAT
    exact ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
        (star_right A1 (.Lreturn _ _ _ _ _ _ _ (hsz ▸ P)) rfl) rfl,
      .ret _ _ _ _ _ _ _ STK (.undef _) (return_regs_agree_callee_save _ _) Q
        (RTLtyping.hasType_undef _)⟩
  | Ireturn_some arg hv harg =>
    simp only [transferAux] at htr
    obtain ⟨e1, h1, htr⟩ := obind_some htr
    obtain ⟨ls1, A1, B1⟩ := exec_moves abi tprog.globalenv ts tf _ m' WTR htr WF SAT
    refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
        (star_right A1 (.Lreturn _ _ _ _ _ _ _ (hsz ▸ P)) rfl) rfl,
      .ret _ _ _ _ _ _ _ STK ?_ (return_regs_agree_callee_save _ _) Q ?_⟩
    · rw [getpair_returnRegs_result, ← hsg]
      exact add_equations_res_lessdef h1 B1
    · rw [← hsg, ← harg]; exact WTR arg

end PRESERVATION

end Allocproof
end CC
