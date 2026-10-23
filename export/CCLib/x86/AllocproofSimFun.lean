/-
  [x86-64 instance of `CCLib/backend/AllocproofSimFun.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness of register allocation, part 8 — the cases of
  `Allocproof.step_simulation` (`backend/Allocproof.v`) for function entry
  (internal and external functions) and function return.
-/
import CCLib.x86.AllocproofSimCall

namespace CC
namespace X86

/- `Archi.win64` (a Rocq `Parameter`): whether the Windows x86-64 ABI is used. -/
variable (win64 : Bool)
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions Smallstep
open Allocation.Eqs (add remove)

section PRESERVATION
variable (win64 : Bool) (regalloc : RTL.Function → Res LTL.Function)
  {prog : RTL.Program} {tprog : LTL.Program}

/-- Inversion of `transf_fundef` on an internal function. -/
theorem transfFundef_internal {f : RTL.Function} {tfd : LTL.Fundef}
    (h : Allocation.transfFundef win64 regalloc (.Internal f) = .OK tfd) :
    ∃ tf, tfd = .Internal tf ∧ Allocation.transfFunction win64 regalloc f = .OK tf := by
  unfold Allocation.transfFundef ASTFundef.transfPartial at h
  dsimp only at h
  cases h' : Allocation.transfFunction win64 regalloc f with
  | Error _ => rw [h'] at h; cases h
  | OK tf => rw [h'] at h; cases h; exact ⟨tf, rfl, rfl⟩

/-- Inversion of `transf_fundef` on an external function. -/
theorem transfFundef_external {ef : ExtFun} {tfd : LTL.Fundef}
    (h : Allocation.transfFundef win64 regalloc (.External ef) = .OK tfd) :
    tfd = .External ef := by
  unfold Allocation.transfFundef ASTFundef.transfPartial at h
  cases h; rfl

/-- `step_simulation`, case of an internal function call. -/
theorem step_simulation_internal {s f args m m1 stk}
    (halloc : Mem.alloc m 0 f.fn_stacksize = (m1, stk)) {S1' : LTL.State}
    (hm : MatchStates win64 regalloc tprog.globalenv (.Callstate s (.Internal f) args m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step win64 tprog.globalenv) S1' E0 S2' ∧
      MatchStates win64 regalloc tprog.globalenv
        (.State s f (.Vptr stk Integers.Ptrofs.zero) f.fn_entrypoint
          (RTL.initRegs args f.fn_params) m1) S2' := by
  cases hm with
  | call _ _ _ _ ts tfd ls m' STK TFD LD AG EXT WTA =>
  obtain ⟨tf, rfl, TF⟩ := transfFundef_internal win64 regalloc TFD
  cases transf_function_inv TF with
  | intro env an mv k e1 e2 WTF ANL HENTRY WF TR TRK CE CU hsz hsg =>
  obtain ⟨m'', U, V⟩ := Mem.alloc_extends EXT halloc (Int.le_refl _) (by rw [hsz]; exact Int.le_refl _)
  have WTRS : WtRegset env (RTL.initRegs args f.fn_params) := by
    apply wt_init_regs
    rw [WTF.wt_params, hsg]; exact WTA
  have SAT0 : Satisf (RTL.initRegs args f.fn_params)
      (LTL.undefRegs destroyedAtFunctionEntry (LTL.callRegs ls)) e2 := by
    refine can_undef_satisf CU (compat_entry_satisf CE (locParameters_one win64 _) ?_)
    rw [call_regs_param_values, hsg]; exact LD
  obtain ⟨ls1, A, B⟩ := exec_moves win64 tprog.globalenv ts tf _ m'' WTRS TRK WF SAT0
  exact ⟨_, plus_left (.function_internal _ _ _ _ _ _ _ U rfl)
      (star_left (.start_block _ _ _ _ _ _ _ HENTRY)
        (star_right A (.Lbranch _ _ _ _ _ _ _) rfl) rfl) rfl,
    .intro _ _ _ _ _ _ _ _ _ _ an e1 env STK TF ANL TR B V WTF WTRS⟩

/-- `step_simulation`, case of an external function call.  The hypotheses
    `hextx`, `hasmx`, `hextw`, `hasmw` are CompCert's axioms
    `external_call_mem_extends` and `external_call_well_typed` for the
    uninterpreted external functions. -/
theorem step_simulation_external
    (TRANSF : Allocation.transfProgram win64 regalloc prog = .OK tprog)
    (hextx : ∀ name sg ge, ExtcallMemExtends (externalFunctionsSem name sg) ge)
    (hasmx : ∀ name sg ge, ExtcallMemExtends (inlineAssemblySem name sg) ge)
    (hextw : ∀ name sg, ExtcallWellTyped (externalFunctionsSem name sg) sg)
    (hasmw : ∀ name sg, ExtcallWellTyped (inlineAssemblySem name sg) sg)
    {s ef args res t m m1}
    (hcall : externalCall ef prog.globalenv.toSenv args m t res m1) {S1' : LTL.State}
    (hm : MatchStates win64 regalloc tprog.globalenv (.Callstate s (.External ef) args m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step win64 tprog.globalenv) S1' t S2' ∧
      MatchStates win64 regalloc tprog.globalenv (.Returnstate s res m1) S2' := by
  cases hm with
  | call _ _ _ _ ts tfd ls m' STK TFD LD AG EXT WTA =>
  have := transfFundef_external win64 regalloc TFD
  subst this
  have hec : ExtcallMemExtends (externalCall ef) prog.globalenv.toSenv :=
    externalCall_memExtends ef _ (fun n sg => hextx n sg _) (fun n sg => hasmx n sg _)
  obtain ⟨res', m'', F, G, J, _⟩ := hec _ _ _ _ _ _ _ hcall EXT LD
  have hsenv := senv_preserved win64 regalloc TRANSF
  refine ⟨_, plus_one (.function_external _ _ _ _ _ _ _ _ _ rfl (hsenv ▸ F) rfl),
    .ret _ _ _ _ _ _ ef.sig STK ?_ ?_ J ?_⟩
  · obtain ⟨mr, hmr⟩ := locResult_one ef.sig
    simp only [hmr, RPair.map, Locmap.getpair, Locmap.setpair, Locmap.gss_reg]
    exact G
  · intro l hl
    rw [AG l hl, locmap_get_set_loc_result_callee_save win64 _ _ _ _ hl]
    cases l with
    | R r => simp only [CalleeSaveLoc] at hl; simp [LTL.undefCallerSaveRegs, hl]
    | S sl ofs ty => cases sl <;> simp_all [CalleeSaveLoc, LTL.undefCallerSaveRegs]
  · exact Val.has_proj_xtype (externalCall_wellTyped ef hextw hasmw _ _ _ _ _ _ hcall)

/-- `step_simulation`, case of a return to the caller. -/
theorem step_simulation_return_state {res f sp pc rs s vres m} {S1' : LTL.State}
    (hm : MatchStates win64 regalloc tprog.globalenv
      (.Returnstate (.Stackframe res f sp pc rs :: s) vres m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step win64 tprog.globalenv) S1' E0 S2' ∧
      MatchStates win64 regalloc tprog.globalenv (.State s f sp pc (rs.set res vres) m) S2' := by
  cases hm with
  | ret _ _ _ ts ls1 m' sg STK LD AG EXT WTR0 =>
  cases STK with
  | cons _ _ _ _ _ _ tf bb ls ts _ an e env STK' TF AN TR WTF WTR hres H =>
  have hty : Val.HasType vres (env res) := by rw [hres]; exact WTR0
  obtain ⟨ls2, A, B⟩ := H vres ls1 m' LD hty AG
  exact ⟨_, plus_left (.return _ _ _ _ _ _ _) A rfl,
    .intro _ _ _ _ _ _ _ _ _ _ an e env STK' TF AN TR B EXT WTF (wt_regset_assign WTR hty)⟩

end PRESERVATION

end Allocproof
end X86
end CC
