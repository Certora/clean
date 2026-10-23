/-
  Correctness proof for RISC-V code generation, part 4 — the cases of
  `step_simulation` (`riscV/Asmgenproof.v`) for control flow: `Mcall`,
  `Mtailcall`, `Mbuiltin`, `Mgoto`, `Mjumptable`, `Mreturn`, internal and
  external function entry, and return to the caller.

  The memory-extension property of external functions and inline assembly,
  which CompCert takes as an axiom (`external_functions_properties`,
  `inline_assembly_properties`), is a hypothesis (`hext`, `hasm`) of the
  cases that perform an external call.
-/
import CCLib.riscV.AsmgenproofStep1

namespace CC
namespace RiscV
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Smallstep Conventions1

/-- Execution of the `Pallocframe` pseudo-instruction.  (Proved by rewriting
    with the equations of the instruction semantics, so that the kernel never
    has to evaluate a memory operation on a concrete allocated block.) -/
theorem exec_Pallocframe (sym : HalfSplit) (ge : Asm.CGenv) (f : Asm.Function) (sz : Z)
    (pos : Integers.Ptrofs) (rs : Regset) (m m1 m2 : Mem) (stk : Block)
    (h1 : Mem.alloc m 0 sz = (m1, stk))
    (h2 : Mem.storev Mptr m1 (Val.offsetPtr (.Vptr stk Integers.Ptrofs.zero) pos) (rs (.IR SP)) =
      some m2) :
    execInstr sym ge f (.Pallocframe sz pos) rs m =
      .Next (nextinstr (((rs.set (.IR .X30) (rs (.IR SP))).set (.IR SP)
        (.Vptr stk Integers.Ptrofs.zero)).set (.IR .X31) .Vundef)) m2 := by
  rw [execInstr.eq_def]
  simp (config := { iota := false, zeta := false, proj := false, etaStruct := .none, eta := false })
    only [execInstr.match_8.eq_137]
  rw [h1]
  simp (config := { iota := false, zeta := true, proj := false, etaStruct := .none, eta := false })
    only [execInstr.match_1.eq_1]
  rw [h2]

section PRESERVATION
variable {o : Options} {prog : Mach.Program} {tprog : Asm.Program}
  (TRANSF : MatchProg o prog tprog) (sym : HalfSplit)
include TRANSF

private theorem decompose_at {fb : Block} {f : Mach.Function} {i : Mach.Instruction}
    {c : Mach.Code} {ep : Bool} {tf : Asm.Function} {tc : Code} {pc : Val}
    (AT : TranslCodeAtPc o prog.globalenv pc fb f (i :: c) ep tf tc) :
    ∃ ofs k, pc = .Vptr fb ofs ∧ transfFunction o f = .OK tf ∧
      Genv.findFunctPtr tprog.globalenv fb = some (.Internal tf) ∧
      (tf.fn_code.length : Z) ≤ Integers.Ptrofs.max_unsigned ∧
      translCode o f c (it1IsParent ep i) = .OK k ∧ translInstr o f i ep k = .OK tc ∧
      CodeTail (Integers.Ptrofs.unsigned ofs) tf.fn_code tc := by
  cases AT with
  | intro b ofs _ _ _ _ _ FIND TF TC CT =>
    simp only [translCode, res_bind_OK] at TC
    obtain ⟨k, hk, TC⟩ := TC
    exact ⟨ofs, k, rfl, TF, functions_transl TRANSF FIND TF, transf_function_no_overflow TF,
      hk, TC, CT⟩

omit TRANSF in
private theorem findFunctionPtr_reg {ge : Mach.CGenv} {rf : Mreg} {ms : Mach.Regset} {f' : Block}
    (H : Mach.findFunctionPtr ge (.inl rf) ms = some f') : ms rf = .Vptr f' Integers.Ptrofs.zero := by
  simp only [Mach.findFunctionPtr] at H
  split at H
  · rename_i b i hb
    split at H
    · rename_i hi
      cases H
      rw [hb, Integers.Ptrofs.same_if_eq hi]
    · cases H
  · cases H

/-- `step_simulation`, case `Mcall`. -/
theorem step_Mcall {s fb sp sig ros c ms m f f' ra st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mcall sig ros :: c) ms m) st)
    (H : Mach.findFunctionPtr prog.globalenv ros ms = some f')
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : ReturnAddressOffset o f c ra) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st E0 st' ∧
      MatchStates o prog.globalenv
        (.Callstate (.Stackframe fb sp (.Vptr fb ra) c :: s) f' ms m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H0; cases H0
    obtain ⟨ofs, k, hpc, TF, FN, NOOV, hk, TC, CT⟩ := decompose_at TRANSF AT
    obtain ⟨i0, hi0⟩ : ∃ i, tc = i :: k := by
      cases ros <;> simp only [translInstr, res_bind_OK, res_pure_OK] at TC
      · obtain ⟨_, _, h⟩ := TC; exact ⟨_, h.symm⟩
      · cases TC; exact ⟨_, rfl⟩
    subst hi0
    have CT1 := code_tail_next_int NOOV CT
    have hk' : translCode o f c false = .OK k := by cases ros <;> exact hk
    have TCA : TranslCodeAtPc o prog.globalenv
        (.Vptr fb (Integers.Ptrofs.add ofs Integers.Ptrofs.one)) fb f c false tf k :=
      .intro _ _ _ _ _ _ _ FIND TF hk' CT1
    have e := return_address_offset_correct TCA H1
    subst e
    have AGX : ∀ v, Agree ms sp ((rs.set .PC v).set (.IR RA)
        (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)) := fun v =>
      agree_exten AG (fun r hd => by
        rw [Regset.gso _ _ (dataPreg_ne_RA hd), Regset.gso _ _ (dataPreg_ne_PC hd)])
    have STK : MatchStack o prog.globalenv (.Stackframe fb sp
        (.Vptr fb (Integers.Ptrofs.add ofs Integers.Ptrofs.one)) c :: s) :=
      .cons _ _ _ _ _ _ _ _ FIND TCA AG.agree_sp_def STACKS
    cases ros with
    | inl rf =>
      simp only [translInstr, res_bind_OK, res_pure_OK] at TC
      obtain ⟨x0, EQ, h⟩ := TC
      simp only [List.cons.injEq, and_true] at h
      subst h
      have hrf := findFunctionPtr_reg H
      have hx0 : rs (.IR x0) = .Vptr f' Integers.Ptrofs.zero := by
        have LD := ireg_val AG EQ
        rw [hrf] at LD
        generalize rs (.IR x0) = v at LD ⊢
        cases LD; rfl
      refine ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) rfl),
        .call _ _ _ _ _ _ STK MEXT (AGX _) ?_ ?_⟩
      · rw [Regset.gso _ _ (by simp), Regset.gss]; exact hx0
      · rw [Regset.gss, hpc]; rfl
    | inr id =>
      simp only [translInstr] at TC
      simp only [Res.OK.injEq, List.cons.injEq, and_true] at TC
      subst TC
      have hsym : Genv.symbolAddress tprog.globalenv id Integers.Ptrofs.zero =
          .Vptr f' Integers.Ptrofs.zero := by
        simp only [Mach.findFunctionPtr] at H
        simp [Genv.symbolAddress, symbols_preserved TRANSF, H]
      refine ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) rfl),
        .call _ _ _ _ _ _ STK MEXT (AGX _) ?_ ?_⟩
      · rw [Regset.gso _ _ (by simp), Regset.gss, hsym]
      · rw [Regset.gss, hpc]; rfl

/-- `step_simulation`, case `Mtailcall`. -/
theorem step_Mtailcall {s fb stk soff sig ros c ms m f f' m2 st}
    (MS : MatchStates o prog.globalenv (.State s fb (.Vptr stk soff) (.Mtailcall sig ros :: c) ms m)
      st)
    (H : Mach.findFunctionPtr prog.globalenv ros ms = some f')
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (Mach.parentSp s))
    (H2 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (Mach.parentRa s))
    (H3 : Mem.free m stk 0 f.fn_stacksize = some m2) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st E0 st' ∧
      MatchStates o prog.globalenv (.Callstate s f' ms m2) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H0; cases H0
    have AT0 := AT
    obtain ⟨ofs, k, hpc, TF, FN, NOOV, _, TC, CT⟩ := decompose_at TRANSF AT
    cases ros with
    | inl rf =>
      simp only [translInstr, res_bind_OK, res_pure_OK] at TC
      obtain ⟨x0, EQ, rfl⟩ := TC
      have hrf := findFunctionPtr_reg H
      have hx0 : rs (.IR x0) = .Vptr f' Integers.Ptrofs.zero := by
        have LD := ireg_val AG EQ
        rw [hrf] at LD
        generalize rs (.IR x0) = v at LD ⊢
        cases LD; rfl
      obtain ⟨rs1, m1, U, V, W, X, _, Z⟩ := make_epilogue_correct (sym := sym)
        (ge := tprog.globalenv) (fn := tf) o
        prog.globalenv f m stk soff s m2 ms rs _ m' H1 H2 H3 AG MEXT STACKS
      obtain ⟨ofs', P, Q⟩ := exec_straight_steps_2 U NOOV hpc FN CT
      have hd : dataPreg (.IR x0) = true := by rw [← ireg_of_eq EQ]; exact preg_of_data rf
      have hsp : Preg.IR x0 ≠ .IR SP := by rw [← ireg_of_eq EQ]; exact preg_of_not_SP rf
      refine ⟨_, plus_right (plus_star (exec_straight_exec TRANSF sym AT0 U))
          (.exec_step_internal _ _ _ _ _ _ _ _ P FN (find_instr_tail Q) rfl) (E0_right _).symm,
        .call _ _ _ _ _ _ STACKS W (agree_set_other _ V rfl) ?_ ?_⟩
      · rw [Regset.gss, Z _ (by simp) (dataPreg_ne_RA hd) hsp (data_ne_x31 hd), hx0]
      · rw [Regset.gso _ _ (by simp), X]
    | inr id =>
      simp only [translInstr] at TC
      cases TC
      have hsym : Genv.symbolAddress tprog.globalenv id Integers.Ptrofs.zero =
          .Vptr f' Integers.Ptrofs.zero := by
        simp only [Mach.findFunctionPtr] at H
        simp [Genv.symbolAddress, symbols_preserved TRANSF, H]
      obtain ⟨rs1, m1, U, V, W, X, _, _⟩ := make_epilogue_correct (sym := sym)
        (ge := tprog.globalenv) (fn := tf) o
        prog.globalenv f m stk soff s m2 ms rs _ m' H1 H2 H3 AG MEXT STACKS
      obtain ⟨ofs', P, Q⟩ := exec_straight_steps_2 U NOOV hpc FN CT
      refine ⟨_, plus_right (plus_star (exec_straight_exec TRANSF sym AT0 U))
          (.exec_step_internal _ _ _ _ _ _ _ _ P FN (find_instr_tail Q) rfl) (E0_right _).symm,
        .call _ _ _ _ _ _ STACKS W (agree_set_other _ (agree_set_other _ V rfl) rfl) ?_ ?_⟩
      · rw [Regset.gso _ _ (by simp), Regset.gss, hsym]
      · rw [Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), X]

/-- `step_simulation`, case `Mbuiltin`. -/
theorem step_Mbuiltin
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv))
    {s fb sp ef args res b ms m vargs t vres m2 st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mbuiltin ef args res :: b) ms m) st)
    (H : EvalBuiltinArgs (Genv.toSenv prog.globalenv) ms sp m args vargs)
    (H1 : externalCall ef (Genv.toSenv prog.globalenv) vargs m t vres m2) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st t st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp b (Mach.setRes res vres (Mach.undefRegs (destroyedByBuiltin ef) ms)) m2)
        st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f tf tc STACKS FIND MEXT AT AG _ =>
    obtain ⟨ofs, k, hpc, TF, FN, NOOV, hk, TC, CT⟩ := decompose_at TRANSF AT
    simp only [translInstr] at TC
    cases TC
    obtain ⟨vargs', P, Q⟩ := builtin_args_match AG MEXT H
    obtain ⟨vres', m2', A, B, C, _⟩ :=
      externalCall_memExtends ef _ hext hasm _ _ _ _ _ _ _ H1 MEXT Q
    rw [sp_val AG] at P
    have hPC : ∀ r' ∈ (destroyedByBuiltin ef).map pregOf, Preg.PC ≠ r' := by
      intro r' hr
      simp only [List.mem_map] at hr
      obtain ⟨mr, _, rfl⟩ := hr
      exact (preg_of_not_PC mr).symm
    refine ⟨_, plus_one (.exec_step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT)
        (by rw [senv_preserved TRANSF]; exact P) (by rw [senv_preserved TRANSF]; exact A) rfl),
      .intro _ _ _ _ false _ _ _ _ f tf k STACKS FIND C ?_ ?_ (fun h => by cases h)⟩
    · rw [nextinstr_pc, set_res_other _ _ _ rfl, undef_regs_other _ _ hPC,
        Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), hpc]
      exact .intro _ _ _ _ _ _ _ FIND TF hk (code_tail_next_int NOOV CT)
    · refine agree_nextinstr (agree_set_res res (agree_undef_regs AG ?_) B)
      intro r hd hn
      rw [undef_regs_other_2 _ hn, Regset.gso _ _ (data_ne_x31 hd),
        Regset.gso _ _ (dataPreg_ne_RA hd)]

/-- `step_simulation`, case `Mgoto`. -/
theorem step_Mgoto {s fb f sp lbl c ms m c' st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mgoto lbl :: c) ms m) st)
    (H : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mach.findLabel lbl f.fn_code = some c') :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st E0 st' ∧
      MatchStates o prog.globalenv (.State s fb sp c' ms m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H; cases H
    obtain ⟨ofs, k, hpc, TF, FN, _, _, TC, CT⟩ := decompose_at TRANSF AT
    simp only [translInstr] at TC
    cases TC
    obtain ⟨tc', rs', GOTO, AT2, INV⟩ := find_label_goto_label (m := m') FIND TF hpc H1
    exact ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) GOTO),
      .intro _ _ _ _ _ _ _ _ _ _ _ _ STACKS FIND MEXT AT2
        (agree_exten AG (fun r hd => INV r (dataPreg_ne_PC hd))) (fun h => by cases h)⟩

/-- `step_simulation`, case `Mjumptable`. -/
theorem step_Mjumptable {s fb f sp arg tbl c ms m n lbl c' st}
    (MS : MatchStates o prog.globalenv (.State s fb sp (.Mjumptable arg tbl :: c) ms m) st)
    (H : ms arg = .Vint n)
    (H0 : CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some lbl)
    (H1 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H2 : Mach.findLabel lbl f.fn_code = some c') :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb sp c' (Mach.undefRegs destroyedByJumptable ms) m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H1; cases H1
    obtain ⟨ofs, k, hpc, TF, FN, _, _, TC, CT⟩ := decompose_at TRANSF AT
    simp only [translInstr, res_bind_OK, res_pure_OK] at TC
    obtain ⟨r, EQ, rfl⟩ := TC
    obtain ⟨tc', rs', A, B, C⟩ := find_label_goto_label (m := m')
      (rs := (rs.set (.IR .X6) .Vundef).set (.IR .X31) .Vundef)
      FIND TF (by rw [Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), hpc]) H2
    have hr : rs (.IR r) = .Vint n := by
      have LD := ireg_val AG EQ
      rw [H] at LD
      generalize rs (.IR r) = v at LD ⊢
      cases LD; rfl
    refine ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) ?_),
      .intro _ _ _ _ _ _ _ _ _ _ _ _ STACKS FIND MEXT B ?_ (fun h => by cases h)⟩
    · show (match rs (.IR r) with
        | .Vint n =>
          match CminorSel.listNthZ tbl (Integers.Int.unsigned n) with
          | none => Outcome.Stuck
          | some lbl => gotoLabel tf lbl ((rs.set (.IR .X6) .Vundef).set (.IR .X31) .Vundef) m'
        | _ => Outcome.Stuck) = _
      rw [hr]
      simp only [H0]
      exact A
    · refine agree_undef_regs AG (fun r' hd' hn => ?_)
      rw [C r' (dataPreg_ne_PC hd'), Regset.gso _ _ (data_ne_x31 hd'),
        Regset.gso _ _ (show r' ≠ .IR .X6 from hn .R6 (by simp [destroyedByJumptable]))]

/-- `step_simulation`, case `Mreturn`. -/
theorem step_Mreturn {s fb stk soff c ms m f m2 st}
    (MS : MatchStates o prog.globalenv (.State s fb (.Vptr stk soff) (.Mreturn :: c) ms m) st)
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (Mach.parentSp s))
    (H2 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (Mach.parentRa s))
    (H3 : Mem.free m stk 0 f.fn_stacksize = some m2) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st E0 st' ∧
      MatchStates o prog.globalenv (.Returnstate s ms m2) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H0; cases H0
    have AT0 := AT
    obtain ⟨ofs, k, hpc, TF, FN, NOOV, _, TC, CT⟩ := decompose_at TRANSF AT
    simp only [translInstr] at TC
    cases TC
    obtain ⟨rs1, m1, U, V, W, X, _, _⟩ := make_epilogue_correct (sym := sym)
      (ge := tprog.globalenv) (fn := tf) o
      prog.globalenv f m stk soff s m2 ms rs _ m' H1 H2 H3 AG MEXT STACKS
    obtain ⟨ofs', P, Q⟩ := exec_straight_steps_2 U NOOV hpc FN CT
    refine ⟨_, plus_right (plus_star (exec_straight_exec TRANSF sym AT0 U))
        (.exec_step_internal _ _ _ _ _ _ _ _ P FN (find_instr_tail Q) rfl) (E0_right _).symm,
      .ret _ _ _ _ _ STACKS W (agree_set_other _ V rfl) ?_⟩
    rw [Regset.gss, X]

/-- `step_simulation`, case of an internal function entry. -/
theorem step_internal {s fb ms m f m1 m2 m3 stk st}
    (MS : MatchStates o prog.globalenv (.Callstate s fb ms m) st)
    (H : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mem.alloc m 0 f.fn_stacksize = (m1, stk))
    (H2 : Mach.storeStack m1 (.Vptr stk Integers.Ptrofs.zero) Tptr f.fn_link_ofs (Mach.parentSp s) =
      some m2)
    (H3 : Mach.storeStack m2 (.Vptr stk Integers.Ptrofs.zero) Tptr f.fn_retaddr_ofs
      (Mach.parentRa s) = some m3) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st E0 st' ∧
      MatchStates o prog.globalenv
        (.State s fb (.Vptr stk Integers.Ptrofs.zero) f.fn_code
          (Mach.undefRegs destroyedAtFunctionEntry ms) m3) st' := by
  cases MS with
  | call _ _ _ _ m' rs STACKS MEXT AG ATPC ATLR =>
    obtain ⟨tf0, A, B⟩ := functions_translated TRANSF H
    simp only [Asmgen.transfFundef, ASTFundef.transfPartial] at B
    cases TF : transfFunction o f with
    | Error _ => rw [TF] at B; cases B
    | OK tf =>
      rw [TF] at B; cases B
      have FN := A
      have NOOV := transf_function_no_overflow TF
      have TF' := TF
      simp only [transfFunction, res_bind_OK] at TF'
      obtain ⟨tf', h1, h2⟩ := TF'
      split at h2
      · cases h2
      simp only [res_pure_OK] at h2
      simp only [translFunction, res_bind_OK, res_pure_OK] at h1
      obtain ⟨c, hc, htf⟩ := h1
      rw [transl_code'_transl_code] at hc
      have hcode : tf.fn_code = .Pallocframe f.fn_stacksize f.fn_link_ofs ::
          storeindPtr RA SP f.fn_retaddr_ofs
            (.Pcfi_rel_offset (Integers.Ptrofs.to_int f.fn_retaddr_ofs) :: c) := by
        rw [← h2, ← htf]
      obtain ⟨m1', C, D⟩ := Mem.alloc_extends MEXT H1 (Int.le_refl _) (Int.le_refl _)
      obtain ⟨m2', F, G⟩ := Mem.storev_extends D H2 (.refl _) (.refl _)
      obtain ⟨m3', P, Q⟩ := Mem.storev_extends G H3 (.refl _) (.refl _)
      have hsp : rs (.IR SP) = Mach.parentSp s := (sp_val AG).symm
      let rs2 : Regset := nextinstr (((rs.set (.IR .X30) (rs (.IR SP))).set (.IR SP)
        (.Vptr stk Integers.Ptrofs.zero)).set (.IR .X31) .Vundef)
      have E1 : execInstr sym tprog.globalenv tf (.Pallocframe f.fn_stacksize f.fn_link_ofs) rs m' =
          .Next rs2 m2' :=
        exec_Pallocframe sym tprog.globalenv tf _ _ rs m' m1' m2' stk C
          (by rw [hsp]; exact F)
      have hrs2SP : rs2 (.IR SP) = .Vptr stk Integers.Ptrofs.zero := by
        simp only [rs2]
        rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gss]
      have hrs2RA : rs2 (.IR RA) = rs (.IR RA) := by
        simp only [rs2]
        rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gso _ _ (by simp),
          Regset.gso _ _ (by simp)]
      obtain ⟨rs3, U, V⟩ := storeind_ptr_correct (sym := sym) (ge := tprog.globalenv) (fn := tf)
        SP f.fn_retaddr_ofs RA (.Pcfi_rel_offset (Integers.Ptrofs.to_int f.fn_retaddr_ofs) :: c)
        rs2 m2' m3' (by rw [hrs2SP, hrs2RA, ATLR]; exact P) (by decide) (by decide)
      have EXEC : ExecStraight sym tprog.globalenv tf tf.fn_code rs m' c (nextinstr rs3) m3' := by
        rw [hcode]
        exact .step _ _ _ _ _ _ _ _ _ E1 (nextinstr_pc _)
          (exec_straight_trans U (.one _ _ _ _ _ _ rfl (nextinstr_pc _)))
      have CT0 : CodeTail (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) tf.fn_code tf.fn_code := by
        rw [Integers.Ptrofs.unsigned_zero]; exact .zero _
      obtain ⟨ofs', X, Y⟩ := exec_straight_steps_2 EXEC NOOV ATPC FN CT0
      have AG2 : Agree (Mach.undefRegs destroyedAtFunctionEntry ms)
          (.Vptr stk Integers.Ptrofs.zero) rs2 := by
        refine agree_nextinstr (agree_set_other _ ?_ rfl)
        refine agree_change_sp (agree_undef_regs AG ?_) (by simp)
        intro r _ hn
        exact Regset.gso _ _ (hn .R30 (by simp [destroyedAtFunctionEntry]))
      refine ⟨_, exec_straight_steps_1 EXEC NOOV ATPC FN CT0,
        .intro _ _ _ _ true _ _ _ _ _ tf c STACKS H Q ?_ ?_ ?_⟩
      · rw [X]; exact .intro _ _ _ _ _ _ _ H TF hc Y
      · exact agree_exten AG2 (fun r hd => by
          rw [nextinstr_inv _ (dataPreg_ne_PC hd), V r (dataPreg_ne_PC hd) (data_ne_x31 hd)])
      · intro _
        rw [nextinstr_inv _ (by simp), V _ (by simp) (by simp)]
        simp only [rs2]
        rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gso _ _ (by simp),
          Regset.gss, hsp]

/-- `step_simulation`, case of an external function call. -/
theorem step_external
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv))
    {s fb ms m t ef args res m2 st}
    (MS : MatchStates o prog.globalenv (.Callstate s fb ms m) st)
    (H : Genv.findFunctPtr prog.globalenv fb = some (.External ef))
    (H1 : Mach.ExtcallArguments ms m (Mach.parentSp s) ef.sig args)
    (H2 : externalCall ef (Genv.toSenv prog.globalenv) args m t res m2) :
    ∃ st', Smallstep.Plus (Asm.Step sym tprog.globalenv) st t st' ∧
      MatchStates o prog.globalenv
        (.Returnstate s (Mach.setPair (locResult ef.sig) res (Mach.undefCallerSaveRegs ms)) m2)
        st' := by
  cases MS with
  | call _ _ _ _ m' rs STACKS MEXT AG ATPC ATLR =>
    obtain ⟨tf, A, B⟩ := functions_translated TRANSF H
    simp only [Asmgen.transfFundef, ASTFundef.transfPartial] at B
    cases B
    obtain ⟨args', C, D⟩ := extcall_arguments_match AG MEXT H1
    obtain ⟨res', m2', P, Q, R, _⟩ := externalCall_memExtends ef _ hext hasm _ _ _ _ _ _ _ H2 MEXT D
    refine ⟨_, plus_one (.exec_step_external _ _ _ _ _ _ _ _ _ ATPC A
        (by rw [senv_preserved TRANSF]; exact P) C rfl),
      .ret _ _ _ _ _ STACKS R
        (agree_set_other _ (agree_set_pair _ (agree_undef_caller_save_regs AG) Q) rfl) ?_⟩
    rw [Regset.gss, ATLR]

omit TRANSF in
/-- `step_simulation`, case of a return to the caller (no Asm step). -/
theorem step_return {f sp ra c s ms m st}
    (MS : MatchStates o prog.globalenv (.Returnstate (.Stackframe f sp ra c :: s) ms m) st) :
    MatchStates o prog.globalenv (.State s f sp c ms m) st := by
  cases MS with
  | ret _ _ _ m' rs STACKS MEXT AG ATPC =>
    cases STACKS with
    | cons _ _ _ _ _ fn tf tc FIND AT SPD STACKS' =>
      refine .intro _ _ _ _ false _ _ _ _ _ tf tc STACKS' FIND MEXT ?_ AG (fun h => by cases h)
      rw [ATPC]; exact AT

end PRESERVATION

end Asmgenproof
end RiscV
end CC
