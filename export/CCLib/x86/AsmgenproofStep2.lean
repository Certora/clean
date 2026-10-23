/-
  Correctness proof for x86-64 code generation, part 4 — the cases of
  `step_simulation` (`x86/Asmgenproof.v`) for control flow: `Mcall`,
  `Mtailcall`, `Mbuiltin`, `Mgoto`, `Mjumptable`, `Mreturn`, internal and
  external function entry, and return to the caller.

  The memory-extension property of external functions and inline assembly,
  which CompCert takes as an axiom (`external_functions_properties`,
  `inline_assembly_properties`), is a hypothesis (`hext`, `hasm`) of the
  cases that perform an external call.
-/
import CCLib.x86.AsmgenproofStep1

namespace CC
namespace X86
namespace Asmgenproof

open Asm Asmgen Asmgenproof0 Asmgenproof1 Smallstep Conventions1

theorem chunk_ofTyp_Tptr : Chunk.ofTyp Tptr = Mptr := rfl

/-! ## Execution of the control-flow instructions -/

section EXEC
variable (ge : Asm.CGenv) (f : Asm.Function) (rs : Regset) (m : Mem)

theorem exec_Pjmp_r (r : Ireg) (sg : Signature) :
    execInstr ge f (.Pjmp_r r sg) rs m = .Next (rs.set .PC (rs (.IR r))) m := by
  rw [execInstr.eq_def]

theorem exec_Pjmp_s (id : Ident) (sg : Signature) :
    execInstr ge f (.Pjmp_s id sg) rs m =
      .Next (rs.set .PC (Genv.symbolAddress ge id Integers.Ptrofs.zero)) m := by
  rw [execInstr.eq_def]

theorem exec_Pret : execInstr ge f .Pret rs m = .Next (rs.set .PC (rs .RA)) m := by
  rw [execInstr.eq_def]

theorem exec_Pcall_r (r : Ireg) (sg : Signature) :
    execInstr ge f (.Pcall_r r sg) rs m =
      .Next ((rs.set .RA (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)).set .PC (rs (.IR r))) m := by
  rw [execInstr.eq_def]

theorem exec_Pcall_s (id : Ident) (sg : Signature) :
    execInstr ge f (.Pcall_s id sg) rs m =
      .Next ((rs.set .RA (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)).set .PC
        (Genv.symbolAddress ge id Integers.Ptrofs.zero)) m := by
  rw [execInstr.eq_def]

theorem exec_Pjmptbl (r : Ireg) (tbl : List Label) :
    execInstr ge f (.Pjmptbl r tbl) rs m =
        (match rs (.IR r) with
         | .Vint n =>
             match CminorSel.listNthZ tbl (Integers.Int.unsigned n) with
             | none => .Stuck
             | some lbl =>
                 gotoLabel f lbl ((rs.set (.IR .RAX) .Vundef).set (.IR .RDX) .Vundef) m
         | _ => .Stuck) := by
  rw [execInstr.eq_def]; rfl

theorem exec_Pfreeframe (sz : Z)
    (rp lp : Integers.Ptrofs) (stk : Block) (soff : Integers.Ptrofs) (m' : Mem)
    (ra sp : Val)
    (hsp : rs (.IR .RSP) = .Vptr stk soff)
    (h1 : Mem.loadv Mptr m (Val.offsetPtr (.Vptr stk soff) rp) = some ra)
    (h2 : Mem.loadv Mptr m (Val.offsetPtr (.Vptr stk soff) lp) = some sp)
    (h3 : Mem.free m stk 0 sz = some m') :
    execInstr ge f (.Pfreeframe sz rp lp) rs m =
      .Next (nextinstr ((rs.set (.IR .RSP) sp).set .RA ra)) m' := by
  rw [execInstr.eq_def]
  simp (config := { iota := false, zeta := false, proj := false, etaStruct := .none, eta := false })
    only [execInstr.match_16.eq_139]
  rw [hsp, h1]
  simp (config := { iota := false, zeta := false, proj := false, etaStruct := .none, eta := false }) only [execInstr.match_14.eq_2]
  rw [h2]
  simp (config := { iota := false, zeta := false, proj := false, etaStruct := .none, eta := false }) only [execInstr.match_14.eq_2, gotoLabel.match_1.eq_1]
  rw [h3]

theorem exec_Pallocframe (sz : Z)
    (rp lp : Integers.Ptrofs) (m1 m2 m3 : Mem) (stk : Block)
    (h1 : Mem.alloc m 0 sz = (m1, stk))
    (h2 : Mem.storev Mptr m1 (Val.offsetPtr (.Vptr stk Integers.Ptrofs.zero) lp) (rs (.IR .RSP)) =
      some m2)
    (h3 : Mem.storev Mptr m2 (Val.offsetPtr (.Vptr stk Integers.Ptrofs.zero) rp) (rs .RA) =
      some m3) :
    execInstr ge f (.Pallocframe sz rp lp) rs m =
      .Next (nextinstr ((rs.set (.IR .RAX) (rs (.IR .RSP))).set (.IR .RSP)
        (.Vptr stk Integers.Ptrofs.zero))) m3 := by
  rw [execInstr.eq_def]
  simp (config := { iota := false, zeta := false, proj := false, etaStruct := .none, eta := false })
    only [execInstr.match_16.eq_138]
  rw [h1]
  simp (config := { iota := false, zeta := true, proj := false, etaStruct := .none, eta := false })
    only [execInstr.match_12.eq_1]
  rw [h2]
  simp (config := { iota := false, zeta := true, proj := false, etaStruct := .none, eta := false })
    only [execInstr.match_10.eq_2]
  rw [h3]

end EXEC

section PRESERVATION
variable {prog : Mach.Program} {tprog : Asm.Program}
  (TRANSF : MatchProg prog tprog) (win64 : Bool)
include TRANSF

private theorem decompose_at {fb : Block} {f : Mach.Function} {i : Mach.Instruction}
    {c : Mach.Code} {ep : Bool} {tf : Asm.Function} {tc : Code} {pc : Val}
    (AT : TranslCodeAtPc prog.globalenv pc fb f (i :: c) ep tf tc) :
    ∃ ofs k, pc = .Vptr fb ofs ∧ transfFunction f = .OK tf ∧
      Genv.findFunctPtr tprog.globalenv fb = some (.Internal tf) ∧
      (tf.fn_code.length : Z) ≤ Integers.Ptrofs.max_unsigned ∧
      translCode f c (it1IsParent ep i) = .OK k ∧ translInstr f i ep k = .OK tc ∧
      CodeTail (Integers.Ptrofs.unsigned ofs) tf.fn_code tc := by
  cases AT with
  | intro b ofs _ _ _ _ _ FIND TF TC CT =>
    simp only [translCode, res_bind_OK] at TC
    obtain ⟨k, hk, TC⟩ := TC
    exact ⟨ofs, k, rfl, TF, functions_transl TRANSF FIND TF, transf_function_no_overflow TF,
      hk, TC, CT⟩

omit TRANSF in
private theorem find_function_ptr_reg {ge : Mach.CGenv} {rf : Mreg} {ms : Mach.Regset}
    {f' : Block} (H : Mach.findFunctionPtr ge (.inl rf) ms = some f') :
    ms rf = .Vptr f' Integers.Ptrofs.zero := by
  simp only [Mach.findFunctionPtr] at H
  split at H
  · rename_i b i hb
    split at H
    · rename_i hi
      cases H
      rw [hb, Integers.Ptrofs.same_if_eq hi]
    · cases H
  · cases H

omit TRANSF in
private theorem lessdef_vptr {v : Val} {b : Block} {o : Integers.Ptrofs}
    (h : Val.Lessdef (.Vptr b o) v) : v = .Vptr b o := by
  generalize hv : Val.Vptr b o = w at h
  cases h with
  | refl => rfl
  | undef => cases hv

/-- `step_simulation`, case `Mcall`. -/
theorem step_Mcall {s fb sp sig ros c ms m f f' ra st}
    (MS : MatchStates prog.globalenv (.State s fb sp (.Mcall sig ros :: c) ms m) st)
    (H : Mach.findFunctionPtr prog.globalenv ros ms = some f')
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : ReturnAddressOffset f c ra) :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st E0 st' ∧
      MatchStates prog.globalenv
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
    have hk' : translCode f c false = .OK k := by cases ros <;> exact hk
    have TCA : TranslCodeAtPc prog.globalenv
        (.Vptr fb (Integers.Ptrofs.add ofs Integers.Ptrofs.one)) fb f c false tf k :=
      .intro _ _ _ _ _ _ _ FIND TF hk' CT1
    have e := return_address_offset_correct TCA H1
    subst e
    have AGX : ∀ v, Agree ms sp ((rs.set .RA (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)).set
        .PC v) := fun v =>
      agree_exten AG (fun r hd => by
        rw [Regset.gso _ _ (dataPreg_ne_PC hd), Regset.gso _ _ (data_diff hd rfl)])
    have STK : MatchStack prog.globalenv (.Stackframe fb sp
        (.Vptr fb (Integers.Ptrofs.add ofs Integers.Ptrofs.one)) c :: s) :=
      .cons _ _ _ _ _ _ _ _ FIND TCA AG.agree_sp_def STACKS
    cases ros with
    | inl rf =>
      simp only [translInstr, res_bind_OK, res_pure_OK] at TC
      obtain ⟨x0, EQ, h⟩ := TC
      simp only [List.cons.injEq, and_true] at h
      subst h
      have hx0 : rs (.IR x0) = .Vptr f' Integers.Ptrofs.zero := by
        have LD := ireg_val AG EQ
        rw [find_function_ptr_reg H] at LD
        exact lessdef_vptr LD
      refine ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) (exec_Pcall_r _ _ _ _ _ _)),
        .call _ _ _ _ _ _ STK MEXT (AGX _) ?_ ?_⟩
      · rw [Regset.gss]; exact hx0
      · rw [Regset.gso _ _ (by simp), Regset.gss, hpc]; rfl
    | inr id =>
      simp only [translInstr] at TC
      simp only [Res.OK.injEq, List.cons.injEq, and_true] at TC
      subst TC
      have hsym : Genv.symbolAddress tprog.globalenv id Integers.Ptrofs.zero =
          .Vptr f' Integers.Ptrofs.zero := by
        simp only [Mach.findFunctionPtr] at H
        simp [Genv.symbolAddress, symbols_preserved TRANSF, H]
      refine ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) (exec_Pcall_s _ _ _ _ _ _)),
        .call _ _ _ _ _ _ STK MEXT (AGX _) ?_ ?_⟩
      · rw [Regset.gss, hsym]
      · rw [Regset.gso _ _ (by simp), Regset.gss, hpc]; rfl

/-- The `Pfreeframe` instruction at the start of the epilogue of `Mtailcall`
and `Mreturn`. -/
private theorem freeframe_step {s : List Mach.Stackframe} {stk : Block} {soff : Integers.Ptrofs}
    {ms : Mach.Regset} {m : Mem} {f : Mach.Function} {m2 : Mem} {rs : Regset} {m' : Mem}
    {tf : Asm.Function}
    (STACKS : MatchStack prog.globalenv s) (MEXT : Mem.Extends m m')
    (AG : Agree ms (.Vptr stk soff) rs)
    (H1 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (Mach.parentSp s))
    (H2 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (Mach.parentRa s))
    (H3 : Mem.free m stk 0 f.fn_stacksize = some m2) :
    ∃ m2', execInstr tprog.globalenv tf (.Pfreeframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs)
        rs m' = .Next (nextinstr ((rs.set (.IR .RSP) (Mach.parentSp s)).set .RA
          (Mach.parentRa s))) m2' ∧ Mem.Extends m2 m2' ∧
      Agree ms (Mach.parentSp s) (nextinstr ((rs.set (.IR .RSP) (Mach.parentSp s)).set .RA
          (Mach.parentRa s))) := by
  have hsp := (sp_val AG).symm
  obtain ⟨parent', A, B⟩ := Mem.loadv_extends MEXT H1 (.refl _)
  have e1 := lessdef_parent_sp STACKS B
  subst e1
  obtain ⟨ra', C, D⟩ := Mem.loadv_extends MEXT H2 (.refl _)
  have e2 := lessdef_parent_ra STACKS D
  subst e2
  obtain ⟨m2', E, F⟩ := Mem.free_parallel_extends MEXT H3
  refine ⟨m2', exec_Pfreeframe _ _ rs m' _ _ _ stk soff m2' _ _ hsp
    (by rw [← chunk_ofTyp_Tptr]; exact C) (by rw [← chunk_ofTyp_Tptr]; exact A) E, F, ?_⟩
  exact agree_nextinstr (agree_set_other _ (agree_change_sp AG (parent_sp_def STACKS)) rfl)

/-- `step_simulation`, case `Mtailcall`. -/
theorem step_Mtailcall {s fb stk soff sig ros c ms m f f' m2 st}
    (MS : MatchStates prog.globalenv (.State s fb (.Vptr stk soff) (.Mtailcall sig ros :: c) ms m)
      st)
    (H : Mach.findFunctionPtr prog.globalenv ros ms = some f')
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (Mach.parentSp s))
    (H2 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (Mach.parentRa s))
    (H3 : Mem.free m stk 0 f.fn_stacksize = some m2) :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st E0 st' ∧
      MatchStates prog.globalenv (.Callstate s f' ms m2) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H0; cases H0
    obtain ⟨ofs, k, hpc, TF, FN, NOOV, _, TC, CT⟩ := decompose_at TRANSF AT
    obtain ⟨m2', E, F, AG2⟩ := freeframe_step TRANSF STACKS MEXT
      AG H1 H2 H3 (tf := tf)
    have hpc2 : nextinstr ((rs.set (.IR .RSP) (Mach.parentSp s)).set .RA (Mach.parentRa s)) .PC =
        .Vptr fb (Integers.Ptrofs.add ofs Integers.Ptrofs.one) := by
      rw [nextinstr_pc, Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), hpc]; rfl
    cases ros with
    | inl rf =>
      simp only [translInstr, res_bind_OK, res_pure_OK] at TC
      obtain ⟨x0, EQ, rfl⟩ := TC
      have CT1 := code_tail_next_int NOOV CT
      have hx0 : rs (.IR x0) = .Vptr f' Integers.Ptrofs.zero := by
        have LD := ireg_val AG EQ
        rw [find_function_ptr_reg H] at LD
        exact lessdef_vptr LD
      have hne : Preg.IR x0 ≠ .IR .RSP := by rw [← ireg_of_eq EQ]; exact preg_of_not_SP rf
      refine ⟨_, plus_left (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) E)
          (star_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc2 FN (find_instr_tail CT1) (exec_Pjmp_r _ _ _ _ _ _))) rfl,
        .call _ _ _ _ _ _ STACKS F (agree_set_other (r := .PC) _ AG2 rfl) ?_ ?_⟩
      · rw [Regset.gss, nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gso _ _ hne,
          hx0]
      · rw [Regset.gso _ _ (by simp), nextinstr_inv _ (by simp), Regset.gss]
    | inr id =>
      simp only [translInstr] at TC
      cases TC
      have CT1 := code_tail_next_int NOOV CT
      have hsym : Genv.symbolAddress tprog.globalenv id Integers.Ptrofs.zero =
          .Vptr f' Integers.Ptrofs.zero := by
        simp only [Mach.findFunctionPtr] at H
        simp [Genv.symbolAddress, symbols_preserved TRANSF, H]
      refine ⟨_, plus_left (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) E)
          (star_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc2 FN (find_instr_tail CT1) (exec_Pjmp_s _ _ _ _ _ _))) rfl,
        .call _ _ _ _ _ _ STACKS F (agree_set_other (r := .PC) _ AG2 rfl) ?_ ?_⟩
      · rw [Regset.gss, hsym]
      · rw [Regset.gso _ _ (by simp), nextinstr_inv _ (by simp), Regset.gss]

/-- `step_simulation`, case `Mbuiltin`. -/
theorem step_Mbuiltin
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv))
    {s fb sp ef args res b ms m vargs t vres m2 st}
    (MS : MatchStates prog.globalenv (.State s fb sp (.Mbuiltin ef args res :: b) ms m) st)
    (H : EvalBuiltinArgs (Genv.toSenv prog.globalenv) ms sp m args vargs)
    (H1 : externalCall ef (Genv.toSenv prog.globalenv) vargs m t vres m2) :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st t st' ∧
      MatchStates prog.globalenv
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
      obtain ⟨mr, _, rfl⟩ := List.mem_map.mp hr
      exact (preg_of_not_PC mr).symm
    refine ⟨_, plus_one (.exec_step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT)
        (by rw [senv_preserved TRANSF]; exact P) (by rw [senv_preserved TRANSF]; exact A) rfl),
      .intro _ _ _ _ false _ _ _ _ f tf k STACKS FIND C ?_ ?_ (fun h => by cases h)⟩
    · rw [nextinstrNf_pc, set_res_other _ _ _ rfl, undef_regs_other _ _ hPC, hpc]
      exact .intro _ _ _ _ _ _ _ FIND TF hk (code_tail_next_int NOOV CT)
    · refine agree_nextinstr_nf (agree_set_res res (agree_undef_regs AG ?_) B)
      intro r _ hn
      exact undef_regs_other_2 _ hn

/-- `step_simulation`, case `Mgoto`. -/
theorem step_Mgoto {s fb f sp lbl c ms m c' st}
    (MS : MatchStates prog.globalenv (.State s fb sp (.Mgoto lbl :: c) ms m) st)
    (H : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mach.findLabel lbl f.fn_code = some c') :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st E0 st' ∧
      MatchStates prog.globalenv (.State s fb sp c' ms m) st' := by
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
    (MS : MatchStates prog.globalenv (.State s fb sp (.Mjumptable arg tbl :: c) ms m) st)
    (H : ms arg = .Vint n)
    (H0 : CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some lbl)
    (H1 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H2 : Mach.findLabel lbl f.fn_code = some c') :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st E0 st' ∧
      MatchStates prog.globalenv
        (.State s fb sp c' (Mach.undefRegs destroyedByJumptable ms) m) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H1; cases H1
    obtain ⟨ofs, k, hpc, TF, FN, _, _, TC, CT⟩ := decompose_at TRANSF AT
    simp only [translInstr, res_bind_OK, res_pure_OK] at TC
    obtain ⟨r, EQ, rfl⟩ := TC
    obtain ⟨tc', rs', A, B, C⟩ := find_label_goto_label (m := m')
      (rs := (rs.set (.IR .RAX) .Vundef).set (.IR .RDX) .Vundef)
      FIND TF (by rw [Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), hpc]) H2
    have hr : rs (.IR r) = .Vint n := by
      have LD := ireg_val AG EQ
      rw [H] at LD
      generalize rs (.IR r) = v at LD ⊢
      cases LD; rfl
    refine ⟨_, plus_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) ?_),
      .intro _ _ _ _ _ _ _ _ _ _ _ _ STACKS FIND MEXT B ?_ (fun h => by cases h)⟩
    · rw [exec_Pjmptbl, hr]
      simp only [H0]
      exact A
    · exact agree_undef_regs AG (fun r' hd' hn => by
        rw [C r' (dataPreg_ne_PC hd'), Regset.gso _ _ (show r' ≠ .IR .RDX from hn .DX (.tail _ (.head _))),
          Regset.gso _ _ (show r' ≠ .IR .RAX from hn .AX (.head _))])

/-- `step_simulation`, case `Mreturn`. -/
theorem step_Mreturn {s fb stk soff c ms m f m2 st}
    (MS : MatchStates prog.globalenv (.State s fb (.Vptr stk soff) (.Mreturn :: c) ms m) st)
    (H0 : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_link_ofs = some (Mach.parentSp s))
    (H2 : Mach.loadStack m (.Vptr stk soff) Tptr f.fn_retaddr_ofs = some (Mach.parentRa s))
    (H3 : Mem.free m stk 0 f.fn_stacksize = some m2) :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st E0 st' ∧
      MatchStates prog.globalenv (.Returnstate s ms m2) st' := by
  cases MS with
  | intro _ _ _ _ ep _ _ m' rs f0 tf tc STACKS FIND MEXT AT AG _ =>
    rw [FIND] at H0; cases H0
    obtain ⟨ofs, k, hpc, TF, FN, NOOV, _, TC, CT⟩ := decompose_at TRANSF AT
    simp only [translInstr] at TC
    cases TC
    obtain ⟨m2', E, F, AG2⟩ := freeframe_step TRANSF STACKS MEXT
      AG H1 H2 H3 (tf := tf)
    have CT1 := code_tail_next_int NOOV CT
    have hpc2 : nextinstr ((rs.set (.IR .RSP) (Mach.parentSp s)).set .RA (Mach.parentRa s)) .PC =
        .Vptr fb (Integers.Ptrofs.add ofs Integers.Ptrofs.one) := by
      rw [nextinstr_pc, Regset.gso _ _ (by simp), Regset.gso _ _ (by simp), hpc]; rfl
    refine ⟨_, plus_left (.exec_step_internal _ _ _ _ _ _ _ _ hpc FN (find_instr_tail CT) E)
        (star_one (.exec_step_internal _ _ _ _ _ _ _ _ hpc2 FN (find_instr_tail CT1) (exec_Pret _ _ _ _))) rfl,
      .ret _ _ _ _ _ STACKS F (agree_set_other (r := .PC) _ AG2 rfl) ?_⟩
    rw [Regset.gss, nextinstr_inv _ (by simp), Regset.gss]

/-- `step_simulation`, case of an internal function entry. -/
theorem step_internal {s fb ms m f m1 m2 m3 stk st}
    (MS : MatchStates prog.globalenv (.Callstate s fb ms m) st)
    (H : Genv.findFunctPtr prog.globalenv fb = some (.Internal f))
    (H1 : Mem.alloc m 0 f.fn_stacksize = (m1, stk))
    (H2 : Mach.storeStack m1 (.Vptr stk Integers.Ptrofs.zero) Tptr f.fn_link_ofs (Mach.parentSp s) =
      some m2)
    (H3 : Mach.storeStack m2 (.Vptr stk Integers.Ptrofs.zero) Tptr f.fn_retaddr_ofs
      (Mach.parentRa s) = some m3) :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st E0 st' ∧
      MatchStates prog.globalenv
        (.State s fb (.Vptr stk Integers.Ptrofs.zero) f.fn_code
          (Mach.undefRegs destroyedAtFunctionEntry ms) m3) st' := by
  cases MS with
  | call _ _ _ _ m' rs STACKS MEXT AG ATPC ATLR =>
    obtain ⟨tf0, A, B⟩ := functions_translated TRANSF H
    simp only [Asmgen.transfFundef, ASTFundef.transfPartial] at B
    cases TF : transfFunction f with
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
      have hcode : tf.fn_code = .Pallocframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs :: c := by
        rw [← h2, ← htf]
      obtain ⟨m1', C, D⟩ := Mem.alloc_extends MEXT H1 (Int.le_refl _) (Int.le_refl _)
      obtain ⟨m2', F, G⟩ := Mem.storev_extends D H2 (.refl _) (.refl _)
      obtain ⟨m3', P, Q⟩ := Mem.storev_extends G H3 (.refl _) (.refl _)
      have hsp : rs (.IR .RSP) = Mach.parentSp s := (sp_val AG).symm
      have EXEC : ExecStraight tprog.globalenv tf tf.fn_code rs m' c
          (nextinstr ((rs.set (.IR .RAX) (rs (.IR .RSP))).set (.IR .RSP)
            (.Vptr stk Integers.Ptrofs.zero))) m3' := by
        rw [hcode]
        exact .one _ _ _ _ _ _ (exec_Pallocframe tprog.globalenv tf rs m' _ _ _ m1' m2' m3' stk
          C (by rw [hsp, ← chunk_ofTyp_Tptr]; exact F)
          (by rw [ATLR, ← chunk_ofTyp_Tptr]; exact P)) (nextinstr_pc _)
      have CT0 : CodeTail (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) tf.fn_code tf.fn_code := by
        rw [Integers.Ptrofs.unsigned_zero]; exact .zero _
      obtain ⟨ofs', X, Y⟩ := exec_straight_steps_2 EXEC NOOV ATPC FN CT0
      refine ⟨_, exec_straight_steps_1 win64 EXEC NOOV ATPC FN CT0,
        .intro _ _ _ _ true _ _ _ _ _ tf c STACKS H Q ?_ ?_ ?_⟩
      · rw [X]; exact .intro _ _ _ _ _ _ _ H TF hc Y
      · refine agree_nextinstr (agree_change_sp (agree_undef_regs AG ?_) (by simp))
        intro r _ hn
        exact Regset.gso _ _ (hn .AX (.head _))
      · intro _
        rw [nextinstr_inv _ (by simp), Regset.gso _ _ (by simp), Regset.gss, hsp]

/-- `step_simulation`, case of an external function call. -/
theorem step_external
    (hext : ∀ name sg, ExtcallMemExtends (externalFunctionsSem name sg) (Genv.toSenv prog.globalenv))
    (hasm : ∀ name sg, ExtcallMemExtends (inlineAssemblySem name sg) (Genv.toSenv prog.globalenv))
    {s fb ms m t ef args res m2 st}
    (MS : MatchStates prog.globalenv (.Callstate s fb ms m) st)
    (H : Genv.findFunctPtr prog.globalenv fb = some (.External ef))
    (H1 : Mach.ExtcallArguments win64 ms m (Mach.parentSp s) ef.sig args)
    (H2 : externalCall ef (Genv.toSenv prog.globalenv) args m t res m2) :
    ∃ st', Smallstep.Plus (Asm.Step win64 tprog.globalenv) st t st' ∧
      MatchStates prog.globalenv
        (.Returnstate s (Mach.setPair (locResult ef.sig) res (Mach.undefCallerSaveRegs win64 ms))
          m2) st' := by
  cases MS with
  | call _ _ _ _ m' rs STACKS MEXT AG ATPC ATLR =>
    obtain ⟨tf, A, B⟩ := functions_translated TRANSF H
    simp only [Asmgen.transfFundef, ASTFundef.transfPartial] at B
    cases B
    obtain ⟨args', C, D⟩ := extcall_arguments_match AG MEXT H1
    obtain ⟨res', m2', P, Q, R, _⟩ := externalCall_memExtends ef _ hext hasm _ _ _ _ _ _ _ H2 MEXT D
    refine ⟨_, plus_one (.exec_step_external _ _ _ _ _ _ _ _ _ ATPC A C
        (by rw [senv_preserved TRANSF]; exact P) rfl),
      .ret _ _ _ _ _ STACKS R
        (agree_set_other _ (agree_set_pair _ (agree_undef_caller_save_regs win64 AG) Q) rfl) ?_⟩
    rw [Regset.gss, ATLR]

omit TRANSF in
/-- `step_simulation`, case of a return to the caller (no Asm step). -/
theorem step_return {f sp ra c s ms m st}
    (MS : MatchStates prog.globalenv (.Returnstate (.Stackframe f sp ra c :: s) ms m) st) :
    MatchStates prog.globalenv (.State s f sp c ms m) st := by
  cases MS with
  | ret _ _ _ m' rs STACKS MEXT AG ATPC =>
    cases STACKS with
    | cons _ _ _ _ _ fn tf tc FIND AT SPD STACKS' =>
      refine .intro _ _ _ _ false _ _ _ _ _ tf tc STACKS' FIND MEXT ?_ AG (fun h => by cases h)
      rw [ATPC]; exact AT

end PRESERVATION

end Asmgenproof
end X86
end CC
