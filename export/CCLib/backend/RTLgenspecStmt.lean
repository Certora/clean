/-
  Abstract specification of RTL generation — port of `backend/RTLgenspec.v`,
  part 4: statements and functions (`alloc_optreg_map_ok`,
  `tr_exitexpr_incr`, `tr_stmt_incr`, `transl_exit_charact`,
  `transl_jumptable_charact`, `transl_exitexpr_charact`,
  `convert_builtin_res_charact`, `transl_stmt_charact`,
  `transl_function_charact`).
-/
import CCLib.backend.RTLgenspecExpr

namespace CC
namespace RTLgen

open Op CminorSel RTL

/-- `RTLgenspec.alloc_optreg_map_ok` -/
theorem alloc_optreg_map_ok {map : Mapping} {optid : Option Ident} {s1 s2 : State} {r : Reg}
    {i : StateIncr s1 s2} (hm : MapValid map s1) (h : allocOptreg map optid s1 = .OK r s2 i) :
    RegMapOk map r optid := by
  unfold allocOptreg at h
  split at h
  · exact .somevar _ _ _ (find_var_inv h).1
  · exact .novar _ _ (new_reg_not_in_map h hm)

/-- `RTLgenspec.tr_exitexpr_incr` -/
theorem tr_exitexpr_incr {s1 s2 : State} (hi : StateIncr s1 s2) {map : Mapping} {a : Exitexpr}
    {ns : Node} {nexits : List Node} :
    TrExitexpr s1.st_code map a ns nexits → TrExitexpr s2.st_code map a ns nexits
  | .XEcond _ _ _ _ h => .XEcond _ _ _ _ h
  | .XEjumptable _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .XEjumptable _ _ _ _ _ _ _ _ h1 (tr_expr_incr hi h2) (instr_at_incr hi h3)
  | .XEcondition _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .XEcondition _ _ _ _ _ _ _ _ (tr_condition_incr hi h1) (tr_exitexpr_incr hi h2)
        (tr_exitexpr_incr hi h3)
  | .XElet _ _ _ _ _ _ _ h1 h2 h3 =>
      .XElet _ _ _ _ _ _ _ h1 (tr_expr_incr hi h2) (tr_exitexpr_incr hi h3)

/-- `RTLgenspec.tr_stmt_incr` -/
theorem tr_stmt_incr {s1 s2 : State} (hi : StateIncr s1 s2) {map : Mapping} {s : CminorSel.Stmt}
    {ns nd : Node} {nexits : List Node} {ngoto : Labelmap} {nret : Node} {rret : Option Reg} :
    TrStmt s1.st_code map s ns nd nexits ngoto nret rret →
    TrStmt s2.st_code map s ns nd nexits ngoto nret rret
  | .Sskip .. => .Sskip _ _ _ _ _
  | .Sassign _ _ _ _ _ _ _ _ _ h1 h2 => .Sassign _ _ _ _ _ _ _ _ _ h1 (tr_expr_incr hi h2)
  | .Sstore _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Sstore _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (tr_expr_incr hi h2)
        (instr_at_incr hi h3)
  | .Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
      .Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_incr hi h1) (tr_exprlist_incr hi h2)
        (instr_at_incr hi h3) h4
  | .Scall_imm _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Scall_imm _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2) h3
  | .Stailcall _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Stailcall _ _ _ _ _ _ _ _ _ _ _ _ _ (tr_expr_incr hi h1) (tr_exprlist_incr hi h2)
        (instr_at_incr hi h3)
  | .Stailcall_imm _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
      .Stailcall_imm _ _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2)
  | .Sbuiltin _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Sbuiltin _ _ _ _ _ _ _ _ _ _ _ _ (tr_exprlist_incr hi h1) (instr_at_incr hi h2) h3
  | .Sseq _ _ _ _ _ _ _ _ _ h1 h2 => .Sseq _ _ _ _ _ _ _ _ _ (tr_stmt_incr hi h1) (tr_stmt_incr hi h2)
  | .Sifthenelse _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Sifthenelse _ _ _ _ _ _ _ _ _ _ _ (tr_stmt_incr hi h1) (tr_stmt_incr hi h2)
        (tr_condition_incr hi h3)
  | .Sloop _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Sloop _ _ _ _ _ _ _ _ _ (tr_stmt_incr hi h1) (instr_at_incr hi h2) (instr_at_incr hi h3)
  | .Sblock _ _ _ _ _ _ _ h1 => .Sblock _ _ _ _ _ _ _ (tr_stmt_incr hi h1)
  | .Sexit _ _ _ _ _ _ _ h1 => .Sexit _ _ _ _ _ _ _ h1
  | .Sswitch _ _ _ _ _ _ _ h1 => .Sswitch _ _ _ _ _ _ _ (tr_exitexpr_incr hi h1)
  | .Sreturn_none .. => .Sreturn_none _ _ _ _ _
  | .Sreturn_some _ _ _ _ _ _ _ h1 => .Sreturn_some _ _ _ _ _ _ _ (tr_expr_incr hi h1)
  | .Slabel _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
      .Slabel _ _ _ _ _ _ _ _ _ h1 (instr_at_incr hi h2) (tr_stmt_incr hi h3)
  | .Sgoto _ _ _ _ _ _ _ h1 => .Sgoto _ _ _ _ _ _ _ h1

/-- `RTLgenspec.transl_exit_charact` -/
theorem transl_exit_charact {nexits : List Node} {n : Nat} {s : State} {ne : Node} {s' : State}
    {incr : StateIncr s s'} (h : translExit nexits n s = .OK ne s' incr) :
    nexits[n]? = some ne ∧ s' = s := by
  unfold translExit at h
  rcases hn : nexits[n]? with _ | ne'
  · rw [hn] at h; cases h
  · rw [hn] at h; cases h; exact ⟨rfl, rfl⟩

/-- `RTLgenspec.transl_jumptable_charact` -/
theorem transl_jumptable_charact {nexits : List Node} :
    ∀ (tbl : List Nat) {s : State} {nl : List Node} {s' : State} {incr : StateIncr s s'},
    translJumptable nexits tbl s = .OK nl s' incr → TrJumptable nexits tbl nl ∧ s' = s
  | [], _, _, _, _, h => by
    cases h
    exact ⟨fun v act h => by simp [CminorSel.listNthZ] at h, rfl⟩
  | t1 :: tl, _, _, _, _, h => by
    unfold translJumptable at h
    obtain ⟨n1, s1, i1, i2, h1, h⟩ := bind_inv h
    obtain ⟨nl, s2, i3, i4, h2, h⟩ := bind_inv h
    cases h
    obtain ⟨A, rfl⟩ := transl_exit_charact h1
    obtain ⟨C, rfl⟩ := transl_jumptable_charact tl h2
    refine ⟨fun v act hv => ?_, rfl⟩
    simp only [CminorSel.listNthZ] at hv ⊢
    split
    · next hz => rw [if_pos hz] at hv; cases hv; exact ⟨n1, rfl, A⟩
    · next hz => rw [if_neg hz] at hv; exact C _ _ hv

/-- `RTLgenspec.transl_exitexpr_charact` -/
theorem transl_exitexpr_charact (nexits : List Node) :
    ∀ (a : Exitexpr) {map : Mapping} {s : State} {ns : Node} {s' : State}
      {INCR : StateIncr s s'},
    translExitexpr map a nexits s = .OK ns s' INCR → MapValid map s →
    TrExitexpr s'.st_code map a ns nexits
  | .XEexit n, map, s, ns, s', _, TR, WF => by
    simp only [translExitexpr] at TR
    exact .XEcond _ _ _ _ (transl_exit_charact TR).1
  | .XEjumptable a tbl, map, s, ns, s', _, TR, WF => by
    simp only [translExitexpr] at TR
    obtain ⟨r, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨tbl', s2, i3, i4, h2, TR⟩ := bind_inv TR
    obtain ⟨n1, s3, i5, i6, h3, h4⟩ := bind_inv TR
    obtain ⟨A, rfl⟩ := transl_jumptable_charact tbl h2
    have i15 := stateIncr_trans i1 i5
    exact .XEjumptable _ _ _ _ _ _ _ _ A
      (transl_expr_charact a h4 (map_valid_incr i15 WF)
        (alloc_reg_target_ok WF (regs_valid_nil _) h1) (regs_valid_nil _)
        (reg_valid_incr i5 (alloc_reg_valid WF h1)))
      (instr_at_incr i6 (add_instr_at h3))
  | .XEcondition a b c, map, s, ns, s', _, TR, WF => by
    simp only [translExitexpr] at TR
    obtain ⟨nc, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨nb, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .XEcondition _ _ _ _ _ _ _ _
      (transl_condexpr_charact a h3 (map_valid_incr i13 WF) (regs_valid_nil _))
      (tr_exitexpr_incr i4 (transl_exitexpr_charact nexits b h2 (map_valid_incr i1 WF)))
      (tr_exitexpr_incr (stateIncr_trans i3 i4) (transl_exitexpr_charact nexits c h1 WF))
  | .XElet a b, map, s, ns, s', _, TR, WF => by
    simp only [translExitexpr] at TR
    obtain ⟨r, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨n1, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    have FR := new_reg_fresh h1
    have RV := new_reg_valid h1
    exact .XElet _ _ _ _ _ _ _ (new_reg_not_in_map h1 WF)
      (transl_expr_charact a h3 (map_valid_incr i13 WF) (fresh_target_ok WF (regs_valid_nil _) FR)
        (regs_valid_nil _) (reg_valid_incr i3 RV))
      (tr_exitexpr_incr i4 (transl_exitexpr_charact nexits b h2
        (add_letvar_valid (map_valid_incr i1 WF) RV)))

/-- `RTLgenspec.convert_builtin_res_charact` -/
theorem convert_builtin_res_charact {map : Mapping} {oty : XType} {res : BuiltinRes Ident}
    {s : State} {res' : BuiltinRes Reg} {s' : State} {INCR : StateIncr s s'}
    (TR : convertBuiltinRes map oty res s = .OK res' s' INCR) (WF : MapValid map s) :
    TrBuiltinRes map res res' := by
  cases res with
  | BR id =>
    simp only [convertBuiltinRes] at TR
    obtain ⟨r, s1, i1, i2, h1, h2⟩ := bind_inv TR
    cases h2
    exact .var _ _ _ (find_var_inv h1).1
  | BR_none =>
    simp only [convertBuiltinRes] at TR
    split at TR
    · cases TR; exact .none _
    · obtain ⟨r, s1, i1, i2, h1, h2⟩ := bind_inv TR
      cases h2
      exact .fresh _ _ (new_reg_not_in_map h1 WF)
  | BR_splitlong => cases TR

theorem handleError_error_inv {A : Type} {f : Mon A} {msg : String} {a : A} {s s' : State}
    {i : StateIncr s s'} (h : handleError f (error msg) s = .OK a s' i) :
    ∃ i', f s = .OK a s' i' := by
  unfold handleError at h
  split at h
  · next a' s'' i'' hf => cases h; exact ⟨_, hf⟩
  · cases h

/-- `RTLgenspec.transl_stmt_charact` -/
theorem transl_stmt_charact (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool)
    (map : Mapping) :
    ∀ (stmt : CminorSel.Stmt) {nd : Node} {nexits : List Node} {ngoto : Labelmap} {nret : Node}
      {rret : Option Reg} {s : State} {ns : Node} {s' : State} {INCR : StateIncr s s'},
    translStmt moreLikely map stmt nd nexits ngoto nret rret s = .OK ns s' INCR →
    MapValid map s → ReturnRegOk s map rret →
    TrStmt s'.st_code map stmt ns nd nexits ngoto nret rret
  | .Sskip, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    cases TR; exact .Sskip _ _ _ _ _
  | .Sassign v b, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨r, s1, i1, i2, h1, h2⟩ := bind_inv TR
    obtain ⟨hr, rfl⟩ := find_var_inv h1
    exact .Sassign _ _ _ _ _ _ _ _ _ hr (transl_expr_assign_charact v b h2 WF (.somevar _ _ _ hr))
  | .Sstore chunk addr al b, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨r, s2, i3, i4, h2, TR⟩ := bind_inv TR
    obtain ⟨no, s3, i5, i6, h3, TR⟩ := bind_inv TR
    obtain ⟨ns', s4, i7, i8, h4, h5⟩ := bind_inv TR
    have RLV := alloc_regs_valid al WF h1
    have i35 := stateIncr_trans i3 i5
    have i37 := stateIncr_trans i35 i7
    have i13 := stateIncr_trans i1 i3
    have i15 := stateIncr_trans i13 i5
    have i17 := stateIncr_trans i15 i7
    exact .Sstore _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h5 (map_valid_incr i17 WF)
        (alloc_regs_target_ok al WF (regs_valid_nil _) h1) (regs_valid_nil _)
        (regs_valid_incr i37 RLV))
      (tr_expr_incr i8 (transl_expr_charact b h4 (map_valid_incr i15 WF)
        (alloc_reg_target_ok (map_valid_incr i1 WF) RLV h2) (regs_valid_incr i35 RLV)
        (reg_valid_incr i5 (alloc_reg_valid (map_valid_incr i1 WF) h2))))
      (instr_at_incr (stateIncr_trans i7 i8) (add_instr_at h3))
  | .Scall optid sig (.inl b) cl, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨rf, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨rargs, s2, i3, i4, h2, TR⟩ := bind_inv TR
    obtain ⟨r, s3, i5, i6, h3, TR⟩ := bind_inv TR
    obtain ⟨n1, s4, i7, i8, h4, TR⟩ := bind_inv TR
    obtain ⟨n2, s5, i9, i10, h5, h6⟩ := bind_inv TR
    have WF1 := map_valid_incr i1 WF
    have RFV := alloc_reg_valid WF h1
    have RFV' : RegsValid [rf] s1 := regs_valid_cons RFV (regs_valid_nil _)
    have RAV := alloc_regs_valid cl WF1 h2
    have i35 := stateIncr_trans i3 i5
    have i37 := stateIncr_trans i35 i7
    have i17 := stateIncr_trans (stateIncr_trans i1 i3) (stateIncr_trans i5 i7)
    have i19 := stateIncr_trans i17 i9
    exact .Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (transl_expr_charact b h6 (map_valid_incr i19 WF)
        (alloc_reg_target_ok WF (regs_valid_nil _) h1) (regs_valid_nil _)
        (reg_valid_incr (stateIncr_trans i37 i9) RFV))
      (tr_exprlist_incr i10 (transl_exprlist_charact cl h5 (map_valid_incr i17 WF)
        (alloc_regs_target_ok cl WF1 RFV' h2) (regs_valid_incr i37 RFV')
        (regs_valid_incr (stateIncr_trans i5 i7) RAV)))
      (instr_at_incr (stateIncr_trans i9 i10) (add_instr_at h4))
      (alloc_optreg_map_ok (map_valid_incr (stateIncr_trans i1 i3) WF) h3)
  | .Scall optid sig (.inr id) cl, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨rargs, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨r, s2, i3, i4, h2, TR⟩ := bind_inv TR
    obtain ⟨n1, s3, i5, i6, h3, h4⟩ := bind_inv TR
    have i35 := stateIncr_trans i3 i5
    exact .Scall_imm _ _ _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact cl h4 (map_valid_incr (stateIncr_trans i1 i35) WF)
        (alloc_regs_target_ok cl WF (regs_valid_nil _) h1) (regs_valid_nil _)
        (regs_valid_incr i35 (alloc_regs_valid cl WF h1)))
      (instr_at_incr i6 (add_instr_at h3))
      (alloc_optreg_map_ok (map_valid_incr i1 WF) h2)
  | .Stailcall sig (.inl b) cl, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨rf, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨rargs, s2, i3, i4, h2, TR⟩ := bind_inv TR
    obtain ⟨n1, s3, i5, i6, h3, TR⟩ := bind_inv TR
    obtain ⟨n2, s4, i7, i8, h4, h5⟩ := bind_inv TR
    have WF1 := map_valid_incr i1 WF
    have RFV := alloc_reg_valid WF h1
    have RFV' : RegsValid [rf] s1 := regs_valid_cons RFV (regs_valid_nil _)
    have RAV := alloc_regs_valid cl WF1 h2
    have i35 := stateIncr_trans i3 i5
    have i15 := stateIncr_trans i1 i35
    have i17 := stateIncr_trans i15 i7
    exact .Stailcall _ _ _ _ _ _ _ _ _ _ _ _ _
      (transl_expr_charact b h5 (map_valid_incr i17 WF)
        (alloc_reg_target_ok WF (regs_valid_nil _) h1) (regs_valid_nil _)
        (reg_valid_incr (stateIncr_trans i35 i7) RFV))
      (tr_exprlist_incr i8 (transl_exprlist_charact cl h4 (map_valid_incr i15 WF)
        (alloc_regs_target_ok cl WF1 RFV' h2) (regs_valid_incr i35 RFV') (regs_valid_incr i5 RAV)))
      (instr_at_incr (stateIncr_trans i7 i8) (add_instr_at h3))
  | .Stailcall sig (.inr id) cl, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨rargs, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨n1, s2, i3, i4, h2, h3⟩ := bind_inv TR
    exact .Stailcall_imm _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact cl h3 (map_valid_incr (stateIncr_trans i1 i3) WF)
        (alloc_regs_target_ok cl WF (regs_valid_nil _) h1) (regs_valid_nil _)
        (regs_valid_incr i3 (alloc_regs_valid cl WF h1)))
      (instr_at_incr i4 (add_instr_at h2))
  | .Sbuiltin res ef args, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨rargs, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨res', s2, i3, i4, h2, TR⟩ := bind_inv TR
    obtain ⟨n1, s3, i5, i6, h3, h4⟩ := bind_inv TR
    have i35 := stateIncr_trans i3 i5
    exact .Sbuiltin _ _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact _ h4 (map_valid_incr (stateIncr_trans i1 i35) WF)
        (alloc_regs_target_ok _ WF (regs_valid_nil _) h1) (regs_valid_nil _)
        (regs_valid_incr i35 (alloc_regs_valid _ WF h1)))
      (instr_at_incr i6 (add_instr_at h3))
      (convert_builtin_res_charact h2 (map_valid_incr i1 WF))
  | .Sseq s1 s2, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨n, s0, i1, i2, h1, h2⟩ := bind_inv TR
    exact .Sseq _ _ _ _ _ _ _ _ _
      (tr_stmt_incr i2 (transl_stmt_charact moreLikely map s2 h1 WF OK))
      (transl_stmt_charact moreLikely map s1 h2 (map_valid_incr i1 WF) (return_reg_ok_incr OK i1))
  | .Sifthenelse c strue sfalse, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    split at TR
    · obtain ⟨nfalse, s1, i1, i2, h1, TR⟩ := bind_inv TR
      obtain ⟨ntrue, s2, i3, i4, h2, h3⟩ := bind_inv TR
      have i13 := stateIncr_trans i1 i3
      exact .Sifthenelse _ _ _ _ _ _ _ _ _ _ _
        (tr_stmt_incr i4 (transl_stmt_charact moreLikely map strue h2 (map_valid_incr i1 WF)
          (return_reg_ok_incr OK i1)))
        (tr_stmt_incr (stateIncr_trans i3 i4) (transl_stmt_charact moreLikely map sfalse h1 WF OK))
        (transl_condexpr_charact c h3 (map_valid_incr i13 WF) (regs_valid_nil _))
    · obtain ⟨ntrue, s1, i1, i2, h1, TR⟩ := bind_inv TR
      obtain ⟨nfalse, s2, i3, i4, h2, h3⟩ := bind_inv TR
      have i13 := stateIncr_trans i1 i3
      exact .Sifthenelse _ _ _ _ _ _ _ _ _ _ _
        (tr_stmt_incr (stateIncr_trans i3 i4) (transl_stmt_charact moreLikely map strue h1 WF OK))
        (tr_stmt_incr i4 (transl_stmt_charact moreLikely map sfalse h2 (map_valid_incr i1 WF)
          (return_reg_ok_incr OK i1)))
        (transl_condexpr_charact c h3 (map_valid_incr i13 WF) (regs_valid_nil _))
  | .Sloop sbody, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨n1, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨n2, s2, i3, i4, h2, TR⟩ := bind_inv TR
    obtain ⟨u, s3, i5, i6, h3, h4⟩ := bind_inv TR
    exact .Sloop _ _ _ _ _ _ _ _ _
      (tr_stmt_incr (stateIncr_trans i5 i6) (transl_stmt_charact moreLikely map sbody h2
        (map_valid_incr i1 WF) (return_reg_ok_incr OK i1)))
      (add_instr_at h4) (instr_at_incr i6 (update_instr_at h3))
  | .Sblock sbody, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    exact .Sblock _ _ _ _ _ _ _ (transl_stmt_charact moreLikely map sbody TR WF OK)
  | .Sexit n, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    exact .Sexit _ _ _ _ _ _ _ (transl_exit_charact TR).1
  | .Sswitch a, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    exact .Sswitch _ _ _ _ _ _ _ (transl_exitexpr_charact nexits a TR WF)
  | .Sreturn none, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    cases TR; exact .Sreturn_none _ _ _ _ _
  | .Sreturn (some a), nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    cases rret with
    | none => simp only [translStmt] at TR; cases TR
    | some r =>
      simp only [translStmt] at TR
      cases OK with
      | some _ h1 h2 =>
        exact .Sreturn_some _ _ _ _ _ _ _
          (transl_expr_charact a TR WF (.other _ _ h1 (by simp)) (regs_valid_nil _) h2)
  | .Slabel lbl s0, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    obtain ⟨ns', s1, i1, i2, h1, TR⟩ := bind_inv TR
    rcases hg : ngoto.get lbl with _ | n
    · rw [hg] at TR; cases TR
    · rw [hg] at TR
      obtain ⟨u, s2, i3, i4, h2, h3⟩ := bind_inv TR
      cases h3
      obtain ⟨i', h2'⟩ := handleError_error_inv h2
      exact .Slabel _ _ _ _ _ _ _ _ _ hg (update_instr_at h2')
        (tr_stmt_incr i3 (transl_stmt_charact moreLikely map s0 h1 WF OK))
  | .Sgoto lbl, nd, nexits, ngoto, nret, rret, s, ns, s', _, TR, WF, OK => by
    simp only [translStmt] at TR
    rcases hg : ngoto.get lbl with _ | n
    · rw [hg] at TR; cases TR
    · rw [hg] at TR; cases TR; exact .Sgoto _ _ _ _ _ _ _ hg

/-- `RTLgenspec.transl_function_charact` -/
theorem transl_function_charact {moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool}
    {f : CminorSel.Function} {tf : RTL.Function} (h : translFunction moreLikely f = .OK tf) :
    TrFunction f tf := by
  unfold translFunction at h
  split at h
  · cases h
  · next nentry rparams sfinal INCR TR =>
    cases h
    unfold translFun at TR
    obtain ⟨ngoto, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨rparams', map1, s2, i3, i4, h2, TR⟩ := bind2_inv TR
    obtain ⟨rvars, map2, s3, i5, i6, h3, TR⟩ := bind2_inv TR
    obtain ⟨rret, s4, i7, i8, h4, TR⟩ := bind_inv TR
    obtain ⟨nret, s5, i9, i10, h5, TR⟩ := bind_inv TR
    obtain ⟨nentry', s6, i11, i12, h6, h7⟩ := bind_inv TR
    cases h7
    obtain ⟨_, B⟩ := add_vars_valid _ h2 (init_mapping_valid _)
    obtain ⟨_, D⟩ := add_vars_valid _ h3 B
    have RR := new_reg_return_ok (sig := f.fn_sig) h4 D
    exact .intro f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 h3 rfl
      (transl_stmt_charact moreLikely _ _ h6 (map_valid_incr (stateIncr_trans i7 i9) D)
        (return_reg_ok_incr RR i9))
      (instr_at_incr i11 (add_instr_at h5))

end RTLgen
end CC
