/-
  [RISC-V instance of `CCLib/backend/RTLgenspecExpr.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Abstract specification of RTL generation — port of `backend/RTLgenspec.v`,
  part 3: the translation of expressions satisfies its relational
  specification (`transl_expr_charact`, `transl_exprlist_charact`,
  `transl_condexpr_charact`, `transl_expr_assign_charact`).
-/
import CCLib.riscV.RTLgenspecDefs

namespace CC
namespace RiscV
namespace RTLgen

open Op CminorSel RTL

theorem fresh_target_ok {map : Mapping} {pr : List Reg} {s : State} {r : Reg}
    {a : CminorSel.Expr} (hm : MapValid map s) (hpr : RegsValid pr s) (hf : RegFresh r s) :
    TargetRegOk map pr a r :=
  .other _ _ (fun h => hf (hm r h)) (fun h => hf (hpr r h))

theorem not_in_addLetvar {map : Mapping} {r rd : Reg} (h1 : ¬ RegInMap map rd) (h2 : rd ≠ r) :
    ¬ RegInMap (addLetvar map r) rd := by
  rintro (⟨id, A⟩ | B)
  · exact h1 (.inl ⟨id, A⟩)
  · cases B with
    | head => exact h2 rfl
    | tail _ B => exact h1 (.inr B)

theorem targetRegOk_other_inv {map : Mapping} {pr : List Reg} {a : CminorSel.Expr} {rd : Reg}
    (h : TargetRegOk map pr a rd) (hv : ∀ id, a ≠ .Evar id) (hl : ∀ n, a ≠ .Eletvar n) :
    ¬ RegInMap map rd ∧ rd ∉ pr := by
  cases h with
  | var id _ _ => exact absurd rfl (hv id)
  | letvar n _ _ => exact absurd rfl (hl n)
  | other _ _ h1 h2 => exact ⟨h1, h2⟩

mutual
/-- `RTLgenspec.transl_expr_charact` -/
theorem transl_expr_charact :
    ∀ (a : CminorSel.Expr) {map : Mapping} {rd : Reg} {nd : Node} {s : State} {ns : Node}
      {s' : State} {pr : List Reg} {INCR : StateIncr s s'},
    translExpr map a rd nd s = .OK ns s' INCR → MapValid map s → TargetRegOk map pr a rd →
    RegsValid pr s → RegValid rd s → TrExpr s'.st_code map pr a ns nd rd none
  | .Evar id, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨r, s1, i1, i2, h1, h2⟩ := bind_inv TR
    obtain ⟨hr, rfl⟩ := find_var_inv h1
    refine .Evar _ _ _ _ _ _ _ _ hr ?_ (add_move_charact h2)
    cases OK with
    | var _ _ h => rw [hr] at h; cases h; exact .inl ⟨rfl, rfl⟩
    | other _ _ h1 h2 => exact .inr ⟨.novar _ _ h1, h2⟩
  | .Eop op al, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    obtain ⟨O1, O2⟩ := targetRegOk_other_inv OK (by simp) (by simp)
    have i13 := stateIncr_trans i1 i3
    exact .Eop _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF) (alloc_regs_target_ok al WF VALID h1)
        (regs_valid_incr i13 VALID) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) (.novar _ _ O1) O2
  | .Eload chunk addr al, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    obtain ⟨O1, O2⟩ := targetRegOk_other_inv OK (by simp) (by simp)
    have i13 := stateIncr_trans i1 i3
    exact .Eload _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF) (alloc_regs_target_ok al WF VALID h1)
        (regs_valid_incr i13 VALID) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) (.novar _ _ O1) O2
  | .Econdition a b c, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨nfalse, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨ntrue, s2, i3, i4, h2, h3⟩ := bind_inv TR
    obtain ⟨O1, O2⟩ := targetRegOk_other_inv OK (by simp) (by simp)
    have i13 := stateIncr_trans i1 i3
    exact .Econdition _ _ _ _ _ _ _ _ _ _ _
      (transl_condexpr_charact a h3 (map_valid_incr i13 WF) (regs_valid_incr i13 VALID))
      (tr_expr_incr i4 (transl_expr_charact b h2 (map_valid_incr i1 WF) (.other _ _ O1 O2)
        (regs_valid_incr i1 VALID) (reg_valid_incr i1 VALID2)))
      (tr_expr_incr (stateIncr_trans i3 i4) (transl_expr_charact c h1 WF (.other _ _ O1 O2)
        VALID VALID2))
  | .Elet b c, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨r, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨nc, s2, i3, i4, h2, h3⟩ := bind_inv TR
    obtain ⟨O1, O2⟩ := targetRegOk_other_inv OK (by simp) (by simp)
    have i13 := stateIncr_trans i1 i3
    have FR := new_reg_fresh h1
    have RV := new_reg_valid h1
    refine .Elet _ _ _ _ _ _ _ _ _ _ (new_reg_not_in_map h1 WF)
      (transl_expr_charact b h3 (map_valid_incr i13 WF) (fresh_target_ok WF VALID FR)
        (regs_valid_incr i13 VALID) (reg_valid_incr i3 RV)) ?_
    refine tr_expr_incr i4 (transl_expr_charact c h2 (add_letvar_valid (map_valid_incr i1 WF) RV)
      (.other _ _ (not_in_addLetvar O1 ?_) O2) (regs_valid_incr i1 VALID) (reg_valid_incr i1 VALID2))
    exact valid_fresh_different VALID2 FR
  | .Eletvar n, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨r, s1, i1, i2, h1, h2⟩ := bind_inv TR
    obtain ⟨hr, rfl⟩ := find_letvar_inv h1
    refine .Eletvar _ _ _ _ _ _ _ _ hr ?_ (add_move_charact h2)
    cases OK with
    | letvar _ _ h => rw [hr] at h; cases h; exact .inl ⟨rfl, rfl⟩
    | other _ _ h1 h2 => exact .inr ⟨.novar _ _ h1, h2⟩
  | .Ebuiltin ef al, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    obtain ⟨O1, O2⟩ := targetRegOk_other_inv OK (by simp) (by simp)
    have i13 := stateIncr_trans i1 i3
    exact .Ebuiltin _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF) (alloc_regs_target_ok al WF VALID h1)
        (regs_valid_incr i13 VALID) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) (.novar _ _ O1) O2
  | .Eexternal id sg al, map, rd, nd, s, ns, s', pr, _, TR, WF, OK, VALID, VALID2 => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    obtain ⟨O1, O2⟩ := targetRegOk_other_inv OK (by simp) (by simp)
    have i13 := stateIncr_trans i1 i3
    exact .Eexternal _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF) (alloc_regs_target_ok al WF VALID h1)
        (regs_valid_incr i13 VALID) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) (.novar _ _ O1) O2

/-- `RTLgenspec.transl_exprlist_charact` -/
theorem transl_exprlist_charact :
    ∀ (al : Exprlist) {map : Mapping} {rl : List Reg} {nd : Node} {s : State} {ns : Node}
      {s' : State} {pr : List Reg} {INCR : StateIncr s s'},
    translExprlist map al rl nd s = .OK ns s' INCR → MapValid map s → TargetRegsOk map pr al rl →
    RegsValid pr s → RegsValid rl s → TrExprlist s'.st_code map pr al ns nd rl
  | .Enil, map, rl, nd, s, ns, s', pr, _, TR, WF, OK, VALID1, VALID2 => by
    cases OK
    simp only [translExprlist] at TR
    cases TR
    exact .Enil _ _ _
  | .Econs b bs, map, rl, nd, s, ns, s', pr, _, TR, WF, OK, VALID1, VALID2 => by
    cases OK with
    | cons _ _ _ r1 rl' O1 O2 =>
      simp only [translExprlist] at TR
      obtain ⟨no, s1, i1, i2, h1, h2⟩ := bind_inv TR
      have V1 : RegValid r1 s := VALID2 r1 (.head _)
      have V2 : RegsValid rl' s := fun r h => VALID2 r (.tail _ h)
      exact .Econs _ _ _ _ _ _ _ _ _
        (transl_expr_charact b h2 (map_valid_incr i1 WF) O1 (regs_valid_incr i1 VALID1)
          (reg_valid_incr i1 V1))
        (tr_exprlist_incr i2 (transl_exprlist_charact bs h1 WF O2 (regs_valid_cons V1 VALID1) V2))

/-- `RTLgenspec.transl_condexpr_charact` -/
theorem transl_condexpr_charact :
    ∀ (a : Condexpr) {map : Mapping} {ntrue nfalse : Node} {s : State} {ns : Node}
      {s' : State} {pr : List Reg} {INCR : StateIncr s s'},
    translCondexpr map a ntrue nfalse s = .OK ns s' INCR → MapValid map s → RegsValid pr s →
    TrCondition s'.st_code map pr a ns ntrue nfalse
  | .CEcond c al, map, ntrue, nfalse, s, ns, s', pr, _, TR, WF, VALID => by
    simp only [translCondexpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨nt, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .CEcond _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF) (alloc_regs_target_ok al WF VALID h1)
        (regs_valid_incr i13 VALID) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2))
  | .CEcondition a b c, map, ntrue, nfalse, s, ns, s', pr, _, TR, WF, VALID => by
    simp only [translCondexpr] at TR
    obtain ⟨nc, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨nb, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .CEcondition _ _ _ _ _ _ _ _ _ _
      (transl_condexpr_charact a h3 (map_valid_incr i13 WF) (regs_valid_incr i13 VALID))
      (tr_condition_incr i4 (transl_condexpr_charact b h2 (map_valid_incr i1 WF)
        (regs_valid_incr i1 VALID)))
      (tr_condition_incr (stateIncr_trans i3 i4) (transl_condexpr_charact c h1 WF VALID))
  | .CElet b c, map, ntrue, nfalse, s, ns, s', pr, _, TR, WF, VALID => by
    simp only [translCondexpr] at TR
    obtain ⟨r, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨nc, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    have FR := new_reg_fresh h1
    have RV := new_reg_valid h1
    exact .CElet _ _ _ _ _ _ _ _ _ (new_reg_not_in_map h1 WF)
      (transl_expr_charact b h3 (map_valid_incr i13 WF) (fresh_target_ok WF VALID FR)
        (regs_valid_incr i13 VALID) (reg_valid_incr i3 RV))
      (tr_condition_incr i4 (transl_condexpr_charact c h2
        (add_letvar_valid (map_valid_incr i1 WF) RV) (regs_valid_incr i1 VALID)))
end

/-- `RTLgenspec.transl_expr_assign_charact` -/
theorem transl_expr_assign_charact (id : Ident) :
    ∀ (a : CminorSel.Expr) {map : Mapping} {rd : Reg} {nd : Node} {s : State} {ns : Node}
      {s' : State} {INCR : StateIncr s s'},
    translExpr map a rd nd s = .OK ns s' INCR → MapValid map s → RegMapOk map rd (some id) →
    TrExpr s'.st_code map [] a ns nd rd (some id)
  | .Evar v, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨r, s1, i1, i2, h1, h2⟩ := bind_inv TR
    obtain ⟨hr, rfl⟩ := find_var_inv h1
    exact .Evar _ _ _ _ _ _ _ _ hr (.inr ⟨OK, by simp⟩) (add_move_charact h2)
  | .Eop op al, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .Eop _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF)
        (alloc_regs_target_ok al WF (regs_valid_nil _) h1)
        (regs_valid_nil _) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) OK (by simp)
  | .Eload chunk addr al, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .Eload _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF)
        (alloc_regs_target_ok al WF (regs_valid_nil _) h1)
        (regs_valid_nil _) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) OK (by simp)
  | .Econdition a b c, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨nfalse, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨ntrue, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .Econdition _ _ _ _ _ _ _ _ _ _ _
      (transl_condexpr_charact a h3 (map_valid_incr i13 WF) (regs_valid_nil _))
      (tr_expr_incr i4 (transl_expr_assign_charact id b h2 (map_valid_incr i1 WF) OK))
      (tr_expr_incr (stateIncr_trans i3 i4) (transl_expr_assign_charact id c h1 WF OK))
  | .Elet b c, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨r, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨nc, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    have FR := new_reg_fresh h1
    have RV := new_reg_valid h1
    refine .Elet _ _ _ _ _ _ _ _ _ _ (new_reg_not_in_map h1 WF)
      (transl_expr_charact b h3 (map_valid_incr i13 WF) (fresh_target_ok WF (regs_valid_nil _) FR)
        (regs_valid_nil _) (reg_valid_incr i3 RV))
      (tr_expr_incr i4 (transl_expr_assign_charact id c h2
        (add_letvar_valid (map_valid_incr i1 WF) RV) ?_))
    cases OK
    exact .somevar _ _ _ (by assumption)
  | .Eletvar n, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨r, s1, i1, i2, h1, h2⟩ := bind_inv TR
    obtain ⟨hr, rfl⟩ := find_letvar_inv h1
    exact .Eletvar _ _ _ _ _ _ _ _ hr (.inr ⟨OK, by simp⟩) (add_move_charact h2)
  | .Ebuiltin ef al, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .Ebuiltin _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF)
        (alloc_regs_target_ok al WF (regs_valid_nil _) h1)
        (regs_valid_nil _) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) OK (by simp)
  | .Eexternal eid sg al, map, rd, nd, s, ns, s', _, TR, WF, OK => by
    simp only [translExpr] at TR
    obtain ⟨rl, s1, i1, i2, h1, TR⟩ := bind_inv TR
    obtain ⟨no, s2, i3, i4, h2, h3⟩ := bind_inv TR
    have i13 := stateIncr_trans i1 i3
    exact .Eexternal _ _ _ _ _ _ _ _ _ _ _
      (transl_exprlist_charact al h3 (map_valid_incr i13 WF)
        (alloc_regs_target_ok al WF (regs_valid_nil _) h1)
        (regs_valid_nil _) (regs_valid_incr i3 (alloc_regs_valid al WF h1)))
      (instr_at_incr i4 (add_instr_at h2)) OK (by simp)

end RTLgen
end RiscV
end CC
