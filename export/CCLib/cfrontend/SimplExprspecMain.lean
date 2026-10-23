/-
  Correctness of the expression and statement translations of
  `CCLib.cfrontend.SimplExpr` with respect to the relational specification — the main
  theorems of `cfrontend/SimplExprspec.v`: `transl_meets_spec`,
  `transl_expr_meets_spec`, `transl_expression_meets_spec`,
  `transl_expr_stmt_meets_spec`, `transl_if_meets_spec`,
  `transl_stmt_meets_spec`, `transl_function_spec` and `transl_fundef_spec`.

  The induction of Rocq's `transl_meets_spec` is split into one lemma per
  expression form (`spec_Ebinop`, …), each assuming the property for the
  subexpressions, and a structural recursion that combines them.
-/
import CCLib.cfrontend.SimplExprspecCorrect

namespace CC
namespace SimplExpr

open Destination SetDestination

section CE

variable (ce : CompositeEnv)

theorem spec_Eval {v ty}  :
    ExprSpec ce (.Eval v ty) := by
  intro dst g sl a g' I H hd
  cases v <;> simp only [translExpr] at H <;> (try exact (error_inv H).elim) <;>
  · mret H
    refine ⟨[], fun le => ?_, contained_nil⟩
    cases dst
    · exact .tr_val_value _ _ _ _ _ rfl fun _ _ _ _ _ => by constructor
    · exact .tr_val_effect ..
    · exact .tr_val_set _ _ _ _ _ _ _ rfl fun _ _ _ _ _ => by constructor

theorem spec_Evar {x ty}  :
    ExprSpec ce (.Evar x ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr] at H
  mret H
  exact ⟨[], fun le => .tr_var .., contained_nil⟩

theorem spec_Esizeof {ty' ty}  :
    ExprSpec ce (.Esizeof ty' ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr] at H
  mret H
  exact ⟨[], fun le => .tr_sizeof .., contained_nil⟩

theorem spec_Ealignof {ty' ty}  :
    ExprSpec ce (.Ealignof ty' ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr] at H
  mret H
  exact ⟨[], fun le => .tr_alignof .., contained_nil⟩

theorem spec_Ederef {r ty} (ih_r : ExprSpec ce r) :
    ExprSpec ce (.Ederef r ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  mret H
  obtain ⟨tmp, A, B⟩ := ih_r _ _ _ _ _ _ E1 trivial
  refine ⟨tmp, fun le => tr_expr_add_dest ce (.tr_deref _ _ _ _ _ _ _ (A le)), ?_⟩
  all_goals side_tac

theorem spec_Efield {r f ty} (ih_r : ExprSpec ce r) :
    ExprSpec ce (.Efield r f ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  mret H
  obtain ⟨tmp, A, B⟩ := ih_r _ _ _ _ _ _ E1 trivial
  refine ⟨tmp, fun le => tr_expr_add_dest ce (.tr_field _ _ _ _ _ _ _ _ (A le)), ?_⟩
  all_goals side_tac

theorem spec_Eaddrof {r ty} (ih_r : ExprSpec ce r) :
    ExprSpec ce (.Eaddrof r ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  mret H
  obtain ⟨tmp, A, B⟩ := ih_r _ _ _ _ _ _ E1 trivial
  refine ⟨tmp, fun le => tr_expr_add_dest ce (.tr_addrof _ _ _ _ _ _ _ (A le)), ?_⟩
  all_goals side_tac

theorem spec_Eunop {op r ty} (ih_r : ExprSpec ce r) :
    ExprSpec ce (.Eunop op r ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  mret H
  obtain ⟨tmp, A, B⟩ := ih_r _ _ _ _ _ _ E1 trivial
  refine ⟨tmp, fun le => tr_expr_add_dest ce (.tr_unop _ _ _ _ _ _ _ _ (A le)), ?_⟩
  all_goals side_tac

theorem spec_Evalof {l ty} (ih_l : ExprSpec ce l) :
    ExprSpec ce (.Evalof l ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  minv2 H sl2 a2 E2
  mret H
  obtain ⟨tmp1, A, B⟩ := ih_l _ _ _ _ _ _ E1 trivial
  obtain ⟨tmp2, C, D⟩ := transl_valof_meets_spec ce E2
  refine ⟨tmp1 ++ tmp2, fun le => tr_expr_add_dest ce
    (tr_sl_eq ce (.tr_valof _ _ _ _ _ _ _ _ _ _ _ (A le) C ?_ ?_ ?_)
      (by simp)), ?_⟩
  all_goals side_tac

theorem spec_Ebinop {op r1 r2 ty} (ih_r1 : ExprSpec ce r1) (ih_r2 : ExprSpec ce r2) :
    ExprSpec ce (.Ebinop op r1 r2 ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  minv2 H sl2 a2 E2
  mret H
  obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
  obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
  refine ⟨tmp1 ++ tmp2, fun le => tr_expr_add_dest ce
    (tr_sl_eq ce (.tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le) ?_ ?_
      ?_) (by simp)), ?_⟩
  all_goals side_tac

theorem spec_Ecast {r1 ty} (ih_r1 : ExprSpec ce r1) :
    ExprSpec ce (.Ecast r1 ty) := by
  intro dst g sl a g' I H hd
  cases dst
  · simp only [translExpr, Mon.bind_eq] at H
    minv2 H sl1 a1 E1
    mret H
    obtain ⟨tmp, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    refine ⟨tmp, fun le => tr_expr_add_dest ce (.tr_cast_val _ _ _ _ _ _ _ (A le)), ?_⟩
    all_goals side_tac
  · simp only [translExpr] at H
    obtain ⟨tmp, A, B⟩ := ih_r1 _ _ _ _ _ _ H trivial
    exact ⟨tmp, fun le => .tr_cast_effects _ _ _ _ _ _ _ (A le), B⟩
  · simp only [translExpr, Mon.bind_eq] at H
    minv2 H sl1 a1 E1
    mret H
    obtain ⟨tmp, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    refine ⟨tmp, fun le => tr_expr_add_dest ce (.tr_cast_val _ _ _ _ _ _ _ (A le)), ?_⟩
    all_goals side_tac

theorem spec_Eseqand {r1 r2 ty} (ih_r1 : ExprSpec ce r1) (ih_r2 : ExprSpec ce r2) :
    ExprSpec ce (.Eseqand r1 r2 ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 a1 E1
    minv H t Et
    minv2 H sl2 a2 E2
    mret H
    have Wt := gensym_within Et
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 (destBelow_set_base Wt)
    refine ⟨t :: (tmp1 ++ tmp2), fun le => .tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le)
      ?_ ?_ ?_ ?_, ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    refine ⟨tmp1 ++ tmp2, fun le => .tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le)
      ?_ ?_ ?_, ?_⟩
    all_goals side_tac
  · rename_i sd
    minv2 H sl1 a1 E1
    minv H t Et
    minv2 H sl2 a2 E2
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    have G := temp_for_sd_charact hd Et (by pos_omega)
    have UC := temp_for_sd_contained G
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 (dest_for_set_cons_below G)
    refine ⟨usedTempForSd ty t sd ++ (tmp1 ++ tmp2), fun le => .tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (A le) (C le) (temp_for_sd_disj G B D) ?_ (incl_sd_cons G ?_) (temp_for_sd_in G),
      ?_⟩
    all_goals side_tac

theorem spec_Eseqor {r1 r2 ty} (ih_r1 : ExprSpec ce r1) (ih_r2 : ExprSpec ce r2) :
    ExprSpec ce (.Eseqor r1 r2 ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 a1 E1
    minv H t Et
    minv2 H sl2 a2 E2
    mret H
    have Wt := gensym_within Et
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 (destBelow_set_base Wt)
    refine ⟨t :: (tmp1 ++ tmp2), fun le => .tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le)
      ?_ ?_ ?_ ?_, ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    refine ⟨tmp1 ++ tmp2, fun le => .tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le)
      ?_ ?_ ?_, ?_⟩
    all_goals side_tac
  · rename_i sd
    minv2 H sl1 a1 E1
    minv H t Et
    minv2 H sl2 a2 E2
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    have G := temp_for_sd_charact hd Et (by pos_omega)
    have UC := temp_for_sd_contained G
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 (dest_for_set_cons_below G)
    refine ⟨usedTempForSd ty t sd ++ (tmp1 ++ tmp2), fun le => .tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (A le) (C le) (temp_for_sd_disj G B D) ?_ (incl_sd_cons G ?_) (temp_for_sd_in G),
      ?_⟩
    all_goals side_tac

theorem spec_Econdition {r1 r2 r3 ty} (ih_r1 : ExprSpec ce r1) (ih_r2 : ExprSpec ce r2) (ih_r3 : ExprSpec ce r3) :
    ExprSpec ce (.Econdition r1 r2 r3 ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 a1 E1
    minv H t Et
    minv2 H sl2 a2 E2
    minv2 H sl3 a3 E3
    mret H
    have Wt := gensym_within Et
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 (destBelow_set_base Wt)
    obtain ⟨tmp3, E, F⟩ := ih_r3 _ _ _ _ _ _ E3
      (destBelow_le (destBelow_set_base Wt) (by pos_omega))
    refine ⟨t :: (tmp1 ++ (tmp2 ++ tmp3)), fun le => .tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (A le) (C le) (E le) ?_ ?_ ?_ ?_ ?_
      ?_, ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    minv2 H sl3 a3 E3
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    obtain ⟨tmp3, E, F⟩ := ih_r3 _ _ _ _ _ _ E3 trivial
    refine ⟨tmp1 ++ (tmp2 ++ tmp3), fun le => .tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (A le) (C le) (E le) ?_ ?_ ?_ ?_ ?_,
      ?_⟩
    all_goals side_tac
  · rename_i sd
    minv2 H sl1 a1 E1
    minv H t Et
    minv2 H sl2 a2 E2
    minv2 H sl3 a3 E3
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    have G := temp_for_sd_charact hd Et (by pos_omega)
    have UC := temp_for_sd_contained G
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 (dest_for_set_cons_below G)
    obtain ⟨tmp3, E, F⟩ := ih_r3 _ _ _ _ _ _ E3
      (destBelow_le (dest_for_set_cons_below G) (by pos_omega))
    refine ⟨usedTempForSd ty t sd ++ (tmp1 ++ (tmp2 ++ tmp3)), fun le =>
      .tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (A le) (C le) (E le) (temp_for_sd_disj G B D)
      (temp_for_sd_disj G B (contained_widen F (by pos_omega) (Mon.ple_refl _)))
      ?_ (incl_sd_cons G ?_) (incl_sd_cons G ?_) (temp_for_sd_in G), ?_⟩
    all_goals side_tac

theorem spec_Eassign {l1 r2 ty} (ih_l1 : ExprSpec ce l1) (ih_r2 : ExprSpec ce r2) :
    ExprSpec ce (.Eassign l1 r2 ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    minv H bf Ebf
    minv H t Et
    mret H
    have Wt := gensym_within Et
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    refine ⟨t :: (tmp1 ++ tmp2), fun le => tr_sl_eq ce
      (.tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le) ?_ ?_
        ?_ ?_ ?_ ?_ rfl rfl TB) (by simp),
      ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    minv H bf Ebf
    mret H
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    refine ⟨tmp1 ++ tmp2, fun le => .tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le)
      ?_ ?_ ?_ TB, ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    minv H bf Ebf
    minv H t Et
    mret H
    have Wt := gensym_within Et
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    refine ⟨t :: (tmp1 ++ tmp2), fun le => tr_sl_eq ce
      (.tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le) ?_ ?_
        ?_ ?_ ?_ ?_ rfl rfl TB) (by simp),
      ?_⟩
    all_goals side_tac

theorem spec_Eassignop {op l1 r2 tyres ty} (ih_l1 : ExprSpec ce l1) (ih_r2 : ExprSpec ce r2) :
    ExprSpec ce (.Eassignop op l1 r2 tyres ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    minv2 H sl3 a3 E3
    minv H bf Ebf
    minv H t Et
    mret H
    have Wt := gensym_within Et
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    obtain ⟨tmp3, R, F⟩ := transl_valof_meets_spec ce E3
    refine ⟨t :: (tmp1 ++ (tmp2 ++ tmp3)), fun le => tr_sl_eq ce
      (.tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le) R
        ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ rfl TB) (by simp),
      ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    minv2 H sl3 a3 E3
    minv H bf Ebf
    mret H
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    obtain ⟨tmp3, R, F⟩ := transl_valof_meets_spec ce E3
    refine ⟨tmp1 ++ (tmp2 ++ tmp3), fun le => tr_sl_eq ce
      (.tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le) rfl R
        ?_ ?_ ?_ ?_ ?_ ?_ TB)
      (by simp), ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 a2 E2
    minv2 H sl3 a3 E3
    minv H bf Ebf
    minv H t Et
    mret H
    have Wt := gensym_within Et
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2 trivial
    obtain ⟨tmp3, R, F⟩ := transl_valof_meets_spec ce E3
    refine ⟨t :: (tmp1 ++ (tmp2 ++ tmp3)), fun le => tr_sl_eq ce
      (.tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le) R
        ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ rfl TB) (by simp),
      ?_⟩
    all_goals side_tac

theorem spec_Epostincr {id l1 ty} (ih_l1 : ExprSpec ce l1) :
    ExprSpec ce (.Epostincr id l1 ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 a1 E1
    minv H bf Ebf
    minv H t Et
    mret H
    have Wt := gensym_within Et
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    refine ⟨t :: tmp1, fun le => tr_sl_eq ce
      (.tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ (A le) ?_ ?_ ?_
        rfl TB) (by simp), ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv H bf Ebf
    minv2 H sl2 a2 E2
    mret H
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, R, D⟩ := transl_valof_meets_spec ce E2
    refine ⟨tmp1 ++ tmp2, fun le => tr_sl_eq ce
      (.tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A le) R rfl ?_ ?_
        ?_ TB) (by simp), ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv H bf Ebf
    minv H t Et
    mret H
    have Wt := gensym_within Et
    have TB := is_bitfield_access_meets_spec ce Ebf
    obtain ⟨tmp1, A, B⟩ := ih_l1 _ _ _ _ _ _ E1 trivial
    refine ⟨t :: tmp1, fun le => tr_sl_eq ce
      (.tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ (A le) ?_ ?_ ?_
        rfl TB) (by simp), ?_⟩
    all_goals side_tac

theorem spec_Ecomma {r1 r2 ty} (ih_r1 : ExprSpec ce r1) (ih_r2 : ExprSpec ce r2) :
    ExprSpec ce (.Ecomma r1 r2 ty) := by
  intro dst g sl a g' I H hd
  simp only [translExpr, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  minv2 H sl2 a2 E2
  mret H
  obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
  obtain ⟨tmp2, C, D⟩ := ih_r2 _ _ _ _ _ _ E2
    (destBelow_le hd (by pos_omega))
  have DJ : listDisjoint tmp1 (addDest dst tmp2) := by
    cases dst
    · exact contained_disjoint' B D (by pos_omega)
    · exact contained_disjoint' B D (by pos_omega)
    · exact listDisjoint_cons_r (contained_disjoint' B D (by pos_omega)) (sd_temp_notin hd B)
  refine ⟨tmp1 ++ tmp2, fun le => .tr_comma _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le) DJ ?_ ?_,
    ?_⟩
  · cases dst <;> incl_tac
  · cases dst <;> incl_tac
  · side_tac

theorem spec_Ecall {r1 rl2 ty} (ih_r1 : ExprSpec ce r1) (ih_rl2 : ExprlistSpec ce rl2) :
    ExprSpec ce (.Ecall r1 rl2 ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 a1 E1
    minv2 H sl2 al2 E2
    minv H t Et
    mret H
    have Wt := gensym_within Et
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_rl2 _ _ _ _ _ E2
    refine ⟨t :: (tmp1 ++ tmp2), fun le => tr_sl_eq ce
      (.tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ (by intro h; cases h) (A le) (C le) ?_
        ?_ ?_ ?_) (by simp), ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 al2 E2
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_rl2 _ _ _ _ _ E2
    refine ⟨tmp1 ++ tmp2, fun le => .tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ (A le) (C le)
      ?_ ?_ ?_, ?_⟩
    all_goals side_tac
  · minv2 H sl1 a1 E1
    minv2 H sl2 al2 E2
    minv H t Et
    mret H
    have Wt := gensym_within Et
    obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
    obtain ⟨tmp2, C, D⟩ := ih_rl2 _ _ _ _ _ E2
    refine ⟨t :: (tmp1 ++ tmp2), fun le => tr_sl_eq ce
      (.tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ (by intro h; cases h) (A le) (C le) ?_
        ?_ ?_ ?_) (by simp), ?_⟩
    all_goals side_tac

theorem spec_Ebuiltin {ef tyargs rl ty} (ih_rl : ExprlistSpec ce rl) :
    ExprSpec ce (.Ebuiltin ef tyargs rl ty) := by
  intro dst g sl a g' I H hd
  cases dst <;> simp only [translExpr, Mon.bind_eq] at H
  · minv2 H sl1 al1 E1
    minv H t Et
    mret H
    have Wt := gensym_within Et
    obtain ⟨tmp1, A, B⟩ := ih_rl _ _ _ _ _ E1
    refine ⟨t :: tmp1, fun le => tr_sl_eq ce
      (.tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ (by intro h; cases h) (A le) ?_
        ?_) (by simp), ?_⟩
    all_goals side_tac
  · minv2 H sl1 al1 E1
    mret H
    obtain ⟨tmp1, A, B⟩ := ih_rl _ _ _ _ _ E1
    refine ⟨tmp1, fun le => .tr_builtin_effects _ _ _ _ _ _ _ _ _ _ (A le) ?_, B⟩
    all_goals side_tac
  · minv2 H sl1 al1 E1
    minv H t Et
    mret H
    have Wt := gensym_within Et
    obtain ⟨tmp1, A, B⟩ := ih_rl _ _ _ _ _ E1
    refine ⟨t :: tmp1, fun le => tr_sl_eq ce
      (.tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ (by intro h; cases h) (A le) ?_
        ?_) (by simp), ?_⟩
    all_goals side_tac

theorem spec_Enil : ExprlistSpec ce .Enil := by
  intro g sl al g' I H
  simp only [translExprlist] at H
  mret H
  exact ⟨[], fun le => .tr_nil .., contained_nil⟩

theorem spec_Econs {r1 rl2} (ih_r1 : ExprSpec ce r1) (ih_rl2 : ExprlistSpec ce rl2) :
    ExprlistSpec ce (.Econs r1 rl2) := by
  intro g sl al g' I H
  simp only [translExprlist, Mon.bind_eq] at H
  minv2 H sl1 a1 E1
  minv2 H sl2 al2 E2
  mret H
  obtain ⟨tmp1, A, B⟩ := ih_r1 _ _ _ _ _ _ E1 trivial
  obtain ⟨tmp2, C, D⟩ := ih_rl2 _ _ _ _ _ E2
  refine ⟨tmp1 ++ tmp2, fun le => .tr_cons _ _ _ _ _ _ _ _ _ _ (A le) (C le) ?_
    ?_ ?_, ?_⟩
  all_goals side_tac

mutual
/-- `SimplExprspec.transl_meets_spec`, expressions. -/
theorem transl_meets_spec_expr : ∀ r, ExprSpec ce r
  | .Eval _ _ => spec_Eval ce
  | .Evar _ _ => spec_Evar ce
  | .Esizeof _ _ => spec_Esizeof ce
  | .Ealignof _ _ => spec_Ealignof ce
  | .Ederef r _ => spec_Ederef ce (transl_meets_spec_expr r)
  | .Efield r _ _ => spec_Efield ce (transl_meets_spec_expr r)
  | .Eaddrof r _ => spec_Eaddrof ce (transl_meets_spec_expr r)
  | .Eunop _ r _ => spec_Eunop ce (transl_meets_spec_expr r)
  | .Evalof l _ => spec_Evalof ce (transl_meets_spec_expr l)
  | .Ebinop _ r1 r2 _ => spec_Ebinop ce (transl_meets_spec_expr r1) (transl_meets_spec_expr r2)
  | .Ecast r1 _ => spec_Ecast ce (transl_meets_spec_expr r1)
  | .Eseqand r1 r2 _ => spec_Eseqand ce (transl_meets_spec_expr r1) (transl_meets_spec_expr r2)
  | .Eseqor r1 r2 _ => spec_Eseqor ce (transl_meets_spec_expr r1) (transl_meets_spec_expr r2)
  | .Econdition r1 r2 r3 _ =>
    spec_Econdition ce (transl_meets_spec_expr r1) (transl_meets_spec_expr r2)
      (transl_meets_spec_expr r3)
  | .Eassign l1 r2 _ => spec_Eassign ce (transl_meets_spec_expr l1) (transl_meets_spec_expr r2)
  | .Eassignop _ l1 r2 _ _ =>
    spec_Eassignop ce (transl_meets_spec_expr l1) (transl_meets_spec_expr r2)
  | .Epostincr _ l1 _ => spec_Epostincr ce (transl_meets_spec_expr l1)
  | .Ecomma r1 r2 _ => spec_Ecomma ce (transl_meets_spec_expr r1) (transl_meets_spec_expr r2)
  | .Ecall r1 rl2 _ => spec_Ecall ce (transl_meets_spec_expr r1) (transl_meets_spec_exprlist rl2)
  | .Ebuiltin _ _ rl _ => spec_Ebuiltin ce (transl_meets_spec_exprlist rl)
  | .Eloc _ _ _ _ => fun _ _ _ _ _ _ H _ => by
    simp only [translExpr] at H; exact (error_inv H).elim
  | .Eparen _ _ _ => fun _ _ _ _ _ _ H _ => by
    simp only [translExpr] at H; exact (error_inv H).elim

/-- `SimplExprspec.transl_meets_spec`, expression lists. -/
theorem transl_meets_spec_exprlist : ∀ rl, ExprlistSpec ce rl
  | .Enil => spec_Enil ce
  | .Econs r1 rl2 => spec_Econs ce (transl_meets_spec_expr r1) (transl_meets_spec_exprlist rl2)
end

/-- `SimplExprspec.transl_meets_spec`: if `transl_expr` succeeds, its result
    satisfies `tr_expr` with temporaries generated during the call; likewise
    for `transl_exprlist`. -/
theorem transl_meets_spec :
    (∀ r dst g sl a g' I, translExpr ce dst r g = .Res (sl, a) g' I → destBelow dst g →
      ∃ tmps, (∀ le, TrExpr ce le dst r sl a (addDest dst tmps)) ∧ contained tmps g g') ∧
    (∀ rl g sl al g' I, translExprlist ce rl g = .Res (sl, al) g' I →
      ∃ tmps, (∀ le, TrExprlist ce le rl sl al tmps) ∧ contained tmps g g') :=
  ⟨transl_meets_spec_expr ce, transl_meets_spec_exprlist ce⟩

/-- `SimplExprspec.transl_expr_meets_spec` -/
theorem transl_expr_meets_spec {r dst g sl a g' I}
    (h : translExpr ce dst r g = .Res (sl, a) g' I) (hd : destBelow dst g) :
    ∃ tmps, ∀ ge e le m, TrTop ce ge e le m dst r sl a tmps := by
  obtain ⟨tmps, A, -⟩ := transl_meets_spec_expr ce r dst g sl a g' I h hd
  exact ⟨addDest dst tmps, fun _ _ le _ => .tr_top_base _ _ _ _ _ (A le)⟩

/-- `SimplExprspec.transl_expression_meets_spec` -/
theorem transl_expression_meets_spec {r g s a g' I}
    (h : translExpression ce r g = .Res (s, a) g' I) : TrExpression ce r s a := by
  simp only [translExpression, Mon.bind_eq] at h
  minv2 h sl a0 E
  mret h
  obtain ⟨tmps, A⟩ := transl_expr_meets_spec ce E trivial
  exact .tr_expression_intro _ _ _ _ A

/-- `SimplExprspec.transl_expr_stmt_meets_spec` -/
theorem transl_expr_stmt_meets_spec {r g s g' I}
    (h : translExprStmt ce r g = .Res s g' I) : TrExprStmt ce r s := by
  simp only [translExprStmt, Mon.bind_eq] at h
  minv2 h sl a0 E
  mret h
  obtain ⟨tmps, A⟩ := transl_expr_meets_spec ce E trivial
  exact .tr_expr_stmt_intro _ _ _ _ A

/-- `SimplExprspec.transl_if_meets_spec` -/
theorem transl_if_meets_spec {r s1 s2 g s g' I}
    (h : translIf ce r s1 s2 g = .Res s g' I) : TrIf ce r s1 s2 s := by
  simp only [translIf, Mon.bind_eq] at h
  minv2 h sl a0 E
  mret h
  obtain ⟨tmps, A⟩ := transl_expr_meets_spec ce E trivial
  exact .tr_if_intro _ _ _ _ _ _ A

theorem isSskip_true {s : Csyntax.Stmt} (h : isSskip s = true) : s = .Sskip := by
  cases s <;> first | rfl | cases h

theorem isSskip_false {s : Csyntax.Stmt} (h : isSskip s = false) : s ≠ .Sskip := by
  intro e; subst e; cases h

mutual
/-- `SimplExprspec.transl_stmt_meets_spec` -/
theorem transl_stmt_meets_spec : ∀ (s : Csyntax.Stmt) (g : Generator) (ts : Stmt) (g' : Generator)
    (I : g.gen_next ≤ g'.gen_next), translStmt ce s g = .Res ts g' I → TrStmt ce s ts
  | .Sskip, _, _, _, _, H => by
    simp only [translStmt] at H; mret H; exact .tr_skip
  | .Sdo e, _, _, _, _, H => by
    simp only [translStmt] at H; exact .tr_do _ _ (transl_expr_stmt_meets_spec ce H)
  | .Ssequence s1 s2, _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv H ts1 E1
    minv H ts2 E2
    mret H
    exact .tr_seq _ _ _ _ (transl_stmt_meets_spec s1 _ _ _ _ E1) (transl_stmt_meets_spec s2 _ _ _ _ E2)
  | .Sifthenelse e s1 s2, _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv H ts1 E1
    minv H ts2 E2
    minv2 H s' a E3
    have T := transl_expression_meets_spec ce E3
    cases h1 : isSskip s1 <;> cases h2 : isSskip s2 <;> simp only [h1, h2] at H <;> mret H
    · exact .tr_ifthenelse _ _ _ _ _ _ _ T (transl_stmt_meets_spec s1 _ _ _ _ E1)
        (transl_stmt_meets_spec s2 _ _ _ _ E2)
    · exact .tr_ifthenelse _ _ _ _ _ _ _ T (transl_stmt_meets_spec s1 _ _ _ _ E1)
        (transl_stmt_meets_spec s2 _ _ _ _ E2)
    · exact .tr_ifthenelse _ _ _ _ _ _ _ T (transl_stmt_meets_spec s1 _ _ _ _ E1)
        (transl_stmt_meets_spec s2 _ _ _ _ E2)
    · obtain rfl := isSskip_true h1
      obtain rfl := isSskip_true h2
      exact .tr_ifthenelse_empty _ _ _ T
  | .Swhile e s1, _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv H s' E1
    minv H ts1 E2
    mret H
    exact .tr_while _ _ _ _ (transl_if_meets_spec ce E1) (transl_stmt_meets_spec s1 _ _ _ _ E2)
  | .Sdowhile e s1, _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv H s' E1
    minv H ts1 E2
    mret H
    exact .tr_dowhile _ _ _ _ (transl_if_meets_spec ce E1) (transl_stmt_meets_spec s1 _ _ _ _ E2)
  | .Sfor s1 e2 s3 s4, _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv H ts1 E1
    minv H s' E2
    minv H ts3 E3
    minv H ts4 E4
    cases h1 : isSskip s1 <;> simp only [h1] at H <;> mret H
    · exact .tr_for_2 _ _ _ _ _ _ _ _ (transl_if_meets_spec ce E2) (isSskip_false h1)
        (transl_stmt_meets_spec s1 _ _ _ _ E1) (transl_stmt_meets_spec s3 _ _ _ _ E3)
        (transl_stmt_meets_spec s4 _ _ _ _ E4)
    · obtain rfl := isSskip_true h1
      exact .tr_for_1 _ _ _ _ _ _ (transl_if_meets_spec ce E2)
        (transl_stmt_meets_spec s3 _ _ _ _ E3) (transl_stmt_meets_spec s4 _ _ _ _ E4)
  | .Sbreak, _, _, _, _, H => by
    simp only [translStmt] at H; mret H; exact .tr_break
  | .Scontinue, _, _, _, _, H => by
    simp only [translStmt] at H; mret H; exact .tr_continue
  | .Sreturn none, _, _, _, _, H => by
    simp only [translStmt] at H; mret H; exact .tr_return_none
  | .Sreturn (some e), _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv2 H s' a E1
    mret H
    exact .tr_return_some _ _ _ (transl_expression_meets_spec ce E1)
  | .Sswitch e ls, _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv2 H s' a E1
    minv H tls E2
    mret H
    exact .tr_switch _ _ _ _ _ (transl_expression_meets_spec ce E1)
      (transl_lblstmt_meets_spec ls _ _ _ _ E2)
  | .Slabel lbl s1, _, _, _, _, H => by
    simp only [translStmt, Mon.bind_eq] at H
    minv H ts1 E1
    mret H
    exact .tr_label _ _ _ (transl_stmt_meets_spec s1 _ _ _ _ E1)
  | .Sgoto lbl, _, _, _, _, H => by
    simp only [translStmt] at H; mret H; exact .tr_goto _

/-- `SimplExprspec.transl_lblstmt_meets_spec` -/
theorem transl_lblstmt_meets_spec : ∀ (ls : Csyntax.LStmts) (g : Generator) (tls : LStmts)
    (g' : Generator) (I : g.gen_next ≤ g'.gen_next),
    translLblstmt ce ls g = .Res tls g' I → TrLblstmts ce ls tls
  | .LSnil, _, _, _, _, H => by
    simp only [translLblstmt] at H; mret H; exact .tr_ls_nil
  | .LScons c s ls1, _, _, _, _, H => by
    simp only [translLblstmt, Mon.bind_eq] at H
    minv H ts E1
    minv H tls1 E2
    mret H
    exact .tr_ls_cons _ _ _ _ _ (transl_stmt_meets_spec s _ _ _ _ E1)
      (transl_lblstmt_meets_spec ls1 _ _ _ _ E2)
end

/-- `SimplExprspec.transl_function_spec` -/
theorem transl_function_spec {firstUnused f tf} (h : translFunction ce firstUnused f = .OK tf) :
    TrFunction ce f tf := by
  unfold translFunction at h
  cases hr : translStmt ce f.fn_body (initialGenerator firstUnused) with
  | Err msg => simp only [hr] at h; cases h
  | Res tbody g' I =>
    simp only [hr] at h
    cases h
    exact .tr_function_intro _ _ (transl_stmt_meets_spec ce _ _ _ _ _ hr) rfl rfl rfl rfl

end CE

/-- `SimplExprspec.transl_fundef_spec` -/
theorem transl_fundef_spec {p : Csyntax.Program} {firstUnused fd tfd}
    (h : translFundef p.prog_comp_env firstUnused fd = .OK tfd) : TrFundef p fd tfd := by
  unfold translFundef at h
  cases fd with
  | Internal f =>
    cases hf : translFunction p.prog_comp_env firstUnused f with
    | OK tf => simp only [hf] at h; cases h; exact .tr_internal _ _ (transl_function_spec _ hf)
    | Error msg => simp only [hf] at h; cases h
  | External ef targs tres cc => cases h; exact .tr_external ..

end SimplExpr
end CC
