/-
  Correctness of register allocation, part 6 — the cases of
  `Allocproof.step_simulation` (`backend/Allocproof.v`) for `Inop`, `Iop`
  and `Iload`.

  On this (64-bit) configuration `Archi.splitlong = false`, so the block
  shapes that split 64-bit integers in two halves (`BSmakelong`, `BSlowlong`,
  `BShighlong`, `BSload2`, `BSload2_1`, `BSload2_2`) cannot occur.
-/
import CCLib.backend.AllocproofSimBasic
import CCLib.aarch64.OpLessdef

namespace CC
namespace Allocproof

open Op Allocation LTL RTLtyping Conventions1 Conventions Smallstep
open Allocation.Eqs (add remove)

section HELPERS
variable (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function)

/-- After executing a block, reaching the successor `s'` of `pc`: the
    simulation relation is re-established at `s'`. -/
theorem match_succ {tge : LTL.CGenv} {s : List RTL.Stackframe} {ts : List LTL.Stackframe}
    {f : RTL.Function} {tf : LTL.Function} {sp : Val} {pc s' : RTL.Node} {rs : RTL.Regset}
    {ls : Locset} {m m' : Mem} {an : PMap (Res Eqs)} {env : Regenv} {bsh : BlockShape}
    {eafter : Eqs}
    (STK : MatchStackframes abi regalloc tge s ts tf.fn_sig)
    (TF : Allocation.transfFunction abi regalloc f = .OK tf)
    (AN : analyze abi f env (pairCodes f tf) = some an)
    (hb : (pairCodes f tf).get pc = some bsh) (hsucc : s' ∈ successorsBlockShape bsh)
    (he : an.get pc = .OK eafter) (hsat : Satisf rs ls eafter) (hm : Mem.Extends m m')
    (WTF : WtFunction abi f env) (WTR : WtRegset env rs) :
    MatchStates abi regalloc tge (.State s f sp s' rs m) (.State ts tf sp s' ls m') := by
  obtain ⟨e', A, B⟩ := satisf_successors AN hb hsucc he hsat
  exact .intro s f sp s' rs m ts tf ls m' an e' env STK TF AN A B hm WTF WTR

end HELPERS

section PRESERVATION
variable (abi : AbiKind) (regalloc : RTL.Function → Res LTL.Function)
  {prog : RTL.Program} {tprog : LTL.Program}
  (TRANSF : Allocation.transfProgram abi regalloc prog = .OK tprog)
include TRANSF

omit TRANSF in
/-- `step_simulation`, case `Inop`. -/
theorem step_simulation_nop {s f sp pc rs m pc'}
    (hc : f.fn_code.get pc = some (.Inop pc')) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv (.State s f sp pc' rs m) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, _⟩ := invert_code WTF hc TR
  cases hexp with
  | nop mv _ k WF =>
  obtain ⟨ls1, X, Y⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF SAT
  exact ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb) (star_right X (.Lbranch _ _ _ _ _ _ _) rfl) rfl,
    match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he Y EXT WTF WTR⟩

/-- `step_simulation`, case `Iop`. -/
theorem step_simulation_op {s f sp pc rs m op args res pc' v}
    (hc : f.fn_code.get pc = some (.Iop op args res pc'))
    (hev : evalOperation prog.globalenv sp op (rs.getList args) m = some v) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv (.State s f sp pc' (rs.set res v) m) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, WTI⟩ := invert_code WTF hc TR
  have WTR' := wt_exec_Iop prog.globalenv WTI hev WTR
  cases hexp with
  | move src dst mv _ k WF =>
    have hv : v = rs.get src := by
      first | (cases hev; rfl) | (simp [evalOperation, Regmap.getList] at hev; exact hev.symm)
    subst hv
    obtain ⟨ls1, X, Y⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF SAT
    exact ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
        (star_right X (.Lbranch _ _ _ _ _ _ _) rfl) rfl,
      match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he
        (subst_reg_satisf Y) EXT WTF WTR'⟩
  | makelong _ _ _ _ _ _ _ hsl => simp [Archi.splitlong] at hsl
  | lowlong _ _ _ _ _ _ hsl => simp [Archi.splitlong] at hsl
  | highlong _ _ _ _ _ _ hsl => simp [Archi.splitlong] at hsl
  | op _ _ _ mv1 args' res' mv2 _ k WF1 WF2 =>
    simp only [transferAux] at htr
    obtain ⟨e1, h1, htr⟩ := obind_some htr
    obtain ⟨e2, h2, htr⟩ := obind_some htr
    obtain ⟨ls1, A1, B1⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF1 SAT
    obtain ⟨X, Y⟩ := transfer_use_def_satisf h2 B1
    obtain ⟨v', F, G⟩ := evalOperation_lessdef prog.globalenv sp op X EXT hev
    obtain ⟨ls2, A2, B2⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR' h1 WF2 (Y v v' G)
    refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
        (star_trans A1 (star_left (.Lop _ _ _ _ _ _ _ _ _ v' _ ?_ rfl)
          (star_right A2 (.Lbranch _ _ _ _ _ _ _) rfl) rfl) rfl) rfl,
      match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he B2 EXT WTF WTR'⟩
    rw [evalOperation_preserved prog.globalenv tprog.globalenv
      (symbols_preserved abi regalloc TRANSF)]
    exact F
  | op_dead _ _ _ mv _ k WF =>
    simp only [transferAux] at htr
    split at htr
    · next hu =>
      obtain ⟨ls1, X, Y⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF SAT
      exact ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
          (star_right X (.Lbranch _ _ _ _ _ _ _) rfl) rfl,
        match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he
          (reg_unconstrained_satisf hu Y) EXT WTF WTR'⟩
    · cases htr

/-- `step_simulation`, case `Iload`. -/
theorem step_simulation_load {s f sp pc rs m chunk addr args dst pc' a v}
    (hc : f.fn_code.get pc = some (.Iload chunk addr args dst pc'))
    (hea : evalAddressing prog.globalenv sp addr (rs.getList args) = some a)
    (hl : Mem.loadv chunk m a = some v) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv (.State s f sp pc' (rs.set dst v) m) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, WTI⟩ := invert_code WTF hc TR
  have WTR' := wt_exec_Iload WTI hl WTR
  cases hexp with
  | load _ _ _ _ mv1 args' dst' mv2 _ k WF1 WF2 =>
    simp only [transferAux] at htr
    obtain ⟨e1, h1, htr⟩ := obind_some htr
    obtain ⟨e2, h2, htr⟩ := obind_some htr
    obtain ⟨ls1, A1, B1⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF1 SAT
    obtain ⟨X, Y⟩ := transfer_use_def_satisf h2 B1
    obtain ⟨a', F, G⟩ := evalAddressing_lessdef prog.globalenv sp addr X hea
    obtain ⟨v', P, Q⟩ := Mem.loadv_extends EXT hl G
    obtain ⟨ls2, A2, B2⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR' h1 WF2 (Y v v' Q)
    refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
        (star_trans A1 (star_left (.Lload _ _ _ _ _ _ _ _ _ _ a' v' _ ?_ P rfl)
          (star_right A2 (.Lbranch _ _ _ _ _ _ _) rfl) rfl) rfl) rfl,
      match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he B2 EXT WTF WTR'⟩
    rw [evalAddressing_preserved prog.globalenv tprog.globalenv
      (symbols_preserved abi regalloc TRANSF)]
    exact F
  | load2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsl => simp [Archi.splitlong] at hsl
  | load2_1 _ _ _ _ _ _ _ _ _ _ _ hsl => simp [Archi.splitlong] at hsl
  | load2_2 _ _ _ _ _ _ _ _ _ _ _ _ hsl => simp [Archi.splitlong] at hsl
  | load_dead _ _ _ _ mv _ k WF =>
    simp only [transferAux] at htr
    split at htr
    · next hu =>
      obtain ⟨ls1, X, Y⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF SAT
      exact ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
          (star_right X (.Lbranch _ _ _ _ _ _ _) rfl) rfl,
        match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he
          (reg_unconstrained_satisf hu Y) EXT WTF WTR'⟩
    · cases htr

/-- `step_simulation`, case `Istore`. -/
theorem step_simulation_store {s f sp pc rs m chunk addr args src pc' a m1}
    (hc : f.fn_code.get pc = some (.Istore chunk addr args src pc'))
    (hea : evalAddressing prog.globalenv sp addr (rs.getList args) = some a)
    (hst : Mem.storev chunk m a (rs.get src) = some m1) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv (.State s f sp pc' rs m1) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, _⟩ := invert_code WTF hc TR
  cases hexp with
  | store _ _ _ _ mv args' src' _ k WF =>
    simp only [transferAux] at htr
    split at htr
    · next hcu =>
      obtain ⟨e1, h1, htr⟩ := obind_some htr
      obtain ⟨ls1, X, Y⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF SAT
      have LD := add_equations_lessdef h1 Y
      cases LD with
      | cons LD1 LD2 =>
      obtain ⟨a', F, G⟩ := evalAddressing_lessdef prog.globalenv sp addr LD2 hea
      obtain ⟨m'', P, Q⟩ := Mem.storev_extends EXT hst G LD1
      refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
          (star_trans X (star_two (.Lstore _ _ _ _ _ _ _ _ _ _ a' _ _ ?_ P rfl)
            (.Lbranch _ _ _ _ _ _ _) rfl) rfl) rfl,
        match_succ abi regalloc STK TF AN hb (by simp [successorsBlockShape]) he
          (can_undef_satisf hcu (add_equations_satisf h1 Y)) Q WTF WTR⟩
      rw [evalAddressing_preserved prog.globalenv tprog.globalenv
        (symbols_preserved abi regalloc TRANSF)]
      exact F
    · cases htr
  | store2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsl => simp [Archi.splitlong] at hsl

omit TRANSF in
/-- `step_simulation`, case `Icond`. -/
theorem step_simulation_cond {s f sp pc rs m cond args ifso ifnot b pc'}
    (hc : f.fn_code.get pc = some (.Icond cond args ifso ifnot))
    (hcond : evalCondition cond (rs.getList args) m = some b)
    (hpc : pc' = (if b then ifso else ifnot)) {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv (.State s f sp pc' rs m) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, _⟩ := invert_code WTF hc TR
  cases hexp with
  | cond _ _ mv args' _ _ k WF =>
    simp only [transferAux] at htr
    split at htr
    · next hcu =>
      obtain ⟨e1, h1, htr⟩ := obind_some htr
      obtain ⟨ls1, X, Y⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF SAT
      have LD := add_equations_lessdef h1 Y
      refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
          (star_right X (.Lcond _ _ _ _ _ _ _ _ _ b _ _ m' (evalCondition_lessdef LD EXT hcond)
            hpc rfl) rfl) rfl,
        match_succ abi regalloc STK TF AN hb ?_ he
          (can_undef_satisf hcu (add_equations_satisf h1 Y)) EXT WTF WTR⟩
      subst hpc; cases b <;> simp [successorsBlockShape]
    · cases htr

omit TRANSF in
/-- `step_simulation`, case `Ijumptable`. -/
theorem step_simulation_jumptable {s f sp pc rs m arg tbl n pc'}
    (hc : f.fn_code.get pc = some (.Ijumptable arg tbl))
    (harg : rs.get arg = .Vint n)
    (hnth : CminorSel.listNthZ tbl (Integers.Int.unsigned n) = some pc') {S1' : LTL.State}
    (hm : MatchStates abi regalloc tprog.globalenv (.State s f sp pc rs m) S1') :
    ∃ S2' : LTL.State, Smallstep.Plus (LTL.Step abi tprog.globalenv) S1' E0 S2' ∧
      MatchStates abi regalloc tprog.globalenv (.State s f sp pc' rs m) S2' := by
  cases hm with
  | intro _ _ _ _ _ _ ts tf ls m' an e env STK TF AN TR SAT EXT WTF WTR =>
  obtain ⟨eafter, bsh, bb, he, hb, hbb, hexp, htr, _⟩ := invert_code WTF hc TR
  cases hexp with
  | jumptable _ mv arg' _ k WF =>
    simp only [transferAux] at htr
    split at htr
    · next hcu =>
      obtain ⟨ls1, X, Y⟩ := exec_moves abi tprog.globalenv ts tf sp m' WTR htr WF SAT
      have LD := add_equation_lessdef Y
      simp only [selVal] at LD
      rw [harg] at LD
      have hls : ls1 (.R arg') = .Vint n := by
        generalize ls1 (.R arg') = w at LD
        cases LD; rfl
      refine ⟨_, plus_left (.start_block _ _ _ _ _ _ _ hbb)
          (star_right X (.Ljumptable _ _ _ _ _ _ _ _ n _ _ hls hnth rfl) rfl) rfl,
        match_succ abi regalloc STK TF AN hb (CleanupLabelsproof.listNthZ_mem hnth) he
          (can_undef_satisf hcu (add_equation_satisf Y)) EXT WTF WTR⟩
    · cases htr

end PRESERVATION

end Allocproof
end CC
