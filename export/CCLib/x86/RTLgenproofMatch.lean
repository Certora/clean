/-
  [x86-64 instance of `CCLib/backend/RTLgenproofMatch.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Correctness of RTL generation — port of `backend/RTLgenproof.v`, part 4:
  the measure over CminorSel states (`size_stmt`, `size_cont`,
  `measure_state`, `lt_state`, `lt_state_wf`), the simulation invariant
  (`tr_fun`, `tr_cont`, `match_stacks`, `match_states`) and its lemmas
  (`match_stacks_call_cont`, `tr_cont_call_cont`, `tr_find_label`).
-/
import CCLib.x86.RTLgenproofBuiltin

namespace CC
namespace X86
namespace RTLgen

open Op CminorSel

/-! ## Measure over CminorSel states -/

/-- `RTLgenproof.size_stmt` -/
def sizeStmt : CminorSel.Stmt → Nat
  | .Sskip => 0
  | .Sseq s1 s2 => sizeStmt s1 + sizeStmt s2 + 1
  | .Sifthenelse _ s1 s2 => sizeStmt s1 + sizeStmt s2 + 1
  | .Sloop s1 => sizeStmt s1 + 1
  | .Sblock s1 => sizeStmt s1 + 1
  | .Sexit _ => 0
  | .Slabel _ s1 => sizeStmt s1 + 1
  | _ => 1

/-- `RTLgenproof.size_cont` -/
def sizeCont : CminorSel.Cont → Nat
  | .Kseq s k1 => sizeStmt s + sizeCont k1 + 1
  | .Kblock k1 => sizeCont k1 + 1
  | _ => 0

/-- `RTLgenproof.measure_state` -/
def measureState : CminorSel.State → Nat × Nat
  | .State _ s k _ _ _ => (sizeStmt s + sizeCont k, sizeStmt s)
  | _ => (0, 0)

/-- `RTLgenproof.lt_state` -/
def LtState (S1 S2 : CminorSel.State) : Prop :=
  Prod.Lex (· < ·) (· < ·) (measureState S1) (measureState S2)

/-- `RTLgenproof.lt_state_intro` -/
theorem lt_state_intro {f1 : CminorSel.Function} {s1 : CminorSel.Stmt} {k1 : CminorSel.Cont} {sp1 : Val}
    {e1 : Cminor.Env} {m1 : Mem} {f2 : CminorSel.Function} {s2 : CminorSel.Stmt} {k2 : CminorSel.Cont}
    {sp2 : Val} {e2 : Cminor.Env} {m2 : Mem}
    (h : sizeStmt s1 + sizeCont k1 < sizeStmt s2 + sizeCont k2 ∨
      (sizeStmt s1 + sizeCont k1 = sizeStmt s2 + sizeCont k2 ∧ sizeStmt s1 < sizeStmt s2)) :
    LtState (.State f1 s1 k1 sp1 e1 m1) (.State f2 s2 k2 sp2 e2 m2) := by
  show Prod.Lex _ _ (_, _) (_, _)
  rcases h with h | ⟨h1, h2⟩
  · exact .left _ _ h
  · rw [h1]; exact .right _ h2

/-- `RTLgenproof.lt_state_wf` -/
theorem lt_state_wf : WellFounded LtState :=
  InvImage.wf measureState (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-! ## The simulation invariant -/

/-- `RTLgenproof.tr_fun` -/
inductive TrFun (tf : RTL.Function) (map : Mapping) (f : CminorSel.Function) (ngoto : Labelmap)
    (nret : RTL.Node) (rret : Option Reg) : Prop where
  | intro (nentry : RTL.Node) (r : Reg) :
      rret = retReg f.fn_sig r →
      TrStmt tf.fn_code map f.fn_body nentry nret [] ngoto nret rret →
      tf.fn_stacksize = f.fn_stackspace →
      TrFun tf map f ngoto nret rret

mutual
/-- `RTLgenproof.tr_cont` -/
inductive TrCont : RTL.Code → Mapping → CminorSel.Cont → RTL.Node → List RTL.Node → Labelmap → RTL.Node →
    Option Reg → List RTL.Stackframe → Prop where
  | Kseq (c map s k nd nexits ngoto nret rret cs n) :
      TrStmt c map s nd n nexits ngoto nret rret →
      TrCont c map k n nexits ngoto nret rret cs →
      TrCont c map (.Kseq s k) nd nexits ngoto nret rret cs
  | Kblock (c map k nd nexits ngoto nret rret cs) :
      TrCont c map k nd nexits ngoto nret rret cs →
      TrCont c map (.Kblock k) nd (nd :: nexits) ngoto nret rret cs
  | Kstop (c map ngoto nret rret cs) :
      c.get nret = some (.Ireturn rret) →
      MatchStacks .Kstop cs →
      TrCont c map .Kstop nret [] ngoto nret rret cs
  | Kcall (c map optid f sp e k ngoto nret rret cs) :
      c.get nret = some (.Ireturn rret) →
      MatchStacks (.Kcall optid f sp e k) cs →
      TrCont c map (.Kcall optid f sp e k) nret [] ngoto nret rret cs

/-- `RTLgenproof.match_stacks` -/
inductive MatchStacks : CminorSel.Cont → List RTL.Stackframe → Prop where
  | stop : MatchStacks .Kstop []
  | call (optid f sp e k r tf n rs cs map nexits ngoto nret rret) :
      MapWf map →
      TrFun tf map f ngoto nret rret →
      MatchEnv map e [] rs →
      RegMapOk map r optid →
      TrCont tf.fn_code map k n nexits ngoto nret rret cs →
      MatchStacks (.Kcall optid f sp e k) (.Stackframe r tf sp n rs :: cs)
end

/-- `RTLgenproof.match_states` -/
inductive MatchStates (moreLikely : Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool) :
    CminorSel.State → RTL.State → Prop where
  | state (f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret) :
      MapWf map →
      TrStmt tf.fn_code map s ns ncont nexits ngoto nret rret →
      TrFun tf map f ngoto nret rret →
      TrCont tf.fn_code map k ncont nexits ngoto nret rret cs →
      MatchEnv map e [] rs →
      Mem.Extends m tm →
      MatchStates moreLikely (.State f s k sp e m) (.State cs tf sp ns rs tm)
  | callstate (f args targs k m tm cs tf) :
      translFundef moreLikely f = .OK tf →
      MatchStacks k cs →
      Val.LessdefList args targs →
      Mem.Extends m tm →
      MatchStates moreLikely (.Callstate f args k m) (.Callstate cs tf targs tm)
  | returnstate (v tv k m tm cs) :
      MatchStacks k cs →
      Val.Lessdef v tv →
      Mem.Extends m tm →
      MatchStates moreLikely (.Returnstate v k m) (.Returnstate cs tv tm)

/-- `RTLgenproof.match_stacks_call_cont` -/
theorem match_stacks_call_cont {c : RTL.Code} {map : Mapping} {k : CminorSel.Cont} {ncont : RTL.Node}
    {nexits : List RTL.Node} {ngoto : Labelmap} {nret : RTL.Node} {rret : Option Reg}
    {cs : List RTL.Stackframe} (h : TrCont c map k ncont nexits ngoto nret rret cs) :
    MatchStacks (CminorSel.callCont k) cs ∧ c.get nret = some (.Ireturn rret) := by
  induction k generalizing ncont nexits with
  | Kstop => cases h with | Kstop _ _ _ _ _ _ h1 h2 => exact ⟨h2, h1⟩
  | Kseq s k ih => cases h with | Kseq _ _ _ _ _ _ _ _ _ _ _ _ h2 => exact ih h2
  | Kblock k ih => cases h with | Kblock _ _ _ _ _ _ _ _ _ h1 => exact ih h1
  | Kcall => cases h with | Kcall _ _ _ _ _ _ _ _ _ _ _ h1 h2 => exact ⟨h2, h1⟩

/-- `RTLgenproof.tr_cont_call_cont` -/
theorem tr_cont_call_cont {c : RTL.Code} {map : Mapping} {k : CminorSel.Cont} {ncont : RTL.Node}
    {nexits : List RTL.Node} {ngoto : Labelmap} {nret : RTL.Node} {rret : Option Reg}
    {cs : List RTL.Stackframe} (h : TrCont c map k ncont nexits ngoto nret rret cs) :
    TrCont c map (CminorSel.callCont k) nret [] ngoto nret rret cs := by
  induction k generalizing ncont nexits with
  | Kstop => cases h with | Kstop _ _ _ _ _ _ h1 h2 => exact .Kstop _ _ _ _ _ _ h1 h2
  | Kseq s k ih => cases h with | Kseq _ _ _ _ _ _ _ _ _ _ _ _ h2 => exact ih h2
  | Kblock k ih => cases h with | Kblock _ _ _ _ _ _ _ _ _ h1 => exact ih h1
  | Kcall => cases h with | Kcall _ _ _ _ _ _ _ _ _ _ _ h1 h2 => exact .Kcall _ _ _ _ _ _ _ _ _ _ _ h1 h2

/-- `RTLgenproof.tr_find_label` -/
theorem tr_find_label {c : RTL.Code} {map : Mapping} {lbl : Cminor.Label} {n : RTL.Node}
    {ngoto : Labelmap} {nret : RTL.Node} {rret : Option Reg} {s' : CminorSel.Stmt} {k' : CminorSel.Cont}
    {cs : List RTL.Stackframe} (hg : ngoto.get lbl = some n) :
    ∀ (s : CminorSel.Stmt) {k : CminorSel.Cont} {ns1 nd1 : RTL.Node} {nexits1 : List RTL.Node},
    CminorSel.findLabel lbl s k = some (s', k') →
    TrStmt c map s ns1 nd1 nexits1 ngoto nret rret →
    TrCont c map k nd1 nexits1 ngoto nret rret cs →
    ∃ ns2 nd2 nexits2, c.get n = some (.Inop ns2) ∧
      TrStmt c map s' ns2 nd2 nexits2 ngoto nret rret ∧
      TrCont c map k' nd2 nexits2 ngoto nret rret cs := by
  intro s
  induction s with
  | Sseq s1 s2 ih1 ih2 =>
    intro k ns1 nd1 nexits1 hf ht hk
    simp only [CminorSel.findLabel] at hf
    cases ht with
    | Sseq _ _ _ _ _ _ _ _ n0 h2 h1 =>
      split at hf
      · next sk hsk =>
        cases hf
        exact ih1 hsk h1 (.Kseq _ _ _ _ _ _ _ _ _ _ _ h2 hk)
      · exact ih2 hf h2 hk
  | Sifthenelse a s1 s2 ih1 ih2 =>
    intro k ns1 nd1 nexits1 hf ht hk
    simp only [CminorSel.findLabel] at hf
    cases ht with
    | Sifthenelse _ _ _ _ _ _ _ _ _ _ _ h1 h2 _ =>
      split at hf
      · next sk hsk =>
        cases hf
        exact ih1 hsk h1 hk
      · exact ih2 hf h2 hk
  | Sloop s ih =>
    intro k ns1 nd1 nexits1 hf ht hk
    simp only [CminorSel.findLabel] at hf
    cases ht with
    | Sloop _ _ _ _ _ _ _ nloop nend hb h1 h2 =>
      exact ih hf hb (.Kseq _ _ _ _ _ _ _ _ _ _ _ (.Sloop _ _ _ _ _ _ _ _ _ hb h2 h2) hk)
  | Sblock s ih =>
    intro k ns1 nd1 nexits1 hf ht hk
    simp only [CminorSel.findLabel] at hf
    cases ht with
    | Sblock _ _ _ _ _ _ _ hb => exact ih hf hb (.Kblock _ _ _ _ _ _ _ _ _ hk)
  | Slabel l s ih =>
    intro k ns1 nd1 nexits1 hf ht hk
    simp only [CminorSel.findLabel] at hf
    cases ht with
    | Slabel _ _ _ _ _ _ _ _ n0 hg0 hc hb =>
      split at hf
      · next he =>
        cases hf
        subst he
        rw [hg] at hg0
        cases hg0
        exact ⟨ns1, nd1, nexits1, hc, hb, hk⟩
      · exact ih hf hb hk
  | _ => intro k ns1 nd1 nexits1 hf; simp [CminorSel.findLabel] at hf

end RTLgen
end X86
end CC
