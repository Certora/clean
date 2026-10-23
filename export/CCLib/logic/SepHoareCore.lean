/-
  First part of the separation-logic Hoare triples (split from `CCLib.logic.SepHoare`): the triple, structural rules, `switch`, loops, `goto`/labels, the frame rule and reads through a fragment.
-/
import CCLib.logic.SepLogic
import CCLib.logic.Hoare
import CCLib.logic.HoareArray
import CCLib.common.MemoryTheory

namespace CC
namespace Sep

open HProp

/-- An assertion: constrains the local environment, the temporaries, and the heap
    fragment.  `HProp`-valued, so `∗` and the BI laws come straight from
    `CCLib/logic/SepLogic.lean`. -/
abbrev Assn := Env → TempEnv → HProp

/-- The memory an outcome ends in. -/
def outMem : Outcome → Mem
  | .Normal _ _ m => m
  | .Break _ _ m => m
  | .Continue _ _ m => m
  | .Return _ m => m
  | .Goto _ _ _ m => m

/-- Postconditions, one per exit kind.  `ret` is heap-only: a returning function
    has no local environment left to describe. -/
structure ExitConds where
  normal : Assn
  brk : Assn
  cont : Assn
  ret : Val → HProp
  /-- **Wave E**: one assertion per label the statement may jump to.  The field
      carries a **default**, so every `ExitConds` literal written before Wave E
      still elaborates unchanged — 21 of them across this file, `Funspec` and
      the example proofs.  That is what kept the
      `Outcome` extension to 14 match arms instead of a file-wide rewrite.
      (`Sep.Assn.no` is defined just below, so the default is spelled out.) -/
  goto : Ident → Assn := fun _ _ _ _ => False

def ExitConds.holds (R : ExitConds) : Outcome → Heap → Prop
  | .Normal e le _, hp => R.normal e le hp
  | .Break e le _, hp => R.brk e le hp
  | .Continue e le _, hp => R.cont e le hp
  | .Return v _, hp => R.ret v hp
  | .Goto lbl e le _, hp => R.goto lbl e le hp

/-- The unsatisfiable assertion, for exits a statement cannot take. -/
def Assn.no : Assn := fun _ _ _ => False

/-- Only-normal-exit postconditions. -/
def ExitConds.only (Q : Assn) : ExitConds :=
  { normal := Q, brk := Assn.no, cont := Assn.no, ret := fun _ _ => False }

/-! ## The triple -/

def Triple (ge : CGenv) (fe : EntryRel) (f : Function) (P : Assn) (s : Stmt)
    (R : ExitConds) : Prop :=
  ∀ k e le hp hf m,
    Heap.disjoint hp hf → Heap.Agrees (Heap.union hp hf) m → P e le hp →
    ∃ o hp',
      Steps (SStep ge fe) (.State f s k e le m) (o.state f k)
      ∧ Heap.disjoint hp' hf
      ∧ Heap.Agrees (Heap.union hp' hf) (outMem o)
      ∧ R.holds o hp'

/-! ## Structural rules

The heap-neutral rules simply hand `hp` back unchanged; only `assign` (and the
entry/exit rules) actually move resources. -/

theorem triple_skip (ge fe f) (P : Assn) : Triple ge fe f P .Sskip (.only P) := by
  intro k e le hp hf m hd hag hP
  exact ⟨.Normal e le m, hp, Steps.refl _, hd, hag, hP⟩

theorem triple_conseq (ge fe f) {P P' : Assn} {s} {R R' : ExitConds}
    (h : Triple ge fe f P s R)
    (hP : ∀ e le hp, P' e le hp → P e le hp)
    (hn : ∀ e le hp, R.normal e le hp → R'.normal e le hp)
    (hb : ∀ e le hp, R.brk e le hp → R'.brk e le hp)
    (hc : ∀ e le hp, R.cont e le hp → R'.cont e le hp)
    (hr : ∀ v hp, R.ret v hp → R'.ret v hp)
    -- Wave E: a trailing `autoParam`, so the 9 pre-existing call sites of this
    -- rule are untouched.  The default closes the two cases that actually occur:
    -- the goto conditions are the same, or the source has none.
    (hg : ∀ lbl e le hp, R.goto lbl e le hp → R'.goto lbl e le hp := by
      intro _ _ _ _ hgg; first | exact hgg | exact hgg.elim) :
    Triple ge fe f P' s R' := by
  intro k e le hp hf m hd hag hP'
  obtain ⟨o, hp', hs, hd', hag', hR⟩ := h k e le hp hf m hd hag (hP e le hp hP')
  refine ⟨o, hp', hs, hd', hag', ?_⟩
  cases o with
  | Normal _ _ _ => exact hn _ _ _ hR
  | Break _ _ _ => exact hb _ _ _ hR
  | Continue _ _ _ => exact hc _ _ _ hR
  | Goto _ _ _ _ => exact hg _ _ _ _ hR
  | Return _ _ => exact hr _ _ hR

theorem triple_exists {α : Sort u} (ge fe f) (P : α → Assn) (s : Stmt) (R : ExitConds)
    (h : ∀ x, Triple ge fe f (P x) s R) :
    Triple ge fe f (fun e le hp => ∃ x, P x e le hp) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨x, hx⟩ := hP
  exact h x k e le hp hf m hd hag hx

theorem triple_vacuous (ge fe f) (s : Stmt) (R : ExitConds) :
    Triple ge fe f Assn.no s R := fun _ _ _ _ _ _ _ _ h => False.elim h

theorem triple_fallthrough (ge fe f) (P Q : Assn) (s : Stmt) (R : ExitConds)
    (h : Triple ge fe f P s (.only Q)) (hn : ∀ e le hp, Q e le hp → R.normal e le hp) :
    Triple ge fe f P s R :=
  triple_conseq ge fe f h (fun _ _ _ x => x) hn
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-- Assignment to a temporary.  The caller gets `Agrees hp m` — the fragment is
    realized by the memory — which is what lets it discharge `EvalExpr`. -/
theorem triple_set (ge fe f) (P Q : Assn) (id : Ident) (a : Expr)
    (h : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
           ∃ v, EvalExpr ge e le m a v ∧ Q e (le.set id v) hp) :
    Triple ge fe f P (.Sset id a) (.only Q) := by
  intro k e le hp hf m hd hag hP
  obtain ⟨v, hev, hQ⟩ := h e le hp m hP (Heap.Agrees_union_left hag)
  exact ⟨.Normal e (le.set id v) m, hp,
         Steps.one (Step.set f id a k e le m v hev), hd, hag, hQ⟩

theorem triple_seq (ge fe f) (P Q : Assn) (R : ExitConds) (s1 s2 : Stmt)
    (h1 : Triple ge fe f P s1 { R with normal := Q })
    (h2 : Triple ge fe f Q s2 R) :
    Triple ge fe f P (.Ssequence s1 s2) R := by
  intro k e le hp hf m hd hag hP
  have hstart : SStep ge fe (.State f (.Ssequence s1 s2) k e le m)
                            (.State f s1 (.Kseq s2 k) e le m) := Step.seq f s1 s2 k e le m
  obtain ⟨o1, hp1, hs1, hd1, hag1, hR1⟩ := h1 (.Kseq s2 k) e le hp hf m hd hag hP
  cases o1 with
  | Goto lbl e' le' m' =>
      -- `gotoTarget` ignores the `Kseq` frame (`gotoTarget_kseq`, by `rfl`), so
      -- s1's landing site *is* the sequence's landing site
      exact ⟨.Goto lbl e' le' m', hp1, Steps.trans (Steps.one hstart) hs1,
             hd1, hag1, hR1⟩
  | Normal e' le' m' =>
      obtain ⟨o2, hp2, hs2, hd2, hag2, hR2⟩ := h2 k e' le' hp1 hf m' hd1 hag1 hR1
      refine ⟨o2, hp2, ?_, hd2, hag2, hR2⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
      exact Steps.step _ _ _ (Step.skip_seq f s2 k e' le' m') hs2
  | Break e' le' m' =>
      refine ⟨.Break e' le' m', hp1, ?_, hd1, hag1, hR1⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
      exact Steps.one (Step.break_seq f s2 k e' le' m')
  | Continue e' le' m' =>
      refine ⟨.Continue e' le' m', hp1, ?_, hd1, hag1, hR1⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
      exact Steps.one (Step.continue_seq f s2 k e' le' m')
  | Return v m' =>
      -- `callCont (Kseq s2 k) = callCont k`, so the endpoint already matches
      exact ⟨.Return v m', hp1, Steps.trans (Steps.one hstart) hs1, hd1, hag1, hR1⟩

theorem triple_if (ge fe f) (P Pt Pf : Assn) (R : ExitConds) (a : Expr) (s1 s2 : Stmt)
    (hg : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
            ∃ v b, EvalExpr ge e le m a v ∧ Cop.boolVal v (typeof a) m = some b
                   ∧ (if b then Pt e le hp else Pf e le hp))
    (h1 : Triple ge fe f Pt s1 R) (h2 : Triple ge fe f Pf s2 R) :
    Triple ge fe f P (.Sifthenelse a s1 s2) R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨v, b, hev, hbv, hbr⟩ := hg e le hp m hP (Heap.Agrees_union_left hag)
  have hstart : SStep ge fe (.State f (.Sifthenelse a s1 s2) k e le m)
                            (.State f (if b then s1 else s2) k e le m) :=
    Step.ifthenelse f a s1 s2 k e le m v b hev hbv
  cases b with
  | true =>
      obtain ⟨o, hp', hs, hd', hag', hR⟩ := h1 k e le hp hf m hd hag (by simpa using hbr)
      exact ⟨o, hp', Steps.trans (Steps.one hstart) hs, hd', hag', hR⟩
  | false =>
      obtain ⟨o, hp', hs, hd', hag', hR⟩ := h2 k e le hp hf m hd hag (by simpa using hbr)
      exact ⟨o, hp', Steps.trans (Steps.one hstart) hs, hd', hag', hR⟩

theorem triple_if_true (ge fe f) (P : Assn) (R : ExitConds) (a : Expr) (s1 s2 : Stmt)
    (hg : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
            ∃ v, EvalExpr ge e le m a v ∧ Cop.boolVal v (typeof a) m = some true)
    (h1 : Triple ge fe f P s1 R) :
    Triple ge fe f P (.Sifthenelse a s1 s2) R := by
  refine triple_if ge fe f P P Assn.no R a s1 s2 (fun e le hp m hP hagr => ?_) h1
    (triple_vacuous ge fe f _ _)
  obtain ⟨v, hev, hbv⟩ := hg e le hp m hP hagr
  exact ⟨v, true, hev, hbv, by simpa using hP⟩

theorem triple_if_false (ge fe f) (P : Assn) (R : ExitConds) (a : Expr) (s1 s2 : Stmt)
    (hg : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
            ∃ v, EvalExpr ge e le m a v ∧ Cop.boolVal v (typeof a) m = some false)
    (h2 : Triple ge fe f P s2 R) :
    Triple ge fe f P (.Sifthenelse a s1 s2) R := by
  refine triple_if ge fe f P Assn.no P R a s1 s2 (fun e le hp m hP hagr => ?_)
    (triple_vacuous ge fe f _ _) h2
  obtain ⟨v, hev, hbv⟩ := hg e le hp m hP hagr
  exact ⟨v, false, hev, hbv, by simpa using hP⟩

theorem triple_break (ge fe f) (P : Assn) :
    Triple ge fe f P .Sbreak
      { normal := Assn.no, brk := P, cont := Assn.no, ret := fun _ _ => False } := by
  intro k e le hp hf m hd hag hP
  exact ⟨.Break e le m, hp, Steps.refl _, hd, hag, hP⟩

theorem triple_continue (ge fe f) (P : Assn) :
    Triple ge fe f P .Scontinue
      { normal := Assn.no, brk := Assn.no, cont := P, ret := fun _ _ => False } := by
  intro k e le hp hf m hd hag hP
  exact ⟨.Continue e le m, hp, Steps.refl _, hd, hag, hP⟩

/-- `return e`.  The locals are freed, so the caller must supply the resulting
    memory and show the fragment still agrees with it — for a function with no
    `fn_vars` that is a no-op (`Mem.freeList` over the empty environment). -/
theorem triple_return (ge fe f) (P : Assn) (Ret : Val → HProp) (a : Expr)
    (h : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
      ∃ v v' m' hp',
        EvalExpr ge e le m a v
        ∧ Cop.semCast v (typeof a) f.fn_return m = some v'
        ∧ Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m'
        ∧ Ret v' hp'
        ∧ (∀ hf, Heap.disjoint hp hf → Heap.Agrees (Heap.union hp hf) m →
              Heap.disjoint hp' hf ∧ Heap.Agrees (Heap.union hp' hf) m')) :
    Triple ge fe f P (.Sreturn (some a))
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  intro k e le hp hf m hd hag hP
  obtain ⟨v, v', m', hp', hev, hcast, hfree, hRet, hframe⟩ :=
    h e le hp m hP (Heap.Agrees_union_left hag)
  obtain ⟨hd', hag'⟩ := hframe hf hd hag
  exact ⟨.Return v' m', hp',
         Steps.one (Step.return_1 f a k e le m v v' m' hev hcast hfree), hd', hag', hRet⟩

/-- **`return;`** — the void return.  `triple_return` above covers
    `Sreturn (some a)` only, so before this there was no rule for a `void`
    function's exit.  `put` in `test/lean/structcopy.c` needs it, and so does
    every `void` function on the zlib path.

    Found while building the acceptance test for `triple_assign_copy`: the brief
    for that rule assumed the test's `FunSpec` would go through, and this is one
    of the two reasons it does not. -/
theorem triple_return_none (ge fe f) (P : Assn) (Ret : Val → HProp)
    (h : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
      ∃ m' hp',
        Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m'
        ∧ Ret .Vundef hp'
        ∧ (∀ hf, Heap.disjoint hp hf → Heap.Agrees (Heap.union hp hf) m →
              Heap.disjoint hp' hf ∧ Heap.Agrees (Heap.union hp' hf) m')) :
    Triple ge fe f P (.Sreturn none)
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  intro k e le hp hf m hd hag hP
  obtain ⟨m', hp', hfree, hRet, hframe⟩ :=
    h e le hp m hP (Heap.Agrees_union_left hag)
  obtain ⟨hd', hag'⟩ := hframe hf hd hag
  exact ⟨.Return .Vundef m', hp',
         Steps.one (Step.return_0 f k e le m m' hfree), hd', hag', hRet⟩

/-! ## `switch`

`Sswitch` selects a labelled-statement suffix, runs it under `Kswitch`, and there
`break` means "leave the switch" (`step_skip_break_switch` maps both `Sskip` and
`Sbreak` to normal exit) while `continue` passes straight through to the enclosing
loop.  So the selected body is verified with `brk` and `normal` *merged*, which is
exactly C's fall-through-or-break behaviour.

`inflate`'s state machine is one large `switch`, so this is on the zlib path. -/

theorem triple_switch (ge fe f) (P : Assn) (R : ExitConds) (a : Expr) (sl : LStmts)
    (hbody : ∀ n : Z, Triple ge fe f P (seqOfLabeledStatement (selectSwitch n sl))
      { normal := R.normal, brk := R.normal, cont := R.cont, ret := R.ret,
        goto := R.goto })
    (hsel : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
            ∃ v n, EvalExpr ge e le m a v ∧ Cop.semSwitchArg v (typeof a) = some n) :
    Triple ge fe f P (.Sswitch a sl) R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨v, n, hev, hsw⟩ := hsel e le hp m hP (Heap.Agrees_union_left hag)
  have hstart : SStep ge fe (.State f (.Sswitch a sl) k e le m)
                            (.State f (seqOfLabeledStatement (selectSwitch n sl))
                              (.Kswitch k) e le m) :=
    Step.switch f a sl k e le m v n hev hsw
  obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
    hbody n (.Kswitch k) e le hp hf m hd hag hP
  cases o with
  | Goto lbl e' le' m' =>
      -- `gotoTarget` ignores the `Kswitch` frame, so the landing site is unchanged
      exact ⟨.Goto lbl e' le' m', hp', Steps.trans (Steps.one hstart) hs,
             hd', hag', hR⟩
  | Normal e' le' m' =>
      -- `Sskip` under `Kswitch` leaves the switch
      refine ⟨.Normal e' le' m', hp', ?_, hd', hag', hR⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs ?_)
      exact Steps.one (Step.skip_break_switch f .Sskip k e' le' m' (.inl rfl))
  | Break e' le' m' =>
      -- so does `Sbreak`, and it lands in the *normal* postcondition
      refine ⟨.Normal e' le' m', hp', ?_, hd', hag', hR⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs ?_)
      exact Steps.one (Step.skip_break_switch f .Sbreak k e' le' m' (.inr rfl))
  | Continue e' le' m' =>
      -- `continue` passes through to the enclosing loop
      refine ⟨.Continue e' le' m', hp', ?_, hd', hag', hR⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs ?_)
      exact Steps.one (Step.continue_switch f k e' le' m')
  | Return v' m' =>
      -- `callCont (Kswitch k) = callCont k`, so the endpoint already matches
      exact ⟨.Return v' m', hp', Steps.trans (Steps.one hstart) hs, hd', hag', hR⟩

/-- **`switch` with the scrutinee pinned.**

    `triple_switch` above demands the body at *every* scrutinee value.  When the
    precondition already fixes the scrutinee — as `inflate_table`'s does, because
    the spec cases on `type ∈ {CODES, LENS, DISTS}` before reaching the switch —
    that would leave triples owed for the two unreachable arms against the same
    postcondition, provable only by weakening `R` into a disjunction over all
    three arms' effects, which then pollutes every later step.

    This is `triple_switch`'s proof with `n := n₀`; the `∀ n` there is consumed
    exactly once, at the selected value, so nothing else changes.  It is a copy
    rather than a derivation because `triple_switch`'s `hsel` produces its `n`
    per-state, so it cannot be instantiated at a single `n₀` up front. -/
theorem triple_switch_const (ge fe f) (P : Assn) (R : ExitConds) (a : Expr)
    (sl : LStmts) (n₀ : Z)
    (hbody : Triple ge fe f P (seqOfLabeledStatement (selectSwitch n₀ sl))
      { normal := R.normal, brk := R.normal, cont := R.cont, ret := R.ret,
        goto := R.goto })
    (hsel : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
            ∃ v, EvalExpr ge e le m a v
                 ∧ Cop.semSwitchArg v (typeof a) = some n₀) :
    Triple ge fe f P (.Sswitch a sl) R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨v, hev, hsw⟩ := hsel e le hp m hP (Heap.Agrees_union_left hag)
  have hstart : SStep ge fe (.State f (.Sswitch a sl) k e le m)
                            (.State f (seqOfLabeledStatement (selectSwitch n₀ sl))
                              (.Kswitch k) e le m) :=
    Step.switch f a sl k e le m v n₀ hev hsw
  obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
    hbody (.Kswitch k) e le hp hf m hd hag hP
  cases o with
  | Goto lbl e' le' m' =>
      exact ⟨.Goto lbl e' le' m', hp', Steps.trans (Steps.one hstart) hs,
             hd', hag', hR⟩
  | Normal e' le' m' =>
      refine ⟨.Normal e' le' m', hp', ?_, hd', hag', hR⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs ?_)
      exact Steps.one (Step.skip_break_switch f .Sskip k e' le' m' (.inl rfl))
  | Break e' le' m' =>
      refine ⟨.Normal e' le' m', hp', ?_, hd', hag', hR⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs ?_)
      exact Steps.one (Step.skip_break_switch f .Sbreak k e' le' m' (.inr rfl))
  | Continue e' le' m' =>
      refine ⟨.Continue e' le' m', hp', ?_, hd', hag', hR⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs ?_)
      exact Steps.one (Step.continue_switch f k e' le' m')
  | Return v' m' =>
      exact ⟨.Return v' m', hp', Steps.trans (Steps.one hstart) hs, hd', hag', hR⟩

/-! ## The loop rule

Unchanged in shape from the non-separating version: a `Nat` measure that must
strictly decrease each trip, so termination comes with the invariant.  The heap
threads through exactly as in `triple_seq`. -/

theorem triple_loop (ge fe f) (R : ExitConds) (I J : Nat → Assn) (s1 s2 : Stmt)
    (hbody : ∀ n, Triple ge fe f (I n) s1
      { normal := J n, brk := R.normal, cont := J n, ret := R.ret,
        goto := R.goto })
    (hincr : ∀ n, Triple ge fe f (J n) s2
      { normal := fun e le hp => ∃ n', n' < n ∧ I n' e le hp,
        brk := R.normal, cont := Assn.no, ret := R.ret, goto := R.goto }) :
    ∀ n, Triple ge fe f (I n) (.Sloop s1 s2) R := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k e le hp hf m hd hag hI
    have hstart : SStep ge fe (.State f (.Sloop s1 s2) k e le m)
                              (.State f s1 (.Kloop1 s1 s2 k) e le m) := Step.loop f s1 s2 k e le m
    obtain ⟨o1, hp1, hs1, hd1, hag1, hR1⟩ :=
      hbody n (.Kloop1 s1 s2 k) e le hp hf m hd hag hI
    -- s1 falls through or continues (run s2), breaks (leave), or returns
    have hbodyCase : ∀ (x : Stmt) (e1 : Env) (le1 : TempEnv) (m1 : Mem) (hpm : Heap),
        (x = Stmt.Sskip ∨ x = Stmt.Scontinue) →
        Heap.disjoint hpm hf → Heap.Agrees (Heap.union hpm hf) m1 → J n e1 le1 hpm →
        Steps (SStep ge fe) (.State f s1 (.Kloop1 s1 s2 k) e le m)
              (.State f x (.Kloop1 s1 s2 k) e1 le1 m1) →
        ∃ o hp', Steps (SStep ge fe) (.State f (.Sloop s1 s2) k e le m) (o.state f k)
               ∧ Heap.disjoint hp' hf ∧ Heap.Agrees (Heap.union hp' hf) (outMem o)
               ∧ R.holds o hp' := by
      intro x e1 le1 m1 hpm hx hdm hagm hJ hreach
      have hto2 : SStep ge fe (.State f x (.Kloop1 s1 s2 k) e1 le1 m1)
                              (.State f s2 (.Kloop2 s1 s2 k) e1 le1 m1) :=
        Step.skip_or_continue_loop1 f s1 s2 k e1 le1 m1 x hx
      obtain ⟨o2, hp2, hs2, hd2, hag2, hR2⟩ :=
        hincr n (.Kloop2 s1 s2 k) e1 le1 hpm hf m1 hdm hagm hJ
      cases o2 with
      | Goto lbl e2 le2 m2 =>
          -- `gotoTarget` ignores `Kloop2`
          exact ⟨.Goto lbl e2 le2 m2, hp2,
                 Steps.trans (Steps.one hstart)
                   (Steps.trans hreach (Steps.step _ _ _ hto2 hs2)),
                 hd2, hag2, hR2⟩
      | Normal e2 le2 m2 =>
          obtain ⟨n', hlt, hI'⟩ := hR2
          obtain ⟨o, hp3, hs3, hd3, hag3, hR3⟩ := ih n' hlt k e2 le2 hp2 hf m2 hd2 hag2 hI'
          refine ⟨o, hp3, ?_, hd3, hag3, hR3⟩
          refine Steps.trans (Steps.one hstart) (Steps.trans hreach ?_)
          refine Steps.step _ _ _ hto2 (Steps.trans hs2 ?_)
          exact Steps.step _ _ _ (Step.skip_loop2 f s1 s2 k e2 le2 m2) hs3
      | Break e2 le2 m2 =>
          refine ⟨.Normal e2 le2 m2, hp2, ?_, hd2, hag2, hR2⟩
          refine Steps.trans (Steps.one hstart) (Steps.trans hreach ?_)
          refine Steps.step _ _ _ hto2 (Steps.trans hs2 ?_)
          exact Steps.one (Step.break_loop2 f s1 s2 k e2 le2 m2)
      | Continue _ _ _ => exact False.elim hR2
      | Return v m2 =>
          refine ⟨.Return v m2, hp2, ?_, hd2, hag2, hR2⟩
          refine Steps.trans (Steps.one hstart) (Steps.trans hreach ?_)
          exact Steps.step _ _ _ hto2 hs2
    cases o1 with
    | Normal e1 le1 m1 => exact hbodyCase .Sskip e1 le1 m1 hp1 (.inl rfl) hd1 hag1 hR1 hs1
    | Continue e1 le1 m1 => exact hbodyCase .Scontinue e1 le1 m1 hp1 (.inr rfl) hd1 hag1 hR1 hs1
    | Break e1 le1 m1 =>
        refine ⟨.Normal e1 le1 m1, hp1, ?_, hd1, hag1, hR1⟩
        refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
        exact Steps.one (Step.break_loop1 f s1 s2 k e1 le1 m1)
    | Return v m1 =>
        exact ⟨.Return v m1, hp1, Steps.trans (Steps.one hstart) hs1, hd1, hag1, hR1⟩
    | Goto lbl e1 le1 m1 =>
        -- `gotoTarget` ignores `Kloop1`
        exact ⟨.Goto lbl e1 le1 m1, hp1, Steps.trans (Steps.one hstart) hs1,
               hd1, hag1, hR1⟩

/-! ## `goto` and `label` — Phase 9 Wave E

`Step.label` just unwraps.  `Sgoto` is the interesting one: because the jump is
folded into the outcome's state (see `CC.gotoTarget`), `triple_goto` *is* the
single `Step.goto`, and the label is resolved later by `triple_body_goto`. -/

/-- A label is transparent: `Step.label` steps straight into its body. -/
theorem triple_label (ge fe f) (P : Assn) (lbl : Ident) (s : Stmt) (R : ExitConds)
    (h : Triple ge fe f P s R) : Triple ge fe f P (.Slabel lbl s) R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨o, hp', hs, hd', hag', hR⟩ := h k e le hp hf m hd hag hP
  exact ⟨o, hp', Steps.step _ _ _ (Step.label f lbl s k e le m) hs, hd', hag', hR⟩

/-- **`goto lbl`.**  Exits with the `Goto` outcome, whose state is already the
    post-jump state — so the single `Step.goto` *is* the whole proof.

    `hres` says the label exists.  It is not red tape: a `goto` to a label not in
    the function has no rule, which is right, because C rejects such a program.
    Note the hypothesis is over an arbitrary continuation, which is sound because
    `findLabel`'s *success* depends only on `f.fn_body` — the continuation is
    merely threaded through. -/
theorem triple_goto (ge fe f) (P : Assn) (lbl : Ident)
    (hres : ∀ kk : Cont, ∃ s' k', findLabel lbl f.fn_body kk = some (s', k')) :
    Triple ge fe f P (.Sgoto lbl)
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := fun _ _ => False,
        goto := fun l => if l = lbl then P else Assn.no } := by
  intro k e le hp hf m hd hag hP
  refine ⟨.Goto lbl e le m, hp, ?_, hd, hag, ?_⟩
  · show Steps (SStep ge fe) (.State f (.Sgoto lbl) k e le m)
           (gotoTarget f k lbl e le m)
    obtain ⟨s', k', hfl⟩ := hres (callCont k)
    rw [show gotoTarget f k lbl e le m = .State f s' k' e le m from by
          unfold gotoTarget; rw [hfl]]
    exact Steps.one (Step.goto f lbl k e le m s' k' hfl)
  · show (if lbl = lbl then P else Assn.no) e le hp
    rw [if_pos rfl]
    exact hP

/-! ### Where a `goto` gets resolved — and why not here

`Step.goto` resolves the label with `findLabel lbl f.fn_body (callCont k)`, so the
landing continuation is `callCont k`, not `k`.  A `Triple` quantifies over **all**
`k`, and for a general `k` those differ — so **no `Triple`-shaped rule can
discharge a jump.**  (This was worth finding out by trying: the first draft of a
`triple_body_goto` fails on exactly that mismatch.)

The resolution therefore lives one level up, in `CCLib/logic/Funspec.lean`, as
`Sep.satisfies_internal_goto`: `SatisfiesAt` carries `isCallCont k`, hence
`callCont k = k`, which is precisely the missing fact.  That is also the right
level *semantically* — `findLabel` searches `f.fn_body`, so a label is a property
of the function, not of a statement. -/

/-! ## The frame rule

The payoff of Phase 7.2-7.3.  It holds because the triple already carries an
arbitrary frame: reassociating the union is the whole proof. -/

/-- Conjoin a heap-only assertion to every exit condition. -/
def ExitConds.frame (R : ExitConds) (Q : HProp) : ExitConds :=
  { normal := fun e le => R.normal e le ∗ Q
    brk := fun e le => R.brk e le ∗ Q
    cont := fun e le => R.cont e le ∗ Q
    ret := fun v => R.ret v ∗ Q
    goto := fun lbl e le => R.goto lbl e le ∗ Q }

/-- **The frame rule.**  Stated for a heap-only `Q`: a general `Assn` frame would
    need VST's modified-variables side condition, since `Sset` changes the
    temporaries. -/
theorem triple_frame (ge fe f) (P : Assn) (s : Stmt) (R : ExitConds) (Q : HProp)
    (h : Triple ge fe f P s R) :
    Triple ge fe f (fun e le => P e le ∗ Q) s (R.frame Q) := by
  intro k e le hp hf m hd hag hPQ
  obtain ⟨h1, h2, hd12, heq, hP, hQ⟩ := hPQ
  subst heq
  rw [Heap.disjoint_union_left] at hd
  -- run the original triple with `h2` folded into the frame
  have hd1 : Heap.disjoint h1 (Heap.union h2 hf) := by
    rw [Heap.disjoint_union_right]; exact ⟨hd12, hd.1⟩
  have hag1 : Heap.Agrees (Heap.union h1 (Heap.union h2 hf)) m := by
    rw [← Heap.union_assoc]; exact hag
  obtain ⟨o, h1', hs, hd1', hag1', hR⟩ := h k e le h1 (Heap.union h2 hf) m hd1 hag1 hP
  rw [Heap.disjoint_union_right] at hd1'
  refine ⟨o, Heap.union h1' h2, hs, ?_, ?_, ?_⟩
  · rw [Heap.disjoint_union_left]; exact ⟨hd1'.2, hd.2⟩
  · rw [Heap.union_assoc]; exact hag1'
  · -- the postcondition regains `Q`
    have hsep : ∀ (S : HProp), S h1' → (S ∗ Q) (Heap.union h1' h2) :=
      fun S hS => ⟨h1', h2, hd1'.1, rfl, hS, hQ⟩
    cases o with
    | Normal _ _ _ => exact hsep _ hR
    | Break _ _ _ => exact hsep _ hR
    | Continue _ _ _ => exact hsep _ hR
    | Return _ _ => exact hsep _ hR
    | Goto _ _ _ _ => exact hsep _ hR

/-! ## Reading through a fragment

Expression evaluation is not a statement rule, so what the program logic needs is
a way to discharge `EvalExpr` for a dereference whose pointee the fragment owns.
These are the separating replacements for `eval_index` in `CCLib/logic/HoareArray.lean`,
which took the whole (non-separating) array as a hypothesis. -/

/-- Evaluating `*a` when the fragment owns the pointee. -/
theorem eval_deref_mapsto {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {a : Expr}
    {ty : Ty} {chunk : Chunk} {p : Permission} {b : Block} {ofs : Integers.Ptrofs}
    {v : Val} {h : Heap}
    (hacc : accessMode ty = .By_value chunk)
    (hpr : permOrder p .Readable = true)
    (hm : mapsto chunk p b (Integers.Ptrofs.unsigned ofs) v h)
    (hag : Heap.Agrees h m)
    (hptr : EvalExpr ge e le m a (.Vptr b ofs))
    (hw : Mem.ChunkNoWrap chunk (Integers.Ptrofs.unsigned ofs) := by exact Or.inl rfl) :
    EvalExpr ge e le m (.Ederef a ty) (Val.loadResult chunk v) := by
  refine EvalExpr.Elvalue _ b ofs .Full _ (EvalLvalue.Ederef a ty b ofs hptr) ?_
  refine DerefLoc.value chunk _ hacc ?_
  rw [Mem.loadv_ptr _ _ _ _ hw]
  exact mapsto_load hpr hm hag

/-- Evaluating `base[idx]` for an `unsigned int` array the fragment owns. -/
theorem eval_index_array {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Integers.Int} {h : Heap} {base idx : Expr} {i : Nat}
    (hpr : permOrder p .Readable = true)
    (harr : arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n)
    (hptr : EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (htyb : typeof base = tptr tuint) (hty : typeof idx = tint)
    (haddr : Integers.Ptrofs.unsigned
               (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i))
             = Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int)) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd base idx (tptr tuint)) tuint) (.Vint (f i)) := by
  have hadd : Cop.semBinaryOperation ge.genv_cenv .Oadd (.Vptr b ofs0) (typeof base)
                (.Vint (Integers.Int.repr i)) (typeof idx) m
              = some (.Vptr b (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i))) := by
    rw [hty, htyb]; exact semAdd_elem _ _ _ _ _
  refine EvalExpr.Elvalue _ b (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i)) .Full _
    (EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop .Oadd _ _ _ (.Vptr b ofs0) (.Vint (Integers.Int.repr i)) _
        hptr hidx hadd)) ?_
  refine DerefLoc.value .Mint32 _ rfl ?_
  rw [Mem.loadv_ptr _ _ _ _ (Or.inl rfl), haddr]
  exact arrayU32_load p b hpr n f i hi (Integers.Ptrofs.unsigned ofs0) h m harr hag

end Sep
end CC
