/-
  A Hoare logic for Clight, over the real semantics.

  ## Design decision: hand-rolled, not Iris

  The plan left open whether to build on iris-lean or hand-roll.  Hand-rolled,
  for two reasons: this development has no external dependencies at all (no
  Mathlib — several standard tactics are simply unavailable here), and the
  soundness story is much shorter, see below.

  ## Soundness is definitional, not a separate theorem

  VST defines `semax` as an inductive relation and then proves a substantial
  soundness theorem connecting it to the step relation.  Here the triple is
  *defined* as a statement about `Step`:

      Triple ge fe f P s R  ≡  from any state satisfying P, executing `s` reaches an
                            outcome satisfying R

  so there is nothing left to prove about soundness — it holds by construction.
  What has to be proved instead is each *rule*, and those proofs are what this
  file contains.  The trade-off: this is a total-correctness logic for terminating
  statements, and it cannot express anything about diverging code.

  ## Scope and honest limits

  * This is a Hoare logic, **not** separation logic: assertions are plain
    predicates on the state, and there is no `∗` and no frame rule.  Separating
    conjunction needs a notion of splitting CompCert's memory (permissions and
    contents together), which is exactly the "juicy memory" layer VST spends a
    great deal of machinery on.  That is deliberately out of scope here.
  * Executions are silent: `Exec` requires the trace to be `E0`, so nothing here
    covers volatile accesses or `annot`.
  * Function calls are not covered by a rule; `is_sorted` needs none.
-/
import CCLib.cfrontend.Clight

namespace CC

/-! ## Silent execution -/

/-- Reflexive-transitive closure of a step relation. -/
inductive Steps (R : State → State → Prop) : State → State → Prop where
  | refl (s) : Steps R s s
  | step (s1 s2 s3) : R s1 s2 → Steps R s2 s3 → Steps R s1 s3

/-- The type of `Clight.step`'s `function_entry` parameter. -/
abbrev EntryRel := Function → List Val → Mem → Env → TempEnv → Mem → Prop

/-- One silent (event-free) Clight step.  Parameterized over the function-entry
    relation exactly as `Clight.step` is, so the logic serves both `step1` and
    `step2` (`clightgen` output is used with `step2`). -/
abbrev SStep (ge : CGenv) (fe : EntryRel) (s s' : State) : Prop := Step ge fe s E0 s'

theorem Steps.trans {R} {a b c} (h1 : Steps R a b) (h2 : Steps R b c) : Steps R a c := by
  induction h1 with
  | refl _ => exact h2
  | step x y _ hxy _ ih => exact Steps.step x y c hxy (ih h2)

theorem Steps.one {R} {a b} (h : R a b) : Steps R a b := Steps.step a b b h (Steps.refl b)

/-- The bridge back to the official semantics: silent steps are `Star` of `Step1`.
    Every theorem proved with this logic therefore says something about `Step`. -/
theorem Steps.toStar {ge : CGenv} {fe : EntryRel} {s s' : State}
    (h : Steps (SStep ge fe) s s') : Star (Step ge fe) s E0 s' := by
  induction h with
  | refl _ => exact Star.refl _
  | step a b c hab _ ih => exact Star.step a E0 b E0 c E0 hab ih rfl

/-! ## Assertions and outcomes -/

/-- An assertion constrains the local environment, the temporaries and memory. -/
abbrev Assn := Env → TempEnv → Mem → Prop

/-- The unsatisfiable assertion, used for exits a statement cannot take. -/
def Assn.no : Assn := fun _ _ _ => False

/-- The **five** ways a Clight statement can finish.  `Goto` was added in Phase 9
    Wave E: `inflate` reaches its cleanup through 37 `goto inf_leave`s, and a
    jump is not any of the other four exits.

    Like `Break`/`Continue`, a `Goto` outcome means "control is *at* the jump" —
    the state is the `Sgoto` statement itself, and no step has been taken.  The
    jump is resolved later, by `Sep.triple_body_goto`, at the level where
    `findLabel` can be evaluated (see there for why that level is the body). -/
inductive Outcome where
  | Normal (e : Env) (le : TempEnv) (m : Mem)
  | Break (e : Env) (le : TempEnv) (m : Mem)
  | Continue (e : Env) (le : TempEnv) (m : Mem)
  | Return (v : Val) (m : Mem)
  | Goto (lbl : Ident) (e : Env) (le : TempEnv) (m : Mem)

/-- Where a `goto lbl` lands: `Step.goto` resolves the label with
    `findLabel lbl f.fn_body (callCont k)`.

    **The jump is folded into the outcome's state, not left in front of it.**  The
    alternative — letting a `Goto` outcome sit *at* the `Sgoto` statement, as
    `Break` sits at `Sbreak` — does not propagate: a `Sbreak` under `Kseq s2 k`
    can step to `k` (`step_break_seq`), but there is no corresponding rule for
    `Sgoto`, because Clight resolves a goto in one step from wherever it stands.

    Folding the jump in works because `callCont` **ignores** exactly the frames
    the structural rules push — `Kseq`, `Kloop1`, `Kloop2`, `Kswitch` — all four
    by `rfl`.  So this state is literally the same under `k` and under
    `Kseq s2 k`, and a `Goto` outcome propagates out of a sequence, loop or
    switch with no work at all.

    The `none` case cannot arise for a program C accepted (a `goto` needs a label
    in scope).  It is mapped to the goto stuck at `callCont k` — note *not* at
    `k`, which would reintroduce the dependence on the pushed frames and destroy
    the invariance the whole design rests on. -/
def gotoTarget (f : Function) (k : Cont) (lbl : Ident) (e : Env) (le : TempEnv)
    (m : Mem) : State :=
  match findLabel lbl f.fn_body (callCont k) with
  | some (s', k') => .State f s' k' e le m
  | none => .State f (.Sgoto lbl) (callCont k) e le m

/-- The state an outcome corresponds to, under continuation `k`.  Note `Return`
    pops to `callCont k`, exactly as `step_return_*` does. -/
def Outcome.state (f : Function) (k : Cont) : Outcome → State
  | .Normal e le m => .State f .Sskip k e le m
  | .Break e le m => .State f .Sbreak k e le m
  | .Continue e le m => .State f .Scontinue k e le m
  | .Return v m => .Returnstate v (callCont k) m
  | .Goto lbl e le m => gotoTarget f k lbl e le m

/-- A goto's landing site does not depend on the frames a structural rule pushed:
    all four hold by `rfl`, which is what makes `Goto` propagate for free. -/
theorem gotoTarget_kseq (f k lbl e le m) (s2 : Stmt) :
    gotoTarget f (.Kseq s2 k) lbl e le m = gotoTarget f k lbl e le m := rfl
theorem gotoTarget_kloop1 (f k lbl e le m) (a b : Stmt) :
    gotoTarget f (.Kloop1 a b k) lbl e le m = gotoTarget f k lbl e le m := rfl
theorem gotoTarget_kloop2 (f k lbl e le m) (a b : Stmt) :
    gotoTarget f (.Kloop2 a b k) lbl e le m = gotoTarget f k lbl e le m := rfl
theorem gotoTarget_kswitch (f k lbl e le m) :
    gotoTarget f (.Kswitch k) lbl e le m = gotoTarget f k lbl e le m := rfl

/-- Postconditions: one assertion per exit kind. -/
structure ExitConds where
  normal : Assn
  brk : Assn
  cont : Assn
  ret : Val → Mem → Prop

/-- Does an outcome satisfy the postconditions? -/
def ExitConds.holds (R : ExitConds) : Outcome → Prop
  | .Normal e le m => R.normal e le m
  | .Break e le m => R.brk e le m
  | .Continue e le m => R.cont e le m
  | .Return v m => R.ret v m
  -- This logic is SUPERSEDED and has no `goto` condition: a jump is simply not
  -- one of its outcomes.  Wave E's real support lives in `CCLib/logic/SepHoare.lean`.
  | .Goto _ _ _ _ => False

/-- Only-normal-exit postconditions. -/
def ExitConds.only (Q : Assn) : ExitConds :=
  { normal := Q, brk := Assn.no, cont := Assn.no, ret := fun _ _ => False }

/-! ## The triple

SUPERSEDED (Phase 7.4) by `CCLib/logic/SepHoare.lean`, which carries a heap frame and
so admits a frame rule and a call rule.  Everything from here down is kept
because `examples/IsSortedReal.lean` still uses it and because the two are worth
comparing; new proofs should use `CC.Sep`.

Note the *infrastructure* above — `Steps`, `SStep`, `EntryRel`, `Outcome`,
`Outcome.state`, `Steps.toStar` — is NOT superseded: `SepHoare` shares it. -/

/-- `Triple ge fe f P s R`: from any state satisfying `P` — under *any* continuation
    — executing `s` silently reaches an outcome satisfying `R`.

    Quantifying over the continuation is what makes the rules compose: it is the
    same device as VST's continuation-agnostic `semax`. -/
def Triple (ge : CGenv) (fe : EntryRel) (f : Function) (P : Assn) (s : Stmt)
    (R : ExitConds) : Prop :=
  ∀ k e le m, P e le m →
    ∃ o, Steps (SStep ge fe) (.State f s k e le m) (o.state f k) ∧ R.holds o

/-! ## Structural rules -/

theorem triple_skip (ge fe f) (P : Assn) : Triple ge fe f P .Sskip (.only P) := by
  intro k e le m hP
  exact ⟨.Normal e le m, Steps.refl _, hP⟩

theorem triple_conseq (ge fe f) {P P' : Assn} {s} {R R' : ExitConds}
    (h : Triple ge fe f P s R)
    (hP : ∀ e le m, P' e le m → P e le m)
    (hn : ∀ e le m, R.normal e le m → R'.normal e le m)
    (hb : ∀ e le m, R.brk e le m → R'.brk e le m)
    (hc : ∀ e le m, R.cont e le m → R'.cont e le m)
    (hr : ∀ v m, R.ret v m → R'.ret v m) :
    Triple ge fe f P' s R' := by
  intro k e le m hP'
  obtain ⟨o, hsteps, hR⟩ := h k e le m (hP e le m hP')
  refine ⟨o, hsteps, ?_⟩
  cases o with
  | Normal e' le' m' => exact hn _ _ _ hR
  | Break e' le' m' => exact hb _ _ _ hR
  | Continue e' le' m' => exact hc _ _ _ hR
  | Return v m' => exact hr _ _ hR
  | Goto _ _ _ _ => exact False.elim hR

/-- Existential precondition: prove the triple for each witness.  Used to peel
    the `∃ i` off a loop invariant so the body proof can name the index. -/
theorem triple_exists {α : Sort u} (ge fe f) (P : α → Assn) (s : Stmt) (R : ExitConds)
    (h : ∀ x, Triple ge fe f (P x) s R) :
    Triple ge fe f (fun e le m => ∃ x, P x e le m) s R := by
  intro k e le m hP
  obtain ⟨x, hx⟩ := hP
  exact h x k e le m hx

/-- Assignment to a temporary. -/
theorem triple_set (ge fe f) (P Q : Assn) (id : Ident) (a : Expr)
    (h : ∀ e le m, P e le m → ∃ v, EvalExpr ge e le m a v ∧ Q e (le.set id v) m) :
    Triple ge fe f P (.Sset id a) (.only Q) := by
  intro k e le m hP
  obtain ⟨v, hev, hQ⟩ := h e le m hP
  exact ⟨.Normal e (le.set id v) m,
         Steps.one (Step.set f id a k e le m v hev), hQ⟩

/-- Assignment through an l-value. -/
theorem triple_assign (ge fe f) (P Q : Assn) (a1 a2 : Expr)
    (h : ∀ e le m, P e le m →
      ∃ loc ofs bf v2 v m',
        EvalLvalue ge e le m a1 loc ofs bf ∧
        EvalExpr ge e le m a2 v2 ∧
        Cop.semCast v2 (typeof a2) (typeof a1) m = some v ∧
        AssignLoc ge.genv_cenv (typeof a1) m loc ofs bf v m' ∧
        Q e le m') :
    Triple ge fe f P (.Sassign a1 a2) (.only Q) := by
  intro k e le m hP
  obtain ⟨loc, ofs, bf, v2, v, m', hlv, hev, hcast, hass, hQ⟩ := h e le m hP
  exact ⟨.Normal e le m',
         Steps.one (Step.assign f a1 a2 k e le m loc ofs bf v2 v m' hlv hev hcast hass), hQ⟩

/-- Sequencing.  The abnormal exits of `s1` pass straight through. -/
theorem triple_seq (ge fe f) (P Q : Assn) (R : ExitConds) (s1 s2 : Stmt)
    (h1 : Triple ge fe f P s1 { R with normal := Q })
    (h2 : Triple ge fe f Q s2 R) :
    Triple ge fe f P (.Ssequence s1 s2) R := by
  intro k e le m hP
  -- enter s1 with the rest of the sequence pushed on the continuation
  have hstart : SStep ge fe (.State f (.Ssequence s1 s2) k e le m)
                         (.State f s1 (.Kseq s2 k) e le m) :=
    Step.seq f s1 s2 k e le m
  obtain ⟨o1, hs1, hR1⟩ := h1 (.Kseq s2 k) e le m hP
  cases o1 with
  | Normal e' le' m' =>
      -- s1 fell through: pop the continuation and run s2
      obtain ⟨o2, hs2, hR2⟩ := h2 k e' le' m' hR1
      refine ⟨o2, ?_, hR2⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
      exact Steps.step _ _ _ (Step.skip_seq f s2 k e' le' m') hs2
  | Break e' le' m' =>
      refine ⟨.Break e' le' m', ?_, hR1⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
      exact Steps.one (Step.break_seq f s2 k e' le' m')
  | Continue e' le' m' =>
      refine ⟨.Continue e' le' m', ?_, hR1⟩
      refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
      exact Steps.one (Step.continue_seq f s2 k e' le' m')
  | Return v m' =>
      -- `callCont (Kseq s2 k) = callCont k`, so the endpoint is already right
      refine ⟨.Return v m', ?_, hR1⟩
      exact Steps.trans (Steps.one hstart) hs1
  | Goto _ _ _ _ => exact False.elim hR1

/-- Conditional.  The caller says which branch the state takes — that is what a
    `forward`-style tactic knows at the point it steps over an `if`, and it avoids
    needing determinism of `EvalExpr` to rule the other branch out. -/
theorem triple_if (ge fe f) (P Pt Pf : Assn) (R : ExitConds) (a : Expr) (s1 s2 : Stmt)
    (hg : ∀ e le m, P e le m →
            ∃ v b, EvalExpr ge e le m a v ∧ Cop.boolVal v (typeof a) m = some b
                   ∧ (if b then Pt e le m else Pf e le m))
    (h1 : Triple ge fe f Pt s1 R) (h2 : Triple ge fe f Pf s2 R) :
    Triple ge fe f P (.Sifthenelse a s1 s2) R := by
  intro k e le m hP
  obtain ⟨v, b, hev, hbv, hbr⟩ := hg e le m hP
  have hstart : SStep ge fe (.State f (.Sifthenelse a s1 s2) k e le m)
                         (.State f (if b then s1 else s2) k e le m) :=
    Step.ifthenelse f a s1 s2 k e le m v b hev hbv
  cases b with
  | true =>
      obtain ⟨o, hs, hR⟩ := h1 k e le m (by simpa using hbr)
      exact ⟨o, Steps.trans (Steps.one hstart) hs, hR⟩
  | false =>
      obtain ⟨o, hs, hR⟩ := h2 k e le m (by simpa using hbr)
      exact ⟨o, Steps.trans (Steps.one hstart) hs, hR⟩

/-- Conditional whose guard the precondition already forces to be true: the else
    branch is unreachable and needs no triple. -/
theorem triple_if_true (ge fe f) (P : Assn) (R : ExitConds) (a : Expr) (s1 s2 : Stmt)
    (hg : ∀ e le m, P e le m →
            ∃ v, EvalExpr ge e le m a v ∧ Cop.boolVal v (typeof a) m = some true)
    (h1 : Triple ge fe f P s1 R) :
    Triple ge fe f P (.Sifthenelse a s1 s2) R := by
  refine triple_if ge fe f P P Assn.no R a s1 s2 (fun e le m hP => ?_) h1
    (fun _ _ _ _ h => False.elim h)
  obtain ⟨v, hev, hbv⟩ := hg e le m hP
  exact ⟨v, true, hev, hbv, by simpa using hP⟩

/-- Conditional whose guard the precondition already forces to be false. -/
theorem triple_if_false (ge fe f) (P : Assn) (R : ExitConds) (a : Expr) (s1 s2 : Stmt)
    (hg : ∀ e le m, P e le m →
            ∃ v, EvalExpr ge e le m a v ∧ Cop.boolVal v (typeof a) m = some false)
    (h2 : Triple ge fe f P s2 R) :
    Triple ge fe f P (.Sifthenelse a s1 s2) R := by
  refine triple_if ge fe f P Assn.no P R a s1 s2 (fun e le m hP => ?_)
    (fun _ _ _ _ h => False.elim h) h2
  obtain ⟨v, hev, hbv⟩ := hg e le m hP
  exact ⟨v, false, hev, hbv, by simpa using hP⟩

/-- `break`. -/
theorem triple_break (ge fe f) (P : Assn) :
    Triple ge fe f P .Sbreak
      { normal := Assn.no, brk := P, cont := Assn.no, ret := fun _ _ => False } := by
  intro k e le m hP
  exact ⟨.Break e le m, Steps.refl _, hP⟩

/-- `continue`. -/
theorem triple_continue (ge fe f) (P : Assn) :
    Triple ge fe f P .Scontinue
      { normal := Assn.no, brk := Assn.no, cont := P, ret := fun _ _ => False } := by
  intro k e le m hP
  exact ⟨.Continue e le m, Steps.refl _, hP⟩

/-- `return e`.  The locals are freed, as `step_return_1` requires. -/
theorem triple_return (ge fe f) (P : Assn) (Ret : Val → Mem → Prop) (a : Expr)
    (h : ∀ e le m, P e le m →
      ∃ v v' m', EvalExpr ge e le m a v
                 ∧ Cop.semCast v (typeof a) f.fn_return m = some v'
                 ∧ Mem.freeList m (blocksOfEnv ge.genv_cenv e) = some m'
                 ∧ Ret v' m') :
    Triple ge fe f P (.Sreturn (some a))
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  intro k e le m hP
  obtain ⟨v, v', m', hev, hcast, hfree, hRet⟩ := h e le m hP
  exact ⟨.Return v' m',
         Steps.one (Step.return_1 f a k e le m v v' m' hev hcast hfree), hRet⟩

/-- An unreachable statement: anything holds of code the precondition rules out. -/
theorem triple_vacuous (ge fe f) (s : Stmt) (R : ExitConds) :
    Triple ge fe f Assn.no s R := fun _ _ _ _ h => False.elim h

/-- A statement that can only fall through (`Sset`, `Sassign`, `Sskip`) placed
    where the surrounding code also allows abnormal exits. -/
theorem triple_fallthrough (ge fe f) (P Q : Assn) (s : Stmt) (R : ExitConds)
    (h : Triple ge fe f P s (.only Q)) (hn : ∀ e le m, Q e le m → R.normal e le m) :
    Triple ge fe f P s R :=
  triple_conseq ge fe f h (fun _ _ _ x => x) hn
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-! ## The loop rule

`Sloop s1 s2` runs `s1`; if that falls through *or* continues, it runs `s2` and
repeats.  A `break` in either part leaves the loop.  Note there is no rule for
`continue` inside `s2` — `Kloop2` has no continue transition — so `s2`'s continue
postcondition must be unsatisfiable.

Termination comes from the `Nat` index: each trip must re-establish the invariant
at a strictly smaller index. -/

theorem triple_loop (ge fe f) (R : ExitConds) (I J : Nat → Assn) (s1 s2 : Stmt)
    (hbody : ∀ n, Triple ge fe f (I n) s1
      { normal := J n, brk := R.normal, cont := J n, ret := R.ret })
    (hincr : ∀ n, Triple ge fe f (J n) s2
      { normal := fun e le m => ∃ n' , n' < n ∧ I n' e le m,
        brk := R.normal, cont := Assn.no, ret := R.ret }) :
    ∀ n, Triple ge fe f (I n) (.Sloop s1 s2) R := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k e le m hI
    have hstart : SStep ge fe (.State f (.Sloop s1 s2) k e le m)
                           (.State f s1 (.Kloop1 s1 s2 k) e le m) :=
      Step.loop f s1 s2 k e le m
    obtain ⟨o1, hs1, hR1⟩ := hbody n (.Kloop1 s1 s2 k) e le m hI
    -- s1 either falls through / continues (run s2), breaks (leave), or returns
    cases o1 with
    | Normal e1 le1 m1 =>
        have hto2 : SStep ge fe (.State f .Sskip (.Kloop1 s1 s2 k) e1 le1 m1)
                             (.State f s2 (.Kloop2 s1 s2 k) e1 le1 m1) :=
          Step.skip_or_continue_loop1 f s1 s2 k e1 le1 m1 .Sskip (.inl rfl)
        obtain ⟨o2, hs2, hR2⟩ := hincr n (.Kloop2 s1 s2 k) e1 le1 m1 hR1
        cases o2 with
        | Normal e2 le2 m2 =>
            obtain ⟨n', hlt, hI'⟩ := hR2
            obtain ⟨o, hs, hR⟩ := ih n' hlt k e2 le2 m2 hI'
            refine ⟨o, ?_, hR⟩
            refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
            refine Steps.step _ _ _ hto2 (Steps.trans hs2 ?_)
            exact Steps.step _ _ _ (Step.skip_loop2 f s1 s2 k e2 le2 m2) hs
        | Break e2 le2 m2 =>
            refine ⟨.Normal e2 le2 m2, ?_, hR2⟩
            refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
            refine Steps.step _ _ _ hto2 (Steps.trans hs2 ?_)
            exact Steps.one (Step.break_loop2 f s1 s2 k e2 le2 m2)
        | Continue e2 le2 m2 => exact False.elim hR2
        | Return v m2 =>
            refine ⟨.Return v m2, ?_, hR2⟩
            refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
            exact Steps.step _ _ _ hto2 hs2
        | Goto _ _ _ _ => exact False.elim hR2
    | Continue e1 le1 m1 =>
        have hto2 : SStep ge fe (.State f .Scontinue (.Kloop1 s1 s2 k) e1 le1 m1)
                             (.State f s2 (.Kloop2 s1 s2 k) e1 le1 m1) :=
          Step.skip_or_continue_loop1 f s1 s2 k e1 le1 m1 .Scontinue (.inr rfl)
        obtain ⟨o2, hs2, hR2⟩ := hincr n (.Kloop2 s1 s2 k) e1 le1 m1 hR1
        cases o2 with
        | Normal e2 le2 m2 =>
            obtain ⟨n', hlt, hI'⟩ := hR2
            obtain ⟨o, hs, hR⟩ := ih n' hlt k e2 le2 m2 hI'
            refine ⟨o, ?_, hR⟩
            refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
            refine Steps.step _ _ _ hto2 (Steps.trans hs2 ?_)
            exact Steps.step _ _ _ (Step.skip_loop2 f s1 s2 k e2 le2 m2) hs
        | Break e2 le2 m2 =>
            refine ⟨.Normal e2 le2 m2, ?_, hR2⟩
            refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
            refine Steps.step _ _ _ hto2 (Steps.trans hs2 ?_)
            exact Steps.one (Step.break_loop2 f s1 s2 k e2 le2 m2)
        | Continue e2 le2 m2 => exact False.elim hR2
        | Return v m2 =>
            refine ⟨.Return v m2, ?_, hR2⟩
            refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
            exact Steps.step _ _ _ hto2 hs2
        | Goto _ _ _ _ => exact False.elim hR2
    | Break e1 le1 m1 =>
        refine ⟨.Normal e1 le1 m1, ?_, hR1⟩
        refine Steps.trans (Steps.one hstart) (Steps.trans hs1 ?_)
        exact Steps.one (Step.break_loop1 f s1 s2 k e1 le1 m1)
    | Return v m1 =>
        refine ⟨.Return v m1, ?_, hR1⟩
        exact Steps.trans (Steps.one hstart) hs1
    | Goto _ _ _ _ => exact False.elim hR1

end CC
