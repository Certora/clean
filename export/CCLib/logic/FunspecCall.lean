/-
  First part of the function-specification layer (split from `CCLib.logic.Funspec`): the call rule and the passage from a body triple to a function specification.
-/
import CCLib.logic.SepHoare

namespace CC
namespace Sep

open HProp

/-- On a *call* continuation, `callCont` is the identity.  This is what makes one
    `SatisfiesAt` serve internal callees (whose body returns to `callCont k`) and
    external ones (where `step_external_function` returns to `k`) alike. -/
theorem callCont_of_isCallCont {k : Cont} (h : isCallCont k = true) : callCont k = k := by
  cases k <;> simp_all [isCallCont, callCont]

/-- A function specification.  `pre`/`post` are heap-only: a callee cannot mention
    its caller's environment or temporaries. -/
structure FunSpec where
  tyargs : List Ty
  tyres : Ty
  cc : CallConv
  pre : List Val → HProp
  post : Val → HProp
  /-- Termination measure on the arguments; see the header. -/
  measure : List Val → Nat

/-- A specification for (some of) the program's functions, keyed by block. -/
abbrev SpecTable := Block → Option FunSpec

/-- `fd` meets `S` at *these* arguments: from a state whose fragment satisfies the
    precondition, the call runs to a `Returnstate` whose fragment satisfies the
    postcondition, with any disjoint frame carried through untouched. -/
def SatisfiesAt (ge : CGenv) (fe : EntryRel) (fd : FunDef) (S : FunSpec)
    (vargs : List Val) : Prop :=
  ∀ k m hp hf, isCallCont k = true → S.pre vargs hp → Heap.disjoint hp hf →
    Heap.Agrees (Heap.union hp hf) m →
    ∃ v m' hp',
      Steps (SStep ge fe) (.Callstate fd vargs k m) (.Returnstate v k m')
      ∧ S.post v hp' ∧ Heap.disjoint hp' hf ∧ Heap.Agrees (Heap.union hp' hf) m'

/-- `fd` meets `S` at every argument list. -/
def Satisfies (ge : CGenv) (fe : EntryRel) (fd : FunDef) (S : FunSpec) : Prop :=
  ∀ vargs, SatisfiesAt ge fe fd S vargs

/-! ## The call rule

Derived from the same frame discipline as everything else: the callee's
`SatisfiesAt` takes an arbitrary frame, so the caller's *other* resources (`h2`)
pass through untouched.  That is the whole reason a call rule is worth having in a
separation logic and not in a plain Hoare logic. -/

/-- The call rule at the actual arguments: the callee need only meet `S` at the
    arguments it is called with (`SatisfiesAt`), which is what a recursive call
    can supply (see `satisfies_rec`). -/
theorem triple_call_at (ge fe f) (S : FunSpec) (optid : Option Ident)
    (a : Expr) (al : List Expr) (P Q : Assn) (b : Block) (fd : FunDef)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hsplit : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
        ∃ vargs h1 h2,
          Heap.disjoint h1 h2 ∧ hp = Heap.union h1 h2
          ∧ EvalExpr ge e le m a (.Vptr b Integers.Ptrofs.zero)
          ∧ EvalExprlist ge e le m al S.tyargs vargs
          ∧ S.pre vargs h1
          ∧ SatisfiesAt ge fe fd S vargs
          ∧ (∀ v h1', S.post v h1' → Heap.disjoint h1' h2 →
                Q e (setOpttemp optid v le) (Heap.union h1' h2))) :
    Triple ge fe f P (.Scall optid a al) (.only Q) := by
  intro k e le hp hf m hd hag hP
  obtain ⟨vargs, h1, h2, hd12, heq, hevf, hevl, hpre, hspec, hQ⟩ :=
    hsplit e le hp m hP (Heap.Agrees_union_left hag)
  subst heq
  rw [Heap.disjoint_union_left] at hd
  -- the caller's other resources join the frame for the duration of the call
  have hd1 : Heap.disjoint h1 (Heap.union h2 hf) := by
    rw [Heap.disjoint_union_right]; exact ⟨hd12, hd.1⟩
  have hag1 : Heap.Agrees (Heap.union h1 (Heap.union h2 hf)) m := by
    rw [← Heap.union_assoc]; exact hag
  obtain ⟨v, m', h1', hcall, hpost, hd1', hag1'⟩ :=
    hspec (.Kcall optid f e le k) m h1 (Heap.union h2 hf) rfl hpre hd1 hag1
  rw [Heap.disjoint_union_right] at hd1'
  refine ⟨.Normal e (setOpttemp optid v le) m', Heap.union h1' h2, ?_, ?_, ?_, ?_⟩
  · -- enter the call, run it, then pop the `Kcall` frame
    refine Steps.step _ _ _
      (Step.call f optid a al k e le m S.tyargs S.tyres S.cc _ vargs fd
        hclass hevf hevl hfind hty) ?_
    -- the callee lands exactly where `step_returnstate` expects it
    exact Steps.trans hcall
      (Steps.one (Step.returnstate v optid f e le k m'))
  · rw [Heap.disjoint_union_left]; exact ⟨hd1'.2, hd.2⟩
  · show Heap.Agrees (Heap.union (Heap.union h1' h2) hf) m'
    rw [Heap.union_assoc]; exact hag1'
  · exact hQ v h1' hpost hd1'.1

theorem triple_call (ge fe f) (S : FunSpec) (optid : Option Ident)
    (a : Expr) (al : List Expr) (P Q : Assn) (b : Block) (fd : FunDef)
    (hspec : ∀ vargs, SatisfiesAt ge fe fd S vargs)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hsplit : ∀ e le hp m, P e le hp → Heap.Agrees hp m →
        ∃ vargs h1 h2,
          Heap.disjoint h1 h2 ∧ hp = Heap.union h1 h2
          ∧ EvalExpr ge e le m a (.Vptr b Integers.Ptrofs.zero)
          ∧ EvalExprlist ge e le m al S.tyargs vargs
          ∧ S.pre vargs h1
          ∧ (∀ v h1', S.post v h1' → Heap.disjoint h1' h2 →
                Q e (setOpttemp optid v le) (Heap.union h1' h2))) :
    Triple ge fe f P (.Scall optid a al) (.only Q) :=
  triple_call_at ge fe f S optid a al P Q b fd hfind hty hclass (fun e le hp m hP hag => by
    obtain ⟨vargs, h1, h2, hd, heq, hevf, hevl, hpre, hQ⟩ := hsplit e le hp m hP hag
    exact ⟨vargs, h1, h2, hd, heq, hevf, hevl, hpre, hspec vargs, hQ⟩)

/-- **Recursive functions with a `WITH` clause.**  VST's specifications are
    families `S w` indexed by the `WITH` variables.  The functions `fd w` meet
    their specifications `S w` if each body meets `S w` assuming the calls at
    smaller `w'` (for a measure `μ`) meet theirs.  For a single recursive
    function `fd` is constant; mutual recursion takes `W` to range over the
    functions as well (e.g. `Bool × Nat` for `even`/`odd`). -/
theorem satisfies_rec {W : Type} (ge : CGenv) (fe : EntryRel) (fd : W → FunDef)
    (S : W → FunSpec) (μ : W → Nat)
    (h : ∀ w, (∀ w', μ w' < μ w → ∀ vargs, SatisfiesAt ge fe (fd w') (S w') vargs) →
      ∀ vargs, SatisfiesAt ge fe (fd w) (S w) vargs) :
    ∀ w vargs, SatisfiesAt ge fe (fd w) (S w) vargs := by
  suffices H : ∀ n w, μ w = n → ∀ vargs, SatisfiesAt ge fe (fd w) (S w) vargs from
    fun w => H _ w rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hw
    exact h w (fun w' hlt => ih (μ w') (hw ▸ hlt) w' rfl)

/-! ## From a body triple to a specification -/

/-- Deriving `SatisfiesAt` from a triple for the body, for a function with no
    block-scoped variables — so `function_entry` leaves memory alone.  This is the
    pattern `is_sorted_call` follows by hand in `examples/IsSortedReal.lean`, generalized.

    For a function *with* `fn_vars` the entry allocates, and the fresh block has
    to be turned into owned cells; that is the resource-transfer step deferred in
    Phase 7.4. -/
theorem satisfies_internal_noVars (ge fe f) (S : FunSpec) (vargs : List Val)
    (Pbody : Assn)
    (hentry : ∀ m : Mem, ∃ le : TempEnv, fe f vargs m emptyEnv le m
                ∧ ∀ hp, S.pre vargs hp → Pbody emptyEnv le hp)
    (body : Triple ge fe f Pbody f.fn_body
        { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post }) :
    SatisfiesAt ge fe (.Internal f) S vargs := by
  intro k m hp hf hk hpre hd hag
  obtain ⟨le, hent, himp⟩ := hentry m
  obtain ⟨o, hp', hs, hd', hag', hR⟩ := body k emptyEnv le hp hf m hd hag (himp hp hpre)
  cases o with
  | Normal _ _ _ => exact False.elim hR
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  -- an unresolved jump out of a function body: the body triple's `goto`
  -- condition is `no`, so this cannot happen.  A body that *does* jump must have
  -- had its labels resolved by `Sep.triple_body_goto` first.
  | Goto _ _ _ _ => exact False.elim hR
  | Return v m' =>
      refine ⟨v, m', hp', ?_, hR, hd', hag'⟩
      -- the body returns to `callCont k`; on a call continuation that *is* `k`
      have hs' : Steps (SStep ge fe) (.State f f.fn_body k emptyEnv le m)
                   (.Returnstate v (callCont k) m') := hs
      rw [callCont_of_isCallCont hk] at hs'
      exact Steps.step _ _ _
        (Step.internal_function f vargs k m emptyEnv le m hent) hs'

/-- **D5 — a function *with* block-scoped locals meets its spec.**  The
    generalisation of `satisfies_internal_noVars`, and what
    `compress2`/`uncompress2` need: both hold a `z_stream` on the stack.

    `hentry` is the entry step packaged as an obligation: running
    `function_entry` yields an environment, temporaries, a memory, **and a
    fragment `hl` for the freshly allocated locals**, with the body's
    precondition holding of the caller's resources *plus* the locals.
    `CC.allocVariables_resources` is what discharges it.

    The body's `ret` condition is `S.post` alone — no locals — because the
    `return` step frees them: `Sep.triple_return` already carries
    `Mem.freeList … = some m'` as a hypothesis, discharged at the use site by
    `CC.freeList_isSome_of_rangePerm` and `CC.undefBytes_rangePerm`.  So the
    locals are *consumed* by the return, and this theorem needs to say nothing
    more about them. -/
theorem satisfies_internal (ge fe f) (S : FunSpec) (vargs : List Val)
    (Pbody : Assn)
    (hentry : ∀ (m : Mem) (hp hf : Heap), S.pre vargs hp → Heap.disjoint hp hf →
        Heap.Agrees (Heap.union hp hf) m →
        ∃ (e : Env) (le : TempEnv) (m1 : Mem) (hl : Heap),
          fe f vargs m e le m1
          ∧ Heap.disjoint (Heap.union hp hl) hf
          ∧ Heap.Agrees (Heap.union (Heap.union hp hl) hf) m1
          ∧ Pbody e le (Heap.union hp hl))
    (body : Triple ge fe f Pbody f.fn_body
        { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post }) :
    SatisfiesAt ge fe (.Internal f) S vargs := by
  intro k m hp hf hk hpre hd hag
  obtain ⟨e, le, m1, hl, hent, hd1, hag1, hPb⟩ := hentry m hp hf hpre hd hag
  obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
    body k e le (Heap.union hp hl) hf m1 hd1 hag1 hPb
  cases o with
  | Normal _ _ _ => exact False.elim hR
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  -- an unresolved jump out of a function body: the body triple's `goto`
  -- condition is `no`, so this cannot happen.  A body that *does* jump must have
  -- had its labels resolved by `Sep.triple_body_goto` first.
  | Goto _ _ _ _ => exact False.elim hR
  | Return v m' =>
      refine ⟨v, m', hp', ?_, hR, hd', hag'⟩
      have hs' : Steps (SStep ge fe) (.State f f.fn_body k e le m1)
                   (.Returnstate v (callCont k) m') := hs
      rw [callCont_of_isCallCont hk] at hs'
      exact Steps.step _ _ _
        (Step.internal_function f vargs k m e le m1 hent) hs'

/-- **Resolving a forward `goto`: a function whose body jumps to a label.**

    This is `satisfies_internal` plus label resolution, and it must live at this
    level rather than as a `Triple` rule: `Step.goto` lands at `callCont k`, a
    `Triple` quantifies over *all* `k`, and only here — where `SatisfiesAt`
    supplies `isCallCont k` — are the two the same continuation.

    `hfind` gives the label's landing site as a function `kcont` of the ambient
    continuation.  For a label at the **top level** of the body — `inflate`'s
    `inf_leave:` — `kcont` is the identity.  For a label *inside* a sequence or
    loop, `findLabel` rebuilds the frames above it, so `kcont` adds them; `hkc`
    then says those frames do not change `callCont`, which holds by `rfl` for
    every frame `findLabel` can add (`Kseq`, `Kloop1`, `Kloop2`, `Kswitch`).
    Both facts compute on a concrete body.

    The target is verified with `goto := no`, so it cannot jump again — that is
    what makes this the *forward* rule, and it is the restriction a backward jump
    (`inflate_fast`'s `dolen`/`dodist`) has to lift with a measure. -/
theorem satisfies_internal_goto (ge fe f) (S : FunSpec) (vargs : List Val)
    (Pbody G : Assn) (lbl : Ident) (starget : Stmt) (kcont : Cont → Cont)
    (hentry : ∀ (m : Mem) (hp hf : Heap), S.pre vargs hp → Heap.disjoint hp hf →
        Heap.Agrees (Heap.union hp hf) m →
        ∃ (e : Env) (le : TempEnv) (m1 : Mem) (hl : Heap),
          fe f vargs m e le m1
          ∧ Heap.disjoint (Heap.union hp hl) hf
          ∧ Heap.Agrees (Heap.union (Heap.union hp hl) hf) m1
          ∧ Pbody e le (Heap.union hp hl))
    (hbody : Triple ge fe f Pbody f.fn_body
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post,
        goto := fun l => if l = lbl then G else Assn.no })
    (hfind : ∀ kk : Cont, findLabel lbl f.fn_body kk = some (starget, kcont kk))
    (hkc : ∀ kk : Cont, callCont (kcont kk) = callCont kk)
    (htarget : Triple ge fe f G starget
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post }) :
    SatisfiesAt ge fe (.Internal f) S vargs := by
  intro k m hp hf hk hpre hd hag
  have hck : callCont k = k := callCont_of_isCallCont hk
  obtain ⟨e, le, m1, hl, hent, hd1, hag1, hPb⟩ := hentry m hp hf hpre hd hag
  obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
    hbody k e le (Heap.union hp hl) hf m1 hd1 hag1 hPb
  -- the body either returns, or jumps to `lbl` and the target returns
  cases o with
  | Normal _ _ _ => exact False.elim hR
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  | Return v m' =>
      refine ⟨v, m', hp', ?_, hR, hd', hag'⟩
      have hs' : Steps (SStep ge fe) (.State f f.fn_body k e le m1)
                   (.Returnstate v (callCont k) m') := hs
      rw [hck] at hs'
      exact Steps.step _ _ _ (Step.internal_function f vargs k m e le m1 hent) hs'
  | Goto lbl' e' le' m' =>
      by_cases hl' : lbl' = lbl
      · subst hl'
        have hG : G e' le' hp' := by
          have hx : (if lbl' = lbl' then G else Assn.no) e' le' hp' := hR
          rwa [if_pos rfl] at hx
        -- the landing site: `callCont k = k`, so the jump stays under `kcont k`
        have hst : gotoTarget f k lbl' e' le' m'
            = .State f starget (kcont k) e' le' m' := by
          unfold gotoTarget
          rw [hck, hfind k]
        obtain ⟨o2, hp2, hs2, hd2, hag2, hR2⟩ :=
          htarget (kcont k) e' le' hp' hf m' hd' hag' hG
        cases o2 with
        | Normal _ _ _ => exact False.elim hR2
        | Break _ _ _ => exact False.elim hR2
        | Continue _ _ _ => exact False.elim hR2
        | Goto _ _ _ _ => exact False.elim hR2
        | Return v m'' =>
            refine ⟨v, m'', hp2, ?_, hR2, hd2, hag2⟩
            have hs2' : Steps (SStep ge fe) (.State f starget (kcont k) e' le' m')
                          (.Returnstate v (callCont (kcont k)) m'') := hs2
            rw [hkc k, hck] at hs2'
            refine Steps.step _ _ _
              (Step.internal_function f vargs k m e le m1 hent) ?_
            exact Steps.trans (hst ▸ hs) hs2'
      · -- a jump to any other label is unsatisfiable: the body's condition is `no`
        have hx : (if lbl' = lbl then G else Assn.no) e' le' hp' := hR
        rw [if_neg hl'] at hx
        exact False.elim hx

/-! ### When the label's target does not stand alone

`findLabel` returns the *labelled statement*, with whatever follows it pushed onto
the continuation.  `satisfies_internal_goto` above verifies that statement with
`normal := Assn.no`, i.e. it must return or jump on every path -- so it does not
apply when the labelled statement falls through and the rest of the work happens
from the continuation.  That is zlib's shape: `inflate`'s `inf_leave:` labels only
the `RESTORE()` do-while, and the whole cleanup tail sits under a `Kseq`
(`fv/InflateAST.lean:label_resolves`).

`LandsReturn` is the obligation such a target actually owes -- *from the landing
state, reach a `Returnstate` at the ambient call continuation* -- and it composes
forward through the pushed frames, so no step-inversion (hence no determinism
hypothesis) is needed. -/

/-- From the landing state `.State f s kland`, reach `.Returnstate _ kret`.

    `kland` is where `findLabel` puts control; `kret` is where the caller expects
    the function to return.  They differ by exactly the frames `findLabel`
    rebuilt, which the composition lemmas below peel one at a time. -/
def LandsReturn (ge : CGenv) (fe : EntryRel) (f : Function) (P : Assn) (s : Stmt)
    (kland kret : Cont) (Ret : Val → HProp) : Prop :=
  ∀ e le hp hf m,
    Heap.disjoint hp hf → Heap.Agrees (Heap.union hp hf) m → P e le hp →
    ∃ v m' hp',
      Steps (SStep ge fe) (.State f s kland e le m) (.Returnstate v kret m')
      ∧ Heap.disjoint hp' hf ∧ Heap.Agrees (Heap.union hp' hf) m' ∧ Ret v hp'

/-- A statement that can only return already lands: a `Triple` holds at every
    continuation, and its `Return` outcome is a `Returnstate` at `callCont`. -/
theorem landsReturn_of_triple (ge fe f) {P : Assn} {s : Stmt} {Ret : Val → HProp}
    (k : Cont)
    (h : Triple ge fe f P s
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := Ret }) :
    LandsReturn ge fe f P s k (callCont k) Ret := by
  intro e le hp hf m hd hag hP
  obtain ⟨o, hp', hs, hd', hag', hR⟩ := h k e le hp hf m hd hag hP
  cases o with
  | Normal _ _ _ => exact False.elim hR
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  | Goto _ _ _ _ => exact False.elim hR
  | Return v m' => exact ⟨v, m', hp', hs, hd', hag', hR⟩

/-- **Peel one `Kseq`.**  The labelled statement runs under `Kseq s₂ k`, falls
    through, and `s₂` carries on at `k`.  `s₁` is verified with `.only`, which is
    right: a `RESTORE()`-style prologue neither returns nor jumps. -/
theorem landsReturn_seq (ge fe f) (P Q : Assn) {Ret : Val → HProp}
    (s1 s2 : Stmt) (k kret : Cont)
    (h1 : Triple ge fe f P s1 (.only Q))
    (h2 : LandsReturn ge fe f Q s2 k kret Ret) :
    LandsReturn ge fe f P s1 (.Kseq s2 k) kret Ret := by
  intro e le hp hf m hd hag hP
  obtain ⟨o1, hp1, hs1, hd1, hag1, hR1⟩ := h1 (.Kseq s2 k) e le hp hf m hd hag hP
  cases o1 with
  | Break _ _ _ => exact False.elim hR1
  | Continue _ _ _ => exact False.elim hR1
  | Return _ _ => exact False.elim hR1
  | Goto _ _ _ _ => exact False.elim hR1
  | Normal e' le' m' =>
      obtain ⟨v, m'', hp2, hs2, hd2, hag2, hRet⟩ := h2 e' le' hp1 hf m' hd1 hag1 hR1
      refine ⟨v, m'', hp2, ?_, hd2, hag2, hRet⟩
      exact Steps.trans hs1 (Steps.step _ _ _ (Step.skip_seq f s2 k e' le' m') hs2)

/-- Weaken a landing obligation. -/
theorem landsReturn_conseq (ge fe f) {P P' : Assn} {s kland kret}
    {Ret Ret' : Val → HProp}
    (h : LandsReturn ge fe f P s kland kret Ret)
    (hP : ∀ e le hp, P' e le hp → P e le hp)
    (hr : ∀ v hp, Ret v hp → Ret' v hp) :
    LandsReturn ge fe f P' s kland kret Ret' := by
  intro e le hp hf m hd hag hP'
  obtain ⟨v, m', hp', hs, hd', hag', hRet⟩ := h e le hp hf m hd hag (hP e le hp hP')
  exact ⟨v, m', hp', hs, hd', hag', hr v hp' hRet⟩

/-- **The forward-`goto` rule, with the target stated where it actually lands.**

    `satisfies_internal_goto` is the special case in which the labelled statement
    itself returns; here the obligation is `LandsReturn` at `kcont kk`, which the
    lemmas above build by peeling the frames `findLabel` rebuilt. -/
theorem satisfies_internal_goto_lands (ge fe f) (S : FunSpec) (vargs : List Val)
    (Pbody G : Assn) (lbl : Ident) (starget : Stmt) (kcont : Cont → Cont)
    (hentry : ∀ (m : Mem) (hp hf : Heap), S.pre vargs hp → Heap.disjoint hp hf →
        Heap.Agrees (Heap.union hp hf) m →
        ∃ (e : Env) (le : TempEnv) (m1 : Mem) (hl : Heap),
          fe f vargs m e le m1
          ∧ Heap.disjoint (Heap.union hp hl) hf
          ∧ Heap.Agrees (Heap.union (Heap.union hp hl) hf) m1
          ∧ Pbody e le (Heap.union hp hl))
    (hbody : Triple ge fe f Pbody f.fn_body
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post,
        goto := fun l => if l = lbl then G else Assn.no })
    (hfind : ∀ kk : Cont, findLabel lbl f.fn_body kk = some (starget, kcont kk))
    (htarget : ∀ kk : Cont, isCallCont kk = true →
        LandsReturn ge fe f G starget (kcont kk) kk S.post) :
    SatisfiesAt ge fe (.Internal f) S vargs := by
  intro k m hp hf hk hpre hd hag
  have hck : callCont k = k := callCont_of_isCallCont hk
  obtain ⟨e, le, m1, hl, hent, hd1, hag1, hPb⟩ := hentry m hp hf hpre hd hag
  obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
    hbody k e le (Heap.union hp hl) hf m1 hd1 hag1 hPb
  cases o with
  | Normal _ _ _ => exact False.elim hR
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  | Return v m' =>
      refine ⟨v, m', hp', ?_, hR, hd', hag'⟩
      have hs' : Steps (SStep ge fe) (.State f f.fn_body k e le m1)
                   (.Returnstate v (callCont k) m') := hs
      rw [hck] at hs'
      exact Steps.step _ _ _ (Step.internal_function f vargs k m e le m1 hent) hs'
  | Goto lbl' e' le' m' =>
      by_cases hl' : lbl' = lbl
      · subst hl'
        have hG : G e' le' hp' := by
          have hx : (if lbl' = lbl' then G else Assn.no) e' le' hp' := hR
          rwa [if_pos rfl] at hx
        have hst : gotoTarget f k lbl' e' le' m'
            = .State f starget (kcont k) e' le' m' := by
          unfold gotoTarget; rw [hck, hfind k]
        obtain ⟨v, m'', hp2, hs2, hd2, hag2, hRet⟩ :=
          htarget k hk e' le' hp' hf m' hd' hag' hG
        refine ⟨v, m'', hp2, ?_, hRet, hd2, hag2⟩
        refine Steps.step _ _ _ (Step.internal_function f vargs k m e le m1 hent) ?_
        exact Steps.trans (hst ▸ hs) hs2
      · have hx : (if lbl' = lbl then G else Assn.no) e' le' hp' := hR
        rw [if_neg hl'] at hx
        exact False.elim hx

/-- **`inflate`'s shape**, packaged: the label covers a statement that falls
    through, and the rest of the function body follows it under one `Kseq`. -/
theorem satisfies_internal_goto_seq (ge fe f) (S : FunSpec) (vargs : List Val)
    (Pbody G Q : Assn) (lbl : Ident) (starget tail : Stmt)
    (hentry : ∀ (m : Mem) (hp hf : Heap), S.pre vargs hp → Heap.disjoint hp hf →
        Heap.Agrees (Heap.union hp hf) m →
        ∃ (e : Env) (le : TempEnv) (m1 : Mem) (hl : Heap),
          fe f vargs m e le m1
          ∧ Heap.disjoint (Heap.union hp hl) hf
          ∧ Heap.Agrees (Heap.union (Heap.union hp hl) hf) m1
          ∧ Pbody e le (Heap.union hp hl))
    (hbody : Triple ge fe f Pbody f.fn_body
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post,
        goto := fun l => if l = lbl then G else Assn.no })
    (hfind : ∀ kk : Cont, findLabel lbl f.fn_body kk = some (starget, .Kseq tail kk))
    (hlabelled : Triple ge fe f G starget (.only Q))
    (htail : Triple ge fe f Q tail
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post }) :
    SatisfiesAt ge fe (.Internal f) S vargs := by
  refine satisfies_internal_goto_lands ge fe f S vargs Pbody G lbl starget
    (fun kk => .Kseq tail kk) hentry hbody hfind (fun kk hkk => ?_)
  have hck : callCont kk = kk := callCont_of_isCallCont hkk
  refine landsReturn_seq ge fe f G Q starget tail kk kk hlabelled ?_
  have h := landsReturn_of_triple ge fe f (Ret := S.post) kk htail
  rwa [hck] at h

/-- **Resolving a `goto` that jumps BACKWARD, with a measure.**

    `inflate_fast`'s `dolen`/`dodist` jump *back* to a label above them, so the
    label's target can jump again and `satisfies_internal_goto` — whose target is
    verified with `goto := no` — does not apply.

    The fix is the discipline `Sep.triple_loop` and `Sep.closure` already use: the
    goto-assertion is **indexed by a `Nat` that must strictly decrease** before the
    label is re-entered.  Well-founded induction on it closes the loop.

    **How big is the measure in practice?  One.**  `dolen`/`dodist` are the
    two-level Huffman table lookup: a code longer than the root table's bits sends
    control back through `dolen` with `here` pointing into a *second-level* table,
    and a second-level entry is never itself a second-level pointer, because zlib
    builds exactly two levels.  So the jump fires at most once per symbol.

    That is worth stating plainly, because it relocates the difficulty: the
    *control-flow* rule below is cheap, while the *termination* argument is a
    data-structure invariant of `inflate_table`'s output — an obligation on
    inftrees.c that any refinement proof of `inflate_fast` needs anyway.  The
    measure is where that invariant gets cashed in. -/
theorem satisfies_internal_goto_measure (ge fe f) (S : FunSpec) (vargs : List Val)
    (Pbody : Assn) (Gm : Nat → Assn) (lbl : Ident) (starget : Stmt)
    (kcont : Cont → Cont)
    (hentry : ∀ (m : Mem) (hp hf : Heap), S.pre vargs hp → Heap.disjoint hp hf →
        Heap.Agrees (Heap.union hp hf) m →
        ∃ (e : Env) (le : TempEnv) (m1 : Mem) (hl : Heap),
          fe f vargs m e le m1
          ∧ Heap.disjoint (Heap.union hp hl) hf
          ∧ Heap.Agrees (Heap.union (Heap.union hp hl) hf) m1
          ∧ Pbody e le (Heap.union hp hl))
    -- the body may jump to `lbl` at any measure
    (hbody : Triple ge fe f Pbody f.fn_body
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post,
        goto := fun l => if l = lbl then (fun e le hp => ∃ n, Gm n e le hp)
                         else Assn.no })
    (hfind : ∀ kk : Cont, findLabel lbl f.fn_body kk = some (starget, kcont kk))
    (hkc : ∀ kk : Cont, callCont (kcont kk) = callCont kk)
    -- …and the target, at measure `n`, either returns or jumps again at a
    -- **strictly smaller** measure
    (htarget : ∀ n : Nat, Triple ge fe f (Gm n) starget
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := S.post,
        goto := fun l => if l = lbl then (fun e le hp => ∃ n', n' < n ∧ Gm n' e le hp)
                         else Assn.no }) :
    SatisfiesAt ge fe (.Internal f) S vargs := by
  intro k m hp hf hk hpre hd hag
  have hck : callCont k = k := callCont_of_isCallCont hk
  -- the target, re-entered at a decreasing measure, always reaches a Returnstate
  have key : ∀ (n : Nat) (e : Env) (le : TempEnv) (hp' : Heap) (m' : Mem),
      Gm n e le hp' → Heap.disjoint hp' hf →
      Heap.Agrees (Heap.union hp' hf) m' →
      ∃ v m'' hp'',
        Steps (SStep ge fe) (.State f starget (kcont k) e le m')
          (.Returnstate v k m'')
        ∧ S.post v hp'' ∧ Heap.disjoint hp'' hf
        ∧ Heap.Agrees (Heap.union hp'' hf) m'' := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro e le hp' m' hG hd' hag'
      obtain ⟨o, hp2, hs, hd2, hag2, hR⟩ :=
        htarget n (kcont k) e le hp' hf m' hd' hag' hG
      cases o with
      | Normal _ _ _ => exact False.elim hR
      | Break _ _ _ => exact False.elim hR
      | Continue _ _ _ => exact False.elim hR
      | Return v m'' =>
          refine ⟨v, m'', hp2, ?_, hR, hd2, hag2⟩
          have hs' : Steps (SStep ge fe) (.State f starget (kcont k) e le m')
                       (.Returnstate v (callCont (kcont k)) m'') := hs
          rwa [hkc k, hck] at hs'
      | Goto lbl' e2 le2 m2 =>
          by_cases hl' : lbl' = lbl
          · subst hl'
            obtain ⟨n', hlt, hG'⟩ : ∃ n', n' < n ∧ Gm n' e2 le2 hp2 := by
              have hx : (if lbl' = lbl' then
                          (fun e le hp => ∃ n', n' < n ∧ Gm n' e le hp) else Assn.no)
                        e2 le2 hp2 := hR
              rwa [if_pos rfl] at hx
            -- re-enter the label at the smaller measure
            obtain ⟨v, m'', hp3, hs3, hpost, hd3, hag3⟩ := ih n' hlt e2 le2 hp2 m2 hG' hd2 hag2
            refine ⟨v, m'', hp3, ?_, hpost, hd3, hag3⟩
            have hst : gotoTarget f (kcont k) lbl' e2 le2 m2
                = .State f starget (kcont k) e2 le2 m2 := by
              unfold gotoTarget; rw [hkc k, hck, hfind k]
            exact Steps.trans (hst ▸ hs) hs3
          · have hx : (if lbl' = lbl then
                        (fun e le hp => ∃ n', n' < n ∧ Gm n' e le hp) else Assn.no)
                      e2 le2 hp2 := hR
            rw [if_neg hl'] at hx
            exact False.elim hx
  -- now the body: it returns, or jumps to `lbl` at some measure
  obtain ⟨e, le, m1, hl, hent, hd1, hag1, hPb⟩ := hentry m hp hf hpre hd hag
  obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
    hbody k e le (Heap.union hp hl) hf m1 hd1 hag1 hPb
  cases o with
  | Normal _ _ _ => exact False.elim hR
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  | Return v m' =>
      refine ⟨v, m', hp', ?_, hR, hd', hag'⟩
      have hs' : Steps (SStep ge fe) (.State f f.fn_body k e le m1)
                   (.Returnstate v (callCont k) m') := hs
      rw [hck] at hs'
      exact Steps.step _ _ _ (Step.internal_function f vargs k m e le m1 hent) hs'
  | Goto lbl' e' le' m' =>
      by_cases hl' : lbl' = lbl
      · subst hl'
        obtain ⟨n, hG⟩ : ∃ n, Gm n e' le' hp' := by
          have hx : (if lbl' = lbl' then (fun e le hp => ∃ n, Gm n e le hp)
                     else Assn.no) e' le' hp' := hR
          rwa [if_pos rfl] at hx
        obtain ⟨v, m'', hp2, hs2, hpost, hd2, hag2⟩ := key n e' le' hp' m' hG hd' hag'
        refine ⟨v, m'', hp2, ?_, hpost, hd2, hag2⟩
        have hst : gotoTarget f k lbl' e' le' m'
            = .State f starget (kcont k) e' le' m' := by
          unfold gotoTarget; rw [hck, hfind k]
        refine Steps.step _ _ _ (Step.internal_function f vargs k m e le m1 hent) ?_
        exact Steps.trans (hst ▸ hs) hs2
      · have hx : (if lbl' = lbl then (fun e le hp => ∃ n, Gm n e le hp)
                   else Assn.no) e' le' hp' := hR
        rw [if_neg hl'] at hx
        exact False.elim hx

/-- The specifications a body may *use*: everything in the table whose measure at
    the actual arguments is strictly below `n`. -/
def Avail (ge : CGenv) (fe : EntryRel) (Δ : SpecTable) (n : Nat) : Prop :=
  ∀ (b : Block) (S : FunSpec) (fd : FunDef) (vargs : List Val),
    Δ b = some S →
    Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd →
    S.measure vargs < n →
    SatisfiesAt ge fe fd S vargs

/-- The per-function obligation: at every argument list, the body meets its spec
    *given* the smaller-measure callees. -/
def BodyOk (ge : CGenv) (fe : EntryRel) (Δ : SpecTable) (f : Function)
    (S : FunSpec) : Prop :=
  ∀ vargs, Avail ge fe Δ (S.measure vargs) → SatisfiesAt ge fe (.Internal f) S vargs

/-- **The closure theorem.**  If every function in the table meets its spec on the
    assumption that smaller-measure callees meet theirs, then all of them meet
    their specs outright.

    Mutual recursion is covered: the measure is global, so `iseven`/`isodd` both
    decrease it and neither needs the other to be "already done". -/
theorem closure (ge : CGenv) (fe : EntryRel) (Δ : SpecTable)
    (hbodies : ∀ (b : Block) (S : FunSpec) (fd : FunDef),
        Δ b = some S →
        Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd →
        ∃ fn, fd = .Internal fn ∧ BodyOk ge fe Δ fn S) :
    ∀ (b : Block) (S : FunSpec) (fd : FunDef) (vargs : List Val),
      Δ b = some S →
      Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd →
      SatisfiesAt ge fe fd S vargs := by
  suffices H : ∀ n b S fd vargs, Δ b = some S →
      Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd →
      S.measure vargs = n → SatisfiesAt ge fe fd S vargs by
    intro b S fd vargs h1 h2; exact H _ b S fd vargs h1 h2 rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro b S fd vargs h1 h2 hmeas
    obtain ⟨fn, hfd, hbody⟩ := hbodies b S fd h1 h2
    subst hfd
    refine hbody vargs (fun b' S' fd' vargs' h1' h2' hlt => ?_)
    exact ih (S'.measure vargs') (by omega) b' S' fd' vargs' h1' h2' rfl

/-- Corollary in the `Satisfies` (all-arguments) form. -/
theorem closure_satisfies (ge : CGenv) (fe : EntryRel) (Δ : SpecTable)
    (hbodies : ∀ (b : Block) (S : FunSpec) (fd : FunDef),
        Δ b = some S →
        Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd →
        ∃ fn, fd = .Internal fn ∧ BodyOk ge fe Δ fn S) :
    ∀ (b : Block) (S : FunSpec) (fd : FunDef),
      Δ b = some S →
      Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd →
      Satisfies ge fe fd S :=
  fun b S fd h1 h2 vargs => closure ge fe Δ hbodies b S fd vargs h1 h2

end Sep
end CC
