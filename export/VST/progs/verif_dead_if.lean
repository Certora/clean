/-
  Port of VST's `progs/verif_dead_if.v`: the functions `f` and `g` of
  `vst/progs/dead_if.c` meet their specifications.

  VST's specifications only ask for the parameters to be `int`s and promise
  nothing (`POST [ tint ] PROP() LOCAL() SEP()`); the Rocq proofs exercise the
  `deadvars` tactic.  The specifications below are stronger: they also give the
  returned value.

  The triples of `CCLib.logic` are *total*-correctness triples, while VST's
  `semax` is partial.  `f` always terminates, so `f_satisfies` is the full
  port of `body_f`.  `g` loops forever as soon as `x + 1 > 0` (the loop body
  never changes `a`), so `g_satisfies` covers the runs where the loop is not
  entered (`x + 1 ≤ 0`, wrapping arithmetic), and `g_diverges` shows that the
  other runs indeed never return: from the call, the program runs forever
  without an event.

  The local states are described by giving the temporary environment exactly
  (`Sep.At`, `CCLib.logic.ExactTemps`): the bodies are straight-line, so each
  assignment just pushes a `PTree.set`.
-/
import VST.progs.dead_if
import CCLib
open CC CC.Sep CC.HProp
open Dead_if

namespace VST.Verif.DeadIf

/-! ## Facts about the generated program -/

/-- The side conditions of `function_entry2` for `f` and `g`. -/
theorem entry_wf_f :
    listNorepet (varNames f_f.fn_vars)
    ∧ listNorepet (varNames f_f.fn_params)
    ∧ listDisjoint (varNames f_f.fn_params) (varNames f_f.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem entry_wf_g :
    listNorepet (varNames f_g.fn_vars)
    ∧ listNorepet (varNames f_g.fn_params)
    ∧ listDisjoint (varNames f_g.fn_params) (varNames f_g.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The temporaries on entry (`f` and `g` have the same parameters and
    temporaries). -/
def le0 (x y z : Integers.Int) : TempEnv :=
  ((((createUndefTemps f_f.fn_temps).set _x (.Vint x)).set _y (.Vint y)).set _z (.Vint z))

theorem temps_eq : f_g.fn_temps = f_f.fn_temps := rfl

/-- The prefix `d = 2; b = 1; c = 0; a = x + 1;` shared by `f` and `g`. -/
def le4 (x y z : Integers.Int) : TempEnv :=
  ((((le0 x y z).set _d (.Vint (Integers.Int.repr 2))).set _b (.Vint (Integers.Int.repr 1))).set
    _c (.Vint (Integers.Int.repr 0))).set _a (.Vint (Integers.Int.add x (Integers.Int.repr 1)))

/-- `a > 0`, i.e. `x + 1 > 0` in wrapping signed arithmetic. -/
def cond (x : Integers.Int) : Bool :=
  Integers.Int.lt (Integers.Int.repr 0) (Integers.Int.add x (Integers.Int.repr 1))

/-! ## The specifications -/

/-- The precondition: three `int` arguments, no memory. -/
def preArgs (x y z : Integers.Int) : List Val → HProp := fun vargs hp =>
  vargs = [.Vint x, .Vint y, .Vint z] ∧ hp = Heap.emp

/-- `f_spec`, with the returned value: `x + y` if `x + 1 > 0`, `z + x`
    otherwise. -/
def fResult (x y z : Integers.Int) : Integers.Int :=
  if cond x then Integers.Int.add (Integers.Int.repr 0) (Integers.Int.add x y)
  else Integers.Int.add z x

def fSpec (x y z : Integers.Int) : Sep.FunSpec where
  tyargs := [tint, tint, tint]
  tyres := tint
  cc := cc_default
  pre := preArgs x y z
  post := fun v hp => v = .Vint (fResult x y z) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- `g_spec` on the runs that return: the result is `c + b = 0 + 1`. -/
def gSpec (x y z : Integers.Int) : Sep.FunSpec where
  tyargs := [tint, tint, tint]
  tyres := tint
  cc := cc_default
  pre := preArgs x y z
  post := fun v hp => v = .Vint (Integers.Int.add (Integers.Int.repr 0) (Integers.Int.repr 1))
    ∧ hp = Heap.emp
  measure := fun _ => 0

/-! ## Evaluation helpers -/

section
variable (ge : CGenv) (fe : EntryRel)

theorem eval_add_temps (e : Env) (L : TempEnv) (m : Mem) (i j : Ident) (vi vj : Integers.Int)
    (hi : L.get i = some (.Vint vi)) (hj : L.get j = some (.Vint vj)) :
    EvalExpr ge e L m (.Ebinop .Oadd (.Etempvar i tint) (.Etempvar j tint) tint)
      (.Vint (Integers.Int.add vi vj)) :=
  EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ hi)
    (EvalExpr.Etempvar _ tint _ hj) (semBinop_add_int _ _ _ _)

/-- `d = 2; b = 1; c = 0; a = x + 1;` -/
theorem prefix_triple {func : Function} (x y z : Integers.Int) (rest : Stmt) (R : Sep.ExitConds)
    (h : Sep.Triple ge fe func (At (le4 x y z)) rest R) :
    Sep.Triple ge fe func (At (le0 x y z))
      (.Ssequence (.Sset _d (.Econst_int (Integers.Int.repr 2) tint))
        (.Ssequence (.Sset _b (.Econst_int (Integers.Int.repr 1) tint))
          (.Ssequence (.Sset _c (.Econst_int (Integers.Int.repr 0) tint))
            (.Ssequence (.Sset _a (.Ebinop .Oadd (.Etempvar _x tint)
                (.Econst_int (Integers.Int.repr 1) tint) tint)) rest)))) R := by
  refine Sep.triple_seq_only ge fe func (Sep.triple_set_at ge fe _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
  refine Sep.triple_seq_only ge fe func (Sep.triple_set_at ge fe _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
  refine Sep.triple_seq_only ge fe func (Sep.triple_set_at ge fe _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
  refine Sep.triple_seq_only ge fe func (Sep.triple_set ge fe func _ _ _ _
    (fun e le hp m hP _ => ?_)) h
  obtain ⟨he, rfl, hh⟩ := hP
  exact ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _x tint _ rfl)
    (EvalExpr.Econst_int _ tint) (semBinop_add_int _ _ _ _), he, rfl, hh⟩

/-- The guard `a > 0`. -/
theorem eval_cond (e : Env) (m : Mem) (x y z : Integers.Int) :
    EvalExpr ge e (le4 x y z) m
      (.Ebinop .Ogt (.Etempvar _a tint) (.Econst_int (Integers.Int.repr 0) tint) tint)
      (Val.ofBool (cond x)) :=
  EvalExpr.Ebinop .Ogt _ _ _ _ _ _ (EvalExpr.Etempvar _a tint _ rfl)
    (EvalExpr.Econst_int _ tint) (semBinop_gt_int _ _ _ _)

/-- `return c + b;` -/
theorem return_triple {func : Function} (L : TempEnv) (vb vc : Integers.Int)
    (hfn : func.fn_return = tint)
    (hb : L.get _b = some (.Vint vb)) (hc : L.get _c = some (.Vint vc)) :
    Sep.Triple ge fe func (At L)
      (.Sreturn (some (.Ebinop .Oadd (.Etempvar _c tint) (.Etempvar _b tint) tint)))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := fun v hp => v = .Vint (Integers.Int.add vc vb) ∧ hp = Heap.emp } := by
  refine Sep.triple_return ge fe func _ _ _ (fun e le hp m h _ => ?_)
  obtain ⟨he, hle, hh⟩ := h
  refine ⟨_, _, m, hp, eval_add_temps ge e le m _ _ _ _ (hle ▸ hc) (hle ▸ hb), ?_, ?_, ⟨rfl, hh⟩,
    fun _ hdj hag => ⟨hdj, hag⟩⟩
  · rw [hfn]; exact semCast_int m _
  · rw [he]; exact freeList_emptyEnv _ _

end

/-! ## `f` -/

section
variable (ge : CGenv)

theorem f_satisfies (x y z : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_f) (fSpec x y z)
      [.Vint x, .Vint y, .Vint z] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf_f
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_f _ _
    (At (le0 x y z)) (fun m => ⟨le0 x y z,
      FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
      fun hp hpre => ⟨rfl, rfl, hpre.2⟩⟩) ?_
  refine prefix_triple ge _ x y z _ _ ?_
  refine Sep.triple_seq ge _ f_f _ (fun e le hp =>
      ∃ vb vc, At le e le hp ∧ le.get _b = some (.Vint vb) ∧ le.get _c = some (.Vint vc)
        ∧ Integers.Int.add vc vb = fResult x y z) _ _ _ ?_ ?_
  · cases hc : cond x
    · refine Sep.triple_if_false ge _ f_f _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
      · obtain ⟨_, rfl, _⟩ := hP
        exact ⟨_, eval_cond ge e m x y z, by rw [hc]; exact boolVal_ofBool_int m false⟩
      · refine Sep.triple_seq_only ge _ f_f (Sep.triple_set_at ge _ _ _ _ (.Vint x) (fun _ => EvalExpr.Etempvar _ tint _ rfl)) ?_
        refine Sep.triple_fallthrough ge _ f_f _ _ _ _
          (Sep.triple_set_at ge _ _ _ _ (.Vint z) (fun _ => EvalExpr.Etempvar _ tint _ rfl)) (fun e le hp h => ?_)
        obtain ⟨he, rfl, hh⟩ := h
        exact ⟨x, z, ⟨he, rfl, hh⟩, rfl, rfl, by simp [fResult, hc]⟩
    · refine Sep.triple_if_true ge _ f_f _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
      · obtain ⟨_, rfl, _⟩ := hP
        exact ⟨_, eval_cond ge e m x y z, by rw [hc]; exact boolVal_ofBool_int m true⟩
      · refine Sep.triple_fallthrough ge _ f_f _ _ _ _
          (Sep.triple_set ge _ f_f _ (At ((le4 x y z).set _b (.Vint (Integers.Int.add x y))))
            _ _ (fun e le hp m hP _ => ?_)) (fun e le hp h => ?_)
        · obtain ⟨he, rfl, hh⟩ := hP
          exact ⟨_, eval_add_temps ge e _ m _ _ x y rfl rfl, he, rfl, hh⟩
        · obtain ⟨he, rfl, hh⟩ := h
          exact ⟨Integers.Int.add x y, Integers.Int.repr 0, ⟨he, rfl, hh⟩, rfl, rfl,
            by simp [fResult, hc]⟩
  · refine Sep.triple_exists ge _ f_f _ _ _ (fun vb => ?_)
    refine Sep.triple_exists ge _ f_f _ _ _ (fun vc => ?_)
    intro k e le hp hf m hd hag hP
    obtain ⟨⟨he, -, hh⟩, hb, hc, hres⟩ := hP
    obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
      return_triple (func := f_f) ge _ le vb vc rfl hb hc k e le hp hf m hd hag ⟨he, rfl, hh⟩
    refine ⟨o, hp', hs, hd', hag', ?_⟩
    cases o <;> try exact hR
    obtain ⟨hv, hh'⟩ := hR
    exact ⟨hv.trans (by rw [hres]), hh'⟩

end

/-! ## `g` -/

/-- The loop of `g`: `while (a > 0) b = x;`. -/
def gGuard : Expr :=
  .Ebinop .Ogt (.Etempvar _a tint) (.Econst_int (Integers.Int.repr 0) tint) tint
def gIf : Stmt := .Sifthenelse gGuard .Sskip .Sbreak
def gSetB : Stmt := .Sset _b (.Etempvar _x tint)
def gLoop : Stmt := .Sloop (.Ssequence gIf gSetB) .Sskip
def gRet : Stmt := .Sreturn (some (.Ebinop .Oadd (.Etempvar _c tint) (.Etempvar _b tint) tint))

theorem g_body_eq : f_g.fn_body =
    .Ssequence (.Sset _d (.Econst_int (Integers.Int.repr 2) tint))
      (.Ssequence (.Sset _b (.Econst_int (Integers.Int.repr 1) tint))
        (.Ssequence (.Sset _c (.Econst_int (Integers.Int.repr 0) tint))
          (.Ssequence (.Sset _a (.Ebinop .Oadd (.Etempvar _x tint)
              (.Econst_int (Integers.Int.repr 1) tint) tint))
            (.Ssequence gLoop gRet)))) := rfl

section
variable (ge : CGenv)

/-- **`g` meets `g_spec` when the loop is not entered** (`x + 1 ≤ 0` in
    wrapping signed arithmetic): it returns `0 + 1`. -/
theorem g_satisfies (x y z : Integers.Int) (hc : cond x = false) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_g) (gSpec x y z)
      [.Vint x, .Vint y, .Vint z] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf_g
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_g _ _
    (At (le0 x y z)) (fun m => ⟨le0 x y z,
      FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
      fun hp hpre => ⟨rfl, rfl, hpre.2⟩⟩) ?_
  rw [g_body_eq]
  refine prefix_triple ge _ x y z _ _ ?_
  refine Sep.triple_seq ge _ f_g _ (At (le4 x y z)) _ _ _ ?_
    (return_triple ge _ _ _ _ rfl rfl rfl)
  -- the loop exits at once
  refine Sep.triple_loop ge _ f_g _ (fun _ => At (le4 x y z)) (fun _ => Sep.Assn.no) _ _
    (fun _ => ?_) (fun _ => Sep.triple_vacuous ge _ f_g _ _) 0
  refine Sep.triple_seq ge _ f_g _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_g _ _)
  refine Sep.triple_if_false ge _ f_g _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
  · obtain ⟨_, rfl, _⟩ := hP
    exact ⟨_, eval_cond ge e m x y z, by rw [hc]; exact boolVal_ofBool_int m false⟩
  · exact Sep.triple_conseq ge _ f_g (Sep.triple_break ge _ f_g _) (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x.elim)

/-- One trip around the loop of `g` when `a > 0`: back at the loop, with `b`
    set to `x`, and `a`, `x` unchanged. -/
theorem g_loop_cycle (x : Integers.Int) (hc : cond x = true) (K : Cont) (le : TempEnv) (m : Mem)
    (ha : le.get _a = some (.Vint (Integers.Int.add x (Integers.Int.repr 1))))
    (hx : le.get _x = some (.Vint x)) :
    Smallstep.Plus (Step ge (FunctionEntry2 ge)) (.State f_g gLoop K emptyEnv le m) E0
      (.State f_g gLoop K emptyEnv (le.set _b (.Vint x)) m) := by
  have hev : EvalExpr ge emptyEnv le m gGuard (Val.ofBool true) := by
    rw [← hc]
    exact EvalExpr.Ebinop .Ogt _ _ _ _ _ _ (EvalExpr.Etempvar _a tint _ ha)
      (EvalExpr.Econst_int _ tint) (semBinop_gt_int _ _ _ _)
  exact steps_plus (Step.loop _ _ _ _ _ _ _) <|
    .step _ _ _ (Step.seq _ _ _ _ _ _ _) <|
    .step _ _ _ (Step.ifthenelse _ _ _ _ _ _ _ _ _ true hev (boolVal_ofBool_int m true)) <|
    .step _ _ _ (Step.skip_seq _ _ _ _ _ _) <|
    .step _ _ _ (Step.set _ _ _ _ _ _ _ _ (EvalExpr.Etempvar _x tint _ hx)) <|
    .step _ _ _ (Step.skip_or_continue_loop1 _ _ _ _ _ _ _ _ (Or.inl rfl)) <|
    .one (Step.skip_loop2 _ _ _ _ _ _ _)

/-- **`g` diverges when `a > 0`** (`x + 1 > 0`): from the call, the program
    runs forever without an event, so no run returns.  (VST's partial-correctness
    `body_g` covers these runs vacuously.) -/
theorem g_diverges (x y z : Integers.Int) (hc : cond x = true) (k : Cont) (m : Mem) :
    Smallstep.ForeverSilent (Step ge (FunctionEntry2 ge))
      (.Callstate (.Internal f_g) [.Vint x, .Vint y, .Vint z] k m) := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf_g
  let Inv : State → Prop := fun s =>
    s = .Callstate (.Internal f_g) [.Vint x, .Vint y, .Vint z] k m
    ∨ ∃ le, s = .State f_g gLoop (.Kseq gRet k) emptyEnv le m
      ∧ le.get _a = some (.Vint (Integers.Int.add x (Integers.Int.repr 1)))
      ∧ le.get _x = some (.Vint x)
  refine Smallstep.forever_silent_of_plus Inv (fun s hs => ?_) (Or.inl rfl)
  rcases hs with rfl | ⟨le, rfl, ha, hx⟩
  · -- the call: function entry, then `d = 2; b = 1; c = 0; a = x + 1;`
    refine ⟨_, ?_, Or.inr ⟨le4 x y z, rfl, rfl, rfl⟩⟩
    have hent : FunctionEntry2 ge f_g [.Vint x, .Vint y, .Vint z] m emptyEnv (le0 x y z) m :=
      FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl
    refine steps_plus (Step.internal_function _ _ _ _ _ _ _ hent) ?_
    rw [g_body_eq]
    exact .step _ _ _ (Step.seq _ _ _ _ _ _ _) <|
      .step _ _ _ (Step.set _ _ _ _ _ _ _ _ (EvalExpr.Econst_int _ tint)) <|
      .step _ _ _ (Step.skip_seq _ _ _ _ _ _) <|
      .step _ _ _ (Step.seq _ _ _ _ _ _ _) <|
      .step _ _ _ (Step.set _ _ _ _ _ _ _ _ (EvalExpr.Econst_int _ tint)) <|
      .step _ _ _ (Step.skip_seq _ _ _ _ _ _) <|
      .step _ _ _ (Step.seq _ _ _ _ _ _ _) <|
      .step _ _ _ (Step.set _ _ _ _ _ _ _ _ (EvalExpr.Econst_int _ tint)) <|
      .step _ _ _ (Step.skip_seq _ _ _ _ _ _) <|
      .step _ _ _ (Step.seq _ _ _ _ _ _ _) <|
      .step _ _ _ (Step.set _ _ _ _ _ _ _ _ (EvalExpr.Ebinop .Oadd _ _ _ _ _ _
        (EvalExpr.Etempvar _x tint _ rfl) (EvalExpr.Econst_int _ tint)
        (semBinop_add_int _ _ _ _))) <|
      .step _ _ _ (Step.skip_seq _ _ _ _ _ _) <|
      .one (Step.seq _ _ _ _ _ _ _)
  · -- one more trip around the loop
    refine ⟨_, g_loop_cycle ge x hc _ le m ha hx, Or.inr ⟨_, rfl, ?_, ?_⟩⟩
    · exact (PTree.gso _ _ _ _ (by decide)).trans ha
    · exact (PTree.gso _ _ _ _ (by decide)).trans hx

end

end VST.Verif.DeadIf
