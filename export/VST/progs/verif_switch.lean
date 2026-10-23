/-
  Port of VST's `progs/verif_switch.v`: the functions `twice` and `f` of
  `vst/progs/switch.c`, written with `switch` statements, meet their
  specifications.

  VST's specifications:

      DECLARE _twice
       WITH n : Z
       PRE [ _n OF tint ] PROP (Int.min_signed <= n+n <= Int.max_signed)
         LOCAL (temp _n (Vint (Int.repr n))) SEP ()
       POST [ tint ] PROP () LOCAL (temp ret_temp (Vint (Int.repr (n+n)))) SEP ().

      DECLARE _f
       WITH x : Z
       PRE [ _x OF tuint ] PROP (0 <= x <= Int.max_unsigned)
         LOCAL (temp _x (Vint (Int.repr x))) SEP ()
       POST [ tint ] PROP () LOCAL (temp ret_temp (Vint (Int.repr 1))) SEP ().

  Here the argument of `twice` is any 32-bit integer `x` and the result is the
  machine sum `x + x` (`Int.add x x`), so VST's no-overflow precondition is not
  needed.  Each `case` is selected by `Sep.triple_switch_const` at the value of
  the scrutinee (`Int.unsigned x`), and the local states are given exactly
  (`Sep.At`, `CCLib.logic.ExactTemps`).
-/
import VST.progs.switch
import CCLib
open CC CC.Sep CC.HProp
open Switch

namespace VST.Verif.Switch

/-- `twice_spec` -/
def twiceSpec (x : Integers.Int) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint x] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (Integers.Int.add x x) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- `f_spec` -/
def fSpec (x : Integers.Int) : Sep.FunSpec where
  tyargs := [tuint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint x] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (Integers.Int.repr 1) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- A 32-bit integer is determined by its unsigned value. -/
theorem eq_of_unsigned {x : Integers.Int} {c : Z}
    (h : Integers.Int.unsigned x = c) : x = Integers.Int.repr c := by
  rw [← h, Integers.Int.repr_unsigned]

theorem semSwitchArg_int (x : Integers.Int) :
    Cop.semSwitchArg (.Vint x) tint = some (Integers.Int.unsigned x) := rfl

theorem semSwitchArg_uint (x : Integers.Int) :
    Cop.semSwitchArg (.Vint x) tuint = some (Integers.Int.unsigned x) := rfl

/-! ## `twice` -/

section
variable (ge : CGenv)

/-- The cases of the `switch` of `twice`. -/
def twiceCases : LStmts := match f_twice.fn_body with
  | .Ssequence (.Sswitch _ sl) _ => sl
  | _ => .LSnil

theorem twice_body_eq : f_twice.fn_body =
    .Ssequence (.Sswitch (.Etempvar _n tint) twiceCases) (.Sreturn (some (.Etempvar _n tint))) :=
  rfl

/-- The local state after the `switch`: `n = x + x`. -/
def TwiceDone (x : Integers.Int) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _n = some (.Vint (Integers.Int.add x x)) ∧ hp = Heap.emp

/-- `n = a; break;`, the rest of the cases being unreachable. -/
theorem set_break (L : TempEnv) (a : Expr) (v : Val) (rest : Stmt) (Q : Sep.Assn)
    (hev : ∀ m, EvalExpr ge emptyEnv L m a v)
    (hQ : ∀ e le hp, At (L.set _n v) e le hp → Q e le hp) :
    Sep.Triple ge (FunctionEntry2 ge) f_twice (At L)
      (.Ssequence (.Ssequence (.Sset _n a) .Sbreak) rest)
      { normal := Q, brk := Q, cont := Sep.Assn.no, ret := (twiceSpec x).post } := by
  refine Sep.triple_seq ge _ f_twice _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_twice _ _)
  refine Sep.triple_seq_only ge _ f_twice (triple_set_at ge _ L _n a v hev) ?_
  exact Sep.triple_conseq ge _ f_twice (Sep.triple_break ge _ f_twice _) (fun _ _ _ x => x)
    (fun _ _ _ x => x.elim) hQ (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

/-- **`twice` satisfies `twice_spec`** (VST's `body_twice`): it returns `x + x`
    for every 32-bit `x`. -/
theorem twice_satisfies (x : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_twice) (twiceSpec x) [.Vint x] := by
  let L : TempEnv := (createUndefTemps f_twice.fn_temps).set _n (.Vint x)
  refine satisfies_at ge f_twice _ _ L (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) ?_
  rw [twice_body_eq]
  refine Sep.triple_seq ge _ f_twice _ (TwiceDone x) _ _ _ ?_ ?_
  · refine Sep.triple_switch_const ge _ f_twice _ _ _ _ (Integers.Int.unsigned x) ?_
      (fun e le hp m hP _ => ?_)
    · have hdone : ∀ v, v = Integers.Int.add x x → ∀ e le hp,
          At (L.set _n (.Vint v)) e le hp → TwiceDone x e le hp := by
        rintro v rfl e le hp ⟨he, rfl, hh⟩
        exact ⟨he, PTree.gss _ _ _, hh⟩
      by_cases h0 : Integers.Int.unsigned x = 0
      · -- case 0: return 0;
        have hx : x = Integers.Int.repr 0 := eq_of_unsigned h0
        rw [h0]
        refine Sep.triple_seq ge _ f_twice _ Sep.Assn.no _ _ _ ?_
          (Sep.triple_vacuous ge _ f_twice _ _)
        refine Sep.triple_conseq ge _ f_twice
          (triple_return_at ge _ L _ _ (.Vint (Integers.Int.add x x))
            (fun _ => EvalExpr.Econst_int _ tint) (fun m => by subst hx; exact semCast_int m _))
          (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
          (fun _ _ _ x => x.elim) (fun _ _ x => x)
      by_cases h1 : Integers.Int.unsigned x = 1
      · -- case 1: n = 2; break;
        have hx : x = Integers.Int.repr 1 := eq_of_unsigned h1
        rw [h1]
        exact set_break ge L _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)
          (hdone _ (by subst hx; decide))
      by_cases h2 : Integers.Int.unsigned x = 4294967295
      · -- case -1: n = -2; break;
        have hx : x = Integers.Int.repr 4294967295 :=
          eq_of_unsigned h2
        rw [h2]
        exact set_break ge L _ _ _ _ (fun m => EvalExpr.Eunop _ _ _ _ _
          (EvalExpr.Econst_int _ tint) (semUnop_neg_int m _)) (hdone _ (by subst hx; decide))
      by_cases h3 : Integers.Int.unsigned x = 3
      · -- case 3: n = n + 0; then (falling through) default: n = n + n; break;
        have hx : x = Integers.Int.repr 3 := eq_of_unsigned h3
        rw [h3]
        refine Sep.triple_seq_only ge _ f_twice (triple_set_at ge _ L _n _ _ (fun _ =>
          EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ rfl)
            (EvalExpr.Econst_int _ tint) (semBinop_add_int _ _ _ _))) ?_
        exact set_break ge _ _ _ _ _ (fun _ =>
          EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ (PTree.gss _ _ _))
            (EvalExpr.Etempvar _ tint _ (PTree.gss _ _ _)) (semBinop_add_int _ _ _ _))
          (fun e le hp ⟨he, hle, hh⟩ => ⟨he, by rw [hle, PTree.gss, hx]; decide, hh⟩)
      · -- default: n = n + n; break;
        have hsel : selectSwitch (Integers.Int.unsigned x) twiceCases
            = .LScons none (.Ssequence (.Sset _n (.Ebinop .Oadd (.Etempvar _n tint)
                (.Etempvar _n tint) tint)) .Sbreak) .LSnil := by
          simp only [selectSwitch, twiceCases, f_twice, selectSwitchCase, selectSwitchDefault]
          simp [Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]
        rw [hsel]
        exact set_break ge L _ _ _ _ (fun _ =>
          EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ rfl)
            (EvalExpr.Etempvar _ tint _ rfl) (semBinop_add_int _ _ _ _)) (hdone _ rfl)
    · obtain ⟨rfl, rfl, _⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ tint _ rfl, semSwitchArg_int x⟩
  · -- return n;
    refine Sep.triple_return ge _ f_twice _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hn, hh⟩ := h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _n tint _ hn, semCast_int m _, ?_, ⟨rfl, hh⟩,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

/-! ## `f` -/

/-- The exits of the body of `f`: only `return` is possible. -/
def fR (x : Integers.Int) : Sep.ExitConds :=
  { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := (fSpec x).post }

/-- The cases of the `switch` of `f`. -/
def fCases : LStmts := match f_f.fn_body with
  | .Sswitch _ sl => sl
  | _ => .LSnil

theorem f_body_eq : f_f.fn_body = .Sswitch (.Etempvar _x tuint) fCases := rfl

/-- `return 1;` -/
theorem f_ret1 (x : Integers.Int) (L : TempEnv) :
    Sep.Triple ge (FunctionEntry2 ge) f_f (At L)
      (.Sreturn (some (.Econst_int (Integers.Int.repr 1) tint))) (fR x) :=
  Sep.triple_conseq ge _ f_f
    (triple_return_at ge _ L _ _ (.Vint (Integers.Int.repr 1))
      (fun _ => EvalExpr.Econst_int _ tint) (fun m => semCast_int m _))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim)
    (fun _ _ _ h => h.elim) (fun _ _ h => h)

/-- `return 1; ...`: whatever follows the `return` is unreachable. -/
theorem f_ret1_seq (x : Integers.Int) (L : TempEnv) (s : Stmt) :
    Sep.Triple ge (FunctionEntry2 ge) f_f (At L)
      (.Ssequence (.Sreturn (some (.Econst_int (Integers.Int.repr 1) tint))) s) (fR x) :=
  Sep.triple_seq ge _ f_f _ Sep.Assn.no _ _ _ (f_ret1 ge x L)
    (Sep.triple_vacuous ge _ f_f _ _)

/-- `skip; s` (an empty `case` falling through). -/
theorem f_skip_seq (x : Integers.Int) (L : TempEnv) (s : Stmt)
    (h : Sep.Triple ge (FunctionEntry2 ge) f_f (At L) s (fR x)) :
    Sep.Triple ge (FunctionEntry2 ge) f_f (At L) (.Ssequence .Sskip s) (fR x) :=
  Sep.triple_seq ge _ f_f _ (At L) _ _ _
    (Sep.triple_fallthrough ge _ f_f _ _ _ _ (Sep.triple_skip ge _ f_f _) (fun _ _ _ h => h)) h

/-- **`f` satisfies `f_spec`** (VST's `body_f`): it returns `1` for every
    32-bit unsigned `x`. -/
theorem f_satisfies (x : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_f) (fSpec x) [.Vint x] := by
  let L : TempEnv := (createUndefTemps f_f.fn_temps).set _x (.Vint x)
  refine satisfies_at ge f_f _ _ L (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) ?_
  rw [f_body_eq]
  refine Sep.triple_switch_const ge _ f_f _ (fR x) _ _ (Integers.Int.unsigned x) ?_
    (fun e le hp m hP _ => ?_)
  · by_cases h1 : Integers.Int.unsigned x = 1
    · rw [h1]
      exact Sep.triple_seq ge _ f_f _ Sep.Assn.no _ _ _ (f_ret1_seq ge x L _)
        (Sep.triple_vacuous ge _ f_f _ _)
    by_cases h2 : Integers.Int.unsigned x = 2
    · rw [h2]
      exact f_skip_seq ge x L _ (f_skip_seq ge x L _ (Sep.triple_seq ge _ f_f _ Sep.Assn.no _ _ _
        (f_ret1_seq ge x L _) (Sep.triple_vacuous ge _ f_f _ _)))
    by_cases h3 : Integers.Int.unsigned x = 3
    · rw [h3]
      exact f_skip_seq ge x L _ (Sep.triple_seq ge _ f_f _ Sep.Assn.no _ _ _
        (f_ret1_seq ge x L _) (Sep.triple_vacuous ge _ f_f _ _))
    by_cases h4 : Integers.Int.unsigned x = 4294967295
    · rw [h4]
      exact Sep.triple_seq ge _ f_f _ Sep.Assn.no _ _ _ (f_ret1_seq ge x L _)
        (Sep.triple_vacuous ge _ f_f _ _)
    · have hsel : selectSwitch (Integers.Int.unsigned x) fCases
          = .LScons none (.Sreturn (some (.Econst_int (Integers.Int.repr 1) tint))) .LSnil := by
        simp only [selectSwitch, fCases, f_f, selectSwitchCase, selectSwitchDefault]
        simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
      rw [hsel]
      exact f_ret1_seq ge x L _
  · obtain ⟨rfl, rfl, _⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ tuint _ rfl, semSwitchArg_uint x⟩

end

end VST.Verif.Switch
