/-
  Port of VST's `progs/verif_fib.v`: the Fibonacci functions of
  `vst/progs/fib.c` meet `fib_spec`.

  VST's specification:

      DECLARE fun_id
       WITH n : Z
       PRE  [ tint ] PROP (0 <= n < 45) PARAMS (Vint (Int.repr n)) SEP ()
       POST [ tint ] PROP () RETURN (Vint (Int.repr (fib_of_Z n))) SEP ().

  `fibNat` is VST's `fib_of_nat`.  The bound `n < 45` keeps the Fibonacci
  numbers below `Int.max_signed`, so that VST's `int` additions do not
  overflow.  Here the result is stated as `Int.repr (fib n)`, i.e. modulo
  `2^32`, and `Int.repr` turns `+` into the machine addition (`repr_add`), so
  overflow is harmless and the only bound left is the one the loop counter
  needs: `n < 2^31`.  `fibLoopSpec` is thus VST's `fib_spec` with a weaker
  precondition.

  Ported: `body_fib_loop` (`fib_loop_satisfies`), with the counted-loop rule
  `Sep.triple_for_lt` (VST's `forward_for_simple_bound`), and
  `body_fib_loop_save_var` (`fib_loop_save_var_satisfies`), a count-down loop
  proved with the general loop rule `Sep.triple_loop` (VST's `forward_loop`),
  and `body_fib_rec` (`fib_rec_satisfies`), a doubly recursive function: the
  specification is the family `fib_spec n` (VST's `WITH n`), and the recursion
  is justified by `Sep.satisfies_rec` with the measure `n` (the triples are
  total-correctness triples, so a recursive call needs a decreasing measure).
-/
import VST.progs.fib
import CCLib
open CC CC.Sep CC.HProp
open Fib

namespace VST.Verif.Fib

/-- VST's `fib_of_nat`. -/
def fibNat : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibNat n + fibNat (n + 1)

/-- `fib n` as a 32-bit integer. -/
def fibInt (n : Nat) : Integers.Int := Integers.Int.repr (fibNat n)

theorem fibInt_add (n : Nat) :
    Integers.Int.add (fibInt n) (fibInt (n + 1)) = fibInt (n + 2) := by
  rw [fibInt, fibInt, repr_add, fibInt, fibNat]
  simp

/-- `fib_spec`: called with `n`, returns `fib n` (modulo `2^32`). -/
def fibSpec (n : Nat) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint (Integers.Int.repr n)] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (fibInt n) ∧ hp = Heap.emp
  measure := fun _ => 0

/-! ## `fib_loop` -/

section FibLoop

/-- The parts of the body. -/
def loopBody : Stmt :=
  .Ssequence (.Sset _a2 (.Ebinop .Oadd (.Etempvar _a0 tint) (.Etempvar _a1 tint) tint))
    (.Ssequence (.Sset _a0 (.Etempvar _a1 tint)) (.Sset _a1 (.Etempvar _a2 tint)))
def incrI : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)

theorem fib_loop_body_eq : f_fib_loop.fn_body =
    .Ssequence (.Sset _a0 (.Econst_int (Integers.Int.repr 0) tint))
      (.Ssequence (.Sset _a1 (.Econst_int (Integers.Int.repr 1) tint))
        (.Ssequence (.Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 0) tint))
            (forLoop _i _n loopBody incrI))
          (.Sreturn (some (.Etempvar _a0 tint))))) := rfl

variable (N : Nat)

/-- The loop invariant (VST's): after `j` iterations, `i = j`,
    `a0 = fib j` and `a1 = fib (j + 1)`. -/
def Inv (j : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _n = some (.Vint (Integers.Int.repr N))
  ∧ le.get _i = some (.Vint (Integers.Int.repr j))
  ∧ le.get _a0 = some (.Vint (fibInt j)) ∧ le.get _a1 = some (.Vint (fibInt (j + 1)))
  ∧ hp = Heap.emp

/-- After the body of iteration `j`: the pair has moved one step. -/
def Mid (j : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _n = some (.Vint (Integers.Int.repr N))
  ∧ le.get _i = some (.Vint (Integers.Int.repr j))
  ∧ le.get _a0 = some (.Vint (fibInt (j + 1))) ∧ le.get _a1 = some (.Vint (fibInt (j + 2)))
  ∧ hp = Heap.emp

variable (ge : CGenv) (fe : EntryRel)

/-- `a2 = a0 + a1; a0 = a1; a1 = a2;` -/
theorem body_triple (j : Nat) :
    Sep.Triple ge fe f_fib_loop (Inv N j) loopBody
      { normal := Mid N j, brk := Sep.Assn.no, cont := Mid N j, ret := fun _ _ => False } := by
  refine Sep.triple_fallthrough ge fe f_fib_loop _ (Mid N j) _ _ ?_ (fun _ _ _ x => x)
  refine Sep.triple_seq_only ge fe f_fib_loop (Q := fun e le hp => Inv N j e le hp
    ∧ le.get _a2 = some (.Vint (fibInt (j + 2)))) ?_ ?_
  · refine Sep.triple_set ge fe f_fib_loop _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hn, hi, h0, h1, hh⟩ := hP
    refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ h0)
      (EvalExpr.Etempvar _ tint _ h1) (semBinop_add_int _ _ _ _), ⟨he,
      (PTree.gso _ _ _ _ (by decide)).trans hn, (PTree.gso _ _ _ _ (by decide)).trans hi,
      (PTree.gso _ _ _ _ (by decide)).trans h0, (PTree.gso _ _ _ _ (by decide)).trans h1, hh⟩,
      ?_⟩
    rw [PTree.gss, fibInt_add]
  refine Sep.triple_seq_only ge fe f_fib_loop (Q := fun e le hp => e = emptyEnv
    ∧ le.get _n = some (.Vint (Integers.Int.repr N))
    ∧ le.get _i = some (.Vint (Integers.Int.repr j))
    ∧ le.get _a0 = some (.Vint (fibInt (j + 1)))
    ∧ le.get _a2 = some (.Vint (fibInt (j + 2))) ∧ hp = Heap.emp) ?_ ?_
  · refine Sep.triple_set ge fe f_fib_loop _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, hn, hi, _, h1, hh⟩, h2⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ tint _ h1, he, (PTree.gso _ _ _ _ (by decide)).trans hn,
      (PTree.gso _ _ _ _ (by decide)).trans hi, PTree.gss _ _ _,
      (PTree.gso _ _ _ _ (by decide)).trans h2, hh⟩
  · refine Sep.triple_set ge fe f_fib_loop _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hn, hi, h0, h2, hh⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ tint _ h2, he, (PTree.gso _ _ _ _ (by decide)).trans hn,
      (PTree.gso _ _ _ _ (by decide)).trans hi, (PTree.gso _ _ _ _ (by decide)).trans h0,
      PTree.gss _ _ _, hh⟩

/-- `i++` -/
theorem incr_triple (j : Nat) :
    Sep.Triple ge fe f_fib_loop (Mid N j) incrI (.only (Inv N (j + 1))) := by
  refine Sep.triple_set ge fe f_fib_loop _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨he, hn, hi, h0, h1, hh⟩ := hP
  exact ⟨_, eval_incr _ j hi, he, (PTree.gso _ _ _ _ (by decide)).trans hn, PTree.gss _ _ _,
    (PTree.gso _ _ _ _ (by decide)).trans h0, (PTree.gso _ _ _ _ (by decide)).trans h1, hh⟩

/-- **`fib_loop` satisfies `fib_spec`** (VST's `body_fib_loop`), for
    `0 ≤ n < 2^31`. -/
theorem fib_loop_satisfies (hN : (N : _root_.Int) < 2147483648) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fib_loop) (fibSpec N)
      [.Vint (Integers.Int.repr N)] := by
  refine satisfies_at ge f_fib_loop _ _
    ((createUndefTemps f_fib_loop.fn_temps).set _n (.Vint (Integers.Int.repr N)))
    (by decide) (by decide) (by decide) rfl rfl (fun _ h => h.2) ?_
  rw [fib_loop_body_eq]
  refine Sep.triple_seq_only ge _ f_fib_loop
    (triple_set_at ge _ _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
  refine Sep.triple_seq_only ge _ f_fib_loop
    (triple_set_at ge _ _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
  refine Sep.triple_seq ge _ f_fib_loop _ (Inv N N) _ _ _ ?_ ?_
  · refine Sep.triple_seq_only ge _ f_fib_loop
      (triple_set_at ge _ _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
    refine Sep.triple_conseq ge _ f_fib_loop
      (triple_for_lt ge _ f_fib_loop _i _n N hN (Inv N) (Mid N) loopBody incrI _
        (fun _ _ _ _ h => h.2.2.1) (fun _ _ _ _ h => h.2.1)
        (fun j _ => body_triple N ge _ j) (fun j _ => incr_triple N ge _ j) 0 (Nat.zero_le _))
      (fun e le hp h => ?_) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x.elim)
    obtain ⟨he, rfl, hh⟩ := h
    exact ⟨he, rfl, rfl, rfl, rfl, hh⟩
  · refine Sep.triple_return ge _ f_fib_loop _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, _, _, h0, _, hh⟩ := h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _a0 tint _ h0, semCast_int m _, ?_, ⟨rfl, hh⟩,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

end FibLoop

/-! ## `fib_loop_save_var` -/

section FibLoopSaveVar

theorem fibInt_sub (n : Nat) :
    Integers.Int.sub (fibInt (n + 2)) (fibInt n) = fibInt (n + 1) := by
  rw [fibInt, fibInt, repr_sub, fibInt, fibNat]
  congr 1
  show ((fibNat n + fibNat (n + 1) : Nat) : _root_.Int) - (fibNat n : _root_.Int)
    = (fibNat (n + 1) : _root_.Int)
  omega

/-- The parts of the body: `for (; n > 0; --n) { a1 = a0 + a1; a0 = a1 - a0; }`. -/
def svGuard : Expr :=
  .Ebinop .Ogt (.Etempvar _n tint) (.Econst_int (Integers.Int.repr 0) tint) tint
def svSetA1 : Stmt := .Sset _a1 (.Ebinop .Oadd (.Etempvar _a0 tint) (.Etempvar _a1 tint) tint)
def svSetA0 : Stmt := .Sset _a0 (.Ebinop .Osub (.Etempvar _a1 tint) (.Etempvar _a0 tint) tint)
def svDecr : Stmt :=
  .Sset _n (.Ebinop .Osub (.Etempvar _n tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def svLoop : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse svGuard .Sskip .Sbreak) (.Ssequence svSetA1 svSetA0)) svDecr

theorem fib_loop_save_var_body_eq : f_fib_loop_save_var.fn_body =
    .Ssequence (.Sset _a0 (.Econst_int (Integers.Int.repr 0) tint))
      (.Ssequence (.Sset _a1 (.Econst_int (Integers.Int.repr 1) tint))
        (.Ssequence svLoop (.Sreturn (some (.Etempvar _a0 tint))))) := rfl

variable (N : Nat)

/-- VST's invariant: after `j` iterations, `n = N - j`, `a0 = fib j`,
    `a1 = fib (j + 1)`. -/
def SvInv (j : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _n = some (.Vint (Integers.Int.repr ((N - j : Nat) : _root_.Int)))
  ∧ le.get _a0 = some (.Vint (fibInt j)) ∧ le.get _a1 = some (.Vint (fibInt (j + 1)))
  ∧ hp = Heap.emp

/-- After the body of iteration `j`. -/
def SvMid (j : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _n = some (.Vint (Integers.Int.repr ((N - j : Nat) : _root_.Int)))
  ∧ le.get _a0 = some (.Vint (fibInt (j + 1))) ∧ le.get _a1 = some (.Vint (fibInt (j + 2)))
  ∧ hp = Heap.emp

variable (ge : CGenv) (fe : EntryRel)

/-- `a1 = a0 + a1; a0 = a1 - a0;` -/
theorem sv_body_triple (j : Nat) :
    Sep.Triple ge fe f_fib_loop_save_var (SvInv N j) (.Ssequence svSetA1 svSetA0)
      (.only (SvMid N j)) := by
  refine Sep.triple_seq_only ge fe f_fib_loop_save_var (Q := fun e le hp => e = emptyEnv
    ∧ le.get _n = some (.Vint (Integers.Int.repr ((N - j : Nat) : _root_.Int)))
    ∧ le.get _a0 = some (.Vint (fibInt j)) ∧ le.get _a1 = some (.Vint (fibInt (j + 2)))
    ∧ hp = Heap.emp) ?_ ?_
  · refine Sep.triple_set ge fe f_fib_loop_save_var _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hn, h0, h1, hh⟩ := hP
    refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ h0)
      (EvalExpr.Etempvar _ tint _ h1) (semBinop_add_int _ _ _ _), he,
      (PTree.gso _ _ _ _ (by decide)).trans hn, (PTree.gso _ _ _ _ (by decide)).trans h0, ?_, hh⟩
    rw [PTree.gss, fibInt_add]
  · refine Sep.triple_set ge fe f_fib_loop_save_var _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hn, h0, h1, hh⟩ := hP
    refine ⟨_, EvalExpr.Ebinop .Osub _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ h1)
      (EvalExpr.Etempvar _ tint _ h0) (semBinop_sub_int _ _ _ _), he,
      (PTree.gso _ _ _ _ (by decide)).trans hn, ?_, (PTree.gso _ _ _ _ (by decide)).trans h1, hh⟩
    rw [PTree.gss, fibInt_sub]

/-- `--n` -/
theorem sv_decr_triple (j : Nat) (hj : j < N) :
    Sep.Triple ge fe f_fib_loop_save_var (SvMid N j) svDecr (.only (SvInv N (j + 1))) := by
  refine Sep.triple_set ge fe f_fib_loop_save_var _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨he, hn, h0, h1, hh⟩ := hP
  refine ⟨_, EvalExpr.Ebinop .Osub _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ hn)
    (EvalExpr.Econst_int _ tint) (semBinop_sub_int _ _ _ _), he, ?_,
    (PTree.gso _ _ _ _ (by decide)).trans h0, (PTree.gso _ _ _ _ (by decide)).trans h1, hh⟩
  rw [PTree.gss, repr_sub]
  congr 3
  show ((N - j : Nat) : _root_.Int) - 1 = ((N - (j + 1) : Nat) : _root_.Int)
  omega

/-- The loop, `k = n` iterations left, ends with `a0 = fib N`. -/
theorem sv_loop_triple (hN : (N : _root_.Int) < 2147483648) (k : Nat) :
    Sep.Triple ge fe f_fib_loop_save_var
      (fun e le hp => ∃ j, SvInv N j e le hp ∧ j ≤ N ∧ N - j = k) svLoop
      { normal := SvInv N N, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := fun _ _ => False } := by
  refine Sep.triple_loop ge fe f_fib_loop_save_var _
    (fun k e le hp => ∃ j, SvInv N j e le hp ∧ j ≤ N ∧ N - j = k)
    (fun k e le hp => ∃ j, SvMid N j e le hp ∧ j < N ∧ N - j = k) _ _
    (fun k => ?_) (fun k => ?_) k
  · refine Sep.triple_exists ge fe f_fib_loop_save_var _ _ _ (fun j => ?_)
    have hguard : ∀ e le hp m, SvInv N j e le hp → j ≤ N →
        EvalExpr ge e le m svGuard (Val.ofBool (decide (j < N))) := by
      intro e le hp m hI hj
      have h : EvalExpr ge e le m svGuard (Val.ofBool (Integers.Int.lt (Integers.Int.repr 0)
          (Integers.Int.repr ((N - j : Nat) : _root_.Int)))) :=
        EvalExpr.Ebinop .Ogt _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ hI.2.1)
          (EvalExpr.Econst_int _ tint) (semBinop_gt_int _ _ _ _)
      rw [lt_repr 0 _ (by omega) (by omega) (by omega) (by omega)] at h
      have : decide (0 < ((N - j : Nat) : _root_.Int)) = decide (j < N) :=
        decide_eq_decide.mpr (by omega)
      rwa [this] at h
    refine Sep.triple_seq ge fe f_fib_loop_save_var _
      (fun e le hp => SvInv N j e le hp ∧ j < N ∧ N - j = k) _ _ _ ?_ ?_
    · by_cases hjN : j < N
      · refine Sep.triple_if_true ge fe f_fib_loop_save_var _ _ _ _ _
          (fun e le hp m hP _ => ?_) ?_
        · refine ⟨_, hguard e le hp m hP.1 hP.2.1, ?_⟩
          simpa [hjN, svGuard, typeof] using boolVal_ofBool_int m true
        · exact Sep.triple_fallthrough ge fe f_fib_loop_save_var _ _ _ _
            (Sep.triple_skip ge fe f_fib_loop_save_var _)
            (fun e le hp h => ⟨h.1, hjN, h.2.2⟩)
      · refine Sep.triple_if_false ge fe f_fib_loop_save_var _ _ _ _ _
          (fun e le hp m hP _ => ?_) ?_
        · refine ⟨_, hguard e le hp m hP.1 hP.2.1, ?_⟩
          simpa [hjN, svGuard, typeof] using boolVal_ofBool_int m false
        · refine Sep.triple_conseq ge fe f_fib_loop_save_var
            (Sep.triple_break ge fe f_fib_loop_save_var _) (fun _ _ _ x => x)
            (fun _ _ _ x => x.elim) (fun e le hp h => ?_) (fun _ _ _ x => x.elim)
            (fun _ _ x => x.elim)
          obtain ⟨hI, hj, _⟩ := h
          have : j = N := by omega
          subst this
          exact hI
    · intro kk e le hp hf m hd hag ⟨hI, hj, hk⟩
      obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
        sv_body_triple N ge fe j kk e le hp hf m hd hag hI
      refine ⟨o, hp', hs, hd', hag', ?_⟩
      cases o with
      | Normal _ _ _ => exact ⟨j, hR, hj, hk⟩
      | _ => exact hR.elim
  · refine Sep.triple_exists ge fe f_fib_loop_save_var _ _ _ (fun j => ?_)
    intro kk e le hp hf m hd hag ⟨hM, hj, hk⟩
    obtain ⟨o, hp', hs, hd', hag', hR⟩ :=
      sv_decr_triple N ge fe j hj kk e le hp hf m hd hag hM
    refine ⟨o, hp', hs, hd', hag', ?_⟩
    cases o with
    | Normal _ _ _ => exact ⟨N - (j + 1), by omega, j + 1, hR, by omega, rfl⟩
    | _ => exact hR.elim

/-- **`fib_loop_save_var` satisfies `fib_spec`** (VST's
    `body_fib_loop_save_var`), for `0 ≤ n < 2^31`. -/
theorem fib_loop_save_var_satisfies (hN : (N : _root_.Int) < 2147483648) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fib_loop_save_var) (fibSpec N)
      [.Vint (Integers.Int.repr N)] := by
  refine satisfies_at ge f_fib_loop_save_var _ _
    ((createUndefTemps f_fib_loop_save_var.fn_temps).set _n (.Vint (Integers.Int.repr N)))
    (by decide) (by decide) (by decide) rfl rfl (fun _ h => h.2) ?_
  rw [fib_loop_save_var_body_eq]
  refine Sep.triple_seq_only ge _ f_fib_loop_save_var
    (triple_set_at ge _ _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
  refine Sep.triple_seq_only ge _ f_fib_loop_save_var
    (triple_set_at ge _ _ _ _ _ (fun _ => EvalExpr.Econst_int _ tint)) ?_
  refine Sep.triple_seq ge _ f_fib_loop_save_var _ (SvInv N N) _ _ _ ?_ ?_
  · refine Sep.triple_conseq ge _ f_fib_loop_save_var (sv_loop_triple N ge _ hN N)
      (fun e le hp h => ?_) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x.elim)
    obtain ⟨he, rfl, hh⟩ := h
    exact ⟨0, ⟨he, by simp; rfl, rfl, rfl, hh⟩, Nat.zero_le _, by omega⟩
  · refine Sep.triple_return ge _ f_fib_loop_save_var _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, _, h0, _, hh⟩ := h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _a0 tint _ h0, semCast_int m _, ?_, ⟨rfl, hh⟩,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

end FibLoopSaveVar

/-! ## `fib_rec` -/

section FibRec

/-- The parts of the body:
    `if (n == 0) return 0; if (n == 1) return 1;
     t1 = fib_rec(n - 2); t2 = fib_rec(n - 1); return t1 + t2;` -/
def recTest (c : Nat) : Expr :=
  .Ebinop .Oeq (.Etempvar _n tint) (.Econst_int (Integers.Int.repr c) tint) tint
def recIf (c : Nat) : Stmt :=
  .Sifthenelse (recTest c) (.Sreturn (some (.Econst_int (Integers.Int.repr c) tint))) .Sskip
def fibRecTy : Ty := .Tfunction [tint] tint cc_default
def recCall (t : Ident) (c : Nat) : Stmt :=
  .Scall (some t) (.Evar _fib_rec fibRecTy)
    [.Ebinop .Osub (.Etempvar _n tint) (.Econst_int (Integers.Int.repr c) tint) tint]
def recRet : Stmt :=
  .Sreturn (some (.Ebinop .Oadd (.Etempvar _t'1 tint) (.Etempvar _t'2 tint) tint))

theorem fib_rec_body_eq : f_fib_rec.fn_body =
    .Ssequence (recIf 0) (.Ssequence (recIf 1)
      (.Ssequence (.Ssequence (recCall _t'1 2) (recCall _t'2 1)) recRet)) := rfl

/-- The specifications `fib_spec n`, indexed by `n < 2^31` (VST's `WITH n`). -/
def W : Type := {n : Nat // (n : _root_.Int) < 2147483648}

variable (ge : CGenv)

/-- The temporaries on entry. -/
def recLe (n : Nat) : TempEnv :=
  (createUndefTemps f_fib_rec.fn_temps).set _n (.Vint (Integers.Int.repr n))

/-- `if (n == c) return c;`: returns `fib c` if `n = c`, falls through
    otherwise. -/
theorem rec_if_triple (n c : Nat) (L : TempEnv) (hn : (n : _root_.Int) < 2147483648)
    (hc : (c : _root_.Int) < 2147483648) (hfc : fibInt c = Integers.Int.repr c)
    (hL : L.get _n = some (.Vint (Integers.Int.repr n))) :
    Sep.Triple ge (FunctionEntry2 ge) f_fib_rec (At L) (recIf c)
      { normal := fun e le hp => At L e le hp ∧ n ≠ c, brk := Sep.Assn.no,
        cont := Sep.Assn.no, ret := (fibSpec n).post } := by
  have hev : ∀ m, EvalExpr ge emptyEnv L m (recTest c) (Val.ofBool (decide (n = c))) := by
    intro m
    have h := EvalExpr.Ebinop (ge := ge) (e := emptyEnv) (le := L) (m := m) .Oeq
      (.Etempvar _n tint) (.Econst_int (Integers.Int.repr c) tint) tint _ _ _
      (EvalExpr.Etempvar _ tint _ hL) (EvalExpr.Econst_int _ tint) (semBinop_eq_int _ _ _ _)
    rw [eq_repr (n : _root_.Int) (c : _root_.Int) (by omega) hn (by omega) hc] at h
    have : decide ((n : _root_.Int) = (c : _root_.Int)) = decide (n = c) :=
      decide_eq_decide.mpr (by omega)
    rwa [this] at h
  refine triple_if_at ge _ _ _ _ _ _ _ (decide (n = c)) hev
    (fun m => by simpa [recTest, typeof] using boolVal_ofBool_int m (decide (n = c))) ?_
  by_cases h : n = c
  · subst h
    simp only [decide_true, if_true]
    refine Sep.triple_conseq ge _ f_fib_rec
      (triple_return_at ge _ L _ (.Vint (Integers.Int.repr n)) (.Vint (fibInt n))
        (fun _ => EvalExpr.Econst_int _ tint) (fun m => by rw [hfc]; exact semCast_int m _))
      (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)
  · simp only [h, decide_false]
    exact Sep.triple_fallthrough ge _ f_fib_rec _ _ _ _ (Sep.triple_skip ge _ f_fib_rec _)
      (fun e le hp hP => ⟨hP, h⟩)

/-- `t = fib_rec(n - c);`, for `c ≤ n` and a callee that meets `fib_spec (n - c)`. -/
theorem rec_call_triple (b : Block)
    (hsym : Genv.findSymbol ge.genv_genv _fib_rec = some b)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero)
      = some (.Internal f_fib_rec))
    (n c : Nat) (t : Ident) (L : TempEnv) (hcn : c ≤ n)
    (hL : L.get _n = some (.Vint (Integers.Int.repr n)))
    (hIH : Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fib_rec) (fibSpec (n - c))
      [.Vint (Integers.Int.repr ((n - c : Nat) : _root_.Int))]) :
    Sep.Triple ge (FunctionEntry2 ge) f_fib_rec (At L) (recCall t c)
      (.only (At (L.set t (.Vint (fibInt (n - c)))))) := by
  refine Sep.triple_call_at ge _ f_fib_rec (fibSpec (n - c)) _ _ _ _ _ b _ hfind rfl rfl
    (fun e le hp m hP _ => ?_)
  obtain ⟨rfl, rfl, rfl⟩ := hP
  have hsub : Integers.Int.sub (Integers.Int.repr n) (Integers.Int.repr c)
      = Integers.Int.repr ((n - c : Nat) : _root_.Int) := by
    rw [repr_sub]; congr 1
    show (n : _root_.Int) - (c : _root_.Int) = ((n - c : Nat) : _root_.Int)
    omega
  refine ⟨_, Heap.emp, Heap.emp, Heap.disjoint_emp_left _, (Heap.emp_union _).symm,
    eval_callee_global rfl hsym rfl,
    EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Ebinop .Osub _ _ _ _ _ _
      (EvalExpr.Etempvar _ tint _ hL) (EvalExpr.Econst_int _ tint)
      (semBinop_sub_int _ _ _ _)) (by rw [hsub]; exact semCast_int m _) (EvalExprlist.nil),
    ⟨rfl, rfl⟩, hIH, fun v h1' hpost _ => ?_⟩
  obtain ⟨rfl, rfl⟩ := hpost
  exact ⟨rfl, rfl, Heap.emp_union _⟩

/-- A pure fact in the precondition. -/
private theorem triple_and_pure {ge : CGenv} {fe : EntryRel} {f : Function} {P : Sep.Assn}
    {φ : Prop} {s : Stmt} {R : Sep.ExitConds} (h : φ → Sep.Triple ge fe f P s R) :
    Sep.Triple ge fe f (fun e le hp => P e le hp ∧ φ) s R :=
  fun k e le hp hf m hd hag hP => h hP.2 k e le hp hf m hd hag hP.1

/-- The body of `fib_rec` at `n`, given the recursive calls at smaller
    arguments. -/
theorem fib_rec_body (b : Block)
    (hsym : Genv.findSymbol ge.genv_genv _fib_rec = some b)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero)
      = some (.Internal f_fib_rec))
    (n : Nat) (hn : (n : _root_.Int) < 2147483648)
    (IH : ∀ n', n' < n → (n' : _root_.Int) < 2147483648 → ∀ vargs,
      Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fib_rec) (fibSpec n') vargs) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fib_rec) (fibSpec n)
      [.Vint (Integers.Int.repr n)] := by
  refine satisfies_at ge f_fib_rec _ _ (recLe n) (by decide) (by decide) (by decide) rfl rfl
    (fun _ h => h.2) ?_
  rw [fib_rec_body_eq]
  refine Sep.triple_seq ge _ f_fib_rec _ _ _ _ _
    (rec_if_triple ge n 0 (recLe n) hn (by decide) rfl rfl) (triple_and_pure fun h0 => ?_)
  refine Sep.triple_seq ge _ f_fib_rec _ _ _ _ _
    (rec_if_triple ge n 1 (recLe n) hn (by decide) rfl rfl) (triple_and_pure fun h1 => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have e2 : j + 2 - 2 = j := by omega
  have e1 : j + 2 - 1 = j + 1 := by omega
  refine Sep.triple_seq_only ge _ f_fib_rec (Sep.triple_seq_only ge _ f_fib_rec
    (rec_call_triple ge b hsym hfind (j + 2) 2 _t'1 (recLe (j + 2)) (by omega) rfl
      (IH _ (by omega) (by omega) _))
    (rec_call_triple ge b hsym hfind (j + 2) 1 _t'2 _ (by omega) rfl
      (IH _ (by omega) (by omega) _))) ?_
  refine Sep.triple_conseq ge _ f_fib_rec
    (triple_return_at ge _ _ _ (.Vint (Integers.Int.add (fibInt (j + 2 - 2)) (fibInt (j + 2 - 1))))
      (.Vint (fibInt (j + 2)))
      (fun _ => EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ rfl)
        (EvalExpr.Etempvar _ tint _ rfl) (semBinop_add_int _ _ _ _))
      (fun m => by rw [e2, e1, fibInt_add]; exact semCast_int m _))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ x => x)

/-- **`fib_rec` satisfies `fib_spec`** (VST's `body_fib_rec`), for
    `0 ≤ n < 2^31`, given that the global `fib_rec` is this function: the
    recursion is justified by `satisfies_rec` with the measure `n`. -/
theorem fib_rec_satisfies (b : Block)
    (hsym : Genv.findSymbol ge.genv_genv _fib_rec = some b)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero)
      = some (.Internal f_fib_rec))
    (n : Nat) (hn : (n : _root_.Int) < 2147483648) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fib_rec) (fibSpec n)
      [.Vint (Integers.Int.repr n)] :=
  satisfies_rec ge _ (fun _ => .Internal f_fib_rec) (fun w : W => fibSpec w.1) (fun w => w.1)
    (fun w IH vargs k m hp hf hk hpre => by
      obtain ⟨rfl, hemp⟩ := hpre
      exact fib_rec_body ge b hsym hfind w.1 w.2 (fun n' hlt hn' => IH ⟨n', hn'⟩ hlt)
        k m hp hf hk ⟨rfl, hemp⟩)
    ⟨n, hn⟩ _

end FibRec

end VST.Verif.Fib
