/-
  Port of VST's `progs/verif_peel.v`: the integer square root `f` of
  `vst/progs/peel.c` meets its specification.

      int f (int b) {
        int i, a;
        for (i=b+1; i*i>b; i--) {
          a=i;
        }
        return a;
      }

  VST's specification:

      DECLARE _f
       WITH b: Z
       PRE [ tint ]
         PROP  (0 <= b; (b+1)*(b+1) < Int.max_signed)
         PARAMS (Vint (Int.repr b))
         SEP   ()
       POST [ tint ]
         EX a:Z,
         PROP ((a-1)*(a-1)<=b /\ a*a>b)
         RETURN (Vint (Int.repr a))
         SEP ().

  The point of VST's proof is that `a` is uninitialized until the middle of
  the first iteration, so no invariant in Floyd's *canonical form* holds
  before the first iteration: VST peels off that iteration
  (`semax_while_peel`).  The assertions of this port are arbitrary
  predicates on the local state, so the invariant can say directly what VST
  cannot: either no iteration has run yet (`i = b + 1`) or `a = i + 1`.  The
  loop is proved with the general loop rule `Sep.triple_loop`, the measure
  being the value of `i` itself.
-/
import VST.progs.peel
import CCLib
open CC CC.Sep CC.HProp
open Peel

namespace VST.Verif.Peel

/-- `f_spec`: called with `0 ≤ b` such that `(b+1)² < Int.max_signed`,
    returns some `a` with `(a-1)² ≤ b < a²`. -/
def fSpec (B : Nat) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint (Integers.Int.repr B)] ∧ hp = Heap.emp
  post := fun v hp => ∃ a : _root_.Int, (a - 1) * (a - 1) ≤ B ∧ (B : _root_.Int) < a * a
    ∧ v = .Vint (Integers.Int.repr a) ∧ hp = Heap.emp
  measure := fun _ => 0

/-! ## The parts of the body -/

def guardExpr : Expr :=
  .Ebinop .Ogt (.Ebinop .Omul (.Etempvar _i tint) (.Etempvar _i tint) tint)
    (.Etempvar _b tint) tint
def setI : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _b tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def setA : Stmt := .Sset _a (.Etempvar _i tint)
def decrI : Stmt :=
  .Sset _i (.Ebinop .Osub (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def loopStmt : Stmt := .Sloop (.Ssequence (.Sifthenelse guardExpr .Sskip .Sbreak) setA) decrI
def retStmt : Stmt := .Sreturn (some (.Etempvar _a tint))

theorem body_eq : f_f.fn_body = .Ssequence (.Ssequence setI loopStmt) retStmt := rfl

/-! ## Arithmetic -/

theorem sq_mono {i j : Nat} (h : i ≤ j) : i * i ≤ j * j := Nat.mul_le_mul h h

theorem lt_succ_sq (B : Nat) : B < (B + 1) * (B + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self B) (Nat.le_mul_self (B + 1))

/-! ## Assertions -/

section
variable (B : Nat)

/-- The loop invariant at `i`: either no iteration has run (`i = b + 1`) or
    `a = i + 1`; and `b < (i+1)²`. -/
def Inv (i : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _b = some (.Vint (Integers.Int.repr B))
  ∧ le.get _i = some (.Vint (Integers.Int.repr i))
  ∧ (i = B + 1 ∨ le.get _a = some (.Vint (Integers.Int.repr (i + 1 : Nat))))
  ∧ i ≤ B + 1 ∧ B < (i + 1) * (i + 1) ∧ hp = Heap.emp

/-- After the guard succeeded (`b < i²`). -/
def Guarded (i : Nat) : Sep.Assn := fun e le hp => Inv B i e le hp ∧ B < i * i

/-- After `a = i`. -/
def Mid (i : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _b = some (.Vint (Integers.Int.repr B))
  ∧ le.get _i = some (.Vint (Integers.Int.repr i))
  ∧ le.get _a = some (.Vint (Integers.Int.repr i))
  ∧ i ≤ B + 1 ∧ B < i * i ∧ hp = Heap.emp

/-- After the loop: `a` is the square root. -/
def Done : Sep.Assn := fun e le hp =>
  ∃ a : Nat, e = emptyEnv ∧ le.get _a = some (.Vint (Integers.Int.repr a))
    ∧ (a - 1) * (a - 1) ≤ B ∧ B < a * a ∧ hp = Heap.emp

def LoopR : Sep.ExitConds :=
  { normal := Done B, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := fun _ _ => False }

end

/-! ## The proof -/

section
variable (B : Nat) (hB : (B + 1) * (B + 1) < 2147483647) (ge : CGenv) (fe : EntryRel)
include hB

/-- The guard `i*i > b` evaluates to `b < i²`. -/
theorem eval_guard (i : Nat) (e : Env) (le : TempEnv) (m : Mem) (hi : i ≤ B + 1)
    (hbv : le.get _b = some (.Vint (Integers.Int.repr B)))
    (hiv : le.get _i = some (.Vint (Integers.Int.repr i))) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (B < i * i))) := by
  have hsq := sq_mono hi
  have h := EvalExpr.Ebinop (ge := ge) (e := e) (le := le) (m := m) .Ogt
    (.Ebinop .Omul (.Etempvar _i tint) (.Etempvar _i tint) tint) (.Etempvar _b tint) tint _ _ _
    (EvalExpr.Ebinop .Omul _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ hiv)
      (EvalExpr.Etempvar _ tint _ hiv) (semBinop_mul_int _ _ _ _))
    (EvalExpr.Etempvar _ tint _ hbv) (semBinop_gt_int _ _ _ _)
  have hB1 : B < 2147483648 := by have := lt_succ_sq B; omega
  have hii : i * i < 2147483648 := by omega
  have hii' : (i : _root_.Int) * (i : _root_.Int) < 2147483648 := by
    rw [← Int.natCast_mul]; omega
  rw [← Integers.Int.repr_mul, lt_repr (B : _root_.Int) ((i : _root_.Int) * (i : _root_.Int))
    (by omega) (by omega) (Int.mul_nonneg (by omega) (by omega)) hii'] at h
  have : decide ((B : _root_.Int) < (i : _root_.Int) * (i : _root_.Int)) = decide (B < i * i) :=
    decide_eq_decide.mpr (by exact_mod_cast Iff.rfl)
  rwa [this] at h

/-- One trip through `if (i*i > b) ; else break; a = i;`. -/
theorem body_triple (i : Nat) :
    Sep.Triple ge fe f_f (Inv B i) (.Ssequence (.Sifthenelse guardExpr .Sskip .Sbreak) setA)
      { normal := Mid B i, brk := Done B, cont := Mid B i, ret := fun _ _ => False } := by
  refine Sep.triple_seq ge fe f_f _ (Guarded B i) _ _ _ ?_ ?_
  · by_cases hg : B < i * i
    · refine Sep.triple_if_true ge fe f_f _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
      · refine ⟨_, eval_guard B hB ge i e le m hP.2.2.2.2.1 hP.2.1 hP.2.2.1, ?_⟩
        simpa [hg, guardExpr, typeof] using boolVal_ofBool_int m true
      · exact Sep.triple_fallthrough ge fe f_f _ _ _ _ (Sep.triple_skip ge fe f_f _)
          (fun e le hp h => ⟨h, hg⟩)
    · refine Sep.triple_if_false ge fe f_f _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
      · refine ⟨_, eval_guard B hB ge i e le m hP.2.2.2.2.1 hP.2.1 hP.2.2.1, ?_⟩
        simpa [hg, guardExpr, typeof] using boolVal_ofBool_int m false
      · refine Sep.triple_conseq ge fe f_f (Sep.triple_break ge fe f_f _) (fun _ _ _ x => x)
          (fun _ _ _ x => x.elim) (fun e le hp h => ?_) (fun _ _ _ x => x.elim)
          (fun _ _ x => x.elim)
        obtain ⟨he, _, _, ha, _, hlt, hh⟩ := h
        have hne : i ≠ B + 1 := fun h => hg (h ▸ lt_succ_sq B)
        refine ⟨i + 1, he, ha.resolve_left hne, ?_, hlt, hh⟩
        simpa using Nat.le_of_not_lt hg
  · refine Sep.triple_fallthrough ge fe f_f _ _ _ _ ?_ (fun _ _ _ x => x)
    refine Sep.triple_set ge fe f_f _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, hb, hi, _, hle, _, hh⟩, hg⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ tint _ hi, he, (PTree.gso _ _ _ _ (by decide)).trans hb,
      (PTree.gso _ _ _ _ (by decide)).trans hi, PTree.gss _ _ _, hle, hg, hh⟩

omit hB in
/-- `i--`, re-establishing the invariant at `i - 1 < i`. -/
theorem decr_triple (i : Nat) :
    Sep.Triple ge fe f_f (Mid B i) decrI
      { normal := fun e le hp => ∃ n', n' < i ∧ Inv B n' e le hp,
        brk := Done B, cont := Sep.Assn.no, ret := fun _ _ => False } := by
  refine Sep.triple_fallthrough ge fe f_f _ _ _ _ ?_ (fun _ _ _ x => x)
  refine Sep.triple_set ge fe f_f _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨he, hb, hi, ha, hle, hg, hh⟩ := hP
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp at hg
    · exact h
  refine ⟨_, EvalExpr.Ebinop .Osub _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ hi)
    (EvalExpr.Econst_int _ tint) (semBinop_sub_int _ _ _ _), i - 1, by omega, he,
    (PTree.gso _ _ _ _ (by decide)).trans hb, ?_, .inr ?_, by omega, ?_, hh⟩
  · rw [PTree.gss, repr_sub, show ((i : _root_.Int) - 1) = ((i - 1 : Nat) : _root_.Int) by omega]
  · rw [(PTree.gso _ _ _ _ (by decide)).trans ha, Nat.sub_add_cancel hi1]
  · rwa [Nat.sub_add_cancel hi1]

/-- The loop, entered with `i ≤ b + 1`. -/
theorem loop_triple (i : Nat) : Sep.Triple ge fe f_f (Inv B i) loopStmt (LoopR B) :=
  Sep.triple_loop ge fe f_f (LoopR B) (Inv B) (Mid B) _ _ (fun i => body_triple B hB ge fe i)
    (fun i => decr_triple B ge fe i) i

/-- **`f` satisfies `f_spec`** (VST's `body_f`). -/
theorem f_satisfies :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_f) (fSpec B)
      [.Vint (Integers.Int.repr B)] := by
  refine satisfies_at ge f_f _ _
    ((createUndefTemps f_f.fn_temps).set _b (.Vint (Integers.Int.repr B)))
    (by decide) (by decide) (by decide) rfl rfl (fun _ h => h.2) ?_
  rw [body_eq]
  refine Sep.triple_seq ge _ f_f _ (Done B) _ _ _ ?_ ?_
  · refine Sep.triple_seq ge _ f_f _ (Inv B (B + 1)) _ _ _ ?_ ?_
    · refine Sep.triple_fallthrough ge _ f_f _ _ _ _ ?_ (fun _ _ _ x => x)
      refine Sep.triple_set ge _ f_f _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨he, rfl, hh⟩ := hP
      refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ tint _ rfl)
        (EvalExpr.Econst_int _ tint) (semBinop_add_int _ _ _ _), he, rfl, ?_, .inl rfl,
        Nat.le_refl _, ?_, hh⟩
      · rw [PTree.gss, repr_add]; rfl
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self B)
          (Nat.le_trans (Nat.le_succ _) (Nat.le_mul_self _))
    · refine Sep.triple_conseq ge _ f_f (loop_triple B hB ge _ (B + 1)) (fun _ _ _ x => x)
        (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  · refine Sep.triple_return ge _ f_f _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨a, he, ha, h1, h2, hh⟩ := h
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp at h2
      · exact h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _a tint _ ha, semCast_int m _, ?_,
      ⟨a, ?_, by exact_mod_cast h2, rfl, hh⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
    · rw [he]; exact freeList_emptyEnv _ _
    · have : ((a : _root_.Int) - 1) = ((a - 1 : Nat) : _root_.Int) := by omega
      rw [this]; exact_mod_cast h1

end

end VST.Verif.Peel
