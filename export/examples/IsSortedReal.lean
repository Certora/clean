/-
  SUPERSEDED (Phase 7.7) by `IsSortedSep.lean`, which proves the same behaviour
  with the *separation* logic — so the array is an owned resource and the frame
  rule applies.  This file is kept because `IsSortedSep` reuses its AST
  definitions and `body_eq`, and because the two proofs are worth comparing.

  **The Phase-6 milestone.**

  `is_sorted` (from `main.c`, exported by `clightgen -lean` into `GenMain`)
  returns `1` whenever its input array is sorted — proved against CompCert's
  *real* Clight semantics via the Hoare logic in `CCLib.logic.Hoare`.

  This replaces `IsSortedProof.lean`, which proved the same statement against the
  hand-written toy interpreter in `ClightSem.lean`.  The difference is the whole
  point of Phases 0-6: the conclusion here is about `CC.Step`, the faithful port
  of `Clight.v`'s step relation, validated by 71,222 operation-level differential
  observations and by 516 whole-program comparisons against `ccomp -interp`.
-/
import GenMain
import CCLib
open CC
open Main   -- the generated module now lives in its own namespace

namespace IsSortedReal

/-! ## The statement of the program

Re-typed from the generated AST, with `body_eq` below checking by `rfl` that the
transcription matches `GenMain` exactly.  If `main.c` or the exporter changes,
`body_eq` fails rather than the proof silently drifting. -/

/-- `i < len` — the loop's exit test. -/
def guardStmt : Stmt :=
  .Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _len tint) tint)
    .Sskip .Sbreak

/-- `numbers[i]` -/
def elemI : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _numbers (tptr tuint)) (.Etempvar _i tint)
            (tptr tuint)) tuint

/-- `numbers[i-1]` -/
def elemIm1 : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _numbers (tptr tuint))
            (.Ebinop .Osub (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
            (tptr tuint)) tuint

/-- `if (numbers[i] < numbers[i-1]) return 0;` -/
def cmpStmt : Stmt :=
  .Sifthenelse (.Ebinop .Olt (.Etempvar _t'1 tuint) (.Etempvar _t'2 tuint) tint)
    (.Sreturn (some (.Econst_int (Integers.Int.repr 0) tint))) .Sskip

def restStmt : Stmt :=
  .Ssequence (.Sset _t'1 elemI) (.Ssequence (.Sset _t'2 elemIm1) cmpStmt)

def bodyStmt : Stmt := .Ssequence guardStmt restStmt

/-- `i = i + 1` -/
def incrStmt : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)

def loopStmt : Stmt := .Sloop bodyStmt incrStmt

/-- `return 1;` at type `_Bool` -/
def ret1 : Stmt := .Sreturn (some (.Econst_int (Integers.Int.repr 1) tint))

def fullBody : Stmt :=
  .Ssequence
    (.Sifthenelse (.Ebinop .Ole (.Etempvar _len tint)
                    (.Econst_int (Integers.Int.repr 1) tint) tint) ret1 .Sskip)
    (.Ssequence (.Sset _last
        (.Ederef (.Ebinop .Oadd (.Etempvar _numbers (tptr tuint))
                   (.Econst_int (Integers.Int.repr 0) tint) (tptr tuint)) tuint))
      (.Ssequence (.Sset _first (.Ecast (.Econst_int (Integers.Int.repr 1) tint) tbool))
        (.Ssequence (.Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 1) tint)) loopStmt)
          ret1)))

/-- The transcription above is exactly the generated AST. -/
theorem body_eq : f_is_sorted.fn_body = fullBody := rfl

/-! ## Identifier distinctness

Taken as a hypothesis so every theorem below is independent of the generated
program.  Discharged once, in `idents_distinct`, by **kernel `decide`** — this
needed `native_decide` until `identOfString` was made kernel-reducible (see
`CCLib.lib.Positive`). -/

/-- The identifiers `is_sorted` writes, each distinct from the ones still live at
    that point.  Field `x_y` reads "writing `x` does not disturb `y`". -/
structure Distinct : Prop where
  last_num : _last ≠ _numbers
  last_len : _last ≠ _len
  first_num : _first ≠ _numbers
  first_len : _first ≠ _len
  i_num : _i ≠ _numbers
  i_len : _i ≠ _len
  t1_num : _t'1 ≠ _numbers
  t1_len : _t'1 ≠ _len
  t1_i : _t'1 ≠ _i
  t2_num : _t'2 ≠ _numbers
  t2_len : _t'2 ≠ _len
  t2_i : _t'2 ≠ _i
  t2_t1 : _t'2 ≠ _t'1

/-! ## Assertions -/

/-- The local state inside `is_sorted`: no block-scoped variables, memory
    untouched at `m0`, `numbers`/`len`/`i` known, and `t'1`/`t'2` known when the
    `Option` arguments say so. -/
def St (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs) (L iv : _root_.Int)
    (t1 t2 : Option Integers.Int) : Assn := fun e le m =>
  e = emptyEnv ∧ m = m0
  ∧ le.get _numbers = some (.Vptr b ofs0)
  ∧ le.get _len = some (.Vint (Integers.Int.repr L))
  ∧ le.get _i = some (.Vint (Integers.Int.repr iv))
  ∧ (match t1 with | none => True | some x => le.get _t'1 = some (.Vint x))
  ∧ (match t2 with | none => True | some x => le.get _t'2 = some (.Vint x))

/-- Loop invariant at measure `n`: `n` iterations left, `i` in `[1, L]`. -/
def LInv (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs) (L : _root_.Int) (n : Nat) : Assn := fun e le m =>
  ∃ iv : _root_.Int, St m0 b ofs0 L iv none none e le m
    ∧ 1 ≤ iv ∧ iv ≤ L ∧ L - iv = (n : _root_.Int)

/-- Mid-loop assertion (guard passed, so `i < L`): what `Sloop`'s second
    statement — the increment — starts from. -/
def LMid (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs) (L : _root_.Int) (n : Nat) : Assn := fun e le m =>
  ∃ iv : _root_.Int, St m0 b ofs0 L iv none none e le m
    ∧ 1 ≤ iv ∧ iv < L ∧ L - iv = (n : _root_.Int)

/-- Mid-body assertion at a *named* index `iv`, with `t'1`/`t'2` known as far as
    execution has got.  Naming `iv` is what lets the body proof talk about
    `arr iv` and `arr (iv-1)`. -/
def AtIv (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs) (L iv : _root_.Int)
    (n : Nat) (t1 t2 : Option Integers.Int) : Assn := fun e le m =>
  St m0 b ofs0 L iv t1 t2 e le m ∧ 1 ≤ iv ∧ iv < L ∧ L - iv = (n : _root_.Int)

/-- After the loop: nothing left to know but that memory is untouched. -/
def Done (m0 : Mem) : Assn := fun e le m => e = emptyEnv ∧ m = m0

/-- The function returns `1` (`true`) and leaves memory alone. -/
def RetOne (m0 : Mem) : Val → Mem → Prop :=
  fun v m => v = .Vint (Integers.Int.repr 1) ∧ m = m0

/-- Precondition of the whole function: `numbers` and `len` are the arguments. -/
def Pre (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs) (L : _root_.Int) : Assn :=
  fun e le m => e = emptyEnv ∧ m = m0
    ∧ le.get _numbers = some (.Vptr b ofs0)
    ∧ le.get _len = some (.Vint (Integers.Int.repr L))

/-- Exit conditions of the whole function: it always returns, and returns `1`. -/
def RetR (m0 : Mem) : ExitConds :=
  { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := RetOne m0 }

/-- Exit conditions for the loop and everything inside it. -/
def LoopR (m0 : Mem) : ExitConds :=
  { normal := Done m0, brk := Assn.no, cont := Assn.no, ret := RetOne m0 }

/-- Exit conditions of the loop *body*: a `break` leaves the loop (landing in
    `Done`), and `continue` is impossible in this program. -/
def BodyR (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs) (L : _root_.Int) (n : Nat) : ExitConds :=
  { normal := LMid m0 b ofs0 L n, brk := Done m0, cont := Assn.no, ret := RetOne m0 }

/-! ## The loop -/

section
variable (ge : CGenv) (fe : EntryRel) (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs)
variable (L : _root_.Int) (arr : _root_.Int → Integers.Int)

/-- `i < len` is true, because `n+1` iterations remain. -/
theorem guard_true (n : Nat) (hL : L < 2147483648) :
    Triple ge fe f_is_sorted (LInv m0 b ofs0 L (n+1)) guardStmt
      (BodyR m0 b ofs0 L (n+1)) := by
  refine triple_if_true ge fe f_is_sorted _ _ _ _ _ (fun e le m hP => ?_) ?_
  · obtain ⟨iv, ⟨_, _, _, hlen, hi, _, _⟩, h1, h2, h3⟩ := hP
    refine ⟨Val.ofBool (Integers.Int.lt (Integers.Int.repr iv) (Integers.Int.repr L)), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Olt _ _ _ _ _ _
        (EvalExpr.Etempvar _i tint _ hi) (EvalExpr.Etempvar _len tint _ hlen)
        (semBinop_lt_int _ _ _ _)
    · rw [lt_repr iv L (by omega) (by omega) (by omega) hL]
      have hlt : iv < L := by omega
      simpa [hlt, typeof] using boolVal_ofBool_int m true
  · refine triple_conseq ge fe f_is_sorted (triple_skip ge fe f_is_sorted _)
      (fun _ _ _ h => h) (fun e le m h => ?_) (fun _ _ _ h => False.elim h)
      (fun _ _ _ h => False.elim h) (fun _ _ h => False.elim h)
    obtain ⟨iv, hst, h1, h2, h3⟩ := h
    exact ⟨iv, hst, h1, by omega, h3⟩

/-- `i < len` is false, because no iterations remain: the loop breaks out. -/
theorem guard_false (hL : L < 2147483648) :
    Triple ge fe f_is_sorted (LInv m0 b ofs0 L 0) guardStmt (BodyR m0 b ofs0 L 0) := by
  refine triple_if_false ge fe f_is_sorted _ _ _ _ _ (fun e le m hP => ?_) ?_
  · obtain ⟨iv, ⟨_, _, _, hlen, hi, _, _⟩, h1, h2, h3⟩ := hP
    refine ⟨Val.ofBool (Integers.Int.lt (Integers.Int.repr iv) (Integers.Int.repr L)), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Olt _ _ _ _ _ _
        (EvalExpr.Etempvar _i tint _ hi) (EvalExpr.Etempvar _len tint _ hlen)
        (semBinop_lt_int _ _ _ _)
    · rw [lt_repr iv L (by omega) (by omega) (by omega) hL]
      have hge : ¬ (iv < L) := by omega
      simpa [hge, typeof] using boolVal_ofBool_int m false
  · refine triple_conseq ge fe f_is_sorted (triple_break ge fe f_is_sorted _)
      (fun _ _ _ h => h) (fun _ _ _ h => False.elim h) (fun e le m h => ?_)
      (fun _ _ _ h => False.elim h) (fun _ _ h => False.elim h)
    obtain ⟨iv, ⟨he, hm, _, _, _, _, _⟩, _⟩ := h
    exact ⟨he, hm⟩

/-- The rest of the loop body: read `numbers[i]` and `numbers[i-1]`, and — because
    the array is sorted — fall through instead of returning `0`. -/
theorem rest_ok (n : Nat) (hd : Distinct) (hL : L < 2147483648)
    (harr : ArrU32 ge.genv_cenv m0 b ofs0 L arr)
    (hsorted : ∀ j : _root_.Int, 1 ≤ j → j < L → Integers.Int.ltu (arr j) (arr (j-1)) = false) :
    Triple ge fe f_is_sorted (LMid m0 b ofs0 L n) restStmt (BodyR m0 b ofs0 L n) := by
  -- name the index once, then work with concrete values of `t'1` / `t'2`
  have key : ∀ iv : _root_.Int,
      Triple ge fe f_is_sorted (AtIv m0 b ofs0 L iv n none none) restStmt
        (BodyR m0 b ofs0 L n) := by
    intro iv
    refine triple_seq ge fe f_is_sorted _ (AtIv m0 b ofs0 L iv n (some (arr iv)) none)
      _ _ _ ?_ ?_
    · -- t'1 = numbers[i]
      refine triple_fallthrough ge fe f_is_sorted _ (AtIv m0 b ofs0 L iv n (some (arr iv)) none)
        _ _ (triple_set ge fe f_is_sorted _ _ _ _ (fun e le m hP => ?_)) (fun _ _ _ x => x)
      obtain ⟨⟨he, hm, hnum, hlen, hi, _, _⟩, h1, hlt, h3⟩ := hP
      refine ⟨.Vint (arr iv), ?_, ?_⟩
      · exact eval_index ge e le m b ofs0 L arr (hm ▸ harr) _numbers hnum
          (.Etempvar _i tint) rfl iv (EvalExpr.Etempvar _i tint _ hi) (by omega) hlt
      · exact ⟨⟨he, hm, (PTree.gso _ _ _ _ hd.t1_num).trans hnum,
                (PTree.gso _ _ _ _ hd.t1_len).trans hlen, (PTree.gso _ _ _ _ hd.t1_i).trans hi,
                PTree.gss _ _ _, trivial⟩, h1, hlt, h3⟩
    refine triple_seq ge fe f_is_sorted _
      (AtIv m0 b ofs0 L iv n (some (arr iv)) (some (arr (iv - 1)))) _ _ _ ?_ ?_
    · -- t'2 = numbers[i-1]
      refine triple_fallthrough ge fe f_is_sorted _
        (AtIv m0 b ofs0 L iv n (some (arr iv)) (some (arr (iv - 1)))) _ _
        (triple_set ge fe f_is_sorted _ _ _ _ (fun e le m hP => ?_)) (fun _ _ _ x => x)
      obtain ⟨⟨he, hm, hnum, hlen, hi, ht1, _⟩, h1, hlt, h3⟩ := hP
      refine ⟨.Vint (arr (iv - 1)), ?_, ?_⟩
      · refine eval_index ge e le m b ofs0 L arr (hm ▸ harr) _numbers hnum
          (.Ebinop .Osub (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
          rfl (iv - 1) ?_ (by omega) (by omega)
        refine EvalExpr.Ebinop .Osub _ _ _ _ _ _
          (EvalExpr.Etempvar _i tint _ hi) (EvalExpr.Econst_int _ tint) ?_
        simp only [typeof]
        rw [semBinop_sub_int, repr_sub]
      · exact ⟨⟨he, hm, (PTree.gso _ _ _ _ hd.t2_num).trans hnum,
                (PTree.gso _ _ _ _ hd.t2_len).trans hlen, (PTree.gso _ _ _ _ hd.t2_i).trans hi,
                (PTree.gso _ _ _ _ hd.t2_t1).trans ht1, PTree.gss _ _ _⟩, h1, hlt, h3⟩
    -- if (numbers[i] < numbers[i-1]) return 0;  --- the guard is false
    refine triple_if_false ge fe f_is_sorted _ _ _ _ _ (fun e le m hP => ?_) ?_
    · obtain ⟨⟨_, _, _, _, _, ht1, ht2⟩, h1, hlt, h3⟩ := hP
      refine ⟨Val.ofBool (Integers.Int.ltu (arr iv) (arr (iv - 1))), ?_, ?_⟩
      · exact EvalExpr.Ebinop .Olt _ _ _ _ _ _
          (EvalExpr.Etempvar _t'1 tuint _ ht1) (EvalExpr.Etempvar _t'2 tuint _ ht2)
          (semBinop_ltu_uint _ _ _ _)
      · rw [hsorted iv h1 hlt]
        simpa [typeof] using boolVal_ofBool_int m false
    · refine triple_fallthrough ge fe f_is_sorted _ _ _ _
        (triple_skip ge fe f_is_sorted _) (fun e le m h => ?_)
      obtain ⟨⟨he, hm, hnum, hlen, hi, _, _⟩, h1, hlt, h3⟩ := h
      exact ⟨iv, ⟨he, hm, hnum, hlen, hi, trivial, trivial⟩, h1, hlt, h3⟩
  intro k e le m hP
  obtain ⟨iv, h⟩ := hP
  exact key iv k e le m h

/-- The whole loop body. -/
theorem body_triple (n : Nat) (hd : Distinct) (hL : L < 2147483648)
    (harr : ArrU32 ge.genv_cenv m0 b ofs0 L arr)
    (hsorted : ∀ j : _root_.Int, 1 ≤ j → j < L → Integers.Int.ltu (arr j) (arr (j-1)) = false) :
    Triple ge fe f_is_sorted (LInv m0 b ofs0 L n) bodyStmt (BodyR m0 b ofs0 L n) := by
  refine triple_seq ge fe f_is_sorted _ (LMid m0 b ofs0 L n) _ _ _ ?_
    (rest_ok ge fe m0 b ofs0 L arr n hd hL harr hsorted)
  cases n with
  | zero => exact guard_false ge fe m0 b ofs0 L hL
  | succ k => exact guard_true ge fe m0 b ofs0 L k hL

/-- `i = i + 1`: the measure drops by one. -/
theorem incr_triple (n : Nat) (hd : Distinct) :
    Triple ge fe f_is_sorted (LMid m0 b ofs0 L n) incrStmt
      { normal := fun e le m => ∃ n', n' < n ∧ LInv m0 b ofs0 L n' e le m,
        brk := Done m0, cont := Assn.no, ret := RetOne m0 } := by
  refine triple_fallthrough ge fe f_is_sorted _ _ _ _
    (triple_set ge fe f_is_sorted _ _ _ _ (fun e le m hP => ?_)) (fun _ _ _ x => x)
  obtain ⟨iv, ⟨he, hm, hnum, hlen, hi, _, _⟩, h1, hlt, h3⟩ := hP
  refine ⟨.Vint (Integers.Int.repr (iv + 1)), ?_, ?_⟩
  · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _
      (EvalExpr.Etempvar _i tint _ hi) (EvalExpr.Econst_int _ tint) ?_
    simp only [typeof]
    rw [semBinop_add_int, repr_add]
  · exact ⟨n - 1, by omega, iv + 1,
      ⟨he, hm, (PTree.gso _ _ _ _ hd.i_num).trans hnum,
       (PTree.gso _ _ _ _ hd.i_len).trans hlen, PTree.gss _ _ _, trivial, trivial⟩,
      by omega, by omega, by omega⟩

/-- The loop: from any starting measure it terminates, and it can only leave via
    the `break` in its guard (never via the `return 0`). -/
theorem loop_triple (hd : Distinct) (hL : L < 2147483648)
    (harr : ArrU32 ge.genv_cenv m0 b ofs0 L arr)
    (hsorted : ∀ j : _root_.Int, 1 ≤ j → j < L → Integers.Int.ltu (arr j) (arr (j-1)) = false)
    (n : Nat) :
    Triple ge fe f_is_sorted (LInv m0 b ofs0 L n) loopStmt (LoopR m0) := by
  refine triple_loop ge fe f_is_sorted (LoopR m0) (LInv m0 b ofs0 L) (LMid m0 b ofs0 L)
    bodyStmt incrStmt (fun n => ?_) (fun n => ?_) n
  · -- the body's exit conditions, with `continue` (impossible here) weakened in
    exact triple_conseq ge fe f_is_sorted
      (body_triple ge fe m0 b ofs0 L arr n hd hL harr hsorted)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ x => x)
  · exact incr_triple ge fe m0 b ofs0 L n hd

/-! ## The function body -/

/-- `return 1;` — the only way this function leaves. -/
theorem ret1_triple (P : Assn) (hP : ∀ e le m, P e le m → e = emptyEnv ∧ m = m0) :
    Triple ge fe f_is_sorted P ret1 (RetR m0) := by
  refine triple_conseq ge fe f_is_sorted
    (triple_return ge fe f_is_sorted P (RetOne m0) _ (fun e le m h => ?_))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ x => x)
  obtain ⟨he, hm⟩ := hP e le m h
  refine ⟨.Vint (Integers.Int.repr 1), .Vint (Integers.Int.repr 1), m, ?_, ?_, ?_, rfl, hm⟩
  · exact EvalExpr.Econst_int _ tint
  · exact semCast_one_bool m
  · rw [he]; exact freeList_emptyEnv _ _

/-- **The function body, against the real Clight semantics.**  Given a sorted
    array of `L` `unsigned int`s at `numbers`, `is_sorted` returns `1`. -/
theorem is_sorted_body (hd : Distinct) (hL0 : 0 ≤ L) (hL : L < 2147483648)
    (harr : ArrU32 ge.genv_cenv m0 b ofs0 L arr)
    (hsorted : ∀ j : _root_.Int, 1 ≤ j → j < L → Integers.Int.ltu (arr j) (arr (j-1)) = false) :
    Triple ge fe f_is_sorted (Pre m0 b ofs0 L) fullBody (RetR m0) := by
  by_cases hsmall : L ≤ 1
  · -- len <= 1: return true straight away; nothing after the `if` runs
    refine triple_seq ge fe f_is_sorted _ Assn.no _ _ _ ?_
      (triple_vacuous ge fe f_is_sorted _ _)
    refine triple_if_true ge fe f_is_sorted _ _ _ _ _ (fun e le m hP => ?_) ?_
    · obtain ⟨_, _, _, hlen⟩ := hP
      refine ⟨Val.ofBool (!Integers.Int.lt (Integers.Int.repr 1) (Integers.Int.repr L)), ?_, ?_⟩
      · exact EvalExpr.Ebinop .Ole _ _ _ _ _ _ (EvalExpr.Etempvar _len tint _ hlen)
          (EvalExpr.Econst_int _ tint) (semBinop_le_int _ _ _ _)
      · rw [lt_repr 1 L (by omega) (by omega) hL0 hL]
        have : ¬ (1 < L) := by omega
        simpa [this, typeof] using boolVal_ofBool_int m true
    · exact ret1_triple ge fe m0 _ (fun _ _ _ h => ⟨h.1, h.2.1⟩)
  · -- len >= 2: run the loop, then return true
    have hbig : 2 ≤ L := by omega
    refine triple_seq ge fe f_is_sorted _ (Pre m0 b ofs0 L) _ _ _ ?_ ?_
    · -- the guard is false, so we fall through the `if`
      refine triple_if_false ge fe f_is_sorted _ _ _ _ _ (fun e le m hP => ?_) ?_
      · obtain ⟨_, _, _, hlen⟩ := hP
        refine ⟨Val.ofBool (!Integers.Int.lt (Integers.Int.repr 1) (Integers.Int.repr L)), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Ole _ _ _ _ _ _ (EvalExpr.Etempvar _len tint _ hlen)
            (EvalExpr.Econst_int _ tint) (semBinop_le_int _ _ _ _)
        · rw [lt_repr 1 L (by omega) (by omega) hL0 hL]
          have : 1 < L := by omega
          simpa [this, typeof] using boolVal_ofBool_int m false
      · exact triple_fallthrough ge fe f_is_sorted _ _ _ _
          (triple_skip ge fe f_is_sorted _) (fun _ _ _ x => x)
    -- last = numbers[0]
    refine triple_seq ge fe f_is_sorted _ (Pre m0 b ofs0 L) _ _ _ ?_ ?_
    · refine triple_fallthrough ge fe f_is_sorted _ (Pre m0 b ofs0 L) _ _
        (triple_set ge fe f_is_sorted _ _ _ _ (fun e le m hP => ?_)) (fun _ _ _ x => x)
      obtain ⟨he, hm, hnum, hlen⟩ := hP
      refine ⟨.Vint (arr 0), ?_, ?_⟩
      · exact eval_index ge e le m b ofs0 L arr (hm ▸ harr) _numbers hnum
          (.Econst_int (Integers.Int.repr 0) tint) rfl 0 (EvalExpr.Econst_int _ tint)
          (by omega) (by omega)
      · exact ⟨he, hm, (PTree.gso _ _ _ _ hd.last_num).trans hnum,
               (PTree.gso _ _ _ _ hd.last_len).trans hlen⟩
    -- first = (_Bool) 1
    refine triple_seq ge fe f_is_sorted _ (Pre m0 b ofs0 L) _ _ _ ?_ ?_
    · refine triple_fallthrough ge fe f_is_sorted _ (Pre m0 b ofs0 L) _ _
        (triple_set ge fe f_is_sorted _ _ _ _ (fun e le m hP => ?_)) (fun _ _ _ x => x)
      obtain ⟨he, hm, hnum, hlen⟩ := hP
      refine ⟨.Vint (Integers.Int.repr 1), ?_, ?_⟩
      · exact EvalExpr.Ecast _ tbool _ _ (EvalExpr.Econst_int _ tint) (semCast_one_bool m)
      · exact ⟨he, hm, (PTree.gso _ _ _ _ hd.first_num).trans hnum,
               (PTree.gso _ _ _ _ hd.first_len).trans hlen⟩
    -- (i = 1; loop) ; return 1
    refine triple_seq ge fe f_is_sorted _ (Done m0) _ _ _ ?_
      (ret1_triple ge fe m0 _ (fun _ _ _ h => h))
    refine triple_seq ge fe f_is_sorted _ (LInv m0 b ofs0 L (L - 1).toNat) _ _ _ ?_ ?_
    · refine triple_fallthrough ge fe f_is_sorted _ (LInv m0 b ofs0 L (L - 1).toNat) _ _
        (triple_set ge fe f_is_sorted _ _ _ _ (fun e le m hP => ?_)) (fun _ _ _ x => x)
      obtain ⟨he, hm, hnum, hlen⟩ := hP
      refine ⟨.Vint (Integers.Int.repr 1), EvalExpr.Econst_int _ tint, 1,
        ⟨he, hm, (PTree.gso _ _ _ _ hd.i_num).trans hnum,
         (PTree.gso _ _ _ _ hd.i_len).trans hlen, PTree.gss _ _ _, trivial, trivial⟩,
        by omega, by omega, by omega⟩
    · exact loop_triple ge fe m0 b ofs0 L arr hd hL harr hsorted _

/-! ## As a statement about `Step`

`Triple` is *defined* in terms of `Steps`, and `Steps.toStar` turns that into
`Star (Step ge fe)` — the port of `Clight.v`'s step relation.  So the theorem
below mentions only CompCert's own semantics; the logic has been discharged. -/

/-- Executing `is_sorted`'s body on a sorted array reaches a `Returnstate`
    carrying `1`, with memory unchanged, under CompCert's Clight step relation. -/
theorem is_sorted_star (hd : Distinct) (hL0 : 0 ≤ L) (hL : L < 2147483648)
    (harr : ArrU32 ge.genv_cenv m0 b ofs0 L arr)
    (hsorted : ∀ j : _root_.Int, 1 ≤ j → j < L → Integers.Int.ltu (arr j) (arr (j-1)) = false)
    (le : TempEnv) (k : Cont)
    (hnum : le.get _numbers = some (.Vptr b ofs0))
    (hlen : le.get _len = some (.Vint (Integers.Int.repr L))) :
    Star (Step ge fe)
      (.State f_is_sorted f_is_sorted.fn_body k emptyEnv le m0) E0
      (.Returnstate (.Vint (Integers.Int.repr 1)) (callCont k) m0) := by
  obtain ⟨o, hs, hR⟩ :=
    is_sorted_body ge fe m0 b ofs0 L arr hd hL0 hL harr hsorted k emptyEnv le m0
      ⟨rfl, rfl, hnum, hlen⟩
  cases o with
  | Normal _ _ _ => exact False.elim hR
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  -- `is_sorted` contains no `goto`, so this outcome is unsatisfiable
  | Goto _ _ _ _ => exact False.elim hR
  | Return v m =>
      obtain ⟨hv, hm⟩ := hR
      subst hv; subst hm
      exact Steps.toStar (body_eq ▸ hs)

end

/-! ## Discharging the identifier hypothesis

One `decide`, for "these seven identifiers are pairwise distinct".  This used to
require `native_decide` (and therefore an extra axiom in every downstream
theorem); making `identOfString` fold over `String.toList` in `CCLib.lib.Positive`
put it back in the kernel's reach.  The values are checkable independently:
`#eval (_numbers, _len, _i, _t'1, _t'2, _last, _first)`. -/
theorem idents_distinct : Distinct := by
  constructor <;> decide

/-- **Phase-6 milestone.**  `is_sorted`, as exported from `main.c` by
    `clightgen -lean`, returns `true` on every sorted array — under CompCert's
    real Clight semantics (`CC.Step`), not a toy model.

    Read the hypotheses as: memory `m0` holds `L` `unsigned int`s at `numbers`
    (`harr`), `L` fits in an `int` (`hL0`, `hL`), the array is sorted in the
    *unsigned* order the C code compares with (`hsorted`), and the two parameters
    arrived in the temporaries `clightgen` put them in (`hnum`, `hlen`). -/
theorem is_sorted_correct (ge : CGenv) (fe : EntryRel) (m0 : Mem) (b : Block)
    (ofs0 : Integers.Ptrofs) (L : _root_.Int) (arr : _root_.Int → Integers.Int)
    (hL0 : 0 ≤ L) (hL : L < 2147483648)
    (harr : ArrU32 ge.genv_cenv m0 b ofs0 L arr)
    (hsorted : ∀ j : _root_.Int, 1 ≤ j → j < L → Integers.Int.ltu (arr j) (arr (j-1)) = false)
    (le : TempEnv) (k : Cont)
    (hnum : le.get _numbers = some (.Vptr b ofs0))
    (hlen : le.get _len = some (.Vint (Integers.Int.repr L))) :
    Star (Step ge fe)
      (.State f_is_sorted f_is_sorted.fn_body k emptyEnv le m0) E0
      (.Returnstate (.Vint (Integers.Int.repr 1)) (callCont k) m0) :=
  is_sorted_star ge fe m0 b ofs0 L arr idents_distinct hL0 hL harr hsorted le k hnum hlen

/-! ## From the call itself

The above starts inside the function body.  This last step covers the call:
`Callstate` takes one `internal_function` step, whose `function_entry2` relation
puts the two parameters into the temporaries the body reads. -/

/-- The side conditions `function_entry2` imposes on `f_is_sorted` — no
    block-scoped variables, distinct parameter names, parameters disjoint from
    temporaries.  Facts about the generated AST; `decide` again because of
    `identOfString`. -/
theorem entry_wf :
    listNorepet (varNames f_is_sorted.fn_vars)
    ∧ listNorepet (varNames f_is_sorted.fn_params)
    ∧ listDisjoint (varNames f_is_sorted.fn_params) (varNames f_is_sorted.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `len` and `numbers` are different identifiers (not part of `Distinct`, which
    only lists the *writes*, but needed to read the parameters back out). -/
theorem len_ne_num : _len ≠ _numbers := by decide

/-- **`is_sorted` called on a sorted array returns `true`.**

    A complete execution under CompCert's Clight semantics with parameters passed
    as temporaries (`FunctionEntry2` — what `clightgen` output is used with):
    from the `Callstate` to the `Returnstate` carrying `1`, memory unchanged. -/
theorem is_sorted_call (ge : CGenv) (m0 : Mem) (b : Block) (ofs0 : Integers.Ptrofs)
    (L : _root_.Int) (arr : _root_.Int → Integers.Int)
    (hL0 : 0 ≤ L) (hL : L < 2147483648)
    (harr : ArrU32 ge.genv_cenv m0 b ofs0 L arr)
    (hsorted : ∀ j : _root_.Int, 1 ≤ j → j < L → Integers.Int.ltu (arr j) (arr (j-1)) = false)
    (k : Cont) :
    Star (Step ge (FunctionEntry2 ge))
      (.Callstate (.Internal f_is_sorted)
        [.Vptr b ofs0, .Vint (Integers.Int.repr L)] k m0) E0
      (.Returnstate (.Vint (Integers.Int.repr 1)) (callCont k) m0) := by
  obtain ⟨hv, hp, hdisj⟩ := entry_wf
  -- the temporary environment `function_entry2` builds for this call
  refine Star.step _ E0 (.State f_is_sorted f_is_sorted.fn_body k emptyEnv
      (PTree.set _len (.Vint (Integers.Int.repr L))
        (PTree.set _numbers (.Vptr b ofs0) (createUndefTemps f_is_sorted.fn_temps))) m0)
      E0 _ E0
    (Step.internal_function f_is_sorted _ k m0 emptyEnv _ m0
      (FunctionEntry2.intro hv hp hdisj (AllocVariables.nil _ _) rfl))
    ?_ rfl
  exact is_sorted_correct ge (FunctionEntry2 ge) m0 b ofs0 L arr hL0 hL harr hsorted _ k
    ((PTree.gso _ _ _ _ len_ne_num).trans (PTree.gss _ _ _)) (PTree.gss _ _ _)

end IsSortedReal
