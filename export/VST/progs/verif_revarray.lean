/-
  Port of VST's `progs/verif_revarray.v`: `reverse` (`vst/progs/revarray.c`)
  reverses an array of `int`s in place.

  VST's specification:

      DECLARE _reverse
       WITH a0: val, sh : share, contents : list int, size: Z
       PRE [ tptr tint, tint ]
         PROP (0 <= size <= Int.max_signed; writable_share sh)
         PARAMS (a0; Vint (Int.repr size))
         SEP (data_at sh (tarray tint size) (map Vint contents) a0)
       POST [ tvoid ]
         PROP() RETURN()
         SEP(data_at sh (tarray tint size) (map Vint (rev contents)) a0).

  Here the separation logic is the one of `CCLib.logic`; the array of `size`
  `int`s at `a0` is `arrayU32 p b ofs size f`, the writable share is a
  writable permission `p`, and `contents` is the list of the elements
  (`Integers.Int`).  `data_at` also implies that the array fits in the
  address space (`field_compatible`); that is the hypothesis `hno`.

  The proof follows `verif_revarray.v`: the loop invariant says that, after
  `j` iterations, `lo = j`, `hi = size - j`, `j ≤ size - j`, and the array
  holds `flip_ends j (size - j) contents` — the first and last `j` elements
  are swapped, the middle is untouched.  `flip` below is `flip_ends`, as a
  function of the index.
-/
import VST.progs.revarray
import VST.progs.verif_min
open CC CC.Sep CC.HProp
open Revarray
open VST.Verif.Min (elems)

namespace VST.Verif.Revarray

/-! ## Reversal, index by index -/

section
variable (c : Nat → Integers.Int) (L : Nat)

/-- VST's `flip_ends j (L - j) contents`, as a function of the index: the
    first and last `j` elements come from the reversed array. -/
def flip (j x : Nat) : Integers.Int := if x < j ∨ L - j ≤ x then c (L - 1 - x) else c x

/-- An update of the array function at index `i` (the form
    `triple_store_index_int` produces). -/
def upd (g : Nat → Integers.Int) (i : Nat) (v : Integers.Int) : Nat → Integers.Int :=
  fun y => if y = i then v else g y

theorem flip_zero : ∀ x, x < L → c x = flip c L 0 x := by
  intro x hx
  unfold flip
  split
  · omega
  · rfl

/-- `flip_fact_1`: once `lo ≥ hi - 1`, the array is reversed. -/
theorem flip_done (j : Nat) (h1 : 2 * j ≤ L) (h2 : ¬ 2 * j + 1 < L) :
    ∀ x, x < L → flip c L j x = c (L - 1 - x) := by
  intro x hx
  unfold flip
  split
  · rfl
  · congr 1; omega

/-- `flip_fact_2`/`flip_fact_3`: one swap moves from `flip j` to
    `flip (j + 1)`. -/
theorem flip_step (j : Nat) (h : 2 * j + 1 < L) :
    ∀ x, x < L →
      upd (upd (flip c L j) (L - j - 1) (flip c L j j)) j (flip c L j (L - j - 1)) x
        = flip c L (j + 1) x := by
  intro x hx
  simp only [upd, flip]
  split <;> split <;> (try split) <;> (try split) <;>
    first | rfl | (congr 1; omega) | omega

end

theorem elems_reverse (contents : List Integers.Int) (x : Nat) (hx : x < contents.length) :
    elems contents.reverse x = elems contents (contents.length - 1 - x) := by
  simp only [elems, List.getD_eq_getElem?_getD, List.getElem?_reverse hx]

/-! ## Facts about the generated program -/

/-- The temporaries `reverse` writes are distinct from the ones it reads. -/
structure Distinct : Prop where
  lo_a : _lo ≠ _a
  lo_n : _lo ≠ _n
  lo_hi : _lo ≠ _hi
  hi_a : _hi ≠ _a
  hi_lo : _hi ≠ _lo
  t_a : _t ≠ _a
  t_lo : _t ≠ _lo
  t_hi : _t ≠ _hi
  s_a : _s ≠ _a
  s_lo : _s ≠ _lo
  s_hi : _s ≠ _hi
  s_t : _s ≠ _t

theorem idents_distinct : Distinct := by constructor <;> decide

/-- The side conditions of `function_entry2` for `reverse`. -/
theorem entry_wf :
    listNorepet (varNames f_reverse.fn_vars)
    ∧ listNorepet (varNames f_reverse.fn_params)
    ∧ listDisjoint (varNames f_reverse.fn_params) (varNames f_reverse.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem n_ne_a : _n ≠ _a := by decide

/-- The parts of the body. -/
def one : Expr := .Econst_int (Integers.Int.repr 1) tint
def hiM1 : Expr := .Ebinop .Osub (.Etempvar _hi tint) one tint
def elt (idx : Expr) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _a (tptr tint)) idx (tptr tint)) tint
def setLo0 : Stmt := .Sset _lo (.Econst_int (Integers.Int.repr 0) tint)
def setHiN : Stmt := .Sset _hi (.Etempvar _n tint)
def guardExpr : Expr := .Ebinop .Olt (.Etempvar _lo tint) hiM1 tint
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def setT : Stmt := .Sset _t (elt (.Etempvar _lo tint))
def setS : Stmt := .Sset _s (elt hiM1)
def storeHi : Stmt := .Sassign (elt hiM1) (.Etempvar _t tint)
def storeLo : Stmt := .Sassign (elt (.Etempvar _lo tint)) (.Etempvar _s tint)
def incLo : Stmt := .Sset _lo (.Ebinop .Oadd (.Etempvar _lo tint) one tint)
def decHi : Stmt := .Sset _hi hiM1
def bodyStmt : Stmt :=
  .Ssequence setT (.Ssequence setS (.Ssequence storeHi (.Ssequence storeLo
    (.Ssequence incLo decHi))))
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) .Sskip
def fullBody : Stmt := .Ssequence setLo0 (.Ssequence setHiN loopStmt)

theorem body_eq : f_reverse.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (L : Nat)
variable (c : Nat → Integers.Int)

/-- The temporaries: `a` as passed, `lo = lov`, `hi = hiv`, and `t`, `s` as
    far as set. -/
def Loc (lov hiv : _root_.Int) (t s : Option Integers.Int) : Env → TempEnv → Prop :=
  fun e le =>
    e = emptyEnv
    ∧ le.get _a = some (.Vptr b ofs0)
    ∧ le.get _lo = some (.Vint (Integers.Int.repr lov))
    ∧ le.get _hi = some (.Vint (Integers.Int.repr hiv))
    ∧ (match t with | none => True | some x => le.get _t = some (.Vint x))
    ∧ (match s with | none => True | some x => le.get _s = some (.Vint x))

/-- The array, holding `g`. -/
abbrev Arr (g : Nat → Integers.Int) : HProp := arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L g

/-- The loop invariant (`reverse_Inv`), `k = size - 2 j` iterations' worth
    of elements left. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ j : Nat, (Loc b ofs0 j ((L : _root_.Int) - j) none none e le ∧ 2 * j ≤ L ∧ L - 2 * j = k)
    ∧ Arr p b ofs0 L (flip c L j) hp

/-- After the guard: `lo < hi - 1`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ j : Nat, (Loc b ofs0 j ((L : _root_.Int) - j) none none e le ∧ 2 * j + 1 < L
    ∧ L - 2 * j = k) ∧ Arr p b ofs0 L (flip c L j) hp

/-- After an iteration that started with `k` left. -/
def LAfter (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ j : Nat, (Loc b ofs0 j ((L : _root_.Int) - j) none none e le ∧ 2 * j ≤ L
    ∧ L - 2 * j < k) ∧ Arr p b ofs0 L (flip c L j) hp

/-- After the loop: the array is reversed. -/
def Done : Sep.Assn := fun e _ hp => e = emptyEnv ∧ Arr p b ofs0 L (fun x => c (L - 1 - x)) hp

/-- The postcondition. -/
def Ret : Val → HProp := fun v hp => v = .Vundef ∧ Arr p b ofs0 L (fun x => c (L - 1 - x)) hp

def IterR (k : Nat) : Sep.ExitConds :=
  { normal := LAfter p b ofs0 L c k, brk := Done p b ofs0 L c,
    cont := LAfter p b ofs0 L c k, ret := Ret p b ofs0 L c }

def LoopR : Sep.ExitConds :=
  { normal := Done p b ofs0 L c, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := Ret p b ofs0 L c }

end

/-! ## The proof -/

private theorem no_ovf_mono (A : _root_.Int) (i l : Nat) (hil : i ≤ l)
    (h : A + 4 * (l : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block)
variable (ofs0 : Integers.Ptrofs) (L : Nat) (c : Nat → Integers.Int)

/-- `hi - 1`, evaluated. -/
theorem eval_hiM1 (e : Env) (le : TempEnv) (m : Mem) (hiv : _root_.Int)
    (hhi : le.get _hi = some (.Vint (Integers.Int.repr hiv))) :
    EvalExpr ge e le m hiM1 (.Vint (Integers.Int.repr (hiv - 1))) := by
  have h := EvalExpr.Ebinop (ge := ge) (e := e) (le := le) (m := m) .Osub _ _ tint _ _ _
    (EvalExpr.Etempvar _hi tint _ hhi) (EvalExpr.Econst_int (Integers.Int.repr 1) tint)
    (semBinop_sub_int _ _ _ _)
  rw [repr_sub] at h
  exact h

/-- The guard `lo < hi - 1`, evaluated. -/
theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (j : Nat) (t s : Option Integers.Int)
    (hL : (L : _root_.Int) < 2147483648) (hj : 2 * j ≤ L)
    (hloc : Loc b ofs0 j ((L : _root_.Int) - j) t s e le) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (2 * j + 1 < L))) := by
  obtain ⟨_, _, hlo, hhi, _⟩ := hloc
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr (j : _root_.Int))
        (Integers.Int.repr ((L : _root_.Int) - j - 1)))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _lo tint _ hlo)
      (eval_hiM1 ge e le m _ hhi) (semBinop_lt_int _ _ _ _)
  rw [lt_repr_signed _ _ (by omega) (by omega) (by omega) (by omega)] at h
  have hdec : decide ((j : _root_.Int) < (L : _root_.Int) - j - 1) = decide (2 * j + 1 < L) := by
    by_cases hlt : 2 * j + 1 < L
    · simp [hlt]; omega
    · simp [hlt]; omega
  rw [hdec] at h
  exact h

/-- The `if` at the top of the loop body: continue while `lo < hi - 1`,
    break out with the reversed array otherwise. -/
theorem if_triple (k : Nat) (hL : (L : _root_.Int) < 2147483648) :
    Sep.Triple ge fe f_reverse (LInv p b ofs0 L c k) ifStmt
      { IterR p b ofs0 L c k with normal := LMid p b ofs0 L c k } := by
  refine Sep.triple_if ge fe f_reverse _ (LMid p b ofs0 L c k)
    (fun e le hp => ∃ j : Nat, (Loc b ofs0 j ((L : _root_.Int) - j) none none e le
      ∧ 2 * j ≤ L ∧ ¬ 2 * j + 1 < L) ∧ Arr p b ofs0 L (flip c L j) hp)
    _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
  · obtain ⟨j, ⟨hloc, hj, hk⟩, harr⟩ := hP
    refine ⟨_, decide (2 * j + 1 < L), eval_guard ge b ofs0 L e le m j none none hL hj hloc,
      by simpa [guardExpr, typeof] using boolVal_ofBool_int m _, ?_⟩
    by_cases hlt : 2 * j + 1 < L
    · simp only [hlt, decide_true]
      exact ⟨j, ⟨hloc, hlt, hk⟩, harr⟩
    · simp only [hlt, decide_false]
      exact ⟨j, ⟨hloc, hj, hlt⟩, harr⟩
  · exact Sep.triple_fallthrough ge fe f_reverse _ _ _ _
      (Sep.triple_skip ge fe f_reverse _) (fun _ _ _ x => x)
  · refine Sep.triple_conseq ge fe f_reverse (Sep.triple_break ge fe f_reverse _)
      (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
      (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
    obtain ⟨j, ⟨⟨he, _⟩, hj, hlt⟩, harr⟩ := h
    refine ⟨he, ?_⟩
    unfold Arr at harr ⊢
    rw [arrayU32_congr p b L (fun x => c (L - 1 - x)) (flip c L j) _
      (fun x hx => (flip_done c L j hj hlt x hx).symm)]
    exact harr

/-- One iteration: `t = a[lo]; s = a[hi-1]; a[hi-1] = t; a[lo] = s; lo++;
    hi--;`. -/
theorem body_triple (k : Nat) (hd : Distinct) (hpw : permOrder p .Writable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_reverse (LMid p b ofs0 L c k) bodyStmt (IterR p b ofs0 L c k) := by
  have hpr := readable_of_writable hpw
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun j => ?_)
  show Sep.Triple ge fe f_reverse
    (fun e le hp => (Loc b ofs0 j ((L : _root_.Int) - j) none none e le ∧ 2 * j + 1 < L
      ∧ L - 2 * j = k) ∧ Arr p b ofs0 L (flip c L j) hp) bodyStmt _
  by_cases hjL : 2 * j + 1 < L
  case neg =>
    exact Sep.triple_pre ge fe f_reverse (fun _ _ _ h => (hjL h.1.2.1).elim)
        (Sep.triple_vacuous ge fe f_reverse _ _)
  -- the two elements swapped
  let tj := flip c L j j
  let sj := flip c L j (L - j - 1)
  have hidx : ((L : _root_.Int) - j - 1) = ((L - j - 1 : Nat) : _root_.Int) := by omega
  -- t = a[lo]
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp =>
      (Loc b ofs0 j ((L : _root_.Int) - j) (some tj) none e le ∧ 2 * j + 1 < L
        ∧ L - 2 * j = k) ∧ Arr p b ofs0 L (flip c L j) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨⟨he, ha, hlo, hhi, _, _⟩, hj, hk⟩, harr⟩ := hP
    refine ⟨.Vint tj, ?_, ?_⟩
    · exact eval_index_array_int hpr harr hag (by omega)
        (EvalExpr.Etempvar _a (tptr tint) _ ha) (EvalExpr.Etempvar _lo tint _ hlo) rfl rfl
        (elemOfs_unsigned ge.genv_cenv ofs0 j (by omega) (no_ovf_mono _ j L (by omega) hno))
    · exact ⟨⟨⟨he, (PTree.gso _ _ _ _ hd.t_a).trans ha, (PTree.gso _ _ _ _ hd.t_lo).trans hlo,
        (PTree.gso _ _ _ _ hd.t_hi).trans hhi, PTree.gss _ _ _, trivial⟩, hj, hk⟩, harr⟩
  -- s = a[hi - 1]
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp =>
      (Loc b ofs0 j ((L : _root_.Int) - j) (some tj) (some sj) e le ∧ 2 * j + 1 < L
        ∧ L - 2 * j = k) ∧ Arr p b ofs0 L (flip c L j) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨⟨he, ha, hlo, hhi, ht, _⟩, hj, hk⟩, harr⟩ := hP
    refine ⟨.Vint sj, ?_, ?_⟩
    · have hi1 := eval_hiM1 ge e le m _ hhi
      rw [hidx] at hi1
      exact eval_index_array_int hpr harr hag (by omega)
        (EvalExpr.Etempvar _a (tptr tint) _ ha) hi1 rfl rfl
        (elemOfs_unsigned ge.genv_cenv ofs0 (L - j - 1) (by omega)
          (no_ovf_mono _ (L - j - 1) L (by omega) hno))
    · exact ⟨⟨⟨he, (PTree.gso _ _ _ _ hd.s_a).trans ha, (PTree.gso _ _ _ _ hd.s_lo).trans hlo,
        (PTree.gso _ _ _ _ hd.s_hi).trans hhi, (PTree.gso _ _ _ _ hd.s_t).trans ht,
        PTree.gss _ _ _⟩, hj, hk⟩, harr⟩
  -- the locals, unchanged by the two stores
  have hR : ∀ e le, (Loc b ofs0 j ((L : _root_.Int) - j) (some tj) (some sj) e le
      ∧ 2 * j + 1 < L ∧ L - 2 * j = k) →
      Loc b ofs0 j ((L : _root_.Int) - j) (some tj) (some sj) e le := fun _ _ h => h.1
  -- a[hi - 1] = t
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp =>
      (Loc b ofs0 j ((L : _root_.Int) - j) (some tj) (some sj) e le ∧ 2 * j + 1 < L
        ∧ L - 2 * j = k)
      ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L (upd (flip c L j) (L - j - 1) tj) hp)
    ?_ ?_
  · exact Sep.triple_store_index_int ge fe f_reverse _ _ _ _ p b ofs0 L (L - j - 1)
      (flip c L j) tj hpw (by omega) hL hno
      (fun e le m h => EvalExpr.Etempvar _a (tptr tint) _ (hR e le h).2.1)
      (fun e le m h => by
        have hi1 := eval_hiM1 ge e le m _ (hR e le h).2.2.2.1
        rw [hidx] at hi1; exact hi1)
      (fun e le m h => EvalExpr.Etempvar _t tint _ (hR e le h).2.2.2.2.1) rfl rfl rfl
  -- a[lo] = s
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp =>
      (Loc b ofs0 j ((L : _root_.Int) - j) (some tj) (some sj) e le ∧ 2 * j + 1 < L
        ∧ L - 2 * j = k)
      ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L
          (upd (upd (flip c L j) (L - j - 1) tj) j sj) hp) ?_ ?_
  · exact Sep.triple_store_index_int ge fe f_reverse _ _ _ _ p b ofs0 L j
      (upd (flip c L j) (L - j - 1) tj) sj hpw (by omega) hL hno
      (fun e le m h => EvalExpr.Etempvar _a (tptr tint) _ (hR e le h).2.1)
      (fun e le m h => EvalExpr.Etempvar _lo tint _ (hR e le h).2.2.1)
      (fun e le m h => EvalExpr.Etempvar _s tint _ (hR e le h).2.2.2.2.2) rfl rfl rfl
  -- lo++
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp =>
      (Loc b ofs0 (j + 1 : Nat) ((L : _root_.Int) - j) none none e le ∧ 2 * j + 1 < L
        ∧ L - 2 * j = k) ∧ Arr p b ofs0 L (flip c L (j + 1)) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨⟨he, ha, hlo, hhi, _, _⟩, hj, hk⟩, harr⟩ := hP
    refine ⟨.Vint (Integers.Int.repr ((j : _root_.Int) + 1)), ?_, ?_⟩
    · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _lo tint _ hlo)
        (EvalExpr.Econst_int _ tint) ?_
      simp only [typeof, one]
      rw [semBinop_add_int, repr_add]
    · refine ⟨⟨⟨he, (PTree.gso _ _ _ _ hd.lo_a).trans ha, ?_,
        (PTree.gso _ _ _ _ hd.lo_hi).trans hhi, trivial, trivial⟩, hj, hk⟩, ?_⟩
      · rw [PTree.gss]; simp
      · unfold Arr
        rw [arrayU32_congr p b L (flip c L (j + 1)) _ _
          (fun x hx => (flip_step c L j hj x hx).symm)]
        exact harr
  -- hi--
  refine Sep.triple_fallthrough ge fe f_reverse _ _ _ _
    (Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
  obtain ⟨⟨⟨he, ha, hlo, hhi, _, _⟩, hj, hk⟩, harr⟩ := hP
  refine ⟨_, eval_hiM1 ge e le m _ hhi, j + 1, ⟨⟨he, (PTree.gso _ _ _ _ hd.hi_a).trans ha,
    (PTree.gso _ _ _ _ hd.hi_lo).trans hlo, ?_, trivial, trivial⟩, by omega, by omega⟩, harr⟩
  rw [PTree.gss, show (L : _root_.Int) - j - 1 = (L : _root_.Int) - ((j + 1 : Nat) : _root_.Int)
    by omega]

/-- The loop: it terminates, and leaves the array reversed. -/
theorem loop_triple (hd : Distinct) (hpw : permOrder p .Writable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616)
    (k : Nat) :
    Sep.Triple ge fe f_reverse (LInv p b ofs0 L c k) loopStmt (LoopR p b ofs0 L c) := by
  refine Sep.triple_loop ge fe f_reverse (LoopR p b ofs0 L c) (LInv p b ofs0 L c)
    (LAfter p b ofs0 L c) _ _ (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_reverse _ (LMid p b ofs0 L c k) _ _ _
      (if_triple ge fe p b ofs0 L c k hL) (body_triple ge fe p b ofs0 L c k hd hpw hL hno)
  · refine Sep.triple_fallthrough ge fe f_reverse _ _ _ _
      (Sep.triple_skip ge fe f_reverse _) (fun e le hp h => ?_)
    obtain ⟨j, ⟨hloc, hj, hk⟩, harr⟩ := h
    exact ⟨L - 2 * j, hk, j, ⟨hloc, hj, rfl⟩, harr⟩

/-- The precondition of the body: the parameters as passed, the array owned. -/
def Pre : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vint (Integers.Int.repr L))
  ∧ Arr p b ofs0 L c hp

/-- **The body of `reverse`**: it reverses the array in place. -/
theorem reverse_body (hd : Distinct) (hpw : permOrder p .Writable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_reverse (Pre p b ofs0 L c) fullBody
      { normal := Done p b ofs0 L c, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p b ofs0 L c } := by
  -- lo = 0
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp =>
      Pre p b ofs0 L c e le hp ∧ le.get _lo = some (.Vint (Integers.Int.repr 0))) ?_ ?_
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, ha, hn, harr⟩ := hP
    exact ⟨_, EvalExpr.Econst_int _ tint, ⟨he, (PTree.gso _ _ _ _ hd.lo_a).trans ha,
      (PTree.gso _ _ _ _ hd.lo_n).trans hn, harr⟩, PTree.gss _ _ _⟩
  -- hi = n
  refine Sep.triple_seq_only ge fe f_reverse (Q := LInv p b ofs0 L c L) ?_ ?_
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, ha, hn, harr⟩, hlo⟩ := hP
    refine ⟨_, EvalExpr.Etempvar _n tint _ hn, 0, ⟨⟨he, (PTree.gso _ _ _ _ hd.hi_a).trans ha,
      (PTree.gso _ _ _ _ hd.hi_lo).trans hlo, ?_, trivial, trivial⟩, by omega, by omega⟩, ?_⟩
    · rw [PTree.gss]; simp
    · unfold Arr at harr ⊢
      rw [arrayU32_congr p b L (flip c L 0) c _ (fun x hx => (flip_zero c L x hx).symm)]
      exact harr
  -- the loop
  exact Sep.triple_conseq ge fe f_reverse (loop_triple ge fe p b ofs0 L c hd hpw hL hno L)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ x => x)

/-! ## As a function specification (VST's `reverse_spec`) -/

/-- `reverse_spec`: called with a pointer to an array of `contents.length`
    `int`s, writable with permission `p`, it leaves the array holding the
    reversed `contents`. -/
def reverseSpec (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
    (contents : List Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tint, tint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)]
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents) hp
  post := fun v hp =>
    v = .Vundef
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents.reverse) hp
  measure := fun _ => 0

/-- **`reverse` satisfies `reverse_spec`** (VST's `body_reverse`): the array
    is writable, its size is at most `Int.max_signed`, and it fits in the
    address space. -/
theorem reverse_satisfies (contents : List Integers.Int)
    (hpw : permOrder p .Writable = true)
    (hL : (contents.length : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_reverse)
      (reverseSpec p b ofs0 contents)
      [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf
  have hrev : ∀ hp, Arr p b ofs0 contents.length
      (fun x => elems contents (contents.length - 1 - x)) hp →
      arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length
        (elems contents.reverse) hp := by
    intro hp h
    rw [arrayU32_congr p b contents.length (elems contents.reverse) _ _
      (fun x hx => elems_reverse contents x hx)]
    exact h
  refine Sep.satisfies_internal_noVars_void ge (FunctionEntry2 ge) f_reverse _ _
    (Pre p b ofs0 contents.length (elems contents)) (fun m => ?_) ?_
  · refine ⟨PTree.set _n (.Vint (Integers.Int.repr contents.length))
              (PTree.set _a (.Vptr b ofs0) (createUndefTemps f_reverse.fn_temps)),
            FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    obtain ⟨_, harr⟩ := hpre
    exact ⟨rfl, (PTree.gso _ _ _ _ n_ne_a).trans (PTree.gss _ _ _), PTree.gss _ _ _, harr⟩
  · have h := body_eq ▸ reverse_body ge (FunctionEntry2 ge) p b ofs0 contents.length
      (elems contents) idents_distinct hpw hL hno
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_reverse h (fun _ _ _ x => x)
      (fun e le hp hr => ?_) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    · obtain ⟨he, harr⟩ := hr
      exact ⟨he, rfl, hrev hp harr⟩
    · obtain ⟨hv, harr⟩ := hr
      exact ⟨hv, hrev hp harr⟩

end
end VST.Verif.Revarray
