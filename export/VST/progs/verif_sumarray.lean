/-
  Port of VST's `progs/verif_sumarray.v`: `sumarray` (`vst/progs/sumarray.c`)
  meets its specification.

  VST's specification:

      DECLARE _sumarray
       WITH a: val, sh : share, contents : list Z, size: Z
       PRE [ tptr tuint, tint ]
        PROP (readable_share sh; 0 <= size <= Int.max_signed;
              Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
        PARAMS (a; Vint (Int.repr size))
        SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
       POST [ tuint ]
        PROP () RETURN (Vint (Int.repr (sum_Z contents)))
        SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

  Here the separation logic is the one of `CCLib.logic` (`Sep.Triple`,
  `Sep.FunSpec`), the array of `size` unsigned integers at `a` is
  `arrayU32 p b ofs size f`, the share `sh` is the permission `p` (readable),
  and `contents` is the list of the elements (`Integers.Int`, so the range
  condition on `contents` is built in).  `data_at` also implies that the
  array fits in the address space (`field_compatible`); that is the
  hypothesis `hno`.  The function is the Clight AST generated from
  `sumarray.c` by the Lean `clightgen` (`VST.progs.sumarray`), with
  parameters passed as temporaries (`FunctionEntry2`, as in VST).

  The proof follows `verif_sumarray.v`: the loop invariant says that `s` is
  the sum of the first `i` elements (`sumTo f i`), and `0 ≤ i ≤ size`.
-/
import VST.progs.sumarray
import CCLib
open CC CC.Sep CC.HProp
open Sumarray

namespace VST.Verif.Sumarray

/-! ## The sum of the first elements -/

/-- `sum_Z` of the first `n` elements, in 32-bit arithmetic. -/
def sumTo (f : Nat → Integers.Int) : Nat → Integers.Int
  | 0 => Integers.Int.repr 0
  | n + 1 => Integers.Int.add (sumTo f n) (f n)

/-- The sum of a list of elements, in 32-bit arithmetic (VST's
    `Int.repr (sum_Z contents)`). -/
def listSum (contents : List Integers.Int) : Integers.Int :=
  contents.foldl Integers.Int.add (Integers.Int.repr 0)

/-- The elements of a list, as a function (`Znth`). -/
def elems (contents : List Integers.Int) (j : Nat) : Integers.Int :=
  contents.getD j (Integers.Int.repr 0)

theorem sumTo_elems (contents : List Integers.Int) :
    ∀ n, n ≤ contents.length → sumTo (elems contents) n = listSum (contents.take n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hlt : n < contents.length := by omega
    rw [sumTo, ih (by omega), List.take_succ_eq_append_getElem hlt, listSum, listSum,
      List.foldl_append]
    simp [elems, hlt]

theorem sumTo_elems_length (contents : List Integers.Int) :
    sumTo (elems contents) contents.length = listSum contents := by
  rw [sumTo_elems contents _ (Nat.le_refl _), List.take_length]

/-! ## Facts about the generated program -/

/-- The temporaries `sumarray` writes are distinct from the ones it reads. -/
structure Distinct : Prop where
  i_a : _i ≠ _a
  i_n : _i ≠ _n
  s_a : _s ≠ _a
  s_n : _s ≠ _n
  s_i : _s ≠ _i
  t1_a : _t'1 ≠ _a
  t1_n : _t'1 ≠ _n
  t1_i : _t'1 ≠ _i
  t1_s : _t'1 ≠ _s

theorem idents_distinct : Distinct := by constructor <;> decide

/-- The side conditions of `function_entry2` for `sumarray`. -/
theorem entry_wf :
    listNorepet (varNames f_sumarray.fn_vars)
    ∧ listNorepet (varNames f_sumarray.fn_params)
    ∧ listDisjoint (varNames f_sumarray.fn_params) (varNames f_sumarray.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem n_ne_a : _n ≠ _a := by decide

/-- The parts of the body. -/
def guardExpr : Expr := .Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint
def elemExpr : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _a (tptr tuint)) (.Etempvar _i tint) (tptr tuint)) tuint
def setT1 : Stmt := .Sset _t'1 elemExpr
def setS : Stmt := .Sset _s (.Ebinop .Oadd (.Etempvar _s tuint) (.Etempvar _t'1 tuint) tuint)
def setI : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def bodyStmt : Stmt := .Ssequence (.Ssequence setT1 setS) setI
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) .Sskip
def retStmt : Stmt := .Sreturn (some (.Etempvar _s tuint))
def fullBody : Stmt :=
  .Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 0) tint))
    (.Ssequence (.Sset _s (.Econst_int (Integers.Int.repr 0) tint))
      (.Ssequence loopStmt retStmt))

theorem body_eq : f_sumarray.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (L : Nat)
variable (f : Nat → Integers.Int)

/-- The local state: `a` and `n` as passed, `i = iv`, `s = sv`, `t'1` as far
    as set, and the array owned. -/
def St (iv : Nat) (sv : Integers.Int) (t1 : Option Integers.Int) : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vint (Integers.Int.repr L))
  ∧ le.get _i = some (.Vint (Integers.Int.repr iv))
  ∧ le.get _s = some (.Vint sv)
  ∧ (match t1 with | none => True | some x => le.get _t'1 = some (.Vint x))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- The loop invariant, `k` iterations left: `s` is the sum of the first `i`
    elements and `0 ≤ i ≤ size`. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (sumTo f iv) none e le hp ∧ iv ≤ L ∧ L - iv = k

/-- After the guard: `i < size`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (sumTo f iv) none e le hp ∧ iv < L ∧ L - iv = k

/-- After `s += a[i]`, before `i++`: the sum includes element `i`. -/
def LSummed (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (sumTo f (iv + 1)) none e le hp ∧ iv < L ∧ L - iv = k

/-- After an iteration that started with `k` iterations left. -/
def LAfter (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (sumTo f iv) none e le hp ∧ iv ≤ L ∧ L - iv + 1 = k

/-- After the loop: `s` is the sum of all the elements. -/
def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _s = some (.Vint (sumTo f L))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- The postcondition: the sum is returned, and the array handed back. -/
def Ret : Val → HProp := fun v hp =>
  v = .Vint (sumTo f L) ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

def LoopR : Sep.ExitConds :=
  { normal := Done p b ofs0 L f, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := Ret p b ofs0 L f }

def IterR (k : Nat) : Sep.ExitConds :=
  { normal := LAfter p b ofs0 L f k, brk := Done p b ofs0 L f,
    cont := LAfter p b ofs0 L f k, ret := Ret p b ofs0 L f }

end

/-! ## The proof -/

private theorem no_ovf_mono (A : _root_.Int) (i l : Nat) (hil : i ≤ l)
    (h : A + 4 * (l : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block)
variable (ofs0 : Integers.Ptrofs) (L : Nat) (f : Nat → Integers.Int) {func : Function}

/-- The guard `i < n`, evaluated. -/
theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (iv : Nat) (sv : Integers.Int)
    (t1 : Option Integers.Int) (hp : Heap) (hL : (L : _root_.Int) < 2147483648) (hiv : iv ≤ L)
    (hSt : St p b ofs0 L f iv sv t1 e le hp) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (iv < L))) := by
  obtain ⟨_, _, hn, hi, _⟩ := hSt
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr iv) (Integers.Int.repr L))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Etempvar _n tint _ hn) (semBinop_lt_int _ _ _ _)
  rw [lt_repr (iv : _root_.Int) (L : _root_.Int) (by omega) (by omega) (by omega) hL] at h
  simpa using h

/-- The `if` at the top of the loop body: continue while `i < n`, break
    out with the sum of all the elements otherwise. -/
theorem if_triple (k : Nat) (hL : (L : _root_.Int) < 2147483648) :
    Sep.Triple ge fe func (LInv p b ofs0 L f k) ifStmt
      { normal := LMid p b ofs0 L f k, brk := Done p b ofs0 L f, cont := Sep.Assn.no,
        ret := fun _ _ => False } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe func _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p b ofs0 L f e le m iv _ none hp hL hiv hSt, ?_⟩
      have : ¬ iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe func (Sep.triple_break ge fe func _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨iv, ⟨he, _, _, _, hs, _, harr⟩, hiv, hk⟩ := h
      have : iv = L := by omega
      subst this
      exact ⟨he, hs, harr⟩
  | succ j =>
    refine Sep.triple_if_true ge fe func _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p b ofs0 L f e le m iv _ none hp hL hiv hSt, ?_⟩
      have : iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe func _ _ _ _
        (Sep.triple_skip ge fe func _) (fun e le hp h => ?_)
      obtain ⟨iv, hSt, hiv, hk⟩ := h
      exact ⟨iv, hSt, by omega, hk⟩

/-- `t'1 = a[i]; s = s + t'1;`: the sum now includes element `i`. -/
theorem sum_triple (k : Nat) (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe func (LMid p b ofs0 L f k) (.Ssequence setT1 setS)
      (.only (LSummed p b ofs0 L f k)) := by
  refine Sep.triple_exists ge fe func _ _ _ (fun iv => ?_)
  refine Sep.triple_seq_only ge fe func (Q := fun e le hp =>
      St p b ofs0 L f iv (sumTo f iv) (some (f iv)) e le hp ∧ iv < L ∧ L - iv = k) ?_ ?_
  · refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, ha, hn, hi, hs, _, harr⟩, hlt, hk⟩ := hP
    refine ⟨.Vint (f iv), ?_, ?_⟩
    · exact eval_index_array hpr harr hag hlt (EvalExpr.Etempvar _a (tptr tuint) _ ha)
        (EvalExpr.Etempvar _i tint _ hi) rfl rfl
        (elemOfs_unsigned ge.genv_cenv ofs0 iv (by omega) (no_ovf_mono _ iv L (by omega) hno))
    · exact ⟨⟨he, (PTree.gso _ _ _ _ hd.t1_a).trans ha, (PTree.gso _ _ _ _ hd.t1_n).trans hn,
        (PTree.gso _ _ _ _ hd.t1_i).trans hi, (PTree.gso _ _ _ _ hd.t1_s).trans hs,
        PTree.gss _ _ _, harr⟩, hlt, hk⟩
  · refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, ha, hn, hi, hs, ht1, harr⟩, hlt, hk⟩ := hP
    refine ⟨.Vint (sumTo f (iv + 1)), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _s tuint _ hs)
        (EvalExpr.Etempvar _t'1 tuint _ ht1) (semBinop_add_uint _ _ _ _)
    · exact ⟨iv, ⟨he, (PTree.gso _ _ _ _ hd.s_a).trans ha, (PTree.gso _ _ _ _ hd.s_n).trans hn,
        (PTree.gso _ _ _ _ hd.s_i).trans hi, PTree.gss _ _ _, trivial, harr⟩, hlt, hk⟩

/-- `i = i + 1`: one iteration fewer is left. -/
theorem incr_triple (k : Nat) (hd : Distinct) :
    Sep.Triple ge fe func (LSummed p b ofs0 L f k) setI (.only (LAfter p b ofs0 L f k)) := by
  refine Sep.triple_exists ge fe func _ _ _ (fun iv => ?_)
  refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨⟨he, ha, hn, hi, hs, _, harr⟩, hlt, hk⟩ := hP
  refine ⟨.Vint (Integers.Int.repr ((iv : _root_.Int) + 1)), ?_, ?_⟩
  · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Econst_int _ tint) ?_
    simp only [typeof]
    rw [semBinop_add_int, repr_add]
  · refine ⟨iv + 1, ⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha,
      (PTree.gso _ _ _ _ hd.i_n).trans hn, ?_, (PTree.gso _ _ _ _ hd.s_i.symm).trans hs,
      trivial, harr⟩, by omega, by omega⟩
    rw [PTree.gss]
    simp

/-- One iteration: `s += a[i]; i++`. -/
theorem body_triple (k : Nat) (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe func (LMid p b ofs0 L f k) bodyStmt (IterR p b ofs0 L f k) :=
  Sep.triple_seq_only ge fe func (sum_triple ge fe p b ofs0 L f k hd hpr hL hno)
    (Sep.triple_fallthrough ge fe func _ _ _ _ (incr_triple ge fe p b ofs0 L f k hd)
      (fun _ _ _ x => x))

/-- The loop: it terminates, and leaves with the sum of all the elements. -/
theorem loop_triple (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616)
    (k : Nat) :
    Sep.Triple ge fe f_sumarray (LInv p b ofs0 L f k) loopStmt (LoopR p b ofs0 L f) := by
  refine Sep.triple_loop ge fe f_sumarray (LoopR p b ofs0 L f) (LInv p b ofs0 L f)
    (LAfter p b ofs0 L f) _ _ (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_sumarray _ (LMid p b ofs0 L f k) _ _ _
      (Sep.triple_conseq ge fe f_sumarray (if_triple ge fe p b ofs0 L f k hL)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (body_triple ge fe p b ofs0 L f k hd hpr hL hno)
  · refine Sep.triple_fallthrough ge fe f_sumarray _ _ _ _
      (Sep.triple_skip ge fe f_sumarray _) (fun e le hp h => ?_)
    obtain ⟨iv, hSt, hiv, hk⟩ := h
    exact ⟨L - iv, by omega, iv, hSt, hiv, rfl⟩

/-- The precondition of the body: the parameters as passed, the array owned. -/
def Pre : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vint (Integers.Int.repr L))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- **The body of `sumarray`**: it returns the sum of the elements and hands
    the array back. -/
theorem sumarray_body (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_sumarray (Pre p b ofs0 L f) fullBody
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p b ofs0 L f } := by
  -- i = 0
  refine Sep.triple_seq_only ge fe f_sumarray (Q := fun e le hp =>
      Pre p b ofs0 L f e le hp ∧ le.get _i = some (.Vint (Integers.Int.repr 0))) ?_ ?_
  · refine Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, ha, hn, harr⟩ := hP
    exact ⟨_, EvalExpr.Econst_int _ tint, ⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha,
      (PTree.gso _ _ _ _ hd.i_n).trans hn, harr⟩, PTree.gss _ _ _⟩
  -- s = 0
  refine Sep.triple_seq_only ge fe f_sumarray (Q := LInv p b ofs0 L f L) ?_ ?_
  · refine Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, ha, hn, harr⟩, hi⟩ := hP
    refine ⟨_, EvalExpr.Econst_int _ tint, 0, ⟨he, (PTree.gso _ _ _ _ hd.s_a).trans ha,
      (PTree.gso _ _ _ _ hd.s_n).trans hn, (PTree.gso _ _ _ _ hd.s_i).trans ?_,
      PTree.gss _ _ _, trivial, harr⟩, by omega, by omega⟩
    simpa using hi
  -- the loop, then `return s`
  refine Sep.triple_seq ge fe f_sumarray _ (Done p b ofs0 L f) _ _ _ ?_ ?_
  · exact Sep.triple_conseq ge fe f_sumarray (loop_triple ge fe p b ofs0 L f hd hpr hL hno L)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)
  · refine Sep.triple_return ge fe f_sumarray _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hs, harr⟩ := h
    refine ⟨.Vint (sumTo f L), .Vint (sumTo f L), m, hp, EvalExpr.Etempvar _s tuint _ hs,
      semCast_uint m _, ?_, ⟨rfl, harr⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

/-! ## As a function specification (VST's `sumarray_spec`) -/

/-- `sumarray_spec`: called with a pointer to an array of `contents.length`
    unsigned integers, readable with permission `p`, it returns the sum of
    `contents` and hands the array back. -/
def sumarraySpec (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
    (contents : List Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tuint, tint]
  tyres := tuint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)]
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents) hp
  post := fun v hp =>
    v = .Vint (listSum contents)
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents) hp
  measure := fun _ => 0

/-- **`sumarray` satisfies `sumarray_spec`** (VST's `body_sumarray`): the
    array is readable (`readable_share sh`), its size is at most
    `Int.max_signed`, and it fits in the address space. -/
theorem sumarray_satisfies (contents : List Integers.Int)
    (hpr : permOrder p .Readable = true)
    (hL : (contents.length : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sumarray)
      (sumarraySpec p b ofs0 contents)
      [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_sumarray _ _
    (Pre p b ofs0 contents.length (elems contents)) (fun m => ?_) ?_
  · refine ⟨PTree.set _n (.Vint (Integers.Int.repr contents.length))
              (PTree.set _a (.Vptr b ofs0) (createUndefTemps f_sumarray.fn_temps)),
            FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    obtain ⟨_, harr⟩ := hpre
    exact ⟨rfl, (PTree.gso _ _ _ _ n_ne_a).trans (PTree.gss _ _ _), PTree.gss _ _ _, harr⟩
  · have h := body_eq ▸ sumarray_body ge (FunctionEntry2 ge) p b ofs0 contents.length
      (elems contents) idents_distinct hpr hL hno
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_sumarray h (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    obtain ⟨hv, harr⟩ := hr
    exact ⟨by rw [hv, sumTo_elems_length], harr⟩

end
end VST.Verif.Sumarray
