/-
  Port of VST's `progs/verif_rotate.v`, first half: `rotate` (`vst/progs/rotate.c`)
  rotates an array of `int`s left by `k` through a `malloc`ed buffer.

      void rotate(int *a, int n, int k) {
        int *b = malloc(sizeof (int) * n);
        if(!b) exit(-1);
        for(int i = 0; i < n-k; i++) b[i] = a[i+k];
        for(int i = n-k; i < n; i++) b[i] = a[i+k-n];
        for(int i = 0; i < n; i++) a[i] = b[i];
        free(b);
      }

  VST's specification:

      DECLARE _rotate
       WITH sh : share, a : val, s : list Z, n : Z, k : Z, gv : globals
       PRE [ tptr tint , tint, tint]
         PROP(writable_share sh; 0 <= n; 0 <= 4 * n <= Ptrofs.max_unsigned; 0 < k < n)
         PARAMS (a; Vint (Int.repr n); Vint (Int.repr k)) GLOBALS (gv)
         SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
       POST [ tvoid ]
         PROP() RETURN()
         SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr (rotate s k))) a).

  Here the array is `arrayU32` (as in `verif_revarray`), `contents` is the list of
  its elements, and `malloc`/`free` are CompCert's own `EF_malloc`/`EF_free`
  (`Sep.mallocSpec`/`Sep.freeSpec`, proved from `Events.v`; no `mem_mgr` is
  needed).  The buffer invariant is VST's `map Vint … ++ Zrepeat Vundef (n-i)`:
  an initialised prefix and a raw suffix (`CCLib.logic.ArrayInit`).  `malloc`
  never returns `NULL` in CompCert's semantics, so the `exit` branch is dead.
  As in `verif_insertionsort`, the program's symbols `malloc` and `free` are
  assumed to name its external functions of those names.  The size bound
  `n < 2^31` (VST gets it from `Vint (Int.repr n)` and `forward_for_simple_bound`)
  and the fact that the array fits in the address space (part of `data_at`) are
  hypotheses.
-/
import VST.progs.rotate
import VST.progs.verif_min
import CCLib
open CC CC.Sep CC.HProp
open Rotate
open VST.Verif.Min (elems)

namespace VST.Verif.Rotate

/-- `sizeof (int) * n`, at type `size_t`, is the size `malloc` is passed. -/
theorem mul_sizeof_eval (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) (n : Nat)
    (hn : (n : _root_.Int) < 2147483648)
    (hle : le.get _n = some (.Vint (Integers.Int.repr n))) :
    EvalExpr ge e le m (.Ebinop .Omul (.Esizeof tint tulong) (.Etempvar _n tint) tulong)
      (Val.Vptrofs (Integers.Ptrofs.repr (4 * n))) := by
  refine EvalExpr.Ebinop .Omul _ _ _ _ _ _ (EvalExpr.Esizeof _ _) (EvalExpr.Etempvar _ _ _ hle) ?_
  simp [Cop.semBinaryOperation, Cop.semMul, Cop.semBinarith, Cop.classifyBinarith, typeof,
    tulong, tint, Cop.binarithType, Cop.semCast, Cop.classifyCast, Val.Vptrofs, Archi.ptr64, sizeof]
  have h1 : Integers.Int.signed (Integers.Int.repr (n : _root_.Int)) = n :=
    toInt_repr_signed _ (by omega) hn
  simp only [Cop.castIntLong, h1, Integers.Ptrofs.to_int64]
  have h4 : ∀ z : _root_.Int, (BitVec.zeroExtend 64 (Integers.Ptrofs.repr z))
      = Integers.Int64.repr z := fun z => by
    show BitVec.setWidth 64 (BitVec.ofInt 64 z) = BitVec.ofInt 64 z
    exact BitVec.setWidth_eq _
  rw [h4, h4, ← Integers.Int64.repr_mul]


/-- `if (!b)` for a weakly valid pointer `b`: the test is false. -/
theorem eval_notbool_ptr (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem) (bb : Block)
    (o : Integers.Ptrofs) (hle : le.get _b = some (.Vptr bb o))
    (hv : Mem.weakValidPointer m bb (Integers.Ptrofs.unsigned o) = true) :
    EvalExpr ge e le m (.Eunop .Onotbool (.Etempvar _b (tptr tint)) tint) (Val.ofBool false) := by
  refine EvalExpr.Eunop .Onotbool _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) ?_
  simp only [Cop.semUnaryOperation, Cop.semNotbool, typeof]
  rw [show tptr tint = Ty.Tpointer tint noattr from rfl, boolVal_ptr_valid m bb o tint noattr hv]
  rfl

/-! ## VST's `rotate` -/

/-- VST's `rotate l k`: `sublist k (Zlength l) l ++ sublist 0 k l`. -/
def rotate {α : Type} (l : List α) (k : Nat) : List α := l.drop k ++ l.take k

/-- The rotated array, as a function of the index. -/
def rot (n k : Nat) (A : Nat → Integers.Int) (j : Nat) : Integers.Int :=
  if j < n - k then A (j + k) else A (j + k - n)

theorem elems_rotate (c : List Integers.Int) (k : Nat) (hk : k ≤ c.length) (j : Nat)
    (hj : j < c.length) : elems (rotate c k) j = rot c.length k (elems c) j := by
  unfold rotate rot elems
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : j < c.length - k
  · rw [if_pos h, List.getElem?_append_left (by simp; omega), List.getElem?_drop,
      Nat.add_comm]
  · rw [if_neg h, List.getElem?_append_right (by simp; omega), List.getElem?_take_of_lt
      (by simp; omega)]
    simp only [List.length_drop]
    congr 2
    omega

/-! ## The specification (VST's `rotate_spec`) -/

/-- `rotate_spec`: the array of `contents.length` `int`s at `a`, writable with
    permission `p`, ends up holding `rotate contents k`. -/
def rotateSpec (p : Permission) (ba : Block) (oa : Integers.Ptrofs)
    (contents : List Integers.Int) (k : Nat) : Sep.FunSpec where
  tyargs := [tptr tint, tint, tint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr ba oa, .Vint (Integers.Int.repr contents.length), .Vint (Integers.Int.repr k)]
    ∧ arrayU32 p ba (Integers.Ptrofs.unsigned oa) contents.length (elems contents) hp
  post := fun v hp =>
    v = .Vundef
    ∧ arrayU32 p ba (Integers.Ptrofs.unsigned oa) contents.length (elems (rotate contents k)) hp
  measure := fun _ => 0

/-! ## The body -/

def callMalloc : Stmt :=
  .Scall (some _t'1) (.Evar _malloc (Ty.Tfunction [tulong] (tptr tvoid) cc_default))
    [.Ebinop .Omul (.Esizeof tint tulong) (.Etempvar _n tint) tulong]
def setB : Stmt := .Sset _b (.Etempvar _t'1 (tptr tvoid))
def ifExit : Stmt :=
  .Sifthenelse (.Eunop .Onotbool (.Etempvar _b (tptr tint)) tint)
    (.Scall none (.Evar _exit (Ty.Tfunction [tint] tvoid cc_default))
      [.Eunop .Oneg (.Econst_int (Integers.Int.repr 1) tint) tint])
    .Sskip
def elemOf (base : Ident) (idx : Expr) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar base (tptr tint)) idx (tptr tint)) tint
def incr (ci : Ident) : Stmt :=
  .Sset ci (.Ebinop .Oadd (.Etempvar ci tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
/-- `t = a[idx]; b[ci] = t;` -/
def fillBody (ci tv : Ident) (idx : Expr) : Stmt :=
  .Ssequence (.Sset tv (elemOf _a idx)) (.Sassign (elemOf _b (.Etempvar ci tint)) (.Etempvar tv tint))
def guard1 : Expr :=
  .Ebinop .Olt (.Etempvar _i__2 tint) (.Ebinop .Osub (.Etempvar _n tint) (.Etempvar _k tint) tint) tint
def idx1 : Expr := .Ebinop .Oadd (.Etempvar _i__2 tint) (.Etempvar _k tint) tint
def idx2 : Expr :=
  .Ebinop .Osub (.Ebinop .Oadd (.Etempvar _i__1 tint) (.Etempvar _k tint) tint) (.Etempvar _n tint) tint
def loopOf (g : Expr) (body incr : Stmt) : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse g .Sskip .Sbreak) body) incr
def loop1 : Stmt := loopOf guard1 (fillBody _i__2 _t'2 idx1) (incr _i__2)
def loop2 : Stmt := loopOf (forGuard _i__1 _n) (fillBody _i__1 _t'3 idx2) (incr _i__1)
/-- `t = b[i]; a[i] = t;` -/
def copyBody : Stmt :=
  .Ssequence (.Sset _t'4 (elemOf _b (.Etempvar _i tint)))
    (.Sassign (elemOf _a (.Etempvar _i tint)) (.Etempvar _t'4 tint))
def loop3 : Stmt := loopOf (forGuard _i _n) copyBody (incr _i)
def callFree : Stmt :=
  .Scall none (.Evar _free (Ty.Tfunction [tptr tvoid] tvoid cc_default)) [.Etempvar _b (tptr tint)]
def setI1 : Stmt := .Sset _i__1 (.Ebinop .Osub (.Etempvar _n tint) (.Etempvar _k tint) tint)
def fullBody : Stmt :=
  .Ssequence (.Ssequence callMalloc setB)
   (.Ssequence ifExit
    (.Ssequence (.Ssequence (.Sset _i__2 (.Econst_int (Integers.Int.repr 0) tint)) loop1)
     (.Ssequence (.Ssequence setI1 loop2)
      (.Ssequence (.Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 0) tint)) loop3)
        callFree))))

theorem body_eq : f_rotate.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (p : Permission) (ba : Block) (oa : Integers.Ptrofs) (n k : Nat)
variable (A : Nat → Integers.Int) (bb : Block)

/-- The size passed to `malloc`. -/
abbrev sz : Integers.Ptrofs := Integers.Ptrofs.repr (4 * (n : _root_.Int))

/-- The temporaries that stay fixed once `b` is set. -/
abbrev TB : List (Ident × Val) :=
  [(_b, .Vptr bb Integers.Ptrofs.zero), (_a, .Vptr ba oa), (_n, .Vint (Integers.Int.repr n)),
   (_k, .Vint (Integers.Int.repr k))]

/-- The array `a`, holding `g`. -/
abbrev HA (g : Nat → Integers.Int) : HProp := arrayU32 p ba (Integers.Ptrofs.unsigned oa) n g

/-- The buffer `b` after `j` elements are copied into it. -/
abbrev Buf (j : Nat) : HProp :=
  arrayU32 .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) j (rot n k A)
    ∗ anyBytes .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + 4 * (j : _root_.Int))
        (4 * (n - j))

/-- The invariant of the two loops filling `b`, with counter `ci`. -/
def FInv (ci : Ident) (j : Nat) : Sep.Assn :=
  LocalSt emptyEnv ((ci, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
    (Buf n k A bb j ∗ (HA p ba oa n A ∗ Sep.mallocToken bb (sz n)))

/-- After the body of a filling loop. -/
def FMid (ci : Ident) (j : Nat) : Sep.Assn :=
  LocalSt emptyEnv ((ci, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
    (Buf n k A bb (j + 1) ∗ (HA p ba oa n A ∗ Sep.mallocToken bb (sz n)))

/-- `a` after `j` elements are copied back. -/
def copied (j : Nat) (x : Nat) : Integers.Int := if x < j then rot n k A x else A x

/-- The invariant of the copying loop. -/
def CInv (j : Nat) : Sep.Assn :=
  LocalSt emptyEnv ((_i, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
    (HA p ba oa n (copied n k A j)
      ∗ (arrayU32 .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) n (rot n k A)
        ∗ Sep.mallocToken bb (sz n)))

def CMid (j : Nat) : Sep.Assn :=
  LocalSt emptyEnv ((_i, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
    (HA p ba oa n (copied n k A (j + 1))
      ∗ (arrayU32 .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) n (rot n k A)
        ∗ Sep.mallocToken bb (sz n)))

end

/-! ## Reading an element -/

private theorem zero_ovf (n : Nat) (hn : (n : _root_.Int) < 2147483648) :
    (0 : _root_.Int) + 4 * (n : _root_.Int) < 18446744073709551616 := by omega

theorem unsigned_zero : Integers.Ptrofs.unsigned Integers.Ptrofs.zero = 0 := by
  simp [Integers.Ptrofs.unsigned, Integers.Ptrofs.zero, Integers.MI.unsigned, Integers.MI.zero]

private theorem no_ovf_mono (A : _root_.Int) (i l : Nat) (hil : i ≤ l)
    (h : A + 4 * (l : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

/-- `base[idx]` for an `int` array in front of the fragment. -/
theorem eval_elem_front {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {Y : HProp}
    {pr : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat} {g : Nat → Integers.Int}
    {hp : Heap} {base : Ident} {idx : Expr} {i : Nat}
    (hpr : permOrder pr .Readable = true)
    (hH : (arrayU32 pr b (Integers.Ptrofs.unsigned ofs0) n g ∗ Y) hp)
    (hag : Heap.Agrees hp m) (hi : i < n) (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (n : _root_.Int) < 18446744073709551616)
    (hb : le.get base = some (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i))) (hty : typeof idx = tint) :
    EvalExpr ge e le m (elemOf base idx) (.Vint (g i)) := by
  obtain ⟨h1, h2, hd, rfl, h1', -⟩ := hH
  exact eval_index_array_int hpr h1' (Heap.Agrees_union_left hag) hi
    (EvalExpr.Etempvar _ _ _ hb) hidx rfl hty
    (elemOfs_unsigned _ ofs0 i (by omega) (no_ovf_mono _ i n (by omega) hno))

/-- The same, for an array that is the first part of the second part of the
    fragment. -/
theorem eval_elem_mid {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {X Y : HProp}
    {pr : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat} {g : Nat → Integers.Int}
    {hp : Heap} {base : Ident} {idx : Expr} {i : Nat}
    (hpr : permOrder pr .Readable = true)
    (hH : (X ∗ (arrayU32 pr b (Integers.Ptrofs.unsigned ofs0) n g ∗ Y)) hp)
    (hag : Heap.Agrees hp m) (hi : i < n) (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (n : _root_.Int) < 18446744073709551616)
    (hb : le.get base = some (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i))) (hty : typeof idx = tint) :
    EvalExpr ge e le m (elemOf base idx) (.Vint (g i)) := by
  obtain ⟨h1, h2, hd, rfl, -, h2'⟩ := hH
  exact eval_elem_front hpr h2' (Heap.Agrees_union_right hd hag) hi hn hno hb hidx hty

/-! ## Index and guard expressions -/

/-- `n - k`. -/
theorem eval_sub_nk {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {n k : Nat} (hkn : k ≤ n)
    (hN : le.get _n = some (.Vint (Integers.Int.repr n)))
    (hK : le.get _k = some (.Vint (Integers.Int.repr k))) :
    EvalExpr ge e le m (.Ebinop .Osub (.Etempvar _n tint) (.Etempvar _k tint) tint)
      (.Vint (Integers.Int.repr ((n - k : Nat) : _root_.Int))) := by
  have hsub : ((n - k : Nat) : _root_.Int) = (n : _root_.Int) - k := by omega
  exact EvalExpr.Ebinop .Osub _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hN) (EvalExpr.Etempvar _ _ _ hK)
    (by simp only [typeof]; rw [semBinop_sub_int, repr_sub, hsub])

/-- `i < n - k`. -/
theorem eval_guard1 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {n k j : Nat}
    (hkn : k ≤ n) (hj : j ≤ n - k) (hn : (n : _root_.Int) < 2147483648)
    (hi : le.get _i__2 = some (.Vint (Integers.Int.repr j)))
    (hN : le.get _n = some (.Vint (Integers.Int.repr n)))
    (hK : le.get _k = some (.Vint (Integers.Int.repr k))) :
    EvalExpr ge e le m guard1 (Val.ofBool (decide (j < n - k))) := by
  have h : EvalExpr ge e le m guard1 (Val.ofBool (Integers.Int.lt (Integers.Int.repr j)
      (Integers.Int.repr ((n - k : Nat) : _root_.Int)))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hi) (eval_sub_nk hkn hN hK)
      (semBinop_lt_int _ _ _ _)
  rw [lt_repr _ _ (by omega) (by omega) (by omega) (by omega)] at h
  simpa using h

/-- `i + k`. -/
theorem eval_idx1 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {k j : Nat}
    (hi : le.get _i__2 = some (.Vint (Integers.Int.repr j)))
    (hK : le.get _k = some (.Vint (Integers.Int.repr k))) :
    EvalExpr ge e le m idx1 (.Vint (Integers.Int.repr ((j + k : Nat) : _root_.Int))) := by
  refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hi)
    (EvalExpr.Etempvar _ _ _ hK) ?_
  simp only [typeof]
  rw [semBinop_add_int, repr_add]
  push_cast
  rfl

/-- `i + k - n`, for `i + k ≥ n`. -/
theorem eval_idx2 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {n k j : Nat} (hjk : n ≤ j + k)
    (hi : le.get _i__1 = some (.Vint (Integers.Int.repr j)))
    (hN : le.get _n = some (.Vint (Integers.Int.repr n)))
    (hK : le.get _k = some (.Vint (Integers.Int.repr k))) :
    EvalExpr ge e le m idx2 (.Vint (Integers.Int.repr ((j + k - n : Nat) : _root_.Int))) := by
  have hsub : ((j + k - n : Nat) : _root_.Int) = (j : _root_.Int) + k - n := by omega
  refine EvalExpr.Ebinop .Osub _ _ _ _ _ _ (EvalExpr.Ebinop .Oadd _ _ _ _ _ _
    (EvalExpr.Etempvar _ _ _ hi) (EvalExpr.Etempvar _ _ _ hK) (semBinop_add_int _ _ _ _))
    (EvalExpr.Etempvar _ _ _ hN) ?_
  simp only [typeof]
  rw [semBinop_sub_int, repr_add, repr_sub, hsub]

/-! ## The loops -/

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (ba : Block) (oa : Integers.Ptrofs)
variable (n k : Nat) (A : Nat → Integers.Int) (bb : Block) (Ret : Val → HProp)

/-- One iteration of a filling loop: `b[j] = a[src]`, where `a[src]` is element
    `j` of the rotated array. -/
theorem fill_body (ci tv : Ident) (idx : Expr) (j src : Nat) (hj : j < n) (hsrc : src < n)
    (hval : A src = rot n k A j) (hpr : permOrder p .Readable = true)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616)
    (hidx : ∀ le m, TempsHold ((ci, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb) le →
      EvalExpr ge emptyEnv le m idx (.Vint (Integers.Int.repr src)))
    (hty : typeof idx = tint)
    (hne : ∀ q ∈ ((ci, Val.Vint (Integers.Int.repr j)) :: TB ba oa n k bb), q.1 ≠ tv) :
    Triple ge fe f_rotate (FInv p ba oa n k A bb ci j) (fillBody ci tv idx)
      { normal := FMid p ba oa n k A bb ci j, brk := Assn.no,
        cont := FMid p ba oa n k A bb ci j, ret := Ret } := by
  unfold fillBody FInv FMid
  refine triple_seq_fwd ge fe f_rotate _ (LocalSt emptyEnv
    ((tv, .Vint (A src)) :: (ci, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
    (Buf n k A bb j ∗ (HA p ba oa n A ∗ Sep.mallocToken bb (sz n)))) _ _ _ ?_ ?_
  · -- `t = a[idx];`
    refine triple_set_local ge fe f_rotate emptyEnv _ _ _ tv _ (.Vint (A src)) (fun _ h => h) hne
      (fun le m hp hT hH hag => ?_)
    exact eval_elem_mid hpr hH hag hsrc hn hno (hT.get (by simp)) (hidx le m hT) hty
  · -- `b[ci] = t;`
    have hst := triple_store_index_init ge fe f_rotate emptyEnv
      ((tv, .Vint (A src)) :: (ci, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
      (HA p ba oa n A ∗ Sep.mallocToken bb (sz n)) (.Etempvar _b (tptr tint)) (.Etempvar ci tint)
      (.Etempvar tv tint) .Freeable bb Integers.Ptrofs.zero n j (rot n k A) (A src) rfl hj hn
      (by rw [unsigned_zero]; exact zero_ovf n hn) (by rw [unsigned_zero]; rfl)
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by simp))) rfl rfl rfl
    refine triple_conseq ge fe f_rotate hst (fun _ _ _ x => x)
      (fun e le hp h => ?_) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    obtain ⟨he, hT, hH⟩ := h
    refine ⟨he, TempsHold_mono (fun q hq => List.mem_cons_of_mem _ hq) hT, ?_⟩
    rwa [arrayU32_congr .Freeable bb (j + 1) (fun x => if x = j then A src else rot n k A x)
      (rot n k A) _ (fun x _ => by by_cases hx : x = j <;> simp [hx, hval])] at hH

/-- The increment of a filling loop. -/
theorem fill_incr (ci : Ident) (j : Nat)
    (hne : ∀ q ∈ TB ba oa n k bb, q.1 ≠ ci) :
    Triple ge fe f_rotate (FMid p ba oa n k A bb ci j) (incr ci)
      (.only (FInv p ba oa n k A bb ci (j + 1))) :=
  triple_set_local ge fe f_rotate emptyEnv _ (TB ba oa n k bb) _ ci _ _
    (fun _ hq => List.mem_cons_of_mem _ hq) hne
    (fun le m hp hT _ _ => eval_incr ci j (hT.get (by simp)))

/-- The first loop: `for (i = 0; i < n - k; i++) b[i] = a[i + k];`. -/
theorem loop1_triple (hkn : k < n) (hpr : permOrder p .Readable = true)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616) :
    Triple ge fe f_rotate (FInv p ba oa n k A bb _i__2 0) loop1
      { normal := FInv p ba oa n k A bb _i__2 (n - k), brk := Assn.no, cont := Assn.no,
        ret := Ret } := by
  unfold loop1 loopOf
  refine triple_for_guard_from ge fe f_rotate guard1 rfl 0 (n - k) (Nat.zero_le _)
    (FInv p ba oa n k A bb _i__2) (FMid p ba oa n k A bb _i__2) _ _ Ret
    (fun j e le hp m hI _ hj => ?_) (fun j _ hj => ?_) (fun j _ hj => ?_)
  · obtain ⟨-, hT, -⟩ := hI
    exact eval_guard1 (by omega) hj hn (hT.get (by simp)) (hT.get (by simp)) (hT.get (by simp))
  · exact fill_body ge fe p ba oa n k A bb Ret _i__2 _t'2 idx1 j (j + k) (by omega) (by omega)
      (by simp [rot, hj]) hpr hn hno
      (fun le m hT => eval_idx1 (hT.get (by simp)) (hT.get (by simp))) rfl (by temps_ne)
  · exact fill_incr ge fe p ba oa n k A bb _i__2 j (by temps_ne)

/-- The second loop: `for (i = n - k; i < n; i++) b[i] = a[i + k - n];`. -/
theorem loop2_triple (hkn : k < n) (hpr : permOrder p .Readable = true)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616) :
    Triple ge fe f_rotate (FInv p ba oa n k A bb _i__1 (n - k)) loop2
      { normal := FInv p ba oa n k A bb _i__1 n, brk := Assn.no, cont := Assn.no,
        ret := Ret } := by
  unfold loop2 loopOf
  refine triple_for_guard_from ge fe f_rotate (forGuard _i__1 _n) rfl (n - k) n (by omega)
    (FInv p ba oa n k A bb _i__1) (FMid p ba oa n k A bb _i__1) _ _ Ret (fun j e le hp m hI _ hj => ?_) (fun j hj0 hj => ?_) (fun j _ hj => ?_)
  · obtain ⟨-, hT, -⟩ := hI
    exact eval_forGuard _i__1 _n j n hn hj (hT.get (by simp)) (hT.get (by simp))
  · exact fill_body ge fe p ba oa n k A bb Ret _i__1 _t'3 idx2 j (j + k - n) (by omega) (by omega)
      (by simp [rot, show ¬ j < n - k from by omega]) hpr hn hno
      (fun le m hT => eval_idx2 (by omega) (hT.get (by simp)) (hT.get (by simp))
        (hT.get (by simp))) rfl (by temps_ne)
  · exact fill_incr ge fe p ba oa n k A bb _i__1 j (by temps_ne)

/-- One iteration of the copying loop: `a[j] = b[j]`. -/
theorem copy_body (j : Nat) (hj : j < n) (hpw : permOrder p .Writable = true)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616) :
    Triple ge fe f_rotate (CInv p ba oa n k A bb j) copyBody
      { normal := CMid p ba oa n k A bb j, brk := Assn.no, cont := CMid p ba oa n k A bb j,
        ret := Ret } := by
  unfold copyBody CInv CMid
  refine triple_seq_fwd ge fe f_rotate _ (LocalSt emptyEnv
    ((_t'4, .Vint (rot n k A j)) :: (_i, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
    (HA p ba oa n (copied n k A j)
      ∗ (arrayU32 .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) n (rot n k A)
        ∗ Sep.mallocToken bb (sz n)))) _ _ _ ?_ ?_
  · -- `t = b[i];`
    refine triple_set_local ge fe f_rotate emptyEnv _ _ _ _t'4 _ (.Vint (rot n k A j))
      (fun _ h => h) (by temps_ne) (fun le m hp hT hH hag => ?_)
    exact eval_elem_mid rfl hH hag hj hn (by rw [unsigned_zero]; exact zero_ovf n hn)
      (hT.get (by simp)) (EvalExpr.Etempvar _ _ _ (hT.get (by simp))) rfl
  · -- `a[i] = t;`
    have hst := triple_store_index_int_frame ge fe f_rotate emptyEnv
      ((_t'4, .Vint (rot n k A j)) :: (_i, .Vint (Integers.Int.repr j)) :: TB ba oa n k bb)
      (arrayU32 .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) n (rot n k A)
        ∗ Sep.mallocToken bb (sz n))
      (.Etempvar _a (tptr tint)) (.Etempvar _i tint) (.Etempvar _t'4 tint) p ba oa n j
      (copied n k A j) (rot n k A j) hpw hj hn hno
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by simp))) rfl rfl rfl
    refine triple_conseq ge fe f_rotate hst (fun _ _ _ x => x)
      (fun e le hp h => ?_) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    obtain ⟨he, hT, hH⟩ := h
    refine ⟨he, TempsHold_mono (fun q hq => List.mem_cons_of_mem _ hq) hT, ?_⟩
    rwa [arrayU32_congr p ba n (fun x => if x = j then rot n k A j else copied n k A j x)
      (copied n k A (j + 1)) _ (fun x _ => by
        by_cases hx : x = j
        · subst hx; simp [copied]
        · simp only [copied, hx, if_false]
          by_cases hxj : x < j
          · simp [hxj, show x < j + 1 from by omega]
          · simp [hxj, show ¬ x < j + 1 from by omega])] at hH

/-- The increment of the copying loop. -/
theorem copy_incr (j : Nat) :
    Triple ge fe f_rotate (CMid p ba oa n k A bb j) (incr _i)
      (.only (CInv p ba oa n k A bb (j + 1))) :=
  triple_set_local ge fe f_rotate emptyEnv _ (TB ba oa n k bb) _ _i _ _
    (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
    (fun le m hp hT _ _ => eval_incr _i j (hT.get (by simp)))

/-- The third loop: `for (i = 0; i < n; i++) a[i] = b[i];`. -/
theorem loop3_triple (hpw : permOrder p .Writable = true)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616) :
    Triple ge fe f_rotate (CInv p ba oa n k A bb 0) loop3
      { normal := CInv p ba oa n k A bb n, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  unfold loop3 loopOf
  exact triple_for_lt ge fe f_rotate _i _n n hn (CInv p ba oa n k A bb) (CMid p ba oa n k A bb)
    copyBody (incr _i) Ret (fun j e le hp h => h.2.1.get (by simp))
    (fun j e le hp h => h.2.1.get (by simp))
    (fun j hj => copy_body ge fe p ba oa n k A bb Ret j hj hpw hn hno)
    (fun j _ => copy_incr ge fe p ba oa n k A bb j) 0 (Nat.zero_le _)

end

/-- The precondition of the body: the parameters, and the array. -/
def Pre (p : Permission) (ba : Block) (oa : Integers.Ptrofs) (n k : Nat)
    (A : Nat → Integers.Int) : Sep.Assn :=
  LocalSt emptyEnv [(_a, .Vptr ba oa), (_n, .Vint (Integers.Int.repr n)),
    (_k, .Vint (Integers.Int.repr k))] (HA p ba oa n A)

/-! ## The straight-line steps -/

theorem unsigned_sz (n : Nat) (hn : (n : _root_.Int) < 2147483648) :
    (Integers.Ptrofs.unsigned (sz n)).toNat = 4 * n := by
  have hmax : Integers.Ptrofs.max_unsigned = 18446744073709551615 := by
    show Integers.MI.max_unsigned Archi.ptrWordsize = _
    rw [Integers.MI.max_unsigned_eq, Integers.MI.modulus_eq, Archi.ptrWordsize_eq]
    rfl
  rw [Integers.Ptrofs.unsigned_repr (by zomega) (by rw [hmax]; zomega)]
  omega

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (ba : Block) (oa : Integers.Ptrofs)
variable (n k : Nat) (A : Nat → Integers.Int)

/-- The fragment right after `b = malloc(…)`. -/
abbrev MStart (bb : Block) : HProp :=
  (Sep.mallocToken bb (sz n) ∗ Sep.mallocPayload bb (sz n)) ∗ HA p ba oa n A

/-- `b = malloc(sizeof (int) * n);` -/
theorem malloc_step (bm : Block) (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default))
    (hn : (n : _root_.Int) < 2147483648) :
    Triple ge fe f_rotate (Pre p ba oa n k A) (.Ssequence callMalloc setB)
      (.only (fun e le hp => ∃ bb, LocalSt emptyEnv (TB ba oa n k bb)
        (MStart p ba oa n A bb) e le hp)) := by
  refine triple_seq_only ge fe f_rotate (Q := fun e le hp => ∃ bb, LocalSt emptyEnv
    ((_t'1, .Vptr bb Integers.Ptrofs.zero) :: [(_a, .Vptr ba oa),
      (_n, .Vint (Integers.Int.repr n)), (_k, .Vint (Integers.Int.repr k))])
    (MStart p ba oa n A bb) e le hp) ?_ ?_
  · refine triple_call_at ge fe f_rotate (Sep.mallocSpec (sz n)) (some _t'1) _ _ _ _ bm _ hfindM
      rfl rfl (fun e le hp m hP _ => ?_)
    obtain ⟨rfl, hT, hA⟩ := hP
    refine ⟨[Val.Vptrofs (sz n)], Heap.emp, hp, Heap.disjoint_emp_left _, (Heap.emp_union _).symm,
      eval_callee_global (PTree.gempty _) hsymM rfl, ?_, ⟨rfl, rfl⟩,
      Sep.malloc_satisfies ge fe (sz n) _ _ _, fun v h1' hpost hd => ?_⟩
    · exact EvalExprlist.cons _ _ _ _ _ _ _ (mul_sizeof_eval ge emptyEnv le m n hn
        (hT.get (by simp))) rfl EvalExprlist.nil
    · obtain ⟨bb, hb⟩ := hpost
      obtain ⟨hv, hb'⟩ := pure_sep_elim hb
      subst hv
      exact ⟨bb, rfl, TempsHold_set (by temps_ne) hT, ⟨h1', hp, hd, rfl, hb', hA⟩⟩
  · refine triple_exists ge fe f_rotate _ _ _ (fun bb => ?_)
    refine triple_conseq ge fe f_rotate (triple_set_local ge fe f_rotate emptyEnv _
      [(_a, .Vptr ba oa), (_n, .Vint (Integers.Int.repr n)), (_k, .Vint (Integers.Int.repr k))]
      _ _b _ (.Vptr bb Integers.Ptrofs.zero) (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bb, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

/-- `if (!b) exit(-1);` — `malloc` never returns `NULL` here. -/
theorem exit_step (bb : Block) (hn0 : 0 < n) (hn : (n : _root_.Int) < 2147483648) :
    Triple ge fe f_rotate (LocalSt emptyEnv (TB ba oa n k bb) (MStart p ba oa n A bb)) ifExit
      (.only (LocalSt emptyEnv (TB ba oa n k bb) (MStart p ba oa n A bb))) := by
  refine triple_if_local ge fe f_rotate emptyEnv _ _ _ false _ _ _
    (fun le m hp hT hH hag => ?_) (triple_skip ge fe f_rotate _)
  refine ⟨_, eval_notbool_ptr ge emptyEnv le m bb Integers.Ptrofs.zero (hT.get (by simp)) ?_,
    boolVal_ofBool_int m false⟩
  obtain ⟨h1, h2, hd, rfl, ⟨ht, hpl, hd', rfl, -, hpay⟩, -⟩ := hH
  have hv := anyBytes_weakValidPointer (mallocPayload_anyBytes hpay)
    (by rw [unsigned_sz n hn]; omega)
    (Heap.Agrees_union_right hd' (Heap.Agrees_union_left hag))
  rwa [unsigned_zero]

/-- `i = 0;` before the first loop. -/
theorem start1_step (bb : Block) (hn : (n : _root_.Int) < 2147483648) :
    Triple ge fe f_rotate (LocalSt emptyEnv (TB ba oa n k bb) (MStart p ba oa n A bb))
      (.Sset _i__2 (.Econst_int (Integers.Int.repr 0) tint))
      (.only (FInv p ba oa n k A bb _i__2 0)) := by
  refine triple_conseq ge fe f_rotate (triple_set_local ge fe f_rotate emptyEnv _ _ _ _i__2 _
    (.Vint (Integers.Int.repr ((0 : Nat) : _root_.Int))) (fun _ h => h) (by temps_ne)
    (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
    (fun _ _ _ x => x) (fun e le hp h => ?_) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ x => x.elim)
  obtain ⟨he, hT, hH⟩ := h
  refine ⟨he, hT, ?_⟩
  rw [MStart, sep_comm_eq (Sep.mallocToken _ _), sep_assoc_eq,
    sep_comm_eq (Sep.mallocToken _ _)] at hH
  obtain ⟨h1, h2, hd, rfl, hpay, hrest⟩ := hH
  refine ⟨h1, h2, hd, rfl, ?_, hrest⟩
  show (emp ∗ _) h1
  rw [emp_sep_eq, unsigned_zero, show (0 : _root_.Int) + 4 * ((0 : Nat) : _root_.Int) = 0 from rfl,
    Nat.sub_zero, ← unsigned_sz n hn]
  exact mallocPayload_anyBytes hpay

/-- `i = n - k;` between the first two loops. -/
theorem setI1_step (bb : Block) (hkn : k ≤ n) :
    Triple ge fe f_rotate (FInv p ba oa n k A bb _i__2 (n - k)) setI1
      (.only (FInv p ba oa n k A bb _i__1 (n - k))) :=
  triple_set_local ge fe f_rotate emptyEnv _ (TB ba oa n k bb) _ _i__1 _ _
    (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
    (fun le m hp hT _ _ => eval_sub_nk hkn (hT.get (by simp)) (hT.get (by simp)))

/-- `i = 0;` before the copying loop: the buffer is full. -/
theorem start3_step (bb : Block) :
    Triple ge fe f_rotate (FInv p ba oa n k A bb _i__1 n)
      (.Sset _i (.Econst_int (Integers.Int.repr 0) tint))
      (.only (CInv p ba oa n k A bb 0)) := by
  refine triple_conseq ge fe f_rotate (triple_set_local ge fe f_rotate emptyEnv _ (TB ba oa n k bb)
    _ _i _ (.Vint (Integers.Int.repr ((0 : Nat) : _root_.Int)))
    (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
    (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
    (fun _ _ _ x => x) (fun e le hp h => ?_) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ x => x.elim)
  obtain ⟨he, hT, hH⟩ := h
  refine ⟨he, hT, ?_⟩
  have hc : copied n k A 0 = A := funext fun x => by simp [copied]
  simp only [Buf, Nat.sub_self, Nat.mul_zero, anyBytes_zero, sep_emp_eq] at hH
  rw [hc, sep_left_comm_eq]
  exact hH

/-- `free(b);` -/
theorem free_step (Ret : Val → HProp) (bb bf : Block)
    (hsymF : Genv.findSymbol ge.genv_genv _free = some bf)
    (hfindF : Genv.findFunct ge.genv_genv (.Vptr bf Integers.Ptrofs.zero)
      = some (.External .EF_free [tptr tvoid] tvoid cc_default))
    (hn : (n : _root_.Int) < 2147483648) :
    Triple ge fe f_rotate (CInv p ba oa n k A bb n) callFree
      { normal := fun e _ hp => e = emptyEnv ∧ HA p ba oa n (rot n k A) hp, brk := Assn.no,
        cont := Assn.no, ret := Ret } := by
  refine triple_conseq ge fe f_rotate (triple_call_at ge fe f_rotate (Sep.freeSpec bb (sz n)) none
    _ _ _ (fun e _ hp => e = emptyEnv ∧ HA p ba oa n (rot n k A) hp) bf _ hfindF rfl rfl
    (fun e le hp m hP _ => ?_))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ x => x.elim)
  obtain ⟨rfl, hT, hH⟩ := hP
  rw [sep_comm_eq (HA _ _ _ _ _), sep_comm_eq (arrayU32 _ _ _ _ _)] at hH
  obtain ⟨h1, h2, hd, rfl, ⟨ht, hb, hd', rfl, htok, harr⟩, hA⟩ := hH
  refine ⟨[.Vptr bb Integers.Ptrofs.zero], Heap.union ht hb, h2, hd, rfl,
    eval_callee_global (PTree.gempty _) hsymF rfl, ?_, ?_, Sep.free_satisfies ge fe bb (sz n) _ _ _,
    fun v h1' hpost _ => ?_⟩
  · exact EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
      (semCast_ptr_ptr _ _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) EvalExprlist.nil
  · refine pure_sep_intro rfl ⟨ht, hb, hd', rfl, htok, ?_⟩
    have h := arrayU32_anyBytes .Freeable bb n (rot n k A) _ hb harr
    rwa [unsigned_zero, ← unsigned_sz n hn] at h
  · obtain ⟨-, rfl⟩ := hpost
    refine ⟨rfl, ?_⟩
    rw [Heap.emp_union]
    have hA' : arrayU32 p ba (Integers.Ptrofs.unsigned oa) n (copied n k A n) h2 := hA
    rwa [arrayU32_congr p ba n (copied n k A n) (rot n k A) _ (fun x hx => by simp [copied, hx])]
      at hA'


end

/-! ## The whole body -/

theorem rotate_body (ge : CGenv) (fe : EntryRel) (p : Permission) (ba : Block)
    (oa : Integers.Ptrofs) (n k : Nat) (A : Nat → Integers.Int) (Ret : Val → HProp)
    (bm bf : Block)
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default))
    (hsymF : Genv.findSymbol ge.genv_genv _free = some bf)
    (hfindF : Genv.findFunct ge.genv_genv (.Vptr bf Integers.Ptrofs.zero)
      = some (.External .EF_free [tptr tvoid] tvoid cc_default))
    (hpw : permOrder p .Writable = true) (hk : 0 < k) (hkn : k < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616) :
    Triple ge fe f_rotate (Pre p ba oa n k A) fullBody
      { normal := fun e _ hp => e = emptyEnv ∧ HA p ba oa n (rot n k A) hp, brk := Assn.no,
        cont := Assn.no, ret := Ret } := by
  have hn0 : 0 < n := by omega
  have hpr := readable_of_writable hpw
  refine triple_seq ge fe f_rotate _ (fun e le hp => ∃ bb, LocalSt emptyEnv (TB ba oa n k bb)
    (MStart p ba oa n A bb) e le hp) _ _ _ ?_ ?_
  · exact triple_conseq ge fe f_rotate (malloc_step ge fe p ba oa n k A bm hsymM hfindM hn)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
      (fun _ _ x => x.elim)
  refine triple_exists ge fe f_rotate _ _ _ (fun bb => ?_)
  refine triple_seq_only ge fe f_rotate (exit_step ge fe p ba oa n k A bb hn0 hn) ?_
  refine triple_seq ge fe f_rotate _ (FInv p ba oa n k A bb _i__2 (n - k)) _ _ _
    (triple_seq_only ge fe f_rotate (start1_step ge fe p ba oa n k A bb hn)
      (loop1_triple ge fe p ba oa n k A bb Ret hkn hpr hn hno)) ?_
  refine triple_seq ge fe f_rotate _ (FInv p ba oa n k A bb _i__1 n) _ _ _
    (triple_seq_only ge fe f_rotate (setI1_step ge fe p ba oa n k A bb (by omega))
      (loop2_triple ge fe p ba oa n k A bb Ret hkn hpr hn hno)) ?_
  refine triple_seq ge fe f_rotate _ (CInv p ba oa n k A bb n) _ _ _
    (triple_seq_only ge fe f_rotate (start3_step ge fe p ba oa n k A bb)
      (loop3_triple ge fe p ba oa n k A bb Ret hpw hn hno)) ?_
  exact free_step ge fe p ba oa n k A Ret bb bf hsymF hfindF hn

/-! ## `rotate` satisfies `rotate_spec` -/

/-- **`rotate` satisfies `rotate_spec`** (VST's `body_rotate`).  `malloc` and
    `free` are the program's external functions of those names. -/
theorem rotate_satisfies (ge : CGenv) (p : Permission) (ba : Block) (oa : Integers.Ptrofs)
    (contents : List Integers.Int) (k : Nat) (bm bf : Block)
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default))
    (hsymF : Genv.findSymbol ge.genv_genv _free = some bf)
    (hfindF : Genv.findFunct ge.genv_genv (.Vptr bf Integers.Ptrofs.zero)
      = some (.External .EF_free [tptr tvoid] tvoid cc_default))
    (hpw : permOrder p .Writable = true) (hk : 0 < k) (hkn : k < contents.length)
    (hn : (contents.length : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_rotate) (rotateSpec p ba oa contents k)
      [.Vptr ba oa, .Vint (Integers.Int.repr contents.length), .Vint (Integers.Int.repr k)] := by
  have hrot : ∀ hp, arrayU32 p ba (Integers.Ptrofs.unsigned oa) contents.length
      (rot contents.length k (elems contents)) hp →
      arrayU32 p ba (Integers.Ptrofs.unsigned oa) contents.length
        (elems (rotate contents k)) hp := by
    intro hp h
    rwa [arrayU32_congr p ba contents.length (elems (rotate contents k)) _ _
      (fun x hx => elems_rotate contents k (by omega) x hx)]
  refine Sep.satisfies_internal_noVars_void ge (FunctionEntry2 ge) f_rotate _ _
    (Pre p ba oa contents.length k (elems contents)) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _) rfl,
      fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> rfl
  · rw [body_eq]
    exact Sep.triple_conseq ge (FunctionEntry2 ge) f_rotate
      (rotate_body ge (FunctionEntry2 ge) p ba oa contents.length k (elems contents)
        (rotateSpec p ba oa contents k).post bm bf hsymM hfindM hsymF hfindF hpw hk hkn hn hno)
      (fun _ _ _ x => x) (fun e le hp h => ⟨h.1, rfl, hrot hp h.2⟩) (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ x => x)

end VST.Verif.Rotate
