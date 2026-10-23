/-
  Port of VST's `progs/verif_min64.v`: `minimum` of `vst/progs/min64.c`
  meets its specification.  This test exercises a `for` loop over a 64-bit
  `long` counter, and loads and stores with a `long` array subscript.

      int minimum(int a[ ], long long n) {
        long long i; int min;
        min=a[0];
        for (i=0; i<n; i++) {
          int j = a[i];
          a[i]=j;  /* to test array-store with 64-bit subscript */
          if (j<min) min=j;
        }
        return min;
      }

  VST's specification:

      DECLARE _minimum
       WITH a: val, n: Z, al: list Z
       PRE [ tptr tint , tlong ]
         PROP  (1 <= n <= Int64.max_signed; Forall repable_signed al)
         PARAMS (a; Vlong (Int64.repr n))
         SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
       POST [ tint ]
         PROP ()
         RETURN (Vint (Int.repr (fold_right Z.min (hd 0 al) al)))
         SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a).

  As in `verif_min` (whose `listMin`, `minTo`, `imin` and `listMin_signed`
  are reused), the array is `arrayU32 p b ofs n f`, here with a *writable*
  permission `p` (VST's `Ews`), since the loop writes each element back.
  `data_at` implies that the array fits in the address space (`hno`); that
  bound also gives `n ≤ Int64.max_signed`.
-/
import VST.progs.min64
import VST.progs.verif_min
open CC CC.Sep CC.HProp
open Min64
open VST.Verif.Min (imin minTo listMin elems minTo_elems_length)

namespace VST.Verif.Min64

/-! ## Facts about the generated program -/

/-- The temporaries `minimum` writes are distinct from the ones it reads. -/
structure Distinct : Prop where
  i_a : _i ≠ _a
  i_n : _i ≠ _n
  i_min : _i ≠ _min
  min_a : _min ≠ _a
  min_n : _min ≠ _n
  min_i : _min ≠ _i
  j_a : _j ≠ _a
  j_n : _j ≠ _n
  j_i : _j ≠ _i
  j_min : _j ≠ _min

theorem idents_distinct : Distinct := by constructor <;> decide

theorem entry_wf :
    listNorepet (varNames f_minimum.fn_vars)
    ∧ listNorepet (varNames f_minimum.fn_params)
    ∧ listDisjoint (varNames f_minimum.fn_params) (varNames f_minimum.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem n_ne_a : _n ≠ _a := by decide

/-- The parts of the body. -/
def elemExpr (idx : Expr) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _a (tptr tint)) idx (tptr tint)) tint
def setMin0 : Stmt := .Sset _min (elemExpr (.Econst_int (Integers.Int.repr 0) tint))
def setI0 : Stmt := .Sset _i (.Ecast (.Econst_int (Integers.Int.repr 0) tint) tlong)
def guardExpr : Expr := .Ebinop .Olt (.Etempvar _i tlong) (.Etempvar _n tlong) tint
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def setJ : Stmt := .Sset _j (elemExpr (.Etempvar _i tlong))
def storeJ : Stmt := .Sassign (elemExpr (.Etempvar _i tlong)) (.Etempvar _j tint)
def minGuard : Expr := .Ebinop .Olt (.Etempvar _j tint) (.Etempvar _min tint) tint
def ifMin : Stmt := .Sifthenelse minGuard (.Sset _min (.Etempvar _j tint)) .Sskip
def bodyStmt : Stmt := .Ssequence setJ (.Ssequence storeJ ifMin)
def incrStmt : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tlong) (.Econst_int (Integers.Int.repr 1) tint) tlong)
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) incrStmt
def retStmt : Stmt := .Sreturn (some (.Etempvar _min tint))
def fullBody : Stmt := .Ssequence setMin0 (.Ssequence (.Ssequence setI0 loopStmt) retStmt)

theorem body_eq : f_minimum.fn_body = fullBody := rfl

/-! ## Assertions

Every assertion is a fact `R e le` about the locals, separated from the array
(`R e le ∧ arrayU32 …`), the shape the array-store rule expects. -/

section
variable (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (L : Nat)
variable (f : Nat → Integers.Int)

/-- The array, owned. -/
def Arr : HProp := arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f

/-- The locals: `a` and `n` as passed, `i = iv`, `min = mv`, `j` as far as set. -/
def Locs (iv : Nat) (mv : Integers.Int) (j : Option Integers.Int) (e : Env) (le : TempEnv) :
    Prop :=
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vlong (Integers.Int64.repr L))
  ∧ le.get _i = some (.Vlong (Integers.Int64.repr iv))
  ∧ le.get _min = some (.Vint mv)
  ∧ (match j with | none => True | some x => le.get _j = some (.Vint x))

/-- The loop invariant, `k` iterations left. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, (Locs b ofs0 L iv (minTo f iv) none e le ∧ iv ≤ L ∧ L - iv = k) ∧ Arr p b ofs0 L f hp

/-- After the guard: `i < n`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, (Locs b ofs0 L iv (minTo f iv) none e le ∧ iv < L ∧ L - iv = k) ∧ Arr p b ofs0 L f hp

/-- After the body, before `i++`. -/
def LAfter (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, (Locs b ofs0 L iv (minTo f (iv + 1)) none e le ∧ iv < L ∧ L - iv = k)
    ∧ Arr p b ofs0 L f hp

/-- After the loop. -/
def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _min = some (.Vint (minTo f L)) ∧ Arr p b ofs0 L f hp

/-- The postcondition. -/
def Ret : Val → HProp := fun v hp => v = .Vint (minTo f L) ∧ Arr p b ofs0 L f hp

def IterR (k : Nat) : Sep.ExitConds :=
  { normal := LAfter p b ofs0 L f k, brk := Done p b ofs0 L f,
    cont := LAfter p b ofs0 L f k, ret := Ret p b ofs0 L f }

def LoopR : Sep.ExitConds :=
  { normal := Done p b ofs0 L f, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := Ret p b ofs0 L f }

end

/-! ## The proof -/

/-- The array fits in the address space, so `n < 2^62`. -/
private theorem L_lt (A : _root_.Int) (L : Nat) (hA : 0 ≤ A)
    (hno : A + 4 * (L : _root_.Int) < 18446744073709551616) :
    (L : _root_.Int) < 9223372036854775808 := by omega

private theorem no_ovf0 (A : _root_.Int) (L : Nat)
    (h : A + 4 * (L : _root_.Int) < 18446744073709551616) :
    A + 4 * ((0 : Nat) : _root_.Int) < 18446744073709551616 := by omega

/-- Storing back the element just read leaves the array unchanged. -/
private theorem update_same (g : Nat → Integers.Int) (i : Nat) :
    (fun j => if j = i then g i else g j) = g := by
  funext j; split <;> simp_all

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block)
variable (ofs0 : Integers.Ptrofs) (L : Nat) (f : Nat → Integers.Int)

/-- The guard `i < n`, evaluated. -/
theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (iv : Nat) (mv : Integers.Int)
    (j : Option Integers.Int) (hL : (L : _root_.Int) < 9223372036854775808) (hiv : iv ≤ L)
    (hl : Locs b ofs0 L iv mv j e le) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (iv < L))) := by
  obtain ⟨_, _, hn, hi, _⟩ := hl
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int64.lt (Integers.Int64.repr iv) (Integers.Int64.repr L))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _i tlong _ hi)
      (EvalExpr.Etempvar _n tlong _ hn) (semBinop_lt_long _ _ _ _)
  rw [lt_repr64 (iv : _root_.Int) (L : _root_.Int) (by omega) (by omega) (by omega) hL] at h
  simpa using h

/-- The `if` at the top of the loop body. -/
theorem if_triple (k : Nat) (hL : (L : _root_.Int) < 9223372036854775808) :
    Sep.Triple ge fe f_minimum (LInv p b ofs0 L f k) ifStmt
      { IterR p b ofs0 L f k with normal := LMid p b ofs0 L f k } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe f_minimum _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, ⟨hl, hiv, hk⟩, _⟩ := hP
      refine ⟨_, eval_guard ge b ofs0 L e le m iv _ none hL hiv hl, ?_⟩
      have : ¬ iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe f_minimum (Sep.triple_break ge fe f_minimum _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨iv, ⟨⟨he, _, _, _, hmin, _⟩, hiv, hk⟩, harr⟩ := h
      have : iv = L := by omega
      subst this
      exact ⟨he, hmin, harr⟩
  | succ j =>
    refine Sep.triple_if_true ge fe f_minimum _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, ⟨hl, hiv, hk⟩, _⟩ := hP
      refine ⟨_, eval_guard ge b ofs0 L e le m iv _ none hL hiv hl, ?_⟩
      have : iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
        (Sep.triple_skip ge fe f_minimum _) (fun e le hp h => ?_)
      obtain ⟨iv, ⟨hl, hiv, hk⟩, harr⟩ := h
      exact ⟨iv, ⟨hl, by omega, hk⟩, harr⟩

/-- The body: `j = a[i]; a[i] = j; if (j < min) min = j;`. -/
theorem body_triple (k : Nat) (hd : Distinct) (hpw : permOrder p .Writable = true)
    (hpr : permOrder p .Readable = true)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_minimum (LMid p b ofs0 L f k) bodyStmt (IterR p b ofs0 L f k) := by
  refine Sep.triple_exists ge fe f_minimum _ _ _ (fun iv => ?_)
  by_cases hlt : iv < L
  case neg =>
    exact Sep.triple_pre ge fe f_minimum (fun _ _ _ h => (hlt h.1.2.1).elim)
      (Sep.triple_vacuous ge fe f_minimum _ _)
  -- the locals once `j` is set
  let Rj : Env → TempEnv → Prop := fun e le =>
    Locs b ofs0 L iv (minTo f iv) (some (f iv)) e le ∧ iv < L ∧ L - iv = k
  show Sep.Triple ge fe f_minimum
    (fun e le hp => (Locs b ofs0 L iv (minTo f iv) none e le ∧ iv < L ∧ L - iv = k)
      ∧ Arr p b ofs0 L f hp) bodyStmt _
  refine Sep.triple_seq_only ge fe f_minimum (Q := fun e le hp => Rj e le ∧ Arr p b ofs0 L f hp)
    ?_ ?_
  · -- j = a[i]
    refine Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨⟨he, ha, hn, hi, hmin, _⟩, hlt, hk⟩, harr⟩ := hP
    refine ⟨.Vint (f iv), ?_, ?_⟩
    · exact eval_index_array_int_long hpr harr hag hlt hno
        (EvalExpr.Etempvar _a (tptr tint) _ ha) (EvalExpr.Etempvar _i tlong _ hi) rfl rfl
    · exact ⟨⟨⟨he, (PTree.gso _ _ _ _ hd.j_a).trans ha, (PTree.gso _ _ _ _ hd.j_n).trans hn,
        (PTree.gso _ _ _ _ hd.j_i).trans hi, (PTree.gso _ _ _ _ hd.j_min).trans hmin,
        PTree.gss _ _ _⟩, hlt, hk⟩, harr⟩
  refine Sep.triple_seq_only ge fe f_minimum (Q := fun e le hp => Rj e le ∧ Arr p b ofs0 L f hp)
    ?_ ?_
  · -- a[i] = j
    have h := triple_store_index_int_long ge fe f_minimum Rj (.Etempvar _a (tptr tint))
      (.Etempvar _i tlong) (.Etempvar _j tint) p b ofs0 L iv f (f iv) hpw hlt hno
      (fun e le m hR => EvalExpr.Etempvar _a (tptr tint) _ hR.1.2.1)
      (fun e le m hR => EvalExpr.Etempvar _i tlong _ hR.1.2.2.2.1)
      (fun e le m hR => EvalExpr.Etempvar _j tint _ hR.1.2.2.2.2.2) rfl rfl rfl
    rw [update_same] at h
    exact h
  · -- if (j < min) min = j;
    refine Sep.triple_if ge fe f_minimum _
      (fun e le hp => (Rj e le ∧ Arr p b ofs0 L f hp) ∧ Integers.Int.lt (f iv) (minTo f iv) = true)
      (fun e le hp => (Rj e le ∧ Arr p b ofs0 L f hp) ∧ Integers.Int.lt (f iv) (minTo f iv) = false)
      _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
    · have hP' := hP
      obtain ⟨⟨⟨_, _, _, _, hmin, hj⟩, _⟩, _⟩ := hP
      refine ⟨Val.ofBool (Integers.Int.lt (f iv) (minTo f iv)),
        Integers.Int.lt (f iv) (minTo f iv), ?_, ?_, ?_⟩
      · exact EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _j tint _ hj)
          (EvalExpr.Etempvar _min tint _ hmin) (semBinop_lt_int _ _ _ _)
      · simpa [minGuard, typeof] using boolVal_ofBool_int m _
      · cases h : Integers.Int.lt (f iv) (minTo f iv) <;> exact ⟨hP', rfl⟩
    · -- min = j
      refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
        (Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
      obtain ⟨⟨⟨⟨he, ha, hn, hi, _, hj⟩, hlt, hk⟩, harr⟩, hcmp⟩ := hP
      refine ⟨.Vint (f iv), EvalExpr.Etempvar _j tint _ hj, iv, ⟨⟨he,
        (PTree.gso _ _ _ _ hd.min_a).trans ha, (PTree.gso _ _ _ _ hd.min_n).trans hn,
        (PTree.gso _ _ _ _ hd.min_i).trans hi, ?_, trivial⟩, hlt, hk⟩, harr⟩
      rw [PTree.gss, minTo, imin, hcmp]; rfl
    · -- skip
      refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
        (Sep.triple_skip ge fe f_minimum _) (fun e le hp hP => ?_)
      obtain ⟨⟨⟨⟨he, ha, hn, hi, hmin, _⟩, hlt, hk⟩, harr⟩, hcmp⟩ := hP
      refine ⟨iv, ⟨⟨he, ha, hn, hi, ?_, trivial⟩, hlt, hk⟩, harr⟩
      rw [minTo, imin, hcmp]; exact hmin

/-- `i++` on the `long` counter: one iteration fewer is left. -/
theorem incr_triple (k : Nat) (hd : Distinct) :
    Sep.Triple ge fe f_minimum (LAfter p b ofs0 L f k) incrStmt
      { normal := fun e le hp => ∃ n', n' < k ∧ LInv p b ofs0 L f n' e le hp,
        brk := Done p b ofs0 L f, cont := Sep.Assn.no, ret := Ret p b ofs0 L f } := by
  refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
    (Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
  obtain ⟨iv, ⟨⟨he, ha, hn, hi, hmin, _⟩, hlt, hk⟩, harr⟩ := hP
  refine ⟨.Vlong (Integers.Int64.repr ((iv : _root_.Int) + 1)), ?_, ?_⟩
  · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _i tlong _ hi)
      (EvalExpr.Econst_int _ tint) ?_
    simp only [typeof]
    rw [semBinop_add_long_int, show Integers.Int.signed (Integers.Int.repr 1) = 1 from rfl,
      repr64_add]
  · refine ⟨L - (iv + 1), by omega, iv + 1, ⟨⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha,
      (PTree.gso _ _ _ _ hd.i_n).trans hn, ?_, (PTree.gso _ _ _ _ hd.i_min).trans hmin,
      trivial⟩, by omega, rfl⟩, harr⟩
    rw [PTree.gss]
    simp

/-- The loop terminates, leaving with the minimum of all the elements. -/
theorem loop_triple (hd : Distinct) (hpw : permOrder p .Writable = true)
    (hpr : permOrder p .Readable = true)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616)
    (k : Nat) :
    Sep.Triple ge fe f_minimum (LInv p b ofs0 L f k) loopStmt (LoopR p b ofs0 L f) := by
  have hL := L_lt _ L (Int.natCast_nonneg _) hno
  refine Sep.triple_loop ge fe f_minimum (LoopR p b ofs0 L f) (LInv p b ofs0 L f)
    (LAfter p b ofs0 L f) _ _ (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_minimum _ (LMid p b ofs0 L f k) _ _ _
      (if_triple ge fe p b ofs0 L f k hL) (body_triple ge fe p b ofs0 L f k hd hpw hpr hno)
  · exact Sep.triple_conseq ge fe f_minimum (incr_triple ge fe p b ofs0 L f k hd)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)

/-- The precondition of the body. -/
def Pre : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vlong (Integers.Int64.repr L))
  ∧ Arr p b ofs0 L f hp

/-- **The body of `minimum`**. -/
theorem minimum_body (hd : Distinct) (hpw : permOrder p .Writable = true)
    (hpr : permOrder p .Readable = true) (hL1 : 1 ≤ L)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_minimum (Pre p b ofs0 L f) fullBody
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p b ofs0 L f } := by
  -- min = a[0]
  refine Sep.triple_seq_only ge fe f_minimum (Q := fun e le hp =>
      Pre p b ofs0 L f e le hp ∧ le.get _min = some (.Vint (f 0))) ?_ ?_
  · refine Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, ha, hn, harr⟩ := hP
    refine ⟨.Vint (f 0), ?_, ⟨he, (PTree.gso _ _ _ _ hd.min_a).trans ha,
      (PTree.gso _ _ _ _ hd.min_n).trans hn, harr⟩, PTree.gss _ _ _⟩
    exact eval_index_array_int (i := 0) hpr harr hag (by omega)
      (EvalExpr.Etempvar _a (tptr tint) _ ha) (EvalExpr.Econst_int _ tint) rfl rfl
      (elemOfs_unsigned ge.genv_cenv ofs0 0 (by omega) (no_ovf0 _ L hno))
  -- i = (long)0; the loop
  refine Sep.triple_seq ge fe f_minimum _ (Done p b ofs0 L f) _ _ _ ?_ ?_
  · refine Sep.triple_seq_only ge fe f_minimum (Q := LInv p b ofs0 L f L) ?_ ?_
    · refine Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨⟨he, ha, hn, harr⟩, hmin⟩ := hP
      refine ⟨.Vlong (Integers.Int64.repr ((0 : Nat) : _root_.Int)),
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ tint) (semCast_int_long _ _), 0,
        ⟨⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha, (PTree.gso _ _ _ _ hd.i_n).trans hn,
        PTree.gss _ _ _, (PTree.gso _ _ _ _ hd.i_min).trans hmin, trivial⟩, by omega, by omega⟩,
        harr⟩
    · exact Sep.triple_conseq ge fe f_minimum
        (loop_triple ge fe p b ofs0 L f hd hpw hpr hno L)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)
  -- return min
  · refine Sep.triple_return ge fe f_minimum _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hmin, harr⟩ := h
    refine ⟨.Vint (minTo f L), .Vint (minTo f L), m, hp, EvalExpr.Etempvar _min tint _ hmin,
      semCast_int m _, ?_, ⟨rfl, harr⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

/-! ## As a function specification (VST's `minimum_spec`) -/

/-- `minimum_spec`: called with a pointer to an array of `contents.length`
    `int`s, writable with permission `p`, and its length as a `long`, it
    returns the minimum of `contents` and hands the array back unchanged. -/
def minimumSpec (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
    (contents : List Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tint, tlong]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr b ofs0, .Vlong (Integers.Int64.repr contents.length)]
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents) hp
  post := fun v hp =>
    v = .Vint (listMin contents)
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents) hp
  measure := fun _ => 0

/-- **`minimum` satisfies `minimum_spec`** (VST's `body_min`): the array is
    writable, non-empty, and fits in the address space. -/
theorem minimum_satisfies (contents : List Integers.Int)
    (hpw : permOrder p .Writable = true)
    (hL1 : 1 ≤ contents.length)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_minimum)
      (minimumSpec p b ofs0 contents)
      [.Vptr b ofs0, .Vlong (Integers.Int64.repr contents.length)] := by
  have hpr : permOrder p .Readable = true := by
    revert hpw; cases p <;> decide
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_minimum _ _
    (Pre p b ofs0 contents.length (elems contents)) (fun m => ?_) ?_
  · refine ⟨PTree.set _n (.Vlong (Integers.Int64.repr contents.length))
              (PTree.set _a (.Vptr b ofs0) (createUndefTemps f_minimum.fn_temps)),
            FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    obtain ⟨_, harr⟩ := hpre
    exact ⟨rfl, (PTree.gso _ _ _ _ n_ne_a).trans (PTree.gss _ _ _), PTree.gss _ _ _, harr⟩
  · have h := body_eq ▸ minimum_body ge (FunctionEntry2 ge) p b ofs0 contents.length
      (elems contents) idents_distinct hpw hpr hL1 hno
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_minimum h (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    obtain ⟨hv, harr⟩ := hr
    exact ⟨by rw [hv, minTo_elems_length], harr⟩

end
end VST.Verif.Min64
