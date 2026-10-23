/-
  Port of VST's `progs/verif_bin_search.v`: `search` of
  `vst/progs/bin_search.c` (binary search in a sorted `int` array) meets its
  specification.

      int search(int a[], int tgt, int lo, int hi){
        int mid, val;
        while(lo < hi){
          mid = (lo + hi) >> 1;
          val = a[mid];
          if (val == tgt) return mid;
          else if (val < tgt) lo = mid + 1;
          else hi = mid;
        }
        return -1;
      }

  VST's specification:

      DECLARE _search
       WITH a: val, sh : share, contents : list Z, tgt : Z, lo : Z, hi : Z
       PRE [ tptr tint, tint, tint, tint ]
         PROP  (readable_share sh; 0 <= lo <= Int.max_signed;
                hi <= Zlength contents <= Int.max_signed;
                Int.min_signed <= hi <= Int.max_signed / 2;
                sorted contents; Forall repable_signed contents; repable_signed tgt)
         PARAMS (a; Vint (Int.repr tgt); Vint (Int.repr lo); Vint (Int.repr hi))
         SEP   (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
       POST [ tint ]
         EX i:Z,
         PROP (if in_dec Z.eq_dec tgt (sublist lo hi contents)
               then Znth i contents = tgt else i = -1)
         RETURN (Vint (Int.repr i))
         SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).

  As in `verif_min`, `contents` is a list of 32-bit integers (so
  `Forall repable_signed` is built in), compared by their signed values;
  `sorted` is `List.Pairwise` on the signed values, and VST's
  `sublist lo hi contents` is `contents.extract lo hi`.  The bounds `lo` and
  `hi` are naturals (VST also allows a negative `hi`, for which the loop is
  not entered).  The postcondition is slightly stronger than VST's: when
  `tgt` occurs, the returned index is in `[lo, hi)`.  `data_at` implies that
  the array fits in the address space (`hno`).

  The proof follows `body_search`: the loop invariant says that `tgt` occurs
  in `[lo, hi)` iff it occurs in the current `[lo', hi')`, and the loop
  terminates because `hi' - lo'` decreases.
-/
import VST.progs.bin_search
import VST.progs.verif_min
open CC CC.Sep CC.HProp
open Bin_search
open VST.Verif.Min (elems)

namespace VST.Verif.BinSearch

/-! ## Sorted lists -/

section Pure
variable (contents : List Integers.Int) (tgt : Integers.Int)

/-- VST's `sorted`, on the signed values. -/
def Sorted : Prop :=
  contents.Pairwise (fun x y => Integers.Int.signed x ≤ Integers.Int.signed y)

/-- `tgt` occurs at an index of `[lo, hi)`. -/
def Found (lo hi : Nat) : Prop := ∃ k, lo ≤ k ∧ k < hi ∧ elems contents k = tgt

theorem elems_eq {i : Nat} (h : i < contents.length) : elems contents i = contents[i] := by
  simp [elems, h]

/-- VST's `sorted_mono`. -/
theorem sorted_mono (hs : Sorted contents) {i j : Nat} (hij : i ≤ j)
    (hj : j < contents.length) :
    Integers.Int.signed (elems contents i) ≤ Integers.Int.signed (elems contents j) := by
  rw [elems_eq contents (by omega), elems_eq contents hj]
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · exact List.pairwise_iff_getElem.mp hs i j (by omega) hj h
  · exact Int.le_refl _

/-- VST's `In_sorted_gt`: if `a[mid] < tgt`, `tgt` can only be right of `mid`. -/
theorem found_right (hs : Sorted contents) {lo mid hi : Nat} (hlo : lo ≤ mid)
    (hhi : hi ≤ contents.length) (hmid : mid < hi)
    (hlt : Integers.Int.signed (elems contents mid) < Integers.Int.signed tgt) :
    Found contents tgt lo hi ↔ Found contents tgt (mid + 1) hi := by
  constructor
  · rintro ⟨k, h1, h2, he⟩
    refine ⟨k, ?_, h2, he⟩
    apply Nat.lt_of_not_le
    intro hk
    have := sorted_mono contents hs hk (by omega)
    rw [he] at this
    exact absurd hlt (Int.not_lt.mpr this)
  · rintro ⟨k, h1, h2, he⟩
    exact ⟨k, by omega, h2, he⟩

/-- VST's `In_sorted_lt`: if `tgt < a[mid]`, `tgt` can only be left of `mid`. -/
theorem found_left (hs : Sorted contents) {lo mid hi : Nat}
    (hhi : hi ≤ contents.length) (hmid : mid < hi)
    (hlt : Integers.Int.signed tgt < Integers.Int.signed (elems contents mid)) :
    Found contents tgt lo hi ↔ Found contents tgt lo mid := by
  constructor
  · rintro ⟨k, h1, h2, he⟩
    refine ⟨k, h1, ?_, he⟩
    apply Nat.lt_of_not_le
    intro hk
    have := sorted_mono contents hs hk (by omega)
    rw [he] at this
    exact absurd hlt (Int.not_lt.mpr this)
  · rintro ⟨k, h1, h2, he⟩
    exact ⟨k, h1, by omega, he⟩

theorem not_found_empty {lo hi : Nat} (h : hi ≤ lo) : ¬ Found contents tgt lo hi := by
  rintro ⟨k, h1, h2, _⟩; omega

/-- Membership in VST's `sublist lo hi contents` is `Found`. -/
theorem mem_extract_iff {lo hi : Nat} (hhi : hi ≤ contents.length) :
    tgt ∈ contents.extract lo hi ↔ Found contents tgt lo hi := by
  rw [List.extract_eq_take_drop, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi', he⟩
    simp only [List.length_take, List.length_drop] at hi'
    refine ⟨lo + i, by omega, by omega, ?_⟩
    rw [elems_eq contents (by omega)]
    simpa [List.getElem_take, List.getElem_drop] using he
  · rintro ⟨k, h1, h2, he⟩
    refine ⟨k - lo, by simp only [List.length_take, List.length_drop]; omega, ?_⟩
    rw [elems_eq contents (by omega)] at he
    simp only [List.getElem_take, List.getElem_drop]
    rw [← he]; congr 1; omega

end Pure

/-! ## The generated program -/

def guardExpr : Expr := .Ebinop .Olt (.Etempvar _lo tint) (.Etempvar _hi tint) tint
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def sumExpr : Expr := .Ebinop .Oadd (.Etempvar _lo tint) (.Etempvar _hi tint) tint
def midExpr : Expr := .Ebinop .Oshr sumExpr (.Econst_int (Integers.Int.repr 1) tint) tint
def setMid : Stmt := .Sset _mid midExpr
def setVal : Stmt :=
  .Sset _val (.Ederef (.Ebinop .Oadd (.Etempvar _a (tptr tint)) (.Etempvar _mid tint)
    (tptr tint)) tint)
def eqGuard : Expr := .Ebinop .Oeq (.Etempvar _val tint) (.Etempvar _tgt tint) tint
def ltGuard : Expr := .Ebinop .Olt (.Etempvar _val tint) (.Etempvar _tgt tint) tint
def setLo : Stmt :=
  .Sset _lo (.Ebinop .Oadd (.Etempvar _mid tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def setHi : Stmt := .Sset _hi (.Etempvar _mid tint)
def retMid : Stmt := .Sreturn (some (.Etempvar _mid tint))
def ifStep : Stmt := .Sifthenelse eqGuard retMid (.Sifthenelse ltGuard setLo setHi)
def bodyStmt : Stmt := .Ssequence setMid (.Ssequence setVal ifStep)
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) .Sskip
def retNeg : Stmt :=
  .Sreturn (some (.Eunop .Oneg (.Econst_int (Integers.Int.repr 1) tint) tint))
def fullBody : Stmt := .Ssequence loopStmt retNeg

theorem body_eq : f_search.fn_body = fullBody := rfl

theorem entry_wf :
    listNorepet (varNames f_search.fn_vars)
    ∧ listNorepet (varNames f_search.fn_params)
    ∧ listDisjoint (varNames f_search.fn_params) (varNames f_search.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Assertions -/

section
variable (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
variable (contents : List Integers.Int) (tgt : Integers.Int) (lo hi : Nat)

/-- The array, owned. -/
def Arr : HProp :=
  arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents)

/-- The locals: `a` and `tgt` as passed, `lo = lo'`, `hi = hi'`, and `mid`,
    `val` as far as set. -/
def Locs (lo' hi' : Nat) (mid val : Option Integers.Int) (e : Env) (le : TempEnv) : Prop :=
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _tgt = some (.Vint tgt)
  ∧ le.get _lo = some (.Vint (Integers.Int.repr lo'))
  ∧ le.get _hi = some (.Vint (Integers.Int.repr hi'))
  ∧ (match mid with | none => True | some x => le.get _mid = some (.Vint x))
  ∧ (match val with | none => True | some x => le.get _val = some (.Vint x))

/-- The facts about the current bounds: `tgt` occurs in `[lo, hi)` iff it
    occurs in `[lo', hi')`. -/
def Bounds (lo' hi' : Nat) : Prop :=
  lo ≤ lo' ∧ lo' ≤ 2147483647 ∧ hi' ≤ hi
  ∧ (Found contents tgt lo hi ↔ Found contents tgt lo' hi')

/-- The loop invariant, with `hi' - lo' = n`. -/
def LInv (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ lo' hi', (Locs b ofs0 tgt lo' hi' none none e le ∧ Bounds contents tgt lo hi lo' hi'
    ∧ hi' - lo' = n) ∧ Arr p b ofs0 contents hp

/-- After the guard: `lo' < hi'`. -/
def LMid (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ lo' hi', (Locs b ofs0 tgt lo' hi' none none e le ∧ Bounds contents tgt lo hi lo' hi'
    ∧ hi' - lo' = n ∧ lo' < hi') ∧ Arr p b ofs0 contents hp

/-- After one iteration: the measure decreased. -/
def LNext (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ n', n' < n ∧ LInv p b ofs0 contents tgt lo hi n' e le hp

/-- After the loop: `tgt` does not occur in `[lo, hi)`. -/
def Done : Sep.Assn := fun e _ hp =>
  e = emptyEnv ∧ ¬ Found contents tgt lo hi ∧ Arr p b ofs0 contents hp

/-- The postcondition: an index of `tgt` in `[lo, hi)` if it occurs there,
    `-1` otherwise, and the array handed back. -/
def Ret : Val → HProp := fun v hp =>
  (∃ i : _root_.Int, v = .Vint (Integers.Int.repr i)
    ∧ (Found contents tgt lo hi → ∃ k : Nat, i = k ∧ lo ≤ k ∧ k < hi ∧ elems contents k = tgt)
    ∧ (¬ Found contents tgt lo hi → i = -1))
  ∧ Arr p b ofs0 contents hp

def IterR (n : Nat) : Sep.ExitConds :=
  { normal := LNext p b ofs0 contents tgt lo hi n, brk := Done p b ofs0 contents tgt lo hi,
    cont := LNext p b ofs0 contents tgt lo hi n, ret := Ret p b ofs0 contents tgt lo hi }

def LoopR : Sep.ExitConds :=
  { normal := Done p b ofs0 contents tgt lo hi, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := Ret p b ofs0 contents tgt lo hi }

end

/-! ## The proof -/

private theorem no_ovf_le (A : _root_.Int) (i n : Nat) (hin : i < n)
    (h : A + 4 * (n : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
variable (contents : List Integers.Int) (tgt : Integers.Int) (lo hi : Nat)

/-- The guard `lo < hi`, evaluated. -/
theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (lo' hi' : Nat) (mid val)
    (hl : Locs b ofs0 tgt lo' hi' mid val e le) (hlo' : lo' ≤ 2147483647)
    (hhi' : hi' ≤ 1073741823) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (lo' < hi'))) := by
  obtain ⟨_, _, _, hlo, hhi, _⟩ := hl
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr lo') (Integers.Int.repr hi'))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _lo tint _ hlo)
      (EvalExpr.Etempvar _hi tint _ hhi) (semBinop_lt_int _ _ _ _)
  rw [lt_repr (lo' : _root_.Int) (hi' : _root_.Int) (by omega) (by omega) (by omega)
    (by omega)] at h
  simpa using h

/-- The `if` at the top of the loop body: continue while `lo < hi`, leave
    (with `tgt` not found) otherwise. -/
theorem if_triple (n : Nat) (hhb : hi ≤ 1073741823) :
    Sep.Triple ge fe f_search (LInv p b ofs0 contents tgt lo hi n) ifStmt
      { IterR p b ofs0 contents tgt lo hi n with normal := LMid p b ofs0 contents tgt lo hi n } := by
  cases n with
  | zero =>
    refine Sep.triple_if_false ge fe f_search _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨lo', hi', ⟨hl, ⟨_, hlo', hhi', _⟩, hn⟩, _⟩ := hP
      refine ⟨_, eval_guard ge b ofs0 tgt e le m lo' hi' _ _ hl hlo' (by omega), ?_⟩
      have : ¬ lo' < hi' := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe f_search (Sep.triple_break ge fe f_search _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨lo', hi', ⟨⟨he, _⟩, ⟨_, _, _, hiff⟩, hn⟩, harr⟩ := h
      exact ⟨he, fun hf => not_found_empty contents tgt (by omega) (hiff.mp hf), harr⟩
  | succ n =>
    refine Sep.triple_if_true ge fe f_search _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨lo', hi', ⟨hl, ⟨_, hlo', hhi', _⟩, hn⟩, _⟩ := hP
      refine ⟨_, eval_guard ge b ofs0 tgt e le m lo' hi' _ _ hl hlo' (by omega), ?_⟩
      have : lo' < hi' := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe f_search _ _ _ _
        (Sep.triple_skip ge fe f_search _) (fun e le hp h => ?_)
      obtain ⟨lo', hi', ⟨hl, hb, hn⟩, harr⟩ := h
      exact ⟨lo', hi', ⟨hl, hb, hn, by omega⟩, harr⟩

/-- One iteration: `mid = (lo + hi) >> 1; val = a[mid];` and either return
    `mid`, or move `lo` or `hi`. -/
theorem body_triple (n : Nat) (hpr : permOrder p .Readable = true) (hs : Sorted contents)
    (hhi : hi ≤ contents.length) (hhb : hi ≤ 1073741823)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.Triple ge fe f_search (LMid p b ofs0 contents tgt lo hi n) bodyStmt
      (IterR p b ofs0 contents tgt lo hi n) := by
  refine Sep.triple_exists ge fe f_search _ _ _ (fun lo' => ?_)
  refine Sep.triple_exists ge fe f_search _ _ _ (fun hi' => ?_)
  -- the facts that do not change during the iteration
  let F : Prop := Bounds contents tgt lo hi lo' hi' ∧ hi' - lo' = n ∧ lo' < hi'
  let mid : Nat := (lo' + hi') / 2
  show Sep.Triple ge fe f_search
    (fun e le hp => (Locs b ofs0 tgt lo' hi' none none e le ∧ F) ∧ Arr p b ofs0 contents hp)
    bodyStmt _
  refine Sep.triple_seq_only ge fe f_search (Q := fun e le hp =>
    (Locs b ofs0 tgt lo' hi' (some (Integers.Int.repr mid)) none e le ∧ F)
      ∧ Arr p b ofs0 contents hp) ?_ ?_
  · -- mid = (lo + hi) >> 1
    refine Sep.triple_set ge fe f_search _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨⟨he, ha, ht, hlo, hhi', _⟩, hF⟩, harr⟩ := hP
    have hF2 := hF
    obtain ⟨⟨_, hlo', hhib, _⟩, _, hlt⟩ := hF2
    refine ⟨.Vint (Integers.Int.repr mid), ?_, ⟨⟨he, (PTree.gso _ _ _ _ (by decide)).trans ha,
      (PTree.gso _ _ _ _ (by decide)).trans ht, (PTree.gso _ _ _ _ (by decide)).trans hlo,
      (PTree.gso _ _ _ _ (by decide)).trans hhi', PTree.gss _ _ _, trivial⟩, hF⟩, harr⟩
    refine EvalExpr.Ebinop .Oshr _ _ _ _ _ _
      (EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _lo tint _ hlo)
        (EvalExpr.Etempvar _hi tint _ hhi') (semBinop_add_int _ _ _ _))
      (EvalExpr.Econst_int _ tint) ?_
    simp only [sumExpr, typeof]
    rw [semBinop_shr_int, repr_add, if_pos (by decide),
      shr_repr_one _ (by omega) (by omega)]
    simp only [mid]
    congr 3
  refine Sep.triple_seq_only ge fe f_search (Q := fun e le hp =>
    (Locs b ofs0 tgt lo' hi' (some (Integers.Int.repr mid)) (some (elems contents mid)) e le ∧ F)
      ∧ Arr p b ofs0 contents hp) ?_ ?_
  · -- val = a[mid]
    refine Sep.triple_set ge fe f_search _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨⟨he, ha, ht, hlo, hhi', hmid, _⟩, hF⟩, harr⟩ := hP
    have hF2 := hF
    obtain ⟨⟨_, hlo', hhib, _⟩, _, hlt⟩ := hF2
    have hmidL : mid < contents.length := by simp only [mid]; omega
    refine ⟨.Vint (elems contents mid), ?_, ⟨⟨he, (PTree.gso _ _ _ _ (by decide)).trans ha,
      (PTree.gso _ _ _ _ (by decide)).trans ht, (PTree.gso _ _ _ _ (by decide)).trans hlo,
      (PTree.gso _ _ _ _ (by decide)).trans hhi', (PTree.gso _ _ _ _ (by decide)).trans hmid,
      PTree.gss _ _ _⟩, hF⟩, harr⟩
    exact eval_index_array_int hpr harr hag hmidL (EvalExpr.Etempvar _a (tptr tint) _ ha)
      (EvalExpr.Etempvar _mid tint _ hmid) rfl rfl
      (elemOfs_unsigned ge.genv_cenv ofs0 mid (by simp only [mid]; omega)
        (no_ovf_le _ mid _ hmidL hno))
  -- the state before the tests
  let Q2 : Sep.Assn := fun e le hp =>
    (Locs b ofs0 tgt lo' hi' (some (Integers.Int.repr mid)) (some (elems contents mid)) e le ∧ F)
      ∧ Arr p b ofs0 contents hp
  refine Sep.triple_if ge fe f_search Q2 (fun e le hp => Q2 e le hp ∧ elems contents mid = tgt)
    (fun e le hp => Q2 e le hp ∧ elems contents mid ≠ tgt) _ _ _ _
    (fun e le hp m hP _ => ?_) ?_ ?_
  · -- val == tgt
    have hP' := hP
    obtain ⟨⟨⟨_, _, ht, _, _, _, hval⟩, _⟩, _⟩ := hP
    refine ⟨_, Integers.Int.eq (elems contents mid) tgt, EvalExpr.Ebinop .Oeq _ _ _ _ _ _ (EvalExpr.Etempvar _val tint _ hval)
      (EvalExpr.Etempvar _tgt tint _ ht) (semBinop_eq_int _ _ _ _), ?_, ?_⟩
    · simpa [eqGuard, typeof] using boolVal_ofBool_int m _
    · rw [eq_decide]
      by_cases h : elems contents mid = tgt
      · rw [decide_eq_true h, if_pos rfl]; exact ⟨hP', h⟩
      · rw [decide_eq_false h, if_neg Bool.false_ne_true]; exact ⟨hP', h⟩
  · -- return mid
    refine Sep.triple_conseq ge fe f_search
      (Sep.triple_return ge fe f_search _ (Ret p b ofs0 contents tgt lo hi) _
        (fun e le hp m hP _ => ?_))
      (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
      (fun _ _ x => x)
    obtain ⟨⟨⟨⟨he, _, _, _, _, hmid, _⟩, ⟨hlo, _, hhib, _⟩, _, hlt⟩, harr⟩, heq⟩ := hP
    have hfound : Found contents tgt lo hi := ⟨mid, by simp only [mid]; omega,
      by simp only [mid]; omega, heq⟩
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _mid tint _ hmid, semCast_int m _, ?_,
      ⟨⟨mid, rfl, fun _ => ⟨mid, rfl, by simp only [mid]; omega,
        by simp only [mid]; omega, heq⟩, fun h => (h hfound).elim⟩, harr⟩,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _
  · -- val < tgt ?
    let Q3 : Sep.Assn := fun e le hp => Q2 e le hp ∧ elems contents mid ≠ tgt
    refine Sep.triple_if ge fe f_search Q3
      (fun e le hp => Q3 e le hp ∧ Integers.Int.signed (elems contents mid)
        < Integers.Int.signed tgt)
      (fun e le hp => Q3 e le hp ∧ ¬ Integers.Int.signed (elems contents mid)
        < Integers.Int.signed tgt) _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
    · have hP' := hP
      obtain ⟨⟨⟨⟨_, _, ht, _, _, _, hval⟩, _⟩, _⟩, _⟩ := hP
      refine ⟨_, Integers.Int.lt (elems contents mid) tgt,
        EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _val tint _ hval)
        (EvalExpr.Etempvar _tgt tint _ ht) (semBinop_lt_int _ _ _ _), ?_, ?_⟩
      · simpa [ltGuard, typeof] using boolVal_ofBool_int m _
      · rw [lt_signed]
        by_cases h : Integers.Int.signed (elems contents mid) < Integers.Int.signed tgt
        · rw [decide_eq_true h, if_pos rfl]; exact ⟨hP', h⟩
        · rw [decide_eq_false h, if_neg Bool.false_ne_true]; exact ⟨hP', h⟩
    · -- lo = mid + 1
      refine Sep.triple_fallthrough ge fe f_search _ _ _ _
        (Sep.triple_set ge fe f_search _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
      obtain ⟨⟨⟨⟨⟨he, ha, ht, _, hhi', hmid, _⟩, ⟨hlo, hlo', hhib, hiff⟩, hn, hlt⟩, harr⟩, _⟩,
        hcmp⟩ := hP
      refine ⟨.Vint (Integers.Int.repr ((mid : _root_.Int) + 1)), ?_, ?_⟩
      · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _mid tint _ hmid)
          (EvalExpr.Econst_int _ tint) ?_
        simp only [typeof]
        rw [semBinop_add_int, repr_add]
      · refine ⟨hi' - (mid + 1), by simp only [mid]; omega, mid + 1, hi',
          ⟨⟨he, (PTree.gso _ _ _ _ (by decide)).trans ha, (PTree.gso _ _ _ _ (by decide)).trans ht,
            by rw [PTree.gss]; simp, (PTree.gso _ _ _ _ (by decide)).trans hhi', trivial, trivial⟩,
          ⟨by simp only [mid]; omega, by simp only [mid]; omega, hhib, ?_⟩, rfl⟩, harr⟩
        exact hiff.trans (found_right contents tgt hs (by simp only [mid]; omega) (by omega)
          (by simp only [mid]; omega) hcmp)
    · -- hi = mid
      refine Sep.triple_fallthrough ge fe f_search _ _ _ _
        (Sep.triple_set ge fe f_search _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
      obtain ⟨⟨⟨⟨⟨he, ha, ht, hlo'', _, hmid, _⟩, ⟨hlo, hlo', hhib, hiff⟩, hn, hlt⟩, harr⟩, hne⟩,
        hcmp⟩ := hP
      have hgt : Integers.Int.signed tgt < Integers.Int.signed (elems contents mid) := by
        have : Integers.Int.signed (elems contents mid) ≠ Integers.Int.signed tgt :=
          fun h => hne (signed_inj h)
        exact Int.lt_iff_le_and_ne.mpr ⟨Int.not_lt.mp hcmp, Ne.symm this⟩
      refine ⟨.Vint (Integers.Int.repr mid), EvalExpr.Etempvar _mid tint _ hmid, ?_⟩
      refine ⟨mid - lo', by simp only [mid]; omega, lo', mid,
        ⟨⟨he, (PTree.gso _ _ _ _ (by decide)).trans ha, (PTree.gso _ _ _ _ (by decide)).trans ht,
          (PTree.gso _ _ _ _ (by decide)).trans hlo'', PTree.gss _ _ _, trivial, trivial⟩,
        ⟨hlo, hlo', by simp only [mid]; omega, ?_⟩, rfl⟩, harr⟩
      exact hiff.trans (found_left contents tgt hs (by omega) (by simp only [mid]; omega) hgt)

/-- The loop: it terminates, and either returns an index of `tgt` or leaves
    knowing that `tgt` does not occur. -/
theorem loop_triple (hpr : permOrder p .Readable = true) (hs : Sorted contents)
    (hhi : hi ≤ contents.length) (hhb : hi ≤ 1073741823)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) (n : Nat) :
    Sep.Triple ge fe f_search (LInv p b ofs0 contents tgt lo hi n) loopStmt
      (LoopR p b ofs0 contents tgt lo hi) := by
  refine Sep.triple_loop ge fe f_search (LoopR p b ofs0 contents tgt lo hi)
    (LInv p b ofs0 contents tgt lo hi) (LNext p b ofs0 contents tgt lo hi) _ _
    (fun n => ?_) (fun n => ?_) n
  · exact Sep.triple_seq ge fe f_search _ (LMid p b ofs0 contents tgt lo hi n) _ _ _
      (if_triple ge fe p b ofs0 contents tgt lo hi n hhb)
      (body_triple ge fe p b ofs0 contents tgt lo hi n hpr hs hhi hhb hno)
  · exact Sep.triple_fallthrough ge fe f_search _ _ _ _ (Sep.triple_skip ge fe f_search _)
      (fun _ _ _ x => x)

/-- **The body of `search`**. -/
theorem search_body (hpr : permOrder p .Readable = true) (hs : Sorted contents)
    (hhi : hi ≤ contents.length) (hhb : hi ≤ 1073741823)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.Triple ge fe f_search (LInv p b ofs0 contents tgt lo hi (hi - lo)) fullBody
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p b ofs0 contents tgt lo hi } := by
  refine Sep.triple_seq ge fe f_search _ (Done p b ofs0 contents tgt lo hi) _ _ _
    (Sep.triple_conseq ge fe f_search
      (loop_triple ge fe p b ofs0 contents tgt lo hi hpr hs hhi hhb hno (hi - lo))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)) ?_
  -- return -1
  refine Sep.triple_return ge fe f_search _ _ _ (fun e le hp m h _ => ?_)
  obtain ⟨he, hnf, harr⟩ := h
  refine ⟨.Vint (Integers.Int.repr (-1)), .Vint (Integers.Int.repr (-1)), m, hp,
    EvalExpr.Eunop .Oneg _ _ _ _ (EvalExpr.Econst_int (Integers.Int.repr 1) tint)
      (by rw [typeof, semUnop_neg_int, neg_repr_one]),
    semCast_int m _, ?_, ⟨⟨-1, rfl, fun hf => (hnf hf).elim, fun _ => rfl⟩, harr⟩,
    fun _ hdj hag => ⟨hdj, hag⟩⟩
  rw [he]; exact freeList_emptyEnv _ _

end

/-! ## As a function specification (VST's `search_spec`) -/

/-- `search_spec`: called with a pointer to a sorted array `contents`
    (readable with permission `p`), a target and bounds `lo`, `hi`, it returns
    an index in `[lo, hi)` holding `tgt` if `tgt` occurs in
    `sublist lo hi contents`, and `-1` otherwise. -/
def searchSpec (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
    (contents : List Integers.Int) (tgt : Integers.Int) (lo hi : Nat) : Sep.FunSpec where
  tyargs := [tptr tint, tint, tint, tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr b ofs0, .Vint tgt, .Vint (Integers.Int.repr lo), .Vint (Integers.Int.repr hi)]
    ∧ Arr p b ofs0 contents hp
  post := fun v hp =>
    (∃ i : _root_.Int, v = .Vint (Integers.Int.repr i)
      ∧ (tgt ∈ contents.extract lo hi →
          ∃ k : Nat, i = k ∧ lo ≤ k ∧ k < hi ∧ contents[k]? = some tgt)
      ∧ (tgt ∉ contents.extract lo hi → i = -1))
    ∧ Arr p b ofs0 contents hp
  measure := fun _ => 0

/-- **`search` satisfies `search_spec`** (VST's `body_search`). -/
theorem search_satisfies (ge : CGenv) (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
    (contents : List Integers.Int) (tgt : Integers.Int) (lo hi : Nat)
    (hpr : permOrder p .Readable = true) (hs : Sorted contents)
    (hlo : lo ≤ 2147483647) (hhi : hi ≤ contents.length) (hhb : hi ≤ 1073741823)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_search)
      (searchSpec p b ofs0 contents tgt lo hi)
      [.Vptr b ofs0, .Vint tgt, .Vint (Integers.Int.repr lo), .Vint (Integers.Int.repr hi)] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_search _ _
    (LInv p b ofs0 contents tgt lo hi (hi - lo)) (fun m => ?_) ?_
  · refine ⟨PTree.set _hi (.Vint (Integers.Int.repr hi)) (PTree.set _lo
      (.Vint (Integers.Int.repr lo)) (PTree.set _tgt (.Vint tgt)
        (PTree.set _a (.Vptr b ofs0) (createUndefTemps f_search.fn_temps)))),
      FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl, fun hp hpre => ?_⟩
    obtain ⟨_, harr⟩ := hpre
    refine ⟨lo, hi, ⟨⟨rfl, ?_, ?_, ?_, PTree.gss _ _ _, trivial, trivial⟩,
      ⟨Nat.le_refl _, hlo, Nat.le_refl _, Iff.rfl⟩, rfl⟩, harr⟩
    · rw [PTree.gso _ _ _ _ (by decide), PTree.gso _ _ _ _ (by decide),
        PTree.gso _ _ _ _ (by decide), PTree.gss]
    · rw [PTree.gso _ _ _ _ (by decide), PTree.gso _ _ _ _ (by decide), PTree.gss]
    · rw [PTree.gso _ _ _ _ (by decide), PTree.gss]
  · have h := body_eq ▸ search_body ge (FunctionEntry2 ge) p b ofs0 contents tgt lo hi
      hpr hs hhi hhb hno
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_search h (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    obtain ⟨⟨i, hv, hf, hnf⟩, harr⟩ := hr
    refine ⟨⟨i, hv, fun hm => ?_, fun hm => hnf fun hf' => hm
      ((mem_extract_iff contents tgt hhi).mpr hf')⟩, harr⟩
    obtain ⟨k, rfl, hk1, hk2, hk⟩ := hf ((mem_extract_iff contents tgt hhi).mp hm)
    refine ⟨k, rfl, hk1, hk2, ?_⟩
    rw [elems_eq contents (by omega)] at hk
    rw [List.getElem?_eq_getElem (by omega), hk]

end VST.Verif.BinSearch
