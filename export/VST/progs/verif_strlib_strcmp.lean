/-
  Port of VST's `progs/verif_strlib.v`, continued: `strcmp` of
  `vst/progs/strlib.c` (`strlen` and `strchr` are in `verif_strlib`).

      int strcmp(const char *str1, const char *str2) {
        size_t i;
        for(i = 0;; i++){
          unsigned char d1 = (unsigned char) str1[i];
          unsigned char d2 = (unsigned char) str2[i];
          if(d1 == 0 && d2 == 0) return 0;
          else if(d1 < d2) return -1;
          else if(d1 > d2) return 1;
        }
      }

  VST's specification:

      strcmp_spec: WITH sh1, sh2, str1, s1 : list byte, str2, s2 : list byte
        PRE [ tptr tschar, tptr tschar ]
          PROP (readable_share sh1; readable_share sh2) PARAMS (str1; str2)
          SEP (cstring sh1 s1 str1; cstring sh2 s2 str2)
        POST [ tint ] EX i : int,
          PROP (if Int.eq_dec i Int.zero then s1 = s2 else s1 <> s2)
          RETURN (Vint i) SEP (cstring sh1 s1 str1; cstring sh2 s2 str2)

  The loop invariant is VST's: the first `i` characters of the two strings
  agree.  The measure is the number of characters left in the shorter
  string: at its end one of `d1`, `d2` is `0`, so the loop returns.
-/
import VST.progs.verif_strlib
open CC CC.Sep CC.HProp
open Strlib

namespace VST.Verif.Strlib

/-- The two strings of `strcmp`. -/
def twoStrings (p1 p2 : Permission) (b1 : Block) (o1 : Integers.Ptrofs) (b2 : Block)
    (o2 : Integers.Ptrofs) (s1 s2 : List Nat) : HProp :=
  cstring p1 b1 (Integers.Ptrofs.unsigned o1) s1 ∗ cstring p2 b2 (Integers.Ptrofs.unsigned o2) s2

/-- `strcmp_spec`: the result is `0` exactly when the strings are equal. -/
def strcmpSpec (p1 p2 : Permission) (b1 : Block) (o1 : Integers.Ptrofs) (b2 : Block)
    (o2 : Integers.Ptrofs) (s1 s2 : List Nat) : Sep.FunSpec where
  tyargs := [tptr tuchar, tptr tuchar]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b1 o1, .Vptr b2 o2]
    ∧ twoStrings p1 p2 b1 o1 b2 o2 s1 s2 hp
  post := fun v hp => (∃ r, v = .Vint r ∧ (r = Integers.Int.zero ↔ s1 = s2))
    ∧ twoStrings p1 p2 b1 o1 b2 o2 s1 s2 hp
  measure := fun _ => 0

namespace Strcmp

/-- `return a;` for an `int` expression `a` with a known value, from a
    function returning `int` without local variables. -/
theorem triple_return_int (ge : CGenv) (fe : EntryRel) (f : Function) (P : Sep.Assn)
    (R : Sep.ExitConds) (a : Expr) (k : Integers.Int) (hret : f.fn_return = tint)
    (hty : typeof a = tint) (hev : ∀ e le m, EvalExpr ge e le m a (.Vint k))
    (h : ∀ e le hp, P e le hp → e = emptyEnv ∧ R.ret (.Vint k) hp) :
    Sep.Triple ge fe f P (.Sreturn (some a)) R :=
  Sep.triple_conseq ge fe f
    (Sep.triple_return ge fe f P R.ret a (fun e le hp m hP _ => by
      obtain ⟨he, hR⟩ := h e le hp hP
      exact ⟨_, _, m, hp, hev e le m, by rw [hty, hret]; exact semCast_int m k,
        by rw [he]; exact freeList_emptyEnv _ _, hR, fun _ hdj hag => ⟨hdj, hag⟩⟩))
    (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => x)

def readAt (str : Ident) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar str (tptr tuchar)) (.Etempvar _i tulong) (tptr tuchar)) tuchar

def load (t d str : Ident) : Stmt :=
  .Ssequence (.Sset t (readAt str)) (.Sset d (.Ecast (.Ecast (.Etempvar t tuchar) tuchar) tuchar))

def setT : Stmt :=
  .Sifthenelse (.Ebinop .Oeq (.Etempvar _d1 tuchar) (.Econst_int (Integers.Int.repr 0) tint) tint)
    (.Sset _t'1 (.Ecast (.Ebinop .Oeq (.Etempvar _d2 tuchar)
      (.Econst_int (Integers.Int.repr 0) tint) tint) tbool))
    (.Sset _t'1 (.Econst_int (Integers.Int.repr 0) tint))

def tests : Stmt :=
  .Sifthenelse (.Etempvar _t'1 tint) (.Sreturn (some (.Econst_int (Integers.Int.repr 0) tint)))
    (.Sifthenelse (.Ebinop .Olt (.Etempvar _d1 tuchar) (.Etempvar _d2 tuchar) tint)
      (.Sreturn (some (.Eunop .Oneg (.Econst_int (Integers.Int.repr 1) tint) tint)))
      (.Sifthenelse (.Ebinop .Ogt (.Etempvar _d1 tuchar) (.Etempvar _d2 tuchar) tint)
        (.Sreturn (some (.Econst_int (Integers.Int.repr 1) tint))) .Sskip))

def loopBody : Stmt :=
  .Ssequence .Sskip (.Ssequence (load _t'2 _d1 _str1)
    (.Ssequence (load _t'3 _d2 _str2) (.Ssequence setT tests)))

theorem body_eq : f_strcmp.fn_body =
    .Ssequence (.Sset _i (.Ecast (.Econst_int (Integers.Int.repr 0) tint) tulong))
      (.Sloop loopBody Strlen.s2) := rfl

section
variable (p1 p2 : Permission) (b1 : Block) (o1 : Integers.Ptrofs) (b2 : Block)
  (o2 : Integers.Ptrofs) (s1 s2 : List Nat)

def Facts (i : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _str1 = some (.Vptr b1 o1) ∧ le.get _str2 = some (.Vptr b2 o2)
    ∧ le.get _i = some (.Vlong (Integers.Int64.repr i)) ∧ twoStrings p1 p2 b1 o1 b2 o2 s1 s2 hp

/-- The first `i` characters agree. -/
def Same (i : Nat) : Prop := ∀ j < i, s1.getD j 0 = s2.getD j 0

/-- The loop invariant, `n` characters left in the shorter string. -/
def Inv (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = min s1.length s2.length ∧ Same s1 s2 i ∧ Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp

/-- After the tests: character `i` is the same non-zero character in both. -/
def Mid (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = min s1.length s2.length ∧ i < min s1.length s2.length ∧ Same s1 s2 (i + 1)
    ∧ Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp

/-- During the body: `q` holds of `i`, `d1` (`k1`) and `d2` (`k2`) hold the
    characters `i` of the strings (when `k1`, `k2`), `t'1` holds `t i` (when
    given). -/
def During (n : Nat) (q : Nat → Prop) (k1 k2 : Bool) (t : Option (Nat → Val)) : Sep.Assn :=
  fun e le hp => ∃ i, i + n = min s1.length s2.length ∧ Same s1 s2 i ∧ q i
    ∧ (k1 → le.get _d1 = some (.Vint (Integers.Int.repr (s1.getD i 0))))
    ∧ (k2 → le.get _d2 = some (.Vint (Integers.Int.repr (s2.getD i 0))))
    ∧ (∀ tv, t = some tv → le.get _t'1 = some (tv i))
    ∧ Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp

def LoopR : Sep.ExitConds :=
  { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := (strcmpSpec p1 p2 b1 o1 b2 o2 s1 s2).post }

abbrev BodyR (n : Nat) : Sep.ExitConds :=
  { normal := Mid p1 p2 b1 o1 b2 o2 s1 s2 n, brk := (LoopR p1 p2 b1 o1 b2 o2 s1 s2).normal,
    cont := Mid p1 p2 b1 o1 b2 o2 s1 s2 n, ret := (LoopR p1 p2 b1 o1 b2 o2 s1 s2).ret,
    goto := (LoopR p1 p2 b1 o1 b2 o2 s1 s2).goto }

/-- The value of `t'1`: whether both characters are `0`. -/
def bothZero (i : Nat) : Val := Val.ofBool (decide (s1.getD i 0 = 0 ∧ s2.getD i 0 = 0))

end

section
variable (ge : CGenv) (fe : EntryRel) (p1 p2 : Permission) (b1 : Block) (o1 : Integers.Ptrofs)
  (b2 : Block) (o2 : Integers.Ptrofs) (s1 s2 : List Nat)
  (hpr1 : permOrder p1 .Readable = true) (hpr2 : permOrder p2 .Readable = true)
  (hno1 : o1.toNat + s1.length + 1 ≤ 18446744073709551616)
  (hno2 : o2.toNat + s2.length + 1 ≤ 18446744073709551616)

theorem semCast_ofBool_bool (m : Mem) (b : Bool) :
    Cop.semCast (Val.ofBool b) tint tbool m = some (Val.ofBool b) := by
  cases b <;> rfl

theorem facts_set {i : Nat} {e : Env} {le : TempEnv} {hp : Heap} (x : Ident) (v : Val)
    (hx1 : x ≠ _str1) (hx2 : x ≠ _str2) (hx3 : x ≠ _i)
    (h : Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp) :
    Facts p1 p2 b1 o1 b2 o2 s1 s2 i e (le.set x v) hp := by
  obtain ⟨he, h1, h2, hii, hs⟩ := h
  exact ⟨he, (PTree.gso _ _ _ _ hx1).trans h1, (PTree.gso _ _ _ _ hx2).trans h2,
    (PTree.gso _ _ _ _ hx3).trans hii, hs⟩

/-- The characters are bytes. -/
theorem bytes {i : Nat} {e : Env} {le : TempEnv} {hp : Heap}
    (h : Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp) : s1.getD i 0 < 256 ∧ s2.getD i 0 < 256 := by
  obtain ⟨-, -, -, -, h1, h2, -, -, hc1, hc2⟩ := h
  exact ⟨cstring_byte (pure_sep_elim hc1).1 i, cstring_byte (pure_sep_elim hc2).1 i⟩

/-- `d == 0` is the end of the string. -/
theorem zero_iff {i : Nat} {e : Env} {le : TempEnv} {hp : Heap}
    (h : Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp) (hi : i ≤ min s1.length s2.length) :
    (s1.getD i 0 = 0 ↔ i = s1.length) ∧ (s2.getD i 0 = 0 ↔ i = s2.length) := by
  obtain ⟨-, -, -, -, h1, h2, -, -, hc1, hc2⟩ := h
  exact ⟨cstring_zero_iff (pure_sep_elim hc1).1 (by omega),
    cstring_zero_iff (pure_sep_elim hc2).1 (by omega)⟩

include hpr1 hpr2 hno1 hno2 in
/-- `str1[i]` and `str2[i]`. -/
theorem eval_read {i : Nat} {e : Env} {le : TempEnv} {hp : Heap} {m : Mem}
    (h : Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp) (hag : Heap.Agrees hp m)
    (hi : i ≤ min s1.length s2.length) :
    EvalExpr ge e le m (readAt _str1) (.Vint (Integers.Int.repr (s1.getD i 0)))
      ∧ EvalExpr ge e le m (readAt _str2) (.Vint (Integers.Int.repr (s2.getD i 0))) := by
  obtain ⟨-, hstr1, hstr2, hii, h1, h2, hd, rfl, hc1, hc2⟩ := h
  obtain ⟨hs1, harr1⟩ := pure_sep_elim hc1
  obtain ⟨hs2, harr2⟩ := pure_sep_elim hc2
  exact ⟨eval_index_bytes_ulong (f := fun j => s1.getD j 0) (i := i) hpr1 harr1 (Heap.Agrees_union_left hag) (by omega)
      (cstring_byte hs1) hstr1 (EvalExpr.Etempvar _ _ _ hii) rfl (by omega),
    eval_index_bytes_ulong (f := fun j => s2.getD j 0) (i := i) hpr2 harr2 (Heap.Agrees_union_right hd hag) (by omega)
      (cstring_byte hs2) hstr2 (EvalExpr.Etempvar _ _ _ hii) rfl (by omega)⟩

include hpr1 hpr2 hno1 hno2 in
/-- `t'2 = str1[i]; d1 = (unsigned char) (unsigned char) t'2;` -/
theorem load1_triple (n : Nat) :
    Sep.Triple ge fe f_strcmp (Inv p1 p2 b1 o1 b2 o2 s1 s2 n) (load _t'2 _d1 _str1)
      (.only (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun _ => True) true false none)) := by
  · refine Sep.triple_seq_only ge fe f_strcmp (Q := fun e le hp => ∃ i,
      i + n = min s1.length s2.length ∧ Same s1 s2 i
      ∧ le.get _t'2 = some (.Vint (Integers.Int.repr (s1.getD i 0)))
      ∧ Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp) ?_ ?_
    · refine Sep.triple_set ge fe f_strcmp _ _ _ _ (fun e le hp m hP hag => ?_)
      obtain ⟨i, hi, hsame, hF⟩ := hP
      exact ⟨_, (eval_read ge p1 p2 b1 o1 b2 o2 s1 s2 hpr1 hpr2 hno1 hno2 hF hag (by omega)).1,
        i, hi, hsame, PTree.gss _ _ _,
        facts_set p1 p2 b1 o1 b2 o2 s1 s2 _ _ (by decide) (by decide) (by decide) hF⟩
    · refine Sep.triple_set ge fe f_strcmp _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨i, hi, hsame, ht, hF⟩ := hP
      have hb := (bytes p1 p2 b1 o1 b2 o2 s1 s2 hF).1
      exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ ht)
          (semCast_uchar_byte m _ hb)) (semCast_uchar_byte m _ hb),
        i, hi, hsame, trivial, fun _ => PTree.gss _ _ _, (fun h => nomatch h),
        (fun _ h => nomatch h),
        facts_set p1 p2 b1 o1 b2 o2 s1 s2 _ _ (by decide) (by decide) (by decide) hF⟩
include hpr1 hpr2 hno1 hno2 in
/-- `t'3 = str2[i]; d2 = (unsigned char) (unsigned char) t'3;` -/
theorem load2_triple (n : Nat) :
    Sep.Triple ge fe f_strcmp
      (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun _ => True) true false none) (load _t'3 _d2 _str2)
      (.only (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun _ => True) true true none)) := by
  · refine Sep.triple_seq_only ge fe f_strcmp (Q := fun e le hp => ∃ i,
      i + n = min s1.length s2.length ∧ Same s1 s2 i
      ∧ le.get _d1 = some (.Vint (Integers.Int.repr (s1.getD i 0)))
      ∧ le.get _t'3 = some (.Vint (Integers.Int.repr (s2.getD i 0)))
      ∧ Facts p1 p2 b1 o1 b2 o2 s1 s2 i e le hp) ?_ ?_
    · refine Sep.triple_set ge fe f_strcmp _ _ _ _ (fun e le hp m hP hag => ?_)
      obtain ⟨i, hi, hsame, -, hd1, -, -, hF⟩ := hP
      exact ⟨_, (eval_read ge p1 p2 b1 o1 b2 o2 s1 s2 hpr1 hpr2 hno1 hno2 hF hag (by omega)).2,
        i, hi, hsame, (PTree.gso _ _ _ _ (by decide)).trans (hd1 rfl), PTree.gss _ _ _,
        facts_set p1 p2 b1 o1 b2 o2 s1 s2 _ _ (by decide) (by decide) (by decide) hF⟩
    · refine Sep.triple_set ge fe f_strcmp _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨i, hi, hsame, hd1, ht, hF⟩ := hP
      have hb := (bytes p1 p2 b1 o1 b2 o2 s1 s2 hF).2
      exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ ht)
          (semCast_uchar_byte m _ hb)) (semCast_uchar_byte m _ hb),
        i, hi, hsame, trivial, fun _ => (PTree.gso _ _ _ _ (by decide)).trans hd1,
        fun _ => PTree.gss _ _ _, (fun _ h => nomatch h),
        facts_set p1 p2 b1 o1 b2 o2 s1 s2 _ _ (by decide) (by decide) (by decide) hF⟩

theorem setT_triple (n : Nat) :
    Sep.Triple ge fe f_strcmp (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun _ => True) true true none)
      setT (.only (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun _ => True) true true
        (some (bothZero s1 s2)))) := by
  refine Sep.triple_if ge fe f_strcmp _
    (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun i => s1.getD i 0 = 0) true true none)
    (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun i => s1.getD i 0 ≠ 0) true true none) _ _ _ _
    (fun e le hp m hP _ => ?_) ?_ ?_
  · obtain ⟨i, hi, hsame, -, hd1, hd2, ht, hF⟩ := hP
    have hb := bytes p1 p2 b1 o1 b2 o2 s1 s2 hF
    refine ⟨_, _, eval_eq_uchar (c := 0) hb.1 (by decide) (EvalExpr.Econst_int _ _) rfl (hd1 rfl),
      boolVal_ofBool_int m _, ?_⟩
    by_cases h : s1.getD i 0 = 0
    · simp only [h, decide_true, if_true]
      exact ⟨i, hi, hsame, h, hd1, hd2, ht, hF⟩
    · simp only [h, decide_false]
      exact ⟨i, hi, hsame, h, hd1, hd2, ht, hF⟩
  · refine Sep.triple_set ge fe f_strcmp _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨i, hi, hsame, h0, hd1, hd2, -, hF⟩ := hP
    have hb := bytes p1 p2 b1 o1 b2 o2 s1 s2 hF
    refine ⟨_, EvalExpr.Ecast _ _ _ _
        (eval_eq_uchar (c := 0) hb.2 (by decide) (EvalExpr.Econst_int _ _) rfl (hd2 rfl))
        (semCast_ofBool_bool m _),
      i, hi, hsame, trivial, fun h => (PTree.gso _ _ _ _ (by decide)).trans (hd1 h),
      fun h => (PTree.gso _ _ _ _ (by decide)).trans (hd2 h), fun tv htv => ?_,
      facts_set p1 p2 b1 o1 b2 o2 s1 s2 _ _ (by decide) (by decide) (by decide) hF⟩
    cases htv
    rw [PTree.gss]
    by_cases h2 : s2.getD i 0 = 0
    · simp only [bothZero, h0, h2, and_self, decide_true]
    · simp only [bothZero, h0, h2, true_and, decide_false]
  · refine Sep.triple_set ge fe f_strcmp _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨i, hi, hsame, h0, hd1, hd2, -, hF⟩ := hP
    refine ⟨_, EvalExpr.Econst_int _ _, i, hi, hsame, trivial,
      fun h => (PTree.gso _ _ _ _ (by decide)).trans (hd1 h),
      fun h => (PTree.gso _ _ _ _ (by decide)).trans (hd2 h), fun tv htv => ?_,
      facts_set p1 p2 b1 o1 b2 o2 s1 s2 _ _ (by decide) (by decide) (by decide) hF⟩
    cases htv
    rw [PTree.gss]
    simp only [bothZero, h0, false_and, decide_false]
    rfl

theorem tests_triple (n : Nat) :
    Sep.Triple ge fe f_strcmp (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun _ => True) true true
      (some (bothZero s1 s2))) tests (BodyR p1 p2 b1 o1 b2 o2 s1 s2 n) := by
  -- the characters differ: the strings differ
  have hne : ∀ i, s1.getD i 0 ≠ s2.getD i 0 → s1 ≠ s2 := fun i h heq => h (heq ▸ rfl)
  refine Sep.triple_if ge fe f_strcmp _
    (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun i => s1.getD i 0 = 0 ∧ s2.getD i 0 = 0) false false
      none)
    (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun i => ¬(s1.getD i 0 = 0 ∧ s2.getD i 0 = 0)) true true
      none) _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
  · obtain ⟨i, hi, hsame, -, hd1, hd2, ht, hF⟩ := hP
    refine ⟨_, _, EvalExpr.Etempvar _ _ _ (ht _ rfl), boolVal_ofBool_int m _, ?_⟩
    by_cases h : s1.getD i 0 = 0 ∧ s2.getD i 0 = 0
    · simp only [h, and_self, decide_true, if_true]
      exact ⟨i, hi, hsame, h, (fun h => nomatch h), (fun h => nomatch h), (fun _ h => nomatch h), hF⟩
    · simp only [h, decide_false]
      exact ⟨i, hi, hsame, h, hd1, hd2, (fun _ h => nomatch h), hF⟩
  -- `return 0;`
  · refine triple_return_int ge fe f_strcmp _ _ _ _ rfl rfl
      (fun _ _ _ => EvalExpr.Econst_int _ _) (fun e le hp h => ?_)
    obtain ⟨i, hi, hsame, ⟨h1, h2⟩, -, -, -, hF⟩ := h
    have hz := zero_iff p1 p2 b1 o1 b2 o2 s1 s2 hF (by omega)
    have hl1 := hz.1.mp h1
    have hl2 := hz.2.mp h2
    refine ⟨hF.1, ⟨_, rfl, iff_of_true rfl (list_eq_of_getD (by omega) fun j hj => ?_)⟩,
      hF.2.2.2.2⟩
    exact hsame j (by omega)
  · refine Sep.triple_if ge fe f_strcmp _
      (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun i => s1.getD i 0 < s2.getD i 0) false false none)
      (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun i => ¬(s1.getD i 0 = 0 ∧ s2.getD i 0 = 0)
        ∧ ¬ s1.getD i 0 < s2.getD i 0) true true none) _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
    · obtain ⟨i, hi, hsame, hq, hd1, hd2, -, hF⟩ := hP
      have hb := bytes p1 p2 b1 o1 b2 o2 s1 s2 hF
      refine ⟨_, _, eval_lt_uchar hb.1 hb.2 (hd1 rfl) (hd2 rfl), boolVal_ofBool_int m _, ?_⟩
      by_cases h : s1.getD i 0 < s2.getD i 0
      · simp only [h, decide_true, if_true]
        exact ⟨i, hi, hsame, h, (fun h => nomatch h), (fun h => nomatch h), (fun _ h => nomatch h), hF⟩
      · simp only [h, decide_false]
        exact ⟨i, hi, hsame, ⟨hq, h⟩, hd1, hd2, (fun _ h => nomatch h), hF⟩
    -- `return -1;`
    · refine triple_return_int ge fe f_strcmp _ _ _ _ rfl rfl
        (fun _ _ _ => EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Econst_int _ _) (semUnop_neg_int _ _))
        (fun e le hp h => ?_)
      obtain ⟨i, -, -, hlt, -, -, -, hF⟩ := h
      exact ⟨hF.1, ⟨_, rfl, iff_of_false (by decide) (hne i (by omega))⟩, hF.2.2.2.2⟩
    · refine Sep.triple_if ge fe f_strcmp _
        (During p1 p2 b1 o1 b2 o2 s1 s2 n (fun i => s2.getD i 0 < s1.getD i 0) false false none)
        (Mid p1 p2 b1 o1 b2 o2 s1 s2 n) _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
      · obtain ⟨i, hi, hsame, ⟨hq1, hq2⟩, hd1, hd2, -, hF⟩ := hP
        have hb := bytes p1 p2 b1 o1 b2 o2 s1 s2 hF
        refine ⟨_, _, eval_gt_uchar hb.1 hb.2 (hd1 rfl) (hd2 rfl), boolVal_ofBool_int m _, ?_⟩
        by_cases h : s2.getD i 0 < s1.getD i 0
        · simp only [h, decide_true, if_true]
          exact ⟨i, hi, hsame, h, (fun h => nomatch h), (fun h => nomatch h), (fun _ h => nomatch h),
            hF⟩
        · simp only [h, decide_false]
          have heq : s1.getD i 0 = s2.getD i 0 := by omega
          have hz := zero_iff p1 p2 b1 o1 b2 o2 s1 s2 hF (by omega)
          have h1 : s1.getD i 0 ≠ 0 := fun h0 => hq1 ⟨h0, heq ▸ h0⟩
          have h2 : s2.getD i 0 ≠ 0 := heq ▸ h1
          have hl1 := mt hz.1.mpr h1
          have hl2 := mt hz.2.mpr h2
          refine ⟨i, hi, by omega, fun j hj => ?_, hF⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hsame j hj
          · exact heq
      -- `return 1;`
      · refine triple_return_int ge fe f_strcmp _ _ _ _ rfl rfl
          (fun _ _ _ => EvalExpr.Econst_int _ _) (fun e le hp h => ?_)
        obtain ⟨i, -, -, hgt, -, -, -, hF⟩ := h
        exact ⟨hF.1, ⟨_, rfl, iff_of_false (by decide) (hne i (by omega))⟩, hF.2.2.2.2⟩
      · exact Sep.triple_fallthrough ge fe f_strcmp _ _ _ _ (Sep.triple_skip ge fe f_strcmp _)
          (fun _ _ _ x => x)

include hpr1 hpr2 hno1 hno2 in
theorem body_triple (n : Nat) :
    Sep.Triple ge fe f_strcmp (Inv p1 p2 b1 o1 b2 o2 s1 s2 n) loopBody
      (BodyR p1 p2 b1 o1 b2 o2 s1 s2 n) := by
  refine Sep.triple_seq_only ge fe f_strcmp (Sep.triple_skip ge fe f_strcmp _) ?_
  refine Sep.triple_seq_only ge fe f_strcmp
    (load1_triple ge fe p1 p2 b1 o1 b2 o2 s1 s2 hpr1 hpr2 hno1 hno2 n) ?_
  refine Sep.triple_seq_only ge fe f_strcmp
    (load2_triple ge fe p1 p2 b1 o1 b2 o2 s1 s2 hpr1 hpr2 hno1 hno2 n) ?_
  exact Sep.triple_seq_only ge fe f_strcmp (setT_triple ge fe p1 p2 b1 o1 b2 o2 s1 s2 n)
    (tests_triple ge fe p1 p2 b1 o1 b2 o2 s1 s2 n)

theorem incr_triple (n : Nat) :
    Sep.Triple ge fe f_strcmp (Mid p1 p2 b1 o1 b2 o2 s1 s2 n) Strlen.s2
      { normal := fun e le hp => ∃ n', n' < n ∧ Inv p1 p2 b1 o1 b2 o2 s1 s2 n' e le hp,
        brk := (LoopR p1 p2 b1 o1 b2 o2 s1 s2).normal, cont := Sep.Assn.no,
        ret := (LoopR p1 p2 b1 o1 b2 o2 s1 s2).ret,
        goto := (LoopR p1 p2 b1 o1 b2 o2 s1 s2).goto } := by
  refine Sep.triple_fallthrough ge fe f_strcmp _ _ _ _
    (Sep.triple_set ge fe f_strcmp _
      (fun e le hp => n - 1 < n ∧ Inv p1 p2 b1 o1 b2 o2 s1 s2 (n - 1) e le hp)
      _ _ (fun e le hp m hP _ => ?_))
    (fun e le hp h => ⟨n - 1, h.1, h.2⟩)
  obtain ⟨i, hi, hlt, hsame, he, h1, h2, hii, hs⟩ := hP
  refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hii)
    (EvalExpr.Econst_int _ _) (semBinop_add_ulong_int _ _ _ _), by omega, i + 1, by omega, hsame,
    he, (PTree.gso _ _ _ _ (by decide)).trans h1, (PTree.gso _ _ _ _ (by decide)).trans h2,
    ?_, hs⟩
  rw [PTree.gss]
  congr 2
  rw [show Integers.Int.signed (Integers.Int.repr 1) = 1 from rfl, repr64_add]
  push_cast; rfl

end

end Strcmp

/-- **`strcmp` satisfies `strcmp_spec`** (VST's `body_strcmp`). -/
theorem strcmp_satisfies (ge : CGenv) (p1 p2 : Permission) (b1 : Block) (o1 : Integers.Ptrofs)
    (b2 : Block) (o2 : Integers.Ptrofs) (s1 s2 : List Nat)
    (hpr1 : permOrder p1 .Readable = true) (hpr2 : permOrder p2 .Readable = true)
    (hno1 : Integers.Ptrofs.unsigned o1 + s1.length + 1 ≤ 18446744073709551616)
    (hno2 : Integers.Ptrofs.unsigned o2 + s2.length + 1 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_strcmp)
      (strcmpSpec p1 p2 b1 o1 b2 o2 s1 s2) [.Vptr b1 o1, .Vptr b2 o2] := by
  open Strcmp in
  have hno1' : o1.toNat + s1.length + 1 ≤ 18446744073709551616 := by
    have : Integers.Ptrofs.unsigned o1 = (o1.toNat : _root_.Int) := rfl
    zomega
  have hno2' : o2.toNat + s2.length + 1 ≤ 18446744073709551616 := by
    have : Integers.Ptrofs.unsigned o2 = (o2.toNat : _root_.Int) := rfl
    zomega
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_strcmp _ _
    (fun e le hp => e = emptyEnv ∧ le.get _str1 = some (.Vptr b1 o1)
      ∧ le.get _str2 = some (.Vptr b2 o2) ∧ twoStrings p1 p2 b1 o1 b2 o2 s1 s2 hp)
    (fun m => ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp hpre =>
        ⟨rfl, (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _), PTree.gss _ _ _,
          hpre.2⟩⟩) ?_
  rw [body_eq]
  -- `i = 0;`
  refine Sep.triple_seq_only ge _ f_strcmp
    (Q := Inv p1 p2 b1 o1 b2 o2 s1 s2 (min s1.length s2.length)) ?_ ?_
  · refine Sep.triple_set ge _ f_strcmp _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, h1, h2, hs⟩ := hP
    exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, 0, by omega,
      fun j hj => absurd hj (Nat.not_lt_zero j), he,
      (PTree.gso _ _ _ _ (by decide)).trans h1, (PTree.gso _ _ _ _ (by decide)).trans h2,
      PTree.gss _ _ _, hs⟩
  -- the loop
  exact Sep.triple_loop ge _ f_strcmp (LoopR p1 p2 b1 o1 b2 o2 s1 s2)
    (Inv p1 p2 b1 o1 b2 o2 s1 s2) (Mid p1 p2 b1 o1 b2 o2 s1 s2) loopBody Strlen.s2
    (body_triple ge _ p1 p2 b1 o1 b2 o2 s1 s2 hpr1 hpr2 hno1' hno2')
    (incr_triple ge _ p1 p2 b1 o1 b2 o2 s1 s2) (min s1.length s2.length)

end VST.Verif.Strlib
