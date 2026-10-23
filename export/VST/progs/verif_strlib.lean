/-
  Port of VST's `progs/verif_strlib.v`: `strlen` and `strchr` of
  `vst/progs/strlib.c`; `strcmp` is in `verif_strlib_strcmp` (`strcpy` and
  `strcat` are not ported yet).

      char *strchr(const char *str, int c) {
        size_t i;
        for(i = 0;; i++){
          char d = str[i];
          if(d == c) return (str + i);
          if(d == 0) return 0;
        }
      }

      size_t strlen(const char *str) {
        size_t i;
        for (i=0; ; i++)
          if (str[i]==0) return i;
      }

  VST's specifications:

      strchr_spec: WITH sh, str, s : list byte, c : byte
        PRE [ tptr tschar, tint ] PROP (readable_share sh; c <> Byte.zero)
          PARAMS (str; Vbyte c) SEP (cstring sh s str)
        POST [ tptr tschar ] EX r,
          PROP ((exists i, Znth i s = c /\ Forall (fun d => d<>c) (sublist 0 i s)
                           /\ r = offset_val i str)
                \/ (Forall (fun d => d<>c) s /\ r = nullval))
          RETURN (r) SEP (cstring sh s str)

      strlen_spec: WITH sh, s : list byte, str
        PRE [ tptr tschar ] PROP (readable_share sh) PARAMS (str)
          SEP (cstring sh s str)
        POST [ size_t ] PROP () RETURN (Vptrofs (Ptrofs.repr (Zlength s)))
          SEP (cstring sh s str)

  `cstring` is `CC.cstring` (`CCLib.logic.CString`): the characters `s`
  (bytes, none of them `0`) followed by a `0`.  `char` is unsigned on
  AArch64, the target of the generated program, so the characters are
  `unsigned char`s.  The string must lie inside the address space (part of
  VST's `field_compatible`): `hno`.

  For `strchr`, `c` is a byte `0 < c < 256` passed as an `int`, and
  "`r = offset_val i str`" is stated as: `r` is a pointer into the block of
  `str` whose offset is that of `str` plus `i`.

  The loops have no exit test: they leave through `return` (at the latest on
  the terminating `0`).  The triples are total, so the proofs also show that
  this happens; the measure is the number of characters left.
-/
import VST.progs.strlib
import CCLib
open CC CC.Sep CC.HProp
open Strlib

namespace VST.Verif.Strlib

/-- `strlen_spec` -/
def strlenSpec (p : Permission) (b : Block) (o : Integers.Ptrofs) (s : List Nat) :
    Sep.FunSpec where
  tyargs := [tptr tuchar]
  tyres := tulong
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b o] ∧ cstring p b (Integers.Ptrofs.unsigned o) s hp
  post := fun v hp => v = .Vlong (Integers.Int64.repr s.length)
    ∧ cstring p b (Integers.Ptrofs.unsigned o) s hp
  measure := fun _ => 0

namespace Strlen

def s1 : Stmt :=
  .Ssequence .Sskip
    (.Ssequence
      (.Sset _t'1 (.Ederef (.Ebinop .Oadd (.Etempvar _str (tptr tuchar)) (.Etempvar _i tulong)
        (tptr tuchar)) tuchar))
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar _t'1 tuchar) (.Econst_int (Integers.Int.repr 0) tint)
          tint)
        (.Sreturn (some (.Etempvar _i tulong))) .Sskip))

def s2 : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tulong) (.Econst_int (Integers.Int.repr 1) tint) tulong)

theorem body_eq : f_strlen.fn_body =
    .Ssequence (.Sset _i (.Ecast (.Econst_int (Integers.Int.repr 0) tint) tulong))
      (.Sloop s1 s2) := rfl

section
variable (p : Permission) (b : Block) (o : Integers.Ptrofs) (s : List Nat)

/-- The local state: `str` and `i` hold `b + o` and `i`, the string is owned. -/
def Facts (i : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _str = some (.Vptr b o)
    ∧ le.get _i = some (.Vlong (Integers.Int64.repr i))
    ∧ cstring p b (Integers.Ptrofs.unsigned o) s hp

/-- The loop invariant, `n` characters left to read. -/
def Inv (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = s.length ∧ Facts p b o s i e le hp

/-- After the test: character `i` was not the end. -/
def Mid (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = s.length ∧ i < s.length ∧ Facts p b o s i e le hp

/-- The loop's exits: only `return`, with `strlen_spec`'s postcondition. -/
def LoopR : Sep.ExitConds :=
  { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := (strlenSpec p b o s).post }

end

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block) (o : Integers.Ptrofs)
  (s : List Nat) (hpr : permOrder p .Readable = true)
  (hno : o.toNat + s.length + 1 ≤ 18446744073709551616)

include hpr hno in
theorem body_triple (n : Nat) :
    Sep.Triple ge fe f_strlen (Inv p b o s n) s1
      { normal := Mid p b o s n, brk := (LoopR p b o s).normal, cont := Mid p b o s n,
        ret := (LoopR p b o s).ret, goto := (LoopR p b o s).goto } := by
  refine Sep.triple_seq_only ge fe f_strlen (Sep.triple_skip ge fe f_strlen _) ?_
  -- `t'1 = str[i];`
  refine Sep.triple_seq_only ge fe f_strlen (Q := fun e le hp => ∃ i, i + n = s.length
      ∧ le.get _t'1 = some (.Vint (Integers.Int.repr (s.getD i 0)))
      ∧ Facts p b o s i e le hp) ?_ ?_
  · refine Sep.triple_set ge fe f_strlen _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨i, hi, he, hstr, hii, hc⟩ := hP
    obtain ⟨hs, harr⟩ := pure_sep_elim hc
    refine ⟨_, eval_index_bytes_ulong hpr harr hag (by omega) (cstring_byte hs) hstr
      (EvalExpr.Etempvar _ _ _ hii) rfl (by omega), i, hi, PTree.gss _ _ _, he,
      (PTree.gso _ _ _ _ (by decide)).trans hstr, (PTree.gso _ _ _ _ (by decide)).trans hii, hc⟩
  -- `if (t'1 == 0) return i;`
  refine Sep.triple_if ge fe f_strlen _
    (fun e le hp => ∃ i, i = s.length ∧ Facts p b o s i e le hp)
    (fun e le hp => ∃ i, i + n = s.length ∧ i < s.length ∧ Facts p b o s i e le hp) _ _ _ _
    (fun e le hp m hP _ => ?_) ?_ ?_
  · obtain ⟨i, hi, ht, hF⟩ := hP
    obtain ⟨hs, -⟩ := pure_sep_elim hF.2.2.2
    have hc := cstring_byte hs i
    refine ⟨_, decide (s.getD i 0 = 0),
      EvalExpr.Ebinop .Oeq _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ ht) (EvalExpr.Econst_int _ _)
        (by
          have h : Integers.Int.eq (Integers.Int.repr (s.getD i 0 : _root_.Int))
              (Integers.Int.repr 0) = decide (s.getD i 0 = 0) :=
            int_eq_nat32 (s.getD i 0) 0 (by omega) (by decide)
          simp only [typeof]
          rw [semBinop_eq_uchar_int, h]),
      boolVal_ofBool_int m _, ?_⟩
    have hz := cstring_zero_iff hs (i := i) (by omega)
    by_cases h0 : s.getD i 0 = 0
    · simp only [h0, decide_true, if_true]
      exact ⟨i, hz.mp h0, hF⟩
    · simp only [h0, decide_false]
      exact ⟨i, hi, by have := mt hz.mpr h0; omega, hF⟩
  · refine Sep.triple_conseq ge fe f_strlen
      (Sep.triple_return ge fe f_strlen _ (LoopR p b o s).ret _ (fun e le hp m h _ => ?_))
      (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
      (fun _ _ _ x => False.elim x) (fun _ _ x => x)
    obtain ⟨i, rfl, he, -, hii, hc⟩ := h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _ _ _ hii, rfl, by rw [he]; exact freeList_emptyEnv _ _,
      ⟨rfl, hc⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
  · exact Sep.triple_fallthrough ge fe f_strlen _ _ _ _ (Sep.triple_skip ge fe f_strlen _)
      (fun _ _ _ x => x)

theorem incr_triple (n : Nat) :
    Sep.Triple ge fe f_strlen (Mid p b o s n) s2
      { normal := fun e le hp => ∃ n', n' < n ∧ Inv p b o s n' e le hp,
        brk := (LoopR p b o s).normal, cont := Sep.Assn.no, ret := (LoopR p b o s).ret,
        goto := (LoopR p b o s).goto } := by
  refine Sep.triple_fallthrough ge fe f_strlen _ _ _ _
    (Sep.triple_set ge fe f_strlen _ (fun e le hp => n - 1 < n ∧ Inv p b o s (n - 1) e le hp) _ _
      (fun e le hp m hP _ => ?_))
    (fun e le hp h => ⟨n - 1, h.1, h.2⟩)
  · obtain ⟨i, hi, hlt, he, hstr, hii, hc⟩ := hP
    refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hii)
      (EvalExpr.Econst_int _ _) (semBinop_add_ulong_int _ _ _ _), by omega, i + 1, by omega, he,
      (PTree.gso _ _ _ _ (by decide)).trans hstr, ?_, hc⟩
    rw [PTree.gss]
    congr 2
    rw [show Integers.Int.signed (Integers.Int.repr 1) = 1 from rfl, repr64_add]
    push_cast; rfl

end

end Strlen

/-- **`strlen` satisfies `strlen_spec`** (VST's `body_strlen`). -/
theorem strlen_satisfies (ge : CGenv) (p : Permission) (b : Block) (o : Integers.Ptrofs)
    (s : List Nat) (hpr : permOrder p .Readable = true)
    (hno : Integers.Ptrofs.unsigned o + s.length + 1 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_strlen) (strlenSpec p b o s)
      [.Vptr b o] := by
  open Strlen in
  have hno' : o.toNat + s.length + 1 ≤ 18446744073709551616 := by
    have : Integers.Ptrofs.unsigned o = (o.toNat : _root_.Int) := rfl
    zomega
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_strlen _ _
    (fun e le hp => e = emptyEnv ∧ le.get _str = some (.Vptr b o)
      ∧ cstring p b (Integers.Ptrofs.unsigned o) s hp)
    (fun m => ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp hpre => ⟨rfl, PTree.gss _ _ _, hpre.2⟩⟩) ?_
  rw [body_eq]
  -- `i = 0;`
  refine Sep.triple_seq_only ge _ f_strlen (Q := Inv p b o s s.length) ?_ ?_
  · refine Sep.triple_set ge _ f_strlen _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hstr, hc⟩ := hP
    exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, 0, by omega, he,
      (PTree.gso _ _ _ _ (by decide)).trans hstr, PTree.gss _ _ _, hc⟩
  -- the loop
  exact Sep.triple_loop ge _ f_strlen (LoopR p b o s) (Inv p b o s) (Mid p b o s) s1 s2
    (body_triple ge _ p b o s hpr hno') (incr_triple ge _ p b o s) s.length

/-! ## `strchr` -/

/-- `strchr_spec`: for a non-zero character `c`, the result points to the
    first occurrence `i` of `c` in `s`, or is `NULL` if there is none. -/
def strchrSpec (p : Permission) (b : Block) (o : Integers.Ptrofs) (s : List Nat) (c : Nat) :
    Sep.FunSpec where
  tyargs := [tptr tuchar, tint]
  tyres := tptr tuchar
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr b o, .Vint (Integers.Int.repr c)]
    ∧ cstring p b (Integers.Ptrofs.unsigned o) s hp
  post := fun v hp => cstring p b (Integers.Ptrofs.unsigned o) s hp ∧
    ((∃ i o', i < s.length ∧ s.getD i 0 = c ∧ (∀ j < i, s.getD j 0 ≠ c)
        ∧ v = .Vptr b o' ∧ Integers.Ptrofs.unsigned o' = Integers.Ptrofs.unsigned o + i)
      ∨ ((∀ j < s.length, s.getD j 0 ≠ c) ∧ v = Val.Vnullptr))
  measure := fun _ => 0

namespace Strchr

def load : Stmt :=
  .Ssequence
    (.Sset _t'1 (.Ederef (.Ebinop .Oadd (.Etempvar _str (tptr tuchar)) (.Etempvar _i tulong)
      (tptr tuchar)) tuchar))
    (.Sset _d (.Ecast (.Etempvar _t'1 tuchar) tuchar))

def ifc : Stmt :=
  .Sifthenelse (.Ebinop .Oeq (.Etempvar _d tuchar) (.Etempvar _c tint) tint)
    (.Sreturn (some (.Ebinop .Oadd (.Etempvar _str (tptr tuchar)) (.Etempvar _i tulong)
      (tptr tuchar)))) .Sskip

def if0 : Stmt :=
  .Sifthenelse (.Ebinop .Oeq (.Etempvar _d tuchar) (.Econst_int (Integers.Int.repr 0) tint) tint)
    (.Sreturn (some (.Econst_int (Integers.Int.repr 0) tint))) .Sskip

def s1 : Stmt := .Ssequence .Sskip (.Ssequence load (.Ssequence ifc if0))

theorem body_eq : f_strchr.fn_body =
    .Ssequence (.Sset _i (.Ecast (.Econst_int (Integers.Int.repr 0) tint) tulong))
      (.Sloop s1 Strlen.s2) := rfl

section
variable (p : Permission) (b : Block) (o : Integers.Ptrofs) (s : List Nat) (c : Nat)

def Facts (i : Nat) : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _str = some (.Vptr b o) ∧ le.get _c = some (.Vint (Integers.Int.repr c))
    ∧ le.get _i = some (.Vlong (Integers.Int64.repr i))
    ∧ cstring p b (Integers.Ptrofs.unsigned o) s hp

/-- The loop invariant: `c` is not among the first `i` characters, `n`
    characters are left. -/
def Inv (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = s.length ∧ (∀ j < i, s.getD j 0 ≠ c) ∧ Facts p b o s c i e le hp

/-- After the tests: character `i` is neither `c` nor the end. -/
def Mid (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = s.length ∧ i < s.length ∧ (∀ j < i + 1, s.getD j 0 ≠ c)
    ∧ Facts p b o s c i e le hp

def LoopR : Sep.ExitConds :=
  { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := (strchrSpec p b o s c).post }

end

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block) (o : Integers.Ptrofs)
  (s : List Nat) (c : Nat) (hpr : permOrder p .Readable = true) (hc : 0 < c ∧ c < 256)
  (hno : o.toNat + s.length + 1 ≤ 18446744073709551616)

/-- The exits of the loop body. -/
abbrev BodyR (n : Nat) : Sep.ExitConds :=
  { normal := Mid p b o s c n, brk := (LoopR p b o s c).normal, cont := Mid p b o s c n,
    ret := (LoopR p b o s c).ret, goto := (LoopR p b o s c).goto }

/-- After `t'1 = str[i]; d = (unsigned char) t'1;`. -/
def Loaded (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = s.length ∧ (∀ j < i, s.getD j 0 ≠ c)
    ∧ le.get _d = some (.Vint (Integers.Int.repr (s.getD i 0))) ∧ Facts p b o s c i e le hp

/-- After the test `d == c`: character `i` is not `c`. -/
def Checked (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ i, i + n = s.length ∧ (∀ j < i + 1, s.getD j 0 ≠ c)
    ∧ le.get _d = some (.Vint (Integers.Int.repr (s.getD i 0))) ∧ Facts p b o s c i e le hp

/-- The two `set`s leave the facts about `str`, `c` and `i` unchanged. -/
theorem facts_set {i : Nat} {e : Env} {le : TempEnv} {hp : Heap} (x : Ident) (v : Val)
    (hx1 : x ≠ _str) (hx2 : x ≠ _c) (hx3 : x ≠ _i) (h : Facts p b o s c i e le hp) :
    Facts p b o s c i e (le.set x v) hp := by
  obtain ⟨he, hstr, hcv, hii, hcs⟩ := h
  exact ⟨he, (PTree.gso _ _ _ _ hx1).trans hstr, (PTree.gso _ _ _ _ hx2).trans hcv,
    (PTree.gso _ _ _ _ hx3).trans hii, hcs⟩

include hpr hno in
theorem load_triple (n : Nat) :
    Sep.Triple ge fe f_strchr (Inv p b o s c n) load (.only (Loaded p b o s c n)) := by
  refine Sep.triple_seq_only ge fe f_strchr (Q := fun e le hp => ∃ i, i + n = s.length
      ∧ (∀ j < i, s.getD j 0 ≠ c)
      ∧ le.get _t'1 = some (.Vint (Integers.Int.repr (s.getD i 0)))
      ∧ Facts p b o s c i e le hp) ?_ ?_
  · refine Sep.triple_set ge fe f_strchr _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨i, hi, hnc, hF⟩ := hP
    obtain ⟨-, hstr, -, hii, hcs⟩ := id hF
    obtain ⟨hs, harr⟩ := pure_sep_elim hcs
    exact ⟨_, eval_index_bytes_ulong hpr harr hag (by omega) (cstring_byte hs) hstr
      (EvalExpr.Etempvar _ _ _ hii) rfl (by omega), i, hi, hnc, PTree.gss _ _ _,
      facts_set p b o s c _ _ (by decide) (by decide) (by decide) hF⟩
  · refine Sep.triple_set ge fe f_strchr _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨i, hi, hnc, ht, hF⟩ := hP
    obtain ⟨hs, -⟩ := pure_sep_elim hF.2.2.2.2
    refine ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ ht)
      (semCast_uchar_byte m _ (cstring_byte hs i)), i, hi, hnc, ?_,
      facts_set p b o s c _ _ (by decide) (by decide) (by decide) hF⟩
    rw [PTree.gss]

include hc hno in
theorem tests_triple (n : Nat) :
    Sep.Triple ge fe f_strchr (Loaded p b o s c n) (.Ssequence ifc if0) (BodyR p b o s c n) := by
  refine Sep.triple_seq ge fe f_strchr _ (Checked p b o s c n) _ _ _ ?_ ?_
  -- `if (d == c) return str + i;`
  · refine Sep.triple_if ge fe f_strchr _
      (fun e le hp => ∃ i, i + n = s.length ∧ (∀ j < i, s.getD j 0 ≠ c) ∧ s.getD i 0 = c
        ∧ Facts p b o s c i e le hp) (Checked p b o s c n) _ _ _ _ (fun e le hp m hP _ => ?_)
      ?_ ?_
    · obtain ⟨i, hi, hnc, hd, hF⟩ := hP
      obtain ⟨hs, -⟩ := pure_sep_elim hF.2.2.2.2
      refine ⟨_, _, eval_eq_uchar (cstring_byte hs i) hc.2 (EvalExpr.Etempvar _ _ _ hF.2.2.1)
        rfl hd, boolVal_ofBool_int m _, ?_⟩
      by_cases h : s.getD i 0 = c
      · simp only [h, decide_true, if_true]
        exact ⟨i, hi, hnc, h, hF⟩
      · simp only [h, decide_false]
        refine ⟨i, hi, fun j hj => ?_, hd, hF⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hnc j hj
        · exact h
    · refine Sep.triple_conseq ge fe f_strchr
        (Sep.triple_return ge fe f_strchr _ (LoopR p b o s c).ret _ (fun e le hp m h _ => ?_))
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
        (fun _ _ _ x => False.elim x) (fun _ _ x => x)
      obtain ⟨i, hi, hnc, hci, he, hstr, -, hii, hcs⟩ := h
      obtain ⟨hs, -⟩ := pure_sep_elim hcs
      have hil : i < s.length := by
        have hz := cstring_zero_iff hs (i := i) (by omega)
        have : i ≠ s.length := fun h => by have := hz.mpr h; omega
        omega
      refine ⟨_, _, m, hp, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hstr)
        (EvalExpr.Etempvar _ _ _ hii) (semAdd_byte_ulong _ _ _ _ _),
        semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩), by rw [he]; exact freeList_emptyEnv _ _,
        ⟨hcs, Or.inl ⟨i, _, hil, hci, hnc, rfl, byteOfsL_unsigned _ o i (by omega)⟩⟩,
        fun _ hdj hag => ⟨hdj, hag⟩⟩
    · exact Sep.triple_fallthrough ge fe f_strchr _ _ _ _ (Sep.triple_skip ge fe f_strchr _)
        (fun _ _ _ x => x)
  -- `if (d == 0) return 0;`
  · refine Sep.triple_if ge fe f_strchr _
      (fun e le hp => ∃ i, i = s.length ∧ (∀ j < i, s.getD j 0 ≠ c)
        ∧ Facts p b o s c i e le hp) (Mid p b o s c n) _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
    · obtain ⟨i, hi, hnc, hd, hF⟩ := hP
      obtain ⟨hs, -⟩ := pure_sep_elim hF.2.2.2.2
      have hz := cstring_zero_iff hs (i := i) (by omega)
      refine ⟨_, _, eval_eq_uchar (c := 0) (cstring_byte hs i) (by decide)
        (EvalExpr.Econst_int _ _) rfl hd, boolVal_ofBool_int m _, ?_⟩
      by_cases h : s.getD i 0 = 0
      · simp only [h, decide_true, if_true]
        exact ⟨i, hz.mp h, fun j hj => hnc j (by omega), hF⟩
      · simp only [h, decide_false]
        exact ⟨i, hi, by have := mt hz.mpr h; omega, hnc, hF⟩
    · refine Sep.triple_conseq ge fe f_strchr
        (Sep.triple_return ge fe f_strchr _ (LoopR p b o s c).ret _ (fun e le hp m h _ => ?_))
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
        (fun _ _ _ x => False.elim x) (fun _ _ x => x)
      obtain ⟨i, rfl, hnc, he, -, -, -, hcs⟩ := h
      exact ⟨_, _, m, hp, EvalExpr.Econst_int _ _, rfl, by rw [he]; exact freeList_emptyEnv _ _,
        ⟨hcs, Or.inr ⟨hnc, rfl⟩⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
    · exact Sep.triple_fallthrough ge fe f_strchr _ _ _ _ (Sep.triple_skip ge fe f_strchr _)
        (fun _ _ _ x => x)

include hpr hc hno in
theorem body_triple (n : Nat) :
    Sep.Triple ge fe f_strchr (Inv p b o s c n) s1 (BodyR p b o s c n) :=
  Sep.triple_seq_only ge fe f_strchr (Sep.triple_skip ge fe f_strchr _)
    (Sep.triple_seq_only ge fe f_strchr (load_triple ge fe p b o s c hpr hno n)
      (tests_triple ge fe p b o s c hc hno n))

theorem incr_triple (n : Nat) :
    Sep.Triple ge fe f_strchr (Mid p b o s c n) Strlen.s2
      { normal := fun e le hp => ∃ n', n' < n ∧ Inv p b o s c n' e le hp,
        brk := (LoopR p b o s c).normal, cont := Sep.Assn.no, ret := (LoopR p b o s c).ret,
        goto := (LoopR p b o s c).goto } := by
  refine Sep.triple_fallthrough ge fe f_strchr _ _ _ _
    (Sep.triple_set ge fe f_strchr _ (fun e le hp => n - 1 < n ∧ Inv p b o s c (n - 1) e le hp)
      _ _ (fun e le hp m hP _ => ?_))
    (fun e le hp h => ⟨n - 1, h.1, h.2⟩)
  obtain ⟨i, hi, hlt, hnc, he, hstr, hcv, hii, hcs⟩ := hP
  refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hii)
    (EvalExpr.Econst_int _ _) (semBinop_add_ulong_int _ _ _ _), by omega, i + 1, by omega, hnc,
    he, (PTree.gso _ _ _ _ (by decide)).trans hstr, (PTree.gso _ _ _ _ (by decide)).trans hcv,
    ?_, hcs⟩
  rw [PTree.gss]
  congr 2
  rw [show Integers.Int.signed (Integers.Int.repr 1) = 1 from rfl, repr64_add]
  push_cast; rfl

end

end Strchr

/-- **`strchr` satisfies `strchr_spec`** (VST's `body_strchr`). -/
theorem strchr_satisfies (ge : CGenv) (p : Permission) (b : Block) (o : Integers.Ptrofs)
    (s : List Nat) (c : Nat) (hpr : permOrder p .Readable = true) (hc : 0 < c ∧ c < 256)
    (hno : Integers.Ptrofs.unsigned o + s.length + 1 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_strchr) (strchrSpec p b o s c)
      [.Vptr b o, .Vint (Integers.Int.repr c)] := by
  open Strchr in
  have hno' : o.toNat + s.length + 1 ≤ 18446744073709551616 := by
    have : Integers.Ptrofs.unsigned o = (o.toNat : _root_.Int) := rfl
    zomega
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_strchr _ _
    (fun e le hp => e = emptyEnv ∧ le.get _str = some (.Vptr b o)
      ∧ le.get _c = some (.Vint (Integers.Int.repr c))
      ∧ cstring p b (Integers.Ptrofs.unsigned o) s hp)
    (fun m => ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp hpre =>
        ⟨rfl, (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _), PTree.gss _ _ _,
          hpre.2⟩⟩) ?_
  rw [body_eq]
  -- `i = 0;`
  refine Sep.triple_seq_only ge _ f_strchr (Q := Inv p b o s c s.length) ?_ ?_
  · refine Sep.triple_set ge _ f_strchr _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hstr, hcv, hcs⟩ := hP
    exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, 0, by omega,
      fun j hj => absurd hj (Nat.not_lt_zero j), he,
      (PTree.gso _ _ _ _ (by decide)).trans hstr, (PTree.gso _ _ _ _ (by decide)).trans hcv,
      PTree.gss _ _ _, hcs⟩
  -- the loop
  exact Sep.triple_loop ge _ f_strchr (LoopR p b o s c) (Inv p b o s c) (Mid p b o s c) s1
    Strlen.s2 (body_triple ge _ p b o s c hpr hc hno') (incr_triple ge _ p b o s c) s.length

end VST.Verif.Strlib
