/-
  Port of VST's `progs/verif_reverse.v`: `sumlist` and `reverse` of
  `vst/progs/reverse.c` on null-terminated linked lists.

      struct list {unsigned head; struct list *tail;};

      unsigned sumlist (struct list *p) {
        unsigned s = 0;  struct list *t = p;  unsigned h;
        while (t) { h = t->head; t = t->tail; s = s + h; }
        return s;
      }

      struct list *reverse (struct list *p) {
        struct list *w, *t, *v;
        w = NULL;  v = p;
        while (v) { t = v->tail; v->tail = w; w = v; v = t; }
        return w;
      }

  VST's specifications:

      sumlist_spec: WITH sh, contents, p
        PRE [tptr t_struct_list] PROP (readable_share sh) PARAMS (p)
          SEP (lseg LS sh (map Vint contents) p nullval)
        POST [tuint] RETURN (Vint (sum_int contents))
          SEP (lseg LS sh (map Vint contents) p nullval)

      reverse_spec: WITH sh, contents, p
        PRE [tptr t_struct_list] PROP (writable_share sh) PARAMS (p)
          SEP (lseg LS sh contents p nullval)
        POST [tptr t_struct_list] EX q, RETURN (q)
          SEP (lseg LS sh (rev contents) q nullval)

  The list predicate is `Sep.listrep` (`CCLib.logic.ListRep`) over the node
  predicate `listNode`: the two fields of a `struct list` at a permission `p`,
  inside the address space (VST's `field_compatible`).  `ge` must use the
  program's composite environment (`hcenv`), so that the field offsets are
  those of `struct list`.

  The loop invariants are VST's: for `sumlist`, the part of the list already
  summed is a segment `lseg c1 p t` in front of the rest `listrep c2 t`; for
  `reverse`, `contents = rev c1 ++ c2`, with `listrep c1 w ∗ listrep c2 v`.
-/
import VST.progs.reverse
import CCLib
open CC CC.Sep CC.HProp
open Reverse

namespace VST.Verif.Reverse

/-! ## The layout of `struct list` -/

abbrev tlist : Ty := .Tstruct _list noattr
abbrev tlistp : Ty := tptr tlist

def coList : Composite :=
  match prog.prog_comp_env.get _list with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem get_list : prog.prog_comp_env.get _list = some coList := rfl
theorem offset_head :
    fieldOffset prog.prog_comp_env _head coList.co_members = .OK (0, .Full) := by decide
theorem offset_tail :
    fieldOffset prog.prog_comp_env _tail coList.co_members = .OK (8, .Full) := by decide

/-- `struct list` as a list layout (`Sep.ListLayout`). -/
def layout : ListLayout :=
  ⟨prog.prog_comp_env, _list, _head, _tail, coList, get_list, offset_head, offset_tail⟩

/-- The list `contents` at `x` (VST's `lseg LS sh contents x nullval`). -/
abbrev listrepL (p : Permission) (contents : List Integers.Int) (x : Val) : HProp :=
  listrep (listNode p) contents x

/-! ## `sumlist` -/

/-- `sum_int`: the sum of the elements, in 32-bit arithmetic. -/
def sumInt (l : List Integers.Int) : Integers.Int := l.foldl Integers.Int.add (Integers.Int.repr 0)

theorem sumInt_snoc (l : List Integers.Int) (a : Integers.Int) :
    sumInt (l ++ [a]) = Integers.Int.add (sumInt l) a := by
  simp [sumInt, List.foldl_append]

namespace Sumlist

def ifStmt : Stmt := .Sifthenelse (.Etempvar _t tlistp) .Sskip .Sbreak
def bodyStmt : Stmt :=
  .Ssequence (.Sset _h (.Efield (.Ederef (.Etempvar _t tlistp) tlist) _head tuint))
    (.Ssequence (.Sset _t (.Efield (.Ederef (.Etempvar _t tlistp) tlist) _tail tlistp))
      (.Sset _s (.Ebinop .Oadd (.Etempvar _s tuint) (.Etempvar _h tuint) tuint)))
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) .Sskip
def fullBody : Stmt :=
  .Ssequence (.Sset _s (.Econst_int (Integers.Int.repr 0) tint))
    (.Ssequence (.Sset _t (.Etempvar _p tlistp))
      (.Ssequence loopStmt (.Sreturn (some (.Etempvar _s tuint)))))

theorem body_eq : f_sumlist.fn_body = fullBody := rfl

section
variable (p : Permission) (contents : List Integers.Int) (x : Val)

/-- The loop invariant, `k` nodes left: the summed part `c1` is a segment
    from `p` to `t`, the rest `c2` a list at `t`. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ c1 c2 t, contents = c1 ++ c2 ∧ c2.length = k ∧ e = emptyEnv
    ∧ le.get _t = some t ∧ le.get _s = some (.Vint (sumInt c1))
    ∧ (lseg (listNode p) c1 x t ∗ listrepL p c2 t) hp

/-- After the test: `t` is a node `a`, followed by the list `c2`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ c1 a c2 b o u, contents = c1 ++ a :: c2 ∧ c2.length + 1 = k ∧ e = emptyEnv
    ∧ le.get _t = some (.Vptr b o) ∧ le.get _s = some (.Vint (sumInt c1))
    ∧ (lseg (listNode p) c1 x (.Vptr b o)
        ∗ (listNode p b (Integers.Ptrofs.unsigned o) a u ∗ listrepL p c2 u)) hp

def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _s = some (.Vint (sumInt contents)) ∧ listrepL p contents x hp

def LoopR : Sep.ExitConds :=
  { normal := Done p contents x, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := fun _ _ => False }

end

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (contents : List Integers.Int) (x : Val)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpr : permOrder p .Readable = true)

theorem if_triple (k : Nat) :
    Sep.Triple ge fe f_sumlist (LInv p contents x k) ifStmt
      { normal := LMid p contents x k, brk := Done p contents x,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe f_sumlist _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨c1, c2, t, -, hk, -, ht, -, hs⟩ := hP
      obtain ⟨_, _, _, _, _, hl⟩ := hs
      rcases listrep_val _ hl with ⟨rfl, _⟩ | ⟨_, _, _, hne⟩
      · exact ⟨_, EvalExpr.Etempvar _ _ _ ht, boolVal_null m _ _⟩
      · exact absurd (List.length_eq_zero_iff.mp hk) hne
    · refine Sep.triple_conseq ge fe f_sumlist (Sep.triple_break ge fe f_sumlist _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨c1, c2, t, hc, hk, he, ht, hsum, h1, h2, hd, rfl, hseg, hl⟩ := h
      have hc2 := List.length_eq_zero_iff.mp hk
      subst hc2
      obtain ⟨rfl, rfl⟩ := hl
      rw [List.append_nil] at hc
      subst hc
      exact ⟨he, hsum, by rw [Heap.union_emp]; exact hseg⟩
  | succ j =>
    refine Sep.triple_if_true ge fe f_sumlist _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · obtain ⟨c1, c2, t, -, hk, -, ht, -, hs⟩ := hP
      obtain ⟨h1, h2, hd, rfl, _, hl⟩ := hs
      rcases listrep_val _ hl with ⟨rfl, hc2⟩ | ⟨b, o, rfl, _⟩
      · subst hc2; simp at hk
      · obtain ⟨a, l', u, rfl, hn⟩ := listrep_ptr _ hl
        exact ⟨_, EvalExpr.Etempvar _ _ _ ht, boolVal_ptr_valid m b o _ _
          (node_valid hn (Heap.Agrees_union_right hd hag))⟩
    · refine Sep.triple_fallthrough ge fe f_sumlist _ _ _ _
        (Sep.triple_skip ge fe f_sumlist _) (fun e le hp h => ?_)
      obtain ⟨c1, c2, t, hc, hk, he, ht, hsum, h1, h2, hd, rfl, hseg, hl⟩ := h
      rcases listrep_val _ hl with ⟨rfl, hc2⟩ | ⟨b, o, rfl, _⟩
      · subst hc2; simp at hk
      · obtain ⟨a, l', u, rfl, hn⟩ := listrep_ptr _ hl
        exact ⟨c1, a, l', b, o, u, hc, by simpa using hk, he, ht, hsum, h1, h2, hd, rfl, hseg, hn⟩

include hcenv hpr in
theorem body_triple (k : Nat) :
    Sep.Triple ge fe f_sumlist (LMid p contents x k) bodyStmt
      (.only (fun e le hp => ∃ k', k' < k ∧ LInv p contents x k' e le hp)) := by
  refine Sep.triple_pre ge fe f_sumlist (P := fun e le hp => ∃ c1 a c2 b o u,
      ∃ _ : contents = c1 ++ a :: c2 ∧ c2.length + 1 = k, e = emptyEnv
      ∧ le.get _t = some (.Vptr b o) ∧ le.get _s = some (.Vint (sumInt c1))
      ∧ (listNode p b (Integers.Ptrofs.unsigned o) a u
          ∗ (lseg (listNode p) c1 x (.Vptr b o) ∗ listrepL p c2 u)) hp)
    (fun e le hp ⟨c1, a, c2, b, o, u, hc, hk, he, ht, hs, hh⟩ =>
      ⟨c1, a, c2, b, o, u, ⟨hc, hk⟩, he, ht, hs, by rwa [sep_left_comm_eq]⟩) ?_
  refine Sep.triple_exists ge fe f_sumlist _ _ _ (fun c1 => ?_)
  refine Sep.triple_exists ge fe f_sumlist _ _ _ (fun a => ?_)
  refine Sep.triple_exists ge fe f_sumlist _ _ _ (fun c2 => ?_)
  refine Sep.triple_exists ge fe f_sumlist _ _ _ (fun b => ?_)
  refine Sep.triple_exists ge fe f_sumlist _ _ _ (fun o => ?_)
  refine Sep.triple_exists ge fe f_sumlist _ _ _ (fun u => ?_)
  refine Sep.triple_exists ge fe f_sumlist _ _ _ (fun ⟨hc, hk⟩ => ?_)
  let H : HProp := listNode p b (Integers.Ptrofs.unsigned o) a u
    ∗ (lseg (listNode p) c1 x (.Vptr b o) ∗ listrepL p c2 u)
  -- `h = t->head;`
  refine Sep.triple_seq_only ge fe f_sumlist (Q := fun e le hp => e = emptyEnv
      ∧ le.get _t = some (.Vptr b o) ∧ le.get _s = some (.Vint (sumInt c1))
      ∧ le.get _h = some (.Vint a) ∧ H hp) ?_ ?_
  · refine Sep.triple_set ge fe f_sumlist _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, ht, hs, hH⟩ := hP
    exact ⟨_, eval_head layout hcenv rfl hpr ht hH hag, he, (PTree.gso _ _ _ _ (by decide)).trans ht,
      (PTree.gso _ _ _ _ (by decide)).trans hs, PTree.gss _ _ _, hH⟩
  -- `t = t->tail;`
  refine Sep.triple_seq_only ge fe f_sumlist (Q := fun e le hp => e = emptyEnv
      ∧ le.get _t = some u ∧ le.get _s = some (.Vint (sumInt c1))
      ∧ le.get _h = some (.Vint a) ∧ H hp) ?_ ?_
  · refine Sep.triple_set ge fe f_sumlist _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, ht, hs, hh, hH⟩ := hP
    have hu : IsLink u := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hl⟩ := hH
      exact isLink_of_listrep hl
    exact ⟨_, eval_tail layout hcenv hpr ht hu hH hag, he, PTree.gss _ _ _,
      (PTree.gso _ _ _ _ (by decide)).trans hs, (PTree.gso _ _ _ _ (by decide)).trans hh, hH⟩
  -- `s = s + h;`
  · refine Sep.triple_set ge fe f_sumlist _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, ht, hs, hh, hH⟩ := hP
    refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hs)
      (EvalExpr.Etempvar _ _ _ hh) (semBinop_add_uint _ m _ _),
      c2.length, by omega, c1 ++ [a], c2, u, by simpa using hc, rfl, he,
      (PTree.gso _ _ _ _ (by decide)).trans ht, by rw [PTree.gss, sumInt_snoc], ?_⟩
    obtain ⟨h1, h23, hd, rfl, hn, h2, h3, hd23, rfl, hseg, hl⟩ := hH
    have hd12 : Heap.disjoint h1 h2 := (Heap.disjoint_union_right.mp hd).1
    have hd13 : Heap.disjoint h1 h3 := (Heap.disjoint_union_right.mp hd).2
    refine ⟨Heap.union h2 h1, h3, Heap.disjoint_union_left.mpr ⟨hd23, hd13⟩, ?_,
      lseg_snoc _ a u b o c1 x _ ⟨h2, h1, Heap.disjoint_comm hd12, rfl, hseg, hn⟩, hl⟩
    rw [Heap.union_comm (Heap.disjoint_comm hd12), Heap.union_assoc]

include hcenv hpr in
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_sumlist (LInv p contents x k) loopStmt (LoopR p contents x) := by
  refine Sep.triple_loop ge fe f_sumlist (LoopR p contents x) (LInv p contents x)
    (fun k e le hp => ∃ k', k' < k ∧ LInv p contents x k' e le hp) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_sumlist _ (LMid p contents x k) _ _ _
      (Sep.triple_conseq ge fe f_sumlist (if_triple ge fe p contents x k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_sumlist _ _ _ _
        (body_triple ge fe p contents x hcenv hpr k) (fun _ _ _ x => x))
  · exact Sep.triple_fallthrough ge fe f_sumlist _ _ _ _
      (Sep.triple_skip ge fe f_sumlist _) (fun _ _ _ x => x)

end

end Sumlist

/-- `sumlist_spec` -/
def sumlistSpec (p : Permission) (contents : List Integers.Int) (x : Val) : Sep.FunSpec where
  tyargs := [tlistp]
  tyres := tuint
  cc := cc_default
  pre := fun vargs hp => vargs = [x] ∧ listrepL p contents x hp
  post := fun v hp => v = .Vint (sumInt contents) ∧ listrepL p contents x hp
  measure := fun _ => 0

/-- **`sumlist` satisfies `sumlist_spec`** (VST's `body_sumlist`). -/
theorem sumlist_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (contents : List Integers.Int) (x : Val)
    (hpr : permOrder p .Readable = true) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sumlist) (sumlistSpec p contents x) [x] := by
  open Sumlist in
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_sumlist _ _
    (fun e le hp => e = emptyEnv ∧ le.get _p = some x ∧ listrepL p contents x hp)
    (fun m => ?_) ?_
  · exact ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, PTree.gss _ _ _, hpre.2⟩⟩
  · rw [body_eq]
    -- `s = 0;`
    refine Sep.triple_seq_only ge _ f_sumlist (Q := fun e le hp => e = emptyEnv
        ∧ le.get _p = some x ∧ le.get _s = some (.Vint (Integers.Int.repr 0))
        ∧ listrepL p contents x hp) ?_ ?_
    · refine Sep.triple_set ge _ f_sumlist _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨he, hx, hl⟩ := hP
      exact ⟨_, EvalExpr.Econst_int _ tint, he, (PTree.gso _ _ _ _ (by decide)).trans hx,
        PTree.gss _ _ _, hl⟩
    -- `t = p;`
    refine Sep.triple_seq_only ge _ f_sumlist (Q := LInv p contents x contents.length) ?_ ?_
    · refine Sep.triple_set ge _ f_sumlist _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨he, hx, hs, hl⟩ := hP
      refine ⟨_, EvalExpr.Etempvar _ _ _ hx, [], contents, x, rfl, rfl, he, PTree.gss _ _ _,
        (PTree.gso _ _ _ _ (by decide)).trans hs, Heap.emp, hp, Heap.disjoint_emp_left _,
        (Heap.emp_union _).symm, ⟨rfl, rfl⟩, hl⟩
    -- the loop, then `return s;`
    refine Sep.triple_seq ge _ f_sumlist _ (Done p contents x) _ _ _
      (Sep.triple_conseq ge _ f_sumlist
        (loop_triple ge _ p contents x hcenv hpr contents.length)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x.elim)) ?_
    refine Sep.triple_return ge _ f_sumlist _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hs, hl⟩ := h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _s tuint _ hs, semCast_uint m _, ?_, ⟨rfl, hl⟩,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

/-! ## `reverse` -/

namespace Rev

def ifStmt : Stmt := .Sifthenelse (.Etempvar _v tlistp) .Sskip .Sbreak
def tailOf (x : Ident) : Expr := .Efield (.Ederef (.Etempvar x tlistp) tlist) _tail tlistp
def bodyStmt : Stmt :=
  .Ssequence (.Sset _t (tailOf _v))
    (.Ssequence (.Sassign (tailOf _v) (.Etempvar _w tlistp))
      (.Ssequence (.Sset _w (.Etempvar _v tlistp)) (.Sset _v (.Etempvar _t tlistp))))
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) .Sskip
def fullBody : Stmt :=
  .Ssequence (.Sset _w (.Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))
    (.Ssequence (.Sset _v (.Etempvar _p tlistp))
      (.Ssequence loopStmt (.Sreturn (some (.Etempvar _w tlistp)))))

theorem body_eq : f_reverse.fn_body = fullBody := rfl

section
variable (p : Permission) (contents : List Integers.Int)

/-- The loop invariant, `k` nodes left: `contents = rev c1 ++ c2`, the
    reversed part `c1` at `w`, the rest `c2` at `v`. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ c1 c2 w v, contents = c1.reverse ++ c2 ∧ c2.length = k ∧ e = emptyEnv
    ∧ le.get _w = some w ∧ le.get _v = some v
    ∧ (listrepL p c1 w ∗ listrepL p c2 v) hp

/-- After the test: `v` is a node `a`, followed by the list `c2`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ c1 a c2 w b o u, contents = c1.reverse ++ a :: c2 ∧ c2.length + 1 = k ∧ e = emptyEnv
    ∧ le.get _w = some w ∧ le.get _v = some (.Vptr b o)
    ∧ (listNode p b (Integers.Ptrofs.unsigned o) a u ∗ (listrepL p c1 w ∗ listrepL p c2 u)) hp

def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ ∃ w, le.get _w = some w ∧ listrepL p contents.reverse w hp

def LoopR : Sep.ExitConds :=
  { normal := Done p contents, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := fun _ _ => False }

end

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (contents : List Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)

theorem if_triple (k : Nat) :
    Sep.Triple ge fe f_reverse (LInv p contents k) ifStmt
      { normal := LMid p contents k, brk := Done p contents,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe f_reverse _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨c1, c2, w, v, -, hk, -, -, hv, hs⟩ := hP
      obtain ⟨_, _, _, _, _, hl⟩ := hs
      rcases listrep_val _ hl with ⟨rfl, _⟩ | ⟨_, _, _, hne⟩
      · exact ⟨_, EvalExpr.Etempvar _ _ _ hv, boolVal_null m _ _⟩
      · exact absurd (List.length_eq_zero_iff.mp hk) hne
    · refine Sep.triple_conseq ge fe f_reverse (Sep.triple_break ge fe f_reverse _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨c1, c2, w, v, hc, hk, he, hw, hv, h1, h2, hd, rfl, hl1, hl⟩ := h
      have hc2 := List.length_eq_zero_iff.mp hk
      subst hc2
      obtain ⟨rfl, rfl⟩ := hl
      rw [List.append_nil] at hc
      subst hc
      exact ⟨he, w, hw, by rw [Heap.union_emp, List.reverse_reverse]; exact hl1⟩
  | succ j =>
    refine Sep.triple_if_true ge fe f_reverse _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · obtain ⟨c1, c2, w, v, -, hk, -, -, hv, hs⟩ := hP
      obtain ⟨h1, h2, hd, rfl, _, hl⟩ := hs
      rcases listrep_val _ hl with ⟨rfl, hc2⟩ | ⟨b, o, rfl, _⟩
      · subst hc2; simp at hk
      · obtain ⟨a, l', u, rfl, hn⟩ := listrep_ptr _ hl
        exact ⟨_, EvalExpr.Etempvar _ _ _ hv, boolVal_ptr_valid m b o _ _
          (node_valid hn (Heap.Agrees_union_right hd hag))⟩
    · refine Sep.triple_fallthrough ge fe f_reverse _ _ _ _
        (Sep.triple_skip ge fe f_reverse _) (fun e le hp h => ?_)
      obtain ⟨c1, c2, w, v, hc, hk, he, hw, hv, h1, h2, hd, rfl, hl1, hl⟩ := h
      rcases listrep_val _ hl with ⟨rfl, hc2⟩ | ⟨b, o, rfl, _⟩
      · subst hc2; simp at hk
      · obtain ⟨a, l', u, rfl, n1, n2, hdn, rfl, hn, hl'⟩ := listrep_ptr _ hl
        have hdn1 : Heap.disjoint h1 n1 := (Heap.disjoint_union_right.mp hd).1
        have hdn2 : Heap.disjoint h1 n2 := (Heap.disjoint_union_right.mp hd).2
        refine ⟨c1, a, l', w, b, o, u, hc, by simpa using hk, he, hw, hv, n1, Heap.union h1 n2,
          Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hdn1, hdn⟩, ?_, hn,
          h1, n2, hdn2, rfl, hl1, hl'⟩
        rw [← Heap.union_assoc, ← Heap.union_assoc, Heap.union_comm hdn1]

include hcenv hpw in
theorem body_triple (k : Nat) :
    Sep.Triple ge fe f_reverse (LMid p contents k) bodyStmt
      (.only (fun e le hp => ∃ k', k' < k ∧ LInv p contents k' e le hp)) := by
  refine Sep.triple_pre ge fe f_reverse (P := fun e le hp => ∃ c1 a c2 w b o u,
      ∃ _ : contents = c1.reverse ++ a :: c2 ∧ c2.length + 1 = k ∧ IsLink w, e = emptyEnv
      ∧ le.get _w = some w ∧ le.get _v = some (.Vptr b o)
      ∧ (listNode p b (Integers.Ptrofs.unsigned o) a u
          ∗ (listrepL p c1 w ∗ listrepL p c2 u)) hp)
    (fun e le hp ⟨c1, a, c2, w, b, o, u, hc, hk, he, hw, hv, hh⟩ =>
      ⟨c1, a, c2, w, b, o, u, ⟨hc, hk, by
        obtain ⟨_, _, _, _, _, _, _, _, _, hl, _⟩ := hh
        exact isLink_of_listrep hl⟩, he, hw, hv, hh⟩) ?_
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun c1 => ?_)
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun a => ?_)
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun c2 => ?_)
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun w => ?_)
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun b => ?_)
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun o => ?_)
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun u => ?_)
  refine Sep.triple_exists ge fe f_reverse _ _ _ (fun ⟨hc, hk, hwl⟩ => ?_)
  let Rl : Env → TempEnv → Prop := fun e le => e = emptyEnv
    ∧ le.get _w = some w ∧ le.get _v = some (.Vptr b o) ∧ le.get _t = some u
  -- `t = v->tail;`
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp => Rl e le
      ∧ (listNode p b (Integers.Ptrofs.unsigned o) a u
          ∗ (listrepL p c1 w ∗ listrepL p c2 u)) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, hw, hv, hH⟩ := hP
    have hu : IsLink u := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hl⟩ := hH
      exact isLink_of_listrep hl
    exact ⟨_, eval_tail layout hcenv (readable_of_writable hpw) hv hu hH hag,
      ⟨he, (PTree.gso _ _ _ _ (by decide)).trans hw, (PTree.gso _ _ _ _ (by decide)).trans hv,
        PTree.gss _ _ _⟩, hH⟩
  -- `v->tail = w;`
  refine Sep.triple_seq_only ge fe f_reverse
    (triple_store_tail layout hcenv fe f_reverse Rl (listrepL p c1 w ∗ listrepL p c2 u) _v _w p b o a u w
      hpw (fun _ _ h => h.2.2.1) (fun _ _ h => h.2.1) hwl) ?_
  -- `w = v;`
  refine Sep.triple_seq_only ge fe f_reverse (Q := fun e le hp => e = emptyEnv
      ∧ le.get _w = some (.Vptr b o) ∧ le.get _t = some u
      ∧ (listNode p b (Integers.Ptrofs.unsigned o) a w
          ∗ (listrepL p c1 w ∗ listrepL p c2 u)) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, hw, hv, ht⟩, hH⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ _ _ hv, he, PTree.gss _ _ _,
      (PTree.gso _ _ _ _ (by decide)).trans ht, hH⟩
  -- `v = t;`
  · refine Sep.triple_set ge fe f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hw, ht, hH⟩ := hP
    refine ⟨_, EvalExpr.Etempvar _ _ _ ht, c2.length, by omega, a :: c1, c2, .Vptr b o, u,
      by simpa using hc, rfl, he, (PTree.gso _ _ _ _ (by decide)).trans hw, PTree.gss _ _ _, ?_⟩
    obtain ⟨h1, h23, hd, rfl, hn, h2, h3, hd23, rfl, hl1, hl2⟩ := hH
    have hd12 : Heap.disjoint h1 h2 := (Heap.disjoint_union_right.mp hd).1
    have hd13 : Heap.disjoint h1 h3 := (Heap.disjoint_union_right.mp hd).2
    refine ⟨Heap.union h1 h2, h3, Heap.disjoint_union_left.mpr ⟨hd13, hd23⟩,
      (Heap.union_assoc _ _ _).symm, listrep_cons _ ⟨h1, h2, hd12, rfl, hn, hl1⟩, hl2⟩

include hcenv hpw in
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_reverse (LInv p contents k) loopStmt (LoopR p contents) := by
  refine Sep.triple_loop ge fe f_reverse (LoopR p contents) (LInv p contents)
    (fun k e le hp => ∃ k', k' < k ∧ LInv p contents k' e le hp) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_reverse _ (LMid p contents k) _ _ _
      (Sep.triple_conseq ge fe f_reverse (if_triple ge fe p contents k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_reverse _ _ _ _
        (body_triple ge fe p contents hcenv hpw k) (fun _ _ _ x => x))
  · exact Sep.triple_fallthrough ge fe f_reverse _ _ _ _
      (Sep.triple_skip ge fe f_reverse _) (fun _ _ _ x => x)

end

end Rev

/-- `reverse_spec`: the result is a list holding the reversed contents. -/
def reverseSpec (p : Permission) (contents : List Integers.Int) (x : Val) : Sep.FunSpec where
  tyargs := [tlistp]
  tyres := tlistp
  cc := cc_default
  pre := fun vargs hp => vargs = [x] ∧ listrepL p contents x hp
  post := fun v hp => listrepL p contents.reverse v hp
  measure := fun _ => 0

/-- **`reverse` satisfies `reverse_spec`** (VST's `body_reverse`). -/
theorem reverse_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (contents : List Integers.Int) (x : Val)
    (hpw : permOrder p .Writable = true) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_reverse) (reverseSpec p contents x) [x] := by
  open Rev in
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_reverse _ _
    (fun e le hp => e = emptyEnv ∧ le.get _p = some x ∧ listrepL p contents x hp)
    (fun m => ?_) ?_
  · exact ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, PTree.gss _ _ _, hpre.2⟩⟩
  · rw [body_eq]
    -- `w = NULL;`
    refine Sep.triple_seq_only ge _ f_reverse (Q := fun e le hp => e = emptyEnv
        ∧ le.get _p = some x ∧ le.get _w = some Val.Vnullptr
        ∧ listrepL p contents x hp) ?_ ?_
    · refine Sep.triple_set ge _ f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨he, hx, hl⟩ := hP
      exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ tint) (semCast_int0_null m), he,
        (PTree.gso _ _ _ _ (by decide)).trans hx, PTree.gss _ _ _, hl⟩
    -- `v = p;`
    refine Sep.triple_seq_only ge _ f_reverse (Q := LInv p contents contents.length) ?_ ?_
    · refine Sep.triple_set ge _ f_reverse _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨he, hx, hw, hl⟩ := hP
      refine ⟨_, EvalExpr.Etempvar _ _ _ hx, [], contents, Val.Vnullptr, x, rfl, rfl, he,
        (PTree.gso _ _ _ _ (by decide)).trans hw, PTree.gss _ _ _, Heap.emp, hp,
        Heap.disjoint_emp_left _, (Heap.emp_union _).symm, ⟨rfl, rfl⟩, hl⟩
    -- the loop, then `return w;`
    refine Sep.triple_seq ge _ f_reverse _ (Done p contents) _ _ _
      (Sep.triple_conseq ge _ f_reverse
        (loop_triple ge _ p contents hcenv hpw contents.length)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x.elim)) ?_
    refine Sep.triple_return ge _ f_reverse _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, w, hw, hl⟩ := h
    refine ⟨_, _, m, hp, EvalExpr.Etempvar _ _ _ hw,
      semCast_ptr_ptr m w _ _ _ _ (isLink_of_listrep hl), ?_, hl,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

end VST.Verif.Reverse
