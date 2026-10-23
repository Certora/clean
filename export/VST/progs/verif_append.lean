/-
  Port of VST's `progs/verif_append.v`: `append` of `vst/progs/append.c`
  destructively appends two null-terminated linked lists.

      struct list {int head; struct list *tail;};

      struct list *append (struct list *x, struct list *y) {
        struct list *t, *u;
        if (x==NULL)
          return y;
        else {
          t = x;
          u = t->tail;
          while (u!=NULL) { t = u; u = t->tail; }
          t->tail = y;
          return x;
        }
      }

  VST's specification:

      append_spec: WITH sh, x, y, s1, s2
        PRE [tptr t_struct_list, tptr t_struct_list] PROP (writable_share sh)
          PARAMS (x; y) SEP (lseg LS sh s1 x nullval; lseg LS sh s2 y nullval)
        POST [tptr t_struct_list] EX r, RETURN (r)
          SEP (lseg LS sh (s1++s2) r nullval)

  The lists are `Sep.listrep (Sep.listNode p)` (`CCLib.logic.ListNode`), at a
  writable permission `p`; `ge` uses the program's composite environment.
  The loop invariant is VST's: the nodes before `t` form a segment
  `lseg s1a x t`, `t` is the node `a` whose link is `u`, followed by the rest
  `s1b` of `s1`, and `s1 = s1a ++ a :: s1b`.
-/
import VST.progs.append
import CCLib
open CC CC.Sep CC.HProp
open Append

namespace VST.Verif.Append

/-! ## The layout of `struct list` -/

abbrev tlist : Ty := .Tstruct _list noattr
abbrev tlistp : Ty := tptr tlist

def coList : Composite :=
  match prog.prog_comp_env.get _list with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

/-- `struct list` as a list layout (`Sep.ListLayout`). -/
def layout : ListLayout :=
  ⟨prog.prog_comp_env, _list, _head, _tail, coList, rfl, by decide, by decide⟩

/-- The list `s` at `x` (VST's `lseg LS sh s x nullval`). -/
abbrev listrepL (p : Permission) (s : List Integers.Int) (x : Val) : HProp :=
  listrep (listNode p) s x

/-- The node at `b + o`. -/
abbrev nodeAt (p : Permission) (b : Block) (o : Integers.Ptrofs) (a : Integers.Int) (u : Val) :
    HProp :=
  listNode p b (Integers.Ptrofs.unsigned o) a u

/-! ## The parts of the body -/

def nullE : Expr := .Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)
def tailOf (x : Ident) : Expr := .Efield (.Ederef (.Etempvar x tlistp) tlist) _tail tlistp
def ifStmt : Stmt := .Sifthenelse (.Ebinop .One (.Etempvar _u tlistp) nullE tint) .Sskip .Sbreak
def bodyStmt : Stmt := .Ssequence (.Sset _t (.Etempvar _u tlistp)) (.Sset _u (tailOf _t))
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) .Sskip
def elseStmt : Stmt :=
  .Ssequence (.Sset _t (.Etempvar _x tlistp))
    (.Ssequence (.Sset _u (tailOf _t))
      (.Ssequence loopStmt
        (.Ssequence (.Sassign (tailOf _t) (.Etempvar _y tlistp))
          (.Sreturn (some (.Etempvar _x tlistp))))))
def fullBody : Stmt :=
  .Sifthenelse (.Ebinop .Oeq (.Etempvar _x tlistp) nullE tint)
    (.Sreturn (some (.Etempvar _y tlistp))) elseStmt

theorem body_eq : f_append.fn_body = fullBody := rfl

theorem eval_null {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} :
    EvalExpr ge e le m nullE Val.Vnullptr :=
  EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ tint) (semCast_int0_null m)

/-! ## Assertions -/

section
variable (p : Permission) (s1 s2 : List Integers.Int) (x y : Val)

/-- `x` and `y` as passed. -/
def Params (e : Env) (le : TempEnv) : Prop :=
  e = emptyEnv ∧ le.get _x = some x ∧ le.get _y = some y

/-- The loop invariant, `k` nodes after `t`. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ s1a a s1b bt ot u, s1 = s1a ++ a :: s1b ∧ s1b.length = k ∧ Params x y e le
    ∧ le.get _t = some (.Vptr bt ot) ∧ le.get _u = some u
    ∧ (lseg (listNode p) s1a x (.Vptr bt ot) ∗ nodeAt p bt ot a u
        ∗ listrepL p s1b u ∗ listrepL p s2 y) hp

/-- After the test: `u` is the node `a'`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ s1a a a' s1b bt ot bu ou u', s1 = s1a ++ a :: a' :: s1b ∧ s1b.length + 1 = k
    ∧ Params x y e le ∧ le.get _t = some (.Vptr bt ot) ∧ le.get _u = some (.Vptr bu ou)
    ∧ (lseg (listNode p) s1a x (.Vptr bt ot) ∗ nodeAt p bt ot a (.Vptr bu ou)
        ∗ nodeAt p bu ou a' u' ∗ listrepL p s1b u' ∗ listrepL p s2 y) hp

/-- After the loop: `t` is the last node of `s1`. -/
def Done : Sep.Assn := fun e le hp =>
  ∃ s1a a bt ot, s1 = s1a ++ [a] ∧ Params x y e le ∧ le.get _t = some (.Vptr bt ot)
    ∧ (lseg (listNode p) s1a x (.Vptr bt ot) ∗ nodeAt p bt ot a Val.Vnullptr
        ∗ listrepL p s2 y) hp

def LoopR : Sep.ExitConds :=
  { normal := Done p s1 s2 x y, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := fun _ _ => False }

end

/-! ## The proof -/

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (s1 s2 : List Integers.Int) (x y : Val)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)

theorem if_triple (k : Nat) :
    Sep.Triple ge fe f_append (LInv p s1 s2 x y k) ifStmt
      { normal := LMid p s1 s2 x y k, brk := Done p s1 s2 x y,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe f_append _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨s1a, a, s1b, bt, ot, u, -, hk, -, -, hu, hs⟩ := hP
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, _⟩ := hs
      have hs1b := List.length_eq_zero_iff.mp hk
      subst hs1b
      obtain ⟨rfl, -⟩ := hl
      refine ⟨_, EvalExpr.Ebinop .One _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hu) eval_null
        (semBinop_ne_null _ m _ _ _ _ _ (Or.inl rfl)), ?_⟩
      simpa [typeof, Val.Vnullptr] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe f_append (Sep.triple_break ge fe f_append _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨s1a, a, s1b, bt, ot, u, hc, hk, hpar, ht, hu, hs⟩ := h
      have hs1b := List.length_eq_zero_iff.mp hk
      subst hs1b
      obtain ⟨h1, h234, hd, rfl, hseg, h2, h34, hd', rfl, hn, h3, h4, hd'', rfl, ⟨rfl, rfl⟩, hl2⟩ :=
        hs
      rw [Heap.emp_union] at hd' ⊢
      exact ⟨s1a, a, bt, ot, hc, hpar, ht, h1, Heap.union h2 h4, hd, rfl, hseg, h2, h4, hd', rfl,
        hn, hl2⟩
  | succ j =>
    refine Sep.triple_if_true ge fe f_append _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · obtain ⟨s1a, a, s1b, bt, ot, u, -, hk, -, -, hu, hs⟩ := hP
      obtain ⟨h1, h234, hd, rfl, _, h2, h34, hd', rfl, _, h3, h4, hd'', rfl, hl, _⟩ := hs
      have hag3 : Heap.Agrees (Heap.union h3 h4) m :=
        Heap.Agrees_union_right hd' (Heap.Agrees_union_right hd hag)
      rcases listrep_val _ hl with ⟨rfl, hc2⟩ | ⟨b, o, rfl, _⟩
      · subst hc2; simp at hk
      · obtain ⟨a', l', u', rfl, hn⟩ := listrep_ptr _ hl
        have hv := node_valid hn (Heap.Agrees_union_left hag3)
        refine ⟨_, EvalExpr.Ebinop .One _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hu) eval_null
          (semBinop_ne_null _ m _ _ _ _ _ (Or.inr ⟨b, o, rfl, hv⟩)), ?_⟩
        simpa [typeof, Val.Vnullptr] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe f_append _ _ _ _
        (Sep.triple_skip ge fe f_append _) (fun e le hp h => ?_)
      obtain ⟨s1a, a, s1b, bt, ot, u, hc, hk, hpar, ht, hu, hs⟩ := h
      obtain ⟨h1, h234, hd, rfl, hseg, h2, h34, hd', rfl, hn, h3, h4, hd'', rfl, hl, hl2⟩ := hs
      rcases listrep_val _ hl with ⟨rfl, hc2⟩ | ⟨b, o, rfl, _⟩
      · subst hc2; simp at hk
      · obtain ⟨a', l', u', rfl, n1, n2, hdn, rfl, hn', hl'⟩ := listrep_ptr _ hl
        have hdn24 : Heap.disjoint n2 h4 := (Heap.disjoint_union_left.mp hd'').2
        have hdn14 : Heap.disjoint n1 h4 := (Heap.disjoint_union_left.mp hd'').1
        refine ⟨s1a, a, a', l', bt, ot, b, o, u', hc, by simpa using hk, hpar, ht, hu,
          h1, _, hd, rfl, hseg, h2, _, hd', rfl, hn, n1, Heap.union n2 h4,
          Heap.disjoint_union_right.mpr ⟨hdn, hdn14⟩, Heap.union_assoc _ _ _, hn',
          n2, h4, hdn24, rfl, hl', hl2⟩

include hcenv hpw in
theorem body_triple (k : Nat) :
    Sep.Triple ge fe f_append (LMid p s1 s2 x y k) bodyStmt
      (.only (fun e le hp => ∃ k', k' < k ∧ LInv p s1 s2 x y k' e le hp)) := by
  refine Sep.triple_pre ge fe f_append (P := fun e le hp => ∃ s1a a a' s1b bt ot bu ou u',
      ∃ _ : s1 = s1a ++ a :: a' :: s1b ∧ s1b.length + 1 = k ∧ IsLink u',
      Params x y e le ∧ le.get _t = some (.Vptr bt ot) ∧ le.get _u = some (.Vptr bu ou)
      ∧ (nodeAt p bu ou a' u' ∗ (lseg (listNode p) s1a x (.Vptr bt ot)
          ∗ nodeAt p bt ot a (.Vptr bu ou)) ∗ listrepL p s1b u' ∗ listrepL p s2 y) hp)
    (fun e le hp ⟨s1a, a, a', s1b, bt, ot, bu, ou, u', hc, hk, hpar, ht, hu, hs⟩ =>
      ⟨s1a, a, a', s1b, bt, ot, bu, ou, u', ⟨hc, hk, by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, _⟩ := hs
        exact isLink_of_listrep hl⟩, hpar, ht, hu, by
          rw [← sep_assoc_eq] at hs
          rw [sep_left_comm_eq]
          exact hs⟩) ?_
  refine Sep.triple_exists ge fe f_append _ _ _ (fun s1a => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun a => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun a' => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun s1b => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun bt => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun ot => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun bu => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun ou => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun u' => ?_)
  refine Sep.triple_exists ge fe f_append _ _ _ (fun ⟨hc, hk, hul⟩ => ?_)
  -- `t = u;`
  refine Sep.triple_seq_only ge fe f_append (Q := fun e le hp => Params x y e le
      ∧ le.get _t = some (.Vptr bu ou)
      ∧ (nodeAt p bu ou a' u' ∗ (lseg (listNode p) s1a x (.Vptr bt ot)
          ∗ nodeAt p bt ot a (.Vptr bu ou)) ∗ listrepL p s1b u' ∗ listrepL p s2 y) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_append _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, hx, hy⟩, ht, hu, hH⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ _ _ hu, ⟨he, (PTree.gso _ _ _ _ (by decide)).trans hx,
      (PTree.gso _ _ _ _ (by decide)).trans hy⟩, PTree.gss _ _ _, hH⟩
  -- `u = t->tail;`
  · refine Sep.triple_set ge fe f_append _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, hx, hy⟩, ht, hH⟩ := hP
    refine ⟨_, eval_tail layout hcenv (readable_of_writable hpw) ht hul hH hag,
      s1b.length, by omega, s1a ++ [a], a', s1b, bu, ou, u', by simpa using hc, rfl,
      ⟨he, (PTree.gso _ _ _ _ (by decide)).trans hx, (PTree.gso _ _ _ _ (by decide)).trans hy⟩,
      (PTree.gso _ _ _ _ (by decide)).trans ht, PTree.gss _ _ _, ?_⟩
    obtain ⟨h1, h234, hd, rfl, hn, h2, h34, hd', rfl, hseg, hrest⟩ := hH
    have hd12 : Heap.disjoint h1 h2 := (Heap.disjoint_union_right.mp hd).1
    have hd134 : Heap.disjoint h1 h34 := (Heap.disjoint_union_right.mp hd).2
    refine ⟨h2, Heap.union h1 h34, Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hd12, hd'⟩,
      ?_, lseg_snoc _ a _ bt ot s1a x h2 hseg, h1, h34, hd134, rfl, hn, hrest⟩
    rw [← Heap.union_assoc, ← Heap.union_assoc, Heap.union_comm hd12]

include hcenv hpw in
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_append (LInv p s1 s2 x y k) loopStmt (LoopR p s1 s2 x y) := by
  refine Sep.triple_loop ge fe f_append (LoopR p s1 s2 x y) (LInv p s1 s2 x y)
    (fun k e le hp => ∃ k', k' < k ∧ LInv p s1 s2 x y k' e le hp) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_append _ (LMid p s1 s2 x y k) _ _ _
      (Sep.triple_conseq ge fe f_append (if_triple ge fe p s1 s2 x y k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_append _ _ _ _
        (body_triple ge fe p s1 s2 x y hcenv hpw k) (fun _ _ _ x => x))
  · exact Sep.triple_fallthrough ge fe f_append _ _ _ _
      (Sep.triple_skip ge fe f_append _) (fun _ _ _ x => x)

end

/-! ## As a function specification -/

/-- `append_spec` -/
def appendSpec (p : Permission) (s1 s2 : List Integers.Int) (x y : Val) : Sep.FunSpec where
  tyargs := [tlistp, tlistp]
  tyres := tlistp
  cc := cc_default
  pre := fun vargs hp => vargs = [x, y] ∧ (listrepL p s1 x ∗ listrepL p s2 y) hp
  post := fun r hp => listrepL p (s1 ++ s2) r hp
  measure := fun _ => 0

/-- **`append` satisfies `append_spec`** (VST's `body_append`). -/
theorem append_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (s1 s2 : List Integers.Int) (x y : Val)
    (hpw : permOrder p .Writable = true) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_append) (appendSpec p s1 s2 x y)
      [x, y] := by
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_append _ _
    (fun e le hp => Params x y e le ∧ (listrepL p s1 x ∗ listrepL p s2 y) hp)
    (fun m => ?_) ?_
  · exact ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨⟨rfl, (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _),
        PTree.gss _ _ _⟩, hpre.2⟩⟩
  rw [body_eq]
  have hret : ∀ (r : Val) (H : HProp) (a : Expr) (hev : ∀ e le m, Params x y e le →
      EvalExpr ge e le m a r) (hty : typeof a = tlistp),
      (∀ hp, H hp → listrepL p (s1 ++ s2) r hp) →
      Sep.Triple ge (FunctionEntry2 ge) f_append (fun e le hp => Params x y e le ∧ H hp)
        (.Sreturn (some a))
        { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
          ret := (appendSpec p s1 s2 x y).post } := by
    intro r H a hev hty himp
    refine Sep.triple_return ge _ f_append _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨hpar, hH⟩ := h
    refine ⟨r, r, m, hp, hev e le m hpar,
      by rw [hty]; exact semCast_ptr_ptr m r _ _ _ _ (isLink_of_listrep (himp hp hH)),
      by rw [hpar.1]; exact freeList_emptyEnv _ _, himp hp hH, fun _ hdj hag => ⟨hdj, hag⟩⟩
  cases s1 with
  | nil =>
    -- `x == NULL`: `return y;`
    refine Sep.triple_if_true ge _ f_append _ _ _ _ _ (fun e le hp m hP _ => ?_)
      (Sep.triple_pre ge _ f_append (P := fun e le hp => Params x y e le ∧ listrepL p s2 y hp)
        (fun e le hp ⟨hpar, hH⟩ => ⟨hpar, ?_⟩)
        (hret y _ _ (fun e le m h => EvalExpr.Etempvar _ _ _ h.2.2) rfl (fun _ h => h)))
    · obtain ⟨⟨he, hx, hy⟩, h1, h2, hd, rfl, ⟨rfl, rfl⟩, _⟩ := hP
      refine ⟨_, EvalExpr.Ebinop .Oeq _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx) eval_null
        (semBinop_eq_null _ m _ _ _ _ _ (Or.inl rfl)), ?_⟩
      simpa [typeof, Val.Vnullptr] using boolVal_ofBool_int m true
    · obtain ⟨h1, h2, hd, rfl, ⟨rfl, rfl⟩, hl⟩ := hH
      rwa [Heap.emp_union]
  | cons a s1' =>
    -- `x` is the first node of `s1`
    refine Sep.triple_pre ge _ f_append (P := fun e le hp => ∃ b o u0,
        ∃ _ : x = .Vptr b o ∧ IsLink u0 ∧ IsLink y, Params x y e le
        ∧ (nodeAt p b o a u0 ∗ listrepL p s1' u0 ∗ listrepL p s2 y) hp)
      (fun e le hp ⟨hpar, hH⟩ => ?_) ?_
    · obtain ⟨h1, h2, hd, rfl, hl, hl2⟩ := hH
      rcases listrep_val _ hl with ⟨_, hne⟩ | ⟨b, o, rfl, _⟩
      · exact absurd hne (List.cons_ne_nil _ _)
      · obtain ⟨a0, l0, u0, heq, n1, n2, hdn, rfl, hn, hl'⟩ := listrep_ptr _ hl
        cases heq
        have hdn1 : Heap.disjoint n1 h2 := (Heap.disjoint_union_left.mp hd).1
        have hdn2 : Heap.disjoint n2 h2 := (Heap.disjoint_union_left.mp hd).2
        exact ⟨b, o, u0, ⟨rfl, isLink_of_listrep hl', isLink_of_listrep hl2⟩, hpar,
          n1, Heap.union n2 h2, Heap.disjoint_union_right.mpr ⟨hdn, hdn1⟩,
          Heap.union_assoc _ _ _, hn, n2, h2, hdn2, rfl, hl', hl2⟩
    refine Sep.triple_exists ge _ f_append _ _ _ (fun b => ?_)
    refine Sep.triple_exists ge _ f_append _ _ _ (fun o => ?_)
    refine Sep.triple_exists ge _ f_append _ _ _ (fun u0 => ?_)
    refine Sep.triple_exists ge _ f_append _ _ _ (fun ⟨hxb, hu0, hyl⟩ => ?_)
    subst hxb
    refine Sep.triple_if_false ge _ f_append _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · obtain ⟨⟨he, hx, hy⟩, hH⟩ := hP
      have hv := node_valid hH hag
      refine ⟨_, EvalExpr.Ebinop .Oeq _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx) eval_null
        (semBinop_eq_null _ m _ _ _ _ _ (Or.inr ⟨b, o, rfl, hv⟩)), ?_⟩
      simpa [typeof, Val.Vnullptr] using boolVal_ofBool_int m false
    -- `t = x;`
    refine Sep.triple_seq_only ge _ f_append (Q := fun e le hp => Params (.Vptr b o) y e le
        ∧ le.get _t = some (.Vptr b o)
        ∧ (nodeAt p b o a u0 ∗ listrepL p s1' u0 ∗ listrepL p s2 y) hp) ?_ ?_
    · refine Sep.triple_set ge _ f_append _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨⟨he, hx, hy⟩, hH⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ _ _ hx, ⟨he, (PTree.gso _ _ _ _ (by decide)).trans hx,
        (PTree.gso _ _ _ _ (by decide)).trans hy⟩, PTree.gss _ _ _, hH⟩
    -- `u = t->tail;`
    refine Sep.triple_seq_only ge _ f_append
      (Q := LInv p (a :: s1') s2 (.Vptr b o) y s1'.length) ?_ ?_
    · refine Sep.triple_set ge _ f_append _ _ _ _ (fun e le hp m hP hag => ?_)
      obtain ⟨⟨he, hx, hy⟩, ht, hH⟩ := hP
      refine ⟨_, eval_tail layout hcenv (readable_of_writable hpw) ht hu0 hH hag,
        [], a, s1', b, o, u0, rfl, rfl,
        ⟨he, (PTree.gso _ _ _ _ (by decide)).trans hx, (PTree.gso _ _ _ _ (by decide)).trans hy⟩,
        (PTree.gso _ _ _ _ (by decide)).trans ht, PTree.gss _ _ _,
        Heap.emp, hp, Heap.disjoint_emp_left _, (Heap.emp_union _).symm, ⟨rfl, rfl⟩, hH⟩
    -- the loop
    refine Sep.triple_seq ge _ f_append _ (Done p (a :: s1') s2 (.Vptr b o) y) _ _ _
      (Sep.triple_conseq ge _ f_append
        (loop_triple ge _ p (a :: s1') s2 (.Vptr b o) y hcenv hpw s1'.length)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x.elim)) ?_
    -- `t->tail = y; return x;`
    refine Sep.triple_pre ge _ f_append (P := fun e le hp => ∃ s1a a' bt ot,
        ∃ _ : a :: s1' = s1a ++ [a'], (Params (.Vptr b o) y e le
          ∧ le.get _t = some (.Vptr bt ot))
        ∧ (nodeAt p bt ot a' Val.Vnullptr
            ∗ lseg (listNode p) s1a (.Vptr b o) (.Vptr bt ot) ∗ listrepL p s2 y) hp)
      (fun e le hp ⟨s1a, a', bt, ot, hc, hpar, ht, hH⟩ =>
        ⟨s1a, a', bt, ot, hc, ⟨hpar, ht⟩, by rwa [sep_left_comm_eq] at hH⟩) ?_
    refine Sep.triple_exists ge _ f_append _ _ _ (fun s1a => ?_)
    refine Sep.triple_exists ge _ f_append _ _ _ (fun a' => ?_)
    refine Sep.triple_exists ge _ f_append _ _ _ (fun bt => ?_)
    refine Sep.triple_exists ge _ f_append _ _ _ (fun ot => ?_)
    refine Sep.triple_exists ge _ f_append _ _ _ (fun hc => ?_)
    refine Sep.triple_seq_only ge _ f_append
      (triple_store_tail layout hcenv _ f_append _ _ _t _y p bt ot a' Val.Vnullptr y hpw
        (fun _ _ h => h.2) (fun _ _ h => h.1.2.2) hyl) ?_
    refine Sep.triple_pre ge _ f_append (fun e le hp h => ⟨h.1.1, h.2⟩)
      (hret (.Vptr b o) _ _ (fun e le m h => EvalExpr.Etempvar _ _ _ h.2.1) rfl
        (fun hp hH => ?_))
    obtain ⟨h1, h23, hd, rfl, hn, h2, h3, hd23, rfl, hseg, hl2⟩ := hH
    have hd12 : Heap.disjoint h1 h2 := (Heap.disjoint_union_right.mp hd).1
    have hd13 : Heap.disjoint h1 h3 := (Heap.disjoint_union_right.mp hd).2
    have := lseg_listrep _ (l2 := a' :: s2) (h := Heap.union h2 (Heap.union h1 h3))
      ⟨h2, Heap.union h1 h3, Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hd12, hd23⟩, rfl,
        hseg, listrep_cons _ ⟨h1, h3, hd13, rfl, hn, hl2⟩⟩
    have hl : a :: s1' ++ s2 = s1a ++ a' :: s2 := by
      rw [hc, List.append_assoc, List.singleton_append]
    show listrepL p (a :: s1' ++ s2) _ _
    rw [hl]
    rwa [← Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm hd12), Heap.union_assoc] at this

end VST.Verif.Append
