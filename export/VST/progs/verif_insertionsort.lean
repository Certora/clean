/-
  Port of VST's `progs/verif_insertion_sort.v`: `insert` of
  `vst/progs/insertionsort.c` inserts a node into a sorted linked list.

      struct list {int head; struct list *tail;};

      struct list *insert(struct list *insert_node, struct list *sorted){
        struct list *index, *previous;
        int sortedvalue, guard, insert_value;
        previous = NULL;
        insert_value = insert_node -> head;
        index = sorted;
        if(index){ sortedvalue = index -> head; }
        guard = index && (insert_value > sortedvalue);
        while(guard){
          previous = index;
          index = index -> tail;
          if(index) { sortedvalue = index -> head; }
          guard = index && (insert_value > sortedvalue);
        }
        insert_node -> tail = index;
        if(previous){ previous->tail = insert_node; return sorted; }
        return insert_node;
      }

  VST's specification:

      Fixpoint insert x xs :=
        match xs with
        | [] => [x]
        | h :: t => if Int.cmp Cle x h then x :: xs else h :: (insert x t)
        end.

      insert_spec: WITH sh, contents, insert_val, sorted_ptr, insert_ptr
        PRE [_insert_node OF (tptr t_struct_list), _sorted OF (tptr t_struct_list)]
          PROP (writable_share sh)
          LOCAL (temp _sorted sorted_ptr; temp _insert_node insert_ptr)
          SEP (lseg LS sh (map Vint contents) sorted_ptr nullval;
               data_at sh t_struct_list (Vint insert_val, nullval) insert_ptr)
        POST [tptr t_struct_list] EX v: val, PROP() LOCAL(temp ret_temp v)
          SEP(lseg LS sh (map Vint (insert insert_val contents)) v nullval).

  As in VST, the specification does not require `contents` to be sorted:
  `insert` is the functional model on any list.  The list predicate is
  `Sep.listrep (Sep.listNode p)` (`CCLib.logic.ListNode`) at a writable
  permission `p`; `ge` uses the program's composite environment.

  The loop invariant is VST's `insert_invariant`: the elements already passed
  (`pre`, all smaller than `insert_val`) form a segment from `sorted` whose
  last node is `previous` (or `pre` is empty, `previous` is `NULL` and
  `index = sorted`), followed by the rest `c2` at `index`; `guard` holds the
  value of `index && insert_val > index->head`.
-/
import VST.progs.insertionsort
import CCLib
open CC CC.Sep CC.HProp
open Insertionsort

namespace VST.Verif.InsertionSort

/-! ## The functional model -/

/-- VST's `insert`. -/
def insert (x : Integers.Int) : List Integers.Int → List Integers.Int
  | [] => [x]
  | h :: t => if Integers.Int.cmp .Cle x h then x :: h :: t else h :: insert x t

/-- VST's `insertion_sort`. -/
def insertionSort (xs : List Integers.Int) : List Integers.Int := xs.foldr insert []

/-- The value of `guard`: `index && insert_value > index->head`. -/
def guardB (v : Integers.Int) : List Integers.Int → Bool
  | [] => false
  | a :: _ => Integers.Int.lt a v

theorem cmp_le_eq (x y : Integers.Int) :
    Integers.Int.cmp .Cle x y = !Integers.Int.lt y x := rfl

theorem insert_split (v : Integers.Int) :
    ∀ (pre c2 : List Integers.Int), (∀ x ∈ pre, Integers.Int.lt x v = true) →
      guardB v c2 = false → insert v (pre ++ c2) = pre ++ v :: c2
  | [], [], _, _ => rfl
  | [], a :: c, _, hg => by
    simp only [guardB] at hg
    simp [insert, cmp_le_eq, hg]
  | x :: pre, c2, hpre, hg => by
    have hx := hpre x (by simp)
    have ih := insert_split v pre c2 (fun y hy => hpre y (by simp [hy])) hg
    simp [insert, cmp_le_eq, hx, ih]

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

/-- The list `s` at `x` (VST's `lseg LS sh (map Vint s) x nullval`). -/
abbrev listrepL (p : Permission) (s : List Integers.Int) (x : Val) : HProp :=
  listrep (listNode p) s x

/-- The node at `b + o`. -/
abbrev nodeAt (p : Permission) (b : Block) (o : Integers.Ptrofs) (a : Integers.Int) (u : Val) :
    HProp :=
  listNode p b (Integers.Ptrofs.unsigned o) a u


/-! ## The parts of the body of `insert` -/

namespace Insert

def nullE : Expr := .Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)
def headOf (x : Ident) : Expr := .Efield (.Ederef (.Etempvar x tlistp) tlist) _head tint
def tailOf (x : Ident) : Expr := .Efield (.Ederef (.Etempvar x tlistp) tlist) _tail tlistp

/-- `if (index) sortedvalue = index->head;` -/
def svStmt : Stmt :=
  .Sifthenelse (.Etempvar _index tlistp) (.Sset _sortedvalue (headOf _index)) .Sskip

/-- `guard = index && (insert_value > sortedvalue);`, through the temporary `t`. -/
def cmpStmt (t : Ident) : Stmt :=
  .Ssequence
    (.Sifthenelse (.Etempvar _index tlistp)
      (.Sset t (.Ecast (.Ebinop .Ogt (.Etempvar _insert_value tint)
        (.Etempvar _sortedvalue tint) tint) tbool))
      (.Sset t (.Econst_int (Integers.Int.repr 0) tint)))
    (.Sset _guard (.Etempvar t tint))

def bodyStmt : Stmt :=
  .Ssequence (.Sset _previous (.Etempvar _index tlistp))
    (.Ssequence (.Sset _index (tailOf _index))
      (.Ssequence svStmt (cmpStmt _t'2)))

def ifStmt : Stmt := .Sifthenelse (.Etempvar _guard tint) .Sskip .Sbreak

def loopStmt : Stmt := swhile (.Etempvar _guard tint) bodyStmt

def retSorted : Stmt := .Sreturn (some (.Etempvar _sorted tlistp))
def retNode : Stmt := .Sreturn (some (.Etempvar _insert_node tlistp))

def linkStmt : Stmt :=
  .Sifthenelse (.Etempvar _previous tlistp)
    (.Ssequence (.Sassign (tailOf _previous) (.Etempvar _insert_node tlistp)) retSorted)
    .Sskip

def finStmt : Stmt :=
  .Ssequence (.Sassign (tailOf _insert_node) (.Etempvar _index tlistp))
    (.Ssequence linkStmt retNode)

def fullBody : Stmt :=
  .Ssequence (.Sset _previous nullE)
    (.Ssequence (.Sset _insert_value (headOf _insert_node))
      (.Ssequence (.Sset _index (.Etempvar _sorted tlistp))
        (.Ssequence svStmt
          (.Ssequence (cmpStmt _t'1)
            (.Ssequence loopStmt finStmt)))))

theorem body_eq : f_insert.fn_body = fullBody := rfl

/-! ### Assertions -/

section
variable (p : Permission)

/-- The part of the list already passed: empty (`previous` is `NULL` and
    `index = sorted`), or a segment from `sorted` whose last node `a` is at
    `previous` and links to `index`. -/
def PreSeg (pre : List Integers.Int) (s prev idx : Val) : HProp := fun h =>
  (pre = [] ∧ prev = Val.Vnullptr ∧ s = idx ∧ h = Heap.emp)
  ∨ ∃ pre' a b o, pre = pre' ++ [a] ∧ prev = .Vptr b o
      ∧ (lseg (listNode p) pre' s prev ∗ nodeAt p b o a idx) h

theorem preSeg_lseg {pre : List Integers.Int} {s prev idx : Val} {h : Heap}
    (hs : PreSeg p pre s prev idx h) : lseg (listNode p) pre s idx h := by
  rcases hs with ⟨rfl, -, rfl, rfl⟩ | ⟨pre', a, b, o, rfl, rfl, hh⟩
  · exact ⟨rfl, rfl⟩
  · exact lseg_snoc _ a idx b o pre' s h hh

variable (bi : Block) (oi : Integers.Ptrofs) (s : Val) (v : Integers.Int)

/-- The temporaries that matter. -/
def Temps (prev idx : Val) (le : TempEnv) : Prop :=
  le.get _insert_node = some (.Vptr bi oi) ∧ le.get _sorted = some s
  ∧ le.get _insert_value = some (.Vint v) ∧ le.get _previous = some prev
  ∧ le.get _index = some idx

/-- The heap: the rest `c2` of the list at `index`, the node being inserted,
    the part already passed. -/
def Heap3 (pre c2 : List Integers.Int) (prev idx : Val) (w : Val) : HProp :=
  listrepL p c2 idx ∗ nodeAt p bi oi v w ∗ PreSeg p pre s prev idx

variable (contents : List Integers.Int)

/-- The loop invariant, `k` nodes left. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ pre c2 prev idx, contents = pre ++ c2 ∧ c2.length = k
    ∧ (∀ x ∈ pre, Integers.Int.lt x v = true) ∧ e = emptyEnv
    ∧ Temps bi oi s v prev idx le ∧ le.get _guard = some (Val.ofBool (guardB v c2))
    ∧ Heap3 p bi oi s v pre c2 prev idx Val.Vnullptr hp

/-- After the test: `index` is the node `a`, smaller than `insert_val`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ pre a c2 prev b o u, contents = pre ++ a :: c2 ∧ c2.length + 1 = k
    ∧ (∀ x ∈ pre, Integers.Int.lt x v = true) ∧ Integers.Int.lt a v = true ∧ e = emptyEnv
    ∧ Temps bi oi s v prev (.Vptr b o) le
    ∧ (nodeAt p b o a u ∗ listrepL p c2 u ∗ nodeAt p bi oi v Val.Vnullptr
        ∗ PreSeg p pre s prev (.Vptr b o)) hp

/-- After the loop. -/
def Done : Sep.Assn := fun e le hp =>
  ∃ pre c2 prev idx, contents = pre ++ c2 ∧ (∀ x ∈ pre, Integers.Int.lt x v = true)
    ∧ guardB v c2 = false ∧ e = emptyEnv ∧ Temps bi oi s v prev idx le
    ∧ Heap3 p bi oi s v pre c2 prev idx Val.Vnullptr hp

def LoopR : Sep.ExitConds :=
  { normal := Done p bi oi s v contents, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := fun _ _ => False }

end


/-- `sortedvalue` holds the first element of `c2`, if any. -/
def SvOk (c2 : List Integers.Int) (le : TempEnv) : Prop :=
  ∀ a c, c2 = a :: c → le.get _sortedvalue = some (.Vint a)

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (v : Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)

include hcenv hpw in
/-- `if (index) sortedvalue = index->head;` -/
theorem sv_triple (Q : Env → TempEnv → Prop) (F : HProp) (c2 : List Integers.Int) (idx : Val)
    (hidx : ∀ e le, Q e le → le.get _index = some idx)
    (hQ : ∀ e le w, Q e le → Q e (le.set _sortedvalue w)) :
    Sep.Triple ge fe f_insert (fun e le hp => Q e le ∧ (listrepL p c2 idx ∗ F) hp) svStmt
      (.only fun e le hp => Q e le ∧ SvOk c2 le ∧ (listrepL p c2 idx ∗ F) hp) := by
  cases c2 with
  | nil =>
    refine Sep.triple_if_false ge fe f_insert _ _ _ _ _ (fun e le hp m hP _ => ?_)
      (Sep.triple_fallthrough ge fe f_insert _ _ _ _ (Sep.triple_skip ge fe f_insert _)
        (fun e le hp ⟨hq, hH⟩ => ⟨hq, (fun a c h => nomatch h), hH⟩))
    obtain ⟨hq, h1, h2, hd, rfl, hl, _⟩ := hP
    obtain ⟨rfl, -⟩ := hl
    exact ⟨_, EvalExpr.Etempvar _ _ _ (hidx e le hq), boolVal_null m _ _⟩
  | cons a c =>
    refine Sep.triple_if_true ge fe f_insert _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · obtain ⟨hq, hH⟩ := hP
      obtain ⟨b, o, u, rfl, -, hH'⟩ := listrep_cons_front hH
      exact ⟨_, EvalExpr.Etempvar _ _ _ (hidx e le hq),
        boolVal_ptr_valid m b o _ _ (node_valid hH' hag)⟩
    · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP hag => ?_)
      obtain ⟨hq, hH⟩ := hP
      obtain ⟨b, o, u, rfl, -, hH'⟩ := listrep_cons_front hH
      refine ⟨_, eval_head layout hcenv rfl (readable_of_writable hpw) (hidx e le hq) hH' hag,
        hQ e le _ hq, fun a' c' h => ?_, hH⟩
      injection h with e1 e2
      subst e1
      exact PTree.gss _ _ _

/-- `guard = index && (insert_value > sortedvalue);` -/
theorem cmp_triple (t : Ident) (Q : Env → TempEnv → Prop) (F : HProp) (c2 : List Integers.Int)
    (idx : Val)
    (hidx : ∀ e le, Q e le → le.get _index = some idx)
    (hv : ∀ e le, Q e le → le.get _insert_value = some (.Vint v))
    (hQt : ∀ e le w, Q e le → Q e (le.set t w))
    (hQg : ∀ e le w, Q e le → Q e (le.set _guard w)) :
    Sep.Triple ge fe f_insert (fun e le hp => Q e le ∧ SvOk c2 le ∧ (listrepL p c2 idx ∗ F) hp)
      (cmpStmt t)
      (.only fun e le hp => Q e le ∧ le.get _guard = some (Val.ofBool (guardB v c2))
        ∧ (listrepL p c2 idx ∗ F) hp) := by
  refine Sep.triple_seq_only ge fe f_insert (Q := fun e le hp => Q e le
      ∧ le.get t = some (Val.ofBool (guardB v c2)) ∧ (listrepL p c2 idx ∗ F) hp) ?_ ?_
  · cases c2 with
    | nil =>
      refine Sep.triple_if_false ge fe f_insert _ _ _ _ _ (fun e le hp m hP _ => ?_)
        (Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP _ =>
          ⟨_, EvalExpr.Econst_int _ _, hQt e le _ hP.1, PTree.gss _ _ _, hP.2.2⟩))
      obtain ⟨hq, -, h1, h2, hd, rfl, hl, _⟩ := hP
      obtain ⟨rfl, -⟩ := hl
      exact ⟨_, EvalExpr.Etempvar _ _ _ (hidx e le hq), boolVal_null m _ _⟩
    | cons a c =>
      refine Sep.triple_if_true ge fe f_insert _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
      · obtain ⟨hq, -, hH⟩ := hP
        obtain ⟨b, o, u, rfl, -, hH'⟩ := listrep_cons_front hH
        exact ⟨_, EvalExpr.Etempvar _ _ _ (hidx e le hq),
          boolVal_ptr_valid m b o _ _ (node_valid hH' hag)⟩
      · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP _ => ?_)
        obtain ⟨hq, hsv, hH⟩ := hP
        exact ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop .Ogt _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hv e le hq)) (EvalExpr.Etempvar _ _ _ (hsv a c rfl))
            (semBinop_gt_int _ m v a)) (semCast_ofBool_bool _ m),
          hQt e le _ hq, PTree.gss _ _ _, hH⟩
  · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨hq, ht, hH⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ _ _ ht, hQg e le _ hq, PTree.gss _ _ _, hH⟩

end

theorem temps_set {bi : Block} {oi : Integers.Ptrofs} {s : Val} {v : Integers.Int}
    {prev idx : Val} {le : TempEnv} (id : Ident) (w : Val)
    (hid : id = _sortedvalue ∨ id = _t'1 ∨ id = _t'2 ∨ id = _guard)
    (h : Temps bi oi s v prev idx le) : Temps bi oi s v prev idx (le.set id w) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rcases hid with rfl | rfl | rfl | rfl <;>
  exact ⟨(PTree.gso _ _ _ _ (by decide)).trans h1, (PTree.gso _ _ _ _ (by decide)).trans h2,
    (PTree.gso _ _ _ _ (by decide)).trans h3, (PTree.gso _ _ _ _ (by decide)).trans h4,
    (PTree.gso _ _ _ _ (by decide)).trans h5⟩

/-- One step of the loop on the heap: the node `a` at `index` joins the part
    already passed. -/
theorem heap_step (p : Permission) {b : Block} {o : Integers.Ptrofs} {a : Integers.Int}
    {u s prev : Val} {c2 pre : List Integers.Int} {N : HProp} {hp : Heap}
    (h : (nodeAt p b o a u ∗ listrepL p c2 u ∗ N ∗ PreSeg p pre s prev (.Vptr b o)) hp) :
    (listrepL p c2 u ∗ N ∗ PreSeg p (pre ++ [a]) s (.Vptr b o) u) hp := by
  have h1 : (nodeAt p b o a u ∗ listrepL p c2 u ∗ N
      ∗ lseg (listNode p) pre s (.Vptr b o)) hp :=
    sep_mono (entails_refl _) (sep_mono (entails_refl _)
      (sep_mono (entails_refl _) (fun _ hh => preSeg_lseg p hh))) hp h
  have e : (nodeAt p b o a u ∗ listrepL p c2 u ∗ N ∗ lseg (listNode p) pre s (.Vptr b o))
      = (listrepL p c2 u ∗ N ∗ (lseg (listNode p) pre s (.Vptr b o) ∗ nodeAt p b o a u)) := by
    rw [sep_left_comm_eq, sep_left_comm_eq (nodeAt p b o a u), sep_comm_eq (nodeAt p b o a u)]
  rw [e] at h1
  exact sep_mono (entails_refl _) (sep_mono (entails_refl _)
    (fun _ hh => Or.inr ⟨pre, a, b, o, rfl, rfl, hh⟩)) hp h1

/-- `return x;` of a link `r` described by `post`, in a function returning
    `struct list *` with no local variables. -/
theorem ret_triple (ge : CGenv) (fe : EntryRel) (f : Function) (hf : f.fn_return = tlistp)
    (post : Val → HProp) (P : Sep.Assn) (x : Ident) (r : Val)
    (hr : ∀ hp, post r hp → IsLink r)
    (h : ∀ e le hp, P e le hp → e = emptyEnv ∧ le.get x = some r ∧ post r hp) :
    Sep.Triple ge fe f P (.Sreturn (some (.Etempvar x tlistp)))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := post } := by
  refine Sep.triple_return ge fe f _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨he, hx, hpost⟩ := h e le hp hP
  exact ⟨r, r, m, hp, EvalExpr.Etempvar _ _ _ hx,
    by rw [hf]; exact semCast_ptr_ptr m r _ _ _ _ (hr hp hpost),
    by rw [he]; exact freeList_emptyEnv _ _, hpost, fun _ hdj hag => ⟨hdj, hag⟩⟩

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (bi : Block) (oi : Integers.Ptrofs)
  (s : Val) (v : Integers.Int) (contents : List Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)

theorem if_triple (k : Nat) :
    Sep.Triple ge fe f_insert (LInv p bi oi s v contents k) ifStmt
      { normal := LMid p bi oi s v contents k, brk := Done p bi oi s v contents,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  unfold LInv
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun pre => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun c2 => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun prev => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun idx => ?_)
  cases hg : guardB v c2 with
  | false =>
    refine Sep.triple_if_false ge fe f_insert _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨-, -, -, -, -, hgd, -⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ _ _ hgd, boolVal_ofBool_int m false⟩
    · refine Sep.triple_conseq ge fe f_insert (Sep.triple_break ge fe f_insert _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨hc, -, hpre, he, ht, -, hH⟩ := h
      exact ⟨pre, c2, prev, idx, hc, hpre, hg, he, ht, hH⟩
  | true =>
    refine Sep.triple_if_true ge fe f_insert _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨-, -, -, -, -, hgd, -⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ _ _ hgd, boolVal_ofBool_int m true⟩
    · refine Sep.triple_fallthrough ge fe f_insert _ _ _ _
        (Sep.triple_skip ge fe f_insert _) (fun e le hp h => ?_)
      obtain ⟨hc, hk, hpre, he, ht, -, hH⟩ := h
      cases c2 with
      | nil => exact absurd hg (by simp [guardB])
      | cons a c =>
        obtain ⟨b, o, u, rfl, -, hH'⟩ := listrep_cons_front hH
        exact ⟨pre, a, c, prev, b, o, u, hc, by simpa using hk, hpre, hg, he, ht, hH'⟩

include hcenv hpw in
theorem body_triple (k : Nat) :
    Sep.Triple ge fe f_insert (LMid p bi oi s v contents k) bodyStmt
      (.only (fun e le hp => ∃ k', k' < k ∧ LInv p bi oi s v contents k' e le hp)) := by
  unfold LMid
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun pre => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun a => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun c2 => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun prev => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun b => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun o => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun u => ?_)
  refine Sep.triple_pre ge fe f_insert (P := fun e le hp =>
      ∃ _ : (contents = pre ++ a :: c2 ∧ c2.length + 1 = k
        ∧ (∀ x ∈ pre, Integers.Int.lt x v = true) ∧ Integers.Int.lt a v = true),
      e = emptyEnv ∧ Temps bi oi s v prev (.Vptr b o) le
      ∧ (nodeAt p b o a u ∗ listrepL p c2 u ∗ nodeAt p bi oi v Val.Vnullptr
          ∗ PreSeg p pre s prev (.Vptr b o)) hp)
    (fun e le hp ⟨hc, hk, hpre, ha, he, ht, hH⟩ => ⟨⟨hc, hk, hpre, ha⟩, he, ht, hH⟩) ?_
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun ⟨hc, hk, hpre, ha⟩ => ?_)
  let N : HProp := nodeAt p bi oi v Val.Vnullptr
  -- `previous = index;`
  refine Sep.triple_seq_only ge fe f_insert (Q := fun e le hp =>
      e = emptyEnv ∧ Temps bi oi s v (.Vptr b o) (.Vptr b o) le
      ∧ (nodeAt p b o a u ∗ listrepL p c2 u ∗ N ∗ PreSeg p pre s prev (.Vptr b o)) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, ⟨h1, h2, h3, h4, h5⟩, hH⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ _ _ h5, he, ⟨(PTree.gso _ _ _ _ (by decide)).trans h1,
      (PTree.gso _ _ _ _ (by decide)).trans h2, (PTree.gso _ _ _ _ (by decide)).trans h3,
      PTree.gss _ _ _, (PTree.gso _ _ _ _ (by decide)).trans h5⟩, hH⟩
  -- `index = index->tail;`
  refine Sep.triple_seq_only ge fe f_insert (Q := fun e le hp =>
      (e = emptyEnv ∧ Temps bi oi s v (.Vptr b o) u le)
      ∧ (listrepL p c2 u ∗ N ∗ PreSeg p (pre ++ [a]) s (.Vptr b o) u) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, ⟨h1, h2, h3, h4, h5⟩, hH⟩ := hP
    have hu : IsLink u := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hl, _⟩ := hH
      exact isLink_of_listrep hl
    exact ⟨_, eval_tail layout hcenv (readable_of_writable hpw) h5 hu hH hag, ⟨he,
      ⟨(PTree.gso _ _ _ _ (by decide)).trans h1, (PTree.gso _ _ _ _ (by decide)).trans h2,
        (PTree.gso _ _ _ _ (by decide)).trans h3, (PTree.gso _ _ _ _ (by decide)).trans h4,
        PTree.gss _ _ _⟩⟩, heap_step p hH⟩
  -- `if (index) sortedvalue = index->head;`
  refine Sep.triple_seq_only ge fe f_insert
    (sv_triple ge fe p hcenv hpw (fun e le => e = emptyEnv ∧ Temps bi oi s v (.Vptr b o) u le)
      _ c2 u (fun _ _ h => h.2.2.2.2.2) (fun _ _ w h => ⟨h.1, temps_set _ w (by simp) h.2⟩))
    ?_
  -- `guard = ...;`
  refine Sep.triple_fallthrough ge fe f_insert _ _ _ _
    (cmp_triple ge fe p v _t'2 (fun e le => e = emptyEnv ∧ Temps bi oi s v (.Vptr b o) u le)
      _ c2 u (fun _ _ h => h.2.2.2.2.2) (fun _ _ h => h.2.2.2.1)
      (fun _ _ w h => ⟨h.1, temps_set _ w (by simp) h.2⟩)
      (fun _ _ w h => ⟨h.1, temps_set _ w (by simp) h.2⟩)) (fun e le hp h => ?_)
  obtain ⟨⟨he, ht⟩, hgd, hH⟩ := h
  exact ⟨c2.length, by omega, pre ++ [a], c2, .Vptr b o, u, by simpa using hc, rfl,
    fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hpre x hx
      · simp at hx; subst hx; exact ha,
    he, ht, hgd, hH⟩

include hcenv hpw in
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_insert (LInv p bi oi s v contents k) loopStmt
      (LoopR p bi oi s v contents) := by
  refine Sep.triple_loop ge fe f_insert (LoopR p bi oi s v contents) (LInv p bi oi s v contents)
    (fun k e le hp => ∃ k', k' < k ∧ LInv p bi oi s v contents k' e le hp) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_insert _ (LMid p bi oi s v contents k) _ _ _
      (Sep.triple_conseq ge fe f_insert (if_triple ge fe p bi oi s v contents k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_insert _ _ _ _
        (body_triple ge fe p bi oi s v contents hcenv hpw k) (fun _ _ _ x => x))
  · exact Sep.triple_fallthrough ge fe f_insert _ _ _ _
      (Sep.triple_skip ge fe f_insert _) (fun _ _ _ x => x)

include hcenv hpw in
/-- `insert_node->tail = index; if (previous) {...} return insert_node;` -/
theorem fin_triple :
    Sep.Triple ge fe f_insert (Done p bi oi s v contents) finStmt
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := fun r hp => listrepL p (insert v contents) r hp } := by
  unfold Done
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun pre => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun c2 => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun prev => ?_)
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun idx => ?_)
  let Rl : Env → TempEnv → Prop := fun e le => e = emptyEnv ∧ Temps bi oi s v prev idx le
  refine Sep.triple_pre ge fe f_insert (P := fun e le hp =>
      ∃ _ : (contents = pre ++ c2 ∧ (∀ x ∈ pre, Integers.Int.lt x v = true)
        ∧ guardB v c2 = false ∧ IsLink idx),
      Rl e le ∧ (nodeAt p bi oi v Val.Vnullptr
        ∗ (listrepL p c2 idx ∗ PreSeg p pre s prev idx)) hp)
    (fun e le hp ⟨hc, hpre, hg, he, ht, hH⟩ => ⟨⟨hc, hpre, hg, by
      obtain ⟨_, _, _, _, hl, _⟩ := hH
      exact isLink_of_listrep hl⟩, ⟨he, ht⟩, by
        unfold Heap3 at hH; rwa [sep_left_comm_eq] at hH⟩) ?_
  refine Sep.triple_exists ge fe f_insert _ _ _ (fun ⟨hc, hpre, hg, hidx⟩ => ?_)
  -- `insert_node->tail = index;`
  refine Sep.triple_seq_only ge fe f_insert
    (triple_store_tail layout hcenv fe f_insert Rl _ _insert_node _index p bi oi v Val.Vnullptr
      idx hpw (fun _ _ h => h.2.1) (fun _ _ h => h.2.2.2.2.2) hidx) ?_
  have hins : insert v contents = pre ++ v :: c2 := by rw [hc]; exact insert_split v pre c2 hpre hg
  -- the two cases of `previous`
  refine Sep.triple_pre ge fe f_insert (P := fun e le hp =>
      (∃ _ : pre = [] ∧ prev = Val.Vnullptr ∧ s = idx,
        Rl e le ∧ (nodeAt p bi oi v idx ∗ listrepL p c2 idx) hp)
      ∨ (∃ pre' a bp op, ∃ _ : pre = pre' ++ [a] ∧ prev = .Vptr bp op,
        Rl e le ∧ (nodeAt p bp op a idx ∗ (nodeAt p bi oi v idx ∗ listrepL p c2 idx
          ∗ lseg (listNode p) pre' s (.Vptr bp op))) hp))
    (fun e le hp ⟨hR, hH⟩ => by
      obtain ⟨h1, h23, hd, rfl, hn, h2, h3, hd', rfl, hl, hS⟩ := hH
      rcases hS with ⟨e1, e2, e3, rfl⟩ | ⟨pre', a, bp, op, e1, rfl, hS⟩
      · refine Or.inl ⟨⟨e1, e2, e3⟩, hR, ?_⟩
        rw [Heap.union_emp] at hd ⊢
        exact ⟨h1, h2, hd, rfl, hn, hl⟩
      · refine Or.inr ⟨pre', a, bp, op, ⟨e1, rfl⟩, hR, ?_⟩
        have hh : (nodeAt p bi oi v idx ∗ (listrepL p c2 idx
            ∗ (lseg (listNode p) pre' s (.Vptr bp op) ∗ nodeAt p bp op a idx)))
            (Heap.union h1 (Heap.union h2 h3)) := ⟨h1, _, hd, rfl, hn, h2, h3, hd', rfl, hl, hS⟩
        have e : (nodeAt p bi oi v idx ∗ (listrepL p c2 idx
            ∗ (lseg (listNode p) pre' s (.Vptr bp op) ∗ nodeAt p bp op a idx)))
            = (nodeAt p bp op a idx ∗ (nodeAt p bi oi v idx ∗ listrepL p c2 idx
              ∗ lseg (listNode p) pre' s (.Vptr bp op))) := by
          rw [sep_comm_eq (lseg _ _ _ _), sep_left_comm_eq (listrepL p c2 idx),
            sep_left_comm_eq (nodeAt p bi oi v idx)]
        rwa [e] at hh) ?_
  refine Sep.triple_or ge fe f_insert ?_ ?_
  · -- `previous` is `NULL`: `return insert_node;`
    refine Sep.triple_exists ge fe f_insert _ _ _ (fun ⟨e1, e2, e3⟩ => ?_)
    subst e1 e2 e3
    refine Sep.triple_seq ge fe f_insert _ _ _ _ _
      (Sep.triple_if_false ge fe f_insert _ _ _ _ _ (fun e le hp m hP _ => ?_)
        (Sep.triple_conseq ge fe f_insert (Sep.triple_skip ge fe f_insert _)
          (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => False.elim x)
          (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)))
      (ret_triple ge fe f_insert rfl _ _ _ _ (fun _ hh => isLink_of_listrep hh) (fun e le hp h => ⟨h.1.1, h.1.2.1, ?_⟩))
    · exact ⟨_, EvalExpr.Etempvar _ _ _ hP.1.2.2.2.2.1, boolVal_null m _ _⟩
    · rw [hins]
      exact listrep_cons _ h.2
  · -- `previous` is the last node `a` of `pre`
    refine Sep.triple_exists ge fe f_insert _ _ _ (fun pre' => ?_)
    refine Sep.triple_exists ge fe f_insert _ _ _ (fun a => ?_)
    refine Sep.triple_exists ge fe f_insert _ _ _ (fun bp => ?_)
    refine Sep.triple_exists ge fe f_insert _ _ _ (fun op => ?_)
    refine Sep.triple_exists ge fe f_insert _ _ _ (fun ⟨e1, e2⟩ => ?_)
    subst e1 e2
    refine Sep.triple_seq ge fe f_insert _ Sep.Assn.no _ _ _ ?_
      (Sep.triple_vacuous ge fe f_insert _ _)
    refine Sep.triple_if_true ge fe f_insert _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · exact ⟨_, EvalExpr.Etempvar _ _ _ hP.1.2.2.2.2.1,
        boolVal_ptr_valid m bp op _ _ (node_valid hP.2 hag)⟩
    refine Sep.triple_seq_only ge fe f_insert
      (triple_store_tail layout hcenv fe f_insert Rl _ _previous _insert_node p bp op a idx
        (.Vptr bi oi) hpw (fun _ _ h => h.2.2.2.2.1) (fun _ _ h => h.2.1) (Or.inr ⟨bi, oi, rfl⟩))
      ?_
    refine ret_triple ge fe f_insert rfl _ _ _ _ (fun _ hh => isLink_of_listrep hh)
      (fun e le hp h => ⟨h.1.1, h.1.2.2.1, ?_⟩)
    obtain ⟨-, hH⟩ := h
    have e : (nodeAt p bp op a (.Vptr bi oi) ∗ (nodeAt p bi oi v idx ∗ listrepL p c2 idx
        ∗ lseg (listNode p) pre' s (.Vptr bp op)))
        = (lseg (listNode p) pre' s (.Vptr bp op) ∗ (nodeAt p bp op a (.Vptr bi oi)
          ∗ (nodeAt p bi oi v idx ∗ listrepL p c2 idx))) := by
      rw [← sep_assoc_eq (nodeAt p bi oi v idx), sep_comm_eq _ (lseg _ _ _ _),
        sep_left_comm_eq]
    rw [e] at hH
    have h1 := sep_mono (entails_refl _) (sep_mono (entails_refl _)
      (fun _ hh => listrep_cons _ hh)) hp hH
    have h2 := sep_mono (entails_refl _) (fun _ hh => listrep_cons _ hh) hp h1
    have h3 := lseg_listrep _ h2
    rw [hins]
    simpa using h3
end

end Insert

/-! ## As a function specification -/

open Insert in
/-- `insert_spec`: the node `insert_ptr = (bi, oi)` holds `insert_val` and a
    `NULL` link; the list at `sorted_ptr = s` holds `contents`. -/
def insertSpec (p : Permission) (contents : List Integers.Int) (v : Integers.Int)
    (s : Val) (bi : Block) (oi : Integers.Ptrofs) : Sep.FunSpec where
  tyargs := [tlistp, tlistp]
  tyres := tlistp
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr bi oi, s]
    ∧ (listrepL p contents s ∗ nodeAt p bi oi v Val.Vnullptr) hp
  post := fun r hp => listrepL p (insert v contents) r hp
  measure := fun _ => 0

open Insert in
/-- **`insert` satisfies `insert_spec`** (VST's `body_insert`). -/
theorem insert_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (contents : List Integers.Int) (v : Integers.Int) (s : Val) (bi : Block)
    (oi : Integers.Ptrofs) (hpw : permOrder p .Writable = true) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_insert) (insertSpec p contents v s bi oi)
      [.Vptr bi oi, s] := by
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_insert _ _
    (fun e le hp => e = emptyEnv ∧ le.get _insert_node = some (.Vptr bi oi)
      ∧ le.get _sorted = some s
      ∧ (listrepL p contents s ∗ nodeAt p bi oi v Val.Vnullptr) hp)
    (fun m => ?_) ?_
  · exact ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _),
        PTree.gss _ _ _, hpre.2⟩⟩
  rw [body_eq]
  let fe := FunctionEntry2 ge
  let N : HProp := nodeAt p bi oi v Val.Vnullptr
  -- `previous = NULL;`
  refine Sep.triple_seq_only ge fe f_insert (Q := fun e le hp => e = emptyEnv
      ∧ le.get _insert_node = some (.Vptr bi oi) ∧ le.get _sorted = some s
      ∧ le.get _previous = some Val.Vnullptr ∧ (listrepL p contents s ∗ N) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, h1, h2, hH⟩ := hP
    exact ⟨_, eval_null_cast, he, (PTree.gso _ _ _ _ (by decide)).trans h1,
      (PTree.gso _ _ _ _ (by decide)).trans h2, PTree.gss _ _ _, hH⟩
  -- `insert_value = insert_node->head;`
  refine Sep.triple_seq_only ge fe f_insert (Q := fun e le hp => e = emptyEnv
      ∧ le.get _insert_node = some (.Vptr bi oi) ∧ le.get _sorted = some s
      ∧ le.get _previous = some Val.Vnullptr ∧ le.get _insert_value = some (.Vint v)
      ∧ (listrepL p contents s ∗ N) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, h1, h2, h3, hH⟩ := hP
    have hH' : (N ∗ listrepL p contents s) hp := by rwa [sep_comm_eq] at hH
    exact ⟨_, eval_head layout hcenv rfl (readable_of_writable hpw) h1 hH' hag, he,
      (PTree.gso _ _ _ _ (by decide)).trans h1, (PTree.gso _ _ _ _ (by decide)).trans h2,
      (PTree.gso _ _ _ _ (by decide)).trans h3, PTree.gss _ _ _, hH⟩
  -- `index = sorted;`
  refine Sep.triple_seq_only ge fe f_insert (Q := fun e le hp =>
      (e = emptyEnv ∧ Temps bi oi s v Val.Vnullptr s le)
      ∧ (listrepL p contents s ∗ N ∗ PreSeg p [] s Val.Vnullptr s) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_insert _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, h1, h2, h3, h4, hH⟩ := hP
    refine ⟨_, EvalExpr.Etempvar _ _ _ h2, ⟨he, (PTree.gso _ _ _ _ (by decide)).trans h1,
      (PTree.gso _ _ _ _ (by decide)).trans h2, (PTree.gso _ _ _ _ (by decide)).trans h4,
      (PTree.gso _ _ _ _ (by decide)).trans h3, PTree.gss _ _ _⟩, ?_⟩
    obtain ⟨h1, h2, hd, rfl, hl, hn⟩ := hH
    refine ⟨h1, h2, hd, rfl, hl, h2, Heap.emp, Heap.disjoint_emp_right _,
      (Heap.union_emp _).symm, hn, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  -- `if (index) sortedvalue = index->head;`
  refine Sep.triple_seq_only ge fe f_insert
    (sv_triple ge fe p hcenv hpw (fun e le => e = emptyEnv ∧ Temps bi oi s v Val.Vnullptr s le)
      _ contents s (fun _ _ h => h.2.2.2.2.2) (fun _ _ w h => ⟨h.1, temps_set _ w (by simp) h.2⟩))
    ?_
  -- `guard = ...;`
  refine Sep.triple_seq_only ge fe f_insert
    (cmp_triple ge fe p v _t'1 (fun e le => e = emptyEnv ∧ Temps bi oi s v Val.Vnullptr s le)
      _ contents s (fun _ _ h => h.2.2.2.2.2) (fun _ _ h => h.2.2.2.1)
      (fun _ _ w h => ⟨h.1, temps_set _ w (by simp) h.2⟩)
      (fun _ _ w h => ⟨h.1, temps_set _ w (by simp) h.2⟩)) ?_
  refine Sep.triple_pre ge fe f_insert (P := LInv p bi oi s v contents contents.length)
    (fun e le hp ⟨⟨he, ht⟩, hgd, hH⟩ => ⟨[], contents, Val.Vnullptr, s, rfl, rfl,
      (fun _ h => nomatch h), he, ht, hgd, hH⟩) ?_
  -- the loop, then the end
  exact Sep.triple_seq ge fe f_insert _ (Done p bi oi s v contents) _ _ _
    (Sep.triple_conseq ge fe f_insert
      (loop_triple ge fe p bi oi s v contents hcenv hpw contents.length)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x.elim))
    (fin_triple ge fe p bi oi s v contents hcenv hpw)

/-! ## `insertionsort`

      struct list *insertionsort (struct list *p) {
        struct list *index, *sorted, *next;
        sorted = NULL;
        index = p;
        while(index){
          next = index -> tail;
          index -> tail = NULL;
          sorted = insert(index, sorted);
          index = next;
        }
        return sorted;
      }

  The loop inserts the elements in list order, so what it computes is
  `isortL contents`, a left fold of `insert`; VST's `insertion_sort` is the
  right fold.  The two agree (both are the sorted permutation of `contents`):
  `isortL_eq_insertionSort` in `verif_insertionsort_sorted`. -/

/-- The list `insertionsort` builds: the elements inserted from left to right. -/
def isortL (xs : List Integers.Int) : List Integers.Int :=
  xs.foldl (fun acc x => insert x acc) []

theorem isortL_snoc (xs : List Integers.Int) (a : Integers.Int) :
    isortL (xs ++ [a]) = insert a (isortL xs) := by
  simp [isortL, List.foldl_append]

namespace ISort

open Insert (nullE tailOf)

def insTy : Ty := .Tfunction [tlistp, tlistp] tlistp cc_default

def callStmt : Stmt :=
  .Ssequence
    (.Scall (some _t'1) (.Evar _insert insTy) [.Etempvar _index tlistp, .Etempvar _sorted tlistp])
    (.Sset _sorted (.Etempvar _t'1 tlistp))

def bodyStmt : Stmt :=
  .Ssequence (.Sset _next (tailOf _index))
    (.Ssequence (.Sassign (tailOf _index) nullE)
      (.Ssequence callStmt (.Sset _index (.Etempvar _next tlistp))))

def ifStmt : Stmt := .Sifthenelse (.Etempvar _index tlistp) .Sskip .Sbreak

def loopStmt : Stmt := swhile (.Etempvar _index tlistp) bodyStmt

def fullBody : Stmt :=
  .Ssequence (.Sset _sorted nullE)
    (.Ssequence (.Sset _index (.Etempvar _p tlistp))
      (.Ssequence loopStmt (.Sreturn (some (.Etempvar _sorted tlistp)))))

theorem body_eq : f_insertionsort.fn_body = fullBody := rfl

section
variable (p : Permission) (contents : List Integers.Int)

/-- The loop invariant, `k` nodes left: the elements `sl` already inserted
    form the list `isortL sl` at `sorted`, the rest `ul` is at `index`. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ sl ul q i, contents = sl ++ ul ∧ ul.length = k ∧ e = emptyEnv
    ∧ le.get _sorted = some q ∧ le.get _index = some i
    ∧ (listrepL p ul i ∗ listrepL p (isortL sl) q) hp

/-- After the test: `index` is the node `a`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ sl a ul q b o u, contents = sl ++ a :: ul ∧ ul.length + 1 = k ∧ e = emptyEnv
    ∧ le.get _sorted = some q ∧ le.get _index = some (.Vptr b o)
    ∧ (nodeAt p b o a u ∗ (listrepL p ul u ∗ listrepL p (isortL sl) q)) hp

def Done : Sep.Assn := fun e le hp =>
  ∃ q, e = emptyEnv ∧ le.get _sorted = some q ∧ listrepL p (isortL contents) q hp

def LoopR : Sep.ExitConds :=
  { normal := Done p contents, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := fun _ _ => False }

end

section
variable (ge : CGenv) (p : Permission) (contents : List Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)
  (bIns : Block) (hsym : Genv.findSymbol ge.genv_genv _insert = some bIns)
  (hfind : Genv.findFunct ge.genv_genv (.Vptr bIns Integers.Ptrofs.zero)
    = some (.Internal f_insert))

theorem if_triple (fe : EntryRel) (k : Nat) :
    Sep.Triple ge fe f_insertionsort (LInv p contents k) ifStmt
      { normal := LMid p contents k, brk := Done p contents,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  unfold LInv
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun sl => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun ul => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun q => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun i => ?_)
  cases ul with
  | nil =>
    refine Sep.triple_if_false ge fe f_insertionsort _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨-, -, -, -, hi, h1, h2, hd, rfl, hl, _⟩ := hP
      obtain ⟨rfl, -⟩ := hl
      exact ⟨_, EvalExpr.Etempvar _ _ _ hi, boolVal_null m _ _⟩
    · refine Sep.triple_conseq ge fe f_insertionsort (Sep.triple_break ge fe f_insertionsort _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨hc, -, he, hq, -, h1, h2, hd, rfl, ⟨-, rfl⟩, hl⟩ := h
      rw [List.append_nil] at hc
      subst hc
      exact ⟨q, he, hq, by rw [Heap.emp_union]; exact hl⟩
  | cons a ul =>
    refine Sep.triple_if_true ge fe f_insertionsort _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · obtain ⟨-, -, -, -, hi, hH⟩ := hP
      obtain ⟨b, o, u, rfl, -, hH'⟩ := listrep_cons_front hH
      exact ⟨_, EvalExpr.Etempvar _ _ _ hi, boolVal_ptr_valid m b o _ _ (node_valid hH' hag)⟩
    · refine Sep.triple_fallthrough ge fe f_insertionsort _ _ _ _
        (Sep.triple_skip ge fe f_insertionsort _) (fun e le hp h => ?_)
      obtain ⟨hc, hk, he, hq, hi, hH⟩ := h
      obtain ⟨b, o, u, rfl, -, hH'⟩ := listrep_cons_front hH
      exact ⟨sl, a, ul, q, b, o, u, hc, by simpa using hk, he, hq, hi, hH'⟩

include hcenv hpw hsym hfind in
theorem body_triple (k : Nat) :
    Sep.Triple ge (FunctionEntry2 ge) f_insertionsort (LMid p contents k) bodyStmt
      (.only (fun e le hp => ∃ k', k' < k ∧ LInv p contents k' e le hp)) := by
  let fe := FunctionEntry2 ge
  unfold LMid
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun sl => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun a => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun ul => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun q => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun b => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun o => ?_)
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun u => ?_)
  refine Sep.triple_pre ge fe f_insertionsort (P := fun e le hp =>
      ∃ _ : contents = sl ++ a :: ul ∧ ul.length + 1 = k, e = emptyEnv
      ∧ le.get _sorted = some q ∧ le.get _index = some (.Vptr b o)
      ∧ (nodeAt p b o a u ∗ (listrepL p ul u ∗ listrepL p (isortL sl) q)) hp)
    (fun e le hp ⟨hc, hk, he, hq, hi, hH⟩ => ⟨⟨hc, hk⟩, he, hq, hi, hH⟩) ?_
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun ⟨hc, hk⟩ => ?_)
  let Rl : Env → TempEnv → Prop := fun e le => e = emptyEnv
    ∧ le.get _sorted = some q ∧ le.get _index = some (.Vptr b o) ∧ le.get _next = some u
  -- `next = index->tail;`
  refine Sep.triple_seq_only ge fe f_insertionsort (Q := fun e le hp => Rl e le
      ∧ (nodeAt p b o a u ∗ (listrepL p ul u ∗ listrepL p (isortL sl) q)) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_insertionsort _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, hq, hi, hH⟩ := hP
    have hu : IsLink u := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hl, _⟩ := hH
      exact isLink_of_listrep hl
    exact ⟨_, eval_tail layout hcenv (readable_of_writable hpw) hi hu hH hag, ⟨he,
      (PTree.gso _ _ _ _ (by decide)).trans hq, (PTree.gso _ _ _ _ (by decide)).trans hi,
      PTree.gss _ _ _⟩, hH⟩
  -- `index->tail = NULL;`
  refine Sep.triple_seq_only ge fe f_insertionsort
    (triple_store_tail_null layout hcenv fe f_insertionsort Rl _ _index p b o a u hpw
      (fun _ _ h => h.2.2.1)) ?_
  -- `sorted = insert(index, sorted);`
  refine Sep.triple_seq_only ge fe f_insertionsort (Q := fun e le hp => e = emptyEnv
      ∧ le.get _next = some u ∧ ∃ r, le.get _sorted = some r
      ∧ (listrepL p ul u ∗ listrepL p (insert a (isortL sl)) r) hp) ?_ ?_
  · refine Sep.triple_seq_only ge fe f_insertionsort (Q := fun e le hp => e = emptyEnv
        ∧ le.get _next = some u ∧ ∃ r, le.get _t'1 = some r
        ∧ (listrepL p (insert a (isortL sl)) r ∗ listrepL p ul u) hp) ?_ ?_
    · refine Sep.triple_call_at ge fe f_insertionsort (insertSpec p (isortL sl) a q b o)
        (some _t'1) (.Evar _insert insTy) [.Etempvar _index tlistp, .Etempvar _sorted tlistp]
        _ _ bIns _ hfind rfl rfl (fun e le hp m hP _ => ?_)
      obtain ⟨⟨he, hq, hi, hn⟩, hH⟩ := hP
      subst he
      have e : (nodeAt p b o a Val.Vnullptr ∗ (listrepL p ul u ∗ listrepL p (isortL sl) q))
          = ((listrepL p (isortL sl) q ∗ nodeAt p b o a Val.Vnullptr) ∗ listrepL p ul u) := by
        rw [sep_assoc_eq, sep_comm_eq, sep_assoc_eq, sep_comm_eq (listrepL p ul u), sep_assoc_eq]
      rw [e] at hH
      obtain ⟨h1, h2, hd, rfl, h1p, h2p⟩ := hH
      have hql : IsLink q := by
        obtain ⟨_, _, _, _, hl, _⟩ := h1p
        exact isLink_of_listrep hl
      refine ⟨[.Vptr b o, q], h1, h2, hd, rfl, eval_callee_global (PTree.gempty _) hsym rfl,
        EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hi)
          (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨b, o, rfl⟩))
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hq)
            (semCast_ptr_ptr m _ _ _ _ _ hql) EvalExprlist.nil),
        ⟨rfl, h1p⟩, insert_satisfies ge hcenv p (isortL sl) a q b o hpw,
        fun r h1' hpost hd' => ⟨rfl, (PTree.gso _ _ _ _ (by decide)).trans hn, r,
          PTree.gss _ _ _, h1', h2, hd', rfl, hpost, h2p⟩⟩
    -- `sorted = t'1;`
    · refine Sep.triple_set ge fe f_insertionsort _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨he, hn, r, hr, hH⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ _ _ hr, he, (PTree.gso _ _ _ _ (by decide)).trans hn, r,
        PTree.gss _ _ _, by rwa [sep_comm_eq] at hH⟩
  -- `index = next;`
  · refine Sep.triple_set ge fe f_insertionsort _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hn, r, hr, hH⟩ := hP
    refine ⟨_, EvalExpr.Etempvar _ _ _ hn, ul.length, by omega, sl ++ [a], ul, r, u,
      by simpa using hc, rfl, he, (PTree.gso _ _ _ _ (by decide)).trans hr, PTree.gss _ _ _,
      by rwa [isortL_snoc]⟩

include hcenv hpw hsym hfind in
theorem loop_triple (k : Nat) :
    Sep.Triple ge (FunctionEntry2 ge) f_insertionsort (LInv p contents k) loopStmt
      (LoopR p contents) := by
  let fe := FunctionEntry2 ge
  refine Sep.triple_loop ge fe f_insertionsort (LoopR p contents) (LInv p contents)
    (fun k e le hp => ∃ k', k' < k ∧ LInv p contents k' e le hp) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_insertionsort _ (LMid p contents k) _ _ _
      (Sep.triple_conseq ge fe f_insertionsort (if_triple ge p contents fe k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_insertionsort _ _ _ _
        (body_triple ge p contents hcenv hpw bIns hsym hfind k) (fun _ _ _ x => x))
  · exact Sep.triple_fallthrough ge fe f_insertionsort _ _ _ _
      (Sep.triple_skip ge fe f_insertionsort _) (fun _ _ _ x => x)

end

end ISort

/-- `insertionsort_spec`, with the list the loop builds (`isortL`). -/
def insertionsortSpecL (p : Permission) (contents : List Integers.Int) (x : Val) :
    Sep.FunSpec where
  tyargs := [tlistp]
  tyres := tlistp
  cc := cc_default
  pre := fun vargs hp => vargs = [x] ∧ listrepL p contents x hp
  post := fun r hp => listrepL p (isortL contents) r hp
  measure := fun _ => 0

open ISort in
/-- **`insertionsort` returns the list `isortL contents`**, when the symbol
    `insert` names `f_insert` (whose specification is `insert_satisfies`). -/
theorem insertionsort_satisfiesL (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (hpw : permOrder p .Writable = true) (contents : List Integers.Int)
    (x : Val) (bIns : Block) (hsym : Genv.findSymbol ge.genv_genv _insert = some bIns)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr bIns Integers.Ptrofs.zero)
      = some (.Internal f_insert)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_insertionsort)
      (insertionsortSpecL p contents x) [x] := by
  let fe := FunctionEntry2 ge
  refine Sep.satisfies_internal_noVars ge fe f_insertionsort _ _
    (fun e le hp => e = emptyEnv ∧ le.get _p = some x ∧ listrepL p contents x hp)
    (fun m => ?_) ?_
  · exact ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, PTree.gss _ _ _, hpre.2⟩⟩
  rw [body_eq]
  -- `sorted = NULL;`
  refine Sep.triple_seq_only ge fe f_insertionsort (Q := fun e le hp => e = emptyEnv
      ∧ le.get _p = some x ∧ le.get _sorted = some Val.Vnullptr
      ∧ listrepL p contents x hp) ?_ ?_
  · refine Sep.triple_set ge fe f_insertionsort _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hx, hH⟩ := hP
    exact ⟨_, eval_null_cast, he, (PTree.gso _ _ _ _ (by decide)).trans hx, PTree.gss _ _ _, hH⟩
  -- `index = p;`
  refine Sep.triple_seq_only ge fe f_insertionsort (Q := LInv p contents contents.length) ?_ ?_
  · refine Sep.triple_set ge fe f_insertionsort _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hx, hs, hH⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ _ _ hx, [], contents, Val.Vnullptr, x, rfl, rfl, he,
      (PTree.gso _ _ _ _ (by decide)).trans hs, PTree.gss _ _ _,
      hp, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm, hH, rfl, rfl⟩
  -- the loop, then `return sorted;`
  refine Sep.triple_seq ge fe f_insertionsort _ (Done p contents) _ _ _
    (Sep.triple_conseq ge fe f_insertionsort
      (loop_triple ge p contents hcenv hpw bIns hsym hfind contents.length)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x.elim)) ?_
  refine Sep.triple_exists ge fe f_insertionsort _ _ _ (fun q => ?_)
  exact Insert.ret_triple ge fe f_insertionsort rfl _ _ _ q (fun _ hh => isLink_of_listrep hh)
    (fun _ _ _ h => h)

end VST.Verif.InsertionSort
