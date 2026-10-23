/-
  Port of VST's `progs/verif_merge.v`: `merge` of `vst/progs/merge.c` merges
  two linked lists in place.

      struct list {int head; struct list *tail;};

      struct list *merge(struct list *a, struct list *b){
        struct list* ret;
        struct list* temp;
        struct list** x;
        int va, vb, cond;
        x = &ret;
        cond = a != NULL && b != NULL;
        while (cond) {
          va = a->head;
          vb = b->head;
          if (va <= vb) { *x = a; x = &(a->tail); a = a->tail; }
          else          { *x = b; x = &(b->tail); b = b->tail; }
          cond = a != NULL && b != NULL;
        }
        if (a != NULL) { *x = a; } else { *x = b; }
        temp = ret;
        return temp;
      }

  VST's specification:

      Fixpoint merge l1 l2 := (* the merge of two lists, by Int.cmp Cle *)

      merge_spec: WITH sh, a, b, a_, b_
        PRE [tlist, tlist] PROP (writable_share sh) PARAMS (a_; b_)
          SEP (lseg LS sh (map Vint a) a_ nullval; lseg LS sh (map Vint b) b_ nullval)
        POST [tlist] EX pt, PROP () RETURN (pt)
          SEP (lseg LS sh (map Vint (merge a b)) pt nullval).

  `ret` is an addressable local (`x = &ret`), so the function is entered
  through `Sep.satisfies_oneLocal` and left through
  `Sep.triple_return_oneLocal` (`CCLib.logic.OneLocal`).

  The loop invariant is VST's `merge_invariant`: the merged prefix `merged`
  hangs from `ret`; `x` points to the cell to be written next, `ret` itself
  while `merged` is empty, else the `tail` field of the last merged node, whose
  value is irrelevant (VST's `Vundef`).  That is `Out` below; writing the
  next node into the cell `*x` gives `Filled` (the merged prefix as a segment
  from `ret` to that node).
-/
import VST.progs.merge
import CCLib
open CC CC.Sep CC.HProp
open Merge

namespace VST.Verif.Merge

/-! ## The functional model -/

/-- VST's `merge`. -/
def merge : List Integers.Int → List Integers.Int → List Integers.Int
  | [], l2 => l2
  | h1 :: t1, [] => h1 :: t1
  | h1 :: t1, h2 :: t2 =>
    if Integers.Int.cmp .Cle h1 h2 then h1 :: merge t1 (h2 :: t2) else h2 :: merge (h1 :: t1) t2
termination_by l1 l2 => l1.length + l2.length

theorem merge_nil_r (l : List Integers.Int) : merge l [] = l := by
  cases l <;> simp [merge]

theorem merge_le {h1 h2 : Integers.Int} (t1 t2 : List Integers.Int)
    (h : Integers.Int.cmp .Cle h1 h2 = true) :
    merge (h1 :: t1) (h2 :: t2) = h1 :: merge t1 (h2 :: t2) := by
  rw [merge]; simp [h]

theorem merge_gt {h1 h2 : Integers.Int} (t1 t2 : List Integers.Int)
    (h : Integers.Int.cmp .Cle h1 h2 = false) :
    merge (h1 :: t1) (h2 :: t2) = h2 :: merge (h1 :: t1) t2 := by
  rw [merge]; simp [h]

/-! ## The layout of `struct list` -/

abbrev tlist : Ty := .Tstruct _list noattr
abbrev tlistp : Ty := tptr tlist
abbrev tlistpp : Ty := tptr tlistp

def coList : Composite :=
  match prog.prog_comp_env.get _list with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

/-- `struct list` as a list layout (`Sep.ListLayout`). -/
def layout : ListLayout :=
  ⟨prog.prog_comp_env, _list, _head, _tail, coList, rfl, by decide, by decide⟩

abbrev listrepL (p : Permission) (s : List Integers.Int) (x : Val) : HProp :=
  listrep (listNode p) s x

abbrev nodeAt (p : Permission) (b : Block) (o : Integers.Ptrofs) (a : Integers.Int) (u : Val) :
    HProp :=
  listNode p b (Integers.Ptrofs.unsigned o) a u

/-! ## The merged prefix -/

section
variable (p : Permission) (bret : Block)

/-- The merged prefix `merged`, with `x` pointing to the cell to write next:
    `ret` itself (with any content) while `merged` is empty; otherwise `ret`
    holds the first node, the nodes form a segment up to the last one, and
    `x` is the address of the last node's `tail` (with any content). -/
def Out (merged : List Integers.Int) (x : Val) : HProp := fun h =>
  (merged = [] ∧ x = .Vptr bret Integers.Ptrofs.zero ∧ ∃ w, mapsto .Mint64 .Freeable bret 0 w h)
  ∨ ∃ m l begin bc oc w, merged = m ++ [l]
      ∧ x = .Vptr bc (Integers.Ptrofs.add oc (Integers.Ptrofs.repr 8))
      ∧ (mapsto .Mint64 .Freeable bret 0 begin ∗ lseg (listNode p) m begin (.Vptr bc oc)
          ∗ nodeAt p bc oc l w) h

/-- The merged prefix after the next node `w` was written into the cell: a
    segment from the node in `ret` to `w`. -/
def Filled (merged : List Integers.Int) (w : Val) : HProp := fun h =>
  ∃ begin, (mapsto .Mint64 .Freeable bret 0 begin ∗ lseg (listNode p) merged begin w) h

/-- The written node `(b, o)` becomes the last merged node. -/
theorem filled_snoc {merged : List Integers.Int} {b : Block} {o : Integers.Ptrofs}
    {v : Integers.Int} {u : Val} {h : Heap}
    (hh : (Filled p bret merged (.Vptr b o) ∗ nodeAt p b o v u) h) :
    Out p bret (merged ++ [v]) (.Vptr b (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8))) h := by
  obtain ⟨h1, h2, hd, rfl, ⟨begin, hF⟩, hn⟩ := hh
  refine Or.inr ⟨merged, v, begin, b, o, u, rfl, rfl, ?_⟩
  rw [← sep_assoc_eq]
  exact ⟨h1, h2, hd, rfl, hF, hn⟩

/-- The end: the rest of the list is written into the cell. -/
theorem filled_listrep {merged rest : List Integers.Int} {w : Val} {h : Heap}
    (hh : (Filled p bret merged w ∗ listrepL p rest w) h) :
    ∃ begin, (mapsto .Mint64 .Freeable bret 0 begin ∗ listrepL p (merged ++ rest) begin) h := by
  obtain ⟨h1, h2, hd, rfl, ⟨begin, hF⟩, hl⟩ := hh
  have h3 : ((mapsto .Mint64 .Freeable bret 0 begin ∗ lseg (listNode p) merged begin w)
      ∗ listrepL p rest w) (Heap.union h1 h2) := ⟨h1, h2, hd, rfl, hF, hl⟩
  rw [sep_assoc_eq] at h3
  exact ⟨begin, sep_mono (entails_refl _) (fun _ hh => lseg_listrep _ hh) _ h3⟩

end

/-! ## The statements of the body -/

def nullE : Expr := .Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)
/-- `*x` -/
def derefX : Expr := .Ederef (.Etempvar _x tlistpp) tlistp
def headOf (y : Ident) : Expr := .Efield (.Ederef (.Etempvar y tlistp) tlist) _head tint
def tailOf (y : Ident) : Expr := .Efield (.Ederef (.Etempvar y tlistp) tlist) _tail tlistp

theorem sep_rot (M S N F : HProp) : ((M ∗ (S ∗ N)) ∗ F) = N ∗ (M ∗ (S ∗ F)) := by
  rw [sep_assoc_eq, sep_assoc_eq, sep_left_comm_eq S N, sep_left_comm_eq M N]

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (bret : Block)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)

include hpw in
/-- **`*x = y;`**: the link `w` in `y` is written into the cell `x` points to. -/
theorem out_store (Rl : Env → TempEnv → Prop) (F : HProp) (y : Ident)
    (merged : List Integers.Int) (x w : Val)
    (hx : ∀ e le, Rl e le → le.get _x = some x) (hy : ∀ e le, Rl e le → le.get y = some w)
    (hw : IsLink w) :
    Sep.Triple ge fe f_merge (fun e le hp => Rl e le ∧ (Out p bret merged x ∗ F) hp)
      (.Sassign derefX (.Etempvar y tlistp))
      (.only fun e le hp => Rl e le ∧ (Filled p bret merged w ∗ F) hp) := by
  refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
      (Rl e le ∧ merged = [] ∧ x = .Vptr bret Integers.Ptrofs.zero
        ∧ ∃ w0, (mapsto .Mint64 .Freeable bret 0 w0 ∗ F) hp)
      ∨ ∃ bc oc, Rl e le ∧ ∃ m l begin w0, merged = m ++ [l]
        ∧ x = .Vptr bc (Integers.Ptrofs.add oc (Integers.Ptrofs.repr 8))
        ∧ ((mapsto .Mint64 .Freeable bret 0 begin ∗ (lseg (listNode p) m begin (.Vptr bc oc)
          ∗ nodeAt p bc oc l w0)) ∗ F) hp)
    (fun e le hp ⟨hR, h1, h2, hd, he, hO, hF⟩ => by
      subst he
      rcases hO with ⟨e1, e2, w0, hm⟩ | ⟨m, l, begin, bc, oc, w0, e1, e2, hh⟩
      · exact Or.inl ⟨hR, e1, e2, w0, h1, h2, hd, rfl, hm, hF⟩
      · exact Or.inr ⟨bc, oc, hR, m, l, begin, w0, e1, e2, h1, h2, hd, rfl, hh, hF⟩) ?_
  refine Sep.triple_or ge fe f_merge ?_ ?_
  · refine Sep.triple_assign ge fe f_merge _ _ _ _ .Mint64 .Freeable bret Integers.Ptrofs.zero
      rfl rfl (fun e le hp m hP _ => ?_)
    obtain ⟨hR, rfl, rfl, w0, h1, h2, hd, rfl, hm, hF⟩ := hP
    refine ⟨w0, w, h1, h2, hd, rfl, hm, EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _
      (hx e le hR)), ⟨w, EvalExpr.Etempvar _ _ _ (hy e le hR), semCast_ptr_ptr m w _ _ _ _ hw⟩,
      fun h1' hm' hd' => ⟨hR, h1', h2, hd', rfl, ⟨w, h1', Heap.emp, Heap.disjoint_emp_right _,
        (Heap.union_emp _).symm, hm', rfl, rfl⟩, hF⟩⟩
  · refine Sep.triple_exists ge fe f_merge _ _ _ (fun bc => ?_)
    refine Sep.triple_exists ge fe f_merge _ _ _ (fun oc => ?_)
    refine Sep.triple_assign ge fe f_merge _ _ _ _ .Mint64 p bc
      (Integers.Ptrofs.add oc (Integers.Ptrofs.repr 8)) hpw rfl (fun e le hp m hP _ => ?_)
    obtain ⟨hR, mm, l, begin, w0, rfl, rfl, hH⟩ := hP
    rw [sep_rot, nodeAt, listNode_tail_front] at hH
    obtain ⟨h1, h2, hd, rfl, hm, hrest⟩ := hH
    have hno := (pure_sep_elim hrest).1
    have haddr : Integers.Ptrofs.unsigned (Integers.Ptrofs.add oc (Integers.Ptrofs.repr 8))
        = Integers.Ptrofs.unsigned oc + 8 :=
      ptrofs_add_nonneg_unsigned oc 8 (by omega) (by zomega)
    refine ⟨w0, w, h1, h2, hd, rfl, by rw [haddr]; exact hm,
      EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hx e le hR)),
      ⟨w, EvalExpr.Etempvar _ _ _ (hy e le hR), semCast_ptr_ptr m w _ _ _ _ hw⟩,
      fun h1' hm' hd' => ⟨hR, ?_⟩⟩
    have hH : (nodeAt p bc oc l w ∗ (mapsto .Mint64 .Freeable bret 0 begin
        ∗ (lseg (listNode p) mm begin (.Vptr bc oc) ∗ F))) (Heap.union h1' h2) := by
      rw [nodeAt, listNode_tail_front]
      exact ⟨h1', h2, hd', rfl, by rw [haddr] at hm'; exact hm', hrest⟩
    rw [← sep_rot] at hH
    exact sep_mono (fun h hh => ⟨begin, sep_mono (entails_refl _)
      (fun h hh => lseg_snoc _ l w bc oc mm begin h hh) h hh⟩) (entails_refl _) _ hH

/-- `*x = y; x = &(y->tail); y = y->tail;` -/
def stepStmt (y : Ident) : Stmt :=
  .Ssequence (.Sassign derefX (.Etempvar y tlistp))
    (.Ssequence (.Sset _x (.Eaddrof (tailOf y) tlistpp)) (.Sset y (tailOf y)))

include hcenv hpw in
/-- **One step of the loop**: the node `v` at `y` joins the merged prefix. -/
theorem step_triple (y : Ident) (hyx : y ≠ _x) (Q : Env → TempEnv → Prop)
    (hQx : ∀ e le w, Q e le → Q e (le.set _x w)) (hQy : ∀ e le w, Q e le → Q e (le.set y w))
    (merged l : List Integers.Int) (v : Integers.Int) (b : Block) (o : Integers.Ptrofs)
    (u x : Val) (F : HProp) :
    Sep.Triple ge fe f_merge
      (fun e le hp => (Q e le ∧ le.get y = some (.Vptr b o) ∧ le.get _x = some x)
        ∧ (nodeAt p b o v u ∗ listrepL p l u ∗ Out p bret merged x ∗ F) hp)
      (stepStmt y)
      (.only fun e le hp =>
        (Q e le ∧ le.get y = some u
          ∧ le.get _x = some (.Vptr b (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8))))
        ∧ (listrepL p l u ∗ Out p bret (merged ++ [v])
            (.Vptr b (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8))) ∗ F) hp) := by
  let o8 := Integers.Ptrofs.add o (Integers.Ptrofs.repr 8)
  let G : HProp := nodeAt p b o v u ∗ (listrepL p l u ∗ F)
  -- `*x = y;`
  refine Sep.triple_seq_only ge fe f_merge (Q := fun e le hp =>
      (Q e le ∧ le.get y = some (.Vptr b o) ∧ le.get _x = some x)
      ∧ (Filled p bret merged (.Vptr b o) ∗ G) hp) ?_ ?_
  · refine Sep.triple_pre ge fe f_merge (fun e le hp ⟨hR, hH⟩ => ⟨hR, by
      rwa [sep_left_comm_eq (listrepL p l u), sep_left_comm_eq (nodeAt p b o v u)] at hH⟩)
      (out_store ge fe p bret hpw _ G y merged x (.Vptr b o) (fun _ _ h => h.2.2)
        (fun _ _ h => h.2.1) (Or.inr ⟨b, o, rfl⟩))
  -- `x = &(y->tail);`
  refine Sep.triple_seq_only ge fe f_merge (Q := fun e le hp =>
      (Q e le ∧ le.get y = some (.Vptr b o) ∧ le.get _x = some (.Vptr b o8))
      ∧ (Filled p bret merged (.Vptr b o) ∗ G) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨hq, hy, -⟩, hH⟩ := hP
    exact ⟨_, EvalExpr.Eaddrof _ _ b _ (lvalue_field layout hcenv hy layout.off_tail tlistp),
      ⟨hQx e le _ hq, (PTree.gso _ _ _ _ (Ne.symm hyx)).trans hy, PTree.gss _ _ _⟩, hH⟩
  -- `y = y->tail;`
  refine Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP hag => ?_)
  obtain ⟨⟨hq, hy, hx⟩, hH⟩ := hP
  have hH' := hH
  rw [sep_left_comm_eq] at hH'
  have hu : IsLink u := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, _⟩ := hH'
    exact isLink_of_listrep hl
  refine ⟨_, eval_tail layout hcenv (readable_of_writable hpw) hy hu hH' hag,
    ⟨hQy e le _ hq, PTree.gss _ _ _, (PTree.gso _ _ _ _ hyx).trans hx⟩, ?_⟩
  rw [← sep_assoc_eq] at hH
  have h2 := sep_mono (fun _ hh => filled_snoc p bret hh) (entails_refl _) hp hH
  rwa [sep_left_comm_eq] at h2

/-! ### `cond = a != NULL && b != NULL;` -/

/-- `y != NULL` -/
def neNull (y : Ident) : Expr := .Ebinop .One (.Etempvar y tlistp) nullE tint

/-- The value of `cond`. -/
def condB (la lb : List Integers.Int) : Bool := !la.isEmpty && !lb.isEmpty

/-- `y != NULL` for the list `l` at `y`. -/
theorem eval_ne_null {e : Env} {le : TempEnv} {m : Mem} {y : Ident} {l : List Integers.Int}
    {v : Val} {F : HProp} {hp : Heap} (hy : le.get y = some v)
    (hH : (listrepL p l v ∗ F) hp) (hag : Heap.Agrees hp m) :
    EvalExpr ge e le m (neNull y) (Val.ofBool (!l.isEmpty)) := by
  cases l with
  | nil =>
    obtain ⟨h1, h2, hd, rfl, ⟨rfl, -⟩, _⟩ := hH
    refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hy) eval_null_cast ?_
    refine (semBinop_ne_null _ _ _ tlist tvoid noattr noattr (Or.inl rfl)).trans ?_
    simp
  | cons a c =>
    obtain ⟨b, o, u, rfl, -, hH'⟩ := listrep_cons_front hH
    refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hy) eval_null_cast ?_
    refine (semBinop_ne_null _ _ _ tlist tvoid noattr noattr
      (Or.inr ⟨b, o, rfl, node_valid hH' hag⟩)).trans ?_
    simp [Val.Vnullptr]

/-- `if (a != NULL) t = (_Bool)(b != NULL); else t = 0; cond = t;` -/
def condStmt (t : Ident) : Stmt :=
  .Ssequence
    (.Sifthenelse (neNull _a) (.Sset t (.Ecast (neNull _b) tbool))
      (.Sset t (.Econst_int (Integers.Int.repr 0) tint)))
    (.Sset _cond (.Etempvar t tint))

theorem cond_triple (t : Ident) (hta : t ≠ _a) (htb : t ≠ _b) (Q : Env → TempEnv → Prop)
    (hQt : ∀ e le w, Q e le → Q e (le.set t w)) (hQc : ∀ e le w, Q e le → Q e (le.set _cond w))
    (la lb : List Integers.Int) (av bv : Val) (F : HProp) :
    Sep.Triple ge fe f_merge
      (fun e le hp => (Q e le ∧ le.get _a = some av ∧ le.get _b = some bv)
        ∧ (listrepL p la av ∗ listrepL p lb bv ∗ F) hp)
      (condStmt t)
      (.only fun e le hp => ((Q e le ∧ le.get _a = some av ∧ le.get _b = some bv)
        ∧ le.get _cond = some (Val.ofBool (condB la lb)))
        ∧ (listrepL p la av ∗ listrepL p lb bv ∗ F) hp) := by
  have hR : ∀ e le w, (Q e le ∧ le.get _a = some av ∧ le.get _b = some bv) →
      (Q e (le.set t w) ∧ (le.set t w).get _a = some av ∧ (le.set t w).get _b = some bv) :=
    fun e le w ⟨hq, ha, hb⟩ => ⟨hQt e le w hq, (PTree.gso _ _ _ _ hta).trans ha,
      (PTree.gso _ _ _ _ htb).trans hb⟩
  refine Sep.triple_seq_only ge fe f_merge (Q := fun e le hp =>
      ((Q e le ∧ le.get _a = some av ∧ le.get _b = some bv)
        ∧ le.get t = some (Val.ofBool (condB la lb)))
      ∧ (listrepL p la av ∗ listrepL p lb bv ∗ F) hp) ?_ ?_
  · cases la with
    | nil =>
      refine Sep.triple_if_false ge fe f_merge _ _ _ _ _ (fun e le hp m hP hag => ?_)
        (Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP _ =>
          ⟨_, EvalExpr.Econst_int _ _, ⟨hR e le _ hP.1, PTree.gss _ _ _⟩, hP.2⟩))
      exact ⟨_, eval_ne_null ge p hP.1.2.1 hP.2 hag, boolVal_ofBool_int m false⟩
    | cons a c =>
      refine Sep.triple_if_true ge fe f_merge _ _ _ _ _ (fun e le hp m hP hag => ?_)
        (Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP hag => ?_))
      · exact ⟨_, eval_ne_null ge p hP.1.2.1 hP.2 hag, boolVal_ofBool_int m true⟩
      · obtain ⟨hq, hH⟩ := hP
        have hH' := hH
        rw [sep_left_comm_eq] at hH'
        exact ⟨_, EvalExpr.Ecast _ _ _ _ (eval_ne_null ge p hq.2.2 hH' hag)
          (semCast_ofBool_bool _ m), ⟨hR e le _ hq, PTree.gss _ _ _⟩, hH⟩
  · refine Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨⟨hq, ha, hb⟩, ht⟩, hH⟩ := hP
    exact ⟨_, EvalExpr.Etempvar _ _ _ ht, ⟨⟨hQc e le _ hq, (PTree.gso _ _ _ _ (by decide)).trans ha,
      (PTree.gso _ _ _ _ (by decide)).trans hb⟩, PTree.gss _ _ _⟩, hH⟩

end

/-! ## The loop -/

/-- The local environment: `ret` at block `bret`. -/
abbrev envR (bret : Block) : Env := emptyEnv.set _ret (bret, tlistp)

/-- The temporaries `a`, `b`, `x`. -/
def Tmp (av bv xv : Val) (le : TempEnv) : Prop :=
  le.get _a = some av ∧ le.get _b = some bv ∧ le.get _x = some xv

section
variable (p : Permission) (bret : Block) (la0 lb0 : List Integers.Int)

/-- The loop invariant (VST's `merge_invariant`), `k` nodes left: the merged
    prefix `merged` followed by the merge of the rests `la` (at `a`) and `lb`
    (at `b`) is the merge of the inputs. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ merged la lb av bv xv, merge la0 lb0 = merged ++ merge la lb ∧ la.length + lb.length = k
    ∧ e = envR bret ∧ Tmp av bv xv le ∧ le.get _cond = some (Val.ofBool (condB la lb))
    ∧ (listrepL p la av ∗ listrepL p lb bv ∗ Out p bret merged xv) hp

/-- After the test: both lists are non-empty. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ merged va la vb lb ba oa ua bb ob ub xv,
    merge la0 lb0 = merged ++ merge (va :: la) (vb :: lb) ∧ la.length + lb.length + 2 = k
    ∧ e = envR bret ∧ Tmp (.Vptr ba oa) (.Vptr bb ob) xv le
    ∧ (nodeAt p ba oa va ua ∗ listrepL p la ua ∗ nodeAt p bb ob vb ub ∗ listrepL p lb ub
        ∗ Out p bret merged xv) hp

/-- After one node was moved, before `cond` is recomputed. -/
def LStep (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ merged la lb av bv xv, merge la0 lb0 = merged ++ merge la lb
    ∧ la.length + lb.length + 1 = k ∧ e = envR bret ∧ Tmp av bv xv le
    ∧ (listrepL p la av ∗ listrepL p lb bv ∗ Out p bret merged xv) hp

/-- After the loop: one of the lists is empty. -/
def Done : Sep.Assn := fun e le hp =>
  ∃ merged la lb av bv xv, merge la0 lb0 = merged ++ merge la lb ∧ condB la lb = false
    ∧ e = envR bret ∧ Tmp av bv xv le
    ∧ (listrepL p la av ∗ listrepL p lb bv ∗ Out p bret merged xv) hp

def LoopR : Sep.ExitConds :=
  { normal := Done p bret la0 lb0, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := fun _ _ => False }

end

def ifStmt : Stmt := .Sifthenelse (.Etempvar _cond tint) .Sskip .Sbreak

def bodyStmt : Stmt :=
  .Ssequence (.Sset _va (headOf _a))
    (.Ssequence (.Sset _vb (headOf _b))
      (.Ssequence
        (.Sifthenelse (.Ebinop .Ole (.Etempvar _va tint) (.Etempvar _vb tint) tint)
          (stepStmt _a) (stepStmt _b))
        (condStmt _t'2)))

def loopStmt : Stmt := swhile (.Etempvar _cond tint) bodyStmt

/-- `if (a != NULL) *x = a; else *x = b;` -/
def finIf : Stmt :=
  .Sifthenelse (neNull _a) (.Sassign derefX (.Etempvar _a tlistp))
    (.Sassign derefX (.Etempvar _b tlistp))

/-- `temp = ret; return temp;` -/
def retStmt : Stmt :=
  .Ssequence (.Sset _temp (.Evar _ret tlistp)) (.Sreturn (some (.Etempvar _temp tlistp)))

def fullBody : Stmt :=
  .Ssequence (.Sset _x (.Eaddrof (.Evar _ret tlistp) tlistpp))
    (.Ssequence (condStmt _t'1) (.Ssequence loopStmt (.Ssequence finIf retStmt)))

theorem body_eq : f_merge.fn_body = fullBody := rfl

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (bret : Block)
  (la0 lb0 : List Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)

theorem if_triple (k : Nat) :
    Sep.Triple ge fe f_merge (LInv p bret la0 lb0 k) ifStmt
      { normal := LMid p bret la0 lb0 k, brk := Done p bret la0 lb0,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  unfold LInv
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun merged => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun la => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun lb => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun av => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun bv => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun xv => ?_)
  cases hg : condB la lb with
  | false =>
    refine Sep.triple_if_false ge fe f_merge _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨-, -, -, -, hcd, -⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ _ _ hcd, boolVal_ofBool_int m false⟩
    · refine Sep.triple_conseq ge fe f_merge (Sep.triple_break ge fe f_merge _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨hm, -, he, ht, -, hH⟩ := h
      exact ⟨merged, la, lb, av, bv, xv, hm, hg, he, ht, hH⟩
  | true =>
    refine Sep.triple_if_true ge fe f_merge _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨-, -, -, -, hcd, -⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ _ _ hcd, boolVal_ofBool_int m true⟩
    · refine Sep.triple_fallthrough ge fe f_merge _ _ _ _
        (Sep.triple_skip ge fe f_merge _) (fun e le hp h => ?_)
      obtain ⟨hm, hk, he, ht, -, hH⟩ := h
      cases la with
      | nil => exact absurd hg (by simp [condB])
      | cons va la =>
        cases lb with
        | nil => exact absurd hg (by simp [condB])
        | cons vb lb =>
          obtain ⟨ba, oa, ua, rfl, -, hH1⟩ := listrep_cons_front hH
          obtain ⟨h1, h2, hd, rfl, hn, h3, h4, hd', rfl, hl, hrest⟩ := hH1
          obtain ⟨bb, ob, ub, rfl, -, hrest'⟩ := listrep_cons_front hrest
          exact ⟨merged, va, la, vb, lb, ba, oa, ua, bb, ob, ub, xv, hm,
            by simp at hk; omega, he, ht, h1, _, hd, rfl, hn, h3, h4, hd', rfl, hl, hrest'⟩

theorem tmp_set {av bv xv : Val} {le : TempEnv} (id : Ident) (w : Val)
    (hid : id = _va ∨ id = _vb ∨ id = _t'1 ∨ id = _t'2 ∨ id = _cond)
    (h : Tmp av bv xv le) : Tmp av bv xv (le.set id w) := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases hid with rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨(PTree.gso _ _ _ _ (by decide)).trans h1, (PTree.gso _ _ _ _ (by decide)).trans h2,
    (PTree.gso _ _ _ _ (by decide)).trans h3⟩

include hcenv hpw in
theorem body_triple (k : Nat) :
    Sep.Triple ge fe f_merge (LMid p bret la0 lb0 k) bodyStmt
      (.only (fun e le hp => ∃ k', k' < k ∧ LInv p bret la0 lb0 k' e le hp)) := by
  unfold LMid
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun merged => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun va => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun la => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun vb => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun lb => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ba => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun oa => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ua => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun bb => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ob => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ub => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun xv => ?_)
  let NA := nodeAt p ba oa va ua
  let NB := nodeAt p bb ob vb ub
  let H : HProp := NA ∗ listrepL p la ua ∗ NB ∗ listrepL p lb ub ∗ Out p bret merged xv
  refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
      ∃ _ : (merge la0 lb0 = merged ++ merge (va :: la) (vb :: lb)
        ∧ la.length + lb.length + 2 = k),
      (e = envR bret ∧ Tmp (.Vptr ba oa) (.Vptr bb ob) xv le) ∧ H hp)
    (fun e le hp ⟨hm, hk, he, ht, hH⟩ => ⟨⟨hm, hk⟩, ⟨he, ht⟩, hH⟩) ?_
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ⟨hm, hk⟩ => ?_)
  -- `va = a->head;`
  refine Sep.triple_seq_only ge fe f_merge (Q := fun e le hp =>
      ((e = envR bret ∧ Tmp (.Vptr ba oa) (.Vptr bb ob) xv le) ∧ le.get _va = some (.Vint va))
      ∧ H hp) ?_ ?_
  · refine Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, ht⟩, hH⟩ := hP
    exact ⟨_, eval_head layout hcenv rfl (readable_of_writable hpw) ht.1 hH hag,
      ⟨⟨he, tmp_set _ _ (by simp) ht⟩, PTree.gss _ _ _⟩, hH⟩
  -- `vb = b->head;`
  refine Sep.triple_seq_only ge fe f_merge (Q := fun e le hp =>
      ((e = envR bret ∧ Tmp (.Vptr ba oa) (.Vptr bb ob) xv le) ∧ le.get _va = some (.Vint va)
        ∧ le.get _vb = some (.Vint vb)) ∧ H hp) ?_ ?_
  · refine Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨⟨he, ht⟩, hva⟩, hH⟩ := hP
    have hH' : (NB ∗ (NA ∗ (listrepL p la ua ∗ (listrepL p lb ub ∗ Out p bret merged xv)))) hp := by
      have e : H = (NB ∗ (NA ∗ (listrepL p la ua ∗ (listrepL p lb ub ∗ Out p bret merged xv)))) := by
        simp only [H, sep_left_comm_eq]
      rwa [e] at hH
    exact ⟨_, eval_head layout hcenv rfl (readable_of_writable hpw) ht.2.1 hH' hag,
      ⟨⟨he, tmp_set _ _ (by simp) ht⟩, (PTree.gso _ _ _ _ (by decide)).trans hva,
        PTree.gss _ _ _⟩, hH⟩
  refine Sep.triple_seq_only ge fe f_merge (Q := LStep p bret la0 lb0 k) ?_ ?_
  · cases hc : Integers.Int.cmp .Cle va vb with
    | true =>
      refine Sep.triple_if_true ge fe f_merge _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
      · obtain ⟨⟨-, hva, hvb⟩, -⟩ := hP
        exact ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hva)
          (EvalExpr.Etempvar _ _ _ hvb) (semBinop_le_int _ m va vb),
          (boolVal_ofBool_int m _).trans (by rw [show (!Integers.Int.lt vb va) = true from hc])⟩
      refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
          ((e = envR bret ∧ le.get _b = some (.Vptr bb ob)) ∧ le.get _a = some (.Vptr ba oa)
            ∧ le.get _x = some xv)
          ∧ (NA ∗ listrepL p la ua ∗ Out p bret merged xv ∗ (NB ∗ listrepL p lb ub)) hp)
        (fun e le hp ⟨⟨⟨he, ha, hb, hx⟩, _⟩, hH⟩ => ⟨⟨⟨he, hb⟩, ha, hx⟩, by
          have e : H = (NA ∗ listrepL p la ua ∗ Out p bret merged xv ∗ (NB ∗ listrepL p lb ub)) := by
            simp only [H, sep_assoc_eq, sep_comm_eq, sep_left_comm_eq]
          rwa [e] at hH⟩) ?_
      refine Sep.triple_fallthrough ge fe f_merge _ _ _ _
        (step_triple ge fe p bret hcenv hpw _a (by decide)
          (fun e le => e = envR bret ∧ le.get _b = some (.Vptr bb ob))
          (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩)
          (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩)
          merged la va ba oa ua xv _) (fun e le hp h => ?_)
      obtain ⟨⟨⟨he, hb⟩, ha, hx⟩, hH⟩ := h
      refine ⟨merged ++ [va], la, vb :: lb, ua, .Vptr bb ob, _, by rw [hm, merge_le _ _ hc]; simp,
        by simp; omega, he, ⟨ha, hb, hx⟩, ?_⟩
      refine sep_mono (entails_refl _) (fun h hh => ?_) hp hH
      rw [sep_comm_eq] at hh
      exact sep_mono (fun _ x => listrep_cons _ x) (entails_refl _) h hh
    | false =>
      refine Sep.triple_if_false ge fe f_merge _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
      · obtain ⟨⟨-, hva, hvb⟩, -⟩ := hP
        exact ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hva)
          (EvalExpr.Etempvar _ _ _ hvb) (semBinop_le_int _ m va vb),
          (boolVal_ofBool_int m _).trans (by rw [show (!Integers.Int.lt vb va) = false from hc])⟩
      refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
          ((e = envR bret ∧ le.get _a = some (.Vptr ba oa)) ∧ le.get _b = some (.Vptr bb ob)
            ∧ le.get _x = some xv)
          ∧ (NB ∗ listrepL p lb ub ∗ Out p bret merged xv ∗ (NA ∗ listrepL p la ua)) hp)
        (fun e le hp ⟨⟨⟨he, ha, hb, hx⟩, _⟩, hH⟩ => ⟨⟨⟨he, ha⟩, hb, hx⟩, by
          have e : H = (NB ∗ listrepL p lb ub ∗ Out p bret merged xv ∗ (NA ∗ listrepL p la ua)) := by
            simp only [H, sep_assoc_eq, sep_comm_eq, sep_left_comm_eq]
          rwa [e] at hH⟩) ?_
      refine Sep.triple_fallthrough ge fe f_merge _ _ _ _
        (step_triple ge fe p bret hcenv hpw _b (by decide)
          (fun e le => e = envR bret ∧ le.get _a = some (.Vptr ba oa))
          (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩)
          (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩)
          merged lb vb bb ob ub xv _) (fun e le hp h => ?_)
      obtain ⟨⟨⟨he, ha⟩, hb, hx⟩, hH⟩ := h
      refine ⟨merged ++ [vb], va :: la, lb, .Vptr ba oa, ub, _,
        by rw [hm, merge_gt _ _ hc]; simp, by simp; omega, he, ⟨ha, hb, hx⟩, ?_⟩
      have e : (listrepL p lb ub ∗ Out p bret (merged ++ [vb])
            (.Vptr bb (Integers.Ptrofs.add ob (Integers.Ptrofs.repr 8))) ∗ (NA ∗ listrepL p la ua))
          = ((NA ∗ listrepL p la ua) ∗ (listrepL p lb ub ∗ Out p bret (merged ++ [vb])
            (.Vptr bb (Integers.Ptrofs.add ob (Integers.Ptrofs.repr 8))))) := by
        simp only [sep_assoc_eq, sep_comm_eq, sep_left_comm_eq]
      rw [e] at hH
      exact sep_mono (fun _ x => listrep_cons _ x) (entails_refl _) hp hH
  -- `cond = a != NULL && b != NULL;`
  unfold LStep
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun merged => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun la => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun lb => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun av => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun bv => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun xv => ?_)
  refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
      ∃ _ : (merge la0 lb0 = merged ++ merge la lb ∧ la.length + lb.length + 1 = k),
      ((e = envR bret ∧ le.get _x = some xv) ∧ le.get _a = some av ∧ le.get _b = some bv)
      ∧ (listrepL p la av ∗ listrepL p lb bv ∗ Out p bret merged xv) hp)
    (fun e le hp ⟨hm, hk, he, ⟨ha, hb, hx⟩, hH⟩ => ⟨⟨hm, hk⟩, ⟨⟨he, hx⟩, ha, hb⟩, hH⟩) ?_
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ⟨hm, hk⟩ => ?_)
  refine Sep.triple_fallthrough ge fe f_merge _ _ _ _
    (cond_triple ge fe p _t'2 (by decide) (by decide)
      (fun e le => e = envR bret ∧ le.get _x = some xv)
      (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩)
      (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩) la lb av bv _)
    (fun e le hp h => ?_)
  obtain ⟨⟨⟨⟨he, hx⟩, ha, hb⟩, hcd⟩, hH⟩ := h
  exact ⟨la.length + lb.length, by omega, merged, la, lb, av, bv, xv, hm, rfl, he,
    ⟨ha, hb, hx⟩, hcd, hH⟩

include hcenv hpw in
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_merge (LInv p bret la0 lb0 k) loopStmt (LoopR p bret la0 lb0) := by
  refine Sep.triple_loop ge fe f_merge (LoopR p bret la0 lb0) (LInv p bret la0 lb0)
    (fun k e le hp => ∃ k', k' < k ∧ LInv p bret la0 lb0 k' e le hp) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_merge _ (LMid p bret la0 lb0 k) _ _ _
      (Sep.triple_conseq ge fe f_merge (if_triple ge fe p bret la0 lb0 k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_merge _ _ _ _
        (body_triple ge fe p bret la0 lb0 hcenv hpw k) (fun _ _ _ x => x))
  · exact Sep.triple_fallthrough ge fe f_merge _ _ _ _
      (Sep.triple_skip ge fe f_merge _) (fun _ _ _ x => x)

end

/-! ## After the loop -/

/-- The rest of the list is written into the cell; the other list is empty. -/
theorem filled_close (p : Permission) (bret : Block) {merged l : List Integers.Int} {w z : Val} {h : Heap}
    (hh : (Filled p bret merged w ∗ (listrepL p l w ∗ listrepL p [] z)) h) :
    ∃ begin, (mapsto .Mint64 .Freeable bret 0 begin ∗ listrepL p (merged ++ l) begin) h := by
  rw [← sep_assoc_eq] at hh
  obtain ⟨h1, h2, hd, rfl, h12, -, rfl⟩ := hh
  rw [Heap.union_emp]
  exact filled_listrep p bret h12

section
variable (p : Permission) (bret : Block) (la0 lb0 : List Integers.Int)

/-- After `*x = a` / `*x = b`: `ret` holds the merged list. -/
def Fin : Sep.Assn := fun e _ hp =>
  e = envR bret ∧ ∃ begin,
    (mapsto .Mint64 .Freeable bret 0 begin ∗ listrepL p (merge la0 lb0) begin) hp

end

theorem merge_nil_l (l : List Integers.Int) : merge [] l = l := by simp [merge]

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (bret : Block)
  (la0 lb0 : List Integers.Int)
  (hcenv : ge.genv_cenv = prog.prog_comp_env) (hpw : permOrder p .Writable = true)

include hpw in
/-- `if (a != NULL) *x = a; else *x = b;` -/
theorem fin_triple :
    Sep.Triple ge fe f_merge (Done p bret la0 lb0) finIf (.only (Fin p bret la0 lb0)) := by
  unfold Done Fin
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun merged => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun la => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun lb => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun av => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun bv => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun xv => ?_)
  let Rl : Env → TempEnv → Prop := fun e le => e = envR bret ∧ Tmp av bv xv le
  refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
      ∃ _ : (merge la0 lb0 = merged ++ merge la lb ∧ condB la lb = false ∧ IsLink av
        ∧ IsLink bv),
      Rl e le ∧ (listrepL p la av ∗ listrepL p lb bv ∗ Out p bret merged xv) hp)
    (fun e le hp ⟨hm, hc, he, ht, hH⟩ => ⟨⟨hm, hc, by
      obtain ⟨_, _, _, _, hl, _⟩ := hH
      exact isLink_of_listrep hl, by
      obtain ⟨_, _, _, _, _, _, _, _, _, hl, _⟩ := hH
      exact isLink_of_listrep hl⟩, ⟨he, ht⟩, hH⟩) ?_
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ⟨hm, hc, hav, hbv⟩ => ?_)
  cases la with
  | nil =>
    refine Sep.triple_if_false ge fe f_merge _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
    · exact ⟨_, eval_ne_null ge p hP.1.2.1 hP.2 hag, boolVal_ofBool_int m false⟩
    refine Sep.triple_pre ge fe f_merge (P := fun e le hp => Rl e le
        ∧ (Out p bret merged xv ∗ (listrepL p lb bv ∗ listrepL p [] av)) hp)
      (fun e le hp ⟨hR, hH⟩ => ⟨hR, by
      have e : (listrepL p [] av ∗ listrepL p lb bv ∗ Out p bret merged xv)
          = (Out p bret merged xv ∗ (listrepL p lb bv ∗ listrepL p [] av)) := by
        simp only [sep_assoc_eq, sep_comm_eq, sep_left_comm_eq]
      rwa [e] at hH⟩) ?_
    refine Sep.triple_fallthrough ge fe f_merge _ _ _ _
      (out_store ge fe p bret hpw Rl _ _b merged xv bv (fun _ _ h => h.2.2.2)
        (fun _ _ h => h.2.2.1) hbv) (fun e le hp h => ?_)
    refine ⟨h.1.1, ?_⟩
    rw [hm, merge_nil_l]
    exact filled_close p bret h.2
  | cons va la =>
    cases lb with
    | cons vb lb => exact absurd hc (by simp [condB])
    | nil =>
      refine Sep.triple_if_true ge fe f_merge _ _ _ _ _ (fun e le hp m hP hag => ?_) ?_
      · exact ⟨_, eval_ne_null ge p hP.1.2.1 hP.2 hag, boolVal_ofBool_int m true⟩
      refine Sep.triple_pre ge fe f_merge (P := fun e le hp => Rl e le
          ∧ (Out p bret merged xv ∗ (listrepL p (va :: la) av ∗ listrepL p [] bv)) hp)
        (fun e le hp ⟨hR, hH⟩ => ⟨hR, by
        have e : (listrepL p (va :: la) av ∗ listrepL p [] bv ∗ Out p bret merged xv)
            = (Out p bret merged xv ∗ (listrepL p (va :: la) av ∗ listrepL p [] bv)) := by
          simp only [sep_assoc_eq, sep_comm_eq]
        rwa [e] at hH⟩) ?_
      refine Sep.triple_fallthrough ge fe f_merge _ _ _ _
        (out_store ge fe p bret hpw Rl _ _a merged xv av (fun _ _ h => h.2.2.2)
          (fun _ _ h => h.2.1) hav) (fun e le hp h => ?_)
      refine ⟨h.1.1, ?_⟩
      rw [hm, merge_nil_r]
      exact filled_close p bret h.2

/-- `temp = ret; return temp;` frees `ret` and returns the merged list. -/
theorem ret_triple :
    Sep.Triple ge fe f_merge (Fin p bret la0 lb0) retStmt
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := fun r hp => listrepL p (merge la0 lb0) r hp } := by
  let Lr : Val → HProp := fun begin => listrepL p (merge la0 lb0) begin
  refine Sep.triple_pre ge fe f_merge (P := fun e le hp => ∃ begin,
      (e = envR bret ∧ IsLink begin)
      ∧ (mapsto .Mint64 .Freeable bret 0 begin ∗ Lr begin) hp)
    (fun e le hp ⟨he, begin, hH⟩ => ⟨begin, ⟨he, by
      obtain ⟨_, _, _, _, _, hl⟩ := hH
      exact isLink_of_listrep hl⟩, hH⟩) ?_
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun begin => ?_)
  -- `temp = ret;`
  refine Sep.triple_seq_only ge fe f_merge (Q := fun e le hp =>
      ((e = envR bret ∧ IsLink begin) ∧ le.get _temp = some begin)
      ∧ (mapsto .Mint64 .Freeable bret 0 begin ∗ Lr begin) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨rfl, hb⟩, hH⟩ := hP
    have hev := hH
    obtain ⟨h1, h2, hd, rfl, hm, -⟩ := hev
    have := eval_lvalue_mapsto (ge := ge) (chunk := .Mint64) (pm := .Freeable) (v := begin)
      (a := .Evar _ret tlistp) (le := le) rfl rfl eval_lvalue_oneLocal rfl hm
      (Heap.Agrees_union_left hag)
    rw [loadResult_link hb] at this
    exact ⟨_, this, ⟨⟨rfl, hb⟩, PTree.gss _ _ _⟩, hH⟩
  -- `return temp;`
  refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
      ∃ L, ∃ _ : L.get _temp = some begin ∧ IsLink begin,
        AtE (envR bret) L (Lr begin ∗ bytesPtsTo bret .Freeable 0 (encodeVal .Mint64 begin))
          e le hp)
    (fun e le hp ⟨⟨⟨he, hb⟩, ht⟩, hH⟩ => ⟨le, ⟨ht, hb⟩, he, rfl, by
      rwa [sep_comm_eq, mapsto_eq_bytes (by decide)] at hH⟩) ?_
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun L => ?_)
  refine Sep.triple_exists ge fe f_merge _ _ _ (fun ⟨hL, hb⟩ => ?_)
  exact Sep.triple_conseq ge fe f_merge
    (triple_return_oneLocal ge fe f_merge _ret tlistp bret L (Lr begin)
      (encodeVal .Mint64 begin) (.Etempvar _temp tlistp) begin begin
      (by rw [length_encodeVal]; rfl) (fun _ _ _ _ => EvalExpr.Etempvar _ _ _ hL)
      (fun m => semCast_ptr_ptr m begin _ _ _ _ hb))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun r hp ⟨hr, h⟩ => hr ▸ h)

end

/-! ## As a function specification -/

/-- `merge_spec`: the lists `la` at `a` and `lb` at `b` are merged into the
    list `merge la lb` at the returned pointer. -/
def mergeSpec (p : Permission) (la lb : List Integers.Int) (a b : Val) : Sep.FunSpec where
  tyargs := [tlistp, tlistp]
  tyres := tlistp
  cc := cc_default
  pre := fun vargs hp => vargs = [a, b] ∧ (listrepL p la a ∗ listrepL p lb b) hp
  post := fun r hp => listrepL p (merge la lb) r hp
  measure := fun _ => 0

/-- **`merge` satisfies `merge_spec`** (VST's `body_merge`). -/
theorem merge_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (hpw : permOrder p .Writable = true) (la lb : List Integers.Int)
    (a b : Val) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_merge) (mergeSpec p la lb a b)
      [a, b] := by
  let L : TempEnv := ((createUndefTemps f_merge.fn_temps).set _a a).set _b b
  refine satisfies_oneLocal ge f_merge _ _ L _ret tlistp rfl (by decide) (by decide) rfl
    (by rw [show sizeof ge.genv_cenv tlistp = 8 from rfl]; decide) fun bret => ?_
  let fe := FunctionEntry2 ge
  rw [body_eq]
  refine Sep.triple_pre ge fe f_merge (P := fun e le hp =>
      e = envR bret ∧ le.get _a = some a ∧ le.get _b = some b
      ∧ (listrepL p la a ∗ listrepL p lb b ∗ mapsto .Mint64 .Freeable bret 0 .Vundef) hp)
    (fun e le hp ⟨he, hl, hH⟩ => by
      subst hl
      refine ⟨he, (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _), PTree.gss _ _ _, ?_⟩
      rw [show (sizeof ge.genv_cenv tlistp).toNat = sizeChunkNat .Mint64 from rfl,
        undefBytes_mapsto _ _ _ undefEncoded_Mint64 (by decide)] at hH
      obtain ⟨h1, h2, hd, rfl, ⟨-, hL⟩, hm⟩ := hH
      rw [← sep_assoc_eq]
      exact ⟨h1, h2, hd, rfl, hL, hm⟩) ?_
  -- `x = &ret;`
  refine Sep.triple_seq_only ge fe f_merge (Q := fun e le hp =>
      ((e = envR bret ∧ le.get _x = some (.Vptr bret Integers.Ptrofs.zero))
        ∧ le.get _a = some a ∧ le.get _b = some b)
      ∧ (listrepL p la a ∗ listrepL p lb b
          ∗ Out p bret [] (.Vptr bret Integers.Ptrofs.zero)) hp) ?_ ?_
  · refine Sep.triple_set ge fe f_merge _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨rfl, ha, hb, hH⟩ := hP
    exact ⟨_, eval_addrof_oneLocal _, ⟨⟨rfl, PTree.gss _ _ _⟩,
      (PTree.gso _ _ _ _ (by decide)).trans ha, (PTree.gso _ _ _ _ (by decide)).trans hb⟩,
      sep_mono (entails_refl _) (sep_mono (entails_refl _)
        (fun _ hm => Or.inl ⟨rfl, rfl, _, hm⟩)) hp hH⟩
  -- `cond = a != NULL && b != NULL;`
  refine Sep.triple_seq_only ge fe f_merge
    (cond_triple ge fe p _t'1 (by decide) (by decide)
      (fun e le => e = envR bret ∧ le.get _x = some (.Vptr bret Integers.Ptrofs.zero))
      (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩)
      (fun _ _ _ h => ⟨h.1, (PTree.gso _ _ _ _ (by decide)).trans h.2⟩) la lb a b _) ?_
  refine Sep.triple_pre ge fe f_merge (P := LInv p bret la lb (la.length + lb.length))
    (fun e le hp ⟨⟨⟨⟨he, hx⟩, ha, hb⟩, hcd⟩, hH⟩ =>
      ⟨[], la, lb, a, b, _, rfl, rfl, he, ⟨ha, hb, hx⟩, hcd, hH⟩) ?_
  -- the loop, then the end
  refine Sep.triple_seq ge fe f_merge _ (Done p bret la lb) _ _ _
    (Sep.triple_conseq ge fe f_merge
      (loop_triple ge fe p bret la lb hcenv hpw (la.length + lb.length))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x.elim)) ?_
  exact Sep.triple_seq_only ge fe f_merge (fin_triple ge fe p bret la lb hpw)
    (ret_triple ge fe p bret la lb)

end VST.Verif.Merge
