/-
  Port of VST's `progs/verif_queue.v`, part 1: the representation of the
  queue of `vst/progs/queue.c`, and `surely_malloc`.

      struct elem { int a, b; struct elem *next; };
      struct fifo { struct elem *head; struct elem *tail; };

      void *surely_malloc (size_t n) {
        void *p = malloc(n);
        if (!p) exit(1);
        return p;
      }

  VST's representation predicates:

      fifo_body contents hd tl :=
        if isnil contents then !!(hd = nullval) && emp
        else EX prefix, !!(contents = prefix ++ tl :: nil)
               && lseg QS Qsh Ews prefix hd tl * list_cell QS Qsh (Vundef,Vundef) tl
                  * field_at Ews t_struct_elem [StructField _next] nullval tl

      fifo contents p := EX hd tl, !! is_pointer_or_null hd && !! is_pointer_or_null tl
        && data_at Ews t_struct_fifo (hd, tl) p * malloc_token Ews t_struct_fifo p
         * fifo_body contents hd tl

  Differences, all coming from the heap model of this port, which has
  permissions per byte but no fractional shares:
  * VST splits each element between the queue (a non-readable share of `a`,
    `b` and the whole `next` field) and the client (a readable share of `a`
    and `b`).  The queue's share of `a`/`b` is what makes the element a valid
    pointer for the `h == NULL` test.  Without shares the queue owns the
    whole element while it is queued, so an element of `contents` is a
    `QElem`: its pointer together with the values of `a` and `b`.
  * Every struct comes from `malloc` and is owned at permission `Freeable`.
  * The `fifo` struct is at offset zero of its block (as `malloc` returns
    it), because its `malloc` token is part of `fifo`.

  `surely_malloc` meets `malloc`'s own specification (`Sep.mallocSpec`): it
  returns a pointer to a fresh block with its token.  `malloc` never returns
  `NULL` in CompCert's semantics, so `exit` is never called.
-/
import VST.progs.queue
import CCLib
open CC CC.Sep CC.HProp
open Queue

namespace VST.Verif.Queue

/-! ## The two structs -/

abbrev telem : Ty := .Tstruct _elem noattr
abbrev tfifo : Ty := .Tstruct _fifo noattr

/-- The composite of a struct of a program's composite environment `ce`. -/
def coOf (ce : CompositeEnv) (id : Ident) : Composite :=
  match ce.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

/-- What the queue operations need of a program's composite environment:
    `struct fifo` with `head` at offset 0 and `tail` at offset 8, and
    `struct elem` with an `int` field `fst` at offset 0 and `next` at offset 8.
    Both `queue.c` (`fst = a`) and `queue2.c` (`fst = data`) have it. -/
structure QueueCenv (ce : CompositeEnv) where
  fst : Ident
  coE : Composite
  coF : Composite
  getE : ce.get _elem = some coE
  getF : ce.get _fifo = some coF
  offFst : fieldOffset ce fst coE.co_members = .OK (0, .Full)
  offNext : fieldOffset ce _next coE.co_members = .OK (8, .Full)
  offHead : fieldOffset ce _head coF.co_members = .OK (0, .Full)
  offTail : fieldOffset ce _tail coF.co_members = .OK (8, .Full)
  szE : sizeof ce telem = 16
  szF : sizeof ce tfifo = 16

/-- `struct elem`: `fst` at offset 0, `next` at offset 8. -/
def QueueCenv.elemL {ce : CompositeEnv} (QC : QueueCenv ce) : ListLayout :=
  ⟨ce, _elem, QC.fst, _next, QC.coE, QC.getE, QC.offFst, QC.offNext⟩

/-- `struct fifo`: `head` at offset 0, `tail` at offset 8. -/
def QueueCenv.fifoL {ce : CompositeEnv} (QC : QueueCenv ce) : ListLayout :=
  ⟨ce, _fifo, _head, _tail, QC.coF, QC.getF, QC.offHead, QC.offTail⟩

/-- The composite environment of `queue.c`. -/
def queueCenv : QueueCenv prog.prog_comp_env :=
  ⟨_a, coOf prog.prog_comp_env _elem, coOf prog.prog_comp_env _fifo, rfl, rfl, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem off_b : fieldOffset prog.prog_comp_env _b (coOf prog.prog_comp_env _elem).co_members = .OK (4, .Full) := by
  decide

theorem sizeof_elem : sizeof prog.prog_comp_env telem = 16 := by decide
theorem sizeof_fifo : sizeof prog.prog_comp_env tfifo = 16 := by decide

/-- The size of both structs, as `malloc` gets it. -/
abbrev sz16 : Integers.Ptrofs := Integers.Ptrofs.repr 16

theorem unsigned_sz16 : Integers.Ptrofs.unsigned sz16 = 16 := by decide

/-! ## Elements -/

/-- An element of the queue: the pointer to its `struct elem`, the value of
    its first field `a`, and the contents `b` of the four bytes after it (the
    field `b` of `queue.c`; padding, `Vundef`, in `queue2.c`). -/
structure QElem where
  ptr : Val
  a : Integers.Int
  b : Val

/-- The `struct elem` at `bk + X` with `a`, `b` and `next = u`. -/
def elemAt (bk : Block) (X : _root_.Int) (a : Integers.Int) (b : Val) (u : Val) : HProp :=
  listNode .Freeable bk X a u ∗ mapsto .Mint32 .Freeable bk (X + 4) b

/-- The node of the queue at `bk + X` holding the element `q`, with link `u`. -/
def qnode (bk : Block) (X : _root_.Int) (q : QElem) (u : Val) : HProp :=
  ⌜q.ptr = .Vptr bk (Integers.Ptrofs.repr X)⌝ ∗ elemAt bk X q.a q.b u

/-! ## The queue -/

/-- VST's `fifo_body`: the nodes from `hd` hold `contents`, and the last one
    is `tl`, with a null link. -/
def fifoBody : List QElem → Val → Val → HProp
  | [], hd, _ => ⌜hd = Val.Vnullptr⌝
  | q :: c, hd, tl => fun h => ∃ pre e, q :: c = pre ++ [e] ∧ e.ptr = tl
      ∧ (lseg qnode pre hd tl ∗ lseg qnode [e] tl Val.Vnullptr) h

/-- The `struct fifo` at `qb` holding `hd` and `tl`, its `malloc` token, and
    the queue's nodes. -/
def fifoH (qb : Block) (hd tl : Val) (contents : List QElem) : HProp :=
  mapsto .Mint64 .Freeable qb 0 hd ∗ (mapsto .Mint64 .Freeable qb 8 tl
    ∗ (mallocToken qb sz16 ∗ fifoBody contents hd tl))

/-- VST's `fifo contents p`: the `struct fifo` at `p`, its `malloc` token, and
    the queue's nodes. -/
def fifo (contents : List QElem) (p : Val) : HProp := fun h =>
  ∃ qb hd tl, p = .Vptr qb Integers.Ptrofs.zero ∧ IsLink hd ∧ IsLink tl
    ∧ fifoH qb hd tl contents h

/-- An element outside the queue, with any link (VST's
    `field_at Qsh' … _a; field_at Qsh' … _b; list_cell QS Qsh …;
    field_at_ Ews … _next`). -/
def elemRep (q : QElem) : HProp := fun h =>
  ∃ bk o u, q.ptr = .Vptr bk o ∧ elemAt bk (Integers.Ptrofs.unsigned o) q.a q.b u h

/-! ## Facts about nodes -/

/-- A node makes its address a weakly valid pointer. -/
theorem qnode_valid {bk : Block} {X : _root_.Int} {q : QElem} {u : Val} {F : HProp} {h : Heap}
    {m : Mem} (hn : (qnode bk X q u ∗ F) h) (hag : Heap.Agrees h m) :
    Mem.weakValidPointer m bk X = true := by
  obtain ⟨h1, h2, hd, rfl, hq, -⟩ := hn
  obtain ⟨-, he⟩ := pure_sep_elim hq
  obtain ⟨h3, h4, hd', rfl, hl, -⟩ := he
  exact node_valid (F := emp) ⟨h3, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm,
    hl, rfl⟩ (Heap.Agrees_union_left (Heap.Agrees_union_left hag))

/-- A non-empty segment next to a frame: its first node, the rest, the frame. -/
theorem lseg_cons_front {q : QElem} {c : List QElem} {x y : Val} {F : HProp} {h : Heap}
    (hl : (lseg qnode (q :: c) x y ∗ F) h) :
    ∃ b o u, x = .Vptr b o ∧ (qnode b (Integers.Ptrofs.unsigned o) q u ∗ (lseg qnode c u y ∗ F)) h := by
  obtain ⟨h1, h2, hd, rfl, ⟨b, o, u, rfl, hs⟩, hF⟩ := hl
  refine ⟨b, o, u, rfl, ?_⟩
  rw [← sep_assoc_eq]
  exact ⟨_, _, hd, rfl, hs, hF⟩

/-- The link at the start of a segment ending at a link is a link. -/
theorem isLink_of_lseg {c : List QElem} {x y : Val} {h : Heap} (hy : IsLink y)
    (hl : lseg qnode c x y h) : IsLink x := by
  cases c with
  | nil => exact hl.1 ▸ hy
  | cons q c =>
    obtain ⟨b, o, u, rfl, -⟩ := hl
    exact Or.inr ⟨b, o, rfl⟩

/-- The pointer of a node's element is the node's address. -/
theorem qnode_ptr {bk : Block} {o : Integers.Ptrofs} {q : QElem} {u : Val} {h : Heap}
    (hq : qnode bk (Integers.Ptrofs.unsigned o) q u h) : q.ptr = .Vptr bk o := by
  have := (pure_sep_elim hq).1
  rwa [Integers.Ptrofs.repr_unsigned] at this

/-- The head of a queue: null for the empty queue, a weakly valid pointer
    otherwise. -/
theorem fifoBody_head {c : List QElem} {hd tl : Val} {F : HProp} {h : Heap} {m : Mem}
    (hb : (fifoBody c hd tl ∗ F) h) (hag : Heap.Agrees h m) :
    (c = [] ∧ hd = Val.Vnullptr)
      ∨ (c ≠ [] ∧ ∃ b o, hd = .Vptr b o
          ∧ Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) := by
  cases c with
  | nil =>
    obtain ⟨h1, h2, hd', rfl, ⟨rfl, rfl⟩, -⟩ := hb
    exact Or.inl ⟨rfl, rfl⟩
  | cons q c =>
    refine Or.inr ⟨List.cons_ne_nil _ _, ?_⟩
    obtain ⟨h1, h2, hd', rfl, ⟨pre, e, -, -, hs⟩, hF⟩ := hb
    cases pre with
    | nil =>
      obtain ⟨h3, h4, hd34, rfl, ⟨rfl, rfl⟩, hl⟩ := hs
      obtain ⟨b, o, u, rfl, hn⟩ := lseg_cons_front (F := emp)
        ⟨h4, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm, hl, rfl⟩
      refine ⟨b, o, rfl, qnode_valid hn ?_⟩
      have hag' := Heap.Agrees_union_left hag
      rw [Heap.emp_union] at hag'
      simpa using hag'
    | cons q' pre =>
      obtain ⟨b, o, u, rfl, hn⟩ := lseg_cons_front hs
      exact ⟨b, o, rfl, qnode_valid hn (Heap.Agrees_union_left hag)⟩

theorem uz (d : _root_.Int) : Integers.Ptrofs.unsigned Integers.Ptrofs.zero + d = d := by
  rw [ptrofs_unsigned_zero, Int.zero_add]

theorem fifoH_tail_front (qb : Block) (hd tl : Val) (c : List QElem) :
    fifoH qb hd tl c = mapsto .Mint64 .Freeable qb 8 tl ∗ (mapsto .Mint64 .Freeable qb 0 hd
      ∗ (mallocToken qb sz16 ∗ fifoBody c hd tl)) := by
  rw [fifoH, sep_left_comm_eq]

/-- The `next` field of an element in front. -/
theorem elemAt_next_front (bk : Block) (X : _root_.Int) (a : Integers.Int) (b u : Val)
    (F : HProp) :
    (elemAt bk X a b u ∗ F) = mapsto .Mint64 .Freeable bk (X + 8) u
      ∗ (⌜X + 16 ≤ 18446744073709551616⌝ ∗ mapsto .Mint32 .Freeable bk X (.Vint a)
        ∗ (mapsto .Mint32 .Freeable bk (X + 4) b ∗ F)) := by
  rw [elemAt, sep_assoc_eq, listNode_tail_front]

/-- The `a` field of an element in front. -/
theorem elemAt_a_front (bk : Block) (X : _root_.Int) (a : Integers.Int) (b u : Val)
    (F : HProp) :
    (elemAt bk X a b u ∗ F) = mapsto .Mint32 .Freeable bk X (.Vint a)
      ∗ (⌜X + 16 ≤ 18446744073709551616⌝ ∗ mapsto .Mint64 .Freeable bk (X + 8) u
        ∗ (mapsto .Mint32 .Freeable bk (X + 4) b ∗ F)) := by
  rw [elemAt, sep_assoc_eq, listNode_head_front]

/-- The `b` field of an element in front. -/
theorem elemAt_b_front (bk : Block) (X : _root_.Int) (a : Integers.Int) (b u : Val)
    (F : HProp) :
    (elemAt bk X a b u ∗ F) = mapsto .Mint32 .Freeable bk (X + 4) b
      ∗ (listNode .Freeable bk X a u ∗ F) := by
  rw [elemAt, sep_assoc_eq, sep_left_comm_eq]

/-- An element lies inside the address space. -/
theorem elemAt_bound {bk : Block} {X : _root_.Int} {a : Integers.Int} {b u : Val} {h : Heap}
    (he : elemAt bk X a b u h) : X + 16 ≤ 18446744073709551616 := by
  obtain ⟨h1, h2, _, rfl, hl, _⟩ := he
  exact (pure_sep_elim hl).1

/-! ## Facts about the queue's nodes -/

theorem qnode_of_elemAt {bk : Block} {o : Integers.Ptrofs} {q : QElem} {u : Val} {h : Heap}
    (hp : q.ptr = .Vptr bk o) (he : elemAt bk (Integers.Ptrofs.unsigned o) q.a q.b u h) :
    qnode bk (Integers.Ptrofs.unsigned o) q u h :=
  pure_sep_intro (by rw [Integers.Ptrofs.repr_unsigned]; exact hp) he

/-- The nodes of a queue whose last element is `e`. -/
theorem fifoBody_snoc {pre : List QElem} {e : QElem} {hd tl : Val} {h : Heap} (hp : e.ptr = tl)
    (hs : (lseg qnode pre hd tl ∗ lseg qnode [e] tl Val.Vnullptr) h) :
    fifoBody (pre ++ [e]) hd tl h := by
  cases hc : pre ++ [e] with
  | nil => simp at hc
  | cons q c => exact ⟨pre, e, hc.symm, hp, hs⟩

/-- The one-element queue. -/
theorem fifoBody_single {bk : Block} {o : Integers.Ptrofs} {e : QElem} {h : Heap}
    (hp : e.ptr = .Vptr bk o) (hq : qnode bk (Integers.Ptrofs.unsigned o) e Val.Vnullptr h) :
    fifoBody [e] (.Vptr bk o) (.Vptr bk o) h := by
  have := fifoBody_snoc (pre := []) hp ⟨Heap.emp, h, Heap.disjoint_emp_left _,
    (Heap.emp_union _).symm, ⟨rfl, rfl⟩, bk, o, Val.Vnullptr, rfl, h, Heap.emp,
    Heap.disjoint_emp_right _, (Heap.union_emp _).symm, hq, rfl, rfl⟩
  simpa using this

/-- Taking the first element off a queue (`fifo_get`): its node, and the rest
    of the queue starting at its link. -/
theorem fifoBody_cons {e : QElem} {c : List QElem} {hd tl : Val} {h : Heap}
    (hb : fifoBody (e :: c) hd tl h) :
    ∃ bk o u, hd = .Vptr bk o ∧ IsLink u
      ∧ (qnode bk (Integers.Ptrofs.unsigned o) e u ∗ fifoBody c u tl) h := by
  obtain ⟨pre, e', heq, hptr, hs⟩ := hb
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨h1, h2, hd12, rfl, ⟨rfl, rfl⟩, b, o, u, rfl, h3, h4, hd34, rfl, hq, ⟨rfl, rfl⟩⟩ := hs
    refine ⟨b, o, Val.Vnullptr, rfl, Or.inl rfl, h3, Heap.emp, Heap.disjoint_emp_right _, ?_, hq,
      rfl, rfl⟩
    simp [Heap.emp_union]
  | cons p0 pre' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hs' := hs
    rw [sep_comm_eq] at hs'
    obtain ⟨-, -, -, -, ⟨bt, ot, -, rfl, -⟩, -⟩ := hs'
    obtain ⟨b, o, u, rfl, h1, h2, hd12, rfl, hq, hrest⟩ := lseg_cons_front hs
    have hu : IsLink u := by
      obtain ⟨h3, h4, -, rfl, hl, -⟩ := hrest
      exact isLink_of_lseg (Or.inr ⟨bt, ot, rfl⟩) hl
    exact ⟨b, o, u, rfl, hu, h1, h2, hd12, rfl, hq, fifoBody_snoc hptr hrest⟩

/-- The last node of a non-empty queue (`fifo_put`). -/
theorem fifoBody_last {c : List QElem} {hd tl : Val} {h : Heap} (hc : c ≠ [])
    (hb : fifoBody c hd tl h) :
    ∃ pre e0 bt ot, c = pre ++ [e0] ∧ tl = .Vptr bt ot
      ∧ (qnode bt (Integers.Ptrofs.unsigned ot) e0 Val.Vnullptr ∗ lseg qnode pre hd tl) h := by
  cases c with
  | nil => exact absurd rfl hc
  | cons q c =>
    obtain ⟨pre, e0, heq, -, h1, h2, hd12, rfl, hl, bt, ot, u, rfl, h3, h4, hd34, rfl, hq,
      ⟨rfl, rfl⟩⟩ := hb
    refine ⟨pre, e0, bt, ot, heq, rfl, h3, h1, Heap.disjoint_comm ?_, ?_, hq, hl⟩
    · rw [Heap.union_emp] at hd12; exact hd12
    · rw [Heap.union_emp]; exact Heap.union_comm (by rwa [Heap.union_emp] at hd12)

/-- Appending a node after the last one (`fifo_put`). -/
theorem fifoBody_put {pre : List QElem} {e0 e : QElem} {hd : Val} {bt pb : Block}
    {ot po : Integers.Ptrofs} {h1 h2 : Heap}
    (hs : (qnode bt (Integers.Ptrofs.unsigned ot) e0 (.Vptr pb po)
      ∗ lseg qnode pre hd (.Vptr bt ot)) h1)
    (hq : qnode pb (Integers.Ptrofs.unsigned po) e Val.Vnullptr h2) (hp : e.ptr = .Vptr pb po)
    (hdj : Heap.disjoint h1 h2) :
    fifoBody (pre ++ [e0] ++ [e]) hd (.Vptr pb po) (Heap.union h1 h2) := by
  rw [sep_comm_eq] at hs
  have hl := lseg_snoc qnode e0 _ bt ot pre hd h1 hs
  exact fifoBody_snoc hp ⟨h1, h2, hdj, rfl, hl, pb, po, Val.Vnullptr, rfl, h2, Heap.emp,
    Heap.disjoint_emp_right _, (Heap.union_emp _).symm, hq, rfl, rfl⟩

/-- The head of a queue is null exactly when the queue is empty. -/
theorem fifoBody_hd {c : List QElem} {hd tl : Val} {h : Heap} (hb : fifoBody c hd tl h) :
    (c = [] ∧ hd = Val.Vnullptr) ∨ (c ≠ [] ∧ ∃ b o, hd = .Vptr b o) := by
  cases c with
  | nil => exact Or.inl ⟨rfl, hb.1⟩
  | cons q c =>
    obtain ⟨b, o, -, rfl, -⟩ := fifoBody_cons hb
    exact Or.inr ⟨List.cons_ne_nil _ _, b, o, rfl⟩

/-- The nodes of the queue in `fifoH`, with the memory they agree with. -/
theorem fifoH_body {qb : Block} {hd tl : Val} {c : List QElem} {F : HProp} {h : Heap} {m : Mem}
    (hH : (fifoH qb hd tl c ∗ F) h) (hag : Heap.Agrees h m) :
    ∃ h4, fifoBody c hd tl h4 ∧ Heap.Agrees h4 m := by
  revert hag
  obtain ⟨-, -, -, rfl, ⟨a1, -, hda, rfl, -, a2, -, hdb, rfl, -, a3, a4, hdc, rfl, -, hb⟩, -⟩ := hH
  intro hag
  exact ⟨a4, hb, Heap.Agrees_union_right hdc (Heap.Agrees_union_right hdb
    (Heap.Agrees_union_right hda (Heap.Agrees_union_left hag)))⟩

/-- The head of the queue in `fifoH`: null for the empty queue, a weakly valid
    pointer otherwise. -/
theorem fifoH_head {qb : Block} {hd tl : Val} {c : List QElem} {F : HProp} {h : Heap} {m : Mem}
    (hH : (fifoH qb hd tl c ∗ F) h) (hag : Heap.Agrees h m) :
    hd = Val.Vnullptr ∨ ∃ b o, hd = .Vptr b o
      ∧ Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true := by
  obtain ⟨h4, hb, hag4⟩ := fifoH_body hH hag
  rcases fifoBody_head (F := emp) ⟨h4, Heap.emp, Heap.disjoint_emp_right _,
    (Heap.union_emp _).symm, hb, rfl⟩ hag4 with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-! ## The expressions of the queue's functions -/

/-- `(void *) 0` -/
abbrev nullE : Expr := .Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)
/-- `x->head` -/
abbrev headOf (x : Ident) : Expr := .Efield (.Ederef (.Etempvar x (tptr tfifo)) tfifo) _head (tptr telem)
/-- `x->tail` -/
abbrev tailOf (x : Ident) : Expr := .Efield (.Ederef (.Etempvar x (tptr tfifo)) tfifo) _tail (tptr telem)
/-- `x->next` -/
abbrev nextOf (x : Ident) : Expr := .Efield (.Ederef (.Etempvar x (tptr telem)) telem) _next (tptr telem)
/-- `x == NULL` -/
abbrev eqNull (x : Ident) : Expr := .Ebinop .Oeq (.Etempvar x (tptr telem)) nullE tint

/-! ## Evaluating the queue's expressions -/

section
variable {ge : CGenv} {ce : CompositeEnv} (QC : QueueCenv ce) (hcenv : ge.genv_cenv = ce)
include QC hcenv

/-- `x->head` for the `struct fifo` at `qb`. -/
theorem eval_head {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {qb : Block} {hd : Val}
    {F : HProp} {h : Heap} (hx : le.get x = some (.Vptr qb Integers.Ptrofs.zero))
    (hl : IsLink hd) (hH : (mapsto .Mint64 .Freeable qb 0 hd ∗ F) h) (hag : Heap.Agrees h m) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar x (tptr tfifo)) tfifo) _head (tptr telem)) hd := by
  have := eval_field_mapsto QC.fifoL hcenv (e := e) (chunk := .Mint64) (ty := tptr telem) QC.fifoL.off_head (Int.le_refl 0)
    (by rw [uz]; decide) rfl rfl hx (by rw [uz]; exact hH) hag
  rw [loadResult_link hl] at this
  exact this

/-- `x->tail` for the `struct fifo` at `qb`. -/
theorem eval_tailQ {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {qb : Block} {tl : Val}
    {F : HProp} {h : Heap} (hx : le.get x = some (.Vptr qb Integers.Ptrofs.zero))
    (hl : IsLink tl) (hH : (mapsto .Mint64 .Freeable qb 8 tl ∗ F) h) (hag : Heap.Agrees h m) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar x (tptr tfifo)) tfifo) _tail (tptr telem)) tl := by
  have := eval_field_mapsto QC.fifoL hcenv (e := e) (chunk := .Mint64) (ty := tptr telem) QC.fifoL.off_tail (by decide)
    (by rw [uz]; decide) rfl rfl hx (by rw [uz]; exact hH) hag
  rw [loadResult_link hl] at this
  exact this

/-- `x->next` for the element at `bk + o`. -/
theorem eval_next {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {bk : Block}
    {o : Integers.Ptrofs} {a : Integers.Int} {b u : Val} {F : HProp} {h : Heap}
    (hx : le.get x = some (.Vptr bk o)) (hu : IsLink u)
    (hH : (elemAt bk (Integers.Ptrofs.unsigned o) a b u ∗ F) h) (hag : Heap.Agrees h m) :
    EvalExpr ge e le m (.Efield (.Ederef (.Etempvar x (tptr telem)) telem) _next (tptr telem)) u := by
  rw [elemAt, sep_assoc_eq] at hH
  exact eval_tail QC.elemL hcenv rfl hx hu hH hag

/-- **`x->head = y;`** -/
theorem triple_store_head (fe : EntryRel) (f : Function) (E : Env) (l : List (Ident × Val))
    (F : HProp) (x y : Ident) (qb : Block) (vold w : Val)
    (hx : ∀ le, TempsHold l le → le.get x = some (.Vptr qb Integers.Ptrofs.zero))
    (hy : ∀ le, TempsHold l le → le.get y = some w) (hw : IsLink w) :
    Triple ge fe f (LocalSt E l (mapsto .Mint64 .Freeable qb 0 vold ∗ F))
      (.Sassign (headOf x) (.Etempvar y (tptr telem)))
      (.only (LocalSt E l (mapsto .Mint64 .Freeable qb 0 w ∗ F))) := by
  have := triple_store_field QC.fifoL hcenv fe f E l F x _head 0 .Mint64 (tptr telem)
    (.Etempvar y (tptr telem)) .Freeable qb Integers.Ptrofs.zero vold w QC.fifoL.off_head
    (Int.le_refl 0) (by decide) rfl rfl hx
    (fun le m hT => ⟨w, EvalExpr.Etempvar _ _ _ (hy le hT), semCast_ptr_ptr m w _ _ _ _ hw⟩)
  rw [uz] at this
  exact this

/-- **`x->tail = y;`** -/
theorem triple_store_tailQ (fe : EntryRel) (f : Function) (E : Env) (l : List (Ident × Val))
    (F : HProp) (x y : Ident) (qb : Block) (vold w : Val)
    (hx : ∀ le, TempsHold l le → le.get x = some (.Vptr qb Integers.Ptrofs.zero))
    (hy : ∀ le, TempsHold l le → le.get y = some w) (hw : IsLink w) :
    Triple ge fe f (LocalSt E l (mapsto .Mint64 .Freeable qb 8 vold ∗ F))
      (.Sassign (tailOf x) (.Etempvar y (tptr telem)))
      (.only (LocalSt E l (mapsto .Mint64 .Freeable qb 8 w ∗ F))) := by
  have := triple_store_field QC.fifoL hcenv fe f E l F x _tail 8 .Mint64 (tptr telem)
    (.Etempvar y (tptr telem)) .Freeable qb Integers.Ptrofs.zero vold w QC.fifoL.off_tail
    (by decide) (by decide) rfl rfl hx
    (fun le m hT => ⟨w, EvalExpr.Etempvar _ _ _ (hy le hT), semCast_ptr_ptr m w _ _ _ _ hw⟩)
  rw [uz] at this
  exact this

/-- **`x->next = a;`** for the element at `bk + o`. -/
theorem triple_store_next (fe : EntryRel) (f : Function) (E : Env) (l : List (Ident × Val))
    (F : HProp) (x : Ident) (a : Expr) (bk : Block) (o : Integers.Ptrofs) (av : Integers.Int)
    (bv u w : Val) (hx : ∀ le, TempsHold l le → le.get x = some (.Vptr bk o))
    (ha : ∀ le m, TempsHold l le →
      ∃ v, EvalExpr ge E le m a v ∧ Cop.semCast v (typeof a) (tptr telem) m = some w) :
    Triple ge fe f (LocalSt E l (elemAt bk (Integers.Ptrofs.unsigned o) av bv u ∗ F))
      (.Sassign (nextOf x) a)
      (.only (LocalSt E l (elemAt bk (Integers.Ptrofs.unsigned o) av bv w ∗ F))) := by
  refine Sep.triple_conseq ge fe f (triple_store_tail_expr QC.elemL hcenv fe f
    (fun e le => e = E ∧ TempsHold l le)
    (mapsto .Mint32 .Freeable bk (Integers.Ptrofs.unsigned o + 4) bv ∗ F) x a .Freeable
    bk o av u w rfl (fun _ le h => hx le h.2) (fun e le m h => by obtain ⟨rfl, hT⟩ := h; exact ha le m hT))
    (fun e le hp hP => ?_) (fun e le hp hQ => ?_) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ x => x.elim)
  · obtain ⟨he, hT, hH⟩ := hP
    rw [elemAt, sep_assoc_eq] at hH
    exact ⟨⟨he, hT⟩, hH⟩
  · obtain ⟨⟨he, hT⟩, hH⟩ := hQ
    refine ⟨he, hT, ?_⟩
    rw [elemAt, sep_assoc_eq]
    exact hH

end

/-- A node in front: its pointer, and the element. -/
theorem qnode_front {bk : Block} {X : _root_.Int} {q : QElem} {u : Val} {F : HProp} {h : Heap}
    (hq : (qnode bk X q u ∗ F) h) :
    q.ptr = .Vptr bk (Integers.Ptrofs.repr X) ∧ (elemAt bk X q.a q.b u ∗ F) h := by
  rw [qnode, sep_assoc_eq] at hq
  exact pure_sep_elim hq

/-- `x == NULL` for `x` null or a weakly valid pointer. -/
theorem eval_eq_null {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {v : Val}
    (hx : le.get x = some v)
    (hv : v = Val.Vnullptr ∨ ∃ b o, v = .Vptr b o
      ∧ Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    EvalExpr ge e le m (.Ebinop .Oeq (.Etempvar x (tptr telem))
      (.Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)) tint)
      (Val.ofBool (decide (v = Val.Vnullptr))) :=
  EvalExpr.Ebinop .Oeq _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx) eval_null_cast
    (semBinop_eq_null _ m _ _ _ _ _ hv)

/-! ## `surely_malloc` -/

def callMalloc : Stmt :=
  .Scall (some _t'1) (.Evar _malloc (Ty.Tfunction [tulong] (tptr tvoid) cc_default))
    [.Etempvar _n tulong]
def ifExit : Stmt :=
  .Sifthenelse (.Eunop .Onotbool (.Etempvar _p (tptr tvoid)) tint)
    (.Scall none (.Evar _exit (Ty.Tfunction [tint] tvoid cc_default))
      [.Econst_int (Integers.Int.repr 1) tint])
    .Sskip
def smBody : Stmt :=
  .Ssequence (.Ssequence callMalloc (.Sset _p (.Etempvar _t'1 (tptr tvoid))))
    (.Ssequence ifExit (.Sreturn (some (.Etempvar _p (tptr tvoid)))))

theorem surely_malloc_body_eq : f_surely_malloc.fn_body = smBody := rfl

/-- **`surely_malloc` satisfies `surely_malloc_spec`** (VST's
    `body_surely_malloc`), which here is `malloc`'s own specification: a fresh
    block of `sz` bytes at offset zero, with its token.  `malloc` is the
    program's external function of that name. -/
theorem surely_malloc_satisfies (ge : CGenv) (sz : Integers.Ptrofs) (bm : Block)
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_surely_malloc) (mallocSpec sz)
      [Val.Vptrofs sz] := by
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_surely_malloc _ _
    (LocalSt emptyEnv [(_n, Val.Vptrofs sz)] emp) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq; rfl
  rw [surely_malloc_body_eq]
  -- `t'1 = malloc(n); p = t'1;`
  refine triple_seq ge _ f_surely_malloc _ (fun e le hp => ∃ bb, LocalSt emptyEnv
    [(_p, .Vptr bb Integers.Ptrofs.zero)] (mallocToken bb sz ∗ mallocPayload bb sz) e le hp)
    _ _ _ ?_ ?_
  · refine triple_fallthrough ge _ f_surely_malloc _ _ _ _ ?_ (fun _ _ _ x => x)
    refine triple_seq_only ge _ f_surely_malloc (Q := fun e le hp => ∃ bb, LocalSt emptyEnv
      [(_t'1, .Vptr bb Integers.Ptrofs.zero)] (mallocToken bb sz ∗ mallocPayload bb sz) e le hp)
      ?_ ?_
    · refine triple_call_at ge _ f_surely_malloc (mallocSpec sz) (some _t'1) _ _ _ _ bm _ hfindM
        rfl rfl (fun e le hp m hP _ => ?_)
      obtain ⟨rfl, hT, rfl⟩ := hP
      refine ⟨[Val.Vptrofs sz], Heap.emp, Heap.emp, Heap.disjoint_emp_left _,
        (Heap.emp_union _).symm, eval_callee_global (PTree.gempty _) hsymM rfl,
        EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (v := Val.Vptrofs sz) (by simp))) rfl
          EvalExprlist.nil, ⟨rfl, rfl⟩, Sep.malloc_satisfies ge _ sz _ _ _,
        fun v h1' hpost hd => ?_⟩
      obtain ⟨bb, hb⟩ := hpost
      obtain ⟨rfl, hb'⟩ := pure_sep_elim hb
      exact ⟨bb, rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_nil _),
        by rw [Heap.union_emp]; exact hb'⟩
    · refine triple_exists ge _ f_surely_malloc _ _ _ (fun bb => ?_)
      exact triple_conseq ge _ f_surely_malloc (triple_set_local ge _ f_surely_malloc emptyEnv _ []
        _ _p _ (.Vptr bb Integers.Ptrofs.zero) (fun _ hq => by simp at hq) (by temps_ne)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
        (fun _ _ _ x => x) (fun e le hp h => ⟨bb, h⟩) (fun _ _ _ x => x.elim)
        (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ f_surely_malloc _ _ _ (fun bb => ?_)
  -- `if (!p) exit(1);`
  refine triple_seq_only ge _ f_surely_malloc (triple_if_local ge _ f_surely_malloc emptyEnv _ _ _
    false _ _ _ (fun le m hp hT hH hag => ?_) (triple_skip ge _ f_surely_malloc _)) ?_
  · obtain ⟨h1, h2, hd, rfl, ht, -⟩ := hH
    have hv := mallocToken_weakValidPointer ht (Heap.Agrees_union_left hag)
    exact ⟨_, eval_notbool_validptr (hT.get (v := .Vptr bb Integers.Ptrofs.zero) (by simp)) (by rw [ptrofs_unsigned_zero]; exact hv),
      boolVal_ofBool_int m false⟩
  -- `return p;`
  refine triple_return_local ge _ f_surely_malloc _ _ _ _ (.Vptr bb Integers.Ptrofs.zero)
    (.Vptr bb Integers.Ptrofs.zero) (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
    (fun m => semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) (fun hp hH => ⟨bb, ?_⟩)
  exact pure_sep_intro rfl hH

end VST.Verif.Queue
