/-
  Port of VST's `progs/verif_queue.v`, part 3: `fifo_put` of
  `vst/progs/queue.c` meets `fifo_put_spec`.

      void fifo_put (struct fifo *Q, struct elem *p) {
        struct elem *h, *t;
        p->next=NULL;
        h = Q->head;
        if (h==NULL) { Q->head=p; Q->tail=p; }
        else { t = Q->tail; t->next=p; Q->tail=p; }
      }

      fifo_put_spec: WITH q, contents, p  PRE [tptr t_struct_fifo, tptr t_struct_elem]
        PARAMS (q; p)
        SEP (fifo contents q; list_cell QS Qsh (Vundef, Vundef) p;
             field_at_ Ews t_struct_elem [StructField _next] p)
        POST [tvoid] SEP (fifo (contents ++ p :: nil) q)

  The element `p` is `elemRep e` (its fields `a`, `b` and a `next` field with
  any contents); afterwards it is the last node of the queue.
-/
import VST.progs.verif_queue
open CC CC.Sep CC.HProp
open Queue

namespace VST.Verif.Queue

/-- `fifo_put_spec` -/
def fifoPutSpec (c : List QElem) (q : Val) (e : QElem) : Sep.FunSpec where
  tyargs := [tptr tfifo, tptr telem]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => vargs = [q, e.ptr] ∧ (fifo c q ∗ elemRep e) hp
  post := fun v hp => v = .Vundef ∧ fifo (c ++ [e]) q hp
  measure := fun _ => 0

/-- `Q->head = p; Q->tail = p;` -/
def putThen : Stmt :=
  .Ssequence (.Sassign (headOf _Q) (.Etempvar _p (tptr telem)))
    (.Sassign (tailOf _Q) (.Etempvar _p (tptr telem)))

/-- `t = Q->tail; t->next = p; Q->tail = p;` -/
def putElse : Stmt :=
  .Ssequence (.Sset _t (tailOf _Q))
    (.Ssequence (.Sassign (nextOf _t) (.Etempvar _p (tptr telem)))
      (.Sassign (tailOf _Q) (.Etempvar _p (tptr telem))))

def putBody : Stmt :=
  .Ssequence (.Sassign (nextOf _p) nullE)
    (.Ssequence (.Sset _h (headOf _Q)) (.Sifthenelse (eqNull _h) putThen putElse))

theorem triple_pre_sep {ge : CGenv} {fe : EntryRel} {f : Function} {E : Env}
    {l : List (Ident × Val)} {H H' : HProp} {s : Stmt} {R : Sep.ExitConds} (heq : H' = H)
    (h : Triple ge fe f (LocalSt E l H) s R) : Triple ge fe f (LocalSt E l H') s R := by
  subst heq; exact h

section
variable (ge : CGenv) {ce : CompositeEnv} (QC : QueueCenv ce) (hcenv : ge.genv_cenv = ce) (c : List QElem) (e : QElem)
  (qb pb : Block) (po : Integers.Ptrofs)

/-- The temporaries of `fifo_put` once `h` is read. -/
abbrev TP (hd : Val) : List (Ident × Val) :=
  [(_h, hd), (_Q, .Vptr qb Integers.Ptrofs.zero), (_p, .Vptr pb po)]

/-- The normal exit of `fifo_put`'s body. -/
abbrev PutPost : Sep.ExitConds :=
  { normal := fun e' _ hp => e' = emptyEnv ∧ (fifoPutSpec c (.Vptr qb Integers.Ptrofs.zero) e).post
      .Vundef hp,
    brk := Assn.no, cont := Assn.no, ret := (fifoPutSpec c (.Vptr qb Integers.Ptrofs.zero) e).post }

include QC hcenv in
/-- The empty queue: `Q->head = p; Q->tail = p;` -/
theorem put_then (tl : Val) (hp : e.ptr = .Vptr pb po) :
    Triple ge (FunctionEntry2 ge) f_fifo_put
      (LocalSt emptyEnv (TP qb pb po Val.Vnullptr)
        (elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr
          ∗ fifoH qb Val.Vnullptr tl []))
      putThen (PutPost [] e qb) := by
  refine triple_pre_sep (H := mapsto .Mint64 .Freeable qb 0 Val.Vnullptr
      ∗ (mapsto .Mint64 .Freeable qb 8 tl ∗ (mallocToken qb sz16
        ∗ (elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr
          ∗ fifoBody [] Val.Vnullptr tl)))) (by unfold fifoH; sep_cancel) ?_
  refine triple_seq_only ge _ f_fifo_put (triple_store_head QC hcenv _ f_fifo_put emptyEnv _ _ _Q _p
    qb _ (.Vptr pb po) (fun le hT => hT.get (by simp)) (fun le hT => hT.get (by simp))
    (Or.inr ⟨_, _, rfl⟩)) ?_
  refine triple_pre_sep (H := mapsto .Mint64 .Freeable qb 8 tl
      ∗ (mapsto .Mint64 .Freeable qb 0 (.Vptr pb po) ∗ (mallocToken qb sz16
        ∗ (elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr
          ∗ fifoBody [] Val.Vnullptr tl)))) (sep_left_comm_eq _ _ _) ?_
  refine Sep.triple_conseq ge _ f_fifo_put (triple_store_tailQ QC hcenv _ f_fifo_put emptyEnv _ _ _Q
    _p qb _ (.Vptr pb po) (fun le hT => hT.get (by simp)) (fun le hT => hT.get (by simp))
    (Or.inr ⟨_, _, rfl⟩)) (fun _ _ _ x => x) (fun e' le hp' hQ => ?_)
    (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  obtain ⟨rfl, -, hH⟩ := hQ
  refine ⟨rfl, rfl, qb, .Vptr pb po, .Vptr pb po, rfl, Or.inr ⟨_, _, rfl⟩, Or.inr ⟨_, _, rfl⟩, ?_⟩
  rw [sep_left_comm_eq, show fifoBody [] Val.Vnullptr tl = ⌜Val.Vnullptr = Val.Vnullptr⌝ from rfl,
    sep_comm_eq (elemAt _ _ _ _ _), pure_true_sep_eq rfl] at hH
  obtain ⟨h1, h2, hd12, rfl, hm0, h3, h4, hd34, rfl, hm8, h5, h6, hd56, rfl, ht, hel⟩ := hH
  exact ⟨h1, _, hd12, rfl, hm0, h3, _, hd34, rfl, hm8, h5, h6, hd56, rfl, ht,
    fifoBody_single hp (qnode_of_elemAt hp hel)⟩

include QC hcenv in
/-- A non-empty queue: `t = Q->tail; t->next = p; Q->tail = p;` -/
theorem put_else (hd tl : Val) (hc : c ≠ []) (hl1 : IsLink hd) (hp : e.ptr = .Vptr pb po) :
    Triple ge (FunctionEntry2 ge) f_fifo_put
      (LocalSt emptyEnv (TP qb pb po hd)
        (elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr ∗ fifoH qb hd tl c))
      putElse (PutPost c e qb) := by
  -- the last node of the queue
  refine triple_pre ge _ f_fifo_put (P := fun e' le hp' => ∃ pre e0 bt ot,
      ∃ _ : c = pre ++ [e0] ∧ tl = .Vptr bt ot
        ∧ e0.ptr = .Vptr bt (Integers.Ptrofs.repr (Integers.Ptrofs.unsigned ot)),
      LocalSt emptyEnv (TP qb pb po hd)
        (mapsto .Mint64 .Freeable qb 8 tl
          ∗ (elemAt bt (Integers.Ptrofs.unsigned ot) e0.a e0.b Val.Vnullptr
            ∗ (mapsto .Mint64 .Freeable qb 0 hd ∗ (mallocToken qb sz16
              ∗ (lseg qnode pre hd tl
                ∗ elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr))))) e' le hp')
    (fun e' le hp' hP => ?_) ?_
  · obtain ⟨he, hT, h1, h2, hd12, rfl, hel, a1, a234, hda, rfl, m0, a2, a34, hdb, rfl, m8, a3, a4,
      hdc, rfl, tok, hb⟩ := hP
    obtain ⟨pre, e0, bt, ot, hc', rfl, b1, b2, hdb12, rfl, hq, hl⟩ := fifoBody_last hc hb
    obtain ⟨hptr, hel0⟩ := pure_sep_elim hq
    refine ⟨pre, e0, bt, ot, ⟨hc', rfl, hptr⟩, he, hT, ?_⟩
    have H : (elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr
        ∗ (mapsto .Mint64 .Freeable qb 0 hd ∗ (mapsto .Mint64 .Freeable qb 8 (.Vptr bt ot)
          ∗ (mallocToken qb sz16 ∗ (elemAt bt (Integers.Ptrofs.unsigned ot) e0.a e0.b Val.Vnullptr
            ∗ lseg qnode pre hd (.Vptr bt ot))))))
        (Heap.union h1 (Heap.union a1 (Heap.union a2 (Heap.union a3 (Heap.union b1 b2))))) :=
      ⟨h1, _, hd12, rfl, hel, a1, _, hda, rfl, m0, a2, _, hdb, rfl, m8, a3, _, hdc, rfl, tok, b1,
        b2, hdb12, rfl, hel0, hl⟩
    have heq : (elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr
        ∗ (mapsto .Mint64 .Freeable qb 0 hd ∗ (mapsto .Mint64 .Freeable qb 8 (.Vptr bt ot)
          ∗ (mallocToken qb sz16 ∗ (elemAt bt (Integers.Ptrofs.unsigned ot) e0.a e0.b Val.Vnullptr
            ∗ lseg qnode pre hd (.Vptr bt ot))))))
        = (mapsto .Mint64 .Freeable qb 8 (.Vptr bt ot)
          ∗ (elemAt bt (Integers.Ptrofs.unsigned ot) e0.a e0.b Val.Vnullptr
            ∗ (mapsto .Mint64 .Freeable qb 0 hd ∗ (mallocToken qb sz16
              ∗ (lseg qnode pre hd (.Vptr bt ot)
                ∗ elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr))))) := by
      sep_cancel
    rw [heq] at H
    exact H
  refine triple_exists ge _ f_fifo_put _ _ _ (fun pre => ?_)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun e0 => ?_)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun bt => ?_)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun ot => ?_)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun ⟨hc', htl, hptr⟩ => ?_)
  subst htl
  -- `t = Q->tail;`
  refine triple_seq_only ge _ f_fifo_put (triple_set_local ge _ f_fifo_put emptyEnv _
    (TP qb pb po hd) _ _t _ (.Vptr bt ot) (fun _ h => h) (by temps_ne)
    (fun le m hp' hT hH hag => eval_tailQ QC hcenv (hT.get (v := .Vptr qb Integers.Ptrofs.zero)
      (by simp)) (Or.inr ⟨_, _, rfl⟩) hH hag)) ?_
  -- `t->next = p;`
  refine triple_pre_sep (sep_left_comm_eq _ _ _) ?_
  refine triple_seq_only ge _ f_fifo_put (triple_store_next QC hcenv _ f_fifo_put emptyEnv _ _ _t
    (.Etempvar _p (tptr telem)) bt ot e0.a e0.b Val.Vnullptr (.Vptr pb po)
    (fun le hT => hT.get (by simp))
    (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (v := .Vptr pb po) (by simp)),
      semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)⟩)) ?_
  -- `Q->tail = p;`
  refine triple_pre_sep (sep_left_comm_eq _ _ _) ?_
  refine Sep.triple_conseq ge _ f_fifo_put (triple_store_tailQ QC hcenv _ f_fifo_put emptyEnv _ _ _Q
    _p qb _ (.Vptr pb po) (fun le hT => hT.get (by simp)) (fun le hT => hT.get (by simp))
    (Or.inr ⟨_, _, rfl⟩)) (fun _ _ _ x => x) (fun e' le hp' hQ => ?_)
    (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  obtain ⟨rfl, -, hH⟩ := hQ
  refine ⟨rfl, rfl, qb, hd, .Vptr pb po, rfl, hl1, Or.inr ⟨_, _, rfl⟩, ?_⟩
  have heq : (mapsto .Mint64 .Freeable qb 8 (.Vptr pb po)
      ∗ (elemAt bt (Integers.Ptrofs.unsigned ot) e0.a e0.b (.Vptr pb po)
        ∗ (mapsto .Mint64 .Freeable qb 0 hd ∗ (mallocToken qb sz16
          ∗ (lseg qnode pre hd (.Vptr bt ot)
            ∗ elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr)))))
      = (mapsto .Mint64 .Freeable qb 0 hd ∗ (mapsto .Mint64 .Freeable qb 8 (.Vptr pb po)
        ∗ (mallocToken qb sz16 ∗ ((elemAt bt (Integers.Ptrofs.unsigned ot) e0.a e0.b (.Vptr pb po)
          ∗ lseg qnode pre hd (.Vptr bt ot))
            ∗ elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b Val.Vnullptr)))) := by
    sep_cancel
  rw [heq] at hH
  obtain ⟨h1, -, hd1, rfl, hm0, h2, -, hd2, rfl, hm8, h3, -, hd3, rfl, ht, -, h6, hd45, rfl,
    ⟨h4, h5, hd4, rfl, hel0, hl⟩, hel⟩ := hH
  subst hc'
  exact ⟨h1, _, hd1, rfl, hm0, h2, _, hd2, rfl, hm8, h3, _, hd3, rfl, ht,
    fifoBody_put ⟨h4, h5, hd4, rfl, qnode_of_elemAt (q := e0) (o := ot)
      (by rw [Integers.Ptrofs.repr_unsigned] at hptr; exact hptr) hel0, hl⟩
      (qnode_of_elemAt hp hel) hp hd45⟩

end

/-- **`fifo_put` satisfies `fifo_put_spec`** (VST's `body_fifo_put`). -/
theorem fifo_put_satisfies (ge : CGenv) {ce : CompositeEnv} (QC : QueueCenv ce) (hcenv : ge.genv_cenv = ce)
    (c : List QElem) (q : Val) (e : QElem) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fifo_put) (fifoPutSpec c q e)
      [q, e.ptr] := by
  refine Sep.satisfies_internal_noVars_void ge _ f_fifo_put _ _
    (LocalSt emptyEnv [(_Q, q), (_p, e.ptr)] (fifo c q ∗ elemRep e)) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  rw [show f_fifo_put.fn_body = putBody from rfl]
  refine triple_fifo_open ge _ f_fifo_put _ _ c q _ _ _ (fun qb hd tl hq hl1 _ => ?_)
  subst hq
  -- the element `p`
  refine triple_pre ge _ f_fifo_put (P := fun e' le hp => ∃ pb po u0,
      ∃ _ : e.ptr = .Vptr pb po
        ∧ ((c = [] ∧ hd = Val.Vnullptr) ∨ (c ≠ [] ∧ ∃ b o, hd = .Vptr b o)),
      LocalSt emptyEnv [(_Q, .Vptr qb Integers.Ptrofs.zero), (_p, .Vptr pb po)]
        (elemAt pb (Integers.Ptrofs.unsigned po) e.a e.b u0 ∗ fifoH qb hd tl c) e' le hp)
    (fun e' le hp hP => ?_) ?_
  · obtain ⟨he, hT, h1, h2, hd12, rfl, hF, pb, po, u0, hp, he2⟩ := hP
    obtain ⟨h4, hb⟩ : ∃ h4, fifoBody c hd tl h4 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h4, _, _, _, hb⟩ := hF
      exact ⟨h4, hb⟩
    refine ⟨pb, po, u0, ⟨hp, fifoBody_hd hb⟩, he, ?_, h2, h1, Heap.disjoint_comm hd12,
      Heap.union_comm hd12, he2, hF⟩
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact hT.get (by simp)
    · rw [← hp]; exact hT.get (by simp)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun pb => ?_)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun po => ?_)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun u0 => ?_)
  refine triple_exists ge _ f_fifo_put _ _ _ (fun ⟨hp, hc⟩ => ?_)
  -- `p->next = NULL;`
  refine triple_seq_only ge _ f_fifo_put (triple_store_next QC hcenv _ f_fifo_put emptyEnv _
    (fifoH qb hd tl c) _p nullE pb po e.a e.b u0 Val.Vnullptr (fun le hT => hT.get (by simp))
    (fun le m hT => ⟨_, eval_null_cast, semCast_ptr_ptr m _ _ _ _ _ (Or.inl rfl)⟩)) ?_
  -- `h = Q->head;`
  refine triple_seq_only ge _ f_fifo_put (triple_set_local ge _ f_fifo_put emptyEnv _
    [(_Q, .Vptr qb Integers.Ptrofs.zero), (_p, .Vptr pb po)] _ _h _ hd (fun _ h => h)
    (by temps_ne) (fun le m hp' hT hH hag => eval_head QC hcenv
      (hT.get (v := .Vptr qb Integers.Ptrofs.zero) (by simp)) hl1
      (by rw [sep_comm_eq, fifoH, sep_assoc_eq] at hH; exact hH) hag)) ?_
  rcases hc with ⟨rfl, rfl⟩ | ⟨hc, bh, oh, rfl⟩
  · -- the queue is empty: `h == NULL`
    refine triple_if_local ge _ f_fifo_put emptyEnv _ _ _ true _ _ _
      (fun le m hp' hT hH hag => ⟨_, eval_eq_null (hT.get (v := Val.Vnullptr) (by simp))
        (Or.inl rfl), by rw [decide_eq_true rfl]; exact boolVal_ofBool_int m true⟩) ?_
    exact put_then ge QC hcenv e qb pb po tl hp
  · -- the queue is not empty
    refine triple_if_local ge _ f_fifo_put emptyEnv _ _ _ false _ _ _
      (fun le m hp' hT hH hag => ?_) ?_
    · rw [sep_comm_eq] at hH
      refine ⟨_, eval_eq_null (hT.get (v := .Vptr bh oh) (by simp)) (fifoH_head hH hag), ?_⟩
      rw [decide_eq_false (by simp [Val.Vnullptr, Archi.ptr64])]
      exact boolVal_ofBool_int m false
    exact put_else ge QC hcenv c e qb pb po (.Vptr bh oh) tl hc (Or.inr ⟨_, _, rfl⟩) hp

end VST.Verif.Queue
