/-
  Port of VST's `progs/verif_queue.v`, part 2: the queue operations of
  `vst/progs/queue.c` meet their specifications.

      int fifo_empty (struct fifo *Q) {
        struct elem *h;
        h = Q->head;
        return (h == NULL);
      }

      struct elem *fifo_get (struct fifo *Q) {
        struct elem *h, *n;
        h=Q->head;
        n=h->next;
        Q->head=n;
        return h;
      }

      void fifo_put (struct fifo *Q, struct elem *p) {
        struct elem *h, *t;
        p->next=NULL;
        h = Q->head;
        if (h==NULL) { Q->head=p; Q->tail=p; }
        else { t = Q->tail; t->next=p; Q->tail=p; }
      }

  VST's specifications:

      fifo_empty_spec: WITH q, contents  PRE [tptr t_struct_fifo] PARAMS (q)
        SEP (fifo contents q)
        POST [tint] RETURN (if isnil contents then Vtrue else Vfalse) SEP (fifo contents q)
      fifo_get_spec: WITH q, contents, p  PRE [tptr t_struct_fifo] PARAMS (q)
        SEP (fifo (p :: contents) q)
        POST [tptr t_struct_elem] RETURN (p)
        SEP (fifo contents q; list_cell QS Qsh (Vundef, Vundef) p;
             field_at_ Ews t_struct_elem [StructField _next] p)
      fifo_put_spec: WITH q, contents, p  PRE [tptr t_struct_fifo, tptr t_struct_elem]
        PARAMS (q; p)
        SEP (fifo contents q; list_cell QS Qsh (Vundef, Vundef) p;
             field_at_ Ews t_struct_elem [StructField _next] p)
        POST [tvoid] SEP (fifo (contents ++ p :: nil) q)

  The representation is the one of `verif_queue_rep`: the elements of
  `contents` are `QElem`s, and an element outside the queue is `elemRep`.
-/
import VST.progs.verif_queue_rep
open CC CC.Sep CC.HProp
open Queue

namespace VST.Verif.Queue

/-! ## Opening `fifo` -/

theorem triple_fifo_open (ge : CGenv) (fe : EntryRel) (f : Function) (E : Env)
    (l : List (Ident × Val)) (c : List QElem) (q : Val) (F : HProp) (s : Stmt) (R : Sep.ExitConds)
    (h : ∀ qb hd tl, q = .Vptr qb Integers.Ptrofs.zero → IsLink hd → IsLink tl →
      Triple ge fe f (LocalSt E l (fifoH qb hd tl c ∗ F)) s R) :
    Triple ge fe f (LocalSt E l (fifo c q ∗ F)) s R := by
  refine triple_pre ge fe f (P := fun e le hp => ∃ qb hd tl,
      ∃ _ : q = .Vptr qb Integers.Ptrofs.zero ∧ IsLink hd ∧ IsLink tl,
      LocalSt E l (fifoH qb hd tl c ∗ F) e le hp) (fun e le hp hP => ?_) ?_
  · obtain ⟨he, hT, h1, h2, hd, heq, ⟨qb, hd', tl, hq, hl1, hl2, hH⟩, hF⟩ := hP
    exact ⟨qb, hd', tl, ⟨hq, hl1, hl2⟩, he, hT, h1, h2, hd, heq, hH, hF⟩
  refine triple_exists ge fe f _ _ _ (fun qb => ?_)
  refine triple_exists ge fe f _ _ _ (fun hd => ?_)
  refine triple_exists ge fe f _ _ _ (fun tl => ?_)
  exact triple_exists ge fe f _ _ _ (fun ⟨hq, hl1, hl2⟩ => h qb hd tl hq hl1 hl2)

/-! ## `fifo_empty` -/

/-- `fifo_empty_spec` -/
def fifoEmptySpec (c : List QElem) (q : Val) : Sep.FunSpec where
  tyargs := [tptr tfifo]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [q] ∧ fifo c q hp
  post := fun v hp => v = Val.ofBool c.isEmpty ∧ fifo c q hp
  measure := fun _ => 0

def emptyBody : Stmt := .Ssequence (.Sset _h (headOf _Q)) (.Sreturn (some (eqNull _h)))

/-- **`fifo_empty` satisfies `fifo_empty_spec`** (VST's `body_fifo_empty`). -/
theorem fifo_empty_satisfies (ge : CGenv) {ce : CompositeEnv} (QC : QueueCenv ce) (hcenv : ge.genv_cenv = ce)
    (c : List QElem) (q : Val) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fifo_empty) (fifoEmptySpec c q) [q] := by
  refine Sep.satisfies_internal_noVars ge _ f_fifo_empty _ _
    (LocalSt emptyEnv [(_Q, q)] (fifo c q ∗ emp)) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, ?_, by rw [sep_emp_eq]; exact hpre.2⟩⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; rfl
  rw [show f_fifo_empty.fn_body = emptyBody from rfl]
  refine triple_fifo_open ge _ f_fifo_empty _ _ c q emp _ _ (fun qb hd tl hq hl1 _ => ?_)
  subst hq
  refine triple_seq_only ge _ f_fifo_empty (triple_set_local ge _ f_fifo_empty emptyEnv _
    [(_Q, .Vptr qb Integers.Ptrofs.zero)] _ _h _ hd (fun _ h => h) (by temps_ne)
    (fun le m hp hT hH hag => eval_head QC hcenv (hT.get (v := .Vptr qb Integers.Ptrofs.zero)
      (by simp)) hl1 (by rw [fifoH, sep_assoc_eq] at hH; exact hH) hag)) ?_
  refine triple_return_local ge _ f_fifo_empty _ _ _ _ (Val.ofBool (decide (hd = Val.Vnullptr)))
    (Val.ofBool (decide (hd = Val.Vnullptr)))
    (fun le m hp hT hH hag => eval_eq_null (hT.get (v := hd) (by simp)) (fifoH_head hH hag))
    (fun m => by cases decide (hd = Val.Vnullptr) <;> rfl) (fun hp hH => ⟨?_, ?_⟩)
  · obtain ⟨h1, -, -, rfl, ⟨-, -, -, rfl, -, -, -, -, rfl, -, -, h4, -, rfl, -, hb⟩, -⟩ := hH
    rcases fifoBody_hd hb with ⟨rfl, rfl⟩ | ⟨hc, b, o, rfl⟩
    · rfl
    · cases c with
      | nil => exact absurd rfl hc
      | cons _ _ => simp [Val.Vnullptr]
  · rw [sep_emp_eq] at hH
    exact ⟨qb, hd, tl, rfl, hl1, ‹_›, hH⟩

/-! ## `fifo_get` -/

/-- `fifo_get_spec` -/
def fifoGetSpec (c : List QElem) (q : Val) (e : QElem) : Sep.FunSpec where
  tyargs := [tptr tfifo]
  tyres := tptr telem
  cc := cc_default
  pre := fun vargs hp => vargs = [q] ∧ fifo (e :: c) q hp
  post := fun v hp => v = e.ptr ∧ (fifo c q ∗ elemRep e) hp
  measure := fun _ => 0

def getBody : Stmt :=
  .Ssequence (.Sset _h (headOf _Q)) (.Ssequence (.Sset _n (nextOf _h))
    (.Ssequence (.Sassign (headOf _Q) (.Etempvar _n (tptr telem)))
      (.Sreturn (some (.Etempvar _h (tptr telem))))))

/-- **`fifo_get` satisfies `fifo_get_spec`** (VST's `body_fifo_get`). -/
theorem fifo_get_satisfies (ge : CGenv) {ce : CompositeEnv} (QC : QueueCenv ce) (hcenv : ge.genv_cenv = ce)
    (c : List QElem) (q : Val) (e : QElem) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fifo_get) (fifoGetSpec c q e) [q] := by
  refine Sep.satisfies_internal_noVars ge _ f_fifo_get _ _
    (LocalSt emptyEnv [(_Q, q)] (fifo (e :: c) q ∗ emp)) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, ?_, by rw [sep_emp_eq]; exact hpre.2⟩⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; rfl
  rw [show f_fifo_get.fn_body = getBody from rfl]
  refine triple_fifo_open ge _ f_fifo_get _ _ (e :: c) q emp _ _ (fun qb hd tl hq _ hl2 => ?_)
  subst hq
  -- the first node comes out of the queue
  refine triple_pre ge _ f_fifo_get (P := fun e' le hp => ∃ bk o u,
      ∃ _ : hd = .Vptr bk o ∧ IsLink u, LocalSt emptyEnv [(_Q, .Vptr qb Integers.Ptrofs.zero)]
        (mapsto .Mint64 .Freeable qb 0 hd ∗ (mapsto .Mint64 .Freeable qb 8 tl
          ∗ (mallocToken qb sz16 ∗ (qnode bk (Integers.Ptrofs.unsigned o) e u
            ∗ fifoBody c u tl)))) e' le hp) (fun e' le hp hP => ?_) ?_
  · obtain ⟨he, hT, hH⟩ := hP
    rw [sep_emp_eq] at hH
    obtain ⟨a1, a234, hda, rfl, m0, a2, a34, hdb, rfl, m8, a3, a4, hdc, rfl, tok, hb⟩ := hH
    obtain ⟨bk, o, u, rfl, hu, hb'⟩ := fifoBody_cons hb
    exact ⟨bk, o, u, ⟨rfl, hu⟩, he, hT, a1, _, hda, rfl, m0, a2, _, hdb, rfl, m8, a3, a4, hdc,
      rfl, tok, hb'⟩
  refine triple_exists ge _ f_fifo_get _ _ _ (fun bk => ?_)
  refine triple_exists ge _ f_fifo_get _ _ _ (fun o => ?_)
  refine triple_exists ge _ f_fifo_get _ _ _ (fun u => ?_)
  refine triple_exists ge _ f_fifo_get _ _ _ (fun ⟨hhd, hu⟩ => ?_)
  subst hhd
  -- `h = Q->head;`
  refine triple_seq_only ge _ f_fifo_get (triple_set_local ge _ f_fifo_get emptyEnv _
    [(_Q, .Vptr qb Integers.Ptrofs.zero)] _ _h _ (.Vptr bk o) (fun _ h => h) (by temps_ne)
    (fun le m hp hT hH hag => eval_head QC hcenv (hT.get (v := .Vptr qb Integers.Ptrofs.zero)
      (by simp)) (Or.inr ⟨bk, o, rfl⟩) hH hag)) ?_
  -- `n = h->next;`
  refine triple_seq_only ge _ f_fifo_get (triple_set_local ge _ f_fifo_get emptyEnv _
    [(_h, .Vptr bk o), (_Q, .Vptr qb Integers.Ptrofs.zero)] _ _n _ u (fun _ h => h)
    (by temps_ne) (fun le m hp hT hH hag => ?_)) ?_
  · have hH' := hH
    simp only [sep_left_comm_eq _ (qnode _ _ _ _)] at hH'
    exact eval_next QC hcenv (hT.get (v := .Vptr bk o) (by simp)) hu (qnode_front hH').2 hag
  -- `Q->head = n;`
  refine triple_seq_only ge _ f_fifo_get (triple_store_head QC hcenv _ f_fifo_get emptyEnv _ _ _Q _n
    qb (.Vptr bk o) u (fun le hT => hT.get (by simp)) (fun le hT => hT.get (by simp)) hu) ?_
  -- `return h;`
  refine triple_return_local ge _ f_fifo_get _ _ _ _ (.Vptr bk o) (.Vptr bk o)
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
    (fun m => semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) (fun hp hH => ?_)
  have heq : (mapsto .Mint64 .Freeable qb 0 u ∗ (mapsto .Mint64 .Freeable qb 8 tl
      ∗ (mallocToken qb sz16 ∗ (qnode bk (Integers.Ptrofs.unsigned o) e u ∗ fifoBody c u tl))))
      = (fifoH qb u tl c ∗ qnode bk (Integers.Ptrofs.unsigned o) e u) := by
    unfold fifoH; sep_cancel
  rw [heq] at hH
  obtain ⟨h1, h2, hd12, rfl, hF, hq⟩ := hH
  have hp := qnode_ptr hq
  exact ⟨hp.symm, h1, h2, hd12, rfl, ⟨qb, u, tl, rfl, hu, hl2, hF⟩, bk, o, u, hp,
    (pure_sep_elim hq).2⟩

end VST.Verif.Queue
