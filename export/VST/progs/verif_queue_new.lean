/-
  Port of VST's `progs/verif_queue.v`, part 4: the two functions of
  `vst/progs/queue.c` that allocate, `fifo_new` and `make_elem`.

      struct fifo *fifo_new(void) {
        struct fifo *Q = (struct fifo *)surely_malloc(sizeof (*Q));
        Q->head = NULL;
        Q->tail = NULL;
        return Q;
      }

      struct elem *make_elem(int a, int b) {
        struct elem *p;
        p = surely_malloc(sizeof (*p));
        p->a = a;
        p->b = b;
        return p;
      }

  VST's specifications:

      fifo_new_spec: WITH gv  PRE [] SEP (mem_mgr gv)
        POST [tptr t_struct_fifo] EX v, RETURN (v) SEP (mem_mgr gv; fifo nil v)
      make_elem_spec: WITH a, b, gv  PRE [tint, tint] PARAMS (Vint a; Vint b) SEP (mem_mgr gv)
        POST [tptr t_struct_elem] EX p, RETURN (p)
        SEP (mem_mgr gv; field_at Qsh' list_struct [StructField _a] (Vint a) p;
             field_at Qsh' list_struct [StructField _b] (Vint b) p;
             list_cell QS Qsh (Vundef, Vundef) p;
             field_at_ Ews t_struct_elem [StructField _next] p;
             malloc_token Ews t_struct_elem p)

  `surely_malloc` is called through `surely_malloc_satisfies`; `malloc` and
  `surely_malloc` are the program's functions of those names.  No `mem_mgr`
  is needed (see `verif_rotate`).
-/
import VST.progs.verif_queue_rep
open CC CC.Sep CC.HProp
open Queue

namespace VST.Verif.Queue

section
variable (ge : CGenv) {ce : CompositeEnv} (hcenv : ge.genv_cenv = ce) (bs bm : Block)
  (hsymS : Genv.findSymbol ge.genv_genv _surely_malloc = some bs)
  (hfindS : Genv.findFunct ge.genv_genv (.Vptr bs Integers.Ptrofs.zero)
    = some (.Internal f_surely_malloc))
  (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
  (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
    = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default))

include hcenv hsymS hfindS hsymM hfindM in
/-- `t'1 = surely_malloc(sizeof (ty));` for a 16-byte struct `ty`. -/
theorem call_surely_malloc (f : Function) (l : List (Ident × Val)) (ty : Ty)
    (hsz : sizeof ce ty = 16) (hne : ∀ p ∈ l, p.1 ≠ _t'1) :
    Triple ge (FunctionEntry2 ge) f (LocalSt emptyEnv l emp)
      (.Scall (some _t'1) (.Evar _surely_malloc (Ty.Tfunction [tulong] (tptr tvoid) cc_default))
        [.Esizeof ty tulong])
      (.only (fun e le hp => ∃ bb, LocalSt emptyEnv ((_t'1, .Vptr bb Integers.Ptrofs.zero) :: l)
        (mallocToken bb sz16 ∗ mallocPayload bb sz16) e le hp)) := by
  refine triple_call_at ge _ f (mallocSpec sz16) (some _t'1) _ _ _ _ bs _ hfindS rfl rfl
    (fun e le hp m hP _ => ?_)
  obtain ⟨rfl, hT, rfl⟩ := hP
  refine ⟨[Val.Vptrofs sz16], Heap.emp, Heap.emp, Heap.disjoint_emp_left _,
    (Heap.emp_union _).symm, eval_callee_global (PTree.gempty _) hsymS rfl, ?_, ⟨rfl, rfl⟩,
    surely_malloc_satisfies ge sz16 bm hsymM hfindM, fun v h1' hpost _ => ?_⟩
  · refine EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Esizeof _ _) ?_ EvalExprlist.nil
    rw [hcenv, hsz]
    rfl
  · obtain ⟨bb, hb⟩ := hpost
    obtain ⟨rfl, hb'⟩ := pure_sep_elim hb
    exact ⟨bb, rfl, TempsHold_set hne hT, by rw [Heap.union_emp]; exact hb'⟩

end

/-- The 16 bytes of a fresh struct, as `8 + 8` raw bytes. -/
theorem payload_8_8 {bb : Block} {h : Heap} (hp : mallocPayload bb sz16 h) :
    (anyBytes .Freeable bb 0 8 ∗ anyBytes .Freeable bb 8 8) h := by
  rw [mallocPayload_undefBytes, unsigned_sz16, show (16 : _root_.Int).toNat = 8 + 8 from rfl,
    undefBytes_append] at hp
  obtain ⟨h1, h2, hd, rfl, hu1, hu2⟩ := hp
  exact ⟨h1, h2, hd, rfl, undefBytes_anyBytes hu1, undefBytes_anyBytes hu2⟩

/-- The 16 bytes of a fresh struct, as `4 + 4` raw bytes and an undefined
    pointer. -/
theorem payload_4_4_8 {bb : Block} {h : Heap} (hp : mallocPayload bb sz16 h) :
    (anyBytes .Freeable bb 0 4 ∗ (anyBytes .Freeable bb 4 4
      ∗ mapsto .Mint64 .Freeable bb 8 .Vundef)) h := by
  rw [mallocPayload_undefBytes, unsigned_sz16, show (16 : _root_.Int).toNat = 4 + (4 + 8) from rfl,
    undefBytes_append, undefBytes_append] at hp
  obtain ⟨h1, h23, hd, rfl, hu1, h2, h3, hd23, rfl, hu2, hu3⟩ := hp
  refine ⟨h1, _, hd, rfl, undefBytes_anyBytes hu1, h2, h3, hd23, rfl, undefBytes_anyBytes hu2, ?_⟩
  rw [show (0 : _root_.Int) + ((4 : Nat) : _root_.Int) + ((4 : Nat) : _root_.Int) = 8 from rfl,
    show (8 : Nat) = sizeChunkNat .Mint64 from rfl,
    undefBytes_mapsto .Freeable bb 8 undefEncoded_Mint64 (by decide)] at hu3
  exact hu3

/-! ## `fifo_new` -/

/-- `fifo_new_spec` -/
def fifoNewSpec : Sep.FunSpec where
  tyargs := []
  tyres := tptr tfifo
  cc := cc_default
  pre := fun vargs => ⌜vargs = []⌝
  post := fun v => fifo [] v
  measure := fun _ => 0

def newBody : Stmt :=
  .Ssequence
    (.Ssequence
      (.Scall (some _t'1) (.Evar _surely_malloc (Ty.Tfunction [tulong] (tptr tvoid) cc_default))
        [.Esizeof tfifo tulong])
      (.Sset _Q (.Ecast (.Etempvar _t'1 (tptr tvoid)) (tptr tfifo))))
    (.Ssequence (.Sassign (headOf _Q) nullE)
      (.Ssequence (.Sassign (tailOf _Q) nullE) (.Sreturn (some (.Etempvar _Q (tptr tfifo))))))

/-- **`fifo_new` satisfies `fifo_new_spec`** (VST's `body_fifo_new`). -/
theorem fifo_new_satisfies (ge : CGenv) {ce : CompositeEnv} (QC : QueueCenv ce)
    (hcenv : ge.genv_cenv = ce)
    (bs bm : Block)
    (hsymS : Genv.findSymbol ge.genv_genv _surely_malloc = some bs)
    (hfindS : Genv.findFunct ge.genv_genv (.Vptr bs Integers.Ptrofs.zero)
      = some (.Internal f_surely_malloc))
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_fifo_new) fifoNewSpec [] := by
  refine Sep.satisfies_internal_noVars ge _ f_fifo_new _ _ (LocalSt emptyEnv [] emp)
    (fun m => ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp hpre => ⟨rfl, TempsHold_nil _, hpre.2⟩⟩) ?_
  rw [show f_fifo_new.fn_body = newBody from rfl]
  refine triple_seq ge _ f_fifo_new _ (fun e le hp => ∃ bb, LocalSt emptyEnv
    [(_Q, .Vptr bb Integers.Ptrofs.zero)] (mallocToken bb sz16 ∗ mallocPayload bb sz16) e le hp)
    _ _ _ ?_ ?_
  · refine triple_fallthrough ge _ f_fifo_new _ _ _ _ ?_ (fun _ _ _ x => x)
    refine triple_seq_only ge _ f_fifo_new (call_surely_malloc ge hcenv bs bm hsymS hfindS hsymM
      hfindM f_fifo_new [] tfifo QC.szF (by simp)) ?_
    refine triple_exists ge _ f_fifo_new _ _ _ (fun bb => ?_)
    exact triple_conseq ge _ f_fifo_new (triple_set_local ge _ f_fifo_new emptyEnv _ [] _ _Q _
      (.Vptr bb Integers.Ptrofs.zero) (fun _ hq => by simp at hq) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _
        (hT.get (v := .Vptr bb Integers.Ptrofs.zero) (by simp)))
        (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bb, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ f_fifo_new _ _ _ (fun bb => ?_)
  -- the payload as two raw pointer-sized fields
  refine triple_pre ge _ f_fifo_new (P := LocalSt emptyEnv [(_Q, .Vptr bb Integers.Ptrofs.zero)]
      (anyBytes .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + 0) (sizeChunkNat .Mint64)
        ∗ (anyBytes .Freeable bb 8 8 ∗ mallocToken bb sz16)))
    (fun e le hp ⟨he, hT, hH⟩ => ⟨he, hT, ?_⟩) ?_
  · rw [sep_comm_eq] at hH
    obtain ⟨h1, h2, hd, rfl, hpay, ht⟩ := hH
    obtain ⟨a1, a2, hda, rfl, hb1, hb2⟩ := payload_8_8 hpay
    obtain ⟨hd1, hd2⟩ := Heap.disjoint_union_left.mp hd
    rw [uz]
    exact ⟨a1, _, Heap.disjoint_union_right.mpr ⟨hda, hd1⟩, Heap.union_assoc _ _ _, hb1, a2, h2,
      hd2, rfl, hb2, ht⟩
  -- `Q->head = NULL;`
  refine triple_seq_only ge _ f_fifo_new (triple_store_field_any QC.fifoL hcenv _ f_fifo_new emptyEnv _ _
    _Q _head 0 .Mint64 (tptr telem) nullE .Freeable bb Integers.Ptrofs.zero Val.Vnullptr
    QC.fifoL.off_head (Int.le_refl 0) (by decide) (by decide) rfl rfl
    (fun le hT => hT.get (by simp))
    (fun le m _ => ⟨_, eval_null_cast, semCast_ptr_ptr m _ _ _ _ _ (Or.inl rfl)⟩)) ?_
  -- `Q->tail = NULL;`
  refine triple_pre ge _ f_fifo_new (P := LocalSt emptyEnv [(_Q, .Vptr bb Integers.Ptrofs.zero)]
      (anyBytes .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + 8) (sizeChunkNat .Mint64)
        ∗ (mapsto .Mint64 .Freeable bb 0 Val.Vnullptr ∗ mallocToken bb sz16)))
    (fun e le hp ⟨he, hT, hH⟩ => ⟨he, hT, ?_⟩) ?_
  · rw [uz] at hH ⊢
    rw [sep_left_comm_eq] at hH
    exact hH
  refine triple_seq_only ge _ f_fifo_new (triple_store_field_any QC.fifoL hcenv _ f_fifo_new emptyEnv _ _
    _Q _tail 8 .Mint64 (tptr telem) nullE .Freeable bb Integers.Ptrofs.zero Val.Vnullptr
    QC.fifoL.off_tail (by decide) (by decide) (by decide) rfl rfl
    (fun le hT => hT.get (by simp))
    (fun le m _ => ⟨_, eval_null_cast, semCast_ptr_ptr m _ _ _ _ _ (Or.inl rfl)⟩)) ?_
  -- `return Q;`
  refine triple_return_local ge _ f_fifo_new _ _ _ _ (.Vptr bb Integers.Ptrofs.zero)
    (.Vptr bb Integers.Ptrofs.zero)
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
    (fun m => semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) (fun hp hH => ?_)
  rw [uz] at hH
  refine ⟨bb, Val.Vnullptr, Val.Vnullptr, rfl, Or.inl rfl, Or.inl rfl, ?_⟩
  obtain ⟨h1, h23, hd, rfl, hm8, h2, h3, hd23, rfl, hm0, ht⟩ := hH
  refine ⟨h2, Heap.union h1 h3, ?_, ?_, hm0, h1, h3, (Heap.disjoint_union_right.mp hd).2,
    rfl, hm8, h3, Heap.emp, Heap.disjoint_emp_right _,
    (Heap.union_emp _).symm, ht, rfl, rfl⟩
  · exact Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm (Heap.disjoint_union_right.mp hd).1, hd23⟩
  · rw [← Heap.union_assoc, Heap.union_comm (Heap.disjoint_union_right.mp hd).1, Heap.union_assoc]

/-! ## `make_elem` -/

/-- `make_elem_spec`: a fresh element holding `a`, `b`, and its token. -/
def makeElemSpec (a b : Integers.Int) : Sep.FunSpec where
  tyargs := [tint, tint]
  tyres := tptr telem
  cc := cc_default
  pre := fun vargs => ⌜vargs = [.Vint a, .Vint b]⌝
  post := fun v hp => ∃ bk, v = .Vptr bk Integers.Ptrofs.zero
    ∧ (elemRep ⟨v, a, .Vint b⟩ ∗ mallocToken bk sz16) hp
  measure := fun _ => 0

/-- `p->fld` at type `int`. -/
abbrev fieldOf (fld : Ident) : Expr := .Efield (.Ederef (.Etempvar _p (tptr telem)) telem) fld tint

def makeBody : Stmt :=
  .Ssequence
    (.Ssequence
      (.Scall (some _t'1) (.Evar _surely_malloc (Ty.Tfunction [tulong] (tptr tvoid) cc_default))
        [.Esizeof telem tulong])
      (.Sset _p (.Etempvar _t'1 (tptr tvoid))))
    (.Ssequence (.Sassign (fieldOf _a) (.Etempvar _a tint))
      (.Ssequence (.Sassign (fieldOf _b) (.Etempvar _b tint))
        (.Sreturn (some (.Etempvar _p (tptr telem))))))

/-- **`make_elem` satisfies `make_elem_spec`** (VST's `body_make_elem`). -/
theorem make_elem_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (bs bm : Block)
    (hsymS : Genv.findSymbol ge.genv_genv _surely_malloc = some bs)
    (hfindS : Genv.findFunct ge.genv_genv (.Vptr bs Integers.Ptrofs.zero)
      = some (.Internal f_surely_malloc))
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default))
    (a b : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_make_elem) (makeElemSpec a b)
      [.Vint a, .Vint b] := by
  refine Sep.satisfies_internal_noVars ge _ f_make_elem _ _
    (LocalSt emptyEnv [(_a, .Vint a), (_b, .Vint b)] emp) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  rw [show f_make_elem.fn_body = makeBody from rfl]
  refine triple_seq ge _ f_make_elem _ (fun e le hp => ∃ bb, LocalSt emptyEnv
    [(_p, .Vptr bb Integers.Ptrofs.zero), (_a, .Vint a), (_b, .Vint b)]
    (mallocToken bb sz16 ∗ mallocPayload bb sz16) e le hp) _ _ _ ?_ ?_
  · refine triple_fallthrough ge _ f_make_elem _ _ _ _ ?_ (fun _ _ _ x => x)
    refine triple_seq_only ge _ f_make_elem (call_surely_malloc ge hcenv bs bm hsymS hfindS hsymM
      hfindM f_make_elem _ telem sizeof_elem (by temps_ne)) ?_
    refine triple_exists ge _ f_make_elem _ _ _ (fun bb => ?_)
    exact triple_conseq ge _ f_make_elem (triple_set_local ge _ f_make_elem emptyEnv _
      [(_a, .Vint a), (_b, .Vint b)] _ _p _ (.Vptr bb Integers.Ptrofs.zero)
      (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bb, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ f_make_elem _ _ _ (fun bb => ?_)
  -- the payload as two raw `int` fields and an undefined `next`
  refine triple_pre ge _ f_make_elem (P := LocalSt emptyEnv
      [(_p, .Vptr bb Integers.Ptrofs.zero), (_a, .Vint a), (_b, .Vint b)]
      (anyBytes .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + 0)
        (sizeChunkNat .Mint32)
        ∗ (anyBytes .Freeable bb 4 4 ∗ (mapsto .Mint64 .Freeable bb 8 .Vundef
          ∗ mallocToken bb sz16))))
    (fun e le hp ⟨he, hT, hH⟩ => ⟨he, hT, ?_⟩) ?_
  · rw [sep_comm_eq] at hH
    obtain ⟨h1, h2, hd, rfl, hpay, ht⟩ := hH
    obtain ⟨a1, a23, hda, rfl, hb1, a2, a3, hd23, rfl, hb2, hm⟩ := payload_4_4_8 hpay
    obtain ⟨hd1, hd2⟩ := Heap.disjoint_union_left.mp hd
    obtain ⟨hd2', hd3'⟩ := Heap.disjoint_union_left.mp hd2
    rw [uz]
    exact ⟨a1, _, Heap.disjoint_union_right.mpr ⟨hda, hd1⟩, Heap.union_assoc _ _ _, hb1, a2, _,
      Heap.disjoint_union_right.mpr ⟨hd23, hd2'⟩, Heap.union_assoc _ _ _, hb2, a3, h2, hd3', rfl,
      hm, ht⟩
  -- `p->a = a;`
  refine triple_seq_only ge _ f_make_elem (triple_store_field_any queueCenv.elemL hcenv _ f_make_elem
    emptyEnv _ _ _p _a 0 .Mint32 tint (.Etempvar _a tint) .Freeable bb Integers.Ptrofs.zero
    (.Vint a) queueCenv.elemL.off_head (Int.le_refl 0) (by decide) (by decide) rfl rfl
    (fun le hT => hT.get (by simp))
    (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (v := .Vint a) (by simp)),
      semCast_int m a⟩)) ?_
  -- `p->b = b;`
  refine triple_pre ge _ f_make_elem (P := LocalSt emptyEnv
      [(_p, .Vptr bb Integers.Ptrofs.zero), (_a, .Vint a), (_b, .Vint b)]
      (anyBytes .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + 4)
        (sizeChunkNat .Mint32)
        ∗ (mapsto .Mint32 .Freeable bb 0 (.Vint a) ∗ (mapsto .Mint64 .Freeable bb 8 .Vundef
          ∗ mallocToken bb sz16))))
    (fun e le hp ⟨he, hT, hH⟩ => ⟨he, hT, ?_⟩) ?_
  · rw [uz] at hH ⊢
    rw [sep_left_comm_eq] at hH
    exact hH
  refine triple_seq_only ge _ f_make_elem (triple_store_field_any queueCenv.elemL hcenv _ f_make_elem
    emptyEnv _ _ _p _b 4 .Mint32 tint (.Etempvar _b tint) .Freeable bb Integers.Ptrofs.zero
    (.Vint b) off_b (by decide) (by decide) (by decide) rfl rfl
    (fun le hT => hT.get (by simp))
    (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (v := .Vint b) (by simp)),
      semCast_int m b⟩)) ?_
  -- `return p;`
  refine triple_return_local ge _ f_make_elem _ _ _ _ (.Vptr bb Integers.Ptrofs.zero)
    (.Vptr bb Integers.Ptrofs.zero)
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
    (fun m => semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) (fun hp hH => ?_)
  refine ⟨bb, rfl, ?_⟩
  rw [uz] at hH
  have heq : (mapsto .Mint32 .Freeable bb 4 (.Vint b) ∗ (mapsto .Mint32 .Freeable bb 0 (.Vint a)
      ∗ (mapsto .Mint64 .Freeable bb 8 .Vundef ∗ mallocToken bb sz16)))
      = (((mapsto .Mint32 .Freeable bb 0 (.Vint a) ∗ mapsto .Mint64 .Freeable bb 8 .Vundef)
        ∗ mapsto .Mint32 .Freeable bb 4 (.Vint b)) ∗ mallocToken bb sz16) := by
    sep_cancel
  rw [heq] at hH
  obtain ⟨h1, h2, hd, rfl, hel, ht⟩ := hH
  refine ⟨h1, h2, hd, rfl, ⟨bb, Integers.Ptrofs.zero, .Vundef, rfl, ?_⟩, ht⟩
  rw [ptrofs_unsigned_zero, elemAt, listNode, pure_true_sep_eq (by decide)]
  exact hel

end VST.Verif.Queue
