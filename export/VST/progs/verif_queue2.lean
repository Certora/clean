/-
  Port of VST's `progs/verif_queue2.v`: `vst/progs/queue2.c` (Clight AST in
  `VST.progs.queue2`) meets its specifications.

  `queue2.c` is `queue.c` with a one-field element:

      struct elem { int data; struct elem *next; };

      struct elem *make_elem(int data) {
        struct elem *p;
        p = surely_malloc(sizeof (*p));
        p->data=data;
        return p;
      }

      int main(void) {
        int i; struct fifo *Q; struct elem *p;
        Q = fifo_new();
        p = make_elem(1); fifo_put(Q,p);
        p = make_elem(2); fifo_put(Q,p);
        p = fifo_get(Q);
        i = p->data;
        free(p);
        return i;
      }

  `surely_malloc`, `fifo_new`, `fifo_put`, `fifo_empty` and `fifo_get` are
  the very functions of `queue.c` (the generated Clight bodies are equal,
  `*_eq` below), and both programs' composite environments have the layout
  `QueueCenv` that the proofs of `verif_queue*` are stated for, so those
  proofs are reused unchanged (`queue2Cenv`).  Only `make_elem` and `main`
  are proved here.  An element of `queue2` is a `QElem` whose second word is
  the struct's padding, left undefined (`Vundef`) by `make_elem`.
-/
import VST.progs.verif_queue_main
import VST.progs.queue2
open CC CC.Sep CC.HProp
open Queue

namespace VST.Verif.Queue2
open VST.Verif.Queue

/-! ## What `queue2.c` shares with `queue.c` -/

theorem f_surely_malloc_eq : Queue2.f_surely_malloc = Queue.f_surely_malloc := rfl
theorem f_fifo_new_eq : Queue2.f_fifo_new = Queue.f_fifo_new := rfl
theorem f_fifo_put_eq : Queue2.f_fifo_put = Queue.f_fifo_put := rfl
theorem f_fifo_empty_eq : Queue2.f_fifo_empty = Queue.f_fifo_empty := rfl
theorem f_fifo_get_eq : Queue2.f_fifo_get = Queue.f_fifo_get := rfl

/-- The composite environment of `queue2.c`: `data` at offset 0, `next` at 8. -/
def queue2Cenv : QueueCenv Queue2.prog.prog_comp_env :=
  ⟨Queue2._data, coOf Queue2.prog.prog_comp_env _elem, coOf Queue2.prog.prog_comp_env _fifo,
    rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **`fifo_empty` of `queue2.c` satisfies `fifo_empty_spec`.** -/
theorem fifo_empty_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = Queue2.prog.prog_comp_env)
    (c : List QElem) (q : Val) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal Queue2.f_fifo_empty) (fifoEmptySpec c q) [q] :=
  Queue.fifo_empty_satisfies ge queue2Cenv hcenv c q

/-- **`fifo_get` of `queue2.c` satisfies `fifo_get_spec`.** -/
theorem fifo_get_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = Queue2.prog.prog_comp_env)
    (c : List QElem) (q : Val) (e : QElem) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal Queue2.f_fifo_get) (fifoGetSpec c q e) [q] :=
  Queue.fifo_get_satisfies ge queue2Cenv hcenv c q e

/-- **`fifo_put` of `queue2.c` satisfies `fifo_put_spec`.** -/
theorem fifo_put_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = Queue2.prog.prog_comp_env)
    (c : List QElem) (q : Val) (e : QElem) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal Queue2.f_fifo_put) (fifoPutSpec c q e)
      [q, e.ptr] :=
  Queue.fifo_put_satisfies ge queue2Cenv hcenv c q e

/-- **`fifo_new` of `queue2.c` satisfies `fifo_new_spec`.** -/
theorem fifo_new_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = Queue2.prog.prog_comp_env)
    (bs bm : Block)
    (hsymS : Genv.findSymbol ge.genv_genv _surely_malloc = some bs)
    (hfindS : Genv.findFunct ge.genv_genv (.Vptr bs Integers.Ptrofs.zero)
      = some (.Internal Queue2.f_surely_malloc))
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal Queue2.f_fifo_new) fifoNewSpec [] :=
  Queue.fifo_new_satisfies ge queue2Cenv hcenv bs bm hsymS hfindS hsymM hfindM

/-! ## `make_elem` -/

/-- The 16 bytes of a fresh element: 4 raw bytes for `data`, the 4 bytes of
    padding and the 8 bytes of `next` undefined. -/
theorem payload_4_u4_8 {bb : Block} {h : Heap} (hp : mallocPayload bb sz16 h) :
    (anyBytes .Freeable bb 0 4 ∗ (mapsto .Mint32 .Freeable bb 4 .Vundef
      ∗ mapsto .Mint64 .Freeable bb 8 .Vundef)) h := by
  rw [mallocPayload_undefBytes, unsigned_sz16, show (16 : _root_.Int).toNat = 4 + (4 + 8) from rfl,
    undefBytes_append, undefBytes_append] at hp
  obtain ⟨h1, h23, hd, rfl, hu1, h2, h3, hd23, rfl, hu2, hu3⟩ := hp
  refine ⟨h1, _, hd, rfl, undefBytes_anyBytes hu1, h2, h3, hd23, rfl, ?_, ?_⟩
  · rw [show (0 : _root_.Int) + ((4 : Nat) : _root_.Int) = 4 from rfl,
      show (4 : Nat) = sizeChunkNat .Mint32 from rfl,
      undefBytes_mapsto .Freeable bb 4 undefEncoded_Mint32 (by decide)] at hu2
    exact hu2
  · rw [show (0 : _root_.Int) + ((4 : Nat) : _root_.Int) + ((4 : Nat) : _root_.Int) = 8 from rfl,
      show (8 : Nat) = sizeChunkNat .Mint64 from rfl,
      undefBytes_mapsto .Freeable bb 8 undefEncoded_Mint64 (by decide)] at hu3
    exact hu3

/-- `make_elem_spec` of `verif_queue2.v`: a fresh element holding `data`
    (and undefined padding), and its token. -/
def makeElemSpec (d : Integers.Int) : Sep.FunSpec where
  tyargs := [tint]
  tyres := tptr telem
  cc := cc_default
  pre := fun vargs => ⌜vargs = [.Vint d]⌝
  post := fun v hp => ∃ bk, v = .Vptr bk Integers.Ptrofs.zero
    ∧ (elemRep ⟨v, d, .Vundef⟩ ∗ mallocToken bk sz16) hp
  measure := fun _ => 0

def makeBody : Stmt :=
  .Ssequence
    (.Ssequence
      (.Scall (some _t'1) (.Evar _surely_malloc (Ty.Tfunction [tulong] (tptr tvoid) cc_default))
        [.Esizeof telem tulong])
      (.Sset _p (.Etempvar _t'1 (tptr tvoid))))
    (.Ssequence (.Sassign (fieldOf Queue2._data) (.Etempvar Queue2._data tint))
      (.Sreturn (some (.Etempvar _p (tptr telem)))))

/-- **`make_elem` of `queue2.c` satisfies `make_elem_spec`** (VST's
    `body_make_elem` of `verif_queue2.v`). -/
theorem make_elem_satisfies (ge : CGenv) (hcenv : ge.genv_cenv = Queue2.prog.prog_comp_env)
    (bs bm : Block)
    (hsymS : Genv.findSymbol ge.genv_genv _surely_malloc = some bs)
    (hfindS : Genv.findFunct ge.genv_genv (.Vptr bs Integers.Ptrofs.zero)
      = some (.Internal Queue2.f_surely_malloc))
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default))
    (d : Integers.Int) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal Queue2.f_make_elem) (makeElemSpec d)
      [.Vint d] := by
  refine Sep.satisfies_internal_noVars ge _ Queue2.f_make_elem _ _
    (LocalSt emptyEnv [(Queue2._data, .Vint d)] emp) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; rfl
  rw [show Queue2.f_make_elem.fn_body = makeBody from rfl]
  refine triple_seq ge _ Queue2.f_make_elem _ (fun e le hp => ∃ bb, LocalSt emptyEnv
    [(_p, .Vptr bb Integers.Ptrofs.zero), (Queue2._data, .Vint d)]
    (mallocToken bb sz16 ∗ mallocPayload bb sz16) e le hp) _ _ _ ?_ ?_
  · refine triple_fallthrough ge _ Queue2.f_make_elem _ _ _ _ ?_ (fun _ _ _ x => x)
    refine triple_seq_only ge _ Queue2.f_make_elem (call_surely_malloc ge hcenv bs bm hsymS
      hfindS hsymM hfindM Queue2.f_make_elem _ telem queue2Cenv.szE (by temps_ne)) ?_
    refine triple_exists ge _ Queue2.f_make_elem _ _ _ (fun bb => ?_)
    exact triple_conseq ge _ Queue2.f_make_elem (triple_set_local ge _ Queue2.f_make_elem
      emptyEnv _ [(Queue2._data, .Vint d)] _ _p _ (.Vptr bb Integers.Ptrofs.zero)
      (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bb, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ Queue2.f_make_elem _ _ _ (fun bb => ?_)
  -- the payload as a raw `int` field, the padding and an undefined `next`
  refine triple_pre ge _ Queue2.f_make_elem (P := LocalSt emptyEnv
      [(_p, .Vptr bb Integers.Ptrofs.zero), (Queue2._data, .Vint d)]
      (anyBytes .Freeable bb (Integers.Ptrofs.unsigned Integers.Ptrofs.zero + 0)
        (sizeChunkNat .Mint32)
        ∗ (mapsto .Mint32 .Freeable bb 4 .Vundef ∗ (mapsto .Mint64 .Freeable bb 8 .Vundef
          ∗ mallocToken bb sz16))))
    (fun e le hp ⟨he, hT, hH⟩ => ⟨he, hT, ?_⟩) ?_
  · rw [sep_comm_eq] at hH
    obtain ⟨h1, h2, hd, rfl, hpay, ht⟩ := hH
    obtain ⟨a1, a23, hda, rfl, hb1, a2, a3, hd23, rfl, hb2, hm⟩ := payload_4_u4_8 hpay
    obtain ⟨hd1, hd2⟩ := Heap.disjoint_union_left.mp hd
    obtain ⟨hd2', hd3'⟩ := Heap.disjoint_union_left.mp hd2
    rw [uz]
    exact ⟨a1, _, Heap.disjoint_union_right.mpr ⟨hda, hd1⟩, Heap.union_assoc _ _ _, hb1, a2, _,
      Heap.disjoint_union_right.mpr ⟨hd23, hd2'⟩, Heap.union_assoc _ _ _, hb2, a3, h2, hd3', rfl,
      hm, ht⟩
  -- `p->data = data;`
  refine triple_seq_only ge _ Queue2.f_make_elem (triple_store_field_any queue2Cenv.elemL hcenv _
    Queue2.f_make_elem emptyEnv _ _ _p Queue2._data 0 .Mint32 tint (.Etempvar Queue2._data tint)
    .Freeable bb Integers.Ptrofs.zero (.Vint d) queue2Cenv.elemL.off_head (Int.le_refl 0)
    (by decide) (by decide) rfl rfl
    (fun le hT => hT.get (by simp))
    (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (v := .Vint d) (by simp)),
      semCast_int m d⟩)) ?_
  -- `return p;`
  refine triple_return_local ge _ Queue2.f_make_elem _ _ _ _ (.Vptr bb Integers.Ptrofs.zero)
    (.Vptr bb Integers.Ptrofs.zero)
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
    (fun m => semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) (fun hp hH => ?_)
  refine ⟨bb, rfl, ?_⟩
  rw [uz] at hH
  have heq : (mapsto .Mint32 .Freeable bb 0 (.Vint d) ∗ (mapsto .Mint32 .Freeable bb 4 .Vundef
      ∗ (mapsto .Mint64 .Freeable bb 8 .Vundef ∗ mallocToken bb sz16)))
      = (((mapsto .Mint32 .Freeable bb 0 (.Vint d) ∗ mapsto .Mint64 .Freeable bb 8 .Vundef)
        ∗ mapsto .Mint32 .Freeable bb 4 .Vundef) ∗ mallocToken bb sz16) := by
    sep_cancel
  rw [heq] at hH
  obtain ⟨h1, h2, hd, rfl, hel, ht⟩ := hH
  refine ⟨h1, h2, hd, rfl, ⟨bb, Integers.Ptrofs.zero, .Vundef, rfl, ?_⟩, ht⟩
  rw [ptrofs_unsigned_zero, elemAt, listNode, pure_true_sep_eq (by decide)]
  exact hel

end VST.Verif.Queue2
