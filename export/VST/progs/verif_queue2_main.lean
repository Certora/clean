/-
  Port of VST's `progs/verif_queue2.v`, part 2: `main` of `vst/progs/queue2.c`.

      int main(void) {
        int i;
        struct fifo *Q;
        struct elem *p;
        Q = fifo_new();
        p = make_elem(1);
        fifo_put(Q,p);
        p = make_elem(2);
        fifo_put(Q,p);
        p = fifo_get(Q);
        i = p->data;
        free(p);
        return i;
      }

      main_spec: WITH gv  PRE [] main_pre prog tt gv
        POST [tint] PROP() RETURN (Vint (Int.repr 1)) SEP(TT).

  As for `queue.c` (`verif_queue_main`), the program's symbols name its
  functions (`QueueFuns`, with `queue2.c`'s `make_elem`), and `malloc`/`free`
  are its external functions of those names.
-/
import VST.progs.verif_queue2
open CC CC.Sep CC.HProp
open Queue

namespace VST.Verif.Queue2
open VST.Verif.Queue

/-! The local variables of `queue2.c`'s `main` are those of `queue.c`. -/
theorem t'1_eq : Queue2._t'1 = _t'1 := rfl
theorem t'2_eq : Queue2._t'2 = _t'2 := rfl
theorem t'3_eq : Queue2._t'3 = _t'3 := rfl
theorem t'4_eq : Queue2._t'4 = _t'4 := rfl
theorem p_eq : Queue2._p = _p := rfl
theorem Q_eq : Queue2._Q = _Q := rfl
theorem i_eq : Queue2._i = _i := rfl
attribute [local simp] t'1_eq t'2_eq t'3_eq t'4_eq p_eq Q_eq i_eq

/-- `main_spec` of `verif_queue2.v`: `main` returns `1`. -/
def mainSpec : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs => ⌜vargs = []⌝
  post := fun v _ => v = .Vint (Integers.Int.repr 1)
  measure := fun _ => 0

/-- The element `make_elem(d)` returns at `bk`. -/
abbrev mk (bk : Block) (d : Nat) : QElem :=
  ⟨.Vptr bk Integers.Ptrofs.zero, Integers.Int.repr d, .Vundef⟩

section
variable (ge : CGenv) (hcenv : ge.genv_cenv = Queue2.prog.prog_comp_env)
  (G : QueueFuns ge Queue2.f_make_elem)

include hcenv G in
/-- `make_elem(d)` from a frame `F`. -/
theorem call_make (t : Ident) (l : List (Ident × Val)) (F : HProp) (d : Nat)
    (hne : ∀ p ∈ l, p.1 ≠ t) :
    Triple ge (FunctionEntry2 ge) Queue2.f_main (LocalSt emptyEnv l F)
      (.Scall (some t) (.Evar _make_elem (.Tfunction [tint] (tptr telem) cc_default))
        [.Econst_int (Integers.Int.repr d) tint])
      (.only (fun e le hp => ∃ bk, LocalSt emptyEnv ((t, .Vptr bk Integers.Ptrofs.zero) :: l)
        ((elemRep (mk bk d) ∗ mallocToken bk sz16) ∗ F) e le hp)) := by
  refine triple_pre_emp (triple_call_at_local ge _ Queue2.f_main (makeElemSpec _) (some t) _ _ l
    emp F _ G.bMake _ [.Vint (Integers.Int.repr d)] G.sym_make G.find_make
    rfl (fun le m _ => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (semCast_int m _)
        EvalExprlist.nil) (fun h hh => ⟨rfl, hh⟩)
    (make_elem_satisfies ge hcenv G.bS G.bM G.sym_S G.find_S G.sym_M G.find_M _)
    (fun le v h1' h2 hT hpost hF hd => ?_))
  obtain ⟨bk, rfl, hH⟩ := hpost
  exact ⟨bk, rfl, TempsHold_set hne hT, h1', h2, hd, rfl, hH, hF⟩

include hcenv in
/-- **`main` of `queue2.c` satisfies `main_spec`** (VST's `body_main` of
    `verif_queue2.v`): `main` returns `1`. -/
theorem main_satisfies (G : QueueFuns ge Queue2.f_make_elem) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal Queue2.f_main) mainSpec [] := by
  refine Sep.satisfies_internal_noVars ge _ Queue2.f_main _ _ (LocalSt emptyEnv [] emp)
    (fun m => ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp hpre => ⟨rfl, TempsHold_nil _, hpre.2⟩⟩) ?_
  refine Sep.triple_seq ge _ Queue2.f_main _ Sep.Assn.no _ _ _ ?_
    (Sep.triple_vacuous ge _ Queue2.f_main _ _)
  -- `Q = fifo_new();`
  refine triple_seq_only ge _ Queue2.f_main (Q := fun e le hp => ∃ qb, LocalSt emptyEnv
    [(_Q, .Vptr qb Integers.Ptrofs.zero)] (fifo [] (.Vptr qb Integers.Ptrofs.zero)) e le hp) ?_ ?_
  · refine triple_seq_only ge _ Queue2.f_main (Q := fun e le hp => ∃ qb, LocalSt emptyEnv
      [(_t'1, .Vptr qb Integers.Ptrofs.zero)] (fifo [] (.Vptr qb Integers.Ptrofs.zero)) e le hp)
      ?_ ?_
    · refine triple_pre_emp (triple_call_at_local ge _ Queue2.f_main fifoNewSpec (some _t'1) _ _
        [] emp emp _ G.bNew _ [] G.sym_new G.find_new rfl (fun _ _ _ => EvalExprlist.nil)
        (fun h hh => ⟨rfl, hh⟩)
        (Queue.fifo_new_satisfies ge queue2Cenv hcenv G.bS G.bM G.sym_S G.find_S G.sym_M
          G.find_M)
        (fun le v h1' h2 hT hpost hF hd => ?_))
      have hpost' := hpost
      obtain ⟨qb, _, _, rfl, _⟩ := hpost'
      refine ⟨qb, rfl, TempsHold_set (by temps_ne) hT, ?_⟩
      rw [show h2 = Heap.emp from hF, Heap.union_emp]
      exact hpost
    · refine triple_exists ge _ Queue2.f_main _ _ _ (fun qb => ?_)
      exact triple_conseq ge _ Queue2.f_main (triple_set_local ge _ Queue2.f_main emptyEnv _ [] _
        _Q _ (.Vptr qb Integers.Ptrofs.zero) (fun _ hq => by simp at hq) (by temps_ne)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
        (fun _ _ _ x => x) (fun e le hp h => ⟨qb, h⟩) (fun _ _ _ x => x.elim)
        (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ Queue2.f_main _ _ _ (fun qb => ?_)
  -- `p = make_elem(1);`
  refine triple_seq_only ge _ Queue2.f_main (Q := fun e le hp => ∃ bk1, LocalSt emptyEnv
    [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
    ((elemRep (mk bk1 1) ∗ mallocToken bk1 sz16) ∗ fifo [] (.Vptr qb Integers.Ptrofs.zero))
    e le hp) ?_ ?_
  · refine triple_seq_only ge _ Queue2.f_main (call_make ge hcenv G _t'2 _ _ 1 (by temps_ne)) ?_
    refine triple_exists ge _ Queue2.f_main _ _ _ (fun bk1 => ?_)
    exact triple_conseq ge _ Queue2.f_main (triple_set_local ge _ Queue2.f_main emptyEnv _
      [(_Q, .Vptr qb Integers.Ptrofs.zero)] _ _p _ (.Vptr bk1 Integers.Ptrofs.zero)
      (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bk1, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ Queue2.f_main _ _ _ (fun bk1 => ?_)
  -- `fifo_put(Q, p);`
  refine triple_pre_sep (H := (fifo [] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1))
    ∗ mallocToken bk1 sz16) (by sep_cancel) ?_
  refine triple_seq_only ge _ Queue2.f_main
    (call_put ge queue2Cenv hcenv G _ qb [] (mk bk1 1) bk1 _ rfl (by simp) (by simp)) ?_
  -- `p = make_elem(2);`
  refine triple_seq_only ge _ Queue2.f_main (Q := fun e le hp => ∃ bk2, LocalSt emptyEnv
    [(_p, .Vptr bk2 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
    ((elemRep (mk bk2 2) ∗ mallocToken bk2 sz16)
      ∗ (fifo ([] ++ [mk bk1 1]) (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk1 sz16))
    e le hp) ?_ ?_
  · refine triple_seq_only ge _ Queue2.f_main (call_make ge hcenv G _t'3 _ _ 2 (by temps_ne)) ?_
    refine triple_exists ge _ Queue2.f_main _ _ _ (fun bk2 => ?_)
    exact triple_conseq ge _ Queue2.f_main (triple_set_local ge _ Queue2.f_main emptyEnv _
      [(_Q, .Vptr qb Integers.Ptrofs.zero)] _ _p _ (.Vptr bk2 Integers.Ptrofs.zero)
      (fun _ hq => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢
                      exact Or.inr (Or.inr hq)) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bk2, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ Queue2.f_main _ _ _ (fun bk2 => ?_)
  -- `fifo_put(Q, p);`
  refine triple_pre_sep (H := (fifo ([] ++ [mk bk1 1]) (.Vptr qb Integers.Ptrofs.zero)
    ∗ elemRep (mk bk2 2)) ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16)) (by sep_cancel) ?_
  refine triple_seq_only ge _ Queue2.f_main
    (call_put ge queue2Cenv hcenv G _ qb _ (mk bk2 2) bk2 _ rfl (by simp) (by simp)) ?_
  -- `p = fifo_get(Q);`
  refine triple_seq_only ge _ Queue2.f_main (Q := LocalSt emptyEnv
    [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
    ((fifo [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1))
      ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16))) ?_ ?_
  · refine triple_seq_only ge _ Queue2.f_main (triple_call_at_local ge _ Queue2.f_main
      (fifoGetSpec [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) (mk bk1 1)) (some _t'4) _ _ _
      _ _ (LocalSt emptyEnv [(_t'4, .Vptr bk1 Integers.Ptrofs.zero),
        (_p, .Vptr bk2 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
        ((fifo [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1))
          ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16)))
      G.bGet _ [.Vptr qb Integers.Ptrofs.zero] G.sym_get G.find_get rfl
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
        (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) EvalExprlist.nil)
      (fun h hh => ⟨rfl, hh⟩) (Queue.fifo_get_satisfies ge queue2Cenv hcenv _ _ _)
      (fun le v h1' h2 hT hpost hF hd => ?_)) ?_
    · obtain ⟨rfl, hH⟩ := hpost
      exact ⟨rfl, TempsHold_set (by temps_ne) hT, h1', h2, hd, rfl, hH, hF⟩
    · exact triple_set_local ge _ Queue2.f_main emptyEnv _ [(_Q, .Vptr qb Integers.Ptrofs.zero)]
        _ _p _ (.Vptr bk1 Integers.Ptrofs.zero)
        (fun _ hq => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢
                        exact Or.inr (Or.inr hq)) (by temps_ne)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
  -- the element `p`
  refine triple_pre ge _ Queue2.f_main (P := fun e le hp => ∃ u, LocalSt emptyEnv
      [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
      (elemAt bk1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) (Integers.Int.repr 1)
        .Vundef u ∗ (mallocToken bk1 sz16
          ∗ (fifo [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))) e le hp)
    (fun e le hp hP => ?_) ?_
  · obtain ⟨he, hT, hH⟩ := hP
    have heq : ((fifo [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1))
        ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16))
        = (elemRep (mk bk1 1) ∗ (mallocToken bk1 sz16
          ∗ (fifo [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))) := by
      sep_cancel
    rw [heq] at hH
    obtain ⟨h1, h2, hd, rfl, ⟨bk, o, u, hptr, hel⟩, hr⟩ := hH
    cases hptr
    exact ⟨u, he, hT, h1, h2, hd, rfl, hel, hr⟩
  refine triple_exists ge _ Queue2.f_main _ _ _ (fun u => ?_)
  -- `i = p->data;`
  refine triple_seq_only ge _ Queue2.f_main (triple_set_local ge _ Queue2.f_main emptyEnv _
    [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)] _ _i _
    (.Vint (Integers.Int.repr 1)) (fun _ h => h) (by temps_ne)
    (fun le m hp hT hH hag => ?_)) ?_
  · rw [elemAt_a_front] at hH
    exact eval_field_mapsto queue2Cenv.elemL hcenv (chunk := .Mint32) (ty := tint)
      queue2Cenv.elemL.off_head (Int.le_refl 0) (by decide) rfl rfl
      (hT.get (id := _p) (v := .Vptr bk1 Integers.Ptrofs.zero) (by simp))
      (by rw [Int.add_zero]; exact hH) hag
  -- `free(p);`
  refine triple_pre_sep (H := (mallocToken bk1 sz16 ∗ elemAt bk1
    (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) (Integers.Int.repr 1) .Vundef u)
    ∗ (fifo [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))
    (by sep_cancel) ?_
  refine triple_seq_only ge _ Queue2.f_main (triple_call_at_local ge _ Queue2.f_main
    (freeSpec bk1 sz16) none _free _ _ _ _ (LocalSt emptyEnv
      [(_i, .Vint (Integers.Int.repr 1)), (_p, .Vptr bk1 Integers.Ptrofs.zero),
        (_Q, .Vptr qb Integers.Ptrofs.zero)]
      (fifo [mk bk2 2] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))
    G.bF _ [.Vptr bk1 Integers.Ptrofs.zero] G.sym_F G.find_F rfl
    (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
      (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) EvalExprlist.nil)
    (fun h hh => ?_) (free_satisfies ge _ bk1 sz16 _ _ _)
    (fun le v h1' h2 hT hpost hF hd => ?_)) ?_
  · obtain ⟨h1, h2, hd, rfl, ht, hel⟩ := hh
    refine pure_sep_intro rfl ⟨h1, h2, hd, rfl, ht, ?_⟩
    have := elemAt_anyBytes hel
    rw [ptrofs_unsigned_zero] at this
    rw [unsigned_sz16]
    exact this
  · refine ⟨rfl, hT, ?_⟩
    rw [hpost.2, Heap.emp_union]
    exact hF
  -- `return i;`
  exact triple_return_local ge _ Queue2.f_main _ _ _ _ (.Vint (Integers.Int.repr 1))
    (.Vint (Integers.Int.repr 1))
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
    (fun m => semCast_int m _) (fun _ _ => rfl)

end

end VST.Verif.Queue2
