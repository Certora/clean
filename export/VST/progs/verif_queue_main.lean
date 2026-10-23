/-
  Port of VST's `progs/verif_queue.v`, part 5: `main` of `vst/progs/queue.c`.

      int main(void) {
        int i, j;
        struct fifo *Q;
        struct elem *p;
        Q = fifo_new();
        p = make_elem(1,10);
        fifo_put(Q,p);
        p = make_elem(2,20);
        fifo_put(Q,p);
        p = fifo_get(Q);
        i = p->a;
        j = p->b;
        free(p);
        return i+j;
      }

      main_spec: WITH gv  PRE [] main_pre prog tt gv
        POST [tint] PROP() RETURN (Vint (Int.repr (1+10))) SEP(TT).

  `main` calls the queue operations through their specifications
  (`verif_queue`, `verif_queue_put`, `verif_queue_new`); the program's
  symbols name its functions (`QueueFuns`), and `malloc`/`free` are its
  external functions of those names.  The program has no global variables,
  so `main` starts from the empty heap.
-/
import VST.progs.verif_queue_put
import VST.progs.verif_queue_new
open CC CC.Sep CC.HProp
open Queue

namespace VST.Verif.Queue

/-- The functions of the program (VST's `Gprog`), with `fMake` the body of
    `make_elem` (the one function that `queue.c` and `queue2.c` do not share). -/
structure QueueFuns (ge : CGenv) (fMake : Function) : Type where
  bS : Block
  bM : Block
  bF : Block
  bNew : Block
  bMake : Block
  bPut : Block
  bGet : Block
  sym_S : Genv.findSymbol ge.genv_genv _surely_malloc = some bS
  find_S : Genv.findFunct ge.genv_genv (.Vptr bS Integers.Ptrofs.zero)
    = some (.Internal f_surely_malloc)
  sym_M : Genv.findSymbol ge.genv_genv _malloc = some bM
  find_M : Genv.findFunct ge.genv_genv (.Vptr bM Integers.Ptrofs.zero)
    = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default)
  sym_F : Genv.findSymbol ge.genv_genv _free = some bF
  find_F : Genv.findFunct ge.genv_genv (.Vptr bF Integers.Ptrofs.zero)
    = some (.External .EF_free [tptr tvoid] tvoid cc_default)
  sym_new : Genv.findSymbol ge.genv_genv _fifo_new = some bNew
  find_new : Genv.findFunct ge.genv_genv (.Vptr bNew Integers.Ptrofs.zero)
    = some (.Internal f_fifo_new)
  sym_make : Genv.findSymbol ge.genv_genv _make_elem = some bMake
  find_make : Genv.findFunct ge.genv_genv (.Vptr bMake Integers.Ptrofs.zero)
    = some (.Internal fMake)
  sym_put : Genv.findSymbol ge.genv_genv _fifo_put = some bPut
  find_put : Genv.findFunct ge.genv_genv (.Vptr bPut Integers.Ptrofs.zero)
    = some (.Internal f_fifo_put)
  sym_get : Genv.findSymbol ge.genv_genv _fifo_get = some bGet
  find_get : Genv.findFunct ge.genv_genv (.Vptr bGet Integers.Ptrofs.zero)
    = some (.Internal f_fifo_get)

/-- `main_spec`: `main` returns `1 + 10`. -/
def mainSpec : Sep.FunSpec where
  tyargs := []
  tyres := tint
  cc := cc_default
  pre := fun vargs => ⌜vargs = []⌝
  post := fun v _ => v = .Vint (Integers.Int.repr 11)
  measure := fun _ => 0

/-- The call rule at the actual arguments, for a global callee, in the
    `LocalSt` style: the fragment is the callee's precondition and a frame. -/
theorem triple_call_at_local (ge : CGenv) (fe : EntryRel) (f : Function) (S : FunSpec)
    (optid : Option Ident) (fid : Ident) (al : List Expr) (l : List (Ident × Val))
    (Hpre Hframe : HProp) (Q : Sep.Assn) (b : Block) (fd : FunDef) (vargs : List Val)
    (hsym : Genv.findSymbol ge.genv_genv fid = some b)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge emptyEnv le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h)
    (hsat : SatisfiesAt ge fe fd S vargs)
    (hpost : ∀ le v h1' h2, TempsHold l le → S.post v h1' → Hframe h2 → Heap.disjoint h1' h2 →
      Q emptyEnv (setOpttemp optid v le) (Heap.union h1' h2)) :
    Triple ge fe f (LocalSt emptyEnv l (Hpre ∗ Hframe))
      (.Scall optid (.Evar fid (.Tfunction S.tyargs S.tyres S.cc)) al) (.only Q) := by
  refine triple_call_at ge fe f S optid _ al _ Q b fd hfind hty rfl (fun e le hp m hP _ => ?_)
  obtain ⟨rfl, hT, h1, h2, hd, rfl, hH1, hH2⟩ := hP
  exact ⟨vargs, h1, h2, hd, rfl, eval_callee_global (PTree.gempty _) hsym rfl, hargs le m hT,
    hpre h1 hH1, hsat, fun v h1' hS hd' => hpost le v h1' h2 hT hS hH2 hd'⟩

/-- An element is 16 owned bytes, which is what `free` takes back. -/
theorem elemAt_anyBytes {bk : Block} {X : _root_.Int} {a : Integers.Int} {b u : Val} {h : Heap}
    (he : elemAt bk X a b u h) : anyBytes .Freeable bk X 16 h := by
  rw [elemAt, listNode] at he
  obtain ⟨h1, h2, hd, rfl, hl, hb⟩ := he
  obtain ⟨ha, hn, hd', rfl, hma, hmn⟩ := (pure_sep_elim hl).2
  obtain ⟨hda, hdn⟩ := Heap.disjoint_union_left.mp hd
  rw [show (16 : Nat) = 4 + (4 + 8) from rfl, anyBytes_split, anyBytes_split]
  refine ⟨ha, Heap.union h2 hn, Heap.disjoint_union_right.mpr ⟨hda, hd'⟩, ?_,
    anyBytes_of_mapsto hma, h2, hn, Heap.disjoint_comm hdn, rfl, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm hdn]
  · have := anyBytes_of_mapsto hb
    rwa [show X + ((4 : Nat) : _root_.Int) = X + 4 from rfl]
  · have := anyBytes_of_mapsto hmn
    rwa [show X + ((4 : Nat) : _root_.Int) + ((4 : Nat) : _root_.Int) = X + 8 by omega]

/-- The element `make_elem(a, b)` returns at `bk`. -/
abbrev mk (bk : Block) (a b : Nat) : QElem :=
  ⟨.Vptr bk Integers.Ptrofs.zero, Integers.Int.repr a, .Vint (Integers.Int.repr b)⟩

theorem triple_pre_emp {ge : CGenv} {fe : EntryRel} {f : Function} {E : Env}
    {l : List (Ident × Val)} {H : HProp} {s : Stmt} {R : Sep.ExitConds}
    (h : Triple ge fe f (LocalSt E l (emp ∗ H)) s R) : Triple ge fe f (LocalSt E l H) s R := by
  rw [emp_sep_eq] at h; exact h

/-- `fifo_put(Q, p)`. -/
theorem call_put (ge : CGenv) {ce : CompositeEnv} (QC : QueueCenv ce)
    (hcenv : ge.genv_cenv = ce) {fMake : Function} (G : QueueFuns ge fMake) {f : Function}
    (l : List (Ident × Val)) (qb : Block) (c : List QElem) (e : QElem) (bk : Block)
    (F : HProp) (hp : e.ptr = .Vptr bk Integers.Ptrofs.zero)
    (hQ : (_Q, .Vptr qb Integers.Ptrofs.zero) ∈ l) (hP : (_p, .Vptr bk Integers.Ptrofs.zero) ∈ l) :
    Triple ge (FunctionEntry2 ge) f
      (LocalSt emptyEnv l ((fifo c (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep e) ∗ F))
      (.Scall none (.Evar _fifo_put (.Tfunction [tptr tfifo, tptr telem] tvoid cc_default))
        [.Etempvar _Q (tptr tfifo), .Etempvar _p (tptr telem)])
      (.only (LocalSt emptyEnv l (fifo (c ++ [e]) (.Vptr qb Integers.Ptrofs.zero) ∗ F))) := by
  refine triple_call_at_local ge _ f (fifoPutSpec c _ e) none _ _ l _ F _ G.bPut _
    [.Vptr qb Integers.Ptrofs.zero, e.ptr] G.sym_put G.find_put rfl
    (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get hQ))
      (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩))
      (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hp ▸ hT.get hP))
        (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, hp⟩)) EvalExprlist.nil))
    (fun h hh => ⟨rfl, hh⟩) (fifo_put_satisfies ge QC hcenv c _ e)
    (fun le v h1' h2 hT hpost hF hd => ⟨rfl, hT, h1', h2, hd, rfl, hpost.2, hF⟩)

section
variable (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (G : QueueFuns ge f_make_elem)

include hcenv G in
/-- `make_elem(a, b)` from a frame `F`. -/
theorem call_make (t : Ident) (l : List (Ident × Val)) (F : HProp) (a b : Nat)
    (hne : ∀ p ∈ l, p.1 ≠ t) :
    Triple ge (FunctionEntry2 ge) f_main (LocalSt emptyEnv l F)
      (.Scall (some t) (.Evar _make_elem (.Tfunction [tint, tint] (tptr telem) cc_default))
        [.Econst_int (Integers.Int.repr a) tint, .Econst_int (Integers.Int.repr b) tint])
      (.only (fun e le hp => ∃ bk, LocalSt emptyEnv ((t, .Vptr bk Integers.Ptrofs.zero) :: l)
        ((elemRep (mk bk a b) ∗ mallocToken bk sz16) ∗ F) e le hp)) := by
  refine triple_pre_emp (triple_call_at_local ge _ f_main (makeElemSpec _ _) (some t) _ _ l emp F
    _ G.bMake _ [.Vint (Integers.Int.repr a), .Vint (Integers.Int.repr b)] G.sym_make G.find_make
    rfl (fun le m _ => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (semCast_int m _)
      (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (semCast_int m _)
        EvalExprlist.nil)) (fun h hh => ⟨rfl, hh⟩)
    (make_elem_satisfies ge hcenv G.bS G.bM G.sym_S G.find_S G.sym_M G.find_M _ _)
    (fun le v h1' h2 hT hpost hF hd => ?_))
  obtain ⟨bk, rfl, hH⟩ := hpost
  exact ⟨bk, rfl, TempsHold_set hne hT, h1', h2, hd, rfl, hH, hF⟩

include hcenv in
/-- **`main` satisfies `main_spec`** (VST's `body_main`): `main` returns
    `1 + 10`. -/
theorem main_satisfies (G : QueueFuns ge f_make_elem) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_main) mainSpec [] := by
  refine Sep.satisfies_internal_noVars ge _ f_main _ _ (LocalSt emptyEnv [] emp)
    (fun m => ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide)
      (AllocVariables.nil _ _) rfl, fun hp hpre => ⟨rfl, TempsHold_nil _, hpre.2⟩⟩) ?_
  refine Sep.triple_seq ge _ f_main _ Sep.Assn.no _ _ _ ?_ (Sep.triple_vacuous ge _ f_main _ _)
  -- `Q = fifo_new();`
  refine triple_seq_only ge _ f_main (Q := fun e le hp => ∃ qb, LocalSt emptyEnv
    [(_Q, .Vptr qb Integers.Ptrofs.zero)] (fifo [] (.Vptr qb Integers.Ptrofs.zero)) e le hp) ?_ ?_
  · refine triple_seq_only ge _ f_main (Q := fun e le hp => ∃ qb, LocalSt emptyEnv
      [(_t'1, .Vptr qb Integers.Ptrofs.zero)] (fifo [] (.Vptr qb Integers.Ptrofs.zero)) e le hp)
      ?_ ?_
    · refine triple_pre_emp (triple_call_at_local ge _ f_main fifoNewSpec (some _t'1) _ _ [] emp
        emp _ G.bNew _ [] G.sym_new G.find_new rfl (fun _ _ _ => EvalExprlist.nil)
        (fun h hh => ⟨rfl, hh⟩)
        (fifo_new_satisfies ge queueCenv hcenv G.bS G.bM G.sym_S G.find_S G.sym_M G.find_M)
        (fun le v h1' h2 hT hpost hF hd => ?_))
      have hpost' := hpost
      obtain ⟨qb, _, _, rfl, _⟩ := hpost'
      refine ⟨qb, rfl, TempsHold_set (by temps_ne) hT, ?_⟩
      rw [show h2 = Heap.emp from hF, Heap.union_emp]
      exact hpost
    · refine triple_exists ge _ f_main _ _ _ (fun qb => ?_)
      exact triple_conseq ge _ f_main (triple_set_local ge _ f_main emptyEnv _ [] _ _Q _
        (.Vptr qb Integers.Ptrofs.zero) (fun _ hq => by simp at hq) (by temps_ne)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
        (fun _ _ _ x => x) (fun e le hp h => ⟨qb, h⟩) (fun _ _ _ x => x.elim)
        (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ f_main _ _ _ (fun qb => ?_)
  -- `p = make_elem(1, 10);`
  refine triple_seq_only ge _ f_main (Q := fun e le hp => ∃ bk1, LocalSt emptyEnv
    [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
    ((elemRep (mk bk1 1 10) ∗ mallocToken bk1 sz16) ∗ fifo [] (.Vptr qb Integers.Ptrofs.zero))
    e le hp) ?_ ?_
  · refine triple_seq_only ge _ f_main (call_make ge hcenv G _t'2 _ _ 1 10 (by temps_ne)) ?_
    refine triple_exists ge _ f_main _ _ _ (fun bk1 => ?_)
    exact triple_conseq ge _ f_main (triple_set_local ge _ f_main emptyEnv _
      [(_Q, .Vptr qb Integers.Ptrofs.zero)] _ _p _ (.Vptr bk1 Integers.Ptrofs.zero)
      (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bk1, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ f_main _ _ _ (fun bk1 => ?_)
  -- `fifo_put(Q, p);`
  refine triple_pre_sep (H := (fifo [] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1 10))
    ∗ mallocToken bk1 sz16) (by sep_cancel) ?_
  refine triple_seq_only ge _ f_main
    (call_put ge queueCenv hcenv G _ qb [] (mk bk1 1 10) bk1 _ rfl (by simp) (by simp)) ?_
  -- `p = make_elem(2, 20);`
  refine triple_seq_only ge _ f_main (Q := fun e le hp => ∃ bk2, LocalSt emptyEnv
    [(_p, .Vptr bk2 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
    ((elemRep (mk bk2 2 20) ∗ mallocToken bk2 sz16)
      ∗ (fifo ([] ++ [mk bk1 1 10]) (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk1 sz16))
    e le hp) ?_ ?_
  · refine triple_seq_only ge _ f_main (call_make ge hcenv G _t'3 _ _ 2 20 (by temps_ne)) ?_
    refine triple_exists ge _ f_main _ _ _ (fun bk2 => ?_)
    exact triple_conseq ge _ f_main (triple_set_local ge _ f_main emptyEnv _
      [(_Q, .Vptr qb Integers.Ptrofs.zero)] _ _p _ (.Vptr bk2 Integers.Ptrofs.zero)
      (fun _ hq => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢
                      exact Or.inr (Or.inr hq)) (by temps_ne)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ⟨bk2, h⟩) (fun _ _ _ x => x.elim)
      (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  refine triple_exists ge _ f_main _ _ _ (fun bk2 => ?_)
  -- `fifo_put(Q, p);`
  refine triple_pre_sep (H := (fifo ([] ++ [mk bk1 1 10]) (.Vptr qb Integers.Ptrofs.zero)
    ∗ elemRep (mk bk2 2 20)) ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16)) (by sep_cancel) ?_
  refine triple_seq_only ge _ f_main
    (call_put ge queueCenv hcenv G _ qb _ (mk bk2 2 20) bk2 _ rfl (by simp) (by simp)) ?_
  -- `p = fifo_get(Q);`
  refine triple_seq_only ge _ f_main (Q := LocalSt emptyEnv
    [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
    ((fifo [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1 10))
      ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16))) ?_ ?_
  · refine triple_seq_only ge _ f_main (triple_call_at_local ge _ f_main
      (fifoGetSpec [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) (mk bk1 1 10)) (some _t'4) _ _ _
      _ _ (LocalSt emptyEnv [(_t'4, .Vptr bk1 Integers.Ptrofs.zero),
        (_p, .Vptr bk2 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
        ((fifo [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1 10))
          ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16)))
      G.bGet _ [.Vptr qb Integers.Ptrofs.zero] G.sym_get G.find_get rfl
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
        (semCast_ptr_ptr m _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩)) EvalExprlist.nil)
      (fun h hh => ⟨rfl, hh⟩) (fifo_get_satisfies ge queueCenv hcenv _ _ _)
      (fun le v h1' h2 hT hpost hF hd => ?_)) ?_
    · obtain ⟨rfl, hH⟩ := hpost
      exact ⟨rfl, TempsHold_set (by temps_ne) hT, h1', h2, hd, rfl, hH, hF⟩
    · exact triple_set_local ge _ f_main emptyEnv _ [(_Q, .Vptr qb Integers.Ptrofs.zero)] _ _p _
        (.Vptr bk1 Integers.Ptrofs.zero)
        (fun _ hq => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq ⊢
                        exact Or.inr (Or.inr hq)) (by temps_ne)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
  -- the element `p`
  refine triple_pre ge _ f_main (P := fun e le hp => ∃ u, LocalSt emptyEnv
      [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)]
      (elemAt bk1 (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) (Integers.Int.repr 1)
        (.Vint (Integers.Int.repr 10)) u ∗ (mallocToken bk1 sz16
          ∗ (fifo [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))) e le hp)
    (fun e le hp hP => ?_) ?_
  · obtain ⟨he, hT, hH⟩ := hP
    have heq : ((fifo [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) ∗ elemRep (mk bk1 1 10))
        ∗ (mallocToken bk2 sz16 ∗ mallocToken bk1 sz16))
        = (elemRep (mk bk1 1 10) ∗ (mallocToken bk1 sz16
          ∗ (fifo [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))) := by
      sep_cancel
    rw [heq] at hH
    obtain ⟨h1, h2, hd, rfl, ⟨bk, o, u, hptr, hel⟩, hr⟩ := hH
    cases hptr
    exact ⟨u, he, hT, h1, h2, hd, rfl, hel, hr⟩
  refine triple_exists ge _ f_main _ _ _ (fun u => ?_)
  -- `i = p->a;`
  refine triple_seq_only ge _ f_main (triple_set_local ge _ f_main emptyEnv _
    [(_p, .Vptr bk1 Integers.Ptrofs.zero), (_Q, .Vptr qb Integers.Ptrofs.zero)] _ _i _
    (.Vint (Integers.Int.repr 1)) (fun _ h => h) (by temps_ne)
    (fun le m hp hT hH hag => ?_)) ?_
  · rw [elemAt_a_front] at hH
    exact eval_field_mapsto queueCenv.elemL hcenv (chunk := .Mint32) (ty := tint) queueCenv.elemL.off_head
      (Int.le_refl 0) (by decide) rfl rfl
      (hT.get (id := _p) (v := .Vptr bk1 Integers.Ptrofs.zero) (by simp))
      (by rw [Int.add_zero]; exact hH) hag
  -- `j = p->b;`
  refine triple_seq_only ge _ f_main (triple_set_local ge _ f_main emptyEnv _
    [(_i, .Vint (Integers.Int.repr 1)), (_p, .Vptr bk1 Integers.Ptrofs.zero),
      (_Q, .Vptr qb Integers.Ptrofs.zero)] _ _j _
    (.Vint (Integers.Int.repr 10)) (fun _ h => h) (by temps_ne)
    (fun le m hp hT hH hag => ?_)) ?_
  · rw [elemAt_b_front] at hH
    exact eval_field_mapsto queueCenv.elemL hcenv (chunk := .Mint32) (ty := tint) off_b
      (by decide) (by decide) rfl rfl
      (hT.get (id := _p) (v := .Vptr bk1 Integers.Ptrofs.zero) (by simp))
      hH hag
  -- `free(p);`
  refine triple_pre_sep (H := (mallocToken bk1 sz16 ∗ elemAt bk1
    (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) (Integers.Int.repr 1) (.Vint (Integers.Int.repr 10)) u)
    ∗ (fifo [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))
    (by sep_cancel) ?_
  refine triple_seq_only ge _ f_main (triple_call_at_local ge _ f_main (freeSpec bk1 sz16) none
    _free _ _ _ _ (LocalSt emptyEnv [(_j, .Vint (Integers.Int.repr 10)),
      (_i, .Vint (Integers.Int.repr 1)), (_p, .Vptr bk1 Integers.Ptrofs.zero),
      (_Q, .Vptr qb Integers.Ptrofs.zero)]
      (fifo [mk bk2 2 20] (.Vptr qb Integers.Ptrofs.zero) ∗ mallocToken bk2 sz16))
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
  -- `return i + j;`
  exact triple_return_local ge _ f_main _ _ _ _
    (.Vint (Integers.Int.add (Integers.Int.repr 1) (Integers.Int.repr 10)))
    (.Vint (Integers.Int.add (Integers.Int.repr 1) (Integers.Int.repr 10)))
    (fun le m hp hT _ _ => EvalExpr.Ebinop .Oadd _ _ _ _ _ _
      (EvalExpr.Etempvar _ _ _ (hT.get (v := .Vint (Integers.Int.repr 1)) (by simp)))
      (EvalExpr.Etempvar _ _ _ (hT.get (v := .Vint (Integers.Int.repr 10)) (by simp)))
      (semBinop_add_int _ _ _ _))
    (fun m => semCast_int m _) (fun _ _ => rfl)

end

end VST.Verif.Queue
