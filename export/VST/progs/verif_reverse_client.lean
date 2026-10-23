/-
  Port of VST's `progs/verif_reverse_client.v`: `last_foo` of
  `vst/progs/reverse_client.c`, a client of a separately compiled `reverse`.

      struct list {unsigned head; struct list *tail;};
      struct list *reverse (struct list *p);

      unsigned int last_foo(struct list * p) {
        unsigned int res;
        p = reverse (p);
        res = p -> head;
        return res;
      }

  VST's specifications:

      reverse_spec: WITH sigma, p
        PRE [tptr t_struct_list] PROP () PARAMS (p) SEP (listrep sigma p)
        POST [tptr t_struct_list] EX q, RETURN (q) SEP (listrep (rev sigma) q)

      last_foo_spec: WITH sigma, p, sigma', x
        PRE [tptr t_struct_list] PROP (sigma = sigma' ++ x :: nil) PARAMS (p)
          SEP (listrep sigma p)
        POST [tuint] RETURN (Vint x) SEP (TT)

  `reverse` is only *declared* in `reverse_client.c`.  As in VST (where
  `reverse_spec` is simply part of `Gprog`), `last_foo_satisfies` assumes that
  whatever function the symbol `reverse` resolves to meets `reverse_spec`.
  The specification and the list predicate are those of `verif_reverse`
  (`VST.Verif.Reverse.reverseSpec`, `listrepL`), not copies of them.

  `last_foo_satisfies_linked` then discharges that assumption when `reverse`
  is the function `f_reverse` of `reverse.c`, by `reverse_satisfies` of
  `verif_reverse`: the two translation units declare the same `struct list`,
  so they have the same composite environment (`compEnv_eq`).
-/
import VST.progs.reverse_client
import VST.progs.verif_reverse
open CC CC.Sep CC.HProp

namespace VST.Verif.ReverseClient

open Reverse_client
open VST.Verif.Reverse (tlist tlistp listrepL reverseSpec layout)

/-- Both files declare the same `struct list`. -/
theorem compEnv_eq : Reverse_client.prog.prog_comp_env = Reverse.prog.prog_comp_env := rfl

/-- `last_foo_spec` (`sigma = sigma' ++ [x]`; the postcondition's `TT` is any heap). -/
def lastFooSpec (p : Permission) (sigma' : List Integers.Int) (x : Integers.Int) (xv : Val) :
    Sep.FunSpec where
  tyargs := [tlistp]
  tyres := tuint
  cc := cc_default
  pre := fun vargs hp => vargs = [xv] ∧ listrepL p (sigma' ++ [x]) xv hp
  post := fun v _ => v = .Vint x
  measure := fun _ => 0

section
variable (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (p : Permission)
  (hpr : permOrder p .Readable = true)

theorem body_eq : f_last_foo.fn_body =
    .Ssequence
      (.Ssequence
        (.Scall (some _t'1) (.Evar _reverse (.Tfunction [tlistp] tlistp cc_default))
          [.Etempvar _p tlistp])
        (.Sset _p (.Etempvar _t'1 tlistp)))
      (.Ssequence
        (.Sset _res (.Efield (.Ederef (.Etempvar _p tlistp) tlist) _head tuint))
        (.Sreturn (some (.Etempvar _res tuint)))) := rfl

include hcenv hpr in
/-- **`last_foo` satisfies `last_foo_spec`** (VST's `body_last_foo`), assuming
    the function `fdRev` that `reverse` names meets `reverse_spec`. -/
theorem last_foo_satisfies (sigma' : List Integers.Int) (x : Integers.Int) (xv : Val)
    (bRev : Block) (fdRev : FunDef)
    (hsym : Genv.findSymbol ge.genv_genv _reverse = some bRev)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr bRev Integers.Ptrofs.zero) = some fdRev)
    (hty : typeOfFundef fdRev = .Tfunction [tlistp] tlistp cc_default)
    (hrev : ∀ (contents : List Integers.Int) (q : Val),
      Sep.SatisfiesAt ge (FunctionEntry2 ge) fdRev (reverseSpec p contents q) [q]) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_last_foo)
      (lastFooSpec p sigma' x xv) [xv] := by
  have hcenv' : ge.genv_cenv = layout.cenv := hcenv.trans compEnv_eq
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_last_foo _ _
    (fun e le hp => e = emptyEnv ∧ le.get _p = some xv ∧ listrepL p (sigma' ++ [x]) xv hp)
    (fun m => ?_) ?_
  · exact ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, PTree.gss _ _ _, hpre.2⟩⟩
  rw [body_eq]
  refine Sep.triple_seq_only ge _ f_last_foo (Q := fun e le hp => e = emptyEnv
      ∧ ∃ q, le.get _p = some q ∧ listrepL p (x :: sigma'.reverse) q hp) ?_ ?_
  -- `t'1 = reverse(p);`
  · refine Sep.triple_seq_only ge _ f_last_foo (Q := fun e le hp => e = emptyEnv
      ∧ ∃ q, le.get _t'1 = some q ∧ listrepL p (x :: sigma'.reverse) q hp) ?_ ?_
    · refine Sep.triple_call_at ge _ f_last_foo (reverseSpec p (sigma' ++ [x]) xv) (some _t'1)
        (.Evar _reverse (.Tfunction [tlistp] tlistp cc_default)) [.Etempvar _p tlistp] _ _
        bRev fdRev hfind hty rfl (fun e le hp m hP _ => ?_)
      obtain ⟨rfl, hx, hl⟩ := hP
      refine ⟨[xv], hp, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm,
        eval_callee_global (PTree.gempty _) hsym rfl,
        EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hx)
          (semCast_ptr_ptr m _ _ _ _ _ (isLink_of_listrep hl)) EvalExprlist.nil,
        ⟨rfl, hl⟩, hrev _ _, fun v h1' hpost _ => ⟨rfl, v, PTree.gss _ _ _, ?_⟩⟩
      rw [Heap.union_emp]
      have h : listrepL p (sigma' ++ [x]).reverse v h1' := hpost
      simpa using h
    -- `p = t'1;`
    · refine Sep.triple_set ge _ f_last_foo _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨he, q, hq, hl⟩ := hP
      exact ⟨_, EvalExpr.Etempvar _ _ _ hq, he, q, PTree.gss _ _ _, hl⟩
  -- `res = p->head;`
  refine Sep.triple_seq_only ge _ f_last_foo (Q := fun e le hp => e = emptyEnv
      ∧ le.get _res = some (.Vint x)) ?_ ?_
  · refine Sep.triple_set ge _ f_last_foo _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, q, hq, hl⟩ := hP
    obtain ⟨b, o, u, rfl, hn⟩ := hl
    exact ⟨_, eval_head layout hcenv' rfl hpr hq hn hag, he, PTree.gss _ _ _⟩
  -- `return res;`
  refine Sep.triple_return ge _ f_last_foo _ _ _ (fun e le hp m h _ => ?_)
  obtain ⟨he, hres⟩ := h
  refine ⟨_, _, m, hp, EvalExpr.Etempvar _res tuint _ hres, semCast_uint m _, ?_, rfl,
    fun _ hdj hag => ⟨hdj, hag⟩⟩
  rw [he]; exact freeList_emptyEnv _ _

end

/-- **`last_foo` linked with `reverse.c`**: when the symbol `reverse` resolves to
    `f_reverse` of `reverse.c` (and the list is held at a writable permission,
    as `reverse_spec` requires in `verif_reverse`), `last_foo` meets
    `last_foo_spec` with no assumption on `reverse`. -/
theorem last_foo_satisfies_linked (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (p : Permission) (hpw : permOrder p .Writable = true)
    (sigma' : List Integers.Int) (x : Integers.Int) (xv : Val) (bRev : Block)
    (hsym : Genv.findSymbol ge.genv_genv _reverse = some bRev)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr bRev Integers.Ptrofs.zero)
      = some (.Internal Reverse.f_reverse)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_last_foo)
      (lastFooSpec p sigma' x xv) [xv] :=
  last_foo_satisfies ge hcenv p (readable_of_writable hpw) sigma' x xv bRev _ hsym hfind rfl
    (fun contents q => VST.Verif.Reverse.reverse_satisfies ge (hcenv.trans compEnv_eq) p
      contents q hpw)

end VST.Verif.ReverseClient
