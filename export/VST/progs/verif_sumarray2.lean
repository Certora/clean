/-
  Port of VST's `progs/verif_sumarray2.v`: the `sumarray` of
  `vst/progs/sumarray2.c`, written with a `for` loop
  (`s=0; for (i=0; i<n; i++) s += a[i];`), meets the specification of the
  `sumarray` of `sumarray.c` (VST's `sumarray_spec` is the same in both files).

  Everything but the shape of the loop is shared with the port of
  `verif_sumarray.v` (`VST.Verif.Sumarray`): the specification
  `sumarraySpec`, the assertions (`LInv`, `LMid`, `LSummed`, `LAfter`, `Done`,
  `Ret`) and the triples of the loop guard (`if_triple`), of `s += a[i]`
  (`sum_triple`) and of `i++` (`incr_triple`).  Here `i++` is the increment
  part of the `for` loop (the second statement of `Sloop`), where it was the end
  of the body of the `while` loop of `sumarray.c`.

  VST's `forward_for_simple_bound` invariant says that `s` is the sum of the
  first `i` elements; it is `LInv` (with `k = size - i` iterations left).
-/
import VST.progs.sumarray2
import VST.progs.verif_sumarray
open CC CC.Sep CC.HProp
open Sumarray2
open VST.Verif.Sumarray (sumTo elems sumTo_elems_length sumarraySpec Distinct
  idents_distinct ifStmt setT1 setS setI retStmt St LInv LMid LSummed LAfter Done Ret LoopR
  Pre if_triple sum_triple incr_triple)

namespace VST.Verif.Sumarray2

/-- The side conditions of `function_entry2` for `sumarray`. -/
theorem entry_wf :
    listNorepet (varNames f_sumarray.fn_vars)
    ∧ listNorepet (varNames f_sumarray.fn_params)
    ∧ listDisjoint (varNames f_sumarray.fn_params) (varNames f_sumarray.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The `for` loop, and the body. -/
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt (.Ssequence setT1 setS)) setI
def fullBody : Stmt :=
  .Ssequence (.Sset _s (.Econst_int (Integers.Int.repr 0) tint))
    (.Ssequence (.Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 0) tint)) loopStmt)
      retStmt)

theorem body_eq : f_sumarray.fn_body = fullBody := rfl

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block)
variable (ofs0 : Integers.Ptrofs) (L : Nat) (f : Nat → Integers.Int)

/-- The `for` loop: it terminates, and leaves with the sum of all the
    elements. -/
theorem loop_triple (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616)
    (k : Nat) :
    Sep.Triple ge fe f_sumarray (LInv p b ofs0 L f k) loopStmt (LoopR p b ofs0 L f) := by
  refine Sep.triple_loop ge fe f_sumarray (LoopR p b ofs0 L f) (LInv p b ofs0 L f)
    (LSummed p b ofs0 L f) _ _ (fun k => ?_) (fun k => ?_) k
  · refine Sep.triple_seq ge fe f_sumarray _ (LMid p b ofs0 L f k) _ _ _
      (Sep.triple_conseq ge fe f_sumarray (if_triple ge fe p b ofs0 L f k hL)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim)) ?_
    exact Sep.triple_fallthrough ge fe f_sumarray _ _ _ _
      (sum_triple ge fe p b ofs0 L f k hd hpr hL hno) (fun _ _ _ x => x)
  · refine Sep.triple_fallthrough ge fe f_sumarray _ _ _ _
      (incr_triple ge fe p b ofs0 L f k hd) (fun e le hp h => ?_)
    obtain ⟨iv, hSt, hiv, hk⟩ := h
    exact ⟨L - iv, by omega, iv, hSt, hiv, rfl⟩

/-- **The body of `sumarray`** (`sumarray2.c`): it returns the sum of the
    elements and hands the array back. -/
theorem sumarray_body (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_sumarray (Pre p b ofs0 L f) fullBody
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p b ofs0 L f } := by
  -- s = 0
  refine Sep.triple_seq_only ge fe f_sumarray (Q := fun e le hp =>
      Pre p b ofs0 L f e le hp ∧ le.get _s = some (.Vint (Integers.Int.repr 0))) ?_ ?_
  · refine Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, ha, hn, harr⟩ := hP
    exact ⟨_, EvalExpr.Econst_int _ tint, ⟨he, (PTree.gso _ _ _ _ hd.s_a).trans ha,
      (PTree.gso _ _ _ _ hd.s_n).trans hn, harr⟩, PTree.gss _ _ _⟩
  refine Sep.triple_seq ge fe f_sumarray _ (Done p b ofs0 L f) _ _ _ ?_ ?_
  · -- i = 0; the loop
    refine Sep.triple_seq_only ge fe f_sumarray (Q := LInv p b ofs0 L f L) ?_ ?_
    · refine Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨⟨he, ha, hn, harr⟩, hs⟩ := hP
      exact ⟨_, EvalExpr.Econst_int _ tint, 0, ⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha,
        (PTree.gso _ _ _ _ hd.i_n).trans hn, PTree.gss _ _ _,
        (PTree.gso _ _ _ _ hd.s_i.symm).trans hs, trivial, harr⟩, by omega, by omega⟩
    · exact Sep.triple_conseq ge fe f_sumarray (loop_triple ge fe p b ofs0 L f hd hpr hL hno L)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)
  · -- return s
    refine Sep.triple_return ge fe f_sumarray _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hs, harr⟩ := h
    refine ⟨.Vint (sumTo f L), .Vint (sumTo f L), m, hp, EvalExpr.Etempvar _s tuint _ hs,
      semCast_uint m _, ?_, ⟨rfl, harr⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

/-- **`sumarray` (`sumarray2.c`) satisfies `sumarray_spec`** (VST's
    `body_sumarray` of `verif_sumarray2.v`), with the specification of the port
    of `verif_sumarray.v`: the array is readable, its size is at most
    `Int.max_signed`, and it fits in the address space. -/
theorem sumarray_satisfies (contents : List Integers.Int)
    (hpr : permOrder p .Readable = true)
    (hL : (contents.length : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sumarray)
      (sumarraySpec p b ofs0 contents)
      [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_sumarray _ _
    (Pre p b ofs0 contents.length (elems contents)) (fun m => ?_) ?_
  · refine ⟨PTree.set _n (.Vint (Integers.Int.repr contents.length))
              (PTree.set _a (.Vptr b ofs0) (createUndefTemps f_sumarray.fn_temps)),
            FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    obtain ⟨_, harr⟩ := hpre
    exact ⟨rfl, (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _), PTree.gss _ _ _, harr⟩
  · have h := body_eq ▸ sumarray_body ge (FunctionEntry2 ge) p b ofs0 contents.length
      (elems contents) idents_distinct hpr hL hno
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_sumarray h (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    obtain ⟨hv, harr⟩ := hr
    exact ⟨by rw [hv, sumTo_elems_length], harr⟩

end
end VST.Verif.Sumarray2
