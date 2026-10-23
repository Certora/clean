/-
  Usability check for the Phase-9 Step-10 temporary-state layer
  (`CCLib.logic.Temps`).

  The claim being tested is the *asymptotic* one: a statement's proof obligation is
  **O(1) in the number of tracked temporaries** instead of O(N).  So the check is
  a `Sset` step over a deliberately long tracked list, discharged by exactly the
  same two one-liners as a step over a two-entry list.  If the cost were still
  per-temporary, this file would grow with the list; it does not.

  It also pins the thing that made it possible: `temps_ne` is kernel `decide`,
  which works only because `identOfString` reduces (see `CCLib.lib.Positive`).  If
  that regresses, this file fails rather than silently falling back.

  The second half of the file covers `localst_fwd`, which extends the same claim
  from a single step to a **chain** of them: the mid-conditions are computed by
  `setLocal` rather than written out, so an N-assignment chain costs N `EvalExpr`
  obligations and no tracked lists at all.
-/
import CCLib
open CC CC.Sep CC.HProp

namespace TempsCheck

/-! Identifiers in the shape `clightgen -lean` emits: named C variables through
    `identOfString`, `-normalize` temporaries as consecutive positives. -/
def _adler : Ident := identOfString "adler"
def _buf : Ident := identOfString "buf"
def _len : Ident := identOfString "len"
def _n : Ident := identOfString "n"
def _sum2 : Ident := identOfString "sum2"
def _t'1 : Ident := (Positive.ofNat 128)
def _t'2 : Ident := (Positive.ofNat 129)
def _t'3 : Ident := (Positive.ofNat 130)
def _t'4 : Ident := (Positive.ofNat 131)
def _t'5 : Ident := (Positive.ofNat 132)
def _t'6 : Ident := (Positive.ofNat 133)
def _t'7 : Ident := (Positive.ofNat 134)
def _t'8 : Ident := (Positive.ofNat 135)
def _t'9 : Ident := (Positive.ofNat 136)
def _t'10 : Ident := (Positive.ofNat 137)
def _t'11 : Ident := (Positive.ofNat 138)
def _t'12 : Ident := (Positive.ofNat 139)
def _t'13 : Ident := (Positive.ofNat 140)
def _t'14 : Ident := (Positive.ofNat 141)
def _t'15 : Ident := (Positive.ofNat 142)
def _t'16 : Ident := (Positive.ofNat 143)
def _t'17 : Ident := (Positive.ofNat 144)

/-- Twenty tracked temporaries — more than a typical function tracks at any one
    point.

    `abbrev`, not `def`: the tactics work on the list's *structure*, so a named
    tracked list has to be reducible (noted in `CCLib.logic.Temps`). -/
abbrev wide (b : Block) (ofs0 : Integers.Ptrofs) : List (Ident × Val) :=
  [(_buf, .Vptr b ofs0), (_len, .Vlong 0), (_n, .Vint 0),
   (_t'1, .Vlong 0), (_t'2, .Vptr b ofs0), (_t'3, .Vint 0), (_t'4, .Vlong 0),
   (_t'5, .Vptr b ofs0), (_t'6, .Vint 0), (_t'7, .Vint 0), (_t'8, .Vint 0),
   (_t'9, .Vint 0), (_t'10, .Vint 0), (_t'11, .Vint 0), (_t'12, .Vint 0),
   (_t'13, .Vint 0), (_t'14, .Vint 0), (_t'15, .Vint 0), (_t'16, .Vint 0),
   (_t'17, .Vint 0)]

/-- The side conditions of `triple_set_local` at twenty tracked temporaries:
    two one-liners, exactly as at two. -/
example (b : Block) (ofs0 : Integers.Ptrofs) :
    (∀ q ∈ wide b ofs0, q ∈ wide b ofs0) ∧ (∀ q ∈ wide b ofs0, q.1 ≠ _sum2) :=
  ⟨by temps_mem, by temps_ne⟩

/-- A whole `Sset` step at twenty tracked temporaries: the same shape as a step
    over two, and it would be identical at a hundred. -/
example (ge : CGenv) (fe : EntryRel) (f : Function) (b : Block)
    (ofs0 : Integers.Ptrofs) (H : HProp) (v : Integers.Int64) :
    Sep.Triple ge fe f (Sep.LocalSt emptyEnv (wide b ofs0) H)
      (.Sset _sum2 (.Econst_long v tulong))
      (.only (Sep.LocalSt emptyEnv ((_sum2, .Vlong v) :: wide b ofs0) H)) := by
  refine Sep.triple_set_local ge fe f _ _ _ _ _ _ (.Vlong v)
    (by temps_mem) (by temps_ne) (fun le m hp hT _ _ => ?_)
  exact EvalExpr.Econst_long _ _

/-- Reading a temporary back out of a long list is also one line, and picks the
    right entry without any distinctness bookkeeping. -/
example (b : Block) (ofs0 : Integers.Ptrofs) (le : TempEnv)
    (hT : Sep.TempsHold (wide b ofs0) le) : le.get _t'13 = some (.Vint 0) :=
  hT.get (by temps_mem)

/-- Dropping a stale entry (what an *update* to an already-tracked temporary
    needs) is the same one-liner. -/
example (b : Block) (ofs0 : Integers.Ptrofs) :
    ∀ q ∈ [(_buf, Val.Vptr b ofs0), (_n, Val.Vint 0)],
      q ∈ (_len, Val.Vlong 0) :: [(_buf, Val.Vptr b ofs0), (_n, Val.Vint 0)] := by
  temps_mem

/-- The load-bearing fact: identifier disequality is *kernel* decidable.  This
    is what removed `native_decide` (and its axiom) from every milestone
    theorem. -/
example : _adler ≠ _sum2 := by decide
example : _t'17 ≠ _t'7 := by decide

/-! ## `localst_fwd`: the mid-conditions are computed, not written

The Step-10 layer made a single step O(1) in the number of tracked temporaries.
What it did *not* do was make a **chain** of steps cheap: `triple_seq_fwd` takes
its mid-condition explicitly, so an N-assignment chain cost N tracked lists
written out by hand.

`localst_fwd` (`CCLib.logic.Temps`) closes it: `setLocal` computes the post-state, so
`triple_set_local`'s `hsub`/`hne` become theorems and a chain leaves exactly one
goal per assignment — its `EvalExpr` obligation, the only part that is not
bookkeeping.  It cut `work_step` from 117 lines to 57.

The checks below pin the three things that can regress. -/

/-- **A four-assignment chain, with no tracked list written anywhere.**  Contrast
    the twenty-temporary `Sset` example above, which needed the list once; a chain
    used to need it once *per assignment*.  Here the postcondition is stated as the
    `setLocal` chain the tactic computes, so the values are inferred too. -/
example (ge : CGenv) (fe : EntryRel) (f : Function) (b : Block)
    (ofs0 : Integers.Ptrofs) (H : HProp) :
    Sep.Triple ge fe f (Sep.LocalSt emptyEnv (wide b ofs0) H)
      (.Ssequence (.Sset _t'1 (.Econst_long 7 tulong))
        (.Ssequence (.Sset _t'2 (.Econst_long 8 tulong))
          (.Ssequence (.Sset _t'3 (.Econst_long 9 tulong))
                      (.Sset _t'4 (.Econst_long 10 tulong)))))
      (.only (Sep.LocalSt emptyEnv
        (Sep.setLocal (Sep.setLocal (Sep.setLocal (Sep.setLocal
          (wide b ofs0) _t'1 (.Vlong 7)) _t'2 (.Vlong 8))
          _t'3 (.Vlong 9)) _t'4 (.Vlong 10)) H)) := by
  localst_fwd
  all_goals (intro le m hp _ _ _; exact EvalExpr.Econst_long _ _)

/-- **`localst_fwd` stops at a statement it does not own.**  The `if` is left as a
    goal — that is the design, not a gap: a branch is where a decision has to be
    made.  Here the two assignments before it are still chained automatically. -/
example (ge : CGenv) (fe : EntryRel) (f : Function) (b : Block)
    (ofs0 : Integers.Ptrofs) (H : HProp) :
    Sep.Triple ge fe f (Sep.LocalSt emptyEnv (wide b ofs0) H)
      (.Ssequence (.Sset _t'1 (.Econst_long 7 tulong))
        (.Ssequence (.Sset _t'2 (.Econst_long 8 tulong))
          (.Sifthenelse (.Etempvar _t'1 tulong) .Sbreak .Sbreak)))
      { normal := Sep.Assn.no,
        brk := Sep.LocalSt emptyEnv
          (Sep.setLocal (Sep.setLocal (wide b ofs0) _t'1 (.Vlong 7))
            _t'2 (.Vlong 8)) H,
        cont := Sep.Assn.no,
        ret := fun _ _ => False } := by
  localst_fwd
  · intro le m hp _ _ _; exact EvalExpr.Econst_long _ _
  · intro le m hp _ _ _; exact EvalExpr.Econst_long _ _
  · -- the `if`, left for us: both arms break, so either guard value works
    refine Sep.triple_if_local ge fe f _ _ _ _ true _ _ _
      (fun le m hp hT _ _ => ?_) (Sep.triple_break ge fe f _)
    exact ⟨.Vlong 7, EvalExpr.Etempvar _t'1 tulong _ (hT.get (by temps_get)), rfl⟩

/-- **Reading a temporary back out of a chain**, which is what `temps_get` exists
    for.  `temps_mem` alone cannot do it: `simp` turns the membership into a
    disjunction of pairwise equalities and stalls, because the tracked *values*
    carry free variables so `decide` refuses the goal.  `temps_get` peels the chain
    with `mem_setLocal_of_mem'` instead, which puts two bare identifiers in front
    of `decide` and leaves the values alone. -/
example (b : Block) (ofs0 : Integers.Ptrofs) (le : TempEnv) (v w : Val)
    (hT : Sep.TempsHold
      (Sep.setLocal (Sep.setLocal (wide b ofs0) _t'1 v) _t'2 w) le) :
    le.get _t'2 = some w ∧ le.get _t'1 = some v ∧ le.get _buf = some (.Vptr b ofs0) :=
  ⟨hT.get (by temps_get), hT.get (by temps_get), hT.get (by temps_get)⟩

end TempsCheck
