/-
  Usability checks for the Phase-7.5 closure theorem.

  `closure` is proved, so it is true.  The risk with a theorem of that shape is
  different: that its interface is unusable — that no realistic body obligation
  can be phrased in terms of `Avail`, or that the recursion cannot actually be
  closed.  The two theorems here discharge that concern by *using* it, for
  self-recursion and for mutual recursion, which are the cases
  `test/lean/corpus/funcs.c` exercises (`fact`, and `iseven`/`isodd`).

  These are interface checks, not program proofs: the function bodies are
  abstract.  Proving a concrete recursive function against its spec is Phase 7.7.
  Keeping them here is regression protection — changing the shape of `Avail`,
  `BodyOk` or `closure` will break these first.
-/
import CCLib
open CC CC.Sep

namespace SepCheck

/-- **Self-recursion closes.**  A body that meets its spec assuming *itself* at
    strictly smaller arguments meets it outright. -/
theorem selfRecursive_ok (ge : CGenv) (fe : EntryRel) (b : Block) (fn : Function)
    (S : FunSpec)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero)
             = some (.Internal fn))
    (hbody : BodyOk ge fe (fun b' => if b' = b then some S else none) fn S) :
    Satisfies ge fe (.Internal fn) S := by
  refine closure_satisfies ge fe (fun b' => if b' = b then some S else none) ?_ b S _
    (by simp) hfind
  intro b' S' fd' h1 h2
  by_cases hb : b' = b
  · subst hb
    try dsimp only at h1  -- older cores leave the spec-table lambda unreduced
    rw [if_pos rfl] at h1
    injection h1 with h1; subst h1
    rw [hfind] at h2
    injection h2 with h2; subst h2
    exact ⟨fn, rfl, hbody⟩
  · try dsimp only at h1
    rw [if_neg hb] at h1; exact absurd h1 (by simp)

/-- The two-function spec table used below. -/
def table (b1 b2 : Block) (S1 S2 : FunSpec) : SpecTable :=
  fun b => if b = b1 then some S1 else if b = b2 then some S2 else none

/-- **Mutual recursion closes.**  Two bodies, each allowed to call *either*
    function at a strictly smaller measure, both meet their specs outright.  This
    is the case a per-function induction cannot handle and a global measure can:
    neither function has to be "already done" before the other. -/
theorem mutualRecursive_ok (ge : CGenv) (fe : EntryRel) (b1 b2 : Block) (hne : b1 ≠ b2)
    (fn1 fn2 : Function) (S1 S2 : FunSpec)
    (hf1 : Genv.findFunct ge.genv_genv (.Vptr b1 Integers.Ptrofs.zero)
           = some (.Internal fn1))
    (hf2 : Genv.findFunct ge.genv_genv (.Vptr b2 Integers.Ptrofs.zero)
           = some (.Internal fn2))
    (hb1 : BodyOk ge fe (table b1 b2 S1 S2) fn1 S1)
    (hb2 : BodyOk ge fe (table b1 b2 S1 S2) fn2 S2) :
    Satisfies ge fe (.Internal fn1) S1 ∧ Satisfies ge fe (.Internal fn2) S2 := by
  have hall : ∀ (b : Block) (S : FunSpec) (fd : FunDef),
      table b1 b2 S1 S2 b = some S →
      Genv.findFunct ge.genv_genv (.Vptr b Integers.Ptrofs.zero) = some fd →
      ∃ fn, fd = .Internal fn ∧ BodyOk ge fe (table b1 b2 S1 S2) fn S := by
    intro b S fd h1 h2
    by_cases hb : b = b1
    · subst hb
      rw [table, if_pos rfl] at h1
      injection h1 with h1; subst h1
      rw [hf1] at h2; injection h2 with h2; subst h2
      exact ⟨fn1, rfl, hb1⟩
    · by_cases hb' : b = b2
      · subst hb'
        rw [table, if_neg hb, if_pos rfl] at h1
        injection h1 with h1; subst h1
        rw [hf2] at h2; injection h2 with h2; subst h2
        exact ⟨fn2, rfl, hb2⟩
      · rw [table, if_neg hb, if_neg hb'] at h1; exact absurd h1 (by simp)
  refine ⟨closure_satisfies ge fe _ hall b1 S1 _ ?_ hf1,
          closure_satisfies ge fe _ hall b2 S2 _ ?_ hf2⟩
  · rw [table, if_pos rfl]
  · rw [table, if_neg (Ne.symm hne), if_pos rfl]

/-! ## Tactic checks (Phase 7.6)

An untested tactic is worthless, so each one is exercised here. -/

open CC.HProp CC.Tactic

/-- `sep_cancel` reorders an arbitrarily permuted chain — the job a hand-rolled
    matcher would have had to do. -/
example (P Q R : HProp) : P ∗ (Q ∗ R) ⊢ R ∗ (Q ∗ P) := by sep_cancel
example (P Q R S : HProp) : ((P ∗ Q) ∗ R) ∗ S ⊢ S ∗ (R ∗ (Q ∗ P)) := by sep_cancel
example (P Q : HProp) : (P ∗ emp) ∗ Q = Q ∗ P := by sep_cancel

/-- And on realistic atoms: two `mapsto`s and an array, reordered. -/
example (p : Permission) (b : Block) (v w : Val) (n : Nat) (fn : Nat → Integers.Int) :
    mapsto .Mint32 p b 0 v ∗ (arrayU32 p b 8 n fn ∗ mapsto .Mint32 p b 4 w)
    ⊢ mapsto .Mint32 p b 4 w ∗ (mapsto .Mint32 p b 0 v ∗ arrayU32 p b 8 n fn) := by
  sep_cancel

/-- The cancellation theorem behind the tactic. -/
example (P Q R : HProp) : sepList [P, Q, R] = sepList [R, P, Q] :=
  sepList_perm
    (List.Perm.trans (List.Perm.cons P (List.Perm.swap R Q [])) (List.Perm.swap R P [Q]))

/-- `forward_set_last` steps over a trailing `Sset`, computing the postcondition
    so that nothing has to be guessed. -/
example (ge : CGenv) (fe : EntryRel) (f : Function) (id : Ident) (a : Expr)
    (P : Sep.Assn) (v : Env → TempEnv → Val)
    (hev : ∀ e le hp m, P e le hp → Heap.Agrees hp m → EvalExpr ge e le m a (v e le)) :
    Sep.Triple ge fe f P (.Sset id a)
      (Sep.ExitConds.only (fun e le hp => ∃ le0, le = le0.set id (v e le0) ∧ P e le0 hp)) := by
  forward_set_last
  exact hev

/-- `forward_set` steps over an `Sset` at the head of a sequence; the
    intermediate assertion is fixed by unification, not supplied. -/
example (ge : CGenv) (fe : EntryRel) (f : Function) (id : Ident) (a : Expr)
    (P : Sep.Assn) (R : Sep.ExitConds) (v : Env → TempEnv → Val)
    (hev : ∀ e le hp m, P e le hp → Heap.Agrees hp m → EvalExpr ge e le m a (v e le))
    (h2 : Sep.Triple ge fe f (fun e le hp => ∃ le0, le = le0.set id (v e le0) ∧ P e le0 hp)
            .Sskip R) :
    Sep.Triple ge fe f P (.Ssequence (.Sset id a) .Sskip) R := by
  forward_set v
  · exact hev
  · exact h2

/-! ## `memcpy` (Phase-9 Step 5)

`memcpy_satisfies` is proved, so it is true; the risk is again the interface.
Two checks:

* the precondition is **satisfiable** — a `memcpy` spec that nothing can meet
  would be worse than no spec;
* the alignment side conditions are **dischargeable** at a realistic
  instantiation (`al = 1`, the byte-copy case, which is what a `struct`
  assignment compiles to).

Non-overlap is deliberately *not* checked here: it is not a hypothesis at all —
`Heap.disjoint_ranges_nonoverlap` derives it from the `∗`. -/

section Memcpy
variable (bsrc bdst : Block) (osrc odst : Integers.Ptrofs)

/-- Source and destination fragments exist, for any byte lists, at any
    addresses — byte ranges carry no alignment constraint. -/
theorem memcpy_pre_satisfiable (src old : List MemVal) (hne : bsrc ≠ bdst) :
    ∃ h, (memcpySpec bsrc osrc .Readable bdst odst .Freeable src old).pre
      [Val.Vptr bdst odst, Val.Vptr bsrc osrc] h := by
  obtain ⟨h1, h1m⟩ := bytesPtsTo_exists bsrc .Readable src (Integers.Ptrofs.unsigned osrc)
  obtain ⟨h2, h2m⟩ := bytesPtsTo_exists bdst .Freeable old (Integers.Ptrofs.unsigned odst)
  -- different blocks, so the two fragments are disjoint for free
  have hd : Heap.disjoint h1 h2 := by
    intro bb oo
    by_cases hb : bb = bsrc
    · exact Or.inr (bytesPtsTo_none bdst .Freeable old _ h2 h2m bb oo
        (Or.inl (by rw [hb]; exact hne)))
    · exact Or.inl (bytesPtsTo_none bsrc .Readable src _ h1 h1m bb oo (Or.inl hb))
  exact ⟨Heap.union h1 h2, pure_sep_intro rfl ⟨h1, h2, hd, rfl, h1m, h2m⟩⟩

/-- At `al = 1` every alignment condition is trivial, so the specification is
    reachable: this is the full hypothesis list of `memcpy_satisfies`, all
    discharged. -/
theorem memcpy_byte_copy (ge : CGenv) (fe : EntryRel) (src old : List MemVal)
    (targs : List Ty) (tres : Ty) (cc : CallConv) (hlen : old.length = src.length) :
    SatisfiesAt ge fe
      (.External (.EF_memcpy ((src.length : Nat) : _root_.Int) 1) targs tres cc)
      (memcpySpec bsrc osrc .Readable bdst odst .Freeable src old)
      [Val.Vptr bdst odst, Val.Vptr bsrc osrc] :=
  memcpy_satisfies ge fe 1 bsrc osrc .Readable bdst odst .Freeable src old
    targs tres cc rfl rfl hlen (Or.inl rfl) (Int.emod_one _)
    (fun _ => Int.emod_one _) (fun _ => Int.emod_one _)

end Memcpy

end SepCheck
