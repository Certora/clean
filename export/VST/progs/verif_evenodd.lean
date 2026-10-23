/-
  Port of VST's `progs/verif_evenodd.v`: the mutually recursive `even` and
  `odd` of `vst/progs/evenodd.c` compute the parity of their (unsigned)
  argument.

  VST's specifications:

      DECLARE _even
       WITH z : Z, v : val
       PRE [ _n OF tuint] PROP(repr z v) LOCAL (`(eq v) (eval_id _n)) SEP ()
       POST [ tint ] local (`(eq (Vint (if Z.even z then Int.one else Int.zero))) retval).

  (and `odd` with `Z.odd`), where `repr z v` says `v = Vint (Int.repr z)` and
  `z ≥ 0`.  Here `z` is a natural number `n` below `2^32` (so that `n` is the
  value of the C `unsigned` argument), and the result is `parityRes b n`
  (`b = true` for `even`).

  The two functions call each other, so their specifications are proved
  together: `Sep.satisfies_rec` over `W = Bool × {n // n < 2^32}` (which
  function, and VST's `WITH z`) with the measure `n`.  Both bodies have the same
  shape (`if (n == 0) return c; return other(n - 1);`), so one lemma,
  `body_ok`, proves both.  The theorems assume that the globals `even` and `odd`
  are these functions (VST's `Gprog`).
-/
import VST.progs.evenodd
import CCLib
open CC CC.Sep CC.HProp
open Evenodd

namespace VST.Verif.Evenodd

/-- The result of `even n` (`b = true`) or `odd n` (`b = false`). -/
def parityRes (b : Bool) (n : Nat) : Integers.Int :=
  if (n % 2 == 0) = b then Integers.Int.repr 1 else Integers.Int.repr 0

theorem parityRes_succ (b : Bool) (n : Nat) : parityRes b (n + 1) = parityRes (!b) n := by
  unfold parityRes
  cases b <;> by_cases h : n % 2 = 0 <;>
    simp [h, show ((n + 1) % 2 = 0) ↔ ¬ (n % 2 = 0) by omega]

/-- `even_spec` (`b = true`) and `odd_spec` (`b = false`) at `n`. -/
def eoSpec (b : Bool) (n : Nat) : Sep.FunSpec where
  tyargs := [tuint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vint (Integers.Int.repr n)] ∧ hp = Heap.emp
  post := fun v hp => v = .Vint (parityRes b n) ∧ hp = Heap.emp
  measure := fun _ => 0

/-- The common shape of the two bodies:
    `if (n == 0) return c; t = callee(n - 1); return t;`. -/
def eoBody (callee : Ident) (c : _root_.Int) : Stmt :=
  .Ssequence
    (.Sifthenelse (.Ebinop .Oeq (.Etempvar _n tuint) (.Econst_int (Integers.Int.repr 0) tint) tint)
      (.Sreturn (some (.Econst_int (Integers.Int.repr c) tint))) .Sskip)
    (.Ssequence
      (.Scall (some _t'1) (.Evar callee (.Tfunction [tuint] tint cc_default))
        [.Ebinop .Osub (.Etempvar _n tuint) (.Econst_int (Integers.Int.repr 1) tint) tuint])
      (.Sreturn (some (.Etempvar _t'1 tint))))

theorem even_body_eq : f_even.fn_body = eoBody _odd 1 := rfl
theorem odd_body_eq : f_odd.fn_body = eoBody _even 0 := rfl

section
variable (ge : CGenv)

/-- One body, `even` or `odd`: given that the callee meets the other
    specification at `n - 1`, the function meets its specification at `n`. -/
theorem body_ok (f : Function) (b : Bool) (callee : Ident) (cb : Block) (fdc : FunDef)
    (hsym : Genv.findSymbol ge.genv_genv callee = some cb)
    (hfind : Genv.findFunct ge.genv_genv (.Vptr cb Integers.Ptrofs.zero) = some fdc)
    (hty : typeOfFundef fdc = .Tfunction [tuint] tint cc_default)
    (hbody : f.fn_body = eoBody callee (if b then 1 else 0))
    (hparams : f.fn_params = [(_n, tuint)]) (hvars : f.fn_vars = [])
    (htemps : f.fn_temps = [(_t'1, tint)]) (hret : f.fn_return = tint)
    (n : Nat) (hn : (n : _root_.Int) < 4294967296)
    (IH : 0 < n → Sep.SatisfiesAt ge (FunctionEntry2 ge) fdc (eoSpec (!b) (n - 1))
      [.Vint (Integers.Int.repr ((n - 1 : Nat) : _root_.Int))]) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f) (eoSpec b n)
      [.Vint (Integers.Int.repr n)] := by
  let L : TempEnv := (createUndefTemps f.fn_temps).set _n (.Vint (Integers.Int.repr n))
  have hL : L.get _n = some (.Vint (Integers.Int.repr n)) := PTree.gss _ _ _
  have hL1 : ∀ v, (L.set _t'1 v).get _t'1 = some v := fun _ => PTree.gss _ _ _
  refine satisfies_at ge f _ _ L (by rw [hvars]; decide) (by rw [hparams]; decide)
    (by rw [hparams, htemps]; decide) hvars (by rw [hparams]; rfl) (fun _ h => h.2) ?_
  rw [hbody]
  -- `n == 0`
  have hev : ∀ m, EvalExpr ge emptyEnv L m
      (.Ebinop .Oeq (.Etempvar _n tuint) (.Econst_int (Integers.Int.repr 0) tint) tint)
      (Val.ofBool (decide (n = 0))) := by
    intro m
    have h := EvalExpr.Ebinop (ge := ge) (e := emptyEnv) (le := L) (m := m) .Oeq
      (.Etempvar _n tuint) (.Econst_int (Integers.Int.repr 0) tint) tint _ _ _
      (EvalExpr.Etempvar _ tuint _ hL) (EvalExpr.Econst_int _ tint) (semBinop_eq_uint_int _ _ _ _)
    rw [eq_repr_unsigned (n : _root_.Int) 0 (by omega) hn (by omega) (by omega)] at h
    have : decide ((n : _root_.Int) = 0) = decide (n = 0) := decide_eq_decide.mpr (by omega)
    rwa [this] at h
  refine Sep.triple_seq ge _ f _ (fun e le hp => At L e le hp ∧ 0 < n) _ _ _
    (triple_if_at ge _ _ _ _ _ _ _ (decide (n = 0)) hev
      (fun m => by simpa [typeof] using boolVal_ofBool_int m (decide (n = 0))) ?_) ?_
  · by_cases h0 : n = 0
    · subst h0
      simp only [decide_true, if_true]
      refine Sep.triple_conseq ge _ f
        (triple_return_at ge _ L _ _ (.Vint (parityRes b 0)) (fun _ => EvalExpr.Econst_int _ tint)
          (fun m => by rw [hret]; cases b <;> exact semCast_int m _))
        (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)
    · simp only [h0, decide_false]
      exact Sep.triple_fallthrough ge _ f _ _ _ _ (Sep.triple_skip ge _ f _)
        (fun e le hp hP => ⟨hP, by omega⟩)
  -- `t = callee(n - 1); return t;`
  intro k e le hp hf m hd hag ⟨hAt, hpos⟩
  revert k e le hp hf m hd hag hAt
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hsub : Integers.Int.sub (Integers.Int.repr ((j + 1 : Nat) : _root_.Int))
      (Integers.Int.repr 1) = Integers.Int.repr ((j + 1 - 1 : Nat) : _root_.Int) := by
    rw [repr_sub]; congr 1
    show ((j + 1 : Nat) : _root_.Int) - 1 = ((j + 1 - 1 : Nat) : _root_.Int)
    omega
  refine Sep.triple_seq_only ge _ f
    (Q := At (L.set _t'1 (.Vint (parityRes (!b) (j + 1 - 1))))) ?_ ?_
  · refine Sep.triple_call_at ge _ f (eoSpec (!b) (j + 1 - 1)) _ _ _ _ _ cb _ hfind hty rfl
      (fun e le hp m hP _ => ?_)
    obtain ⟨rfl, rfl, rfl⟩ := hP
    refine ⟨_, Heap.emp, Heap.emp, Heap.disjoint_emp_left _, (Heap.emp_union _).symm,
      eval_callee_global (PTree.gempty _) hsym rfl,
      EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Ebinop .Osub _ _ _ _ _ _
        (EvalExpr.Etempvar _ tuint _ hL) (EvalExpr.Econst_int _ tint)
        (semBinop_sub_uint_int _ _ _ _)) (by rw [hsub]; exact semCast_uint m _)
        EvalExprlist.nil,
      ⟨rfl, rfl⟩, IH (by omega), fun v h1' hpost _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := hpost
    exact ⟨rfl, rfl, Heap.emp_union _⟩
  · refine Sep.triple_conseq ge _ f
      (triple_return_at ge _ _ _ _ (.Vint (parityRes b (j + 1)))
        (fun _ => EvalExpr.Etempvar _ tint _ (hL1 _))
        (fun m => by
          rw [hret, parityRes_succ, show j + 1 - 1 = j by omega]
          exact semCast_int m _))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)

/-- `W`: which function (`true` for `even`), and VST's `WITH z`. -/
def W : Type := Bool × {n : Nat // (n : _root_.Int) < 4294967296}

/-- The function `w` names. -/
def eoFun (w : W) : FunDef := if w.1 then .Internal f_even else .Internal f_odd

/-- **`even` and `odd` satisfy `even_spec` and `odd_spec`** (VST's `body_even`
    and `body_odd`), for `n < 2^32`, given that the globals `even` and `odd`
    are these functions. -/
theorem evenodd_satisfies (be bo : Block)
    (hsym_e : Genv.findSymbol ge.genv_genv _even = some be)
    (hfind_e : Genv.findFunct ge.genv_genv (.Vptr be Integers.Ptrofs.zero)
      = some (.Internal f_even))
    (hsym_o : Genv.findSymbol ge.genv_genv _odd = some bo)
    (hfind_o : Genv.findFunct ge.genv_genv (.Vptr bo Integers.Ptrofs.zero)
      = some (.Internal f_odd))
    (n : Nat) (hn : (n : _root_.Int) < 4294967296) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_even) (eoSpec true n)
      [.Vint (Integers.Int.repr n)]
    ∧ Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_odd) (eoSpec false n)
      [.Vint (Integers.Int.repr n)] := by
  have H := satisfies_rec ge _ eoFun (fun w : W => eoSpec w.1 w.2.1) (fun w => w.2.1)
    (fun w IH vargs k m hp hf hk hpre => by
      obtain ⟨b, n, hn⟩ := w
      obtain ⟨rfl, hemp⟩ := hpre
      have IH' : 0 < n → Sep.SatisfiesAt ge (FunctionEntry2 ge) (eoFun (!b, ⟨n - 1, by omega⟩))
          (eoSpec (!b) (n - 1)) [.Vint (Integers.Int.repr ((n - 1 : Nat) : _root_.Int))] :=
        fun hpos => IH (!b, ⟨n - 1, by omega⟩) (by show n - 1 < n; omega) _
      cases b
      · exact body_ok ge f_odd false _even be _ hsym_e hfind_e rfl rfl rfl rfl rfl rfl n hn IH'
          k m hp hf hk ⟨rfl, hemp⟩
      · exact body_ok ge f_even true _odd bo _ hsym_o hfind_o rfl rfl rfl rfl rfl rfl n hn IH'
          k m hp hf hk ⟨rfl, hemp⟩)
  exact ⟨H (true, ⟨n, hn⟩) _, H (false, ⟨n, hn⟩) _⟩

end

end VST.Verif.Evenodd
