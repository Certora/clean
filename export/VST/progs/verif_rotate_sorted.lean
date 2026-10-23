/-
  Port of VST's `progs/verif_rotate.v`, second half: `sorted_rotate`
  (`vst/progs/rotate.c`) calls `rotate` and adds `N` to the elements that
  wrapped around, so a sorted array with elements in `[0, N]` stays sorted.

      void sorted_rotate(int *a, int n, int k, int N) {
        rotate(a, n, k);
        for(int i = n-k; i < n; i++)
          a[i] += N;
      }

  VST's specification:

      DECLARE _sorted_rotate
       WITH sh : share, a : val, s : list Z, n : Z, k : Z, N : Z, gv : globals
       PRE [ tptr tint , tint, tint, tint]
         PROP(writable_share sh; 0 <= n; 0 <= 4 * n <= Ptrofs.max_unsigned;
              0 < k < n; 0 <= N*2 < Int.max_signed;
              Forall (fun x => 0 <= x <= N) s; sorted Z.le s)
         PARAMS (a; Vint (Int.repr n); Vint (Int.repr k); Vint (Int.repr N)) GLOBALS (gv)
         SEP (mem_mgr gv; data_at sh (tarray tint n) (map Vint (map Int.repr s)) a)
       POST [ tvoid ]
         PROP(sorted Z.le (sorted_rotate s k N))
         RETURN()
         SEP (mem_mgr gv; data_at sh (tarray tint n)
                (map Vint (map Int.repr (sorted_rotate s k N))) a).

  `sorted` is Lean core's `List.Pairwise (· ≤ ·)`.  The call to `rotate` uses
  `rotate_satisfies` (`verif_rotate`).  VST's bound `0 <= N*2 < Int.max_signed`
  rules out signed overflow, which is undefined in C; in CompCert's semantics
  `int` addition wraps, and the array contents are stated through `Int.repr`
  exactly as in VST, so the bound is not needed here.
-/
import VST.progs.verif_rotate
open CC CC.Sep CC.HProp
open Rotate
open VST.Verif.Min (elems)
open VST.Verif.Rotate

namespace VST.Verif.RotateSorted

/-! ## VST's `sorted_rotate`, and why it is sorted -/

/-- VST's `sorted_rotate l k N`:
    `sublist k (Zlength l) l ++ map (Z.add N) (sublist 0 k l)`. -/
def sortedRotate (l : List _root_.Int) (k : Nat) (N : _root_.Int) : List _root_.Int :=
  l.drop k ++ (l.take k).map (N + ·)

/-- The 32-bit representations of a list of integers (`map Int.repr`). -/
def reprs (l : List _root_.Int) : List Integers.Int := l.map Integers.Int.repr

/-- `sorted_rotate` of a sorted list with elements in `[0, N]` is sorted. -/
theorem sortedRotate_sorted (s : List _root_.Int) (k : Nat) (N : _root_.Int)
    (hs : ∀ x ∈ s, 0 ≤ x ∧ x ≤ N) (hsort : s.Pairwise (· ≤ ·)) :
    (sortedRotate s k N).Pairwise (· ≤ ·) := by
  unfold sortedRotate
  refine List.pairwise_append.mpr ⟨hsort.sublist (List.drop_sublist _ _), ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (hsort.sublist (List.take_sublist _ _)).imp (fun h => by omega)
  · intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have h1 := hs a (List.mem_of_mem_drop ha)
    have h2 := hs c (List.mem_of_mem_take hc)
    omega

theorem elems_reprs (l : List _root_.Int) (x : Nat) :
    elems (reprs l) x = Integers.Int.repr (l.getD x 0) := by
  unfold elems reprs
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[x]? <;> rfl

theorem rotate_reprs (l : List _root_.Int) (k : Nat) :
    rotate (reprs l) k = reprs (rotate l k) := by
  simp [rotate, reprs, List.map_drop, List.map_take]

/-- `sorted_rotate`, index by index. -/
theorem getD_sortedRotate (l : List _root_.Int) (k : Nat) (N : _root_.Int) (hk : k ≤ l.length)
    (x : Nat) (hx : x < l.length) :
    (sortedRotate l k N).getD x 0
      = if x < l.length - k then (rotate l k).getD x 0 else N + (rotate l k).getD x 0 := by
  unfold sortedRotate rotate
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : x < l.length - k
  · rw [if_pos h, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega)]
  · rw [if_neg h, List.getElem?_append_right (by simp; omega),
      List.getElem?_append_right (by simp; omega), List.getElem?_map,
      List.getElem?_take_of_lt (by simp; omega)]
    simp only [List.length_drop]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

/-! ## The specification (VST's `sorted_rotate_spec`) -/

def sortedRotateSpec (p : Permission) (ba : Block) (oa : Integers.Ptrofs) (s : List _root_.Int)
    (k : Nat) (N : _root_.Int) : Sep.FunSpec where
  tyargs := [tptr tint, tint, tint, tint]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr ba oa, .Vint (Integers.Int.repr s.length), .Vint (Integers.Int.repr k),
      .Vint (Integers.Int.repr N)]
    ∧ arrayU32 p ba (Integers.Ptrofs.unsigned oa) s.length (elems (reprs s)) hp
  post := fun v hp =>
    v = .Vundef ∧ (sortedRotate s k N).Pairwise (· ≤ ·)
    ∧ arrayU32 p ba (Integers.Ptrofs.unsigned oa) s.length (elems (reprs (sortedRotate s k N))) hp
  measure := fun _ => 0

/-! ## The body -/

def callRotate : Stmt :=
  .Scall none (.Evar _rotate (Ty.Tfunction [tptr tint, tint, tint] tvoid cc_default))
    [.Etempvar _a (tptr tint), .Etempvar _n tint, .Etempvar _k tint]
def setI : Stmt := .Sset _i (.Ebinop .Osub (.Etempvar _n tint) (.Etempvar _k tint) tint)
/-- `t = a[i]; a[i] = t + N;` -/
def addBody : Stmt :=
  .Ssequence (.Sset _t'1 (elemOf _a (.Etempvar _i tint)))
    (.Sassign (elemOf _a (.Etempvar _i tint))
      (.Ebinop .Oadd (.Etempvar _t'1 tint) (.Etempvar _N tint) tint))
def addLoop : Stmt := loopOf (forGuard _i _n) addBody (incr _i)
def fullBody : Stmt := .Ssequence callRotate (.Ssequence setI addLoop)

theorem body_eq : f_sorted_rotate.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (p : Permission) (ba : Block) (oa : Integers.Ptrofs) (n k : Nat) (N : _root_.Int)
variable (R : Nat → Integers.Int)

/-- The parameters. -/
abbrev T0 : List (Ident × Val) :=
  [(_a, .Vptr ba oa), (_n, .Vint (Integers.Int.repr n)), (_k, .Vint (Integers.Int.repr k)),
   (_N, .Vint (Integers.Int.repr N))]

/-- The rotated array `R` after `N` is added to the elements `n - k ≤ x < j`. -/
def added (j x : Nat) : Integers.Int :=
  if n - k ≤ x ∧ x < j then Integers.Int.add (R x) (Integers.Int.repr N) else R x

def AInv (j : Nat) : Sep.Assn :=
  LocalSt emptyEnv ((_i, .Vint (Integers.Int.repr j)) :: T0 ba oa n k N)
    (arrayU32 p ba (Integers.Ptrofs.unsigned oa) n (added n k N R j))

/-- After the body of the loop, before `i++`. -/
def AMid (j : Nat) : Sep.Assn :=
  LocalSt emptyEnv ((_i, .Vint (Integers.Int.repr j)) :: T0 ba oa n k N)
    (arrayU32 p ba (Integers.Ptrofs.unsigned oa) n (added n k N R (j + 1)))

end

/-! ## The loop -/

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (ba : Block) (oa : Integers.Ptrofs)
variable (n k : Nat) (N : _root_.Int) (R : Nat → Integers.Int) (Ret : Val → HProp)

private theorem no_ovf_mono' (A : _root_.Int) (i l : Nat) (hil : i ≤ l)
    (h : A + 4 * (l : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

/-- One iteration: `a[j] += N`. -/
theorem add_body (j : Nat) (hj0 : n - k ≤ j) (hj : j < n) (hpw : permOrder p .Writable = true)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616) :
    Triple ge fe f_sorted_rotate (AInv p ba oa n k N R j) addBody
      { normal := AMid p ba oa n k N R j, brk := Assn.no,
        cont := AMid p ba oa n k N R j, ret := Ret } := by
  have hpr := readable_of_writable hpw
  have hRj : added n k N R j j = R j := by simp [added]
  unfold addBody AInv AMid
  refine triple_seq_fwd ge fe f_sorted_rotate _ (LocalSt emptyEnv
    ((_t'1, .Vint (R j)) :: (_i, .Vint (Integers.Int.repr j)) :: T0 ba oa n k N)
    (arrayU32 p ba (Integers.Ptrofs.unsigned oa) n (added n k N R j))) _ _ _ ?_ ?_
  · -- `t = a[i];`
    refine triple_set_local ge fe f_sorted_rotate emptyEnv _ _ _ _t'1 _ (.Vint (R j))
      (fun _ h => h) (by temps_ne) (fun le m hp hT hH hag => ?_)
    rw [← hRj]
    exact eval_index_array_int hpr hH hag hj (EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
      (EvalExpr.Etempvar _ _ _ (hT.get (by simp))) rfl rfl
      (elemOfs_unsigned _ oa j (by omega) (no_ovf_mono' _ j n (by omega) hno))
  · -- `a[i] = t + N;`
    have hst := triple_store_index_int ge fe f_sorted_rotate
      (fun e le => e = emptyEnv ∧ TempsHold
        ((_t'1, .Vint (R j)) :: (_i, .Vint (Integers.Int.repr j)) :: T0 ba oa n k N) le)
      (.Etempvar _a (tptr tint)) (.Etempvar _i tint)
      (.Ebinop .Oadd (.Etempvar _t'1 tint) (.Etempvar _N tint) tint) p ba oa n j
      (added n k N R j) (Integers.Int.add (R j) (Integers.Int.repr N)) hpw hj hn hno
      (fun e le m h => EvalExpr.Etempvar _ _ _ (h.2.get (by simp)))
      (fun e le m h => EvalExpr.Etempvar _ _ _ (h.2.get (by simp)))
      (fun e le m h => EvalExpr.Ebinop .Oadd _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (h.2.get (by simp))) (EvalExpr.Etempvar _ _ _ (h.2.get (by simp)))
        (semBinop_add_int _ _ _ _)) rfl rfl rfl
    refine triple_conseq ge fe f_sorted_rotate hst (fun e le hp h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
      (fun e le hp h => ?_) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    obtain ⟨⟨he, hT⟩, hH⟩ := h
    refine ⟨he, TempsHold_mono (fun q hq => List.mem_cons_of_mem _ hq) hT, ?_⟩
    rwa [arrayU32_congr p ba n _ (added n k N R (j + 1)) _ (fun x _ => by
      by_cases hx : x = j
      · subst hx; simp [added, hj0]
      · simp only [added, hx, if_false]
        by_cases hxj : n - k ≤ x ∧ x < j
        · simp [hxj, show x < j + 1 from by omega]
        · simp only [hxj, if_false]
          rw [if_neg (by omega)])] at hH

/-- The loop: `for (i = n - k; i < n; i++) a[i] += N;`. -/
theorem add_loop (hkn : k ≤ n) (hpw : permOrder p .Writable = true)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (n : _root_.Int) < 18446744073709551616) :
    Triple ge fe f_sorted_rotate (AInv p ba oa n k N R (n - k)) addLoop
      { normal := AInv p ba oa n k N R n, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  unfold addLoop loopOf
  refine triple_for_guard_from ge fe f_sorted_rotate (forGuard _i _n) rfl (n - k) n (by omega)
    (AInv p ba oa n k N R) (AMid p ba oa n k N R) _ _ Ret
    (fun j e le hp m hI _ hj => ?_) (fun j hj0 hj => ?_) (fun j _ _ => ?_)
  · obtain ⟨-, hT, -⟩ := hI
    exact eval_forGuard _i _n j n hn hj (hT.get (by simp)) (hT.get (by simp))
  · exact add_body ge fe p ba oa n k N R Ret j hj0 hj hpw hn hno
  · exact triple_set_local ge fe f_sorted_rotate emptyEnv _ (T0 ba oa n k N) _ _i _ _
      (fun _ hq => List.mem_cons_of_mem _ hq) (by temps_ne)
      (fun le m hp hT _ _ => eval_incr _i j (hT.get (by simp)))

end

/-! ## `sorted_rotate` satisfies `sorted_rotate_spec` -/

/-- **`sorted_rotate` satisfies `sorted_rotate_spec`** (VST's
    `body_sorted_rotate`).  `rotate`, `malloc` and `free` are the program's
    functions of those names. -/
theorem sorted_rotate_satisfies (ge : CGenv) (p : Permission) (ba : Block) (oa : Integers.Ptrofs)
    (s : List _root_.Int) (k : Nat) (N : _root_.Int) (br bm bf : Block)
    (hsymR : Genv.findSymbol ge.genv_genv _rotate = some br)
    (hfindR : Genv.findFunct ge.genv_genv (.Vptr br Integers.Ptrofs.zero)
      = some (.Internal f_rotate))
    (hsymM : Genv.findSymbol ge.genv_genv _malloc = some bm)
    (hfindM : Genv.findFunct ge.genv_genv (.Vptr bm Integers.Ptrofs.zero)
      = some (.External .EF_malloc [tulong] (tptr tvoid) cc_default))
    (hsymF : Genv.findSymbol ge.genv_genv _free = some bf)
    (hfindF : Genv.findFunct ge.genv_genv (.Vptr bf Integers.Ptrofs.zero)
      = some (.External .EF_free [tptr tvoid] tvoid cc_default))
    (hpw : permOrder p .Writable = true) (hk : 0 < k) (hkn : k < s.length)
    (hn : (s.length : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned oa + 4 * (s.length : _root_.Int) < 18446744073709551616)
    (hs : ∀ x ∈ s, 0 ≤ x ∧ x ≤ N) (hsort : s.Pairwise (· ≤ ·)) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sorted_rotate)
      (sortedRotateSpec p ba oa s k N)
      [.Vptr ba oa, .Vint (Integers.Int.repr s.length), .Vint (Integers.Int.repr k),
        .Vint (Integers.Int.repr N)] := by
  have hlen : (reprs s).length = s.length := List.length_map _
  let n := s.length
  let R := elems (rotate (reprs s) k)
  have hfin : ∀ hp, arrayU32 p ba (Integers.Ptrofs.unsigned oa) n (added n k N R n) hp →
      arrayU32 p ba (Integers.Ptrofs.unsigned oa) n (elems (reprs (sortedRotate s k N))) hp := by
    intro hp h
    rwa [arrayU32_congr p ba n _ (added n k N R n) _ (fun x hx => by
      simp only [added, R, n, rotate_reprs, elems_reprs,
        getD_sortedRotate s k N (Nat.le_of_lt hkn) x hx]
      by_cases h1 : x < s.length - k
      · have h2 : ¬ (s.length - k ≤ x ∧ x < s.length) := by omega
        simp only [h1, h2, if_true, if_false]
      · have h2 : s.length - k ≤ x ∧ x < s.length := ⟨by omega, hx⟩
        simp only [h1, h2, and_self, if_true, if_false]
        rw [repr_add, Int.add_comm])]
  refine Sep.satisfies_internal_noVars_void ge (FunctionEntry2 ge) f_sorted_rotate _ _
    (LocalSt emptyEnv (T0 ba oa n k N) (arrayU32 p ba (Integers.Ptrofs.unsigned oa) n
      (elems (reprs s)))) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> rfl
  rw [body_eq]
  unfold fullBody
  -- `rotate(a, n, k);`
  refine triple_seq_only ge _ f_sorted_rotate (Q := LocalSt emptyEnv (T0 ba oa n k N)
    (arrayU32 p ba (Integers.Ptrofs.unsigned oa) n R)) ?_ ?_
  · refine triple_call_at ge _ f_sorted_rotate (rotateSpec p ba oa (reprs s) k) none _ _ _ _ br
      _ hfindR rfl rfl (fun e le hp m hP _ => ?_)
    obtain ⟨rfl, hT, hA⟩ := hP
    refine ⟨[.Vptr ba oa, .Vint (Integers.Int.repr (reprs s).length), .Vint (Integers.Int.repr k)],
      hp, Heap.emp, Heap.disjoint_emp_right _, (Heap.union_emp _).symm,
      eval_callee_global (PTree.gempty _) hsymR rfl, ?_, ⟨rfl, by rw [hlen]; exact hA⟩,
      rotate_satisfies ge p ba oa (reprs s) k bm bf hsymM hfindM hsymF hfindF hpw hk
        (by omega) (by rw [hlen]; exact hn) (by rw [hlen]; exact hno),
      fun v h1' hpost _ => ⟨rfl, hT, ?_⟩⟩
    · rw [hlen]
      exact EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
        (semCast_ptr_ptr _ _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩))
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by simp; exact Or.inl rfl)))
          (semCast_int _ _)
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by simp)))
            (semCast_int _ _) EvalExprlist.nil))
    · rw [Heap.union_emp]
      have h := hpost.2
      rwa [hlen] at h
  -- `i = n - k;`
  refine triple_seq_only ge _ f_sorted_rotate (Q := AInv p ba oa n k N R (n - k)) ?_ ?_
  · refine triple_conseq ge _ f_sorted_rotate (triple_set_local ge _ f_sorted_rotate emptyEnv _
      (T0 ba oa n k N) _ _i _ _ (fun _ h => h) (by temps_ne)
      (fun le m hp hT _ _ => eval_sub_nk (n := n) (k := k) (Nat.le_of_lt hkn) (hT.get (by simp)) (hT.get (by simp))))
      (fun _ _ _ x => x) (fun e le hp h => ?_) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
      (fun _ _ x => x.elim)
    obtain ⟨he, hT, hH⟩ := h
    refine ⟨he, hT, ?_⟩
    rwa [arrayU32_congr p ba n _ R _ (fun x _ => by
      simp only [added, n]
      rw [if_neg (show ¬ (s.length - k ≤ x ∧ x < s.length - k) by omega)])]
  -- the loop
  exact Sep.triple_conseq ge _ f_sorted_rotate
    (add_loop ge _ p ba oa n k N R (sortedRotateSpec p ba oa s k N).post (by omega) hpw hn hno)
    (fun _ _ _ x => x)
    (fun e le hp h => ⟨h.1, rfl, sortedRotate_sorted s k N hs hsort, hfin hp h.2.2⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

end VST.Verif.RotateSorted
