/-
  Port of VST's `progs/verif_dotprod.v`, function `dotprod` of
  `vst/progs/dotprod.c`:

      double dotprod (int n, double x[], double y[]) {
        int i;
        double sum = 0.0;
        for (i=0; i<n; i++)
            sum += x[i] * y[i];
        return sum;
      }

  VST's specification:

      Definition dotprod (fx fy : list float) : float :=
        fold_left Float.add (map2 Float.mul fx fy) Float.zero .

      DECLARE _dotprod
       WITH n: Z, x: val, y : val, fx : list float, fy: list float, sh: share
       PRE  [ tint, tptr tdouble, tptr tdouble]
           PROP (0 <= n < Int.max_signed)
           PARAMS (Vint (Int.repr n); x; y)
           SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
                data_at Tsh (tarray tdouble n) (map Vfloat fy) y)
       POST [ tdouble ]
           PROP () RETURN (Vfloat (dotprod fx fy))
           SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
                data_at Tsh (tarray tdouble n) (map Vfloat fy) y).

  The arrays are `Sep.arrayF64` (`CCLib.logic.HoareArrayDouble`), owned at a
  readable permission `p`; `x`, `y` are `Vptr bx ox`, `Vptr byy oy`; the
  lengths of `fx`, `fy` are `n` (implicit in VST's `data_at` of an array of
  length `n`), and the arrays fit in the address space (VST's
  `field_compatible`).  The float operations are those of the exact IEEE-754
  model of the port (`Floats.Float.add`/`mul`).  The proof follows VST's:
  the loop invariant says that `sum` is the dot product of the first `i`
  elements (`dotTo`).
-/
import VST.progs.dotprod
import CCLib
open CC CC.Sep CC.HProp
open Dotprod

namespace VST.Verif.Dotprod

/-! ## The dot product -/

/-- VST's `dotprod`: `fold_left Float.add (map2 Float.mul fx fy) Float.zero`. -/
def dotprod (fx fy : List Floats.Float) : Floats.Float :=
  (List.zipWith Floats.Float.mul fx fy).foldl Floats.Float.add Floats.Float.zero

/-- The dot product of the first `n` elements. -/
def dotTo (f g : Nat → Floats.Float) : Nat → Floats.Float
  | 0 => Floats.Float.zero
  | n + 1 => Floats.Float.add (dotTo f g n) (Floats.Float.mul (f n) (g n))

/-- The elements of a list, as a function (`Znth`). -/
def elems (l : List Floats.Float) (j : Nat) : Floats.Float := l.getD j Floats.Float.zero

theorem dotTo_elems (fx fy : List Floats.Float) :
    ∀ k, k ≤ fx.length → k ≤ fy.length →
      dotTo (elems fx) (elems fy) k
        = (List.zipWith Floats.Float.mul (fx.take k) (fy.take k)).foldl
            Floats.Float.add Floats.Float.zero := by
  intro k
  induction k with
  | zero => intro _ _; simp [dotTo]
  | succ k ih =>
    intro hx hy
    rw [dotTo, ih (by omega) (by omega), List.take_succ_eq_append_getElem (by omega),
      List.take_succ_eq_append_getElem (by omega),
      List.zipWith_append (by simp; omega), List.foldl_append]
    simp [elems, show k < fx.length by omega, show k < fy.length by omega]

theorem dotTo_full (fx fy : List Floats.Float) (n : Nat) (hx : fx.length = n)
    (hy : fy.length = n) : dotTo (elems fx) (elems fy) n = dotprod fx fy := by
  rw [dotTo_elems fx fy n (by omega) (by omega), ← hx, List.take_length,
    show fx.length = fy.length by omega, List.take_length]
  rfl

/-! ## The parts of the body -/

def guardExpr : Expr := .Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint
def elemX : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _x (tptr tdouble)) (.Etempvar _i tint) (tptr tdouble)) tdouble
def elemY : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _y (tptr tdouble)) (.Etempvar _i tint) (tptr tdouble)) tdouble
def setSum : Stmt :=
  .Sset _sum (.Ebinop .Oadd (.Etempvar _sum tdouble)
    (.Ebinop .Omul (.Etempvar _t'1 tdouble) (.Etempvar _t'2 tdouble) tdouble) tdouble)
def bodyStmt : Stmt := .Ssequence (.Sset _t'1 elemX) (.Ssequence (.Sset _t'2 elemY) setSum)
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def setI : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) setI
def retStmt : Stmt := .Sreturn (some (.Etempvar _sum tdouble))
def fullBody : Stmt :=
  .Ssequence (.Sset _sum (.Econst_float (Floats.Float.ofBits (Integers.Int64.repr 0)) tdouble))
    (.Ssequence (.Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 0) tint)) loopStmt) retStmt)

theorem body_eq : f_dotprod.fn_body = fullBody := rfl

theorem zero_bits : Floats.Float.ofBits (Integers.Int64.repr 0) = Floats.Float.zero := by decide

/-! ## Assertions -/

section
variable (p : Permission) (bx byy : Block) (ox oy : Integers.Ptrofs) (n : Nat)
  (fx fy : Nat → Floats.Float)

/-- The two arrays. -/
def Arrs : HProp :=
  arrayF64 p bx (Integers.Ptrofs.unsigned ox) n fx ∗ arrayF64 p byy (Integers.Ptrofs.unsigned oy) n fy

/-- The local state: the parameters as passed, `i = iv`, `sum = sv`. -/
def St (iv : Nat) (sv : Floats.Float) : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _x = some (.Vptr bx ox) ∧ le.get _y = some (.Vptr byy oy)
  ∧ le.get _n = some (.Vint (Integers.Int.repr n))
  ∧ le.get _i = some (.Vint (Integers.Int.repr iv))
  ∧ le.get _sum = some (.Vfloat sv)
  ∧ Arrs p bx byy ox oy n fx fy hp

/-- The loop invariant, `k` iterations left. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p bx byy ox oy n fx fy iv (dotTo fx fy iv) e le hp ∧ iv ≤ n ∧ n - iv = k

def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p bx byy ox oy n fx fy iv (dotTo fx fy iv) e le hp ∧ iv < n ∧ n - iv = k

def LSummed (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p bx byy ox oy n fx fy iv (dotTo fx fy (iv + 1)) e le hp ∧ iv < n ∧ n - iv = k

def LAfter (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p bx byy ox oy n fx fy iv (dotTo fx fy iv) e le hp ∧ iv ≤ n ∧ n - iv + 1 = k

def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _sum = some (.Vfloat (dotTo fx fy n)) ∧ Arrs p bx byy ox oy n fx fy hp

def Ret : Val → HProp := fun v hp =>
  v = .Vfloat (dotTo fx fy n) ∧ Arrs p bx byy ox oy n fx fy hp

def LoopR : Sep.ExitConds :=
  { normal := Done p bx byy ox oy n fx fy, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := Ret p bx byy ox oy n fx fy }

end

/-! ## The proof -/

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (bx byy : Block) (ox oy : Integers.Ptrofs)
  (n : Nat) (fx fy : Nat → Floats.Float) {func : Function}
  (hpr : permOrder p .Readable = true)
  (hn : (n : _root_.Int) < 2147483648)
  (hnox : Integers.Ptrofs.unsigned ox + 8 * (n : _root_.Int) ≤ 18446744073709551616)
  (hnoy : Integers.Ptrofs.unsigned oy + 8 * (n : _root_.Int) ≤ 18446744073709551616)

include hn in
theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (iv : Nat) (sv : Floats.Float) (hp : Heap)
    (hiv : iv ≤ n) (hSt : St p bx byy ox oy n fx fy iv sv e le hp) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (iv < n))) := by
  obtain ⟨_, _, _, hnn, hi, _⟩ := hSt
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr iv) (Integers.Int.repr n))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Etempvar _n tint _ hnn) (semBinop_lt_int _ _ _ _)
  rw [lt_repr (iv : _root_.Int) (n : _root_.Int) (by omega) (by omega) (by omega) hn] at h
  simpa using h

include hn in
theorem if_triple (k : Nat) :
    Sep.Triple ge fe func (LInv p bx byy ox oy n fx fy k) ifStmt
      { normal := LMid p bx byy ox oy n fx fy k, brk := Done p bx byy ox oy n fx fy,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe func _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p bx byy ox oy n fx fy hn e le m iv _ hp hiv hSt, ?_⟩
      have : ¬ iv < n := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe func (Sep.triple_break ge fe func _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨iv, ⟨he, _, _, _, _, hs, harr⟩, hiv, hk⟩ := h
      have : iv = n := by omega
      subst this
      exact ⟨he, hs, harr⟩
  | succ j =>
    refine Sep.triple_if_true ge fe func _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p bx byy ox oy n fx fy hn e le m iv _ hp hiv hSt, ?_⟩
      have : iv < n := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe func _ _ _ _
        (Sep.triple_skip ge fe func _) (fun e le hp h => ?_)
      obtain ⟨iv, hSt, hiv, hk⟩ := h
      exact ⟨iv, hSt, by omega, hk⟩

include hpr hn hnox hnoy in
/-- `t'1 = x[i]; t'2 = y[i]; sum = sum + t'1 * t'2;` -/
theorem body_triple (k : Nat) :
    Sep.Triple ge fe func (LMid p bx byy ox oy n fx fy k) bodyStmt
      (.only (LSummed p bx byy ox oy n fx fy k)) := by
  refine Sep.triple_exists ge fe func _ _ _ (fun iv => ?_)
  -- `t'1 = x[i];`
  refine Sep.triple_seq_only ge fe func (Q := fun e le hp =>
      St p bx byy ox oy n fx fy iv (dotTo fx fy iv) e le hp ∧ iv < n ∧ n - iv = k
      ∧ le.get _t'1 = some (.Vfloat (fx iv))) ?_ ?_
  · refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, hx, hy, hnn, hi, hs, harr⟩, hlt, hk⟩ := hP
    obtain ⟨_, hax, hagx⟩ := sep_left_agrees harr hag
    refine ⟨.Vfloat (fx iv), eval_index_f64 hpr hax hagx hlt (EvalExpr.Etempvar _ _ _ hx)
      (EvalExpr.Etempvar _i tint _ hi) rfl hn hnox, ⟨he, ?_, ?_, ?_, ?_, ?_, harr⟩, hlt, hk,
      PTree.gss _ _ _⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
  -- `t'2 = y[i];`
  refine Sep.triple_seq_only ge fe func (Q := fun e le hp =>
      St p bx byy ox oy n fx fy iv (dotTo fx fy iv) e le hp ∧ iv < n ∧ n - iv = k
      ∧ le.get _t'1 = some (.Vfloat (fx iv)) ∧ le.get _t'2 = some (.Vfloat (fy iv))) ?_ ?_
  · refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, hx, hy, hnn, hi, hs, harr⟩, hlt, hk, ht1⟩ := hP
    obtain ⟨_, hay, hagy⟩ := sep_right_agrees harr hag
    refine ⟨.Vfloat (fy iv), eval_index_f64 hpr hay hagy hlt (EvalExpr.Etempvar _ _ _ hy)
      (EvalExpr.Etempvar _i tint _ hi) rfl hn hnoy, ⟨he, ?_, ?_, ?_, ?_, ?_, harr⟩, hlt, hk,
      ?_, PTree.gss _ _ _⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
  -- `sum = sum + t'1 * t'2;`
  · refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, hx, hy, hnn, hi, hs, harr⟩, hlt, hk, ht1, ht2⟩ := hP
    refine ⟨.Vfloat (dotTo fx fy (iv + 1)),
      EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hs)
        (EvalExpr.Ebinop .Omul _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ ht1)
          (EvalExpr.Etempvar _ _ _ ht2) (semBinop_mul_double _ _ _ _))
        (semBinop_add_double _ _ _ _),
      iv, ⟨he, ?_, ?_, ?_, ?_, PTree.gss _ _ _, harr⟩, hlt, hk⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)

theorem incr_triple (k : Nat) :
    Sep.Triple ge fe func (LSummed p bx byy ox oy n fx fy k) setI
      (.only (LAfter p bx byy ox oy n fx fy k)) := by
  refine Sep.triple_exists ge fe func _ _ _ (fun iv => ?_)
  refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨⟨he, hx, hy, hnn, hi, hs, harr⟩, hlt, hk⟩ := hP
  refine ⟨.Vint (Integers.Int.repr ((iv : _root_.Int) + 1)), ?_, ?_⟩
  · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Econst_int _ tint) ?_
    simp only [typeof]
    rw [semBinop_add_int, repr_add]
  · refine ⟨iv + 1, ⟨he, ?_, ?_, ?_, ?_, ?_, harr⟩, by omega, by omega⟩
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gss]; simp
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption

include hpr hn hnox hnoy in
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_dotprod (LInv p bx byy ox oy n fx fy k) loopStmt
      (LoopR p bx byy ox oy n fx fy) := by
  refine Sep.triple_loop ge fe f_dotprod (LoopR p bx byy ox oy n fx fy)
    (LInv p bx byy ox oy n fx fy) (LSummed p bx byy ox oy n fx fy) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_dotprod _ (LMid p bx byy ox oy n fx fy k) _ _ _
      (Sep.triple_conseq ge fe f_dotprod (if_triple ge fe p bx byy ox oy n fx fy hn k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_dotprod _ _ _ _
        (body_triple ge fe p bx byy ox oy n fx fy hpr hn hnox hnoy k) (fun _ _ _ x => x))
  · refine Sep.triple_fallthrough ge fe f_dotprod _ _ _ _
      (incr_triple ge fe p bx byy ox oy n fx fy k) (fun e le hp h => ?_)
    obtain ⟨iv, hSt, hiv, hk⟩ := h
    exact ⟨n - iv, by omega, iv, hSt, hiv, rfl⟩

/-- The precondition of the body: the parameters as passed, the arrays owned. -/
def Pre : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _x = some (.Vptr bx ox) ∧ le.get _y = some (.Vptr byy oy)
  ∧ le.get _n = some (.Vint (Integers.Int.repr n))
  ∧ Arrs p bx byy ox oy n fx fy hp

include hpr hn hnox hnoy in
/-- **The body of `dotprod`**: it returns the dot product and hands the arrays
    back. -/
theorem dotprod_body :
    Sep.Triple ge fe f_dotprod (Pre p bx byy ox oy n fx fy) fullBody
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p bx byy ox oy n fx fy } := by
  -- `sum = 0.0;`
  refine Sep.triple_seq_only ge fe f_dotprod (Q := fun e le hp =>
      Pre p bx byy ox oy n fx fy e le hp ∧ le.get _sum = some (.Vfloat Floats.Float.zero)) ?_ ?_
  · refine Sep.triple_set ge fe f_dotprod _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, hx, hy, hnn, harr⟩ := hP
    refine ⟨_, EvalExpr.Econst_float _ tdouble, ⟨he, ?_, ?_, ?_, harr⟩, ?_⟩
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gss, zero_bits]
  refine Sep.triple_seq ge fe f_dotprod _ (Done p bx byy ox oy n fx fy) _ _ _ ?_ ?_
  · -- `i = 0;` then the loop
    refine Sep.triple_seq_only ge fe f_dotprod (Q := LInv p bx byy ox oy n fx fy n) ?_
      (Sep.triple_conseq ge fe f_dotprod (loop_triple ge fe p bx byy ox oy n fx fy hpr hn hnox hnoy n)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x))
    refine Sep.triple_set ge fe f_dotprod _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨⟨he, hx, hy, hnn, harr⟩, hs⟩ := hP
    refine ⟨_, EvalExpr.Econst_int _ tint, 0, ⟨he, ?_, ?_, ?_, PTree.gss _ _ _, ?_, harr⟩,
      by omega, by omega⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
  · -- `return sum;`
    refine Sep.triple_return ge fe f_dotprod _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hs, harr⟩ := h
    refine ⟨.Vfloat (dotTo fx fy n), .Vfloat (dotTo fx fy n), m, hp,
      EvalExpr.Etempvar _sum tdouble _ hs, semCast_double_double m _, ?_, ⟨rfl, harr⟩,
      fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

end

/-! ## As a function specification (VST's `dotprod_spec`) -/

/-- `dotprod_spec` -/
def dotprodSpec (p : Permission) (bx byy : Block) (ox oy : Integers.Ptrofs)
    (fx fy : List Floats.Float) : Sep.FunSpec where
  tyargs := [tint, tptr tdouble, tptr tdouble]
  tyres := tdouble
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vint (Integers.Int.repr fx.length), .Vptr bx ox, .Vptr byy oy]
    ∧ Arrs p bx byy ox oy fx.length (elems fx) (elems fy) hp
  post := fun v hp =>
    v = .Vfloat (dotprod fx fy) ∧ Arrs p bx byy ox oy fx.length (elems fx) (elems fy) hp
  measure := fun _ => 0

/-- **`dotprod` satisfies `dotprod_spec`** (VST's `body_dotprod`). -/
theorem dotprod_satisfies (ge : CGenv) (p : Permission) (bx byy : Block) (ox oy : Integers.Ptrofs)
    (fx fy : List Floats.Float) (hlen : fy.length = fx.length)
    (hpr : permOrder p .Readable = true)
    (hn : (fx.length : _root_.Int) < 2147483648)
    (hnox : Integers.Ptrofs.unsigned ox + 8 * (fx.length : _root_.Int) ≤ 18446744073709551616)
    (hnoy : Integers.Ptrofs.unsigned oy + 8 * (fx.length : _root_.Int) ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_dotprod) (dotprodSpec p bx byy ox oy fx fy)
      [.Vint (Integers.Int.repr fx.length), .Vptr bx ox, .Vptr byy oy] := by
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_dotprod _ _
    (Pre p bx byy ox oy fx.length (elems fx) (elems fy)) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨rfl, rfl, rfl, rfl, hpre.2⟩⟩
  · have h := body_eq ▸ dotprod_body ge (FunctionEntry2 ge) p bx byy ox oy fx.length
      (elems fx) (elems fy) hpr hn hnox hnoy
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_dotprod h (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    obtain ⟨hv, harr⟩ := hr
    exact ⟨by rw [hv, dotTo_full fx fy _ rfl hlen], harr⟩

end VST.Verif.Dotprod
