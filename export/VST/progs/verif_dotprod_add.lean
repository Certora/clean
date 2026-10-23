/-
  Port of VST's `progs/verif_dotprod.v`, function `add` of
  `vst/progs/dotprod.c`:

      #define N 3
      void add (double x[], double y[], double z[]) {
        int i;
        for (i=0; i<N; i++)
            x[i] = y[i] + z[i];
      }

  VST's specification:

      DECLARE _add
       WITH x: val, y : val, z: val, fy : list float, fz: list float
       PRE  [ tptr tdouble, tptr tdouble, tptr tdouble]
           PROP () PARAMS (x; y; z)
           SEP (data_at_ Tsh (tarray tdouble 3)  x ;
                data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
                data_at Tsh (tarray tdouble 3) (map Vfloat fz) z)
       POST [ tvoid ]
           PROP () RETURN ()
           SEP (data_at Tsh (tarray tdouble 3) (map Vfloat (map2 Float.add fy fz)) x;
                data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
                data_at Tsh (tarray tdouble 3) (map Vfloat fz) z).

  `x` is owned at a writable permission `px` with arbitrary initial contents
  `vx0` (VST's `data_at_`), `y`, `z` at a readable permission `p`; the arrays
  fit in the address space (VST's `field_compatible`).  The loop invariant
  says that the first `i` elements of `x` are already the sums (`upd`).
-/
import VST.progs.verif_dotprod
open CC CC.Sep CC.HProp
open Dotprod
open VST.Verif.Dotprod (elems)

namespace VST.Verif.DotprodAdd

/-! ## The parts of the body -/

def guardExpr : Expr :=
  .Ebinop .Olt (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 3) tint) tint
def elemOf (a : Ident) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar a (tptr tdouble)) (.Etempvar _i tint) (tptr tdouble)) tdouble
def sumExpr : Expr := .Ebinop .Oadd (.Etempvar _t'1 tdouble) (.Etempvar _t'2 tdouble) tdouble
def storeStmt : Stmt :=
  .Sassign (.Ederef (.Ebinop .Oadd (.Etempvar _x (tptr tdouble)) (.Etempvar _i tint)
    (tptr tdouble)) tdouble) sumExpr
def bodyStmt : Stmt :=
  .Ssequence (.Sset _t'1 (elemOf _y)) (.Ssequence (.Sset _t'2 (elemOf _z)) storeStmt)
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def setI : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) setI
def fullBody : Stmt := .Ssequence (.Sset _i (.Econst_int (Integers.Int.repr 0) tint)) loopStmt

theorem body_eq : f_add.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (px p : Permission) (bx byy bz : Block) (ox oy oz : Integers.Ptrofs)
  (vx0 : Nat → Val) (fy fz : Nat → Floats.Float)

/-- The contents of `x` after `iv` iterations. -/
def upd (iv : Nat) (j : Nat) : Val :=
  if j < iv then .Vfloat (Floats.Float.add (fy j) (fz j)) else vx0 j

theorem upd_succ (iv : Nat) :
    (fun j => if j = iv then Val.Vfloat (Floats.Float.add (fy iv) (fz iv)) else upd vx0 fy fz iv j)
      = upd vx0 fy fz (iv + 1) := by
  funext j
  by_cases h : j = iv
  · subst h; simp [upd]
  · simp only [upd, h, if_false]
    by_cases h' : j < iv
    · simp [h', show j < iv + 1 by omega]
    · simp [h', show ¬ j < iv + 1 by omega]

/-- The source arrays. -/
def Src : HProp :=
  arrayF64 p byy (Integers.Ptrofs.unsigned oy) 3 fy ∗ arrayF64 p bz (Integers.Ptrofs.unsigned oz) 3 fz

/-- The three arrays, `iv` elements of `x` written. -/
def Arrs (iv : Nat) : HProp :=
  arrayV64 px bx (Integers.Ptrofs.unsigned ox) 3 (upd vx0 fy fz iv) ∗ Src p byy bz oy oz fy fz

/-- The parameters as passed. -/
def Params (e : Env) (le : TempEnv) : Prop :=
  e = emptyEnv
  ∧ le.get _x = some (.Vptr bx ox) ∧ le.get _y = some (.Vptr byy oy)
  ∧ le.get _z = some (.Vptr bz oz)

/-- The local state: the parameters, `i = iv`, `iv` elements written. -/
def St (iv : Nat) : Sep.Assn := fun e le hp =>
  Params bx byy bz ox oy oz e le ∧ le.get _i = some (.Vint (Integers.Int.repr iv))
  ∧ Arrs px p bx byy bz ox oy oz vx0 fy fz iv hp

def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St px p bx byy bz ox oy oz vx0 fy fz iv e le hp ∧ iv ≤ 3 ∧ 3 - iv = k

def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St px p bx byy bz ox oy oz vx0 fy fz iv e le hp ∧ iv < 3 ∧ 3 - iv = k

/-- After the store: element `iv` written, `i` not yet incremented. -/
def LStored (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv : Nat, (Params bx byy bz ox oy oz e le ∧ le.get _i = some (.Vint (Integers.Int.repr iv))
    ∧ Arrs px p bx byy bz ox oy oz vx0 fy fz (iv + 1) hp) ∧ iv < 3 ∧ 3 - iv = k

def Done : Sep.Assn := fun e _ hp =>
  e = emptyEnv ∧ Arrs px p bx byy bz ox oy oz vx0 fy fz 3 hp

def LoopR : Sep.ExitConds :=
  { normal := Done px p bx byy bz ox oy oz vx0 fy fz, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := fun _ _ => False }

end

/-! ## The proof -/

section
variable (ge : CGenv) (fe : EntryRel) (px p : Permission) (bx byy bz : Block)
  (ox oy oz : Integers.Ptrofs) (vx0 : Nat → Val) (fy fz : Nat → Floats.Float) {func : Function}
  (hpw : permOrder px .Writable = true) (hpr : permOrder p .Readable = true)
  (hnox : Integers.Ptrofs.unsigned ox + 8 * 3 ≤ 18446744073709551616)
  (hnoy : Integers.Ptrofs.unsigned oy + 8 * 3 ≤ 18446744073709551616)
  (hnoz : Integers.Ptrofs.unsigned oz + 8 * 3 ≤ 18446744073709551616)

theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (iv : Nat) (hiv : iv ≤ 3)
    (hi : le.get _i = some (.Vint (Integers.Int.repr iv))) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (iv < 3))) := by
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr iv) (Integers.Int.repr 3))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Econst_int _ tint) (semBinop_lt_int _ _ _ _)
  rw [lt_repr (iv : _root_.Int) 3 (by omega) (by omega) (by omega) (by omega)] at h
  have hd : decide ((iv : _root_.Int) < 3) = decide (iv < 3) := by
    by_cases hc : iv < 3
    · simp [hc]; omega
    · simp [hc]; omega
  rwa [hd] at h

theorem if_triple (k : Nat) :
    Sep.Triple ge fe func (LInv px p bx byy bz ox oy oz vx0 fy fz k) ifStmt
      { normal := LMid px p bx byy bz ox oy oz vx0 fy fz k,
        brk := Done px p bx byy bz ox oy oz vx0 fy fz,
        cont := Sep.Assn.no, ret := fun _ _ => False } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe func _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, ⟨_, hi, _⟩, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge e le m iv hiv hi, ?_⟩
      have : ¬ iv < 3 := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe func (Sep.triple_break ge fe func _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨iv, ⟨⟨he, _⟩, _, harr⟩, hiv, hk⟩ := h
      have : iv = 3 := by omega
      subst this
      exact ⟨he, harr⟩
  | succ j =>
    refine Sep.triple_if_true ge fe func _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, ⟨_, hi, _⟩, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge e le m iv hiv hi, ?_⟩
      have : iv < 3 := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe func _ _ _ _
        (Sep.triple_skip ge fe func _) (fun e le hp h => ?_)
      obtain ⟨iv, hSt, hiv, hk⟩ := h
      exact ⟨iv, hSt, by omega, hk⟩

include hpw hpr hnox hnoy hnoz in
/-- `t'1 = y[i]; t'2 = z[i]; x[i] = t'1 + t'2;` -/
theorem body_triple (k : Nat) :
    Sep.Triple ge fe func (LMid px p bx byy bz ox oy oz vx0 fy fz k) bodyStmt
      (.only (LStored px p bx byy bz ox oy oz vx0 fy fz k)) := by
  refine Sep.triple_conseq ge fe func (P := fun e le hp =>
      ∃ iv, ∃ _ : iv < 3 ∧ 3 - iv = k, St px p bx byy bz ox oy oz vx0 fy fz iv e le hp) ?_
    (fun _ _ _ ⟨iv, hSt, hlt, hk⟩ => ⟨iv, ⟨hlt, hk⟩, hSt⟩) (fun _ _ _ x => x)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  refine Sep.triple_exists ge fe func _ _ _ (fun iv => ?_)
  refine Sep.triple_exists ge fe func _ _ _ (fun ⟨hlt, hk⟩ => ?_)
  -- `t'1 = y[i];`
  refine Sep.triple_seq_only ge fe func (Q := fun e le hp =>
      St px p bx byy bz ox oy oz vx0 fy fz iv e le hp ∧ iv < 3 ∧ 3 - iv = k
      ∧ le.get _t'1 = some (.Vfloat (fy iv))) ?_ ?_
  · refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, hx, hy, hz⟩, hi, harr⟩ := hP
    obtain ⟨_, hsrc, hag1⟩ := sep_right_agrees harr hag
    obtain ⟨_, hay, hagy⟩ := sep_left_agrees hsrc hag1
    refine ⟨.Vfloat (fy iv), eval_index_f64 hpr hay hagy hlt (EvalExpr.Etempvar _ _ _ hy)
      (EvalExpr.Etempvar _i tint _ hi) rfl (by omega) hnoy,
      ⟨⟨he, ?_, ?_, ?_⟩, ?_, harr⟩, hlt, hk, PTree.gss _ _ _⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
  -- `t'2 = z[i];`
  refine Sep.triple_seq_only ge fe func (Q := fun e le hp =>
      St px p bx byy bz ox oy oz vx0 fy fz iv e le hp ∧ iv < 3 ∧ 3 - iv = k
      ∧ le.get _t'1 = some (.Vfloat (fy iv)) ∧ le.get _t'2 = some (.Vfloat (fz iv))) ?_ ?_
  · refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨⟨he, hx, hy, hz⟩, hi, harr⟩, -, -, ht1⟩ := hP
    obtain ⟨_, hsrc, hag1⟩ := sep_right_agrees harr hag
    obtain ⟨_, haz, hagz⟩ := sep_right_agrees hsrc hag1
    refine ⟨.Vfloat (fz iv), eval_index_f64 hpr haz hagz hlt (EvalExpr.Etempvar _ _ _ hz)
      (EvalExpr.Etempvar _i tint _ hi) rfl (by omega) hnoz,
      ⟨⟨he, ?_, ?_, ?_⟩, ?_, harr⟩, hlt, hk, ?_, PTree.gss _ _ _⟩ <;>
    (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
  -- `x[i] = t'1 + t'2;`
  · let Rl : Env → TempEnv → Prop := fun e le =>
      Params bx byy bz ox oy oz e le ∧ le.get _i = some (.Vint (Integers.Int.repr iv))
      ∧ le.get _t'1 = some (.Vfloat (fy iv)) ∧ le.get _t'2 = some (.Vfloat (fz iv))
    have hst := triple_store_index_f64 ge fe func Rl (Src p byy bz oy oz fy fz)
      (.Etempvar _x (tptr tdouble)) (.Etempvar _i tint) sumExpr px bx ox 3 iv
      (upd vx0 fy fz iv) (Floats.Float.add (fy iv) (fz iv)) hpw (by omega) (by omega) hnox
      (fun e le m h => EvalExpr.Etempvar _ _ _ h.1.2.1)
      (fun e le m h => EvalExpr.Etempvar _i tint _ h.2.1)
      (fun e le m h => EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ h.2.2.1)
        (EvalExpr.Etempvar _ _ _ h.2.2.2) (semBinop_add_double _ _ _ _))
      rfl rfl
    rw [upd_succ] at hst
    refine Sep.triple_conseq ge fe func hst (fun e le hp h => ?_) (fun e le hp h => ?_)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    · obtain ⟨⟨hpar, hi, harr⟩, -, -, ht1, ht2⟩ := h
      exact ⟨⟨hpar, hi, ht1, ht2⟩, harr⟩
    · obtain ⟨⟨hpar, hi, _, _⟩, harr⟩ := h
      exact ⟨iv, ⟨hpar, hi, harr⟩, by omega, by omega⟩

theorem incr_triple (k : Nat) :
    Sep.Triple ge fe func (LStored px p bx byy bz ox oy oz vx0 fy fz k) setI
      (.only (fun e le hp => ∃ k', k' < k ∧ LInv px p bx byy bz ox oy oz vx0 fy fz k' e le hp)) := by
  refine Sep.triple_exists ge fe func _ _ _ (fun iv => ?_)
  refine Sep.triple_set ge fe func _ _ _ _ (fun e le hp m hP _ => ?_)
  obtain ⟨⟨⟨he, hx, hy, hz⟩, hi, harr⟩, hlt, hk⟩ := hP
  refine ⟨.Vint (Integers.Int.repr ((iv : _root_.Int) + 1)), ?_, ?_⟩
  · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Econst_int _ tint) ?_
    simp only [typeof]
    rw [semBinop_add_int, repr_add]
  · refine ⟨3 - (iv + 1), by omega, iv + 1, ⟨⟨he, ?_, ?_, ?_⟩, ?_, harr⟩, by omega, rfl⟩
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gso _ _ _ _ (by decide)]; assumption
    · rw [PTree.gss]; simp

include hpw hpr hnox hnoy hnoz in
theorem loop_triple (k : Nat) :
    Sep.Triple ge fe f_add (LInv px p bx byy bz ox oy oz vx0 fy fz k) loopStmt
      (LoopR px p bx byy bz ox oy oz vx0 fy fz) := by
  refine Sep.triple_loop ge fe f_add (LoopR px p bx byy bz ox oy oz vx0 fy fz)
    (LInv px p bx byy bz ox oy oz vx0 fy fz) (LStored px p bx byy bz ox oy oz vx0 fy fz) _ _
    (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_add _ (LMid px p bx byy bz ox oy oz vx0 fy fz k) _ _ _
      (Sep.triple_conseq ge fe f_add (if_triple ge fe px p bx byy bz ox oy oz vx0 fy fz k)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
        (fun _ _ x => x.elim))
      (Sep.triple_fallthrough ge fe f_add _ _ _ _
        (body_triple ge fe px p bx byy bz ox oy oz vx0 fy fz hpw hpr hnox hnoy hnoz k)
        (fun _ _ _ x => x))
  · exact Sep.triple_fallthrough ge fe f_add _ _ _ _
      (incr_triple ge fe px p bx byy bz ox oy oz vx0 fy fz k) (fun _ _ _ x => x)

end

/-! ## As a function specification (VST's `add_spec`) -/

/-- `add_spec`; `vx0` are the (arbitrary) initial contents of `x` (`data_at_`). -/
def addSpec (px p : Permission) (bx byy bz : Block) (ox oy oz : Integers.Ptrofs)
    (vx0 : Nat → Val) (fy fz : List Floats.Float) : Sep.FunSpec where
  tyargs := [tptr tdouble, tptr tdouble, tptr tdouble]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr bx ox, .Vptr byy oy, .Vptr bz oz]
    ∧ (arrayV64 px bx (Integers.Ptrofs.unsigned ox) 3 vx0
        ∗ Src p byy bz oy oz (elems fy) (elems fz)) hp
  post := fun _ hp =>
    (arrayF64 px bx (Integers.Ptrofs.unsigned ox) 3 (elems (List.zipWith Floats.Float.add fy fz))
      ∗ Src p byy bz oy oz (elems fy) (elems fz)) hp
  measure := fun _ => 0

theorem arrs_zero (px : Permission) (bx : Block) (o : _root_.Int) (vx0 : Nat → Val)
    (fy fz : Nat → Floats.Float) :
    arrayV64 px bx o 3 (upd vx0 fy fz 0) = arrayV64 px bx o 3 vx0 := by
  congr 1

theorem arrs_full (px : Permission) (bx : Block) (o : _root_.Int) (vx0 : Nat → Val)
    (fy fz : List Floats.Float) (hy : fy.length = 3) (hz : fz.length = 3) :
    arrayV64 px bx o 3 (upd vx0 (elems fy) (elems fz) 3)
      = arrayF64 px bx o 3 (elems (List.zipWith Floats.Float.add fy fz)) := by
  unfold arrayF64 arrayV64 array8
  refine arrayOf_congr _ _ _ (fun j hj => ?_)
  unfold cell8
  simp [upd, hj, elems, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem (show j < fy.length by omega),
    List.getElem?_eq_getElem (show j < fz.length by omega)]

/-- **`add` satisfies `add_spec`** (VST's `body_add`). -/
theorem add_satisfies (ge : CGenv) (px p : Permission) (bx byy bz : Block)
    (ox oy oz : Integers.Ptrofs) (vx0 : Nat → Val) (fy fz : List Floats.Float)
    (hy : fy.length = 3) (hz : fz.length = 3)
    (hpw : permOrder px .Writable = true) (hpr : permOrder p .Readable = true)
    (hnox : Integers.Ptrofs.unsigned ox + 8 * 3 ≤ 18446744073709551616)
    (hnoy : Integers.Ptrofs.unsigned oy + 8 * 3 ≤ 18446744073709551616)
    (hnoz : Integers.Ptrofs.unsigned oz + 8 * 3 ≤ 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_add)
      (addSpec px p bx byy bz ox oy oz vx0 fy fz) [.Vptr bx ox, .Vptr byy oy, .Vptr bz oz] := by
  refine satisfies_internal_noVars_void ge (FunctionEntry2 ge) f_add _ _
    (fun e le hp => Params bx byy bz ox oy oz e le
      ∧ Arrs px p bx byy bz ox oy oz vx0 (elems fy) (elems fz) 0 hp) (fun m => ?_) ?_
  · refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide) (AllocVariables.nil _ _)
      rfl, fun hp hpre => ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    rw [Arrs, arrs_zero]; exact hpre.2
  · rw [body_eq]
    refine Sep.triple_seq_only ge (FunctionEntry2 ge) f_add
      (Q := LInv px p bx byy bz ox oy oz vx0 (elems fy) (elems fz) 3) ?_
      (Sep.triple_conseq ge (FunctionEntry2 ge) f_add
        (loop_triple ge (FunctionEntry2 ge) px p bx byy bz ox oy oz vx0 (elems fy) (elems fz)
          hpw hpr hnox hnoy hnoz 3)
        (fun _ _ _ x => x) (fun e le hp h => ?_) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x.elim))
    · refine Sep.triple_set ge (FunctionEntry2 ge) f_add _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨⟨he, hx, hy', hz'⟩, harr⟩ := hP
      refine ⟨_, EvalExpr.Econst_int _ tint, 0, ⟨⟨he, ?_, ?_, ?_⟩, PTree.gss _ _ _, harr⟩,
        by omega, by omega⟩ <;>
      (rw [PTree.gso _ _ _ _ (by decide)]; assumption)
    · obtain ⟨he, harr⟩ := h
      refine ⟨he, ?_⟩
      show (arrayF64 _ _ _ _ _ ∗ _) hp
      rw [← arrs_full px bx _ vx0 fy fz hy hz]
      exact harr

end VST.Verif.DotprodAdd
