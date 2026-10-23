/-
  Expression simplification: semantic preservation — port of
  `cfrontend/SimplExprproof.v`, part 3: the semantics of the smart
  constructors (`makeif`, `make_set`, `make_assign`, `makeseq`) in Clight, and
  the execution of the statements produced by `tr_rvalof`.

  Differences from Rocq:
  * `step_makeif` is proved by case analysis on `eval_simpl_expr` instead of
    `functional induction`;
  * the source and target global environments are related by `GenvRel`.
-/
import CCLib.cfrontend.SimplExprproofContext

namespace CC
namespace SimplExpr

open Destination SetDestination Cstrategy

/-! ## Static evaluation -/

/-- `SimplExprproof.sem_cast_deterministic` -/
theorem semCast_deterministic {v : Val} {ty ty' : Ty} {m1 m2 : Mem} {v1 v2 : Val}
    (h1 : Cop.semCast v ty ty' m1 = some v1) (h2 : Cop.semCast v ty ty' m2 = some v2) :
    v1 = v2 := by
  unfold Cop.semCast at h1 h2
  cases hc : Cop.classifyCast ty ty' <;> simp only [hc] at h1 h2 <;> cases v <;>
    simp_all <;> (try split at h1) <;> (try split at h2) <;> simp_all

/-- `SimplExprproof.eval_simpl_expr_sound` -/
theorem eval_simpl_expr_sound {tge : CGenv} {e le m} :
    ∀ (a : Expr) {v}, EvalExpr tge e le m a v →
      match evalSimplExpr a with
      | some v' => v' = v
      | none => True
  | .Econst_int _ _, _, h => by
    cases h with
    | Econst_int => rfl
    | Elvalue _ _ _ _ _ hl _ => cases hl
  | .Econst_float _ _, _, h => by
    cases h with
    | Econst_float => rfl
    | Elvalue _ _ _ _ _ hl _ => cases hl
  | .Econst_single _ _, _, h => by
    cases h with
    | Econst_single => rfl
    | Elvalue _ _ _ _ _ hl _ => cases hl
  | .Econst_long _ _, _, h => by
    cases h with
    | Econst_long => rfl
    | Elvalue _ _ _ _ _ hl _ => cases hl
  | .Ecast a ty, _, h => by
    cases h with
    | Ecast _ _ v1 v h1 hc =>
      have ih := eval_simpl_expr_sound a h1
      simp only [evalSimplExpr]
      cases hs : evalSimplExpr a with
      | none => trivial
      | some v' =>
        rw [hs] at ih
        subst ih
        cases hc' : Cop.semCast v' (typeof a) ty Mem.empty with
        | none => simp [hc']
        | some v'' => simp only [hc']; exact semCast_deterministic hc' hc
    | Elvalue _ _ _ _ _ hl _ => cases hl
  | .Evar _ _, _, _ => trivial
  | .Etempvar _ _, _, _ => trivial
  | .Ederef _ _, _, _ => trivial
  | .Eaddrof _ _, _, _ => trivial
  | .Eunop _ _ _, _, _ => trivial
  | .Ebinop _ _ _ _, _, _ => trivial
  | .Efield _ _ _, _, _ => trivial
  | .Esizeof _ _, _, _ => trivial
  | .Ealignof _ _, _, _ => trivial

theorem weakValidPointer_empty (b : Block) (ofs : Z) : Mem.weakValidPointer Mem.empty b ofs = false := by
  simp [Mem.weakValidPointer, Mem.validPointer, Mem.perm, Mem.empty, PMap.gi, permOrder']

/-- `SimplExprproof.static_bool_val_sound` -/
theorem static_bool_val_sound {v : Val} {t : Ty} {m : Mem} {b : Bool}
    (h : Cop.boolVal v t Mem.empty = some b) : Cop.boolVal v t m = some b := by
  unfold Cop.boolVal at h ⊢
  cases hcb : Cop.classifyBool t <;> simp only [hcb] at h ⊢ <;> cases v <;>
    simp_all [weakValidPointer_empty]

section STEPS
variable {ge : Csem.CGenv} {tge : CGenv}

/-- `SimplExprproof.step_makeif` -/
theorem step_makeif {f a s1 s2 k e le m v1 b} (hev : EvalExpr tge e le m a v1)
    (hb : Cop.boolVal v1 (typeof a) m = some b) :
    Smallstep.Star (Step1 tge) (.State f (makeif a s1 s2) k e le m) E0
      (.State f (if b then s1 else s2) k e le m) := by
  unfold makeif
  have hs := eval_simpl_expr_sound a hev
  split
  · rename_i v hv
    rw [hv] at hs
    subst hs
    split
    · rename_i b' hb'
      have := static_bool_val_sound (m := m) hb'
      rw [hb] at this
      cases this
      exact Smallstep.Star.refl _
    · exact Smallstep.star_one (Step.ifthenelse _ _ _ _ _ _ _ _ _ _ hev hb)
  · exact Smallstep.star_one (Step.ifthenelse _ _ _ _ _ _ _ _ _ _ hev hb)

variable (GR : GenvRel ge tge)
include GR

/-- `SimplExprproof.step_make_set` -/
theorem step_make_set {id a ty m b ofs bf t v e le f k}
    (hd : Csem.DerefLoc ge ty m b ofs bf t v) (hl : EvalLvalue tge e le m a b ofs bf)
    (hty : typeof a = ty) :
    Step1 tge (.State f (makeSet bf id a) k e le m) t (.State f .Sskip k e (le.set id v) m) := by
  have hd' := deref_loc_translated GR.senv hd
  subst hty
  unfold makeSet
  split
  · rename_i hc
    rw [hc] at hd'
    obtain ⟨rfl, hd'⟩ := hd'
    exact .set _ _ _ _ _ _ _ _ (.Elvalue _ _ _ _ _ hl hd')
  · rename_i chunk hc
    rw [hc] at hd'
    obtain ⟨rfl, hd'⟩ := hd'
    exact .builtin _ (some id) _ _ _ _ _ _ _ [.Vptr b ofs] _ _ _
      (.cons _ _ _ _ _ _ _ (.Eaddrof _ _ _ _ hl) (by simp [Cop.semCast, Cop.classifyCast, typeof])
        .nil)
      (.intro _ _ _ _ _ _ hd')

/-- `SimplExprproof.step_make_assign` -/
theorem step_make_assign {a1 a2 ty m b ofs bf t v m' v' v2 e le f k}
    (ha : Csem.AssignLoc ge ty m b ofs bf v t m' v') (hl : EvalLvalue tge e le m a1 b ofs bf)
    (hev : EvalExpr tge e le m a2 v2) (hc : Cop.semCast v2 (typeof a2) ty m = some v)
    (hty : typeof a1 = ty) :
    Step1 tge (.State f (makeAssign bf a1 a2) k e le m) t (.State f .Sskip k e le m') := by
  have ha' := assign_loc_translated GR.senv GR.cenv ha
  subst hty
  unfold makeAssign
  split
  · rename_i hch
    rw [hch] at ha'
    obtain ⟨rfl, ha'⟩ := ha'
    exact .assign _ _ _ _ _ _ _ _ _ _ _ _ _ hl hev hc ha'
  · rename_i chunk hch
    rw [hch] at ha'
    obtain ⟨rfl, ha'⟩ := ha'
    exact .builtin _ none _ _ _ _ _ _ _ [.Vptr b ofs, v] _ _ _
      (.cons _ _ _ _ _ _ _ (.Eaddrof _ _ _ _ hl) (by simp [Cop.semCast, Cop.classifyCast, typeof])
        (.cons _ _ _ _ _ _ _ hev hc .nil))
      (.intro _ _ _ _ _ _ _ ha')

end STEPS

/-! ## Statement sequences -/

/-- `SimplExprproof.Kseqlist` -/
def Kseqlist : List Stmt → Cont → Cont
  | [], k => k
  | s :: l, k => .Kseq s (Kseqlist l k)

/-- `SimplExprproof.Kseqlist_app` -/
theorem Kseqlist_app (sl1 sl2 : List Stmt) (k : Cont) :
    Kseqlist (sl1 ++ sl2) k = Kseqlist sl1 (Kseqlist sl2 k) := by
  induction sl1 with
  | nil => rfl
  | cons s l ih => simp only [List.cons_append, Kseqlist, ih]

theorem push_seq_rec {tge : CGenv} {f e le m} :
    ∀ (sl : List Stmt) (s : Stmt) (k : Cont),
      Smallstep.Star (Step1 tge) (.State f (makeseqRec s sl) k e le m) E0
        (.State f s (Kseqlist sl k) e le m)
  | [], _, _ => Smallstep.Star.refl _
  | s' :: l, s, k =>
    Smallstep.star_right (push_seq_rec l (.Ssequence s s') k) (Step.seq _ _ _ _ _ _ _) rfl

/-- `SimplExprproof.push_seq` -/
theorem push_seq {tge : CGenv} {f sl k e le m} :
    Smallstep.Star (Step1 tge) (.State f (makeseq sl) k e le m) E0
      (.State f .Sskip (Kseqlist sl k) e le m) :=
  push_seq_rec sl .Sskip k

/-! ## Reading an l-value through `tr_rvalof` -/

section RVALOF
variable {ge : Csem.CGenv} {tge : CGenv} (GR : GenvRel ge tge) {ce : CompositeEnv}
  (hce : tge.genv_cenv = ce)
include GR hce

/-- `SimplExprproof.step_tr_rvalof` -/
theorem step_tr_rvalof {ty m b ofs bf t v e le a sl a' tmp f k}
    (hd : Csem.DerefLoc ge ty m b ofs bf t v) (hl : EvalLvalue tge e le m a b ofs bf)
    (htr : TrRvalof ce ty a sl a' tmp) (hty : typeof a = ty) :
    ∃ le', Smallstep.Star (Step1 tge) (.State f .Sskip (Kseqlist sl k) e le m) t
        (.State f .Sskip k e le' m) ∧
      EvalExpr tge e le' m a' v ∧ typeof a' = typeof a ∧
      ∀ x, x ∉ tmp → le'.get x = le.get x := by
  cases htr with
  | tr_rvalof_nonvol =>
    rename_i hv
    have hd' := deref_loc_translated GR.senv hd
    rw [chunkForVolatileType_eq_none.2 (by simp [hv])] at hd'
    obtain ⟨rfl, hd'⟩ := hd'
    subst hty
    exact ⟨le, Smallstep.Star.refl _, .Elvalue _ _ _ _ _ hl hd', rfl, fun _ _ => rfl⟩
  | tr_rvalof_vol =>
    rename_i t0 bf0 hv hbf hin
    have := is_bitfield_access_sound hce hl hbf
    subst this
    refine ⟨le.set t0 v, Smallstep.star_two (Step.skip_seq _ _ _ _ _ _) (step_make_set GR hd hl hty)
      rfl, .Etempvar _ _ _ (PTree.gss _ _ _), hty.symm, fun x hx => PTree.gso _ _ _ _ ?_⟩
    rintro rfl; exact hx hin

end RVALOF

end SimplExpr
end CC
