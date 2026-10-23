/-
  Port of `cfrontend/Cexec.v`, part 4: `step_expr_sound` and
  `step_exprlist_sound` (`Cexec.v` lines 1413–1613): every reduct listed by
  `stepExpr` is a correct reduction (a head reduction at a reduction context,
  or a correct claim that the expression is stuck), and no reduct is listed
  only when the expression is fully reduced.
-/
import CCLib.cfrontend.CexecExpr

namespace CC
namespace Cexec

open Csyntax

section EXPRS

variable (ge : Csem.CGenv) (ox : ExtOracle) (e : Env) (w : World)

/-- The wrong-kind cases of `step_expr_sound`. -/
theorem stepExpr_wrongKind {k a m} (h : k ≠ Cstrategy.exprKind a)
    (hs : stepExpr ge ox e w k a m = stuck) : ReductsOk ge e w k a m (stepExpr ge ox e w k a m) := by
  rw [hs]; exact wrong_kind_ok ge e w h

mutual
/-- `Cexec.step_expr_sound` -/
theorem stepExpr_sound (hinj : Genv.SymbInjective ge.genv_genv) (hS : ox.Sound)
    (hC : ox.Complete) :
    ∀ (a : Csyntax.Expr) (k : Csem.Kind) (m : Mem),
      ReductsOk ge e w k a m (stepExpr ge ox e w k a m)
  | .Eval v ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eval v ty, .RV, m => ⟨(fun _ _ h => nomatch h), (fun _ => by simp [isVal])⟩
  | .Evar x ty, .RV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Evar x ty, .LV, m => by
      simp only [stepExpr]
      split
      · next b ty' hget =>
          split
          · next heq => subst heq; apply topred_ok; exact .var_local _ _ _ _ hget
          · next hne =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨b', hb' | ⟨hn, _⟩⟩
              · rw [hget] at hb'; cases hb'; exact hne rfl
              · rw [hget] at hn; cases hn
      · next hget =>
          split
          · next b hb => apply topred_ok; exact .var_global _ _ _ _ hget hb
          · next hb =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨b', hb' | ⟨_, hf⟩⟩
              · rw [hget] at hb'; cases hb'
              · rw [hb] at hf; cases hf
  | .Eloc b ofs bf ty, .LV, m => ⟨(fun _ _ h => nomatch h), (fun _ => by simp [isLoc])⟩
  | .Eloc b ofs bf ty, .RV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ederef r ty, .RV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ederef r ty, .LV, m => by
      simp only [stepExpr]
      split
      · next b ofs ty' hv =>
          rw [isVal_inv hv]; apply topred_ok; exact .deref _ _ _ _ _
      · next x hnp hv =>
          obtain ⟨v, ty'⟩ := x
          rw [isVal_inv hv]
          refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
          rintro ⟨b, ofs, rfl⟩
          exact hnp b ofs ty' rfl
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r .RV m) rfl
            (.deref _ _ _ (.top _)) hv
  | .Efield r f ty, .RV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Efield r f ty, .LV, m => by
      simp only [stepExpr]
      split
      · next b ofs ty' hv =>
          rw [isVal_inv hv]
          split
          · next id a =>
              split
              · next co hco =>
                  split
                  · next msg hfo =>
                      refine not_invert_ok ge e w (fun _ _ h => nomatch h)
                        (fun _ _ _ _ h => nomatch h) ?_
                      rintro ⟨b', ofs', _, co', delta, bf, hco', hfo'⟩
                      rw [hco] at hco'; cases hco'; rw [hfo] at hfo'; cases hfo'
                  · next delta bf hfo => apply topred_ok; exact .field_struct _ _ _ _ _ _ _ _ _ _ hco hfo
              · next hco =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h)
                    (fun _ _ _ _ h => nomatch h) ?_
                  rintro ⟨b', ofs', _, co', delta, bf, hco', hfo'⟩
                  rw [hco] at hco'; cases hco'
          · next id a =>
              split
              · next co hco =>
                  split
                  · next msg hfo =>
                      refine not_invert_ok ge e w (fun _ _ h => nomatch h)
                        (fun _ _ _ _ h => nomatch h) ?_
                      rintro ⟨b', ofs', _, co', delta, bf, hco', hfo'⟩
                      rw [hco] at hco'; cases hco'; rw [hfo] at hfo'; cases hfo'
                  · next delta bf hfo => apply topred_ok; exact .field_union _ _ _ _ _ _ _ _ _ _ hco hfo
              · next hco =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h)
                    (fun _ _ _ _ h => nomatch h) ?_
                  rintro ⟨b', ofs', _, co', delta, bf, hco', hfo'⟩
                  rw [hco] at hco'; cases hco'
          · next hs hu =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h)
                (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨b', ofs', _, hty⟩
              split at hty
              · next id a => exact hs id a rfl
              · next id a => exact hu id a rfl
              · exact hty
      · next x hnp hv =>
          obtain ⟨v, ty'⟩ := x
          rw [isVal_inv hv]
          refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
          rintro ⟨b, ofs, rfl, _⟩
          exact hnp b ofs ty' rfl
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r .RV m) rfl
            (.field _ _ _ _ (.top _)) hv
  | .Evalof l ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eaddrof l ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eunop op r ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ebinop op r1 r2 ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ecast r ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eseqand r1 r2 ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eseqor r1 r2 ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Econdition r1 r2 r3 ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Esizeof ty' ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ealignof ty' ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eassign l r ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eassignop op l r tyres ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Epostincr id l ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ecomma r1 r2 ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ecall r rl ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Ebuiltin ef tyargs rl ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Eparen r tycast ty, .LV, m => stepExpr_wrongKind ge ox e w nofun rfl
  | .Evalof l ty, .RV, m => by
      simp only [stepExpr]
      split
      · next b ofs bf ty' hl =>
          rw [isLoc_inv hl]
          split
          · next heq =>
              subst heq
              split
              · next w' t v hd =>
                  obtain ⟨h1, h2⟩ := doDerefLoc_sound ge hd
                  apply topred_ok; exact ⟨.rvalof _ _ _ _ _ _ _ h1, w', h2⟩
              · next hd =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                  rintro ⟨_, t, v, w', h1, h2⟩
                  rw [doDerefLoc_complete ge hinj h1 h2] at hd; cases hd
          · next hne =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨heq, _⟩; exact hne heq.symm
      · next hl =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC l .LV m) rfl
            (.rvalof _ _ _ (.top _)) hl
  | .Eaddrof l ty, .RV, m => by
      simp only [stepExpr]
      split
      · next b ofs bf ty' hl =>
          rw [isLoc_inv hl]
          split
          · apply topred_ok; exact ⟨.addrof _ _ _ _ _, w, .nil _⟩
          · refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
            intro h; cases h
      · next hl =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC l .LV m) rfl
            (.addrof _ _ _ (.top _)) hl
  | .Eunop op r ty, .RV, m => by
      simp only [stepExpr]
      split
      · next v1 ty1 hv =>
          rw [isVal_inv hv]
          split
          · next v hu => apply topred_ok; exact ⟨.unop _ _ _ _ _ _ hu, w, .nil _⟩
          · next hu =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨v, hv'⟩; rw [hu] at hv'; cases hv'
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r .RV m) rfl
            (.unop _ _ _ _ (.top _)) hv
  | .Ebinop op r1 r2 ty, .RV, m => by
      simp only [stepExpr]
      split
      · next v1 ty1 v2 ty2 hv1 hv2 =>
          rw [isVal_inv hv1, isVal_inv hv2]
          split
          · next v hb => apply topred_ok; exact ⟨.binop _ _ _ _ _ _ _ _ hb, w, .nil _⟩
          · next hb =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨v, hv'⟩; rw [hb] at hv'; cases hv'
      · next hnot =>
          refine incontext2_ok ge e w (stepExpr_sound hinj hS hC r1 .RV m)
            (stepExpr_sound hinj hS hC r2 .RV m) rfl rfl
            (.binop_left _ _ _ _ _ (.top _)) (.binop_right _ _ _ _ _ (.top _)) ?_
          cases h1 : isVal r1 with
          | none => exact .inl rfl
          | some p =>
              cases h2 : isVal r2 with
              | none => exact .inr rfl
              | some q => exact (hnot p.1 p.2 q.1 q.2 h1 h2).elim
  | .Ecast r ty, .RV, m => by
      simp only [stepExpr]
      split
      · next v1 ty1 hv =>
          rw [isVal_inv hv]
          split
          · next v hu => apply topred_ok; exact ⟨.cast _ _ _ _ _ hu, w, .nil _⟩
          · next hu =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨v, hv'⟩; rw [hu] at hv'; cases hv'
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r .RV m) rfl
            (.cast _ _ _ (.top _)) hv
  | .Eseqand r1 r2 ty, .RV, m => by
      simp only [stepExpr]
      split
      · next v1 ty1 hv =>
          rw [isVal_inv hv]
          split
          · next b hb =>
              cases b
              · apply topred_ok; exact ⟨.seqand_false _ _ _ _ _ hb, w, .nil _⟩
              · apply topred_ok; exact ⟨.seqand_true _ _ _ _ _ hb, w, .nil _⟩
          · next hb =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨b, hb'⟩; rw [hb] at hb'; cases hb'
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r1 .RV m) rfl
            (.seqand _ _ _ _ (.top _)) hv
  | .Eseqor r1 r2 ty, .RV, m => by
      simp only [stepExpr]
      split
      · next v1 ty1 hv =>
          rw [isVal_inv hv]
          split
          · next b hb =>
              cases b
              · apply topred_ok; exact ⟨.seqor_false _ _ _ _ _ hb, w, .nil _⟩
              · apply topred_ok; exact ⟨.seqor_true _ _ _ _ _ hb, w, .nil _⟩
          · next hb =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨b, hb'⟩; rw [hb] at hb'; cases hb'
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r1 .RV m) rfl
            (.seqor _ _ _ _ (.top _)) hv
  | .Econdition r1 r2 r3 ty, .RV, m => by
      simp only [stepExpr]
      split
      · next v1 ty1 hv =>
          rw [isVal_inv hv]
          split
          · next b hb => apply topred_ok; exact ⟨.condition _ _ _ _ _ _ _ hb, w, .nil _⟩
          · next hb =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨b, hb'⟩; rw [hb] at hb'; cases hb'
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r1 .RV m) rfl
            (.condition _ _ _ _ _ (.top _)) hv
  | .Esizeof ty' ty, .RV, m => by
      simp only [stepExpr]; apply topred_ok; exact ⟨.sizeof _ _ _, w, .nil _⟩
  | .Ealignof ty' ty, .RV, m => by
      simp only [stepExpr]; apply topred_ok; exact ⟨.alignof _ _ _, w, .nil _⟩
  | .Eassign l r ty, .RV, m => by
      simp only [stepExpr]
      split
      · next b ofs bf ty1 v2 ty2 hl hv =>
          rw [isLoc_inv hl, isVal_inv hv]
          split
          · next heq =>
              subst heq
              split
              · next v hc =>
                  split
                  · next w' t m' v' ha =>
                      obtain ⟨h1, h2⟩ := doAssignLoc_sound ge ha
                      apply topred_ok; exact ⟨.assign _ _ _ _ _ _ _ _ _ _ _ hc h1, w', h2⟩
                  · next ha =>
                      refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                      rintro ⟨v', m', v'', t, w', _, hc', h1, h2⟩
                      rw [hc] at hc'; cases hc'
                      rw [doAssignLoc_complete ge hinj h1 h2] at ha; cases ha
              · next hc =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                  rintro ⟨v', _, _, _, _, _, hc', _⟩; rw [hc] at hc'; cases hc'
          · next hne =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨_, _, _, _, _, heq, _⟩; exact hne heq.symm
      · next hnot =>
          refine incontext2_ok ge e w (stepExpr_sound hinj hS hC l .LV m)
            (stepExpr_sound hinj hS hC r .RV m) rfl rfl
            (.assign_left _ _ _ _ (.top _)) (.assign_right _ _ _ _ (.top _)) ?_
          cases h1 : isLoc l with
          | none => exact .inl rfl
          | some p =>
              cases h2 : isVal r with
              | none => exact .inr rfl
              | some q => exact (hnot p.1 p.2.1 p.2.2.1 p.2.2.2 q.1 q.2 h1 h2).elim
  | .Eassignop op l r tyres ty, .RV, m => by
      simp only [stepExpr]
      split
      · next b ofs bf ty1 v2 ty2 hl hv =>
          rw [isLoc_inv hl, isVal_inv hv]
          split
          · next heq =>
              subst heq
              split
              · next w' t v1 hd =>
                  obtain ⟨h1, h2⟩ := doDerefLoc_sound ge hd
                  apply topred_ok; exact ⟨.assignop _ _ _ _ _ _ _ _ _ _ _ h1, w', h2⟩
              · next hd =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                  rintro ⟨t, v1, w', _, h1, h2⟩
                  rw [doDerefLoc_complete ge hinj h1 h2] at hd; cases hd
          · next hne =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨_, _, _, heq, _⟩; exact hne heq.symm
      · next hnot =>
          refine incontext2_ok ge e w (stepExpr_sound hinj hS hC l .LV m)
            (stepExpr_sound hinj hS hC r .RV m) rfl rfl
            (.assignop_left _ _ _ _ _ _ (.top _)) (.assignop_right _ _ _ _ _ _ (.top _)) ?_
          cases h1 : isLoc l with
          | none => exact .inl rfl
          | some p =>
              cases h2 : isVal r with
              | none => exact .inr rfl
              | some q => exact (hnot p.1 p.2.1 p.2.2.1 p.2.2.2 q.1 q.2 h1 h2).elim
  | .Epostincr id l ty, .RV, m => by
      simp only [stepExpr]
      split
      · next b ofs bf ty1 hl =>
          rw [isLoc_inv hl]
          split
          · next heq =>
              subst heq
              split
              · next w' t v1 hd =>
                  obtain ⟨h1, h2⟩ := doDerefLoc_sound ge hd
                  apply topred_ok; exact ⟨.postincr _ _ _ _ _ _ _ _ _ h1 rfl, w', h2⟩
              · next hd =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                  rintro ⟨t, v1, w', _, h1, h2⟩
                  rw [doDerefLoc_complete ge hinj h1 h2] at hd; cases hd
          · next hne =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨_, _, _, heq, _⟩; exact hne heq.symm
      · next hl =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC l .LV m) rfl
            (.postincr _ _ _ _ (.top _)) hl
  | .Ecomma r1 r2 ty, .RV, m => by
      simp only [stepExpr]
      split
      · next x hv =>
          obtain ⟨v, ty1⟩ := x
          rw [isVal_inv hv]
          split
          · next ht => apply topred_ok; exact ⟨.comma _ _ _ _ _ ht, w, .nil _⟩
          · next ht =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              exact ht
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r1 .RV m) rfl
            (.comma _ _ _ _ (.top _)) hv
  | .Eparen r tycast ty, .RV, m => by
      simp only [stepExpr]
      split
      · next v1 ty1 hv =>
          rw [isVal_inv hv]
          split
          · next v hu => apply topred_ok; exact ⟨.paren _ _ _ _ _ _ hu, w, .nil _⟩
          · next hu =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              rintro ⟨v, hv'⟩; rw [hu] at hv'; cases hv'
      · next hv =>
          exact incontext_ok ge e w (stepExpr_sound hinj hS hC r .RV m) rfl
            (.paren _ _ _ _ (.top _)) hv
  | .Ecall r rl ty, .RV, m => by
      simp only [stepExpr]
      split
      · next vf tyf vtl hv hvl =>
          rw [isVal_inv hv]
          have hall := isValList_allValues hvl
          split
          · next tyargs tyres cconv hcf =>
              split
              · next fd hfd =>
                  split
                  · next vargs hca =>
                      split
                      · next hty =>
                          apply topred_ok
                          exact ⟨.call _ _ _ _ _ _ _ _ _ _ hfd (semCastArguments_sound hvl hca) hty hcf, rfl⟩
                      · next hty =>
                          refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                          intro hinv
                          obtain ⟨_, _, _, _, _, hcf', hfd', _, hty'⟩ := hinv hall
                          rw [hcf] at hcf'; cases hcf'; rw [hfd] at hfd'; cases hfd'; exact hty hty'
                  · next hca =>
                      refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                      intro hinv
                      obtain ⟨_, _, _, _, _, hcf', _, hca', _⟩ := hinv hall
                      rw [hcf] at hcf'; cases hcf'
                      obtain ⟨vtl', h1, h2⟩ := semCastArguments_complete hca'
                      rw [hvl] at h1; cases h1; rw [hca] at h2; cases h2
              · next hfd =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                  intro hinv
                  obtain ⟨_, _, _, _, _, hcf', hfd', _, _⟩ := hinv hall
                  rw [hcf] at hcf'; cases hcf'; rw [hfd] at hfd'; cases hfd'
          · next hcf =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              intro hinv
              obtain ⟨_, _, _, _, _, hcf', _, _, _⟩ := hinv hall
              exact hcf _ _ _ hcf'
      · next hnot =>
          refine incontext2_list_ok ge e w (stepExpr_sound hinj hS hC r .RV m)
            (stepExprlist_sound hinj hS hC rl m) ?_
          cases h1 : isVal r with
          | none => exact .inl rfl
          | some p =>
              cases h2 : isValList rl with
              | none => exact .inr rfl
              | some q => exact (hnot p.1 p.2 q h1 h2).elim
  | .Ebuiltin ef tyargs rl ty, .RV, m => by
      simp only [stepExpr]
      split
      · next vtl hvl =>
          have hall := isValList_allValues hvl
          split
          · next vargs hca =>
              split
              · next hext =>
                  refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
                  intro hinv
                  obtain ⟨vargs', t, vres, m', w', hca', hec, hp⟩ := hinv hall
                  obtain ⟨vtl', h1, h2⟩ := semCastArguments_complete hca'
                  rw [hvl] at h1; cases h1; rw [hca] at h2; cases h2
                  rw [doExternal_complete ge ox hinj hC hec hp] at hext; cases hext
              · next w' t v m' hext =>
                  obtain ⟨h1, h2⟩ := doExternal_sound ge ox hS hext
                  apply topred_ok
                  exact ⟨.builtin _ _ _ _ _ _ _ _ _ (semCastArguments_sound hvl hca) h1, w', h2⟩
          · next hca =>
              refine not_invert_ok ge e w (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) ?_
              intro hinv
              obtain ⟨vargs', t, vres, m', w', hca', _, _⟩ := hinv hall
              obtain ⟨vtl', h1, h2⟩ := semCastArguments_complete hca'
              rw [hvl] at h1; cases h1; rw [hca] at h2; cases h2
      · next hvl =>
          exact incontext_list_ok ge e w (stepExprlist_sound hinj hS hC rl m) hvl

/-- `Cexec.step_exprlist_sound` -/
theorem stepExprlist_sound (hinj : Genv.SymbInjective ge.genv_genv) (hS : ox.Sound)
    (hC : ox.Complete) :
    ∀ (al : Csyntax.ExprList) (m : Mem), ListReductsOk ge e w al m (stepExprlist ge ox e w al m)
  | .Enil, m => ⟨(fun _ _ h => nomatch h), (fun _ => by simp [isValList])⟩
  | .Econs a1 al, m =>
      incontext2_list_ok' ge e w (stepExpr_sound hinj hS hC a1 .RV m)
        (stepExprlist_sound hinj hS hC al m)
end

end EXPRS

end Cexec
end CC
