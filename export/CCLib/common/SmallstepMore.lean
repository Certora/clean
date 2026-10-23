/-
  The remaining sequence lemmas of `common/Smallstep.v` (complementing
  `CCLib.common.Smallstep`): runs of two, three and four steps
  (`star_three`, `star_four`, `plus_two`, `plus_three`, `plus_four`),
  `plus_left'`/`plus_right'`, and the induction principles `plus_ind2` and
  `plus_E0_ind`.
-/
import CCLib.common.Smallstep
import CCLib.common.EventsTraceinf

namespace CC
namespace Smallstep

variable {σ : Type} {R : σ → Trace → σ → Prop}

theorem star_three {s1 t1 s2 t2 s3 t3 s4 t} (h1 : R s1 t1 s2) (h2 : R s2 t2 s3)
    (h3 : R s3 t3 s4) (ht : t = Eapp t1 (Eapp t2 t3)) : Star R s1 t s4 :=
  .step h1 (star_two h2 h3 rfl) ht

theorem star_four {s1 t1 s2 t2 s3 t3 s4 t4 s5 t} (h1 : R s1 t1 s2) (h2 : R s2 t2 s3)
    (h3 : R s3 t3 s4) (h4 : R s4 t4 s5) (ht : t = Eapp t1 (Eapp t2 (Eapp t3 t4))) :
    Star R s1 t s5 :=
  .step h1 (star_three h2 h3 h4 rfl) ht

theorem plus_two {s1 t1 s2 t2 s3 t} (h1 : R s1 t1 s2) (h2 : R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 :=
  plus_left h1 (star_one h2) ht

theorem plus_three {s1 t1 s2 t2 s3 t3 s4 t} (h1 : R s1 t1 s2) (h2 : R s2 t2 s3)
    (h3 : R s3 t3 s4) (ht : t = Eapp t1 (Eapp t2 t3)) : Plus R s1 t s4 :=
  plus_left h1 (star_two h2 h3 rfl) ht

theorem plus_four {s1 t1 s2 t2 s3 t3 s4 t4 s5 t} (h1 : R s1 t1 s2) (h2 : R s2 t2 s3)
    (h3 : R s3 t3 s4) (h4 : R s4 t4 s5) (ht : t = Eapp t1 (Eapp t2 (Eapp t3 t4))) :
    Plus R s1 t s5 :=
  plus_left h1 (star_three h2 h3 h4 rfl) ht

theorem plus_left' {s1 t1 s2 t2 s3 t} (h1 : R s1 t1 s2) (h2 : Plus R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 :=
  plus_left h1 (plus_star h2) ht

theorem plus_right' {s1 t1 s2 t2 s3 t} (h1 : Plus R s1 t1 s2) (h2 : R s2 t2 s3)
    (ht : t = Eapp t1 t2) : Plus R s1 t s3 :=
  plus_right (plus_star h1) h2 ht

/-- `plus_ind2`: induction on a non-empty run, by its first step. -/
theorem plus_ind2 (P : σ → Trace → σ → Prop)
    (base : ∀ s1 t s2, R s1 t s2 → P s1 t s2)
    (ind : ∀ s1 t1 s2 t2 s3 t, R s1 t1 s2 → Plus R s2 t2 s3 → P s2 t2 s3 →
      t = Eapp t1 t2 → P s1 t s3) :
    ∀ {s1 t s2}, Plus R s1 t s2 → P s1 t s2 := by
  have key : ∀ {s1 t s2}, Star R s1 t s2 → ∀ {s0 t0}, R s0 t0 s1 → P s0 (Eapp t0 t) s2 := by
    intro s1 t s2 h
    induction h with
    | refl => intro s0 t0 h0; rw [E0_right]; exact base _ _ _ h0
    | step hr hs heq ih =>
      intro s0 t0 h0
      exact ind _ _ _ _ _ _ h0 (.intro hr hs heq) (heq ▸ ih hr) rfl
  intro s1 t s2 h
  cases h with
  | intro hr hs heq => subst heq; exact key hs hr

/-- `plus_E0_ind` -/
theorem plus_E0_ind (P : σ → σ → Prop)
    (h : ∀ s1 s2 s3, R s1 E0 s2 → Star R s2 E0 s3 → P s1 s3) :
    ∀ {s1 s2}, Plus R s1 E0 s2 → P s1 s2 := by
  intro s1 s2 hp
  cases hp with
  | intro hr hs heq =>
    obtain ⟨rfl, rfl⟩ := Eapp_E0_inv heq.symm
    exact h _ _ _ hr hs

end Smallstep
end CC
