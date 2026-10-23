/-
  Forward simulations with the "eventually" modality — port of the
  `eventually` part of `common/Smallstep.v`: the predicate `eventually`
  (`eventually_now`, `eventually_later`), `eventually_one`,
  `eventually_trans`, `eventually_implies`, `eventually_and_invariant`, and the
  simulation diagrams `forward_simulation_eventually_star_wf` and
  `forward_simulation_eventually_star`.

  Difference from Rocq: `eventually` is stated directly for a step relation
  `R` and a final-state predicate `fin` (Rocq abstracts over `genv` and writes
  `Eventually L` for the instance with `step L`, `final_state L`,
  `globalenv L`). Because Lean's kernel rejects the nested occurrence of
  `Eventually` under `∧`, the second constructor takes the two conjuncts
  as separate hypotheses; `Eventually.later'` is Rocq's form.
-/
import CCLib.common.Simulation

namespace CC
namespace Smallstep

section Eventually
variable {σ : Type} (R : σ → Trace → σ → Prop) (fin : σ → Integers.Int → Prop)

/-- `Smallstep.eventually`: all transition sequences of length `n` starting from
`s` are silent and lead to a state satisfying `P` (some transitions may get stuck on
non-final states). -/
inductive Eventually : Nat → σ → (σ → Prop) → Prop where
  | now {s : σ} {P : σ → Prop} : P s → Eventually 0 s P
  | later {n : Nat} {s : σ} {P : σ → Prop} :
      (∀ r, ¬ fin s r) →
      (∀ t s', R s t s' → t = E0) →
      (∀ t s', R s t s' → Eventually n s' P) →
      Eventually (n + 1) s P

/-- The second constructor in Rocq's form (silent steps leading to `eventually n`). -/
theorem Eventually.later' {R : σ → Trace → σ → Prop} {fin : σ → Integers.Int → Prop}
    {n : Nat} {s : σ} {P : σ → Prop} (h1 : ∀ r, ¬ fin s r)
    (h2 : ∀ t s', R s t s' → t = E0 ∧ Eventually R fin n s' P) : Eventually R fin (n + 1) s P :=
  .later h1 (fun t s' h => (h2 t s' h).1) (fun t s' h => (h2 t s' h).2)

theorem Eventually.later_inv {R : σ → Trace → σ → Prop} {fin : σ → Integers.Int → Prop}
    {n : Nat} {s : σ} {P : σ → Prop} (h : Eventually R fin (n + 1) s P) :
    (∀ r, ¬ fin s r) ∧ ∀ t s', R s t s' → t = E0 ∧ Eventually R fin n s' P := by
  cases h with
  | later h1 h2 h3 => exact ⟨h1, fun t s' h => ⟨h2 t s' h, h3 t s' h⟩⟩

variable {R fin}

/-- `Smallstep.eventually_one` -/
theorem eventually_one {s : σ} {P : σ → Prop} (h1 : ∀ r, ¬ fin s r)
    (h2 : ∀ t s', R s t s' → t = E0 ∧ P s') : Eventually R fin 1 s P :=
  .later h1 (fun t s' h => (h2 t s' h).1) (fun t s' h => .now (h2 t s' h).2)

/-- `Smallstep.eventually_trans` -/
theorem eventually_trans {n1 : Nat} {s1 : σ} {P1 P2 : σ → Prop} {n2 : Nat}
    (h : Eventually R fin n1 s1 P1) (h2 : ∀ s2, P1 s2 → Eventually R fin n2 s2 P2) :
    Eventually R fin (n1 + n2) s1 P2 := by
  induction h with
  | now hp => rw [Nat.zero_add]; exact h2 _ hp
  | later hfin hE0 _ ih =>
    rw [Nat.add_right_comm]
    exact .later hfin hE0 fun t s' hs => ih t s' hs h2

/-- `Smallstep.eventually_implies` -/
theorem eventually_implies {n : Nat} {s : σ} {P1 P2 : σ → Prop} (h : Eventually R fin n s P1)
    (himp : ∀ s, P1 s → P2 s) : Eventually R fin n s P2 := by
  have := eventually_trans (n2 := 0) h (fun s hs => .now (himp s hs))
  rwa [Nat.add_zero] at this

/-- `Smallstep.eventually_and_invariant` -/
theorem eventually_and_invariant (Inv : σ → Prop) (hinv : ∀ s t s', R s t s' → Inv s → Inv s')
    {n : Nat} {s : σ} {P : σ → Prop} (h : Eventually R fin n s P) (hs : Inv s) :
    Eventually R fin n s (fun s' => P s' ∧ Inv s') := by
  induction h with
  | now hp => exact .now ⟨hp, hs⟩
  | later hfin hE0 _ ih =>
    exact .later hfin hE0 fun t s' hstep => ih t s' hstep (hinv _ _ _ hstep hs)

end Eventually

section ForwardEventually
variable {L1 L2 : Semantics} (match_states : L1.state → L2.state → Prop)
  (hpub : ∀ id, L2.symbolenv.public_symbol id = L1.symbolenv.public_symbol id)
  (hinit : ∀ s1, L1.initial_state s1 → ∃ s2, L2.initial_state s2 ∧ match_states s1 s2)
  (hfinal : ∀ s1 s2 r, match_states s1 s2 → L1.final_state s1 r → L2.final_state s2 r)
include hpub hinit hfinal

/-- `Smallstep.forward_simulation_eventually_star_wf` -/
theorem forward_simulation_eventually_star_wf (order : L1.state → L1.state → Prop)
    (hwf : WellFounded order)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      (∃ s2', (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ order s1' s1)) ∧
        match_states s1' s2') ∨
      (∃ n s2', Plus L2.step s2 t s2' ∧
        Eventually L1.step L1.final_state n s1' (fun s1'' => match_states s1'' s2'))) :
    ForwardSimulation L1 L2 := by
  let lex := Prod.lex (⟨Nat.lt, Nat.lt_wfRel.wf⟩ : WellFoundedRelation Nat)
    (⟨order, hwf⟩ : WellFoundedRelation L1.state)
  refine ⟨Nat × L1.state, lex.rel,
    fun i s1 s2 => i.2 = s1 ∧
      Eventually L1.step L1.final_state i.1 s1 (fun s1'' => match_states s1'' s2), ?_⟩
  refine
    { order_wf := lex.wf
      initial_states := ?_
      final_states := ?_
      simulation := ?_
      public_preserved := hpub }
  · intro s1 h
    obtain ⟨s2, h2, hm⟩ := hinit s1 h
    exact ⟨(0, s1), s2, h2, rfl, .now hm⟩
  · rintro ⟨n, s11⟩ s1 s2 r ⟨hP, hQ⟩ hf
    cases hQ with
    | now hm => exact hfinal _ _ _ hm hf
    | later hnf _ _ => exact absurd hf (hnf r)
  · rintro s1 t s1' hst ⟨n, s11⟩ s2 ⟨hP, hQ⟩
    cases hQ with
    | now hm =>
      rcases hsim s1 t s1' hst s2 hm with ⟨s2', A, B⟩ | ⟨n', s2', A, B⟩
      · refine ⟨(0, s1'), s2', ?_, rfl, .now B⟩
        rcases A with A | ⟨A1, A2⟩
        · exact .inl A
        · refine .inr ⟨A1, ?_⟩
          dsimp only at hP
          subst hP
          exact Prod.Lex.right _ A2
      · exact ⟨(n', s1'), s2', .inl A, rfl, B⟩
    | later hnf hE0 hst' =>
      rename_i n0
      have hev := hst' t s1' hst
      obtain rfl := hE0 t s1' hst
      refine ⟨(n0, s1'), s2, .inr ⟨.refl _, ?_⟩, rfl, hev⟩
      exact Prod.Lex.left _ _ (Nat.lt_succ_self n0)

/-- `Smallstep.forward_simulation_eventually_star` -/
theorem forward_simulation_eventually_star (measure : L1.state → Nat)
    (hsim : ∀ s1 t s1', L1.step s1 t s1' → ∀ s2, match_states s1 s2 →
      (∃ s2', (Plus L2.step s2 t s2' ∨ (Star L2.step s2 t s2' ∧ measure s1' < measure s1)) ∧
        match_states s1' s2') ∨
      (∃ n s2', Plus L2.step s2 t s2' ∧
        Eventually L1.step L1.final_state n s1' (fun s1'' => match_states s1'' s2'))) :
    ForwardSimulation L1 L2 :=
  forward_simulation_eventually_star_wf match_states hpub hinit hfinal
    (fun x y => measure x < measure y) (InvImage.wf measure Nat.lt_wfRel.wf) hsim

end ForwardEventually

end Smallstep
end CC
