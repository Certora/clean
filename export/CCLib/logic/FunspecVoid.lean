/-
  A `void` function whose body falls off its end meets its specification.

  `satisfies_internal_noVars` asks the body to leave only through `return`.
  A `void` function may instead reach the end of its body (`Sskip` under a
  call continuation): Clight's `step_skip_call` then returns `Vundef`.  The
  variant below accepts both exits.
-/
import CCLib.logic.FunspecCall

namespace CC
namespace Sep

open HProp

/-- Deriving `SatisfiesAt` for a function with no block-scoped variables
whose body may fall off its end (returning `Vundef`) as well as `return`. -/
theorem satisfies_internal_noVars_void (ge fe f) (S : FunSpec) (vargs : List Val)
    (Pbody : Assn)
    (hentry : ∀ m : Mem, ∃ le : TempEnv, fe f vargs m emptyEnv le m
                ∧ ∀ hp, S.pre vargs hp → Pbody emptyEnv le hp)
    (body : Triple ge fe f Pbody f.fn_body
        { normal := fun e _ hp => e = emptyEnv ∧ S.post .Vundef hp, brk := Assn.no,
          cont := Assn.no, ret := S.post }) :
    SatisfiesAt ge fe (.Internal f) S vargs := by
  intro k m hp hf hk hpre hd hag
  obtain ⟨le, hent, himp⟩ := hentry m
  obtain ⟨o, hp', hs, hd', hag', hR⟩ := body k emptyEnv le hp hf m hd hag (himp hp hpre)
  cases o with
  | Normal e' le' m' =>
      obtain ⟨he, hpost⟩ := hR
      subst he
      refine ⟨.Vundef, m', hp', ?_, hpost, hd', hag'⟩
      have hs' : Steps (SStep ge fe) (.State f f.fn_body k emptyEnv le m)
                   (.State f .Sskip k emptyEnv le' m') := hs
      exact Steps.step _ _ _ (Step.internal_function f vargs k m emptyEnv le m hent)
        (Steps.trans hs' (Steps.one (Step.skip_call f k emptyEnv le' m' m' hk
          (freeList_emptyEnv _ _))))
  | Break _ _ _ => exact False.elim hR
  | Continue _ _ _ => exact False.elim hR
  | Goto _ _ _ _ => exact False.elim hR
  | Return v m' =>
      refine ⟨v, m', hp', ?_, hR, hd', hag'⟩
      have hs' : Steps (SStep ge fe) (.State f f.fn_body k emptyEnv le m)
                   (.Returnstate v (callCont k) m') := hs
      rw [callCont_of_isCallCont hk] at hs'
      exact Steps.step _ _ _
        (Step.internal_function f vargs k m emptyEnv le m hent) hs'

end Sep
end CC
