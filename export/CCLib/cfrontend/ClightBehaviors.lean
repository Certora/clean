/-
  Clight as a `Smallstep.Semantics` — the `Clight.semantics1`/`semantics2`
  definitions of `cfrontend/Clight.v`, plus the generic results of
  `Smallstep.lean` and `Behaviors.lean` instantiated to Clight:

  * `semantics1 p` / `semantics2 p` : the two Clight semantics (parameters as
    stack variables / as temporaries);
  * `semantics1_determinate` / `semantics2_determinate` : Rocq's
    `semantics_determinate`, stated with Smallstep's `determinate` record;
  * `program_behaves_exists1` / `program_behaves_exists2` : every Clight
    program has a behaviour (terminates, diverges, reacts or goes wrong);
  * `star_iff` : the Clight-specific `CC.Star` used by the program logic is the
    generic `Smallstep.Star`, so terminating runs proved with the program logic
    give `Terminates` behaviours (`behaves_terminates1`).
-/
import CCLib.common.Behaviors
import CCLib.common.Determinism

namespace CC
namespace Clight

open Smallstep

/-- `Clight.semantics1`: parameters are stack-allocated variables. -/
def semantics1 (p : Program) : Semantics where
  state := State
  step := Step1 p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv.genv_genv

/-- `Clight.semantics2`: parameters are temporaries. -/
def semantics2 (p : Program) : Semantics where
  state := State
  step := Step2 p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv.genv_genv

/-- The Clight-specific `CC.Star` (used by the program logic) coincides with
    the generic `Smallstep.Star`. -/
theorem star_iff {R : State → Trace → State → Prop} {s t s'} :
    CC.Star R s t s' ↔ Smallstep.Star R s t s' := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step _ _ _ _ _ _ hr _ ht ih => exact .step hr ih ht
  · intro h
    induction h with
    | refl => exact .refl _
    | step hr _ ht ih => exact .step _ _ _ _ _ _ hr ih ht

/-- `Clight.semantics_determinate` for `semantics1`. -/
theorem semantics1_determinate (p : Program) : Smallstep.Determinate (semantics1 p) :=
  let h := semantics_determinate1 p
  { sd_determ := h.sd_determ
    sd_traces := h.sd_traces
    sd_initial_determ := h.sd_initial_determ
    sd_final_nostep := fun s r hs t s' => h.sd_final_nostep s r t s' hs
    sd_final_determ := h.sd_final_determ }

/-- `Clight.semantics_determinate` for `semantics2`. -/
theorem semantics2_determinate (p : Program) : Smallstep.Determinate (semantics2 p) :=
  let h := semantics_determinate2 p
  { sd_determ := h.sd_determ
    sd_traces := h.sd_traces
    sd_initial_determ := h.sd_initial_determ
    sd_final_nostep := fun s r hs t s' => h.sd_final_nostep s r t s' hs
    sd_final_determ := h.sd_final_determ }

/-- Every Clight program (semantics 1) has a behaviour. -/
theorem program_behaves_exists1 (p : Program) : ∃ beh, ProgramBehaves (semantics1 p) beh :=
  program_behaves_exists _

/-- Every Clight program (semantics 2) has a behaviour. -/
theorem program_behaves_exists2 (p : Program) : ∃ beh, ProgramBehaves (semantics2 p) beh :=
  program_behaves_exists _

/-- A terminating run, as produced by the program logic, is a `Terminates`
    behaviour of the program. -/
theorem behaves_terminates1 {p : Program} {s s' t r} (hi : InitialState p s)
    (hs : CC.Star (Step1 p.globalenv) s t s') (hf : FinalState s' r) :
    ProgramBehaves (semantics1 p) (.Terminates t r) :=
  .runs (L := semantics1 p) hi (.terminates (star_iff.mp hs) hf)

/-- Same for semantics 2. -/
theorem behaves_terminates2 {p : Program} {s s' t r} (hi : InitialState p s)
    (hs : CC.Star (Step2 p.globalenv) s t s') (hf : FinalState s' r) :
    ProgramBehaves (semantics2 p) (.Terminates t r) :=
  .runs (L := semantics2 p) hi (.terminates (star_iff.mp hs) hf)

end Clight
end CC
