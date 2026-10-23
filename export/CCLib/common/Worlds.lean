/-
  Deterministic external worlds — port of the first part of
  `common/Determinism.v` ("Deterministic worlds": `world`, `nextworld_*`,
  `possible_event`, `possible_trace`, `possible_trace_app`, …), which is what
  the reference interpreter `CCLib.cfrontend.Cexec` (`cfrontend/Cexec.v`) needs.

  Notes on faithfulness:
  * Rocq's `world` is a `CoInductive` type with one constructor
    `World io vload vstore`, whose three fields return the next world.  Lean has
    no coinductive types, so a world is represented by an arbitrary *state
    machine*: a type of states `σ`, the current state, and the three transition
    functions over `σ`.  Every Rocq world is such a machine (take `σ := world`)
    and every machine unfolds to a Rocq world, so the two types describe the
    same behaviours.  The only visible difference is that two `World`s with the
    same behaviour need not be equal (Rocq would need bisimilarity for that
    too); nothing in `Determinism.v` or `Cexec.v` compares worlds.
  * Because it packs a type, `World` lives in `Type 1`.
-/
import CCLib.common.Events

namespace CC

/-- `Determinism.world`: an external world, given as a state machine.  For an
    external call (name and arguments), a volatile load or a volatile store it
    either gets stuck (`none`) or returns a result and the next state. -/
structure World : Type 1 where
  /-- the type of the world's internal states -/
  σ : Type
  /-- the current state -/
  st : σ
  /-- answers to system calls -/
  io : σ → String → List EventVal → Option (EventVal × σ)
  /-- answers to volatile loads -/
  vload : σ → Chunk → Ident → Integers.Ptrofs → Option (EventVal × σ)
  /-- reactions to volatile stores -/
  vstore : σ → Chunk → Ident → Integers.Ptrofs → EventVal → Option σ

namespace World

/-- The same machine, moved to state `s`. -/
def withState (w : World) (s : w.σ) : World := { w with st := s }

end World

/-- `Determinism.nextworld_io` -/
def nextworldIo (w : World) (evname : String) (evargs : List EventVal) :
    Option (EventVal × World) :=
  (w.io w.st evname evargs).map fun p => (p.1, w.withState p.2)

/-- `Determinism.nextworld_vload` -/
def nextworldVload (w : World) (chunk : Chunk) (id : Ident) (ofs : Integers.Ptrofs) :
    Option (EventVal × World) :=
  (w.vload w.st chunk id ofs).map fun p => (p.1, w.withState p.2)

/-- `Determinism.nextworld_vstore` -/
def nextworldVstore (w : World) (chunk : Chunk) (id : Ident) (ofs : Integers.Ptrofs)
    (v : EventVal) : Option World :=
  (w.vstore w.st chunk id ofs v).map fun s => w.withState s

/-- `Determinism.possible_event`: the event is accepted by world `w1`, which
    then becomes `w2`. -/
inductive PossibleEvent : World → Event → World → Prop where
  | syscall (w1 evname evargs evres w2) :
      nextworldIo w1 evname evargs = some (evres, w2) →
      PossibleEvent w1 (.Event_syscall evname evargs evres) w2
  | vload (w1 chunk id ofs evres w2) :
      nextworldVload w1 chunk id ofs = some (evres, w2) →
      PossibleEvent w1 (.Event_vload chunk id ofs evres) w2
  | vstore (w1 chunk id ofs evarg w2) :
      nextworldVstore w1 chunk id ofs evarg = some w2 →
      PossibleEvent w1 (.Event_vstore chunk id ofs evarg) w2
  | annot (w1 id args) :
      PossibleEvent w1 (.Event_annot id args) w1

/-- `Determinism.possible_trace`: every event of the finite trace `t` is
    accepted, starting from world `w` and ending in world `w'`. -/
inductive PossibleTrace : World → Trace → World → Prop where
  | nil (w) : PossibleTrace w E0 w
  | cons (w1 ev w2 t w3) :
      PossibleEvent w1 ev w2 → PossibleTrace w2 t w3 →
      PossibleTrace w1 (ev :: t) w3

/-- `Determinism.possible_trace_app` -/
theorem possibleTrace_app {w0 t1 w1 t2 w2}
    (h1 : PossibleTrace w0 t1 w1) (h2 : PossibleTrace w1 t2 w2) :
    PossibleTrace w0 (Eapp t1 t2) w2 := by
  induction h1 with
  | nil => exact h2
  | cons _ _ _ _ _ he _ ih => exact .cons _ _ _ _ _ he (ih h2)

/-- `Determinism.possible_trace_app_inv` -/
theorem possibleTrace_app_inv {t1 t2 w0 w2}
    (h : PossibleTrace w0 (Eapp t1 t2) w2) :
    ∃ w1, PossibleTrace w0 t1 w1 ∧ PossibleTrace w1 t2 w2 := by
  induction t1 generalizing w0 with
  | nil => exact ⟨w0, .nil _, h⟩
  | cons ev t1 ih =>
      cases h with
      | cons _ _ w1' _ _ he ht =>
          obtain ⟨w1, h1, h2⟩ := ih ht
          exact ⟨w1, .cons _ _ _ _ _ he h1, h2⟩

/-- The empty trace is possible only without changing the world. -/
theorem possibleTrace_E0_inv {w w'} (h : PossibleTrace w E0 w') : w' = w := by
  cases h; rfl

/-- A one-event trace. -/
theorem possibleTrace_single {w ev w'} (h : PossibleEvent w ev w') :
    PossibleTrace w [ev] w' :=
  .cons _ _ _ _ _ h (.nil _)

/-- Inversion for a one-event trace. -/
theorem possibleTrace_single_inv {w ev w'} (h : PossibleTrace w [ev] w') :
    PossibleEvent w ev w' := by
  cases h with
  | cons _ _ _ _ _ he ht => cases ht; exact he

end CC
