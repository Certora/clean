/-
  Port of `MenhirLib/Automaton.v`: LR(1) automata with the annotations used
  by the validators.

  Rocq's module types `AutInit` and `T` become the classes `AutInit` and
  `AutomatonT`; the functor `Types` becomes definitions parameterised by
  `AutInit`.
-/
import CCLib.MenhirLib.Grammar

namespace CC
namespace MenhirLib

/-- The states of the automaton and the symbol on top of the stack in each
non-initial state (Rocq's `AutInit`). -/
class AutInit [Alphs] [GrammarT] where
  /-- The non-initial states. -/
  noninitstate : Type
  [nonInitStateAlph : Alphabet noninitstate]
  /-- The initial states. -/
  initstate : Type
  [initStateAlph : Alphabet initstate]
  /-- When we are at this state, we know that this symbol is the top of the
  stack. -/
  last_symb_of_non_init_state : noninitstate → Symbol

export AutInit (noninitstate initstate last_symb_of_non_init_state)

@[reducible] instance AutInit.instNonInitStateAlph [Alphs] [GrammarT] [I : AutInit] :
    Alphabet I.noninitstate := I.nonInitStateAlph
@[reducible] instance AutInit.instInitStateAlph [Alphs] [GrammarT] [I : AutInit] :
    Alphabet I.initstate := I.initStateAlph

section Types
variable [Alphs] [GrammarT] [AutInit]

/-- The states: the initial ones are separated from the others. -/
inductive State where
  | Init : initstate → State
  | Ninit : noninitstate → State

namespace State

def inj : State → Nat
  | .Init i => 2 * Alphabet.inj i
  | .Ninit s => 2 * Alphabet.inj s + 1

theorem inj_inj (x y : State) (h : x.inj = y.inj) : x = y := by
  cases x with
  | Init a => cases y with
    | Init b => rw [Alphabet.inj_inj a b (by simp only [inj] at h; omega)]
    | Ninit b => simp only [inj] at h; omega
  | Ninit a => cases y with
    | Init b => simp only [inj] at h; omega
    | Ninit b => rw [Alphabet.inj_inj a b (by simp only [inj] at h; omega)]

instance alphabet : Alphabet State where
  inj := State.inj
  inj_inj := State.inj_inj
  all_list := (all_list : List initstate).map State.Init ++
    (all_list : List noninitstate).map State.Ninit
  all_list_forall x := by
    cases x with
    | Init t => exact List.mem_append_left _ (List.mem_map_of_mem (all_list_forall t))
    | Ninit n => exact List.mem_append_right _ (List.mem_map_of_mem (all_list_forall n))

instance : DecidableEq State := Alphabet.decEq

end State

instance : Coe noninitstate State := ⟨State.Ninit⟩
instance : Coe initstate State := ⟨State.Init⟩

/-- The action to perform after having read a lookahead terminal. -/
inductive lookahead_action (term : terminal) where
  | Shift_act (s : noninitstate) : Symbol.T term = last_symb_of_non_init_state s →
      lookahead_action term
  | Reduce_act : production → lookahead_action term
  | Fail_act : lookahead_action term

/-- The action of a state: either a reduction without looking at the input,
or a decision depending on the lookahead terminal. -/
inductive action where
  | Default_reduce_act : production → action
  | Lookahead_act : (∀ term : terminal, lookahead_action term) → action

/-- A set of LR(1) items sharing the same core (an annotation needed to
validate completeness). -/
structure item where
  /-- The pseudo-production of the item. -/
  prod_item : production
  /-- The position of the dot. -/
  dot_pos_item : Nat
  /-- The lookahead symbols of the item. -/
  lookaheads_item : List terminal

end Types

/-- An LR(1) automaton with its annotations (Rocq's `Automaton.T`). -/
class AutomatonT [Alphs] [GrammarT] [AutInit] where
  /-- For each initial state, the non terminal it recognizes. -/
  start_nt : initstate → nonterminal
  /-- The action table. -/
  action_table : State → action
  /-- The goto table. -/
  goto_table : State → ∀ nt : nonterminal,
    Option { s : noninitstate // Symbol.NT nt = last_symb_of_non_init_state s }
  /-- The symbols known to be just below the top of the stack (the head of
  the list is the closest to the top). -/
  past_symb_of_non_init_state : noninitstate → List Symbol
  /-- Predicates satisfied by the (strictly) previous states of the stack. -/
  past_state_of_non_init_state : noninitstate → List (State → Bool)
  /-- The items of each state. -/
  items_of_state : State → List item
  /-- The nullable non-terminals. -/
  nullable_nterm : nonterminal → Bool
  /-- The terminals that can begin a word derived from a non-terminal. -/
  first_nterm : nonterminal → List terminal

export AutomatonT (start_nt action_table goto_table past_symb_of_non_init_state
  past_state_of_non_init_state items_of_state nullable_nterm first_nterm)

end MenhirLib
end CC
