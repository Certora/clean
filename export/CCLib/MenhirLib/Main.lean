/-
  Port of `MenhirLib/Main.v`: the validated parser and its three theorems
  (correctness, completeness and unambiguity of the grammar).

  Rocq's functor `Make (Aut : Automaton.T)` becomes the namespace `Main`,
  whose definitions are parameterised by the automaton classes.

  `InterpreterFast` is imported so that the compiled code of `parse` uses the
  offset-based interpreter (`@[csimp] parse_eq_parse_fast`).
-/
import CCLib.MenhirLib.Interpreter_correct
import CCLib.MenhirLib.Interpreter_complete
import CCLib.MenhirLib.InterpreterFast

namespace CC
namespace MenhirLib
namespace Main

variable [Alphs] [GrammarT] [AutInit] [AutomatonT]

/-- The completeness validator. -/
def complete_validator : Unit → Bool := is_complete

/-- The safety validator. -/
def safe_validator : Unit → Bool := is_safe

/-- The parser, for an automaton accepted by the safety validator.
`log_n_steps` bounds the number of steps by `2 ^ log_n_steps`. -/
def parse (safe : safe_validator () = true) (init : initstate) (log_n_steps : Nat)
    (buffer : Buffer) : parse_result (symbol_semantic_type (.NT (start_nt init))) :=
  MenhirLib.parse init (safe_is_validator safe) buffer log_n_steps

/-- Correctness theorem: if the parser accepts, its result is the semantic
value of a parse tree of a prefix of the input, and the rest of the input is
returned. -/
theorem parse_correct (safe : safe_validator () = true) (init : initstate) (log_n_steps : Nat)
    (buffer : Buffer) :
    match parse safe init log_n_steps buffer with
    | .Parsed_pr sem buffer_new =>
      ∃ word, ∃ pt : parse_tree (.NT (start_nt init)) word,
        buffer = app_buf word buffer_new ∧ pt_sem pt = sem
    | _ => True :=
  MenhirLib.parse_correct init _ buffer log_n_steps

/-- Completeness theorem: for every parse tree of a word, the parser run on
this word followed by any input returns the semantic value of the tree and the
rest of the input if it has enough fuel, times out otherwise, and never
fails. -/
theorem parse_complete (safe : safe_validator () = true) (init : initstate) (log_n_steps : Nat)
    (word : List token) (buffer_end : Buffer) (complete : complete_validator () = true)
    (tree : parse_tree (.NT (start_nt init)) word) :
    match parse safe init log_n_steps (app_buf word buffer_end) with
    | .Fail_pr_full _ _ => False
    | .Parsed_pr sem_res buffer_end_res =>
      sem_res = pt_sem tree ∧ buffer_end_res = buffer_end ∧ pt_size tree ≤ 2 ^ log_n_steps
    | .Timeout_pr => 2 ^ log_n_steps < pt_size tree := by
  have := MenhirLib.parse_complete init (safe_is_validator safe) (complete_is_validator complete)
    word buffer_end tree log_n_steps
  unfold parse
  revert this
  cases MenhirLib.parse init (safe_is_validator safe) (app_buf word buffer_end) log_n_steps <;>
    exact id

/-- Unambiguity theorem: two parse trees of the same word have the same
semantic value. -/
theorem unambiguity (safe : safe_validator () = true) (complete : complete_validator () = true)
    (htok : Nonempty token) (init : initstate) (word : List token)
    (tree1 tree2 : parse_tree (.NT (start_nt init)) word) : pt_sem tree1 = pt_sem tree2 := by
  obtain ⟨tok⟩ := htok
  let buf_end : Buffer := fun _ => tok
  have h1 := parse_complete safe init (pt_size tree1) word buf_end complete tree1
  have h2 := parse_complete safe init (pt_size tree1) word buf_end complete tree2
  revert h1 h2
  cases parse safe init (pt_size tree1) (app_buf word buf_end) with
  | Fail_pr_full _ _ => intro h; exact h.elim
  | Timeout_pr =>
    intro h1
    exact absurd h1 (Nat.not_lt.2 (Nat.le_of_lt (Nat.lt_two_pow_self)))
  | Parsed_pr sem _ =>
    rintro ⟨rfl, _⟩ ⟨h, _⟩
    exact h

end Main

end MenhirLib
end CC
