/-
  Port of `MenhirLib/Interpreter.v`: the LR(1) interpreter.

  Differences from Rocq:
  * input buffers (`buffer`, a coinductive stream in Rocq) are functions
    `Nat → token`;
  * Rocq thunks the propositions given to the interpreter (`thunkP`) and
    re-proves equalities by decision (`reprove`, `cast`) to avoid reducing
    proof terms at run time.  Lean erases proofs and casts in compiled code,
    so the propositions are passed directly and values are transported with
    `cast`;
  * the stack invariant is a recursive definition instead of a pair of
    mutually inductive predicates, and `pop` is reasoned about directly
    (Rocq's declarative `pop_spec` is not needed).
-/
import CCLib.MenhirLib.Validator_safe

namespace CC
namespace MenhirLib

section Interpreter
variable [Alphs] [GrammarT] [AutInit] [AutomatonT]

/-! ## Input buffers -/

/-- Input buffers: infinite streams of tokens. -/
abbrev Buffer := Nat → token

def buf_head (b : Buffer) : token := b 0
def buf_tail (b : Buffer) : Buffer := fun n => b (n + 1)
def Buf_cons (t : token) (b : Buffer) : Buffer := fun n =>
  match n with
  | 0 => t
  | n + 1 => b n

/-- Concatenation of a list and an input buffer. -/
def app_buf : List token → Buffer → Buffer
  | [], buf => buf
  | t :: q, buf => Buf_cons t (app_buf q buf)

omit [AutInit] [AutomatonT] in
@[simp] theorem buf_head_cons (t : token) (b : Buffer) : buf_head (Buf_cons t b) = t := rfl

omit [AutInit] [AutomatonT] in
@[simp] theorem buf_tail_cons (t : token) (b : Buffer) : buf_tail (Buf_cons t b) = b := rfl

omit [AutInit] [AutomatonT] in
theorem buf_cons_head_tail (b : Buffer) : Buf_cons (buf_head b) (buf_tail b) = b := by
  funext n; cases n <;> rfl

omit [AutInit] [AutomatonT] in
theorem app_buf_assoc (l1 l2 : List token) (buf : Buffer) :
    app_buf l1 (app_buf l2 buf) = app_buf (l1 ++ l2) buf := by
  induction l1 with
  | nil => rfl
  | cons t q ih => simp [app_buf, ih]

/-! ## Stacks -/

/-- The type of a non initial state: the type of semantic values associated
with the last symbol of this state. -/
def noninitstate_type (s : noninitstate) : Type :=
  symbol_semantic_type (last_symb_of_non_init_state s)

/-- The stack of the automaton: non-initial states with a semantic value for
their last symbol. -/
abbrev Stack := List (Σ s : noninitstate, noninitstate_type s)

variable (init : initstate)

/-- The top state of a stack. -/
def state_of_stack : Stack → State
  | [] => .Init init
  | ⟨s, _⟩ :: _ => .Ninit s

/-- The stack of states of an automaton stack. -/
def state_stack_of_stack (stk : Stack) : List (State → Bool) :=
  stk.map (fun cell => singleton_state_pred (.Ninit cell.1)) ++ [singleton_state_pred (.Init init)]

/-- The stack of symbols of an automaton stack. -/
def symb_stack_of_stack (stk : Stack) : List Symbol :=
  stk.map (fun cell => last_symb_of_non_init_state cell.1)

/-- The stack invariant for the top of the stack. -/
def stack_invariant_top (stk : Stack) : Prop :=
  head_symbs_of_state (state_of_stack init stk) <+: symb_stack_of_stack stk ∧
  prefix_pred (head_states_of_state (state_of_stack init stk)) (state_stack_of_stack init stk)

/-- The stack invariant: the assumptions on the states hold at every level of
the stack. -/
def stack_invariant : Stack → Prop
  | [] => stack_invariant_top init []
  | c :: r => stack_invariant_top init (c :: r) ∧ stack_invariant r

theorem stack_invariant.top {stk : Stack} (h : stack_invariant init stk) :
    stack_invariant_top init stk := by
  cases stk with
  | nil => exact h
  | cons c r => exact h.1

omit [Alphs] [GrammarT] [AutInit] [AutomatonT] in
theorem implb_self (b : Bool) : (!b || b) = true := by cases b <;> rfl

theorem stack_invariant_nil : stack_invariant init [] := by
  refine ⟨List.nil_prefix, ?_⟩
  exact .cons _ _ _ _ (fun x => implb_self _) (.nil _)

/-- `pop` pops some symbols from the stack, and returns the popped semantic
values applied to `action`. -/
def pop : (symbols_to_pop : List Symbol) → {A : Type} → (stk : Stack) →
    symbols_to_pop <+: symb_stack_of_stack stk →
    arrows_right A (symbols_to_pop.map symbol_semantic_type) → Stack × A
  | [], _, stk, _, action => (stk, action)
  | t :: q, _, ⟨s, sem⟩ :: stk, hp, action =>
    have h := List.cons_prefix_cons.1 hp
    pop q stk h.2 (action (cast (congrArg symbol_semantic_type h.1.symm) sem))
  | _ :: _, _, [], hp, _ => absurd hp (by simp [symb_stack_of_stack])

theorem pop_preserves_invariant (symbols_to_pop : List Symbol) {A : Type} (stk : Stack) hp
    (action : arrows_right A (symbols_to_pop.map symbol_semantic_type)) :
    stack_invariant init stk → stack_invariant init (pop symbols_to_pop stk hp action).1 := by
  induction symbols_to_pop generalizing stk with
  | nil => intro h; exact h
  | cons t q ih =>
    intro h
    match stk, hp, h with
    | ⟨s, sem⟩ :: stk, hp, h => exact ih _ _ _ h.2
    | [], hp, _ => exact absurd hp (by simp [symb_stack_of_stack])

omit [AutomatonT] in
theorem state_stack_of_stack_cons (c : Σ s : noninitstate, noninitstate_type s) (r : Stack) :
    state_stack_of_stack init (c :: r) =
      singleton_state_pred (.Ninit c.1) :: state_stack_of_stack init r := rfl

omit [AutomatonT] in
theorem state_stack_of_stack_head (stk : Stack) :
    ∃ l, state_stack_of_stack init stk = singleton_state_pred (state_of_stack init stk) :: l := by
  cases stk with
  | nil => exact ⟨_, rfl⟩
  | cons c r => exact ⟨_, rfl⟩

omit [AutomatonT] in
theorem pop_state_valid (symbols_to_pop : List Symbol) {A : Type} (stk : Stack) hp
    (action : arrows_right A (symbols_to_pop.map symbol_semantic_type))
    (lpred : List (State → Bool)) :
    prefix_pred lpred (state_stack_of_stack init stk) →
    state_valid_after_pop (state_of_stack init (pop symbols_to_pop stk hp action).1)
      symbols_to_pop lpred := by
  induction symbols_to_pop generalizing stk lpred with
  | nil =>
    intro hpp
    cases lpred with
    | nil => exact .nil2 _
    | cons p pl =>
      refine .nil1 _ _ ?_
      show p (state_of_stack init stk) = true
      obtain ⟨l, hl⟩ := state_stack_of_stack_head init stk
      rw [hl] at hpp
      cases hpp with
      | cons _ _ _ _ himpl _ =>
        have := himpl (state_of_stack init stk)
        rw [singleton_state_pred_refl] at this
        simpa using this
  | cons t q ih =>
    intro hpp
    match stk, hp, hpp with
    | ⟨s, sem⟩ :: stk, hp, hpp =>
      cases lpred with
      | nil => exact .nil2 _
      | cons p pl =>
        refine .cons _ _ _ _ (ih _ _ _ pl ?_)
        rw [state_stack_of_stack_cons] at hpp
        cases hpp with
        | cons _ _ _ _ _ h => exact h
    | [], hp, _ => exact absurd hp (by simp [symb_stack_of_stack])

/-- The result of one step of the automaton: failure (the input is
rejected), acceptance (with the semantic value and the rest of the input) or
progress. -/
inductive step_result where
  | Fail_sr_full : State → token → step_result
  | Accept_sr : symbol_semantic_type (.NT (start_nt init)) → Buffer → step_result
  | Progress_sr : Stack → Buffer → step_result

variable {init}

theorem reduce_pop_ok {stk : Stack} {prod : production}
    (Hval : valid_for_reduce (state_of_stack init stk) prod) (Hi : stack_invariant init stk) :
    prod_rhs_rev prod <+: symb_stack_of_stack stk :=
  Hval.1.trans (Hi.top init).1

theorem reduce_accept_ok' {stk : Stack} {prod : production}
    (Hval : valid_for_reduce (state_of_stack init stk) prod) (Hi : stack_invariant init stk)
    (hg : goto_table (state_of_stack init
      (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1)
      (prod_lhs prod) = none) :
    (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1 = [] ∧
    prod_lhs prod = start_nt init := by
  have hv := Hval.2 _ (pop_state_valid init _ stk (reduce_pop_ok Hval Hi) (prod_action prod) _
    (Hi.top init).2)
  revert hv
  rw [hg]
  generalize (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1 = stk'
  cases stk' with
  | nil => exact fun h => ⟨rfl, h⟩
  | cons c r => exact False.elim

theorem reduce_accept_ok {stk : Stack} {prod : production}
    (Hval : valid_for_reduce (state_of_stack init stk) prod) (Hi : stack_invariant init stk)
    (hg : goto_table (state_of_stack init
      (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1)
      (prod_lhs prod) = none) :
    prod_lhs prod = start_nt init :=
  (reduce_accept_ok' Hval Hi hg).2

/-- `reduce_step` does a reduce action: it pops some elements from the stack,
executes the action of the production and follows the goto for the produced
non terminal symbol. -/
def reduce_step (stk : Stack) (prod : production) (buffer : Buffer)
    (Hval : valid_for_reduce (state_of_stack init stk) prod) (Hi : stack_invariant init stk) :
    step_result init :=
  let r := pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)
  match hg : goto_table (state_of_stack init r.1) (prod_lhs prod) with
  | some ⟨state_new, e⟩ =>
    .Progress_sr (⟨state_new, cast (congrArg symbol_semantic_type e) r.2⟩ :: r.1) buffer
  | none =>
    .Accept_sr (cast (congrArg (fun nt => symbol_semantic_type (.NT nt))
      (reduce_accept_ok Hval Hi hg)) r.2) buffer

/-- The two possible outcomes of `reduce_step`. -/
theorem reduce_step_spec (stk : Stack) (prod : production) (buffer : Buffer)
    (Hval : valid_for_reduce (state_of_stack init stk) prod) (Hi : stack_invariant init stk) :
    (∃ state_new e,
      goto_table (state_of_stack init
        (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1)
        (prod_lhs prod) = some ⟨state_new, e⟩ ∧
      reduce_step stk prod buffer Hval Hi =
        .Progress_sr (⟨state_new, cast (congrArg symbol_semantic_type e)
          (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).2⟩ ::
          (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1) buffer) ∨
    (∃ e : prod_lhs prod = start_nt init,
      goto_table (state_of_stack init
        (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1)
        (prod_lhs prod) = none ∧
      (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).1 = [] ∧
      reduce_step stk prod buffer Hval Hi =
        .Accept_sr (cast (congrArg (fun nt => symbol_semantic_type (.NT nt)) e)
          (pop (prod_rhs_rev prod) stk (reduce_pop_ok Hval Hi) (prod_action prod)).2) buffer) := by
  unfold reduce_step
  dsimp only
  split
  · rename_i state_new e hg
    exact Or.inl ⟨state_new, e, hg, rfl⟩
  · rename_i hg
    exact Or.inr ⟨reduce_accept_ok Hval Hi hg, hg, (reduce_accept_ok' Hval Hi hg).1, rfl⟩

theorem goto_preserves_invariant {stk : Stack} (Hsafe : safe) (nt : nonterminal)
    (state_new : noninitstate) (e) (sem)
    (hg : goto_table (state_of_stack init stk) nt = some ⟨state_new, e⟩)
    (Hi : stack_invariant init stk) :
    stack_invariant init (⟨state_new, sem⟩ :: stk) := by
  have h1 := Hsafe.2.1 (state_of_stack init stk) nt
  have h2 := Hsafe.2.2.2.1 (state_of_stack init stk) nt
  rw [hg] at h1 h2
  refine ⟨⟨?_, ?_⟩, Hi⟩
  · exact List.cons_prefix_cons.2 ⟨rfl, h1.trans (Hi.top init).1⟩
  · exact .cons _ _ _ _ (fun x => implb_self _) (prefix_pred_trans h2 (Hi.top init).2)

theorem reduce_step_stack_invariant_preserved (Hsafe : safe) {stk : Stack} {prod : production}
    {buffer : Buffer} {Hv : valid_for_reduce (state_of_stack init stk) prod}
    {Hi : stack_invariant init stk} {stk' : Stack} {buffer' : Buffer} :
    reduce_step stk prod buffer Hv Hi = .Progress_sr stk' buffer' → stack_invariant init stk' := by
  unfold reduce_step
  dsimp only
  have Hi' := pop_preserves_invariant init (prod_rhs_rev prod) stk (reduce_pop_ok Hv Hi)
    (prod_action prod) Hi
  split
  · rename_i state_new e hg
    intro h
    injection h with h1 h2
    subst h1
    exact goto_preserves_invariant Hsafe _ _ _ _ hg Hi'
  · intro h; cases h

theorem reduce_ok_of_default (Hsafe : safe) {s : State} {prod : production}
    (ha : action_table s = .Default_reduce_act prod) : valid_for_reduce s prod := by
  have := Hsafe.2.2.2.2 s
  rw [ha] at this
  exact this

theorem reduce_ok_of_lookahead (Hsafe : safe) {s : State} {awt} {t : terminal}
    {prod : production} (ha : action_table s = .Lookahead_act awt)
    (hl : awt t = .Reduce_act prod) : valid_for_reduce s prod := by
  have := Hsafe.2.2.2.2 s
  rw [ha] at this
  have := this t
  rw [hl] at this
  exact this

variable (Hsafe : safe) (init)

/-- One step of parsing. -/
def step (stk : Stack) (buffer : Buffer) (Hi : stack_invariant init stk) : step_result init :=
  match ha : action_table (state_of_stack init stk) with
  | .Default_reduce_act prod => reduce_step stk prod buffer (reduce_ok_of_default Hsafe ha) Hi
  | .Lookahead_act awt =>
    match hl : awt (token_term (buf_head buffer)) with
    | .Shift_act state_new e =>
      .Progress_sr (⟨state_new, cast (congrArg symbol_semantic_type e)
        (token_sem (buf_head buffer))⟩ :: stk) (buf_tail buffer)
    | .Reduce_act prod => reduce_step stk prod buffer (reduce_ok_of_lookahead Hsafe ha hl) Hi
    | .Fail_act => .Fail_sr_full (state_of_stack init stk) (buf_head buffer)

/-- The possible outcomes of `step`. -/
theorem step_spec (stk : Stack) (buffer : Buffer) (Hi : stack_invariant init stk) :
    (∃ prod Hv, action_table (state_of_stack init stk) = .Default_reduce_act prod ∧
      step init Hsafe stk buffer Hi = reduce_step stk prod buffer Hv Hi) ∨
    (∃ awt state_new e, action_table (state_of_stack init stk) = .Lookahead_act awt ∧
      awt (token_term (buf_head buffer)) = .Shift_act state_new e ∧
      step init Hsafe stk buffer Hi = .Progress_sr (⟨state_new,
        cast (congrArg symbol_semantic_type e) (token_sem (buf_head buffer))⟩ :: stk)
        (buf_tail buffer)) ∨
    (∃ awt prod Hv, action_table (state_of_stack init stk) = .Lookahead_act awt ∧
      awt (token_term (buf_head buffer)) = .Reduce_act prod ∧
      step init Hsafe stk buffer Hi = reduce_step stk prod buffer Hv Hi) ∨
    (∃ awt, action_table (state_of_stack init stk) = .Lookahead_act awt ∧
      awt (token_term (buf_head buffer)) = .Fail_act ∧
      step init Hsafe stk buffer Hi = .Fail_sr_full (state_of_stack init stk) (buf_head buffer)) := by
  unfold step
  split
  · rename_i prod ha
    exact Or.inl ⟨prod, reduce_ok_of_default Hsafe ha, ha, rfl⟩
  · rename_i awt ha
    split
    · rename_i state_new e hl
      exact Or.inr (Or.inl ⟨awt, state_new, e, ha, hl, rfl⟩)
    · rename_i prod hl
      exact Or.inr (Or.inr (Or.inl ⟨awt, prod, reduce_ok_of_lookahead Hsafe ha hl, ha, hl, rfl⟩))
    · rename_i hl
      exact Or.inr (Or.inr (Or.inr ⟨awt, ha, hl, rfl⟩))

theorem step_stack_invariant_preserved {stk : Stack} {buffer : Buffer} {Hi}
    {stk' : Stack} {buffer' : Buffer} :
    step init Hsafe stk buffer Hi = .Progress_sr stk' buffer' → stack_invariant init stk' := by
  unfold step
  split
  · exact reduce_step_stack_invariant_preserved Hsafe
  · rename_i awt ha
    split
    · rename_i state_new e hl
      intro h
      injection h with h1 h2
      subst h1
      have h1 := Hsafe.1 (state_of_stack init stk)
      have h2 := Hsafe.2.2.1 (state_of_stack init stk)
      rw [ha] at h1 h2
      have h1 := h1 (token_term (buf_head buffer))
      have h2 := h2 (token_term (buf_head buffer))
      rw [hl] at h1 h2
      refine ⟨⟨?_, ?_⟩, Hi⟩
      · exact List.cons_prefix_cons.2 ⟨rfl, h1.trans (Hi.top init).1⟩
      · exact .cons _ _ _ _ (fun x => implb_self _) (prefix_pred_trans h2 (Hi.top init).2)
    · exact reduce_step_stack_invariant_preserved Hsafe
    · intro h; cases h

/-- The main loop of the parser.  `log_n_steps` is the logarithm (in base 2)
of the number of steps to perform. -/
def parse_fix : (stk : Stack) → (buffer : Buffer) → (log_n_steps : Nat) →
    stack_invariant init stk →
    { sr : step_result init //
      ∀ stk' buffer', sr = .Progress_sr stk' buffer' → stack_invariant init stk' }
  | stk, buffer, 0, Hi =>
    ⟨step init Hsafe stk buffer Hi, fun _ _ => step_stack_invariant_preserved init Hsafe⟩
  | stk, buffer, n + 1, Hi =>
    match parse_fix stk buffer n Hi with
    | ⟨.Progress_sr stk' buffer', Hi'⟩ => parse_fix stk' buffer' n (Hi' _ _ rfl)
    | sr => sr

/-- The final result of a parsing: a failure (the automaton has rejected the
input word), a timeout (the automaton has spent all the given
`2^log_n_steps` steps), or a semantic value with the rest of the input
buffer. -/
inductive parse_result (A : Type) where
  | Fail_pr_full : State → token → parse_result A
  | Timeout_pr : parse_result A
  | Parsed_pr : A → Buffer → parse_result A

/-- The parser. -/
def parse (buffer : Buffer) (log_n_steps : Nat) :
    parse_result (symbol_semantic_type (.NT (start_nt init))) :=
  match (parse_fix init Hsafe [] buffer log_n_steps (stack_invariant_nil init)).1 with
  | .Fail_sr_full st tok => .Fail_pr_full st tok
  | .Accept_sr sem buffer' => .Parsed_pr sem buffer'
  | .Progress_sr _ _ => .Timeout_pr

end Interpreter

end MenhirLib
end CC
